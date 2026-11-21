//! Shopping Sessions pipeline. See rules.md.
use memchr::memchr;
use memmap2::Mmap;
use rayon::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::hash::{BuildHasherDefault, Hasher};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;
use xxhash_rust::xxh3::{xxh3_128, xxh3_64};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const DAY: i64 = 86_400_000;
const GAP: i64 = 1_800_000;
const WEEK: i64 = 7 * DAY;
const NB: usize = 256;
const CHUNK: usize = 8 << 20;
const BAD: u8 = 255;

// ---------- hashing helpers ----------
#[derive(Default)]
struct IdH(u64);
impl Hasher for IdH {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        unreachable!()
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = x
    }
}
type IdMap<V> = HashMap<u64, V, BuildHasherDefault<IdH>>;

/// Exact byte-string dictionary (hash + verification).
struct Dict<'a> {
    map: IdMap<(&'a [u8], u32)>,
}
impl<'a> Dict<'a> {
    #[inline]
    fn get(&self, k: &[u8]) -> Option<u32> {
        match self.map.get(&xxh3_64(k)) {
            Some((s, v)) if *s == k => Some(*v),
            _ => None,
        }
    }
}

// ---------- CSV ----------
struct Lines<'a> {
    d: &'a [u8],
}
impl<'a> Iterator for Lines<'a> {
    type Item = &'a [u8];
    #[inline]
    fn next(&mut self) -> Option<&'a [u8]> {
        if self.d.is_empty() {
            return None;
        }
        match memchr(b'\n', self.d) {
            Some(p) => {
                let l = &self.d[..p];
                self.d = &self.d[p + 1..];
                Some(l)
            }
            None => {
                let l = self.d;
                self.d = &[];
                Some(l)
            }
        }
    }
}

#[inline]
fn unquote(f: &[u8]) -> Option<&[u8]> {
    if memchr(b'"', f).is_none() {
        return Some(f);
    }
    let n = f.len();
    if n >= 2 && f[0] == b'"' && f[n - 1] == b'"' && memchr(b'"', &f[1..n - 1]).is_none() {
        Some(&f[1..n - 1])
    } else {
        None
    }
}

/// Split a line into exactly N fields; false if malformed.
#[inline]
fn split_fields<'a, const N: usize>(line: &'a [u8], out: &mut [&'a [u8]; N]) -> bool {
    let len = line.len();
    let mut start = 0;
    let mut n = 0;
    loop {
        let end = match memchr(b',', &line[start..]) {
            Some(p) => start + p,
            None => len,
        };
        if n >= N {
            return false;
        }
        match unquote(&line[start..end]) {
            Some(v) => out[n] = v,
            None => return false,
        }
        n += 1;
        if end == len {
            break;
        }
        start = end + 1;
    }
    n == N
}

// ---------- timestamps ----------
#[inline]
fn d2(b: &[u8], i: usize) -> Option<i64> {
    let a = b[i].wrapping_sub(b'0');
    let c = b[i + 1].wrapping_sub(b'0');
    if a < 10 && c < 10 {
        Some((a as i64) * 10 + c as i64)
    } else {
        None
    }
}
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
#[inline]
fn dim(y: i64, m: i64) -> i64 {
    match m {
        2 => {
            if y % 4 == 0 && (y % 100 != 0 || y % 400 == 0) {
                29
            } else {
                28
            }
        }
        4 | 6 | 9 | 11 => 30,
        _ => 31,
    }
}
#[inline]
fn parse_dt(b: &[u8]) -> Option<i64> {
    if b[4] != b'-' || b[7] != b'-' || b[10] != b'T' || b[13] != b':' || b[16] != b':' {
        return None;
    }
    let y = d2(b, 0)? * 100 + d2(b, 2)?;
    let m = d2(b, 5)?;
    let d = d2(b, 8)?;
    let hh = d2(b, 11)?;
    let mi = d2(b, 14)?;
    let s = d2(b, 17)?;
    if !(1..=12).contains(&m) || d < 1 || d > dim(y, m) || hh > 23 || mi > 59 || s > 59 {
        return None;
    }
    Some(days_from_civil(y, m, d) * DAY + (hh * 3600 + mi * 60 + s) * 1000)
}
#[inline]
fn parse_digits(b: &[u8]) -> Option<i64> {
    if b.is_empty() {
        return None;
    }
    let mut v: i64 = 0;
    for &c in b {
        let x = c.wrapping_sub(b'0');
        if x >= 10 {
            return None;
        }
        v = v.checked_mul(10)?.checked_add(x as i64)?;
    }
    Some(v)
}
/// Returns None for any bad timestamp (including F3 overflow, which is out of any window).
#[inline]
fn parse_ts(b: &[u8]) -> Option<i64> {
    match b.len() {
        20 if b[19] == b'Z' => parse_dt(b),
        25 if (b[19] == b'+' || b[19] == b'-') && b[22] == b':' => {
            let base = parse_dt(b)?;
            let oh = d2(b, 20)?;
            let om = d2(b, 23)?;
            if oh > 23 || om > 59 {
                return None;
            }
            let off = (oh * 60 + om) * 60_000;
            Some(if b[19] == b'+' { base - off } else { base + off })
        }
        _ => {
            // F3: digits only; any non-digit (or overflow) is bad/out of window.
            if b.is_empty() || !b.iter().all(|c| c.is_ascii_digit()) {
                return None;
            }
            let nz = b.iter().position(|&c| c != b'0').unwrap_or(b.len());
            parse_digits(&b[nz..]).or(if nz == b.len() { Some(0) } else { None })
        }
    }
}
#[inline]
fn parse_price(b: &[u8]) -> Option<u32> {
    if b.is_empty() || !b.iter().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let nz = b.iter().position(|&c| c != b'0').unwrap_or(b.len());
    let r = &b[nz..];
    if r.is_empty() || r.len() > 8 {
        return None;
    }
    let v = parse_digits(r)?;
    if (1..=10_000_000).contains(&v) {
        Some(v as u32)
    } else {
        None
    }
}

// ---------- file handling ----------
fn list_csv(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.is_file() && p.extension().map(|x| x == "csv").unwrap_or(false))
            .collect(),
        Err(_) => vec![],
    };
    v.sort();
    v
}
fn map_files(paths: &[PathBuf]) -> Vec<Mmap> {
    paths
        .iter()
        .filter_map(|p| {
            let f = File::open(p).ok()?;
            if f.metadata().ok()?.len() == 0 {
                return None;
            }
            let m = unsafe { Mmap::map(&f).ok()? };
            #[cfg(unix)]
            let _ = m.advise(memmap2::Advice::Sequential);
            Some(m)
        })
        .collect()
}
/// Body of each file (header removed) split into ~CHUNK pieces at line boundaries.
fn chunks<'a>(maps: &'a [Mmap]) -> Vec<&'a [u8]> {
    let mut out = vec![];
    for m in maps {
        let d: &[u8] = m;
        let mut body = match memchr(b'\n', d) {
            Some(p) => &d[p + 1..],
            None => continue,
        };
        while body.len() > CHUNK {
            let cut = match memchr(b'\n', &body[CHUNK..]) {
                Some(p) => CHUNK + p + 1,
                None => body.len(),
            };
            out.push(&body[..cut]);
            body = &body[cut..];
        }
        if !body.is_empty() {
            out.push(body);
        }
    }
    out
}
fn read_small(p: &Path) -> Vec<u8> {
    std::fs::read(p).unwrap_or_default()
}

// ---------- records ----------
#[derive(Clone, Copy)]
struct Ev<'a> {
    e0: u64,
    e1: u64,
    ingest: i64,
    ts: i64,
    uid: &'a [u8],
    price: u32,
    cat: u8,
    typ: u8,
}
#[derive(Clone, Copy)]
struct Sv<'a> {
    pkey: u64,
    ts: i64,
    name: &'a [u8],
    price: u32,
    cat: u8,
    typ: u8,
}
#[derive(Clone, Copy)]
struct Ck<'a> {
    pkey: u64,
    ts: i64,
    cid: &'a [u8],
    camp: u32,
}
struct URow<'a> {
    name: &'a [u8],
    day: i32,
    sessions: i64,
    events: i64,
    revenue: i64,
    top: Option<u8>,
}

/// Maps a user id to its person: (key, name).
struct Persons<'a> {
    map: IdMap<u32>,
    person: Vec<(u64, &'a [u8])>,
}
impl<'a> Persons<'a> {
    #[inline]
    fn resolve(&self, uid: &'a [u8]) -> (u64, &'a [u8]) {
        let h = xxh3_64(uid);
        match self.map.get(&h) {
            Some(&i) => self.person[i as usize],
            None => (h, uid),
        }
    }
}

fn find(p: &mut [u32], mut x: u32) -> u32 {
    while p[x as usize] != x {
        let g = p[p[x as usize] as usize];
        p[x as usize] = g;
        x = g;
    }
    x
}

fn transpose<T>(parts: Vec<Vec<Vec<T>>>) -> Vec<Vec<Vec<T>>> {
    let mut out: Vec<Vec<Vec<T>>> = (0..NB).map(|_| Vec::with_capacity(parts.len())).collect();
    for p in parts {
        for (b, v) in p.into_iter().enumerate() {
            if !v.is_empty() {
                out[b].push(v);
            }
        }
    }
    out
}
fn concat<T: Copy>(vs: Vec<Vec<T>>) -> Vec<T> {
    let n = vs.iter().map(|v| v.len()).sum();
    let mut out = Vec::with_capacity(n);
    for v in vs {
        out.extend_from_slice(&v);
    }
    out
}
fn empty_buckets<T>() -> Vec<Vec<T>> {
    (0..NB).map(|_| Vec::new()).collect()
}

fn json_str<'a>(s: &'a str, key: &str) -> &'a str {
    let i = s.find(&format!("\"{}\"", key)).expect("manifest key");
    let rest = &s[i + key.len() + 2..];
    let a = rest.find('"').unwrap() + 1;
    let b = rest[a..].find('"').unwrap() + a;
    &rest[a..b]
}

fn main() {
    let t0 = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let data = PathBuf::from(std::env::var("DATA_DIR").unwrap_or_else(|_| {
        args.get(args.len().wrapping_sub(2)).cloned().unwrap_or("/data".into())
    }));
    let outdir = PathBuf::from(std::env::var("OUTPUT_DIR").unwrap_or("/output".into()));
    let ncpu: usize = std::env::var("NCPU").ok().and_then(|x| x.parse().ok()).unwrap_or(8);
    rayon::ThreadPoolBuilder::new().num_threads(ncpu).build_global().unwrap();
    let lap = |s: &str| eprintln!("[{:>8.3}s] {}", t0.elapsed().as_secs_f64(), s);

    // manifest
    let man = String::from_utf8(read_small(&data.join("manifest.json"))).unwrap();
    let ws = parse_ts(json_str(&man, "window_start").as_bytes()).expect("window_start");
    let we = parse_ts(json_str(&man, "window_end").as_bytes()).expect("window_end");
    let base_day = ws.div_euclid(DAY);
    let ndays = ((we - 1).div_euclid(DAY) - base_day + 1) as usize;

    // products
    let prod_raw = read_small(&data.join("products.csv"));
    let mut prows: Vec<(&[u8], &[u8])> = vec![];
    for l in lines(&prod_raw).skip(1) {
        let mut f = [&b""[..]; 2];
        if split_fields(l, &mut f) {
            prows.push((f[0], f[1]));
        }
    }
    let mut catnames: Vec<&[u8]> = prows.iter().map(|r| r.1).collect();
    catnames.push(b"unknown");
    catnames.sort();
    catnames.dedup();
    let unknown_cat = catnames.binary_search(&&b"unknown"[..]).unwrap() as u8;
    let ncat = catnames.len();
    assert!(ncat < 255);
    let mut products = Dict { map: IdMap::default() };
    for (p, c) in &prows {
        let ci = catnames.binary_search(c).unwrap() as u32;
        products.map.insert(xxh3_64(p), (p, ci));
    }

    // campaigns
    let camp_raw = read_small(&data.join("campaigns.csv"));
    let mut camps: Vec<(&[u8], &[u8])> = vec![];
    let mut campaigns = Dict { map: IdMap::default() };
    for l in lines(&camp_raw).skip(1) {
        let mut f = [&b""[..]; 2];
        if split_fields(l, &mut f) && campaigns.get(f[0]).is_none() {
            campaigns.map.insert(xxh3_64(f[0]), (f[0], camps.len() as u32));
            camps.push((f[0], f[1]));
        }
    }
    let ncamp = camps.len();
    let organic = ncamp as u32;

    let ev_maps = map_files(&list_csv(&data.join("events")));
    let ck_maps = map_files(&list_csv(&data.join("clicks")));
    let lk_maps = map_files(&list_csv(&data.join("links")));
    lap("setup");

    // ---------- links ----------
    let lk_chunks = chunks(&lk_maps);
    let pairs: Vec<Vec<(&[u8], &[u8])>> = lk_chunks
        .par_iter()
        .map(|ch| {
            let mut v = vec![];
            for l in lines(ch) {
                let mut f = [&b""[..]; 2];
                if split_fields(l, &mut f) && !f[0].is_empty() && !f[1].is_empty() {
                    v.push((f[0], f[1]));
                }
            }
            v
        })
        .collect();
    let mut map: IdMap<u32> = IdMap::default();
    let mut ids: Vec<&[u8]> = vec![];
    let mut parent: Vec<u32> = vec![];
    for v in &pairs {
        for &(a, b) in v {
            let mut get = |s| -> u32 {
                let h = xxh3_64(s);
                *map.entry(h).or_insert_with(|| {
                    ids.push(s);
                    parent.push(parent.len() as u32);
                    (ids.len() - 1) as u32
                })
            };
            let ia = get(a);
            let ib = get(b);
            let ra = find(&mut parent, ia);
            let rb = find(&mut parent, ib);
            if ra != rb {
                parent[ra as usize] = rb;
            }
        }
    }
    let n = ids.len();
    let mut rootname: Vec<u32> = (0..n as u32).collect(); // per root: index of min id
    for i in 0..n as u32 {
        let r = find(&mut parent, i);
        if ids[i as usize] < ids[rootname[r as usize] as usize] {
            rootname[r as usize] = i;
        }
    }
    let mut person: Vec<(u64, &[u8])> = Vec::with_capacity(n);
    for i in 0..n as u32 {
        let r = find(&mut parent, i);
        let nm = ids[rootname[r as usize] as usize];
        person.push((xxh3_64(nm), nm));
    }
    let persons = Persons { map, person };
    drop(pairs);
    lap(&format!("links: {} ids", n));

    // ---------- clicks ----------
    let ck_chunks = chunks(&ck_maps);
    let cw0 = ws - WEEK;
    let ck_parts: Vec<Vec<Vec<Ck>>> = ck_chunks
        .par_iter()
        .fold(empty_buckets, |mut acc, ch| {
            for l in lines(ch) {
                let mut f = [&b""[..]; 4];
                if !split_fields(l, &mut f) || f[0].is_empty() || f[1].is_empty() {
                    continue;
                }
                let ts = match parse_ts(f[3]) {
                    Some(t) if t >= cw0 && t < we => t,
                    _ => continue,
                };
                let camp = match campaigns.get(f[2]) {
                    Some(c) => c,
                    None => continue,
                };
                let (pkey, _) = persons.resolve(f[1]);
                acc[(pkey >> 56) as usize].push(Ck { pkey, ts, cid: f[0], camp });
            }
            acc
        })
        .collect();
    let ck_b = transpose(ck_parts);
    lap("clicks parsed");

    // ---------- events: parse ----------
    let ev_chunks = chunks(&ev_maps);
    let ev_parts: Vec<Vec<Vec<Ev>>> = ev_chunks
        .par_iter()
        .fold(empty_buckets, |mut acc, ch| {
            for l in lines(ch) {
                let mut f = [&b""[..]; 7];
                if !split_fields(l, &mut f) || f[0].is_empty() {
                    continue;
                }
                let h = xxh3_128(f[0]);
                let ingest = parse_ts(f[3]).unwrap_or(i64::MAX);
                let mut typ = match f[4] {
                    b"view" => 0u8,
                    b"cart" => 1,
                    b"purchase" => 2,
                    _ => BAD,
                };
                let mut ts = 0;
                let mut price = 0;
                let mut cat = 0;
                if typ != BAD {
                    if f[1].is_empty() || f[5].is_empty() {
                        typ = BAD;
                    } else {
                        match parse_ts(f[2]) {
                            Some(t) if t >= ws && t < we => {
                                ts = t;
                                if ingest.saturating_sub(t) > DAY {
                                    typ = BAD;
                                } else if typ == 2 {
                                    match parse_price(f[6]) {
                                        Some(p) => {
                                            price = p;
                                            cat = products.get(f[5]).map(|c| c as u8).unwrap_or(unknown_cat);
                                        }
                                        None => typ = BAD,
                                    }
                                }
                            }
                            _ => typ = BAD,
                        }
                    }
                }
                acc[(h >> 120) as usize].push(Ev {
                    e0: (h >> 64) as u64,
                    e1: h as u64,
                    ingest,
                    ts,
                    uid: f[1],
                    price,
                    cat,
                    typ,
                });
            }
            acc
        })
        .collect();
    let ev_b = transpose(ev_parts);
    lap("events parsed");

    // ---------- events: dedup + resolve ----------
    let sv_parts: Vec<Vec<Vec<Sv>>> = ev_b
        .into_par_iter()
        .map(|vs| {
            let mut v = concat(vs);
            v.sort_unstable_by(|a, b| (a.e0, a.e1, a.ingest).cmp(&(b.e0, b.e1, b.ingest)));
            let mut out: Vec<Vec<Sv>> = empty_buckets();
            let mut i = 0;
            while i < v.len() {
                let e = v[i];
                let mut j = i + 1;
                while j < v.len() && v[j].e0 == e.e0 && v[j].e1 == e.e1 {
                    j += 1;
                }
                if e.typ != BAD {
                    let (pkey, name) = persons.resolve(e.uid);
                    out[(pkey >> 56) as usize].push(Sv { pkey, ts: e.ts, name, price: e.price, cat: e.cat, typ: e.typ });
                }
                i = j;
            }
            out
        })
        .collect();
    let sv_b = transpose(sv_parts);
    lap("events deduped");

    // ---------- sessions ----------
    let nacc = (ncamp + 1) * ndays;
    let work: Vec<(Vec<Vec<Sv>>, Vec<Vec<Ck>>)> = sv_b.into_iter().zip(ck_b).collect();
    let results: Vec<(Vec<URow>, Vec<[i64; 4]>)> = work
        .into_par_iter()
        .fold(
            || (Vec::new(), vec![[0i64; 4]; nacc]),
            |(mut urows, mut acc), (svs, cks)| {
                let mut ev = concat(svs);
                let mut ck = concat(cks);
                ev.sort_unstable_by_key(|s| (s.pkey, s.ts));
                ck.sort_unstable_by(|a, b| a.pkey.cmp(&b.pkey).then(a.ts.cmp(&b.ts)).then(a.cid.cmp(b.cid)));
                let mut cnt = vec![0u32; ncamp];
                let mut inlist = vec![false; ncamp];
                let mut active: Vec<u32> = vec![];
                let mut catsum = vec![0i64; ncat];
                let mut ci = 0;
                let mut i = 0;
                while i < ev.len() {
                    let pk = ev[i].pkey;
                    let mut pe = i;
                    while pe < ev.len() && ev[pe].pkey == pk {
                        pe += 1;
                    }
                    while ci < ck.len() && ck[ci].pkey < pk {
                        ci += 1;
                    }
                    let cs0 = ci;
                    while ci < ck.len() && ck[ci].pkey == pk {
                        ci += 1;
                    }
                    let cs = &ck[cs0..ci];
                    let name = ev[i].name;
                    let (mut lo, mut hi) = (0usize, 0usize);
                    let mut cur_day: i64 = -1;
                    let mut u = URow { name, day: 0, sessions: 0, events: 0, revenue: 0, top: None };
                    let mut k = i;
                    while k < pe {
                        let s = ev[k].ts;
                        let mut j = k + 1;
                        while j < pe && ev[j].ts - ev[j - 1].ts <= GAP {
                            j += 1;
                        }
                        let day = s.div_euclid(DAY) - base_day;
                        if day != cur_day {
                            if cur_day >= 0 {
                                u.top = top_of(&catsum);
                                urows.push(u);
                                catsum.iter_mut().for_each(|x| *x = 0);
                            }
                            u = URow { name, day: (base_day + day) as i32, sessions: 0, events: 0, revenue: 0, top: None };
                            cur_day = day;
                        }
                        let mut rev = 0i64;
                        let mut purch = false;
                        for e in &ev[k..j] {
                            if e.typ == 2 {
                                purch = true;
                                rev += e.price as i64;
                                catsum[e.cat as usize] += e.price as i64;
                            }
                        }
                        u.sessions += 1;
                        u.events += (j - k) as i64;
                        u.revenue += rev;
                        // clicks window [s - WEEK, s]
                        while hi < cs.len() && cs[hi].ts <= s {
                            let c = cs[hi].camp as usize;
                            cnt[c] += 1;
                            if !inlist[c] {
                                inlist[c] = true;
                                active.push(c as u32);
                            }
                            hi += 1;
                        }
                        while lo < hi && cs[lo].ts < s - WEEK {
                            cnt[cs[lo].camp as usize] -= 1;
                            lo += 1;
                        }
                        let d = day as usize;
                        let credit = if hi > lo {
                            let t = cs[hi - 1].ts;
                            let mut q = hi - 1;
                            while q > lo && cs[q - 1].ts == t {
                                q -= 1;
                            }
                            active.retain(|&c| {
                                let keep = cnt[c as usize] > 0;
                                if !keep {
                                    inlist[c as usize] = false;
                                }
                                keep
                            });
                            for &c in &active {
                                acc[c as usize * ndays + d][3] += 1;
                            }
                            cs[q].camp
                        } else {
                            organic
                        };
                        let a = &mut acc[credit as usize * ndays + d];
                        a[0] += 1;
                        a[1] += purch as i64;
                        a[2] += rev;
                        k = j;
                    }
                    if cur_day >= 0 {
                        u.top = top_of(&catsum);
                        urows.push(u);
                        catsum.iter_mut().for_each(|x| *x = 0);
                    }
                    for &c in &active {
                        cnt[c as usize] = 0;
                        inlist[c as usize] = false;
                    }
                    active.clear();
                    i = pe;
                }
                (urows, acc)
            },
        )
        .collect();
    lap("sessions built");

    // merge campaign accumulators
    let mut acc = vec![[0i64; 4]; nacc];
    let mut ugroups: Vec<Vec<URow>> = vec![];
    for (u, a) in results {
        for (x, y) in acc.iter_mut().zip(a.iter()) {
            for t in 0..4 {
                x[t] += y[t];
            }
        }
        ugroups.push(u);
    }

    // ---------- output ----------
    let ud = outdir.join("user_daily");
    let cd = outdir.join("campaign_daily");
    std::fs::create_dir_all(&ud).unwrap();
    std::fs::create_dir_all(&cd).unwrap();
    let catnames = Arc::new(catnames);
    let mut groups: Vec<Vec<URow>> = (0..ncpu.max(1)).map(|_| Vec::new()).collect();
    let mut sizes = vec![0usize; groups.len()];
    for u in ugroups {
        let g = (0..sizes.len()).min_by_key(|&g| sizes[g]).unwrap();
        sizes[g] += u.len();
        if groups[g].is_empty() {
            groups[g] = u;
        } else {
            groups[g].extend(u);
        }
    }
    groups.par_iter().enumerate().for_each(|(i, rows)| {
        if i == 0 || !rows.is_empty() {
            write_users(&ud.join(format!("part-{:05}.parquet", i)), rows, &catnames);
        }
    });
    let mut crows: Vec<(&[u8], &[u8], i32, [i64; 4])> = vec![];
    for c in 0..=ncamp {
        for d in 0..ndays {
            let a = acc[c * ndays + d];
            if a[0] > 0 || a[3] > 0 {
                let (id, ch): (&[u8], &[u8]) = if c == ncamp { (b"organic", b"organic") } else { camps[c] };
                crows.push((id, ch, (base_day + d as i64) as i32, a));
            }
        }
    }
    write_campaigns(&cd.join("part-00000.parquet"), &crows);
    lap("done");
}

#[inline]
fn top_of(catsum: &[i64]) -> Option<u8> {
    let mut best: Option<u8> = None;
    let mut bv = 0i64;
    for (i, &v) in catsum.iter().enumerate() {
        if v > bv {
            bv = v;
            best = Some(i as u8);
        }
    }
    best
}

fn s(b: &[u8]) -> std::borrow::Cow<'_, str> {
    String::from_utf8_lossy(b)
}

use arrow_array::{ArrayRef, Date32Array, Int64Array, RecordBatch, StringArray};
use arrow_schema::{DataType, Field, Schema};
use parquet::arrow::ArrowWriter;
use parquet::basic::Compression;
use parquet::file::properties::WriterProperties;

fn props() -> WriterProperties {
    WriterProperties::builder().set_compression(Compression::UNCOMPRESSED).build()
}

fn write_users(path: &Path, rows: &[URow], cats: &[&[u8]]) {
    let schema = Arc::new(Schema::new(vec![
        Field::new("user_id", DataType::Utf8, false),
        Field::new("day", DataType::Date32, false),
        Field::new("sessions", DataType::Int64, false),
        Field::new("events", DataType::Int64, false),
        Field::new("revenue_cents", DataType::Int64, false),
        Field::new("top_category", DataType::Utf8, true),
    ]));
    let cols: Vec<ArrayRef> = vec![
        Arc::new(StringArray::from_iter_values(rows.iter().map(|r| s(r.name)))),
        Arc::new(Date32Array::from_iter_values(rows.iter().map(|r| r.day))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.sessions))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.events))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.revenue))),
        Arc::new(StringArray::from_iter(rows.iter().map(|r| r.top.map(|t| s(cats[t as usize]))))),
    ];
    let batch = RecordBatch::try_new(schema.clone(), cols).unwrap();
    let f = File::create(path).unwrap();
    let mut w = ArrowWriter::try_new(f, schema, Some(props())).unwrap();
    w.write(&batch).unwrap();
    w.close().unwrap();
}

fn write_campaigns(path: &Path, rows: &[(&[u8], &[u8], i32, [i64; 4])]) {
    let schema = Arc::new(Schema::new(vec![
        Field::new("campaign_id", DataType::Utf8, false),
        Field::new("channel", DataType::Utf8, false),
        Field::new("day", DataType::Date32, false),
        Field::new("sessions", DataType::Int64, false),
        Field::new("purchasing_sessions", DataType::Int64, false),
        Field::new("revenue_cents", DataType::Int64, false),
        Field::new("assisted_sessions", DataType::Int64, false),
    ]));
    let cols: Vec<ArrayRef> = vec![
        Arc::new(StringArray::from_iter_values(rows.iter().map(|r| s(r.0)))),
        Arc::new(StringArray::from_iter_values(rows.iter().map(|r| s(r.1)))),
        Arc::new(Date32Array::from_iter_values(rows.iter().map(|r| r.2))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.3[0]))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.3[1]))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.3[2]))),
        Arc::new(Int64Array::from_iter_values(rows.iter().map(|r| r.3[3]))),
    ];
    let batch = RecordBatch::try_new(schema.clone(), cols).unwrap();
    let f = File::create(path).unwrap();
    let mut w = ArrowWriter::try_new(f, schema, Some(props())).unwrap();
    w.write(&batch).unwrap();
    w.close().unwrap();
}

#[inline]
fn lines(d: &[u8]) -> Lines<'_> {
    Lines { d }
}
