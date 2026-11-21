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
const CHUNK: usize = 4 << 20;
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

/// Split a line into exactly N fields; false if malformed.
#[inline]
fn split_fields<'a, const N: usize>(line: &'a [u8], out: &mut [&'a [u8]; N]) -> bool {
    // One pass: find commas; a field containing a quote must be exactly "...".
    let mut n = 0;
    let mut start = 0;
    let mut quoted = false;
    let mut i = 0;
    let len = line.len();
    while i <= len {
        let c = if i < len { line[i] } else { b',' };
        if c == b',' {
            if n >= N {
                return false;
            }
            let f = &line[start..i];
            out[n] = if quoted {
                let m = f.len();
                if m < 2 || f[0] != b'"' || f[m - 1] != b'"' || f[1..m - 1].contains(&b'"') {
                    return false;
                }
                &f[1..m - 1]
            } else {
                f
            };
            n += 1;
            start = i + 1;
            quoted = false;
        } else if c == b'"' {
            quoted = true;
        }
        i += 1;
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
// Compact records: byte strings are stored as raw pointer + length into the input mmaps,
// which live for the whole run.
#[inline(always)]
fn bs(p: *const u8, n: u32) -> &'static [u8] {
    unsafe { std::slice::from_raw_parts(p, n as usize) }
}
/// 48 bytes. ts is ms since window_start, ing is ingest seconds (offset), pc = price | cat<<24, lt = uid len | typ<<24.
#[derive(Clone, Copy)]
struct Ev {
    e0: u64,
    e1: u64,
    uh: u64,
    up: *const u8,
    ts: u32,
    ing: u32,
    pc: u32,
    lt: u32,
}
unsafe impl Send for Ev {}
unsafe impl Sync for Ev {}
impl Ev {
    #[inline(always)]
    fn typ(&self) -> u8 {
        (self.lt >> 24) as u8
    }
    #[inline(always)]
    fn uid(&self) -> &'static [u8] {
        bs(self.up, self.lt & 0xFF_FFFF)
    }
}
/// 32 bytes.
#[derive(Clone, Copy)]
struct Sv {
    pkey: u64,
    ts: i64,
    np: *const u8,
    pc: u32,
    lt: u32,
}
unsafe impl Send for Sv {}
unsafe impl Sync for Sv {}
impl Sv {
    #[inline(always)]
    fn typ(&self) -> u8 {
        (self.lt >> 24) as u8
    }
    #[inline(always)]
    fn name(&self) -> &'static [u8] {
        bs(self.np, self.lt & 0xFF_FFFF)
    }
    #[inline(always)]
    fn price(&self) -> u32 {
        self.pc & 0xFF_FFFF
    }
    #[inline(always)]
    fn cat(&self) -> u8 {
        (self.pc >> 24) as u8
    }
}
/// 32 bytes.
#[derive(Clone, Copy)]
struct Ck {
    pkey: u64,
    ts: i64,
    cp: *const u8,
    cl: u32,
    camp: u32,
}
unsafe impl Send for Ck {}
unsafe impl Sync for Ck {}
impl Ck {
    #[inline(always)]
    fn cid(&self) -> &'static [u8] {
        bs(self.cp, self.cl)
    }
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
/// Flat open-addressing table: uid hash -> (person key, person name). One cache line per probe.
#[derive(Clone, Copy)]
struct Slot<'a> {
    key: u64,
    pkey: u64,
    name: &'a [u8],
}
struct Persons<'a> {
    mask: usize,
    slots: Vec<Slot<'a>>,
}
impl<'a> Persons<'a> {
    /// Build the table from link pairs: concurrent CAS insert (slot index = union-find node),
    /// sequential union-find on u32s, parallel min-name per component.
    fn from_links(pairs: &[Vec<(u64, u64, &'a [u8], &'a [u8])>], total: usize) -> Self {
        use std::sync::atomic::{AtomicU32, AtomicU64, Ordering::*};
        let cap = (total * 3).next_power_of_two().max(16);
        let mask = cap - 1;
        let keys: Vec<AtomicU64> = (0..cap).into_par_iter().map(|_| AtomicU64::new(0)).collect();
        let mut names: Vec<(usize, u32)> = vec![(0, 0); cap];
        let nptr = names.as_mut_ptr() as usize;
        let insert = |h: u64, nm: &[u8]| -> u32 {
            let mut i = (h as usize) & mask;
            loop {
                let cur = keys[i].load(Relaxed);
                if cur == h {
                    return i as u32;
                }
                if cur == 0 {
                    match keys[i].compare_exchange(0, h, AcqRel, Acquire) {
                        Ok(_) => {
                            // only the CAS winner writes this slot's name
                            unsafe { *(nptr as *mut (usize, u32)).add(i) = (nm.as_ptr() as usize, nm.len() as u32) };
                            return i as u32;
                        }
                        Err(x) if x == h => return i as u32,
                        Err(_) => {}
                    }
                }
                i = (i + 1) & mask;
            }
        };
        let idp: Vec<Vec<(u32, u32)>> = pairs
            .par_iter()
            .map(|v| v.iter().map(|&(ha, hb, a, b)| (insert(ha, a), insert(hb, b))).collect())
            .collect();
        let mut parent: Vec<u32> = (0..cap as u32).into_par_iter().collect();
        for v in &idp {
            for &(ia, ib) in v {
                let ra = find(&mut parent, ia);
                let rb = find(&mut parent, ib);
                if ra != rb {
                    parent[ra as usize] = rb;
                }
            }
        }
        drop(idp);
        // flatten to roots (sequential, cheap: trees are shallow after path halving)
        for i in 0..cap {
            if keys[i].load(Relaxed) != 0 {
                let r = find(&mut parent, i as u32);
                parent[i] = r;
            }
        }
        let name = |i: usize| -> &'a [u8] {
            let (p, n) = names[i];
            unsafe { std::slice::from_raw_parts(p as *const u8, n as usize) }
        };
        let best: Vec<AtomicU32> = (0..cap).into_par_iter().map(|_| AtomicU32::new(u32::MAX)).collect();
        (0..cap).into_par_iter().with_min_len(4096).for_each(|i| {
            if keys[i].load(Relaxed) == 0 {
                return;
            }
            let r = parent[i] as usize;
            let mut cur = best[r].load(Relaxed);
            loop {
                if cur != u32::MAX && name(cur as usize) <= name(i) {
                    break;
                }
                match best[r].compare_exchange_weak(cur, i as u32, AcqRel, Relaxed) {
                    Ok(_) => break,
                    Err(x) => cur = x,
                }
            }
        });
        let slots: Vec<Slot<'a>> = (0..cap)
            .into_par_iter()
            .with_min_len(4096)
            .map(|i| {
                let k = keys[i].load(Relaxed);
                if k == 0 {
                    return Slot { key: 0, pkey: 0, name: &[] };
                }
                let nm = name(best[parent[i] as usize].load(Relaxed) as usize);
                Slot { key: k, pkey: xxh3_64(nm), name: nm }
            })
            .collect();
        Persons { mask, slots }
    }
    #[inline(always)]
    fn prefetch(&self, h: u64) {
        let p = unsafe { self.slots.as_ptr().add((h.max(1) as usize) & self.mask) } as *const u8;
        prefetch(p);
    }
    #[inline(always)]
    fn get(&self, h: u64, uid: &'a [u8]) -> (u64, &'a [u8]) {
        let k = h.max(1);
        let mut i = (k as usize) & self.mask;
        loop {
            let s = unsafe { self.slots.get_unchecked(i) };
            if s.key == k {
                return (s.pkey, s.name);
            }
            if s.key == 0 {
                return (h, uid);
            }
            i = (i + 1) & self.mask;
        }
    }
}

#[inline(always)]
fn prefetch(p: *const u8) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        std::arch::x86_64::_mm_prefetch(p as *const i8, std::arch::x86_64::_MM_HINT_T0);
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        std::arch::asm!("prfm pldl1keep, [{0}]", in(reg) p, options(nostack, readonly, preserves_flags));
    }
}
const PF: usize = 16;

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
/// NB bucket vectors pre-sized for ~n records spread evenly (+25% and a little slack).
fn reserved_buckets<T>(n: usize) -> Vec<Vec<T>> {
    let c = n / NB + n / NB / 4 + 16;
    (0..NB).map(|_| Vec::with_capacity(c)).collect()
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
    let ncpu: usize = std::env::var("NCPU").ok().and_then(|x| x.parse().ok()).unwrap_or(8);
    rayon::ThreadPoolBuilder::new().num_threads(ncpu).build_global().unwrap();
    let reps: usize = std::env::var("REPEAT").ok().and_then(|x| x.parse().ok()).unwrap_or(1);
    for _ in 0..reps {
        run(ncpu);
    }
    std::process::exit(0);
}

fn run(ncpu: usize) {
    let t0 = Instant::now();
    let args: Vec<String> = std::env::args().collect();
    let data = PathBuf::from(std::env::var("DATA_DIR").unwrap_or_else(|_| {
        args.get(args.len().wrapping_sub(2)).cloned().unwrap_or("/data".into())
    }));
    let outdir = PathBuf::from(std::env::var("OUTPUT_DIR").unwrap_or("/output".into()));
    let use_radix = std::env::var("RADIX").map(|v| v != "0").unwrap_or(true);
    let lap = |s: &str| eprintln!("[{:>8.3}s] {}", t0.elapsed().as_secs_f64(), s);

    // manifest
    let man = String::from_utf8(read_small(&data.join("manifest.json"))).unwrap();
    let ws = parse_ts(json_str(&man, "window_start").as_bytes()).expect("window_start");
    let we = parse_ts(json_str(&man, "window_end").as_bytes()).expect("window_end");
    let base_day = ws.div_euclid(DAY);
    let ndays = ((we - 1).div_euclid(DAY) - base_day + 1) as usize;

    // products
    let prod_raw = read_small(&data.join("products.csv"));
    let prod_body = match memchr(b'\n', &prod_raw) {
        Some(p) => &prod_raw[p + 1..],
        None => &prod_raw[prod_raw.len()..],
    };
    let mut prows: Vec<(&[u8], u32)> = Vec::with_capacity(prod_body.len() / 12);
    let mut rawcat: Vec<&[u8]> = vec![];
    let mut catidx: HashMap<&[u8], u32> = HashMap::new();
    for_each_row::<2, _>(prod_body, |f| {
        let n = rawcat.len() as u32;
        let ci = *catidx.entry(f[1]).or_insert_with(|| {
            rawcat.push(f[1]);
            n
        });
        prows.push((f[0], ci));
    });
    let mut catnames: Vec<&[u8]> = rawcat.clone();
    catnames.push(b"unknown");
    catnames.sort();
    catnames.dedup();
    let remap: Vec<u32> = rawcat.iter().map(|c| catnames.binary_search(c).unwrap() as u32).collect();
    let unknown_cat = catnames.binary_search(&&b"unknown"[..]).unwrap() as u8;
    let ncat = catnames.len();
    assert!(ncat < 255);
    let mut products = Dict { map: IdMap::default() };
    products.map.reserve(prows.len());
    for &(p, ci) in &prows {
        products.map.entry(xxh3_64(p)).or_insert((p, remap[ci as usize]));
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

    let ing0 = ws.div_euclid(1000) - (1i64 << 31);
    let ev_maps = map_files(&list_csv(&data.join("events")));
    let ck_maps = map_files(&list_csv(&data.join("clicks")));
    let lk_maps = map_files(&list_csv(&data.join("links")));
    lap("setup");

    let build_links = || {
        // ---------- links (parallel) ----------
        let lk_chunks = chunks(&lk_maps);
        let pairs: Vec<Vec<(u64, u64, &[u8], &[u8])>> = lk_chunks
            .par_iter()
            .map(|ch| {
                let mut v = Vec::with_capacity(ch.len() / 20);
                for_each_row::<2, _>(ch, |f| {
                    if !f[0].is_empty() && !f[1].is_empty() {
                        v.push((xxh3_64(f[0]).max(1), xxh3_64(f[1]).max(1), f[0], f[1]));
                    }
                });
                v
            })
            .collect();
        let total: usize = pairs.iter().map(|v| v.len()).sum();
        Persons::from_links(&pairs, total)
    };
    let parse_events = || {
        // ---------- events: parse ----------
        let ev_chunks = chunks(&ev_maps);
        let ev_parts: Vec<Vec<Vec<Ev>>> = ev_chunks
            .par_iter()
            .map(|ch| {
                let mut acc: Vec<Vec<Ev>> = reserved_buckets(ch.len() / 64);
                let mut dc = DateCache::new();
                for_each_row::<7, _>(ch, |f| {
                    if f[0].is_empty() {
                        return;
                    }
                    let h = xxh3_128(f[0]);
                    let ingest = dc.parse(f[3]).unwrap_or(i64::MAX);
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
                            match dc.parse(f[2]) {
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
                    let ing = if ingest == i64::MAX {
                        u32::MAX
                    } else {
                        (ingest.div_euclid(1000) - ing0).clamp(0, u32::MAX as i64 - 1) as u32
                    };
                    let uid = f[1];
                    if uid.len() >= 1 << 24 {
                        typ = BAD;
                    }
                    acc[(h >> 120) as usize].push(Ev {
                        e0: (h >> 64) as u64,
                        e1: h as u64,
                        uh: if typ != BAD { xxh3_64(uid) } else { 0 },
                        up: uid.as_ptr(),
                        ts: if typ != BAD { (ts - ws) as u32 } else { 0 },
                        ing,
                        pc: price | ((cat as u32) << 24),
                        lt: (uid.len() as u32 & 0xFF_FFFF) | ((typ as u32) << 24),
                    });
                });
                acc
            })
            .collect();
            transpose(ev_parts)
    };
    let links_then_clicks = || {
        let persons = build_links();
            // ---------- clicks ----------
            let ck_chunks = chunks(&ck_maps);
            let cw0 = ws - WEEK;
            let ck_parts: Vec<Vec<Vec<Ck>>> = ck_chunks
                .par_iter()
                .map(|ch| {
                    let mut dc = DateCache::new();
                    let mut flat: Vec<(u64, Ck)> = Vec::with_capacity(ch.len() / 40);
                    for_each_row::<4, _>(ch, |f| {
                        if f[0].is_empty() || f[1].is_empty() {
                            return;
                        }
                        let ts = match dc.parse(f[3]) {
                            Some(t) if t >= cw0 && t < we => t,
                            _ => return,
                        };
                        let camp = match campaigns.get(f[2]) {
                            Some(c) => c,
                            None => return,
                        };
                        if f[0].len() >= 1 << 31 {
                            return;
                        }
                        flat.push((xxh3_64(f[1]), Ck { pkey: 0, ts, cp: f[0].as_ptr(), cl: f[0].len() as u32, camp }));
                    });
                    let mut acc: Vec<Vec<Ck>> = reserved_buckets(flat.len());
                    for i in 0..flat.len() {
                        if i + PF < flat.len() {
                            persons.prefetch(flat[i + PF].0);
                        }
                        let (h, mut c) = flat[i];
                        c.pkey = persons.get(h, &[]).0;
                        acc[(c.pkey >> 56) as usize].push(c);
                    }
                    acc
                })
                .collect();
            let ck_b = transpose(ck_parts);

        (persons, ck_b)
    };
    let ((persons, ck_b), ev_b) = rayon::join(links_then_clicks, parse_events);
    lap("parse_all");


    // ---------- events: dedup + resolve ----------
    let sv_parts: Vec<Vec<Vec<Sv>>> = ev_b
        .into_par_iter()
        .map(|vs| {
            // sort 16-byte keys (e0, location) instead of moving whole records
            let total: usize = vs.iter().map(|v| v.len()).sum();
            let mut keys: Vec<(u64, u64)> = Vec::with_capacity(total);
            for (pi, part) in vs.iter().enumerate() {
                for (ei, e) in part.iter().enumerate() {
                    keys.push((e.e0, ((pi as u64) << 32) | ei as u64));
                }
            }
            let low = |k: u64| k & ((1u64 << 33) - 1);
            if use_radix {
                radix33(&mut keys);
            } else {
                keys.sort_unstable_by_key(|k| low(k.0));
            }
            let at = |loc: u64| &vs[(loc >> 32) as usize][(loc & 0xffff_ffff) as usize];
            let mut out: Vec<Vec<Sv>> = empty_buckets();
            let mut surv: Vec<&Ev> = Vec::with_capacity(keys.len());
            macro_rules! emit {
                ($e:expr) => {{
                    let e: &Ev = $e;
                    if e.typ() != BAD {
                        surv.push(e);
                    }
                }};
            }
            let mut grp: Vec<&Ev> = vec![];
            let mut i = 0;
            while i < keys.len() {
                let mut j = i + 1;
                while j < keys.len() && low(keys[j].0) == low(keys[i].0) {
                    j += 1;
                }
                if j == i + 1 {
                    emit!(at(keys[i].1));
                } else {
                    grp.clear();
                    grp.extend(keys[i..j].iter().map(|k| at(k.1)));
                    grp.sort_unstable_by_key(|e| (e.e0, e.e1, e.ing));
                    let mut a = 0;
                    while a < grp.len() {
                        let mut b = a + 1;
                        while b < grp.len() && grp[b].e0 == grp[a].e0 && grp[b].e1 == grp[a].e1 {
                            b += 1;
                        }
                        emit!(grp[a]);
                        a = b;
                    }
                }
                i = j;
            }
            for i in 0..surv.len() {
                if i + PF < surv.len() {
                    persons.prefetch(surv[i + PF].uh);
                }
                let e = surv[i];
                let (pkey, name) = persons.get(e.uh, e.uid());
                out[(pkey >> 56) as usize].push(Sv {
                    pkey,
                    ts: ws + e.ts as i64,
                    np: name.as_ptr(),
                    pc: e.pc,
                    lt: (name.len() as u32 & 0xFF_FFFF) | (e.lt & 0xFF00_0000),
                });
            }
            out
        })
        .collect();
    let sv_b = transpose(sv_parts);
    lap("ev_dedup");

    // ---------- sessions ----------
    let nacc = (ncamp + 1) * ndays;
    let kbase = ws - WEEK;
    let kfits = we - kbase < (1i64 << 31); // else psort falls back to the comparator everywhere
    let work: Vec<(Vec<Vec<Sv>>, Vec<Vec<Ck>>)> = sv_b.into_iter().zip(ck_b).collect();
    // one campaign accumulator per worker thread; one task per bucket for load balance
    let nthr = rayon::current_num_threads() + 1;
    let accs: Vec<std::sync::Mutex<Vec<[i64; 4]>>> = (0..nthr).map(|_| std::sync::Mutex::new(Vec::new())).collect();
    let results: Vec<Vec<URow>> = work
        .into_par_iter()
        .map(
            |(svs, cks)| {
                let tid = rayon::current_thread_index().unwrap_or(nthr - 1);
                let mut guard = accs[tid].lock().unwrap();
                if guard.is_empty() {
                    *guard = vec![[0i64; 4]; nacc];
                }
                let acc: &mut Vec<[i64; 4]> = &mut guard;
                let mut urows: Vec<URow> = Vec::new();
                let ev = psort(svs, |s: &Sv| s.pkey, |a: &Sv, b: &Sv| {
                    (pord(a.pkey), a.ts).cmp(&(pord(b.pkey), b.ts))
                }, |s: &Sv| skey(s.pkey, s.ts, kbase), false, kfits);
                let ck = psort(cks, |c: &Ck| c.pkey, |a: &Ck, b: &Ck| {
                    (pord(a.pkey), a.ts).cmp(&(pord(b.pkey), b.ts)).then_with(|| a.cid().cmp(b.cid()))
                }, |c: &Ck| skey(c.pkey, c.ts, kbase), true, kfits);
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
                    while ci < ck.len() && pord(ck[ci].pkey) < pord(pk) {
                        ci += 1;
                    }
                    let cs0 = ci;
                    while ci < ck.len() && ck[ci].pkey == pk {
                        ci += 1;
                    }
                    let cs = &ck[cs0..ci];
                    let name = ev[i].name();
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
                            if e.typ() == 2 {
                                purch = true;
                                rev += e.price() as i64;
                                catsum[e.cat() as usize] += e.price() as i64;
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
                urows
            },
        )
        .collect();
    lap("sessions");

    // merge campaign accumulators
    let mut acc = vec![[0i64; 4]; nacc];
    for a in accs {
        let a = a.into_inner().unwrap();
        for (x, y) in acc.iter_mut().zip(a.iter()) {
            for t in 0..4 {
                x[t] += y[t];
            }
        }
    }
    let ugroups: Vec<Vec<URow>> = results;
    lap("merge");

    // ---------- output ----------
    let ud = outdir.join("user_daily");
    let cd = outdir.join("campaign_daily");
    std::fs::create_dir_all(&ud).unwrap();
    std::fs::create_dir_all(&cd).unwrap();
    let catnames = Arc::new(catnames);
    // group bucket outputs into ~ncpu files by reference (no copying of rows)
    let mut groups: Vec<Vec<&[URow]>> = (0..ncpu.max(1)).map(|_| Vec::new()).collect();
    let mut sizes = vec![0usize; groups.len()];
    for u in &ugroups {
        let g = (0..sizes.len()).min_by_key(|&g| sizes[g]).unwrap();
        sizes[g] += u.len();
        groups[g].push(u);
    }
    let write_all_users = || {
        groups.par_iter().enumerate().for_each(|(i, rows)| {
            if i == 0 || rows.iter().any(|r| !r.is_empty()) {
                write_users(&ud.join(format!("part-{:05}.parquet", i)), rows, &catnames);
            }
        })
    };
    let write_camps = || {
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
    };
    rayon::join(write_all_users, write_camps);
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

#[inline]
fn s(b: &[u8]) -> std::borrow::Cow<'_, str> {
    match std::str::from_utf8(b) {
        Ok(x) => std::borrow::Cow::Borrowed(x),
        Err(_) => String::from_utf8_lossy(b),
    }
}

use arrow_array::{ArrayRef, Date32Array, Int64Array, RecordBatch, StringArray};
use arrow_schema::{DataType, Field, Schema};
use parquet::arrow::ArrowWriter;
use parquet::basic::Compression;
use parquet::file::properties::WriterProperties;

fn props() -> WriterProperties {
    WriterProperties::builder()
        .set_compression(Compression::UNCOMPRESSED)
        .set_dictionary_enabled(false)
        .set_statistics_enabled(parquet::file::properties::EnabledStatistics::None)
        .build()
}

fn write_users(path: &Path, parts: &[&[URow]], cats: &[&[u8]]) {
    use arrow_array::builder::StringBuilder;
    let n: usize = parts.iter().map(|p| p.len()).sum();
    let rows = || parts.iter().flat_map(|p| p.iter());
    let nbytes: usize = rows().map(|r| r.name.len()).sum();
    let mut names = StringBuilder::with_capacity(n, nbytes);
    let mut tops = StringBuilder::with_capacity(n, n * 8);
    for r in rows() {
        names.append_value(s(r.name));
        match r.top {
            Some(t) => tops.append_value(s(cats[t as usize])),
            None => tops.append_null(),
        }
    }
    let schema = Arc::new(Schema::new(vec![
        Field::new("user_id", DataType::Utf8, false),
        Field::new("day", DataType::Date32, false),
        Field::new("sessions", DataType::Int64, false),
        Field::new("events", DataType::Int64, false),
        Field::new("revenue_cents", DataType::Int64, false),
        Field::new("top_category", DataType::Utf8, true),
    ]));
    let cols: Vec<ArrayRef> = vec![
        Arc::new(names.finish()),
        Arc::new(Date32Array::from_iter_values(rows().map(|r| r.day))),
        Arc::new(Int64Array::from_iter_values(rows().map(|r| r.sessions))),
        Arc::new(Int64Array::from_iter_values(rows().map(|r| r.events))),
        Arc::new(Int64Array::from_iter_values(rows().map(|r| r.revenue))),
        Arc::new(tops.finish()),
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

/// LSD radix sort of (key, payload) pairs on the low 33 bits of key (3 passes of 11 bits).
/// Equal low-33 keys end up adjacent; callers compare full keys within such runs.
fn radix33(a: &mut Vec<(u64, u64)>) {
    radix_bits(a, 3)
}

/// LSD radix on the low 11*passes bits of key.
fn radix_bits(a: &mut Vec<(u64, u64)>, passes: usize) {
    const B: usize = 11;
    const R: usize = 1 << B;
    const M: u64 = (R - 1) as u64;
    let n = a.len();
    let mask = if passes * B >= 64 { u64::MAX } else { (1u64 << (passes * B)) - 1 };
    if n < 256 {
        a.sort_unstable_by_key(|k| k.0 & mask);
        return;
    }
    let mut h = vec![[0u32; R]; passes];
    for k in a.iter() {
        for (p, hp) in h.iter_mut().enumerate() {
            hp[((k.0 >> (p * B)) & M) as usize] += 1;
        }
    }
    for hp in h.iter_mut() {
        let mut sum = 0u32;
        for c in hp.iter_mut() {
            let t = *c;
            *c = sum;
            sum += t;
        }
    }
    let mut buf: Vec<(u64, u64)> = Vec::with_capacity(n);
    unsafe { buf.set_len(n) };
    let (mut src, mut dst) = (std::mem::take(a), buf);
    for (p, hp) in h.iter_mut().enumerate() {
        let sh = p * B;
        for k in src.iter() {
            let d = ((k.0 >> sh) & M) as usize;
            unsafe { *dst.get_unchecked_mut(hp[d] as usize) = *k };
            hp[d] += 1;
        }
        std::mem::swap(&mut src, &mut dst);
    }
    *a = src;
}

/// u128 sort key equivalent to (pord(pk), ts) when ts - base fits in 31 bits.
#[inline(always)]
fn skey(pk: u64, ts: i64, base: i64) -> u128 {
    (((pk & ((1u64 << 33) - 1)) as u128) << 95) | ((pk as u128) << 31) | ((ts - base) as u128 & 0x7FFF_FFFF)
}

/// Person order used by the session phase: low 33 bits first (radix key), full key to break ties.
#[inline]
fn pord(pk: u64) -> (u64, u64) {
    (pk & ((1u64 << 33) - 1), pk)
}

// ---------- SIMD structural scan ----------
/// Bitmasks of ',' '\n' '"' for a 64-byte block (bit i = byte i).
#[inline(always)]
fn block_masks(b: &[u8; 64]) -> (u64, u64, u64) {
    #[cfg(target_arch = "x86_64")]
    unsafe {
        use std::arch::x86_64::*;
        let c = _mm_set1_epi8(b',' as i8);
        let n = _mm_set1_epi8(b'\n' as i8);
        let q = _mm_set1_epi8(b'"' as i8);
        let (mut cm, mut nm, mut qm) = (0u64, 0u64, 0u64);
        for k in 0..4 {
            let v = _mm_loadu_si128(b.as_ptr().add(16 * k) as *const __m128i);
            cm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, c)) as u32 as u64 & 0xffff) << (16 * k);
            nm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, n)) as u32 as u64 & 0xffff) << (16 * k);
            qm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, q)) as u32 as u64 & 0xffff) << (16 * k);
        }
        (cm, nm, qm)
    }
    #[cfg(target_arch = "aarch64")]
    unsafe {
        use std::arch::aarch64::*;
        const BITS: [u8; 16] = [1, 2, 4, 8, 16, 32, 64, 128, 1, 2, 4, 8, 16, 32, 64, 128];
        let bits = vld1q_u8(BITS.as_ptr());
        #[inline(always)]
        unsafe fn m16(eq: uint8x16_t, bits: uint8x16_t) -> u64 {
            let t = vandq_u8(eq, bits);
            (vaddv_u8(vget_low_u8(t)) as u64) | ((vaddv_u8(vget_high_u8(t)) as u64) << 8)
        }
        let c = vdupq_n_u8(b',');
        let n = vdupq_n_u8(b'\n');
        let q = vdupq_n_u8(b'"');
        let (mut cm, mut nm, mut qm) = (0u64, 0u64, 0u64);
        for k in 0..4 {
            let v = vld1q_u8(b.as_ptr().add(16 * k));
            cm |= m16(vceqq_u8(v, c), bits) << (16 * k);
            nm |= m16(vceqq_u8(v, n), bits) << (16 * k);
            qm |= m16(vceqq_u8(v, q), bits) << (16 * k);
        }
        (cm, nm, qm)
    }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    {
        let (mut cm, mut nm, mut qm) = (0u64, 0u64, 0u64);
        for (i, &x) in b.iter().enumerate() {
            cm |= ((x == b',') as u64) << i;
            nm |= ((x == b'\n') as u64) << i;
            qm |= ((x == b'"') as u64) << i;
        }
        (cm, nm, qm)
    }
}

/// Slow path for one field: strip a whole-field quote pair; None if any other quote.
#[inline(never)]
fn unq(f: &[u8]) -> Option<&[u8]> {
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

/// Calls f for every well-formed line of exactly N fields (quotes stripped), per the CSV dialect.
/// Quote validity per field is a bitmask test over a 128-bit window of the last two blocks' quote bits.
#[inline(always)]
fn for_each_row<'a, const N: usize, F: FnMut(&[&'a [u8]; N])>(d: &'a [u8], mut f: F) {
    assert!(N <= 7);
    let len = d.len();
    let dp = d.as_ptr();
    let mut fields: [&'a [u8]; 8] = [&[]; 8];
    let mut nf = 0usize;
    let mut bad = false;
    let mut fs = 0usize;
    let mut base = 0usize;
    let mut qprev: u64 = 0;
    let mut tmp: [u8; 64];
    let sl = |a: usize, b: usize| -> &'a [u8] { unsafe { std::slice::from_raw_parts(dp.add(a), b - a) } };
    while base < len {
        let blk: &[u8; 64] = if base + 64 <= len {
            unsafe { &*(dp.add(base) as *const [u8; 64]) }
        } else {
            tmp = [0u8; 64];
            tmp[..len - base].copy_from_slice(&d[base..]);
            &tmp
        };
        let (cm, nm, qm) = block_masks(blk);
        let win: u128 = ((qm as u128) << 64) | qprev as u128;
        let mut s = cm | nm;
        while s != 0 {
            let i = s.trailing_zeros() as usize;
            let p = base + i;
            let l = p - fs;
            if fs + 64 >= base && l <= 64 {
                // branch-free: qd = field has quotes; ok = exactly a quote at each end (len >= 2)
                let off = fs + 64 - base;
                let m = if l == 64 { u64::MAX } else { (1u64 << l) - 1 };
                let qb = (win >> off) as u64 & m;
                let pat = 1u64 | (1u64 << (l.wrapping_sub(1) & 63));
                let qd = (qb != 0) as usize;
                let ok = (qb == pat) & (l >= 2);
                bad |= (qd != 0) & !ok;
                let st = fs + qd;
                let en = (p - qd).max(st);
                fields[nf.min(7)] = sl(st, en);
            } else {
                match unq(sl(fs, p)) {
                    Some(x) => fields[nf.min(7)] = x,
                    None => bad = true,
                }
            }
            nf += 1;
            if (nm >> i) & 1 != 0 {
                if !bad && nf == N {
                    f(unsafe { &*(fields.as_ptr() as *const [&'a [u8]; N]) });
                }
                nf = 0;
                bad = false;
            }
            fs = p + 1;
            s &= s - 1;
        }
        qprev = qm;
        base += 64;
    }
    if fs < len || nf > 0 {
        match unq(sl(fs, len)) {
            Some(x) => fields[nf.min(7)] = x,
            None => bad = true,
        }
        nf += 1;
        if !bad && nf == N {
            f(unsafe { &*(fields.as_ptr() as *const [&'a [u8]; N]) });
        }
    }
}

/// Per-thread cache of validated dates: "YYYY-MM-DD" -> day number (or invalid).
struct DateCache {
    keys: [u64; 256],
    days: [i64; 256],
}
impl DateCache {
    fn new() -> Self {
        DateCache { keys: [0; 256], days: [0; 256] }
    }
    #[inline(always)]
    fn day(&mut self, b: &[u8]) -> Option<i64> {
        // b.len() >= 19 and b[4] == b[7] == '-' are checked by the caller
        let a = u64::from_le_bytes(b[0..8].try_into().unwrap());
        let key = (a & 0x00FF_FF00_FFFF_FFFF) | ((b[8] as u64) << 32) | ((b[9] as u64) << 56);
        let i = (key.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 56) as usize;
        if self.keys[i] == key {
            let d = self.days[i];
            return if d == i64::MIN { None } else { Some(d) };
        }
        let r = (|| {
            let y = d2(b, 0)? * 100 + d2(b, 2)?;
            let m = d2(b, 5)?;
            let d = d2(b, 8)?;
            if !(1..=12).contains(&m) || d < 1 || d > dim(y, m) {
                return None;
            }
            Some(days_from_civil(y, m, d))
        })();
        self.keys[i] = key;
        self.days[i] = r.unwrap_or(i64::MIN);
        r
    }
    #[inline(always)]
    fn dt(&mut self, b: &[u8]) -> Option<i64> {
        if b[4] != b'-' || b[7] != b'-' || b[10] != b'T' || b[13] != b':' || b[16] != b':' {
            return None;
        }
        let hh = d2(b, 11)?;
        let mi = d2(b, 14)?;
        let s = d2(b, 17)?;
        if hh > 23 || mi > 59 || s > 59 {
            return None;
        }
        Some(self.day(b)? * DAY + (hh * 3600 + mi * 60 + s) * 1000)
    }
    /// Same semantics as parse_ts.
    #[inline(always)]
    fn parse(&mut self, b: &[u8]) -> Option<i64> {
        match b.len() {
            20 if b[19] == b'Z' => self.dt(b),
            25 if (b[19] == b'+' || b[19] == b'-') && b[22] == b':' => {
                let base = self.dt(b)?;
                let oh = d2(b, 20)?;
                let om = d2(b, 23)?;
                if oh > 23 || om > 59 {
                    return None;
                }
                let off = (oh * 60 + om) * 60_000;
                Some(if b[19] == b'+' { base - off } else { base + off })
            }
            1..=18 => {
                let mut v: i64 = 0;
                for &c in b {
                    let x = c.wrapping_sub(b'0');
                    if x >= 10 {
                        return None;
                    }
                    v = v * 10 + x as i64;
                }
                Some(v)
            }
            _ => parse_ts(b),
        }
    }
}

/// Concatenate parts while partitioning on bits 22..33 of the person key (consistent with `pord`),
/// then sort each small partition. One read + one write per record instead of concat + key radix + gather.
fn psort<T: Copy, P: Fn(&T) -> u64, C: Fn(&T, &T) -> std::cmp::Ordering, K: Fn(&T) -> u128>(
    parts: Vec<Vec<T>>,
    pk: P,
    cmp: C,
    key: K,
    ties: bool,
    use_key: bool,
) -> Vec<T> {
    // partition on the top `bits` bits of the low-33 person-key field (consistent with `pord`),
    // sized for ~8 records per partition
    let n: usize = parts.iter().map(|p| p.len()).sum();
    let bits = ((n / 8).max(1).ilog2()).min(12);
    let nsb: usize = 1 << bits;
    let shift = 33 - bits;
    let sb = |x: &T| ((pk(x) >> shift) as usize) & (nsb - 1);
    let mut off = vec![0usize; nsb + 1];
    for p in &parts {
        for x in p {
            off[sb(x) + 1] += 1;
        }
    }
    for i in 0..nsb {
        off[i + 1] += off[i];
    }
    let mut out: Vec<T> = Vec::with_capacity(n);
    let mut pos = off.clone();
    unsafe {
        let o = out.as_mut_ptr();
        for p in &parts {
            for x in p {
                let d = sb(x);
                *o.add(pos[d]) = *x;
                pos[d] += 1;
            }
        }
        out.set_len(n);
    }
    drop(parts);
    for i in 0..nsb {
        let r = &mut out[off[i]..off[i + 1]];
        if use_key && r.len() > 1 {
            // large partition (heavy users): sort by a precomputed u128 key, fix equal-key runs with cmp
            r.sort_unstable_by_key(|x| key(x));
            if ties {
                let mut a = 0;
                while a < r.len() {
                    let ka = key(&r[a]);
                    let mut b = a + 1;
                    while b < r.len() && key(&r[b]) == ka {
                        b += 1;
                    }
                    if b - a > 1 {
                        r[a..b].sort_unstable_by(&cmp);
                    }
                    a = b;
                }
            }
        } else if r.len() > 1 {
            r.sort_unstable_by(&cmp);
        }
    }
    out
}


