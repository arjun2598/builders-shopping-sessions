# Shopping Sessions: native Rust pipeline.
FROM rust:1.85-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo 'fn main(){}' > src/main.rs && cargo build --release && rm -rf src
COPY src ./src
RUN touch src/main.rs && cargo build --release

FROM debian:bookworm-slim
COPY --from=build /src/target/release/shopsess /usr/local/bin/shopsess
ENV MIMALLOC_PURGE_DELAY=-1 MIMALLOC_ARENA_EAGER_COMMIT=1
USER 1000:1000
CMD ["/usr/local/bin/shopsess"]
