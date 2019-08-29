#!/bin/bash -x
set -ex

cargo build
cargo test --features doc
cargo test --features doc --examples

cargo test --bench json --bench http -- --test
cargo check --bench mp4 --features mp4

cargo build --no-default-features
cargo test --no-default-features --examples
