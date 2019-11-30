#!/bin/bash -x
set -ex

if [[ ${TRAVIS_RUST_VERSION} = "1.33.0" ]]; then
    ALL_FEATURES="--features rust-1-33"
else
    ALL_FEATURES="--all-features"
fi

cargo build
cargo test $ALL_FEATURES
cargo test $ALL_FEATURES --examples

cargo test --bench json --bench http -- --test
cargo check --bench mp4 --features mp4

cargo build --no-default-features
cargo test --no-default-features --examples
