#!/bin/bash -x
set -ex

if [[ "$TRAVIS_RUST_VERSION" == "1.40.0" ]]; then
    cargo "$@" check
    cargo "$@" check --no-default-features
else
    cargo "$@" build
    cargo "$@" test --all-features
    cargo "$@" test --all-features --examples

    cargo "$@" test --bench json --bench http -- --test
    cargo "$@" check --bench mp4 --features mp4

    cargo "$@" build --no-default-features
    cargo "$@" test --no-default-features --examples
fi
