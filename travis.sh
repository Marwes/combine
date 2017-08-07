#!/bin/bash

cargo build &&
    cargo test &&
    cargo check --bench json &&
    cargo check --bench http &&
    cargo check --bench mp4 --features mp4