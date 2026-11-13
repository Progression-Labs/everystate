#!/bin/sh
# Builds the WebAssembly module and puts it next to the JS wrapper.
set -e
cd "$(dirname "$0")/.."
cargo build --release --target wasm32-unknown-unknown --lib
cp target/wasm32-unknown-unknown/release/everystate.wasm wasm/everystate.wasm
ls -l wasm/everystate.wasm
