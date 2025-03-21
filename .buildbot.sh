#! /bin/sh

set -e

export CARGO_HOME="`pwd`/.cargo_install"
export RUSTUP_HOME="`pwd`/.rustup"
export WASMTIME_HOME="`pwd`/.wasmtime"
export RUSTFLAGS="--cfg grmtools_extra_checks"

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
sh rustup.sh --default-host x86_64-unknown-linux-gnu --default-toolchain stable -y --no-modify-path

export PATH=`pwd`/.cargo_install/bin/:$WASMTIME_HOME/bin:$PATH

# Install wasmtime once debian trixie is stablized
# we can likely just use rust-wasmtime.
touch .wasmtime_profile
if [ "X`which wasmtime`" = "X" ]; then
    PROFILE=".wasmtime_profile" bash -c 'curl https://wasmtime.dev/install.sh -sSf | bash'
fi
. ./.wasmtime_profile

rustup target add wasm32-unknown-unknown
rustup target add wasm32-wasip2
cargo install wasm-bindgen-cli

cargo fmt --all -- --check

rustup toolchain install stable
rustup default stable

cargo test
cargo test --release
cargo test --target wasm32-unknown-unknown
cargo test --target wasm32-wasip2

cargo test --lib cfgrammar --features serde
cargo test --lib lrpar --features serde

root=`pwd`
cd $root/lrlex/examples/calc_manual_lex
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
# Touching these files shouldn't invalidate the cache (via --cfg grmtools_extra_checks)
touch src/main.rs && CACHE_EXPECTED=y cargo build
cd $root/lrpar/examples/calc_actions
echo -n "2 + 3 * 4" | cargo run --package nimbleparse -- src/calc.l src/calc.y -
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
touch src/main.rs && CACHE_EXPECTED=y cargo build
cd $root/lrpar/examples/calc_ast
echo -n "2 + 3 * 4" | cargo run --package nimbleparse -- src/calc.l src/calc.y -
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
touch src/main.rs && CACHE_EXPECTED=y cargo build
cd $root/lrpar/examples/calc_parsetree
echo -n "2 + 3 * 4" | cargo run --package nimbleparse -- src/calc.l src/calc.y -
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
touch src/main.rs && CACHE_EXPECTED=y cargo build
cd $root/lrpar/examples/clone_param
echo -n "1+++" | cargo run --package nimbleparse -- src/param.l src/param.y -
cd $root/lrpar/examples/start_states
echo -n "/* /* commented out */ */ uncommented text /* */" | cargo run --package nimbleparse -- src/comment.l src/comment.y -
cd $root

RUSTDOCFLAGS="-Dwarnings" cargo doc --no-deps

which cargo-deny | cargo install cargo-deny || true
if [ "X`which cargo-deny`" != "X" ]; then
    cargo-deny check license
fi
