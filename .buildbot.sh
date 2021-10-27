#! /bin/sh

set -e

export CARGO_HOME="`pwd`/.cargo"
export RUSTUP_HOME="`pwd`/.rustup"

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
sh rustup.sh -y --no-modify-path
export PATH=`pwd`/.cargo/bin/:$PATH

rustup toolchain install nightly
rustup component add --toolchain nightly rustfmt-preview || cargo +nightly install --force rustfmt-nightly
cargo +nightly fmt --all -- --check

rustup toolchain install stable
rustup default stable
cargo test
cargo test --release

root=`pwd`
cd $root/lrlex/examples/calc_manual_lex
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
cd $root/lrpar/examples/calc_actions
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
cd $root/lrpar/examples/calc_ast
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
cd $root/lrpar/examples/calc_parsetree
echo "2 + 3 * 4" | cargo run | grep "Result: 14"
cd $root

RUSTDOCFLAGS="-Dwarnings" cargo doc --no-deps

which cargo-deny | cargo install cargo-deny || true
if [ "X`which cargo-deny`" != "X"]; then
    cargo-deny check license
fi
