#!/bin/bash -e

if grep -e CentOS </etc/os-release >/dev/null 2>&1; then
    COMPILER=rust-centos-x86_64.tar.gz
else
    COMPILER=rust-x86_64.tar.gz
fi

stdbuf -oL printf "Fetching sel4-aware Rust compiler..."
(
    rm -rf rust &&
        mkdir rust &&
        cd rust &&
        curl -O https://infinitenegativeutility.com/$COMPILER &&
        tar -xf $COMPILER
) >/dev/null 2>&1
echo " done."

stdbuf -oL printf "Fetching sel4 sysroot..."
(
    rm -rf sysroot &&
        mkdir sysroot &&
        cd sysroot &&
        curl -O https://infinitenegativeutility.com/x86_64-sel4-robigalia.tar.gz &&
        tar -xf x86_64-sel4-robigalia.tar.gz
) >/dev/null 2>&1
echo " done."

stdbuf -oL printf "Setting up tree-local Cargo configuration..."
mkdir -p .cargo
cat >.cargo/config <<EOF
[build]
target = "x86_64-sel4-robigalia"
rustflags = ["--sysroot", "sysroot"]
rustc = "rust/bin/rustc"
EOF
echo " done."
