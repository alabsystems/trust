#!/usr/bin/env bash
# GOAL ITEM 4 — rustc-MIR CORRESPONDENCE: the EXECUTION-ORACLE side.
#
# Compiles the four differential-harness functions with the REAL Trust
# compiler (trustc) and runs them on the SAME concrete samples the Clean
# reflection-denotation harness reduces (crates/trust-clean/src/clean_ground.rs,
# the `differential_*` tests). Prints one line per sample:  fn args => result.
#
# This is the honest, runnable oracle: miri (a true MIR interpreter) is NOT
# built in this checkout (only `cargo check`-ed), so we use the COMPILED
# BINARY. miri would test MIR semantics; the compiled binary tests codegen —
# both are rustc's real behavior. We use the binary and say so.
#
# Agreement between THIS output and the Clean-denotation reduction over the
# same samples is the empirical model-vs-rustc correspondence for the fragment.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TRUSTC="${TRUSTC:-$REPO_ROOT/build/aarch64-apple-darwin/stage2/bin/trustc}"
export LIBRARY_PATH="${LIBRARY_PATH:-/opt/homebrew/lib}"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

cat > "$TMP/diff.rs" <<'RS'
fn add(a: i32, b: i32) -> i32  { a + b }
fn poly(a: i32, b: i32) -> i32 { a * b - a }
fn abs(x: i32) -> i32          { if x < 0 { -x } else { x } }
fn idiv(a: i32, b: i32) -> i32 { a / b }

fn main() {
    // add — must match differential_add_agrees_with_rustc_on_sample
    for &(a, b) in &[(3,4),(0,0),(-5,100),(2147483646,1),(-2147483648,0),(123456,-654321)] {
        println!("add {} {} => {}", a, b, add(a, b));
    }
    // poly — a*b - a
    for &(a, b) in &[(3,4),(0,999),(-2,-3),(7,0),(1000,1000)] {
        println!("poly {} {} => {}", a, b, poly(a, b));
    }
    // abs — the branch (i32::MIN excluded: overflow)
    for &x in &[0,5,-5,2147483647,-2147483647,-1,42] {
        println!("abs {} => {}", x, abs(x));
    }
    // idiv — trunc toward zero (i32::MIN/-1 excluded: overflow)
    for &(a, b) in &[(12,4),(-7,2),(7,-2),(-8,-2),(0,5),(100,7)] {
        println!("idiv {} {} => {}", a, b, idiv(a, b));
    }
}
RS

"$TRUSTC" -O "$TMP/diff.rs" -o "$TMP/diff" 2>/dev/null
"$TMP/diff"
