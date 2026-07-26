#!/usr/bin/env bash
# Build the `ay` SMT solver and install it beside the stage2 `trustc`.
#
# WHY: the compiler's solver dispatch (`resolve_solver_path` in
# compiler/rustc_mir_transform/src/trust_verify.rs) probes for an `ay`
# executable in trustc's OWN bin directory — `sibling_solver`. If `ay` is not
# there, every source-safety obligation degrades to `unknown`/`runtime_checked`
# and `trustc` proves nothing useful. "Batteries on" therefore
# requires `ay` to be installed beside `trustc`. A plain `./x.py build` does NOT
# yet do this (and in fact wipes first-party/ay/target), so run this after each
# stage2 build until ay is a first-class bootstrap tool (install_bin, like
# targo).
#
# Usage:  scripts/install-ay-beside-trustc.sh [--host <triple>]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOST="${2:-$("$REPO_ROOT/build/"*/stage2/bin/trustc -vV 2>/dev/null | sed -n 's/^host: //p' | head -1)}"
HOST="${HOST:-aarch64-apple-darwin}"

BIN_DIR="$REPO_ROOT/build/$HOST/stage2/bin"
if [ ! -x "$BIN_DIR/trustc" ]; then
  echo "error: no stage2 trustc at $BIN_DIR/trustc — run ./x.py build --stage 2 first" >&2
  exit 1
fi

echo "Building ay (release, --features cli) ..."
( cd "$REPO_ROOT/first-party/ay" && cargo build --release --bin ay --features cli )

AY_BIN="$REPO_ROOT/first-party/ay/target/release/ay"
[ -x "$AY_BIN" ] || { echo "error: ay binary not produced at $AY_BIN" >&2; exit 1; }

cp "$AY_BIN" "$BIN_DIR/ay"
echo "Installed ay -> $BIN_DIR/ay"
echo
echo "Verify batteries-on:"
echo "  printf 'pub fn idx(a:[u8;8])->u8{a[3]}\\n' > /tmp/p.rs"
echo "  $BIN_DIR/trustc --crate-type lib /tmp/p.rs   # -> 1 proved"
