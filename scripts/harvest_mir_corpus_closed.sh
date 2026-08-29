#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────────────
# DEPENDENCY-CLOSED, MONOMORPHIZED MIR corpus harvest.
#
# WHY THIS EXISTS, and why the sibling `harvest_mir_corpus.sh` is not enough: that one
# compiles each registry crate ALONE, with no `--extern`, so a callee living in a
# dependency is never dumped. Its own header says so. Any interprocedural number read
# off it is a statement about the HARVEST, not the compiler.
#
# TWO FLAGS ARE LOAD-BEARING. Both have produced a published wrong conclusion:
#
#   1. Driving the dump through `cargo` (not a bare `trustc` per crate) is what makes
#      the corpus DEPENDENCY-CLOSED: every unit in the graph is compiled, so callees in
#      dependencies get bodies. Measured: without closure, 82.6% of single-call bodies
#      had an absent callee and the certification programme looked capped. With closure
#      AND mono, that falls to 39.5%.
#
#   2. `TRUST_DUMP_MONO=1` emits the monomorphic INSTANTIATIONS. Without it only the
#      GENERIC body is dumped, whose callees are unresolved trait projections
#      (`<S as Trait>::m`) that can never match any def_path — so the absent-callee
#      histogram fills with phantoms and a "long tail of std functions to model"
#      appears that does not exist. Measured on the same 5-crate graph: 42.6% of the
#      31,087 bodies are instantiations, i.e. the flag more than doubles the corpus.
#
#   `-Ztrust-policy=advisory` is the third: the dump requires batteries-on verification,
#   and STRICT policy dies inside third-party code before the dump completes.
#   `--unverified` does NOT work — it switches verification off, and with it the dump.
#
# Cost: ~37 min and ~4 GB for the 5-crate graph below (~150 units). Watch the disk;
# this repo has filled a volume three times.
#
# Usage:  scripts/harvest_mir_corpus_closed.sh [OUT_DIR] [PROJECT_DIR]
# Then:   TRUST_LANE_HISTOGRAM_DIR=<OUT_DIR> \
#           targo --unverified test -p trust-clean --lib <instrument> -- --nocapture
# ─────────────────────────────────────────────────────────────────────────────────────
set -uo pipefail

ROOT=$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)
OUT=${1:-$HOME/trust-corpora/mir-closed-mono}
PROJ=${2:-$OUT.project}
BIN=${TRUST_BIN_DIR:-$ROOT/build/aarch64-apple-darwin/stage1/bin}

for tool in trustc cargo; do
  [ -x "$BIN/$tool" ] || { echo "missing $BIN/$tool — build stage1 first" >&2; exit 2; }
done

mkdir -p "$OUT" "$PROJ/src"
if [ ! -f "$PROJ/Cargo.toml" ]; then
  # A deliberately ORDINARY dependency set: parsing, iteration, text and data handling.
  # Change it freely — the point is a real graph, not this particular one.
  cat > "$PROJ/Cargo.toml" <<'TOML'
[package]
name = "closedcorpus"
version = "0.1.0"
edition = "2021"

[dependencies]
itertools = "0.12"
regex-syntax = "0.8"
semver = "1"
url = "2"
csv = "1"
TOML
  echo "pub fn root() {}" > "$PROJ/src/lib.rs"
fi

echo "harvesting into $OUT (project $PROJ)"
cd "$PROJ" || exit 2
TRUST_DUMP_MONO=1 \
RUSTC="$BIN/trustc" \
CARGO_TARGET_DIR="$PROJ/.target" \
RUSTFLAGS="-Ztrust-policy=advisory -Ztrust-dump=mir-only:$OUT" \
  "$BIN/cargo" build --offline
status=$?

echo "DONE ($status): $(find "$OUT" -name '*.json' | wc -l | tr -d ' ') bodies -> $OUT"
echo "  instantiations: $(find "$OUT" -name '*.json' -exec grep -l '::<' {} + 2>/dev/null | wc -l | tr -d ' ') (expect ~40%; near 0 means TRUST_DUMP_MONO did not take)"
