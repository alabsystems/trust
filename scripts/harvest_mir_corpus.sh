#!/usr/bin/env bash
#
# Harvest a MIR-dump corpus from the local crates.io registry, for coverage measurement.
#
# ─────────────────────────────────────────────────────────────────────────────────────
# READ THIS BEFORE CHANGING THE FLAGS. Both of the following were learned by publishing a
# wrong number and then having to correct it.
#
#  1. `--crate-name` MUST CARRY THE VERSION. Both halves were learned the hard way.
#     Without `--crate-name` at all, every crate compiles as the crate `lib`, so
#     `lib::error::Error::fmt` names a different function in each of the 13 registry crates
#     that has one. Measured on the 2026-08-26 corpus (56,328 bodies): 11,088 of 39,249
#     def_paths occurred in MORE THAN ONE FILE, spanning 28,167 bodies — HALF THE CORPUS.
#     That unsoundness inflated a published compositional-reachability figure by 1.7x
#     (+216 vs the true +130).
#
#     BUT ADDING A BARE `--crate-name` FIXED NOTHING, measured: 990 distinct crate roots
#     and 11,021 ambiguous def_paths spanning 27,821 bodies — statistically unchanged. The
#     dominant cause was never the `lib` naming; it is that the registry holds MANY
#     VERSIONS of the same crate (`cc` x9, `syn` x7, `log`/`getrandom`/`bitflags` x5), and
#     stripping `-X.Y.Z` to get a crate name merges them all. Only 7% of the ambiguity was
#     std-rooted. Hence the version is part of the name: `hashbrown_0_15_2`.
#
#  2. `--unverified` DOES NOT WORK HERE, and the failure is silent.
#     The dump is produced by the batteries-on verification pass, so an unverified build
#     emits NOTHING. `-Ztrust-policy=advisory` is what keeps a body's failed obligations
#     from failing the compile while still running the pass.
#
# KNOWN LIMIT, and it bounds what the corpus can answer. Each crate is compiled ALONE with
# no `--extern`, so a callee living in a dependency crate is never dumped. Measured: 55% of
# the callees of call-returning bodies are absent from the corpus entirely. Do not read a
# low interprocedural-reachability number as a statement about the COMPILER until the
# harvest is dependency-closed.
#
# macOS has no `timeout(1)`; `perl -e 'alarm N; exec @ARGV'` is the portable equivalent
# and is used deliberately.
# ─────────────────────────────────────────────────────────────────────────────────────
#
# Usage:  scripts/harvest_mir_corpus.sh [OUT_DIR]
# Then:   TRUST_LANE_HISTOGRAM_DIR=<OUT_DIR> targo --unverified test -p trust-clean --lib <instrument>
set -uo pipefail

OUT=${1:-$HOME/trust-corpora/mir-named}
TRUSTC=${TRUSTC:-$(git -C "$(dirname "$0")/.." rev-parse --show-toplevel)/build/host/stage2/bin/trustc}
OBJS="$(dirname "$OUT")/.objs"
PER_CRATE_TIMEOUT=${PER_CRATE_TIMEOUT:-90}

if [ ! -x "$TRUSTC" ]; then
  echo "no trustc at $TRUSTC — build stage2 or set TRUSTC=" >&2
  exit 2
fi
mkdir -p "$OUT" "$OBJS"

n=0
ok=0
for d in $(ls -d ~/.cargo/registry/src/*/*/ 2>/dev/null | sort); do
  lib="$d/src/lib.rs"
  [ -f "$lib" ] || continue
  base=$(basename "$d")
  # KEEP the version and sanitize the whole thing to a valid crate identifier, so
  # `hashbrown-0.14.5` and `hashbrown-0.15.2` are DIFFERENT crates — which they are.
  name=$(printf '%s' "$base" | tr '.-+' '___')
  case "$name" in [0-9]*) name="c$name" ;; esac
  if TRUST_DUMP_MONO=1 perl -e "alarm $PER_CRATE_TIMEOUT; exec @ARGV" "$TRUSTC" \
      --crate-name "$name" --crate-type=lib --edition 2021 \
      -Ztrust-policy=advisory -Ztrust-dump="mir-only:$OUT" \
      --out-dir "$OBJS" "$lib" >/dev/null 2>&1; then
    ok=$((ok + 1))
  fi
  n=$((n + 1))
  if [ $((n % 50)) -eq 0 ]; then
    echo "$n crates ($ok clean), $(find "$OUT" -name '*.json' | wc -l | tr -d ' ') bodies"
  fi
done
echo "DONE $n crates ($ok clean), $(find "$OUT" -name '*.json' | wc -l | tr -d ' ') bodies -> $OUT"
