#!/usr/bin/env bash
# Corpus census driver — the REPRODUCIBLE way to measure the clean-kernel lane.
#
# Usage:
#   scripts/corpus_census.sh <census-binary> <fixtures-root> <out-dir> [per-dir-cap-secs]
#
# Build the binary first:
#   RUSTC_BOOTSTRAP=1 cargo build -p trust-clean --manifest-path crates/Cargo.toml \
#     --bin corpus-census-2026-07-24
#
# Needs NO `trustc` and NO stage2 build: committed dumps are serialized
# `VerifiableFunction`s and the per-function proof is pure computation, so this is
# reproducible from a source checkout alone.
#
# WHY THIS SCRIPT EXISTS — do not "simplify" it into one invocation.
#
# `prove_dump_dir`'s budget path carries a PER-INVOCATION RESOURCE FUSE: once ONE
# function exceeds its budget, every LATER function in that directory is declined
# ("earlier timed-out proof worker may still be detached"). Rust cannot safely kill a
# timed-out compute thread, so the fuse is the right call there — but it means a
# budgeted single-process run UNDERSTATES the result savagely. Measured 2026-07-24:
# 1768 fuse-declines against 79 real timeouts. Fail-closed, so it can never inflate a
# proven count — but it would have looked like evidence.
#
# So: run each directory UNBUDGETED (`--budget 0` = inline, no worker, no fuse), and
# isolate each directory in its OWN PROCESS under a wall-clock backstop. A genuinely
# non-terminating body then costs exactly one directory, and that directory is recorded
# in `gaps.txt` as an explicit hole rather than silently counted as a zero.
#
# macOS has no timeout(1); the perl alarm backstop is the in-repo convention.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

set -uo pipefail
BIN="${1:?census binary}"; ROOT="${2:?fixtures root}"; OUT="${3:?out dir}"; CAP="${4:-240}"

mkdir -p "$OUT"
: > "$OUT/rows.tsv"
: > "$OUT/gaps.txt"

# Every directory that DIRECTLY contains a .json dump (prove_dump_dir reads one
# directory non-recursively, and composition is per-directory).
find "$ROOT" -name '*.json' -print0 | xargs -0 -n1 dirname | sort -u > "$OUT/dirs.txt"

run_one() {
  d="$1"; bin="$2"; out="$3"; cap="$4"
  if perl -e 'alarm shift; exec @ARGV' "$cap" \
        "$bin" --budget 0 --jobs 1 "$d" > "$out/tmp.$$.tsv" 2>"$out/tmp.$$.err"; then
    grep -v '^#' "$out/tmp.$$.tsv" | grep -v '^dir[[:space:]]' >> "$out/rows.tsv"
  else
    echo "$d" >> "$out/gaps.txt"
  fi
  rm -f "$out/tmp.$$.tsv" "$out/tmp.$$.err"
}
export -f run_one

xargs -I{} -P 8 bash -c 'run_one "$@"' _ {} "$BIN" "$OUT" "$CAP" < "$OUT/dirs.txt"

echo "measured_dirs $(wc -l < "$OUT/rows.tsv")"
echo "gap_dirs      $(wc -l < "$OUT/gaps.txt")"
awk -F'\t' 'NF>=12 {t+=$2; i+=$3; g+=$4; n+=$5; k+=$6; ff+=$10; tir+=$11; ms+=$12}
  END {
    printf "\nfunctions                    %d\ninhabited                    %d\ntype_grounded_not_inhabited  %d\nnot_grounded                 %d\nKERNEL_REJECTED              %d  (MUST be 0)\n", t,i,g,n,k
    printf "\n--- R4 MIGRATION (trust-ir is the TARGET IR; MirSem is a compatibility lane) ---\n"
    printf "fully_faithful               %d\n  via_trustir                %d  (%.1f%%)\n  mirsem_fallback            %d  (teardown exit criterion: 0)\n", ff, tir, (ff?100*tir/ff:0), ms
    if (ff != tir + ms) { printf "\nINVARIANT VIOLATED: fully_faithful != via_trustir + mirsem_fallback\n"; exit 2 }
  }' "$OUT/rows.tsv"
