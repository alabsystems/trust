#!/usr/bin/env bash
# Corpus census driver — the REPRODUCIBLE way to measure the clean-kernel lane.
#
# Usage:
#   scripts/corpus_census.sh <census-binary> <fixtures-root> <out-dir> [per-dir-cap-secs]
#
# Build the binary first:
#   build/host/stage2/bin/targo --unverified build -p trust-clean --manifest-path Cargo.toml \
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
# Per-directory RESIDENT MEMORY ceiling (KiB) and worker count. Defaults chosen so
# that JOBS * MEMCAP stays well inside a developer machine: 6 * 3 GiB = 18 GiB worst
# case, against a measured steady-state of ~2.5 GB for the worst real body.
MEMCAP_KB="${CENSUS_MEMCAP_KB:-3145728}"
JOBS="${CENSUS_JOBS:-6}"

mkdir -p "$OUT"
: > "$OUT/rows.tsv"
: > "$OUT/gaps.txt"

# Every directory that DIRECTLY contains a .json dump (prove_dump_dir reads one
# directory non-recursively, and composition is per-directory).
find "$ROOT" -name '*.json' -print0 | xargs -0 -n1 dirname | sort -u > "$OUT/dirs.txt"

run_one() {
  d="$1"; bin="$2"; out="$3"; cap="$4"; memcap="$5"
  # The child runs in the BACKGROUND and is `wait`ed, not run in the foreground:
  # a caught signal is not delivered while a foreground external command runs
  # (measured 2026-08-20: 20s trap latency foreground vs 0s through `child & wait`).
  perl -e 'alarm shift; exec @ARGV' "$cap" \
        "$bin" --budget 0 --jobs 1 "$d" > "$out/tmp.$$.tsv" 2>"$out/tmp.$$.err" &
  child=$!
  # MEMORY BACKSTOP, the sibling of the wall-clock one above. A body that eats the
  # machine must cost exactly ONE directory — recorded as an explicit gap — the same
  # way a non-terminating body does. Without this the failure is not a lost
  # directory, it is a lost MACHINE: measured 2026-08-24, one real crates.io body
  # (`<unicode_bom::Bom as From<&[u8]>>::from`) held 19.3 GB resident under the
  # pre-fix prover, and -P 8 of those OOM-killed the session. It still plateaus
  # around 2.5 GB after the prover-side bounds, so 8 in parallel is ~20 GB and the
  # ceiling is not optional.
  ( while kill -0 "$child" 2>/dev/null; do
      rss=$(ps -o rss= -p "$child" 2>/dev/null | tr -d ' ')
      if [ -n "$rss" ] && [ "$rss" -gt "$memcap" ]; then
        echo "$d	rss_kb=$rss" >> "$out/memkills.txt"
        kill -9 "$child" 2>/dev/null
        break
      fi
      sleep 2
    done ) &
  watcher=$!
  if wait "$child"; then
    kill "$watcher" 2>/dev/null
    # Keep the binary's HEADER once, so the summary can index columns BY NAME.
    # Positional indices silently rot: `unsupported_obligations` was inserted mid-row
    # on 2026-08-24 and shifted every column after it, which made the summary print
    # `fully_faithful` from the `unsupported_obligations` slot and report a bogus
    # INVARIANT VIOLATED against correct data (caught 2026-08-25).
    if [ ! -s "$out/header.tsv" ]; then
      grep -m1 '^dir[[:space:]]' "$out/tmp.$$.tsv" > "$out/header.tsv" || true
    fi
    grep -v '^#' "$out/tmp.$$.tsv" | grep -v '^dir[[:space:]]' >> "$out/rows.tsv"
  else
    kill "$watcher" 2>/dev/null
    echo "$d" >> "$out/gaps.txt"
  fi
  wait "$watcher" 2>/dev/null
  rm -f "$out/tmp.$$.tsv" "$out/tmp.$$.err"
}
export -f run_one

xargs -I{} -P "$JOBS" bash -c 'run_one "$@"' _ {} "$BIN" "$OUT" "$CAP" "$MEMCAP_KB" < "$OUT/dirs.txt"

echo "measured_dirs $(wc -l < "$OUT/rows.tsv")"
if [ -s "$OUT/memkills.txt" ]; then
  echo "memory_killed_dirs $(wc -l < "$OUT/memkills.txt") (see $OUT/memkills.txt) — these are GAPS, not zeros"
fi
echo "gap_dirs      $(wc -l < "$OUT/gaps.txt")"
# COLUMNS BY NAME (see header.tsv above) — never by position.
awk -F'\t' -v hdr="$OUT/header.tsv" '
  BEGIN {
    if ((getline h < hdr) > 0) {
      nc = split(h, hn, "\t")
      for (c = 1; c <= nc; c++) { col[hn[c]] = c }
    }
    need = "total inhabited type_grounded_not_inhabited not_grounded kernel_rejected fully_faithful via_trustir mirsem_fallback safety_obligations safety_discharged unsupported_obligations unrefutable_by_construction"
    nn = split(need, want, " ")
    for (c = 1; c <= nn; c++) {
      if (!(want[c] in col)) {
        printf "\nCENSUS HEADER MISMATCH: no column named %s -- refusing to sum by position\n", want[c]
        bad = 1
      }
    }
  }
  !bad && NF >= nc {
    t   += $col["total"];          i  += $col["inhabited"]
    g   += $col["type_grounded_not_inhabited"]
    n   += $col["not_grounded"];   k  += $col["kernel_rejected"]
    ff  += $col["fully_faithful"]
    tir += $col["via_trustir"];    ms += $col["mirsem_fallback"]
    so  += $col["safety_obligations"];        sd += $col["safety_discharged"]
    uo  += $col["unsupported_obligations"];   ur += $col["unrefutable_by_construction"]
  }
  END {
    # The header check lives HERE, not in BEGIN: an exit inside BEGIN still runs
    # END, so a BEGIN-side exit printed a full summary of ZEROS instead of refusing
    # (measured 2026-08-25 by renaming a column and watching it report success).
    # NOTE: no apostrophes in this block -- it sits inside a single-quoted program.
    if (bad) { exit 3 }
    printf "\nfunctions                    %d\ninhabited                    %d\ntype_grounded_not_inhabited  %d\nnot_grounded                 %d\nKERNEL_REJECTED              %d  (MUST be 0)\n", t,i,g,n,k
    printf "\n--- SAFETY (what a user experiences as verification) ---\n"
    printf "safety_obligations           %d\nsafety_discharged            %d  (%.1f%% raw)\n", so, sd, (so?100*sd/so:0)
    printf "  unsupported (formula true) %d\n  UNREFUTABLE by construction %d  (disclosed superset; no refutation can exist)\n", uo, ur
    printf "  contentful denominator     %d  -> %.1f%% discharged\n", so-ur, ((so-ur)?100*sd/(so-ur):0)
    printf "\n--- R4 MIGRATION (trust-ir is the TARGET IR; MirSem is a compatibility lane) ---\n"
    printf "fully_faithful               %d\n  via_trustir                %d  (%.1f%%)\n  mirsem_fallback            %d  (teardown exit criterion: 0)\n", ff, tir, (ff?100*tir/ff:0), ms
    # KERNEL_REJECTED printed "(MUST be 0)" from the start and NOTHING tested it
    # (found 2026-08-26 wiring this script to its first gate row). A kernel
    # rejection is the census refuting its own artifact, so it has to be an exit,
    # not a caption. Checked before the fully_faithful identity: a rejected term
    # makes that tally meaningless anyway.
    if (k != 0) { printf "\nINVARIANT VIOLATED: KERNEL_REJECTED=%d, MUST be 0\n", k; exit 4 }
    if (ff != tir + ms) { printf "\nINVARIANT VIOLATED: fully_faithful != via_trustir + mirsem_fallback\n"; exit 2 }
  }' "$OUT/rows.tsv"
