#!/usr/bin/env bash
# The idiomatic-Rust sample.
#
# WHY IT EXISTS. `tests/ordinary-rust-sweep/` contains no `vec![a, b, c]` and no
# `#[derive(Debug)]` — measured 2026-09-20, zero of its eighty programs — so two
# of the five rows in docs/DECISION_QUEUE.md are INVISIBLE to it. A corpus that
# cannot see an item is not evidence about that item.
#
# HOW IT WAS BUILT, and the property that matters. Written from a list of TASKS a
# developer would write (an error enum, a default list, a sort, a formatted
# message, a parse with a fallback, ...), NOT from the failure list — and measured
# only after all fourteen existed. It has not been tuned since. Adding programs
# because they fail would destroy exactly the property that makes the number mean
# anything; see the curated-probe hazard the sweep's README records.
#
# It pins NO per-file expectation, for the same reason the sweep does not: its job
# is to report what ordinary code does, not to lock in a verdict.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
TC="${1:-$ROOT/build/aarch64-apple-darwin/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC" >&2; exit 2; }
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT
mkdir -p "$W/out"
pass=0; fail=0
for f in "$ROOT"/tests/idiomatic-rust-sample/*.rs; do
  n="$(basename "$f" .rs)"
  out="$("$TC" -Ztrust-verify=on --crate-type=lib --edition 2021 --emit=metadata --out-dir "$W/out" "$f" 2>&1)"
  if [ $? -eq 0 ]; then
    pass=$((pass+1)); printf "  ok    %s\n" "$n"
  else
    fail=$((fail+1))
    why="$(printf '%s' "$out" | grep -oE 'NOT-VANILLA callee=`[^`]*`|union core::mem::maybe_uninit::MaybeUninit|\[[a-z_:]+\] (FAILED|UNKNOWN)|lowering did not complete' | head -1)"
    printf "  FAIL  %-34s %s\n" "$n" "$why"
  fi
done
echo "idiomatic sample: $pass / $((pass+fail)) verify"
echo "a failure here is a DAILY-DRIVER fact, not a bug report: read README.md for"
echo "which decision each one belongs to before treating any of them as work."
