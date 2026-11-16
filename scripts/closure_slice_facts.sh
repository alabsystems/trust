#!/usr/bin/env bash
# The closure/slice-fact probes.
#
# Every row records the disposition it was MEASURED at. The point of the set is
# the SPLIT it makes visible: `windows(2)` + indexing fails in TWO different ways
# depending on whether the body is a closure or a loop, and the counterexamples
# say which:
#
#   c1 (closure)  w__slice_len = 1, then = 0   the postcondition never arrives
#   c7 (loop)     w__slice_len#s6_0 = 2        the fact IS present; it refutes anyway
#
# So "a closure is verified in isolation with its caller's guarantee dropped" is
# at most half the account — c7 has no closure at all. Five controls verify, and
# they are what make that a claim about INDEXING rather than about closures.
#
# HISTORICAL (2026-09-19): the two refusals above are the split as first
# recorded, and BOTH halves have since closed. Each fixture's own
# `//@ slice-facts:` line is the expectation this script checks, and both now
# read `verifies`:
#   c1  since 420d95eb26f (2026-09-25, D2 tier 1 `ADAPTER_YIELD`). Measured
#       2026-09-27 on pack 5ab8dcccfcb: exit 0, and the closure's 2 of 2 rows
#       proved under the disclosed ADAPTER_YIELD modeled fact.
#   c7  since 4006bc923fb (2026-09-20, the slice-stability gate asks about the
#       interval, not the whole function). Measured on the same pack: exit 0,
#       3 proved and 1 runtime-checked. It is not all-proved; see the fixture.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
TC="${1:-$ROOT/build/aarch64-apple-darwin/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC" >&2; exit 2; }
D="$ROOT/tests/closure-slice-facts"
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT
pass=0; diverged=0; split=0
for f in "$D"/*.rs; do
  n="$(basename "$f" .rs)"
  exp="$(sed -n 's|^//@ slice-facts: *||p' "$f" | head -1)"
  [ -n "$exp" ] || continue
  o="$W/$n"; mkdir -p "$o"
  "$TC" --edition 2021 -Ztrust-verify=on --crate-type=lib --out-dir "$o" "$f" > "$W/$n.log" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then got=verifies; else got=refuses; fi
  if [ "$got" != "$exp" ]; then
    echo "DIVERGED $n: recorded=$exp measured=$got (rc=$rc)"
    sed -n '/^error/{p;q;}' "$W/$n.log" | cut -c1-130
    diverged=$((diverged+1)); continue
  fi
  # For a refusing row, also show the witness the header names — a refusal that
  # stops carrying its counterexample shape is a different refusal.
  wit="$(sed -n 's|^//@ slice-facts-witness: *||p' "$f" | head -1)"
  if [ -n "$wit" ]; then
    if ! grep -qF -- "$wit" "$W/$n.log"; then
      echo "CHANGED $n: still refuses, but its counterexample no longer shows '$wit'"
      echo "  — a refusal that stops carrying its recorded witness is a DIFFERENT refusal;"
      echo "    read it before re-recording, the split this set exists for may have moved."
      diverged=$((diverged+1)); continue
    fi
  fi
  pass=$((pass+1))
  # Trust: 2026-09-21 — the PER-ROW VERDICT SPLIT.
  #
  # A refusing program that ALSO proves a bounds row for the same function is a
  # FALSE REFUTATION in the strict sense: the compiler holds a proof of the
  # check and reports the function as failing anyway. A refusing program with no
  # proved row is an honest inability. Those are different defects and they were
  # classified four times from proxies — symbol counts, obligation-record
  # presence, body shape — before anyone measured the quantity the distinction
  # is actually about. Measured 2026-09-21: g5/h1/h6 SPLIT, c1/c3 do not, n1 has
  # one row and refuses correctly.
  #
  # So the split is reported here, where the corpus is already being run, rather
  # than left to a separate wire dump nobody remembers to take. Diagnostic only:
  # it changes no verdict and no row's pass/fail.
  if [ "$got" = refuses ]; then
    "$TC" --edition 2021 -Ztrust-verify=on -Ztrust-verify-output=json \
      --crate-type=lib --out-dir "$o" "$f" > "$W/$n.wire" 2>&1 || true
    # Count proved rows of kind `slice` ONLY, pairing the two fields per row.
    # A bare grep for `"outcome":"proved"` over-reports: `n1` is a TRUE
    # refutation whose proved row is its OVERFLOW obligation, and it was
    # flagged as a split on the first run of this check.
    proved="$(python3 - "$W/$n.wire" <<'PYEOF'
import io, json, sys
text = io.open(sys.argv[1], encoding="utf-8", errors="replace").read()
decoder, at, rows = json.JSONDecoder(), 0, []
while at < len(text):
    while at < len(text) and text[at] not in "{[":
        at += 1
    if at >= len(text):
        break
    try:
        value, end = decoder.raw_decode(text, at)
    except Exception:
        at += 1
        continue
    at = end
    def walk(node):
        if isinstance(node, dict):
            if "kind" in node and "outcome" in node:
                yield node
            for child in node.values():
                yield from walk(child)
        elif isinstance(node, list):
            for child in node:
                yield from walk(child)
    rows.extend(walk(value))
print(sum(1 for r in rows if r.get("kind") == "slice" and r.get("outcome") == "proved"))
PYEOF
)"
    if [ "${proved:-0}" -gt 0 ]; then
      echo "  SPLIT $n: refuses, and $proved slice row(s) PROVED in the same function"
      split=$((split+1))
    fi
  fi
done
echo "closure/slice facts: $pass as recorded, $diverged diverged, $split verdict-split"
[ "$diverged" -eq 0 ]
