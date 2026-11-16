#!/usr/bin/env bash
# The vec!-literal lowering gap.
#
# `vec![a, b, c]` — the most idiomatic Vec construction in Rust — does not lower
# into typed TrustIr: its boxed-slice path projects a field of the UNION
# `core::mem::maybe_uninit::MaybeUninit`, and trust-ir has no union
# representation, so the whole bundle fails and the function gets no native
# evidence.
#
# The four `verifies` rows are what make that a LOWERING gap rather than a claim
# about Vec: `vec![x; n]`, `[..].to_vec()`, `Vec::from([..])` and `Vec::new()` +
# `push` all build the same kind of value and all verify. Without them, a1's red
# would only show that some Vec program fails.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
TC="${1:-$ROOT/build/aarch64-apple-darwin/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC" >&2; exit 2; }
D="$ROOT/tests/vec-literal-lowering"
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT
pass=0; diverged=0
for f in "$D"/*.rs; do
  n="$(basename "$f" .rs)"
  exp="$(sed -n 's|^//@ vec-lowering: *||p' "$f" | head -1)"
  [ -n "$exp" ] || continue
  o="$W/$n"; mkdir -p "$o"
  "$TC" --edition 2024 -Ztrust-verify=on --out-dir "$o" "$f" > "$W/$n.log" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then got=verifies; else got=refuses; fi
  if [ "$got" != "$exp" ]; then
    echo "DIVERGED $n: recorded=$exp measured=$got (rc=$rc)"
    sed -n '/^error/{p;q;}' "$W/$n.log" | cut -c1-130
    diverged=$((diverged+1)); continue
  fi
  why="$(sed -n 's|^//@ vec-lowering-why: *||p' "$f" | head -1)"
  if [ -n "$why" ] && ! grep -qF -- "$why" "$W/$n.log"; then
    echo "CHANGED $n: still refuses, but no longer on '$why'"
    echo "  read the new reason before re-recording — the gap may have moved, not closed"
    diverged=$((diverged+1)); continue
  fi
  pass=$((pass+1))
done
echo "vec-literal lowering: $pass as recorded, $diverged diverged"
[ "$diverged" -eq 0 ]
