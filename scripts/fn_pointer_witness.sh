#!/usr/bin/env bash
# The fn-pointer witness.
#
# RE-POINTED 2026-09-19, WHEN THE HOLE CLOSED. It used to pass while the hole was
# open and that pass was the finding; its header promised that whoever closed the
# hole would come back and invert it. This is that inversion.
#
# What it now asserts:
#   1. the consumer REFUSES under `-Ztrust-verify=on`. Before the fix it built
#      green and the binary panicked at runtime with exit 101, through a
#      verify-off dependency's `pub static F: fn() = boom;` — no unsafe, no
#      attribute, no exotic flag on the crate under test.
#   2. every genuinely-unresolved fn-pointer shape refuses, and the one shape
#      whose target is statically REIFIED still verifies — the boundary between
#      a green that is earned and a green that is an absence.
#   3. the near-neighbours (`&dyn Fn`, generic `F: Fn`, the tail-call form) and
#      the arithmetic control are unchanged, so the fix moved exactly the
#      fn-pointer call and nothing else.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
TC="${1:-$ROOT/build/aarch64-apple-darwin/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC" >&2; exit 2; }
D="$ROOT/tests/fn-pointer-witness"
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT
fail=0

"$TC" --edition 2021 -Ztrust-verify=off --crate-type=lib --out-dir "$W" "$D/dep/dep.rs" > "$W/dep.log" 2>&1 \
  || { echo "SETUP BROKEN: the verify-off dependency did not build"; sed -n '/^error/{p;q;}' "$W/dep.log"; exit 2; }

"$TC" --edition 2021 -Ztrust-verify=on --extern dep="$W/libdep.rlib" -L "$W" \
      --out-dir "$W" "$D/user.rs" > "$W/user.log" 2>&1
build_rc=$?
if [ "$build_rc" -ne 0 ] && grep -q 'user::call' "$W/user.log"; then
  echo "1. consumer REFUSES, naming \`user::call\`   (the hole is CLOSED)"
elif [ "$build_rc" -ne 0 ]; then
  echo "1. consumer refuses, but NOT on \`user::call\` — read the error, this may be"
  echo "   a different failure that merely looks like the fix working:"
  sed -n '/^error/{p;q;}' "$W/user.log" | cut -c1-140
  fail=1
else
  echo "1. REGRESSION: the consumer builds GREEN again — the hole is OPEN."
  "$W/user" > "$W/run.log" 2>&1
  echo "   and the binary exits $? (101 = it panics; this is a green build of a panicking program)"
  fail=1
fi

# 3. THE FRAGMENT. Every shape below is recorded at the disposition it was
# MEASURED at, and the two `refuses` neighbours plus the arithmetic control are
# what make the `verifies` rows facts rather than a dead instrument: the
# fn-pointer bodies emit NO verification report line at all, while the control
# emits "1 failed out of 1 obligation(s)" on the same compiler and flags.
for f in "$D"/fragment/*.rs; do
  n="$(basename "$f" .rs)"
  exp="$(sed -n 's|^//@ fn-ptr-witness: *||p' "$f" | head -1)"
  [ -n "$exp" ] || continue
  o="$W/frag-$n"; mkdir -p "$o"
  "$TC" --edition 2021 -Ztrust-verify=on --crate-type=lib --out-dir "$o" "$f" > "$W/$n.log" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then got=verifies; else got=refuses; fi
  if [ "$got" != "$exp" ]; then
    echo "3. DIVERGED $n: recorded=$exp measured=$got (rc=$rc)"
    sed -n '/^error/{p;q;}' "$W/$n.log" | cut -c1-130
    fail=1
  fi
  # THE ROW IS INVISIBLE IN HUMAN MODE. Each fn-pointer body carries exactly one
  # `native-verification-gap` row with `outcome: unknown` — the compiler RECORDS
  # that something went unmodelled and shows the user nothing. That row only
  # appears under `-Ztrust-verify-output=json`, which is why an earlier draft of
  # this script concluded "no obligation at all" from human stderr. Check the
  # JSON, and record per shape which outcomes the body carries.
  gap_exp="$(sed -n 's|^//@ fn-ptr-witness-gap: *||p' "$f" | head -1)"
  if [ -n "$gap_exp" ]; then
    oj="$W/json-$n"; mkdir -p "$oj"
    "$TC" --edition 2021 -Ztrust-verify=on -Ztrust-verify-output=json --crate-type=lib \
          --out-dir "$oj" "$f" > "$W/$n.json" 2>&1
    gaps=$(grep -c 'native-verification-gap' "$W/$n.json")
    outs=$(grep -o '"outcome":"[a-z_]*"' "$W/$n.json" | sort -u | sed 's/"outcome":"//;s/"//' | paste -sd, -)
    min_gaps=1
    case "$gap_exp" in
      unknown-only)             want="unknown"; min_gaps=1 ;;
      proved-plus-unknown)      want="proved,unknown"; min_gaps=1 ;;
      proved-unreach-no-gap)    want="proved"; min_gaps=0 ;;
      no-rows-at-all)              want=""; min_gaps=0 ;;
      proved-plus-unknown-no-gap)  want="proved,unknown"; min_gaps=0 ;;
      *)                   want="$gap_exp" ;;
    esac
    if [ "$gaps" -lt "${min_gaps:-1}" ] || [ "$outs" != "$want" ]; then
      echo "3. CHANGED $n: recorded gap=$gap_exp (outcomes '$want'); measured gaps=$gaps outcomes='$outs'"
      fail=1
    fi
  fi
done
[ "$fail" -eq 0 ] && echo "3. fragment as recorded: the 4 genuinely-unresolved shapes REFUSE; f5 (a statically reified pointer) still verifies, and that green is earned; the tail-call form, the dyn and generic neighbours and the arithmetic control are unchanged"

[ "$fail" -eq 0 ] && echo "fn-pointer witness: as recorded (the hole is CLOSED)" \
                 || echo "fn-pointer witness: DIVERGED"
exit "$fail"
