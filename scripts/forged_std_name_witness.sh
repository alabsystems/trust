#!/usr/bin/env bash
# The forged-`std` crate-name witness.
#
# WHY IT EXISTS. `crate_is_authentic_std` — a predicate whose NAME asserts
# authenticity — used to end in `|| tcx.crate_name(krate).as_str() == "std"`.
# A verify-off dependency that merely CALLS ITSELF `std`, never resident in the
# sysroot, was therefore graded inside the foundational TCB. That is spelling as
# authority, the same defect closed at HOLE A where `depA::a::std::io::_print`
# was classified as std's own print backend by a `.contains()`.
#
# Found 2026-09-20 by two independent adversarial lenses attacking a PROPOSED
# drop-glue tolerance (W3), not by a failing test — which is exactly why it
# needs one now.
#
# WHAT IT ASSERTS: byte-identical source, built twice under different
# `--crate-name`s, must be treated IDENTICALLY. The instrument is
# `TRUST_MASK_TRACE`, which names a masked fail-closed source.
#
# NO LIVE FALSE PROOF was ever demonstrated through the spoof — both spellings
# refuse — so this guards a classification, not a known hole. A DIVERGENCE here
# means the name is load-bearing again.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
TC="${1:-$ROOT/build/aarch64-apple-darwin/stage1/bin/trustc}"
[ -x "$TC" ] || { echo "no trustc at $TC" >&2; exit 2; }
W="$(mktemp -d)"; trap 'rm -rf "$W"' EXIT

cat > "$W/dep.rs" <<'EOF'
#![no_std]
pub struct Bomb { pub x: u32 }
impl Drop for Bomb { fn drop(&mut self) { if self.x > 0 { panic!("boom"); } } }
EOF
cat > "$W/prog.rs" <<'EOF'
extern crate boom;
struct W { b: boom::Bomb }
fn main() { let _w = W { b: boom::Bomb { x: 1 } }; }
EOF
# POSITIVE CONTROL for the instrument itself: a LOCAL panicking Drop must fire.
cat > "$W/local.rs" <<'EOF'
struct Bomb(u32);
impl Drop for Bomb { fn drop(&mut self) { if self.0 > 0 { panic!("boom"); } } }
fn main() { let _b = Bomb(1); }
EOF
ctl=$(TRUST_MASK_TRACE=1 "$TC" --edition 2021 -Ztrust-verify=on --emit=metadata \
        --out-dir "$W" "$W/local.rs" 2>&1 | grep -c 'masked fail-closed source')
if [ "$ctl" -eq 0 ]; then
  echo "INSTRUMENT DEAD: TRUST_MASK_TRACE did not fire on a local panicking Drop."
  echo "  A zero below would then be a fact about the instrument, not the compiler."
  exit 1
fi

fail=0
declare -a fires
for name in notstd std; do
  # REBUILD the dep with THIS compiler each run: a stale rlib from an earlier
  # toolchain silently changes the answer (measured 2026-09-20 — it read as a
  # regression until the deps were rebuilt).
  "$TC" --edition 2021 --crate-name "$name" --crate-type=rlib -Cmetadata="m$name" \
        -Ztrust-verify=off "$W/dep.rs" -o "$W/lib$name.rlib" >/dev/null 2>&1
  out="$(TRUST_MASK_TRACE=1 "$TC" --edition 2021 -Ztrust-verify=on \
          --extern "boom=$W/lib$name.rlib" --emit=metadata --out-dir "$W" \
          "$W/prog.rs" 2>&1)"
  rc=$?
  n="$(printf '%s' "$out" | grep -c 'masked fail-closed source')"
  fires+=("$n")
  printf "  crate-name=%-7s rc=%s  masked-source-reports=%s\n" "$name" "$rc" "$n"
  if [ "$rc" -ne 1 ]; then
    echo "  DIVERGED: a dependency whose Drop panics must be refused, got rc=$rc"
    fail=1
  fi
done

if [ "${fires[0]}" != "${fires[1]}" ]; then
  echo "DIVERGED: the two spellings were treated DIFFERENTLY (${fires[0]} vs ${fires[1]})."
  # Single quotes: inside double quotes the backticks would RUN the predicate name.
  echo '  The crate NAME is load-bearing again — `crate_is_authentic_std` is deciding'
  echo "  authenticity on a string the judged crate chose."
  fail=1
fi
[ "$fail" -eq 0 ] && echo "forged-std witness: both spellings treated identically (${fires[0]} each)"
exit "$fail"
