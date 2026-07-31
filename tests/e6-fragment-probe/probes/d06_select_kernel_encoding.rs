//@ probe-shape: Select
//@ probe-expect: defeq-rejected
//@ probe-note: THE OLD ENCODING NO LONGER DISCHARGES — deliberate, 2026-07-26.
//@ probe-note:
//@ probe-note: This island is written in the compiler's former internal form,
//@ probe-note: `Bool.rec (motive := ..) b a (Bool.not (Nat.ble ..))`. It used to be the
//@ probe-note: ONLY spelling that worked, which is what made the second language
//@ probe-note: unwritable by hand. The mint now emits Clean's `ite` term instead, so
//@ probe-note: this spelling stops matching.
//@ probe-note:
//@ probe-note: That is a real capability loss for anyone who wrote islands against the
//@ probe-note: old form, and it is recorded here rather than left to be discovered:
//@ probe-note: the four §1 ui fixtures had to be ported for exactly this reason. The
//@ probe-note: replacement is `f01` — write `if a < b then a else b` and nothing else.
clean {
  def sel (a : UInt64) (b : UInt64) : UInt64 :=
    Bool.rec (motive := fun _ => UInt64) b a (Bool.not (Nat.ble (UInt64.toNat b) (UInt64.toNat a)))
}
pub fn min2(a: u64, b: u64) -> u64
    ensures result == sel(a, b)
{ if a < b { a } else { b } }
