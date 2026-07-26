//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: Select DOES discharge — but only when the island is written in the
//@ probe-note: kernel's internal encoding. Compare f01/f02/f03, which are the same
//@ probe-note: program written the way a human would and do NOT discharge.
clean {
  def sel (a : UInt64) (b : UInt64) : UInt64 :=
    Bool.rec (motive := fun _ => UInt64) b a (Bool.not (Nat.ble (UInt64.toNat b) (UInt64.toNat a)))
}
pub fn min2(a: u64, b: u64) -> u64
    ensures result == sel(a, b)
{ if a < b { a } else { b } }
