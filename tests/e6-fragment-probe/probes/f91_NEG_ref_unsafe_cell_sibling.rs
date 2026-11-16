//@ probe-shape: none
//@ probe-expect: clause-outside-fragment
//@ probe-note: NEGATIVE, must stay red. `f84` is an `UnsafeCell` as the WHOLE pointee; this
//@ probe-note: is the SIBLING form, which is what a real struct looks like, and it is a
//@ probe-note: separate row because K2 reaches the cell at a different depth (`raw`, not
//@ probe-note: the pointee itself) and because the scalar sibling `n` gives the view
//@ probe-note: something to want.
//@ probe-note: SINCE I2 `Freeze` IS THE ONLY NET HERE. Under I1 two things refused `Slot`:
//@ probe-note: C2 (`Ty::is_freeze`, with K2 behind it) and the all-or-nothing vocabulary
//@ probe-note: rule D-REF-8, since `UnsafeCell<u32>` is a `ty::Adt` outside the scalar
//@ probe-note: vocabulary. I2 skips unsupported fields, so the second net is gone BY
//@ probe-note: CONSTRUCTION — this cell sibling is skipped exactly like `f80`'s `Vec<u8>`
//@ probe-note: — and C2/K2 are all that stand between this program and a defining equation
//@ probe-note: over bytes another alias may legally mutate during the call. Neither is
//@ probe-note: kernel-checked; `docs/TCB.md`'s `EnsuresCitationViewDischarge` row says so.
//@ probe-note: THE MUTATION CONTROL THAT MEASURES IT WAS RUN, 2026-09-19, both directions
//@ probe-note: on a stage-1 build: with BOTH `is_freeze` and `trust_k2_no_inline_unsafe_cell`
//@ probe-note: stubbed out this probe goes `discharged` (so do `f71` and `f84`, while the
//@ probe-note: `Freeze` twin `f85` is unchanged), and restoring both guards returns it to
//@ probe-note: `clause-outside-fragment`. A bless that turns this row green is that
//@ probe-note: regression, not churn.
clean { def id32uc (x : UInt32) : UInt32 := x }
use std::cell::UnsafeCell;
pub struct Slot { pub n: u32, pub raw: UnsafeCell<u32> }
impl Slot {
    pub fn raw_of(&self) -> u32
        ensures result == id32uc(self.n)
    { self.n }
}
