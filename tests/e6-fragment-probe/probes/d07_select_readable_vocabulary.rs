//@ probe-shape: Select
//@ probe-expect: discharged
//@ probe-note: STOPGAP, NOT THE SHAPE TO TEACH. Same program as d06/f01, but the
//@ probe-note: comparison is named once as a Bool-valued helper. It discharges, but it
//@ probe-note: is still boilerplate the author should never have to write. RULED
//@ probe-note: 2026-07-25: the target is `if a < b then a else b` with nothing else.
//@ probe-note: WHEN THAT LANDS, DELETE THE HELPERS HERE. If this probe still needs
//@ probe-note: `u64_lt` afterwards, the work is not finished.
//@ probe-note: This does NOT close f01: `if a < b then a else b` still fails, because
//@ probe-note: Clean's `if` over a Prop goes through Decidable/ite, which is defeq to
//@ probe-note: nothing in the Bool.rec world. See
//@ probe-note: docs/design/2026-07-25-select-encoding-ergonomics.md.
clean {
    def u64_lt (a : UInt64) (b : UInt64) : Bool :=
        Bool.not (Nat.ble (UInt64.toNat b) (UInt64.toNat a))
    def min_isl (a : UInt64) (b : UInt64) : UInt64 := cond (u64_lt a b) a b
}
pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{ if a < b { a } else { b } }
