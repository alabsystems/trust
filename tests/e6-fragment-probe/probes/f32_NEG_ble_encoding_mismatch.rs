//@ probe-shape: ComparisonBool
//@ probe-expect: defeq-rejected
//@ probe-note: THE ENCODING CONTRACT, stated as a refusal. This is f26 with the island
//@ probe-note: rewritten to `Nat.ble` — the boolean spelling an author reaches for first,
//@ probe-note: and one that is TRUE of exactly the same pairs. It does not discharge: on
//@ probe-note: neutral arguments `Nat.ble x y` and `Decidable.decide (Nat.le x y)
//@ probe-note: (Nat.decLe x y)` are stuck at different head constants (`Nat.ble` versus
//@ probe-note: the `Bool.rec` dispatcher inside `Nat.decLe`). That is an IOTA mismatch —
//@ probe-note: no reducibility setting bridges it, exactly as with the select encoding
//@ probe-note: (docs/design/2026-07-25-select-encoding-ergonomics.md). Keeping this probe
//@ probe-note: red is what makes "the mint emits what Clean's elaborator emits" a
//@ probe-note: measured property rather than a claim: re-encode the mint over `Nat.ble`
//@ probe-note: and f26 goes red while this one goes green, so the diff says in one line
//@ probe-note: which encoding the compiler now speaks.
clean {
    def le_ble (a : BitVec 64) (b : BitVec 64) : Bool :=
        Nat.ble (Nat.xor (BitVec.toNat a) 9223372036854775808)
                (Nat.xor (BitVec.toNat b) 9223372036854775808)
}
pub fn le_i64_ble(a: i64, b: i64) -> bool
    ensures result == le_ble(a, b)
{ a <= b }
