//@ probe-shape: none
//@ probe-expect: island-only
//@ probe-note: THE LOAD-BEARING SOUNDNESS ARTIFACT for the `ite` select encoding.
//@ probe-note:
//@ probe-note: The mint now emits Clean's own `ite` term, so the discharge is a
//@ probe-note: TAUTOLOGY ABOUT `instLTUInt64`: both sides are the same term, Eq.refl
//@ probe-note: checks, and nothing is verified about what `<` MEANS. The old
//@ probe-note: `Nat.ble`-over-`toNat` encoding stated unsignedness out loud; this one
//@ probe-note: delegates it. These theorems are what keep that honest.
//@ probe-note:
//@ probe-note: Each is proved by `fun h => h` — the two sides are δβ-identical through
//@ probe-note: `UInt64.lt` -> `instLTBitVec` -> `Nat.lt` over `BitVec.toNat`. That is
//@ probe-note: exactly what FAILS for a signed carrier, whose `.lt` would not unfold to
//@ probe-note: a Nat order on `toNat`. So the theorem cannot be vacuously true: swap in
//@ probe-note: a signed instance and this file stops compiling.
//@ probe-note:
//@ probe-note: Witness it rules out: a = 2^63, b = 0. Unsigned, `a < b` is false and
//@ probe-note: Rust returns b. Signed, it is true and the island would denote a. Without
//@ probe-note: these theorems that divergence reports `Proved` with kernel-defeq
//@ probe-note: strength — a false accept.
clean {
    theorem u64_lt_agrees : forall (a : UInt64) (b : UInt64),
        Iff (LT.lt a b) (Nat.lt (UInt64.toNat a) (UInt64.toNat b)) :=
        fun a b => Iff.intro (fun h => h) (fun h => h)

    theorem u64_le_agrees : forall (a : UInt64) (b : UInt64),
        Iff (LE.le a b) (Nat.le (UInt64.toNat a) (UInt64.toNat b)) :=
        fun a b => Iff.intro (fun h => h) (fun h => h)

    theorem u32_lt_agrees : forall (a : UInt32) (b : UInt32),
        Iff (LT.lt a b) (Nat.lt (UInt32.toNat a) (UInt32.toNat b)) :=
        fun a b => Iff.intro (fun h => h) (fun h => h)

    theorem u16_lt_agrees : forall (a : UInt16) (b : UInt16),
        Iff (LT.lt a b) (Nat.lt (UInt16.toNat a) (UInt16.toNat b)) :=
        fun a b => Iff.intro (fun h => h) (fun h => h)

    theorem u8_lt_agrees : forall (a : UInt8) (b : UInt8),
        Iff (LT.lt a b) (Nat.lt (UInt8.toNat a) (UInt8.toNat b)) :=
        fun a b => Iff.intro (fun h => h) (fun h => h)
}

pub fn rust_side(x: u64) -> u64 {
    x
}
