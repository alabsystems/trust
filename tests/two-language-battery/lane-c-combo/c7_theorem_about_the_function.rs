//@ battery-lane: C-combo
//@ battery-expect: pass
//@ battery-flags: -Ztrust-verify=on -Copt-level=0
//! LANE C (THE COMBO) — the theorem is about the FUNCTION, not about a
//! restatement of its body.
//!
//! Read this beside `c1_cited_min2.rs`. Both prove the same postcondition about
//! the same Rust function. The difference is what the Lean theorem talks about.
//!
//! c1 states its theorem over a Lean RESTATEMENT of the body:
//!
//!     Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x)
//!
//! That works, and it is what shipped first — but the author had to write the
//! body twice, once in Rust and once in Lean, and get the second copy to match
//! the compiler's encoding of the first. When it did not match, the failure was
//! silent (an undischarged clause) and the fix required knowing which recursor
//! the mint emitted. The history of that trap is `f01`, `d06`, and `d11` in the
//! fragment probe corpus, and the encoding it depends on has already changed
//! once (`Bool.rec` over `Nat.ble` -> `ite`), which rewrote c1's island.
//!
//! This file states its theorem over `min2` ITSELF, through the E6 kernel import
//! the compiler minted from `min2`'s own MIR:
//!
//!     Nat.le (UInt64.toNat (trust_import_c7_theorem_about_the_function__min2 a b))
//!            (UInt64.toNat a)
//!
//! There is now exactly ONE definition of what `min2` means, and both languages
//! point at it. The theorem cannot drift from the body, because it does not
//! contain a copy of the body. Change the Rust and the theorem is automatically
//! about the new function — it either still proves the clause or stops
//! compiling, which is the whole point of "one program, two languages".
//!
//! Why this needs item 10 phase 2: the import does not exist until the whole
//! crate has been walked and its admissions minted, so an island naming it is
//! deferred, and a citation to a deferred theorem cannot be adjudicated during
//! the walk. The body's verdict is withheld and published after the mint. See
//! `docs/design/2026-07-26-program-2-remaining-three.md` §1 for why the
//! discharge had to move rather than the island.

clean {
    theorem min2_le_left_of_import :
        forall (a : UInt64) (b : UInt64),
            Nat.le (UInt64.toNat (trust_import_c7_theorem_about_the_function__min2 a b))
                   (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => Nat.le.refl (UInt64.toNat a))
}

/// Ordinary Rust, and its own postcondition is proved by the Lean theorem above
/// — which never mentions `if`, `<`, or any encoding of this body.
pub fn min2(a: u64, b: u64) -> u64
    ensures result <= a by min2_le_left_of_import
{
    if a < b { a } else { b }
}

fn main() {
    let (a, b) = (41u64, 7u64);
    let _picked = min2(a, b);
}
