//@ compile-flags: -Z trust-verify=off
//@ check-pass
//! DEFECT 1 (measured 2026-09-13, sealed toolchain trustc 43f8b339f): Unicode
//! inside an inline island was refused by the RUST lexer — `error: unknown
//! start of token: \u{2264}` at the `≤` — before the island parser ran, and
//! the `E0425` that followed named the wrong thing. The island body is Clean
//! (Lean) text: `docs/TWO_LANGUAGE_100_PERCENT_GOAL.md` G2, "a Rust token
//! tree is not the lexical boundary of the Lean language". The lexer now
//! recognises an item-position island and scans its body as Clean bytes to
//! the matching `}` (`rustc_parse::lexer::trust_clean_island`), so the Rust
//! lexer never sees `≤ ≥ ≠ → ∀ λ ⟨ ⟩ ∧ ∨ ¬ ↔ ×` or a primed name — exactly
//! as it never saw the text of an out-of-line `clean mod name;` unit. Every
//! declaration is kernel-checked, and `min2` is callable from Rust.

mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        theorem le_self (n : Nat) : n ≤ n := Nat.le_refl n
        theorem ge_self (n : Nat) : n ≥ n := Nat.le_refl n
        theorem ne_zero : (1 : Nat) ≠ 0 := by decide
        theorem all_refl : ∀ n : Nat, n = n := fun n => rfl
        theorem imp_self' (p : Prop) : p → p := λ h => h
        theorem conj (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
        theorem or_left (p q : Prop) (hp : p) : p ∨ q := Or.inl hp
        theorem not_false' : ¬ False := fun h => h
        theorem iff_self' (p : Prop) : p ↔ p := ⟨fun h => h, fun h => h⟩
        def pair (a b : Nat) : Nat × Nat := (a, b)
        def id' (a : UInt64) : UInt64 := a
        theorem id'_eq (h' : 0 = 0) (a : UInt64) : id' a = a := rfl
    }
}

fn main() {
    let lo = m::min2(7, 41);
    assert!(lo == 7);
}
