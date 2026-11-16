//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ run-pass
//@ dont-check-compiler-stderr
//! A tactic-proof theorem beside a Rust-callable `def` in ONE island, proved
//! and kernel-checked end to end.
//!
//! History (two fixes, both measured 2026-09-13): this fixture began life as a
//! check-fail. First (DEFECT 2, island lexer) a theorem whose tactic proof did
//! not elaborate made the island register NOTHING, silently — the only symptom
//! was the downstream `E0425`; the rejection is now reported at the mint seam
//! (`rustc_resolve::trust_clean_mint::decide`), pinned by
//! `clean_island_kernel_reject.rs`. Then (W2 r11) the tactic proof itself did
//! not elaborate — Clean's `unfold`/`split` had a de Bruijn bug and `omega`
//! had no kernel replay at the `UInt64` carrier. With both fixed on the pinned
//! clean branch, `by unfold min2; split <;> omega` PROVES: `min2` and
//! `min2_le_left` both register, `min2` is callable from Rust, and the emitted
//! binary computes `min2(7, 41) = 7`. The `Nat` twin is
//! `tests/two-language-programs/r20_island_tactic_theorem_nat`.

mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
        theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
          unfold min2
          split <;> omega
    }
}

fn main() {
    let lo = m::min2(7, 41);
    assert!(lo == 7, "min2(7, 41) selects the smaller value");
    assert!(m::min2(41, 7) == 7, "and in the other argument order");
}
