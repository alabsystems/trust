//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@ run-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! ONE PROGRAM, TWO LANGUAGES — the capstone: every landed E9 discharge mode
//! in a single EXECUTABLE. Rust functions with first-class ensures clauses,
//! proven by Clean island theorems (rfl-trivial through dependent case-split),
//! kernel-checked at compile time with zero solver proofs for the clauses,
//! compiled through real codegen (the island/monomorphize ICE fix) and run.
//! Modes: cited postcondition; result bound to the defining equation; a
//! program function used definitionally in a spec; multi-clause conjunction;
//! the min2 case-split flagship; arbitrary-body result-free discharge.
//! Pinned to -Copt-level=0: under -O the inliner copies `println!` formatting
//! internals into `main`, whose obligations are out of this fixture's scope —
//! release-mode DISCHARGE coverage lives in `e9_release_mode_discharge`.
// ONE PROGRAM, TWO LANGUAGES — every landed discharge mode in a single binary.
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
    theorem min2_le_left : forall (x : UInt64) (y : UInt64),
        Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt x y)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => y) (fun _ => x))) (UInt64.toNat x))
            (instDecidableUInt64Lt x y)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat x) (UInt64.toNat y)) h)
            (fun h => Nat.le.refl (UInt64.toNat x))
}

pub fn ident(x: u64) -> u64 { x }
pub fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

// slice 1: cited postcondition
pub fn s1(x: u64) -> u64 ensures x >= x by u64_ge_refl { x }
// slice 4: result bound to the defining equation
pub fn s4(x: u64) -> u64 ensures result >= x by u64_ge_refl { x }
// slice 2: program fn used definitionally in the spec
pub fn s2(x: u64) -> u64 ensures ident(x) >= ident(x) by u64_ge_refl { x }
// slice 3: multi-clause conjunction
pub fn s3(x: u64) -> u64 ensures x >= x by u64_ge_refl ensures x <= x by u64_ge_refl { x }
// case-split flagship: min2 proven by real proof engineering
pub fn s5(x: u64, y: u64) -> u64 ensures min2(x, y) <= x by min2_le_left { x }
// slice 6: arbitrary body, result-free clause
pub fn s6(x: u64) -> u64 ensures ident(x) >= ident(x) by u64_ge_refl {
    let a = x ^ 3; let b = a ^ 3; b
}

fn main() {
    let (a, b) = (41u64, 7u64);
    // Keep the capstone executable without importing `println!`'s opaque std
    // formatting machinery into this proof-surface fixture. The six calls are
    // still emitted and run; the test is about their exact cited contracts.
    let _outputs = (s1(a), s2(a), s3(a), s4(a), s5(a, b), s6(a));
}
