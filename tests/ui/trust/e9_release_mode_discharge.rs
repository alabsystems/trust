//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -O
//@ check-pass
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! RELEASE-MODE discharge: the same min2 case-split citation as
//! `e9_min2_case_split_discharge`, plus an S4 wrapping-call composition,
//! compiled under `-O`. The optimizer reshapes the select lowering, while
//! Trust's inliner gate preserves exact compiler-authenticated core
//! `wrapping_*` calls until the final verification pass. Both admissions and
//! discharges must survive release builds: a program must never verify in debug
//! and fail in release.

clean {
    def composed_isl (x : UInt64) : UInt64 := (x + 1) * 2

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

pub fn min2(a: u64, b: u64) -> u64 { if a < b { a } else { b } }

pub fn caller(x: u64, y: u64) -> u64 ensures min2(x, y) <= x by min2_le_left { x }

pub fn composed(x: u64) -> u64
    ensures result == composed_isl(x)
{
    x.wrapping_add(1).wrapping_mul(2)
}

fn main() {}
