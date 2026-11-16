//! The AUTHENTICATED lane credits Lean: `targo trust check main.rs`, single-file
//! mode, on a program whose two contracts are discharged by the Clean kernel —
//! one UNCITED (`result == min_isl(a, b)`: definitional equality against an
//! island definition, wire solver `clean-kernel-defeq`) and one CITED
//! (`ensures result >= x by u64_ge_refl`: the island theorem re-checked against
//! the compiler-elaborated goal, wire solver `clean-kernel-citation`).
//!
//! What this row pins (wf1-probe-package finding a2, measured 2026-09-16 on two
//! toolchains): raw `trustc` called these rows "kernel-certified" and the JSON
//! wire called them `proved`, but they carried no `proof_evidence`, so the
//! publication boundary printed `4 obligation(s) passed the compiler, 0
//! published, 4 WITHHELD` and `Gate: INCONCLUSIVE [strict lane, exit 1]`. The
//! verified lane graded EVERY Lean-discharged contract UNKNOWN. The consumer was
//! right to withhold an evidence-free row and is unchanged; the compiler now
//! attaches the kernel-audited `clean_cic` artifact
//! (`trust_certify::clean_island::certify_ensures_discharge`), and this row is
//! green only when those rows PUBLISH.
//!
//! `r15` covers the same discharges through raw `trustc`; `r14` covers `targo
//! trust build` on a package that cites nothing. Neither reaches the seam this
//! row exists for. The close negative twin is `r28`.

clean {
    def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)
}

pub fn min2(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{
    if a < b { a } else { b }
}

pub fn keep(x: u64) -> u64
    ensures result >= x by u64_ge_refl
{
    x
}

fn main() {
    let m = min2(7, 41);
    let _k = keep(m);
}
