//@ revisions: off on
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@ check-pass
//@ only-64bit
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! TG3 (COMPILE-TIME-FACTS-1, 2026-11-05) SUPERSEDES the history below: the
//! unverified-lane allowance it describes is gone. With verification off the
//! kernel-only lane E6-imports the cited functions' bodies, so the `off`
//! revision now judges every `result` clause exactly as `on` does — the
//! "NOT checked" note is never printed, and a false `result` citation is a hard
//! error in both revisions. The two revisions stay so that this parity is pinned.
//!
//! The everyday dev loop of a converted crate: `targo --unverified
//! build|test|run` passes `-Ztrust-verify=off`, and a crate that spells its
//! contracts in the grammar (`ensures result >= x by thm`) must BUILD there.
//!
//! It did not. With verification off there is no body walk, so no function body
//! is kernel-imported; the citation sweep's discharge attempt cannot bind
//! `result`, and its fallback reading ∀-closes it — `∀ x result, x <= result`,
//! which no honest theorem proves. That was reported as `error: citation …
//! failed the strict Clean statement/certification audit … TypeMismatch`: a
//! false accusation against a citation the verified lane ACCEPTS (measured on
//! two toolchains, probe-package `01-pkg-cite`). The only escape was the
//! `#[cfg_attr(trust_verify, trust::ensures(..))]` spelling plus a proc-macro
//! dependency.
//!
//! Now, in the unverified lane ONLY, a statement mismatch on an `ensures` whose
//! clause mentions `result` is answered with what can still be enforced without
//! the body — the cited declaration exists, is a theorem with a proof term, is
//! not `unsafe`/`partial`, and its whole closure passes the strict audit — and a
//! note that says, in so many words, that the clause was NOT checked. That lane
//! makes no proof claim by definition and already says so once per crate.
//!
//! The `on` revision is the SAME source and pins that nothing moved there: the
//! citation is kernel-discharged against the imported body, exactly as before.
//! The close negative twin is `native_clause_citation_result_unverified_false`.

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

// The measured repro, verbatim.
pub fn keep(x: u64) -> u64
    ensures result >= x by u64_ge_refl
    //~^ NOTE citation `u64_ge_refl` kernel-discharges this postcondition statement
{
    x
}

// The same on a `usize` function — the two defects this lane fixes meet here:
// the dominant integer type of a converted crate, in its everyday build.
pub fn keep_us(x: usize) -> usize
    ensures result >= x by u64_ge_refl
    //~^ NOTE citation `u64_ge_refl` kernel-discharges this postcondition statement
{
    x
}

// A `result`-FREE clause needs no body, so it is still JUDGED in both lanes.
pub fn refl(x: u64) -> u64
    ensures x >= x by u64_ge_refl
    //~^ NOTE citation `u64_ge_refl` kernel-discharges this postcondition statement
{
    x
}

fn main() {
    let _ = keep(1);
    let _ = keep_us(2);
    let _ = refl(3);
}
