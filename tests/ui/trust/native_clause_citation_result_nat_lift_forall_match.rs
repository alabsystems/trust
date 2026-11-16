//@ revisions: off on adv
//@ needs-trust-verify
//@[off] compile-flags: -Ztrust-verify=off
//@[on] compile-flags: -Ztrust-verify=on
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@[off] check-pass
//@[on] check-fail
//@[adv] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@[on] normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! d1 (2026-09-28): the ONE verified-lane class change the fix makes, pinned so
//! it is a reviewed act rather than a side effect (report §4.3, case 3).
//!
//! The E9 citation sweep's ∀-`result` fallback now elaborates a cited `ensures`
//! in the discharge rung's mode (`ProofLift`) instead of `Strict`. A LIFTED
//! clause whose ∀-`result` reading the cited theorem DOES prove therefore moves
//! from a hard "outside the exact statement fragment: unsupported term shape"
//! error to the advisory "has a Clean-kernel statement match" note — exactly the
//! note its UNLIFTED twin (`result == result by u16_self`) already gets in every
//! lane (MEASURED, report variant k).
//!
//! Why that is sound: the sweep is diagnostic-only and credits no row; a kernel
//! proof of `∀ result, P result` implies `P` for the real return value; and the
//! body here (a `match`) is not E6-importable, so no discharge lane credits the
//! postcondition either. Under the default STRICT policy the build therefore
//! still fails, on the unproved obligation itself (`on`: MEASURED before the fix
//! as these two errors plus the citation error). What changes is the ADVISORY
//! policy, where the citation error was the only error (MEASURED): `adv` flips
//! from fail to pass, with the Level-0 gap reported as the warning it already
//! was. The post-fix expectations in all three revisions are INFERRED from the
//! code, not measured.

clean {
    theorem toNat_self : forall (r : UInt16), Eq (UInt16.toNat r) (UInt16.toNat r) :=
        fun r => Eq.refl (UInt16.toNat r)
}

pub fn j_taut(x: u16) -> u16
//[on]~^ ERROR Trust Level 0 safety verification incomplete for `native_clause_citation_result_nat_lift_forall_match::j_taut`
//[on]~| ERROR Trust strict verification failed for `native_clause_citation_result_nat_lift_forall_match::j_taut`
//[adv]~^^^ WARN Trust Level 0 safety verification incomplete for `native_clause_citation_result_nat_lift_forall_match::j_taut`
    ensures (result as nat) == (result as nat) by toNat_self
    //~^ NOTE citation `toNat_self` has a Clean-kernel statement match with a clean certification audit
{
    match x {
        0 => 0,
        _ => x,
    }
}

fn main() {
    let _ = j_taut(3);
}
