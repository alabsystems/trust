#![crate_type = "lib"]
// ENUM VARIANT PAYLOAD range fact — the regression guard for a kernel-certified
// FALSE PROOF on the commonest enum in the language.
//
// `Ty::Adt::fields` is the FLAT union view an enum carries for the
// `SetDiscriminant` lowering — `[("__tag", i64), ("__v1_0", u64)]` — so a
// variant-relative `Downcast(1).Field(0)` resolved through `project_ty` answered
// with flat slot 0, the synthetic `__tag: i64`. The range fact `type_ranges`
// then attached to the payload said a `u64` lies in `[i64::MIN, i64::MAX]`,
// which is not a missing bound but a wrong one: it EXCLUDES every value above
// `i64::MAX`, so it deletes the only counterexample and the obligation is
// discharged.
//
// This body panics — `Some(u64::MAX)` makes `x + 1` overflow — so the gate must
// see it REFUTED. Reporting it proved, or DECLINING it, is the defect back.
pub fn add_one(e: Option<u64>) -> u64 {
    match e {
        Some(x) => x + 1,
        None => 0,
    }
}
