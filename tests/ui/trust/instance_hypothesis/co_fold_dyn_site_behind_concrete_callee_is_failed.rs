//~ NOTE "line_start":40,"col_start":0,"line_end":45,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":47,"col_start":0,"line_end":50,"col_end":1},"outcome":"runtime_checked"
//~| NOTE "line_start":53,"col_start":0,"line_end":58,"col_end":1},"outcome":"runtime_checked"
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! rg concrete-misclassified (2026-10-05). Preview 2 (stage-1 `c797f90c1`) reported 11
//! clean-ck0 rows naming CONCRETE callees (`Term::unfold_apps`, `infer_in`,
//! `[T]::contains`) as "open, uncontracted generic trait dispatch", `failed` where
//! 10-03 published `runtime_checked`. Minimal shape, measured on that stage-1: no
//! concrete callee is classified as open dispatch. The row is the whole-function
//! panic-freedom FOLD, named after its first marked site (here the concrete
//! `Vec::<u32>::push`); it is decided per fold site (OD-1 phase 0, `52d352514b`), and
//! the co-folded `env.arity()` is a virtual call on a trait object the caller
//! supplies, an adversarial open dispatch since OD-1 item 14 (`04c39335f3`;
//! `dyn_open_trait_call_is_failed.rs`). A downstream `impl Env for W { fn arity(&self)
//! -> u32 { panic!() } }` passed in makes the body panic, so the row stays `failed`
//! (line 1, first pin). What changed is the reason text only: it named every deciding
//! site "generic"; it now says VIRTUAL (`dyn`) and that the named callee is only the
//! fold's representative (pinned by the unit test
//! `l0_refutation_names_a_virtual_co_folded_site_and_the_representative`).
//! Controls: the concrete callee alone (`concrete_only`, second pin) and the same
//! two calls through a trait object the body builds itself
//! (`concrete_then_self_built_dyn`, third pin) both stay `runtime_checked`.
pub trait Env {
    fn arity(&self) -> u32;
}

struct Local;
impl Env for Local {
    fn arity(&self) -> u32 {
        7
    }
}

pub fn concrete_then_dyn(env: &dyn Env, v: &mut Vec<u32>) -> u32 {
    // The fold's representative is this concrete call, not the refuted site.
    v.push(1);
    // The deciding site: a virtual call on an argument-supplied `&dyn Env`.
    env.arity()
}

pub fn concrete_only(v: &mut Vec<u32>) -> u32 {
    v.push(1);
    0
}

// Same two calls; the trait object is built here, so no caller chooses it.
pub fn concrete_then_self_built_dyn(v: &mut Vec<u32>) -> u32 {
    let l = Local;
    let env: &dyn Env = &l;
    v.push(1);
    env.arity()
}
