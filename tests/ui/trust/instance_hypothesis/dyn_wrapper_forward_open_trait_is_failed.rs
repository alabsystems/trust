//~ NOTE "line_start":41,"col_start":4,"line_end":43,"col_end":5},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":44,"col_start":4,"line_end":46,"col_end":5},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":49,"col_start":0,"line_end":51,"col_end":1},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":53,"col_start":0,"line_end":56,"col_end":1},"outcome":"runtime_checked","solver":"trust-full-verifier
//~| NOTE "crate_name":"dyn_wrapper_forward_open_trait_is_failed","functions_analyzed":4,"functions_verified":0,"total_proved":0,"total_failed":3,
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), recipe baseline: the shape of clean-ck0's
//! `StagingEnv`/`MutualStagingEnv` (`base: &dyn validate::Env`, built in `pub fn
//! add_inductive(env: &mut dyn MutableEnv, ..)`) and ty `tla-backend`'s
//! `RunFixedFacts(&dyn SemanticAuthorityPreparationFacts)` (built in `pub fn
//! semantic_authority_preparation_decline`), reduced to one file. `Facts` and its
//! subtrait `Prep` are public, unsealed and have no blanket impl, so a downstream
//! crate chooses the trait object `decline` receives. The private wrapper `Fixed`
//! forwards every method to that object, so each forwarding method (`Fixed::a`,
//! `Fixed::b`) and the private `refusal` keep OD-1 item 14's `failed` row (line 1,
//! first three pins): a downstream panicking impl is a concrete witness. `decline`
//! builds `&Fixed(f)` itself, so its own call stays `runtime_checked` (fourth pin).
//! The crate summary (fifth pin) has exactly three failed rows. Siblings:
//! `dyn_wrapper_forward_sealed_each_trait_stays_runtime_checked.rs` (recipe C),
//! `dyn_wrapper_forward_*_known_gap.rs` and
//! `dyn_wrapper_forward_panic_free_open_trait_is_error.rs`.

pub trait Facts {
    fn a(&self) -> bool;
    fn b(&self) -> bool;
}

pub trait Prep: Facts {
    fn c(&self) -> bool;
}

struct Fixed<'f>(&'f dyn Prep);

impl Facts for Fixed<'_> {
    fn a(&self) -> bool {
        self.0.a()
    }
    fn b(&self) -> bool {
        self.0.b() && !self.0.c()
    }
}

fn refusal(f: &dyn Facts) -> bool {
    f.a() || f.b()
}

pub fn decline(f: &dyn Prep) -> bool {
    let w = Fixed(f);
    refusal(&w)
}
