//~ NOTE "crate_name":"dyn_wrapper_forward_fact_snapshot_has_no_rows","functions_analyzed":5,"functions_verified":5,"total_proved":5,"total_failed":0,"total_unknown":0,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":0,
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ check-pass
//! DYN-WRAPPER-FORWARD-1 (2026-10-10), recipe (A), FACT SNAPSHOT: the
//! wrapper-forwarding shape of `dyn_wrapper_forward_open_trait_is_failed.rs` with the
//! accessor-only traits replaced by `Copy` structs the implementor fills in. No call
//! dispatches, so nothing is open to a downstream impl: every function proves and the
//! crate summary has no failed, unknown, skipped or runtime-checked row (line 1).
//! This is the recipe the ruling recommends for ty `tla-backend`, whose facts traits
//! are all `&self` accessors returning `bool`/`Option<bool>`/`u64`.

#[derive(Clone, Copy)]
pub struct Facts {
    pub a: bool,
    pub b: bool,
}

#[derive(Clone, Copy)]
pub struct Prep {
    pub facts: Facts,
    pub c: bool,
}

fn fixed(p: &Prep) -> Facts {
    Facts { a: p.facts.a, b: p.facts.b && !p.c }
}

fn refusal(f: &Facts) -> bool {
    f.a || f.b
}

pub fn decline(p: &Prep) -> bool {
    refusal(&fixed(p))
}
