//~ NOTE "line_start":48,"col_start":24,"line_end":48,"col_end":53},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":52,"col_start":12,"line_end":52,"col_end":38},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":58,"col_start":20,"line_end":58,"col_end":41},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE "line_start":65,"col_start":12,"line_end":65,"col_end":28},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//~| NOTE [trust-instance-hypothesis] call to `<impl Fn(u32) -> bool as core::ops::function::Fn<(u32,)>>::call` in `dyn_closure_capture_of_pub_fn_param_is_failed::generic_twin::{closure#0}`: the panic-freedom of this open generic dispatch is assumed for every instantiation; the obligation moves to each instance","location":{"file":"$DIR/dyn_closure_capture_of_pub_fn_param_is_failed.rs","line_start":70,"col_start":28,"line_end":70,"col_end":53},"outcome":"skipped","solver":"trust-classifier
//~| NOTE "line_start":74,"col_start":21,"line_end":74,"col_end":34},"outcome":"failed","solver":"level0-refutation-fail-closed-over-runtime_checked
//@ revisions: advisory
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=both --crate-type=lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@[advisory] check-pass
//! CLOSURE-CAPTURE-ROOT (2026-10-11, docs/DECISION_QUEUE.md; an amendment of OD-1
//! item 14 / "L0 refutation rows" class (c)): a closure that calls a trait object it
//! CAPTURED FROM ITS PARENT's PARAMETER calls the caller's choice. Each parent below is
//! `pub`, so a downstream `|_| panic!()` (or `impl Env for W { .. panic!() }`) handed in
//! panics through the closure. Before the amendment the closure rows read
//! `runtime_checked` (`dyn_receiver_root::argument_root` rejected every field of a
//! closure's environment), while the `impl Fn` twin refuted, so `--allow-l0-gaps`
//! conditional-passed the `&dyn` spelling only (measured: a3d-wire
//! `sock::stale_instance_files`). Shapes: a by-reference capture (the a3d reduction), a
//! `move` capture, a closure nested in a closure, a precise capture of the field
//! `h.env` of a `&Holder` parameter, a PRIVATE parent whose one call site forwards a
//! `pub fn`'s own `&dyn Fn` (DYN-ARG-PROVENANCE-1: a forwarded trait object keeps the
//! refutation). The `impl Fn` twin (`generic_twin`) is NOT a `dyn` receiver: since
//! OD-1-T6-CALLABLE (`81c69e67b9`, landed in parallel with this fixture) a plain
//! closure's call on a captured type-parameter callable is the root's own open dispatch,
//! an `assumption:instance-hypothesis` row (advisory `assumed`, strict CONDITIONAL,
//! certify refuses) discharged at each concrete instance, exactly as
//! `closure_captured_callable_admitted.rs`'s `shared`/`paths_of`; its old class (c)
//! `failed` row is gone by that ruling, not by this one; that a panicking callable's
//! instance fails its discharge is pinned by `dyn_closure_capture_generic_twin_discharge.rs`
//! (here it would fall past compiletest's 512 KiB stderr capture). Controls:
//! `dyn_closure_capture_private_fn_local_values_stays_runtime_checked.rs`,
//! `dyn_receiver_built_locally_stays_runtime_checked.rs` (`closure_upvar`).
//! Line 1 pins each closure row by its location.
pub trait Env {
    fn arity(&self) -> u32;
}

pub struct Holder<'a> {
    pub env: &'a dyn Env,
}

pub fn by_ref(names: &[&str], pid_alive: &dyn Fn(u32) -> bool) -> usize {
    names.iter().filter(|n| pid_alive(n.len() as u32)).count()
}

pub fn by_move(pid_alive: &dyn Fn(u32) -> bool) -> bool {
    let c = move |x: u32| pid_alive(x);
    c(1)
}

pub fn nested(pid_alive: &dyn Fn(u32) -> bool) -> bool {
    let outer = |x: u32| {
        let inner = |y: u32| pid_alive(y);
        inner(x)
    };
    outer(2)
}

pub fn field(h: &Holder<'_>) -> u32 {
    let c = || h.env.arity();
    c()
}

pub fn generic_twin(names: &[&str], pid_alive: impl Fn(u32) -> bool) -> usize {
    names.iter().filter(|n| pid_alive(n.len() as u32)).count()
}

fn private_parent(xs: &[u32], keep: &dyn Fn(u32) -> bool) -> usize {
    xs.iter().filter(|x| keep(**x)).count()
}

pub fn forwards(xs: &[u32], keep: &dyn Fn(u32) -> bool) -> usize {
    private_parent(xs, keep)
}
