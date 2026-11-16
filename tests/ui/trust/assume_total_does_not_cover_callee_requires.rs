//@ revisions: direct direct_strict direct_certify direct_advisory let_certify reify_certify
//@ revisions: map_certify param_certify dyn_certify closure_certify method_certify
//@ revisions: guarded_certify twin_certify twin_param_certify
//@ revisions: dep_direct dep_direct_certify dep_direct_memory_safe dep_direct_advisory
//@ revisions: dep_reify_certify dep_param_certify dep_guarded_certify dep_twin_certify
//@ revisions: sink_reify_certify sink_param_certify sink_unsize_certify sink_twin_certify
//@ revisions: value_promoted_certify value_const_certify value_const_val_certify
//@ revisions: value_static_certify value_static_dyn_certify value_dep_promoted_certify
//@ revisions: value_twin_certify
//@ revisions: value_assoc_const_certify value_assoc_fn_certify value_assoc_twin_certify
//@ revisions: value_assoc_dyn_certify value_assoc_drop_certify
//@ revisions: thread_local_certify closure_table_certify closure_value_mutant_certify
//@ revisions: phantom_certify phantom_mutant_certify
//@ revisions: recursive_type_certify recursive_type_control_certify
//@ revisions: recursive_type_no_impl_certify
//@ revisions: table_static table_static_certify table_static_advisory caller_promoted_certify
//@ revisions: method_const_certify method_static_certify method_promoted_certify
//@ revisions: method_rpitit_certify method_reify_certify method_twin_certify
//@ revisions: assoc_param_certify assoc_mk_certify assoc_caller_unsize_certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: assume_total_requires_dep.rs
//@ aux-build: assume_total_callable_sink.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[direct_strict] compile-flags: -Ztrust-policy=strict
//@[direct_certify] compile-flags: -Ztrust-policy=certify
//@[direct_advisory] compile-flags: -Ztrust-policy=advisory
//@[let_certify] compile-flags: -Ztrust-policy=certify
//@[reify_certify] compile-flags: -Ztrust-policy=certify
//@[map_certify] compile-flags: -Ztrust-policy=certify
//@[param_certify] compile-flags: -Ztrust-policy=certify
//@[dyn_certify] compile-flags: -Ztrust-policy=certify
//@[closure_certify] compile-flags: -Ztrust-policy=certify
//@[method_certify] compile-flags: -Ztrust-policy=certify
//@[guarded_certify] compile-flags: -Ztrust-policy=certify
//@[twin_certify] compile-flags: -Ztrust-policy=certify
//@[twin_param_certify] compile-flags: -Ztrust-policy=certify
//@[dep_direct_certify] compile-flags: -Ztrust-policy=certify
//@[dep_direct_memory_safe] compile-flags: -Ztrust-policy=memory-safe
//@[dep_direct_advisory] compile-flags: -Ztrust-policy=advisory
//@[dep_reify_certify] compile-flags: -Ztrust-policy=certify
//@[dep_param_certify] compile-flags: -Ztrust-policy=certify
//@[dep_guarded_certify] compile-flags: -Ztrust-policy=certify
//@[dep_twin_certify] compile-flags: -Ztrust-policy=certify
//@[sink_reify_certify] compile-flags: -Ztrust-policy=certify
//@[sink_param_certify] compile-flags: -Ztrust-policy=certify
//@[sink_unsize_certify] compile-flags: -Ztrust-policy=certify
//@[sink_twin_certify] compile-flags: -Ztrust-policy=certify
//@[value_promoted_certify] compile-flags: -Ztrust-policy=certify
//@[value_const_certify] compile-flags: -Ztrust-policy=certify
//@[value_const_val_certify] compile-flags: -Ztrust-policy=certify
//@[value_static_certify] compile-flags: -Ztrust-policy=certify
//@[value_static_dyn_certify] compile-flags: -Ztrust-policy=certify
//@[value_dep_promoted_certify] compile-flags: -Ztrust-policy=certify
//@[value_twin_certify] compile-flags: -Ztrust-policy=certify
//@[value_assoc_const_certify] compile-flags: -Ztrust-policy=certify
//@[value_assoc_fn_certify] compile-flags: -Ztrust-policy=certify
//@[value_assoc_twin_certify] compile-flags: -Ztrust-policy=certify
//@[value_assoc_dyn_certify] compile-flags: -Ztrust-policy=certify
//@[value_assoc_drop_certify] compile-flags: -Ztrust-policy=certify
//@[thread_local_certify] compile-flags: -Ztrust-policy=certify
//@[closure_table_certify] compile-flags: -Ztrust-policy=certify
//@[closure_value_mutant_certify] compile-flags: -Ztrust-policy=certify
//@[phantom_certify] compile-flags: -Ztrust-policy=certify
//@[phantom_mutant_certify] compile-flags: -Ztrust-policy=certify
//@[recursive_type_certify] compile-flags: -Ztrust-policy=certify
//@[recursive_type_control_certify] compile-flags: -Ztrust-policy=certify
//@[recursive_type_no_impl_certify] compile-flags: -Ztrust-policy=certify
//@[table_static_certify] compile-flags: -Ztrust-policy=certify
//@[table_static_advisory] compile-flags: -Ztrust-policy=advisory
//@[caller_promoted_certify] compile-flags: -Ztrust-policy=certify
//@[method_const_certify] compile-flags: -Ztrust-policy=certify
//@[method_static_certify] compile-flags: -Ztrust-policy=certify
//@[method_promoted_certify] compile-flags: -Ztrust-policy=certify
//@[method_rpitit_certify] compile-flags: -Ztrust-policy=certify
//@[method_reify_certify] compile-flags: -Ztrust-policy=certify
//@[method_twin_certify] compile-flags: -Ztrust-policy=certify
//@[assoc_param_certify] compile-flags: -Ztrust-policy=certify
//@[assoc_mk_certify] compile-flags: -Ztrust-policy=certify
//@[assoc_caller_unsize_certify] compile-flags: -Ztrust-policy=certify
//@[direct] check-fail
//@[direct_strict] check-fail
//@[direct_certify] check-fail
//@[direct_advisory] check-pass
//@[let_certify] check-fail
//@[reify_certify] check-fail
//@[map_certify] check-fail
//@[param_certify] check-fail
//@[dyn_certify] check-fail
//@[closure_certify] check-fail
//@[method_certify] check-fail
//@[guarded_certify] check-pass
//@[twin_certify] check-pass
//@[twin_param_certify] check-fail
//@[dep_direct] check-fail
//@[dep_direct_certify] check-fail
//@[dep_direct_memory_safe] check-fail
//@[dep_direct_advisory] check-pass
//@[dep_reify_certify] check-fail
//@[dep_param_certify] check-fail
//@[dep_guarded_certify] check-fail
//@[dep_twin_certify] check-fail
//@[sink_reify_certify] check-fail
//@[sink_param_certify] check-fail
//@[sink_unsize_certify] check-fail
//@[sink_twin_certify] check-fail
//@[value_promoted_certify] check-fail
//@[value_const_certify] check-fail
//@[value_const_val_certify] check-fail
//@[value_static_certify] check-fail
//@[value_static_dyn_certify] check-fail
//@[value_dep_promoted_certify] check-fail
//@[value_twin_certify] check-fail
//@[value_assoc_const_certify] check-fail
//@[value_assoc_fn_certify] check-fail
//@[value_assoc_twin_certify] check-fail
//@[value_assoc_dyn_certify] check-fail
//@[value_assoc_drop_certify] check-fail
//@[thread_local_certify] check-fail
//@[closure_table_certify] check-fail
//@[closure_value_mutant_certify] check-fail
//@[phantom_certify] check-pass
//@[phantom_mutant_certify] check-fail
//@[recursive_type_certify] check-fail
//@[recursive_type_control_certify] check-pass
//@[recursive_type_no_impl_certify] check-pass
//@[table_static] check-fail
//@[table_static_certify] check-fail
//@[table_static_advisory] check-pass
//@[caller_promoted_certify] check-fail
//@[method_const_certify] check-fail
//@[method_static_certify] check-fail
//@[method_promoted_certify] check-fail
//@[method_rpitit_certify] check-fail
//@[method_reify_certify] check-fail
//@[method_twin_certify] check-fail
//@[assoc_param_certify] check-fail
//@[assoc_mk_certify] check-fail
//@[assoc_caller_unsize_certify] check-fail
//@[twin_certify] forbid-output: does not cover the preconditions its calls owe
//@[dep_twin_certify] forbid-output: does not cover the preconditions its calls owe
//@[sink_twin_certify] forbid-output: does not cover the preconditions its calls owe
//@[value_twin_certify] forbid-output: does not cover the preconditions its calls owe
//@[value_assoc_twin_certify] forbid-output: does not cover the preconditions its calls owe
//@[thread_local_certify] forbid-output: does not cover the preconditions its calls owe
//@[closure_table_certify] forbid-output: does not cover the preconditions its calls owe
//@[phantom_certify] forbid-output: does not cover the preconditions its calls owe
//@[recursive_type_control_certify] forbid-output: does not cover the preconditions its calls owe
//@[recursive_type_no_impl_certify] forbid-output: does not cover the preconditions its calls owe
//@[twin_param_certify] forbid-output: carries a `requires`
//@[value_twin_certify] forbid-output: into a value that no call site charges
//@[value_assoc_twin_certify] forbid-output: into a value that no call site charges
//@[table_static_advisory] forbid-output: does not cover the preconditions its calls owe
//@[method_twin_certify] forbid-output: into a value that no call site charges
//@[method_twin_certify] forbid-output: does not cover the preconditions its calls owe
//@[closure_certify] forbid-output: ::p::{closure#0}`: function carries #[trust::assume_total]
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A body carrying `#[trust::assume_total]` may not leave a callee's `requires`
//! charged to nobody (docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-09-30 … —
//! `#[trust::assume_total]` charged none of its calls"). The attribute assumes the
//! body's TOTALITY (no panic, termination). A callee's `requires` is not totality:
//! the callee is verified UNDER it and the check proved under it is elided, so a
//! call outside the clause returns a wrong value instead of panicking.
//!
//! `add1(x) requires x < 100 { x + 1 }` is verified under its clause (the overflow
//! row kernel-certified, the check elided); `inc`/`add1_wrapping` are `requires`-free.
//! The `dep_*` revisions take `add1` from `auxiliary/assume_total_requires_dep.rs`,
//! built on the default policy; the `sink_*` and `value_*` revisions hand a callable
//! to `auxiliary/assume_total_callable_sink.rs`, built verify-off, whose items call
//! it — the `value_*` ones inside the non-generic `fn` field of its `H`, built in a
//! promoted, a `const` or a `static`, or behind a `static` `&dyn`.
//!
//! BEFORE (a stage 1 of `fbc6068e3`, measured 2026-09-30 by compiling each shape
//! as a `--crate-type lib` under each policy, and by emulating compiletest on this
//! file): every check-fail revision built exit 0 under the default policy, strict
//! and certify — and, for each `dep_*` shape, under memory-safe — printing only
//! `Trust: ASSUMPTION [assumed-total]` (two lines for `closure_certify`: `p` and its
//! closure). Linked into a verify-off `main`, the certify and default builds of
//! `direct`, `param`, `dyn`, `closure`, `dep_direct` and `dep_param` printed
//! `p(u32::MAX) = 0`, and `map` printed `Some(0)`; the `collect`/`collect_param`
//! shapes (local, fn-pointer parameter and cross-crate, each at `-Zinline-mir=yes`
//! and at `-Copt-level=3 -Zmir-opt-level=2`) and the `sink` reify, parameter and
//! unsize shapes returned `[0]` for `[u32::MAX]` in the same probe, and so did the
//! `value` promoted, `const` (by reference and by value), `static`, `static` `&dyn`
//! and cross-crate shapes (also an associated and an inline `const`), each at `-O0`,
//! `-Zinline-mir=yes` and `-Copt-level=3 -Zmir-opt-level=2`; the verify-off build of
//! each panics "attempt to add with overflow"
//! (`assume_total_callee_requires_really_overflows.rs` is that witness). `param`,
//! `dyn` and `collect_param` are the route where the `requires`-carrying item is
//! turned into a value in a VERIFIED body (`p` passes `add1` to `call`), which no
//! gate refuses: only the call site in `call` can, and the skip removed it. The
//! controls built exit 0 too.
//!
//! AFTER (predicted — no stage 1 with the fix was built for this commit): such a
//! body is verified exactly as if the attribute were absent, with a warning
//! (`uncharged_callable::assume_total_cannot_cover_calls`). The verdicts were
//! MEASURED on the same stage 1 through stand-ins: this file with an empty
//! `unsafe {}` added to each flagged body, which D8-P0 already verifies in full with
//! the attribute kept (so `p` still calls an `assume_total` `call`, and the closure's
//! `p` keeps its skip), passed the emulated compiletest in 35 of 37 revisions, with
//! the new rule's own notes (`this body holds …`) the one thing it cannot show —
//! those twelve were checked instead by compiling the rule's walk VERBATIM into a
//! `rustc_private` driver on the installed trust toolchain (`321aaeda7`), which ran it
//! on each revision's optimized MIR and printed exactly the annotated text;
//! `dep_direct_memory_safe` passes with the attribute removed instead (the
//! stand-in's `unsafe` moves the body off the memory-safe lane), and
//! `dep_reify_certify`'s note names a FOREIGN item, which the L1/L2 source fix in
//! this base adds and that stage 1 predates. Each check-fail revision is refused —
//! by `[precond] FAILED` (counterexample `y = 100`) for a direct call, by the
//! indirect-call gate for a pointer or a value (`reify`, `map` with the `requires`
//! note; `param`, `dep_param`), by the absent-callee row for the `dyn Fn` call and
//! for each `sink_*` and `value_*` shape, which calls a verify-off function — and
//! advisory reports the warning and the `[precond] FAILED` row and builds.
//! `dep_direct_memory_safe` is refused by the `[precond]` row (memory-safe refuses a
//! contract row). The `*_inline_certify` revisions are refused, as the same bodies
//! without the attribute are, by rows unrelated to `add1` too (`NonNull` casts,
//! `PtrOffset`, the uncounted `collect` allocation). The costs this pins:
//! `guarded_certify` still builds (its
//! call is charged and PROVED, with the warning), but `dep_guarded_certify`'s proved
//! call to a dependency meets the absent-callee refusal every verified body's
//! dependency call meets; and `twin_param_certify` — a `requires`-free target behind
//! a fn-pointer parameter — is refused by the gate, since the call site cannot see
//! its target. The twins keep the skip (`ASSUMPTION [assumed-total]`, no warning):
//! the attribute is honoured for a body that owes no callee anything and holds no
//! callable that could — `inc` in the inlined `Map`, reified and handed to the
//! verify-off sink, or in the promoted `H` — although `inc(y) * 2` can overflow and
//! the verified twin is refused on it.
//!
//! RECONCILED with origin/main (2026-10-02; AFTER predicted, no stage 1 with it): main's
//! ADT-residual rules (prepared, not built) make the indirect-call gate refuse an owing
//! item anywhere inside a call's type argument and a cast whose source carries one, so
//! in `collect_inline_certify`, `dep_collect_inline_certify`, `sink_reify_certify` and
//! `sink_unsize_certify` the warning's note is the GATE clause, which names `add1`
//! ("— here `…::add1`, which carries a `requires` …"), and no longer the held-callable
//! one; the `*_inline_certify` ERROR annotations match any of the error forms that
//! name the function. The verified callers `p` of `param`, `dyn`, `dep_param`,
//! `collect_param_inline` and `sink_param` reify `add1` and are refused by the same
//! cast rule (unannotated).
//!
//! Added 2026-10-02 (third review; AFTER predicted): `value_assoc_const_certify` and
//! `value_assoc_fn_certify` — a LOCAL impl's associated constant holds `add1` and a
//! verify-off function generic over the trait evaluates it (MEASURED OPEN at `-O0` by
//! the review), flagged by the associated-constant walk; `value_assoc_twin_certify`, the
//! `inc` control, keeps the skip. Two over-refusals the review measured, each with a
//! mutation control that is still refused: `thread_local_certify` (a dependency's
//! `thread_local!` read) and `closure_table_certify` (a dependency's static table of a
//! coerced closure) keep the skip, while `closure_value_mutant_certify` — a dependency's
//! coerced closure whose parent was instantiated with a fn pointer — and
//! `value_static_certify` stay refused; `phantom_certify` (`PhantomData<fn() -> u32>`)
//! keeps it, while `phantom_mutant_certify` (`Option<fn() -> u32>`) is flagged.
//!
//! Added 2026-10-02 (fifth review, which found the hang by reading; AFTER predicted):
//! `recursive_type_certify` — a body naming a POLYMORPHICALLY recursive local ADT
//! (`Nested<T>` holds `Option<Box<Nested<(T, T)>>>`), whose fields name a new type at
//! every step, must FINISH: the associated-constant walk's step budget runs out and the
//! body is verified (fail-closed), refused on the `* 2` overflow. Controls:
//! `recursive_type_control_certify` (the same with a regular `Option<Box<Nested<T>>>`,
//! which the walk's dedup ends) and `recursive_type_no_impl_certify` (the polymorphic
//! type, but no local impl of a foreign trait with associated constants or types, so
//! the walk does not run) keep the skip.
//!
//! Added 2026-10-02 (fourth review, which predicted the routes by reading; AFTER
//! predicted): `value_assoc_dyn_certify` (`&MyT` unsized to `&dyn sink::Run`, whose
//! blanket impl reads `T::H`) and `value_assoc_drop_certify` (`sink::Guard::<MyT>`'s
//! `Drop` reads it) — no call names `MyT`, and the walk keys it from the body's
//! locals' and constants' types; `value_assoc_twin_certify` now exercises both with
//! the `inc` impl and keeps the skip.
//!
//! NOT pinned here, because the rule does not reach them (residuals; docs/KNOWN_HAZARDS.md):
//! a callable the `assume_total` body neither names nor holds in a constant, which it
//! gets at run time as a VALUE whose type does not show it, and hands to verify-off
//! code that calls it. Minted in a VERIFIED caller — `add1` reified into a dependency
//! struct's non-generic `fn` field, `&dep::Wrap(add1)` unsized to `&dyn dep::Tr`, or
//! `dep::Wrap<fn {add1}>` as the instantiation of a `T: dep::Tr` parameter — each
//! built exit 0 and returned `[0]` at `-O0` on `fbc6068e3`; main's ADT-residual rules
//! refuse each in the caller (MEASURED 2026-10-03), unless the reification is in the
//! caller's promoted. Without the attribute each body is refused by the dependency
//! call's absent-callee row.
//!
//! Added 2026-10-03 (the minting-site seam, `uncharged_callable::
//! refuse_requires_carrying_values_minted_outside_verified_bodies`). The routes the
//! residuals above recorded OPEN, each refused where `add1` is minted, which no
//! verification pass reads: `table_static`/`table_static_certify` (a `static` returned to
//! the body by a verified `table()`; `table_static_advisory` warns there and builds),
//! `caller_promoted_certify` (the verified caller's promoted), `method_const_certify`,
//! `method_static_certify`, `method_promoted_certify` and `method_rpitit_certify` (a
//! verified impl method returning a pointer minted in a `const` — by reference: a method
//! returning a bare fn-pointer `const` is refused by the native lowering, `unsupported
//! constant of MIR type fn(u32) -> u32`, before any rule here looks — a `static` or a
//! promoted, or the item through an RPITIT), and `assoc_param_certify`,
//! `assoc_mk_certify`, `assoc_caller_unsize_certify` (the associated-constant route
//! through a type the body does not name, refused at the local impl's `const H`). The
//! existing `value_*` revisions gain the same error at their minting lines.
//! BEFORE (MEASURED 2026-10-03, stage 1 of `782780ea0d`, each revision compiled directly
//! with this file's flags and auxiliaries): every new check-fail revision compiles exit 0
//! except `method_reify_certify` (main's cast rule; it pins that rule, not the seam) and
//! `assoc_mk_certify`/`assoc_caller_unsize_certify`, which the spawn census already
//! refused — `UnmodeledThreadSpawnEffect` rows on `add1` and on the verified body that
//! unsizes `&MyT` to `&dyn sink::Run` (`mk`, `q`), on certify and strict alike; each
//! `value_*` revision lacks the new annotation. Linked into a verify-off `main`, the
//! library of each exit-0 revision (certify; `table_static` on the default policy too)
//! RETURNED `0` for `u32::MAX` (the verify-off build of the same source panics).
//! AFTER (MEASURED on the seam's stage 1; docs/KNOWN_HAZARDS.md names it): each is
//! refused at its minting line, and
//! `method_twin_certify` (`inc` in every method shape) and the `value_*_twin` revisions
//! forbid the new error and pass. Not reached, even so: a value minted in a VERIFY-OFF
//! crate, or written at run time into a mutable static by code no verdict covers.
//! Trust (r15, 2026-10-07): the `assume_total` revocation also asks the ONE enumeration
//! of edges into code this compilation does not verify (`unverified_edges`;
//! `unverified_edge_kinds.rs`). Seven controls here kept their skip by calling into a
//! dependency — `sink` is verify-OFF, and `dep::add1_wrapping` belongs to a crate this
//! compilation does not verify — so they never asked whether that code was memory-safe,
//! only whether it owed a `requires`. `closure_table_certify`, `dep_twin_certify`,
//! `method_twin_certify`, `sink_twin_certify`, `thread_local_certify` (`LocalKey::with`
//! runs the dependency's initializer), `value_assoc_twin_certify` and
//! `value_twin_certify` are now revoked with the edge warning and verified in full, which
//! certify refuses (the dependency call is an absent callee). Their `forbid-output` lines
//! still hold: none of them owes a `requires`. MEASURED before (stage-1 `ae0494648a`, the
//! r14 review): a verify-off dependency's safe fn writing through null, called from an
//! `assume_total` body, built rc=0 in default, strict and memory-safe, and each binary
//! died with SIGSEGV (139).
#![allow(dead_code)]

#[cfg(any(
    dep_direct,
    dep_direct_certify,
    dep_direct_memory_safe,
    dep_direct_advisory,
    dep_reify_certify,
    dep_param_certify,
    dep_guarded_certify,
    dep_twin_certify,
    value_dep_promoted_certify
))]
extern crate assume_total_requires_dep as dep;

#[cfg(any(
    sink_reify_certify,
    sink_param_certify,
    sink_unsize_certify,
    sink_twin_certify,
    value_promoted_certify,
    value_const_certify,
    value_const_val_certify,
    value_static_certify,
    value_static_dyn_certify,
    value_dep_promoted_certify,
    value_twin_certify,
    value_assoc_const_certify,
    value_assoc_fn_certify,
    value_assoc_twin_certify,
    value_assoc_dyn_certify,
    value_assoc_drop_certify,
    thread_local_certify,
    closure_table_certify,
    closure_value_mutant_certify,
    recursive_type_certify,
    recursive_type_control_certify,
    table_static,
    table_static_certify,
    table_static_advisory,
    caller_promoted_certify,
    method_const_certify,
    method_static_certify,
    method_promoted_certify,
    method_rpitit_certify,
    method_reify_certify,
    method_twin_certify,
    assoc_param_certify,
    assoc_mk_certify,
    assoc_caller_unsize_certify
))]
extern crate assume_total_callable_sink as sink;

#[cfg(any(
    direct,
    direct_strict,
    direct_certify,
    direct_advisory,
    let_certify,
    reify_certify,
    map_certify,
    param_certify,
    dyn_certify,
    closure_certify,
    method_certify,
    guarded_certify,
    sink_reify_certify,
    sink_param_certify,
    sink_unsize_certify,
    value_promoted_certify,
    value_const_certify,
    value_const_val_certify,
    value_static_certify,
    value_static_dyn_certify,
    value_assoc_const_certify,
    value_assoc_fn_certify,
    value_assoc_dyn_certify,
    value_assoc_drop_certify,
    table_static,
    table_static_certify,
    table_static_advisory,
    caller_promoted_certify,
    method_const_certify,
    method_static_certify,
    method_promoted_certify,
    method_rpitit_certify,
    method_reify_certify,
    assoc_param_certify,
    assoc_mk_certify,
    assoc_caller_unsize_certify
))]
pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

#[cfg(any(
    twin_certify,
    twin_param_certify,
    sink_twin_certify,
    value_twin_certify,
    value_assoc_twin_certify,
    method_twin_certify
))]
pub fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[cfg(any(direct, direct_strict, direct_certify, direct_advisory))]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[direct,direct_strict,direct_certify,direct_advisory]~^ WARN does not cover the preconditions its calls owe
    //[direct,direct_strict,direct_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[direct,direct_strict,direct_certify,direct_advisory]~| NOTE [precond] FAILED
    add1(y)
}

#[cfg(let_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[let_certify]~^ WARN does not cover the preconditions its calls owe
    //[let_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[let_certify]~| NOTE [precond] FAILED
    let g = add1;
    g(y)
}

#[cfg(reify_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[reify_certify]~^ WARN does not cover the preconditions its calls owe
    //[reify_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[reify_certify]~| NOTE `add1` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = add1;
    fp(y)
}

#[cfg(map_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> Option<u32> {
    //[map_certify]~^ WARN does not cover the preconditions its calls owe
    //[map_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[map_certify]~| NOTE `add1` carries a `requires` its callers owe
    Some(y).map(add1)
}

// The value is made in a VERIFIED body and called in the skipped one.
#[cfg(param_certify)]
#[trust::assume_total]
fn call(f: fn(u32) -> u32, y: u32) -> u32 {
    //[param_certify]~^ WARN does not cover the preconditions its calls owe
    //[param_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::call`
    f(y)
}

#[cfg(param_certify)]
pub fn p(y: u32) -> u32 {
    call(add1, y)
}

#[cfg(dyn_certify)]
#[trust::assume_total]
fn call(f: &dyn Fn(u32) -> u32, y: u32) -> u32 {
    //[dyn_certify]~^ WARN does not cover the preconditions its calls owe
    //[dyn_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::call`
    f(y)
}

#[cfg(dyn_certify)]
pub fn p(y: u32) -> u32 {
    call(&add1, y)
}

// The closure inherits the attribute; `p`'s own body owes nothing and keeps it.
#[cfg(closure_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    let c = |x: u32| add1(x);
    //[closure_certify]~^ WARN does not cover the preconditions its calls owe
    //[closure_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p::{closure#0}`
    //[closure_certify]~| NOTE [precond] FAILED
    c(y)
}

// The attribute on the impl reaches its methods.
#[cfg(method_certify)]
pub struct S;

#[cfg(method_certify)]
#[trust::assume_total]
impl S {
    pub fn p(&self, y: u32) -> u32 {
        //[method_certify]~^ WARN does not cover the preconditions its calls owe
        //[method_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::S::p`
        //[method_certify]~| NOTE [precond] FAILED
        add1(y)
    }
}

// The call is charged and proved: verified as if the attribute were absent, and it
// builds.
#[cfg(guarded_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[guarded_certify]~^ WARN does not cover the preconditions its calls owe
    if y < 100 { add1(y) } else { 0 }
}

// The control: no callee owes anything, so the skip stands (the verified twin is
// refused on the `* 2` overflow the attribute assumes away).
#[cfg(twin_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    inc(y) * 2
}

// The cost: the target is `requires`-free, but the call site cannot see that.
#[cfg(twin_param_certify)]
#[trust::assume_total]
fn call(f: fn(u32) -> u32, y: u32) -> u32 {
    //[twin_param_certify]~^ WARN does not cover the preconditions its calls owe
    //[twin_param_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::call`
    f(y)
}

#[cfg(twin_param_certify)]
pub fn p(y: u32) -> u32 {
    call(inc, y)
}

#[cfg(any(dep_direct, dep_direct_certify, dep_direct_memory_safe, dep_direct_advisory))]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[dep_direct,dep_direct_certify,dep_direct_memory_safe,dep_direct_advisory]~^ WARN does not cover the preconditions its calls owe
    //[dep_direct,dep_direct_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[dep_direct_memory_safe]~| ERROR Trust memory-safe verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[dep_direct,dep_direct_certify,dep_direct_memory_safe,dep_direct_advisory]~| NOTE [precond] FAILED
    dep::add1(y)
}

#[cfg(dep_reify_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[dep_reify_certify]~^ WARN does not cover the preconditions its calls owe
    //[dep_reify_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[dep_reify_certify]~| NOTE add1` carries a `requires` its callers owe
    let fp: fn(u32) -> u32 = dep::add1;
    fp(y)
}

#[cfg(dep_param_certify)]
#[trust::assume_total]
fn call(f: fn(u32) -> u32, y: u32) -> u32 {
    //[dep_param_certify]~^ WARN does not cover the preconditions its calls owe
    //[dep_param_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::call`
    f(y)
}

#[cfg(dep_param_certify)]
pub fn p(y: u32) -> u32 {
    call(dep::add1, y)
}

// The precondition is proved, and the dependency call now meets the absent-callee
// row that the skip used to remove.
#[cfg(dep_guarded_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[dep_guarded_certify]~^ WARN does not cover the preconditions its calls owe
    //[dep_guarded_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[dep_guarded_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    if y < 100 { dep::add1(y) } else { 0 }
}

#[cfg(dep_twin_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[dep_twin_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    dep::add1_wrapping(y) * 2
}

// `add1` reified and handed, as a VALUE, to a non-generic verify-off function that
// calls it: no call in this body names `add1` or carries it in a type argument. The
// reification is a cast whose source is `add1`, which main's ADT-residual cast rule
// makes the indirect-call gate refuse, so the gate clause answers.
#[cfg(sink_reify_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[sink_reify_certify]~^ WARN does not cover the preconditions its calls owe
    //[sink_reify_certify]~| NOTE add1`, which carries a `requires` its callers owe
    //[sink_reify_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[sink_reify_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::apply(add1, y)
}

// A fn-pointer parameter a verified caller fills with `add1`, handed on uncalled.
#[cfg(sink_param_certify)]
#[trust::assume_total]
fn call(f: fn(u32) -> u32, y: u32) -> u32 {
    //[sink_param_certify]~^ WARN does not cover the preconditions its calls owe
    //[sink_param_certify]~| NOTE this body holds `fn(u32) -> u32`
    //[sink_param_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::call`
    //[sink_param_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::apply(f, y)
}

#[cfg(sink_param_certify)]
pub fn p(y: u32) -> u32 {
    call(add1, y)
}

// `add1` inside a dependency's generic impl, reached through an unsizing coercion
// to `dyn sink::Tr` in this body — a cast whose source carries `add1`, so the gate
// clause answers (main's ADT-residual cast rule).
#[cfg(sink_unsize_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[sink_unsize_certify]~^ WARN does not cover the preconditions its calls owe
    //[sink_unsize_certify]~| NOTE add1`, which carries a `requires` its callers owe
    //[sink_unsize_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[sink_unsize_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    let w = sink::Wrap(add1);
    let d: &dyn sink::Tr = &w;
    d.m(y)
}

// The control: a local `requires`-free item reified and handed on keeps the skip
// (the pointer's target is named and owes nothing).
#[cfg(sink_twin_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[sink_twin_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    sink::apply(inc, y) * 2
}

// `add1` reified into a verify-off struct's non-generic `fn` field, and PROMOTED: the
// reification moves into `p::promoted[0]`, a body no pass verifies, and `p` holds only a
// `&sink::H` constant. No type in `p` names `add1`; the constant's VALUE does.
#[cfg(value_promoted_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_promoted_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_promoted_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `&sink::H` constant)
    //[value_promoted_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_promoted_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_h(&sink::H { f: add1 }, y)
    //[value_promoted_certify]~^ ERROR Trust verification failed for a promoted constant in
}

// The same through a local `const` item, by reference (promoted) and by value.
#[cfg(any(value_const_certify, value_const_val_certify))]
const HC: sink::H = sink::H { f: add1 };
//[value_const_certify,value_const_val_certify]~^ ERROR Trust verification failed for `assume_total_does_not_cover_callee_requires::HC` (a `const` initializer)

#[cfg(value_const_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_const_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_const_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `&sink::H` constant)
    //[value_const_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_const_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_h(&HC, y)
}

#[cfg(value_const_val_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_const_val_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_const_val_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `sink::H` constant)
    //[value_const_val_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_const_val_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_h_val(HC, y)
}

// A `static`, read through its initializer.
#[cfg(value_static_certify)]
static HS: sink::H = sink::H { f: add1 };
//[value_static_certify]~^ ERROR Trust verification failed for `assume_total_does_not_cover_callee_requires::HS` (a `static` initializer)

#[cfg(value_static_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_static_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_static_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `&sink::H` constant)
    //[value_static_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_static_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_h(&HS, y)
}

// A `static` `&dyn` whose vtable was made for `sink::Wrap<fn(u32) -> u32 {add1}>`.
#[cfg(value_static_dyn_certify)]
static SD: &(dyn sink::Tr + Sync) = &sink::Wrap(add1);
//[value_static_dyn_certify]~^ ERROR Trust verification failed for `assume_total_does_not_cover_callee_requires::SD` (a `static` initializer)

#[cfg(value_static_dyn_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_static_dyn_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_static_dyn_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (in the `sink::Wrap<fn(u32) -> u32 {add1}>` vtable
    //[value_static_dyn_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_static_dyn_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    SD.m(y)
}

#[cfg(value_dep_promoted_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_dep_promoted_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_dep_promoted_certify]~| NOTE this body holds `fn(u32) -> u32 {dep::add1}` (a function pointer in the value of a `&sink::H` constant)
    //[value_dep_promoted_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_dep_promoted_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_h(&sink::H { f: dep::add1 }, y)
    //[value_dep_promoted_certify]~^ ERROR Trust verification failed for a promoted constant in
}

// The control: a `requires`-free item in the same promoted keeps the skip.
#[cfg(value_twin_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_twin_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    sink::run_h(&sink::H { f: inc }, y) * 2
}

// The third review's route: a verify-off function generic over `T: sink::HasH`
// evaluates `T::H` itself, and the local impl's associated constant reifies `add1`.
// Nothing in `p` names `add1`: the associated-constant walk evaluates the constants of
// this crate's impls for `MyT`, a type `p` names.
#[cfg(any(
    value_assoc_const_certify,
    value_assoc_fn_certify,
    value_assoc_twin_certify,
    value_assoc_dyn_certify,
    value_assoc_drop_certify,
    method_const_certify,
    method_static_certify,
    method_promoted_certify,
    method_rpitit_certify,
    method_reify_certify,
    method_twin_certify,
    assoc_param_certify,
    assoc_mk_certify,
    assoc_caller_unsize_certify
))]
pub struct MyT;

#[cfg(any(
    value_assoc_const_certify,
    value_assoc_dyn_certify,
    value_assoc_drop_certify,
    assoc_param_certify,
    assoc_mk_certify,
    assoc_caller_unsize_certify
))]
impl sink::HasH for MyT {
    const H: sink::H = sink::H { f: add1 };
    //[value_assoc_const_certify,value_assoc_dyn_certify,value_assoc_drop_certify]~^ ERROR Trust verification failed for
    //[assoc_param_certify,assoc_mk_certify,assoc_caller_unsize_certify]~^^ ERROR Trust verification failed for
}

#[cfg(value_assoc_const_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_assoc_const_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_assoc_const_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `sink::H` constant), the associated constant
    //[value_assoc_const_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_assoc_const_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_assoc::<MyT>(y)
}

#[cfg(value_assoc_fn_certify)]
impl sink::HasF for MyT {
    const F: fn(u32) -> u32 = add1;
    //[value_assoc_fn_certify]~^ ERROR Trust verification failed for
}

#[cfg(value_assoc_fn_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_assoc_fn_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_assoc_fn_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `fn(u32) -> u32` constant), the associated constant
    //[value_assoc_fn_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    //[value_assoc_fn_certify]~| NOTE an unproven panic-freedom obligation for a call to an absent callee
    sink::run_f::<MyT>(y)
}

// The control: a `requires`-free item in the same associated constant keeps the skip.
#[cfg(value_assoc_twin_certify)]
impl sink::HasH for MyT {
    const H: sink::H = sink::H { f: inc };
}

#[cfg(value_assoc_twin_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_assoc_twin_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    let _g = sink::Guard::<MyT> { y, t: core::marker::PhantomData };
    sink::run_assoc::<MyT>(y) * 2 + sink::run_dyn(&MyT, y)
}

// The fourth review's routes: no CALL names `MyT`. `&MyT` is unsized to `&dyn
// sink::Run`, whose blanket impl reads `T::H` (the call `run_dyn` has no type
// arguments), and `sink::Guard::<MyT>`'s drop glue reads it (a `Drop` terminator is
// not a call). The walk keys `MyT` from the promoted `&MyT`'s type and from the
// `Guard<MyT>` local's type.
#[cfg(value_assoc_dyn_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_assoc_dyn_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_assoc_dyn_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `sink::H` constant), the associated constant
    //[value_assoc_dyn_certify]~| ERROR for `assume_total_does_not_cover_callee_requires::p`
    sink::run_dyn(&MyT, y) * 2
}

#[cfg(value_assoc_drop_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[value_assoc_drop_certify]~^ WARN does not cover the preconditions its calls owe
    //[value_assoc_drop_certify]~| NOTE this body holds `fn(u32) -> u32 {add1}` (a function pointer in the value of a `sink::H` constant), the associated constant
    //[value_assoc_drop_certify]~| ERROR for `assume_total_does_not_cover_callee_requires::p`
    let _g = sink::Guard::<MyT> { y, t: core::marker::PhantomData };
    y * 2
}

// A dependency's `thread_local!`: the static `LocalKey` holds a closure the dependency
// coerced to a fn pointer. Its generics parent is its typeck root, the non-generic
// `static`, so it has no parent arguments; it captures nothing and carries no
// `requires`: the skip stands (before, it answered "uncharged").
#[cfg(thread_local_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[thread_local_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    sink::COUNTER.with(|c| c.get()) * y
}

// A dependency's static table holding a closure it coerced to a fn pointer: the skip
// stands. `value_static_certify` is the same shape with `add1` in the table.
#[cfg(closure_table_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[closure_table_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    sink::run_h(&sink::TABLE, y) * 2
}

// The mutation control for the two above: a dependency's coerced closure whose PARENT
// was instantiated with a fn pointer (`G::<fn(u32) -> u32>::H`) is asked through that
// argument, and refused.
#[cfg(closure_value_mutant_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[closure_value_mutant_certify]~^ WARN does not cover the preconditions its calls owe
    //[closure_value_mutant_certify]~| NOTE this body holds `fn(u32) -> u32` (a function pointer in the value of a `
    //[closure_value_mutant_certify]~| ERROR Trust strict verification failed for `assume_total_does_not_cover_callee_requires::p`
    sink::run_h(&sink::G::<fn(u32) -> u32>::H, y)
}

// A `PhantomData<fn() -> u32>` holds no value: the skip stands (before, it answered
// "uncharged" as a fn pointer held as data), and the attribute assumes the `* 2`.
#[cfg(phantom_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    core::hint::black_box(core::marker::PhantomData::<fn() -> u32>);
    y * 2
}

// The mutation control: the same fn-pointer type held as DATA in an `Option` is still
// flagged, and the body, verified, is refused on the `* 2` overflow.
#[cfg(phantom_mutant_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[phantom_mutant_certify]~^ WARN does not cover the preconditions its calls owe
    //[phantom_mutant_certify]~| NOTE this body holds `fn() -> u32`
    //[phantom_mutant_certify]~| ERROR for `assume_total_does_not_cover_callee_requires::p`
    core::hint::black_box(None::<fn() -> u32>);
    y * 2
}

// The fifth review's hang: the associated-constant walk opens a local ADT's fields
// instantiated with its arguments, and `Nested<u32>`'s field names `Nested<(u32, u32)>`,
// whose field names `Nested<((u32, u32), (u32, u32))>`, without end. The walk's step
// budget ends it: "cannot read", and `p` is verified and refused on the `* 2`.
#[cfg(any(recursive_type_certify, recursive_type_control_certify, recursive_type_no_impl_certify))]
pub struct Nested<T> {
    v: T,
    #[cfg(any(recursive_type_certify, recursive_type_no_impl_certify))]
    inner: Option<Box<Nested<(T, T)>>>,
    #[cfg(recursive_type_control_certify)]
    inner: Option<Box<Nested<T>>>,
}

// A local impl of a foreign trait with an associated constant, for a type `p` does not
// name: without one the walk does not run (`recursive_type_no_impl_certify`).
#[cfg(any(recursive_type_certify, recursive_type_control_certify))]
pub struct Unnamed;

#[cfg(any(recursive_type_certify, recursive_type_control_certify))]
impl sink::HasF for Unnamed {
    const F: fn(u32) -> u32 = core::convert::identity::<u32>;
}

#[cfg(recursive_type_certify)]
#[trust::assume_total]
pub fn p(n: &Nested<u32>, y: u32) -> u32 {
    //[recursive_type_certify]~^ WARN does not cover the preconditions its calls owe
    //[recursive_type_certify]~| NOTE the walk's step budget ran out
    //[recursive_type_certify]~| ERROR for `assume_total_does_not_cover_callee_requires::p`
    let _ = n;
    y * 2
}

// The controls: a regular recursion, and the polymorphic one with no impl to match.
#[cfg(any(recursive_type_control_certify, recursive_type_no_impl_certify))]
#[trust::assume_total]
pub fn p(n: &Nested<u32>, y: u32) -> u32 {
    let _ = n;
    y * 2
}

// Trust (2026-10-03, the minting-site seam): the residual (b) and METHOD routes. Each
// mints `add1` where no verification pass looks, and the seam refuses it THERE.
//
// (b), a `static` returned to the body by a verified call: at `-O0` nothing in `p` holds
// the static, and `p` keeps its skip (MEASURED OPEN 2026-10-03 on a stage 1 of
// `782780ea0d`). The advisory revision warns at `HG` and builds; `p` keeps its skip.
#[cfg(any(table_static, table_static_certify, table_static_advisory))]
static HG: sink::H = sink::H { f: add1 };
//[table_static,table_static_certify]~^ ERROR Trust verification failed for `assume_total_does_not_cover_callee_requires::HG` (a `static` initializer)
//[table_static_advisory]~^^ WARN Trust (advisory): Trust verification failed for

#[cfg(any(table_static, table_static_certify, table_static_advisory))]
pub fn table() -> &'static sink::H {
    &HG
}

#[cfg(any(table_static, table_static_certify, table_static_advisory))]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    sink::run_h(table(), y)
}

// (b), the verified CALLER's promoted: `q` makes one direct call with no callable type
// argument, and `call` holds a parameter (MEASURED OPEN 2026-10-03).
#[cfg(caller_promoted_certify)]
#[trust::assume_total]
pub fn call(h: &sink::H, y: u32) -> u32 {
    sink::run_h(h, y)
}

#[cfg(caller_promoted_certify)]
pub fn q(y: u32) -> u32 {
    call(&sink::H { f: add1 }, y)
    //[caller_promoted_certify]~^ ERROR Trust verification failed for a promoted constant in `assume_total_does_not_cover_callee_requires::q`
}

// The METHOD route: a verified impl method returns a pointer minted in a `const`, a
// `static` or a promoted, or the item itself through an opaque type (an RPITIT). The
// method's own body mints nothing a gate reads; the seam refuses the minting site.
// The `const` shape returns a REFERENCE to the constant: a method returning a bare
// fn-pointer `const` (`fn g() -> fn(u32) -> u32 { G }`) is refused BEFORE the seam by
// the native lowering (`unsupported constant of MIR type fn(u32) -> u32`; MEASURED
// 2026-10-03, stage 1 of `782780ea0d`), so it pins nothing about the route.
#[cfg(method_const_certify)]
const GH: sink::H = sink::H { f: add1 };
//[method_const_certify]~^ ERROR Trust verification failed for `assume_total_does_not_cover_callee_requires::GH` (a `const` initializer)

#[cfg(method_const_certify)]
impl sink::HasGH for MyT {
    fn g() -> &'static sink::H {
        &GH
    }
}

#[cfg(method_const_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    sink::run_gh::<MyT>(y)
}

#[cfg(method_static_certify)]
static S: fn(u32) -> u32 = add1;
//[method_static_certify]~^ ERROR Trust verification failed for `assume_total_does_not_cover_callee_requires::S` (a `static` initializer)

#[cfg(method_static_certify)]
impl sink::HasG for MyT {
    fn g() -> fn(u32) -> u32 {
        S
    }
}

#[cfg(any(method_static_certify, method_reify_certify))]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    sink::run_g::<MyT>(y)
}

#[cfg(method_promoted_certify)]
impl sink::HasGH for MyT {
    fn g() -> &'static sink::H {
        &sink::H { f: add1 }
        //[method_promoted_certify]~^ ERROR Trust verification failed for a promoted constant in
    }
}

#[cfg(method_promoted_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    sink::run_gh::<MyT>(y)
}

#[cfg(method_rpitit_certify)]
impl sink::HasGI for MyT {
    fn g() -> impl Fn(u32) -> u32 {
        //[method_rpitit_certify]~^ ERROR Trust verification failed for the opaque return type of
        add1
    }
}

#[cfg(method_rpitit_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    sink::run_gi::<MyT>(y)
}

// The method that reifies `add1` in its OWN body: main's cast rule (2026-09-30) already
// refuses it (MEASURED 2026-10-03). Not a regression test of the seam; it passes before.
#[cfg(method_reify_certify)]
impl sink::HasG for MyT {
    fn g() -> fn(u32) -> u32 {
        //[method_reify_certify]~^ ERROR Trust strict verification failed for
        add1
    }
}

// The control: every method shape with the `requires`-free `inc`. Each needs its own
// implementing type (`MyT`, `MyU`, `MyV`, `MyW`). Nothing is refused and `p` keeps its
// skip.
#[cfg(method_twin_certify)]
pub struct MyU;

#[cfg(method_twin_certify)]
pub struct MyV;

#[cfg(method_twin_certify)]
pub struct MyW;

#[cfg(method_twin_certify)]
const GH: sink::H = sink::H { f: inc };

#[cfg(method_twin_certify)]
static S: fn(u32) -> u32 = inc;

#[cfg(method_twin_certify)]
impl sink::HasGH for MyT {
    fn g() -> &'static sink::H {
        &GH
    }
}

#[cfg(method_twin_certify)]
impl sink::HasG for MyU {
    fn g() -> fn(u32) -> u32 {
        S
    }
}

#[cfg(method_twin_certify)]
impl sink::HasG for MyV {
    fn g() -> fn(u32) -> u32 {
        inc
    }
}

#[cfg(method_twin_certify)]
impl sink::HasGH for MyW {
    fn g() -> &'static sink::H {
        &sink::H { f: inc }
    }
}

#[cfg(method_twin_certify)]
impl sink::HasGI for MyT {
    fn g() -> impl Fn(u32) -> u32 {
        inc
    }
}

#[cfg(method_twin_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    //[method_twin_certify]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    sink::run_gh::<MyT>(y)
        + sink::run_g::<MyU>(y)
        + sink::run_g::<MyV>(y)
        + sink::run_gh::<MyW>(y)
        + sink::run_gi::<MyT>(y)
}

// The associated-constant route through a type the body does not NAME: each is refused at
// the local impl's `const H` above (annotated there), wherever `MyT` later travels.
#[cfg(assoc_param_certify)]
#[trust::assume_total]
pub fn p<T: sink::HasH>(y: u32) -> u32 {
    sink::run_assoc::<T>(y)
}

#[cfg(assoc_param_certify)]
pub fn q(y: u32) -> u32 {
    p::<MyT>(y)
}

#[cfg(assoc_mk_certify)]
pub fn mk() -> &'static dyn sink::Run {
    &MyT
}

#[cfg(assoc_mk_certify)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    sink::run_dyn(mk(), y)
}

#[cfg(assoc_caller_unsize_certify)]
#[trust::assume_total]
pub fn call(r: &dyn sink::Run, y: u32) -> u32 {
    sink::run_dyn(r, y)
}

#[cfg(assoc_caller_unsize_certify)]
pub fn q(y: u32) -> u32 {
    call(&MyT, y)
}

//[twin_certify]~? RAW ASSUMPTION [assumed-total] `assume_total_does_not_cover_callee_requires::p`
//[closure_certify]~? RAW ASSUMPTION [assumed-total] `assume_total_does_not_cover_callee_requires::p`
//[phantom_certify]~? RAW ASSUMPTION [assumed-total] `assume_total_does_not_cover_callee_requires::p`
//[recursive_type_control_certify,recursive_type_no_impl_certify]~? RAW ASSUMPTION [assumed-total] `assume_total_does_not_cover_callee_requires::p`
