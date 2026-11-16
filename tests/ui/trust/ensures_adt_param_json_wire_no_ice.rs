//@ revisions: trait_impl_ref_self trait_impl_ref_self_certify trait_impl_mut_self
//@ revisions: trait_impl_by_value_self trait_impl_called inherent_ref_self
//@ revisions: struct_by_value struct_by_ref option_param
//@ needs-trust-verify
//@ check-pass
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@[trait_impl_ref_self_certify] compile-flags: -Ztrust-policy=certify
//@ edition: 2021
//@ dont-check-compiler-stderr
#![crate_type = "lib"]
//! **Regression: a fully proved `ensures` on a fn whose parameter type names an
//! ADT must not ICE on the JSON wire — a trait impl method's `&self` above all.**
//!
//! The E9 island-admission seam (`admit_clause_island_definitions`) builds, for
//! EVERY contract-bearing body it visits, a shadow map from each parameter name
//! to the help line a clause author would see if a clause named that binding
//! (`trust_fn_clause_shadow_idents` -> `trust_clause_shadow_help`). The line
//! rendered the parameter type with a bare `{ty}`. A type that names an ADT
//! (`&S`, `S`, `Option<u32>`) prints through the `trimmed_def_paths` query,
//! which arms rustc's `must_produce_diag`; the line is consulted only if a
//! clause names a shadowed binding, so on a compile that otherwise emits no
//! diagnostic the assertion fired at session teardown, after the proved rows
//! were written. MEASURED on stage 1 of `bd8681c2628` with exactly the header
//! flags above, every revision here:
//!
//!     thread 'rustc' panicked at compiler/rustc_errors/src/lib.rs:478:17:
//!     `trimmed_def_paths` called, diagnostics were expected but none were emitted
//!     exit 101
//!
//! with `RUST_BACKTRACE=1` naming `trust_clause_shadow_help` (four of its five
//! branches, one per parameter reading) under `trust_fn_clause_shadow_idents`,
//! `admit_clause_island_definitions`, `grade_uncited_island_ensures_clause`.
//! The same on strict, the default policy and `certify`, built as an rlib or
//! checked. It was first logged in `docs/KNOWN_HAZARDS.md` as "a trait impl
//! method carrying an `ensures` crashes trustc at session end"; the trait impl
//! is incidental — `&self` names the impl's `Self` type, an ADT. Controls that
//! passed on the same stage 1 (no ADT in the signature): a scalar-only free fn,
//! a trait DEFAULT method (`&Self` is a type parameter), a generic `&T`.
//!
//! Fix: `trust_clause_shadow_help` renders under `with_no_trimmed_paths!`. The
//! ensures is still CHECKED: each revision pins its crate summary with the
//! function verified and nothing failed or unknown (the postcondition rows are
//! `proved`), and `ensures_adt_param_json_wire_violated_stays_rejected.rs`
//! pins that a false clause in the same shapes still fails the build.
//!
//! ── WHY THESE EXACT FLAGS ────────────────────────────────────────────────────
//!
//! `must_produce_diag` is satisfied by ANY emission, so the defect only shows on
//! a compile that emits no diagnostic at all (`json_output_contract_only_no_ice.rs`
//! has the long form): text output prints a verification `note:`, and
//! `--error-format=json` — compiletest's default — wraps every `TRUST_JSON` row
//! in a `note:` diagnostic. Only the human error format writes the rows with a
//! raw `eprintln!`; without it this file cannot fail. So every revision is a lib
//! crate with only `pub` items (no dead-code warning) whose obligations PROVE.
//! Before trusting a green from this file after any edit, re-measure it against
//! a compiler WITHOUT the fix and confirm each revision still exits 101.
//!
//! The pins are RAW annotations (a human error format makes every stderr line a
//! RAW diagnostic, and a matching `error-pattern` would be fatal), one per
//! revision, on the `crate_summary` row; stderr is otherwise unchecked because
//! the function rows carry paths, claim digests and engine detail.
//!
//! ── WHY `trait_impl_called` HAS A LINEAR BODY ────────────────────────────────
//!
//! It was first `if x != 0 { 100 / x } else { 0 }`, and that revision went red
//! on m16 (2026-09-30) with two `unknown` rows on `<S as Td>::m`: the division
//! branch's body row and the clause marker it leaves undischarged. That was
//! recorded as a std-with-debug-assertions effect; it is not one. The verifier
//! input is byte-identical under either std (same native bundle and request
//! digests), and the red is LOAD: `100 / x <= 100` is nonlinear, the Clean
//! kernel does not certify it, and its only prover, ay-chc, needs seconds of
//! wall clock for it. Every red run at a budget of 500 ms or more also prints a
//! refutation that strict certification withdrew ("step t0 uses unverified
//! trust rule"); no green run does. Measured on m16's std at origin/main
//! `486460dbe77`: 5 of 5 compiletest runs of this file and 18 of 18 concurrent
//! compiles green, 36 of 36 concurrent compiles red, all with exactly those two
//! rows; still 36 of 36 red at `-Ztrust-verify-timeout-ms=120000`, so a larger
//! budget is no remedy here; serially red at 3000 ms, green at 5000. A refusal
//! under load is sound, but a check-pass pin on it measured the machine.
//!
//! The ICE needs only the signature (`&self` names the ADT `S`) and a compile
//! that emits no diagnostic, both unchanged. Both branches of the new body are
//! certified by the Clean kernel, which no solver budget gates: they prove at
//! `-Ztrust-verify-timeout-ms=1`, and 36 of 36 concurrent compiles are green.
//! With the fix reverted (stage 1 of `486460dbe77`, the helper rendering its
//! bare `{ty}` again), every revision here, the new `trait_impl_called`
//! included, still exits 101 with the `trimmed_def_paths` panic. The division
//! shape is pinned, starved and refused, by
//! `ensures_nonlinear_div_solver_starved_stays_refused.rs`.

#[cfg(any(
    trait_impl_ref_self,
    trait_impl_ref_self_certify,
    trait_impl_called,
    inherent_ref_self
))]
pub struct S;

#[cfg(any(trait_impl_ref_self, trait_impl_ref_self_certify))]
pub trait Get {
    fn get(&self) -> u32;
}

#[cfg(any(trait_impl_ref_self, trait_impl_ref_self_certify))]
impl Get for S {
    fn get(&self) -> u32
        ensures result == 7
    {
        7
    }
}

#[cfg(trait_impl_mut_self)]
pub struct Counter {
    pub n: u32,
}

#[cfg(trait_impl_mut_self)]
pub trait Tick {
    fn tick(&mut self, d: u32) -> u32;
}

#[cfg(trait_impl_mut_self)]
impl Tick for Counter {
    fn tick(&mut self, d: u32) -> u32
        ensures result == d
    {
        let _ = self.n;
        d
    }
}

#[cfg(trait_impl_by_value_self)]
#[derive(Clone, Copy)]
pub struct Cell {
    pub n: u32,
}

#[cfg(trait_impl_by_value_self)]
pub trait Take {
    fn take(self) -> u32;
}

#[cfg(trait_impl_by_value_self)]
impl Take for Cell {
    fn take(self) -> u32
        ensures result == self.n
    {
        self.n
    }
}

// The probe shape the defect was found with: the impl method AND a caller that
// reaches it through the trait. The body is linear (see the header).
#[cfg(trait_impl_called)]
pub trait Td {
    fn m(&self, x: u32) -> u32;
}

#[cfg(trait_impl_called)]
impl Td for S {
    fn m(&self, x: u32) -> u32
        ensures result <= 100
    {
        if x <= 100 { x } else { 100 }
    }
}

#[cfg(trait_impl_called)]
pub fn p(y: u32) -> u32 {
    S.m(y)
}

#[cfg(inherent_ref_self)]
impl S {
    pub fn get(&self) -> u32
        ensures result == 7
    {
        7
    }
}

#[cfg(any(struct_by_value, struct_by_ref))]
#[derive(Clone, Copy)]
pub struct P {
    pub x: u32,
}

#[cfg(struct_by_value)]
pub fn by_value(p: P) -> u32
    ensures result == p.x
{
    p.x
}

#[cfg(struct_by_ref)]
pub fn by_ref(p: &P) -> u32
    ensures result == p.x
{
    p.x
}

#[cfg(option_param)]
pub fn keep(o: Option<u32>, x: u32) -> u32
    ensures result == x
{
    let _ = o;
    x
}

//[trait_impl_ref_self]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":1,"functions_verified":1,"total_proved":2,"total_failed":0,"total_unknown":0
//[trait_impl_ref_self_certify]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":1,"functions_verified":1,"total_proved":2,"total_failed":0,"total_unknown":0
//[trait_impl_mut_self]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":1,"functions_verified":1,"total_proved":2,"total_failed":0,"total_unknown":0
//[trait_impl_by_value_self]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":2,"functions_verified":2,"total_proved":3,"total_failed":0,"total_unknown":0
//[trait_impl_called]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":2,"functions_verified":2,"total_proved":4,"total_failed":0,"total_unknown":0
//[inherent_ref_self]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":1,"functions_verified":1,"total_proved":2,"total_failed":0,"total_unknown":0
//[struct_by_value]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":2,"functions_verified":2,"total_proved":3,"total_failed":0,"total_unknown":0
//[struct_by_ref]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":2,"functions_verified":2,"total_proved":3,"total_failed":0,"total_unknown":0
//[option_param]~? RAW TRUST_JSON:{"type":"crate_summary","crate_name":"ensures_adt_param_json_wire_no_ice","functions_analyzed":1,"functions_verified":1,"total_proved":2,"total_failed":0,"total_unknown":0
