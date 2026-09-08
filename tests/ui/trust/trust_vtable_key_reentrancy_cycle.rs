//@ check-pass
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr

// `-Ztrust-verify=on` is LOAD-BEARING, not decoration. Compiletest isolates the inherited
// Rust corpus from the verifier by appending `-Ztrust-verify=off` to every test
// compilation (`common.rs::configure_trust_verification_isolation`), and the crash lives
// in the extractor's `TyKind::Dynamic` arm, which only runs when verification does.
// Measured on the sealed stage before the fix: this file SIGBUSes under `=on` and
// compiles in 0.30 s under `=off`. Without these two directives the test would pass
// against the unfixed compiler and pin nothing.

// Trust: a trait object whose KEY mentions a type that HOLDS that trait object used to
// take `trustc` down with a SIGBUS — a native stack overflow inside the verifier itself.
//
// REPRODUCED 2026-09-01 on the sealed stage `trust-62a7cf46`. Every function below is
// ordinary Rust; the crash needed no pathological nesting, no deep generics and no
// unusual flags — only verification ON, which is the default. `clean-runtime` is the
// shipped instance: it dies with the identical backtrace cycle, and with
// `TRUST_VCGEN_TRACE_BUDGET=1` the last 200 completed key-render walks before the SIGBUS
// alternate `(io_runtime::IoValue,)` and `io_runtime::IoValue`, exactly 100 each — this
// cycle turning.
//
// THE MECHANISM, and why it is not "a missing cycle guard". `trust-mir-extract`'s type
// lowering carries four bounds — a depth limit, a node budget, a produced-tree budget and
// an `adt_stack` back-edge guard — and all four are present and correct. They live in the
// `TyLoweringCtx`, and `faithful_key_skeleton` classifies each node of a trait object's
// key by starting a FRESH one (`faithful_vtable_key_ty` -> `convert_ty_in_env`). So every
// bound was RESET once per trip around the cycle:
//
//     convert_ty_inner(dyn ..)  ->  faithful_principal_key  ->  faithful_key_skeleton
//       ->  convert_ty_in_env   ->  the holding ADT's fields  ->  the same dyn
//
// A guard that is discarded at a re-entrant boundary is not a guard. The fix is a
// thread-local in-progress set that SURVIVES the boundary, plus a well-founded frame
// bound for the generic families that re-enter with a fresh type every trip and so never
// repeat one. Both outcomes are REPORTED under their own refusal tags
// (`RefusalShape::SelfReferential`, `RefusalShape::ReentryBoundExceeded`) and both land
// on the pre-existing fail-closed value `principal_key: None`, which takes the THIN
// spelling in the bridge — so a refusal can only lose a proof, never mint an identity.
//
// WHAT DISTINGUISHES A CRASHING SHAPE FROM A SAFE ONE, measured as a controlled pair
// (`Cycle3` vs `Guarded` below, which differ in exactly one field). `canonical_cut_set`
// computes its cut points over the NOMINAL FIELD graph — `nominal_frontier` peels
// `Ref`/`RawPtr`/`Adt` fields and does NOT follow a trait object's predicate arguments.
// So a type whose ONLY cycle runs through a `dyn`'s key is not recognised as recursive,
// is not a cut point, and the fresh walk expands it instead of emitting a by-name marker
// — which is what lets the cycle close. Give that same type an ORDINARY recursive field
// and it becomes a cut point, the fresh walk returns a one-node marker, and the cycle
// never forms. That is why the `Action` case below does NOT reproduce today, and it is
// pinned here deliberately: it is the property the safe cases rely on, so a future change
// to the cut set cannot quietly re-open this class.
//
// WHAT THIS TEST ASSERTS: that `trustc` TERMINATES on all of these shapes. Before the fix
// it did not return at all on the three marked REPRODUCED — it died on signal, so there
// was no verdict to be right or wrong about. Which rows end up refused is a coverage
// decision recorded elsewhere; a crash is not.

use std::sync::Arc;

// ── Cycle 1: REPRODUCED. Through the trait object's PRINCIPAL ARGUMENT, Fn sugar ──────
// `dyn Fn(&[V]) -> u32` desugars to `Fn<(&[V],)>`, so rendering the key lowers `(&[V],)`
// — which walks into `V`, whose field is that same trait object.

pub enum V {
    Unit,
    F(Arc<dyn Fn(&[V]) -> u32 + Send + Sync>),
}

pub fn v_tag(v: &V) -> u32 {
    match v {
        V::Unit => 0,
        V::F(_) => 1,
    }
}

// ── Cycle 2: REPRODUCED. A BARE NOMINAL principal argument, no `Fn` sugar ─────────────
// Measured separately, because the obvious reading of cycle 1 — "the `Fn`-sugar tuple is
// the escape hatch, a tuple is not nominal so the cut set never cuts it" — is FALSE:
// `dyn Take<Cycle2>` puts the recursive type in the argument position directly and still
// SIGBUSes. The tuple is incidental; the argument POSITION is the edge.

pub trait Take<T> {
    fn take(&self, t: &T) -> u32;
}

pub enum Cycle2 {
    Unit,
    F(Arc<dyn Take<Cycle2> + Send + Sync>),
}

pub fn cycle2_tag(v: &Cycle2) -> u32 {
    match v {
        Cycle2::Unit => 0,
        Cycle2::F(_) => 1,
    }
}

// ── Cycle 3: REPRODUCED. MUTUAL — neither type re-enters ITSELF ──────────────────────
// The in-progress set is a SET, not a self-check: `A` -> `dyn ..(B)` -> `B` -> `dyn ..(A)`
// closes a cycle in which no single type is ever its own immediate re-entry. A guard
// written as `ty == the_one_being_rendered` would not catch this; measured, it SIGBUSes.

pub enum A {
    Stop,
    ToB(Arc<dyn Fn(&B) -> u32 + Send + Sync>),
}

pub enum B {
    Stop,
    ToA(Arc<dyn Fn(&A) -> u32 + Send + Sync>),
}

pub fn mutual_tag(a: &A, b: &B) -> u32 {
    let l = match a {
        A::Stop => 0,
        A::ToB(_) => 1,
    };
    let r = match b {
        B::Stop => 0,
        B::ToA(_) => 1,
    };
    l + r
}

// ── Control: `Guarded` is `Cycle2` PLUS ONE ORDINARY RECURSIVE FIELD ─────────────────
// Measured: this does NOT reproduce, and the pair `Cycle2`/`Guarded` isolates why — the
// extra `Next(Box<Guarded>)` makes the type recursive in the NOMINAL FIELD graph, so
// `canonical_cut_set` cuts it and the fresh key-render walk returns a one-node by-name
// marker instead of expanding. Keep both: the difference between them is the whole
// characterisation of the crashing class.

pub enum Guarded {
    Unit,
    Next(Box<Guarded>),
    F(Arc<dyn Take<Guarded> + Send + Sync>),
}

pub fn guarded_tag(v: &Guarded) -> u32 {
    match v {
        Guarded::Unit => 0,
        Guarded::Next(_) => 1,
        Guarded::F(_) => 2,
    }
}

// ── Control: the `clean-runtime` ASSOCIATED-TYPE BINDING shape ────────────────────────
// `Output = Action` is the binding term and `Action` holds the trait object, so this
// looks like a cycle — and measured, it is NOT one today, for the same reason `Guarded`
// is safe: `Bind(Box<Action>, ..)` makes `Action` recursive in the nominal field graph,
// so it is a cut point. Pinned because the binding term reaches the renderer through the
// same entry point as a principal argument, so the day the cut set stops covering it
// this becomes cycle 4.

pub enum Value {
    Unit,
    Nat(u64),
    Pair(Box<Value>, Box<Value>),
    List(Vec<Value>),
}

pub enum Action {
    Pure(Value),
    Bind(Box<Action>, Box<dyn FnOnce(Value) -> Action>),
    Map(Box<Action>, Box<dyn FnOnce(Value) -> Value>),
}

pub fn action_tag(a: &Action) -> u32 {
    match a {
        Action::Pure(_) => 0,
        Action::Bind(..) => 1,
        Action::Map(..) => 2,
    }
}

// ── Control: an ACYCLIC trait object over the same machinery ─────────────────────────
// `Plain` does not hold the trait object, so nothing re-enters and the key is rendered
// exactly as it was before this guard existed. The guard costs a terminating input
// nothing — it fires only on a re-entry.

pub struct Plain(pub u32);

// The body is deliberately trivial: naming the trait object in the SIGNATURE is what
// makes the extractor render its key, which is the thing under test. Calling it, or
// taking `size_of_val` of the fat pointer, adds an unrelated panic-freedom obligation
// over an absent callee that strict policy correctly refuses — measured, and it would
// make this fixture fail for a reason that has nothing to do with the cycle.
pub fn plain_tag(_f: &(dyn Fn(&Plain) -> u32 + Send + Sync)) -> u32 {
    7
}

fn main() {}
