//! REAL-MIR pin: a call handed `&*self` does not havoc `self`'s frozen scalar
//! fields (TRUST-10).
//!
//! # What was wrong
//!
//! bit-vec 0.9.1 (`src/lib.rs:1824`) has
//!
//! ```text
//! pub fn remove(&mut self, at: usize) -> bool {
//!     assert!(at < self.nbits, ..);
//!     self.ensure_invariant();          // fn ensure_invariant(&self)
//!     self.nbits -= 1;
//!     ..
//! ```
//!
//! Compiled with `-Ztrust-policy=advisory` it reported
//!
//! ```text
//! [overflow:sub] FAILED (ay-in-process); counterexample: … at = 0, self*.1 = 1, self*.1#e_s1_t = 0
//! ```
//!
//! `self.nbits` is 1 at the assert and 0 after the call, which received only a
//! shared reborrow. The call havoc list carries the base name `self` for every
//! `&mut` local, so the call re-versioned every field. A reference passed as an
//! argument is protected for the call: writing a byte it covers (outside an
//! `UnsafeCell`) during the call is undefined behaviour, so the counterexample is
//! not an execution. `callee_write_set::refine_shared_reborrow_havoc` now keeps
//! the frozen scalar fields of the reborrowed place.
//!
//! # The matrix
//!
//! | fixture | expectation |
//! |---|---|
//! | `remove` (guard, `self.check()` taking `&self`, `self.n -= 1`) | `[overflow:sub]` not REFUTED |
//! | `remove_after_reset` (the call takes `&mut self` and sets `n = 0`) | `[overflow:sub]` REFUTED |
//! | `dec_unguarded` (`self.check()` then `self.n -= 1`, no guard) | `[overflow:sub]` REFUTED |
//! | `remove_then_push` (`remove`, then `self.v.push(0)` borrows a field mutably) | `[overflow:sub]` not REFUTED |
//!
//! `remove_then_push` is bit-vec's own shape: its `remove` goes on to borrow
//! `self.storage` mutably, and a `&mut (*self).f` anywhere in the body used to count as
//! an alias of `self` itself, which refused the refinement for the whole method
//! (`local_defs::pointer_is_pinned` now asks only whether the POINTER can change).
//! `remove_after_reset` and `dec_unguarded` are the load-bearing half: a call that
//! CAN write the field, and a real underflow behind a `&self` call, must both keep
//! their refutation. The `UnsafeCell`, `Box`, covered-prefix, escape and
//! aggregate-argument exclusions are pinned on hand-built MIR in
//! `src/generate/callee_write_set/tests.rs`.
//!
//! # Fixtures
//!
//! `tests/fixtures/shared_reborrow_call_*_mir.json` are the compiler's own
//! extraction of the source below, captured with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> shared_reborrow_call.rs
//! ```
//!
//! ```text
//! pub struct S { n: usize, v: Vec<u32> }
//! impl S {
//!     fn check(&self) { let _ = self.v.len(); }
//!     fn reset(&mut self) { self.n = 0; }
//!     pub fn remove(&mut self, at: usize) {
//!         assert!(at < self.n);
//!         self.check();
//!         self.n -= 1;
//!     }
//!     pub fn remove_after_reset(&mut self, at: usize) {
//!         assert!(at < self.n);
//!         self.reset();
//!         self.n -= 1;
//!     }
//!     pub fn dec_unguarded(&mut self) {
//!         self.check();
//!         self.n -= 1;
//!     }
//!     pub fn remove_then_push(&mut self, at: usize) {
//!         assert!(at < self.n);
//!         self.check();
//!         self.n -= 1;
//!         self.v.push(0);
//!     }
//! }
//! ```
use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/shared_reborrow_call_");
    let text = std::fs::read_to_string(format!("{path}{name}_mir.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The verdict of every `[overflow:sub]` row of `name`, each dispatched to the
/// deterministic in-process ay the bridge uses.
fn sub_overflow_rows(name: &str) -> Vec<String> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            let mut rows = Vec::new();
            for vc in &vcs {
                if !matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. }) {
                    continue;
                }
                let verdict = match router
                    .verify_all(std::slice::from_ref(vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC")
                    .1
                {
                    VerificationResult::Proved { .. } => "PROVED".to_string(),
                    VerificationResult::Failed { .. } => "REFUTED".to_string(),
                    other => format!("{other:?}").chars().take(24).collect(),
                };
                rows.push(verdict);
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

/// bit-vec's `remove` shape: the guard `at < self.n` survives `self.check()`.
#[test]
fn a_guard_survives_a_call_that_takes_only_a_shared_reborrow() {
    let rows = sub_overflow_rows("remove");
    assert!(!rows.is_empty(), "the fixture must produce an `[overflow:sub]` row");
    assert!(
        rows.iter().all(|v| v != "REFUTED"),
        "`self.n >= 1` after the assert, and `check(&self)` cannot write `n`; a refutation \
         is a counterexample over a havocked frozen field: {rows:?}"
    );
}

/// bit-vec's `remove` shape: the method also borrows a field mutably after the call.
#[test]
fn a_guard_survives_when_the_method_also_borrows_a_field_mutably() {
    let rows = sub_overflow_rows("remove_then_push");
    assert!(!rows.is_empty(), "the fixture must produce an `[overflow:sub]` row");
    assert!(
        rows.iter().all(|v| v != "REFUTED"),
        "`&mut (*self).v` borrows the pointee; it cannot reseat `self`, and `check(&self)` \
         cannot write `n`: {rows:?}"
    );
}

/// The call takes `&mut self` and does set `n = 0`: the underflow is real.
#[test]
fn a_mutable_receiver_call_still_kills_the_guard() {
    let rows = sub_overflow_rows("remove_after_reset");
    assert!(
        rows.iter().any(|v| v == "REFUTED"),
        "`reset(&mut self)` writes `n = 0` before `n -= 1`; this must stay refuted: {rows:?}"
    );
}

/// No guard at all: `n == 0` is a real input, the `&self` call changes nothing.
#[test]
fn a_real_underflow_behind_a_shared_reborrow_call_stays_refuted() {
    let rows = sub_overflow_rows("dec_unguarded");
    assert!(
        rows.iter().any(|v| v == "REFUTED"),
        "`self.n -= 1` with `n == 0` is reachable; this must stay refuted: {rows:?}"
    );
}
