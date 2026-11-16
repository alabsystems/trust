//@ needs-trust-verify
//@ revisions: bundled nobundle
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@[bundled] dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[bundled] check-fail
//@[nobundle] rustc-env:TRUST_NO_BUNDLE_STD=1
//@[nobundle] check-fail
//! "A fixture whose mutant survives when the body is not read is the shape
//! wanted." — plan of record `docs/design/2026-08-19-verified-sysroot-scoping.md`
//! (deleted by `6ba5324748a`; read it at `6ba5324748a^`),
//! §5 step 2a′. This is that fixture: the corpus's only bundling-dependent RED
//! (§2.5's `method_named_write` analysis), distilled to its two-line trigger
//! and pinned in BOTH directions under the same certify policy §2.5 ran.
//!
//! `Result::<(), io::Error>::unwrap_or_default` bundles, and its body reaches a
//! `Drop` terminator whose glue the prover cannot lower — `io::Error` can
//! transitively hold a `Box<dyn Error + Send + Sync>` whose `Drop` IS user
//! code, so modelling it total on type identity would be unsound
//! (`tests/trust-falsification/proved/method_named_write.rs` records the three
//! measured dead ends). The obligation is REAL, and it exists ONLY because the
//! prover read the real body:
//!
//!   * `bundled` (check-fail): the lane reads the body, mints the drop-glue
//!     obligation, and certify refuses it. An honest red — §2.5: "an obligation
//!     that exists only because the prover read real code is the whole point".
//!   * `nobundle` (check-fail since 2026-09-28): `TRUST_NO_BUNDLE_STD=1`, so the
//!     body is never read. Until 2026-09-28 the same functions then sailed through
//!     green: `unwrap_or_default` is a closure-driving consumer, and the bridge gave
//!     the unread call a may-panic marker that nothing requested
//!     (`docs/KNOWN_HAZARDS.md`, "A may-panic MARKER is only as good as its
//!     CARRIER"). That green was the hole, and a real one: the `Err` arm drops the
//!     `io::Error`, whose boxed payload's `Drop` is user code. With the carrier, the
//!     unread call is charged conservatively and certify refuses it. The mutant no
//!     longer survives the body going unread; it now dies for a different reason
//!     than in `bundled`.
//!
//! `probe_const_ok` is the decisive twin from the corpus header: its tag is a
//! compile-time-constant `Ok`, and it minted the byte-identical row anyway —
//! the lane does not consult the tag, so no Ok-pinning cleverness explains a
//! future colour change here.
//!
//! What a flip means:
//!
//!   * `bundled` goes GREEN: the B-lane stopped reading this body (the silent
//!     coverage-deletion refactor §5 2a′ warns about — this row is the net for
//!     the corpus's red direction), or drop glue for `io::Error` started being
//!     assumed total (route 1 of the measured dead ends, unsound), or std's
//!     drop glue actually lowers now — in which case celebrate, re-derive this
//!     fixture, and move `method_named_write` too.
//!   * `nobundle` went RED on 2026-09-28, for the second reason this list gave:
//!     the unread call's obligation stopped being never-minted. §2.5's 125/0
//!     baseline was measured with that hole open, so its numbers need
//!     re-measuring. If `nobundle` goes GREEN again, an unread consumer call has
//!     lost its carrier.

// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): still refused, but no
// longer zero-row. The call into the bundled body now carries the counted panic-freedom
// aggregate (one unproved `runtime_checked` row), so ZERO-ROW-GATE's note is gone and the
// body is refused on that row instead.
//[nobundle]~vv ERROR Trust strict verification failed for `native_bundle_std_red_depends_on_bundled_body::probe_unwrap_or_default`
//[nobundle]~v ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_red_depends_on_bundled_body::probe_unwrap_or_default`
pub fn probe_unwrap_or_default(r: Result<(), std::io::Error>) { //[bundled]~ ERROR Trust strict verification failed for `native_bundle_std_red_depends_on_bundled_body::probe_unwrap_or_default`
    r.unwrap_or_default()
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(e)): still refused, but no
// longer zero-row. The call into the bundled body now carries the counted panic-freedom
// aggregate (one unproved `runtime_checked` row), so ZERO-ROW-GATE's note is gone and the
// body is refused on that row instead.
//[nobundle]~vv ERROR Trust strict verification failed for `native_bundle_std_red_depends_on_bundled_body::probe_const_ok`
//[nobundle]~v ERROR Trust Level 0 safety verification incomplete for `native_bundle_std_red_depends_on_bundled_body::probe_const_ok`
pub fn probe_const_ok() { //[bundled]~ ERROR Trust strict verification failed for `native_bundle_std_red_depends_on_bundled_body::probe_const_ok`
    let r: Result<(), std::io::Error> = Ok(());
    r.unwrap_or_default()
}

fn main() {}
