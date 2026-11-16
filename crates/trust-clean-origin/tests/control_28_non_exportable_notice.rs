// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 28 — THE NON-EXPORTABLE NOTICE IS A REFUSAL, NEVER EVIDENCE.**
//!
//! # What this pins
//!
//! 2026-09-16: a library crate may DEFINE a Clean-origin def whose verdict
//! cannot leave it (well-founded / per-equation recursion — no wire tag for the
//! evidence form; a def calling the crate's own Rust `fn`s — no callee table on
//! the importer's side). The export provider writes a
//! [`NonExportableNotice`] in the certificate's place and the importer's
//! readmission provider fatals on it. That moved a refusal from the EXPORT
//! seam to the IMPORT seam, so the things that must hold are about the row:
//!
//! 1. it round-trips, and both reasons survive;
//! 2. **it can never be read as a certificate** — `VerdictDigest::decode`
//!    refuses the notice's bytes, and `NonExportableNotice::recognize` answers
//!    `None` for a real digest's bytes (no cross-talk in either direction);
//! 3. a DAMAGED notice refuses whole at every truncation point, on an unknown
//!    version, an unknown reason, an empty name and a tail — it is never
//!    "recognised loosely" and never falls through to the digest lane;
//! 4. the only constructor from the emission side that takes a plan returns a
//!    notice for a Rust call chain and for NOTHING else (the close negative
//!    twin: an exportable projection gets no notice, so it cannot be silently
//!    demoted to non-exportable);
//! 5. the v7/D3 note a USER sees is the note this crate renders — the
//!    `control_25` discipline, pointed at the two `ui` fixtures
//!    `clean_origin_wf_lib_direct_call_refused.stderr` and
//!    `clean_origin_rust_call_lib_direct_call_refused.stderr`, because no
//!    pre-push lane runs a `ui` test;
//! 6. (4b) the SIBLING of a Rust-calling def is refused for a reason this
//!    crate can state truthfully: the exporter's island does not elaborate
//!    without the exporter's callee table (put to the real elaborator here),
//!    only a Rust-callee notice yields the sibling note, and a well-founded
//!    notice never does.
//!
//! The export-seam half — that a WELL-FOUNDED verdict converts into a notice
//! and a mistranslated body does NOT — lives in
//! `control_8_wf_rec_emitter_mutation.rs`, beside the measured emission it
//! needs.

use clean_kernel::{BinderInfo, Environment, Expr, Name};
use trust_certify::clean_island::{CleanIslandSession, RustCallee};
use trust_clean_origin::admission::{
    VERDICT_DIGEST_MAGIC, VerdictDigest, mint_encoded_digest_for_export,
};
use trust_clean_origin::{
    NON_EXPORTABLE_NOTICE_FORMAT_V1, NON_EXPORTABLE_NOTICE_MAGIC, NonExportableNotice,
    NonExportableReason, NoticeDecodeRefusal, RustCalleeRef, plan_clean_origin_body,
    plan_clean_origin_body_with_rust_callees,
};
use trust_symbols::{AxiomClosure, CicKernelRecheck, KernelAuthority as _, TermDigest};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── wire helpers ───────────────────────────────
//
// Hand-built, on purpose: the crate offers no constructor from a bare name, so
// a test that wants arbitrary bytes writes the documented layout itself —
// which also pins that layout against `encode`.

fn put_str(out: &mut Vec<u8>, text: &str) {
    out.extend_from_slice(&u32::try_from(text.len()).unwrap().to_le_bytes());
    out.extend_from_slice(text.as_bytes());
}

fn wf_notice_bytes(decl: &str, evidence_form: &str) -> Vec<u8> {
    let mut out = NON_EXPORTABLE_NOTICE_MAGIC.to_vec();
    out.push(NON_EXPORTABLE_NOTICE_FORMAT_V1);
    put_str(&mut out, decl);
    out.push(1);
    put_str(&mut out, evidence_form);
    out
}

fn rust_callee_notice_bytes(decl: &str) -> Vec<u8> {
    let mut out = NON_EXPORTABLE_NOTICE_MAGIC.to_vec();
    out.push(NON_EXPORTABLE_NOTICE_FORMAT_V1);
    put_str(&mut out, decl);
    out.push(2);
    out
}

fn recognised(bytes: &[u8]) -> NonExportableNotice {
    NonExportableNotice::recognize(bytes)
        .expect("the bytes carry the notice magic")
        .expect("and are a whole notice")
}

// ───────────────────────── 1. round trip, both reasons ────────────────────

#[test]
fn both_reasons_round_trip_and_encode_is_the_documented_layout() {
    let wf = recognised(&wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq"));
    assert_eq!(wf.decl(), "countdownSum");
    assert_eq!(
        wf.reason(),
        &NonExportableReason::UnspellableFaithfulness {
            evidence_form: "WellFoundedFunctionalDefeq".to_owned()
        }
    );
    assert_eq!(
        wf.encode(),
        wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq"),
        "encode must be exactly the documented layout — the importer reads these bytes"
    );
    assert_eq!(NonExportableNotice::recognize(&wf.encode()), Some(Ok(wf)));

    let rc = recognised(&rust_callee_notice_bytes("twice_inc"));
    assert_eq!(rc.decl(), "twice_inc");
    assert_eq!(rc.reason(), &NonExportableReason::RustCallees);
    assert_eq!(rc.encode(), rust_callee_notice_bytes("twice_inc"));
}

// ─────────────── 2. a notice is never a certificate, and vice versa ───────

/// `control_4`'s `pick` fixture, verbatim: the projection fragment the emitter
/// can actually serialize, entered through the FULL kernel check.
fn env_with_pick() -> Environment {
    let uint64 = || Expr::const_(Name::from_string("UInt64"), vec![]);
    let mut env = Environment::new();
    env.init_uint_arith().expect("UInt8/16/32/64 must initialize");
    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("pick"),
        level_params: vec![],
        type_: Expr::arrow(uint64(), Expr::arrow(uint64(), uint64())),
        // `fun x y => x`: source parameter 0 is de Bruijn 1 under two binders.
        value: Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(BinderInfo::Default, uint64(), Expr::bvar(1)),
        ),
        is_reducible: true,
    })
    .expect("`pick` is a well-typed UInt64 -> UInt64 -> UInt64 definition");
    env
}

/// The serialized body as the extractor reports it: `_0 = move _1`, `return`.
fn extracted_pick() -> VerifiableFunction {
    VerifiableFunction {
        name: "pick".into(),
        def_path: "crate::m::pick".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: (0..3).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

#[test]
fn a_notice_never_decodes_as_a_digest_and_a_digest_is_never_recognised_as_a_notice() {
    for notice in [
        wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq"),
        wf_notice_bytes("sumTo", "PerEquationDefeq"),
        rust_callee_notice_bytes("twice_inc"),
    ] {
        assert!(
            VerdictDigest::decode(&notice).is_err(),
            "A NON-EXPORTABLE NOTICE DECODED AS A VERDICT DIGEST: an importer would carry it \
             into readmission as a certificate"
        );

        // THE ADVERSARIAL TWIN (the crate-level half of
        // `tests/run-make/trust-clean-origin-non-exportable-notice`): rewrite the
        // magic so the row CLAIMS to be a certificate. The magic is not what keeps
        // a notice out of the certificate lane — a notice does not CONTAIN a
        // certificate, so the relabelled bytes must still refuse, and must no
        // longer be recognised as a notice (the refusal then belongs to the
        // certificate decoder, fail-closed).
        let mut relabelled = notice.clone();
        relabelled[..VERDICT_DIGEST_MAGIC.len()].copy_from_slice(&VERDICT_DIGEST_MAGIC);
        assert_eq!(NonExportableNotice::recognize(&relabelled), None);
        assert!(
            VerdictDigest::decode(&relabelled).is_err(),
            "A NOTICE RELABELLED WITH THE CERTIFICATE MAGIC DECODED AS A CERTIFICATE"
        );
    }

    // The close twin, through the REAL export seam: an exportable projection
    // exports a certificate, and that certificate is not a notice.
    let env = env_with_pick();
    let status = CicKernelRecheck::held_by_kernel_recheck()
        .kernel_checked(TermDigest::of_bytes(b"control-28-fixture"), AxiomClosure::audited([]));
    let digest = mint_encoded_digest_for_export(&env, "pick", &status, &extracted_pick())
        .expect("a kernel-checked projection with a faithful body must export a CERTIFICATE");
    assert!(VerdictDigest::decode(&digest).is_ok());
    assert_eq!(
        NonExportableNotice::recognize(&digest),
        None,
        "a real certificate must fall through to the digest lane, never be refused as a notice"
    );

    // Bytes too short to carry any magic are not a notice either; the digest
    // decoder is what refuses them.
    assert_eq!(NonExportableNotice::recognize(b""), None);
    assert_eq!(NonExportableNotice::recognize(b"TVN"), None);
    assert!(VerdictDigest::decode(b"TVN").is_err());
}

// ──────────────────── 3. a damaged notice refuses whole ───────────────────

#[test]
fn every_truncation_of_a_notice_refuses_and_none_panics_or_falls_through() {
    for whole in [
        wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq"),
        rust_callee_notice_bytes("twice_inc"),
    ] {
        for cut in NON_EXPORTABLE_NOTICE_MAGIC.len()..whole.len() {
            let outcome = NonExportableNotice::recognize(&whole[..cut]);
            assert!(
                matches!(outcome, Some(Err(NoticeDecodeRefusal::Truncated { .. }))),
                "a notice cut at byte {cut} of {} must refuse as truncated — `None` here \
                 would hand a damaged notice to the digest lane; got {outcome:?}",
                whole.len()
            );
        }
    }
}

#[test]
fn unknown_version_unknown_reason_empty_name_and_a_tail_all_refuse() {
    let mut future = wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq");
    future[NON_EXPORTABLE_NOTICE_MAGIC.len()] = NON_EXPORTABLE_NOTICE_FORMAT_V1 + 1;
    assert!(matches!(
        NonExportableNotice::recognize(&future),
        Some(Err(NoticeDecodeRefusal::UnknownFormatVersion { found: 2, supported: 1 }))
    ));

    let mut odd_reason = rust_callee_notice_bytes("twice_inc");
    *odd_reason.last_mut().unwrap() = 3;
    let refusal = NonExportableNotice::recognize(&odd_reason).unwrap().unwrap_err();
    assert!(
        matches!(refusal, NoticeDecodeRefusal::Malformed { field: "reason", .. }),
        "got {refusal:?}"
    );
    assert!(refusal.note().contains("options:"), "v7/D3: {}", refusal.note());
    assert!(
        refusal.note().contains("NOT imported"),
        "the note must say the definition is refused, not merely that bytes were odd: {}",
        refusal.note()
    );

    assert!(matches!(
        NonExportableNotice::recognize(&rust_callee_notice_bytes("")),
        Some(Err(NoticeDecodeRefusal::Malformed { field: "decl", .. }))
    ));
    assert!(matches!(
        NonExportableNotice::recognize(&wf_notice_bytes("countdownSum", "")),
        Some(Err(NoticeDecodeRefusal::Malformed { field: "evidence form", .. }))
    ));

    let mut tailed = rust_callee_notice_bytes("twice_inc");
    tailed.push(0);
    assert!(matches!(
        NonExportableNotice::recognize(&tailed),
        Some(Err(NoticeDecodeRefusal::TrailingBytes { count: 1 }))
    ));
    // The tail that would matter most: a whole certificate appended to a
    // notice. Still a refusal — the row is one record or it is nothing.
    let mut smuggled = rust_callee_notice_bytes("twice_inc");
    smuggled.extend_from_slice(b"TVDG");
    assert!(matches!(
        NonExportableNotice::recognize(&smuggled),
        Some(Err(NoticeDecodeRefusal::TrailingBytes { count: 4 }))
    ));
}

// ───────── 4. the plan constructor: a Rust call chain, and nothing else ────

fn declared_inc() -> Vec<RustCallee> {
    vec![RustCallee { clean_name: "inc".into(), params: vec![Ty::u64()], result: Ty::u64() }]
}

fn inc_table() -> Vec<RustCalleeRef> {
    vec![RustCalleeRef {
        def_path: "clean_origin_rust_call_lib_aux::m::inc".to_owned(),
        clean_name: "inc".into(),
        params: vec![Ty::u64()],
        result: Ty::u64(),
    }]
}

#[test]
fn only_a_rust_call_chain_plan_yields_a_notice() {
    // The island of `tests/ui/trust/auxiliary/clean_origin_rust_call_lib_aux.rs`,
    // through the REAL elaborator with the callee declared.
    let mut session = CleanIslandSession::new();
    session.declare_rust_callees(&declared_inc()).expect("the callee declares");
    let batch = session.check_all(&[RUST_CALL_LIB_ISLAND]);
    assert!(!batch.is_rejected(), "side A must elaborate: {batch:?}");
    let env = session.environment().expect("an untainted session has an environment");

    let chain = plan_clean_origin_body_with_rust_callees(env, "twice_inc", &inc_table())
        .expect("`twice_inc` plans as a Rust call chain");
    let notice = NonExportableNotice::for_rust_call_chain(&chain)
        .expect("a def that calls the crate's own Rust fn has no exportable certificate");
    assert_eq!(notice.decl(), "twice_inc");
    assert_eq!(notice.reason(), &NonExportableReason::RustCallees);

    // THE CLOSE NEGATIVE TWIN: same island, same callee table, a def that does
    // not call Rust. It must get NO notice — otherwise the export provider
    // would stop certifying exportable defs and every cross-crate call to them
    // would start refusing.
    let projection = plan_clean_origin_body_with_rust_callees(env, "keep", &inc_table())
        .expect("`keep` plans as an ordinary projection");
    assert_eq!(NonExportableNotice::for_rust_call_chain(&projection), None);
    let plain = plan_clean_origin_body(&env_with_pick(), "pick").expect("`pick` plans");
    assert_eq!(NonExportableNotice::for_rust_call_chain(&plain), None);
}

// ───── 4b. the SIBLING of a Rust-calling def: refused, and told the truth ─────

/// The island of `clean_origin_rust_call_lib_aux.rs`, verbatim.
const RUST_CALL_LIB_ISLAND: &str = "def twice_inc (x : UInt64) : UInt64 := inc (inc x)\n\
                                    def keep (x : UInt64) : UInt64 := x";

/// THE FACT the sibling diagnostic rests on, put to the real elaborator: an
/// importer re-elaborates the exporter's island sources in a FRESH session
/// (`clean_origin_import.rs` step 4), and a Rust callee is a compiler-declared
/// constant, never island text. So the island that elaborates in the defining
/// crate does not elaborate on the importer's side — for `keep` either.
#[test]
fn the_exporters_island_elaborates_with_its_callee_table_and_not_without_it() {
    let mut exporter = CleanIslandSession::new();
    exporter.declare_rust_callees(&declared_inc()).expect("the callee declares");
    let batch = exporter.check_all(&[RUST_CALL_LIB_ISLAND]);
    assert!(!batch.is_rejected() && !exporter.is_tainted(), "side A must elaborate: {batch:?}");

    let mut importer = CleanIslandSession::new();
    let batch = importer.check_all(&[RUST_CALL_LIB_ISLAND]);
    assert!(
        batch.is_rejected() || importer.is_tainted(),
        "the importer has no `inc`; if this island elaborates without the callee table the \
         sibling refusal (and its note) no longer describes anything real: {batch:?}"
    );
    assert!(
        importer.environment().is_none(),
        "a session that could not elaborate the exporter's islands must yield NO environment \
         — readmission of `keep` has nothing to re-plan against, and refuses"
    );
}

#[test]
fn only_a_rust_callee_notice_explains_a_blocked_sibling_and_it_is_not_the_skew_guess() {
    let rc = recognised(&rust_callee_notice_bytes("twice_inc"));
    let note = rc
        .sibling_import_note("keep")
        .expect("a Rust-calling def is exactly what stops its crate's islands re-elaborating");
    assert!(note.contains("`keep`") && note.contains("`twice_inc`"), "{note}");
    assert!(note.contains("calls a Rust `fn`"), "the WHY: {note}");
    assert!(
        note.contains("NOT kernel skew"),
        "the arm this note replaces tells the user to rebuild the dependency; this one must \
         say that will not help: {note}"
    );
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(note.lines().all(|line| !line.starts_with(' ')), "{note}");

    // THE CLOSE NEGATIVE TWIN: a well-founded def is pure Clean text and
    // re-elaborates anywhere, so it never blocks a sibling — blaming it would
    // hide a REAL kernel-skew refusal behind a wrong explanation.
    let wf = recognised(&wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq"));
    assert_eq!(wf.sibling_import_note("keep2"), None);
    let mut pure = CleanIslandSession::new();
    let batch = pure.check_all(&[
        "def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0\n\
         termination_by n",
    ]);
    assert!(
        !batch.is_rejected() && !pure.is_tainted(),
        "a well-founded def must elaborate in a fresh session with no callee table: {batch:?}"
    );
}

// ─────────────── 5. fixture parity: the note a USER reads ─────────────────

fn fixture(file: &str) -> String {
    let path = format!("{}/../../tests/ui/trust/{file}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read `{path}`: {e}"))
}

/// The first `= note:` body of a committed `.stderr` — `rustc` prints it as
/// `   = note: <first line>` plus continuation lines indented by exactly 11
/// spaces, and does not re-wrap (see `control_25`, whose reader this mirrors).
fn first_note_from_stderr(stderr: &str) -> String {
    const HEAD: &str = "   = note: ";
    const CONT: &str = "           ";
    let mut lines = stderr.lines().peekable();
    while let Some(line) = lines.next() {
        let Some(first) = line.strip_prefix(HEAD) else { continue };
        let mut body = vec![first.to_owned()];
        while let Some(next) = lines.peek() {
            let Some(rest) = next.strip_prefix(CONT) else { break };
            body.push(rest.to_owned());
            lines.next();
        }
        return body.join("\n");
    }
    panic!("the fixture carries no `= note:` at all — the refusal lost its v7/D3 note");
}

fn assert_parity(file: &str, notice: &NonExportableNotice) {
    let rendered = notice.import_note();
    assert!(rendered.contains("options:"), "v7/D3 — the refusal must carry options: {rendered}");
    assert!(
        rendered.lines().all(|line| !line.starts_with(' ')),
        "a rendered line with leading whitespace would make the 11-space continuation \
         strip below inexact"
    );
    assert_eq!(
        first_note_from_stderr(&fixture(file)).trim_end(),
        rendered.trim_end(),
        "\n\nThe note committed in `tests/ui/trust/{file}` is NOT what this crate renders \
         today. A user reads the fixture's version; ruling v7/D3 says that text IS the fix. \
         Fix whichever is stale — no pre-push lane runs the `ui` suite, so nothing else \
         will tell you.\n"
    );
}

#[test]
fn the_import_refusals_a_user_reads_are_the_ones_this_crate_renders() {
    let wf = recognised(&wf_notice_bytes("countdownSum", "WellFoundedFunctionalDefeq"));
    assert!(
        wf.import_note().contains("no wire tag"),
        "the WHY of this refusal is the missing wire tag; the note must say so: {}",
        wf.import_note()
    );
    assert!(wf.import_note().contains("WellFoundedFunctionalDefeq"));
    assert_parity("clean_origin_wf_lib_direct_call_refused.stderr", &wf);

    let rc = recognised(&rust_callee_notice_bytes("twice_inc"));
    assert!(rc.import_note().contains("calls a Rust `fn`"), "{}", rc.import_note());
    assert_parity("clean_origin_rust_call_lib_direct_call_refused.stderr", &rc);
}
