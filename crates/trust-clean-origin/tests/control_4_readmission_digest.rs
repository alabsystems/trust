// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 4 — THE I7 RE-ADMISSION FIXTURE.**
//!
//! The increment's acceptance control, verbatim from
//! `docs/design/2026-08-04-two-language-compiler-architecture.md` §7:
//!
//! > an imported certificate minted under a different kernel version must be
//! > re-checked or refused, never accepted on a matching source hash
//!
//! This file runs both halves of every decision: the digest must REFUSE on
//! each single-field skew (kernel version, axiom closure, environment content,
//! carrier decision, defeq marker, and every byte-level corruption), and the
//! identical-everything digest must READMIT — a gate that refuses everything
//! is as useless as one that admits everything, and only the pair
//! distinguishes a real decision from a constant function.
//!
//! # How the wire-tamper tests work, stated so they are not "simplified" later
//!
//! [`trust_clean_origin::admission::VerdictDigest`] is sealed: the only
//! constructors are the mint (which demands sealed evidence) and `decode`. So
//! a digest whose carrier field lies cannot be built through the API — which
//! is the point — and the tests that need one build it the way an attacker or
//! a corrupt transport would: by editing the ENCODED BYTES and decoding them.
//! That doubles as the fail-closed-parse exercise. The byte edits target the
//! `u64` renderings, which appear exactly three times in this fixture's
//! encoding (argument carrier, result carrier, defeq marker) and nowhere else
//! (the hex field's alphabet has no `u`; `UInt64` differs in case).

use clean_kernel::{BinderInfo, Environment, Expr, Name};
use trust_clean_carrier::{CarrierSignature, carrier_signature_for};
use trust_clean_origin::admission::{
    DecodeRefusal, DigestMintRefusal, ExportDigestRefusal, ReadmissionRefusal, VerdictDigest,
    environment_digest_for, local_kernel_version, mint_encoded_digest_for_export,
    mint_verdict_digest, readmit,
};
use trust_clean_origin::{EmitRefusal, Faithful, check_faithful};
use trust_symbols::{Assumption, AxiomClosure, CicKernelRecheck, KernelAuthority as _, KernelStatus, TermDigest};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Fixture
// ---------------------------------------------------------------------------

fn uint64_ty() -> Expr {
    Expr::const_(Name::from_string("UInt64"), vec![])
}

fn u64_carrier() -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_at(
        &uint64_ty(),
        &trust_types::Ty::Int { width: 64, signed: false },
    )
    .expect("UInt64 -> u64 is the exact-width carrier and must be granted")
}

/// `fun a => UInt64.add a a` — `double`'s body, also usable as a trivially
/// faithful side B for the gate.
fn double_body() -> Expr {
    let a = Expr::bvar(0);
    Expr::lam(
        BinderInfo::Default,
        uint64_ty(),
        Expr::app(Expr::app(Expr::const_(Name::from_string("UInt64.add"), vec![]), a.clone()), a),
    )
}

/// `fun a => UInt64.mul a a` — same name, same type, DIFFERENT content.
fn double_body_mul() -> Expr {
    let a = Expr::bvar(0);
    Expr::lam(
        BinderInfo::Default,
        uint64_ty(),
        Expr::app(Expr::app(Expr::const_(Name::from_string("UInt64.mul"), vec![]), a.clone()), a),
    )
}

/// An environment holding `def double (a : UInt64) : UInt64 := <body>`,
/// entered through the FULL kernel check.
fn env_with_double(body: Expr) -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith()
        .expect("UInt8/16/32/64 plus wrapping add/sub/mul must initialize");
    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("double"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), uint64_ty()),
        value: body,
        is_reducible: true,
    })
    .expect("`double` must be admissible: a well-typed UInt64 -> UInt64 definition");
    env
}

/// A kernel-checked status with an audited-EMPTY closure — the honest status
/// of the fixture definitions, which really do rest on nothing.
fn certified_status() -> KernelStatus {
    CicKernelRecheck::held_by_kernel_recheck()
        .kernel_checked(TermDigest::of_bytes(b"control-4-fixture"), AxiomClosure::audited([]))
}

fn signature() -> CarrierSignature {
    carrier_signature_for(&Expr::arrow(uint64_ty(), uint64_ty()))
        .expect("UInt64 -> UInt64 carries exactly in both positions")
}

/// A REAL gate verdict for `double` — evidence, not a stand-in.
fn faithful_for(env: &Environment, side_b: &Expr) -> Faithful {
    check_faithful(env, "double", side_b, &u64_carrier())
        .expect("the gate must admit a lowering identical to the definition body")
}

/// The whole honest mint, end to end.
fn honest_digest(env: &Environment) -> VerdictDigest {
    let environment =
        environment_digest_for(env, "double").expect("`double` is in the environment");
    mint_verdict_digest(&certified_status(), environment, &signature(), &faithful_for(env, &double_body()))
        .expect("every input is the sealed evidence the mint demands")
}

/// Replace the `index`-th occurrence of `needle` in `bytes`.
///
/// Same length in and out, so every length prefix stays valid — the tamper is
/// a FIELD-VALUE change, not a framing change, which is what makes the decode
/// succeed and the semantic check the thing that must catch it.
fn tamper(bytes: &[u8], needle: &[u8], replacement: &[u8], index: usize) -> Vec<u8> {
    assert_eq!(needle.len(), replacement.len(), "tamper must preserve framing");
    let mut found = 0usize;
    let mut out = bytes.to_vec();
    let mut at = 0usize;
    while at + needle.len() <= out.len() {
        if &out[at..at + needle.len()] == needle {
            if found == index {
                out[at..at + needle.len()].copy_from_slice(replacement);
                return out;
            }
            found += 1;
        }
        at += 1;
    }
    panic!("occurrence {index} of {needle:?} not found ({found} present) — the fixture's \
            encoding changed; re-derive the tamper offsets before trusting this file");
}

// ---------------------------------------------------------------------------
// Round trip
// ---------------------------------------------------------------------------

#[test]
fn round_trip_encode_decode_is_identity() {
    let env = env_with_double(double_body());
    let digest = honest_digest(&env);

    let decoded = VerdictDigest::decode(&digest.encode())
        .expect("a freshly encoded digest must decode whole");

    assert_eq!(decoded, digest, "decode(encode(d)) must be d, field for field");
    // And the decoded claim, being identical, must still readmit — the round
    // trip may not degrade a certificate.
    readmit(&decoded, local_kernel_version(), &env)
        .expect("an identical round-tripped digest must readmit");
}

#[test]
fn round_trip_preserves_a_named_assumption() {
    // A digest CARRYING assumptions is legal on the wire (the disclosure is
    // the product); it is re-admission to CALL that refuses it. The round
    // trip must not drop or re-kind the names.
    let env = env_with_double(double_body());
    let status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"control-4-assumption-bearing"),
        AxiomClosure::audited([
            Assumption::trust_marker("sorryAx").expect("named"),
            Assumption::domain_axiom("key_lemma").expect("named"),
        ]),
    );
    let environment = environment_digest_for(&env, "double").expect("present");
    let digest =
        mint_verdict_digest(&status, environment, &signature(), &faithful_for(&env, &double_body()))
            .expect("an assumption-bearing verdict still mints — it discloses");

    let decoded = VerdictDigest::decode(&digest.encode()).expect("decodes whole");
    assert_eq!(decoded, digest);
    let names: Vec<&str> = decoded.assumptions().iter().map(Assumption::name).collect();
    assert_eq!(names, vec!["key_lemma", "sorryAx"], "disclosure must survive the wire by name");
}

// ---------------------------------------------------------------------------
// THE ACCEPTANCE CONTROL, VERBATIM
// ---------------------------------------------------------------------------

#[test]
fn acceptance_control_a_different_kernel_version_refuses_even_when_everything_else_matches() {
    let env = env_with_double(double_body());
    let digest = honest_digest(&env);

    // Establish "everything else matches": under the TRUE local version this
    // exact digest readmits. Without this half the refusal below could be
    // about anything.
    readmit(&digest, local_kernel_version(), &env)
        .expect("the identical-everything digest must readmit under the minting kernel");

    // The control: same digest, same environment, same carrier, same closure,
    // same defeq marker — presented to a DIFFERENT kernel version.
    let other_version = format!("{}-other", local_kernel_version());
    let refusal = readmit(&digest, &other_version, &env).expect_err(
        "THE ACCEPTANCE CONTROL FAILED: a certificate minted under kernel X was \
         accepted by kernel Y. The design doc's I7 row forbids exactly this — a \
         kernel verdict does not survive a kernel change, whatever else matches.",
    );
    match refusal {
        ReadmissionRefusal::KernelVersionSkew { ref minted_under, ref local, .. } => {
            assert_eq!(minted_under, local_kernel_version());
            assert_eq!(local, &other_version);
        }
        other => panic!("expected KernelVersionSkew, got {other:?}"),
    }
    // v7/D3: the refusal must carry the fix, with options.
    let note = refusal.note();
    assert!(note.contains("options:"), "a refusal without options is a defect (v7/D3): {note}");
    assert!(note.contains("rebuild"), "the note must name the rebuild resolution: {note}");
    assert!(note.contains("re-check"), "the note must name the re-check seam: {note}");
}

// ---------------------------------------------------------------------------
// Field skews, one at a time
// ---------------------------------------------------------------------------

#[test]
fn axiom_closure_mismatch_refuses() {
    // Identical kernel, identical environment, identical carrier — but the
    // verdict rests on a named assumption. CALL re-admission must refuse and
    // disclose the name.
    let env = env_with_double(double_body());
    let status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"control-4-sorry"),
        AxiomClosure::audited([Assumption::trust_marker("sorryAx").expect("named")]),
    );
    let environment = environment_digest_for(&env, "double").expect("present");
    let digest =
        mint_verdict_digest(&status, environment, &signature(), &faithful_for(&env, &double_body()))
            .expect("minting an assumption-bearing digest is legal; re-admitting it to CALL is not");

    let refusal = readmit(&digest, local_kernel_version(), &env)
        .expect_err("an assumption-bearing certificate must not readmit to CALL");
    match refusal {
        ReadmissionRefusal::AssumptionBearing { ref assumptions, .. } => {
            assert_eq!(assumptions, &vec!["sorryAx".to_owned()], "disclosed BY NAME");
        }
        other => panic!("expected AssumptionBearing, got {other:?}"),
    }
    assert!(refusal.note().contains("options:"));
}

#[test]
fn environment_content_skew_refuses_same_name_same_type_different_body() {
    // The sharpest environment test: the local `double` has the SAME name,
    // SAME type, SAME carrier decision — only the body differs (mul, not
    // add). A source hash of the call site, a name match, and the whole
    // carrier decision all agree here; only the environment digest sees it.
    let env_add = env_with_double(double_body());
    let env_mul = env_with_double(double_body_mul());
    let digest = honest_digest(&env_add);

    let refusal = readmit(&digest, local_kernel_version(), &env_mul).expect_err(
        "a verdict about `a + a` must not be re-admitted over an environment where \
         `double` is `a * a` — the emitted call would produce different values than \
         the definition the verdict was about",
    );
    assert!(
        matches!(refusal, ReadmissionRefusal::EnvironmentSkew { .. }),
        "expected EnvironmentSkew, got {refusal:?}"
    );
    assert!(refusal.note().contains("options:"));
}

#[test]
fn a_missing_local_declaration_refuses() {
    let env_with = env_with_double(double_body());
    let digest = honest_digest(&env_with);

    let mut env_without = Environment::new();
    env_without.init_uint_arith().expect("prelude");

    let refusal = readmit(&digest, local_kernel_version(), &env_without)
        .expect_err("a certificate about a declaration the local environment lacks must refuse");
    assert!(
        matches!(refusal, ReadmissionRefusal::DeclarationMissing { .. }),
        "expected DeclarationMissing, got {refusal:?}"
    );
}

#[test]
fn an_undisclosed_assumption_found_locally_refuses() {
    // The lying-producer lane. `leak`'s body references the axiom `mystery`,
    // but the digest is minted with a (false) audited-empty closure — the
    // sealed KernelStatus is only as honest as its producer, and this test IS
    // that dishonest producer. The importer's local DAG walk must catch it.
    let mut env = Environment::new();
    env.init_uint_arith().expect("prelude");
    env.add_decl(clean_kernel::Declaration::Axiom {
        name: Name::from_string("mystery"),
        level_params: vec![],
        type_: uint64_ty(),
    })
    .expect("an axiom of UInt64 type is admissible");
    let leak_body = Expr::lam(
        BinderInfo::Default,
        uint64_ty(),
        Expr::const_(Name::from_string("mystery"), vec![]),
    );
    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("leak"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), uint64_ty()),
        value: leak_body.clone(),
        is_reducible: true,
    })
    .expect("`leak` is well-typed");

    let faithful = check_faithful(&env, "leak", &leak_body, &u64_carrier())
        .expect("side B identical to the definition body is trivially defeq");
    let environment = environment_digest_for(&env, "leak").expect("present");
    let lying_status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"control-4-liar"),
        AxiomClosure::audited([]), // THE LIE: `leak` rests on `mystery`.
    );
    let digest = mint_verdict_digest(&lying_status, environment, &signature(), &faithful)
        .expect("the mint trusts the sealed status; the importer is who must catch the lie");

    let refusal = readmit(&digest, local_kernel_version(), &env).expect_err(
        "a certificate claiming an empty closure over a DAG that names `mystery` \
         must be refused — the disclosure is the product",
    );
    match refusal {
        ReadmissionRefusal::UndisclosedAssumptions { ref found, .. } => {
            assert_eq!(found, &vec!["mystery".to_owned()], "the catch must name what it found");
        }
        other => panic!("expected UndisclosedAssumptions, got {other:?}"),
    }
}

#[test]
fn carrier_mismatch_refuses() {
    // Byte-level tamper (see module docs): occurrence 0 of "u64" is the
    // ARGUMENT carrier, occurrence 1 the RESULT carrier. Both must refuse as
    // carrier skew against the locally recomputed decision.
    let env = env_with_double(double_body());
    let bytes = honest_digest(&env).encode();

    for (occurrence, position_hint) in [(0usize, "argument 0"), (1usize, "the result")] {
        let tampered = tamper(&bytes, b"u64", b"u32", occurrence);
        let decoded = VerdictDigest::decode(&tampered)
            .expect("a same-length value tamper preserves framing, so it must decode — \
                     the SEMANTIC check is what has to catch it");
        let refusal = readmit(&decoded, local_kernel_version(), &env)
            .expect_err("a carrier decision differing from the local one must refuse");
        match refusal {
            ReadmissionRefusal::CarrierSkew { ref position, ref imported, ref local, .. } => {
                assert_eq!(position, position_hint);
                assert!(imported.contains("u32"), "imported side: {imported}");
                assert!(local.contains("u64"), "local side: {local}");
            }
            other => panic!("expected CarrierSkew at {position_hint}, got {other:?}"),
        }
    }
}

#[test]
fn defeq_marker_mismatch_refuses() {
    // Occurrence 2 of "u64" is the defeq marker's admitted-at. With both
    // carrier positions intact, the marker alone disagreeing must refuse.
    let env = env_with_double(double_body());
    let bytes = honest_digest(&env).encode();

    let tampered = tamper(&bytes, b"u64", b"u32", 2);
    let decoded = VerdictDigest::decode(&tampered).expect("framing preserved");
    let refusal = readmit(&decoded, local_kernel_version(), &env)
        .expect_err("a defeq marker naming a non-local carrier must refuse");
    match refusal {
        ReadmissionRefusal::DefeqSkew { ref claimed, ref local, .. } => {
            assert_eq!(claimed, "u32");
            assert_eq!(local, "u64");
        }
        other => panic!("expected DefeqSkew, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Fail-closed parsing
// ---------------------------------------------------------------------------

#[test]
fn every_truncation_refuses_and_none_panics() {
    let env = env_with_double(double_body());
    let bytes = honest_digest(&env).encode();

    for cut in 0..bytes.len() {
        assert!(
            VerdictDigest::decode(&bytes[..cut]).is_err(),
            "a digest truncated to {cut} of {} bytes must refuse, not partially parse",
            bytes.len()
        );
    }
}

#[test]
fn corrupted_magic_refuses() {
    let env = env_with_double(double_body());
    let mut bytes = honest_digest(&env).encode();
    bytes[0] ^= 0xff;

    assert!(
        matches!(
            VerdictDigest::decode(&bytes),
            Err(DecodeRefusal::NotAVerdictDigest { .. })
        ),
        "bytes without the magic are not a digest at all"
    );
}

#[test]
fn unknown_format_version_refuses_not_best_effort_parses() {
    let env = env_with_double(double_body());
    let mut bytes = honest_digest(&env).encode();
    bytes[4] = 2; // a future format this reader has never heard of

    match VerdictDigest::decode(&bytes) {
        Err(DecodeRefusal::UnknownFormatVersion { found, supported }) => {
            assert_eq!(found, 2);
            assert_eq!(supported, 1);
        }
        other => panic!(
            "an unknown format version must refuse outright — a best-effort parse \
             fails open on exactly the field a new version added; got {other:?}"
        ),
    }
}

#[test]
fn trailing_bytes_refuse() {
    let env = env_with_double(double_body());
    let mut bytes = honest_digest(&env).encode();
    bytes.push(0);

    assert!(
        matches!(VerdictDigest::decode(&bytes), Err(DecodeRefusal::TrailingBytes { count: 1 })),
        "a digest with a tail is not the digest it appears to be"
    );
}

#[test]
fn corrupted_hex_refuses() {
    // Flip one environment-digest character to a non-hex byte. The field is
    // validated on decode, so the corruption is caught at the parse rather
    // than surviving into a comparison that could never match anything.
    let env = env_with_double(double_body());
    let digest = honest_digest(&env);
    let bytes = digest.encode();
    let hex = digest.environment().as_hex().as_bytes().to_vec();
    let tampered_hex: Vec<u8> =
        hex.iter().map(|&b| if b == hex[0] { b'z' } else { b }).collect();
    let tampered = tamper(&bytes, &hex, &tampered_hex, 0);

    assert!(
        matches!(
            VerdictDigest::decode(&tampered),
            Err(DecodeRefusal::Malformed { field: "environment digest", .. })
        ),
        "a non-hex environment digest must refuse at the parse"
    );
}

// ---------------------------------------------------------------------------
// The mint's own refusals
// ---------------------------------------------------------------------------

#[test]
fn mint_refuses_a_non_kernel_checked_status() {
    let env = env_with_double(double_body());
    let environment = environment_digest_for(&env, "double").expect("present");

    let refusal = mint_verdict_digest(
        &KernelStatus::Parsed,
        environment,
        &signature(),
        &faithful_for(&env, &double_body()),
    )
    .expect_err("a parse is not a kernel verdict, so there is no verdict to digest");
    assert!(
        matches!(refusal, DigestMintRefusal::NotKernelChecked { .. }),
        "expected NotKernelChecked, got {refusal:?}"
    );
    assert!(refusal.note().contains("options:"));
}

#[test]
fn mint_refuses_an_unrecorded_closure() {
    // `KernelChecked` with an unrecorded closure — "nobody looked" must not
    // cross a crate boundary looking like "nothing found".
    let env = env_with_double(double_body());
    let environment = environment_digest_for(&env, "double").expect("present");
    let status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"control-4-unrecorded"),
        AxiomClosure::unrecorded(),
    );

    let refusal =
        mint_verdict_digest(&status, environment, &signature(), &faithful_for(&env, &double_body()))
            .expect_err("an unrecorded closure cannot be disclosed, so it cannot be exported");
    assert!(
        matches!(refusal, DigestMintRefusal::ClosureUnrecorded { .. }),
        "expected ClosureUnrecorded, got {refusal:?}"
    );
}

#[test]
fn mint_refuses_evidence_from_two_different_decisions() {
    // A Faithful admitted at u64 stitched to a signature whose result carries
    // at bool: each is real sealed evidence, but not about the same decision.
    let env = env_with_double(double_body());
    let environment = environment_digest_for(&env, "double").expect("present");
    let mismatched = carrier_signature_for(&Expr::arrow(
        uint64_ty(),
        Expr::const_(Name::from_string("Bool"), vec![]),
    ))
    .expect("UInt64 -> Bool carries in both positions");

    let refusal = mint_verdict_digest(
        &certified_status(),
        environment,
        &mismatched,
        &faithful_for(&env, &double_body()),
    )
    .expect_err("a digest stitched from mismatched evidence would bind nothing");
    assert!(
        matches!(refusal, DigestMintRefusal::EvidenceMismatch { .. }),
        "expected EvidenceMismatch, got {refusal:?}"
    );
}

// ---------------------------------------------------------------------------
// The environment digest itself
// ---------------------------------------------------------------------------

#[test]
fn environment_digest_binds_content_and_is_insertion_order_independent() {
    // Same declarations, different insertion order -> same digest (the hash
    // is over canonicalized content, so build nondeterminism cannot manufacture
    // skew). Different body -> different digest (the hash binds content, which
    // is exactly what a source hash of the call site would fail to do).
    let mut env_ab = Environment::new();
    env_ab.init_uint_arith().expect("prelude");
    let decl_a = clean_kernel::Declaration::Definition {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), uint64_ty()),
        value: Expr::lam(BinderInfo::Default, uint64_ty(), Expr::bvar(0)),
        is_reducible: true,
    };
    let decl_b = clean_kernel::Declaration::Definition {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), uint64_ty()),
        value: Expr::lam(BinderInfo::Default, uint64_ty(), Expr::bvar(0)),
        is_reducible: true,
    };
    env_ab.add_decl(decl_a.clone()).expect("a");
    env_ab.add_decl(decl_b.clone()).expect("b");

    let mut env_ba = Environment::new();
    env_ba.init_uint_arith().expect("prelude");
    env_ba.add_decl(decl_b).expect("b");
    env_ba.add_decl(decl_a).expect("a");

    // `a` references only UInt64 machinery, identically in both environments.
    assert_eq!(
        environment_digest_for(&env_ab, "a").expect("present"),
        environment_digest_for(&env_ba, "a").expect("present"),
        "insertion order must not leak into the digest"
    );

    assert_ne!(
        environment_digest_for(&env_with_double(double_body()), "double").expect("present"),
        environment_digest_for(&env_with_double(double_body_mul()), "double").expect("present"),
        "a different definition body must produce a different environment digest"
    );
}

#[test]
fn environment_digest_refuses_a_missing_subject() {
    let env = env_with_double(double_body());
    let refusal = environment_digest_for(&env, "no_such_def")
        .expect_err("a subject that does not resolve has no closure to digest");
    assert!(refusal.note().contains("options:"));
}

// ---------------------------------------------------------------------------
// The export seam (I7 encode half) — mint_encoded_digest_for_export
// ---------------------------------------------------------------------------
//
// The compiler's rmeta export provider makes exactly ONE crate call:
// `mint_encoded_digest_for_export(env, name, status, extracted)` -> wire bytes.
// These tests run that seam end to end against the real kernel, with the same
// hand-built `VerifiableFunction` shape `control_3` uses (and justifies: the
// decision procedure under test is the same object the compiler calls; whether
// the compiler's emitter really produces this MIR is the compiler lane's
// business).

/// An environment holding `def pick (x : UInt64) (y : UInt64) : UInt64 := x` —
/// the projection fragment the emitter can actually serialize, entered through
/// the FULL kernel check.
fn env_with_pick() -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith().expect("UInt8/16/32/64 must initialize");
    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("pick"),
        level_params: vec![],
        type_: Expr::arrow(uint64_ty(), Expr::arrow(uint64_ty(), uint64_ty())),
        // `fun x y => x`: source parameter 0 is de Bruijn 1 under two binders.
        value: Expr::lam(
            BinderInfo::Default,
            uint64_ty(),
            Expr::lam(BinderInfo::Default, uint64_ty(), Expr::bvar(1)),
        ),
        is_reducible: true,
    })
    .expect("`pick` is a well-typed UInt64 -> UInt64 -> UInt64 definition");
    env
}

/// The serialized body as the extractor reports it: one block,
/// `_0 = move _{param+1}`, `return` — `param` is what the body actually
/// computes, the knob the mistranslation test turns.
fn extracted_pick(param: usize) -> VerifiableFunction {
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
                    rvalue: Rvalue::Use(Operand::Move(Place::local(param + 1))),
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
    }
}

#[test]
fn export_seam_bytes_decode_whole_and_readmit_against_the_same_environment() {
    // The whole I7 encode->wire->import loop at the decision level: A's export
    // seam mints bytes about the body being serialized; B decodes them and
    // readmits against (here) an identical environment. This is the positive
    // control that makes the seam's refusal tests below meaningful.
    let env = env_with_pick();
    let bytes =
        mint_encoded_digest_for_export(&env, "pick", &certified_status(), &extracted_pick(0))
            .expect("a kernel-checked projection with a faithful body must export");

    let decoded = VerdictDigest::decode(&bytes).expect("seam output must decode whole");
    assert_eq!(decoded.decl(), "pick");
    assert_eq!(
        decoded.kernel_version(),
        local_kernel_version(),
        "the seam must stamp the LINKED kernel, never a caller-supplied string"
    );
    assert!(decoded.assumptions().is_empty(), "the fixture's audited closure is empty");
    assert_eq!(decoded.carrier().arguments().len(), 2);
    assert_eq!(decoded.carrier().result().rust_carrier(), "u64");
    assert_eq!(decoded.defeq().admitted_at_rust(), "u64");

    readmit(&decoded, local_kernel_version(), &env)
        .expect("an identical-everything exported digest must readmit");
}

#[test]
fn export_seam_refuses_a_mistranslated_serialized_body() {
    // The body handed to the seam computes `y` for a definition that says `x`.
    // The seam re-earns its own Faithful against the body being SERIALIZED, so
    // this must refuse — a digest minted from the MIR-gate's earlier verdict
    // would have signed a body other than the one that travels.
    let env = env_with_pick();
    let refusal =
        mint_encoded_digest_for_export(&env, "pick", &certified_status(), &extracted_pick(1))
            .expect_err(
                "THE SEAM IS DECORATION IF THIS PASSES: it would export a certificate \
                 about a body it never re-checked",
            );
    assert_eq!(refusal.decl(), "pick");
    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect: {refusal:?}");
    assert!(
        matches!(refusal, ExportDigestRefusal::Emit(EmitRefusal::LoweringShapeMismatch { .. })),
        "expected the planned/serialized shape disagreement; got {refusal:?}"
    );
    assert!(!refusal.note().is_empty());
}

#[test]
fn export_seam_refuses_a_status_that_is_not_a_kernel_verdict() {
    let env = env_with_pick();
    let refusal =
        mint_encoded_digest_for_export(&env, "pick", &KernelStatus::Parsed, &extracted_pick(0))
            .expect_err("a parse is not a kernel verdict; there is nothing to export");
    assert!(
        matches!(refusal, ExportDigestRefusal::Mint(DigestMintRefusal::NotKernelChecked { .. })),
        "expected NotKernelChecked via the mint; got {refusal:?}"
    );
    assert!(
        refusal.is_compiler_defect(),
        "on the export path a def that minted cannot honestly lose its kernel status"
    );
    assert!(refusal.note().contains("options:"), "v7/D3: {}", refusal.note());
}

#[test]
fn export_seam_refuses_a_declaration_outside_the_emittable_fragment() {
    // A NULLARY constant is the measured outside of the fragment (every
    // `ConstantUint` probe in tests/e6-fragment-probe is defeq-rejected or
    // unproved, and the widened planner's arity-0 arm still refuses). Not
    // `double`: the fragment widened to wrapping binops while this control was
    // written, which is exactly why this test pins a shape that CANNOT enter a
    // fragment silently — a nullary def has nothing to project and no operands
    // under binders. The refusal must be the CAPABILITY family with options —
    // the same v7/D3 note the local lane gives — never a defect headline.
    let mut env = Environment::new();
    env.init_uint_arith().expect("uint arith");
    env.add_decl(clean_kernel::Declaration::Definition {
        name: Name::from_string("six"),
        level_params: vec![],
        type_: uint64_ty(),
        value: Expr::app(
            Expr::const_(Name::from_string("UInt64.ofNat"), vec![]),
            Expr::nat_lit(6),
        ),
        is_reducible: true,
    })
    .expect("`six` is admissible");

    let refusal =
        mint_encoded_digest_for_export(&env, "six", &certified_status(), &extracted_pick(0))
            .expect_err("a nullary constant is outside the measured callable fragment");
    assert!(
        matches!(refusal, ExportDigestRefusal::Emit(EmitRefusal::NotEmittable { .. })),
        "expected NotEmittable; got {refusal:?}"
    );
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is not a defect");
    assert!(refusal.note().contains("options:"), "v7/D3: {}", refusal.note());
}

#[test]
fn export_seam_discloses_assumptions_and_call_readmission_refuses_them() {
    // An assumption-bearing verdict may EXPORT (the disclosure is the product);
    // it is CALL re-admission on the importing side that must refuse. The wire
    // must carry the names through the seam unchanged.
    let env = env_with_pick();
    let status = CicKernelRecheck::held_by_kernel_recheck().kernel_checked(
        TermDigest::of_bytes(b"control-4-export-disclosure"),
        AxiomClosure::audited([Assumption::trust_marker("sorryAx").expect("named")]),
    );
    let bytes = mint_encoded_digest_for_export(&env, "pick", &status, &extracted_pick(0))
        .expect("an assumption-bearing verdict still exports — it discloses");

    let decoded = VerdictDigest::decode(&bytes).expect("decodes whole");
    let names: Vec<&str> = decoded.assumptions().iter().map(Assumption::name).collect();
    assert_eq!(names, vec!["sorryAx"], "the disclosure must survive the seam by name");

    let refusal = readmit(&decoded, local_kernel_version(), &env)
        .expect_err("an assumption-bearing certificate must not readmit to CALL");
    assert!(
        matches!(refusal, ReadmissionRefusal::AssumptionBearing { .. }),
        "expected AssumptionBearing; got {refusal:?}"
    );
}

// ---------------------------------------------------------------------------
// The positive control
// ---------------------------------------------------------------------------

#[test]
fn positive_control_the_identical_everything_digest_readmits() {
    let env = env_with_double(double_body());
    let digest = honest_digest(&env);

    let readmitted = readmit(&digest, local_kernel_version(), &env).expect(
        "A GATE THAT REFUSES EVERYTHING IS AS USELESS AS ONE THAT ADMITS \
         EVERYTHING. The identical-everything certificate must readmit; if this \
         fails, every refusal test above is testing a constant function.",
    );
    assert_eq!(readmitted.decl(), "double");
    assert_eq!(readmitted.kernel_version(), local_kernel_version());
    assert_eq!(
        readmitted.admitted_at_rust(),
        "u64",
        "re-admission is at the CARRIER type the local decision re-confirmed"
    );
}
