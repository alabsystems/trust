//! Trust (VF5): the "proved (calculus)" authority — its mint
//! (`install_calculus_row_authorities`), its grade, and its exclusion from
//! `Certified` totals until the owner's E4.7 ruling.
//!
//! The certificates come from `trust_certify::calculus_row::test_support`'s
//! stand-in VF5 family, checked through the real reference entry: the fence
//! (a certificate only from a `ReferenceAccepted` token) is the production one.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_certify::calculus_row::{self, test_support};

use super::super::*;
use super::test_vc;

fn unknown() -> VerificationResult {
    VerificationResult::Unknown {
        solver: trust_types::Symbol::intern("test"),
        time_ms: 1,
        reason: "test".to_string(),
    }
}

/// These are reporting-projection controls with the existing kernel-checked
/// stand-in family. They do not license the production VF5 base or establish
/// a source/native correspondence theorem.
#[test]
fn late_calculus_projection_preserves_unrelated_refusal_and_identity() {
    let symbol = b"_RNvCs_vf5_late_projection";
    let mut precondition = test_vc(902);
    precondition.kind = VcKind::Precondition { callee: "unrelated_callee".to_owned() };
    let mut results = vec![(test_vc(901), unknown()), (precondition, unknown())];
    let bindings = vec![None; results.len()];
    let mut authorities = vec![None; results.len()];
    let original = build_proof_results_with_runtime_checks(
        false, &results, &[], &bindings, &authorities, None,
    );
    assert_eq!(original.dispositions[ObligationId::from_usize(1)].status, TrustStatus::Failed);
    let certificate = test_support::certified_toy_row(symbol, ARTIFACT);
    calculus_row::register(certificate.clone());
    let minted = install_calculus_certificate_authorities(
        &certificate, symbol, ARTIFACT, true, &results, &mut authorities,
    );
    assert_eq!(minted, [0]);
    results[0].1 = calculus_row_result();
    let projected = calculus_pending::project_calculus_dispositions(
        &original, &results, &bindings, &authorities, &minted,
    ).expect("exact certificate row");
    assert_eq!(projected.dispositions[ObligationId::from_usize(0)].status, TrustStatus::Trusted);
    assert!(!projected.dispositions[ObligationId::from_usize(0)].certified);
    assert_eq!(projected.dispositions[ObligationId::from_usize(1)],
        original.dispositions[ObligationId::from_usize(1)]);
    assert_eq!(projected.fingerprints, original.fingerprints);
    assert_eq!(projected.premises, original.premises);
    assert_eq!(projected.summary.total, original.summary.total);
    assert_eq!(projected.summary.failed, 1, "unrelated debt never disappears");
    assert_eq!(projected.summary.max_level, original.summary.max_level);
    assert_eq!(original.summary.trusted, 0, "cached eager result was not mutated");
}

#[test]
fn late_calculus_projection_refuses_missing_stale_or_duplicate_authority() {
    let symbol = b"_RNvCs_vf5_late_projection_refusal";
    let mut results = vec![(test_vc(911), unknown())];
    let bindings = vec![None];
    let mut authorities = vec![None];
    let original = build_proof_results_with_runtime_checks(
        false, &results, &[], &bindings, &authorities, None,
    );
    results[0].1 = calculus_row_result();
    assert!(calculus_pending::project_calculus_dispositions(
        &original, &results, &bindings, &authorities, &[0],
    ).is_none(), "public label is not authority");
    let certificate = test_support::certified_toy_row(symbol, ARTIFACT);
    calculus_row::register(certificate.clone());
    assert_eq!(install_calculus_certificate_authorities(
        &certificate, symbol, ARTIFACT, true, &results, &mut authorities,
    ), [0]);
    assert!(calculus_pending::project_calculus_dispositions(
        &original, &results, &bindings, &authorities, &[0, 0],
    ).is_none(), "one private row cannot be counted twice");
    results[0].0 = test_vc(912);
    assert!(calculus_pending::project_calculus_dispositions(
        &original, &results, &bindings, &authorities, &[0],
    ).is_none(), "row drift loses the exact authority");
}

fn failed() -> VerificationResult {
    VerificationResult::Failed {
        solver: trust_types::Symbol::intern("test"),
        time_ms: 1,
        counterexample: None,
    }
}

/// The artifact the certificates in these tests are about.
const ARTIFACT: &[u8] = &[84, 82, 85, 83, 84];

/// A certificate for `symbol` over [`ARTIFACT`], recorded in this process (each
/// test uses its own symbol: the side table is process-wide).
fn recorded(symbol: &[u8]) -> calculus_row::CalculusRowCertificate {
    let certificate = test_support::certified_toy_row(symbol, ARTIFACT);
    calculus_row::register(certificate.clone());
    certificate
}

/// Mint over `results` as the pipeline does, for the body the module names
/// `symbol` in the published `artifact`: the authorities, then the calculus
/// result on every minted row.
fn mint_over(
    symbol: &[u8],
    artifact: &[u8],
    overflow_checks: bool,
    results: &mut [(VerificationCondition, VerificationResult)],
) -> (Vec<Option<ResultProofAuthority>>, Vec<usize>) {
    let mut authorities = vec![None; results.len()];
    let minted = install_calculus_row_authorities(
        symbol,
        artifact,
        overflow_checks,
        results,
        &mut authorities,
    );
    for index in &minted {
        results[*index].1 = calculus_row_result();
    }
    (authorities, minted)
}

fn mint(
    symbol: &[u8],
    results: &mut [(VerificationCondition, VerificationResult)],
) -> (Vec<Option<ResultProofAuthority>>, Vec<usize>) {
    mint_over(symbol, ARTIFACT, true, results)
}

fn dispositions(
    results: &[(VerificationCondition, VerificationResult)],
    authorities: &[Option<ResultProofAuthority>],
) -> TrustProofResults {
    build_proof_results_with_runtime_checks(
        false,
        results,
        &[],
        &vec![None; results.len()],
        authorities,
        None,
    )
}

fn vc_of(kind: VcKind, line: u32) -> VerificationCondition {
    let mut vc = test_vc(line);
    vc.kind = kind;
    vc
}

/// A certificate for the function mints `CalculusRowProved` on its unclaimed
/// L0 rows, which then read proved, `Trusted`/`Constructive`, conditional,
/// graded `proven-calculus` through the reference entry with the three VF5
/// premises, and hand out no kernel evidence.
#[test]
fn a_recorded_certificate_mints_a_trusted_calculus_row() {
    let symbol = b"_RNvCs_vf5_mint_positive";
    recorded(symbol);
    let mut results = vec![(test_vc(10), unknown()), (test_vc(11), unknown())];
    let (authorities, minted) = mint(symbol, &mut results);
    assert_eq!(minted, vec![0, 1]);
    for (index, (vc, result)) in results.iter().enumerate() {
        let authority = authorities[index].as_ref().expect("minted");
        assert!(matches!(authority, ResultProofAuthority::CalculusRowProved { .. }));
        assert!(authority.is_static_proof_for(index, vc, result, None));
        assert!(!authority.is_unconditional_static_proof_for(index, vc, result, None));
        assert!(authority.kernel_evidence_for(index, vc, None).is_none());
        assert_eq!(
            trust_disposition_for_authority(Some(authority), index, vc, result, None),
            Some((TrustStatus::Trusted, TrustProofStrength::Constructive))
        );
        let grade = trust_grade_for_row(authority, vc);
        assert_eq!(
            grade,
            trust_types::authority_grade::ObligationGrade::new(
                trust_types::authority_grade::GradeEncoding::ProvenCalculus,
                trust_types::authority_grade::GradeDischarge::KernelReferenceChecked,
                &trust_types::authority_grade::CALCULUS_ROW_PREMISES,
            )
        );
        assert!(grade.is_calculus_proved());
        assert_eq!(grade.admitted(), Ok(()));
        // Another row's VC, or another result, is not this authority's.
        assert!(!authority.matches_row(index, &test_vc(99), None));
        assert!(!authority.matches_compiler_result(&unknown()));
    }
}

/// Negative controls: no certificate recorded for the symbol, a certificate
/// about another function, a certificate the process did not record, a
/// refuted covered row, a row another lane claimed, and a row outside L0 each
/// mint nothing there.
#[test]
fn the_mint_refuses_what_the_certificate_does_not_cover() {
    let symbol = b"_RNvCs_vf5_mint_negative";
    recorded(symbol);
    let fresh = || vec![(test_vc(20), unknown()), (test_vc(21), unknown())];

    assert!(mint(b"_RNvCs_vf5_never_recorded", &mut fresh()).1.is_empty(), "no certificate");
    // The body the module names `_RNvCs_vf5_other` is not the one the recorded
    // certificate is about: the lookup is by the module's symbol for the body.
    assert!(mint(b"_RNvCs_vf5_other", &mut fresh()).1.is_empty(), "another function");
    let _unrecorded = test_support::certified_toy_row(b"_RNvCs_vf5_unrecorded", ARTIFACT);
    assert!(
        mint(b"_RNvCs_vf5_unrecorded", &mut fresh()).1.is_empty(),
        "a certificate the process did not record"
    );

    // A solver refuted one covered row: the calculus contradicts it, so nothing
    // in the function is minted.
    let mut refuted = vec![(test_vc(22), unknown()), (test_vc(23), failed())];
    assert!(mint(symbol, &mut refuted).1.is_empty());

    // A row another lane claimed keeps its authority; a postcondition row is not
    // an L0 obligation. The remaining row is minted (the control).
    let mut postcondition = test_vc(25);
    postcondition.kind = VcKind::Postcondition;
    let mut results =
        vec![(test_vc(24), unknown()), (postcondition, unknown()), (test_vc(26), unknown())];
    let mut authorities = vec![None; results.len()];
    let claimed = exact_result_row_identity(0, &results[0].0).expect("row identity");
    authorities[0] = Some(ResultProofAuthority::InterproceduralCalleeClosure { row: claimed });
    let minted =
        install_calculus_row_authorities(symbol, ARTIFACT, true, &results, &mut authorities);
    assert_eq!(minted, vec![2]);
    assert!(matches!(
        authorities[0],
        Some(ResultProofAuthority::InterproceduralCalleeClosure { .. })
    ));
    assert!(authorities[1].is_none());
    results[2].1 = calculus_row_result();
    assert!(matches!(authorities[2], Some(ResultProofAuthority::CalculusRowProved { .. })));
}

/// Review finding 1: a certificate is about one artifact. The same symbol over
/// any other bytes (a stale artifact from before the body changed, another
/// crate's module that names a function the same way) mints nothing.
/// Control: the certificate's own bytes mint.
#[test]
fn a_certificate_mints_only_over_its_own_artifact() {
    let symbol = b"_RNvCs1234_6revfoo1f";
    recorded(symbol);
    let fresh = || vec![(test_vc(50), unknown())];
    let mut stale = ARTIFACT.to_vec();
    stale[2] ^= 1;
    assert!(mint_over(symbol, &stale, true, &mut fresh()).1.is_empty(), "a changed artifact");
    assert!(mint_over(symbol, &ARTIFACT[..4], true, &mut fresh()).1.is_empty(), "truncated");
    assert!(mint_over(symbol, &[], true, &mut fresh()).1.is_empty(), "no artifact");
    assert_eq!(mint_over(symbol, ARTIFACT, true, &mut fresh()).1, vec![0], "control");
}

/// Review finding 5: only the L0 kinds `ClosedSafe` excludes are covered. An
/// unbounded allocation, a format-string row, an unmodeled construct and an
/// `Assertion` row are never minted; an overflow row only when the compile
/// checks overflow. Controls: a division-by-zero and an `Unreachable` row
/// beside them are minted, and the overflow row is with overflow checks on.
#[test]
fn the_mint_covers_only_what_closed_safe_excludes() {
    let symbol = b"_RNvCs_vf5_kinds";
    recorded(symbol);
    let overflow = VcKind::ArithmeticOverflow {
        op: BinOp::Add,
        operand_tys: (trust_types::Ty::usize(), trust_types::Ty::usize()),
    };
    let kinds = || {
        vec![
            (vc_of(VcKind::DivisionByZero, 60), unknown()),
            (vc_of(VcKind::Unreachable, 61), unknown()),
            (
                vc_of(
                    VcKind::UnboundedAllocation {
                        callee: "alloc".into(),
                        count: "n".into(),
                        detail: "d".into(),
                    },
                    62,
                ),
                unknown(),
            ),
            (
                vc_of(
                    VcKind::FormatStringViolation { callee: "printf".into(), evidence: "e".into() },
                    63,
                ),
                unknown(),
            ),
            (vc_of(VcKind::UnsupportedMir { kind: "k".into(), detail: "d".into() }, 64), unknown()),
            (vc_of(VcKind::Assertion { message: "ffi non-null".into() }, 65), unknown()),
            (vc_of(overflow.clone(), 66), unknown()),
        ]
    };
    for (vc, _) in &kinds()[2..] {
        assert!(is_strict_l0_vc_kind(&vc.kind), "each excluded kind is L0: {:?}", vc.kind);
    }
    assert_eq!(mint_over(symbol, ARTIFACT, false, &mut kinds()).1, vec![0, 1]);
    assert_eq!(mint_over(symbol, ARTIFACT, true, &mut kinds()).1, vec![0, 1, 6]);
}

/// A certificate withdrawn after the mint (two artifacts claimed the symbol)
/// authorizes nothing: the row no longer reads proved.
#[test]
fn a_withdrawn_certificate_authorizes_nothing() {
    let symbol = b"_RNvCs_vf5_withdrawn";
    recorded(symbol);
    let mut results = vec![(test_vc(30), unknown())];
    let (authorities, minted) = mint(symbol, &mut results);
    assert_eq!(minted, vec![0]);
    let authority = authorities[0].as_ref().expect("minted");
    assert!(authority.is_static_proof_for(0, &results[0].0, &results[0].1, None));
    calculus_row::register(test_support::certified_toy_row(symbol, &[9, 9]));
    assert!(calculus_row::calculus_row_certificate_for(symbol).is_none());
    assert!(!authority.is_static_proof_for(0, &results[0].0, &results[0].1, None));
    assert_eq!(
        trust_disposition_for_authority(Some(authority), 0, &results[0].0, &results[0].1, None),
        None
    );
    // Withdrawal is sticky: the original certificate registered again mints nothing.
    calculus_row::register(test_support::certified_toy_row(symbol, ARTIFACT));
    assert!(mint(symbol, &mut vec![(test_vc(31), unknown())]).1.is_empty());
}

/// Review findings 1 and 3: a body is matched to the one function the
/// published module names by its def path, and only when that function's
/// symbol resolves back to it. An ambiguous path (absent from the module's
/// `display_paths`, which removes ambiguity) or an ambiguous symbol (absent
/// from `symbols`) matches nothing. Control: the unambiguous path gives the
/// module's own symbol.
#[test]
fn a_body_is_matched_to_one_function_of_the_published_module() {
    let mut module = trust_ir::Module::new("demo");
    let ty = module
        .add_func_type(trust_ir::FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    for (index, name) in [(0u32, "_RNvCs1_4demo1f"), (1, "_RNvCs1_4demo1g")] {
        module
            .try_add_function(trust_ir::Function::new(
                trust_ir::FuncId::new(index),
                name,
                ty,
                trust_ir::BlockId::new(0),
            ))
            .expect("Module::try_add_function: test fixture");
    }
    let f = trust_ir::FuncId::new(0);
    let g = trust_ir::FuncId::new(1);
    let display_paths: BTreeMap<String, trust_ir::FuncId> =
        [("f".to_string(), f), ("g".to_string(), g)].into_iter().collect();
    let symbols: BTreeMap<String, trust_ir::FuncId> =
        [("_RNvCs1_4demo1f".to_string(), f)].into_iter().collect();
    assert_eq!(
        calculus_row_symbol_in_module("f", &display_paths, &symbols, &module).as_deref(),
        Some("_RNvCs1_4demo1f")
    );
    // `g`'s symbol is ambiguous in the module (absent from `symbols`).
    assert_eq!(calculus_row_symbol_in_module("g", &display_paths, &symbols, &module), None);
    // A path the module does not index (or indexes ambiguously).
    assert_eq!(calculus_row_symbol_in_module("h", &display_paths, &symbols, &module), None);
    // A path whose function's symbol resolves to ANOTHER function.
    let crossed: BTreeMap<String, trust_ir::FuncId> =
        [("_RNvCs1_4demo1f".to_string(), g)].into_iter().collect();
    assert_eq!(calculus_row_symbol_in_module("f", &display_paths, &crossed, &module), None);
}

/// E4.7, the exclusion: as shipped, a calculus row is `Trusted`, so a body of
/// calculus rows has a `Certified` total of 0 and licenses no elision.
/// Negative control: the same rows under the ruling taken
/// (`calculus_row_disposition(true)`) are `Certified`, so the total would
/// count them; the shipped flag is what keeps them out.
#[test]
fn calculus_row_exclusion_keeps_certified_totals_at_zero_until_e4_7() {
    let symbol = b"_RNvCs_vf5_exclusion";
    recorded(symbol);
    let mut results = vec![(test_vc(40), unknown()), (test_vc(41), unknown())];
    let (authorities, minted) = mint(symbol, &mut results);
    assert_eq!(minted.len(), 2);

    assert!(!trust_types::authority_grade::E4_7_CALCULUS_ROWS_CERTIFIED);
    let shipped = dispositions(&results, &authorities);
    assert_eq!(shipped.summary.certified, 0, "calculus rows are out of Certified totals");
    assert_eq!(shipped.summary.trusted, 2, "and counted as proved");
    assert!(shipped.dispositions.iter().all(|disposition| !disposition.certified));

    // The negative control: the ruling taken.
    assert_eq!(
        calculus_row_disposition(true),
        (TrustStatus::Certified, TrustProofStrength::Constructive)
    );
    assert_eq!(
        calculus_row_disposition(false),
        (TrustStatus::Trusted, TrustProofStrength::Constructive)
    );
    let mut flipped: IndexVec<ObligationId, TrustDisposition> = IndexVec::new();
    for disposition in shipped.dispositions.iter() {
        let (status, strength) = calculus_row_disposition(true);
        flipped.push(TrustDisposition {
            kind: disposition.kind,
            status,
            strength,
            certified: matches!(status, TrustStatus::Certified),
        });
    }
    assert_eq!(TrustFunctionSummary::from_dispositions(&flipped).certified, 2);
}
