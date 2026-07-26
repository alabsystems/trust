// trust-js-certify-bridge — M3 D2 acceptance: kernel-certified JS builtins.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::Expr;
use trust_certify::finite_dfa::{
    certify_finite_sim, enum_cases_refl_proof, enum_transition_body, FiniteSimSpec, SimFlavor,
};
use trust_ir::ProofEvidence;

use trust_js_certify_bridge::{
    ascii_domain, certify_encuri_unreserved_ascii, certify_hexval_ascii, certify_tolowercase_ascii,
    certify_touppercase_ascii, certify_whitespace_ascii, extract_interp_encuri_unreserved_table,
    extract_interp_hexval_table, extract_interp_lowercase_table, extract_interp_uppercase_table,
    extract_interp_whitespace_table, node_encuri_unreserved_table, node_hexval_table,
    node_lowercase_table, node_uppercase_table, node_whitespace_table, table_checksum,
    CertifiedBuiltin, ASCII_DOMAIN, ASSURANCE_TIER, ENCURI_UNRESERVED_ASCII_TRANSCRIPTION,
    ENCURI_UNRESERVED_TRANSCRIPTION_SHA256, HEXVAL_ASCII_TRANSCRIPTION, HEXVAL_NOT_A_DIGIT,
    HEXVAL_TRANSCRIPTION_SHA256, TOLOWER_ASCII_TRANSCRIPTION, TOUPPER_ASCII_TRANSCRIPTION,
    TOUPPER_TRANSCRIPTION_SHA256, TRANSCRIPTION_SHA256, WHITESPACE_ASCII_TRANSCRIPTION,
    WHITESPACE_TRANSCRIPTION_SHA256,
};

/// One certified-builtin case, wired to its public API.
struct Case {
    name: &'static str,
    certify: fn() -> Result<Option<CertifiedBuiltin>, String>,
    extract: fn() -> Result<[u8; ASCII_DOMAIN], String>,
    node: fn() -> Result<[u8; ASCII_DOMAIN], String>,
    transcription: [u8; ASCII_DOMAIN],
    pinned_sha: &'static str,
}

fn tolower_case() -> Case {
    Case {
        name: "toLowerCase",
        certify: certify_tolowercase_ascii,
        extract: extract_interp_lowercase_table,
        node: node_lowercase_table,
        transcription: TOLOWER_ASCII_TRANSCRIPTION,
        pinned_sha: TRANSCRIPTION_SHA256,
    }
}

fn toupper_case() -> Case {
    Case {
        name: "toUpperCase",
        certify: certify_touppercase_ascii,
        extract: extract_interp_uppercase_table,
        node: node_uppercase_table,
        transcription: TOUPPER_ASCII_TRANSCRIPTION,
        pinned_sha: TOUPPER_TRANSCRIPTION_SHA256,
    }
}

fn whitespace_case() -> Case {
    Case {
        name: "trim-whitespace",
        certify: certify_whitespace_ascii,
        extract: extract_interp_whitespace_table,
        node: node_whitespace_table,
        transcription: WHITESPACE_ASCII_TRANSCRIPTION,
        pinned_sha: WHITESPACE_TRANSCRIPTION_SHA256,
    }
}

fn hexval_case() -> Case {
    Case {
        name: "uri-decode-hexval",
        certify: certify_hexval_ascii,
        extract: extract_interp_hexval_table,
        node: node_hexval_table,
        transcription: HEXVAL_ASCII_TRANSCRIPTION,
        pinned_sha: HEXVAL_TRANSCRIPTION_SHA256,
    }
}

fn encuri_unreserved_case() -> Case {
    Case {
        name: "encodeuricomponent-unreserved",
        certify: certify_encuri_unreserved_ascii,
        extract: extract_interp_encuri_unreserved_table,
        node: node_encuri_unreserved_table,
        transcription: ENCURI_UNRESERVED_ASCII_TRANSCRIPTION,
        pinned_sha: ENCURI_UNRESERVED_TRANSCRIPTION_SHA256,
    }
}

fn cells(t: &[u8; ASCII_DOMAIN]) -> Vec<Expr> {
    t.iter().map(|&b| Expr::nat_lit(u64::from(b))).collect()
}

/// The full acceptance sweep for one builtin:
/// (i) checksum pinned, (iii) extracted == transcription 128/128,
/// (iv) interp trace-equal to Node 128/128, (ii) Some(CleanCic) + kernel
/// re-check, honest tier + emitted certificate.
fn run_full(case: &Case) {
    // (i) transcription checksum is pinned.
    assert_eq!(
        table_checksum(&case.transcription),
        case.pinned_sha,
        "[{}] transcription edited without re-pinning its SHA-256",
        case.name
    );

    // (iii) the interpreter's extracted table equals the transcription on all
    // 128 cells (no interp bug, no transcription error).
    let extracted = (case.extract)().unwrap_or_else(|e| panic!("[{}] extract: {e}", case.name));
    for i in 0..ASCII_DOMAIN {
        assert_eq!(
            extracted[i], case.transcription[i],
            "[{}] interp disagrees with transcription at code point {i}: interp={} transcription={}",
            case.name, extracted[i], case.transcription[i]
        );
    }

    // (iv) behavioural cross-check: interp trace-equal to Node on all 128 cells.
    let node = (case.node)().unwrap_or_else(|e| panic!("[{}] node: {e}", case.name));
    for i in 0..ASCII_DOMAIN {
        assert_eq!(
            extracted[i], node[i],
            "[{}] interp vs Node divergence at code point {i}: interp={} node={}",
            case.name, extracted[i], node[i]
        );
    }

    // (ii) the KERNEL CHECK PASSES — a real CleanCic receipt, not a stub.
    let certified = (case.certify)()
        .unwrap_or_else(|e| panic!("[{}] extract: {e}", case.name))
        .unwrap_or_else(|| panic!("[{}] kernel check must pass and mint a CleanCic", case.name));

    match &certified.evidence {
        ProofEvidence::CleanCic { term, context, lineage, .. } => {
            assert!(!term.is_empty(), "[{}] proof term must be non-empty", case.name);
            assert!(!context.is_empty(), "[{}] serialized context non-empty", case.name);
            assert_ne!(
                *lineage,
                trust_ir::ProofDigest::zero(),
                "[{}] lineage digest must bind the obligation",
                case.name
            );
        }
        other => panic!("[{}] expected CleanCic, got {other:?}", case.name),
    }
    assert!(certified.recheck(), "[{}] minted receipt must re-check through the kernel", case.name);

    // Honest tier + a passing kernel check are recorded in the certificate.
    let cert = certified.to_certificate();
    assert_eq!(cert.assurance_tier, ASSURANCE_TIER, "[{}] tier verbatim", case.name);
    assert!(!cert.assurance_tier.contains("refines ECMA-262"), "[{}] no over-claim", case.name);
    assert!(cert.kernel_check.passed, "[{}] cert records passing kernel check", case.name);
    assert_eq!(cert.transcription_sha256, case.pinned_sha, "[{}] cert checksum", case.name);
    assert_eq!(cert.extracted_table, case.transcription.to_vec(), "[{}] cert extracted", case.name);
    assert_eq!(
        cert.obligation.lineage_sha256, cert.clean_cic.lineage_sha256,
        "[{}] obligation/receipt lineage agree",
        case.name
    );

    // Emit the committed artifact and round-trip it.
    let path =
        certified.emit_certificate().unwrap_or_else(|e| panic!("[{}] emit: {e}", case.name));
    let back: trust_js_certify_bridge::BuiltinCertificate =
        serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).expect("re-read cert");
    assert_eq!(back.assurance_tier, ASSURANCE_TIER);
    assert!(back.kernel_check.passed);
}

/// SOUNDNESS negative control: perturbing one transcription cell so the
/// interpreter genuinely disagrees makes the kernel re-check fail closed.
fn assert_one_wrong_cell_fails(case: &Case) {
    let domain = ascii_domain();
    let extracted = (case.extract)().unwrap();

    let mut wrong = case.transcription;
    // Flip cell 0 to a guaranteed-different value; the interpreter still reduces
    // to `extracted[0]`, so the claimed cell can no longer be discharged.
    wrong[0] = extracted[0].wrapping_add(1);
    assert_ne!(wrong[0], extracted[0], "[{}] perturbed cell must differ", case.name);

    let impl_def = enum_transition_body(&domain, &cells(&extracted)).unwrap();
    let spec_def = enum_transition_body(&domain, &cells(&wrong)).unwrap();
    let proof = enum_cases_refl_proof(&domain, &cells(&wrong)).unwrap();
    let term = clean_auto::bridge::ay_contract::serialize_term(&proof).unwrap();

    let spec = FiniteSimSpec {
        label: format!("trust-js.{}.NEGATIVE-CONTROL", case.name),
        flavor: SimFlavor::EnumCases { domain, impl_def, spec_def },
    };
    assert!(
        certify_finite_sim(&spec, &term).is_none(),
        "[{}] a single disagreeing cell must fail the kernel re-check",
        case.name
    );
}

// ── per-builtin acceptance ────────────────────────────────────────────────────

#[test]
fn tolowercase_certifies_and_cross_checks() {
    run_full(&tolower_case());
}

#[test]
fn touppercase_certifies_and_cross_checks() {
    run_full(&toupper_case());
}

#[test]
fn whitespace_predicate_certifies_and_cross_checks() {
    run_full(&whitespace_case());
}

#[test]
fn hexval_certifies_and_cross_checks() {
    run_full(&hexval_case());
}

#[test]
fn encuri_unreserved_certifies_and_cross_checks() {
    run_full(&encuri_unreserved_case());
}

// ── shared soundness + honesty ────────────────────────────────────────────────

#[test]
fn all_builtins_fail_closed_on_one_wrong_cell() {
    for case in [
        tolower_case(),
        toupper_case(),
        whitespace_case(),
        hexval_case(),
        encuri_unreserved_case(),
    ] {
        assert_one_wrong_cell_fails(&case);
    }
}

#[test]
fn assurance_tier_is_honest() {
    assert!(ASSURANCE_TIER.contains("OUR TRANSCRIPTION"));
    assert!(ASSURANCE_TIER.contains("kernel-checked"));
    assert!(!ASSURANCE_TIER.contains("refines ECMA-262"));
}

#[test]
fn ascii_domain_is_128_nullary_ctors() {
    let d = ascii_domain();
    assert_eq!(d.num_params, 0);
    assert_eq!(d.types.len(), 1);
    assert_eq!(d.types[0].constructors.len(), ASCII_DOMAIN);
}

#[test]
fn transcriptions_encode_the_ecma_rules() {
    // toLowerCase: A->a, Z->z, identity elsewhere.
    assert_eq!(TOLOWER_ASCII_TRANSCRIPTION[0x41], 0x61);
    assert_eq!(TOLOWER_ASCII_TRANSCRIPTION[0x5A], 0x7A);
    assert_eq!(TOLOWER_ASCII_TRANSCRIPTION[0x40], 0x40);
    // toUpperCase: a->A, z->Z, identity elsewhere.
    assert_eq!(TOUPPER_ASCII_TRANSCRIPTION[0x61], 0x41);
    assert_eq!(TOUPPER_ASCII_TRANSCRIPTION[0x7A], 0x5A);
    assert_eq!(TOUPPER_ASCII_TRANSCRIPTION[0x60], 0x60);
    // whitespace predicate: exactly {0x09,0x0A,0x0B,0x0C,0x0D,0x20} are 1.
    let ones: Vec<usize> =
        (0..ASCII_DOMAIN).filter(|&i| WHITESPACE_ASCII_TRANSCRIPTION[i] == 1).collect();
    assert_eq!(ones, vec![0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20]);
    // hex-digit value: '0'->0, '9'->9, 'A'/'a'->10, 'F'/'f'->15; sentinel 16
    // for every non-HexDigit ('G', 'g', ':', '/' just outside the ranges, etc.).
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x30], 0); // '0'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x39], 9); // '9'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x41], 10); // 'A'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x46], 15); // 'F'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x61], 10); // 'a'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x66], 15); // 'f'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x47], HEXVAL_NOT_A_DIGIT); // 'G'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x67], HEXVAL_NOT_A_DIGIT); // 'g'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x2f], HEXVAL_NOT_A_DIGIT); // '/'
    assert_eq!(HEXVAL_ASCII_TRANSCRIPTION[0x3a], HEXVAL_NOT_A_DIGIT); // ':'
    // exactly the 22 HexDigit code points carry a real value.
    let digits: Vec<usize> =
        (0..ASCII_DOMAIN).filter(|&i| HEXVAL_ASCII_TRANSCRIPTION[i] != HEXVAL_NOT_A_DIGIT).collect();
    assert_eq!(digits.len(), 22);
}

#[test]
fn encuri_unreserved_transcription_is_exactly_the_unreserved_set() {
    // The uriUnescaped set (uriAlpha ∪ DecimalDigit ∪ uriMark) intersected with
    // ASCII, computed independently here from the ECMA-262 §19.2.6.4 character
    // classes, must be EXACTLY the code points the transcription marks `1`.
    let mut expected = std::collections::BTreeSet::new();
    for c in 0x41u8..=0x5A {
        expected.insert(c as usize); // A-Z
    }
    for c in 0x61u8..=0x7A {
        expected.insert(c as usize); // a-z
    }
    for c in 0x30u8..=0x39 {
        expected.insert(c as usize); // 0-9
    }
    for c in [b'-', b'_', b'.', b'!', b'~', b'*', b'\'', b'(', b')'] {
        expected.insert(c as usize); // uriMark: - _ . ! ~ * ' ( )
    }
    // 26 + 26 + 10 + 9 = 71 unreserved code points.
    assert_eq!(expected.len(), 71);

    for i in 0..ASCII_DOMAIN {
        let want = u8::from(expected.contains(&i));
        assert_eq!(
            ENCURI_UNRESERVED_ASCII_TRANSCRIPTION[i], want,
            "encodeURIComponent unreserved predicate wrong at code point {i} \
             (0x{i:02x}): got {} want {want}",
            ENCURI_UNRESERVED_ASCII_TRANSCRIPTION[i]
        );
    }
    // And the codomain is strictly boolean.
    assert!(ENCURI_UNRESERVED_ASCII_TRANSCRIPTION.iter().all(|&b| b == 0 || b == 1));
    // Spot-check a few escaped code points are 0: space, %, /, reserved chars.
    for esc in [0x20usize, 0x25, 0x2f, 0x3b, 0x3f, 0x40, 0x23, 0x00, 0x7f] {
        assert_eq!(ENCURI_UNRESERVED_ASCII_TRANSCRIPTION[esc], 0, "0x{esc:02x} must escape");
    }
}
