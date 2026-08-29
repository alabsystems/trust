use rustc_hir::def_id::LOCAL_CRATE;
use rustc_hir::definitions::{DefPath, DefPathData, DisambiguatedDefPathData};
use rustc_span::sym;

use super::{trust_spec_contract_builtin_name_from_symbols, trust_spec_contract_def_path_matches};

#[test]
fn trust_spec_contract_names_require_exact_trust_namespace() {
    assert_eq!(
        trust_spec_contract_builtin_name_from_symbols(sym::trust, sym::requires),
        Some((sym::requires, sym::trust_contracts_requires))
    );
    assert_eq!(
        trust_spec_contract_builtin_name_from_symbols(sym::trust, sym::ensures),
        Some((sym::ensures, sym::trust_contracts_ensures))
    );
    assert_eq!(trust_spec_contract_builtin_name_from_symbols(sym::other, sym::requires), None);
}

/// Trust (D4): `trust::decreases` reaches a compiler-owned builtin.
///
/// Without this mapping the attribute reached no builtin, trust-spec exported
/// no such proc macro, and a crate that linked the compat shim got E0433 for a
/// clause that verifies with exactly native semantics on both the first-class
/// and `register_tool(trust)` surfaces. The compat surface DELETED a working
/// clause, so a dual-building crate could not state a termination measure at
/// all.
#[test]
fn trust_spec_decreases_maps_to_the_native_desugaring_builtin() {
    assert_eq!(
        trust_spec_contract_builtin_name_from_symbols(sym::trust, sym::decreases),
        Some((sym::decreases, sym::trust_contracts_decreases))
    );
    // Namespace discipline is unchanged: only the reserved `trust` namespace
    // is intercepted.
    assert_eq!(trust_spec_contract_builtin_name_from_symbols(sym::other, sym::decreases), None);
}

/// Trust (D4): the interception keys on the RESOLVED def, so every spelling
/// that resolves to trust-spec's crate-root `decreases` gets the builtin —
/// `use trust::decreases as measure`, `#[::trust::decreases]`, a Cargo package
/// rename. This is the same rename-resistance the requires/ensures fail-open
/// post-mortem paid for once.
#[test]
fn trust_spec_decreases_def_path_must_be_crate_root_proc_macro() {
    let decreases = sym::decreases;
    let root = DefPath {
        krate: LOCAL_CRATE,
        data: vec![DisambiguatedDefPathData {
            data: DefPathData::MacroNs(decreases),
            disambiguator: 0,
        }],
    };
    let nested = DefPath {
        krate: LOCAL_CRATE,
        data: vec![
            DisambiguatedDefPathData { data: DefPathData::TypeNs(sym::nested), disambiguator: 0 },
            DisambiguatedDefPathData { data: DefPathData::MacroNs(decreases), disambiguator: 0 },
        ],
    };
    let disambiguated = DefPath {
        krate: LOCAL_CRATE,
        data: vec![DisambiguatedDefPathData {
            data: DefPathData::MacroNs(decreases),
            disambiguator: 1,
        }],
    };

    assert!(trust_spec_contract_def_path_matches(&root, decreases));
    assert!(!trust_spec_contract_def_path_matches(&nested, decreases));
    assert!(!trust_spec_contract_def_path_matches(&disambiguated, decreases));
}

/// Trust: `invariant` must map, and must map to the REFUSAL builtin.
///
/// The mapping is what makes the refusal reachable at all. While `invariant`
/// was absent from this table the resolver installed no builtin, trust-spec's
/// passthrough proc macro ran, and the annotation was erased with no
/// diagnostic — MEASURED bit-identical obligation sets with and without the
/// attribute. If this test starts failing because someone removed the arm, the
/// silent erasure is back.
#[test]
fn trust_spec_invariant_maps_to_the_refusal_builtin() {
    assert_eq!(
        trust_spec_contract_builtin_name_from_symbols(sym::trust, sym::invariant),
        Some((sym::invariant, sym::trust_contracts_invariant))
    );
    // Namespace check applies to `invariant` exactly as to its siblings: an
    // unrelated crate's `invariant` attribute must not be captured.
    assert_eq!(trust_spec_contract_builtin_name_from_symbols(sym::other, sym::invariant), None);
}

/// Trust (D4 SUPERSEDES D1, integration 2026-08-27): D1 shipped a test named
/// `trust_spec_decreases_is_not_mapped` asserting the OPPOSITE of the two D4
/// tests above. Its stated reason was that any mapping "would create a SECOND
/// silent erasure of exactly the kind this lane removed". That reason is sound
/// for a PASSTHROUGH and does not hold for a DESUGARING: `ExpandTrustDecreases`
/// replaces the proc macro before expansion and re-emits the native clause
/// spelling verbatim, so there is nothing left to erase. The D1 test was
/// DELETED here rather than ignored, because leaving two contradictory
/// assertions in one file is how a surface acquires two implementations.
//
// (no test body: the assertion it made is now made in the negative by the two
// D4 tests above, which require the mapping to EXIST.)

#[test]
fn trust_spec_contract_def_path_must_be_crate_root_proc_macro() {
    let requires = sym::requires;
    let root_requires = DefPath {
        krate: LOCAL_CRATE,
        data: vec![DisambiguatedDefPathData {
            data: DefPathData::MacroNs(requires),
            disambiguator: 0,
        }],
    };
    let nested_requires = DefPath {
        krate: LOCAL_CRATE,
        data: vec![
            DisambiguatedDefPathData { data: DefPathData::TypeNs(sym::nested), disambiguator: 0 },
            DisambiguatedDefPathData { data: DefPathData::MacroNs(requires), disambiguator: 0 },
        ],
    };
    let disambiguated_requires = DefPath {
        krate: LOCAL_CRATE,
        data: vec![DisambiguatedDefPathData {
            data: DefPathData::MacroNs(requires),
            disambiguator: 1,
        }],
    };

    assert!(trust_spec_contract_def_path_matches(&root_requires, requires));
    assert!(!trust_spec_contract_def_path_matches(&nested_requires, requires));
    assert!(!trust_spec_contract_def_path_matches(&disambiguated_requires, requires));
}

/// Trust: the `invariant` refusal keys on the RESOLVED DEF, not the spelling.
///
/// This is the rename-resistance property. Because the decision is made on the
/// def path of the resolved proc macro, `use trust::invariant as inv;`,
/// `#[::trust::invariant(..)]` and a Cargo package rename all reach the same
/// refusal. Keying on the literal `trust::invariant` spelling is the exact bug
/// the comment in `trust_spec_contract_attr_extension` records as already paid
/// for once with `requires`/`ensures`: every other spelling fell through to the
/// passthrough and compiled clean while never being verified.
#[test]
fn trust_spec_invariant_def_path_must_be_crate_root_proc_macro() {
    let invariant = sym::invariant;
    let root_invariant = DefPath {
        krate: LOCAL_CRATE,
        data: vec![DisambiguatedDefPathData {
            data: DefPathData::MacroNs(invariant),
            disambiguator: 0,
        }],
    };
    let nested_invariant = DefPath {
        krate: LOCAL_CRATE,
        data: vec![
            DisambiguatedDefPathData { data: DefPathData::TypeNs(sym::nested), disambiguator: 0 },
            DisambiguatedDefPathData { data: DefPathData::MacroNs(invariant), disambiguator: 0 },
        ],
    };

    assert!(trust_spec_contract_def_path_matches(&root_invariant, invariant));
    assert!(!trust_spec_contract_def_path_matches(&nested_invariant, invariant));
}
