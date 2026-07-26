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
