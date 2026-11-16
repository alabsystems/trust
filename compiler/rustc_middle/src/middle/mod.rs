pub mod codegen_fn_attrs;
pub mod dead_code;
pub mod debugger_visualizer;
pub mod deduced_param_attrs;
pub mod dependency_format;
pub mod exported_symbols;
pub mod lang_items;
pub mod lib_features {
    use rustc_data_structures::unord::UnordMap;
    use rustc_macros::{BlobDecodable, Encodable, StableHash};
    use rustc_span::{Span, Symbol};

    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    #[derive(StableHash, Encodable, BlobDecodable)]
    pub enum FeatureStability {
        AcceptedSince(Symbol),
        Unstable { old_name: Option<Symbol> },
    }

    #[derive(StableHash, Debug, Default)]
    pub struct LibFeatures {
        pub stability: UnordMap<Symbol, (FeatureStability, Span)>,
    }

    impl LibFeatures {
        pub fn to_sorted_vec(&self) -> Vec<(Symbol, FeatureStability)> {
            self.stability
                .to_sorted_stable_ord()
                .iter()
                .map(|&(&sym, &(stab, _))| (sym, stab))
                .collect()
        }
    }
}
pub mod privacy;
pub mod region;
pub mod resolve;
pub mod resolve_bound_vars;
pub mod stability;
// Trust: cross-crate PROOF-position citation, increment 2 — the transport
// manifest that rides beside a crate's `clean { … }` island sources.
pub mod trust_clean_proof;
// Trust: step 2 increment 6 (6.2) — the trust-ir rmeta carrier types.
pub mod trust_ir_entry;
// Trust: CB4 — identify the items rustc's libtest harness synthesizes by
// expansion provenance (never by name or by the forgeable attribute alone).
pub mod trust_test_harness;
