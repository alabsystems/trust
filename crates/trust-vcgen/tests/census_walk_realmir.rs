// Trust (2026-10-11, OD-1-T3-CENSUS-WALK): D33's unsafe-operation census, pinned on
// REAL extracted MIR. The fixtures under `fixtures/census_walk/` are
//
//     trustc --edition 2021 --crate-type lib --emit=metadata -Cpanic=abort \
//            -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory census_walk.rs
//
// on stage1 of `fix3/t3-census-walker` `fcaa6855ce` (one function per file, named
// by the function; the source sits beside them). Every function projects THROUGH a
// recursive type, which the extractor spells as a bare `Ty::Datatype` marker with
// its definition in `body.datatype_defs`. Before the census walk was typed with the
// body's own place typing (`place_ty_step`), each of these bodies was refused whole
// as "a place step the type walk cannot follow" — the measured class-D shape
// (tla-cert `CaseBranch::serialize`, clean-ck0 `<Term as Hash>::hash`/`hash_kind`,
// merge-contract `visit_enum`, astream-agent `run_turn`).
//
// The unit tests in `sep_engine.rs` pin the walk on hand-written types; THESE pin
// the producer's real spelling (marker plus table entry, flat `__tag`/`__v{v}_{f}`
// enum view, `Box` as `Unique`/`NonNull`/raw pointer), so a producer change to the
// marker or table layout is caught here.
//
// Every direction is load-bearing:
//   * the four safe bodies (`Box`-recursive enum, `&`-recursive enum, `&`-recursive
//     struct, `&`-recursive enum with a tuple payload) are census-clean, under both
//     census variants;
//   * the two whose places step THROUGH a marker before their last step
//     (`node_next_val`: a struct field; `tree_pairs`: a non-final variant field,
//     `[Deref, Downcast(1), Field(0), Field(1)]`, at two marker levels) are
//     refused again ("cannot follow") with their definition table emptied: the
//     table entry, not a by-name guess, admits them.
//     `term_head` and `chain_second` stay clean without the table because every
//     marker step they take is the final `Downcast`-`Field` step the census has
//     exempted since 2026-09-29; they pin the producer shape, not the table;
//   * a union reached through a recursive struct still meets the union-field arm;
//   * a raw pointer in a variant of a recursive enum still meets the raw-deref arm
//     (variant-relative field typing, not the flat slot).
use trust_types::*;
use trust_vcgen::{
    body_has_unsafe_operation, body_has_unsafe_operation_modulo_ref_unsize,
    body_unsafe_operation_witness,
};

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/census_walk/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// The fixture's first parameter is `&<bare marker>` and the table defines that
/// marker: the producer shape this file pins. If the extractor stops spelling the
/// recursive type this way, the census assertions below would no longer test what
/// they claim to, so fail here first.
fn assert_marker_param_with_definition(func: &VerifiableFunction, marker: &str) {
    let param = func.body.locals.iter().find(|l| l.index == 1).expect("parameter _1");
    let Ty::Ref { inner, .. } = &param.ty else {
        panic!("{}: _1 is not a reference: {:?}", func.name, param.ty);
    };
    assert!(
        matches!(inner.as_ref(), Ty::Datatype { name, variants } if name == marker && variants.is_empty()),
        "{}: _1 is not `&{marker}` as a bare marker: {:?}",
        func.name,
        param.ty
    );
    assert!(
        func.body.datatype_defs.contains_key(marker),
        "{}: no table entry for `{marker}`; keys: {:?}",
        func.name,
        func.body.datatype_defs.keys().collect::<Vec<_>>()
    );
}

fn without_table(func: &VerifiableFunction) -> VerifiableFunction {
    let mut func = func.clone();
    func.body.datatype_defs.clear();
    func
}

#[test]
fn recursive_types_projected_through_are_census_clean() {
    for (name, marker) in [
        ("term_head", "census_walk::Term"),
        ("chain_second", "census_walk::Chain"),
        ("node_next_val", "census_walk::Node"),
        ("tree_pairs", "census_walk::Tree"),
    ] {
        let func = load(name);
        assert_marker_param_with_definition(&func, marker);
        assert_eq!(body_unsafe_operation_witness(&func, false), None, "{name}");
        assert_eq!(body_unsafe_operation_witness(&func, true), None, "{name}");
        assert!(!body_has_unsafe_operation(&func), "{name}");
        assert!(!body_has_unsafe_operation_modulo_ref_unsize(&func), "{name}");
    }
}

#[test]
fn without_the_definition_table_the_same_bodies_stay_refused() {
    for name in ["node_next_val", "tree_pairs"] {
        let func = without_table(&load(name));
        assert_eq!(
            body_unsafe_operation_witness(&func, false),
            Some("a place step the type walk cannot follow"),
            "{name}"
        );
        assert!(body_has_unsafe_operation(&func), "{name}");
        assert!(body_has_unsafe_operation_modulo_ref_unsize(&func), "{name}");
    }
}

#[test]
fn a_union_behind_a_recursive_struct_is_still_an_unsafe_operation() {
    let func = load("unode_next_bits");
    assert_marker_param_with_definition(&func, "census_walk::UNode");
    assert_eq!(body_unsafe_operation_witness(&func, false), Some("a union field access"));
    assert_eq!(body_unsafe_operation_witness(&func, true), Some("a union field access"));
    assert!(body_has_unsafe_operation(&func));
    assert!(body_has_unsafe_operation_modulo_ref_unsize(&func));
}

#[test]
fn a_raw_pointer_variant_of_a_recursive_enum_is_still_an_unsafe_operation() {
    let func = load("raw_chain_second");
    assert_marker_param_with_definition(&func, "census_walk::RawChain");
    assert_eq!(
        body_unsafe_operation_witness(&func, false),
        Some("a dereference of a raw pointer (or of a non-reference)")
    );
    assert!(body_has_unsafe_operation(&func));
    assert!(body_has_unsafe_operation_modulo_ref_unsize(&func));
}
