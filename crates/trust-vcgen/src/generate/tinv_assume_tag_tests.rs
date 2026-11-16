//! TINV step 10.1: the type-invariant assumption tag (`trust_types::type_invariant_assume_tag`)
//! survives the vcgen version-token grammar byte for byte.
//!
//! The generator spells versions and sentinels into names after a `#` (`n#s1_0`, `n#e`,
//! `n#pre_s2_0`, `n#tinvu_s3`), and dozens of helpers split names on it. A tag is
//! conjoined BARE (`And([Var(tag, Bool), I])`) and the mint compares the tags it finds in a
//! row's formula with the tags the use site installed, so a renamer, a seal or a tie that
//! re-spelled a tag would break the disclosure channel. The tag has no `#`, `:`, `.` or `*`
//! by construction (trust-types `tinv_assume_tags.rs`); this file checks the consequence on
//! the real helpers and on a whole generation, at every program point of a real-MIR body.
use proptest::prelude::*;
use trust_types::{
    BlockId, Formula, Sort, TINV_ASSUME_TAG_PREFIX, VerifiableFunction, type_invariant_assume_tag,
};

use super::{
    conjoin_preconditions_versioned_at_point_recorded, entry_sentinel_ties_for_exempt_facts,
    seal_bare_reads, version_rename_at,
};

fn load() -> VerifiableFunction {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/tinv_mut_pointee_entry_rename_mir.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("deserialize")
}

/// Every program point `(block, k)` of `func`, the terminal included.
fn points(func: &VerifiableFunction) -> Vec<(BlockId, usize)> {
    func.body.blocks.iter().flat_map(|b| (0..=b.stmts.len()).map(move |k| (b.id, k))).collect()
}

/// The use-site fact shape over names the body versions (`self*.1` is written at bb2[0]).
fn fact(tag: &str) -> Formula {
    Formula::And(vec![
        Formula::Var(tag.to_string(), Sort::Bool),
        Formula::Le(
            Box::new(Formula::Var("self*.1".into(), Sort::Int)),
            Box::new(Formula::Var("self*.0".into(), Sort::Int)),
        ),
    ])
}

/// The tag-prefixed names of `f`, each with its sort.
fn tag_names(f: &Formula) -> Vec<(String, Sort)> {
    let mut out = Vec::new();
    f.visit(&mut |n| {
        if let Formula::Var(name, sort) = n
            && name.starts_with(TINV_ASSUME_TAG_PREFIX)
        {
            out.push((name.clone(), sort.clone()));
        }
    });
    out
}

fn check_helpers(func: &VerifiableFunction, tag: &str) {
    let sv = super::stmt_versions_for(func);
    let bare = Formula::Var(tag.to_string(), Sort::Bool);
    assert!(!sv.ever_versioned(func, tag), "{tag} is versioned somewhere");
    for (block, k) in points(func) {
        assert_eq!(sv.version_token_at(func, block, k, tag), None, "{tag} at {block:?}[{k}]");
        assert_eq!(version_rename_at(&bare, &sv, func, block, k), bare, "rename at {block:?}[{k}]");
        assert_eq!(
            seal_bare_reads(&sv, func, block, k, bare.clone()),
            Some(bare.clone()),
            "seal at {block:?}[{k}]"
        );
        // The fact's place names ARE re-versioned (the point of the test is that the tag
        // beside them is not).
        let renamed = version_rename_at(&fact(tag), &sv, func, block, k);
        assert_eq!(tag_names(&renamed), vec![(tag.to_string(), Sort::Bool)]);
        let sealed = seal_bare_reads(&sv, func, block, k, renamed.clone()).expect("no collision");
        assert_eq!(tag_names(&sealed), vec![(tag.to_string(), Sort::Bool)]);
        let ties = entry_sentinel_ties_for_exempt_facts(
            func,
            &sv,
            block,
            k,
            std::slice::from_ref(&sealed),
            &Formula::Bool(true),
        );
        assert!(ties.iter().all(|t| tag_names(t).is_empty()), "a tie names the tag: {ties:?}");
        // The entry channel keeps the tag bare whatever it renames around it.
        let (formula, kept) = conjoin_preconditions_versioned_at_point_recorded(
            func,
            block,
            k,
            &[fact(tag)],
            &Default::default(),
            Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("self*.1".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
        );
        assert_eq!(tag_names(&formula), vec![(tag.to_string(), Sort::Bool)], "{formula:?}");
        assert!(kept.contains(&fact(tag)), "{kept:?}");
    }
}

#[test]
fn the_tag_passes_every_version_helper_unchanged_at_every_point() {
    let func = load();
    for (path, id) in [("a::S", 0u32), ("a::S", 1), ("a::S#e", 0), ("self*.1", 7)] {
        check_helpers(&func, &type_invariant_assume_tag(path, id));
    }
}

/// A whole generation: the tagged fact rides in as a precondition through every pass of
/// the safety walk (path defs, the entry conjoin and its rename, guards, the type-range
/// battery, the final SSA-token normalize), and every row that carries a tag carries it
/// exactly, Bool-sorted.
#[test]
fn a_whole_generation_carries_the_tag_byte_identically() {
    let mut func = load();
    let tag = type_invariant_assume_tag("a::S", 0);
    func.preconditions = vec![fact(&tag)];
    let vcs = crate::generate_vcs(&func);
    let mut carried = 0usize;
    for vc in &vcs {
        let names = tag_names(&vc.formula);
        carried += usize::from(!names.is_empty());
        for (name, sort) in names {
            assert_eq!((name.as_str(), &sort), (tag.as_str(), &Sort::Bool), "{:?}", vc.kind);
        }
        if let trust_types::TinvTagScan::Tags(found) = vc.type_invariant_tags() {
            assert_eq!(found.into_iter().collect::<Vec<_>>(), vec![tag.clone()]);
            assert!(vc.kernel_authority_refusal().is_some());
        }
    }
    assert!(carried > 0, "no row carried the precondition: the test would be vacuous");
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, ..ProptestConfig::default() })]

    /// Over arbitrary def paths (including the separators themselves) and ids, the tag
    /// spelling has no grammar character and passes every helper unchanged.
    #[test]
    fn any_tag_passes_the_version_grammar(path in "[a-zA-Z0-9_:#.*$ ]{0,24}", id in any::<u32>()) {
        let tag = type_invariant_assume_tag(&path, id);
        prop_assert!(!tag.contains(['#', ':', '.', '*']), "{}", tag);
        let func = load();
        check_helpers(&func, &tag);
    }
}
