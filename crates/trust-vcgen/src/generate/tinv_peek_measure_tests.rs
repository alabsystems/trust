//! MEASUREMENT (2026-10-06, TINV P1 `peek` lemma design, diagnosis item 7): inside the
//! REAL `peek` body of `tests/fixtures/tinv_p1_json_parser_fx.json`
//!
//! ```text
//! bb0: StorageLive(_2); StorageLive(_3); _5 = copy (*_1).0; _3 = &(*_5);
//!      StorageLive(_4); _4 = copy (*_1).1;
//!      _2 = <[u8]>::get::<usize>(move _3, move _4) -> bb1
//! bb1: StorageDead(_4); StorageDead(_3); _0 = Option::<&u8>::copied(move _2) -> bb2
//! bb2: StorageDead(_2); Return                         (_1: &P, P { b: &[u8], i: usize })
//! ```
//!
//! (a) do `self*.1` and `self*.0__slice_len` keep their entry versions across `get` and
//! `copied`, and what does each call havoc; (b) do the slice-length ties
//! `_3__slice_len == _5__slice_len == self*.0__slice_len` exist at the `get` call, and at
//! which versions. Observed values are pinned; a pin that flips means the walk changed,
//! not that this file is wrong.

use trust_types::Sort;

use super::*;
use crate::generate::path_defs::{
    TermHavoc, escape_havoc, func_has_pointer_laundering, function_havoc_names,
    protected_private_mut_param, terminator_def_names_structured,
};
use crate::type_invariant::obligations::{TinvPointRow, TinvStateSpec, sigma_of_root};
use crate::type_invariant::{TinvType, candidate};

const FIXTURE: &str = include_str!("../../tests/fixtures/tinv_p1_json_parser_fx.json");
const PEEK: &str = "tinvp1::P::<'_>::peek";

#[derive(serde::Deserialize)]
struct InventoryRow {
    func: VerifiableFunction,
}

fn all() -> Vec<VerifiableFunction> {
    let rows: Vec<InventoryRow> = serde_json::from_str(FIXTURE).expect("fixture bundle");
    rows.into_iter().map(|r| r.func).collect()
}

fn peek() -> VerifiableFunction {
    all().into_iter().find(|f| f.def_path == PEEK).expect("peek is in the inventory")
}

fn int(name: &str) -> Formula {
    Formula::var_owned(name.into(), Sort::Int)
}

/// Every `Var` name in `f`, sorted and deduplicated.
fn vars(f: &Formula) -> Vec<String> {
    let mut out = Vec::new();
    f.visit(&mut |n| {
        if let Formula::Var(name, _) = n {
            out.push(name.clone());
        }
    });
    out.sort();
    out.dedup();
    out
}

fn havoc_kind(h: &TermHavoc) -> &'static str {
    match h {
        TermHavoc::None => "None",
        TermHavoc::Function => "Function",
        TermHavoc::Refined(_) => "Refined",
        TermHavoc::Escape(_) => "Escape",
    }
}

// ---------------------------------------------------------------------------------------
// (a) the call havoc and the version oracle
// ---------------------------------------------------------------------------------------

#[test]
fn peek_call_havoc_is_dest_only_and_self_keeps_its_entry_version() {
    let f = peek();
    // The shape the claims are about.
    let term = |b: usize| format!("{:?}", f.body.blocks[b].terminator);
    assert!(term(0).contains("get::<usize>") && term(1).contains("copied"), "{f:#?}");
    assert!(matches!(f.body.blocks[2].terminator, Terminator::Return));

    // The walk's scope (tinv_check_rows): no callee write sets.
    let _ws = callee_write_set::enter_callee_write_sets(None);

    // WHY none of `*self`'s OWN bytes is havocked: the whole-function havoc list of `peek` is
    // EMPTY. It is built from `&mut`/`&raw` borrow targets plus locals whose type holds a
    // mutable reference or raw pointer; `peek` has neither (`_1: &P`, `P { &[u8], usize }`,
    // `_3/_5: &[u8]`, `_2: Option<&u8>`). So no call havocs anything but its own
    // destination and the stored-reference names below, whichever arm (`arg_grants_no_write` + `escape_havoc`, or the full arm
    // with its 13b / TRUST-10 refinements) decides it. Rule (b)
    // (`protected_private_mut_param`) is never consulted for `_1`: it is not `&mut`.
    assert!(function_havoc_names(&f).is_empty(), "{:?}", function_havoc_names(&f));
    assert!(!protected_private_mut_param(&f, 1));
    assert!(!func_has_pointer_laundering(&f));
    assert_eq!(havoc_kind(&escape_havoc(&f)), "None");

    // Per call: the structured def list and its flattening.
    let defs = |b: usize| terminator_def_names_structured(&f, &f.body.blocks[b]);
    // `get(move _3: &[u8], move _4: usize)`: `_4` is a pure value, `_3` a shared ref
    // (unique def `&(*_5)`, `_5: &[u8]`, derefs shared only) to `[u8]`: the
    // `arg_grants_no_write` arm, whose havoc is `escape_havoc(peek)` = None.
    // Since CALL-HAVOC-ESCAPE-2 every call also havocs the memory behind every reference
    // loaded from memory (`path_defs::stored_ref_pointee_names`): `self*.0*` (the bytes
    // behind `self.b`), with its discriminant carrier `__trust_mir__discr_<name>` (review
    // of `d1697fccf6`). `*self`'s OWN bytes are not in the list. MEASURED 2026-10-06.
    // Until RETURN-PAYLOAD-RETAG-1 (gate RCA precision D2, 2026-10-18) `_2` was named
    // here too, whole, with `__trust_mir__discr__2` (an `Option<&u8>`: a reference inside
    // an enum variant was covered by the containing place). `_2`'s one value is `get`'s
    // return value (`local_defs::unique_value_call`; no `&mut`/`&raw` borrow of the slot),
    // so the `&u8` inside it is the retagged call-return reference the KEPT rule keeps,
    // and only `get`'s own destination names it. MEASURED 2026-10-19 on the merged main
    // tree of fix/precision-2026-10-17.
    let get = defs(0);
    assert_eq!(havoc_kind(&get.havoc), "None");
    assert_eq!(
        get.flatten(&f),
        ["_2", "_2__slice_len", "self*.0*", "__trust_mir__discr_self*.0*"].map(String::from)
    );
    // `copied(move _2: Option<&u8>)`: `Option<&u8>` holds a reference, so it is neither
    // a pure value nor a shared ref local; the FULL arm decides. Its base list is the
    // (empty) whole-function list, so it havocs `_0` (+ its derived length name) and the
    // same stored-reference names (without `_2` since RETURN-PAYLOAD-RETAG-1, as above).
    let copied = defs(1);
    assert_eq!(havoc_kind(&copied.havoc), "Function");
    assert_eq!(
        copied.flatten(&f),
        ["_0", "_0__slice_len", "self*.0*", "__trust_mir__discr_self*.0*"].map(String::from)
    );

    // The version oracle the walk uses.
    let sv = stmt_versions_for(&f);
    let at = |b: usize, k: usize, name: &str| sv.version_token_at(&f, BlockId(b), k, name);
    let ret = f.body.blocks[2].stmts.len();
    for name in ["self*.1", "self*.0__slice_len"] {
        // Entry spelling at every point, through both calls, up to and at `Return`.
        for (b, k) in [(0, 0), (0, 6), (1, 0), (1, 2), (2, 0), (2, ret)] {
            assert_eq!(at(b, k, name), None, "{name} at bb{b}[{k}]");
        }
        assert!(!sv.ever_versioned(&f, name), "{name}");
    }
    // The havocked `self*.0*` and, by the kill relation's ancestor rebinding, `self*.0`,
    // `self*` and `self` are re-versioned at each call (CALL-HAVOC-ESCAPE-2; MEASURED
    // 2026-10-06). The two names the lemma reads above are not.
    for name in ["self*.0*", "self*.0", "self*", "self"] {
        assert!(sv.ever_versioned(&f, name), "{name}");
        let want = [None, None, Some("s0_t"), Some("s0_t"), Some("s1_t"), Some("s1_t")];
        for ((b, k), want) in
            [(0, 0), (0, 6), (1, 0), (1, 2), (2, 0), (2, ret)].into_iter().zip(want)
        {
            assert_eq!(at(b, k, name).as_deref(), want, "{name} at bb{b}[{k}]");
        }
    }
    // The call destinations ARE versioned after their calls (the oracle is live), and
    // the bb0 slice-length temporaries carry their establish-point tokens to `Return`
    // (MEASURED 2026-10-06).
    assert_eq!(at(0, 6, "_2"), None);
    assert_eq!(at(1, 0, "_2").as_deref(), Some("s0_t"));
    assert_eq!(at(2, ret, "_0").as_deref(), Some("s1_t"));
    assert_eq!(at(0, 6, "_5__slice_len").as_deref(), Some("s0_2"));
    assert_eq!(at(0, 6, "_3__slice_len").as_deref(), Some("s0_3"));
    assert_eq!(at(2, ret, "_3__slice_len").as_deref(), Some("s0_3"));
}

// ---------------------------------------------------------------------------------------
// (b) the slice-length ties, block-local and as the TINV walk delivers them at Return
// ---------------------------------------------------------------------------------------

#[test]
fn peek_slice_len_ties_exist_at_the_get_call() {
    let f = peek();
    let _ws = callee_write_set::enter_callee_write_sets(None);
    let block = &f.body.blocks[0];
    // The establish-point-versioned block defs of bb0 up to the `get` terminator.
    let defs = crate::guards::extract_block_definitions_until_versioned_indexed(
        &f,
        block,
        block.stmts.len(),
    );
    for (k, d) in &defs {
        eprintln!("bb0 def @stmt{k}: {d:?}");
    }
    // `_5 = copy (*_1).0` (push_copy_slice_len) and `_3 = &(*_5)` (push_borrow_slice_len).
    let copy_tie = Formula::Eq(Box::new(int("_5__slice_len")), Box::new(int("self*.0__slice_len")));
    let borrow_tie = Formula::Eq(Box::new(int("_3__slice_len")), Box::new(int("_5__slice_len")));
    assert!(defs.contains(&(2, copy_tie)), "{defs:?}");
    assert!(defs.contains(&(3, borrow_tie)), "{defs:?}");
    // The index read: `_4 == self*.1`.
    assert!(defs.contains(&(5, Formula::Eq(Box::new(int("_4")), Box::new(int("self*.1"))))));
}

/// A hand-built R row at `peek`'s `Return` for the lemma body `self.i < len(self.b)`, no
/// preconditions, no post-call facts (the lemma-probe discipline), walked by the real
/// shim. What reaches it: the ties and the index read at ENTRY spelling (nothing
/// re-versions `self*.1` or `self*.0__slice_len`), but NO fact about `get`'s result, so the row is refuted.
#[test]
fn peek_return_row_sees_entry_spelling_but_no_get_some_fact() {
    let f = peek();
    let mut probe = f.clone();
    probe.preconditions.clear();
    probe.postconditions.clear();
    probe.contracts.clear();
    probe.spec = Default::default();

    let ty: TinvType = candidate::synthesize("tinvp1::P", &all()).expect("P synthesizes").ty;
    let root = Place { local: 1, projections: vec![Projection::Deref] };
    let sigma = sigma_of_root(&probe, &ty, &root);
    assert_eq!(sigma.value[1], Some(int("self*.1")));
    assert_eq!(sigma.len[0], Some(int("self*.0__slice_len")));
    let core = Formula::Lt(Box::new(int("self*.1")), Box::new(int("self*.0__slice_len")));
    let site = TypeInvariantSite { block: 2, statement_index: f.body.blocks[2].stmts.len() };
    let key = TinvRowKey {
        ty: ty.def_path.clone(),
        conjunct: 0,
        point: TypeInvariantPoint::Return,
        site,
        ordinal: 0,
        edge: None,
    };
    let row = RequestRow {
        key: key.clone(),
        ty: 0,
        point: TinvPointRow {
            point: TypeInvariantPoint::Return,
            site,
            row_point: usize::MAX,
            root,
            sigma_src: crate::type_invariant::obligations::SigmaSource::Root,
            state: TinvStateSpec::At,
            failure: None,
        },
        sigma,
        core,
        edge_guard: None,
    };
    let request = TinvRowRequest::new(
        probe.def_path.clone(),
        vec![RequestType {
            def_path: ty.def_path.clone(),
            post_calls: Vec::new(),
            constructions: Vec::new(),
            arm_facts: Vec::new(),
        }],
        vec![row],
    );
    let rows = tinv_check_rows(&probe, request).expect("peek's hand-built row is walked");
    assert_eq!(rows.len(), 1);
    let vc = &rows[0].1;
    eprintln!("peek Return row formula: {:?}", vc.formula);
    let names = vars(&vc.formula);
    eprintln!("peek Return row vars: {names:?}");
    // The core reads the ENTRY spelling at Return (no `#` token on `self*.1` or
    // `self*.0__slice_len`). Since CALL-HAVOC-ESCAPE-2 the re-versioned `self*.0` and
    // `self*.0*` appear at their entry tokens `#e`, tied to the bare entry names.
    assert!(names.contains(&"self*.1".to_string()), "{names:?}");
    assert!(names.contains(&"self*.0__slice_len".to_string()), "{names:?}");
    assert!(
        !names.iter().any(|n| (n.starts_with("self*.1") || n.starts_with("self*.0__slice_len"))
            && n.contains('#')),
        "{names:?}"
    );
    // MEASURED 2026-10-06: the bb0 ties reach `Return` at their bb0 tokens, chaining
    // `_3__slice_len#s0_3 == _5__slice_len#s0_2 == self*.0__slice_len` and `_4 == self*.1`;
    // nothing names `_2` or `_0` (no `get`-`Some` fact, no `copied` fact).
    assert_eq!(
        names,
        [
            "_3*#s0_3",
            "_3__slice_len#s0_3",
            "_4",
            "_5",
            "_5__slice_len#s0_2",
            "self*.0",
            "self*.0#e",
            "self*.0*",
            "self*.0*#e",
            "self*.0__slice_len",
            "self*.1",
        ]
    );
    for tie in [
        Formula::Eq(Box::new(int("_5__slice_len#s0_2")), Box::new(int("self*.0__slice_len"))),
        Formula::Eq(Box::new(int("_3__slice_len#s0_3")), Box::new(int("_5__slice_len#s0_2"))),
        Formula::Eq(Box::new(int("_4")), Box::new(int("self*.1"))),
    ] {
        let mut hit = false;
        vc.formula.visit(&mut |n| hit |= *n == tie);
        assert!(hit, "{tie:?} missing from {:?}", vc.formula);
    }
    let verdict = solve(&vc.formula);
    eprintln!("peek Return row verdict: {verdict:?}");
    assert!(matches!(verdict, VerificationResult::Failed { .. }), "{verdict:?}");
}
