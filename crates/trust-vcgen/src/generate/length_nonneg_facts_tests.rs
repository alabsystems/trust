// Trust (NEGATIVE-LENGTH class): unit cover for `conjoin_length_nonneg_bounds`
// and its admission set `length_nonneg_base_names`.
//
// Four directions are load-bearing and each is asserted separately:
//
//  1. the bound lands on the SAME `{place}__slice_len` symbol
//     `slice_len_formula` mints, so it actually binds the obligations' variable
//     (a bound over a differently spelled name is inert);
//  2. it attaches for a ZERO-SIZED element too — `0 <= len` is
//     element-independent, and `&[()]` is exactly the fixture whose merged
//     `Unreachable` row was refuted with `a__slice_len = -1` at HEAD;
//  3. it attaches NO upper bound. The `len <= isize::MAX` half is false for a
//     ZST element and is pointer-width dependent, so it stays where it already
//     is (`conjoin_slice_len_bounds`, non-ZST-gated). Publishing it here would
//     be the one direction that can hide a real `len + k` overflow;
//  4. it NEVER introduces a free variable. That is what separates this from the
//     `build_global_invariant_facts` spelling, which was measured to break the
//     `callsite_replay_tests` caller-grounding gate by adding an unpinned name
//     to composed candidates.
//
// WHICH MUTANT KILLS WHICH, all of them built and run rather than argued:
//
//     NO-OP          body returns its argument   attaches_* (x2), zero_sized_element_*
//     OFF-BY-ONE     mints `1 <= len`            attaches_* (x2), zero_sized_element_*
//     INVERTED       mints `len <= 0`            attaches_* (x2), zero_sized_element_*,
//                                                never_attaches_an_upper_bound
//     UPPER BOUND    `len <= isize::MAX` added   attaches_* (x2), zero_sized_element_*,
//                                                never_attaches_an_upper_bound
//     UNCONDITIONAL  a bound for every admitted  attaches_* (x2), zero_sized_element_*,
//                    base, not only the names    introduces_no_free_variable
//                    the formula already has
//     SIGNED DEST    `is_signed()` check dropped a_signed_length_destination_is_declined
//     ANY LOCAL      every local admitted as a   a_function_with_no_length_quantity_*,
//                    "length"                    a_signed_length_destination_is_declined
//
// Directions 1 and 2 go red against the NO-OP stub only because they read the
// returned Formula STRUCTURALLY — see `attached_bounds`, which documents the
// substring assertion they used to carry and which passed against the stub.
// Directions 3 and 4 are MUST-NOT properties that the stub satisfies, so they are
// not evidence that the pass works; the ledger above is what shows they are not
// inert either — each has a mutant that makes it fire.
use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Rvalue, Sort, SourceSpan, Statement,
    Terminator, Ty, UnOp, VerifiableBody, VerifiableFunction,
};

use super::{conjoin_length_nonneg_bounds, length_nonneg_base_names};

/// `fn f(a: &[T]) -> usize { let n = PtrMetadata(a); n }` — the lowering every
/// slice PATTERN test and `<[T]>::len()` produce.
fn slice_len_read(elem: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "test::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(elem) }),
                    },
                    name: Some("a".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("n".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::usize(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn var(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

/// The merged-`Unreachable` path condition, over whichever length name is asked
/// for: `len != 0 ∧ ¬(len >= 1)` — UNSAT for a `usize`, SAT at `len = -1`.
fn negative_length_witness_goal(name: &str) -> Formula {
    Formula::And(vec![
        Formula::Not(Box::new(Formula::Eq(Box::new(var(name)), Box::new(Formula::Int(0))))),
        Formula::Not(Box::new(Formula::Ge(Box::new(var(name)), Box::new(Formula::Int(1))))),
    ])
}

fn canonical_slice_len(func: &VerifiableFunction) -> String {
    match crate::slice_len_formula(func, &Operand::Copy(Place::local(1))) {
        Some(Formula::Var(name, _)) => name,
        other => panic!("a slice place must mint a `__slice_len` var, got {other:?}"),
    }
}

/// The bounds this conjoin ADDED, read STRUCTURALLY.
///
/// Not a substring probe on `format!("{out:?}")` — that is the shape this file
/// was first written in and it was VACUOUS: `negative_length_witness_goal`
/// itself contains `Not(Ge(Var(name), Int(1)))`, so `"Ge(Var(\"{name}\""` is
/// already present in the UNCHANGED goal and the assertion passed against an
/// identity `conjoin_length_nonneg_bounds`. Measured: with the body stubbed to
/// `return formula`, the three "attaches" tests still went green. So read the
/// wrapper the function actually builds — `And([bounds.., goal])` — require the
/// goal to be the LAST conjunct and untouched, and return only the prefix.
///
/// The `conjuncts.len() >= 2` guard this helper used to carry has been DELETED as
/// INERT: `negative_length_witness_goal` is itself a two-element `And`, so an
/// identity conjoin returns a length-2 `And` and that assertion could not fire —
/// its message ("no bound was attached") named a defect it never caught. The
/// identity case is caught by the `last() == goal` check below (the last conjunct
/// of the unchanged goal is `Not(Ge(..))`, not the goal), which also short-circuits
/// the slice on any length under 2.
fn attached_bounds(out: &Formula, goal: &Formula) -> Vec<Formula> {
    let Formula::And(conjuncts) = out else {
        panic!("the conjoin must wrap the goal in an `And`, got {out:?}");
    };
    assert_eq!(
        conjuncts.last(),
        Some(goal),
        "the goal must be the LAST conjunct and byte-identical (an identity conjoin lands \
         here): {out:?}"
    );
    conjuncts[..conjuncts.len() - 1].to_vec()
}

/// `0 <= name`, exactly as this pass mints it.
fn lower_bound_over(name: &str) -> Formula {
    Formula::Ge(Box::new(var(name)), Box::new(Formula::Int(0)))
}

#[test]
fn attaches_the_lower_bound_over_the_canonical_slice_len_symbol() {
    let func = slice_len_read(Ty::Int { width: 32, signed: false });
    let canonical = canonical_slice_len(&func);
    let goal = negative_length_witness_goal(&canonical);
    let out = conjoin_length_nonneg_bounds(&func, goal.clone());
    assert_eq!(
        attached_bounds(&out, &goal),
        vec![lower_bound_over(&canonical)],
        "the ONLY attached fact must be `0 <= {canonical}` over the canonical symbol: {out:?}"
    );
}

#[test]
fn attaches_to_the_ssa_versioned_spelling_too() {
    // Path guards version their reads at the guard's SOURCE block, so the name in
    // the formula can be `a__slice_len#s4_1`. Matching on the formula's own names
    // (base = everything before `#`) is what makes the bound reach those.
    let func = slice_len_read(Ty::Int { width: 32, signed: false });
    let versioned = format!("{}#s4_1", canonical_slice_len(&func));
    let goal = negative_length_witness_goal(&versioned);
    let out = conjoin_length_nonneg_bounds(&func, goal.clone());
    assert_eq!(
        attached_bounds(&out, &goal),
        vec![lower_bound_over(&versioned)],
        "the bound must land on the VERSIONED spelling `{versioned}`: {out:?}"
    );
}

#[test]
fn zero_sized_element_still_gets_the_lower_bound() {
    // `&[()]`: `len` can reach `usize::MAX`, so no UPPER bound is sound — but
    // `0 <= len` is, and it is what deletes the `a__slice_len = -1` model.
    let func = slice_len_read(Ty::Unit);
    let canonical = canonical_slice_len(&func);
    let goal = negative_length_witness_goal(&canonical);
    let out = conjoin_length_nonneg_bounds(&func, goal.clone());
    assert_eq!(
        attached_bounds(&out, &goal),
        vec![lower_bound_over(&canonical)],
        "a ZST-element slice must still be bounded below, and below ONLY: {out:?}"
    );
}

#[test]
fn never_attaches_an_upper_bound() {
    // The half that could hide a real `len + k` overflow must not appear, for ANY
    // element type. The goal itself carries no `Le`/`Lt`, so any occurrence in the
    // result came from this conjoin.
    for elem in [Ty::Int { width: 8, signed: false }, Ty::Unit, Ty::Bool] {
        let func = slice_len_read(elem);
        let canonical = canonical_slice_len(&func);
        let out = conjoin_length_nonneg_bounds(&func, negative_length_witness_goal(&canonical));
        let s = format!("{out:?}");
        assert!(!s.contains("Le("), "no upper bound may be attached: {s}");
        assert!(!s.contains("Lt("), "no upper bound may be attached: {s}");
    }
}

#[test]
fn introduces_no_free_variable() {
    // THE property that separates this from an unconditional global fact: a
    // formula that mentions no length must come back with its free-variable set
    // unchanged, so a lane that gates on caller-grounded free vars is untouched.
    let func = slice_len_read(Ty::Int { width: 32, signed: false });
    let unrelated = Formula::Not(Box::new(Formula::Eq(
        Box::new(var("some_other_local")),
        Box::new(Formula::Int(7)),
    )));
    let out = conjoin_length_nonneg_bounds(&func, unrelated.clone());
    let mut before: Vec<String> = unrelated.free_variables().into_iter().collect();
    let mut after: Vec<String> = out.free_variables().into_iter().collect();
    before.sort();
    after.sort();
    assert_eq!(before, after, "the conjoin must not add a free variable: {out:?}");
}

#[test]
fn a_function_with_no_length_quantity_admits_nothing() {
    // Fail-closed: no slice/str/container local and no length read => empty set.
    let mut func = slice_len_read(Ty::Int { width: 32, signed: false });
    func.body.locals[1].ty = Ty::Int { width: 32, signed: false };
    func.body.blocks[0].stmts.clear();
    assert!(
        length_nonneg_base_names(&func).is_empty(),
        "no length quantity must admit no name: {:?}",
        length_nonneg_base_names(&func)
    );
}

#[test]
fn a_signed_length_destination_is_declined() {
    // The `0 <= dest` half of the derivation is the DECLARED type. A signed
    // destination has no such implication, so it must be declined rather than
    // asserted from the recognizer alone.
    let mut func = slice_len_read(Ty::Int { width: 32, signed: false });
    func.body.locals[2].ty = Ty::Int { width: 64, signed: true };
    let names = length_nonneg_base_names(&func);
    let dest = crate::place_to_var_name(&func, &Place::local(2));
    assert!(!names.contains(&dest), "a signed length destination must be declined: {names:?}");
    // ...while the slice parameter's own length symbol is still admitted.
    assert!(names.contains(&canonical_slice_len(&func)), "the slice length is still a length");
}
