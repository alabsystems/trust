use trust_types::UnwindEdge;
use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{collection_abstract_len_with_base_opts, generate_vcs};
use crate::guards;

fn vec_u32() -> Ty {
    Ty::adt("alloc::vec::Vec<u32>", vec![])
}

/// `struct T { history: Vec<u32>, other: Vec<u32> }` — field 0 is `history`,
/// field 1 is `other`.
fn t_struct() -> Ty {
    Ty::adt(
        "test::T",
        vec![("history".to_string(), vec_u32()), ("other".to_string(), vec_u32())],
    )
}

/// `&((*_1).<f>)` — the field place a reborrow temp borrows.
fn field_place(f: usize) -> Place {
    Place { local: 1, projections: vec![Projection::Deref, Projection::Field(f)] }
}

/// The reproducer's essential MIR shape — each container access goes through a
/// FRESH shared reborrow temp, exactly as rustc lowers autoref:
/// ```text
/// fn f(self: &T /* &mut T when self_mutable */, i: usize) -> u32 {
///   b0: _3 = &((*_1).<guard_field>); _4 = Vec::is_empty(move _3) -> b1
///   b1: _5 = &((*_1).<guard_field>); _6 = Vec::len(move _5)      -> b2
///   b2: _7 = &((*_1).<index_field>); _8 = Index::index(move _7, copy _2) -> b3
///   b3: return
/// }
/// ```
fn field_vec_func(
    self_mutable: bool,
    guard_field: usize,
    index_field: usize,
) -> VerifiableFunction {
    let vec_ref = Ty::Ref { mutable: false, inner: Box::new(vec_u32()) };
    let reborrow = |dest: usize, f: usize| Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Ref { mutable: false, place: field_place(f) },
        span: SourceSpan::default(),
    };
    let call = |callee: &str, args: Vec<Operand>, dest: usize, target: u32| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target as usize)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        is_foreign: false,
    };
    VerifiableFunction {
        name: "field_vec".to_string(),
        def_path: "test::field_vec".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: self_mutable, inner: Box::new(t_struct()) },
                    name: Some("self".into()),
                },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: vec_ref.clone(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
                LocalDecl { index: 5, ty: vec_ref.clone(), name: None },
                LocalDecl { index: 6, ty: Ty::usize(), name: None },
                LocalDecl { index: 7, ty: vec_ref, name: None },
                LocalDecl {
                    index: 8,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: None,
                },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![reborrow(3, guard_field)],
                    terminator: call(
                        "alloc::vec::Vec::<u32>::is_empty",
                        vec![Operand::Move(Place::local(3))],
                        4,
                        1,
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![reborrow(5, guard_field)],
                    terminator: call(
                        "alloc::vec::Vec::<u32>::len",
                        vec![Operand::Move(Place::local(5))],
                        6,
                        2,
                    ),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![reborrow(7, index_field)],
                    terminator: call(
                        "core::ops::index::Index::index",
                        vec![Operand::Move(Place::local(7)), Operand::Copy(Place::local(2))],
                        8,
                        3,
                    ),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// POSITIVE: guard receiver (`_3`), index receiver (`_7`), and `.len()` tie
/// (`_6 = len(_5)`) must ALL resolve to the SAME canonical field length var —
/// `coll_len(self*.0)` — or the fix is inert (a fact on one var can never
/// discharge a bound on another).
#[test]
fn field_guard_and_index_share_one_len_var() {
    let func = field_vec_func(false, 0, 0);
    // Helper level: the place key IS the canonical field place.
    assert_eq!(guards::base_collection_place_unique(&func, 3), Some(field_place(0)));
    assert_eq!(guards::base_collection_place_unique(&func, 7), Some(field_place(0)));
    // Guard side.
    let guard = guards::owned_container_len_var(&func, &Operand::Move(Place::local(3)))
        .expect("guard side must recover the field length var");
    assert_eq!(guard.var_name(), Some("self*.0"), "place-keyed canonical field var");
    // Index-bound side — the SAME var, recovered through a DIFFERENT temp.
    let (_base, bound) =
        collection_abstract_len_with_base_opts(&func, &Operand::Move(Place::local(7)), true)
            .expect("index side must recover the field length var");
    assert_eq!(
        guard.var_name(),
        bound.var_name(),
        "guard and index must share ONE length var or the guard cannot discharge the bound"
    );
    // `.len()` tie — `_6 == coll_len(self*.0)`, seeded at the len call's return
    // target (b2), the fact that discharges `_6 - 1` underflow + the index bound.
    let ties = guards::slice_last_some_nonempty_definitions(&func);
    let facts =
        ties.get(&BlockId(2)).expect("len tie must be seeded at the len call's return target");
    assert!(
        facts.iter().any(|f| matches!(f, Formula::Eq(l, r)
            if l.var_name() == Some("_6") && r.var_name() == Some("self*.0"))),
        "the `.len()` result must tie to the SAME field length var; got {facts:?}"
    );
}

/// End-to-end: the field-Vec scalar index emits a SliceBoundsCheck whose bound
/// reads the CANONICAL field length var (so guard facts in that vocabulary can
/// discharge it at solve time) — and it is a real obligation, not a silent skip.
#[test]
fn field_index_vc_reads_place_keyed_len() {
    let func = field_vec_func(false, 0, 0);
    let vcs = generate_vcs(&func);
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)
            && vc.formula.to_smtlib().contains("self*.0")),
        "the scalar-index VC must reference coll_len(self*.0); got {:#?}",
        vcs.iter()
            .map(|vc| (vc.kind.description(), vc.formula.to_smtlib()))
            .collect::<Vec<_>>()
    );
}

/// WRONG-FIELD NEGATIVE (fail-closed BY CONSTRUCTION): the key is the FULL
/// projected place, so a guard on `self.history` (`.0`) and an index into
/// `self.other` (`.1`) mint DIFFERENT vars — `if !self.a.is_empty() { self.b[0] }`
/// can never falsely prove. (This is exactly why the identity must be a place,
/// not the struct local: one shared struct-local key would merge the fields.)
#[test]
fn wrong_field_guard_does_not_unify() {
    let func = field_vec_func(false, 0, 1);
    let guard = guards::owned_container_len_var(&func, &Operand::Move(Place::local(3)))
        .expect("guard side recovers its OWN field var");
    let (_base, bound) =
        collection_abstract_len_with_base_opts(&func, &Operand::Move(Place::local(7)), true)
            .expect("index side recovers its OWN field var");
    assert_eq!(guard.var_name(), Some("self*.0"));
    assert_eq!(bound.var_name(), Some("self*.1"));
    assert_ne!(
        guard.var_name(),
        bound.var_name(),
        "a guard on self.history must NEVER discharge self.other[i]"
    );
}

/// &MUT-SELF NEGATIVE (fail-closed BY CONSTRUCTION): the field key requires a
/// SHARED-ref root (`Ty::Ref { mutable: false }` match in
/// `shared_stable_field_reborrow_place`), so a `&mut self` root — under which
/// the field could be resized between guard and index — DECLINES to the
/// whole-local per-temp identity, whose vars never unify across the two fresh
/// reborrow temps: the guard cannot discharge the index (today's sound
/// behavior, unchanged).
#[test]
fn mut_self_root_fails_closed_to_per_temp_vars() {
    let func = field_vec_func(true, 0, 0);
    // Helper level: the field key declines — fall back to the whole-local leaf.
    assert_eq!(guards::base_collection_place_unique(&func, 3), Some(Place::local(3)));
    assert_eq!(guards::base_collection_place_unique(&func, 7), Some(Place::local(7)));
    // Consumer level: per-temp vars that never unify, and neither side leaks
    // the canonical field var.
    let guard = guards::owned_container_len_var(&func, &Operand::Move(Place::local(3)));
    let bound =
        collection_abstract_len_with_base_opts(&func, &Operand::Move(Place::local(7)), true);
    let gname = guard.as_ref().and_then(|f| f.var_name()).map(str::to_owned);
    let bname = bound.as_ref().and_then(|(_, f)| f.var_name()).map(str::to_owned);
    assert_ne!(gname.as_deref(), Some("self*.0"), "&mut self must not mint the field key");
    assert_ne!(bname.as_deref(), Some("self*.0"), "&mut self must not mint the field key");
    assert!(
        gname.is_none() || gname != bname,
        "under &mut self the guard var must NOT unify with the index var \
         (guard {gname:?}, index {bname:?})"
    );
}
