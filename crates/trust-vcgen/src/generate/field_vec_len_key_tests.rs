use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
};

use super::{collection_abstract_len_with_base_opts, generate_vcs};
use crate::guards;

fn vec_u32() -> Ty {
    Ty::adt("alloc::vec::Vec<u32>", vec![])
}

/// `struct T { history: Vec<u32>, other: Vec<u32> }` — field 0 is `history`,
/// field 1 is `other`. Stamped `Struct`, as every real dump stamps its ADTs: an ADT of
/// unrecorded kind may be a union, and a field of a union behind `&self` is not
/// body-stable when the union may hold a cell byte (INTERIOR-MUT-CHANNEL-2, 2026-10-16).
fn t_struct() -> Ty {
    let mut ty = Ty::adt(
        "test::T",
        vec![("history".to_string(), vec_u32()), ("other".to_string(), vec_u32())],
    );
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(trust_types::AdtKind::Struct);
    }
    ty
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
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
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
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
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
        vcs.iter().map(|vc| (vc.kind.description(), vc.formula.to_smtlib())).collect::<Vec<_>>()
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

/// The container-length recognizer GRANTS a stable length (`coll_len`) to std's
/// `Vec` and `String` by their exact authenticated paths, never by the path's tail:
/// a user type named `Vec` or `String` has its own `len` and `Index` (see
/// `tests/data/user_type_named_vec.rs`, whose `Vec` got std `Vec`'s index/value tie
/// through the same tail test and was a certified false proof).
#[test]
fn only_std_vec_and_string_have_a_container_length() {
    let func_with = |name: &str| VerifiableFunction {
        name: "len_of".to_string(),
        def_path: "test::len_of".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::adt(name, vec![])) },
                    name: Some("v".into()),
                },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::u32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let len_of = |name: &str| {
        guards::owned_container_len_var(&func_with(name), &Operand::Copy(Place::local(1)))
    };
    for name in ["alloc::vec::Vec<u32>", "std::vec::Vec<u32>", "alloc::string::String"] {
        assert!(len_of(name).is_some(), "std's `{name}` keeps its container length");
    }
    for name in ["mycrate::Vec<u32>", "Vec<u32>", "mycrate::String", "string::String"] {
        assert!(len_of(name).is_none(), "a user `{name}` must not get a container length");
    }
}

/// IDX-TIE-1 (2026-10-03) fixture for `build_len_guard_field_map`: a dominating
/// field-length guard and a scalar field index whose callee is `index_callee`.
/// ```text
/// fn f(self: &T, i: usize) -> u32 {
///   b0: _5 = &((*_1).0); _6 = Vec::len(move _5)             -> b1
///   b1: _9 = Ge(copy _6, const 4); switchInt(move _9) [0: b3, otherwise: b2]
///   b2: _7 = &((*_1).0); _8 = <index_callee>(move _7, copy _2) -> b4
///   b3: return            b4: return
/// }
/// ```
fn guarded_field_index_func(index_callee: &str) -> VerifiableFunction {
    let mut func = field_vec_func(false, 0, 0);
    let call = |callee: &str, args: Vec<Operand>, dest: usize, target: usize| Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: crate::sep_engine::tests::fixture_key(callee),
        is_foreign: false,
    };
    let reborrow = |dest: usize| Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Ref { mutable: false, place: field_place(0) },
        span: SourceSpan::default(),
    };
    func.body.locals.push(LocalDecl { index: 9, ty: Ty::Bool, name: None });
    func.body.blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![reborrow(5)],
            terminator: call(
                "alloc::vec::Vec::<u32>::len",
                vec![Operand::Move(Place::local(5))],
                6,
                1,
            ),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: vec![Statement::Assign {
                place: Place::local(9),
                rvalue: Rvalue::BinaryOp(
                    trust_types::BinOp::Ge,
                    Operand::Copy(Place::local(6)),
                    Operand::Constant(trust_types::ConstValue::Uint(4, 64)),
                ),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(9)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![reborrow(7)],
            terminator: call(
                index_callee,
                vec![Operand::Move(Place::local(7)), Operand::Copy(Place::local(2))],
                8,
                4,
            ),
        },
        BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
    ];
    func
}

fn field_guard_facts(func: &VerifiableFunction) -> usize {
    super::build_len_guard_field_map(func).values().map(Vec::len).sum()
}

/// POSITIVE: std's `Vec` `Index<usize>`, in the extractor's spelling, gets the
/// dominating-guard field-length fact.
#[test]
fn std_field_index_gets_the_guard_fact() {
    let func =
        guarded_field_index_func("<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index");
    assert_eq!(field_guard_facts(&func), 1);
}

/// IDX-TIE-1: a method that is merely NAMED `index` gets no fact from this lane
/// (uniformity with the value tie; the fact is meant for std's scalar index).
#[test]
fn a_user_method_named_index_gets_no_guard_fact() {
    for user in [
        "<alloc::vec::Vec<u32> as lenf::Pick>::index",
        "<alloc::vec::Vec<u32> as core::ops::index::Index<lenf::K>>::index",
        "core::ops::index::Index::index",
    ] {
        assert_eq!(field_guard_facts(&guarded_field_index_func(user)), 0, "{user}");
    }
}
