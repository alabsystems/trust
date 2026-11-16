//! TINV step 8a/8b: candidate synthesis on hand-built bodies (the P1/P2/P3 shapes, derived
//! `Clone`/`Default`, refusals, determinism) and the entry-pinning contract on the step-0(a)
//! real-MIR fixture.

use trust_types::{
    AdtKind, AggregateKind, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand,
    Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge,
    VerifiableBody, VerifiableFunction,
};

use super::super::{
    CandidateConjunct, FieldTerm, Sigma, TinvType, field_var, instantiate, obligations,
};
use super::*;

// ---------------------------------------------------------------------------------------
// Builders
// ---------------------------------------------------------------------------------------

fn adt_kind(name: &str, fields: Vec<(&str, Ty)>, kind: AdtKind) -> Ty {
    Ty::Adt {
        adt_kind: Some(kind),
        layout: None,
        variants: Vec::new().into(),
        name: name.into(),
        fields: fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect::<Vec<_>>().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn adt(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    adt_kind(name, fields, AdtKind::Struct)
}

fn uint(width: u32) -> Ty {
    Ty::Int { width, signed: false }
}

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

fn vec_ty() -> Ty {
    Ty::Seq { elem: Box::new(uint(8)), drop_auth: None }
}

fn slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(uint(8)) }) }
}

fn shared_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(t) }
}

fn mut_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

fn option_ty(t: Ty) -> Ty {
    adt_kind("core::option::Option", vec![("0", t)], AdtKind::Enum)
}

fn func(
    def_path: &str,
    locals: Vec<Ty>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).into(),
        def_path: def_path.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, ty)| LocalDecl { index, ty, name: None })
                .collect(),
            blocks,
            arg_count,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn blk(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn call(callee: &str, args: Vec<Operand>, dest: Place, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
        callee_key: None,
    }
}

fn uk(v: u128, w: u32) -> Operand {
    Operand::Constant(ConstValue::Uint(v, w))
}

fn ik(v: i128) -> Operand {
    Operand::Constant(ConstValue::Int(v))
}

fn mv(l: usize) -> Operand {
    Operand::Move(Place::local(l))
}

fn place(local: usize, projections: Vec<Projection>) -> Place {
    Place { local, projections }
}

/// `(*_l).i`.
fn pointee_field(local: usize, i: usize) -> Place {
    place(local, vec![Projection::Deref, Projection::Field(i)])
}

fn agg(name: &str, ops: Vec<Operand>) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: name.into(), variant: 0, active_field: None, args: None },
        ops,
    )
}

/// The fields a template reads.
fn fields_of(t: &Template) -> Vec<usize> {
    match *t {
        Template::GeConst { f, .. } | Template::LeConst { f, .. } => vec![f],
        Template::Lt { a, b } | Template::Le { a, b } => vec![a, b],
        Template::LeLen { a, g } => vec![a, g],
        Template::LenEqProd { f, g, h } => vec![f, g, h],
    }
}

fn displayed(set: &CandidateSet) -> Vec<String> {
    describe(set).into_values().collect()
}

fn has(set: &CandidateSet, s: &str) -> bool {
    displayed(set).iter().any(|d| d == s)
}

// --- P2: `Screen { cols, rows, row, col }`, all `u16` --------------------------------------

const SCREEN: &str = "c::Screen";
const CLAMP: &str = "<u16 as core::cmp::Ord>::clamp";
const U16_DEFAULT: &str = "<u16 as core::default::Default>::default";

fn screen_ty() -> Ty {
    adt(SCREEN, vec![("cols", uint(16)), ("rows", uint(16)), ("row", uint(16)), ("col", uint(16))])
}

/// `fn new(c, r) -> Screen { Screen { cols: c.clamp(1, 1000), rows: r.clamp(1, 1000), row: 0, col: 0 } }`
fn screen_new() -> VerifiableFunction {
    func(
        "c::Screen::new",
        vec![screen_ty(), uint(16), uint(16), uint(16), uint(16)],
        2,
        vec![
            blk(0, vec![], call(CLAMP, vec![mv(1), uk(1, 16), uk(1000, 16)], Place::local(3), 1)),
            blk(1, vec![], call(CLAMP, vec![mv(2), uk(1, 16), uk(1000, 16)], Place::local(4), 2)),
            blk(
                2,
                vec![assign(
                    Place::local(0),
                    agg(SCREEN, vec![mv(3), mv(4), uk(0, 16), uk(0, 16)]),
                )],
                Terminator::Return,
            ),
        ],
    )
}

/// The derived `Default`: four `<u16 as Default>::default()` calls, then the aggregate.
fn screen_default() -> VerifiableFunction {
    let mut blocks: Vec<BasicBlock> = (0..4)
        .map(|k| blk(k, vec![], call(U16_DEFAULT, vec![], Place::local(k + 1), k + 1)))
        .collect();
    blocks.push(blk(
        4,
        vec![assign(Place::local(0), agg(SCREEN, vec![mv(1), mv(2), mv(3), mv(4)]))],
        Terminator::Return,
    ));
    func(
        "c::<impl core::default::Default for c::Screen>::default",
        vec![screen_ty(), uint(16), uint(16), uint(16), uint(16)],
        0,
        blocks,
    )
}

/// The derived `Clone` of a `Copy`-field struct: field copies, then the aggregate.
fn screen_clone() -> VerifiableFunction {
    let stmts = (0..4)
        .map(|i| assign(Place::local(i + 2), Rvalue::Use(Operand::Copy(pointee_field(1, i)))))
        .chain([assign(Place::local(0), agg(SCREEN, vec![mv(2), mv(3), mv(4), mv(5)]))])
        .collect();
    func(
        "c::<impl core::clone::Clone for c::Screen>::clone",
        vec![screen_ty(), shared_ref(screen_ty()), uint(16), uint(16), uint(16), uint(16)],
        1,
        vec![blk(0, stmts, Terminator::Return)],
    )
}

/// `fn down(&mut self) { if self.row < 7 { self.row = 42 } }` (comparison and store
/// constants).
fn screen_down() -> VerifiableFunction {
    func(
        "c::Screen::down",
        vec![Ty::Unit, mut_ref(screen_ty()), uint(16), Ty::Bool],
        1,
        vec![
            blk(
                0,
                vec![
                    assign(Place::local(2), Rvalue::Use(Operand::Copy(pointee_field(1, 2)))),
                    assign(Place::local(3), Rvalue::BinaryOp(BinOp::Lt, mv(2), uk(7, 16))),
                ],
                Terminator::SwitchInt {
                    discr: mv(3),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(
                1,
                vec![assign(pointee_field(1, 2), Rvalue::Use(uk(42, 16)))],
                Terminator::Goto(BlockId(2)),
            ),
            blk(2, vec![], Terminator::Return),
        ],
    )
}

// --- P1: `Parser { b: &[u8], i: usize }` ---------------------------------------------------

const PARSER: &str = "c::P";

fn parser_ty() -> Ty {
    adt(PARSER, vec![("b", slice_ref()), ("i", uint(64))])
}

/// `pub fn parse(b: &[u8]) { let p = P { b, i: 0 }; }`
fn parse_fn() -> VerifiableFunction {
    func(
        "c::parse",
        vec![Ty::Unit, slice_ref(), parser_ty()],
        1,
        vec![blk(
            0,
            vec![assign(
                Place::local(2),
                agg(PARSER, vec![Operand::Copy(Place::local(1)), uk(0, 64)]),
            )],
            Terminator::Return,
        )],
    )
}

// --- P3: `G { grid: Vec<u8>, cols: u16, rows: u16 }` ---------------------------------------

const GRID: &str = "c::G";

fn grid_ty() -> Ty {
    adt(GRID, vec![("grid", vec_ty()), ("cols", uint(16)), ("rows", uint(16))])
}

fn grid_new() -> VerifiableFunction {
    func(
        "c::G::new",
        vec![grid_ty(), uint(16), uint(16), uint(64), vec_ty()],
        2,
        vec![
            blk(
                0,
                vec![assign(Place::local(3), Rvalue::BinaryOp(BinOp::Mul, mv(1), mv(2)))],
                call("alloc::vec::from_elem", vec![uk(0, 8), mv(3)], Place::local(4), 1),
            ),
            blk(
                1,
                vec![assign(Place::local(0), agg(GRID, vec![mv(4), mv(1), mv(2)]))],
                Terminator::Return,
            ),
        ],
    )
}

// ---------------------------------------------------------------------------------------
// 8a: shapes, terms, evaluation
// ---------------------------------------------------------------------------------------

/// `c::K` with one field of every classified kind.
fn kitchen_fields() -> Vec<(&'static str, Ty)> {
    vec![
        ("a", uint(16)),
        ("b", i64_ty()),
        ("c", Ty::PtrSizedInt { signed: false }),
        ("d", Ty::Bool),
        ("e", vec_ty()),
        ("f", slice_ref()),
        ("g", Ty::Ref { mutable: false, inner: Box::new(Ty::Str) }),
        ("h", option_ty(vec_ty())),
        ("i", Ty::Char),
    ]
}

fn kitchen_tinv() -> TinvType {
    TinvType {
        def_path: "c::K".into(),
        fields: kitchen_fields().into_iter().map(|(n, t)| (n.to_string(), t)).collect(),
        conjuncts: Vec::new(),
    }
}

#[test]
fn shapes_classify_int_bool_len_and_nothing_else() {
    let shapes: Vec<FieldShape> =
        kitchen_fields().iter().map(|(n, t)| classify_field(n, t).0).collect();
    assert_eq!(shapes[0], FieldShape::Int { min: 0, max: Some(65535) });
    assert_eq!(
        shapes[1],
        FieldShape::Int { min: i128::from(i64::MIN), max: Some(i128::from(i64::MAX)) }
    );
    assert_eq!(shapes[2], FieldShape::Int { min: 0, max: Some(i128::from(u64::MAX)) });
    assert_eq!(shapes[3], FieldShape::Bool);
    assert_eq!(shapes[4], FieldShape::Len(LenCarrier::OwnedContainer));
    assert_eq!(shapes[5], FieldShape::Len(LenCarrier::SliceRef));
    assert_eq!(shapes[6], FieldShape::Len(LenCarrier::SliceRef));
    assert_eq!(shapes[7], FieldShape::NoTerm);
    assert_eq!(shapes[8], FieldShape::NoTerm, "a char is not an integer term");
    assert_eq!(classify_field("w", &uint(128)).0, FieldShape::Int { min: 0, max: None });
    let (_, note) = classify_field("saved", &option_ty(vec_ty()));
    assert!(note.is_some_and(|n| n.contains("discriminant")), "the Option note names why");
}

/// A shape proposes a term exactly where step 7.4's `Sigma` renders one, so no
/// candidate reads a term that can never be stated, and every rendered term is
/// Int-sorted (G16), on a pointee root and on a by-value root.
#[test]
fn shapes_agree_with_sigma_rendering_and_terms_are_int_sorted() {
    let k = adt("c::K", kitchen_fields());
    let tinv = kitchen_tinv();
    for (root_ty, root) in
        [(mut_ref(k.clone()), place(1, vec![Projection::Deref])), (k.clone(), Place::local(1))]
    {
        let f = func(
            "c::K::touch",
            vec![Ty::Unit, root_ty],
            1,
            vec![blk(0, vec![], Terminator::Return)],
        );
        let sigma = obligations::sigma_of_root(&f, &tinv, &root);
        for (i, (name, ty)) in tinv.fields.iter().enumerate() {
            let shape = classify_field(name, ty).0;
            assert_eq!(
                shape.term(i) == Some(FieldTerm::Value(i)),
                sigma.value[i].is_some(),
                "{name}"
            );
            assert_eq!(shape.term(i) == Some(FieldTerm::Len(i)), sigma.len[i].is_some(), "{name}");
            for t in sigma.value[i].iter().chain(&sigma.len[i]) {
                assert!(matches!(t, Formula::Var(_, Sort::Int)), "{name}: {t:?} is not an Int var");
            }
        }
    }
}

/// (name, sort) parity: the Value term of `_5.i` after `_5 = K { .. }` is exactly the
/// left-hand side the aggregate's field definition binds (`guards.rs`
/// `aggregate_field_definitions`: `operand_to_formula(copy field_place)`), so the
/// conjunct's symbol is the one the body defines. A Len term of a `Vec` field carries
/// the field's own name.
#[test]
fn value_terms_are_the_aggregate_definition_lhs() {
    let k = adt("c::K", kitchen_fields());
    let n = kitchen_fields().len();
    let mut locals = vec![Ty::Unit];
    locals.extend(kitchen_fields().into_iter().map(|(_, t)| t));
    locals.push(k);
    let dest = Place::local(n + 1);
    let kind =
        AggregateKind::Adt { name: "c::K".into(), variant: 0, active_field: None, args: None };
    let ops: Vec<Operand> = (1..=n).map(mv).collect();
    let f = func(
        "c::K::new",
        locals,
        n,
        vec![blk(
            0,
            vec![assign(dest.clone(), Rvalue::Aggregate(kind.clone(), ops))],
            Terminator::Return,
        )],
    );
    let sigma = obligations::sigma_of_root(&f, &kitchen_tinv(), &dest);
    for i in 0..n {
        let fp = crate::aggregate_field_place(&dest, &kind, i, n).expect("struct field place");
        let lhs = crate::operand_to_formula(&f, &Operand::Copy(fp.clone()));
        if let Some(v) = &sigma.value[i] {
            assert_eq!(v, &lhs, "field {i}: Value term differs from the definition lhs");
        }
        if let (Some(Formula::Var(name, Sort::Int)), Ty::Seq { .. }) =
            (&sigma.len[i], &kitchen_fields()[i].1)
        {
            assert_eq!(name, &crate::place_to_var_name(&f, &fp), "field {i}: Vec length name");
        }
    }
}

/// The versioning invariant: every term variable of field place `p` is re-versioned by
/// a write to `p` (`dest_write_rebinds`), so an entry hypothesis can never share a
/// symbol with a post-write goal. The discriminant spelling FAILS this check, which is
/// why v1 has no `is_some` template.
#[test]
fn every_term_is_rebound_by_a_write_to_its_field_and_a_discriminant_is_not() {
    let k = adt("c::K", kitchen_fields());
    let f = func(
        "c::K::touch",
        vec![Ty::Unit, mut_ref(k)],
        1,
        vec![blk(0, vec![], Terminator::Return)],
    );
    let sigma = obligations::sigma_of_root(&f, &kitchen_tinv(), &place(1, vec![Projection::Deref]));
    let mut checked = 0;
    for i in 0..kitchen_fields().len() {
        let field = crate::place_to_var_name(&f, &pointee_field(1, i));
        for t in sigma.value[i].iter().chain(&sigma.len[i]) {
            let Formula::Var(name, _) = t else { panic!("{t:?}") };
            assert!(
                crate::generate::dest_write_rebinds(&field, name),
                "{field} does not rebind {name}"
            );
            checked += 1;
        }
        let discr = crate::discriminant_formula_var_name(&field);
        assert!(
            !crate::generate::dest_write_rebinds(&field, &discr),
            "{field}: the discriminant name {discr} is now versioned with its place; 8e may start"
        );
    }
    assert_eq!(checked, 6, "a, b, c values; e, f, g lengths");
}

/// The discriminant false-proof canary: `alt <=> is_some(saved)` would "preserve"
/// through `self.saved = Some(..)` because the discriminant symbol is shared between
/// entry and post-write. No conjunct may read either field.
#[test]
fn option_and_bool_fields_get_no_conjunct_only_a_note() {
    const A: &str = "c::A";
    let a_ty = adt(A, vec![("alt", Ty::Bool), ("saved", option_ty(vec_ty())), ("k", uint(64))]);
    let ctor = func(
        "c::A::new",
        vec![a_ty.clone(), Ty::Bool, option_ty(vec_ty())],
        2,
        vec![blk(
            0,
            vec![assign(Place::local(0), agg(A, vec![mv(1), mv(2), uk(3, 64)]))],
            Terminator::Return,
        )],
    );
    let set = synthesize(A, &[ctor]).expect("synthesizes");
    assert!(!set.templates.is_empty());
    for t in &set.templates {
        assert!(fields_of(t).iter().all(|f| *f == 2), "{t:?} reads alt or saved");
    }
    assert!(set.notes.iter().any(|n| n.contains("`saved`") && n.contains("discriminant")));
    assert!(set.notes.iter().any(|n| n.contains("`alt`") && n.contains("8e")));
}

fn load_entry_fixture() -> VerifiableFunction {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/tinv_mut_pointee_entry_rename_mir.json"
    );
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("deserialize")
}

/// The entry-pinning contract steps 7 and 10 must follow (plan formula_construction 5),
/// on real MIR (`a::S { v: Vec<u8>, k: usize }`, `(*self).k = self.v.len()` at bb2[0]):
/// renaming the instantiated hypothesis at bb0[0] leaves it BARE, and a later
/// whole-formula rename at a post-write point re-stamps those bare names with the
/// post-write version (the `vac` hazard). Sealed at bb0[0], a later rename leaves it
/// alone.
#[test]
fn an_entry_hypothesis_left_bare_is_restamped_and_a_sealed_one_is_not() {
    let func = load_entry_fixture();
    let tinv = TinvType {
        def_path: "a::S".into(),
        fields: vec![("v".into(), vec_ty()), ("k".into(), uint(64))],
        conjuncts: Vec::new(),
    };
    let c = CandidateConjunct { id: 0, formula: Template::LeLen { a: 1, g: 0 }.formula() };
    let sigma = obligations::sigma_of_root(&func, &tinv, &place(1, vec![Projection::Deref]));
    let hyp = instantiate(&c, &sigma).expect("k <= len(v) is statable on *self");
    assert!(format!("{hyp:?}").contains("\"self*.1\""), "{hyp:?}");

    let sv = crate::generate::stmt_versions_for(&func);
    let at_entry = crate::generate::version_rename_at(&hyp, &sv, &func, BlockId(0), 0);
    assert_eq!(at_entry, hyp, "at bb0[0] every read is the entry version: the rename is bare");

    let restamped = crate::generate::version_rename_at(&at_entry, &sv, &func, BlockId(2), 1);
    assert!(
        format!("{restamped:?}").contains("\"self*.1#"),
        "a bare entry hypothesis is re-stamped with the post-write version: {restamped:?}"
    );

    let sealed = crate::generate::seal_bare_reads(&sv, &func, BlockId(0), 0, at_entry)
        .expect("no `#` collision");
    assert!(!format!("{sealed:?}").contains("\"self*.1\""), "sealed: {sealed:?}");
    let later = crate::generate::version_rename_at(&sealed, &sv, &func, BlockId(2), 1);
    assert_eq!(later, sealed, "a sealed hypothesis is never re-stamped");
}

#[test]
fn eval_is_exact_three_valued_and_never_true_on_overflow() {
    let prod = Template::LenEqProd { f: 0, g: 1, h: 2 }.formula();
    let val = |len, g, h| FieldValuation { value: vec![None, g, h], len: vec![len, None, None] };
    assert_eq!(eval(&prod, &val(Some(6), Some(2), Some(3))), Some(true));
    assert_eq!(eval(&prod, &val(Some(5), Some(2), Some(3))), Some(false));
    // 2^64 * 2^64 overflows i128 (2^62 * 2^62 = 2^124 would not).
    let big = Some(1i128 << 64);
    assert_eq!(eval(&prod, &val(Some(0), big, big)), None, "overflow is unknown, never true");
    assert_eq!(eval(&prod, &val(Some(6), None, Some(3))), None, "a missing term is unknown");
    assert_eq!(
        eval(&prod, &val(Some(-1), Some(0), Some(0))),
        None,
        "a negative length is no length"
    );

    let le = Template::Le { a: 0, b: 1 }.formula();
    let ab = |a, b| FieldValuation { value: vec![a, b], len: vec![None, None] };
    let and = |xs: Vec<Formula>| Formula::And(xs);
    let f_false = Formula::Bool(false);
    assert_eq!(eval(&and(vec![le.clone(), f_false.clone()]), &ab(None, Some(1))), Some(false));
    assert_eq!(eval(&and(vec![le.clone(), Formula::Bool(true)]), &ab(None, Some(1))), None);
    assert_eq!(
        eval(&Formula::Or(vec![le.clone(), Formula::Bool(true)]), &ab(None, Some(1))),
        Some(true)
    );
    assert_eq!(
        eval(&Formula::Implies(Box::new(f_false), Box::new(le.clone())), &ab(None, None)),
        Some(true)
    );
    // Not a placeholder, outside the language, or ill-sorted: unknown.
    let other =
        Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(1)));
    assert_eq!(eval(&other, &ab(Some(0), Some(0))), None);
    let bv = Formula::Le(
        Box::new(Formula::BitVec { value: 1, width: 8 }),
        Box::new(field_var(FieldTerm::Value(0))),
    );
    assert_eq!(eval(&bv, &ab(Some(0), Some(0))), None);
    let ill = Formula::Lt(Box::new(Formula::Bool(true)), Box::new(Formula::Int(1)));
    assert_eq!(eval(&ill, &ab(None, None)), None);
}

#[test]
fn templates_display_in_source_terms() {
    let fields: Vec<(String, Ty)> =
        ["grid", "cols", "rows"].iter().map(|n| ((*n).to_string(), uint(16))).collect();
    let cases = [
        (Template::GeConst { f: 2, c: 1 }, "1 <= rows"),
        (Template::LeConst { f: 2, c: 1000 }, "rows <= 1000"),
        (Template::Lt { a: 1, b: 2 }, "cols < rows"),
        (Template::Le { a: 1, b: 2 }, "cols <= rows"),
        (Template::LeLen { a: 1, g: 0 }, "cols <= len(grid)"),
        (Template::LenEqProd { f: 0, g: 1, h: 2 }, "len(grid) == cols * rows"),
    ];
    for (t, s) in cases {
        assert_eq!(t.display(&fields), s);
    }
}

/// G16: every conjunct of the P1-P3 seeds is in the template language: Int
/// comparisons, `*`, literals and placeholder variables, with no bit-vector node and no
/// cast. And a bit-vector-sorted term is not lifted: `instantiate` refuses it.
#[test]
fn every_conjunct_is_in_the_int_template_language_and_bitvectors_are_refused() {
    fn walk(f: &Formula) {
        if let Formula::Var(..) = f {
            assert!(super::super::as_field_var(f).is_some(), "{f:?} is not a placeholder");
            return;
        }
        assert!(!matches!(f, Formula::BitVec { .. }), "{f:?}");
        let kids = super::super::admitted_children(f)
            .unwrap_or_else(|| panic!("{f:?} outside the language"));
        kids.into_iter().for_each(walk);
    }
    let sets = [
        synthesize(SCREEN, &[screen_new(), screen_down()]).expect("P2"),
        synthesize(PARSER, &[parse_fn()]).expect("P1"),
        synthesize(GRID, &[grid_new()]).expect("P3"),
    ];
    for set in &sets {
        assert!(!set.ty.conjuncts.is_empty());
        for c in &set.ty.conjuncts {
            walk(&c.formula);
        }
    }
    let c = CandidateConjunct { id: 0, formula: Template::GeConst { f: 0, c: 1 }.formula() };
    let bv_sigma =
        Sigma { value: vec![Some(Formula::Var("x.0".into(), Sort::BitVec(16)))], len: vec![None] };
    assert_eq!(instantiate(&c, &bv_sigma), None, "no BvToInt lift: a BitVec term is unstatable");
}

// ---------------------------------------------------------------------------------------
// 8b: templates on the positive shapes
// ---------------------------------------------------------------------------------------

#[test]
fn p2_screen_seeds_the_dimension_and_cursor_bounds() {
    let set = synthesize(SCREEN, &[screen_new()]).expect("synthesizes");
    for want in
        ["1 <= rows", "rows <= 1000", "1 <= cols", "cols <= 1000", "row < rows", "col < cols"]
    {
        assert!(has(&set, want), "missing `{want}` in {:?}", displayed(&set));
    }
    // The site's literals delete what they falsify.
    assert!(!has(&set, "1 <= row"), "row = 0 at the constructor");
    assert!(has(&set, "row <= 0"));
    assert!(!has(&set, "0 <= rows"), "implied by the type: never generated");
    assert!(set.notes.iter().any(|n| n.contains("pre-filter")));
    assert!(set.const_witnesses.is_empty(), "cols/rows are not literals at the constructor");
}

#[test]
fn p2_derived_default_and_clone_are_sites_and_default_deletes_what_zero_falsifies() {
    let set = synthesize(SCREEN, &[screen_new(), screen_default(), screen_clone()]).expect("ok");
    let fns: Vec<&str> = set.sites.iter().map(|s| s.function.as_str()).collect();
    assert_eq!(
        fns,
        [
            "c::<impl core::clone::Clone for c::Screen>::clone",
            "c::<impl core::default::Default for c::Screen>::default",
            "c::Screen::new",
        ],
        "every construction is a site, derived bodies included (rail 28)"
    );
    for gone in ["1 <= rows", "row < rows", "1 <= cols"] {
        assert!(!has(&set, gone), "`{gone}` is false at Default (all zero)");
    }
    for kept in ["rows <= 1000", "row <= rows", "cols <= 1000"] {
        assert!(has(&set, kept), "`{kept}` holds at every site");
    }
    // Default is the one all-known site: its valuation is a non-vacuity witness, and
    // every surviving conjunct holds on it.
    assert_eq!(set.const_witnesses.len(), 1);
    let (site, w) = &set.const_witnesses[0];
    assert_eq!(site.function, "c::<impl core::default::Default for c::Screen>::default");
    assert!(w.is_complete_and_in_range(&set.shapes));
    let all = Formula::And(set.ty.conjuncts.iter().map(|c| c.formula.clone()).collect());
    assert_eq!(eval(&all, w), Some(true));
}

#[test]
fn p1_parser_seeds_i_le_len_b_over_the_slice_carrier() {
    let set = synthesize(PARSER, &[parse_fn()]).expect("synthesizes");
    assert_eq!(set.shapes[0], FieldShape::Len(LenCarrier::SliceRef));
    assert!(has(&set, "i <= len(b)"), "{:?}", displayed(&set));
    // It instantiates on a `&mut P` root with step 7.4's terms.
    let f = func(
        "c::P::bump",
        vec![Ty::Unit, mut_ref(parser_ty())],
        1,
        vec![blk(0, vec![], Terminator::Return)],
    );
    let sigma = obligations::sigma_of_root(&f, &set.ty, &place(1, vec![Projection::Deref]));
    let id =
        set.templates.iter().position(|t| *t == Template::LeLen { a: 1, g: 0 }).expect("present");
    let inst = instantiate(&set.ty.conjuncts[id], &sigma).expect("statable");
    let shown = format!("{inst:?}");
    assert!(shown.contains("__slice_len"), "{shown}");
}

#[test]
fn p3_grid_seeds_len_eq_prod_once_and_flags_it_uncertifiable() {
    let set = synthesize(GRID, &[grid_new()]).expect("synthesizes");
    let prods: Vec<&Template> =
        set.templates.iter().filter(|t| matches!(t, Template::LenEqProd { .. })).collect();
    assert_eq!(
        prods,
        [
            &Template::LenEqProd { f: 0, g: 1, h: 1 },
            &Template::LenEqProd { f: 0, g: 1, h: 2 },
            &Template::LenEqProd { f: 0, g: 2, h: 2 },
        ],
        "cols*rows once (g <= h), never also rows*cols"
    );
    assert!(has(&set, "len(grid) == cols * rows"));
    assert!(prods.iter().all(|t| !t.kernel_certifiable_today()));
    assert!(
        set.templates
            .iter()
            .filter(|t| !matches!(t, Template::LenEqProd { .. }))
            .all(Template::kernel_certifiable_today)
    );
    assert!(set.notes.iter().any(|n| n.contains("0(b)")));
}

#[test]
fn the_prefilter_only_deletes_conjuncts_a_literal_site_falsifies() {
    const I: &str = "c::I";
    let i_ty = adt(I, vec![("i", i64_ty())]);
    let mk = |name: &str, v: i128| {
        func(
            name,
            vec![i_ty.clone()],
            0,
            vec![blk(0, vec![assign(Place::local(0), agg(I, vec![ik(v)]))], Terminator::Return)],
        )
    };
    let set = synthesize(I, &[mk("c::zero", 0), mk("c::five", 5)]).expect("ok");
    for kept in ["0 <= i", "i <= 5"] {
        assert!(has(&set, kept), "{kept}: {:?}", displayed(&set));
    }
    for gone in ["i <= 0", "i <= 1", "1 <= i", "5 <= i"] {
        assert!(!has(&set, gone), "{gone}");
    }
    assert_eq!(set.const_witnesses.len(), 2);
    for (_, w) in &set.const_witnesses {
        for c in &set.ty.conjuncts {
            assert_eq!(eval(&c.formula, w), Some(true));
        }
    }
}

/// Property: on random all-literal constructions, every surviving conjunct is true at
/// every site, and every site is a witness.
#[test]
fn prefilter_survivors_hold_at_every_random_literal_site() {
    const R: &str = "c::R";
    let r_ty = adt(R, vec![("a", uint(8)), ("b", uint(8)), ("c", uint(8))]);
    let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..40 {
        let n = usize::try_from(next() % 4).unwrap_or(0) + 1;
        let mut sites = Vec::new();
        let mut inventory = Vec::new();
        for j in 0..n {
            let vals: Vec<u128> = (0..3).map(|_| u128::from(next() % 256)).collect();
            inventory.push(func(
                &format!("c::mk{j}"),
                vec![r_ty.clone()],
                0,
                vec![blk(
                    0,
                    vec![assign(Place::local(0), agg(R, vals.iter().map(|v| uk(*v, 8)).collect()))],
                    Terminator::Return,
                )],
            ));
            sites.push(vals);
        }
        let set = synthesize(R, &inventory).expect("ok");
        assert_eq!(set.const_witnesses.len(), n);
        for vals in &sites {
            let v = FieldValuation {
                value: vals.iter().map(|x| i128::try_from(*x).ok()).collect(),
                len: vec![None; 3],
            };
            for (c, t) in set.ty.conjuncts.iter().zip(&set.templates) {
                assert_eq!(eval(&c.formula, &v), Some(true), "{t:?} at {vals:?}");
            }
        }
    }
}

// ---------------------------------------------------------------------------------------
// 8b: the constant pool
// ---------------------------------------------------------------------------------------

fn pools_of(ty: &str, inventory: &[VerifiableFunction]) -> (Vec<BTreeSet<i128>>, Vec<String>) {
    let order: Vec<&VerifiableFunction> = inventory.iter().collect();
    let mut scanned = Vec::new();
    for (fi, f) in order.iter().enumerate() {
        scanned.extend(scan(f, ty, false).expect("scans").into_iter().map(|s| (fi, s)));
    }
    let fields = scanned[0].1.fields.clone();
    let shapes: Vec<FieldShape> = fields.iter().map(|(n, t)| classify_field(n, t).0).collect();
    let mut notes = Vec::new();
    let pools = constant_pools(&order, ty, &scanned, &shapes, &fields, &mut notes);
    (pools, notes)
}

#[test]
fn pool_reads_clamp_comparison_and_store_constants() {
    let (pools, _) = pools_of(SCREEN, &[screen_new(), screen_down()]);
    assert_eq!(pools[0], BTreeSet::from([0, 1, 1000]), "cols: clamp(1, 1000) and 0/1");
    assert_eq!(pools[1], BTreeSet::from([0, 1, 1000]));
    assert_eq!(pools[2], BTreeSet::from([0, 1, 6, 7, 8, 42]), "row: `row < 7` and `row = 42`");
    assert_eq!(pools[3], BTreeSet::from([0, 1]));
}

#[test]
fn pool_refuses_inverted_clamp_user_ord_and_out_of_range_constants() {
    // clamp(x, 9, 3) panics: it bounds nothing.
    let mut f = screen_new();
    if let Terminator::Call { args, .. } = &mut f.body.blocks[0].terminator {
        args[1] = uk(9, 16);
        args[2] = uk(3, 16);
    }
    let (pools, _) = pools_of(SCREEN, &[f]);
    assert_eq!(pools[0], BTreeSet::from([0, 1]));

    // NAME-ANCHOR-2: the trait path is std's, but `Self` (the destination) is a user
    // ADT, so the impl that runs is the user's.
    const E: &str = "c::E";
    let e_ty = adt(E, vec![("0", uint(8))]);
    let user = func(
        "c::user",
        vec![Ty::Unit, e_ty.clone(), e_ty],
        1,
        vec![blk(
            0,
            vec![],
            call(
                "<c::E as core::cmp::Ord>::clamp",
                vec![mv(1), uk(1, 8), uk(5, 8)],
                Place::local(2),
                1,
            ),
        )],
    );
    assert!(ord_constants(&user, &user.body.blocks[0].terminator).is_empty());

    // `row < 0` on an unsigned field: `-1` is out of range and dropped.
    let mut down = screen_down();
    if let Statement::Assign { rvalue: Rvalue::BinaryOp(_, _, c), .. } =
        &mut down.body.blocks[0].stmts[1]
    {
        *c = uk(0, 16);
    }
    let (pools, _) = pools_of(SCREEN, &[screen_new(), down]);
    assert!(pools[2].iter().all(|c| *c >= 0), "{:?}", pools[2]);
}

#[test]
fn pool_is_capped_at_the_smallest_and_largest_four() {
    const I: &str = "c::I";
    let i_ty = adt(I, vec![("i", i64_ty())]);
    let n = 10usize;
    // `_t = copy (*_1).0; _{t+1} = Eq(move _t, const 100*(k+1))`, through distinct temps
    // so each has a unique definition.
    let mut locals = vec![Ty::Unit, shared_ref(i_ty.clone())];
    locals.extend((0..2 * n).map(|k| if k % 2 == 0 { i64_ty() } else { Ty::Bool }));
    let stmts: Vec<Statement> = (0..n)
        .flat_map(|k| {
            let t = 2 + 2 * k;
            let c = 100 * (i128::try_from(k).unwrap_or(0) + 1);
            [
                assign(Place::local(t), Rvalue::Use(Operand::Copy(pointee_field(1, 0)))),
                assign(Place::local(t + 1), Rvalue::BinaryOp(BinOp::Eq, mv(t), ik(c))),
            ]
        })
        .collect();
    let user = func("c::I::many", locals, 1, vec![blk(0, stmts, Terminator::Return)]);
    let ctor = func(
        "c::I::new",
        vec![i_ty],
        0,
        vec![blk(0, vec![assign(Place::local(0), agg(I, vec![ik(0)]))], Terminator::Return)],
    );
    let (pools, notes) = pools_of(I, &[ctor, user]);
    assert_eq!(pools[0], BTreeSet::from([0, 1, 99, 100, 901, 999, 1000, 1001]));
    assert_eq!(pools[0].len(), MAX_POOL_PER_FIELD);
    assert!(notes.iter().any(|n| n.contains("32 constants, kept the 4 smallest and 4 largest")));
}

// ---------------------------------------------------------------------------------------
// 8b: construction sites and refusals
// ---------------------------------------------------------------------------------------

#[test]
fn sites_are_s_aggregates_only() {
    // A ctor shim: the arguments straight into the aggregate.
    let shim = func(
        "c::Screen::{constructor#0}",
        vec![screen_ty(), uint(16), uint(16), uint(16), uint(16)],
        4,
        vec![blk(
            0,
            vec![assign(Place::local(0), agg(SCREEN, vec![mv(1), mv(2), mv(3), mv(4)]))],
            Terminator::Return,
        )],
    );
    assert_eq!(construction_sites(&shim, SCREEN).expect("ok").len(), 1);
    // The same shape under another name is not a site of `Screen`.
    let other_ty = adt(
        "c::Other",
        vec![("cols", uint(16)), ("rows", uint(16)), ("row", uint(16)), ("col", uint(16))],
    );
    let other = func(
        "c::Other::new",
        vec![other_ty, uint(16)],
        1,
        vec![blk(
            0,
            vec![assign(Place::local(0), agg("c::Other", vec![mv(1), mv(1), mv(1), mv(1)]))],
            Terminator::Return,
        )],
    );
    assert_eq!(construction_sites(&other, SCREEN).expect("ok"), Vec::new());
}

fn one_stmt(locals: Vec<Ty>, stmt: Statement) -> VerifiableFunction {
    func("c::f", locals, 0, vec![blk(0, vec![stmt], Terminator::Return)])
}

#[test]
fn a_constant_that_may_hold_s_refuses() {
    let refuses = |f: &VerifiableFunction, known: bool| {
        assert!(
            matches!(
                construction_sites(f, SCREEN),
                Err(CandidateRefusal::ConstantConstruction { position_known, .. }) if position_known == known
            ),
            "{:?}",
            construction_sites(f, SCREEN)
        );
    };
    // `_1 = const <Screen>`: a const item or a GVN-folded literal.
    let opaque = Operand::Constant(ConstValue::opaque_const());
    refuses(
        &one_stmt(
            vec![Ty::Unit, screen_ty()],
            assign(Place::local(1), Rvalue::Use(opaque.clone())),
        ),
        true,
    );
    // Inside another aggregate, at a field typed `Screen`.
    let owner = adt("c::Owner", vec![("s", screen_ty())]);
    refuses(
        &one_stmt(
            vec![Ty::Unit, owner],
            assign(Place::local(1), agg("c::Owner", vec![opaque.clone()])),
        ),
        true,
    );
    // A unit struct is a constant: any constant at an `S`-typed position refuses.
    const U: &str = "c::U";
    let unit = func(
        "c::u",
        vec![Ty::Unit, adt(U, vec![])],
        0,
        vec![blk(
            0,
            vec![assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::Unit)))],
            Terminator::Return,
        )],
    );
    assert!(matches!(
        construction_sites(&unit, U),
        Err(CandidateRefusal::ConstantConstruction { position_known: true, .. })
    ));
    // An opaque call argument may be an `S` value: its position is not typed here.
    let arg = func(
        "c::g",
        vec![Ty::Unit],
        0,
        vec![
            blk(0, vec![], call("c::use_s", vec![opaque.clone()], Place::local(0), 1)),
            blk(1, vec![], Terminator::Return),
        ],
    );
    refuses(&arg, false);
    // A `&Screen` scalar-field constant names `S` itself.
    let sref = Operand::Constant(ConstValue::struct_scalar_fields_ref(SCREEN, vec![]));
    let sref_arg = func(
        "c::g",
        vec![Ty::Unit],
        0,
        vec![
            blk(0, vec![], call("c::use_s", vec![sref], Place::local(0), 1)),
            blk(1, vec![], Terminator::Return),
        ],
    );
    refuses(&sref_arg, false);

    // Scalars and strings hold no `S`, wherever they are; an opaque constant at a
    // position typed away from `S` is not one either.
    let fine = func(
        "c::h",
        vec![Ty::Unit, uint(16), slice_ref()],
        0,
        vec![
            blk(
                0,
                vec![
                    assign(Place::local(1), Rvalue::Use(uk(3, 16))),
                    assign(Place::local(2), Rvalue::Use(opaque)),
                ],
                call(
                    "core::panicking::panic",
                    vec![Operand::Constant(ConstValue::Str { bytes: b"x".to_vec() })],
                    Place::local(0),
                    1,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    );
    assert_eq!(construction_sites(&fine, SCREEN), Ok(Vec::new()));
}

#[test]
fn refusals_withhold_the_type() {
    // No aggregate anywhere.
    assert_eq!(synthesize(SCREEN, &[screen_down()]), Err(CandidateRefusal::NoConstructor));

    // The destination does not resolve to `S`.
    let unresolved =
        one_stmt(vec![Ty::Unit, Ty::Unit], assign(Place::local(1), agg(SCREEN, vec![])));
    assert!(matches!(
        construction_sites(&unresolved, SCREEN),
        Err(CandidateRefusal::Unresolved { .. })
    ));

    // An `S` place assigned by a cast: a construction this scan cannot see.
    let cast = one_stmt(
        vec![Ty::Unit, screen_ty(), uint(64)],
        assign(Place::local(1), Rvalue::Cast(mv(2), screen_ty())),
    );
    assert!(matches!(construction_sites(&cast, SCREEN), Err(CandidateRefusal::Unresolved { .. })));

    // An enum, a variant other than 0, an active field.
    const E: &str = "c::E";
    let e = adt_kind(E, vec![("0", uint(8))], AdtKind::Enum);
    let enum_ctor =
        one_stmt(vec![Ty::Unit, e.clone()], assign(Place::local(1), agg(E, vec![uk(1, 8)])));
    assert!(matches!(construction_sites(&enum_ctor, E), Err(CandidateRefusal::NotAStruct { .. })));
    for (variant, active_field) in [(1, None), (0, Some(0))] {
        let kind = AggregateKind::Adt { name: SCREEN.into(), variant, active_field, args: None };
        let f = one_stmt(
            vec![Ty::Unit, screen_ty()],
            assign(Place::local(1), Rvalue::Aggregate(kind, vec![uk(0, 16)])),
        );
        assert!(matches!(construction_sites(&f, SCREEN), Err(CandidateRefusal::NotAStruct { .. })));
    }

    // Two constructions that disagree on a field's type.
    let skewed_ty = adt(
        SCREEN,
        vec![("cols", i64_ty()), ("rows", uint(16)), ("row", uint(16)), ("col", uint(16))],
    );
    let skewed = func(
        "c::skewed",
        vec![skewed_ty, i64_ty(), uint(16)],
        2,
        vec![blk(
            0,
            vec![assign(Place::local(0), agg(SCREEN, vec![mv(1), mv(2), mv(2), mv(2)]))],
            Terminator::Return,
        )],
    );
    assert!(matches!(
        synthesize(SCREEN, &[screen_new(), skewed]),
        Err(CandidateRefusal::ShapeDisagrees { function }) if function == "c::skewed"
    ));
    // An operand count that is not the field count.
    let short = one_stmt(
        vec![Ty::Unit, screen_ty()],
        assign(Place::local(1), agg(SCREEN, vec![uk(0, 16)])),
    );
    assert!(matches!(
        construction_sites(&short, SCREEN),
        Err(CandidateRefusal::ShapeDisagrees { .. })
    ));

    // Twenty `u64` fields enumerate more than MAX_CONJUNCTS candidates.
    const W: &str = "c::W";
    let names: Vec<String> = (0..20).map(|i| format!("f{i}")).collect();
    let w_ty = adt(W, names.iter().map(|n| (n.as_str(), uint(64))).collect());
    let mut locals = vec![w_ty];
    locals.extend((0..20).map(|_| uint(64)));
    let wide = func(
        "c::W::new",
        locals,
        20,
        vec![blk(
            0,
            vec![assign(Place::local(0), agg(W, (1..=20).map(mv).collect()))],
            Terminator::Return,
        )],
    );
    assert!(matches!(
        synthesize(W, &[wide]),
        Err(CandidateRefusal::TooManyConjuncts { count }) if count > MAX_CONJUNCTS
    ));
}

#[test]
fn synthesis_is_independent_of_inventory_order() {
    let inv = vec![screen_down(), screen_new(), screen_clone(), screen_default()];
    let base = synthesize(SCREEN, &inv).expect("ok");
    let mut rev = inv.clone();
    rev.reverse();
    assert_eq!(synthesize(SCREEN, &rev).expect("ok"), base);
    let rotated: Vec<VerifiableFunction> = inv[2..].iter().chain(&inv[..2]).cloned().collect();
    assert_eq!(synthesize(SCREEN, &rotated).expect("ok"), base);
    let ids: Vec<u32> = base.ty.conjuncts.iter().map(|c| c.id).collect();
    assert_eq!(ids, (0..u32::try_from(ids.len()).unwrap_or(0)).collect::<Vec<_>>());
    assert_eq!(base.ty.def_path, SCREEN, "the key is the aggregate's crate-qualified name");
}

// ---------------------------------------------------------------------------------------
// Decision TINV-32: the compiler's per-body constant evidence
// ---------------------------------------------------------------------------------------

/// A body that passes an opaque constant (`for f in RUNGS`, `unwrap_or(Cell::BLANK)`) to a
/// call: the position is not typed, so without evidence it refuses every candidate.
fn opaque_arg_body(def_path: &str, c: ConstValue) -> VerifiableFunction {
    func(
        def_path,
        vec![Ty::Unit],
        0,
        vec![
            blk(
                0,
                vec![],
                call(
                    "core::iter::IntoIterator::into_iter",
                    vec![Operand::Constant(c)],
                    Place::local(0),
                    1,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

fn image_of(ty: Ty) -> ConstValue {
    let ConstValue::MemoryImage(mut image) = crate::memory_image_tests::image(1) else {
        unreachable!("the fixture is a memory image")
    };
    image.ty = ty;
    ConstValue::MemoryImage(image)
}

#[test]
fn b1_constant_evidence_clears_an_opaque_call_argument() {
    let rungs = image_of(Ty::Array { elem: Box::new(Ty::Float { width: 64 }), len: 6 });
    for c in [ConstValue::opaque_const(), rungs] {
        let inv = [opaque_arg_body("c::a_rungs", c), screen_new()];
        // No evidence: withheld, exactly as before.
        assert!(matches!(
            synthesize(SCREEN, &inv),
            Err(CandidateRefusal::ConstantConstruction { position_known: false, .. })
        ));
        assert!(matches!(
            synthesize_with_constant_evidence(SCREEN, &inv, &[false, false]),
            Err(CandidateRefusal::ConstantConstruction { position_known: false, .. })
        ));
        // A slice not parallel to the inventory is no evidence.
        assert!(matches!(
            synthesize_with_constant_evidence(SCREEN, &inv, &[true]),
            Err(CandidateRefusal::ConstantConstruction { .. })
        ));
        // Evidence for the body: synthesizes, with the same set as without the body.
        let set = synthesize_with_constant_evidence(SCREEN, &inv, &[true, false]).expect("ok");
        assert_eq!(set, synthesize(SCREEN, &[screen_new()]).expect("ok"));
    }
}

#[test]
fn b2_constant_evidence_is_per_type() {
    // One body; the evidence clears SCREEN for it but not PARSER (a constant of the body
    // reaches `c::P`): SCREEN synthesizes and PARSER is still refused.
    let inv =
        [opaque_arg_body("c::a_shared", ConstValue::opaque_const()), screen_new(), parse_fn()];
    assert!(synthesize_with_constant_evidence(SCREEN, &inv, &[true, false, false]).is_ok());
    assert!(matches!(
        synthesize_with_constant_evidence(PARSER, &inv, &[false, false, false]),
        Err(CandidateRefusal::ConstantConstruction { position_known: false, .. })
    ));
}

#[test]
fn b3_evidence_never_clears_where_the_extraction_says_s() {
    // `_1 = const <Screen>`: a position typed exactly S. Evidence claiming the body's
    // constants hold no S contradicts MIR typing, so the refusal stands.
    let at_s = one_stmt(
        vec![Ty::Unit, screen_ty()],
        assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::opaque_const()))),
    );
    // ... and at a position that reaches S (`Option<Screen>`).
    let at_option_s = one_stmt(
        vec![Ty::Unit, option_ty(screen_ty())],
        assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::opaque_const()))),
    );
    // A memory image whose (diagnostic) type IS S, passed to a call.
    let image_s = opaque_arg_body("c::a_image", image_of(screen_ty()));
    for body in [at_s, at_option_s, image_s] {
        assert!(
            matches!(
                synthesize_with_constant_evidence(
                    SCREEN,
                    &[body.clone(), screen_new()],
                    &[true, true]
                ),
                Err(CandidateRefusal::ConstantConstruction { .. })
            ),
            "{}",
            body.def_path
        );
    }
}

#[test]
fn b4_evidence_never_clears_a_symbolic_or_unsupported_operand() {
    for op in [
        Operand::Symbolic(Formula::Bool(true)),
        Operand::unsupported("Const", "unsupported constant of MIR type Cell".to_string()),
    ] {
        let body = func(
            "c::a_opaque",
            vec![Ty::Unit],
            0,
            vec![
                blk(0, vec![], call("c::use_it", vec![op], Place::local(0), 1)),
                blk(1, vec![], Terminator::Return),
            ],
        );
        assert!(matches!(
            synthesize_with_constant_evidence(SCREEN, &[body, screen_new()], &[true, true]),
            Err(CandidateRefusal::ConstantConstruction { position_known: false, .. })
        ));
    }
}

#[test]
fn b5_evidence_clears_a_known_position_of_unknown_reach() {
    // A constant stored into a local whose extracted type is an undefined datatype marker
    // (reach Unknown): refused without evidence, cleared with it. A memory image (an
    // extracted rustc constant); an `OpaqueConst` whole rvalue is b6's case.
    let unknown = Ty::Datatype { name: "c::Gone".into(), variants: vec![] };
    let body = one_stmt(
        vec![Ty::Unit, unknown],
        assign(Place::local(1), Rvalue::Use(Operand::Constant(image_of(uint(8))))),
    );
    let inv = [body, screen_new()];
    assert!(matches!(
        synthesize_with_constant_evidence(SCREEN, &inv, &[false, false]),
        Err(CandidateRefusal::ConstantConstruction { position_known: true, .. })
    ));
    assert!(synthesize_with_constant_evidence(SCREEN, &inv, &[true, false]).is_ok());
}

#[test]
fn b6_evidence_never_clears_an_opaque_const_whole_rvalue() {
    // The extractor lowers a `Box<T> -> Box<dyn Trait>` unsize (and other non-constant
    // rvalues) to `Rvalue::Use(Operand::Constant(OpaqueConst))`: no rustc constant
    // stands behind it, so the census's evidence does not cover it.
    let unknown = Ty::Datatype { name: "c::Gone".into(), variants: vec![] };
    let body = one_stmt(
        vec![Ty::Unit, unknown],
        assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::opaque_const()))),
    );
    assert!(matches!(
        synthesize_with_constant_evidence(SCREEN, &[body, screen_new()], &[true, true]),
        Err(CandidateRefusal::ConstantConstruction { position_known: true, .. })
    ));
}

#[test]
fn b7_evidence_never_clears_a_struct_constant_of_s() {
    // A scalar-field struct constant whose ADT is `S` (or holds one in a field) passed to
    // a call: the extraction itself says it is an `S`.
    for c in [
        ConstValue::struct_scalar_fields_ref(SCREEN, vec![]),
        ConstValue::struct_scalar_fields_ref(
            "c::Outer",
            vec![ConstValue::struct_scalar_fields_ref(SCREEN, vec![])],
        ),
    ] {
        let body = opaque_arg_body("c::a_struct", c);
        assert!(matches!(
            synthesize_with_constant_evidence(SCREEN, &[body, screen_new()], &[true, true]),
            Err(CandidateRefusal::ConstantConstruction { position_known: false, .. })
        ));
    }
}
