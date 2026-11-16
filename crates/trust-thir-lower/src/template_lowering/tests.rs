//! Unit tests for the level-S template lane (step 6.5.1). TyCtxt-free: the sentinel modules are
//! built by hand, as `rmeta_entry/tests.rs::per_body_module` builds its modules. The rustc half
//! (`capture`, the template-mode arms of `LowerCx`) is pinned end to end by
//! `tests/run-make/trust-ir-template-encode`.

use trust_ir::template::{TEMPLATE_BODY_NAME, TemplateError};
use trust_ir::{
    Block, BlockId, ClosureTy, Constant, ConstantG, DropGlueEntry, EnumDef, EnumId, EnumVariant,
    FieldDef, FuncId, FuncTy, FuncTyId, Function, Global, Inst, InstG, InstrNode, Linkage, Module,
    ParamId, RecordDef, RecordId, StructDef, StructId, StructRepr, TemplateRef,
    TupleLayoutDescriptor, Ty, TyG, TyId, ValueId,
};
use trust_ir_build::template::{TemplateViolation, validate_template};

use super::*;

fn v(i: u32) -> ValueId {
    ValueId::new(i)
}

fn node(inst: Inst) -> InstrNode {
    InstrNode::new(inst)
}

fn node_r(inst: Inst, r: u32) -> InstrNode {
    InstrNode::new(inst).with_result(v(r))
}

fn t0() -> Ty {
    type_param_sentinel(0)
}

fn ext0() -> TyG<TemplateRef> {
    TyG::Ext(TemplateRef::Param(ParamId::new(0)))
}

/// A one-function sentinel module: `fn(params..) -> returns` whose entry block binds `v0..` to
/// the parameters and runs `body`.
fn sentinel_module(params: Vec<Ty>, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("dep");
    let ty = module
        .add_func_type(FuncTy { params: params.clone(), returns, is_vararg: false, abi: None })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::new(FuncId::new(0), "dep::ident", ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    for (i, p) in params.into_iter().enumerate() {
        b = b.with_param(v(i as u32), p);
    }
    b.body = body;
    f.blocks = vec![b];
    module.functions.push(f);
    module
}

/// `ident<T>(x: T) -> T { x }`, in sentinels.
fn ident_module() -> Module {
    sentinel_module(vec![t0()], vec![t0()], vec![node(Inst::Return { values: vec![v(0)] })])
}

fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "arm64-apple-macosx11.0.0".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

fn type_facts() -> LaneFacts {
    LaneFacts { params: vec![LaneParam::Type], ..LaneFacts::default() }
}

fn abstracted(module: &Module, facts: &LaneFacts) -> Result<Template, EntryRefusal> {
    abstract_template(module, facts, "dep::ident".to_string())
}

/// A template built by the level map alone, with no escape check (the teeth of test 2).
fn unchecked(module: &Module, facts: &LaneFacts) -> Template {
    finish_template(level_map(module, facts).expect("the level map"), facts, "dep::x".to_string())
        .expect("a body")
}

// ---------------------------------------------------------------------------------------- 1

/// A type parameter's sentinel becomes `$0` wherever the level map reaches: a block parameter, a
/// signature row, a type row (through every nesting `TyG` has), an instruction's type and a
/// global's type. Fails if any arm of `abstract_ty` drops or keeps a sentinel. A parameter-typed
/// global is refused by the escape check in 6.5.1 (T2: no hole row; test 2), so the global's arm
/// is measured on the level map alone.
#[test]
fn a_type_parameter_sentinel_becomes_a_template_parameter_in_every_mapped_table() {
    let nested = Ty::Tuple(vec![
        Ty::Ref(Box::new(t0())),
        Ty::RefMut(Box::new(t0())),
        Ty::PtrConst(Box::new(t0())),
        Ty::PtrMut(Box::new(t0())),
        Ty::Rc(Box::new(t0())),
        Ty::Vector(Box::new(t0()), 4),
        Ty::Tuple(vec![Ty::U8, t0()]),
    ]);
    let mut module = sentinel_module(
        vec![t0()],
        vec![t0()],
        vec![
            node_r(Inst::Alloca { ty: t0(), count: None, align: None }, 1),
            node(Inst::Return { values: vec![v(0)] }),
        ],
    );
    module.types.push(nested.clone());
    let t = abstracted(&module, &type_facts()).expect("abstracts");
    let mut with_global = module.clone();
    with_global.globals.push(Global {
        name: "__trust_promoted_0".to_string(),
        ty: t0(),
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let level_mapped = unchecked(&with_global, &type_facts());
    let expected_nested = TyG::Tuple(vec![
        TyG::Ref(Box::new(ext0())),
        TyG::RefMut(Box::new(ext0())),
        TyG::PtrConst(Box::new(ext0())),
        TyG::PtrMut(Box::new(ext0())),
        TyG::Rc(Box::new(ext0())),
        TyG::Vector(Box::new(ext0()), 4),
        TyG::Tuple(vec![TyG::U8, ext0()]),
    ]);
    assert_eq!(t.module.types, vec![expected_nested], "a type row, through every nesting");
    assert_eq!(t.module.func_types[0].params, vec![ext0()], "a signature row");
    assert_eq!(t.module.func_types[0].returns, vec![ext0()]);
    assert_eq!(t.module.functions[0].blocks[0].params[0].1, ext0(), "a block parameter");
    assert!(
        matches!(&t.module.functions[0].blocks[0].body[0].inst, InstG::Alloca { ty, .. } if *ty == ext0()),
        "an instruction's type"
    );
    assert_eq!(level_mapped.module.globals[0].ty, ext0(), "a global's type");
    assert_eq!(
        abstracted(&with_global, &type_facts()).expect_err("refused").reason(),
        "invalid(sentinel in the type of global row 0 (T2: no hole row in 6.5.1))",
        "and the escape check refuses a parameter-typed global"
    );
    assert_eq!(t.header.params, vec![TemplateParam::Type]);
    assert!(!format!("{:?}", t.module).contains("Dialect"), "no sentinel survives the map");
}

// ---------------------------------------------------------------------------------------- 2

/// The escape check: a sentinel in a table the level map CLONES is refused, `template-unsupported`
/// in a struct or enum row registered from parameter args and `invalid` anywhere else; a
/// non-empty `universes` or `predicates` is `template-unsupported`. Since the 2026-10-13
/// amendment: a struct or enum row registered from parameter args is `template-unsupported`
/// with no visible sentinel too; a sentinel reached only as a slice's element row is seen; and a
/// declaration's signature or a global's type that names a parameter is `invalid` (T2). The
/// teeth: the same template built by the level map alone passes `validate_template` (measured
/// per case below), so the escape check is the only rule that refuses it.
#[test]
fn a_sentinel_in_a_copied_table_refuses() {
    let base = ident_module;
    let class = |r: Result<Template, EntryRefusal>| -> String { r.expect_err("refused").reason() };
    let mut cases: Vec<(&str, Module, LaneFacts, &str)> = Vec::new();

    let mut m = base();
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "Wrapper".to_string(),
        fields: vec![FieldDef { name: "0".to_string(), ty: t0(), offset: None }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let mut param_rows = type_facts();
    param_rows.param_adt_structs.insert(0);
    cases.push((
        "a struct row from parameter args",
        m.clone(),
        param_rows,
        "template-unsupported(parameter-dependent ADT row (6.5.2))",
    ));
    cases.push((
        "a struct row",
        m,
        type_facts(),
        "invalid(sentinel in ground table structs row 0)",
    ));

    let mut m = base();
    m.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![EnumVariant { name: "A".to_string(), fields: vec![t0()], field_names: Vec::new() }],
    ));
    let mut param_rows = type_facts();
    param_rows.param_adt_enums.insert(0);
    cases.push((
        "an enum row from parameter args",
        m.clone(),
        param_rows,
        "template-unsupported(parameter-dependent ADT row (6.5.2))",
    ));
    cases.push(("an enum row", m, type_facts(), "invalid(sentinel in ground table enums row 0)"));

    let mut m = base();
    m.records.push(RecordDef {
        id: RecordId::new(0),
        name: "R".to_string(),
        fields: vec![FieldDef { name: "f".to_string(), ty: t0(), offset: None }],
    });
    cases.push((
        "a record row",
        m,
        type_facts(),
        "invalid(sentinel in ground table records row 0)",
    ));

    let mut m = base();
    m.closure_types.push(ClosureTy { func: FuncTyId::new(0), captures: Vec::new() });
    cases.push((
        "a closure type's signature",
        m,
        type_facts(),
        "invalid(sentinel in ground table closure_types row 0)",
    ));
    let mut m = base();
    let unit_sig = m
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    m.closure_types.push(ClosureTy { func: unit_sig, captures: vec![t0()] });
    cases.push((
        "a closure type's capture",
        m,
        type_facts(),
        "invalid(sentinel in ground table closure_types row 0)",
    ));

    let mut m = base();
    m.types.push(Ty::Tuple(vec![t0(), Ty::U8]));
    m.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 16,
        align: 8,
        field_offsets: vec![0, 8],
    });
    cases.push((
        "a tuple layout's type row",
        m,
        type_facts(),
        "invalid(sentinel in ground table tuple_layouts row 0)",
    ));

    // The glue is a signed `(ptr) -> ()` declaration, so the row is well-formed but for its type.
    let mut m = base();
    let glue_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut glue = Function::new(FuncId::new(1), "dep_drop_glue", glue_ty, BlockId::new(0));
    glue.calling_conv = trust_ir::CallingConv::Rust;
    m.functions.push(glue);
    m.target_info = Some(target());
    m.drop_glue.push(DropGlueEntry { glue: FuncId::new(1), ty: t0() });
    cases.push((
        "a drop-glue row",
        m,
        type_facts(),
        "invalid(sentinel in ground table drop_glue row 0)",
    ));

    let mut m = base();
    m.universes.push(trust_ir::Universe::IntRange { lo: 0, hi: 1 });
    cases.push((
        "universes",
        m,
        type_facts(),
        "template-unsupported(universes or predicates in a template)",
    ));
    let mut m = base();
    m.predicates.push(trust_ir::Pred::Interval { lo: 0, hi: 1 });
    cases.push((
        "predicates",
        m,
        type_facts(),
        "template-unsupported(universes or predicates in a template)",
    ));

    // trust-ir wire v58: a closure layout (no type in it; a ground closure type) and a nominal
    // origin (no type in it either; a ground struct row) are refused by name.
    let mut m = base();
    let unit_sig = m
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    m.closure_types.push(ClosureTy { func: unit_sig, captures: vec![Ty::U8] });
    m.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
        origin: None,
        closure: trust_ir::ClosureTyId::new(0),
        size: 1,
        align: 1,
        capture_offsets: vec![0],
    });
    cases.push((
        "a closure layout",
        m,
        type_facts(),
        "template-unsupported(closure layouts in a template)",
    ));
    let mut m = base();
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "Ground".to_string(),
        fields: vec![FieldDef { name: "0".to_string(), ty: Ty::U8, offset: None }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: Some(trust_ir::ty::TypeOrigin::Rust {
            stable_crate_id: 1,
            def_path_hash: [0; 16],
            args_digest: trust_ir::ProofDigest::zero(),
        }),
    });
    cases.push((
        "a nominal origin",
        m,
        type_facts(),
        "template-unsupported(a nominal type origin in a template)",
    ));

    // A parameter-dependent ADT row with NO visible sentinel is still the instance's layout:
    // `P<T> { p: *const T }`, and `Option<&T>`, whose generic row is `enum { None, Some(ptr) }`
    // with no layout while every instance is niche-encoded (plan §0.14).
    let mut m = base();
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "P".to_string(),
        fields: vec![FieldDef { name: "p".to_string(), ty: Ty::Ptr, offset: None }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let mut param_rows = type_facts();
    param_rows.param_adt_structs.insert(0);
    cases.push((
        "a sentinel-free struct row from parameter args",
        m,
        param_rows,
        "template-unsupported(parameter-dependent ADT row (6.5.2))",
    ));
    let mut m = base();
    m.enums.push(EnumDef::new(
        EnumId::new(0),
        "Option",
        vec![
            EnumVariant { name: "None".to_string(), fields: Vec::new(), field_names: Vec::new() },
            EnumVariant {
                name: "Some".to_string(),
                fields: vec![Ty::Ptr],
                field_names: Vec::new(),
            },
        ],
    ));
    let mut param_rows = type_facts();
    param_rows.param_adt_enums.insert(0);
    cases.push((
        "a sentinel-free enum row from parameter args",
        m,
        param_rows,
        "template-unsupported(parameter-dependent ADT row (6.5.2))",
    ));

    // A sentinel reached only as a slice's element row: trust-ir's `TyG::for_each_row` does not
    // follow `FatPtr(Slice(row))`, so neither T5 (a ground table) nor T2 (a declaration, a
    // global) sees it; the escape check's walk does.
    let slice_of_t = Ty::FatPtr(trust_ir::FatPtrKind::Slice(TyId::new(0)));
    let mut m = base();
    m.types.push(t0());
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "View".to_string(),
        fields: vec![FieldDef { name: "s".to_string(), ty: slice_of_t.clone(), offset: None }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    cases.push((
        "a slice element in a struct row",
        m,
        type_facts(),
        "invalid(sentinel in ground table structs row 0)",
    ));
    let mut m = base();
    m.types.push(t0());
    let decl_ty = m
        .add_func_type(FuncTy {
            params: vec![slice_of_t.clone()],
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut decl = Function::new(FuncId::new(1), "dep_callee", decl_ty, BlockId::new(0));
    decl.calling_conv = trust_ir::CallingConv::Rust;
    m.functions.push(decl);
    m.target_info = Some(target());
    cases.push((
        "a slice element in a declaration's signature",
        m,
        type_facts(),
        "invalid(sentinel in the signature of unkeyed declaration row 1)",
    ));
    let mut m = base();
    m.types.push(t0());
    m.globals.push(Global {
        name: "__trust_promoted_0".to_string(),
        ty: slice_of_t,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    cases.push((
        "a slice element in a global's type",
        m,
        type_facts(),
        "invalid(sentinel in the type of global row 0 (T2: no hole row in 6.5.1))",
    ));

    // Since trust-ir a62127c9b ("Map nominal field carriers through the shared IR level
    // map", first pinned by cc8142aba3) T5 reads a struct or enum field's type inline
    // (`ty_is_generic`), so a sentinel in a cloned nominal row is ALSO refused by the
    // validator. Pin that second refusal, by table, rather than dropping the rows.
    let t5_nominal = [
        ("a struct row from parameter args", "struct"),
        ("a struct row", "struct"),
        ("an enum row from parameter args", "enum"),
        ("an enum row", "enum"),
    ];
    let mut accepted_unchecked = Vec::new();
    let mut t5_refused = Vec::new();
    for (what, module, facts, expected) in &cases {
        assert_eq!(class(abstracted(module, facts)), *expected, "{what}");
        let violations = validate_template(&unchecked(module, facts));
        if violations.is_empty() {
            accepted_unchecked.push(*what);
        }
        if let Some((_, table)) = t5_nominal.iter().find(|(name, _)| name == what) {
            assert!(
                violations.iter().any(|e| matches!(
                    e,
                    TemplateViolation::Structure(TemplateError::ExtInGroundTable { table: t, .. })
                        if t == table
                )),
                "{what}: T5 refuses the sentinel in the {table} table: {violations:?}"
            );
            t5_refused.push(*what);
        }
    }
    assert_eq!(
        t5_refused,
        t5_nominal.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
        "every nominal case is measured"
    );
    // MEASURED (the teeth): without the escape check `validate_template` ACCEPTS each of these
    // — no amendment-S rule reads a level-R dialect type inline in a cloned record, closure,
    // drop-glue or slice-element row (struct and enum fields: T5 above), nothing
    // reads `universes`, `predicates`, `closure_layouts` or a row's `origin`, no rule reads a
    // generic row with no parameter in it, and T2/T5 do not follow a slice's element row. (A sentinel reached through a MAPPED row — a closure
    // type's signature, a tuple layout's type row — is also T5's `ExtInGroundTable`; the escape
    // check refuses it first, by name.)
    assert_eq!(
        accepted_unchecked,
        vec![
            "a record row",
            "a closure type's capture",
            "a drop-glue row",
            "universes",
            "predicates",
            "a closure layout",
            "a nominal origin",
            "a sentinel-free struct row from parameter args",
            "a sentinel-free enum row from parameter args",
            "a slice element in a struct row",
            "a slice element in a declaration's signature",
            "a slice element in a global's type",
        ],
        "the cases only the escape check refuses"
    );
    // The control: the same module with no sentinel in a cloned table abstracts and validates.
    let t = abstracted(&ident_module(), &type_facts()).expect("abstracts");
    assert_eq!(validate_template(&t), Vec::new());
}

// ---------------------------------------------------------------------------------------- 3

/// A const parameter's sentinel is `$0` only at the ROOT of an `Inst::Const` of exactly the
/// parameter's scalar type; at another type, inside an aggregate, in a global initializer, as a
/// global's name or in a type parameter's place it is refused.
#[test]
fn a_const_parameter_sentinel_is_admitted_only_at_an_inst_const_root() {
    let facts = LaneFacts { params: vec![LaneParam::Const(Ty::Usize)], ..LaneFacts::default() };
    let with = |inst: Inst| {
        sentinel_module(
            Vec::new(),
            vec![Ty::Usize],
            vec![node_r(inst, 0), node(Inst::Return { values: vec![v(0)] })],
        )
    };
    let root = with(Inst::Const { ty: Ty::Usize, value: const_param_sentinel(0) });
    let t = abstracted(&root, &facts).expect("the root is the parameter");
    assert!(matches!(
        &t.module.functions[0].blocks[0].body[0].inst,
        InstG::Const { ty: TyG::Usize, value: ConstantG::Ext(TemplateRef::Param(p)) } if p.index() == 0
    ));
    assert_eq!(t.header.params, vec![TemplateParam::Const { ty: Ty::Usize }]);
    assert_eq!(validate_template(&t), Vec::new(), "and it validates");

    let invalid_class = |m: &Module, facts: &LaneFacts, what: &str| {
        let r = abstracted(m, facts).expect_err(what);
        assert_eq!(r.class(), "invalid", "{what}: {r:?}");
    };
    invalid_class(
        &with(Inst::Const { ty: Ty::U32, value: const_param_sentinel(0) }),
        &facts,
        "at a type other than the parameter's",
    );
    invalid_class(
        &with(Inst::Const {
            ty: Ty::Tuple(vec![Ty::Usize]),
            value: Constant::Aggregate(vec![const_param_sentinel(0)]),
        }),
        &facts,
        "an aggregate's child",
    );
    let global = |name: &str, initializer: Option<Constant>| Global {
        name: name.to_string(),
        ty: Ty::Usize,
        mutable: false,
        initializer,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    };
    let mut in_init = root.clone();
    in_init.globals.push(global("__trust_promoted_0", Some(const_param_sentinel(0))));
    invalid_class(&in_init, &facts, "a global initializer");
    let mut as_name = root.clone();
    as_name.globals.push(global("!trust_template_param::0", Some(Constant::Int(0))));
    invalid_class(&as_name, &facts, "a GlobalAddr target");
    invalid_class(&root, &type_facts(), "a type parameter's sentinel in a constant position");
    // A sentinel symbol with an addend, or a malformed index, is not the parameter.
    invalid_class(
        &with(Inst::Const {
            ty: Ty::Usize,
            value: Constant::SymbolAddr {
                symbol: "!trust_template_param::0".to_string(),
                addend: 1,
            },
        }),
        &facts,
        "an addend",
    );
    invalid_class(
        &with(Inst::Const {
            ty: Ty::Usize,
            value: Constant::SymbolAddr {
                symbol: "!trust_template_param::00".to_string(),
                addend: 0,
            },
        }),
        &facts,
        "a non-canonical index",
    );
}

// ---------------------------------------------------------------------------------------- 4

/// The embedding is the inverse of the abstraction's level map: abstract, embed, abstract again
/// gives the same template, and the embedded module is the sentinel module up to the body row's
/// host facts (which the abstraction resets).
#[test]
fn abstraction_round_trips_through_the_embedding() {
    let facts = LaneFacts {
        params: vec![LaneParam::Type, LaneParam::Const(Ty::U8)],
        ..LaneFacts::default()
    };
    let mut m = sentinel_module(
        vec![t0(), Ty::Ref(Box::new(t0()))],
        vec![Ty::Tuple(vec![t0(), Ty::U8])],
        vec![
            node_r(Inst::Const { ty: Ty::U8, value: const_param_sentinel(1) }, 2),
            node_r(Inst::Alloca { ty: t0(), count: None, align: None }, 3),
            node(Inst::Return { values: vec![v(0)] }),
        ],
    );
    m.types.push(Ty::Vector(Box::new(t0()), 2));
    m.functions[0].name = TEMPLATE_BODY_NAME.to_string();
    let t = abstract_template(&m, &facts, "dep::f".to_string()).expect("abstracts");
    let embedded = embed_template(&t);
    assert_eq!(embedded, m, "the embedding is the sentinel module (its body row already default)");
    let again = abstract_template(&embedded, &facts, "dep::f".to_string()).expect("abstracts");
    assert_eq!(again, t, "abstract . embed . abstract = abstract");
}

// ---------------------------------------------------------------------------------------- 5

/// T7: the body row is named `!template_body` and every fact the host answers is left at its
/// default, whatever the lowering stamped on it.
#[test]
fn the_body_row_leaves_every_host_fact_default() {
    let mut m = ident_module();
    {
        let body = &mut m.functions[0];
        body.linkage = Linkage::Internal;
        body.visibility = trust_ir::Visibility::Hidden;
        body.calling_conv = trust_ir::CallingConv::Rust;
        body.attrs = trust_ir::FuncAttrs { cold: true, ..trust_ir::FuncAttrs::default() };
        body.body_gate = Some(trust_ir::BodyGate::Ungated);
        body.display_path = Some("dep::ident".to_string());
        body.section = Some("__TEXT,__text".to_string());
        body.retained = true;
    }
    let t = abstracted(&m, &type_facts()).expect("abstracts");
    let body = &t.module.functions[0];
    assert_eq!(body.name, TEMPLATE_BODY_NAME);
    assert_eq!(body.linkage, Linkage::default());
    assert_eq!(body.visibility, trust_ir::Visibility::default());
    assert_eq!(body.calling_conv, trust_ir::CallingConv::default());
    assert_eq!(body.attrs, trust_ir::FuncAttrs::default());
    assert_eq!(body.body_gate, None);
    assert_eq!(body.display_path, None);
    assert_eq!(body.section, None);
    assert!(!body.retained);
    assert!(body.source_provenance.is_none());
    assert!(
        !t.structural_violations()
            .iter()
            .any(|e| matches!(e, TemplateError::TemplateBodyShape { .. })),
        "{:?}",
        t.structural_violations()
    );
    // The teeth: the same module through the level map with the facts kept is refused by T7.
    let kept = Template {
        header: t.header.clone(),
        module: {
            let mut module = level_map(&m, &type_facts()).expect("maps");
            module.functions[0].name = TEMPLATE_BODY_NAME.to_string();
            module
        },
    };
    assert!(
        kept.structural_violations()
            .iter()
            .any(|e| matches!(e, TemplateError::TemplateBodyShape { .. })),
        "a body row stating a host fact is a T7 violation"
    );
}

// ---------------------------------------------------------------------------------------- 6

/// The escape check destructures `ModuleG` EXHAUSTIVELY: its pattern has no `..`, so a table
/// trust-ir adds does not compile until it is classified (a source scan of this file).
#[test]
fn the_escape_check_destructures_every_module_table() {
    let source = crate::source_scan::sibling_source("template_lowering.rs");
    let at = source.find("fn escape_check(").expect("the escape check is defined");
    let body = &source[at..];
    let start = body.find("let ModuleG {").expect("it destructures ModuleG");
    let end = body[start..].find("} = sentinel;").expect("the pattern binds the sentinel module");
    let pattern: String = body[start..start + end]
        .lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(!pattern.contains(".."), "no rest pattern: {pattern}");
    for table in [
        "structs",
        "enums",
        "records",
        "closure_types",
        "globals",
        "tuple_layouts",
        "drop_glue",
        "closure_layouts",
        "blobs",
        "universes",
        "predicates",
        "functions",
        "func_types",
        "types",
    ] {
        assert!(pattern.contains(table), "`{table}` is classified");
    }
}

// ---------------------------------------------------------------------------------------- 7

/// The class a `Structure(e)` violation of a template that HAS structural violations gets: one
/// arm per `TemplateError` variant, no wildcard, so a new variant does not compile here until
/// its class is stated (INC6.5-CLASSES).
fn expected_class(e: &TemplateError) -> &'static str {
    match e {
        TemplateError::TemplateUnsupported { .. }
        | TemplateError::OpaqueOperation { .. }
        | TemplateError::ParamDependentLiteral { .. } => "template-unsupported",
        TemplateError::NotATemplate
        | TemplateError::Binary(_)
        | TemplateError::InvalidIdentity
        | TemplateError::ParamOutOfScope { .. }
        | TemplateError::ParamKindMismatch { .. }
        | TemplateError::HoleOutOfScope { .. }
        | TemplateError::HoleKindMismatch { .. }
        | TemplateError::DuplicateHole { .. }
        | TemplateError::GroundHole { .. }
        | TemplateError::InvalidHostKey { .. }
        | TemplateError::HoleCycle { .. }
        | TemplateError::HoleRowMismatch { .. }
        | TemplateError::UnusedHole { .. }
        | TemplateError::GenericRowNotAHole { .. }
        | TemplateError::ExtInGroundTable { .. }
        | TemplateError::TemplateBodyShape { .. } => "invalid",
    }
}

/// `template_refusal` classes by VARIANT: a proof-surface `TemplateUnsupported` (and T3/T4) is
/// `template-unsupported`, every other structural variant and every `LevelR` is `invalid`, and
/// `validate_template`'s no-skolem fallback — a `Structure(TemplateUnsupported)` for a template
/// with NO structural violation — is `invalid`. Fails if the proof surface is classed `invalid`
/// or the fallback `template-unsupported`.
#[test]
fn template_violations_are_classed_by_variant() {
    let at = || "here".to_string();
    let variants = vec![
        TemplateError::NotATemplate,
        TemplateError::Binary("short".to_string()),
        TemplateError::InvalidIdentity,
        TemplateError::ParamOutOfScope { param: 3, at: at() },
        TemplateError::ParamKindMismatch { param: 0, at: at() },
        TemplateError::HoleOutOfScope { hole: 0, at: at() },
        TemplateError::HoleKindMismatch { hole: 0, at: at() },
        TemplateError::DuplicateHole { hole: 1, first: 0 },
        TemplateError::GroundHole { hole: 0 },
        TemplateError::InvalidHostKey { hole: 0 },
        TemplateError::HoleCycle { hole: 0, names: 1 },
        TemplateError::HoleRowMismatch { why: at() },
        TemplateError::UnusedHole { hole: 0 },
        TemplateError::GenericRowNotAHole { row: at() },
        TemplateError::ParamDependentLiteral { at: at() },
        TemplateError::OpaqueOperation { at: at() },
        TemplateError::ExtInGroundTable { table: "structs", index: 0 },
        TemplateError::TemplateBodyShape { why: at() },
        TemplateError::TemplateUnsupported {
            what: "instruction proofs or proof contexts (proof surface stays on level R)"
                .to_string(),
        },
    ];
    // A template WITH a structural violation (an empty identity, T9), so a `TemplateUnsupported`
    // in it is a real construct, not the fallback.
    let mut broken = abstracted(&ident_module(), &type_facts()).expect("abstracts");
    broken.header.identity = String::new();
    assert!(!broken.structural_violations().is_empty());
    for e in variants {
        let refusal = template_refusal(&broken, &[TemplateViolation::Structure(e.clone())]);
        assert_eq!(refusal.class(), expected_class(&e), "{e:?}");
        assert!(
            refusal.reason().contains(&format!("{e}")),
            "the reason names the rule: {refusal:?}"
        );
    }
    // Every `LevelR` (T6) is invalid.
    let level_r = template_refusal(
        &broken,
        &[TemplateViolation::LevelR(trust_ir_build::ValidationError::EmptyFunction)],
    );
    assert_eq!(level_r.class(), "invalid");
    assert!(level_r.reason().starts_with("invalid(T6"), "{level_r:?}");
    // The no-skolem fallback: a structurally VALID template, refused as `TemplateUnsupported`.
    let valid = abstracted(&ident_module(), &type_facts()).expect("abstracts");
    assert!(valid.structural_violations().is_empty());
    let fallback = template_refusal(
        &valid,
        &[TemplateViolation::Structure(TemplateError::TemplateUnsupported {
            what: "a template with no skolem instance (x)".to_string(),
        })],
    );
    assert_eq!(fallback.class(), "invalid", "the fallback is never template-unsupported");
    // Only the FIRST violation classes the template.
    let first_wins = template_refusal(
        &broken,
        &[
            TemplateViolation::Structure(TemplateError::OpaqueOperation { at: at() }),
            TemplateViolation::LevelR(trust_ir_build::ValidationError::EmptyFunction),
        ],
    );
    assert_eq!(first_wins.class(), "template-unsupported");
}

/// The sentinel spellings are canonical and the lane's own: `param_<p>` in the
/// `trust_template` namespace at version 1, `!trust_template_param::<p>` with no addend.
#[test]
fn sentinels_are_canonical() {
    assert_eq!(
        dialect_sentinel(match &type_param_sentinel(7) {
            TyG::Dialect(d) => d,
            other => panic!("{other:?}"),
        }),
        Sentinel::Param(7)
    );
    assert_eq!(symbol_sentinel(&const_param_sentinel(12)), Sentinel::Param(12));
    assert_eq!(dialect_sentinel(&DialectTy::new(SENTINEL_NAMESPACE, "hole_0", 1)), Sentinel::Hole(0));
    for name in ["param_", "param_07", "param_x", "hole_", "hole_00", "hole_x"] {
        let d = DialectTy::new(SENTINEL_NAMESPACE, name, SENTINEL_VERSION);
        assert_eq!(dialect_sentinel(&d), Sentinel::Malformed, "{name}");
    }
    assert_eq!(
        dialect_sentinel(&DialectTy::new("other", "param_0", SENTINEL_VERSION)),
        Sentinel::Foreign
    );
    assert_eq!(
        dialect_sentinel(&DialectTy::new(SENTINEL_NAMESPACE, "param_0", 2)),
        Sentinel::Malformed
    );
    // A dialect type the lane did not mint is refused, never mapped.
    let foreign = sentinel_module(
        vec![Ty::Dialect(Box::new(DialectTy::new("other", "t", 1)))],
        Vec::new(),
        vec![node(Inst::Return { values: Vec::new() })],
    );
    assert_eq!(abstracted(&foreign, &type_facts()).expect_err("refused").class(), "invalid");
}

/// Merely spelling a canonical hole sentinel never owns its Rust key. The
/// header must independently bind every original owner index and dense HoleId.
#[test]
fn type_holes_require_owned_keys_arguments_and_dense_ids() {
    use crate::template_key::{HoleKey, KeyConst, KeyTy};
    let h = Ty::Dialect(Box::new(DialectTy::new(SENTINEL_NAMESPACE, "hole_0", 1)));
    let module = sentinel_module(vec![h.clone()], vec![h], vec![node(Inst::Return { values: vec![v(0)] })]);
    let mut facts = LaneFacts {
        owner: Some((1, 2)), parameter_indices: vec![1, 3],
        params: vec![LaneParam::Type, LaneParam::Const(Ty::Usize)], ..Default::default()
    };
    assert!(abstracted(&module, &facts).is_err(), "unowned sentinel");
    facts.type_holes.push(TypeHole {
        id: HoleId::new(0),
        key: HoleKey::Type(KeyTy::Array(Box::new(KeyTy::Param(1)), KeyConst::Param(3))),
        dependencies: vec![(1, TemplateArg::Type(ext0())), (3, TemplateArg::Const {
            value: ConstantG::Ext(TemplateRef::Param(ParamId::new(1))), ty: Ty::Usize,
        })],
    });
    let template = abstracted(&module, &facts).unwrap();
    assert!(validate_template(&template).is_empty());
    let mut changed = facts.clone(); changed.owner = None;
    assert!(abstracted(&module, &changed).is_err());
    changed = facts.clone(); changed.type_holes[0].dependencies.reverse();
    assert!(abstracted(&module, &changed).is_err());
    changed = facts.clone(); changed.parameter_indices[1] = 2;
    assert!(abstracted(&module, &changed).is_err());
    changed = facts.clone(); changed.type_holes[0].id = HoleId::new(1);
    assert!(abstracted(&module, &changed).is_err());
    changed = facts.clone(); changed.type_holes.push(changed.type_holes[0].clone());
    assert!(abstracted(&module, &changed).is_err());
}

// ---------------------------------------------------------------------------------------- 8

/// Every trust-ir v67-v70 tensor construct is refused BY NAME, `template-unsupported`, wherever
/// the lane can meet it: a `Ty::Tensor` the level map reaches (`abstract_ty`) and one in a table
/// it clones unmapped (the escape check's walk), each of the six tensor instructions (named even
/// at a non-tensor type), a `Constant::TensorBlob` at an `Inst::Const` root and in a global
/// initializer, and a non-empty `Module::blobs`. The sentinel-free control still abstracts.
#[test]
fn every_tensor_construct_is_refused_by_name() {
    let reason = |m: &Module| abstracted(m, &type_facts()).expect_err("refused").reason();
    let tensor = Ty::Tensor(Box::new(Ty::I32), 1);
    let blob = Constant::TensorBlob {
        digest: trust_ir::blob::BlobDigest::of(&[0, 0, 0, 0]),
        dims: vec![1],
    };

    // A tensor in a mapped position (a block parameter and the signature).
    let mapped = sentinel_module(
        vec![tensor.clone()],
        vec![tensor.clone()],
        vec![node(Inst::Return { values: vec![v(0)] })],
    );
    assert_eq!(
        reason(&mapped),
        "template-unsupported(a tensor type `tensor<i32, 1>` in a template)"
    );

    // A tensor in a table the level map clones unmapped (a struct row's field).
    let mut cloned = ident_module();
    cloned.structs.push(StructDef {
        id: StructId::new(0),
        name: "Weights".to_string(),
        fields: vec![FieldDef { name: "0".to_string(), ty: tensor.clone(), offset: None }],
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    assert_eq!(reason(&cloned), "template-unsupported(a tensor type in a template table)");

    // The six instructions, each at a scalar type so only the by-name scan can see it.
    let cases = [
        (
            "TensorContract",
            Inst::TensorContract {
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(0),
                batch: Vec::new(),
                contract: Vec::new(),
            },
        ),
        ("TensorMap", Inst::TensorMap { ty: Ty::I32, args: vec![v(0)], body: Vec::new() }),
        (
            "TensorReduce",
            Inst::TensorReduce {
                ty: Ty::I32,
                src: v(0),
                op: trust_ir::TensorReduceOp::Add,
                axes: Vec::new(),
                order: trust_ir::TensorReduceOrder::RowMajor,
            },
        ),
        (
            "TensorView",
            Inst::TensorView {
                ty: Ty::I32,
                src: v(0),
                params: Vec::new(),
                exprs: Vec::new(),
                shape: Vec::new(),
                index: Vec::new(),
                fill: None,
            },
        ),
        ("TensorGather", Inst::TensorGather { ty: Ty::I32, data: v(0), coords: vec![v(0)] }),
        (
            "TensorScatter",
            Inst::TensorScatter { ty: Ty::I32, init: v(0), src: v(0), coords: vec![v(0)] },
        ),
    ];
    for (name, inst) in cases {
        let m = sentinel_module(
            vec![Ty::I32],
            vec![Ty::I32],
            vec![node_r(inst, 1), node(Inst::Return { values: vec![v(1)] })],
        );
        assert_eq!(
            reason(&m),
            format!("template-unsupported(a tensor instruction `{name}` in a template)"),
        );
    }

    // A blob constant at an `Inst::Const` root, at a scalar type so only the constant map sees it.
    assert_eq!(
        abstract_root_const(&blob, &Ty::U64, &type_facts()).expect_err("refused").reason(),
        "template-unsupported(a tensor weight blob constant in a template)",
    );

    // A blob constant in a global initializer (cloned unmapped).
    let mut in_init = ident_module();
    in_init.globals.push(Global {
        name: "weights".to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(blob),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    assert_eq!(
        reason(&in_init),
        "template-unsupported(a tensor weight blob in a template global initializer)",
    );

    // A non-empty blob table.
    let mut with_blobs = ident_module();
    with_blobs.intern_blob(vec![0, 0, 0, 0]);
    assert_eq!(reason(&with_blobs), "template-unsupported(tensor weight blobs in a template)");

    // The control.
    let t = abstracted(&ident_module(), &type_facts()).expect("abstracts");
    assert_eq!(validate_template(&t), Vec::new());
}
