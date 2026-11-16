//! Two complete-constructor spellings that BMC-LANE-1 introduced and no other test
//! pinned. The cast rows extend `lower::layout_sensitive_cast_fallback_tests`,
//! which pins the other `Rvalue::Cast` fallbacks, with the same `cast_fn` fixture.
//!
//! * The `Rvalue::Cast` arm that turns a pointer or integer into a one-field struct
//!   whose field 0 has the source's trust-ir type. It used to emit an `Undef` seed
//!   of the struct type and one `InsertField(0)`. It now emits one
//!   `MakeAggregate { variant: None, fields: [src] }`. `*const T -> NonNull<T>`
//!   and `u64 -> struct H { h: u64 }` both reach it.
//! * `emit_complete_aggregate`'s `(Array, None)` arm: `[]` at `[T; 0]` is one
//!   `Const { ty: Array(_, 0), value: Constant::Array([]) }`. It used to be an
//!   `Undef` of the array type.
//!
//! * The R107 non-zero charge on a cast into `NonNull`/`NonZero`. The newtype arm
//!   above made such a construction EXECUTABLE, so the charge must reach it: it
//!   matches the extractor's definitional spellings (`core::ptr::non_null::NonNull`,
//!   `core::num::nonzero::NonZero`) as well as the re-exported ones, its zero has
//!   the compare's own type, a fat source compares its data lane, an operand that
//!   is itself a reference (non-null by its own validity invariant) is not charged,
//!   neither is a validity-wrapper source (`NonNull`, `NonZero`), and neither is a
//!   member the COMPILER authenticated as a foreign `core`/`alloc`/`std` body (the
//!   MIR `[unsafe:validity-transmute]` row's exemption; never keyed on a def path).
//!   Since R107-IDENTITY-1 the target is identified first by the extractor's
//!   verdict on its definition (`Ty::Adt::validity_wrapper`), whatever its name;
//!   the name test is a second, additive trigger for a target with no stamp.
//!
//! The reference interpreter refuses an `Undef` at an aggregate type
//! (`UndefinedBehavior`), so it could not run the old spellings. It runs both new
//! ones, and these tests run it on each.

use trust_ir::inst::AssertKind;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty as IrTy;
use trust_ir::{Constant, Inst, InstrNode, Module, ValueId};
use trust_ir_build::validate_module;
use trust_types::fx::FxHashSet;
use trust_types::{
    AggregateKind, BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use crate::lower::{lower_to_trust_ir, lower_to_trust_ir_functions_with_test_sysroot_members};

/// `fn cast_fn(a: From) -> To { a as To }`, spelled as the extractor spells a
/// transmute: `_0 = Rvalue::Cast(Copy(_1), To)`. The same fixture as
/// `layout_sensitive_cast_fallback_tests::cast_fn`.
fn cast_fn(from: Ty, to: Ty) -> VerifiableFunction {
    VerifiableFunction {
        name: "cast_fn".to_string(),
        def_path: "test::cast_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: to.clone(), name: None },
                LocalDecl { index: 1, ty: from, name: Some("a".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), to.clone()),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: to,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// A `NonNull<pointee>` struct named `name`: one thin raw-pointer field, the
/// shape of `tests::nonnull_of`.
fn nonnull_of(name: &str, pointee: Ty) -> Ty {
    Ty::adt(
        name,
        vec![("pointer".to_string(), Ty::RawPtr { mutable: false, pointee: Box::new(pointee) })],
    )
}

/// `struct H { h: u64 }`, the hash-wrapper shape R150 widened the arm for.
fn hash_wrapper() -> Ty {
    Ty::adt("test::H", vec![("h".to_string(), Ty::u64())])
}

fn lower(func: &VerifiableFunction) -> Module {
    let module = lower_to_trust_ir(func).expect("the fixture must lower");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "the lowered module must validate: {errors:?}");
    module
}

/// Every instruction of the module's one function, in block and program order.
fn nodes(module: &Module) -> Vec<&InstrNode> {
    assert_eq!(module.functions.len(), 1, "one fixture function");
    module.functions[0].blocks.iter().flat_map(|block| block.body.iter()).collect()
}

/// The value of the function's one parameter, as the body reads it.
fn the_parameter(module: &Module) -> ValueId {
    let entry = &module.functions[0].blocks[0];
    let [(param, _)] = entry.params.as_slice() else {
        panic!("one entry parameter, got {:?}", entry.params)
    };
    *param
}

/// The registered struct the fixture's destination type maps to.
fn struct_ty(module: &Module, name: &str) -> IrTy {
    let rows: Vec<_> = module.structs.iter().filter(|row| row.name == name).collect();
    let [row] = rows.as_slice() else { panic!("one `{name}` struct row, got {rows:?}") };
    IrTy::Struct(row.id)
}

/// The index of the one `MakeAggregate` in `nodes`; asserts it is the only one,
/// that it builds `ty` with no variant, and that its one field is `field`.
fn the_constructor(nodes: &[&InstrNode], ty: &IrTy, field: ValueId) -> usize {
    let constructors: Vec<usize> = nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| matches!(node.inst, Inst::MakeAggregate { .. }))
        .map(|(index, _)| index)
        .collect();
    let [index] = constructors.as_slice() else {
        panic!("exactly one MakeAggregate, got {constructors:?} in {nodes:#?}")
    };
    let Inst::MakeAggregate { ty: built, variant, fields } = &nodes[*index].inst else {
        unreachable!()
    };
    assert_eq!(built, ty, "the constructor builds the destination struct");
    assert_eq!(*variant, None, "a struct constructor names no variant");
    assert_eq!(fields.as_slice(), [field], "field 0 is the cast's source value, unchanged");
    *index
}

/// No `Undef` anywhere in the function (so none at the struct type: the old seed
/// is gone) and no `InsertField` anywhere (so no write into a seed).
fn assert_no_seed(nodes: &[&InstrNode]) {
    for node in nodes {
        assert!(!matches!(node.inst, Inst::Undef { .. }), "no Undef may be emitted: {node:?}");
        assert!(
            !matches!(node.inst, Inst::InsertField { .. }),
            "no InsertField may be emitted: {node:?}"
        );
    }
}

/// The struct `outcome` returned, as its lanes.
fn returned_lanes(
    outcome: &trust_ir::interpret::InterpretOutcome,
    ty: &IrTy,
) -> Vec<InterpretValue> {
    let [returned] = outcome.returns.as_slice() else {
        panic!("one returned value, got {:?}", outcome.returns)
    };
    assert_eq!(&returned.ty, ty, "the returned value has the destination struct type");
    let InterpretValueKind::Aggregate(lanes) = &returned.kind else {
        panic!("the returned struct is an aggregate value, got {returned:?}")
    };
    lanes.clone()
}

/// `*const u8 -> core::ptr::non_null::NonNull<u8>`, with the definitional path the
/// verifier-lane extractor renders (`safe_def_path_str` prints no re-exports; see
/// `trust-mir-extract` `convert.rs`). Field 0 is a raw pointer, the source's type,
/// so the one-field newtype arm builds the struct with one constructor of the
/// parameter.
///
/// This row checks the constructor; the R107 non-null charge that precedes it is
/// pinned by `a_raw_pointer_or_integer_into_nonnull_or_nonzero_asserts_a_typed_zero_compare`.
#[test]
fn a_pointer_cast_to_nonnull_is_one_constructor_of_the_pointer() {
    let func = cast_fn(
        Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
        nonnull_of("core::ptr::non_null::NonNull", Ty::u8()),
    );
    let module = lower(&func);
    let nonnull = struct_ty(&module, "core::ptr::non_null::NonNull");
    let param = the_parameter(&module);
    let nodes = nodes(&module);
    the_constructor(&nodes, &nonnull, param);
    assert_no_seed(&nodes);

    // A non-null pointer argument: a nonzero address with no allocation (the
    // interpreter's `DanglingPtr`, the value `NonNull::dangling()` makes). The
    // cast reads no memory, so no allocation is needed.
    let pointer = InterpretValue { ty: IrTy::Ptr, kind: InterpretValueKind::DanglingPtr(0x1000) };
    let outcome = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![pointer.clone()])
        .expect("the NonNull construction executes on a non-null pointer");
    assert_eq!(returned_lanes(&outcome, &nonnull), vec![pointer], "lane 0 is the argument");
}

/// The `param != 0` compares R107 emits for the cast's source `param`, each with
/// the index of its compare and its result. Asserts each zero is `Int(0)` at the
/// compare's own type `cmp_ty`.
fn r107_compares(nodes: &[&InstrNode], lhs: ValueId, cmp_ty: &IrTy) -> Vec<(usize, ValueId)> {
    let def = |value: ValueId| {
        nodes.iter().find(|node| node.results.as_slice() == [value]).map(|node| &node.inst)
    };
    nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match (&node.inst, node.results.as_slice()) {
            (Inst::ICmp { op: trust_ir::inst::ICmpOp::Ne, ty, lhs: l, rhs }, [result])
                if *l == lhs =>
            {
                assert_eq!(ty, cmp_ty, "the compare has the source's own type: {node:?}");
                assert!(
                    matches!(def(*rhs), Some(Inst::Const { ty: zero_ty, value: Constant::Int(0) }) if zero_ty == cmp_ty),
                    "the zero is `Int(0)` at the compare type {cmp_ty:?}: {:?}",
                    def(*rhs)
                );
                Some((index, *result))
            }
            _ => None,
        })
        .collect()
}

/// The index of the one `Assert` of `cond`. R107's charge is UNKINDED (the R87
/// discipline: `AssertKind::Unspecified`, no site, no proof annotation), so no lane
/// reads it as a classified check it can discharge by kind and it stays refutable.
/// A kinded or annotated assert fails here.
fn the_assert_of(nodes: &[&InstrNode], cond: ValueId) -> usize {
    let asserts: Vec<usize> = nodes
        .iter()
        .enumerate()
        .filter(|(_, node)| matches!(&node.inst, Inst::Assert { cond: c, .. } if *c == cond))
        .map(|(index, _)| index)
        .collect();
    let [index] = asserts.as_slice() else { panic!("one Assert of the compare, got {asserts:?}") };
    let node = nodes[*index];
    assert!(
        matches!(node.inst, Inst::Assert { kind: AssertKind::Unspecified, site: None, .. }),
        "the R107 charge is an unkinded assert with no site: {node:?}"
    );
    assert!(node.proofs.is_empty(), "the R107 charge carries no proof annotation: {node:?}");
    *index
}

/// `cast_fn`, lowered as the member named `def_path`.
fn cast_fn_at(def_path: &str, from: Ty, to: Ty) -> VerifiableFunction {
    VerifiableFunction { def_path: def_path.to_string(), ..cast_fn(from, to) }
}

/// `func` alone, lowered through the seam that carries a compiler-authenticated
/// sysroot member set, and validated.
fn lower_with_sysroot_members(func: &VerifiableFunction, members: &[&str]) -> Module {
    let members: FxHashSet<String> = members.iter().map(|member| member.to_string()).collect();
    let module = lower_to_trust_ir_functions_with_test_sysroot_members(
        func.def_path.clone(),
        std::slice::from_ref(func),
        &members,
    )
    .expect("the fixture must lower");
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "the lowered module must validate: {errors:?}");
    module
}

/// R107 is keyed on the COMPILER's verdict on the lowered body, the bridge half of
/// the MIR `[unsafe:validity-transmute]` row's exemption (docs/TCB.md: "the
/// statement's nearest inlined instance is an artifact-authenticated sysroot def ...
/// std's own transmutes are std's obligation"). A member the compiler authenticated
/// as a foreign `core`/`alloc`/`std` body (`compiler_sysroot_members`, which only
/// the two compiler-context entries accept, decided on the member ledger) is not
/// charged, whatever its spelling: a qualified `<_ as _>` std impl and a generic
/// instance tagged `::<__trust_args@…>` included, as the MIR row exempts them by
/// DefId. Every other body is charged, whatever its def path spells: the very same
/// std paths when the compiler did not vouch for them (the unstamped root of a crate
/// built `--crate-name core` spells exactly these, hostile review 4, F1), on the
/// plain API, with an empty set and with a set that names another body.
///
/// Before the exemption the charge landed in the std members every `println!`
/// bundles (`core::fmt::Arguments::from_str`'s `s.as_ptr()` transmute, unprovable),
/// whose unlinked `Assert` withheld the `std-print-dispatch` attestation from every
/// printing program (BMC-LANE-1 hostile review #0). The exempt body still runs: a
/// null source executes to `NonNull(null)`, which is the std premise this exemption
/// rests on, stated here so a reader cannot mistake it for a check.
#[test]
fn r107_exempts_only_a_member_the_compiler_authenticated() {
    let raw_u8 = || Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let nonnull_u8 = || nonnull_of("core::ptr::non_null::NonNull", Ty::u8());
    let null = InterpretValue { ty: IrTy::Ptr, kind: InterpretValueKind::NullPtr };
    let std_paths = [
        "core::fmt::Arguments::<'a>::from_str",
        "core::ptr::non_null::NonNull::<T>::from_ref",
        "alloc::raw_vec::RawVecInner::<A>::ptr",
        "std::sys::pal::unix::fs::File::fd",
        "<alloc::alloc::Global as core::alloc::Allocator>::allocate",
        "core::ptr::non_null::NonNull::<u8>::from_ref::<__trust_args@00000000deadbeef>",
    ];
    for exempt in std_paths {
        let module =
            lower_with_sysroot_members(&cast_fn_at(exempt, raw_u8(), nonnull_u8()), &[exempt]);
        let wrapper = struct_ty(&module, "core::ptr::non_null::NonNull");
        let param = the_parameter(&module);
        let nodes = nodes(&module);
        the_constructor(&nodes, &wrapper, param);
        assert!(
            !nodes.iter().any(|node| matches!(node.inst, Inst::Assert { .. } | Inst::ICmp { .. })),
            "{exempt}: a compiler-authenticated sysroot member is not charged: {nodes:#?}"
        );
        let outcome = Interpreter::with_module(&module)
            .execute_func(module.functions[0].id, vec![null.clone()])
            .expect("the exempt std body executes on a null source");
        assert_eq!(returned_lanes(&outcome, &wrapper), vec![null.clone()], "{exempt}");
    }
    let other_paths = [
        "core::wrap",
        "__trust_crate@1973d11b2baa21fa::core::fmt::Arguments::<'a>::from_str",
        "mydep::wrap",
        "test::cast_fn",
    ];
    for charged in std_paths.into_iter().chain(other_paths) {
        let func = cast_fn_at(charged, raw_u8(), nonnull_u8());
        for (route, module) in [
            ("the plain API", lower(&func)),
            ("an empty set", lower_with_sysroot_members(&func, &[])),
            ("a set naming another body", lower_with_sysroot_members(&func, &["core::other"])),
        ] {
            let wrapper = struct_ty(&module, "core::ptr::non_null::NonNull");
            let param = the_parameter(&module);
            let nodes = nodes(&module);
            let constructor = the_constructor(&nodes, &wrapper, param);
            let compares = r107_compares(&nodes, param, &IrTy::Ptr);
            let [(compare, nonzero)] = compares.as_slice() else {
                panic!(
                    "{charged} ({route}): one `param != 0` compare, got {compares:?} in {nodes:#?}"
                )
            };
            let assert = the_assert_of(&nodes, *nonzero);
            assert!(
                *compare < assert && assert < constructor,
                "{charged} ({route}): compare, assert, constructor"
            );
            let error = Interpreter::with_module(&module)
                .execute_func(module.functions[0].id, vec![null.clone()])
                .expect_err("a null source fails the R107 assert");
            assert_eq!(error.code, InterpretErrorCode::Panic, "{charged} ({route}): {error:?}");
        }
    }
}

/// R107 charges a cast into the wrapper of a `core` the compiler did not load from its
/// own sysroot (hostile review 5, F1). The extractor prints every type of that crate
/// under the unauthenticated-crate stamp, `__trust_crate@<id>::core::…`, and the bare
/// prefix test missed it: the genuine `core` under `cargo -Zbuild-std` or
/// `--extern core=` lost the charge (measured 0 asserts). The stamped names here are
/// minted by the producer's own `stamp_unauthenticated_crate_path`, so a change to the
/// stamp's format turns this red instead of silently uncharging the lane. The stamp is
/// the only thing read past: a stamped path that is not a wrapper charges nothing, as
/// it does unstamped.
#[test]
fn r107_charges_a_cast_into_the_wrapper_of_a_stamped_core() {
    let stamped = |path: &str| {
        trust_types::stamp_unauthenticated_crate_path(path.to_string(), 0x931e_3e58_7780_8317, true)
    };
    let raw_u8 = || Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let null = InterpretValue { ty: IrTy::Ptr, kind: InterpretValueKind::NullPtr };
    let rows: Vec<(Ty, Ty, IrTy, InterpretValue)> = vec![
        (
            raw_u8(),
            nonnull_of(&stamped("core::ptr::non_null::NonNull"), Ty::u8()),
            IrTy::Ptr,
            null.clone(),
        ),
        (raw_u8(), nonnull_of(&stamped("core::ptr::NonNull"), Ty::u8()), IrTy::Ptr, null),
        (
            Ty::i32(),
            Ty::adt(stamped("core::num::nonzero::NonZero"), vec![("0".to_string(), Ty::i32())]),
            IrTy::I32,
            InterpretValue::int(IrTy::I32, 0).expect("fits"),
        ),
        (
            Ty::u32(),
            Ty::adt(stamped("core::num::NonZero"), vec![("0".to_string(), Ty::u32())]),
            IrTy::U32,
            InterpretValue::int(IrTy::U32, 0).expect("fits"),
        ),
    ];
    for (from, to, cmp_ty, zero_arg) in rows {
        let Ty::Adt { name, .. } = &to else { unreachable!() };
        assert!(name.starts_with("__trust_crate@"), "{name}: the fixture must be stamped");
        let module = lower(&cast_fn(from, to.clone()));
        let wrapper = struct_ty(&module, name);
        let param = the_parameter(&module);
        let nodes = nodes(&module);
        let constructor = the_constructor(&nodes, &wrapper, param);
        let compares = r107_compares(&nodes, param, &cmp_ty);
        let [(compare, nonzero)] = compares.as_slice() else {
            panic!("{name}: one `param != 0` compare, got {compares:?} in {nodes:#?}")
        };
        let assert = the_assert_of(&nodes, *nonzero);
        assert!(*compare < assert && assert < constructor, "{name}: compare, assert, constructor");
        let error = Interpreter::with_module(&module)
            .execute_func(module.functions[0].id, vec![zero_arg])
            .expect_err("a zero source fails the R107 assert");
        assert_eq!(error.code, InterpretErrorCode::Panic, "{name}: {error:?}");
    }

    let not_a_wrapper = nonnull_of(&stamped("mydep::ptr::NonNull"), Ty::u8());
    let module = lower(&cast_fn(raw_u8(), not_a_wrapper));
    let nodes = nodes(&module);
    assert!(
        !nodes.iter().any(|node| matches!(node.inst, Inst::Assert { .. } | Inst::ICmp { .. })),
        "a stamped path that is not std's wrapper is not charged: {nodes:#?}"
    );
}

/// R107 on a raw-pointer or integer source, with the definitional spelling the
/// extractor renders and the re-exported one: one `param != 0` compare whose zero
/// has the source's own type, its `Assert`, then the constructor. A nonzero source
/// executes to the wrapper of it; a zero source fails the assert (`Panic`).
///
/// Before this pin the arm matched only the re-exported spellings, so on the
/// extractor's it charged nothing, and on the others its `i64` zero made a pointer
/// or signed source's module invalid (`icmp ptr` against `i64`).
#[test]
fn a_raw_pointer_or_integer_into_nonnull_or_nonzero_asserts_a_typed_zero_compare() {
    let raw_u8 = || Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let pointer = |kind| InterpretValue { ty: IrTy::Ptr, kind };
    let rows: Vec<(Ty, Ty, IrTy, InterpretValue, InterpretValue)> = vec![
        (
            raw_u8(),
            nonnull_of("core::ptr::non_null::NonNull", Ty::u8()),
            IrTy::Ptr,
            pointer(InterpretValueKind::DanglingPtr(0x1000)),
            pointer(InterpretValueKind::NullPtr),
        ),
        (
            raw_u8(),
            nonnull_of("core::ptr::NonNull", Ty::u8()),
            IrTy::Ptr,
            pointer(InterpretValueKind::DanglingPtr(0x1000)),
            pointer(InterpretValueKind::NullPtr),
        ),
        (
            Ty::i32(),
            Ty::adt("core::num::nonzero::NonZero", vec![("0".to_string(), Ty::i32())]),
            IrTy::I32,
            InterpretValue::int(IrTy::I32, -5).expect("fits"),
            InterpretValue::int(IrTy::I32, 0).expect("fits"),
        ),
        (
            Ty::u32(),
            Ty::adt("core::num::NonZero", vec![("0".to_string(), Ty::u32())]),
            IrTy::U32,
            InterpretValue::int(IrTy::U32, 7).expect("fits"),
            InterpretValue::int(IrTy::U32, 0).expect("fits"),
        ),
    ];
    for (from, to, cmp_ty, nonzero_arg, zero_arg) in rows {
        let module = lower(&cast_fn(from, to.clone()));
        let Ty::Adt { name, .. } = &to else { unreachable!() };
        let wrapper = struct_ty(&module, name);
        let param = the_parameter(&module);
        let nodes = nodes(&module);
        let constructor = the_constructor(&nodes, &wrapper, param);
        assert_no_seed(&nodes);
        let compares = r107_compares(&nodes, param, &cmp_ty);
        let [(compare, nonzero)] = compares.as_slice() else {
            panic!("{name}: one `param != 0` compare, got {compares:?} in {nodes:#?}")
        };
        let assert = the_assert_of(&nodes, *nonzero);
        assert!(*compare < assert && assert < constructor, "{name}: compare, assert, constructor");

        let outcome = Interpreter::with_module(&module)
            .execute_func(module.functions[0].id, vec![nonzero_arg.clone()])
            .expect("a nonzero source executes");
        assert_eq!(returned_lanes(&outcome, &wrapper), vec![nonzero_arg], "{name}: lane 0");
        let error = Interpreter::with_module(&module)
            .execute_func(module.functions[0].id, vec![zero_arg])
            .expect_err("a zero source fails the R107 assert");
        assert_eq!(error.code, InterpretErrorCode::Panic, "{name}: {error:?}");
    }
}

/// R107 on a FAT raw pointer (`*const [u8] -> NonNull<[u8]>`): the charge compares
/// the pointer's `PtrData` lane with `const ptr 0` (an `icmp` at the fat type is
/// not a trust-ir comparison), then the constructor wraps the whole fat pointer.
#[test]
fn a_fat_raw_pointer_into_nonnull_asserts_its_data_lane_is_not_null() {
    let slice_u8 = || Ty::Slice { elem: Box::new(Ty::u8()) };
    let module = lower(&cast_fn(
        Ty::RawPtr { mutable: false, pointee: Box::new(slice_u8()) },
        nonnull_of("core::ptr::non_null::NonNull", slice_u8()),
    ));
    let wrapper = struct_ty(&module, "core::ptr::non_null::NonNull");
    let param = the_parameter(&module);
    let nodes = nodes(&module);
    let constructor = the_constructor(&nodes, &wrapper, param);
    assert_no_seed(&nodes);
    let data: Vec<(usize, ValueId)> = nodes
        .iter()
        .enumerate()
        .filter_map(|(index, node)| match (&node.inst, node.results.as_slice()) {
            (Inst::PtrData { ptr, .. }, [result]) if *ptr == param => Some((index, *result)),
            _ => None,
        })
        .collect();
    let [(data_index, data)] = data.as_slice() else {
        panic!("one PtrData of the fat source, got {data:?} in {nodes:#?}")
    };
    let compares = r107_compares(&nodes, *data, &IrTy::Ptr);
    let [(compare, nonzero)] = compares.as_slice() else {
        panic!("one `data != 0` compare, got {compares:?} in {nodes:#?}")
    };
    let assert = the_assert_of(&nodes, *nonzero);
    assert!(
        *data_index < *compare && *compare < assert && assert < constructor,
        "data lane, compare, assert, constructor: {nodes:#?}"
    );
}

/// An operand that is itself a REFERENCE is not charged: it is non-null by its own
/// validity invariant (`Arguments::new`'s `&[u8; N] -> NonNull<u8>`, the coroutine
/// `&mut Context` shim). The constructor is still the one-field newtype's.
/// `NonNull::from_ref` is NOT this shape: it transmutes `&raw const *r`, a raw
/// pointer, which `a_raw_pointer_or_integer_into_nonnull_or_nonzero_asserts_a_typed_zero_compare`
/// shows is charged outside real-sysroot std (`from_ref` itself is a std member, and
/// `r107_charges_every_body_but_an_authenticated_sysroot_member` exempts those).
#[test]
fn a_reference_into_nonnull_is_not_charged() {
    let module = lower(&cast_fn(
        Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) },
        nonnull_of("core::ptr::non_null::NonNull", Ty::u8()),
    ));
    let wrapper = struct_ty(&module, "core::ptr::non_null::NonNull");
    let param = the_parameter(&module);
    let nodes = nodes(&module);
    the_constructor(&nodes, &wrapper, param);
    assert_no_seed(&nodes);
    assert!(
        !nodes.iter().any(|node| matches!(node.inst, Inst::Assert { .. } | Inst::ICmp { .. })),
        "a reference source charges no compare and no assert: {nodes:#?}"
    );
}

/// R107 charges an integer source whose wrapper is NOT built by the constructor
/// arm, and the charge comes before the stamped havoc that builds it. Every integer
/// type the arm charges has a row into the definitional `NonNull<u8>` (field 0 is a
/// raw pointer, not the source's type), which is the shape the extractor admits: an
/// address word into `NonNull` (`usize_to_nonnull`, `Arguments::from_str`'s
/// `transmute(s.len() << 1 | 1)`, and `asserted_wrap`, which admits a value source
/// on the premise that this arm charges it). The last row is the real `NonZero<u32>`,
/// whose field is core's niche-typed `NonZeroU32Inner`. A nonzero source passes the
/// assert and stops at the havoc (`UndefinedBehavior`: the interpreter refuses an
/// aggregate `Undef`); a zero source fails the assert first (`Panic`).
#[test]
fn an_integer_into_a_wrapper_of_another_field_type_is_charged_before_its_havoc() {
    let int = |width, signed| Ty::Int { width, signed };
    let nonnull_u8 = || nonnull_of("core::ptr::non_null::NonNull", Ty::u8());
    let rows: Vec<(Ty, Ty, IrTy)> = vec![
        (int(8, false), nonnull_u8(), IrTy::U8),
        (int(16, false), nonnull_u8(), IrTy::U16),
        (int(32, false), nonnull_u8(), IrTy::U32),
        (int(64, false), nonnull_u8(), IrTy::U64),
        (int(128, false), nonnull_u8(), IrTy::U128),
        (Ty::PtrSizedInt { signed: false }, nonnull_u8(), IrTy::Usize),
        (int(8, true), nonnull_u8(), IrTy::I8),
        (int(16, true), nonnull_u8(), IrTy::I16),
        (int(32, true), nonnull_u8(), IrTy::I32),
        (int(64, true), nonnull_u8(), IrTy::I64),
        (int(128, true), nonnull_u8(), IrTy::I128),
        (Ty::PtrSizedInt { signed: true }, nonnull_u8(), IrTy::Isize),
        (
            Ty::u32(),
            Ty::adt(
                "core::num::nonzero::NonZero",
                vec![(
                    "0".to_string(),
                    Ty::adt(
                        "core::num::niche_types::NonZeroU32Inner",
                        vec![("0".into(), Ty::u32())],
                    ),
                )],
            ),
            IrTy::U32,
        ),
    ];
    for (from, to, cmp_ty) in rows {
        let module = lower(&cast_fn(from, to.clone()));
        let Ty::Adt { name, .. } = &to else { unreachable!() };
        let wrapper = struct_ty(&module, name);
        let param = the_parameter(&module);
        let nodes = nodes(&module);
        let compares = r107_compares(&nodes, param, &cmp_ty);
        let [(_, nonzero)] = compares.as_slice() else {
            panic!("{cmp_ty:?} -> {name}: one `param != 0` compare, got {compares:?} in {nodes:#?}")
        };
        let assert = the_assert_of(&nodes, *nonzero);
        let havocs: Vec<usize> = nodes
            .iter()
            .enumerate()
            .filter(|(_, node)| matches!(&node.inst, Inst::Undef { ty } if *ty == wrapper))
            .map(|(index, _)| index)
            .collect();
        let [havoc] = havocs.as_slice() else {
            panic!("{cmp_ty:?} -> {name}: one Undef of the wrapper, got {havocs:?}")
        };
        assert!(assert < *havoc, "{cmp_ty:?} -> {name}: the charge precedes the havoc: {nodes:#?}");
        assert!(!nodes.iter().any(|node| matches!(node.inst, Inst::MakeAggregate { .. })));

        let run = |value: i128| {
            Interpreter::with_module(&module).execute_func(
                module.functions[0].id,
                vec![InterpretValue::int(cmp_ty.clone(), value).expect("fits")],
            )
        };
        let zero = run(0).expect_err("a zero source fails the R107 assert");
        assert_eq!(zero.code, InterpretErrorCode::Panic, "{cmp_ty:?} -> {name}: {zero:?}");
        let nonzero =
            run(1).expect_err("a nonzero source passes the assert and stops at the havoc");
        assert_eq!(
            nonzero.code,
            InterpretErrorCode::UndefinedBehavior,
            "{cmp_ty:?} -> {name}: the assert passes a nonzero source: {nonzero:?}"
        );
    }
}

/// A source that is itself a validity wrapper is not charged: `NonNull<u8> ->
/// NonNull<i32>` (a `NonNull::cast` spelled as one transmute) and the
/// `NonZero<usize>` that `NonNull::without_provenance` transmutes are each non-zero
/// by their own invariant. An `icmp` at a struct type is not a trust-ir comparison,
/// so charging one would make the module invalid, as the old `i64` zero made a
/// pointer source's. Every source that is neither a raw pointer nor an integer takes
/// this uncharged path, which this test justifies only for validity wrappers; any other
/// aggregate or a float is the gap `lower.rs`'s R107 comment states (charged by the
/// MIR row's HIR half when the user writes it). The `NonNull` row's module validates.
/// The `NonZero` row's struct-to-struct bitcast needs an ADT layout, which only the
/// FAITHFUL lane's extractor fills (`trust-mir-extract` `ty_convert.rs`); the verifier
/// lane carries none, there or in this fixture, so the module is refused for that
/// layout alone (fail-closed) and for no charge.
#[test]
fn a_validity_wrapper_source_is_not_charged() {
    let nonzero_usize = Ty::adt(
        "core::num::nonzero::NonZero",
        vec![(
            "0".to_string(),
            Ty::adt(
                "core::num::niche_types::NonZeroUsizeInner",
                vec![("0".into(), Ty::PtrSizedInt { signed: false })],
            ),
        )],
    );
    let rows = [
        (
            nonnull_of("core::ptr::non_null::NonNull", Ty::u8()),
            nonnull_of("core::ptr::non_null::NonNull", Ty::i32()),
            true,
        ),
        (nonzero_usize, nonnull_of("core::ptr::non_null::NonNull", Ty::u8()), false),
    ];
    for (from, to, validates) in rows {
        let module = lower_to_trust_ir(&cast_fn(from.clone(), to.clone())).expect("lowers");
        let errors = validate_module(&module);
        if validates {
            assert!(errors.is_empty(), "{from:?} -> {to:?} must validate: {errors:?}");
        } else {
            assert!(
                !errors.is_empty()
                    && errors
                        .iter()
                        .all(|error| format!("{error:?}").starts_with("CastLayoutUnsupported")),
                "{from:?} -> {to:?}: refused for the fixture's missing layout alone: {errors:?}"
            );
        }
        let nodes = nodes(&module);
        assert!(
            !nodes.iter().any(|node| matches!(node.inst, Inst::Assert { .. } | Inst::ICmp { .. })),
            "{from:?} -> {to:?}: a validity-wrapper source charges no compare and no assert: {nodes:#?}"
        );
    }
}

#[test]
fn an_integer_cast_to_a_one_field_wrapper_of_its_type_is_one_constructor() {
    let module = lower(&cast_fn(Ty::u64(), hash_wrapper()));
    let wrapper = struct_ty(&module, "test::H");
    let param = the_parameter(&module);
    let nodes = nodes(&module);

    the_constructor(&nodes, &wrapper, param);
    assert_no_seed(&nodes);
    // No validity invariant is owed for `test::H`: the R107 assert is keyed on the
    // `NonNull`/`NonZero` names only.
    assert!(
        !nodes.iter().any(|node| matches!(node.inst, Inst::Assert { .. })),
        "a u64 -> H cast charges no assert: {nodes:#?}"
    );

    let argument = InterpretValue::int(IrTy::U64, 0xDEAD_BEEF_0000_0001).expect("fits in u64");
    let outcome = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![argument.clone()])
        .expect("the wrapper construction executes");
    assert_eq!(returned_lanes(&outcome, &wrapper), vec![argument], "lane 0 is the argument");
}

/// NEGATIVE CONTROL. `u32 -> H { h: u64 }`: field 0's type (`u64`) is not the
/// source's (`u32`), so field 0 is not the value and the constructor arm must not
/// fire. Today the arm's other branch emits one `Undef` of the struct type stamped
/// `FreshSymbolicHavoc`: a fact-free value, which the interpreter refuses to run.
#[test]
fn an_integer_cast_to_a_one_field_wrapper_of_another_type_is_a_stamped_havoc() {
    let module = lower(&cast_fn(Ty::u32(), hash_wrapper()));
    let wrapper = struct_ty(&module, "test::H");
    let nodes = nodes(&module);

    assert!(
        !nodes.iter().any(|node| matches!(
            node.inst,
            Inst::MakeAggregate { .. } | Inst::InsertField { .. } | Inst::Cast { .. }
        )),
        "a width-changing wrapper cast builds nothing and emits no cast: {nodes:#?}"
    );
    let havocs: Vec<&&InstrNode> =
        nodes.iter().filter(|node| matches!(node.inst, Inst::Undef { .. })).collect();
    let [havoc] = havocs.as_slice() else { panic!("exactly one Undef, got {havocs:#?}") };
    assert!(matches!(&havoc.inst, Inst::Undef { ty } if *ty == wrapper), "{havoc:?}");
    assert!(
        havoc.proofs.iter().any(|proof| matches!(proof, ProofAnnotation::FreshSymbolicHavoc)),
        "the havoc is stamped FreshSymbolicHavoc: {havoc:?}"
    );

    let argument = InterpretValue::int(IrTy::U32, 7).expect("fits in u32");
    let error = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![argument])
        .expect_err("an Undef at a struct type does not execute");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
}

/// `fn f() -> [i32; 0] { [] }`: the empty array is one empty-array constant.
#[test]
fn an_empty_array_construction_is_the_empty_array_constant() {
    let array = Ty::Array { elem: Box::new(Ty::i32()), len: 0 };
    let func = VerifiableFunction {
        name: "empty_array".to_string(),
        def_path: "test::empty_array".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: array.clone(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(AggregateKind::Array, vec![]),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: array,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    let module = lower(&func);
    let nodes = nodes(&module);
    // `[i32; 0]` maps to `Array(elem, 0)`, `elem` naming the module's `i32` type row.
    let is_empty_i32_array =
        |ty: &IrTy| matches!(ty, IrTy::Array(elem, 0) if module.ty(*elem) == Some(&IrTy::I32));

    let constants: Vec<&&InstrNode> = nodes
        .iter()
        .filter(|node| matches!(&node.inst, Inst::Const { ty, .. } if is_empty_i32_array(ty)))
        .collect();
    let [constant] = constants.as_slice() else {
        panic!("exactly one Const at [i32 x 0], got {constants:#?} in {nodes:#?}")
    };
    let Inst::Const { ty: array_ty, value } = &constant.inst else { unreachable!() };
    assert!(
        matches!(value, Constant::Array(lanes) if lanes.is_empty()),
        "the constant is the empty array: {constant:?}"
    );
    for node in &nodes {
        assert!(
            !matches!(
                &node.inst,
                Inst::Undef { ty } | Inst::MakeAggregate { ty, .. } | Inst::ArraySplat { ty, .. }
                    if is_empty_i32_array(ty)
            ),
            "no Undef, MakeAggregate or ArraySplat at [i32 x 0]: {node:?}"
        );
    }

    let outcome = Interpreter::with_module(&module)
        .execute_func(module.functions[0].id, vec![])
        .expect("the empty array executes");
    let [returned] = outcome.returns.as_slice() else {
        panic!("one returned value, got {:?}", outcome.returns)
    };
    assert_eq!(&returned.ty, array_ty, "{returned:?}");
    let InterpretValueKind::Array(lanes) = &returned.kind else {
        panic!("the returned value is an array, got {returned:?}")
    };
    assert_eq!(lanes.len(), 0, "the returned array is empty: {returned:?}");
}

/// `ty` (a `Ty::Adt`) carrying the extractor's identity stamp `wrapper`, as
/// `trust-mir-extract`'s `validity_wrapper_of` writes it from the ADT's definition.
fn stamped_wrapper(mut ty: Ty, wrapper: trust_types::ValidityWrapper) -> Ty {
    let Ty::Adt { validity_wrapper, .. } = &mut ty else { panic!("a wrapper is an ADT: {ty:?}") };
    *validity_wrapper = Some(wrapper);
    ty
}

/// R107-IDENTITY-1: the charge follows the EXTRACTOR'S VERDICT on the target's
/// definition (`Ty::Adt::validity_wrapper`), not its printed name. Every target here
/// is spelled under a name the name test does not list (a `#![no_core]` crate's own
/// `non_null` lang item prints `mycore::Ptr`, and the compiler uses it as THE
/// `NonNull` of that compilation; the extractor's `ptr_to_nonnull` admits a
/// transmute into it by that same lang item). Each carries the stamp and is charged
/// exactly as the definitional `core` spelling is: one `param != 0` compare at the
/// source's own type, its unkinded `Assert`, then the constructor; a zero source
/// fails the assert.
///
/// Before the stamp the arm read only the name, so each of these lowered with no
/// charge and a native lane could prove a body that wraps a null pointer or a zero.
/// The same names without the stamp are the control: still uncharged, because no
/// verdict and no listed name says they are wrappers.
#[test]
fn r107_charges_a_stamped_validity_wrapper_under_any_name() {
    use trust_types::ValidityWrapper;
    let raw_u8 = || Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let null = InterpretValue { ty: IrTy::Ptr, kind: InterpretValueKind::NullPtr };
    let rows: Vec<(Ty, Ty, ValidityWrapper, IrTy, InterpretValue)> = vec![
        (raw_u8(), nonnull_of("mycore::Ptr", Ty::u8()), ValidityWrapper::NonNull, IrTy::Ptr, null),
        (
            Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
            Ty::adt(
                "mycore::ptr::Ptr",
                vec![(
                    "pointer".to_string(),
                    Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                )],
            ),
            ValidityWrapper::NonNull,
            IrTy::Ptr,
            InterpretValue { ty: IrTy::Ptr, kind: InterpretValueKind::NullPtr },
        ),
        (
            Ty::u32(),
            Ty::adt("mycore::Nz", vec![("0".to_string(), Ty::u32())]),
            ValidityWrapper::NonZero,
            IrTy::U32,
            InterpretValue::int(IrTy::U32, 0).expect("fits"),
        ),
        (
            Ty::i64(),
            Ty::adt("mycore::num::Nz", vec![("0".to_string(), Ty::i64())]),
            ValidityWrapper::NonZero,
            IrTy::I64,
            InterpretValue::int(IrTy::I64, 0).expect("fits"),
        ),
    ];
    for (from, to, wrapper, cmp_ty, zero_arg) in rows {
        let Ty::Adt { name, .. } = &to else { unreachable!() };
        let name = name.clone();
        assert!(
            !crate::lower::r107_name_is_validity_wrapper(&name),
            "{name}: the fixture must be a spelling the name test does not list"
        );

        // The control: the same name with no stamp is not a wrapper to R107.
        let unstamped = lower(&cast_fn(from.clone(), to.clone()));
        let unstamped_nodes = nodes(&unstamped);
        assert!(
            !unstamped_nodes
                .iter()
                .any(|node| matches!(node.inst, Inst::Assert { .. } | Inst::ICmp { .. })),
            "{name}: with no stamp and an unlisted name nothing is charged: {unstamped_nodes:#?}"
        );

        let module = lower(&cast_fn(from, stamped_wrapper(to, wrapper)));
        let ty = struct_ty(&module, &name);
        let param = the_parameter(&module);
        let nodes = nodes(&module);
        let constructor = the_constructor(&nodes, &ty, param);
        let compares = r107_compares(&nodes, param, &cmp_ty);
        let [(compare, nonzero)] = compares.as_slice() else {
            panic!("{name} ({wrapper:?}): one `param != 0` compare, got {compares:?} in {nodes:#?}")
        };
        let assert = the_assert_of(&nodes, *nonzero);
        assert!(*compare < assert && assert < constructor, "{name}: compare, assert, constructor");
        let error = Interpreter::with_module(&module)
            .execute_func(module.functions[0].id, vec![zero_arg])
            .expect_err("a zero source fails the R107 assert");
        assert_eq!(error.code, InterpretErrorCode::Panic, "{name}: {error:?}");
    }
}

/// R107-IDENTITY-1: the stamp only ever ADDS the charge. It does not override the
/// arm's other gates: a reference source and a validity-wrapper source stay
/// uncharged on a stamped target (the reasons the arm's comment gives), and a member
/// the compiler authenticated as std's own body stays exempt. And the name test still
/// charges a listed spelling that carries no stamp (a decoded body), so dropping
/// either trigger is a loss this test sees.
#[test]
fn r107_identity_stamp_adds_the_charge_and_keeps_the_other_gates() {
    use trust_types::ValidityWrapper;
    let charged =
        |module: &Module| nodes(module).iter().any(|node| matches!(node.inst, Inst::Assert { .. }));
    let raw_u8 = || Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let stamped_ptr =
        || stamped_wrapper(nonnull_of("mycore::Ptr", Ty::u8()), ValidityWrapper::NonNull);

    let reference = Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) };
    assert!(
        !charged(&lower(&cast_fn(reference, stamped_ptr()))),
        "a reference source is non-null by its own validity invariant, stamp or no stamp"
    );
    let wrapper_source =
        stamped_wrapper(nonnull_of("mycore::Ptr", Ty::u8()), ValidityWrapper::NonNull);
    let other_target =
        stamped_wrapper(nonnull_of("mycore::Other", Ty::u8()), ValidityWrapper::NonNull);
    // Read off the module before validation: a struct-to-struct cast has no layout
    // evidence in these fixtures (as in `a_validity_wrapper_source_is_not_charged`),
    // and the charge is what is tested here.
    let unvalidated = lower_to_trust_ir(&cast_fn(wrapper_source, other_target))
        .expect("the wrapper-to-wrapper fixture lowers");
    assert!(!charged(&unvalidated), "a validity-wrapper source is non-zero by its own invariant");
    let exempt = "core::ptr::non_null::NonNull::<u8>::from_ref";
    assert!(
        !charged(&lower_with_sysroot_members(
            &cast_fn_at(exempt, raw_u8(), stamped_ptr()),
            &[exempt]
        )),
        "a compiler-authenticated std member is std's obligation, stamp or no stamp"
    );
    assert!(
        charged(&lower(&cast_fn_at(exempt, raw_u8(), stamped_ptr()))),
        "the same member, not authenticated, is charged on the stamp alone"
    );
    assert!(
        charged(&lower(&cast_fn(raw_u8(), nonnull_of("core::ptr::non_null::NonNull", Ty::u8())))),
        "an unstamped definitional spelling is still charged by the name test"
    );
}
