//! Trust (bridge-abi): `lower_module_to_lir` must REFUSE BY NAME, not guess, when
//! the module it is handed declares `StructPassingPolicy::Unclassified` and a
//! by-value aggregate crosses a call edge.
//!
//! # Why this test exists
//!
//! `crates/trust-cg-bridge` classifies by-value aggregates with its OWN size and
//! shape rules — a `Ty::Struct` of <=16 bytes with two plain scalar fields rides
//! a register pair, a single-field one rides Direct, a larger one rides a hidden
//! pointer — and it reads `ParamAttrs::sret` for the indirect return. trust's own
//! producer (`trust_thir_lower::stamp_target_info_if_vacuous`) emits NO
//! `ParamAttrs` at all and stamps `struct_passing = unclassified`, whose
//! contract in `trust_ir` is a contract on the CONSUMER:
//!
//! > A CONSUMER MUST NOT infer either scheme from it — it is a declaration of
//! > absence, not a third convention. A backend needing a classification must
//! > refuse the module rather than pick one.
//!
//! `lower_module_to_lir` is a PUBLIC library API with no `FnAbi` argument. The
//! rustc driver happens to cross-check every admitted parameter and the return
//! against rustc's real `PassMode` before calling it (the F1 ABI validator in
//! `rustc_codegen_trust_cg`), so on that lane the classification is checked
//! against an authority that has the answer. Every OTHER caller got the size
//! rule with nothing behind it — "self-consistent both ways, wrong across a
//! codegen boundary", the class trust-cg measured and fixed in 822fdc69 /
//! 67122610 where a `{i32,i32}` packed into one register made llvm x tcg exit
//! 188 at `-O0`.
//!
//! So the admission is now explicit: the bare entry point refuses, and the ONLY
//! way past it is to ATTACH the cross-check
//! (`lower_module_to_lir_with_abi_cross_check`) — evidence added, never a check
//! relaxed.
//!
//! # One rule for all three policies (trust-ir SPEC §17, ratified 2026-09-27)
//!
//! The format now states the consumer's obligation for every
//! `struct_passing` value, and this converter holds ONE rule against it: a
//! by-value aggregate edge is admitted only under `unclassified` PLUS the
//! cross-check token. Under `native_c` the consumer must classify by the
//! target's C ruleset, which this converter does not implement (its size rules
//! are rustc Rust-ABI shapes, and the token attests rustc's placement, not the
//! C one); under `always_memory` the module claims no such slot exists. Both
//! are refused with or without the token — until 2026-09-27 both were admitted
//! unchecked (`a_declared_policy_is_not_second_guessed`, retired), on the
//! retracted reading that the policy obliged the producer to mark
//! `byval`/`sret`. A recorded `ParamAttrs.pass` / `ParamAttrs.ext` /
//! `FuncAttrs.ret` fact, which this converter does not read, is refused under
//! every policy.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_cg_bridge::{
    AbiPassModeCrossCheck, ModuleLirError, lower_module_to_lir,
    lower_module_to_lir_maybe_cross_checked, lower_module_to_lir_with_abi_cross_check,
    lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check,
};
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FieldDef, FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, GlobalId, StructId, ValueId};
use trust_ir::{
    ArgExt, Block, Constant, Endianness, EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding,
    EnumVariant, Function as IrFunction, Global, Linkage, Module, ParamAttrs, PassMode, StructDef,
    StructPassingPolicy, TargetInfo,
};

/// A pinned AArch64 target carrying `policy` as its aggregate-passing claim.
fn target(policy: StructPassingPolicy) -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".to_string(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: policy,
    }
}

/// `fn r(R) -> usize { r.start - r.end }` with `R` a 16-byte two-scalar struct —
/// the `Range<usize>` argument shape, and a shape this converter DOES lower
/// (`by_value_pair_struct_param_maps_fields_to_register_formals`). The aggregate
/// is therefore a real crossing, not a shape that would have been refused for
/// some other reason.
fn pair_struct_module(target_info: Option<TargetInfo>) -> Module {
    let mut module = Module::new("t");
    module.target_info = target_info;
    module.structs.push(StructDef {
        id: StructId::new(0),
        name: "R".to_string(),
        fields: vec![
            FieldDef { name: "start".to_string(), ty: Ty::Usize, offset: Some(8) },
            FieldDef { name: "end".to_string(), ty: Ty::Usize, offset: Some(0) },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let sty = Ty::Struct(StructId::new(0));
    module.func_types.push(FuncTy {
        params: vec![sty.clone()],
        returns: vec![Ty::Usize],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "r", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    b0.params.push((ValueId::new(0), sty));
    b0.body.push(
        InstrNode::new(Inst::ExtractField { ty: Ty::Usize, aggregate: ValueId::new(0), field: 0 })
            .with_result(ValueId::new(1)),
    );
    b0.body.push(
        InstrNode::new(Inst::ExtractField { ty: Ty::Usize, aggregate: ValueId::new(0), field: 1 })
            .with_result(ValueId::new(2)),
    );
    b0.body.push(
        InstrNode::new(Inst::BinOp {
            op: trust_ir::inst::BinOp::Sub,
            ty: Ty::Usize,
            lhs: ValueId::new(1),
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
    );
    b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(3)] }));
    f.blocks.push(b0);
    module.functions.push(f);
    module
}

/// `fn k(u64) -> u64 { x }` — the same module shape with NO aggregate anywhere.
/// This is the positive control: it proves the refusal below is about the
/// aggregate crossing and not about `unclassified` (or about `target_info`
/// being pinned at all).
fn scalar_module(target_info: Option<TargetInfo>) -> Module {
    let mut module = Module::new("t");
    module.target_info = target_info;
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    b0.params.push((ValueId::new(0), Ty::U64));
    b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    f.blocks.push(b0);
    module.functions.push(f);
    module
}

/// The 16-byte two-`usize` `Range` shape, fields in declaration order.
fn range_struct() -> StructDef {
    StructDef {
        id: StructId::new(0),
        name: "R".to_string(),
        fields: vec![
            FieldDef { name: "start".to_string(), ty: Ty::Usize, offset: Some(0) },
            FieldDef { name: "end".to_string(), ty: Ty::Usize, offset: Some(8) },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }
}

/// [`scalar_module`]'s `k(u64) -> u64` with a call spliced in to a bodyless
/// callee `takes_range(R) -> usize`: the function being lowered is entirely
/// scalar, and the aggregate crosses the edge to its CALLEE.
fn aggregate_callee_edge_module(target_info: Option<TargetInfo>) -> Module {
    let mut module = scalar_module(target_info);
    module.structs.push(range_struct());
    // The CALLEE's signature is the one carrying the aggregate.
    module.func_types.push(FuncTy {
        params: vec![Ty::Struct(StructId::new(0))],
        returns: vec![Ty::Usize],
        is_vararg: false,
        abi: None,
    });
    module.functions.push(IrFunction::new(
        FuncId::new(1),
        "takes_range",
        FuncTyId::new(1),
        BlockId::new(0),
    ));
    // Splice a call to it into the scalar caller, before its `Return`.
    let caller = &mut module.functions[0];
    let body = &mut caller.blocks[0].body;
    body.insert(
        0,
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(9)),
    );
    module
}

/// `fn r(R) -> usize { g(r) }` under `unclassified`: the function being lowered
/// takes the aggregate (the edge a token attests) and FORWARDS it to a callee
/// `g(R) -> usize` (an edge it does not). `g` is a local pure leaf `{ 7 }` when
/// `inlinable_callee`, and a bodyless declaration otherwise.
fn aggregate_forwarding_module(inlinable_callee: bool) -> Module {
    let mut module = Module::new("t");
    module.target_info = Some(target(StructPassingPolicy::Unclassified));
    module.structs.push(range_struct());
    let sty = Ty::Struct(StructId::new(0));
    module.func_types.push(FuncTy {
        params: vec![sty.clone()],
        returns: vec![Ty::Usize],
        is_vararg: false,
        abi: None,
    });
    let mut r = IrFunction::new(FuncId::new(0), "r", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    b0.params.push((ValueId::new(0), sty.clone()));
    b0.body.push(
        InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] })
            .with_result(ValueId::new(1)),
    );
    b0.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
    r.blocks.push(b0);
    module.functions.push(r);
    let mut g = IrFunction::new(FuncId::new(1), "g", FuncTyId::new(0), BlockId::new(0));
    if inlinable_callee {
        let mut body = Block::new(BlockId::new(0));
        body.params.push((ValueId::new(0), sty));
        body.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Usize, value: Constant::Int(7) })
                .with_result(ValueId::new(1)),
        );
        body.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        g.blocks.push(body);
    }
    module.functions.push(g);
    module
}

/// A module global whose NAME is the function symbol `name`: `GlobalAddr` of it
/// is how a frontend spells `&name`, and it is the KNOWN-target shape both the
/// real-call arm (`global_addr_provenance`) and the recorded-fact scan
/// (`resolve_static_indirect_callee`) resolve through `function_by_name`.
fn function_symbol_proxy(name: &str) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    }
}

/// `enum E { A, B }` with the producer's direct one-byte tag. It is the one
/// by-value aggregate this converter CARRIES as a scalar
/// (`fieldless_enum_carrier`), so a slot of it reaches the lowering rather than
/// being refused as an unsupported type first. Only the admission decides it.
fn fieldless_enum() -> EnumDef {
    let variants = ["A", "B"]
        .iter()
        .map(|name| EnumVariant {
            name: (*name).to_string(),
            fields: Vec::new(),
            field_names: Vec::new(),
        })
        .collect();
    let mut def = EnumDef::new(EnumId::new(0), "E", variants);
    def.discriminants = vec![Some(0), Some(1)];
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 0 },
        size: 1,
        align: 1,
        variant_field_offsets: vec![Vec::new(); 2],
    });
    def
}

/// How the indirect call in [`indirect_edge_module`] obtains its function
/// pointer and its argument.
#[derive(Debug, Clone, Copy)]
enum IndirectShape {
    /// `f(fp: ptr) -> u64 { fp(E::B) }` — an OPEN target (an incoming fn
    /// pointer); the argument is a constant, so the function's OWN signature
    /// carries no aggregate at all.
    OpenConstArg,
    /// `f(e: E, fp: ptr) -> u64 { fp(e) }` — an OPEN target; the argument is the
    /// function's own aggregate formal (the edge a token DOES place), forwarded
    /// across an edge it does not.
    OpenForwardedArg,
    /// `f() -> u64 { (&g)(E::B) }` with `g(E) -> u64` a local body — a KNOWN
    /// target through a function-symbol proxy global.
    KnownTarget,
}

/// An `unclassified` module whose function 0 makes one `CallIndirect` with
/// declared signature `(arg) -> u64`, where `arg` is `E` when `aggregate` and
/// `u8` otherwise (the scalar twin, which must lower). The function pointer and
/// the argument come from `shape`.
fn indirect_edge_module(shape: IndirectShape, aggregate: bool) -> Module {
    let mut module = Module::new("t");
    module.target_info = Some(target(StructPassingPolicy::Unclassified));
    module.enums.push(fieldless_enum());
    let (arg_ty, arg_value) = if aggregate {
        (Ty::Enum(EnumId::new(0)), Constant::Aggregate(vec![Constant::Int(1)]))
    } else {
        (Ty::U8, Constant::Int(1))
    };
    let own_params = match shape {
        IndirectShape::OpenConstArg => vec![Ty::Ptr],
        IndirectShape::OpenForwardedArg => vec![arg_ty.clone(), Ty::Ptr],
        IndirectShape::KnownTarget => Vec::new(),
    };
    // FuncTy 0: the lowered function. FuncTy 1: the indirect edge's `sig`.
    module.func_types.push(FuncTy {
        params: own_params,
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    module.func_types.push(FuncTy {
        params: vec![arg_ty.clone()],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });

    let (arg, fp, called) = (ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let mut f = IrFunction::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    let mut b0 = Block::new(BlockId::new(0));
    match shape {
        IndirectShape::OpenConstArg => {
            b0.params.push((fp, Ty::Ptr));
            b0.body.push(
                InstrNode::new(Inst::Const { ty: arg_ty.clone(), value: arg_value })
                    .with_result(arg),
            );
        }
        IndirectShape::OpenForwardedArg => {
            b0.params.push((arg, arg_ty.clone()));
            b0.params.push((fp, Ty::Ptr));
        }
        IndirectShape::KnownTarget => {
            b0.body.push(
                InstrNode::new(Inst::Const { ty: arg_ty.clone(), value: arg_value })
                    .with_result(arg),
            );
            b0.body.push(
                InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) }).with_result(fp),
            );
        }
    }
    b0.body.push(
        InstrNode::new(Inst::CallIndirect {
            callee: fp,
            sig: FuncTyId::new(1),
            args: vec![arg],
            calling_conv: Default::default(),
        })
        .with_result(called),
    );
    b0.body.push(InstrNode::new(Inst::Return { values: vec![called] }));
    f.blocks.push(b0);
    module.functions.push(f);

    if let IndirectShape::KnownTarget = shape {
        // `g(arg) -> u64 { 7 }`, the proxy global's function, typed exactly as
        // the edge's `sig`.
        module.globals.push(function_symbol_proxy("g"));
        let mut g = IrFunction::new(FuncId::new(1), "g", FuncTyId::new(1), BlockId::new(0));
        let mut body = Block::new(BlockId::new(0));
        body.params.push((ValueId::new(0), arg_ty));
        body.body.push(
            InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) })
                .with_result(ValueId::new(1)),
        );
        body.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }));
        g.blocks.push(body);
        module.functions.push(g);
    }
    module
}

fn refusal(result: Result<impl Sized, ModuleLirError>, what: &str) -> (String, String) {
    match result {
        Ok(_) => panic!("{what}: expected a refusal, got a lowering"),
        Err(ModuleLirError::UnclassifiedAggregateAbi { name, detail }) => {
            let rendered = ModuleLirError::UnclassifiedAggregateAbi {
                name: name.clone(),
                detail: detail.clone(),
            }
            .to_string();
            (detail, rendered)
        }
        Err(other) => {
            panic!("{what}: expected `UnclassifiedAggregateAbi`, got a DIFFERENT refusal: {other}")
        }
    }
}

/// THE REFUSAL. An `unclassified` module whose own signature passes an aggregate
/// by value is refused by name, before any size rule is consulted.
#[test]
fn unclassified_module_with_by_value_aggregate_is_refused_by_name() {
    let module = pair_struct_module(Some(target(StructPassingPolicy::Unclassified)));
    let (detail, _) = refusal(
        lower_module_to_lir(&module, FuncId::new(0)),
        "a 16-byte two-scalar struct formal under `unclassified`",
    );
    assert!(
        detail.contains("the function's own signature"),
        "the refusal must name WHICH edge carries the aggregate, got: {detail}"
    );
    assert!(
        detail.contains("parameter 0"),
        "the refusal must name WHICH slot carries it, got: {detail}"
    );
}

/// RULING v7/D3: a refusal carries the fix, with options. All three are named,
/// and each is actionable by a different party (the consumer, the producer, the
/// author of the signature).
#[test]
fn the_refusal_carries_the_fix_and_its_options() {
    let module = pair_struct_module(Some(target(StructPassingPolicy::Unclassified)));
    let (_, rendered) = refusal(lower_module_to_lir(&module, FuncId::new(0)), "options check");
    for fragment in [
        "struct_passing = unclassified",
        "must refuse the module rather than pick one",
        "lower_module_to_lir_with_abi_cross_check",
        "validate_codegen_instance_abi_trust_ir",
        "pre-lower the crossing",
        "leading `sret` pointer parameter",
        "scalarize the signature",
    ] {
        assert!(
            rendered.contains(fragment),
            "the refusal must mention `{fragment}`; full text was:\n{rendered}"
        );
    }
    // The RETRACTED advice (trust-ir SPEC §17): "stamp `native_c` or
    // `always_memory` and emit the `byval`/`sret` marks that policy promises".
    // No producer ever carried that marking, and this converter now refuses a
    // by-value aggregate under both declared policies, so the refusal must not
    // send a producer there.
    assert!(
        !rendered.contains("byval"),
        "the refusal must not repeat the retracted byval/sret-marking advice:\n{rendered}"
    );
}

/// THE WAY PAST IT IS EVIDENCE, NOT A RELAXATION. With a pass-mode cross-check
/// attached the SAME module lowers, and lowers to the same two register formals
/// the converter produced before this gate existed — so the driver's lane is
/// unchanged in output, only in what it had to say about itself.
#[test]
fn an_attached_pass_mode_cross_check_admits_the_same_module() {
    let module = pair_struct_module(Some(target(StructPassingPolicy::Unclassified)));
    let cross_check = AbiPassModeCrossCheck::attested_by("test: rustc FnAbi PassMode::Pair");
    let lir = lower_module_to_lir_with_abi_cross_check(&module, FuncId::new(0), &cross_check)
        .expect("the cross-checked lowering must be admitted");
    assert_eq!(lir.signature.params.len(), 2, "two register formals, exactly as before the gate");
    assert_eq!(cross_check.authority(), "test: rustc FnAbi PassMode::Pair");
}

/// POSITIVE CONTROL. A scalar module under the SAME `unclassified` policy still
/// lowers through the bare entry point: the claim ranges over nothing, so there
/// is nothing to refuse.
#[test]
fn a_scalar_module_under_unclassified_still_lowers() {
    let module = scalar_module(Some(target(StructPassingPolicy::Unclassified)));
    let lir = lower_module_to_lir(&module, FuncId::new(0))
        .expect("a scalar signature makes the `unclassified` claim vacuous");
    assert_eq!(lir.signature.params.len(), 1);
}

/// `NATIVE_C` IS REFUSED, WITH OR WITHOUT A TOKEN (trust-ir SPEC §17). Under
/// `native_c` the CONSUMER must place a by-value aggregate by the target's C
/// ruleset for the edge's convention. This converter implements none — its
/// size rules are rustc Rust-ABI shapes — and the token attests rustc's
/// placement for the lowered instance, not the C placement the module claims.
/// So the declared policy that used to be admitted unchecked (the retired
/// `a_declared_policy_is_not_second_guessed`) is now refused by its own name,
/// on the function's own edge and on a callee's, and the scalar twin under the
/// same policy still lowers: the refusal is about the aggregate, not the value.
#[test]
fn native_c_by_value_aggregate_is_refused_with_or_without_a_token() {
    let module = pair_struct_module(Some(target(StructPassingPolicy::NativeC)));
    let token = AbiPassModeCrossCheck::attested_by("test: rustc FnAbi PassMode::Pair");
    for (what, result) in [
        ("bare", lower_module_to_lir(&module, FuncId::new(0))),
        (
            "with a pass-mode cross-check",
            lower_module_to_lir_with_abi_cross_check(&module, FuncId::new(0), &token),
        ),
    ] {
        match result {
            Err(ModuleLirError::NativeCAggregateAbiUnsupported { detail, .. }) => assert!(
                detail.contains("the function's own signature") && detail.contains("parameter 0"),
                "{what}: the refusal must name the edge and the slot, got: {detail}"
            ),
            Err(other) => panic!("{what}: expected `NativeCAggregateAbiUnsupported`, got: {other}"),
            Ok(_) => panic!(
                "{what}: a `native_c` by-value aggregate was LOWERED by a converter that \
                 implements no native-C aggregate ruleset"
            ),
        }
    }

    let callee_edge = aggregate_callee_edge_module(Some(target(StructPassingPolicy::NativeC)));
    match lower_module_to_lir_with_abi_cross_check(&callee_edge, FuncId::new(0), &token) {
        Err(ModuleLirError::NativeCAggregateAbiUnsupported { detail, .. }) => assert!(
            detail.contains("the call edge to `takes_range`"),
            "the refusal must name the callee edge, got: {detail}"
        ),
        other => panic!("a `native_c` aggregate callee edge must be refused, got: {other:?}"),
    }

    let scalar = scalar_module(Some(target(StructPassingPolicy::NativeC)));
    lower_module_to_lir(&scalar, FuncId::new(0))
        .expect("a scalar signature makes the `native_c` claim range over nothing");
}

/// `ALWAYS_MEMORY` IS REFUSED EVEN WITH A TOKEN (trust-ir SPEC §17). The policy
/// says every aggregate crossing is pre-lowered, so a by-value aggregate slot
/// means the module contradicts itself (`AlwaysMemoryByValueAggregate` in the
/// ratified validator) — and no evidence from outside a module reconciles it
/// with itself. The scalar twin lowers.
#[test]
fn always_memory_by_value_aggregate_is_refused_even_with_a_token() {
    let module = pair_struct_module(Some(target(StructPassingPolicy::AlwaysMemory)));
    let token = AbiPassModeCrossCheck::attested_by("test: rustc FnAbi PassMode::Pair");
    for (what, result) in [
        ("bare", lower_module_to_lir(&module, FuncId::new(0))),
        (
            "with a pass-mode cross-check",
            lower_module_to_lir_with_abi_cross_check(&module, FuncId::new(0), &token),
        ),
        (
            "with carried evidence",
            lower_module_to_lir_maybe_cross_checked(&module, FuncId::new(0), Some(&token)),
        ),
    ] {
        match result {
            Err(ModuleLirError::AlwaysMemoryByValueAggregate { detail, .. }) => assert!(
                detail.contains("parameter 0"),
                "{what}: the refusal must name the slot, got: {detail}"
            ),
            Err(other) => panic!("{what}: expected `AlwaysMemoryByValueAggregate`, got: {other}"),
            Ok(_) => panic!(
                "{what}: an `always_memory` module with a by-value aggregate slot was LOWERED"
            ),
        }
    }

    let scalar = scalar_module(Some(target(StructPassingPolicy::AlwaysMemory)));
    lower_module_to_lir(&scalar, FuncId::new(0))
        .expect("a scalar signature is pre-lowered by construction");
}

/// Push `g(u64) -> u64 { x }` as function 1 of [`scalar_module`], with `record`
/// applied to its attributes; returns its `FuncTyId` (the indirect edge's `sig`).
fn add_indirect_fact_callee(m: &mut Module, record: fn(&mut IrFunction)) -> FuncTyId {
    let callee_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut callee = IrFunction::new(FuncId::new(1), "g", callee_ty, BlockId::new(0));
    let mut body = Block::new(BlockId::new(0));
    body.params.push((ValueId::new(0), Ty::U64));
    body.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
    callee.blocks.push(body);
    record(&mut callee);
    m.functions.push(callee);
    callee_ty
}

/// Splice `fp = <pointer>; fp(x)` into [`scalar_module`]'s `k` ahead of its
/// `Return`, where `pointer` defines value 8 statically naming function 1.
fn insert_indirect_call(m: &mut Module, pointer: InstrNode, sig: FuncTyId) {
    let body = &mut m.functions[0].blocks[0].body;
    body.insert(0, pointer);
    body.insert(
        1,
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(8),
            sig,
            args: vec![ValueId::new(0)],
            calling_conv: Default::default(),
        })
        .with_result(ValueId::new(9)),
    );
}

/// A RECORDED SLOT FACT THIS CONVERTER DOES NOT READ IS REFUSED UNDER EVERY
/// POLICY (trust-ir SPEC §17). `ParamAttrs.pass`, a non-`None`
/// `ParamAttrs.ext` and any `FuncAttrs.ret` fact each state how a slot crosses
/// the edge; this converter places every slot itself and reads none of them,
/// so it cannot establish that the fact agrees with what it emits. Held on the
/// SCALAR module, so no aggregate refusal can stand in for it, on the
/// function's own edge, on a direct callee's, and on an indirect callee's that
/// resolves statically (both static shapes: a function-symbol proxy global and
/// a `Const FnDef`), under all three policies and with no pinned target, with
/// and without a token. The unmodified module lowers in every one of those
/// cells.
#[test]
fn recorded_pass_ext_and_ret_facts_are_refused_under_every_policy() {
    let token = AbiPassModeCrossCheck::attested_by("test: rustc FnAbi");
    let targets = [
        None,
        Some(target(StructPassingPolicy::Unclassified)),
        Some(target(StructPassingPolicy::NativeC)),
        Some(target(StructPassingPolicy::AlwaysMemory)),
    ];
    type Shape = (&'static str, &'static str, fn(&mut Module));
    let shapes: [Shape; 7] = [
        ("own parameter `pass`", "`ParamAttrs.pass = direct` on parameter 0", |m| {
            m.functions[0].attrs.params =
                vec![ParamAttrs { pass: Some(PassMode::Direct), ..Default::default() }];
        }),
        ("own parameter `ext`", "`ParamAttrs.ext = zeroext` on parameter 0", |m| {
            m.functions[0].attrs.params =
                vec![ParamAttrs { ext: ArgExt::ZeroExt, ..Default::default() }];
        }),
        ("own return slot", "`FuncAttrs.ret` return-slot fact", |m| {
            m.functions[0].attrs.ret = ParamAttrs { ext: ArgExt::SignExt, ..Default::default() };
        }),
        ("own return slot `pass`", "`FuncAttrs.ret` return-slot fact", |m| {
            m.functions[0].attrs.ret =
                ParamAttrs { pass: Some(PassMode::Direct), ..Default::default() };
        }),
        (
            "callee parameter `pass`",
            "the call edge to `scalar_callee` records `ParamAttrs.pass = indirect`",
            |m| {
                let callee_ty = m
                    .add_func_type(FuncTy {
                        params: vec![Ty::U64],
                        returns: vec![Ty::U64],
                        is_vararg: false,
                        abi: None,
                    })
                    .expect("Module::add_func_type: test fixture");
                let mut callee =
                    IrFunction::new(FuncId::new(1), "scalar_callee", callee_ty, BlockId::new(0));
                callee.attrs.params = vec![ParamAttrs {
                    pass: Some(PassMode::Indirect { on_stack: false }),
                    ..Default::default()
                }];
                m.functions.push(callee);
                m.functions[0].blocks[0].body.insert(
                    0,
                    InstrNode::new(Inst::Call {
                        callee: FuncId::new(1),
                        args: vec![ValueId::new(0)],
                    })
                    .with_result(ValueId::new(9)),
                );
            },
        ),
        (
            "indirect callee `ext`, known target through a proxy global",
            "an indirect call edge that resolves statically to `g` records `ParamAttrs.ext = \
             zeroext` on parameter 0",
            |m| {
                let callee_ty = add_indirect_fact_callee(m, |callee| {
                    callee.attrs.params =
                        vec![ParamAttrs { ext: ArgExt::ZeroExt, ..Default::default() }];
                });
                m.globals.push(function_symbol_proxy("g"));
                insert_indirect_call(
                    m,
                    InstrNode::new(Inst::GlobalAddr { global: GlobalId::new(0) })
                        .with_result(ValueId::new(8)),
                    callee_ty,
                );
            },
        ),
        (
            "indirect callee `pass`, known target through `Const FnDef`",
            "an indirect call edge that resolves statically to `g` records `ParamAttrs.pass = \
             direct` on parameter 0",
            |m| {
                let callee_ty = add_indirect_fact_callee(m, |callee| {
                    callee.attrs.params =
                        vec![ParamAttrs { pass: Some(PassMode::Direct), ..Default::default() }];
                });
                insert_indirect_call(
                    m,
                    InstrNode::new(Inst::Const {
                        ty: Ty::Ptr,
                        value: Constant::FnDef(FuncId::new(1)),
                    })
                    .with_result(ValueId::new(8)),
                    callee_ty,
                );
            },
        ),
    ];

    for target_info in &targets {
        for evidence in [None, Some(&token)] {
            let cell = format!("target {:?}, token {}", target_info, evidence.is_some());
            let control = scalar_module(target_info.clone());
            lower_module_to_lir_maybe_cross_checked(&control, FuncId::new(0), evidence)
                .unwrap_or_else(|e| panic!("{cell}: the fact-free control must lower, got: {e}"));
            for (what, needle, apply) in &shapes {
                let mut module = scalar_module(target_info.clone());
                apply(&mut module);
                match lower_module_to_lir_maybe_cross_checked(&module, FuncId::new(0), evidence) {
                    Err(ModuleLirError::RecordedAbiSlotFact { detail, .. }) => assert!(
                        detail.contains(needle),
                        "{cell}, {what}: the refusal must name the fact (`{needle}`), got: {detail}"
                    ),
                    Err(other) => {
                        panic!("{cell}, {what}: expected `RecordedAbiSlotFact`, got: {other}")
                    }
                    Ok(_) => panic!(
                        "{cell}, {what}: a recorded slot fact this converter does not read was \
                         silently dropped"
                    ),
                }
            }
        }
    }
}

/// THE TOKEN COVERS THE LOWERED INSTANCE'S OWN SIGNATURE, NOT ITS CALLEES'.
///
/// The in-tree attester mints the token from rustc's `FnAbi` for the instance
/// it lowers. Under it the admission skips the function's own signature and
/// the DIRECT callee edges, and still scans every `CallIndirect`'s declared
/// `sig`. Every half is pinned here, on the real-call entry point WITH a token:
///
/// * DIRECT, spliced: a local pure leaf callee taking the aggregate is
///   INLINED, and the LIR carries no call opcode at all;
/// * DIRECT, not spliceable: a bodyless callee taking the aggregate is REFUSED
///   (`UnsupportedInst { Call }`) — the real-call arm realizes a `Bl` only for a
///   callee in the single-register scalar fragment
///   (`callee_is_real_call_composable`), so the lowering, not the admission,
///   keeps this edge from becoming a boundary;
/// * INDIRECT: a `CallIndirect` is never spliced, and the real-call arm
///   realizes an OPEN one as a `BLR` after checking only arity and a scalar
///   return. So an aggregate on its declared `sig` is refused BY THE ADMISSION
///   (`UnclassifiedAggregateAbi`), token or not — for an open target whose
///   argument is a constant, one that forwards the function's own
///   token-placed aggregate formal, and a known target through a proxy global.
///   The scalar twin of each still lowers to a real `CallIndirect`, so the
///   refusal is about the aggregate and not about the indirect call.
///
/// Until 2026-09-27 the token ended the scan outright, and both OPEN shapes
/// were admitted and emitted as a `BLR` carrying an enum no authority placed
/// (measured by the review of trust 945998483e).
#[test]
fn a_token_does_not_admit_a_realized_aggregate_call_edge() {
    let token = AbiPassModeCrossCheck::attested_by("test: rustc FnAbi for `r` only");

    let inlinable = aggregate_forwarding_module(true);
    let lir = lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check(
        &inlinable,
        &inlinable.functions[0],
        &token,
    )
    .expect("a pure leaf aggregate callee is spliced inline, so no edge crosses");
    let calls: Vec<String> = lir
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter())
        .filter_map(|inst| match &inst.opcode {
            trust_cg_lower::instructions::Opcode::Call { name, .. } => Some(name.clone()),
            trust_cg_lower::instructions::Opcode::CallIndirect => Some("<indirect>".to_string()),
            _ => None,
        })
        .collect();
    assert!(
        calls.is_empty(),
        "an aggregate callee edge must never be realized as a call under a token that \
         attested only the caller's own signature; emitted calls: {calls:?}"
    );

    let opaque = aggregate_forwarding_module(false);
    match lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check(
        &opaque,
        &opaque.functions[0],
        &token,
    ) {
        Err(ModuleLirError::UnsupportedInst { inst: "Call", .. }) => {}
        Err(other) => panic!(
            "a non-inlinable aggregate callee must be refused as an unsupported call, got: {other}"
        ),
        Ok(lir) => panic!(
            "a call whose aggregate argument no FnAbi classified was EMITTED: {:?}",
            lir.blocks
                .values()
                .flat_map(|block| block.instructions.iter())
                .map(|inst| format!("{:?}", inst.opcode))
                .collect::<Vec<_>>()
        ),
    }

    let opcodes = |lir: &trust_cg_lower::function::Function| -> Vec<String> {
        lir.blocks
            .values()
            .flat_map(|block| block.instructions.iter())
            .map(|inst| format!("{:?}", inst.opcode))
            .collect()
    };
    for shape in
        [IndirectShape::OpenConstArg, IndirectShape::OpenForwardedArg, IndirectShape::KnownTarget]
    {
        let module = indirect_edge_module(shape, true);
        match lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check(
            &module,
            &module.functions[0],
            &token,
        ) {
            Err(ModuleLirError::UnclassifiedAggregateAbi { detail, .. }) => assert!(
                detail.contains("an indirect call edge's declared signature passes parameter 0")
                    && detail.contains("OWN signature edge"),
                "{shape:?}: the refusal must name the indirect edge, its slot, and why the \
                 token does not place it, got: {detail}"
            ),
            Err(other) => panic!(
                "{shape:?}: an aggregate on an indirect call edge must be refused by the \
                 admission (`UnclassifiedAggregateAbi`), got a DIFFERENT refusal: {other}"
            ),
            Ok(lir) => panic!(
                "{shape:?}: an indirect call whose aggregate argument no FnAbi classified was \
                 EMITTED under a token that placed only the caller's own signature: {:?}",
                opcodes(&lir)
            ),
        }

        let scalar = indirect_edge_module(shape, false);
        let lir = lower_trust_ir_function_to_lir_real_calls_with_abi_cross_check(
            &scalar,
            &scalar.functions[0],
            &token,
        )
        .unwrap_or_else(|e| panic!("{shape:?}: the scalar twin must lower, got: {e}"));
        assert!(
            lir.blocks.values().flat_map(|block| block.instructions.iter()).any(|inst| matches!(
                inst.opcode,
                trust_cg_lower::instructions::Opcode::CallIndirect
            )),
            "{shape:?}: the scalar twin must lower to a real `CallIndirect`, got: {:?}",
            opcodes(&lir)
        );
    }
}

/// SCOPE. A module that pins NO target makes no `struct_passing` claim at all, so
/// it is not the declared-absence this gate is about. Pinned here so a later
/// widening to `target_info: None` is a deliberate, visible change rather than a
/// silent one.
#[test]
fn an_unpinned_target_is_out_of_this_gate_s_scope() {
    let module = pair_struct_module(None);
    assert!(
        lower_module_to_lir(&module, FuncId::new(0)).is_ok(),
        "an unpinned module is out of scope for the `unclassified` gate"
    );
}

/// THE CALLEE EDGE. The function being lowered is entirely scalar; the aggregate
/// crosses the edge to a callee it calls. That is still an ABI boundary this
/// lowering realizes, so it is still refused — and the refusal names the callee.
#[test]
fn an_aggregate_on_a_callee_edge_is_refused_and_names_the_callee() {
    let module = aggregate_callee_edge_module(Some(target(StructPassingPolicy::Unclassified)));

    let (detail, _) = refusal(
        lower_module_to_lir(&module, FuncId::new(0)),
        "an aggregate crossing a callee edge",
    );
    assert!(
        detail.contains("the call edge to `takes_range`"),
        "the refusal must name the callee whose edge carries the aggregate, got: {detail}"
    );
}

/// THE CARRIED FORM, which is what the F1 proven-output gate uses. The gate
/// EMITS the bytes the codegen unit ships, so it re-lowers and is itself a
/// codegen boundary; it stores the shipping path's
/// `Option<AbiPassModeCrossCheck>` on its `TrustIrGateSource` and passes it
/// here, so the gate is admitted on exactly the shipping path's evidence and a
/// gate source assembled WITHOUT evidence is refused just as the bare entry
/// point is.
#[test]
fn the_carried_form_admits_exactly_when_the_evidence_is_present() {
    let module = pair_struct_module(Some(target(StructPassingPolicy::Unclassified)));
    assert!(
        matches!(
            lower_module_to_lir_maybe_cross_checked(&module, FuncId::new(0), None),
            Err(ModuleLirError::UnclassifiedAggregateAbi { .. })
        ),
        "no carried evidence must refuse exactly as the bare entry point does"
    );
    let cross_check = AbiPassModeCrossCheck::attested_by("test");
    assert!(
        lower_module_to_lir_maybe_cross_checked(&module, FuncId::new(0), Some(&cross_check))
            .is_ok(),
        "carried evidence must admit exactly as the named entry point does"
    );
}

/// THE DRIVER'S EXACT SHAPE. `rustc_codegen_trust_cg`'s F1 frontend mints the
/// token on the success path of `validate_codegen_instance_abi_trust_ir`, hands
/// it to `lower_module_to_lir_with_abi_cross_check`, and then STORES it on the
/// `TrustIrGateSource` so the gate's re-lowerings carry the same evidence. This
/// pins that three-step shape here, where it compiles and runs without a
/// trust-cg-backend build.
#[cfg(feature = "ay-proofs")]
mod driver_shape {
    use trust_cg_bridge::AbiPassModeCrossCheck;
    use trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource;
    use trust_ir::StructPassingPolicy;
    use trust_ir::value::FuncId;

    use super::{pair_struct_module, target};

    #[test]
    fn the_f1_frontend_shape_lowers_and_carries_its_evidence_to_the_gate() {
        let mut module = pair_struct_module(Some(target(StructPassingPolicy::Unclassified)));
        let func_id = FuncId::new(0);
        // (1) minted where the ABI cross-check is earned.
        let abi_cross_check = AbiPassModeCrossCheck::attested_by(
            "rustc_codegen_trust_cg: validate_codegen_instance_abi_* over rustc's FnAbi PassMode \
             for this exact instance, immediately before lowering",
        );
        // (2) the shipping lowering, which the bare entry point would refuse.
        if let Some(function) = module.function_by_id_mut(func_id) {
            function.name = "_ZN4test1rE".to_string();
        }
        let lir = trust_cg_bridge::lower_module_to_lir_with_abi_cross_check(
            &module,
            func_id,
            &abi_cross_check,
        )
        .expect("the F1 lane's lowering must be admitted by its own cross-check");
        assert_eq!(lir.name, "_ZN4test1rE");
        // (3) the same evidence carried to the gate, which re-lowers and emits.
        let source = TrustIrGateSource {
            symbol: "_ZN4test1rE".to_string(),
            module: module.into(),
            func_id,
            abi_cross_check: Some(abi_cross_check),
        };
        let carried = source.abi_cross_check.as_ref().expect("evidence must reach the gate");
        assert!(
            trust_cg_bridge::lower_module_to_lir_maybe_cross_checked(
                &source.module,
                source.func_id,
                Some(carried),
            )
            .is_ok(),
            "the gate's re-lowering must be admitted on the shipping path's evidence"
        );
        assert!(
            matches!(
                trust_cg_bridge::lower_module_to_lir_maybe_cross_checked(
                    &source.module,
                    source.func_id,
                    None,
                ),
                Err(trust_cg_bridge::ModuleLirError::UnclassifiedAggregateAbi { .. })
            ),
            "and WITHOUT it the same gate source is refused by name"
        );
    }
}
