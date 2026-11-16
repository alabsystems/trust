// switch_case_encoding.rs — pins for the LIR `Switch` case-constant encoding.
//
// THE DEFECT (measured 2026-09-27 against the LLVM oracle, trustc
// 0cb693917, `-Zcodegen-backend=trust-cg`):
//
// * trust-ir frontend (`-Ztrust-cg-frontend=trust-ir`, `module_to_lir`):
//   `enum G { A = -3, B = 7 }` has an i8 tag, and `match g { G::A => 100,
//   G::B => 200 }` returned 200 for `G::A` — the emitted code zero-extended the
//   selector (`uxtb w1, w0` = 253) and compared it with the case constant
//   materialized from the SIGNED trust-ir value (`mov w0, #-3` = 0xFFFF_FFFD),
//   so the `A` arm was unreachable. Same for `repr(i8)`/`repr(i16)` negative
//   discriminants, `matches!`, `if let`, a plain `match !(x as i8) { -1 => ..
//   }`, a dense (jump-table) arm set, `u32` cases >= 2^31 in a binary-search
//   switch, and a 128-bit selector (compared on its low 64 bits only).
// * MIR lane (`lower.rs`): a 32-bit selector's MIR case `0xFFFF_FFFF` (a
//   `u32::MAX`, or MIR's spelling of `i32 -1`) went through as 4294967295; the
//   jump-table lowering sign-extends a 32-bit selector, so every such arm
//   routed to the default.
//
// Under the default STRICT output gate every one of those functions was
// refused (Refuted, or Unknown and fail-closed); under the explicit
// `-Ztrust-cg-output-gate=allow-unknown` opt-in they shipped wrong values.
//
// THE CONTRACT these pins hold the converters to is trust-cg-lower's own (its
// trust-ir adapter's `normalize_switch_case_value`): an 8/16-bit selector's
// case constant is its ZERO-extended pattern, a 32/64-bit selector's is its
// two's-complement value, and a 128-bit selector is refused. Every executing
// test links the emitted object against a C driver and checks each arm, and the
// trust-ir tests also check the expectations against the trust-ir reference
// interpreter, so a test cannot encode a wrong expectation of its own.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::process::Command;

use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::{ModuleLirError, lower_module_to_lir};
use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::types::Type as LirType;
use trust_ir::inst::{Inst, SwitchCase};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty as IrTy};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};
use trust_types::{
    BasicBlock, BlockId as VfBlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ---------------------------------------------------------------------------
// Shared: the LIR case list, native link + run.
// ---------------------------------------------------------------------------

fn switch_cases(lir: &LirFunction) -> Vec<i64> {
    let mut found = Vec::new();
    let mut blocks: Vec<_> = lir.blocks.iter().collect();
    blocks.sort_by_key(|(block, _)| block.0);
    for (_, block) in blocks {
        for inst in &block.instructions {
            if let Opcode::Switch { cases, .. } = &inst.opcode {
                found.extend(cases.iter().map(|(value, _)| *value));
            }
        }
    }
    found
}

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::host()
}

/// Link `object` with a C driver that calls `symbol(arg)` for every probe and
/// exits nonzero, naming the probe, on the first wrong answer.
fn link_and_run(object: &[u8], symbol: &str, c_arg_ty: &str, probes: &[(i128, u64)]) {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!("SKIP native execution: requires an aarch64-apple-darwin host");
        return;
    }
    let directory = tempfile::TempDir::new().expect("temporary link directory");
    let object_path = directory.path().join("switch.o");
    let driver_path = directory.path().join("driver.c");
    let executable_path = directory.path().join("switch");
    fs::write(&object_path, object).expect("write object");
    let mut checks = String::new();
    for (arg, expected) in probes {
        checks.push_str(&format!(
            "  if ({symbol}(({c_arg_ty})({arg}LL)) != UINT64_C({expected})) {{ \
               printf(\"{symbol}(%lld) = %llu, want {expected}\\n\", (long long)({arg}LL), \
               (unsigned long long){symbol}(({c_arg_ty})({arg}LL))); return 1; }}\n"
        ));
    }
    fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\n#include <stdio.h>\n\
             extern uint64_t {symbol}({c_arg_ty});\n\
             int main(void) {{\n{checks}  return 0;\n}}\n"
        ),
    )
    .expect("write C driver");
    let linked = Command::new("cc")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&executable_path)
        .output()
        .expect("invoke cc");
    assert!(
        linked.status.success(),
        "native link failed: {}",
        String::from_utf8_lossy(&linked.stderr)
    );
    let ran = Command::new(&executable_path).output().expect("run the linked switch");
    assert!(
        ran.status.success(),
        "the emitted switch dispatched wrongly: {}",
        String::from_utf8_lossy(&ran.stdout)
    );
}

// ---------------------------------------------------------------------------
// trust-ir lane (`lower_module_to_lir`).
//
//   bb0(x: T): switch x [c_0 -> bb1, ..., c_n -> bb(n+1)], default -> bb(n+2)
//   bb(i+1):   return v_i
//   bb(n+2):   return v_default
// ---------------------------------------------------------------------------

fn switch_module(name: &str, sel: IrTy, arms: &[(i128, u64)], default: u64) -> Module {
    let mut module = Module::new("switch_case_encoding");
    module.func_types.push(FuncTy {
        params: vec![sel.clone()],
        returns: vec![IrTy::U64],
        is_vararg: false,
        abi: None,
    });
    let mut function = IrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    let x = ValueId::new(0);
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((x, sel));
    let default_block = BlockId::new(arms.len() as u32 + 1);
    entry.body.push(InstrNode::new(Inst::Switch {
        value: x,
        default: default_block,
        default_args: vec![],
        cases: arms
            .iter()
            .enumerate()
            .map(|(i, (case, _))| SwitchCase {
                value: Constant::Int(*case),
                target: BlockId::new(i as u32 + 1),
                args: vec![],
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }));
    function.blocks.push(entry);
    let mut next_value = 1u32;
    let returns = arms.iter().map(|(_, value)| *value).chain(std::iter::once(default));
    for (i, value) in returns.enumerate() {
        let mut block = Block::new(BlockId::new(i as u32 + 1));
        let result = ValueId::new(next_value);
        next_value += 1;
        block.body.push(
            InstrNode::new(Inst::Const { ty: IrTy::U64, value: Constant::Int(i128::from(value)) })
                .with_result(result),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![result] }));
        function.blocks.push(block);
    }
    module.functions.push(function);
    module
}

/// The trust-ir reference interpreter's answer for `f(arg)`.
fn interpret(module: &Module, sel: &IrTy, arg: i128) -> u64 {
    let outcome = Interpreter::with_module(module)
        .execute_func(FuncId::new(0), vec![InterpretValue::int(sel.clone(), arg).expect("arg")])
        .expect("interpreter execute_func");
    outcome.returns[0].as_int().expect("integer return").as_unsigned() as u64
}

/// Lower, check the LIR case encoding, check the probes against the reference
/// interpreter, then emit, link and run every probe natively.
fn check_trust_ir_switch(
    name: &str,
    sel: IrTy,
    c_arg_ty: &str,
    arms: &[(i128, u64)],
    default: u64,
    expected_lir_cases: &[i64],
    probes: &[(i128, u64)],
) {
    let module = switch_module(name, sel.clone(), arms, default);
    for (arg, want) in probes {
        assert_eq!(interpret(&module, &sel, *arg), *want, "reference interpreter: {name}({arg})");
    }
    let lir = lower_module_to_lir(&module, FuncId::new(0)).expect("the switch must lower");
    assert_eq!(switch_cases(&lir), expected_lir_cases, "LIR case encoding for {name}");
    let object = backend().emit_object(&[lir]).expect("emit the switch object");
    link_and_run(&object, name, c_arg_ty, probes);
}

#[test]
fn trust_ir_i8_negative_cases_are_zero_extended_and_dispatch() {
    // The `enum G { A = -3, B = 7 }` tag switch, spelled on its i8 carrier.
    check_trust_ir_switch(
        "tir_switch_i8_neg",
        IrTy::I8,
        "int8_t",
        &[(-3, 100), (7, 200)],
        5,
        &[253, 7],
        &[(-3, 100), (7, 200), (0, 5), (3, 5), (-128, 5), (127, 5)],
    );
}

#[test]
fn trust_ir_i8_dense_negative_cases_dispatch_through_the_jump_table() {
    // Four dense arms select the jump-table strategy (`repr(i8)` A=-4..D=-1).
    check_trust_ir_switch(
        "tir_switch_i8_dense",
        IrTy::I8,
        "int8_t",
        &[(-4, 1), (-3, 2), (-2, 3), (-1, 4)],
        50,
        &[252, 253, 254, 255],
        &[(-4, 1), (-3, 2), (-2, 3), (-1, 4), (0, 50), (-5, 50), (4, 50)],
    );
}

#[test]
fn trust_ir_i16_negative_cases_are_zero_extended_and_dispatch() {
    // `#[repr(i16)] enum Q { A = -300, B = -1, C = 5 }`.
    check_trust_ir_switch(
        "tir_switch_i16_neg",
        IrTy::I16,
        "int16_t",
        &[(-300, 1), (-1, 2), (5, 3)],
        9,
        &[65236, 65535, 5],
        &[(-300, 1), (-1, 2), (5, 3), (0, 9), (300, 9), (-32768, 9)],
    );
}

#[test]
fn trust_ir_u32_high_cases_are_twos_complement_and_dispatch() {
    // Sparse (binary search) and dense (jump table) arm sets above 2^31.
    check_trust_ir_switch(
        "tir_switch_u32_sparse",
        IrTy::U32,
        "uint32_t",
        &[(0xFFFF_FFFF, 10), (0xFFFF_0000, 20), (5, 30), (0x8000_0000, 40), (0x7000_0000, 60)],
        50,
        &[-1, -65536, 5, -2_147_483_648, 0x7000_0000],
        &[
            (0xFFFF_FFFF, 10),
            (0xFFFF_0000, 20),
            (5, 30),
            (0x8000_0000, 40),
            (0x7000_0000, 60),
            (0xFFFF_FFFE, 50),
            (0, 50),
        ],
    );
    check_trust_ir_switch(
        "tir_switch_u32_dense",
        IrTy::U32,
        "uint32_t",
        &[(0xFFFF_FFFF, 10), (0xFFFF_FFFE, 20), (0xFFFF_FFFD, 30), (0xFFFF_FFFC, 40)],
        50,
        &[-1, -2, -3, -4],
        &[(0xFFFF_FFFF, 10), (0xFFFF_FFFE, 20), (0xFFFF_FFFD, 30), (0xFFFF_FFFC, 40), (0, 50)],
    );
}

#[test]
fn trust_ir_i32_negative_cases_keep_their_twos_complement_value() {
    // The 32-bit encoding was already right for SIGNED spellings; pin it.
    check_trust_ir_switch(
        "tir_switch_i32_neg",
        IrTy::I32,
        "int32_t",
        &[(-1, 10), (-2, 20), (-3, 30), (-4, 40)],
        50,
        &[-1, -2, -3, -4],
        &[(-1, 10), (-2, 20), (-3, 30), (-4, 40), (0, 50), (1, 50)],
    );
}

#[test]
fn trust_ir_128_bit_selector_is_refused_by_name() {
    // The LIR switch compares only the low 64 bits: `x | 2^64` matched case 1.
    let module = switch_module("tir_switch_u128", IrTy::U128, &[(1, 10), (2, 20)], 30);
    match lower_module_to_lir(&module, FuncId::new(0)) {
        Err(ModuleLirError::UnencodableSwitchCase { detail, .. }) => {
            assert!(detail.contains("128-bit selector"), "names the width: {detail}");
        }
        other => panic!("a 128-bit switch must be refused by name, got {other:?}"),
    }
}

#[test]
fn trust_ir_cases_that_collide_at_the_selector_width_are_refused() {
    // `-1` and `255` are one i8 selector value; which arm was meant is lost.
    let module = switch_module("tir_switch_i8_dup", IrTy::I8, &[(-1, 10), (255, 20)], 30);
    match lower_module_to_lir(&module, FuncId::new(0)) {
        Err(ModuleLirError::UnencodableSwitchCase { detail, .. }) => {
            assert!(detail.contains("same selector value"), "names the collision: {detail}");
        }
        other => panic!("colliding case constants must be refused, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// MIR lane (`lower.rs`): a `VerifiableFunction` with a multi-way `SwitchInt`.
// MIR spells every case as the zero-extended bit pattern at the discriminant's
// width.
// ---------------------------------------------------------------------------

fn mir_switch(name: &str, discr: Ty, arms: &[(u128, u64)], default: u64) -> VerifiableFunction {
    let ret = |value: u64, id: usize| BasicBlock {
        id: VfBlockId(id),
        stmts: vec![Statement::Assign {
            place: Place::local(0),
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(u128::from(value), 64))),
            span: SourceSpan::default(),
        }],
        terminator: Terminator::Return,
    };
    let mut blocks = vec![BasicBlock {
        id: VfBlockId(0),
        stmts: vec![],
        terminator: Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(1)),
            targets: arms
                .iter()
                .enumerate()
                .map(|(i, (case, _))| (*case, VfBlockId(i + 1)))
                .collect(),
            otherwise: VfBlockId(arms.len() + 1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    }];
    for (i, (_, value)) in arms.iter().enumerate() {
        blocks.push(ret(*value, i + 1));
    }
    blocks.push(ret(default, arms.len() + 1));
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("switch_case_encoding::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: discr, name: Some("x".into()) },
            ],
            blocks,
            arg_count: 1,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn check_mir_switch(
    name: &str,
    discr: Ty,
    c_arg_ty: &str,
    arms: &[(u128, u64)],
    default: u64,
    expected_lir_cases: &[i64],
    probes: &[(i128, u64)],
) {
    let function = mir_switch(name, discr, arms, default);
    let lir = backend().lower_function(&function).expect("the SwitchInt must lower");
    assert_eq!(switch_cases(&lir), expected_lir_cases, "LIR case encoding for {name}");
    let object = backend().emit_object(&[lir]).expect("emit the switch object");
    link_and_run(&object, name, c_arg_ty, probes);
}

#[test]
fn mir_u32_high_dense_switchint_is_twos_complement_and_dispatches() {
    // `match !(x as u32) { 0xFFFF_FFFF => 10, .. }` — was 50 on every arm.
    check_mir_switch(
        "mir_switch_u32_dense",
        Ty::u32(),
        "uint32_t",
        &[(0xFFFF_FFFF, 10), (0xFFFF_FFFE, 20), (0xFFFF_FFFD, 30), (0xFFFF_FFFC, 40)],
        50,
        &[-1, -2, -3, -4],
        &[(0xFFFF_FFFF, 10), (0xFFFF_FFFE, 20), (0xFFFF_FFFD, 30), (0xFFFF_FFFC, 40), (7, 50)],
    );
}

#[test]
fn mir_i32_negative_dense_switchint_dispatches() {
    // `match !(x as i32) { -1 => 10, -2 => 20, -3 => 30, -4 => 40, _ => 50 }`:
    // MIR carries -1 as 0xFFFF_FFFF.
    check_mir_switch(
        "mir_switch_i32_dense",
        Ty::i32(),
        "int32_t",
        &[(0xFFFF_FFFF, 10), (0xFFFF_FFFE, 20), (0xFFFF_FFFD, 30), (0xFFFF_FFFC, 40)],
        50,
        &[-1, -2, -3, -4],
        &[(-1, 10), (-2, 20), (-3, 30), (-4, 40), (0, 50)],
    );
}

#[test]
fn mir_i8_negative_switchint_keeps_zero_extended_cases() {
    // Already right (MIR's pattern IS the zero-extended one); pin it so the
    // shared encoder cannot regress the narrow MIR lane.
    check_mir_switch(
        "mir_switch_i8_dense",
        Ty::i8(),
        "int8_t",
        &[(255, 10), (254, 20), (253, 30), (252, 40)],
        50,
        &[255, 254, 253, 252],
        &[(-1, 10), (-2, 20), (-3, 30), (-4, 40), (0, 50), (4, 50)],
    );
}

// ---------------------------------------------------------------------------
// MIR lane, ONE label (`if let`, `match x { c => .., _ => .. }`): lowered as
// `Icmp eq` + `Brif`, not a `Switch`. Trust (ticket 216 cg-bridge): the case
// constant was an `I64` of `label as i64` whatever the selector. Measured on
// 50b0bfe77a (aarch64-apple-darwin): an i32/u32 selector against any label
// above 4095 (`0xFFFF_FFFF`, 70000, `0x8000_0000`) was REFUSED by the encoder
// ("CMP register widths must agree": a W register against an X register), and a
// 128-bit label was truncated to its low 64 bits in the LIR (`2^64` became
// `Iconst 0`), refused only because ISel then failed on the mixed widths. It is
// now encoded as the multi-way arm encodes it and materialized at the
// selector's own type.
// ---------------------------------------------------------------------------

/// The one `Iconst` the single-label compare materializes (the only one in
/// block 0; the arms' return constants live in their own blocks).
fn single_label_constant(lir: &LirFunction) -> (LirType, i64) {
    let entry = lir.blocks.iter().find(|(block, _)| block.0 == 0).expect("entry block").1;
    assert!(
        entry.instructions.iter().any(|i| matches!(i.opcode, Opcode::Brif { .. })),
        "a single label lowers to Icmp + Brif, not a Switch"
    );
    let constants: Vec<(LirType, i64)> = entry
        .instructions
        .iter()
        .filter_map(|i| match &i.opcode {
            Opcode::Iconst { ty, imm } => Some((ty.clone(), *imm)),
            _ => None,
        })
        .collect();
    assert_eq!(constants.len(), 1, "one case constant in the entry block: {constants:?}");
    constants[0].clone()
}

fn check_mir_single_label(
    name: &str,
    discr: Ty,
    c_arg_ty: &str,
    label: u128,
    expected_constant: (LirType, i64),
    probes: &[(i128, u64)],
) {
    let function = mir_switch(name, discr, &[(label, 10)], 50);
    let lir = backend().lower_function(&function).expect("the single-label SwitchInt must lower");
    assert_eq!(single_label_constant(&lir), expected_constant, "case constant for {name}");
    let object = backend().emit_object(&[lir]).expect("emit the single-label object");
    link_and_run(&object, name, c_arg_ty, probes);
}

#[test]
fn mir_single_label_i32_negative_label_dispatches() {
    // `match x { -1 => 10, _ => 50 }` on i32: MIR's label is 0xFFFF_FFFF.
    check_mir_single_label(
        "mir_single_i32_m1",
        Ty::i32(),
        "int32_t",
        0xFFFF_FFFF,
        (LirType::I32, -1),
        &[(-1, 10), (0, 50), (1, 50), (0x7FFF_FFFF, 50), (-2, 50)],
    );
    // Above the 12-bit compare immediate: materialized, compared at W width.
    check_mir_single_label(
        "mir_single_i32_70000",
        Ty::i32(),
        "int32_t",
        70000,
        (LirType::I32, 70000),
        &[(70000, 10), (0, 50), (-70000, 50), (70001, 50)],
    );
}

#[test]
fn mir_single_label_u32_high_labels_dispatch() {
    check_mir_single_label(
        "mir_single_u32_max",
        Ty::u32(),
        "uint32_t",
        0xFFFF_FFFF,
        (LirType::I32, -1),
        &[(0xFFFF_FFFF, 10), (0, 50), (0x7FFF_FFFF, 50), (0xFFFF_FFFE, 50)],
    );
    check_mir_single_label(
        "mir_single_u32_2p31",
        Ty::u32(),
        "uint32_t",
        0x8000_0000,
        (LirType::I32, -0x8000_0000),
        &[(0x8000_0000, 10), (0, 50), (0x7FFF_FFFF, 50)],
    );
}

#[test]
fn mir_single_label_narrow_and_64_bit_selectors_stay_right() {
    // These dispatched on 50b0bfe77a too (ISel zero-extends a narrow compare's
    // operands; a 64-bit selector matched its I64 constant). Pin them at their
    // new constant types.
    check_mir_single_label(
        "mir_single_i8_m1",
        Ty::i8(),
        "int8_t",
        255,
        (LirType::I8, 255),
        &[(-1, 10), (0, 50), (127, 50), (-128, 50)],
    );
    check_mir_single_label(
        "mir_single_u8_200",
        Ty::u8(),
        "uint8_t",
        200,
        (LirType::I8, 200),
        &[(200, 10), (0, 50), (72, 50)],
    );
    check_mir_single_label(
        "mir_single_i16_m1",
        Ty::i16(),
        "int16_t",
        0xFFFF,
        (LirType::I16, 0xFFFF),
        &[(-1, 10), (0, 50), (0x7FFF, 50)],
    );
    check_mir_single_label(
        "mir_single_i64_m1",
        Ty::i64(),
        "int64_t",
        u128::from(u64::MAX),
        (LirType::I64, -1),
        &[(-1, 10), (0, 50), (0xFFFF_FFFF, 50)],
    );
}

#[test]
fn mir_single_label_128_bit_selector_is_refused_by_name() {
    // `match x { 2^64 => .., _ => .. }` on u128/i128: the label has no i64
    // spelling. It was truncated to `Iconst I64 0` in the LIR, a compare `x == 0`
    // (the object was refused only later, by ISel's mixed-width failure).
    for (name, ty) in [("mir_single_u128", Ty::u128()), ("mir_single_i128", Ty::i128())] {
        let function = mir_switch(name, ty, &[(1u128 << 64, 10)], 50);
        match backend().lower_function(&function) {
            Err(e) => {
                let e = format!("{e:?}");
                assert!(e.contains("SwitchInt") && e.contains("128-bit selector"), "{name}: {e}");
            }
            Ok(lir) => panic!("{name}: a 128-bit single-label switch must be refused, got {lir:?}"),
        }
    }
}
