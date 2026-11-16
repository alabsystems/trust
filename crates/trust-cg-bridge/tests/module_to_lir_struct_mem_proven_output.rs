// module_to_lir_struct_mem_proven_output.rs — the "trust-ir first" codegen seam,
// extended to N-FIELD `Ty::Struct` IN MEMORY (a scalar-field struct round-tripped
// through ONE stack slot AS A UNIT), proven over the real emitted bytes.
//
// This is the DOMINANT real-backend aggregate: the trust-ir bridge emits
// `Ty::Struct(sid)` for EVERY Rust struct/ADT/closure-env (see
// `crates/trust-ir-bridge/src/lower.rs` `map_type_ctx` Adt/Closure arms), with a
// `StructDef { fields: Vec<FieldDef>, repr: Rust }` in `Module.structs`. A struct
// local promoted across blocks (`promote_local_to_memory`) round-trips through a
// whole-aggregate stack slot with the tuple slice's shape, only the type is
// `Ty::Struct(sid)` (see `module_to_lir_aggregate_mem_proven_output.rs`, whose
// TEST 9 pins the bridge's promoted tuple). Since BMC-LANE-1 (2026-11-06) the
// bridge spells a complete struct construction as ONE `make_aggregate struct.0
// [a, b]` (pinned in trust-ir-bridge's `physical_struct_construction_tests.rs`);
// before it, the construction was an `undef struct.0` seed under one
// `insertfield` per field. This file builds both spellings of the stored value
// by hand (`StructBase`), in one block:
//
//   bb0(a, b):
//     %u  = undef struct.0                  ; UndefSeed: the legacy base
//     %t0 = insertfield struct.0 %u,  0, a  ; field x <- a
//     %t  = insertfield struct.0 %t0, 1, b  ; field y <- b   (full SSA aggregate)
//       -- or, Constructor (the bridge's spelling since BMC-LANE-1) --
//     %t  = make_aggregate struct.0 [a, b]  ; no seed, no insertfield
//     %s  = alloca struct.0                 ; AGGREGATE stack slot
//     store struct.0 %t -> *%s              ; WHOLE-aggregate store
//     %ld = load  struct.0 *%s              ; WHOLE-aggregate load
//     %f0 = extractfield i32 %ld, 0
//     %f1 = extractfield i32 %ld, 1
//     %r  = add %f0, %f1                     ; a + b
//     return %r
//
// The converter (PASS 1.7, `analyze_aggregate_memory` + `lower_aggregate_inst`)
// THREADS the Module's struct table: it resolves `Ty::Struct(sid) ->
// module.struct_def(sid) -> def.fields` and lays the fields out with the C-style
// `aggregate_mem_layout`, BYTE-FOR-BYTE the interpreter's `struct_layout`
// (`first-party/trust-ir/.../interpret.rs`), which reads the SAME `def.fields`.
// The whole-aggregate Store/Load decompose into PER-FIELD Str/Ldr at the field
// OFFSETS (2-field: x@0, y@4 in an 8-byte/align-4 slot; 3-field: x@0, y@4, z@8 in
// a 12-byte/align-4 slot). We feed the produced LIR into the EXISTING verified
// `TrustCgCodegenBackend::emit_object` emitter and prove the emitted machine bytes
// compute the field-derived result for ALL inputs:
//
//   (1) PROVEN-OUTPUT (infinite domain): the emitted bytes are decoded into
//       machine effects (NOT reconstructed from the IR), the field Str/Ldr become
//       array-theory Store/Select over the symbolic MEM, merged into a symbolic
//       output Formula; ay (QF_ABV) proves that Formula equals the field sum for
//       ALL 2^32 x ... inputs (UNSAT of the negation).
//   (2) NEGATIVE CONTROL: the SAME bytes proven against a `+1` / wrong-offset spec
//       MUST be SAT — otherwise the discharge is vacuous.
//   (3) Str/Ldr-AT-OFFSETS: the produced LIR must carry exactly N field Stores and
//       N field Loads, addressed at the correct C-style offsets, and the emitted
//       __text must contain real Str AND Ldr.
//   (4) VALUE-DIFFERENTIAL (layout agreement): the trust-ir reference INTERPRETER
//       round-trips a `Ty::Struct`-in-memory value through the SAME `struct_layout`
//       (computed from `def.fields`) that `aggregate_mem_layout` reproduces. The
//       interpreter faults on the `Undef` seed and has no
//       `(Ty::Struct, Constant::Aggregate)` constant arm (probed at c58fa68), so
//       the seed spelling of the whole-`Store(struct)`/`Load(struct)` round trip
//       is not interpreter-executable; the stand-in for it fills the slot via
//       typed field Stores through byte-offset GEPs, then reads the WHOLE struct
//       back with a single `Load(struct)` — exercising the SAME `struct_layout` +
//       `decode_value` offset math (x@0, y@4[, z@8]) the converter's emitted
//       bytes are proven against. The constructor spelling IS executable, so
//       TESTS 9-11 run the interpreter and the emitted bytes on the SAME module,
//       including a mixed-width `{u8, i32}` struct (u8@0, i32@4).
//   (5) DECLARED LAYOUTS (TESTS 12-17, CG-DECLARED-LAYOUT-1): every struct in
//       (1)-(4) declares no layout, the one case in which the interpreter's
//       layout IS declaration order, so (4) agrees there by construction. TESTS
//       12-17 build what the producer builds — structs with a declared
//       size/align/`FieldDef::offset` triple and tuples with a
//       `Module::tuple_layouts` descriptor, reordered as rustc reorders them —
//       and check the LIR offsets and the emitted bytes' field placement against
//       the interpreter's own slot image of the same type.
//
// A wrong struct lowering (wrong field offset, swapped fields, dropped store, wrong
// width, mis-resolved StructDef) makes ay return a COUNTEREXAMPLE rather than
// silently passing — demonstrated by the mandatory SAT negative controls and the
// field-offset Str/Ldr assertions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(feature = "ay-proofs")]

use ay::{BigInt, Logic, Solver, Term};
use trust_cg_bridge::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use trust_cg_bridge::lower_trust_ir_function_to_lir;
use trust_cg_lower::instructions::Opcode as LirOpcode;
use trust_disasm::{Opcode, decode_aarch64};
use trust_ir::inst::{BinOp, CastOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FieldDef, FuncTy, StructDef, StructRepr, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, StructId, ValueId};
use trust_ir::{
    Block, Constant, Endianness, Function as IrFunction, Module, StructPassingPolicy, TargetInfo,
    TupleLayoutDescriptor,
};
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
use trust_types::{Formula, Sort};

// ---------------------------------------------------------------------------
// Build the struct-in-memory Module for the whole-aggregate round-trip shape:
// the stored struct value (`StructBase`) + Alloca(struct) + whole Store(struct)
// + whole Load(struct) + per-field ExtractField + field sum.
//
// `field_tys` are the struct's scalar field types in declaration order (2 or 3).
// The function sums ALL fields as i32: field0 + field1 [+ field2], each field
// narrower than 32 bits widened first (`ZExt` if unsigned, `SExt` if signed).
// ---------------------------------------------------------------------------

/// How the stored struct value is spelled.
#[derive(Clone, Copy, Debug)]
enum StructBase {
    /// `undef struct.0` under one `insertfield` per field: the bridge's spelling
    /// before BMC-LANE-1. The interpreter faults on the seed.
    UndefSeed,
    /// One `make_aggregate struct.0 [p0, p1, ..]`, no seed and no `insertfield`:
    /// the bridge's spelling of a complete construction since BMC-LANE-1. The
    /// interpreter executes it.
    Constructor,
}

/// The cast that widens a field of type `ty` to the i32 sum, if it is narrower.
fn widen_to_i32(ty: &Ty) -> Option<CastOp> {
    match ty {
        Ty::I32 | Ty::U32 => None,
        Ty::U8 | Ty::U16 | Ty::Bool => Some(CastOp::ZExt),
        Ty::I8 | Ty::I16 => Some(CastOp::SExt),
        other => panic!("the field-sum fixture does not cover a {other:?} field"),
    }
}

fn make_struct_sum_module(field_tys: &[Ty]) -> Module {
    make_struct_sum_module_spelled(field_tys, StructBase::UndefSeed)
}

fn make_struct_sum_module_spelled(field_tys: &[Ty], spelling: StructBase) -> Module {
    let n = field_tys.len();
    assert!(n == 2 || n == 3, "test covers 2- and 3-field structs");
    let mut module = Module::new("struct_mem_module");
    module.func_types.push(FuncTy {
        params: field_tys.to_vec(),
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: None,
    });
    // Register the StructDef in the module table EXACTLY as the bridge does:
    // Vec<FieldDef> each with offset None, size/align None, repr Rust.
    let sid = StructId::new(0);
    let fields: Vec<FieldDef> = field_tys
        .iter()
        .enumerate()
        .map(|(i, ty)| FieldDef { name: format!("f{i}"), ty: ty.clone(), offset: None })
        .collect();
    module.add_struct(StructDef {
        id: sid,
        name: "P".into(),
        fields,
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let sty = Ty::Struct(sid);

    let mut function = IrFunction::new(FuncId::new(0), "ss", FuncTyId::new(0), BlockId::new(0));

    // Dense ValueId allocation.
    let mut next = 0u32;
    let mut nv = || {
        let v = ValueId::new(next);
        next += 1;
        v
    };
    let params: Vec<ValueId> = (0..n).map(|_| nv()).collect();
    let base = nv();
    // n InsertField results.
    let inserts: Vec<ValueId> = (0..n).map(|_| nv()).collect();
    let slot = nv();
    let ld = nv();
    let extracts: Vec<ValueId> = (0..n).map(|_| nv()).collect();
    // n-1 add results.
    let adds: Vec<ValueId> = (0..(n - 1)).map(|_| nv()).collect();

    let mut bb0 = Block::new(BlockId::new(0));
    for (p, ty) in params.iter().zip(field_tys) {
        bb0.params.push((*p, ty.clone()));
    }

    let cur = match spelling {
        StructBase::UndefSeed => {
            // undef struct.0 (the legacy bridge base: since BMC-LANE-1 the bridge
            // emits `MakeAggregate` for a complete struct; the interpreter traps on
            // the seed, so this is the LOWERING + PROVEN-OUTPUT shape).
            bb0.body.push(InstrNode::new(Inst::Undef { ty: sty.clone() }).with_result(base));

            // Chain InsertFields: field k <- param k.
            let mut cur = base;
            for (k, ins) in inserts.iter().enumerate() {
                bb0.body.push(
                    InstrNode::new(Inst::InsertField {
                        ty: sty.clone(),
                        aggregate: cur,
                        field: k as u32,
                        value: params[k],
                    })
                    .with_result(*ins),
                );
                cur = *ins;
            }
            cur
        }
        StructBase::Constructor => {
            // make_aggregate struct.0 [p0, p1, ..] (the `inserts` ids stay unused).
            bb0.body.push(
                InstrNode::new(Inst::MakeAggregate {
                    ty: sty.clone(),
                    variant: None,
                    fields: params.clone(),
                })
                .with_result(base),
            );
            base
        }
    };

    // alloca struct.0 ; store struct.0 %cur -> *%slot ; load struct.0 *%slot.
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: sty.clone(), count: None, align: None })
            .with_result(slot),
    );
    bb0.body.push(InstrNode::new(Inst::Store {
        ty: sty.clone(),
        ptr: slot,
        value: cur,
        volatile: false,
        align: None,
    }));
    bb0.body.push(
        InstrNode::new(Inst::Load { ty: sty.clone(), ptr: slot, volatile: false, align: None })
            .with_result(ld),
    );

    // extractfield i32 %ld, k for each field.
    for (k, ex) in extracts.iter().enumerate() {
        bb0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: field_tys[k].clone(),
                aggregate: ld,
                field: k as u32,
            })
            .with_result(*ex),
        );
    }

    // Widen each field narrower than i32 (none for an all-i32 struct, whose
    // module is unchanged by this step).
    let summands: Vec<ValueId> = extracts
        .iter()
        .zip(field_tys)
        .map(|(ex, ty)| match widen_to_i32(ty) {
            None => *ex,
            Some(op) => {
                let wide = nv();
                bb0.body.push(
                    InstrNode::new(Inst::Cast {
                        op,
                        src_ty: ty.clone(),
                        dst_ty: Ty::I32,
                        operand: *ex,
                    })
                    .with_result(wide),
                );
                wide
            }
        })
        .collect();

    // Sum: acc = f0 + f1 [+ f2].
    let mut acc = summands[0];
    for (i, add) in adds.iter().enumerate() {
        bb0.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: acc,
                rhs: summands[i + 1],
            })
            .with_result(*add),
        );
        acc = *add;
    }
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![acc] }));

    function.blocks.push(bb0);
    module.functions.push(function);
    module
}

// A Module that fills a struct slot via typed field Stores through byte-offset
// GEPs (x@0, y@4[, z@8]), then a WHOLE `Load(struct)` -> Aggregate, ExtractField
// each, and sums them. This IS interpreter-executable (unlike the whole-Store
// shape above), so it is the value-differential stand-in that proves the
// interpreter's `struct_layout`/`decode_value` offsets match the converter's.
fn make_struct_gep_fill_module(field_tys: &[Ty]) -> Module {
    let n = field_tys.len();
    let mut module = Module::new("struct_gep_fill");
    module.func_types.push(FuncTy {
        params: field_tys.to_vec(),
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: None,
    });
    let sid = StructId::new(0);
    let fields: Vec<FieldDef> = field_tys
        .iter()
        .enumerate()
        .map(|(i, ty)| FieldDef { name: format!("f{i}"), ty: ty.clone(), offset: None })
        .collect();
    module.add_struct(StructDef {
        id: sid,
        name: "P".into(),
        fields,
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    let sty = Ty::Struct(sid);

    let mut function = IrFunction::new(FuncId::new(0), "ss", FuncTyId::new(0), BlockId::new(0));
    let mut next = 0u32;
    let mut nv = || {
        let v = ValueId::new(next);
        next += 1;
        v
    };
    let params: Vec<ValueId> = (0..n).map(|_| nv()).collect();
    let slot = nv();

    let mut bb0 = Block::new(BlockId::new(0));
    for (p, ty) in params.iter().zip(field_tys) {
        bb0.params.push((*p, ty.clone()));
    }
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: sty.clone(), count: None, align: None })
            .with_result(slot),
    );
    // For an all-i32 struct, field k is at byte offset 4*k.
    for k in 0..n {
        let off = nv();
        let gep = nv();
        bb0.body.push(
            InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int((4 * k) as i128) })
                .with_result(off),
        );
        bb0.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I8,
                base: slot,
                indices: vec![off],
                inbounds: true,
            })
            .with_result(gep),
        );
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: gep,
            value: params[k],
            volatile: false,
            align: None,
        }));
    }
    // Whole-struct Load -> Aggregate, ExtractField each, sum.
    let ld = nv();
    bb0.body.push(
        InstrNode::new(Inst::Load { ty: sty.clone(), ptr: slot, volatile: false, align: None })
            .with_result(ld),
    );
    let extracts: Vec<ValueId> = (0..n).map(|_| nv()).collect();
    for (k, ex) in extracts.iter().enumerate() {
        bb0.body.push(
            InstrNode::new(Inst::ExtractField {
                ty: field_tys[k].clone(),
                aggregate: ld,
                field: k as u32,
            })
            .with_result(*ex),
        );
    }
    let mut acc = extracts[0];
    for i in 0..(n - 1) {
        let add = nv();
        bb0.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: acc,
                rhs: extracts[i + 1],
            })
            .with_result(add),
        );
        acc = add;
    }
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    function.blocks.push(bb0);
    module.functions.push(function);
    module
}

// ---------------------------------------------------------------------------
// Emit the Module-derived LIR to an object and extract __text.
// ---------------------------------------------------------------------------

fn host_triple() -> String {
    if cfg!(target_vendor = "apple") {
        if cfg!(target_arch = "aarch64") {
            "aarch64-apple-darwin".to_string()
        } else {
            "x86_64-apple-darwin".to_string()
        }
    } else {
        TrustCgTargetArch::host().triple().to_string()
    }
}

fn emit_module_text(module: &Module) -> (Vec<u8>, u64) {
    let function = &module.functions[0];
    let lir = lower_trust_ir_function_to_lir(module, function)
        .expect("lower_module_to_lir failed for struct-in-memory sum");
    let triple = host_triple();
    let backend = TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), triple);
    let obj = backend.emit_object(&[lir]).expect("emit_object failed");
    macho_text(&obj).expect("could not extract __text section from emitted object")
}

fn macho_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };
    if rd_u32(0)? != 0xfeed_facf {
        return None;
    }
    let ncmds = rd_u32(16)?;
    let mut cmd_off = 32usize;
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off)?;
        let cmdsize = rd_u32(cmd_off + 4)? as usize;
        if cmd == 0x19 {
            let nsects = rd_u32(cmd_off + 64)?;
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                let sname = &obj[sec..sec + 16];
                if sname.starts_with(b"__text\0") {
                    let addr = rd_u64(sec + 32)?;
                    let size = rd_u64(sec + 40)? as usize;
                    let offset = rd_u32(sec + 48)? as usize;
                    return Some((obj.get(offset..offset + size)?.to_vec(), addr));
                }
                sec += 80;
            }
        }
        cmd_off += cmdsize;
    }
    None
}

/// Count single-register `Str` / `Ldr` opcodes (excluding the `Stp`/`Ldp` frame
/// pair ops).
fn count_single_ldr_str(code: &[u8], base: u64) -> (usize, usize) {
    let mut strs = 0usize;
    let mut ldrs = 0usize;
    let mut pc = base;
    while (pc - base) as usize + 4 <= code.len() {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        if let Ok(insn) = decode_aarch64(&bytes, pc) {
            match insn.opcode {
                Opcode::Str | Opcode::Strb | Opcode::Strh => strs += 1,
                Opcode::Ldr
                | Opcode::Ldrb
                | Opcode::Ldrh
                | Opcode::Ldrsb
                | Opcode::Ldrsh
                | Opcode::Ldrsw => ldrs += 1,
                _ => {}
            }
        }
        pc += 4;
    }
    (strs, ldrs)
}

// ===========================================================================
// SYMBOLIC EXECUTOR (straight-line; mirrors the tuple/aggregate proven-output).
// ===========================================================================

fn symbolic_machine_output(code: &[u8], base: u64) -> Formula {
    machine_output_from(code, base, MachineState::symbolic())
}

/// The emitted bytes run with argument register X_k holding the CONCRETE
/// `args[k]` (zero-extended from its own width); the stack pointer and memory
/// stay symbolic, so the output still needs the solver.
fn concrete_machine_output(code: &[u8], base: u64, field_tys: &[Ty], args: &[i128]) -> Formula {
    let mut state = MachineState::symbolic();
    for (k, (ty, arg)) in field_tys.iter().zip(args).enumerate() {
        let mask = (1i128 << field_width(ty)) - 1;
        state.gpr[k] = Formula::BitVec { value: arg & mask, width: 64 };
    }
    machine_output_from(code, base, state)
}

fn machine_output_from(code: &[u8], base: u64, mut state: MachineState) -> Formula {
    let sem = Aarch64Semantics;
    let mut pc = base;
    let mut steps = 0u32;

    loop {
        let off = (pc - base) as usize;
        if off + 4 > code.len() {
            panic!("ran past end of __text without hitting RET");
        }
        let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");
        let is_ret = insn.opcode == Opcode::Ret;

        let effects = sem
            .effects(&state, &insn)
            .unwrap_or_else(|e| panic!("Aarch64Semantics::effects failed at {pc:#x}: {e:?}"));
        state.apply_effects(&effects).unwrap_or_else(|e| {
            panic!(
                "apply_effects rejected an effect from emitted insn {:?} at {:#x}: {:?}",
                insn.opcode, pc, e
            )
        });

        steps += 1;
        if is_ret {
            break;
        }
        pc += 4;
        assert!(steps < 1000, "decode loop runaway (no RET)");
    }

    state.read_gpr(0, 32)
}

// ---------------------------------------------------------------------------
// Formula -> ay::Term translation (QF_ABV).
// ---------------------------------------------------------------------------

fn var_term(solver: &mut Solver, name: &str, sort: &Sort) -> Term {
    match sort {
        Sort::BitVec(w) => solver.bv_var(name, *w),
        Sort::Bool => solver.bool_var(name),
        Sort::Array(idx, elem) => {
            let (Sort::BitVec(iw), Sort::BitVec(ew)) = (idx.as_ref(), elem.as_ref()) else {
                panic!("unsupported array sort for Var {name}: {sort:?}");
            };
            solver
                .declare_const(name, ay::Sort::array(ay::Sort::bitvec(*iw), ay::Sort::bitvec(*ew)))
        }
        other => panic!("unexpected Var sort in machine output for {name}: {other:?}"),
    }
}

fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => var_term(solver, name, sort),
        Formula::Bool(b) => solver.bool_const(*b),
        Formula::BitVec { value, width } => {
            solver.try_bv_const_bigint(&BigInt::from(*value), *width).expect("bv const")
        }
        Formula::BvAdd(a, b, _) => bin2(solver, a, b, Solver::try_bvadd),
        Formula::BvSub(a, b, _) => bin2(solver, a, b, Solver::try_bvsub),
        Formula::BvMul(a, b, _) => bin2(solver, a, b, Solver::try_bvmul),
        Formula::BvAnd(a, b, _) => bin2(solver, a, b, Solver::try_bvand),
        Formula::BvOr(a, b, _) => bin2(solver, a, b, Solver::try_bvor),
        Formula::BvXor(a, b, _) => bin2(solver, a, b, Solver::try_bvxor),
        Formula::BvShl(a, b, _) => bin2(solver, a, b, Solver::try_bvshl),
        Formula::BvLShr(a, b, _) => bin2(solver, a, b, Solver::try_bvlshr),
        Formula::BvAShr(a, b, _) => bin2(solver, a, b, Solver::try_bvashr),
        Formula::BvConcat(a, b) => bin2(solver, a, b, Solver::try_bvconcat),
        Formula::BvNot(a, _) => {
            let a = formula_to_term(solver, a);
            solver.try_bvnot(a).expect("bvnot")
        }
        Formula::BvZeroExt(a, bits) => {
            let a = formula_to_term(solver, a);
            solver.try_bvzeroext(a, *bits).expect("bvzeroext")
        }
        Formula::BvSignExt(a, bits) => {
            let a = formula_to_term(solver, a);
            solver.try_bvsignext(a, *bits).expect("bvsignext")
        }
        Formula::BvExtract { inner, high, low } => {
            let inner = formula_to_term(solver, inner);
            solver.try_bvextract(inner, *high, *low).expect("bvextract")
        }
        Formula::BvULt(a, b, _) => bin2(solver, a, b, Solver::try_bvult),
        Formula::BvULe(a, b, _) => bin2(solver, a, b, Solver::try_bvule),
        Formula::BvSLt(a, b, _) => bin2(solver, a, b, Solver::try_bvslt),
        Formula::BvSLe(a, b, _) => bin2(solver, a, b, Solver::try_bvsle),
        Formula::Eq(a, b) => bin2(solver, a, b, Solver::try_eq),
        Formula::Not(a) => {
            let a = formula_to_term(solver, a);
            solver.try_not(a).expect("not")
        }
        Formula::And(terms) => {
            let ts: Vec<Term> = terms.iter().map(|t| formula_to_term(solver, t)).collect();
            solver.try_and_many(&ts).expect("and")
        }
        Formula::Or(terms) => {
            let ts: Vec<Term> = terms.iter().map(|t| formula_to_term(solver, t)).collect();
            solver.try_or_many(&ts).expect("or")
        }
        Formula::Ite(cond, then_v, else_v) => {
            let c = formula_to_term(solver, cond);
            let t = formula_to_term(solver, then_v);
            let e = formula_to_term(solver, else_v);
            solver.try_ite(c, t, e).expect("ite")
        }
        Formula::Select(arr, idx) => {
            let a = formula_to_term(solver, arr);
            let i = formula_to_term(solver, idx);
            solver.try_select(a, i).expect("select")
        }
        Formula::Store(arr, idx, val) => {
            let a = formula_to_term(solver, arr);
            let i = formula_to_term(solver, idx);
            let v = formula_to_term(solver, val);
            solver.try_store(a, i, v).expect("store")
        }
        other => panic!("formula_to_term: unhandled Formula variant in machine output: {other:?}"),
    }
}

fn bin2(
    solver: &mut Solver,
    a: &Formula,
    b: &Formula,
    op: fn(&mut Solver, Term, Term) -> Result<Term, ay::SolverError>,
) -> Term {
    let a = formula_to_term(solver, a);
    let b = formula_to_term(solver, b);
    op(solver, a, b).expect("binary op")
}

/// UNSAT of the negation == proven-equal over ALL inputs.
fn discharge_equal(machine_out: &Formula, ir_out: &Formula) -> bool {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("ay Solver::try_new");
    let lhs = formula_to_term(&mut solver, machine_out);
    let rhs = formula_to_term(&mut solver, ir_out);
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    solver.try_assert_term(differ).expect("assert");
    let result = solver.check_sat();
    if result.is_unsat() {
        true
    } else if result.is_sat() {
        false
    } else {
        panic!("ay returned unknown: {result:?}");
    }
}

// ---------------------------------------------------------------------------
// IR-spec helpers. W_n = low 32 bits of argument register X_n.
// ---------------------------------------------------------------------------

fn wn(n: u32) -> Formula {
    Formula::BvExtract {
        inner: Box::new(Formula::Var(format!("X{n}"), Sort::BitVec(64))),
        high: 31,
        low: 0,
    }
}

fn bv32(value: i128) -> Formula {
    Formula::BitVec { value, width: 32 }
}

/// f0 + f1 [+ f2] spec (2- or 3-field field sum).
fn field_sum_spec(n: usize) -> Formula {
    let mut acc = wn(0);
    for k in 1..n as u32 {
        acc = Formula::BvAdd(Box::new(acc), Box::new(wn(k)), 32);
    }
    acc
}

/// field sum + 1 (deliberately WRONG, negative control).
fn field_sum_plus_one_spec(n: usize) -> Formula {
    Formula::BvAdd(Box::new(field_sum_spec(n)), Box::new(bv32(1)), 32)
}

/// Just f0 (what the bytes would compute if field 1's Str/Ldr collapsed onto
/// offset 0 or were dropped) — a WRONG-OFFSET negative control with teeth: it is
/// distinguishable from f0+f1 only because field 1 really lives at its own offset.
fn field0_only_spec() -> Formula {
    wn(0)
}

/// The bit width of a field type the field-sum fixture covers.
fn field_width(ty: &Ty) -> u32 {
    match ty {
        Ty::I8 | Ty::U8 => 8,
        Ty::I16 | Ty::U16 => 16,
        Ty::I32 | Ty::U32 => 32,
        other => panic!("the field-sum fixture does not cover a {other:?} field"),
    }
}

/// Argument register X_`reg` read as a field of type `ty`, widened to i32 the
/// way `make_struct_sum_module_spelled` widens it.
fn field_term(reg: u32, ty: &Ty) -> Formula {
    let width = field_width(ty);
    let low = Formula::BvExtract {
        inner: Box::new(Formula::Var(format!("X{reg}"), Sort::BitVec(64))),
        high: width - 1,
        low: 0,
    };
    match widen_to_i32(ty) {
        None => low,
        Some(CastOp::ZExt) => Formula::BvZeroExt(Box::new(low), 32 - width),
        Some(CastOp::SExt) => Formula::BvSignExt(Box::new(low), 32 - width),
        Some(other) => panic!("unexpected widening {other:?}"),
    }
}

/// The i32 sum of field k = argument k, for any covered field widths.
fn typed_field_sum_spec(field_tys: &[Ty]) -> Formula {
    sum_of(field_tys.iter().enumerate().map(|(k, ty)| field_term(k as u32, ty)))
}

/// What the bytes would compute if lanes 0 and 1 were swapped: field 0 holds
/// argument 1 cut to field 0's width, and field 1 holds argument 0 cut to field
/// 1's width. Distinguishable from the right sum only when the two widths differ.
fn swapped_lanes_field_sum_spec(field_tys: &[Ty]) -> Formula {
    sum_of(field_tys.iter().enumerate().map(|(k, ty)| {
        let reg = match k {
            0 => 1,
            1 => 0,
            k => k as u32,
        };
        field_term(reg, ty)
    }))
}

fn sum_of(mut terms: impl Iterator<Item = Formula>) -> Formula {
    let first = terms.next().expect("at least one field");
    terms.fold(first, |acc, term| Formula::BvAdd(Box::new(acc), Box::new(term), 32))
}

// ---------------------------------------------------------------------------
// VALUE-DIFFERENTIAL: the trust-ir interpreter on the gep-fill stand-in Module.
// ---------------------------------------------------------------------------

fn interpret_struct_gep_fill(module: &Module, args_i: &[i128]) -> i128 {
    let interp = Interpreter::with_module(module);
    let args: Vec<InterpretValue> =
        args_i.iter().map(|a| InterpretValue::int(Ty::I32, *a).expect("arg")).collect();
    let outcome = interp
        .execute_func(FuncId::new(0), args)
        .expect("interpreter execute_func failed (struct-in-memory round trip)");
    outcome.returns[0].as_int().expect("integer return").as_signed()
}

// ===========================================================================
// TEST 1 — 2-FIELD struct: well-formed LIR with ONE aggregate slot (size 8,
// align 4), TWO field Str + TWO field Ldr, real Str/Ldr in the emitted bytes.
// ===========================================================================

#[test]
fn struct_2field_emits_slot_with_field_stores_and_loads() {
    let field_tys = [Ty::I32, Ty::I32];
    let module = make_struct_sum_module(&field_tys);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("lower struct");

    assert_eq!(lir.stack_slots.len(), 1, "expected exactly one aggregate stack slot");
    assert_eq!(lir.stack_slots[0].size, 8, "2-field i32 struct C-layout size is 8 bytes");
    assert_eq!(lir.stack_slots[0].align, 4, "2-field i32 struct C-layout align is 4 bytes");

    let mut lir_stores = 0usize;
    let mut lir_loads = 0usize;
    let mut offset_geps = 0usize;
    for blk in lir.blocks.values() {
        for ins in &blk.instructions {
            match ins.opcode {
                LirOpcode::Store { .. } => lir_stores += 1,
                LirOpcode::Load { .. } => lir_loads += 1,
                LirOpcode::ArrayGep { .. } => offset_geps += 1,
                _ => {}
            }
        }
    }
    assert_eq!(lir_stores, 2, "expected 2 per-field Stores");
    assert_eq!(lir_loads, 2, "expected 2 per-field Loads");
    // Field 1 @ offset 4 -> a base+4 address computation for both store and load.
    assert!(offset_geps >= 2, "expected >= 2 field-offset address computations, got {offset_geps}");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");
    let (strs, ldrs) = count_single_ldr_str(&code, base);
    assert!(strs >= 2, "expected >= 2 Str (two field stores), got {strs}");
    assert!(ldrs >= 2, "expected >= 2 Ldr (two field loads), got {ldrs}");
}

// ===========================================================================
// TEST 2 — 3-FIELD struct: proves the N-field generalization + NON-TRIVIAL field
// offsets 0/4/8. ONE slot (size 12, align 4), THREE field Str + THREE field Ldr.
// ===========================================================================

#[test]
fn struct_3field_emits_slot_with_three_field_stores_and_loads() {
    let field_tys = [Ty::I32, Ty::I32, Ty::I32];
    let module = make_struct_sum_module(&field_tys);
    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("lower 3-field struct");

    assert_eq!(lir.stack_slots.len(), 1, "one aggregate slot");
    assert_eq!(lir.stack_slots[0].size, 12, "3-field i32 struct C-layout size is 12 bytes");
    assert_eq!(lir.stack_slots[0].align, 4, "3-field i32 struct C-layout align is 4 bytes");

    let mut lir_stores = 0usize;
    let mut lir_loads = 0usize;
    for blk in lir.blocks.values() {
        for ins in &blk.instructions {
            match ins.opcode {
                LirOpcode::Store { .. } => lir_stores += 1,
                LirOpcode::Load { .. } => lir_loads += 1,
                _ => {}
            }
        }
    }
    assert_eq!(lir_stores, 3, "expected 3 per-field Stores (x@0, y@4, z@8)");
    assert_eq!(lir_loads, 3, "expected 3 per-field Loads (x@0, y@4, z@8)");

    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty(), "emitted __text is empty");
    let (strs, ldrs) = count_single_ldr_str(&code, base);
    assert!(strs >= 3, "expected >= 3 Str, got {strs}");
    assert!(ldrs >= 3, "expected >= 3 Ldr, got {ldrs}");
}

// ===========================================================================
// TEST 3 — PROVEN OUTPUT (infinite domain): the 2-field struct bytes compute
// f0 + f1 for ALL inputs. UNSAT.
// ===========================================================================

#[test]
fn struct_2field_bytes_compute_field_sum_for_all_inputs() {
    let module = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty());
    let machine_out = symbolic_machine_output(&code, base);
    let spec = field_sum_spec(2);
    assert!(
        discharge_equal(&machine_out, &spec),
        "PROVEN-OUTPUT FAILED: 2-field struct bytes not proven equal to f0+f1.\n  out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 4 — PROVEN OUTPUT: the 3-field struct bytes compute f0 + f1 + f2 for ALL
// inputs (the N-field generalization proven at the byte level). UNSAT.
// ===========================================================================

#[test]
fn struct_3field_bytes_compute_field_sum_for_all_inputs() {
    let module = make_struct_sum_module(&[Ty::I32, Ty::I32, Ty::I32]);
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty());
    let machine_out = symbolic_machine_output(&code, base);
    let spec = field_sum_spec(3);
    assert!(
        discharge_equal(&machine_out, &spec),
        "PROVEN-OUTPUT FAILED: 3-field struct bytes not proven equal to f0+f1+f2.\n  out = {machine_out:?}"
    );
}

// ===========================================================================
// TEST 5 — MANDATORY NEGATIVE CONTROLS: the SAME struct bytes proven against a
// `+1` spec MUST be SAT (both arities). A non-SAT result would make the positive
// certificate vacuous (e.g. a collapsed field offset or dropped store).
// ===========================================================================

#[test]
fn negative_control_struct_bytes_vs_plus_one_is_sat() {
    for n in [2usize, 3usize] {
        let field_tys: Vec<Ty> = (0..n).map(|_| Ty::I32).collect();
        let module = make_struct_sum_module(&field_tys);
        let (code, base) = emit_module_text(&module);
        assert!(!code.is_empty());
        let machine_out = symbolic_machine_output(&code, base);
        let wrong = field_sum_plus_one_spec(n);
        assert!(
            !discharge_equal(&machine_out, &wrong),
            "VACUITY CHECK FAILED ({n}-field): struct bytes 'proven' equal to (field sum)+1"
        );
    }
}

// ===========================================================================
// TEST 5b — WRONG-OFFSET negative control: the 2-field struct bytes must NOT
// equal `f0` alone (SAT). If field 1's Str/Ldr had collapsed onto offset 0 (or
// been dropped), the bytes would compute f0 and this would be UNSAT — proving the
// field-1-at-offset-4 layout has teeth, not just the additive `+1` control.
// ===========================================================================

#[test]
fn negative_control_struct_bytes_vs_field0_only_is_sat() {
    let module = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    let (code, base) = emit_module_text(&module);
    assert!(!code.is_empty());
    let machine_out = symbolic_machine_output(&code, base);
    assert!(
        !discharge_equal(&machine_out, &field0_only_spec()),
        "WRONG-OFFSET VACUITY FAILED: struct bytes 'proven' equal to f0 alone; field 1's \
         offset-4 Str/Ldr carries no observable weight"
    );
}

// ===========================================================================
// TEST 6 — VALUE-DIFFERENTIAL (layout agreement): the trust-ir interpreter
// round-trips a `Ty::Struct`-in-memory value through the SAME `struct_layout`
// (offsets x@0, y@4[, z@8], computed from `def.fields`) that the converter's
// `aggregate_mem_layout` reproduces. A passing interpret shows the interpreter's
// struct byte_size/struct_layout agrees with the converter's emitted-byte layout
// for a struct that DECLARES NO LAYOUT (`size: None`), the only kind built here;
// declared layouts are TESTS 12-17.
//
// (The SEED spelling of the whole-`Store(struct)`/`Load(struct)` round trip the
// converter lowers is NOT interpreter-executable — the interpreter faults on the
// `Undef` seed and has no `(Ty::Struct, Constant::Aggregate)` constant arm — so
// the interpreter-executable stand-in fills the slot via typed field Stores and
// reads the whole struct back, exercising the identical field-offset math. The
// constructor spelling is executable as it stands: TESTS 9-11.)
// ===========================================================================

#[test]
fn struct_value_diff_interpreter_round_trips_ty_struct_in_memory() {
    // 2-field.
    let m2 = make_struct_gep_fill_module(&[Ty::I32, Ty::I32]);
    assert_eq!(interpret_struct_gep_fill(&m2, &[5, 7]), 12);
    assert_eq!(interpret_struct_gep_fill(&m2, &[0, 0]), 0);
    assert_eq!(interpret_struct_gep_fill(&m2, &[-3, 10]), 7);
    assert_eq!(interpret_struct_gep_fill(&m2, &[100, -50]), 50);

    // 3-field (non-trivial offsets 0/4/8).
    let m3 = make_struct_gep_fill_module(&[Ty::I32, Ty::I32, Ty::I32]);
    assert_eq!(interpret_struct_gep_fill(&m3, &[1, 2, 3]), 6);
    assert_eq!(interpret_struct_gep_fill(&m3, &[10, 20, 30]), 60);
    assert_eq!(interpret_struct_gep_fill(&m3, &[-5, 5, 100]), 100);
}

// ===========================================================================
// TEST 7 — the value-diff stand-in and the converter share the SAME layout: the
// converter's emitted 2-field-struct bytes (whole-Store shape) compute f0+f1 AND
// the interpreter's gep-fill round-trip returns f0+f1, over shared concrete
// inputs — a direct cross-check that both agree on the field offsets. This closes
// the loop between the (interpreter-executable) value-diff and the (converter-
// lowered, ay-proven) emitted bytes even though they use different seed shapes.
// ===========================================================================

// ===========================================================================
// TEST 8 — FAIL-CLOSED on shapes outside the proven slice: a nested-aggregate
// field (struct-of-tuple), a float / i128 field, a missing StructDef, and a
// non-default repr must all be REJECTED (the converter never lays them out under
// a layout the emitted bytes are not proven against).
// ===========================================================================

fn lower_err(module: &Module) -> bool {
    lower_trust_ir_function_to_lir(module, &module.functions[0]).is_err()
}

#[test]
fn struct_fail_closed_on_unsupported_field_and_repr_shapes() {
    // (a) nested-aggregate field: struct { a: i32, inner: (i32, i32) }.
    let mut m = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    // Rewrite the StructDef's field 1 to a nested tuple (non-scalar).
    m.structs[0].fields[1].ty = Ty::Tuple(vec![Ty::I32, Ty::I32]);
    assert!(lower_err(&m), "struct with a nested-aggregate field must fail closed");

    // (b) float field.
    let mut mf = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    mf.structs[0].fields[1].ty = Ty::F32;
    assert!(lower_err(&mf), "struct with a float field must fail closed");

    // (c) i128 field (out of the i8..i64 slice).
    let mut mi = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    mi.structs[0].fields[1].ty = Ty::I128;
    assert!(lower_err(&mi), "struct with an i128 field must fail closed");

    // (d) missing StructDef: point the alloca at a StructId with no def.
    let mut md = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    md.structs.clear();
    assert!(lower_err(&md), "struct alloca with no StructDef must fail closed");

    // (e) non-default repr (C / packed): only natural repr(Rust) layout is proven.
    let mut mc = make_struct_sum_module(&[Ty::I32, Ty::I32]);
    mc.structs[0].repr = StructRepr::C;
    assert!(lower_err(&mc), "struct with a non-default repr must fail closed");
}

#[test]
fn struct_converter_bytes_and_interpreter_agree_on_field_sum() {
    let field_tys = [Ty::I32, Ty::I32];
    // Converter path: emitted bytes proven == f0+f1 for ALL inputs (superset of
    // any concrete point).
    let conv = make_struct_sum_module(&field_tys);
    let (code, base) = emit_module_text(&conv);
    assert!(discharge_equal(&symbolic_machine_output(&code, base), &field_sum_spec(2)));
    // Interpreter path (gep-fill stand-in): same field offsets, concrete points.
    let interp_m = make_struct_gep_fill_module(&field_tys);
    for (a, b) in [(5i128, 7i128), (41, 1), (-3, 10)] {
        assert_eq!(interpret_struct_gep_fill(&interp_m, &[a, b]), a + b);
    }
}

// ===========================================================================
// TESTS 9-11 — the COMPLETE-CONSTRUCTOR spelling (`StructBase::Constructor`):
// the stored struct is ONE `make_aggregate struct.0 [p0, p1, ..]`, with no seed
// and no InsertField, which is how the bridge spells a complete construction
// since BMC-LANE-1. PASS 1.7 records the constructor's lanes as the struct's
// field values (`lower_aggregate_inst`'s MakeAggregate arm), and the whole
// Store becomes one per-field Store per lane at that field's offset and width.
// The widths are mixed (`{u8, i32}` and `{i32, u8}`: offsets 0 and 4 in an
// 8-byte, 4-aligned slot), so a lowering that put a lane in the wrong field
// changes the result even though `+` is commutative. The proven-output check,
// the +1 vacuity control and the concrete oracle run over it as over the seed
// spelling; the concrete oracle here runs the interpreter and the emitted
// bytes on the SAME module, which the constructor spelling makes possible.
// ===========================================================================

/// The struct field types the constructor spelling is checked at.
const CONSTRUCTOR_FIELD_TYS: [&[Ty]; 4] =
    [&[Ty::I32, Ty::I32], &[Ty::U8, Ty::I32], &[Ty::I32, Ty::U8], &[Ty::I32, Ty::I32, Ty::I32]];

fn interpret_struct_sum(module: &Module, field_tys: &[Ty], args: &[i128]) -> i128 {
    let interp = Interpreter::with_module(module);
    let args: Vec<InterpretValue> = field_tys
        .iter()
        .zip(args)
        .map(|(ty, a)| InterpretValue::int(ty.clone(), *a).expect("arg"))
        .collect();
    let outcome = interp
        .execute_func(FuncId::new(0), args)
        .expect("interpreter execute_func failed (constructor-spelled struct round trip)");
    outcome.returns[0].as_int().expect("integer return").as_signed()
}

#[test]
fn struct_make_aggregate_stores_each_lane_at_its_field_width() {
    let field_tys = [Ty::U8, Ty::I32];
    let module = make_struct_sum_module_spelled(&field_tys, StructBase::Constructor);
    let insts: Vec<&Inst> =
        module.functions[0].blocks.iter().flat_map(|b| &b.body).map(|n| &n.inst).collect();
    assert!(
        !insts.iter().any(|inst| matches!(inst, Inst::Undef { .. } | Inst::InsertField { .. })),
        "the constructor spelling carries no seed and no InsertField"
    );
    assert_eq!(
        insts.iter().filter(|inst| matches!(inst, Inst::MakeAggregate { .. })).count(),
        1,
        "one complete constructor"
    );

    let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
        .expect("lower {u8, i32} constructor");
    assert_eq!(lir.stack_slots.len(), 1, "one aggregate slot");
    assert_eq!(lir.stack_slots[0].size, 8, "{{u8, i32}}: u8 @0, pad, i32 @4 -> 8 bytes");
    assert_eq!(lir.stack_slots[0].align, 4, "{{u8, i32}} aligns to its i32 field");
    let lir_insts: Vec<_> = lir.blocks.values().flat_map(|b| &b.instructions).collect();
    let stores: Vec<_> = lir_insts
        .iter()
        .filter_map(|i| match &i.opcode {
            LirOpcode::Store { ty, .. } => Some((i.args[0], ty.clone())),
            _ => None,
        })
        .collect();
    use trust_cg_lower::instructions::Value;
    use trust_cg_lower::types::Type as LirType;
    assert_eq!(
        stores,
        vec![(Value(0), LirType::I8), (Value(1), LirType::I32)],
        "lane 0 (the u8 param) is stored 1 byte wide, lane 1 (the i32 param) 4 bytes wide"
    );
    let loads: Vec<_> = lir_insts
        .iter()
        .filter_map(|i| match &i.opcode {
            LirOpcode::Load { ty, .. } => Some(ty.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(loads, vec![LirType::I8, LirType::I32], "each field loads at its own width");

    // The 1-byte field reaches the machine bytes as a byte store and a byte load.
    let (code, base) = emit_module_text(&module);
    let count = |wanted: Opcode| {
        code.chunks_exact(4)
            .enumerate()
            .filter(|(k, word)| {
                let pc = base + 4 * *k as u64;
                decode_aarch64(&<[u8; 4]>::try_from(*word).unwrap(), pc)
                    .is_ok_and(|insn| insn.opcode == wanted)
            })
            .count()
    };
    assert_eq!(count(Opcode::Strb), 1, "the u8 field is stored with one STRB");
    assert_eq!(count(Opcode::Ldrb), 1, "the u8 field is loaded with one LDRB");
}

#[test]
fn struct_make_aggregate_bytes_compute_field_sum_for_all_inputs() {
    for field_tys in CONSTRUCTOR_FIELD_TYS {
        let module = make_struct_sum_module_spelled(field_tys, StructBase::Constructor);
        let (code, base) = emit_module_text(&module);
        assert!(!code.is_empty(), "emitted __text is empty for {field_tys:?}");
        let machine_out = symbolic_machine_output(&code, base);
        let spec = typed_field_sum_spec(field_tys);
        assert!(
            discharge_equal(&machine_out, &spec),
            "PROVEN-OUTPUT FAILED: {field_tys:?} constructor bytes not proven equal to the field \
             sum.\n  out = {machine_out:?}"
        );
        // Vacuity: the same bytes are NOT the field sum + 1.
        let plus_one = Formula::BvAdd(Box::new(spec), Box::new(bv32(1)), 32);
        assert!(
            !discharge_equal(&machine_out, &plus_one),
            "VACUITY CHECK FAILED ({field_tys:?}): constructor bytes 'proven' equal to (field \
             sum)+1"
        );
        // Lane order has teeth wherever the first two widths differ.
        if field_width(&field_tys[0]) != field_width(&field_tys[1]) {
            assert!(
                !discharge_equal(&machine_out, &swapped_lanes_field_sum_spec(field_tys)),
                "LANE-ORDER VACUITY FAILED ({field_tys:?}): the bytes also equal the sum with \
                 lanes 0 and 1 swapped"
            );
        }
    }
}

#[test]
fn struct_make_aggregate_bytes_and_interpreter_agree_on_concrete_inputs() {
    let points: [[i128; 3]; 5] =
        [[5, 7, 9], [255, 1, -2], [200, -300, 0], [0, 2147483647, 1], [255, 2147483647, -1]];
    for field_tys in CONSTRUCTOR_FIELD_TYS {
        let module = make_struct_sum_module_spelled(field_tys, StructBase::Constructor);
        let (code, base) = emit_module_text(&module);
        for point in points {
            // Each argument fits its field type (the u8 points are 0..=255).
            let args: Vec<i128> = field_tys
                .iter()
                .zip(point)
                .map(|(ty, a)| if *ty == Ty::U8 { a & 0xff } else { a })
                .collect();
            let expected = args.iter().fold(0i32, |acc, a| acc.wrapping_add(*a as i32));
            assert_eq!(
                interpret_struct_sum(&module, field_tys, &args),
                i128::from(expected),
                "interpreter on {field_tys:?} {args:?}"
            );
            let out = concrete_machine_output(&code, base, field_tys, &args);
            assert!(
                discharge_equal(&out, &bv32(i128::from(expected) & 0xffff_ffff)),
                "the emitted {field_tys:?} bytes on {args:?} must return {expected}; got {out:?}"
            );
        }
    }
}

// ===========================================================================
// TESTS 12-17 — DECLARED LAYOUTS (CG-DECLARED-LAYOUT-1, 2026-11-10).
//
// Every `StructDef` above is `size: None, align: None` with no field offset: the
// one branch on which the interpreter's layout IS declaration order, so the
// layout agreement checked above holds by construction there. The producer does
// not build that shape: `register_struct` fills `size`/`align`/`FieldDef::offset`
// from rustc's reorder-aware layout for every concrete struct, and the bridge
// fills `Module::tuple_layouts` from rustc's tuple layouts; the interpreter lays
// both out at the DECLARED offsets (`declared_struct_layout`, `tuple_layout_in`).
// Until CG-DECLARED-LAYOUT-1 the converter laid them out in declaration order.
//
// The cases below are declared and reordered (the structs as the producer
// declares them, see `declared_cases`), and the ORACLE for where each field
// lives is the reference interpreter itself: the slot image it writes for a
// stored value, read back one byte at a time (`interpreter_slot_image`). The
// checks:
//   12 — the interpreter really uses the declaration (and each case's declared
//        offsets differ from declaration order, so every case discriminates);
//   13 — the LIR slot is the declared size/alignment, and each field's Str and
//        Ldr address the interpreter's offset;
//   14 — the EMITTED BYTES write each field at the interpreter's offset relative
//        to every other field, proven by ay for every SP and input;
//   15 — the emitted bytes compute f0 - f1 [+ f2] for ALL inputs (+1 and
//        lane-swap vacuity controls);
//   16 — VALUE-DIFFERENTIAL: interpreter and emitted bytes agree on concrete
//        inputs on the same module, `S { a@4, b@0 }` included;
//   17 — a declaration the interpreter refuses is refused.
// Declaration order on a declared layout (the pre-2026-11-10 converter) fails 13
// and 14; 15 and 16 are value-level and hold under any layout a whole round trip
// uses, which is why 13 and 14 exist.
// ===========================================================================

/// How a declared-layout case declares its layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Declared {
    /// A `StructDef` with `size`, `align` and every `FieldDef::offset`.
    Struct,
    /// A `Ty::Tuple` with a `Module::tuple_layouts` descriptor.
    Tuple,
    /// A `StructDef` with no `size`, `align` or `FieldDef::offset`: the
    /// interpreter lays it out in declaration order (`size`/`offsets` are then
    /// that layout, as an expectation only; nothing is declared).
    Undeclared,
}

#[derive(Clone, Debug)]
struct DeclaredCase {
    label: &'static str,
    declared: Declared,
    field_tys: Vec<Ty>,
    size: u64,
    align: u64,
    offsets: Vec<u64>,
}

/// The struct layouts are the producer's own: `trustc -Ztrust-dump=ir` (sealed
/// 29ebb403d, 2026-11-10) declares `struct P { a: u8, b: u32 }` as
/// `{ a: u8 @4, b: u32 @0 } size=8 align=4` and `struct Q { a: u8, b: u16, c: u32 }`
/// as `{ a: u8 @6, b: u16 @4, c: u32 @0 } size=8 align=4` (largest alignment first;
/// the `i16` here is that `u16` signed, so the widening is exercised both ways).
/// The tuple descriptors are hand-built reorders the interpreter accepts (rustc
/// kept `(u8, u32)` in declaration order in that dump).
fn declared_cases() -> Vec<DeclaredCase> {
    let case = |label, declared, field_tys: &[Ty], size, align, offsets: &[u64]| DeclaredCase {
        label,
        declared,
        field_tys: field_tys.to_vec(),
        size,
        align,
        offsets: offsets.to_vec(),
    };
    vec![
        case("S { a: i32 @4, b: i32 @0 }", Declared::Struct, &[Ty::I32, Ty::I32], 8, 4, &[4, 0]),
        case("S { a: u8 @4, b: i32 @0 }", Declared::Struct, &[Ty::U8, Ty::I32], 8, 4, &[4, 0]),
        case(
            "S { a: u8 @6, b: i16 @4, c: i32 @0 }",
            Declared::Struct,
            &[Ty::U8, Ty::I16, Ty::I32],
            8,
            4,
            &[6, 4, 0],
        ),
        case("(i32, i32) @ [4, 0]", Declared::Tuple, &[Ty::I32, Ty::I32], 8, 4, &[4, 0]),
        case("(u8, i32) @ [4, 0]", Declared::Tuple, &[Ty::U8, Ty::I32], 8, 4, &[4, 0]),
    ]
}

/// The target the producer stamps on a module that declares layouts (the
/// `-Ztrust-dump=ir` header `target "arm64-apple-macosx" 8 little
/// structpass=unclassified`). The interpreter refuses a tuple descriptor on a
/// module with no target (`LayoutError::TupleLayoutTargetMissing`).
fn producer_target() -> TargetInfo {
    TargetInfo {
        triple: "arm64-apple-macosx".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::Unclassified,
    }
}

/// Register `case`'s aggregate type in `module` with its declared layout (on
/// the producer's target) and return it.
fn declare_aggregate(module: &mut Module, case: &DeclaredCase) -> Ty {
    module.target_info = Some(producer_target());
    match case.declared {
        Declared::Struct => {
            let sid = StructId::new(0);
            let fields = case
                .field_tys
                .iter()
                .zip(&case.offsets)
                .enumerate()
                .map(|(i, (ty, off))| FieldDef {
                    name: format!("f{i}"),
                    ty: ty.clone(),
                    offset: Some(*off),
                })
                .collect();
            module.add_struct(StructDef {
                id: sid,
                name: "S".into(),
                fields,
                size: Some(case.size),
                align: Some(case.align),
                repr: StructRepr::Rust,
                origin: None,
            });
            Ty::Struct(sid)
        }
        Declared::Undeclared => {
            let sid = StructId::new(0);
            let fields = case
                .field_tys
                .iter()
                .enumerate()
                .map(|(i, ty)| FieldDef { name: format!("f{i}"), ty: ty.clone(), offset: None })
                .collect();
            module.add_struct(StructDef {
                id: sid,
                name: "S".into(),
                fields,
                size: None,
                align: None,
                repr: StructRepr::Rust,
                origin: None,
            });
            Ty::Struct(sid)
        }
        Declared::Tuple => {
            let tup = Ty::Tuple(case.field_tys.clone());
            let tuple_type = module.add_type(tup.clone()).expect("Module::add_type");
            module.tuple_layouts.push(TupleLayoutDescriptor {
                tuple_type,
                size: case.size,
                align: case.align,
                field_offsets: case.offsets.clone(),
            });
            tup
        }
    }
}

/// Dense `ValueId`s for a hand-built body.
struct Ids(u32);

impl Ids {
    fn next(&mut self) -> ValueId {
        let v = ValueId::new(self.0);
        self.0 += 1;
        v
    }
}

/// Push the stored value of `aty` built from `params` in `spelling`; return it.
fn push_stored_value(
    bb: &mut Block,
    ids: &mut Ids,
    aty: &Ty,
    params: &[ValueId],
    spelling: StructBase,
) -> ValueId {
    match spelling {
        StructBase::UndefSeed => {
            let mut cur = ids.next();
            bb.body.push(InstrNode::new(Inst::Undef { ty: aty.clone() }).with_result(cur));
            for (k, p) in params.iter().enumerate() {
                let next = ids.next();
                bb.body.push(
                    InstrNode::new(Inst::InsertField {
                        ty: aty.clone(),
                        aggregate: cur,
                        field: k as u32,
                        value: *p,
                    })
                    .with_result(next),
                );
                cur = next;
            }
            cur
        }
        StructBase::Constructor => {
            let made = ids.next();
            bb.body.push(
                InstrNode::new(Inst::MakeAggregate {
                    ty: aty.clone(),
                    variant: None,
                    fields: params.to_vec(),
                })
                .with_result(made),
            );
            made
        }
    }
}

/// `(p0, p1[, p2]) -> f0 - f1 [+ f2]` through one slot of `case`'s declared
/// type: build the value (`spelling`), `alloca`, whole `store`, whole `load`,
/// `extractfield` each, widen each narrower field to i32, combine. `-` makes the
/// result depend on which lane is which even at equal widths.
fn make_declared_module(case: &DeclaredCase, spelling: StructBase) -> Module {
    let mut module = Module::new("declared_layout_module");
    module.func_types.push(FuncTy {
        params: case.field_tys.clone(),
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: None,
    });
    let aty = declare_aggregate(&mut module, case);
    let mut function = IrFunction::new(FuncId::new(0), "dl", FuncTyId::new(0), BlockId::new(0));
    let mut ids = Ids(0);
    let params: Vec<ValueId> = case.field_tys.iter().map(|_| ids.next()).collect();
    let mut bb0 = Block::new(BlockId::new(0));
    for (p, ty) in params.iter().zip(&case.field_tys) {
        bb0.params.push((*p, ty.clone()));
    }
    let stored = push_stored_value(&mut bb0, &mut ids, &aty, &params, spelling);
    let slot = ids.next();
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: aty.clone(), count: None, align: None })
            .with_result(slot),
    );
    bb0.body.push(InstrNode::new(Inst::Store {
        ty: aty.clone(),
        ptr: slot,
        value: stored,
        volatile: false,
        align: None,
    }));
    let acc = push_whole_load_combination(&mut bb0, &mut ids, &aty, slot, &case.field_tys);
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    function.blocks.push(bb0);
    module.functions.push(function);
    module
}

/// `load aty *slot`, `extractfield` each field, then [`push_combination`] of the
/// fields; returns the combination.
fn push_whole_load_combination(
    bb: &mut Block,
    ids: &mut Ids,
    aty: &Ty,
    slot: ValueId,
    field_tys: &[Ty],
) -> ValueId {
    let ld = ids.next();
    bb.body.push(
        InstrNode::new(Inst::Load { ty: aty.clone(), ptr: slot, volatile: false, align: None })
            .with_result(ld),
    );
    let mut fields = Vec::new();
    for (k, ty) in field_tys.iter().enumerate() {
        let ex = ids.next();
        bb.body.push(
            InstrNode::new(Inst::ExtractField { ty: ty.clone(), aggregate: ld, field: k as u32 })
                .with_result(ex),
        );
        fields.push((ex, ty.clone()));
    }
    push_combination(bb, ids, &fields)
}

/// Widen each `(value, type)` lane narrower than 32 bits to i32 and combine
/// them as `l0 - l1 [+ l2]`; returns the combination.
fn push_combination(bb: &mut Block, ids: &mut Ids, fields: &[(ValueId, Ty)]) -> ValueId {
    let mut lanes = Vec::new();
    for (ex, ty) in fields {
        let lane = match widen_to_i32(ty) {
            None => *ex,
            Some(op) => {
                let wide = ids.next();
                bb.body.push(
                    InstrNode::new(Inst::Cast {
                        op,
                        src_ty: ty.clone(),
                        dst_ty: Ty::I32,
                        operand: *ex,
                    })
                    .with_result(wide),
                );
                wide
            }
        };
        lanes.push(lane);
    }
    let mut acc = lanes[0];
    for (k, lane) in lanes.iter().enumerate().skip(1) {
        let r = ids.next();
        let op = if k == 1 { BinOp::Sub } else { BinOp::Add };
        bb.body.push(
            InstrNode::new(Inst::BinOp { op, ty: Ty::I32, lhs: acc, rhs: *lane }).with_result(r),
        );
        acc = r;
    }
    acc
}

/// `f0 - f1 [+ f2]` with argument register `regs[k]` as field `k`.
fn declared_combination_spec(field_tys: &[Ty], regs: &[u32]) -> Formula {
    let terms: Vec<Formula> =
        field_tys.iter().zip(regs).map(|(ty, reg)| field_term(*reg, ty)).collect();
    let mut acc = terms[0].clone();
    for (k, term) in terms.iter().enumerate().skip(1) {
        acc = if k == 1 {
            Formula::BvSub(Box::new(acc), Box::new(term.clone()), 32)
        } else {
            Formula::BvAdd(Box::new(acc), Box::new(term.clone()), 32)
        };
    }
    acc
}

/// A value for field `k` of type `ty` whose bytes occur nowhere else in the
/// image: byte `j` is `0x10 * (k + 1) + j + 1`.
fn marker_value(k: usize, ty: &Ty) -> i128 {
    (0..field_width(ty) / 8).map(|j| (0x10 * (k as i128 + 1) + i128::from(j) + 1) << (8 * j)).sum()
}

/// The reference interpreter's image of the slot of `case`'s type after a whole
/// store of the marker values: byte `i` as an `u8` load at `slot + i`, `None`
/// where the interpreter refuses to read one (padding). One execution per byte,
/// so a refused padding byte does not hide the others.
fn interpreter_slot_image(case: &DeclaredCase) -> Vec<Option<u8>> {
    (0..case.size)
        .map(|byte| {
            let mut module = Module::new("declared_layout_image");
            module.func_types.push(FuncTy {
                params: case.field_tys.clone(),
                returns: vec![Ty::U8],
                is_vararg: false,
                abi: None,
            });
            let aty = declare_aggregate(&mut module, case);
            let mut function =
                IrFunction::new(FuncId::new(0), "image", FuncTyId::new(0), BlockId::new(0));
            let mut ids = Ids(0);
            let params: Vec<ValueId> = case.field_tys.iter().map(|_| ids.next()).collect();
            let mut bb0 = Block::new(BlockId::new(0));
            for (p, ty) in params.iter().zip(&case.field_tys) {
                bb0.params.push((*p, ty.clone()));
            }
            let stored =
                push_stored_value(&mut bb0, &mut ids, &aty, &params, StructBase::Constructor);
            let slot = ids.next();
            bb0.body.push(
                InstrNode::new(Inst::Alloca { ty: aty.clone(), count: None, align: None })
                    .with_result(slot),
            );
            bb0.body.push(InstrNode::new(Inst::Store {
                ty: aty,
                ptr: slot,
                value: stored,
                volatile: false,
                align: None,
            }));
            let off = ids.next();
            let addr = ids.next();
            let read = ids.next();
            bb0.body.push(
                InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(i128::from(byte)) })
                    .with_result(off),
            );
            bb0.body.push(
                InstrNode::new(Inst::GEP {
                    pointee_ty: Ty::I8,
                    base: slot,
                    indices: vec![off],
                    inbounds: true,
                })
                .with_result(addr),
            );
            bb0.body.push(
                InstrNode::new(Inst::Load { ty: Ty::U8, ptr: addr, volatile: false, align: None })
                    .with_result(read),
            );
            bb0.body.push(InstrNode::new(Inst::Return { values: vec![read] }));
            function.blocks.push(bb0);
            module.functions.push(function);
            let args: Vec<InterpretValue> = case
                .field_tys
                .iter()
                .enumerate()
                .map(|(k, ty)| InterpretValue::int(ty.clone(), marker_value(k, ty)).expect("arg"))
                .collect();
            Interpreter::with_module(&module).execute_func(FuncId::new(0), args).ok().map(|out| {
                (out.returns[0].as_int().expect("integer return").as_signed() & 0xff) as u8
            })
        })
        .collect()
}

/// Where the reference interpreter puts each field of `case`'s type: the one
/// place its marker bytes occur in [`interpreter_slot_image`].
fn interpreter_field_offsets(case: &DeclaredCase) -> Vec<u64> {
    let image = interpreter_slot_image(case);
    case.field_tys
        .iter()
        .enumerate()
        .map(|(k, ty)| {
            let width = (field_width(ty) / 8) as usize;
            let bytes: Vec<Option<u8>> =
                (0..width).map(|j| Some((marker_value(k, ty) >> (8 * j)) as u8)).collect();
            let hits: Vec<usize> = (0..=image.len().saturating_sub(width))
                .filter(|&at| image[at..at + width] == bytes[..])
                .collect();
            let [at] = hits.as_slice() else {
                panic!("{}: field {k}'s bytes occur at {hits:?} in {image:02x?}", case.label)
            };
            *at as u64
        })
        .collect()
}

/// The declaration-order offsets of `field_tys` (the interpreter's
/// `aggregate_layout` for a type that declares none).
fn declaration_order_offsets(field_tys: &[Ty]) -> Vec<u64> {
    let mut offset = 0u64;
    field_tys
        .iter()
        .map(|ty| {
            let width = u64::from(field_width(ty) / 8);
            offset = offset.div_ceil(width) * width;
            let at = offset;
            offset += width;
            at
        })
        .collect()
}

/// Each LIR field access's byte offset in its slot, in emission order: the
/// `(stored value, offset)` of every `Store` and the offset of every `Load`.
/// The address is the slot's `StackAddr` (offset 0) or an `ArrayGep i8` off it
/// by an `Iconst` (`emit_field_addr`'s two spellings); anything else panics.
fn lir_field_offsets(
    lir: &trust_cg_lower::function::Function,
) -> (Vec<(trust_cg_lower::instructions::Value, i64)>, Vec<i64>) {
    use trust_cg_lower::instructions::{Instruction, Value};
    let insts: Vec<&Instruction> = lir.blocks.values().flat_map(|b| &b.instructions).collect();
    let def = |v: Value| insts.iter().find(|i| i.results.contains(&v)).copied();
    let offset_of = |addr: Value| -> i64 {
        let addr = def(addr).expect("field address is defined");
        match (&addr.opcode, addr.args.as_slice()) {
            (LirOpcode::StackAddr { .. }, []) => 0,
            (LirOpcode::ArrayGep { elem_ty: trust_cg_lower::types::Type::I8 }, [base, idx]) => {
                assert!(
                    matches!(def(*base).map(|b| &b.opcode), Some(LirOpcode::StackAddr { .. })),
                    "field address is not slot-relative: {addr:?}"
                );
                let Some(LirOpcode::Iconst { imm, .. }) = def(*idx).map(|i| &i.opcode) else {
                    panic!("field offset is not a constant: {addr:?}")
                };
                *imm
            }
            other => panic!("unexpected field address {other:?}"),
        }
    };
    let stores = insts
        .iter()
        .filter(|i| matches!(i.opcode, LirOpcode::Store { .. }))
        .map(|i| (i.args[0], offset_of(i.args[1])))
        .collect();
    let loads = insts
        .iter()
        .filter(|i| matches!(i.opcode, LirOpcode::Load { .. }))
        .map(|i| offset_of(i.args[0]))
        .collect();
    (stores, loads)
}

/// One memory write the emitted bytes perform.
struct MemWriteRecord {
    address: Formula,
    value: Formula,
    width_bytes: u32,
}

/// Run the straight-line emitted bytes from the fully symbolic state, keeping
/// every `MemWrite` effect in program order.
fn symbolic_memory_writes(code: &[u8], base: u64) -> Vec<MemWriteRecord> {
    use trust_machine_sem::Effect;
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
    let mut writes = Vec::new();
    let mut pc = base;
    for _ in 0..1000 {
        let off = (pc - base) as usize;
        let bytes: [u8; 4] = code[off..off + 4].try_into().expect("inside __text");
        let insn = decode_aarch64(&bytes, pc).expect("decode_aarch64 failed");
        let effects = sem.effects(&state, &insn).expect("Aarch64Semantics::effects failed");
        for effect in &effects {
            if let Effect::MemWrite { address, value, width_bytes } = effect {
                writes.push(MemWriteRecord {
                    address: address.clone(),
                    value: value.clone(),
                    width_bytes: *width_bytes,
                });
            }
        }
        state.apply_effects(&effects).expect("apply_effects");
        if insn.opcode == Opcode::Ret {
            return writes;
        }
        pc += 4;
    }
    panic!("decode loop runaway (no RET)");
}

fn low_bits(f: Formula, bits: u32) -> Formula {
    Formula::BvExtract { inner: Box::new(f), high: bits - 1, low: 0 }
}

/// The address of the ONE emitted write that stores argument X_`k` as field
/// `k` of type `ty` (ay proves the stored bytes are that argument's low bytes).
fn field_write_address(writes: &[MemWriteRecord], k: usize, ty: &Ty, label: &str) -> Formula {
    let width = field_width(ty);
    let arg = low_bits(Formula::Var(format!("X{k}"), Sort::BitVec(64)), width);
    let hits: Vec<&MemWriteRecord> = writes
        .iter()
        .filter(|w| {
            w.width_bytes * 8 == width && discharge_equal(&low_bits(w.value.clone(), width), &arg)
        })
        .collect();
    let [hit] = hits.as_slice() else {
        panic!("{label}: expected one write of field {k}, found {}", hits.len())
    };
    hit.address.clone()
}

fn emit_case_text(case: &DeclaredCase, spelling: StructBase) -> (Vec<u8>, u64) {
    emit_module_text(&make_declared_module(case, spelling))
}

const SPELLINGS: [StructBase; 2] = [StructBase::UndefSeed, StructBase::Constructor];

// ===========================================================================
// TEST 12 — the interpreter lays every declared case out at its DECLARED
// offsets, which differ from declaration order: each case discriminates, and the
// oracle the next tests use is the interpreter's own layout, not a copy of the
// converter's.
// ===========================================================================

#[test]
fn declared_layout_is_the_interpreter_s_layout_and_is_not_declaration_order() {
    for case in declared_cases() {
        assert_eq!(
            interpreter_field_offsets(&case),
            case.offsets,
            "{}: the interpreter lays the slot out at the declared offsets",
            case.label
        );
        assert_ne!(
            case.offsets,
            declaration_order_offsets(&case.field_tys),
            "{}: a case whose declared offsets are declaration order cannot catch a converter \
             that ignores them",
            case.label
        );
    }
    // The item's named case, byte for byte: `b` at 0..4, `a` at 4..8.
    let reordered = &declared_cases()[0];
    let image: Vec<Option<u8>> = interpreter_slot_image(reordered);
    assert_eq!(
        image,
        [0x21, 0x22, 0x23, 0x24, 0x11, 0x12, 0x13, 0x14].map(Some).to_vec(),
        "S {{ a@4, b@0 }}: the interpreter's slot holds b then a"
    );
}

// ===========================================================================
// TEST 13 — the LIR slot is the declared size/alignment and every field's Str
// and Ldr address the interpreter's offset (both spellings of the stored value).
// ===========================================================================

#[test]
fn declared_layout_lir_slot_and_field_offsets_are_the_interpreter_s() {
    use trust_cg_lower::instructions::Value;
    for case in declared_cases() {
        let want = interpreter_field_offsets(&case);
        for spelling in SPELLINGS {
            let module = make_declared_module(&case, spelling);
            let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
                .unwrap_or_else(|e| panic!("{} ({spelling:?}) must lower: {e}", case.label));
            assert_eq!(lir.stack_slots.len(), 1, "{}: one aggregate slot", case.label);
            assert_eq!(
                (u64::from(lir.stack_slots[0].size), u64::from(lir.stack_slots[0].align)),
                (case.size, case.align),
                "{} ({spelling:?}): the slot is the declared size/alignment",
                case.label
            );
            let (stores, loads) = lir_field_offsets(&lir);
            let want_i: Vec<i64> = want.iter().map(|o| *o as i64).collect();
            let want_stores: Vec<(Value, i64)> =
                want_i.iter().enumerate().map(|(k, o)| (Value(k as u32), *o)).collect();
            assert_eq!(
                stores, want_stores,
                "{} ({spelling:?}): field k (param k) is stored at the interpreter's offset",
                case.label
            );
            assert_eq!(
                loads, want_i,
                "{} ({spelling:?}): field k is loaded from the interpreter's offset",
                case.label
            );
        }
    }
}

// ===========================================================================
// TEST 14 — the EMITTED BYTES place the fields where the interpreter does:
// the one write of each field, found by ay on its stored value, sits at the
// interpreter's offset relative to every other field's write, for every SP and
// every input (ay: UNSAT of the negated address difference).
// ===========================================================================

#[test]
fn declared_layout_bytes_write_each_field_at_the_interpreter_s_offset() {
    for case in declared_cases() {
        let want = interpreter_field_offsets(&case);
        for spelling in SPELLINGS {
            let label = format!("{} ({spelling:?})", case.label);
            let (code, base) = emit_case_text(&case, spelling);
            let writes = symbolic_memory_writes(&code, base);
            let addrs: Vec<Formula> = case
                .field_tys
                .iter()
                .enumerate()
                .map(|(k, ty)| field_write_address(&writes, k, ty, &label))
                .collect();
            for j in 0..addrs.len() {
                for k in 0..addrs.len() {
                    if j == k {
                        continue;
                    }
                    let diff =
                        Formula::BvSub(Box::new(addrs[k].clone()), Box::new(addrs[j].clone()), 64);
                    let delta = (i128::from(want[k]) - i128::from(want[j])) & 0xffff_ffff_ffff_ffff;
                    assert!(
                        discharge_equal(&diff, &Formula::BitVec { value: delta, width: 64 }),
                        "{label}: field {k}'s write is not {} bytes from field {j}'s (the \
                         interpreter's offsets {want:?})",
                        i128::from(want[k]) - i128::from(want[j])
                    );
                }
            }
        }
    }
}

// ===========================================================================
// TEST 15 — PROVEN OUTPUT: the declared-layout bytes compute f0 - f1 [+ f2] for
// ALL inputs, and are neither that +1 nor the result with lanes 0 and 1 swapped.
// ===========================================================================

#[test]
fn declared_layout_bytes_compute_the_combination_for_all_inputs() {
    for case in declared_cases() {
        let regs: Vec<u32> = (0..case.field_tys.len() as u32).collect();
        let spec = declared_combination_spec(&case.field_tys, &regs);
        let mut swapped = regs.clone();
        swapped.swap(0, 1);
        let swapped_spec = declared_combination_spec(&case.field_tys, &swapped);
        for spelling in SPELLINGS {
            let (code, base) = emit_case_text(&case, spelling);
            let out = symbolic_machine_output(&code, base);
            assert!(
                discharge_equal(&out, &spec),
                "PROVEN-OUTPUT FAILED: {} ({spelling:?}) bytes are not f0 - f1 [+ f2].\n  out = \
                 {out:?}",
                case.label
            );
            let plus_one = Formula::BvAdd(Box::new(spec.clone()), Box::new(bv32(1)), 32);
            assert!(
                !discharge_equal(&out, &plus_one),
                "VACUITY CHECK FAILED: {} ({spelling:?}) bytes 'proven' equal to the result + 1",
                case.label
            );
            assert!(
                !discharge_equal(&out, &swapped_spec),
                "LANE-ORDER VACUITY FAILED: {} ({spelling:?}) bytes also equal the result with \
                 lanes 0 and 1 swapped",
                case.label
            );
        }
    }
}

// ===========================================================================
// TEST 16 — VALUE-DIFFERENTIAL: the reference interpreter and the emitted bytes
// run the SAME constructor-spelled module on concrete inputs and agree, the
// reordered `S { a@4, b@0 }` first among them.
// ===========================================================================

#[test]
fn declared_layout_bytes_and_interpreter_agree_on_concrete_inputs() {
    let points: [[i128; 3]; 5] =
        [[7, 9, 1], [255, 1, -2], [200, -300, 0], [0, 2147483647, 1], [255, -2147483648, -1]];
    for case in declared_cases() {
        let module = make_declared_module(&case, StructBase::Constructor);
        let (code, base) = emit_module_text(&module);
        for point in points {
            // Each argument cut to its field type, as the caller passes it.
            let args: Vec<i128> = case
                .field_tys
                .iter()
                .zip(point)
                .map(|(ty, a)| match ty {
                    Ty::U8 => a & 0xff,
                    Ty::I16 => i128::from(a as i16),
                    _ => a,
                })
                .collect();
            let expected = args.iter().enumerate().fold(0i32, |acc, (k, a)| match k {
                0 => *a as i32,
                1 => acc.wrapping_sub(*a as i32),
                _ => acc.wrapping_add(*a as i32),
            });
            assert_eq!(
                interpret_struct_sum(&module, &case.field_tys, &args),
                i128::from(expected),
                "interpreter on {} {args:?}",
                case.label
            );
            let out = concrete_machine_output(&code, base, &case.field_tys, &args);
            assert!(
                discharge_equal(&out, &bv32(i128::from(expected) & 0xffff_ffff)),
                "the emitted {} bytes on {args:?} must return {expected}; got {out:?}",
                case.label
            );
        }
    }
}

// ===========================================================================
// TEST 17 — a declaration the interpreter refuses is refused, never repaired
// into a layout of the converter's own: the declared-layout reader fails closed
// on each of the interpreter's own refusal reasons.
// ===========================================================================

#[test]
fn declared_layout_the_interpreter_refuses_is_refused() {
    let base = declared_cases()[0].clone();
    let rows: [(&str, u64, u64, [u64; 2]); 4] = [
        ("misaligned field", 12, 4, [2, 8]),
        ("overlapping fields", 8, 4, [0, 0]),
        ("field past the size", 8, 4, [4, 8]),
        ("over-aligned field", 8, 2, [4, 0]),
    ];
    // A tuple descriptor on a module with no target: the interpreter refuses it
    // (`TupleLayoutTargetMissing`), so the converter must too.
    let tuple = DeclaredCase { declared: Declared::Tuple, ..base.clone() };
    let mut targetless = make_declared_module(&tuple, StructBase::Constructor);
    targetless.target_info = None;
    let args: Vec<InterpretValue> =
        [7, 9].iter().map(|a| InterpretValue::int(Ty::I32, *a).expect("arg")).collect();
    assert!(
        Interpreter::with_module(&targetless).execute_func(FuncId::new(0), args).is_err(),
        "a tuple descriptor with no target: the interpreter must refuse it"
    );
    assert!(lower_err(&targetless), "a tuple descriptor with no target must be refused");
    for declared in [Declared::Struct, Declared::Tuple] {
        for (why, size, align, offsets) in rows {
            let case =
                DeclaredCase { declared, size, align, offsets: offsets.to_vec(), ..base.clone() };
            let module = make_declared_module(&case, StructBase::Constructor);
            let args: Vec<InterpretValue> =
                [7, 9].iter().map(|a| InterpretValue::int(Ty::I32, *a).expect("arg")).collect();
            assert!(
                Interpreter::with_module(&module).execute_func(FuncId::new(0), args).is_err(),
                "{declared:?} {why}: the interpreter must refuse the declaration"
            );
            assert!(
                lower_err(&module),
                "{declared:?} {why}: the converter must refuse what the interpreter refuses"
            );
        }
    }
}

// ===========================================================================
// TESTS 18-21 — FIELD POINTERS (F1-FIELD-POINTER-AGREEMENT-1, 2026-11-10).
//
// The F1 producer spells `s.f = v` and `&s.f` on a promoted struct local as a
// FIELD POINTER: `%c = const i64 <rustc offset>; %p = gep i8 %slot, %c`, then a
// Store/Load at the field's type through `%p` (`lower_field_of_local_addr`).
// PASS 1.7 step 1b admits such a pointer only when `c` starts exactly one field
// of the slot's layout, which is the interpreter's own (CG-DECLARED-LAYOUT-1),
// and the pointer is only ever the address of a non-volatile Load/Store at that
// field's type. The cases are the declared STRUCT cases above, reordered as the
// producer declares them, plus three undeclared structs; the ORACLE for each
// field pointer's offset is the interpreter's slot image
// (`interpreter_field_offsets`), never the converter's layout. The checks:
//   18 — FILL: field k is stored through a field pointer at the interpreter's
//        offset of field k, then the struct is read WHOLE. The LIR stores param k
//        and loads field k at that offset, and the EMITTED BYTES write each field
//        at the interpreter's offset relative to every other field (ay, every SP
//        and input);
//   19 — PROVEN OUTPUT of the fill: the bytes compute f0 - f1 [+ f2] for ALL
//        inputs (+1 and lane-swap vacuity controls) and agree with the
//        interpreter on the same module on concrete inputs;
//   20 — READ: a whole store, then each field read back through its own field
//        pointer: proven for ALL inputs and agreeing with the interpreter. And a
//        fill at the DECLARATION-ORDER offsets of each reordered struct is either
//        refused or, where those offsets start fields of the declared layout,
//        agrees with the interpreter on what that different program computes;
//   21 — the interpreter-executable stand-in of TESTS 6-7
//        (`make_struct_gep_fill_module`) now lowers too, and its bytes compute the
//        field sum the interpreter computes.
// The refusals (padding, mid-field, past the end, non-constant, multi-index,
// tuple slots, any other use or access type) are the unit tests in
// `src/module_to_lir.rs`.
// ===========================================================================

/// The struct cases field pointers are checked at: every declared STRUCT case
/// above, and three undeclared structs (declaration order).
fn field_pointer_cases() -> Vec<DeclaredCase> {
    let undeclared = |label, field_tys: &[Ty], size, align, offsets: &[u64]| DeclaredCase {
        label,
        declared: Declared::Undeclared,
        field_tys: field_tys.to_vec(),
        size,
        align,
        offsets: offsets.to_vec(),
    };
    let mut cases: Vec<DeclaredCase> =
        declared_cases().into_iter().filter(|c| c.declared == Declared::Struct).collect();
    cases.push(undeclared("S { a: i32, b: i32 }", &[Ty::I32, Ty::I32], 8, 4, &[0, 4]));
    cases.push(undeclared("S { a: u8, b: i32 }", &[Ty::U8, Ty::I32], 8, 4, &[0, 4]));
    cases.push(undeclared(
        "S { a: i32, b: i32, c: i32 }",
        &[Ty::I32, Ty::I32, Ty::I32],
        12,
        4,
        &[0, 4, 8],
    ));
    cases
}

/// `%c = const i64 offset; %p = gep i8 %slot, %c`; returns `%p`.
fn push_field_pointer(bb: &mut Block, ids: &mut Ids, slot: ValueId, offset: u64) -> ValueId {
    let off = ids.next();
    bb.body.push(
        InstrNode::new(Inst::Const { ty: Ty::I64, value: Constant::Int(i128::from(offset)) })
            .with_result(off),
    );
    let ptr = ids.next();
    bb.body.push(
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I8,
            base: slot,
            indices: vec![off],
            inbounds: true,
        })
        .with_result(ptr),
    );
    ptr
}

/// `(p0, p1[, p2]) -> f0 - f1 [+ f2]` with field k FILLED through a field pointer
/// at `offsets[k]` (`s.fk = pk`), then the struct read whole.
fn make_field_pointer_fill_module(case: &DeclaredCase, offsets: &[u64]) -> Module {
    let mut module = Module::new("field_pointer_fill");
    module.func_types.push(FuncTy {
        params: case.field_tys.clone(),
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: None,
    });
    let aty = declare_aggregate(&mut module, case);
    let mut function = IrFunction::new(FuncId::new(0), "fpf", FuncTyId::new(0), BlockId::new(0));
    let mut ids = Ids(0);
    let params: Vec<ValueId> = case.field_tys.iter().map(|_| ids.next()).collect();
    let mut bb0 = Block::new(BlockId::new(0));
    for (p, ty) in params.iter().zip(&case.field_tys) {
        bb0.params.push((*p, ty.clone()));
    }
    let slot = ids.next();
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: aty.clone(), count: None, align: None })
            .with_result(slot),
    );
    for ((p, ty), offset) in params.iter().zip(&case.field_tys).zip(offsets) {
        let ptr = push_field_pointer(&mut bb0, &mut ids, slot, *offset);
        bb0.body.push(InstrNode::new(Inst::Store {
            ty: ty.clone(),
            ptr,
            value: *p,
            volatile: false,
            align: None,
        }));
    }
    let acc = push_whole_load_combination(&mut bb0, &mut ids, &aty, slot, &case.field_tys);
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    function.blocks.push(bb0);
    module.functions.push(function);
    module
}

/// `(p0, p1[, p2]) -> f0 - f1 [+ f2]` with the struct stored WHOLE (one
/// constructor) and field k READ back through a field pointer at `offsets[k]`.
fn make_field_pointer_read_module(case: &DeclaredCase, offsets: &[u64]) -> Module {
    let mut module = Module::new("field_pointer_read");
    module.func_types.push(FuncTy {
        params: case.field_tys.clone(),
        returns: vec![Ty::I32],
        is_vararg: false,
        abi: None,
    });
    let aty = declare_aggregate(&mut module, case);
    let mut function = IrFunction::new(FuncId::new(0), "fpr", FuncTyId::new(0), BlockId::new(0));
    let mut ids = Ids(0);
    let params: Vec<ValueId> = case.field_tys.iter().map(|_| ids.next()).collect();
    let mut bb0 = Block::new(BlockId::new(0));
    for (p, ty) in params.iter().zip(&case.field_tys) {
        bb0.params.push((*p, ty.clone()));
    }
    let stored = push_stored_value(&mut bb0, &mut ids, &aty, &params, StructBase::Constructor);
    let slot = ids.next();
    bb0.body.push(
        InstrNode::new(Inst::Alloca { ty: aty.clone(), count: None, align: None })
            .with_result(slot),
    );
    bb0.body.push(InstrNode::new(Inst::Store {
        ty: aty,
        ptr: slot,
        value: stored,
        volatile: false,
        align: None,
    }));
    let mut fields = Vec::new();
    for (ty, offset) in case.field_tys.iter().zip(offsets) {
        let ptr = push_field_pointer(&mut bb0, &mut ids, slot, *offset);
        let read = ids.next();
        bb0.body.push(
            InstrNode::new(Inst::Load { ty: ty.clone(), ptr, volatile: false, align: None })
                .with_result(read),
        );
        fields.push((read, ty.clone()));
    }
    let acc = push_combination(&mut bb0, &mut ids, &fields);
    bb0.body.push(InstrNode::new(Inst::Return { values: vec![acc] }));
    function.blocks.push(bb0);
    module.functions.push(function);
    module
}

/// Each argument cut to its field type, as the caller passes it.
fn cut_to_field_types(field_tys: &[Ty], point: [i128; 3]) -> Vec<i128> {
    field_tys
        .iter()
        .zip(point)
        .map(|(ty, a)| match ty {
            Ty::U8 => a & 0xff,
            Ty::I16 => i128::from(a as i16),
            _ => a,
        })
        .collect()
}

/// `a0 - a1 [+ a2]` in wrapping i32 for the arguments of `lanes[k]`.
fn combination_of(args: &[i128], lanes: &[usize]) -> i32 {
    lanes.iter().enumerate().fold(0i32, |acc, (k, lane)| match k {
        0 => args[*lane] as i32,
        1 => acc.wrapping_sub(args[*lane] as i32),
        _ => acc.wrapping_add(args[*lane] as i32),
    })
}

const FIELD_POINTER_POINTS: [[i128; 3]; 5] =
    [[7, 9, 1], [255, 1, -2], [200, -300, 0], [0, 2147483647, 1], [255, -2147483648, -1]];

/// The interpreter and the emitted bytes of `module` agree on the concrete
/// points, and both return `a[lanes[0]] - a[lanes[1]] [+ a[lanes[2]]]`.
fn assert_interpreter_and_bytes_agree(module: &Module, case: &DeclaredCase, lanes: &[usize]) {
    let (code, base) = emit_module_text(module);
    for point in FIELD_POINTER_POINTS {
        let args = cut_to_field_types(&case.field_tys, point);
        let expected = combination_of(&args, lanes);
        assert_eq!(
            interpret_struct_sum(module, &case.field_tys, &args),
            i128::from(expected),
            "interpreter on {} {args:?}",
            case.label
        );
        let out = concrete_machine_output(&code, base, &case.field_tys, &args);
        assert!(
            discharge_equal(&out, &bv32(i128::from(expected) & 0xffff_ffff)),
            "the emitted {} bytes on {args:?} must return {expected}; got {out:?}",
            case.label
        );
    }
}

// ===========================================================================
// TEST 18 — FILL through field pointers: the LIR addresses and the emitted
// bytes' writes sit at the interpreter's offsets.
// ===========================================================================

#[test]
fn field_pointer_fill_lir_and_bytes_address_the_interpreter_s_offsets() {
    use trust_cg_lower::instructions::Value;
    for case in field_pointer_cases() {
        let want = interpreter_field_offsets(&case);
        assert_eq!(want, case.offsets, "{}: the interpreter's offsets", case.label);
        let module = make_field_pointer_fill_module(&case, &want);
        let lir = lower_trust_ir_function_to_lir(&module, &module.functions[0])
            .unwrap_or_else(|e| panic!("{}: the field-pointer fill must lower: {e}", case.label));
        assert_eq!(lir.stack_slots.len(), 1, "{}: one aggregate slot", case.label);
        assert_eq!(
            (u64::from(lir.stack_slots[0].size), u64::from(lir.stack_slots[0].align)),
            (case.size, case.align),
            "{}: the slot is the interpreter's size/alignment",
            case.label
        );
        let (stores, loads) = lir_field_offsets(&lir);
        let want_i: Vec<i64> = want.iter().map(|o| *o as i64).collect();
        let want_stores: Vec<(Value, i64)> =
            want_i.iter().enumerate().map(|(k, o)| (Value(k as u32), *o)).collect();
        assert_eq!(
            stores, want_stores,
            "{}: param k is stored through field k's pointer at the interpreter's offset",
            case.label
        );
        assert_eq!(loads, want_i, "{}: the whole load reads field k there", case.label);

        let (code, base) = emit_module_text(&module);
        let writes = symbolic_memory_writes(&code, base);
        let addrs: Vec<Formula> = case
            .field_tys
            .iter()
            .enumerate()
            .map(|(k, ty)| field_write_address(&writes, k, ty, case.label))
            .collect();
        for j in 0..addrs.len() {
            for k in 0..addrs.len() {
                if j == k {
                    continue;
                }
                let diff =
                    Formula::BvSub(Box::new(addrs[k].clone()), Box::new(addrs[j].clone()), 64);
                let delta = (i128::from(want[k]) - i128::from(want[j])) & 0xffff_ffff_ffff_ffff;
                assert!(
                    discharge_equal(&diff, &Formula::BitVec { value: delta, width: 64 }),
                    "{}: field {k}'s field-pointer write is not {} bytes from field {j}'s (the \
                     interpreter's offsets {want:?})",
                    case.label,
                    i128::from(want[k]) - i128::from(want[j])
                );
            }
        }
    }
}

// ===========================================================================
// TEST 19 — PROVEN OUTPUT of the fill, and interpreter agreement on it.
// ===========================================================================

#[test]
fn field_pointer_fill_bytes_compute_the_combination_and_agree_with_the_interpreter() {
    for case in field_pointer_cases() {
        let want = interpreter_field_offsets(&case);
        let module = make_field_pointer_fill_module(&case, &want);
        let (code, base) = emit_module_text(&module);
        let out = symbolic_machine_output(&code, base);
        let regs: Vec<u32> = (0..case.field_tys.len() as u32).collect();
        let spec = declared_combination_spec(&case.field_tys, &regs);
        assert!(
            discharge_equal(&out, &spec),
            "PROVEN-OUTPUT FAILED: {} field-pointer fill bytes are not f0 - f1 [+ f2].\n  out = \
             {out:?}",
            case.label
        );
        let plus_one = Formula::BvAdd(Box::new(spec), Box::new(bv32(1)), 32);
        assert!(
            !discharge_equal(&out, &plus_one),
            "VACUITY CHECK FAILED: {} field-pointer fill bytes 'proven' equal to the result + 1",
            case.label
        );
        let mut swapped = regs.clone();
        swapped.swap(0, 1);
        assert!(
            !discharge_equal(&out, &declared_combination_spec(&case.field_tys, &swapped)),
            "LANE-ORDER VACUITY FAILED: {} field-pointer fill bytes also equal the result with \
             lanes 0 and 1 swapped",
            case.label
        );
        let lanes: Vec<usize> = (0..case.field_tys.len()).collect();
        assert_interpreter_and_bytes_agree(&module, &case, &lanes);
    }
}

// ===========================================================================
// TEST 20 — READ through field pointers after a whole store; and a fill at the
// declaration-order offsets of a reordered struct.
// ===========================================================================

#[test]
fn field_pointer_reads_compute_the_combination_and_agree_with_the_interpreter() {
    for case in field_pointer_cases() {
        let want = interpreter_field_offsets(&case);
        let module = make_field_pointer_read_module(&case, &want);
        let (code, base) = emit_module_text(&module);
        let out = symbolic_machine_output(&code, base);
        let regs: Vec<u32> = (0..case.field_tys.len() as u32).collect();
        let spec = declared_combination_spec(&case.field_tys, &regs);
        assert!(
            discharge_equal(&out, &spec),
            "PROVEN-OUTPUT FAILED: {} field-pointer read bytes are not f0 - f1 [+ f2].\n  out = \
             {out:?}",
            case.label
        );
        let mut swapped = regs.clone();
        swapped.swap(0, 1);
        assert!(
            !discharge_equal(&out, &declared_combination_spec(&case.field_tys, &swapped)),
            "LANE-ORDER VACUITY FAILED: {} field-pointer read bytes also equal the result with \
             lanes 0 and 1 swapped",
            case.label
        );
        let lanes: Vec<usize> = (0..case.field_tys.len()).collect();
        assert_interpreter_and_bytes_agree(&module, &case, &lanes);
    }
}

/// A fill at each reordered struct's DECLARATION-ORDER offsets is a different
/// program: a declaration-order converter would read it as `s.fk = pk`. Where
/// such an offset starts no field of the declared layout, or a field of another
/// type, the converter refuses it; where every offset starts a field of the
/// declared layout at the stored type (`S { a: i32 @4, b: i32 @0 }`: offset 0 is
/// `b`, 4 is `a`), it lowers, and the bytes compute what the interpreter
/// computes for it: `p1 - p0`, not `p0 - p1`. Both outcomes occur.
#[test]
fn field_pointer_fill_at_declaration_order_offsets_is_refused_or_agrees_with_the_interpreter() {
    let (mut refused, mut agreed) = (0usize, 0usize);
    for case in declared_cases().into_iter().filter(|c| c.declared == Declared::Struct) {
        let want = interpreter_field_offsets(&case);
        let order = declaration_order_offsets(&case.field_tys);
        assert_ne!(order, want, "{}: the case must discriminate", case.label);
        let module = make_field_pointer_fill_module(&case, &order);
        match lower_trust_ir_function_to_lir(&module, &module.functions[0]) {
            Err(e) => {
                let why = e.to_string();
                assert!(
                    why.contains("aggregate slot") || why.contains("field pointer"),
                    "{}: refused, but not by the slot/field-pointer guard: {why}",
                    case.label
                );
                refused += 1;
            }
            Ok(_) => {
                // Param k lands in the declared field that starts at `order[k]`.
                let lanes: Vec<usize> = (0..case.field_tys.len())
                    .map(|field| {
                        order.iter().position(|o| *o == want[field]).unwrap_or_else(|| {
                            panic!("{}: field {field} is written by no param", case.label)
                        })
                    })
                    .collect();
                assert_ne!(
                    lanes,
                    (0..case.field_tys.len()).collect::<Vec<_>>(),
                    "{}: the declaration-order program must permute the lanes",
                    case.label
                );
                assert_interpreter_and_bytes_agree(&module, &case, &lanes);
                agreed += 1;
            }
        }
    }
    assert!(refused > 0 && agreed > 0, "refused {refused}, agreed {agreed}: both must occur");
}

// ===========================================================================
// TEST 21 — the interpreter-executable stand-in of TESTS 6-7 lowers now: its
// bytes compute the field sum for ALL inputs, as the interpreter does.
// ===========================================================================

#[test]
fn struct_gep_fill_stand_in_lowers_and_its_bytes_compute_the_field_sum() {
    for n in [2usize, 3] {
        let field_tys = vec![Ty::I32; n];
        let module = make_struct_gep_fill_module(&field_tys);
        let (code, base) = emit_module_text(&module);
        let out = symbolic_machine_output(&code, base);
        assert!(
            discharge_equal(&out, &field_sum_spec(n)),
            "PROVEN-OUTPUT FAILED: the {n}-field gep-fill bytes are not the field sum.\n  out = \
             {out:?}"
        );
        assert!(
            !discharge_equal(&out, &field_sum_plus_one_spec(n)),
            "VACUITY CHECK FAILED: the {n}-field gep-fill bytes 'proven' equal to the sum + 1"
        );
        for point in [[5i128, 7, 9], [-3, 10, 2147483647], [100, -50, -2147483648]] {
            let args = &point[..n];
            let expected = args.iter().fold(0i32, |acc, a| acc.wrapping_add(*a as i32));
            assert_eq!(interpret_struct_gep_fill(&module, args), i128::from(expected));
            let out = concrete_machine_output(&code, base, &field_tys, args);
            assert!(
                discharge_equal(&out, &bv32(i128::from(expected) & 0xffff_ffff)),
                "the {n}-field gep-fill bytes on {args:?} must return {expected}; got {out:?}"
            );
        }
    }
}
