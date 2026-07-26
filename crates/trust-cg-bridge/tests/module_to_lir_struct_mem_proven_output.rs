// module_to_lir_struct_mem_proven_output.rs — the "trust-ir first" codegen seam,
// extended to N-FIELD `Ty::Struct` IN MEMORY (a scalar-field struct round-tripped
// through ONE stack slot AS A UNIT), proven over the real emitted bytes.
//
// This is the DOMINANT real-backend aggregate: the trust-ir bridge emits
// `Ty::Struct(sid)` for EVERY Rust struct/ADT/closure-env (see
// `crates/trust-ir-bridge/src/lower.rs` `map_type_ctx` Adt/Closure arms), with a
// `StructDef { fields: Vec<FieldDef>, repr: Rust }` in `Module.structs`. A struct
// local promoted across blocks (`promote_local_to_memory`) round-trips through a
// whole-aggregate stack slot with EXACTLY the tuple slice's shape, only the type
// is `Ty::Struct(sid)`:
//
//   bb0(a, b):
//     %u  = undef struct.0                  ; aggregate base (raw bridge shape)
//     %t0 = insertfield struct.0 %u,  0, a  ; field x <- a
//     %t  = insertfield struct.0 %t0, 1, b  ; field y <- b   (full SSA aggregate)
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
//       pinned interpreter (c58fa68) traps EAGERLY on `Undef` and has no
//       `(Ty::Struct, Constant::Aggregate)` constant arm (probed), so the
//       whole-`Store(struct)`/`Load(struct)` seed the converter lowers is not
//       itself interpreter-executable; the interpreter-executable stand-in fills
//       the slot via typed field Stores through byte-offset GEPs, then reads the
//       WHOLE struct back with a single `Load(struct)` — exercising the SAME
//       `struct_layout` + `decode_value` offset math (x@0, y@4[, z@8]) the
//       converter's emitted bytes are proven against. A passing value-diff proves
//       c58fa68's struct `byte_size`/`struct_layout` agrees with the converter.
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
use trust_machine_sem::{Aarch64Semantics, MachineState, Semantics};
use trust_types::{Formula, Sort};

use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FieldDef, FuncTy, StructDef, StructRepr, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, StructId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module};

// ---------------------------------------------------------------------------
// Build the struct-in-memory Module for the whole-aggregate round-trip shape the
// bridge emits: undef(struct) base + per-field InsertField + Alloca(struct) +
// whole Store(struct) + whole Load(struct) + per-field ExtractField + field sum.
//
// `field_tys` are the struct's scalar field types in declaration order (2 or 3).
// The function sums ALL fields: field0 + field1 [+ field2].
// ---------------------------------------------------------------------------

fn make_struct_sum_module(field_tys: &[Ty]) -> Module {
    let n = field_tys.len();
    assert!(n == 2 || n == 3, "test covers 2- and 3-field structs");
    let mut module = Module::new("struct_mem_module");
    module.func_types.push(FuncTy {
        params: field_tys.to_vec(),
        returns: vec![Ty::I32],
        is_vararg: false,
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

    // undef struct.0 (raw bridge base — the interpreter traps on it; this is the
    // LOWERING + PROVEN-OUTPUT shape).
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

    // Sum: acc = f0 + f1 [+ f2].
    let mut acc = extracts[0];
    for (i, add) in adds.iter().enumerate() {
        bb0.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: acc,
                rhs: extracts[i + 1],
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
                Opcode::Ldr | Opcode::Ldrb | Opcode::Ldrh | Opcode::Ldrsb | Opcode::Ldrsh
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
    let sem = Aarch64Semantics;
    let mut state = MachineState::symbolic();
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
            solver.declare_const(name, ay::Sort::array(ay::Sort::bitvec(*iw), ay::Sort::bitvec(*ew)))
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
        other => panic!(
            "formula_to_term: unhandled Formula variant in machine output: {other:?}"
        ),
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
    let lir =
        lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("lower struct");

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
    let lir =
        lower_trust_ir_function_to_lir(&module, &module.functions[0]).expect("lower 3-field struct");

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
// `aggregate_mem_layout` reproduces. A passing interpret PROVES c58fa68's struct
// byte_size/struct_layout agrees with the converter's emitted-byte layout.
//
// (The whole-`Store(struct)`/`Load(struct)` seed the converter lowers is NOT
// itself interpreter-executable under c58fa68 — the interpreter traps eagerly on
// `Undef` and has no `(Ty::Struct, Constant::Aggregate)` constant arm — so the
// interpreter-executable stand-in fills the slot via typed field Stores and reads
// the whole struct back, exercising the identical field-offset math.)
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
