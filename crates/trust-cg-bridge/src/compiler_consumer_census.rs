//! The F1 consumer census: the same `trust_ir::Module`s through BOTH codegen
//! consumers — the frozen `module_to_lir` (F1 today) and trust-cg's
//! `Compiler::compile` (R-5's one consumer) — for both AArch64 triples, plus a
//! JIT-vs-reference-interpreter value check wherever trust-cg compiles.
//!
//! The rendered census IS `docs/audits/2026-09-30-f1-consumer-census.md`:
//! [`census_matches_the_committed_audit`] fails when the two differ.
//! Regenerate with `TRUST_REGEN_F1_CONSUMER_CENSUS=1` and review the diff.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;
use std::path::PathBuf;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{
    CodegenLicensePolicy, CompileError, Compiler, CompilerConfig, ExecutableBuffer,
    UnlicensedBodyPolicy,
};
use trust_cg_lower::AdapterError;
use trust_ir::inst::{BinOp, Inst};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FieldDef, FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, StructId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Linkage, Module, StructDef};

use super::{
    ViaCompilerError, ViaCompilerTarget, compile_trust_ir_module_via_compiler,
    compile_unchecked_boundary, jit_trust_ir_module_via_compiler, refuse_f1_boundary,
};
use crate::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};
use crate::module_to_lir::{function_has_unfaithful_assert, lower_module_to_lir};

const AUDIT: &str = "docs/audits/2026-09-30-f1-consumer-census.md";
const REGEN_ENV: &str = "TRUST_REGEN_F1_CONSUMER_CENSUS";
const FIXTURES: [&str; 3] = ["m1probe", "m1bounds", "m1shift"];

/// The codegen license every census compile states: trust-cg's default with
/// claim-less bodies PERMITTED.
///
/// Every subject is claim-less (`body_gate: None`): the `direct_shadow`
/// fixtures were minted on 2026-08-31, before the direct lane stamped
/// `trust-direct-lane-structural` on its bodies, and the hand-built modules
/// state no claim. The census measures which SHAPES each consumer lowers, not
/// licensing, and trust-cg's default refuses every claim-less body by its
/// license (DG-73) before any shape is judged, so it states `Permit`, as
/// trust-cg's own tests do for their hand-built fixtures (LD-W7-1). The negative
/// control [`the_default_license_refuses_the_claim_less_subjects`] pins that the
/// default still refuses them. Nothing here reaches a lane: the shipping
/// consumer compiles under the D31 license (`f1_compile::f1_codegen_license`).
fn census_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn fixture(name: &str) -> Module {
    let path = repo_root()
        .join("crates/trust-bmc/tests/fixtures/direct_shadow")
        .join(name)
        .join("module.trust-ir.bin");
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|e| panic!("decode {}: {e:?}", path.display()))
}

// ---------------------------------------------------------------------------
// Hand-built modules: one shape per R-8 axis the fixtures do not reach.
// ---------------------------------------------------------------------------

fn function(
    id: u32,
    name: &str,
    ty: u32,
    params: &[(u32, Ty)],
    body: Vec<InstrNode>,
) -> IrFunction {
    let mut f = IrFunction::new(FuncId::new(id), name, FuncTyId::new(ty), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    for (v, t) in params {
        b.params.push((ValueId::new(*v), t.clone()));
    }
    b.body = body;
    f.blocks.push(b);
    f
}

fn binop(op: BinOp, ty: Ty, lhs: u32, rhs: u32, out: u32) -> InstrNode {
    InstrNode::new(Inst::BinOp { op, ty, lhs: ValueId::new(lhs), rhs: ValueId::new(rhs) })
        .with_result(ValueId::new(out))
}

fn constant(ty: Ty, value: Constant, out: u32) -> InstrNode {
    InstrNode::new(Inst::Const { ty, value }).with_result(ValueId::new(out))
}

fn ret(v: u32) -> InstrNode {
    InstrNode::new(Inst::Return { values: vec![ValueId::new(v)] })
}

fn binary_fn_ty(module: &mut Module, ty: Ty) {
    module.func_types.push(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty],
        is_vararg: false,
        abi: None,
    });
}

/// `entry(a, b) = mix(a, b) & 0xff` with `mix(a, b) = (a ^ b) | 1` an
/// `Internal` function reached by a DIRECT `Call` — no `Assert` anywhere.
fn internal_call_module() -> Module {
    let mut m = Module::new("hand_internal_call");
    binary_fn_ty(&mut m, Ty::I64);
    let mut mix = function(
        0,
        "hand_mix",
        0,
        &[(0, Ty::I64), (1, Ty::I64)],
        vec![
            binop(BinOp::Xor, Ty::I64, 0, 1, 2),
            constant(Ty::I64, Constant::Int(1), 3),
            binop(BinOp::Or, Ty::I64, 2, 3, 4),
            ret(4),
        ],
    );
    mix.linkage = Linkage::Internal;
    let entry = function(
        1,
        "hand_entry",
        0,
        &[(0, Ty::I64), (1, Ty::I64)],
        vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            constant(Ty::I64, Constant::Int(0xff), 3),
            binop(BinOp::And, Ty::I64, 2, 3, 4),
            ret(4),
        ],
    );
    m.functions.push(mix);
    m.functions.push(entry);
    m
}

/// `fma_ish(a, b) = a * b + 1.5` over `f64`.
fn f64_module() -> Module {
    let mut m = Module::new("hand_f64");
    binary_fn_ty(&mut m, Ty::F64);
    m.functions.push(function(
        0,
        "hand_f64_mul_add",
        0,
        &[(0, Ty::F64), (1, Ty::F64)],
        vec![
            binop(BinOp::FMul, Ty::F64, 0, 1, 2),
            constant(Ty::F64, Constant::Float(1.5), 3),
            binop(BinOp::FAdd, Ty::F64, 2, 3, 4),
            ret(4),
        ],
    ));
    m
}

/// `wide(a, b) = (a + b) ^ a` over `i128`, wrapping `Add` (no `Assert`).
fn i128_module() -> Module {
    let mut m = Module::new("hand_i128");
    binary_fn_ty(&mut m, Ty::I128);
    m.functions.push(function(
        0,
        "hand_i128_add_xor",
        0,
        &[(0, Ty::I128), (1, Ty::I128)],
        vec![binop(BinOp::Add, Ty::I128, 0, 1, 2), binop(BinOp::Xor, Ty::I128, 2, 0, 3), ret(3)],
    ));
    m
}

/// `pair(s: S) -> u64 { s.a ^ s.b }`, `S = { a: u64 @0, b: u64 @8 }` passed BY
/// VALUE (16 bytes, two plain scalars: the register-pair shape).
fn by_value_struct_module() -> Module {
    let mut m = Module::new("hand_by_value_struct");
    m.structs.push(StructDef {
        id: StructId::new(0),
        name: "S".to_string(),
        fields: vec![
            FieldDef { name: "a".to_string(), ty: Ty::U64, offset: Some(0) },
            FieldDef { name: "b".to_string(), ty: Ty::U64, offset: Some(8) },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    });
    let s = Ty::Struct(StructId::new(0));
    m.func_types.push(FuncTy {
        params: vec![s.clone()],
        returns: vec![Ty::U64],
        is_vararg: false,
        abi: None,
    });
    m.functions.push(function(
        0,
        "hand_struct_xor",
        0,
        &[(0, s)],
        vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: ValueId::new(0),
                field: 0,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: ValueId::new(0),
                field: 1,
            })
            .with_result(ValueId::new(2)),
            binop(BinOp::Xor, Ty::U64, 1, 2, 3),
            ret(3),
        ],
    ));
    m
}

/// The NEGATIVE TWIN of the internal-call row: the same callee carrying an
/// overflow-checked `i64` add (`Overflow` + `Select` + `Assert`), so the
/// `Assert` reaches the caller only through the call edge.
fn callee_assert_module() -> Module {
    let mut m = internal_call_module();
    m.name = "hand_callee_assert".to_string();
    let mix = &mut m.functions[0];
    mix.name = "hand_mix_checked".to_string();
    mix.blocks[0].body = vec![
        InstrNode::new(Inst::Overflow {
            op: trust_ir::inst::OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_results([ValueId::new(2), ValueId::new(3)]),
        constant(Ty::Bool, Constant::Bool(false), 4),
        constant(Ty::Bool, Constant::Bool(true), 5),
        InstrNode::new(Inst::Select {
            ty: Ty::Bool,
            cond: ValueId::new(3),
            then_val: ValueId::new(4),
            else_val: ValueId::new(5),
        })
        .with_result(ValueId::new(6)),
        // The kind the producer gives this check (trust-ir v52): the `i64` add overflow.
        InstrNode::new(Inst::Assert {
            cond: ValueId::new(6),
            kind: trust_ir::AssertKind::Overflow(trust_ir::AssertOverflowOp::Add),
            site: None,
        }),
        ret(2),
    ];
    m.functions[1].name = "hand_entry_calls_checked".to_string();
    m
}

fn subjects() -> Vec<(String, Module)> {
    let mut out: Vec<(String, Module)> =
        FIXTURES.iter().map(|n| (format!("direct_shadow/{n}"), fixture(n))).collect();
    out.push(("hand: direct Internal call".to_string(), internal_call_module()));
    out.push(("hand: callee carries Assert".to_string(), callee_assert_module()));
    out.push(("hand: f64".to_string(), f64_module()));
    out.push(("hand: i128".to_string(), i128_module()));
    out.push(("hand: by-value struct".to_string(), by_value_struct_module()));
    out
}

// ---------------------------------------------------------------------------
// Per-function isolation, so a module-granular consumer gets a per-function
// verdict: every body except the subject and its transitive direct callees
// becomes a declaration. A demoted body takes with it what only a body can
// carry: its debug value names and lexical scopes (a declaration defines no
// value) and the proof obligations sited in it or scoped to it (their sites
// name blocks that are gone). trust-ir's validator, which trust-cg's ingestion
// admission runs since WS7.3, refuses both leftovers (`InvalidValueName`,
// `ObligationSiteOutOfRange`); before WS7.3 trust-cg compiled past them.
// ---------------------------------------------------------------------------

fn isolate(module: &Module, id: FuncId) -> Module {
    let mut keep = BTreeSet::from([id.index()]);
    let mut work = vec![id];
    while let Some(f) = work.pop() {
        let Some(func) = module.function_by_id(f) else { continue };
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::Call { callee, .. } = &node.inst
                && keep.insert(callee.index())
            {
                work.push(*callee);
            }
        }
    }
    let mut out = module.clone();
    for f in &mut out.functions {
        if !keep.contains(&f.id.index()) {
            f.blocks.clear();
            f.value_names = None;
            f.scopes = None;
            if matches!(f.linkage, Linkage::Internal | Linkage::Private) {
                f.linkage = Linkage::External;
            }
        }
    }
    out.proof_obligations.retain(|o| {
        let kept = |f: FuncId| keep.contains(&f.index());
        o.site.as_ref().is_none_or(|site| kept(site.function)) && o.function.is_none_or(kept)
    });
    out
}

/// `module` as `Compiler` compiles it for `triple`: unchanged, unless it has
/// an FFI boundary and no `target_info`, when it states `triple` (8-byte
/// pointers, little-endian, `NativeC` struct passing: the C ABI trust-cg lowers
/// a target-free module by). Isolation turns a neighbour body into a bodyless
/// declaration, an FFI boundary, and trust-cg's ingestion admission refuses an
/// untargeted one (`TargetInfoRequired`, WS7.3) rather than guess its ABI; a
/// caller that compiles for a known target names it (trust-cg LD-53). The
/// `direct_shadow` fixtures carry their own target and are never restamped.
fn for_target(module: &Module, triple: &str) -> Module {
    let mut out = module.clone();
    if out.target_info.is_none() && out.requires_target_info() {
        out.target_info = Some(trust_ir::TargetInfo {
            triple: triple.to_string(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
    }
    out
}

/// [`for_target`] at the host's triple, for the host JIT (on a host outside
/// [`ViaCompilerTarget::ALL`] the JIT refuses before reading the module).
fn for_host_jit(module: &Module) -> Module {
    ViaCompilerTarget::host()
        .map_or_else(|| module.clone(), |host| for_target(module, host.triple()))
}

// ---------------------------------------------------------------------------
// Values: the input grid, the interpreter, and the JIT call.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
enum Arg {
    I(i128),
    F(f64),
    Pair(u64, u64),
}

fn int_grid(ty: &Ty) -> Option<Vec<i128>> {
    Some(match ty {
        Ty::I32 => vec![0, 1, -1, 2, 7, -7, 0x55, 1000, i32::MIN.into(), i32::MAX.into()],
        Ty::U32 => vec![0, 1, 2, 7, 31, 32, 33, 0x55, u32::MAX.into(), (u32::MAX - 1).into()],
        Ty::I64 => vec![0, 1, -1, 7, 0x55, -1000, i64::MIN.into(), i64::MAX.into()],
        Ty::U64 | Ty::Usize => vec![0, 1, 7, 63, 64, 0x55, u64::MAX.into(), (u64::MAX - 1).into()],
        Ty::I128 => vec![0, 1, -1, 0x55, 1 << 64, -(1 << 70) + 3, i128::MIN, i128::MAX],
        _ => return None,
    })
}

const F_GRID: [f64; 8] = [0.0, -0.0, 1.5, -2.25, 1e300, f64::INFINITY, f64::NAN, f64::MIN_POSITIVE];

fn axis(module: &Module, ty: &Ty) -> Option<Vec<Arg>> {
    if let Some(g) = int_grid(ty) {
        return Some(g.into_iter().map(Arg::I).collect());
    }
    match ty {
        Ty::F64 => Some(F_GRID.iter().map(|f| Arg::F(*f)).collect()),
        Ty::Struct(sid) => {
            let def = module.structs.get(sid.as_usize())?;
            let plain = def.fields.len() == 2
                && def.fields.iter().all(|f| f.ty == Ty::U64)
                && def.fields[0].offset == Some(0)
                && def.fields[1].offset == Some(8);
            plain.then(|| {
                let g = int_grid(&Ty::U64).unwrap_or_default();
                g.iter()
                    .flat_map(|a| g.iter().map(move |b| Arg::Pair(*a as u64, *b as u64)))
                    .collect()
            })
        }
        _ => None,
    }
}

/// The input grid for `sig`, or `None` when a parameter or the return is
/// outside what [`call_jit`] can pass.
fn grid(module: &Module, sig: &FuncTy) -> Option<Vec<Vec<Arg>>> {
    let [ret] = sig.returns.as_slice() else { return None };
    int_grid(ret).map(|_| ()).or((*ret == Ty::F64).then_some(()))?;
    match sig.params.as_slice() {
        [] => Some(vec![vec![]]),
        [p] => Some(axis(module, p)?.into_iter().map(|a| vec![a]).collect()),
        [p, q] if p == q => {
            let a = axis(module, p)?;
            Some(a.iter().flat_map(|x| a.iter().map(move |y| vec![*x, *y])).collect())
        }
        _ => None,
    }
}

fn to_interp(ty: &Ty, arg: Arg) -> InterpretValue {
    match arg {
        Arg::I(v) => InterpretValue::int(ty.clone(), v).expect("grid value fits its type"),
        Arg::F(f) => {
            InterpretValue { ty: ty.clone(), kind: InterpretValueKind::FloatBits(f.to_bits()) }
        }
        Arg::Pair(a, b) => InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::Aggregate(vec![
                InterpretValue::int(Ty::U64, a.into()).expect("u64"),
                InterpretValue::int(Ty::U64, b.into()).expect("u64"),
            ]),
        },
    }
}

/// A result as raw bits at the return type's width, for exact comparison.
fn interp_bits(v: &InterpretValue) -> Option<u128> {
    match &v.kind {
        InterpretValueKind::Int(i) => Some(i.as_unsigned()),
        InterpretValueKind::FloatBits(b) => Some(u128::from(*b)),
        _ => None,
    }
}

fn width_mask(ty: &Ty) -> u128 {
    match ty {
        Ty::I32 | Ty::U32 => u128::from(u32::MAX),
        Ty::I128 => u128::MAX,
        _ => u128::from(u64::MAX),
    }
}

/// Call the JIT'd function at `ptr` with `args` per `sig`; the result as bits.
///
/// # Safety
/// `ptr` must be the entry of a function trust-cg compiled for `sig` in a live
/// executable buffer.
unsafe fn call_jit(ptr: *const u8, sig: &FuncTy, args: &[Arg]) -> u128 {
    macro_rules! call {
        ($fty:ty, $($a:expr),*) => {{
            let f: $fty = unsafe { std::mem::transmute::<*const u8, $fty>(ptr) };
            f($($a),*)
        }};
    }
    let ret = &sig.returns[0];
    match (sig.params.as_slice(), args) {
        ([], []) => match ret {
            Ty::I32 | Ty::U32 => u128::from(call!(extern "C" fn() -> u32,)),
            Ty::I128 => call!(extern "C" fn() -> u128,),
            Ty::F64 => u128::from(call!(extern "C" fn() -> f64,).to_bits()),
            _ => u128::from(call!(extern "C" fn() -> u64,)),
        },
        ([Ty::Struct(_)], [Arg::Pair(a, b)]) => {
            u128::from(call!(extern "C" fn(u64, u64) -> u64, *a, *b))
        }
        ([Ty::F64, Ty::F64], [Arg::F(a), Arg::F(b)]) => {
            u128::from(call!(extern "C" fn(f64, f64) -> f64, *a, *b).to_bits())
        }
        ([Ty::I32 | Ty::U32, _], [Arg::I(a), Arg::I(b)]) => {
            u128::from(call!(extern "C" fn(u32, u32) -> u32, *a as u32, *b as u32))
        }
        ([Ty::I128, _], [Arg::I(a), Arg::I(b)]) => {
            call!(extern "C" fn(u128, u128) -> u128, *a as u128, *b as u128)
        }
        ([_, _], [Arg::I(a), Arg::I(b)]) => {
            u128::from(call!(extern "C" fn(u64, u64) -> u64, *a as u64, *b as u64))
        }
        ([_], [Arg::I(a)]) => u128::from(call!(extern "C" fn(u64) -> u64, *a as u64)),
        _ => unreachable!("grid() admitted a signature call_jit cannot pass"),
    }
}

#[derive(Default)]
struct Agreement {
    agree: usize,
    disagree: Vec<String>,
    /// Inputs the interpreter rejected: a failed `Assert` (a panic), or UB.
    skipped_panic: usize,
    skipped_other: usize,
}

impl Agreement {
    fn render(&self) -> String {
        let mut s = format!("{} agree", self.agree);
        if !self.disagree.is_empty() {
            let _ =
                write!(s, ", **{} DISAGREE** (first: {})", self.disagree.len(), self.disagree[0]);
        }
        if self.skipped_panic > 0 {
            let _ = write!(s, "; {} skipped (interpreter: failed `Assert`)", self.skipped_panic);
        }
        if self.skipped_other > 0 {
            let _ = write!(s, "; {} skipped (interpreter: other error)", self.skipped_other);
        }
        s
    }
}

fn agreement(module: &Module, id: FuncId, buffer: &ExecutableBuffer) -> Result<Agreement, String> {
    let func = module.function_by_id(id).ok_or("no function")?;
    let sig = module.func_types.get(func.ty.as_usize()).ok_or("no func type")?;
    let inputs = grid(module, sig).ok_or("signature outside the JIT runner")?;
    let ptr = buffer
        .get_fn_ptr_bound(&func.name)
        .ok_or_else(|| format!("symbol `{}` absent from the JIT buffer", func.name))?
        .as_ptr();
    let interp = Interpreter::with_module(module);
    let mut out = Agreement::default();
    for args in inputs {
        let ivals: Vec<InterpretValue> =
            sig.params.iter().zip(&args).map(|(t, a)| to_interp(t, *a)).collect();
        let expected = match interp.execute_func(id, ivals) {
            Ok(outcome) => outcome.returns.first().and_then(interp_bits),
            Err(e) if e.code == InterpretErrorCode::Panic => {
                out.skipped_panic += 1;
                continue;
            }
            Err(_) => {
                out.skipped_other += 1;
                continue;
            }
        };
        let Some(expected) = expected else {
            out.skipped_other += 1;
            continue;
        };
        // SAFETY: `ptr` is `func`'s entry in the live `buffer`, compiled for `sig`.
        let got = unsafe { call_jit(ptr, sig, &args) };
        let ret = &sig.returns[0];
        let same = if *ret == Ty::F64 {
            let (g, e) = (f64::from_bits(got as u64), f64::from_bits(expected as u64));
            (g.is_nan() && e.is_nan()) || got == expected
        } else {
            got & width_mask(ret) == expected & width_mask(ret)
        };
        if same {
            out.agree += 1;
        } else {
            out.disagree.push(format!("{args:?}: jit {got:#x} != interp {expected:#x}"));
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// The census.
// ---------------------------------------------------------------------------

fn class<T, E>(r: &Result<T, E>, name: impl Fn(&E) -> String) -> String {
    match r {
        Ok(_) => "accept".to_string(),
        Err(e) => format!("refuse `{}`", name(e)),
    }
}

fn module_to_lir_row(module: &Module, id: FuncId) -> (String, Vec<String>) {
    match lower_module_to_lir(module, id) {
        Err(e) => (format!("refuse `{}`", e.class_name()), vec![]),
        Ok(lir) => {
            let emits = ViaCompilerTarget::ALL
                .iter()
                .map(|t| {
                    match TrustCgCodegenBackend::try_new_for_triple(
                        TrustCgTargetArch::AArch64,
                        t.triple(),
                    )
                    .and_then(|b| b.emit_object(std::slice::from_ref(&lir)))
                    {
                        Ok(_) => "emit".to_string(),
                        Err(e) => format!("emit refused: {}", first_words(&e.to_string())),
                    }
                })
                .collect();
            ("accept".to_string(), emits)
        }
    }
}

fn first_words(s: &str) -> String {
    let s: String = s.chars().take(240).collect();
    s.replace('|', "/").replace('\n', " ")
}

fn raw_jit(module: &Module) -> Result<trust_cg_codegen::JitCompilationResult, ViaCompilerError> {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = OptLevel::O2;
    Ok(Compiler::new(config)
        .with_codegen_license(census_license())
        .compile_module_to_jit(module, &HashMap::new())?)
}

struct Totals {
    functions: usize,
    with_assert: usize,
    lir_accept: usize,
    api_accept: [usize; 2],
    raw_accept: [usize; 2],
    jit_rows: usize,
    jit_disagree: usize,
}

fn render() -> String {
    let mut rows = String::new();
    let mut details = String::new();
    let mut t = Totals {
        functions: 0,
        with_assert: 0,
        lir_accept: 0,
        api_accept: [0; 2],
        raw_accept: [0; 2],
        jit_rows: 0,
        jit_disagree: 0,
    };
    for (label, module) in subjects() {
        for func in module.functions.iter().filter(|f| !f.blocks.is_empty()) {
            t.functions += 1;
            let iso = isolate(&module, func.id);
            let asserts = function_has_unfaithful_assert(func);
            t.with_assert += usize::from(asserts);
            let (lir, emits) = module_to_lir_row(&module, func.id);
            t.lir_accept += usize::from(lir == "accept");
            let mut api = Vec::new();
            let mut raw = Vec::new();
            for (i, target) in ViaCompilerTarget::ALL.iter().enumerate() {
                let compiled = for_target(&iso, target.triple());
                let a = compile_trust_ir_module_via_compiler(&compiled, *target, census_license());
                t.api_accept[i] += usize::from(a.is_ok());
                api.push(class(&a, ViaCompilerError::class_name));
                let r = compile_unchecked_boundary(&compiled, *target, census_license());
                t.raw_accept[i] += usize::from(r.is_ok());
                if let Err(e) = &r {
                    let _ = writeln!(
                        details,
                        "* `{}` / `{}` (raw, {}): {}",
                        label,
                        func.name,
                        target.triple(),
                        first_words(&e.to_string())
                    );
                }
                raw.push(class(&r, ViaCompilerError::class_name));
            }
            // JIT: through the API (F1 boundary applied); when the boundary
            // refuses, trust-cg's raw JIT over the inputs where every `Assert`
            // holds, so the value half of the measurement still reaches it.
            let jitted = for_host_jit(&iso);
            let jit = match jit_trust_ir_module_via_compiler(&jitted, census_license()) {
                Ok(j) => match agreement(&jitted, func.id, &j.buffer) {
                    Ok(a) => {
                        t.jit_rows += 1;
                        t.jit_disagree += a.disagree.len();
                        format!("api: {}", a.render())
                    }
                    Err(why) => format!("api: not run ({why})"),
                },
                Err(e) if refuse_f1_boundary(&jitted).is_err() => match raw_jit(&jitted) {
                    Ok(j) => match agreement(&jitted, func.id, &j.buffer) {
                        Ok(a) => {
                            t.jit_rows += 1;
                            t.jit_disagree += a.disagree.len();
                            format!("raw (API refused `{}`): {}", e.class_name(), a.render())
                        }
                        Err(why) => format!("raw: not run ({why})"),
                    },
                    Err(r) => format!("raw JIT refused `{}`", r.class_name()),
                },
                Err(e) => format!("JIT refused `{}`", e.class_name()),
            };
            let _ = writeln!(
                rows,
                "| {label} | `{}` | {} | {} | {} | {} | {} | {} | {} | {jit} |",
                func.name,
                if asserts { "yes" } else { "no" },
                lir,
                emits.first().map_or("—", String::as_str),
                emits.get(1).map_or("—", String::as_str),
                api[0],
                api[1],
                if raw[0] == raw[1] { raw[0].clone() } else { format!("{} / {}", raw[0], raw[1]) },
            );
        }
    }

    let mut doc = String::new();
    let _ = write!(
        doc,
        "# F1 consumer census — `module_to_lir` vs trust-cg `Compiler::compile` (2026-09-30)

**GENERATED — do not edit by hand.** Written by the test
`compiler_consumer::census::census_matches_the_committed_audit` in
`crates/trust-cg-bridge/src/compiler_consumer_census.rs`, which fails when this file and the census
differ. Regenerate with `{REGEN_ENV}=1 targo --unverified test -p trust-cg-bridge --lib census` and
review the diff. A dated measurement: re-run it, do not quote it.

## What is measured

The same `trust_ir::Module`s go through both codegen consumers the plan names
([plan](../PLAN.md) §2, R-5 and the R-8 items):

* **`module_to_lir`** — the frozen F1 converter (`lower_module_to_lir`, bare entry: no pass-mode
  cross-check is attested, because no rustc `FnAbi` exists here), then the bridge backend's
  `emit_object` for each triple.
* **`Compiler` API** — `compile_trust_ir_module_via_compiler`, i.e. trust-cg's `Compiler::compile` at
  `O2` with **proofs OFF** (the bridge builds trust-cg-codegen without `verify`), behind the F1
  boundary (`refuse_f1_boundary`: no `Assert`, no Clean origin).
* **`Compiler` raw** — the same compile WITHOUT the F1 boundary: what trust-cg itself accepts.
* **JIT vs interpreter** — trust-cg's host JIT (`aarch64-apple-darwin`, `O2`, the AArch64
  `Unchecked` validation default) run over an input grid and compared bit-for-bit with
  `trust_ir::interpret::Interpreter`. Through the API where it accepts; where the API refuses only
  for the F1 boundary, through the raw JIT on the inputs where every `Assert` holds (inputs where
  the interpreter reports a failed `Assert` are skipped and counted — those are exactly the inputs
  whose behaviour neither consumer can make faithful).
* **The codegen license** — every subject is claim-less (`body_gate: None`), and trust-cg's default
  license refuses a claim-less body before it judges any shape (DG-73). Every `Compiler` compile
  here (API, raw and JIT) therefore states trust-cg's default policy with
  `UnlicensedBodyPolicy::Permit` (`census_license`), and the test
  `the_default_license_refuses_the_claim_less_subjects` pins that the default refuses each subject
  by its license. The shipping consumer (`f1_compile`) compiles under the D31 license instead,
  which refuses a claim-less body.
* **The target** — trust-cg's ingestion admission runs trust-ir's validator (WS7.3), which refuses
  a module with an FFI boundary (a bodyless declaration) and no `target_info`
  (`TargetInfoRequired`). Where isolation leaves such a declaration in a hand-built module, the
  module is compiled stating the triple it is compiled for (the host's for the JIT; `native_c`
  struct passing, the C ABI trust-cg lowers a target-free module by). The fixtures carry their own
  target and are compiled as they are.

Each function is compiled ISOLATED: every other body in its module becomes a declaration, except its
transitive direct callees; a demoted body takes its debug value names, its scopes and the proof
obligations sited in or scoped to it along (trust-ir's validator refuses each once its body is
gone). Subjects: the three production-driver fixtures in
`crates/trust-bmc/tests/fixtures/direct_shadow/` (minted 2026-08-31 by the stage2 driver; their
target is `aarch64-unknown-linux-gnu`, `structpass=unclassified`), plus hand-built modules for the
R-8 axes the fixtures do not reach (direct `Internal` call, `f64`, `i128`, by-value struct; no
`target_info`), and the negative twin of the call row whose callee carries an `Assert`.

Nothing here is a lane: no rustc code calls `compiler_consumer` (a tripwire test enforces it), and
no byte in this census is proven.

## Totals

| | count |
|---|---|
| functions with a body | {} |
| … carrying an `Assert` | {} |
| `module_to_lir` accepts | {} |
| `Compiler` API accepts (darwin / linux) | {} / {} |
| `Compiler` raw accepts (darwin / linux) | {} / {} |
| functions value-checked on the JIT | {} |
| JIT-vs-interpreter disagreements | {} |

## Per function

| subject | function | `Assert` | `module_to_lir` | emit darwin | emit linux | `Compiler` API darwin | `Compiler` API linux | `Compiler` raw (darwin / linux) | JIT vs interpreter |
|---|---|---|---|---|---|---|---|---|---|
{rows}
## Reading notes

Written against the data above; when the data moves the census test fails, and these notes must be
re-read with the regenerated tables.

* **`Assert` dominates.** 9 of the 17 bodies carry one; with part 1's predicate both consumers refuse
  them (the `module_to_lir` column shows an earlier refusal — `UnclassifiedAggregateAbi` — for the two
  `m1bounds` bodies, whose ABI check runs first). A caller with no `Assert` of its own is refused when
  its callee carries one: `module_to_lir` after inlining, the `Compiler` API because isolation keeps
  the callee's body in the module.
* **trust-cg itself now refuses every `Assert`-bearing body too** (since the train that pins
  trust-cg `7ace0c56` with trust-ir v57): the fixtures' asserts predate assert kinds and trust-cg
  refuses a kindless check at its admission floor (`require_assert_panic_kinds`); the hand-built
  callee's check carries the kind the producer gives it (`Overflow(Add)`) and is refused for want
  of a panic site (`AssertPanicUnsupported`: a faithful lowering calls the kind's `core` panic
  entry with the site's location). So no JIT row runs an `Assert`-bearing body any more. Until
  that train trust-cg compiled every such scalar body and its raw JIT agreed with the interpreter
  on every input where all the `Assert`s held.
* **trust-cg refuses whole modules, not functions.** The `m1bounds` const-init bodies are refused by
  `Compiler` for a NEIGHBOUR: isolation keeps `pick`'s declaration, whose by-value `[i32; 7]`
  parameter under `struct_passing = unclassified` the adapter refuses module-wide. `module_to_lir`
  decides per function and accepts them.
* **Direct `Internal` calls now reach a Mach-O object** on `Compiler` as well as ELF (they were
  refused `AotDirectModuleFunctionBindingUnsupported` on darwin before trust-cg's Mach-O
  linkage binding); `module_to_lir` never emits the call at all (it inlines the leaf).
* **`f64` is the clearest R-5 gain:** `module_to_lir` refuses the type; `Compiler` compiles it on both
  triples and the JIT agrees on the grid (NaN compared as NaN, `-0.0` bit-exact). `i128` and the
  register-pair by-value struct are accepted by both.
* **Nothing here is proven** (proofs off, no output gate) — agreement is a value check over a grid.

## Raw `Compiler` refusals, first words

{}",
        t.functions,
        t.with_assert,
        t.lir_accept,
        t.api_accept[0],
        t.api_accept[1],
        t.raw_accept[0],
        t.raw_accept[1],
        t.jit_rows,
        t.jit_disagree,
        if details.is_empty() { "None.\n".to_string() } else { details },
    );
    doc
}

/// THE CENSUS. Renders the measurement and compares it with the committed
/// audit (or rewrites the audit under `TRUST_REGEN_F1_CONSUMER_CENSUS=1`).
#[test]
#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
fn census_matches_the_committed_audit() {
    let rendered = render();
    let path = repo_root().join(AUDIT);
    if std::env::var_os(REGEN_ENV).is_some() {
        std::fs::write(&path, &rendered).expect("write the census audit");
        return;
    }
    let committed = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        committed == rendered,
        "the F1 consumer census changed; regenerate `{AUDIT}` with {REGEN_ENV}=1 and review the \
         diff.\n--- rendered ---\n{rendered}"
    );
}

/// The API refuses an `Assert`-bearing module BY NAME before trust-cg sees it.
///
/// Trust (trust-ir v52/v54): this test used to show that trust-cg itself would
/// have compiled the refused shape. It no longer does, at the train that names
/// trust-cg `7ace0c56`: trust-cg refuses a kindless (`Unspecified`) assert at its
/// admission floor (`require_assert_panic_kinds`), and a KINDED one without a
/// panic site, because a faithful lowering calls the kind's panic entry with
/// the site's location (`AssertPanicUnsupported`). The producer kinds this
/// check (the shift's `Overflow(Shl)`) and names no site yet (the Trust half of
/// amendment P is after this train), so both spellings are asked: the boundary
/// refuses each by name first, and trust-cg's own refusal of each is pinned
/// with its reason, so a trust-cg that starts compiling an unsited assert is
/// noticed here. The boundary is asked under trust-cg's DEFAULT license (it
/// answers before any license is read); trust-cg's own refusals are asked
/// under [`census_license`], because under the default the license refuses the
/// claim-less fixture before its assert floor is reached.
#[test]
fn api_refuses_assert_before_trust_cg_which_refuses_it_too() {
    let stored = fixture("m1shift");
    let mut kinded = stored.clone();
    let mut asserts = 0;
    for node in &mut kinded.functions[0].blocks[0].body {
        if let Inst::Assert { kind, site: None, .. } = &mut node.inst {
            *kind = trust_ir::AssertKind::Overflow(trust_ir::AssertOverflowOp::Shl);
            asserts += 1;
        }
    }
    assert_eq!(asserts, 1, "the fixture carries exactly one siteless Assert");
    for m in [&stored, &kinded] {
        let err = compile_trust_ir_module_via_compiler(
            m,
            ViaCompilerTarget::Aarch64UnknownLinuxGnu,
            CodegenLicensePolicy::default(),
        )
        .expect_err("an Assert-bearing module must be refused");
        assert!(
            matches!(&err, ViaCompilerError::ImplicitPanicUnfaithful { function, .. } if function == "sh_safe"),
            "{err:?}"
        );
        assert!(err.to_string().contains("[implicit-panic-unfaithful]"), "{err}");
    }
    let floor = compile_unchecked_boundary(
        &stored,
        ViaCompilerTarget::Aarch64UnknownLinuxGnu,
        census_license(),
    )
    .expect_err("trust-cg refuses a kindless assert at its own floor");
    assert!(format!("{floor:?}").contains("require_assert_panic_kinds"), "{floor:?}");
    let unsited = compile_unchecked_boundary(
        &kinded,
        ViaCompilerTarget::Aarch64UnknownLinuxGnu,
        census_license(),
    )
    .expect_err("trust-cg refuses a kinded assert with no panic site");
    assert!(format!("{unsited:?}").contains("AssertPanicUnsupported"), "{unsited:?}");
}

/// `m1shift` with its one `Assert` removed (the same shift, unguarded).
fn assert_free_twin() -> Module {
    let mut m = fixture("m1shift");
    let body = &mut m.functions[0].blocks[0].body;
    let before = body.len();
    body.retain(|n| !matches!(n.inst, Inst::Assert { .. }));
    assert_eq!(body.len(), before - 1, "the fixture carries exactly one Assert");
    m
}

/// NEGATIVE TWIN: with the `Assert` gone (the same shift, unguarded), the API
/// passes the module to trust-cg and, under the census license, an object
/// comes back.
#[test]
fn api_admits_the_assert_free_twin() {
    let m = assert_free_twin();
    let out = compile_trust_ir_module_via_compiler(
        &m,
        ViaCompilerTarget::Aarch64UnknownLinuxGnu,
        census_license(),
    )
    .expect("an Assert-free module reaches trust-cg");
    assert!(!out.object_code.is_empty());
}

/// Whether `err` is trust-cg's license refusal of a claim-less body of
/// `module` (`AdapterError::UnlicensedBody`, DG-73).
fn is_unlicensed_body_refusal(module: &Module, err: &ViaCompilerError) -> bool {
    let ViaCompilerError::Compiler(error) = err else { return false };
    let CompileError::Adapter(AdapterError::UnlicensedBody { function }) = &**error else {
        return false;
    };
    module
        .functions
        .iter()
        .any(|f| !f.blocks.is_empty() && f.body_gate.is_none() && f.name == *function)
}

/// NEGATIVE CONTROL for [`census_license`]: every isolated subject the census
/// compiles under `Permit` (on either triple, and on the host JIT), and the
/// `Assert`-free twin, is refused under trust-cg's DEFAULT license, by that
/// license (`UnlicensedBody` naming a claim-less body of the module).
/// FAILS if the default starts admitting a claim-less body (DG-73 weakened),
/// or if a census acceptance no longer rests on the stated `Permit` (the
/// census would then need no policy, and should not state one).
#[test]
fn the_default_license_refuses_the_claim_less_subjects() {
    let mut all = subjects();
    all.push(("m1shift without its Assert".to_string(), assert_free_twin()));
    let (mut objects, mut jits) = (0usize, 0usize);
    for (label, module) in &all {
        for func in module.functions.iter().filter(|f| !f.blocks.is_empty()) {
            let iso = isolate(module, func.id);
            for target in ViaCompilerTarget::ALL {
                let compiled = for_target(&iso, target.triple());
                if compile_unchecked_boundary(&compiled, target, census_license()).is_err() {
                    continue;
                }
                let err =
                    compile_unchecked_boundary(&compiled, target, CodegenLicensePolicy::default())
                        .expect_err("the default license refuses a claim-less body");
                assert!(
                    is_unlicensed_body_refusal(&compiled, &err),
                    "{label} / {} ({}): {err:?}",
                    func.name,
                    target.triple()
                );
                assert!(err.to_string().contains("carries no codegen license"), "{err}");
                objects += 1;
            }
            let jitted = for_host_jit(&iso);
            if jit_trust_ir_module_via_compiler(&jitted, census_license()).is_ok() {
                let Err(err) =
                    jit_trust_ir_module_via_compiler(&jitted, CodegenLicensePolicy::default())
                else {
                    panic!("{label} / {}: the default license admitted it on the JIT", func.name);
                };
                assert!(
                    is_unlicensed_body_refusal(&jitted, &err),
                    "{label} / {} (JIT): {err:?}",
                    func.name
                );
                jits += 1;
            }
        }
    }
    // Six accepted subjects (the five hand-built bodies the census accepts and
    // the twin) on two triples; the JIT runs only on an admitted host.
    assert_eq!(objects, 12, "the control judged {objects} object compiles");
    if ViaCompilerTarget::host().is_some() {
        assert_eq!(jits, 6, "the control judged {jits} JIT compiles");
    }
}

/// The F1 boundary also carries the Clean-origin refusal (under any license:
/// it answers before trust-cg reads one).
#[test]
fn api_refuses_clean_origin() {
    let mut m = internal_call_module();
    m.functions[0].producer = Some(trust_ir::Producer::Clean);
    let err = compile_trust_ir_module_via_compiler(
        &m,
        ViaCompilerTarget::Aarch64AppleDarwin,
        CodegenLicensePolicy::default(),
    )
    .expect_err("a Clean-origin body must be refused");
    assert!(matches!(err, ViaCompilerError::CleanOriginBelowCodegenGate { .. }), "{err:?}");
}

/// The census compares against the committed audit only on an AArch64 Apple
/// host (the JIT half executes host code, and the rendered rows include the
/// host's JIT results). Elsewhere the committed audit is NOT checked; say so
/// in the test output rather than passing silently.
#[test]
#[cfg(not(all(target_arch = "aarch64", target_vendor = "apple")))]
fn census_matches_the_committed_audit() {
    eprintln!(
        "NOT CHECKED: `{AUDIT}` is compared only on an aarch64 Apple host; this host's \
         JIT rows would differ, so the committed census is unverified here"
    );
}

/// Every needle that names the measurement API or the trap oracle.
const TRIPWIRE_NEEDLES: [&str; 4] = [
    "compiler_consumer",
    "compile_trust_ir_module_via_compiler",
    "jit_trust_ir_module_via_compiler",
    "trap_assert_oracle",
];

/// Collect `(rs sources, Cargo.toml manifests)` under `root`, never following a
/// symlink and skipping `target/` build output and this crate itself.
fn tripwire_files(root: &std::path::Path, own: &std::path::Path) -> (Vec<PathBuf>, Vec<PathBuf>) {
    let (mut sources, mut manifests) = (Vec::new(), Vec::new());
    let mut dirs = vec![root.to_path_buf()];
    while let Some(dir) = dirs.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else { continue };
        for entry in entries {
            let path = entry.expect("dir entry").path();
            let Ok(meta) = std::fs::symlink_metadata(&path) else { continue };
            if meta.file_type().is_symlink() {
                continue;
            }
            if meta.is_dir() {
                let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
                if name != "target" && name != ".git" && path != own {
                    dirs.push(path);
                }
            } else if path.extension().is_some_and(|e| e == "rs") {
                sources.push(path);
            } else if path.file_name().is_some_and(|n| n == "Cargo.toml") {
                manifests.push(path);
            }
        }
    }
    (sources, manifests)
}

/// TRIPWIRE: this is a measurement API, and the trap oracle is a test oracle.
/// The day any other Trust crate or the rustc plugin names either (or a
/// manifest that depends on this crate mentions `test-hooks`, the only
/// feature that compiles the oracle outside this crate's unit tests), it has
/// become a shipping lane without the proven-output gate or with an unfaithful
/// panic, and this fails.
///
/// Scope: `compiler/rustc_codegen_trust_cg`, `crates/` (minus this crate and
/// `target/`) and `targo-trust/`. The manifest check is deliberately coarse —
/// ANY `test-hooks` text in a manifest that names `trust-cg-bridge` trips it,
/// so a table-form `[dependencies.trust-cg-bridge]` or a
/// `"trust-cg-bridge/test-hooks"` feature edge cannot slip past a line match.
#[test]
fn no_compiler_caller() {
    let own = repo_root().join("crates/trust-cg-bridge");
    let mut hits = Vec::new();
    let mut scanned = 0usize;
    let mut plugin_scanned = false;
    for root in ["compiler/rustc_codegen_trust_cg", "crates", "targo-trust"] {
        let (sources, manifests) = tripwire_files(&repo_root().join(root), &own);
        for path in sources {
            scanned += 1;
            plugin_scanned |= root.starts_with("compiler/");
            let text = std::fs::read_to_string(&path).unwrap_or_default();
            for needle in TRIPWIRE_NEEDLES {
                if text.contains(needle) {
                    hits.push(format!("{} names `{needle}`", path.display()));
                }
            }
        }
        for path in manifests {
            let text = std::fs::read_to_string(&path).unwrap_or_default();
            if text.contains("trust-cg-bridge") && text.contains("test-hooks") {
                hits.push(format!("{} may enable trust-cg-bridge's `test-hooks`", path.display()));
            }
        }
    }
    assert!(plugin_scanned, "the tripwire scanned no plugin source: it would pass vacuously");
    assert!(scanned > 100, "the tripwire scanned only {scanned} sources: wrong root?");
    assert!(hits.is_empty(), "the measurement API reached another lane: {hits:#?}");
}
