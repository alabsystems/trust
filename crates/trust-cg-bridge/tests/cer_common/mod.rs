// tests/cer_common — shared support for the call-event refinement (CER) gate
// tests (increment 5, step 5.2): hand-built trust-ir modules, compilation with
// trust-cg's `Compiler::compile` for aarch64-apple-darwin and
// aarch64-unknown-linux-gnu, and MACHINE-SIDE object patchers for the mutation
// battery. A patcher changes only the bytes the gate reads; the spec side (the
// producer module and P) is untouched unless a test says otherwise.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![allow(dead_code)]

#[cfg(feature = "ay-proofs")]
use std::collections::BTreeMap;
#[cfg(feature = "ay-proofs")]
use std::sync::Arc;

#[cfg(feature = "ay-proofs")]
use trust_cg_bridge::call_event::{
    CerInput, CerReport, FnPlacement, ProducerBody, ProducerModule, verify_compiled_module,
};
use trust_cg_bridge::compiled_object::CompiledObject;
#[cfg(feature = "ay-proofs")]
use trust_cg_bridge::compiled_object::{ObjectRefusal, RelocationModel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CodegenLicensePolicy, CompileError, Compiler, CompilerConfig, UnlicensedBodyPolicy,
};
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{
    Block, Constant, Endianness, Function, Linkage, Module, Producer, StructPassingPolicy,
    TargetInfo, Ty,
};

pub const DARWIN: &str = "aarch64-apple-darwin";
pub const LINUX: &str = "aarch64-unknown-linux-gnu";
pub const BOTH: [&str; 2] = [DARWIN, LINUX];

// ===========================================================================
// MODULE BUILDING
// ===========================================================================

/// Builds a trust-ir module function by function. `FuncId`s are positions.
pub struct ModBuilder {
    pub m: Module,
}

impl ModBuilder {
    pub fn new(name: &str) -> Self {
        ModBuilder { m: Module::new(name) }
    }

    pub fn sig(&mut self, params: &[Ty], ret: Option<Ty>) -> FuncTyId {
        let id = FuncTyId::new(self.m.func_types.len() as u32);
        self.m.func_types.push(FuncTy {
            params: params.to_vec(),
            returns: ret.into_iter().collect(),
            is_vararg: false,
            abi: None,
        });
        id
    }

    /// A body-less declaration (an External callee).
    pub fn declare(&mut self, name: &str, sig: FuncTyId) -> FuncId {
        let id = FuncId::new(self.m.functions.len() as u32);
        let mut f = Function::new(id, name, sig, BlockId::new(0));
        f.linkage = Linkage::External;
        f.producer = Some(Producer::TRust);
        self.m.functions.push(f);
        id
    }

    /// Reserve a defined function (body filled by [`ModBuilder::body`]).
    pub fn reserve(&mut self, name: &str, sig: FuncTyId, linkage: Linkage) -> FuncId {
        let id = self.declare(name, sig);
        self.m.functions[id.as_usize()].linkage = linkage;
        id
    }

    /// Fill `id`'s body with `build`.
    pub fn body(&mut self, id: FuncId, build: impl FnOnce(&mut FnBody)) {
        let sig = self.m.functions[id.as_usize()].ty;
        let params = self.m.func_types[sig.as_usize()].params.clone();
        let mut fb = FnBody::new(&params);
        build(&mut fb);
        self.m.functions[id.as_usize()].blocks = fb.blocks;
    }

    pub fn define(
        &mut self,
        name: &str,
        sig: FuncTyId,
        linkage: Linkage,
        build: impl FnOnce(&mut FnBody),
    ) -> FuncId {
        let id = self.reserve(name, sig, linkage);
        self.body(id, build);
        id
    }

    pub fn finish(self) -> Module {
        self.m
    }
}

/// Builds one function body in SSA form.
pub struct FnBody {
    pub blocks: Vec<Block>,
    next: u32,
    cur: usize,
    pub params: Vec<ValueId>,
}

impl FnBody {
    fn new(params: &[Ty]) -> Self {
        let mut fb = FnBody {
            blocks: vec![Block::new(BlockId::new(0))],
            next: 0,
            cur: 0,
            params: Vec::new(),
        };
        for ty in params {
            let v = fb.fresh();
            fb.blocks[0].params.push((v, ty.clone()));
            fb.params.push(v);
        }
        fb
    }

    fn fresh(&mut self) -> ValueId {
        let v = ValueId::new(self.next);
        self.next += 1;
        v
    }

    pub fn p(&self, i: usize) -> ValueId {
        self.params[i]
    }

    fn push(&mut self, inst: Inst) -> ValueId {
        let v = self.fresh();
        self.blocks[self.cur].body.push(InstrNode::new(inst).with_result(v));
        v
    }

    /// Push any single-result instruction.
    pub fn push_inst(&mut self, inst: Inst) -> ValueId {
        self.push(inst)
    }

    /// Push a result-less instruction.
    pub fn push_inst_void(&mut self, inst: Inst) {
        self.push_void(inst);
    }

    fn push_void(&mut self, inst: Inst) {
        self.blocks[self.cur].body.push(InstrNode::new(inst));
    }

    pub fn konst(&mut self, ty: Ty, v: i128) -> ValueId {
        self.push(Inst::Const { ty, value: Constant::Int(v) })
    }

    pub fn bin(&mut self, op: BinOp, ty: Ty, a: ValueId, c: ValueId) -> ValueId {
        self.push(Inst::BinOp { op, ty, lhs: a, rhs: c })
    }

    pub fn icmp(&mut self, op: ICmpOp, ty: Ty, a: ValueId, c: ValueId) -> ValueId {
        self.push(Inst::ICmp { op, ty, lhs: a, rhs: c })
    }

    pub fn call(&mut self, callee: FuncId, args: &[ValueId]) -> ValueId {
        self.push(Inst::Call { callee, args: args.to_vec() })
    }

    pub fn call_void(&mut self, callee: FuncId, args: &[ValueId]) {
        self.push_void(Inst::Call { callee, args: args.to_vec() });
    }

    pub fn extract(&mut self, ty: Ty, agg: ValueId, field: u32) -> ValueId {
        self.push(Inst::ExtractField { ty, aggregate: agg, field })
    }

    pub fn make_pair(&mut self, ty: Ty, a: ValueId, c: ValueId) -> ValueId {
        self.push(Inst::MakeAggregate { ty, variant: None, fields: vec![a, c] })
    }

    pub fn ret(&mut self, v: ValueId) {
        self.push_void(Inst::Return { values: vec![v] });
    }

    pub fn ret_void(&mut self) {
        self.push_void(Inst::Return { values: vec![] });
    }

    /// A new block with parameters; returns its id and parameter values.
    pub fn block(&mut self, params: &[Ty]) -> (BlockId, Vec<ValueId>) {
        let id = BlockId::new(self.blocks.len() as u32);
        let mut blk = Block::new(id);
        let mut vs = Vec::new();
        for ty in params {
            let v = self.fresh();
            blk.params.push((v, ty.clone()));
            vs.push(v);
        }
        self.blocks.push(blk);
        (id, vs)
    }

    pub fn switch_to(&mut self, id: BlockId) {
        self.cur = id.as_usize();
    }

    pub fn cond_br(
        &mut self,
        c: ValueId,
        t: BlockId,
        targs: &[ValueId],
        e: BlockId,
        eargs: &[ValueId],
    ) {
        self.push_void(Inst::CondBr {
            cond: c,
            then_target: t,
            then_args: targs.to_vec(),
            else_target: e,
            else_args: eargs.to_vec(),
        });
    }

    pub fn br(&mut self, t: BlockId, args: &[ValueId]) {
        self.push_void(Inst::Br { target: t, args: args.to_vec() });
    }
}

// ===========================================================================
// PKG-C5c-L0: THE LADDER'S LOOP RUNGS (r03, s06, s24) AS TRUST-IR
// ===========================================================================

/// A loop rung of tests/trust-f1-ladder, each `extern "C" fn rung(x: u64) -> u64`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoopRung {
    /// `while i < x { s = s + (i ^ (s >> 3)); i += 1 } s`
    R03,
    /// `while i < x { s += i; i += 1 } s`
    S06,
    /// `loop { if i <= 1 { break } i = if i & 1 == 0 { i >> 1 } else { i * 3 + 1 }; n += 1 } n`
    S24,
}

pub const LOOP_RUNGS: [LoopRung; 3] = [LoopRung::R03, LoopRung::S06, LoopRung::S24];

/// The rung's function `rung` in a module of its own, laid out as the producer
/// lays out the ladder's: bb0 the entry, bb1 the loop header (its parameters
/// the loop variables), then the blocks in source order.
pub fn loop_rung_module(rung: LoopRung, linkage: Linkage) -> Module {
    let mut mb = ModBuilder::new("loop_rung");
    let s = mb.sig(&[Ty::U64], Some(Ty::U64));
    mb.define("rung", s, linkage, |fb| loop_rung_body(rung, fb));
    mb.finish()
}

/// The body of [`loop_rung_module`]'s `rung`.
pub fn loop_rung_body(rung: LoopRung, fb: &mut FnBody) {
    let x = fb.p(0);
    match rung {
        LoopRung::R03 | LoopRung::S06 => {
            let (head, hv) = fb.block(&[Ty::U64, Ty::U64]);
            let (body, _) = fb.block(&[]);
            let (exit, _) = fb.block(&[]);
            let zero = fb.konst(Ty::U64, 0);
            fb.br(head, &[zero, zero]);
            fb.switch_to(head);
            let (i, s) = (hv[0], hv[1]);
            let go = fb.icmp(ICmpOp::Ult, Ty::U64, i, x);
            fb.cond_br(go, body, &[], exit, &[]);
            fb.switch_to(body);
            let s2 = if rung == LoopRung::S06 {
                fb.bin(BinOp::Add, Ty::U64, s, i)
            } else {
                let three = fb.konst(Ty::U64, 3);
                let sh = fb.bin(BinOp::LShr, Ty::U64, s, three);
                let t = fb.bin(BinOp::Xor, Ty::U64, i, sh);
                fb.bin(BinOp::Add, Ty::U64, s, t)
            };
            let one = fb.konst(Ty::U64, 1);
            let i2 = fb.bin(BinOp::Add, Ty::U64, i, one);
            fb.br(head, &[i2, s2]);
            fb.switch_to(exit);
            fb.ret(s);
        }
        LoopRung::S24 => {
            let (head, hv) = fb.block(&[Ty::U64, Ty::U64]);
            let (done, _) = fb.block(&[]);
            let (test, _) = fb.block(&[]);
            let (even, _) = fb.block(&[]);
            let (odd, _) = fb.block(&[]);
            let (join, jv) = fb.block(&[Ty::U64]);
            let zero = fb.konst(Ty::U64, 0);
            fb.br(head, &[x, zero]);
            fb.switch_to(head);
            let (i, n) = (hv[0], hv[1]);
            let one = fb.konst(Ty::U64, 1);
            let stop = fb.icmp(ICmpOp::Ule, Ty::U64, i, one);
            fb.cond_br(stop, done, &[], test, &[]);
            fb.switch_to(done);
            fb.ret(n);
            fb.switch_to(test);
            let one = fb.konst(Ty::U64, 1);
            let low = fb.bin(BinOp::And, Ty::U64, i, one);
            let zero = fb.konst(Ty::U64, 0);
            let is_even = fb.icmp(ICmpOp::Eq, Ty::U64, low, zero);
            fb.cond_br(is_even, even, &[], odd, &[]);
            fb.switch_to(even);
            let one = fb.konst(Ty::U64, 1);
            let half = fb.bin(BinOp::LShr, Ty::U64, i, one);
            fb.br(join, &[half]);
            fb.switch_to(odd);
            let three = fb.konst(Ty::U64, 3);
            let m = fb.bin(BinOp::Mul, Ty::U64, i, three);
            let one = fb.konst(Ty::U64, 1);
            let p = fb.bin(BinOp::Add, Ty::U64, m, one);
            fb.br(join, &[p]);
            fb.switch_to(join);
            let one = fb.konst(Ty::U64, 1);
            let n2 = fb.bin(BinOp::Add, Ty::U64, n, one);
            fb.br(head, &[jv[0], n2]);
        }
    }
}

// ===========================================================================
// PKG-C5c S2a: A SITED DIVISION CHECK (LADDER RUNG s21)
// ===========================================================================

/// The panic entry `AssertKind::DivByZero` names (its `core` lang item; a
/// hand-built module has no session to mangle it).
pub const DIV_ENTRY: &str = "panic_const_div_by_zero";
/// The Location record a sited division check passes to [`DIV_ENTRY`].
pub const DIV_LOCATION: &str = "rung_location";
/// The NUL-terminated file name the pointer record points at.
pub const DIV_LOCATION_FILE: &str = "rung_location_file";

/// The Location record of [`sited_div`]'s `M_cg`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DivRecord {
    /// The producer's shape: an immutable Internal pointer record
    /// `{ file: ptr, len: u64, line: u32, col: u32 }` whose `file` is
    /// [`DIV_LOCATION_FILE`] (the PKG-CP pointer-record image).
    Pointer,
    /// 24 plain bytes (no pointer), Internal, `mutable` and thread-local
    /// (`TlsModel::LocalExec`) as given.
    Bytes { mutable: bool, tls: bool },
}

/// An Internal, non-TLS global holding the flat image `elements`, typed the
/// way trust-cg-lower types a flat allocation image (`type_flat_image`).
fn div_image_global(
    m: &mut Module,
    name: &str,
    elements: Vec<Constant>,
    align: u32,
    mutable: bool,
    tls: bool,
) -> trust_ir::value::GlobalId {
    let image = trust_cg_lower::global_image::type_flat_image(m, name, elements, 8)
        .expect("a flat byte/relocation image");
    let id = trust_ir::value::GlobalId::new(m.globals.len() as u32);
    m.globals.push(trust_ir::Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.to_string(),
        ty: image.ty,
        mutable,
        initializer: Some(image.initializer),
        linkage: Linkage::Internal,
        tls: tls.then_some(trust_ir::TlsModel::LocalExec),
        align: Some(align),
    });
    id
}

/// `rung(x: u64) -> u64`, ladder rung s21 (`tests/trust-f1-ladder/micro/s21_div_var.rs`,
/// `if x != 0 { 1000 / x } else { 0 }`) when `guarded`, else `1000 / x`, as the
/// compiler lane hands it to F1: `(m_cg, producer)`. The producer holds the
/// division's check unsited (`assert x != 0, div_by_zero`, as the THIR producer
/// emits it); `M_cg`'s copy sites it at [`DIV_ENTRY`] and the Location global
/// `record` (stage-1 trustc 80c41bb667's `-Ztrust-dump=ir:` of s21: `{entry: 1,
/// location: Global(1)}`). Guarded, the check is dead (`x != 0` on its only
/// path); unguarded it is live. Neither module carries a target.
pub fn sited_div(guarded: bool, record: DivRecord) -> (Module, Module) {
    let body = |mb: &mut ModBuilder, site: Option<trust_ir::inst::PanicSite>| {
        let sig = mb.sig(&[Ty::U64], Some(Ty::U64));
        mb.define("rung", sig, Linkage::External, |fb| {
            let x = fb.p(0);
            let divide = |fb: &mut FnBody| {
                let k = fb.konst(Ty::U64, 1000);
                let z = fb.konst(Ty::U64, 0);
                let ok = fb.icmp(ICmpOp::Ne, Ty::U64, x, z);
                fb.push_inst_void(Inst::Assert {
                    cond: ok,
                    kind: trust_ir::AssertKind::DivByZero,
                    site: site.clone(),
                });
                fb.bin(BinOp::UDiv, Ty::U64, k, x)
            };
            if guarded {
                let zero = fb.konst(Ty::U64, 0);
                let c = fb.icmp(ICmpOp::Ne, Ty::U64, x, zero);
                let (then, _) = fb.block(&[]);
                let (otherwise, _) = fb.block(&[]);
                let (join, r) = fb.block(&[Ty::U64]);
                fb.cond_br(c, then, &[], otherwise, &[]);
                fb.switch_to(then);
                let q = divide(fb);
                fb.br(join, &[q]);
                fb.switch_to(otherwise);
                let z = fb.konst(Ty::U64, 0);
                fb.br(join, &[z]);
                fb.switch_to(join);
                fb.ret(r[0]);
            } else {
                let q = divide(fb);
                fb.ret(q);
            }
        });
    };
    let mut m_cg = ModBuilder::new("rung");
    let entry_sig = m_cg.sig(&[Ty::Ptr], None);
    let entry = m_cg.declare(DIV_ENTRY, entry_sig);
    let location = match record {
        DivRecord::Pointer => {
            let file = "tests/trust-f1-ladder/micro/s21_div_var.rs";
            let mut name: Vec<Constant> =
                file.bytes().map(|b| Constant::Int(i128::from(b))).collect();
            name.push(Constant::Int(0));
            div_image_global(&mut m_cg.m, DIV_LOCATION_FILE, name, 1, false, false);
            let mut image =
                vec![Constant::SymbolAddr { symbol: DIV_LOCATION_FILE.into(), addend: 0 }];
            let mut tail = (file.len() as u64).to_le_bytes().to_vec();
            tail.extend(1u32.to_le_bytes());
            tail.extend(65u32.to_le_bytes());
            image.extend(tail.into_iter().map(|b| Constant::Int(i128::from(b))));
            div_image_global(&mut m_cg.m, DIV_LOCATION, image, 8, false, false)
        }
        DivRecord::Bytes { mutable, tls } => {
            let image = (1..=24).map(Constant::Int).collect();
            div_image_global(&mut m_cg.m, DIV_LOCATION, image, 8, mutable, tls)
        }
    };
    body(
        &mut m_cg,
        Some(trust_ir::inst::PanicSite {
            entry,
            location: trust_ir::inst::PanicLocation::Global(location),
        }),
    );
    let mut producer = ModBuilder::new("rung");
    body(&mut producer, None);
    (m_cg.finish(), producer.finish())
}

/// [`sited_div`] compiled for `triple` at `opt`: the bytes from `M_cg`, the gate reading the
/// producer's unsited check. Static.
#[cfg(feature = "ay-proofs")]
pub fn sited_div_fixture(guarded: bool, record: DivRecord, triple: &str, opt: OptLevel) -> Fixture {
    let (m_cg, producer) = sited_div(guarded, record);
    let m_cg = targeted(&m_cg, triple);
    let object = compile(&m_cg, triple, opt);
    let mut fx = Fixture::with_object(m_cg, object, triple);
    let producer = Arc::new(targeted(&producer, triple));
    fx.bodies = producer
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| (f.name.clone(), ProducerBody { producer: 0, func: f.id }))
        .collect();
    fx.producers = vec![ProducerModule::named_by_symbols(producer)];
    fx
}

/// The measured DIV-SPLIT-1 label of `rung` in [`sited_div_fixture`]`(true, Pointer, _, O0)`
/// (PKG-C5c-S3b, 2026-11-15, both triples): the S3b operand congruence (`bvf_div_cong`) beside
/// the folded s21 O0 label's theorems. The same string is pinned in the unit tests
/// (`src/verify_output_instantiate/div_split/tests.rs` `S21_SITED_O0_LABEL`, which cannot import
/// this module): change both together.
pub const S21_SITED_O0_LABEL: &str = "Clean.BVC.bvf_div_cong+Clean.BVC.bvf_or_cong+\
Clean.BVC.bvf_or_zero_id+Clean.BVC.bvf_sub_cong+Trust.BVB.ite_cong+Trust.BVB.ite_false+\
Trust.BVB.ite_true+Trust.BVB.sub_zero+kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";

// ===========================================================================
// COMPILING AND RUNNING THE GATE
// ===========================================================================

/// The codegen license [`compile`] states for these fixtures: trust-cg's
/// default policy with claim-less bodies PERMITTED.
///
/// Every module here is hand-built and claim-less (`body_gate: None`), and
/// trust-cg's default license refuses a claim-less body (trust-cg decision gate
/// DG-73, roadmap WS7.5) before it lowers anything. What these tests exercise is
/// the gate over the bytes (which never reads `body_gate`), not the license, so
/// they state `Permit`, as trust-cg's own tests do for their hand-built
/// fixtures (trust-cg LD-W7-1). The license the shipping consumer compiles
/// under (D31) is `tests/f1_compile.rs`'s subject, and the negative control
/// `compiled_object_reader::the_default_license_refuses_the_claim_less_fixtures`
/// pins that the default still refuses these fixtures.
pub fn fixture_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// `module` with its `target_info` pinned to `triple` when it needs one and
/// has none.
///
/// A module with an FFI boundary (a bodyless declaration, such as an External
/// callee) and no `target_info` is refused by trust-cg's ingestion admission
/// (`TargetInfoRequired`, WS7.3), which declines to guess an ABI. A producer
/// states the target it emitted for (the rustc plugin's M_cg carries the
/// compilation's triple), so a fixture compiled for several triples states each
/// compile's own: only a module that lacks a target and requires one is
/// pinned (trust-cg LD-59's rule), and every other module is returned
/// unchanged. The stamped struct passing is `NativeC`, the C ABI trust-cg
/// lowers a target-free module by, so the bytes are the ones a target-free
/// compile produced before that admission.
pub fn targeted(module: &Module, triple: &str) -> Module {
    let mut module = module.clone();
    if module.target_info.is_none() && module.requires_target_info() {
        module.target_info = Some(TargetInfo {
            triple: triple.to_string(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
    }
    module
}

/// Compile `module`, [`targeted`] at `triple`, with trust-cg's
/// `Compiler::compile` for `triple` under `license`. Boxed: `CompileError` is
/// large.
pub fn compile_under(
    module: &Module,
    triple: &str,
    opt: OptLevel,
    license: CodegenLicensePolicy,
) -> Result<Vec<u8>, Box<CompileError>> {
    let spec = TargetSpec::parse(triple).expect("triple parses");
    let config = CompilerConfig { opt_level: opt, parallel: false, ..CompilerConfig::default() };
    Ok(Compiler::new_for_target_spec(config, spec)
        .with_codegen_license(license)
        .compile(&targeted(module, triple))
        .map_err(Box::new)?
        .object_code)
}

/// Compile `module`, [`targeted`] at `triple`, with trust-cg's
/// `Compiler::compile` for `triple` under [`fixture_license`].
pub fn compile(module: &Module, triple: &str, opt: OptLevel) -> Vec<u8> {
    compile_under(module, triple, opt, fixture_license())
        .unwrap_or_else(|e| panic!("{triple}: Compiler::compile failed: {e}"))
}

/// One gate run's inputs: `M_cg`, the producers (by default `M_cg` itself,
/// named by symbol), the bodies, P and the shipped object.
#[cfg(feature = "ay-proofs")]
pub struct Fixture {
    pub m_cg: Arc<Module>,
    pub producers: Vec<ProducerModule>,
    pub bodies: BTreeMap<String, ProducerBody>,
    pub placements: BTreeMap<String, FnPlacement>,
    pub object: Vec<u8>,
    pub model: RelocationModel,
    pub triple: String,
}

#[cfg(feature = "ay-proofs")]
impl Fixture {
    /// Compile `module` and take it as its own producer, with the natural
    /// all-scalar P. The module the gate reads is the one compiled: [`targeted`]
    /// at `triple`.
    pub fn new(module: Module, triple: &str, opt: OptLevel) -> Self {
        let module = targeted(&module, triple);
        let object = compile(&module, triple, opt);
        Self::with_object(module, object, triple)
    }

    pub fn with_object(module: Module, object: Vec<u8>, triple: &str) -> Self {
        let m_cg = Arc::new(module);
        let producers = vec![ProducerModule::named_by_symbols(m_cg.clone())];
        let mut bodies = BTreeMap::new();
        let mut placements = BTreeMap::new();
        for f in &m_cg.functions {
            if !f.blocks.is_empty() {
                bodies.insert(f.name.clone(), ProducerBody { producer: 0, func: f.id });
            }
            if let Ok(p) = FnPlacement::from_scalar_signature(&m_cg, f) {
                placements.insert(f.name.clone(), p);
            }
        }
        Fixture {
            m_cg,
            producers,
            bodies,
            placements,
            object,
            model: RelocationModel::Static,
            triple: triple.to_string(),
        }
    }

    /// Run the gate on a thread with rustc's compiler-thread stack (8 MiB,
    /// `rustc_interface`'s default) — the environment it runs in once wired
    /// (step 5.4). The 2 MiB default test-thread stack is not representative:
    /// MEASURED, an O0 spill-heavy body (`mutant_mixed_inline_and_call_sites_of_
    /// one_callee`) overflows it in a debug build and passes at 3 MiB.
    pub fn verify(&self) -> Result<CerReport, ObjectRefusal> {
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(8 << 20)
                .spawn_scoped(scope, || {
                    verify_compiled_module(&CerInput {
                        m_cg: &self.m_cg,
                        producers: &self.producers,
                        bodies: &self.bodies,
                        placements: &self.placements,
                        object: &self.object,
                        relocation_model: self.model,
                    })
                })
                .expect("spawn the gate thread")
                .join()
                .expect("the gate thread panicked")
        })
    }

    pub fn report(&self) -> CerReport {
        self.verify().unwrap_or_else(|e| {
            panic!("{}: object refused: {e}\n{}", self.triple, disassemble(&self.object))
        })
    }

    /// Patch the object with `f` (machine side only).
    pub fn patched(&self, f: impl FnOnce(&mut Vec<u8>)) -> Fixture {
        let mut object = self.object.clone();
        f(&mut object);
        Fixture {
            m_cg: self.m_cg.clone(),
            producers: self.producers.clone(),
            bodies: self.bodies.clone(),
            placements: self.placements.clone(),
            object,
            model: self.model,
            triple: self.triple.clone(),
        }
    }
}

/// A readable account of a report for assertion messages.
#[cfg(feature = "ay-proofs")]
pub fn explain(report: &CerReport) -> String {
    let mut s = String::new();
    for c in &report.certificates {
        s.push_str(&format!("{} {}\n", c.symbol, c.grade));
        for (n, o) in [
            ("O0", &c.obligations.o0_abi),
            ("O1", &c.obligations.o1_binding),
            ("O2", &c.obligations.o2_pairing),
            ("O3", &c.obligations.o3_events),
            ("O4", &c.obligations.o4_return),
            ("O5", &c.obligations.o5_frame),
        ] {
            s.push_str(&format!("   {n} {:?}: {}\n", o.grade, o.detail));
        }
    }
    s
}

/// The refusal `c` must carry for a store or load through a pointer parameter
/// of a module that states its target, on a Darwin leg (`darwin`) or a Linux
/// one. Since af4b2d3abd the IR access reaches the source byte-memory model,
/// whose PTR.3b frontier (`ResultMemory::missing_integration`, call_event/source_memory.rs) sends the
/// function to the bounded-leaf route (call_event.rs). That route is modeled
/// for qualified Darwin targets only, so on Linux it has no evidence and O4 is
/// the frontier's own reason. On Darwin the route runs and its joint kernel
/// goal is declined (`try_kernel_recheckable_original_conjunction` returns
/// None), so O4 names that decline after the frontier's reason. Measured
/// 2026-11-06 on the load: the return equation is true but unreflectable.
/// The machine assembles the u64 as an `Or` of zero-extended memory reads
/// shifted by 8·i; the bit route (`scalar_bits`) has no `Select` arm, and the
/// fallback (`reflect` and `original_value`) has no shift arm. Each leg must
/// name its own refusal. Returns what differs.
#[cfg(feature = "ay-proofs")]
pub fn pointer_memory_refusal(
    c: &trust_cg_bridge::call_event::FunctionCertificate,
    darwin: bool,
) -> Result<(), String> {
    const FRONTIER: &str = "PTR.3b source memory modeled (1 access path(s)";
    const DECLINED: &str = "leaf original scalar/ABI/coverage/exit-memory joint kernel declined";
    let o4 = &c.obligations.o4_return.detail;
    let leaf = c.leaf_memory.as_ref().map(|d| d.status.as_str()).unwrap_or("<no leaf diagnostic>");
    if !o4.starts_with(FRONTIER) {
        return Err(format!("O4 does not open with the PTR.3b frontier: {o4}"));
    }
    let (o4_ok, leaf_ok) = if darwin {
        (o4.ends_with(&format!("; {DECLINED}; Unknown")), leaf.starts_with(DECLINED))
    } else {
        (!o4.contains("joint kernel"), leaf.starts_with("leaf evidence unavailable: "))
    };
    if o4_ok && leaf_ok {
        Ok(())
    } else {
        Err(format!("darwin={darwin}: O4 `{o4}`, leaf `{leaf}`"))
    }
}

/// Disassembly of every code section, for diagnostics.
pub fn disassemble(obj: &[u8]) -> String {
    let Ok(o) = CompiledObject::parse(obj) else { return "<unparseable object>".into() };
    let mut s = String::new();
    for sec in &o.sections {
        if sec.class != trust_cg_bridge::compiled_object::SectionClass::Code {
            continue;
        }
        s.push_str(&format!("section {}\n", sec.name));
        for (i, w) in sec.bytes.chunks(4).enumerate() {
            let off = (i * 4) as u64;
            for sym in o.symbols.iter().filter(|y| y.section == Some(sec.index) && y.value == off) {
                s.push_str(&format!("{}:\n", sym.raw_name));
            }
            let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
            let text = trust_disasm::decode_aarch64(w, off)
                .map(|i| format!("{:?} {:?}", i.opcode, i.operands().collect::<Vec<_>>()))
                .unwrap_or_else(|_| "<?>".into());
            let reloc = sec
                .relocations
                .iter()
                .find(|r| r.offset == off)
                .map(|r| {
                    format!(
                        "   ; {} {}",
                        r.kind.name(),
                        o.reloc_symbol(r).map_or("", |y| y.raw_name.as_str())
                    )
                })
                .unwrap_or_default();
            s.push_str(&format!("  {off:4x}: {word:08x}  {text}{reloc}\n"));
        }
    }
    s
}

// ===========================================================================
// MACHINE-SIDE OBJECT PATCHERS
// ===========================================================================

fn rd32(o: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(o[at..at + 4].try_into().unwrap())
}
fn rd64(o: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(o[at..at + 8].try_into().unwrap())
}
fn wr32(o: &mut [u8], at: usize, v: u32) {
    o[at..at + 4].copy_from_slice(&v.to_le_bytes());
}
fn wr64(o: &mut [u8], at: usize, v: u64) {
    o[at..at + 8].copy_from_slice(&v.to_le_bytes());
}

pub fn is_macho(o: &[u8]) -> bool {
    rd32(o, 0) == 0xfeed_facf
}

/// Mach-O: (file offset of each section header, sectname, segname).
fn macho_section_headers(o: &[u8]) -> Vec<(usize, String, String)> {
    let mut out = Vec::new();
    let ncmds = rd32(o, 16) as usize;
    let mut c = 32;
    for _ in 0..ncmds {
        let cmd = rd32(o, c);
        let size = rd32(o, c + 4) as usize;
        if cmd == 0x19 {
            let n = rd32(o, c + 64) as usize;
            for i in 0..n {
                let h = c + 72 + i * 80;
                let name = |b: &[u8]| {
                    String::from_utf8_lossy(&b[..b.iter().position(|x| *x == 0).unwrap_or(16)])
                        .into_owned()
                };
                out.push((h, name(&o[h..h + 16]), name(&o[h + 16..h + 32])));
            }
        }
        c += size;
    }
    out
}

/// Mach-O LC_SYMTAB (symoff, nsyms, stroff, strsize).
fn macho_symtab(o: &[u8]) -> (usize, usize, usize, usize) {
    let ncmds = rd32(o, 16) as usize;
    let mut c = 32;
    for _ in 0..ncmds {
        if rd32(o, c) == 0x2 {
            return (
                rd32(o, c + 8) as usize,
                rd32(o, c + 12) as usize,
                rd32(o, c + 16) as usize,
                rd32(o, c + 20) as usize,
            );
        }
        c += rd32(o, c + 4) as usize;
    }
    panic!("no LC_SYMTAB");
}

/// ELF: section header offsets and names.
fn elf_sections(o: &[u8]) -> Vec<(usize, String)> {
    let shoff = rd64(o, 40) as usize;
    let shnum = u16::from_le_bytes([o[60], o[61]]) as usize;
    let shstrndx = u16::from_le_bytes([o[62], o[63]]) as usize;
    let names = rd64(o, shoff + shstrndx * 64 + 24) as usize;
    (0..shnum)
        .map(|i| {
            let h = shoff + i * 64;
            let n = names + rd32(o, h) as usize;
            let end = o[n..].iter().position(|b| *b == 0).unwrap();
            (h, String::from_utf8_lossy(&o[n..n + end]).into_owned())
        })
        .collect()
}

/// File offset of the (single) code section's bytes.
pub fn text_file_offset(o: &[u8]) -> usize {
    if is_macho(o) {
        let (h, ..) =
            macho_section_headers(o).into_iter().find(|(_, s, _)| s == "__text").expect("__text");
        rd32(o, h + 48) as usize
    } else {
        let (h, _) = elf_sections(o).into_iter().find(|(_, n)| n == ".text").expect(".text");
        rd64(o, h + 24) as usize
    }
}

/// The in-section offset of symbol `name`'s definition.
pub fn symbol_offset(o: &[u8], name: &str) -> u64 {
    let obj = CompiledObject::parse(o).expect("parses");
    obj.symbols
        .iter()
        .find(|s| s.name == name && s.section.is_some())
        .map(|s| s.value)
        .unwrap_or_else(|| panic!("no symbol `{name}`"))
}

/// The in-section offsets of `name`'s instruction words, `[start, end)`.
pub fn function_words(o: &[u8], name: &str) -> Vec<(u64, u32)> {
    let obj = CompiledObject::parse(o).expect("parses");
    let start = symbol_offset(o, name);
    let text = obj
        .sections
        .iter()
        .find(|s| s.class == trust_cg_bridge::compiled_object::SectionClass::Code)
        .unwrap();
    let mut next = text.size;
    for s in &obj.symbols {
        if s.section == Some(text.index)
            && s.value > start
            && s.value < next
            && !s.name.starts_with('$')
        {
            next = s.value;
        }
    }
    (start..next).step_by(4).map(|off| (off, rd32(&text.bytes, off as usize))).collect()
}

/// Read the instruction word at in-section offset `off`.
pub fn word_at(o: &[u8], off: u64) -> u32 {
    rd32(o, text_file_offset(o) + off as usize)
}

/// Overwrite the instruction word at in-section offset `off`.
pub fn patch_word(o: &mut [u8], off: u64, word: u32) {
    let at = text_file_offset(o) + off as usize;
    wr32(o, at, word);
}

/// File offsets of the code section's relocation records, in table order.
fn text_reloc_records(o: &[u8]) -> Vec<usize> {
    if is_macho(o) {
        let (h, ..) = macho_section_headers(o).into_iter().find(|(_, s, _)| s == "__text").unwrap();
        let reloff = rd32(o, h + 56) as usize;
        let n = rd32(o, h + 60) as usize;
        (0..n).map(|i| reloff + i * 8).collect()
    } else {
        let (h, _) =
            elf_sections(o).into_iter().find(|(_, n)| n == ".rela.text").expect(".rela.text");
        let off = rd64(o, h + 24) as usize;
        let size = rd64(o, h + 32) as usize;
        (0..size / 24).map(|i| off + i * 24).collect()
    }
}

/// (record file offset, in-section offset, raw type, symbol index) of each
/// code relocation (Mach-O ADDEND records included as they are).
pub fn text_relocs(o: &[u8]) -> Vec<(usize, u64, u32, usize)> {
    text_reloc_records(o)
        .into_iter()
        .map(|r| {
            if is_macho(o) {
                let w1 = rd32(o, r + 4);
                (r, u64::from(rd32(o, r)), w1 >> 28, (w1 & 0xff_ffff) as usize)
            } else {
                let info = rd64(o, r + 8);
                (r, rd64(o, r), (info & 0xffff_ffff) as u32, (info >> 32) as usize)
            }
        })
        .collect()
}

pub fn set_reloc_offset(o: &mut [u8], record: usize, off: u64) {
    if is_macho(o) {
        wr32(o, record, off as u32);
    } else {
        wr64(o, record, off);
    }
}

pub fn set_reloc_type(o: &mut [u8], record: usize, ty: u32) {
    if is_macho(o) {
        let w1 = rd32(o, record + 4);
        wr32(o, record + 4, (w1 & 0x0fff_ffff) | (ty << 28));
    } else {
        let info = rd64(o, record + 8);
        wr64(o, record + 8, (info & 0xffff_ffff_0000_0000) | u64::from(ty));
    }
}

pub fn set_reloc_symbol(o: &mut [u8], record: usize, sym: usize) {
    if is_macho(o) {
        let w1 = rd32(o, record + 4);
        wr32(o, record + 4, (w1 & 0xff00_0000) | (sym as u32 & 0xff_ffff));
    } else {
        let info = rd64(o, record + 8);
        wr64(o, record + 8, (info & 0xffff_ffff) | ((sym as u64) << 32));
    }
}

/// ELF: set the explicit addend of the RELA record at file offset `record`.
pub fn set_elf_reloc_addend(o: &mut [u8], record: usize, addend: i64) {
    assert!(!is_macho(o), "a Mach-O relocation carries no explicit addend");
    wr64(o, record + 16, addend as u64);
}

/// ELF: the symbol-table index of the section symbol (`STT_SECTION`) of the
/// section `function` is defined in, and `function`'s offset in that section.
pub fn elf_section_symbol_of(o: &[u8], function: &str) -> (usize, u64) {
    use trust_cg_bridge::compiled_object::SymbolKind;
    let obj = CompiledObject::parse(o).expect("parses");
    let f = obj.symbols.iter().find(|s| s.name == function).expect("function symbol");
    let sec = f.section.expect("a defined function");
    let s = obj
        .symbols
        .iter()
        .find(|s| s.kind == SymbolKind::Section && s.section == Some(sec))
        .unwrap_or_else(|| panic!("no section symbol for `{function}`'s section"));
    (s.index, f.value)
}

/// The symbol-table index of `name`.
pub fn symbol_index(o: &[u8], name: &str) -> usize {
    let obj = CompiledObject::parse(o).expect("parses");
    obj.symbols
        .iter()
        .find(|s| s.name == name)
        .map(|s| s.index)
        .unwrap_or_else(|| panic!("no symbol `{name}`"))
}

/// File offset of symbol `index`'s table entry.
fn symbol_entry(o: &[u8], index: usize) -> usize {
    if is_macho(o) {
        macho_symtab(o).0 + index * 16
    } else {
        let (h, _) = elf_sections(o).into_iter().find(|(_, n)| n == ".symtab").expect(".symtab");
        rd64(o, h + 24) as usize + index * 24
    }
}

/// Move symbol `name`'s value by `delta` bytes.
pub fn shift_symbol(o: &mut [u8], name: &str, delta: i64) {
    let e = symbol_entry(o, symbol_index(o, name));
    // n_value (Mach-O nlist_64) and st_value (ELF64 Sym) both sit at +8.
    let at = e + 8;
    let v = rd64(o, at);
    wr64(o, at, (v as i64 + delta) as u64);
}

/// ELF: set symbol `name`'s `st_size`.
pub fn set_elf_symbol_size(o: &mut [u8], name: &str, size: u64) {
    let e = symbol_entry(o, symbol_index(o, name));
    wr64(o, e + 16, size);
}

/// Flip symbol `name` between local and global binding.
pub fn flip_symbol_binding(o: &mut [u8], name: &str) {
    let e = symbol_entry(o, symbol_index(o, name));
    if is_macho(o) {
        o[e + 4] ^= 0x01; // N_EXT
    } else {
        // Every local symbol precedes every other, and `.symtab`'s `sh_info`
        // is the first non-local index: the flipped symbol is first moved to
        // that boundary (swapping table entries and renumbering every
        // relocation), so the reader sees the flipped binding rather than a
        // disordered table.
        let index = symbol_index(o, name);
        let (h, _) = elf_sections(o).into_iter().find(|(_, n)| n == ".symtab").expect(".symtab");
        let first_global = rd32(o, h + 44) as usize;
        let bind = o[e + 4] >> 4;
        let (slot, moved) = if bind == 0 {
            assert_eq!(index + 1, first_global, "`{name}` is the last local symbol");
            (index, first_global - 1)
        } else {
            swap_elf_symbols(o, index, first_global);
            (first_global, first_global + 1)
        };
        let at = symbol_entry(o, slot);
        let flipped = if bind == 0 { 1 } else { 0 };
        o[at + 4] = (flipped << 4) | (o[at + 4] & 0xf);
        o[h + 44..h + 48].copy_from_slice(&u32::try_from(moved).unwrap().to_le_bytes());
    }
}

/// Swap ELF symbol-table entries `a` and `b`, renumbering every `SHT_RELA`
/// entry that names either.
fn swap_elf_symbols(o: &mut [u8], a: usize, b: usize) {
    if a == b {
        return;
    }
    let (ea, eb) = (symbol_entry(o, a), symbol_entry(o, b));
    let entry_a: Vec<u8> = o[ea..ea + 24].to_vec();
    o.copy_within(eb..eb + 24, ea);
    o[eb..eb + 24].copy_from_slice(&entry_a);
    let shoff = rd64(o, 40) as usize;
    let shnum = usize::from(u16::from_le_bytes([o[60], o[61]]));
    let relas: Vec<usize> =
        (0..shnum).map(|i| shoff + i * 64).filter(|h| rd32(o, h + 4) == 4).collect();
    for h in relas {
        let (ro, rs) = (rd64(o, h + 24) as usize, rd64(o, h + 32) as usize);
        for r in (ro..ro + rs).step_by(24) {
            let info = rd64(o, r + 8);
            let s = (info >> 32) as usize;
            let s = if s == a {
                b
            } else if s == b {
                a
            } else {
                s
            };
            let info = ((s as u64) << 32) | (info & 0xffff_ffff);
            o[r + 8..r + 16].copy_from_slice(&info.to_le_bytes());
        }
    }
}

/// Rename the first section whose name is `from` to `to` (same length).
pub fn rename_section(o: &mut [u8], from: &str, to: &str) {
    assert_eq!(from.len(), to.len());
    if is_macho(o) {
        let (h, ..) = macho_section_headers(o)
            .into_iter()
            .find(|(_, s, _)| s == from)
            .unwrap_or_else(|| panic!("no section {from}"));
        o[h..h + from.len()].copy_from_slice(to.as_bytes());
    } else {
        let shoff = rd64(o, 40) as usize;
        let shstrndx = u16::from_le_bytes([o[62], o[63]]) as usize;
        let names = rd64(o, shoff + shstrndx * 64 + 24) as usize;
        let (h, _) = elf_sections(o)
            .into_iter()
            .find(|(_, n)| n == from)
            .unwrap_or_else(|| panic!("no section {from}"));
        let n = names + rd32(o, h) as usize;
        o[n..n + from.len()].copy_from_slice(to.as_bytes());
    }
}

/// The names of every section.
pub fn section_names(o: &[u8]) -> Vec<String> {
    if is_macho(o) {
        macho_section_headers(o).into_iter().map(|(_, s, g)| format!("{g},{s}")).collect()
    } else {
        elf_sections(o).into_iter().map(|(_, n)| n).collect()
    }
}

// ===========================================================================
// A64 ENCODINGS
// ===========================================================================

pub const NOP: u32 = 0xd503_201f;
pub const RET: u32 = 0xd65f_03c0;

pub fn is_bl(w: u32) -> bool {
    w & 0xfc00_0000 == 0x9400_0000
}
pub fn is_b(w: u32) -> bool {
    w & 0xfc00_0000 == 0x1400_0000
}
pub fn enc_bl(delta: i64) -> u32 {
    0x9400_0000 | ((delta / 4) as u32 & 0x03ff_ffff)
}
pub fn enc_b(delta: i64) -> u32 {
    0x1400_0000 | ((delta / 4) as u32 & 0x03ff_ffff)
}
/// `mov xd, xm` (orr xd, xzr, xm).
pub fn enc_mov(d: u32, m: u32) -> u32 {
    0xaa00_03e0 | (m << 16) | d
}
/// `mov xd, sp` (add xd, sp, #0).
pub fn enc_mov_from_sp(d: u32) -> u32 {
    0x9100_03e0 | d
}
/// `add xd, xn, #imm`.
pub fn enc_add_imm(d: u32, n: u32, imm: u32) -> u32 {
    0x9100_0000 | (imm << 10) | (n << 5) | d
}
/// `str xt, [sp, #imm]` (unsigned offset, imm a multiple of 8).
pub fn enc_str_sp(t: u32, imm: u32) -> u32 {
    0xf900_0000 | ((imm / 8) << 10) | (31 << 5) | t
}

/// Offsets of every `bl` in `name`.
pub fn bl_offsets(o: &[u8], name: &str) -> Vec<u64> {
    function_words(o, name).into_iter().filter(|(_, w)| is_bl(*w)).map(|(off, _)| off).collect()
}

/// The code relocation record sitting at in-section offset `off`.
pub fn reloc_at(o: &[u8], off: u64) -> (usize, u32, usize) {
    text_relocs(o)
        .into_iter()
        .filter(|(_, at, ty, _)| *at == off && !(is_macho(o) && *ty == 10))
        .map(|(r, _, ty, sym)| (r, ty, sym))
        .next()
        .unwrap_or_else(|| panic!("no relocation at {off:#x}"))
}

/// Delete the code relocation `record` (the last record is moved into its slot
/// and the count shrinks by one).
pub fn delete_reloc(o: &mut [u8], record: usize) {
    let records = text_reloc_records(o);
    let last = *records.last().expect("a relocation to delete");
    let size = if is_macho(o) { 8 } else { 24 };
    let bytes = o[last..last + size].to_vec();
    o[record..record + size].copy_from_slice(&bytes);
    if is_macho(o) {
        let (h, ..) = macho_section_headers(o).into_iter().find(|(_, s, _)| s == "__text").unwrap();
        let n = rd32(o, h + 60);
        wr32(o, h + 60, n - 1);
    } else {
        let (h, _) = elf_sections(o).into_iter().find(|(_, n)| n == ".rela.text").unwrap();
        let sz = rd64(o, h + 32);
        wr64(o, h + 32, sz - 24);
    }
}
