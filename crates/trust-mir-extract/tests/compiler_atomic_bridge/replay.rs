// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Closed ByteV1 execution of the ORIGINAL compiler-owned lowered module.
//! No module fixture, JSON round trip, ABI relabeling, or instruction rewrite
//! occurs here. This does not establish Rust/MIR refinement, discharge pending
//! obligations, prove concurrent behavior, or cover production Arc/Name code.

use std::sync::OnceLock;

use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};
use clean_verify::eval_ir::{EvalIrVocabulary, shared_specification_with_stack};
use trust_ir::{BlockId, Constant, FuncId, Inst, Module, ProofStatus, Ty, ValueId};
use trust_ir_build::core_execution::{
    Assembler, BranchPremises, Catalog, Coordinate, EntryTarget, Limits, MachineModel,
    MemoryPremises, MemoryResult, NatTerm, PendingEquality, ScalarPremises,
};
use trust_ir_build::core_reflection::reflect_core_module_v1;
use trust_ir_build::scoped_local::LocalScope;
use trust_ir_build::translation::{
    SourceTranslationModel, TranslationProofEncoding, TranslationRechecker,
};

#[path = "replay/proof.rs"]
mod proof;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}
fn app(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(c(name), args)
}
fn nat(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn scalar(value: u64) -> Expr {
    app("IRScalar.int_", [nat(value)])
}
fn pointer(value: u64) -> Expr {
    app("IRScalar.ptr_", [nat(value)])
}
fn list(ty: &str, values: &[Expr]) -> Expr {
    values.iter().rev().fold(app("IRList.nil", [c(ty)]), |tail, value| {
        app("IRList.cons", [c(ty), value.clone(), tail])
    })
}
fn eq(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [ty, value],
    )
}
fn providers() -> Expr {
    let lam = |ty, body| Expr::lam(BinderInfo::Default, ty, body);
    lam(
        c("Nat"),
        lam(
            app("IRList", [c("IRScalar")]),
            lam(
                c("IRByteMemoryV1"),
                lam(
                    c("Nat"),
                    app(
                        "IRByteImportResultV1.mk",
                        [
                            c("Nat"),
                            app("IROutcome.stuck", [c("IRFault.no_func")]),
                            Expr::bvar(1),
                            Expr::bvar(0),
                        ],
                    ),
                ),
            ),
        ),
    )
}

fn allocations() -> Expr {
    list(
        "IRByteAllocationV1",
        &[
            app("IRByteAllocationV1.mk", [nat(16), nat(32), nat(0), c("Bool.true")]),
            app("IRByteAllocationV1.mk", [nat(80), nat(8), nat(7), c("Bool.false")]),
        ],
    )
}
fn background(frame_word: u64) -> Expr {
    app(
        "ir_byte_write_word_v1",
        [
            Expr::lam(BinderInfo::Default, c("Nat"), app("IROption.some", [c("Nat"), nat(173)])),
            nat(32),
            nat(8),
            nat(frame_word),
        ],
    )
}
fn memory_from(bytes: Expr) -> Expr {
    app("IRByteMemoryV1.mk", [allocations(), bytes, nat(128)])
}
fn memory(frame_word: u64) -> Expr {
    memory_from(app("ir_byte_write_word_v1", [background(frame_word), nat(16), nat(8), nat(41)]))
}
fn written(frame_word: u64, value: u64) -> Expr {
    memory_from(app(
        "ir_byte_write_word_v1",
        [app("ir_byte_mem_bytes_v1", [memory(frame_word)]), nat(16), nat(8), nat(value)],
    ))
}

#[derive(Clone)]
struct Invocation {
    pointer: u64,
    old: u64,
    new: u64,
    frame_word: u64,
    host: u64,
    next_owner: u64,
    owners: Vec<Expr>,
}
impl Default for Invocation {
    fn default() -> Self {
        Self {
            pointer: 16,
            old: 41,
            new: 48,
            frame_word: 77,
            host: 37,
            next_owner: 9,
            owners: vec![],
        }
    }
}
fn terminal(invocation: &Invocation) -> Expr {
    // Independent complete postcondition, not copied from an assembler result.
    let world = app(
        "IRByteWorldV1.mk",
        [
            c("Nat"),
            written(invocation.frame_word, invocation.new),
            nat(invocation.host),
            list("Nat", &invocation.owners),
            nat(invocation.next_owner),
        ],
    );
    app(
        "IRByteConfigV1.halted",
        [c("Nat"), app("IROutcome.ret", [list("IRScalar", &[scalar(invocation.old)])]), world],
    )
}
fn initial(model: &MachineModel, address: u64) -> Expr {
    app(
        "ir_byte_init_v1",
        [
            c("Nat"),
            model.context().clone(),
            nat(0),
            list("IRScalar", &[pointer(address)]),
            memory(77),
            nat(37),
        ],
    )
}
struct SequentialAtomicModel;
impl SourceTranslationModel for SequentialAtomicModel {
    type Source = Invocation;
    fn build_environment() -> Result<Environment, String> {
        Ok(shared_specification_with_stack(EvalIrVocabulary::ByteV1)
            .map_err(|error| error.to_string())?
            .env()
            .clone())
    }
    fn reconstruct(source: &Invocation, target: &Module) -> Result<Expr, String> {
        let reflected = reflect_core_module_v1(target, &[(FuncId::new(0), 4096)])
            .map_err(|error| error.to_string())?;
        let function = reflected.function(FuncId::new(0)).ok_or("missing wrapper")?;
        let signature = target.func_type(function.ty).ok_or("missing signature")?;
        if signature.params != [Ty::Ptr] || signature.returns != [Ty::U64] {
            return Err("expected the measured scalar U64 wrapper signature".into());
        }
        let model = MachineModel::new(c("Nat"), &reflected, providers());
        Ok(eq(
            model.config_type(),
            model.run(&NatTerm::literal(8), initial(&model, source.pointer)),
            terminal(source),
        ))
    }
}
fn checker() -> &'static TranslationRechecker<SequentialAtomicModel> {
    static CHECKER: OnceLock<TranslationRechecker<SequentialAtomicModel>> = OnceLock::new();
    CHECKER.get_or_init(|| TranslationRechecker::new(Default::default()).unwrap())
}

/// Candidate postconditions are reconstructed from the same original module;
/// a rejected changed endpoint must be a semantic kernel failure, not a limit.
fn rejects(source: &Invocation, module: &Module, proof: &[u8]) {
    let error = checker().recheck_dag_v2(source, module, proof).unwrap_err();
    assert_eq!(error.stage(), "kernel audit", "{error}");
    for resource in ["heartbeat", "budget", "timeout", "fuel exhausted", "recursion limit"] {
        assert!(
            !error.reason().to_ascii_lowercase().contains(resource),
            "semantic refusal required: {error}"
        );
    }
}

/// Receives the original value returned by compiler-owned lowering. The
/// invocation is an explicit sequential model contract, not a Rust source
/// semantics claim: external live storage at 16 initially holds 41, and the
/// independently specified whole terminal world holds 48 and returns 41.
pub(super) fn actual_u64(module: &Module) {
    let before = module.clone(); // Equality snapshot only, NOT the positive input.
    let invocation = Invocation::default();
    let proof = proof::assemble(module);
    let checked = checker().recheck_dag_v2(&invocation, module, &proof).unwrap();
    assert!(std::ptr::eq(checked.target(), module));
    assert!(std::ptr::eq(checked.source(), &invocation));
    assert_eq!(checked.proof_term(), proof);
    assert_eq!(checked.proof_encoding(), TranslationProofEncoding::LosslessDagV2);

    // Independently change each observation while retaining the SAME proof.
    // Both pointer addresses are live, aligned, initialized in the initial
    // memory; the substitution is not merely a malformed pointer control.
    for changed in [
        Invocation { old: 48, ..Invocation::default() },
        Invocation { new: 41, ..Invocation::default() },
        Invocation { frame_word: 78, ..Invocation::default() },
        Invocation { host: 38, ..Invocation::default() },
        Invocation { next_owner: 8, ..Invocation::default() },
        Invocation { owners: vec![nat(8)], ..Invocation::default() },
        Invocation { pointer: 32, ..Invocation::default() },
    ] {
        rejects(&changed, module, &proof);
    }

    // Clones are NEGATIVE controls only. These retain a well-formed program
    // but change its semantics, so the proof must not attach to either.
    let mut changed = module.clone();
    changed.functions[0].blocks[0].body[4].inst =
        Inst::Const { ty: Ty::U64, value: Constant::Int(8) };
    assert!(trust_ir_build::validate_module(&changed).is_empty());
    rejects(&invocation, &changed, &proof);
    let mut changed = module.clone();
    changed.functions[0].blocks[1].body[0].inst = Inst::Return { values: vec![ValueId::new(8)] };
    assert!(trust_ir_build::validate_module(&changed).is_empty());
    rejects(&invocation, &changed, &proof);
    let mut changed = module.clone();
    changed.structs[1].fields[0].offset = Some(8);
    assert!(reflect_core_module_v1(&changed, &[(FuncId::new(0), 4096)]).is_err());

    assert_eq!(*module, before, "replay must preserve the entire original module");
    assert_eq!(module.proof_obligations.len(), 2);
    assert!(module.proof_obligations.iter().all(|row| row.status == ProofStatus::Pending));
    assert!(module.proof_obligations.iter().all(|row| row.spec.is_none()));
    assert!(module.proof_certificates.is_empty());
    assert!(module.completeness.is_none());
    assert!(module.functions.iter().all(|function| function.source_provenance.is_none()));
    println!(
        "ACTUAL_ATOMIC_REPLAY function={} profile=ByteV1 encoding=LosslessDagV2 \
         closed_invocations=1 endpoint_refusals=7 module_kernel_refusals=2 \
         layout_refusals=1 pending_obligations=2 source_refinement=unproved concurrency=unproved",
        module.functions[0].name
    );
}

/// Trust-IR 412dedab ("Reflect nominal Usize64 byte operations with checked
/// sequential replay", pinned since ca1ef61a3a) admits nominal `Usize` ONLY on
/// an actual supported 64-bit little-endian target, as `IRTy.usize_ 64` -- a
/// distinct nominal type, never an equal-width U64 alias -- and admits its
/// atomic only as Add/Relaxed through the target-indexed
/// `IRInst.atomic_fetch_add_relaxed_usize_seq`, whose width is read from the
/// module's target (`usize_bits`), not assumed. This compiler-owned module
/// carries exactly such a target, so reflection now succeeds. Reflection is not
/// replay: no closed invocation, source refinement, or concurrency claim is
/// attached to the Usize module here, and the unsupported-target, ordering and
/// operation refusals remain fail-closed.
pub(super) fn usize_reflected(module: &Module) {
    fn contains(term: &Expr, needle: &Expr) -> bool {
        term == needle || term.get_app_args_iter().any(|arg| contains(arg, needle))
    }
    let before = module.clone();
    let reflected = reflect_core_module_v1(module, &[(FuncId::new(0), 4096)])
        .expect("target-authenticated Usize64 reflects in the ByteV1 atomic profile");
    assert!(std::ptr::eq(reflected.module(), module), "reflection borrows the original");
    let context = reflected.context_term();
    // The actual SSA operands (pointer v7, increment v8) at the target's width.
    assert!(contains(
        context,
        &app("IRInst.atomic_fetch_add_relaxed_usize_seq", [nat(64), nat(7), nat(8)])
    ));
    assert!(contains(context, &app("IRTy.usize_", [nat(64)])));
    assert!(
        !contains(context, &app("IRInst.atomic_fetch_add_relaxed_u64_seq", [nat(7), nat(8)])),
        "nominal Usize must not be relabeled as the U64 atomic"
    );
    assert_eq!(*module, before, "reflection must preserve original metadata");

    // Fail-closed controls on diagnostic clones: the admission is target-indexed
    // and exactly Add/Relaxed.
    let refused =
        |candidate: &Module| reflect_core_module_v1(candidate, &[(FuncId::new(0), 4096)]).is_err();
    let mut changed = module.clone();
    changed.target_info = None;
    assert!(refused(&changed), "Usize without a target has no width");
    let mut changed = module.clone();
    changed.target_info.as_mut().expect("compiler target").pointer_size = 4;
    assert!(refused(&changed), "a 32-bit target is not admitted");
    let mut changed = module.clone();
    changed.target_info.as_mut().expect("compiler target").endianness = trust_ir::Endianness::Big;
    assert!(refused(&changed), "a big-endian target is not admitted");
    let mut changed = module.clone();
    let Inst::AtomicRMW { ordering, .. } = &mut changed.functions[0].blocks[0].body[5].inst else {
        panic!("the sixth emitted node is the atomic")
    };
    *ordering = trust_ir::inst::Ordering::SeqCst;
    assert!(refused(&changed), "only Relaxed has sequential atomic reflection");
    let mut changed = module.clone();
    let Inst::AtomicRMW { op, .. } = &mut changed.functions[0].blocks[0].body[5].inst else {
        panic!("the sixth emitted node is the atomic")
    };
    *op = trust_ir::inst::AtomicRMWOp::Sub;
    assert!(refused(&changed), "only Add has sequential atomic reflection");
}
