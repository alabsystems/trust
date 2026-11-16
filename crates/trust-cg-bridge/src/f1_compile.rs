// trust-cg-bridge/f1_compile.rs — F1's SHIPPING CONSUMER for the compiler lane
// (increment 5, step 5.4.1): one `trust_ir::Module` (M_cg) compiled by
// trust-cg's `Compiler::compile`, the call-event refinement gate run over the
// bytes that come back, and those SAME bytes handed out only when
// `CerReport::ships` allows them under the policy.
//
// Design of record: docs/design/2026-10-01-step2-inc5-real-calls-retarget.md
// §3 and §5.4; implementation plan
// docs/design/2026-10-08-step2-inc5-step4-compiler-lane-plan.md §1 (sub-step
// 5.4.1); D30-D32 and the decisions INC5.4-GLUE, -JUMPTABLE,
// -STACK, -PARALLEL, -PIC and -CER-LANE in docs/DECISION_QUEUE.md.
//
// WHAT IT DOES, in order, on ONE thread of its own (`GATE_STACK_BYTES`):
//   1. BOUNDARY — a body trust-cg must not see is refused before trust-cg sees
//      it: a Clean-origin body (step 3 owns admitting those), a body of a
//      deprecated producer (tSwift, tC), and any body carrying a check with no
//      faithful panic to deliver: an `Assert` without a `PanicSite` (there is
//      no entry to call and no location to report), a sited `Assert` whose
//      kind is `Unspecified` (the check names no Rust panic), and every
//      `AssertInvoke` (the unwinding form, which PKG-CP does not admit). A
//      sited `Assert` of a named kind passes the boundary (PKG-CP): trust-cg
//      lowers its failure to `call entry(operands.., location)` then a trap
//      (trust-ir SPEC_RATIFICATIONS §19.1). Passing the boundary grants
//      nothing: the census, the compile and the gate below still decide. The
//      gate does not model the failure call yet; it grades such a function
//      Unknown (O2: "a divergent call event, modeled at step 5.7"), so strict
//      refuses it at step 7 and only allow-unknown ships it. That is a defect
//      of the gate, not policy; tests/f1_compile.rs
//      `a_sited_overflow_check_is_unknown_strict_refuses_and_allow_unknown_ships`
//      pins the measured result. The producer emits no site; on the compiler
//      lane the rustc plugin sites each check of its codegen module that it
//      can match to rustc's own MIR `Assert` and folds each constant-true one
//      (`trust_ir_frontend::panic_sites`, PKG-CP), and refuses a function with
//      any other check before this boundary. The `lir` lanes still refuse every
//      reachable `Assert` (`refuse_unfaithful_panic`).
//   2. CENSUS — `Compiler::preflight` under the D31 license (exactly
//      `trust-direct-lane-structural` and `trust-instance-lane-structural`,
//      plus `trust-upstream-mir-lane` only when the caller says that flag is
//      set; a claim-less body is REFUSED). Every row is reported; nothing is
//      compiled when there is one.
//   3. COMPILE — `Compiler::compile` with the configuration of design §3.2:
//      proofs, debug info, unwind tables, the superoptimizer, the artifact
//      cache and the parallel pipeline all off.
//   4. RESULT CONTRACT — the result must carry exactly what this
//      configuration produces and nothing a later reader could mistake for
//      evidence: a non-empty object, no proofs, no certified pass chain, no
//      trace, no inline-only body premise, no stack-limit or dialect report,
//      no cache telemetry, and the explicit target that was asked for.
//      `proof_optimization_certificates` is never read for a decision: under
//      D31(c) the gate is F1's only shipping authority.
//   5. GATE — `call_event::verify_compiled_module` over `object_code`.
//   6. BINDING — the report's object digest is the digest of those bytes.
//   7. SHIPPING — `CerReport::ships(policy)` is the ONLY decision. No
//      certificate grade is read here: a per-function [PROVED] is not the
//      shipping grade (the closure is).
//   8. DISCLOSURE — under allow-unknown, every function the closure could not
//      close is named with what blocks it.
//
// WHAT IT DOES NOT DO. It does not build M_cg, S or P (the rustc plugin does,
// from rustc's FnAbi, at step 5.4.2); it trusts none of them either — the gate
// reads the producer bodies and P against the bytes. Nothing in the rustc
// plugin calls this module at 5.4.1, so nothing ships through it yet.
//
// FAIL-CLOSED. A panic anywhere on the gate thread is a refusal
// (`F1Refusal::Gate`); a stack overflow aborts the process before an object
// exists, which ships nothing. `RUST_MIN_STACK` cannot shrink the thread: its
// size is explicit.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use sha2::{Digest, Sha256};
use trust_cg_codegen::lir_module_prep::InlineOnlyBodyEvidence;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CompilationResult, CompileError, Compiler, CompilerConfig, TargetSelectionOrigin,
};
use trust_cg_lower::{
    CodegenLicensePolicy, RelocationModel as CgRelocationModel, UnlicensedBodyPolicy,
};
use trust_ir::inst::Inst;
use trust_ir::value::FuncId;
use trust_ir::{Module, Producer};

use crate::call_event::{
    CerInput, CerReport, FnPlacement, ProducerBody, ProducerModule, verify_compiled_module,
};
use crate::compiled_object::{ObjectRefusal, RelocationModel, hex};
use crate::verify_output::EmitPolicy;

#[path = "f1_compile/native_questions.rs"]
mod native_questions;
pub use native_questions::{F1NativeQuestionCompilation, NativeQuestionFunctionBinding};

// ===========================================================================
// THE D31 LICENSE
// ===========================================================================

/// The authority the direct (handoff) lane stamps on a body it admitted
/// (`crates/trust-thir-lower/src/crate_module.rs`).
pub const TRUST_DIRECT_LANE_AUTHORITY: &str = "trust-direct-lane-structural";

/// The authority the instance lane stamps on a body it assembled
/// (`compiler/rustc_codegen_trust_cg/src/trust_ir_frontend/instance_assembly.rs`).
pub const TRUST_INSTANCE_LANE_AUTHORITY: &str = "trust-instance-lane-structural";

/// The consumer-stamped authority of `-Ztrust-ir-upstream-mir` bodies (D31(b)),
/// recognized only while that flag is set.
pub const TRUST_UPSTREAM_MIR_LANE_AUTHORITY: &str = "trust-upstream-mir-lane";

/// The gate thread's stack (INC5.4-STACK). MEASURED at step 5.2: the gate
/// overflows a 2 MiB stack on an O0 spill-heavy body in a debug build.
pub const GATE_STACK_BYTES: usize = 16 << 20;
const _: () = assert!(GATE_STACK_BYTES >= 8 << 20);

/// The D31 codegen license: exactly the direct and instance lane authorities,
/// plus the upstream-MIR authority when `upstream_mir_lane` is true, and a
/// claim-less body REFUSED (`recognizing_nothing()` alone would permit it).
/// The drop-glue lane's authority is not recognized (INC5.4-GLUE).
#[must_use]
pub fn f1_codegen_license(upstream_mir_lane: bool) -> CodegenLicensePolicy {
    let license = CodegenLicensePolicy::recognizing_nothing()
        .with_recognized_authority(TRUST_DIRECT_LANE_AUTHORITY)
        .with_recognized_authority(TRUST_INSTANCE_LANE_AUTHORITY)
        .with_unlicensed(UnlicensedBodyPolicy::Refuse);
    if upstream_mir_lane {
        license.with_recognized_authority(TRUST_UPSTREAM_MIR_LANE_AUTHORITY)
    } else {
        license
    }
}

// ===========================================================================
// CONFIGURATION
// ===========================================================================

/// The targets the compiler lane compiles for. Every other rustc target tuple
/// is refused (musl and every non-AArch64 target included).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum F1Target {
    /// Mach-O, Apple AArch64 ABI.
    Aarch64AppleDarwin,
    /// ELF, AAPCS64.
    Aarch64UnknownLinuxGnu,
}

impl F1Target {
    /// The target for rustc's target tuple, matched exactly; `None` refuses.
    #[must_use]
    pub fn from_rustc_tuple(tuple: &str) -> Option<Self> {
        match tuple {
            "aarch64-apple-darwin" => Some(Self::Aarch64AppleDarwin),
            "aarch64-unknown-linux-gnu" => Some(Self::Aarch64UnknownLinuxGnu),
            _ => None,
        }
    }

    /// The spelled-out triple handed to trust-cg (explicit, so the object
    /// format never comes from the host).
    #[must_use]
    pub const fn triple(self) -> &'static str {
        match self {
            Self::Aarch64AppleDarwin => "aarch64-apple-darwin",
            Self::Aarch64UnknownLinuxGnu => "aarch64-unknown-linux-gnu",
        }
    }

    /// Whether the target's objects are ELF (otherwise Mach-O).
    #[must_use]
    pub const fn is_elf(self) -> bool {
        matches!(self, Self::Aarch64UnknownLinuxGnu)
    }
}

/// rustc's `-Copt-level`, bridge-owned so the plugin needs no trust-cg-codegen
/// dependency (`s` and `z` are refused by the plugin before this point).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum F1OptLevel {
    /// `-Copt-level=0`.
    O0,
    /// `-Copt-level=1`.
    O1,
    /// `-Copt-level=2`.
    O2,
    /// `-Copt-level=3`.
    O3,
}

impl F1OptLevel {
    fn cg(self) -> OptLevel {
        match self {
            Self::O0 => OptLevel::O0,
            Self::O1 => OptLevel::O1,
            Self::O2 => OptLevel::O2,
            Self::O3 => OptLevel::O3,
        }
    }
}

/// How one M_cg is compiled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct F1CompileConfig {
    /// The target.
    pub target: F1Target,
    /// The optimization level.
    pub opt_level: F1OptLevel,
    /// rustc's relocation model (INC5.4-PIC: Linux compiles under it).
    pub relocation: RelocationModel,
    /// The effective rustc frame-pointer policy is `Always`. Requires an entry
    /// FP/LR frame on every AArch64 object function, including storage-free leaves.
    /// This changes code generation, never a body license or proof policy.
    pub force_frame_pointers: bool,
    /// Symbols the module inliner must never splice (`#[inline(never)]`).
    pub never_inline: BTreeSet<String>,
    /// Whether `-Ztrust-ir-upstream-mir` is set (D31(b)).
    pub upstream_mir_lane: bool,
}

impl F1CompileConfig {
    /// The relocation model the object is compiled under and the one the gate
    /// reads: rustc's on ELF; `Static` on Mach-O, where trust-cg implements no
    /// other (a Mach-O default definition binds within the image either way).
    #[must_use]
    pub fn compiled_relocation(&self) -> RelocationModel {
        if self.target.is_elf() { self.relocation } else { RelocationModel::Static }
    }

    /// Design §3.2's configuration. Never attaches a compile-artifact cache.
    pub(crate) fn compiler_config(&self) -> CompilerConfig {
        CompilerConfig {
            opt_level: self.opt_level.cg(),
            emit_proofs: false,
            emit_debug: false,
            // INC5.4-PARALLEL: the serial pipeline the gate tests use, until
            // step 5.5 measures determinism and cost.
            parallel: false,
            panic_unwind: false,
            cegis_superopt_budget_sec: None,
            relocation_model: match self.compiled_relocation() {
                RelocationModel::Static => CgRelocationModel::Static,
                RelocationModel::Pie => CgRelocationModel::Pie,
                RelocationModel::Pic => CgRelocationModel::Pic,
            },
            function_sections: false,
            aarch64_isa_profile: None,
            aarch64_force_frame_pointers: self.force_frame_pointers,
            never_inline: self.never_inline.clone(),
            eh_frames_cannot_unwind: false,
            ..CompilerConfig::default()
        }
    }

    fn compiler(&self) -> Result<Compiler, F1Refusal> {
        self.compiler_with_config(self.compiler_config())
    }

    fn compiler_with_config(&self, effective: CompilerConfig) -> Result<Compiler, F1Refusal> {
        let spec = TargetSpec::parse(self.target.triple()).map_err(|e| {
            F1Refusal::Compile(CensusRow {
                func: None,
                symbol: String::new(),
                variant: "TargetSpec".into(),
                detail: format!("trust-cg rejected target `{}`: {e}", self.target.triple()),
            })
        })?;
        Ok(Compiler::new_for_target_spec(effective, spec)
            .with_codegen_license(f1_codegen_license(self.upstream_mir_lane)))
    }
}

/// Everything one compile reads.
#[derive(Debug, Clone, Copy)]
pub struct F1CompileInput<'a> {
    /// The module compiled (M_cg).
    pub m_cg: &'a Module,
    /// The producer modules the gate reads the specification from.
    pub producers: &'a [ProducerModule],
    /// Each defined symbol's producer body.
    pub bodies: &'a BTreeMap<String, ProducerBody>,
    /// P, by symbol, for every definition and every callee.
    pub placements: &'a BTreeMap<String, FnPlacement>,
    /// The output-gate policy.
    pub policy: EmitPolicy,
    /// How to compile.
    pub config: &'a F1CompileConfig,
}

// ===========================================================================
// RESULTS AND REFUSALS
// ===========================================================================

/// One refused function (a census row, a boundary row, or the residual
/// compile error, which may name no function).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CensusRow {
    /// The refused function in M_cg, when the refusal names one.
    pub func: Option<FuncId>,
    /// Its symbol (empty when `func` is `None`).
    pub symbol: String,
    /// The refusal's variant (`Adapter::<variant>` for an adapter refusal).
    pub variant: String,
    /// The refusal, rendered.
    pub detail: String,
}

/// The bytes that may ship, the report they are bound to, and the disclosure.
#[derive(Debug, Clone)]
pub struct F1Shipped {
    /// The object: exactly the bytes the gate verified.
    pub object: Vec<u8>,
    /// The gate's report over `object`.
    pub report: CerReport,
    /// One line per function the closure could not close (allow-unknown):
    /// `"<symbol>: <grade>; blocked by [<callee>, ...]"`.
    pub unclosed: Vec<String>,
}

/// Why nothing ships.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum F1Refusal {
    /// A body below F1's codegen boundary (refused before trust-cg sees it).
    Boundary(Vec<CensusRow>),
    /// trust-cg's preflight census: every refused function.
    Census(Vec<CensusRow>),
    /// trust-cg's residual compile error after an empty census.
    Compile(CensusRow),
    /// The compile result carries something this configuration must not produce.
    ResultContract(String),
    /// The gate refused the whole object (O1).
    Object(ObjectRefusal),
    /// The report is not bound to the bytes compiled.
    Binding(String),
    /// `CerReport::ships` refused the object under the policy.
    Policy(String),
    /// The gate thread panicked (or could not be spawned).
    Gate(String),
}

impl std::fmt::Display for F1Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let row = |f: &mut std::fmt::Formatter<'_>, tag: &str, r: &CensusRow| {
            if r.symbol.is_empty() {
                write!(f, "[{tag}:{}] {}", r.variant, r.detail)
            } else {
                write!(f, "[{tag}:{}] `{}`: {}", r.variant, r.symbol, r.detail)
            }
        };
        let rows = |f: &mut std::fmt::Formatter<'_>, tag: &str, rs: &[CensusRow]| {
            for (i, r) in rs.iter().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                row(f, tag, r)?;
            }
            Ok(())
        };
        match self {
            F1Refusal::Boundary(rs) => rows(f, "f1-boundary", rs),
            F1Refusal::Census(rs) => rows(f, "trust-cg-refused", rs),
            F1Refusal::Compile(r) => row(f, "trust-cg-refused", r),
            F1Refusal::ResultContract(s) => write!(f, "[f1-output-gate:result-contract] {s}"),
            F1Refusal::Object(r) => write!(f, "[f1-output-gate:object] {r}"),
            F1Refusal::Binding(s) => write!(f, "[f1-output-gate:binding] {s}"),
            F1Refusal::Policy(s) => write!(f, "[f1-output-gate:policy] {s}"),
            F1Refusal::Gate(s) => write!(f, "[f1-output-gate:panic] {s}"),
        }
    }
}

impl std::error::Error for F1Refusal {}

/// The leading identifier of a `Debug` rendering (the variant's name).
fn leading_identifier(debug: &str) -> String {
    debug.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect()
}

/// The variant of a trust-cg compile error: the leading identifier of its
/// `Debug` rendering, or `Adapter::<variant>` for an adapter refusal.
#[must_use]
pub fn compile_error_variant(e: &CompileError) -> String {
    match e {
        CompileError::Adapter(a) => format!("Adapter::{}", leading_identifier(&format!("{a:?}"))),
        other => leading_identifier(&format!("{other:?}")),
    }
}

fn row_for(m_cg: &Module, func: Option<FuncId>, error: &CompileError) -> CensusRow {
    CensusRow {
        func,
        symbol: func
            .and_then(|id| m_cg.function_by_id(id))
            .map(|f| f.name.clone())
            .unwrap_or_default(),
        variant: compile_error_variant(error),
        detail: error.to_string(),
    }
}

// ===========================================================================
// THE GATE THREAD (INC5.4-STACK)
// ===========================================================================

/// Run `f` on a thread of its own with a `GATE_STACK_BYTES` stack, whatever
/// thread calls. A panic is an `Err` carrying its message; a stack overflow
/// aborts the process, which writes no object.
fn on_gate_thread<T: Send>(f: impl FnOnce() -> T + Send) -> Result<T, String> {
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .name("trust-cg-f1-gate".into())
            .stack_size(GATE_STACK_BYTES)
            .spawn_scoped(scope, f)
            .map_err(|e| {
                format!("could not spawn the gate thread ({GATE_STACK_BYTES} bytes): {e}")
            })?;
        handle.join().map_err(|payload| {
            payload
                .downcast_ref::<&str>()
                .map(|s| (*s).to_string())
                .or_else(|| payload.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "the gate thread panicked with a non-string payload".into())
        })
    })
}

// ===========================================================================
// THE CONSUMER
// ===========================================================================

/// trust-cg's preflight census of `m_cg` under the D31 license, run on the
/// gate thread. This is the only preflight this module offers: there is no
/// variant that runs on the caller's thread.
pub fn census_trust_ir_module(
    m_cg: &Module,
    config: &F1CompileConfig,
) -> Result<Vec<CensusRow>, F1Refusal> {
    on_gate_thread(|| config.compiler().map(|compiler| census_rows(m_cg, &compiler)))
        .unwrap_or_else(|panic| Err(F1Refusal::Gate(panic)))
}

fn census_rows(m_cg: &Module, compiler: &Compiler) -> Vec<CensusRow> {
    compiler.preflight(m_cg).iter().map(|(id, e)| row_for(m_cg, Some(*id), e)).collect()
}

/// Compile `input.m_cg`, verify the object, and hand it out only when
/// `CerReport::ships(input.policy)` allows it. Every step runs on the gate
/// thread; see the module comment for the order.
pub fn compile_and_verify_trust_ir_module(
    input: &F1CompileInput<'_>,
) -> Result<F1Shipped, F1Refusal> {
    let mut unused = None;
    on_gate_thread(|| compile_and_verify(input, false, &mut unused))
        .unwrap_or_else(|panic| Err(F1Refusal::Gate(panic)))
}

/// Bind diagnostic native questions to the exact module the ordinary F1
/// consumer compiles. This establishes identity only: native verdicts do not
/// authorize shipping, remove checks, or change the direct producer's tier.
/// A rewritten codegen image needs questions formed over that new image.
pub fn compile_and_verify_trust_ir_module_with_native_questions(
    input: &F1CompileInput<'_>,
    questions: &trust_ir::NativeVerificationBundle,
) -> Result<F1NativeQuestionCompilation, F1Refusal> {
    on_gate_thread(|| {
        let correspondence = native_questions::bind(input.m_cg, questions)?;
        let mut unused = None;
        let shipped = compile_and_verify(input, false, &mut unused)?;
        Ok(F1NativeQuestionCompilation::new(shipped, correspondence))
    })
    .unwrap_or_else(|panic| Err(F1Refusal::Gate(panic)))
}

/// The ordinary outcome plus optional non-authorizing input data. Retention
/// never substitutes for `ships`, a proof, source agreement or metadata check.
pub struct F1Captured {
    pub outcome: Result<F1Shipped, F1Refusal>,
    pub capture: Result<
        crate::compiler_input_capture::CompilerInputCapture,
        crate::compiler_input_capture::CaptureIncomplete,
    >,
}

/// Explicit observational variant for a diagnostic sink. The SAME Compiler
/// and gate run once, including on a later Strict refusal. No capture is made
/// by the normal API. Capture refusal leaves the ordinary outcome unchanged.
pub fn compile_and_verify_trust_ir_module_captured(input: &F1CompileInput<'_>) -> F1Captured {
    let mut retained = None;
    let outcome = on_gate_thread(|| compile_and_verify(input, true, &mut retained))
        .unwrap_or_else(|panic| Err(F1Refusal::Gate(panic)));
    F1Captured {
        outcome,
        capture: retained.unwrap_or_else(|| {
            Err(crate::compiler_input_capture::CaptureIncomplete::new(
                "actual Compiler object/CER input boundary was not reached",
            ))
        }),
    }
}

fn compile_and_verify(
    input: &F1CompileInput<'_>,
    capture_requested: bool,
    retained: &mut Option<
        Result<
            crate::compiler_input_capture::CompilerInputCapture,
            crate::compiler_input_capture::CaptureIncomplete,
        >,
    >,
) -> Result<F1Shipped, F1Refusal> {
    let m_cg = input.m_cg;

    // 1. Boundary.
    let boundary = boundary_rows(m_cg);
    if !boundary.is_empty() {
        return Err(F1Refusal::Boundary(boundary));
    }

    // 2. Census.
    let effective = input.config.compiler_config();
    let capture_configuration = capture_requested.then(|| {
        crate::compiler_input_capture::CompilerCaptureConfig::from_effective(
            input.config,
            input.policy,
            &effective,
        )
    });
    let compiler = input.config.compiler_with_config(effective)?;
    let census = census_rows(m_cg, &compiler);
    if !census.is_empty() {
        return Err(F1Refusal::Census(census));
    }

    // 3. Compile.
    let result = compiler.compile(m_cg).map_err(|e| F1Refusal::Compile(row_for(m_cg, None, &e)))?;

    // 4. Result contract.
    check_result_contract(&result, input.config).map_err(F1Refusal::ResultContract)?;

    // 5. Gate. Capture observes this exact input and actual effective
    // configuration before any gate outcome. It grants no checked token.
    let cer_input = CerInput {
        m_cg,
        producers: input.producers,
        bodies: input.bodies,
        placements: input.placements,
        object: &result.object_code,
        relocation_model: input.config.compiled_relocation(),
    };
    if let Some(configuration) = capture_configuration {
        *retained = Some(match configuration {
            Err(reason) => Err(reason.at_input(&cer_input)),
            Ok(configuration) => std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                crate::compiler_input_capture::CompilerInputCapture::capture(
                    &cer_input,
                    configuration,
                )
            }))
            .unwrap_or_else(|_| {
                Err(crate::compiler_input_capture::CaptureIncomplete::new(
                    "optional Compiler input capture panicked; no complete data retained",
                )
                .at_input(&cer_input))
            }),
        });
    }
    let mut report = verify_compiled_module(&cer_input).map_err(F1Refusal::Object)?;
    crate::compiler_frame_inputs::attach(&cer_input, &result.aarch64_frame_inputs, &mut report)
        .map_err(F1Refusal::Binding)?;

    // 6. Binding.
    let digest = hex(&Sha256::digest(&result.object_code));
    if report.object_sha256 != digest {
        return Err(F1Refusal::Binding(format!(
            "the report binds object {} but the compiled object is {digest}",
            report.object_sha256
        )));
    }

    // 7. Shipping: the closure decides, through `ships`, and nothing else.
    report.ships(input.policy).map_err(|reason| {
        let context = crate::compiler_frame_inputs::refusal_context(&report, input.policy);
        F1Refusal::Policy(if context.is_empty() { reason } else { format!("{reason}; {context}") })
    })?;

    // 8. Disclosure.
    let unclosed = report
        .closure
        .unclosed
        .iter()
        .map(|u| format!("{}: {}; blocked by [{}]", u.symbol, u.grade, u.blocked_by.join(", ")))
        .collect();
    Ok(F1Shipped { object: result.object_code, report, unclosed })
}

/// F1's own codegen boundary over M_cg's bodies.
fn boundary_rows(m_cg: &Module) -> Vec<CensusRow> {
    let mut rows = Vec::new();
    for f in m_cg.functions.iter().filter(|f| !f.is_declaration()) {
        let mut push = |variant: &str, detail: String| {
            rows.push(CensusRow {
                func: Some(f.id),
                symbol: f.name.clone(),
                variant: variant.into(),
                detail,
            });
        };
        match &f.producer {
            Some(Producer::Clean) => push(
                "CleanOriginBelowCodegenGate",
                "a Clean-origin body is not admitted to F1 codegen (step 3 owns admitting it)"
                    .into(),
            ),
            Some(p @ (Producer::TSwift | Producer::TC)) => push(
                "DeprecatedProducer",
                format!("a body of the deprecated producer {p:?} is not admitted to F1 codegen"),
            ),
            _ => {}
        }
        // The first check in the body that has no faithful panic to deliver.
        // A sited `Assert` of a named kind is not one: its failure is the call
        // its `PanicSite` names (PKG-CP).
        let unfaithful_check = f.blocks.iter().find_map(|block| {
            block.body.iter().enumerate().find_map(|(index, node)| {
                let why = match &node.inst {
                    Inst::Assert { site: None, .. } => {
                        "an `Assert` without a panic site; there is no entry to call and no \
                         location to report, so a failed check could only be a bare trap, which \
                         is not Rust's panic"
                    }
                    Inst::Assert { kind, site: Some(_), .. } if kind.is_unspecified() => {
                        "a sited `Assert` of `Unspecified` kind; the check names no Rust panic, \
                         so no entry is the faithful one"
                    }
                    Inst::AssertInvoke { .. } => {
                        "an `AssertInvoke`; the unwinding form of a failed check is not \
                         admitted to F1 codegen"
                    }
                    _ => return None,
                };
                Some((block.id.index(), index, why))
            })
        });
        if let Some((block, index, why)) = unfaithful_check {
            push("ImplicitPanicUnfaithful", format!("the body carries {why} (bb{block}.{index})"));
        }
    }
    rows
}

/// Design §3.2's checks on the result, extended to every field this
/// configuration must leave empty (plan §1(a) step 4).
fn check_result_contract(
    result: &CompilationResult,
    config: &F1CompileConfig,
) -> Result<(), String> {
    let mut broken = Vec::new();
    if result.object_code.is_empty() {
        broken.push("the object is empty".to_string());
    }
    if result.proofs.is_some() {
        broken.push("the result carries proof certificates (emit_proofs is off)".into());
    }
    if result.certified_pass_chain.is_some() {
        broken.push("the result carries a certified pass chain".into());
    }
    if result.trace.is_some() {
        broken.push("the result carries a compiler trace".into());
    }
    if result.inline_only_bodies != InlineOnlyBodyEvidence::default() {
        broken.push(format!(
            "the object rests on inline-only bodies ({} spliced, {} withheld, {} authenticated)",
            result.inline_only_bodies.spliced.len(),
            result.inline_only_bodies.withheld.len(),
            result.inline_only_bodies.authenticated.len()
        ));
    }
    if result.stack_limits.is_some() {
        broken.push("the result carries a stack-limit report".into());
    }
    if result.dialect_legalization.is_some() {
        broken.push("the result carries a dialect legalization report".into());
    }
    if !result.compile_artifact_cache_telemetry.is_empty() {
        broken.push(
            "the result carries compile-artifact cache telemetry (no cache is attached)".into(),
        );
    }
    if result.target_selection.origin != TargetSelectionOrigin::Explicit {
        broken.push(format!("the target was not explicit: {:?}", result.target_selection.origin));
    }
    if result.target_selection.triple != config.target.triple() {
        broken.push(format!(
            "the object was compiled for `{}`, not `{}`",
            result.target_selection.triple,
            config.target.triple()
        ));
    }
    if broken.is_empty() { Ok(()) } else { Err(broken.join("; ")) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_error_variant_names_the_variant() {
        let adapter = CompileError::Adapter(trust_cg_lower::AdapterError::UnlicensedBody {
            function: "f".into(),
        });
        assert_eq!(compile_error_variant(&adapter), "Adapter::UnlicensedBody");
        let binding = CompileError::AotDirectModuleFunctionBindingUnsupported {
            target: "x".into(),
            call_count: 1,
        };
        assert_eq!(compile_error_variant(&binding), "AotDirectModuleFunctionBindingUnsupported");
    }

    #[test]
    fn force_frame_pointers_reaches_only_the_aarch64_codegen_setting() {
        for target in [F1Target::Aarch64AppleDarwin, F1Target::Aarch64UnknownLinuxGnu] {
            let mut config = F1CompileConfig {
                target,
                opt_level: F1OptLevel::O3,
                relocation: RelocationModel::Pic,
                force_frame_pointers: false,
                never_inline: BTreeSet::new(),
                upstream_mir_lane: false,
            };
            let ordinary = config.compiler_config();
            assert!(!ordinary.aarch64_force_frame_pointers);
            config.force_frame_pointers = true;
            let mut forced = config.compiler_config();
            assert!(forced.aarch64_force_frame_pointers);
            assert!(!forced.emit_proofs);
            assert!(!forced.parallel);
            assert!(!forced.panic_unwind);
            forced.aarch64_force_frame_pointers = false;
            assert_eq!(format!("{ordinary:?}"), format!("{forced:?}"));
        }
    }

    #[test]
    fn the_license_is_exactly_d31() {
        let off = f1_codegen_license(false);
        assert_eq!(off.unlicensed, UnlicensedBodyPolicy::Refuse);
        assert_eq!(
            off.recognized_authorities,
            BTreeSet::from([
                TRUST_DIRECT_LANE_AUTHORITY.to_string(),
                TRUST_INSTANCE_LANE_AUTHORITY.to_string()
            ])
        );
        let on = f1_codegen_license(true);
        assert_eq!(on.unlicensed, UnlicensedBodyPolicy::Refuse);
        assert_eq!(on.recognized_authorities.len(), 3);
        assert!(on.recognizes(TRUST_UPSTREAM_MIR_LANE_AUTHORITY));
    }
}
