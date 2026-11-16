// trust-cg-bridge/call_event.rs — CALL-EVENT REFINEMENT (CER): the F1 output
// gate over the object trust-cg's `Compiler::compile` ships (increment 5, step
// 5.2: the gate core).
//
// WHAT IT PROVES. For each function f DEFINED in the shipped object, that f's
// bytes refine f's PRODUCER trust-ir, with every call treated as an abstract
// EVENT: the callee's link symbol, the arguments (placed where rustc's FnAbi
// puts them — the placement table P), and a result both sides share. Design of
// record: docs/design/2026-10-01-step2-inc5-real-calls-retarget.md §5.
//
//   O0  ABI guarantee — at every reachable `ret` and relocated tail `b`:
//       X19-X29, SP and D8-D15 equal their entry values, control returns to
//       the entry X30, and (Darwin) X18 is never written. (verify_output's
//       `AbiExit` reading, shared with the step-5.0 gates.)
//   O1  object binding — `compiled_object::ObjectLayout::bind` (sections,
//       extents, text coverage, symbols, relocation consumption). Structural.
//   O2  pairing — a bijection π between f's IR call sites and its machine call
//       sites (`bl`, relocated `b`), equal callee symbols, and CFG precedence
//       agreeing in both directions. Structural, in this file.
//   O3  event equality — per pair: the IR site is reached exactly when the
//       machine site is, and the arguments read through P are equal there.
//   O4  return equality — `spec_reach ⇒ machine_reach ∧ ret_mach == ret_spec`.
//       That says nothing where an unsited runtime check fails (`spec_reach`
//       only drops those executions), so O4 also requires that no unsited
//       check can fail on a reached path; otherwise the function is Unknown
//       until the failure path is modeled as a divergent panic event. An
//       `Unreachable` terminator, the caller's or an inlined callee's, still
//       only drops its executions: the producer emits it only where reaching
//       it is undefined behaviour.
//   O5  frame confinement and escape — every machine store lies in
//       `[SP_entry − frame, SP_entry)`; a call whose argument holds an
//       SP-derived value is Unknown (escape); stack-passed arguments are Unknown.
//
// NO CALLEE BODY IS EVER INLINED TO DISCHARGE A `bl`. A call the machine makes
// is an event: its result is ONE fresh variable `R` bound on both sides, never
// the callee's semantics. The ONLY place a callee's IR is interpreted is a site
// trust-cg's OPT-4 actually inlined — an IR call to a co-emitted body with no
// machine call to it anywhere in f's extent — and there the callee's OWN
// producer IR is interpreted (`verify_output_trust_ir::interpret_inlined_call`),
// which is translation validation of a real transformation.
//
// THE MACHINE RELY AT EACH CALL. X0-X17, X30, NZCV, V0-V7, V16-V31 and the
// upper halves of V8-V15 are havocked (X18 too, off Darwin); X19-X29, SP, the
// low halves of D8-D15 (and X18 on Darwin) are preserved; the caller's frame
// `[SP_at_call, SP_entry)` is preserved and all other memory becomes fresh. The
// result bits the callee's FnAbi defines are the shared `R`. Qualified Darwin
// C-u8 Zext places zeroes in W0[31:8]; all higher unspecified bits are fresh. Divergence (`D_s`) is implicit and shared: every obligation
// after a paired event is stated for the executions in which the callee
// returns, so a callee that never returns ends both executions at the same
// event, after O3 matched it.
//
// DISCHARGE. O0, O3 and O4 are one conjunction of unconditional (ITE-merged)
// bit-vector equations against `true` — no uninterpreted function and no world
// token, the form AY 0.27.0 certifies (design fact V2). Each equation is first
// decided by ay (a counterexample is Refuted, an undecided one Unknown); then
// `verify_output::try_kernel_recheckable_conjunction` asks the CLEAN KERNEL to
// re-check the conjunction. Kernel success is [PROVED]; anything else is
// [VALIDATED] (`AyValidated`), which StrictProvenOnly refuses (fact V3).
//
// A REFUTATION IS NEVER FABRICATED BY THE PAIRING. When more than one bijection
// satisfies the structural constraints, a counterexample under one of them is
// not evidence against the bytes: the gate tries every structurally valid
// bijection (a proof under any one is a proof — the pairing is a witness), and
// reports Refuted only when the pairing was unique.
//
// ASSUMPTIONS, recorded per callee in each certificate:
//   * `CoEmitted(g)` — discharged by g's own certificate (O0 + O4 + O5); the
//     closure report checks that, as a greatest fixpoint over recursion SCCs;
//   * `External(g)` — a declaration, or a definition preemptible under PIC;
//     rests on the Trusted row EXTERNAL-CALLEE (owner ruling D30).
//
// FAIL-CLOSED EVERYWHERE: any shape outside the modeled fragment is Unknown,
// never Proven. On x86-64 every function is Unknown, as today.
//
// BLOCKED, NOT UNKNOWN: a variadic split between fixed and anonymous
// arguments that the modules the gate reads do not establish is Refuted under
// every policy, before anything else is read and on x86-64 too. A guessed split
// miscompiles without a trace, and Unknown ships under `AllowUnknown`. Read in
// the function's producer body AND its `M_cg` body: a signature with no fixed
// parameter or under a convention with no variadic form (`variadic_split`), an
// unreadable signature, a call short of its callee's fixed prefix, a variadic
// callee of SeqMap / drop glue / a panic entry, any variadic indirect call, the
// address of a variadic function (in a body or a data initializer), and a
// symbol two modules declare with different splits, one of them variadic
// (`block_unknown_variadic_split`).
//
// FROZEN (scripts/frozen-files.txt, SAMPLE-MORE-OR-REFUSE-MORE) at step 5.2's
// exit: a change may widen what is compared or add a refusal; it may never
// widen what is accepted without an explicit frozen waiver and a complete
// physical contract (including the recorded domain and kernel-checked laws).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::ControlFlow;
use std::sync::Arc;

use sha2::{Digest, Sha256};
use trust_disasm::{Opcode, decode_aarch64};
use trust_ir::inst::Inst;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{CallingConv, Constant, DropResolution, Module, Ty as IrTy};
use trust_machine_sem::{
    Aarch64Semantics, Effect, Flags, MachineState, Semantics, condition_to_formula,
};
use trust_types::{Formula, Sort};

use crate::compiled_object::{
    CompiledObject, FunctionWindow, MachineSiteKind, ObjectExpectations, ObjectFormat,
    ObjectLayout, ObjectRefusal, RelocationModel, hex,
};
use crate::verify_output::{
    AbiConjunct, AbiDischarge, AbiExit, Discharge, EmitPolicy, OutputVerdict, PathOutcome,
    ProvenEvidence, abi_fold, abi_guarantee_residue, b, discharge_abi_guarantee,
    discharge_equal_pre, discharge_valid, formula_reads_memory, ite_unless_same, pred_to_int,
    sp_offset, try_kernel_recheckable_conjunction, wn, xn,
};
use crate::verify_output_trust_ir::{
    IrValue, LocalSlots, SigPosition, bind_block_args, eval_ir_inst, eval_ir_overflow,
    interpret_inlined_call, lookup, merge_reach, scalar_reg_width, signature_reg_width,
};

pub mod abi_extensions;
mod aggregate_values;
mod closed_branch;
#[cfg(test)]
#[path = "call_event/closure_original_tests.rs"]
mod closure_original_tests;
mod closure_values;
pub mod compact_unwind;
pub mod leaf_call_instance;
pub mod leaf_memory;
#[cfg(test)]
#[path = "call_event/scalar_original_tests.rs"]
mod scalar_original_tests;
#[cfg(test)]
#[path = "call_event/signed_original_tests.rs"]
mod signed_original_tests;
#[path = "call_event/source_memory.rs"]
mod source_memory;
use closure_values::{Capture, ClosureValue};

/// The schema name of one per-function certificate record.
pub const CERTIFICATE_SCHEMA: &str = "trust-cg-bridge.call-refinement.v1";

// ===========================================================================
// THE PLACEMENT TABLE P (read from rustc's FnAbi at step 5.4)
// ===========================================================================

/// An argument or result extension the ABI attaches to a slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum AbiExt {
    /// No extension: the bits above the declared width are not part of the value.
    None,
    /// Zero-extended by the writer.
    Zext,
    /// Sign-extended by the writer.
    Sext,
}

/// Where one scalar lives at the call boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Slot {
    /// One general-purpose register `X{n}` (read at the declared width).
    Gpr(u8),
    /// A 128-bit value in the register pair `X{lo}` (low) / `X{hi}` (high).
    GprPair {
        /// Low half.
        lo: u8,
        /// High half.
        hi: u8,
    },
    /// The caller's outgoing argument area at `SP + offset` (Unknown: under
    /// AAPCS64 the callee owns that area; step 5.10).
    Stack {
        /// Byte offset from the stack pointer at the call.
        offset: u32,
    },
    /// Passed as a pointer to a caller copy (Unknown until step 5.10).
    Indirect,
}

/// One scalar's placement: its slot, the width the FnAbi makes observable (the
/// declared width), and the extension contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ScalarPlace {
    /// The slot.
    pub slot: Slot,
    /// The observable (declared) width in bits.
    pub width: u32,
    /// The extension contract.
    pub ext: AbiExt,
}

impl ScalarPlace {
    /// A scalar of `width` bits in `X{reg}` with no extension.
    #[must_use]
    pub fn gpr(reg: u8, width: u32) -> Self {
        ScalarPlace { slot: Slot::Gpr(reg), width, ext: AbiExt::None }
    }
}

/// One PRODUCER parameter's placement.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ParamPlace {
    /// Not passed (a zero-sized parameter).
    Ignore,
    /// One scalar.
    Scalar(ScalarPlace),
    /// A two-field aggregate passed as two scalars (FnAbi `PassMode::Pair`):
    /// field 0 then field 1.
    Pair(ScalarPlace, ScalarPlace),
}

/// The PRODUCER result's placement.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ReturnPlace {
    /// No result.
    Void,
    /// One scalar (`X0`, or the `X0`/`X1` pair for 128 bits).
    Scalar(ScalarPlace),
    /// Returned through a caller-provided pointer (sret; Unknown until 5.10).
    Indirect,
}

/// P for one function: where each producer parameter and the result live.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct FnPlacement {
    /// One entry per PRODUCER parameter, in order.
    pub params: Vec<ParamPlace>,
    /// The result.
    pub ret: ReturnPlace,
}

impl FnPlacement {
    /// SHA-256 of this placement's canonical JSON, as certificates record it.
    #[must_use]
    pub fn digest(&self) -> String {
        hex(&Sha256::digest(serde_json::to_vec(self).unwrap_or_default()))
    }

    /// The AAPCS64 integer-register placement of an ALL-SCALAR signature: each
    /// parameter takes the next `X` register (a 128-bit one the next even
    /// pair), the result `X0` (or `X0`/`X1`). A convenience for HAND-BUILT
    /// modules; the production P is read from rustc's FnAbi (step 5.4). Errs
    /// on any type it does not place.
    pub fn from_scalar_signature(
        module: &Module,
        func: &trust_ir::Function,
    ) -> Result<Self, String> {
        let ty = module
            .func_types
            .get(func.ty.as_usize())
            .ok_or_else(|| format!("`{}` names a FuncTy the module lacks", func.name))?;
        let mut next = 0u8;
        let mut params = Vec::new();
        for p in &ty.params {
            let width = signature_reg_width(module, p, SigPosition::Parameter)?;
            if width == 128 {
                next += next % 2;
                params.push(ParamPlace::Scalar(ScalarPlace {
                    slot: Slot::GprPair { lo: next, hi: next + 1 },
                    width,
                    ext: AbiExt::None,
                }));
                next += 2;
            } else {
                params.push(ParamPlace::Scalar(ScalarPlace::gpr(next, width)));
                next += 1;
            }
            if next > 8 {
                return Err("more than 8 integer argument registers".into());
            }
        }
        let ret = match ty.returns.as_slice() {
            [] => ReturnPlace::Void,
            [r] => {
                let width = signature_reg_width(module, r, SigPosition::Return)?;
                let ext = if matches!(r, IrTy::Bool) { AbiExt::Zext } else { AbiExt::None };
                let slot = if width == 128 { Slot::GprPair { lo: 0, hi: 1 } } else { Slot::Gpr(0) };
                ReturnPlace::Scalar(ScalarPlace { slot, width, ext })
            }
            _ => return Err("multi-value results are not placed by this helper".into()),
        };
        Ok(FnPlacement { params, ret })
    }
}

// ===========================================================================
// INPUTS
// ===========================================================================

/// One producer module and the symbol table S for the functions it names.
#[derive(Debug, Clone)]
pub struct ProducerModule {
    /// The producer's module (`star` or `base` at step 5.4), shared, never cloned.
    pub module: Arc<Module>,
    /// S: each producer `FuncId` to its link symbol.
    pub symbols: BTreeMap<FuncId, String>,
}

impl ProducerModule {
    /// A producer module whose functions are already named by their symbols.
    #[must_use]
    pub fn named_by_symbols(module: Arc<Module>) -> Self {
        let symbols = module.functions.iter().map(|f| (f.id, f.name.clone())).collect();
        ProducerModule { module, symbols }
    }
}

/// Where a function's producer body is: a producer module and a `FuncId` in it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProducerBody {
    /// Index into [`CerInput::producers`].
    pub producer: usize,
    /// The body inside that module.
    pub func: FuncId,
}

/// Everything the call-event gate reads.
#[derive(Debug, Clone, Copy)]
pub struct CerInput<'a> {
    /// The module that was compiled (`M_cg`).
    pub m_cg: &'a Module,
    /// The producer modules.
    pub producers: &'a [ProducerModule],
    /// Each defined symbol's producer body (taken before legalization).
    pub bodies: &'a BTreeMap<String, ProducerBody>,
    /// P, by symbol, for every definition and every callee.
    pub placements: &'a BTreeMap<String, FnPlacement>,
    /// The shipped object's bytes.
    pub object: &'a [u8],
    /// The relocation model the object was compiled under.
    pub relocation_model: RelocationModel,
}

// ===========================================================================
// OUTPUTS
// ===========================================================================

/// The grade of one obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Grade {
    /// Discharged.
    Proven,
    /// Not decided (outside the fragment, solver undecided, a premise missing).
    Unknown,
    /// The bytes violate it.
    Refuted,
    /// Not reached: an earlier obligation already decided the function.
    NotReached,
}

/// One obligation's grade and why.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ObligationGrade {
    /// The grade.
    pub grade: Grade,
    /// The account behind it.
    pub detail: String,
}

impl ObligationGrade {
    fn not_reached() -> Self {
        ObligationGrade { grade: Grade::NotReached, detail: String::new() }
    }
    fn proven(detail: impl Into<String>) -> Self {
        ObligationGrade { grade: Grade::Proven, detail: detail.into() }
    }
    fn unknown(detail: impl Into<String>) -> Self {
        ObligationGrade { grade: Grade::Unknown, detail: detail.into() }
    }
    fn refuted(detail: impl Into<String>) -> Self {
        ObligationGrade { grade: Grade::Refuted, detail: detail.into() }
    }
}

/// The six obligations of one function.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Obligations {
    /// O0 — ABI guarantee.
    pub o0_abi: ObligationGrade,
    /// O1 — object binding.
    pub o1_binding: ObligationGrade,
    /// O2 — pairing.
    pub o2_pairing: ObligationGrade,
    /// O3 — event equality.
    pub o3_events: ObligationGrade,
    /// O4 — return equality.
    pub o4_return: ObligationGrade,
    /// O5 — frame confinement and escape.
    pub o5_frame: ObligationGrade,
}

impl Obligations {
    fn all(&self) -> [&ObligationGrade; 6] {
        [
            &self.o0_abi,
            &self.o1_binding,
            &self.o2_pairing,
            &self.o3_events,
            &self.o4_return,
            &self.o5_frame,
        ]
    }
}

/// How one paired call site is discharged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum CallSiteKind {
    /// A `bl` paired with an IR call.
    Direct,
    /// A relocated (or local) `b` paired with an IR call: call-then-return.
    Tail,
    /// An IR call trust-cg inlined; the callee's producer IR is interpreted.
    InterpretedInline,
}

/// One call site of a certificate.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CallSiteRecord {
    /// In-section offset of the machine instruction (`None` when inlined).
    pub offset: Option<u64>,
    /// The relocation that names the callee (`None` when unrelocated/inlined).
    pub reloc: Option<String>,
    /// The callee's symbol.
    pub symbol: String,
    /// The IR site, `bb<block>.<index>` in the producer body.
    pub ir_site: String,
    /// How it is discharged.
    pub kind: CallSiteKind,
}

/// A premise a certificate rests on.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", content = "symbol")]
pub enum Assumption {
    /// Discharged by the callee's own certificate (closure report).
    CoEmitted(String),
    /// Rests on the Trusted row EXTERNAL-CALLEE (D30).
    External(String),
}

/// One `trust-cg-bridge.call-refinement.v1` record.
#[derive(Debug, Clone, serde::Serialize)]
pub struct FunctionCertificate {
    /// [`CERTIFICATE_SCHEMA`].
    pub schema: String,
    /// The function's symbol.
    pub symbol: String,
    /// Its `M_cg` linkage.
    pub linkage: String,
    /// The code section holding it.
    pub section: String,
    /// Its extent `[start, end)`, in-section offsets.
    pub extent: (u64, u64),
    /// SHA-256 of its bytes.
    pub text_sha256: String,
    /// SHA-256 of its producer function's serialized trust-ir.
    pub producer_ir_sha256: String,
    /// P digests for f and every callee it names.
    pub placement_sha256: BTreeMap<String, String>,
    /// Qualified physical extension contracts, including explicit entry domain
    /// and the P digest. These records are not independent proof authority.
    pub abi_contracts: BTreeMap<String, abi_extensions::ContractRecord>,
    /// Actual executor callbacks, explicitly pending. This field participates
    /// in no obligation grade or shipping decision.
    pub memory_observation: Option<crate::cer_memory_machine::ObservationDiagnostics>,
    /// Actual AOT frame inputs and still-required semantic witnesses. This
    /// request is never a proof grade, even when its byte envelope matches.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub frame_inputs: Option<crate::compiler_frame_inputs::PendingFrameInput>,
    /// The actual observer session, retained internally for typed frame-input
    /// construction. Pending observations never enter a grade or proof.
    #[serde(skip)]
    pub(crate) frame_execution: Option<crate::cer_memory_machine::PendingMachineMemory>,
    /// Actual immutable source/P custody of the observed entry, sealed before
    /// the report exposes mutable diagnostic fields. Not proof authority.
    #[cfg(feature = "frame-step-reference")]
    #[serde(skip)]
    pub(crate) frame_step_subject: Option<crate::original_conjunction_certificate::SubjectBinding>,
    /// Original straight-line leaf inputs remain Unknown until the SAME
    /// scalar+memory kernel conjunction is consumed. Never a grade input here.
    pub leaf_memory: Option<leaf_memory::Diagnostic>,
    /// Untrusted retained metadata proof wire; only a private checked wrapper
    /// constructed against this actual execution can verify a section.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub compact_unwind: Option<compact_unwind::Certificate>,
    /// The call sites.
    pub call_sites: Vec<CallSiteRecord>,
    /// The grade of each obligation.
    pub obligations: Obligations,
    /// The assumptions.
    pub assumptions: Vec<Assumption>,
    /// `[PROVED]`, `[VALIDATED]`, `Unknown` or `Refuted`.
    pub grade: String,
    /// Retained original CIC packet and exact live subject binding. Wire only;
    /// independent replay must recheck it, never trust the grade or a label.
    pub original_proof:
        Option<crate::original_conjunction_certificate::OriginalConjunctionCertificate>,
    /// The verdict, in the gate's common type (not serialized).
    #[serde(skip)]
    pub verdict: OutputVerdict,
}

impl FunctionCertificate {
    /// Whether the verdict is [PROVED] by the clean kernel.
    #[must_use]
    pub fn is_kernel_proved(&self) -> bool {
        self.verdict.is_kernel_proved()
    }
}

/// A function the closure could not close, and what blocks it.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct Unclosed {
    /// The function.
    pub symbol: String,
    /// Its own grade.
    pub grade: String,
    /// The co-emitted callees (transitively) not closed-proven.
    pub blocked_by: Vec<String>,
}

/// The closure report (greatest fixpoint).
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct ClosureReport {
    /// Closed-proven at the strict grade ([PROVED]).
    pub closed_kernel: Vec<String>,
    /// Closed-proven at any Proven grade.
    pub closed_proven: Vec<String>,
    /// Functions not closed at the strict grade, with what blocks each.
    pub unclosed: Vec<Unclosed>,
}

/// The gate's result over one object.
#[derive(Debug, Clone, serde::Serialize)]
pub struct CerReport {
    /// [`CERTIFICATE_SCHEMA`].
    pub schema: String,
    /// SHA-256 of the object the certificates bind to.
    pub object_sha256: String,
    /// One certificate per defined function, in symbol order.
    pub certificates: Vec<FunctionCertificate>,
    /// The closure report.
    pub closure: ClosureReport,
    /// Sections disclosed as unverified (unwind metadata).
    pub unverified_sections: Vec<String>,
    /// Actual metadata record denominator and bounded proof/refusal detail.
    #[serde(skip_serializing_if = "compact_unwind::SectionReport::omitted_on_wire")]
    pub compact_unwind: compact_unwind::SectionReport,
}

impl CerReport {
    /// The certificate of `symbol`.
    #[must_use]
    pub fn certificate(&self, symbol: &str) -> Option<&FunctionCertificate> {
        self.certificates.iter().find(|c| c.symbol == symbol)
    }

    /// The certificates file's JSON (`<stem>.trust-cg-certificates.json`).
    #[must_use]
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_default()
    }

    /// Write `<stem>.trust-cg-certificates.json` and return its path.
    pub fn write_certificates(
        &self,
        stem: &std::path::Path,
    ) -> std::io::Result<std::path::PathBuf> {
        let mut name = stem.as_os_str().to_owned();
        name.push(".trust-cg-certificates.json");
        let path = std::path::PathBuf::from(name);
        std::fs::write(&path, self.to_json())?;
        Ok(path)
    }

    /// Whether the object may ship under `policy`. Strict ships only when every
    /// function is kernel-[PROVED] and closed; allow-unknown ships unless a
    /// function is Refuted (and names every unclosed one).
    pub fn ships(&self, policy: EmitPolicy) -> Result<(), String> {
        let refuted: Vec<&str> = self
            .certificates
            .iter()
            .filter(|c| matches!(c.verdict, OutputVerdict::Refuted { .. }))
            .map(|c| c.symbol.as_str())
            .collect();
        if !refuted.is_empty() {
            return Err(format!("Refuted (miscompile): {}", refuted.join(", ")));
        }
        match policy {
            EmitPolicy::AllowUnknown => Ok(()),
            EmitPolicy::StrictProvenOnly => {
                if self.closure.unclosed.is_empty() {
                    Ok(())
                } else {
                    Err(format!(
                        "strict: not closed-[PROVED]: {}",
                        self.closure
                            .unclosed
                            .iter()
                            .map(|u| format!(
                                "{} ({}; blocked by [{}])",
                                u.symbol,
                                u.grade,
                                u.blocked_by.join(", ")
                            ))
                            .collect::<Vec<_>>()
                            .join("; ")
                    ))
                }
            }
        }
    }
}

// ===========================================================================
// THE GATE
// ===========================================================================

/// Run the call-event gate over one shipped object.
///
/// `Err` is an O1 refusal of the whole object. `Ok` carries one certificate
/// per defined function (each Proven, Unknown or Refuted) and the closure.
pub fn verify_compiled_module(input: &CerInput<'_>) -> Result<CerReport, ObjectRefusal> {
    verify_compiled_module_inner(input, None, None, false)
}

/// Fresh real observation for conditional per-step replay. No function proof
/// or solver is produced; every resulting function verdict remains Unknown.
#[cfg(feature = "frame-step-reference")]
pub(crate) fn observe_compiled_module_for_frame(
    input: &CerInput<'_>,
) -> Result<CerReport, ObjectRefusal> {
    verify_compiled_module_inner(input, None, None, true)
}

#[derive(Clone, Copy)]
enum OriginalMode<'a> {
    Produce,
    Replay(&'a OriginalReplayWireRow),
}

fn verify_compiled_module_inner(
    input: &CerInput<'_>,
    replay: Option<&BTreeMap<String, OriginalReplayWireRow>>,
    mut leaf_proofs: Option<&mut BTreeMap<String, leaf_call_instance::ActualLeafProof>>,
    observe_only: bool,
) -> Result<CerReport, ObjectRefusal> {
    let splits = SplitIndex::new(input);
    if is_x86_64_object(input.object) {
        return Ok(all_unknown_report(
            input,
            &splits,
            "byte-level output preservation is wired for AArch64 machine semantics only; x86-64 \
             code is Unknown (fail-closed)",
        ));
    }
    let object = CompiledObject::parse(input.object)?;
    let expect =
        ObjectExpectations::from_module(input.m_cg, object.format, input.relocation_model)?;
    let layout = ObjectLayout::bind(object, &expect)?;
    let x18_reserved = layout.object.format == ObjectFormat::MachO;
    let observer_object = crate::cer_memory_machine::BoundObject::bind(
        input.object,
        input.m_cg,
        input.relocation_model,
    );
    let mut certificates = Vec::new();
    let actual_functions =
        input.m_cg.functions.iter().filter(|function| !function.blocks.is_empty()).count();
    // Optional scalar packets must not make a previously supported large
    // legacy scalar object enter the bounded original-replay population.
    let retain_scalar_original =
        actual_functions <= crate::original_conjunction_certificate::MAX_REPLAY_FUNCTIONS;
    let mut source_memory_roots = BTreeSet::new();
    let unwind_inventory = compact_unwind::Inventory::read(input, &layout);
    let mut checked_unwind = Vec::new();
    let mut actual_leaf_proofs = BTreeMap::new();
    for window in layout.windows.values() {
        let certificate = verify_function(
            input,
            &splits,
            &layout,
            window,
            x18_reserved,
            &observer_object,
            &mut source_memory_roots,
            &unwind_inventory,
            &mut checked_unwind,
            replay,
            retain_scalar_original,
            Some(&mut actual_leaf_proofs),
            observe_only,
        );
        #[cfg(feature = "frame-step-reference")]
        let certificate = {
            let mut certificate = certificate;
            if certificate.frame_execution.is_some() {
                certificate.frame_step_subject =
                    crate::original_conjunction_certificate::SubjectBinding::from_input(
                        input,
                        &certificate,
                    )
                    .ok();
            }
            certificate
        };
        certificates.push(certificate);
    }
    let pending_memory_callers =
        refuse_unproved_memory_calls(&mut certificates, &source_memory_roots);
    // Provider preparation remains a conservative leaf-only phase. Ordinary
    // producer/replay performs complete original caller composition here;
    // neither the provider-phase report nor an instance label licenses a caller.
    if !observe_only && leaf_proofs.is_none() {
        leaf_call_instance::compose_memory_tails(
            input,
            &layout,
            &mut certificates,
            &actual_leaf_proofs,
            &pending_memory_callers,
            replay,
            retain_scalar_original,
        );
    }
    // Independently sealed actual tail PRE-states grant metadata authority
    // only. No function grade or original caller theorem is changed here.
    if !observe_only {
        leaf_call_instance::tail_unwind::check_records(
            input,
            &layout,
            &unwind_inventory,
            &mut certificates,
            &mut checked_unwind,
            replay,
        );
    }
    let closure = closure_report(&certificates);
    let (unwind_report, checked_section) =
        compact_unwind::finish_section(&unwind_inventory, &checked_unwind, &layout);
    let mut report = CerReport {
        schema: CERTIFICATE_SCHEMA.into(),
        object_sha256: layout.object.sha256_hex(),
        certificates,
        closure,
        unverified_sections: layout
            .unverified_sections
            .iter()
            .filter(|name| name.as_str() != "__LD,__compact_unwind" || checked_section.is_none())
            .cloned()
            .collect(),
        compact_unwind: unwind_report,
    };
    compact_unwind::preserve_function_retention(&mut report);
    crate::original_conjunction_certificate::enforce_report_limits(&mut report, actual_functions);
    if let Some(proofs) = leaf_proofs {
        proofs.extend(actual_leaf_proofs);
        proofs.retain(|symbol, _| {
            report
                .certificate(symbol)
                .is_some_and(|row| row.is_kernel_proved() && row.original_proof.is_some())
        });
    }
    Ok(report)
}

/// Result of rechecking retained original proofs. It is not a source license or
/// a substitute for missing legacy evidence, and never changes shipping policy.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct OriginalReplayReport {
    pub object_sha256: String,
    pub unverified_sections: Vec<String>,
    pub rows: Vec<OriginalReplayRow>,
    pub elapsed_millis: u128,
}
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct OriginalReplayRow {
    pub symbol: String,
    pub replayed: bool,
    pub detail: String,
    pub packet_bytes: usize,
    pub term_nodes: usize,
}
impl OriginalReplayReport {
    /// Every actual defined function's retained original proof was replayed.
    /// This does not cover the separately reported auxiliary object sections.
    pub fn all_replayed(&self) -> bool {
        !self.rows.is_empty() && self.rows.iter().all(|row| row.replayed)
    }
}

// Only the fields used below are read from an ordinary report. Neither its
// grade strings nor unknown diagnostic fields ever become live verdicts.
#[derive(serde::Deserialize)]
struct OriginalReplaySidecar {
    schema: String,
    object_sha256: String,
    certificates: Vec<OriginalReplayWireRow>,
}
#[derive(serde::Deserialize)]
struct OriginalReplayWireRow {
    symbol: String,
    linkage: String,
    section: String,
    extent: (u64, u64),
    text_sha256: String,
    producer_ir_sha256: String,
    placement_sha256: BTreeMap<String, String>,
    #[serde(default)]
    original_proof: Option<crate::original_conjunction_certificate::OriginalConjunctionCertificate>,
    #[serde(default)]
    compact_unwind: Option<compact_unwind::Certificate>,
}

/// Reconstruct the real sealed leaf obligations from independently supplied
/// object/producer/module/P inputs, then check the RETAINED proof. No compiler,
/// solver or original proof producer is called. Every actual function stays in
/// the denominator; unsupported legacy/missing rows explicitly fail replay.
pub fn replay_original_certificates(
    input: &CerInput<'_>,
    sidecar: &[u8],
) -> Result<OriginalReplayReport, String> {
    if sidecar.is_empty()
        || sidecar.len() > crate::original_conjunction_certificate::MAX_SIDECAR_BYTES
    {
        return Err("original proof sidecar byte budget".into());
    }
    let started = std::time::Instant::now();
    let wire: OriginalReplaySidecar = serde_json::from_slice(sidecar).map_err(|e| e.to_string())?;
    let object_sha256 = hex(&Sha256::digest(input.object));
    let expected: BTreeSet<_> = input
        .m_cg
        .functions
        .iter()
        .filter(|function| !function.blocks.is_empty())
        .map(|function| function.name.clone())
        .collect();
    if wire.schema != CERTIFICATE_SCHEMA
        || wire.object_sha256 != object_sha256
        || wire.certificates.is_empty()
        || wire.certificates.len() > crate::original_conjunction_certificate::MAX_REPLAY_FUNCTIONS
        || expected.len() != wire.certificates.len()
    {
        return Err("original proof sidecar object/schema/function population mismatch".into());
    }
    let mut packets = BTreeMap::new();
    for row in wire.certificates {
        if !expected.contains(&row.symbol) || packets.contains_key(&row.symbol) {
            return Err("original proof sidecar duplicate/unowned function".into());
        }
        packets.insert(row.symbol.clone(), row);
    }
    if packets.keys().cloned().collect::<BTreeSet<_>>() != expected {
        return Err("original proof sidecar incomplete function denominator".into());
    }
    let report = verify_compiled_module_inner(input, Some(&packets), None, false)
        .map_err(|e| e.to_string())?;
    let rows = report
        .certificates
        .iter()
        .map(|certificate| {
            let replayed = certificate.is_kernel_proved() && certificate.original_proof.is_some();
            OriginalReplayRow {
                symbol: certificate.symbol.clone(),
                replayed,
                detail: if replayed {
                    "retained original CIC proof rechecked against actual subject".into()
                } else {
                    format!(
                        "not replayed: {}: {}{}",
                        certificate.grade,
                        certificate.obligations.o4_return.detail,
                        certificate
                            .leaf_memory
                            .as_ref()
                            .map(|diagnostic| format!("; leaf: {}", diagnostic.status))
                            .unwrap_or_default()
                    )
                },
                packet_bytes: certificate
                    .original_proof
                    .as_ref()
                    .and_then(|p| p.encoded_bytes().ok())
                    .unwrap_or(0),
                term_nodes: certificate.original_proof.as_ref().map_or(0, |p| p.term_nodes()),
            }
        })
        .collect();
    Ok(OriginalReplayReport {
        object_sha256,
        rows,
        unverified_sections: report.unverified_sections,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

fn is_x86_64_object(obj: &[u8]) -> bool {
    let macho = obj.len() >= 8
        && obj[..4] == 0xfeed_facfu32.to_le_bytes()
        && obj[4..8] == 0x0100_0007u32.to_le_bytes();
    let elf = obj.len() >= 20
        && obj.starts_with(b"\x7fELF")
        && u16::from_le_bytes([obj[18], obj[19]]) == 62;
    macho || elf
}

fn all_unknown_report(input: &CerInput<'_>, splits: &SplitIndex<'_>, why: &str) -> CerReport {
    let certificates: Vec<FunctionCertificate> = input
        .m_cg
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .map(|f| {
            let mut c = blank_certificate(&f.name, &format!("{:?}", f.linkage));
            c.obligations.o1_binding = ObligationGrade::unknown(why);
            // Unknown here ships under `AllowUnknown`; an unknown variadic split must not
            // (x86-64 SysV places anonymous arguments by AL as well).
            block_unknown_variadic_split(input, splits, &f.name, &mut c.obligations);
            finish(&mut c, None);
            c
        })
        .collect();
    let closure = closure_report(&certificates);
    CerReport {
        schema: CERTIFICATE_SCHEMA.into(),
        object_sha256: hex(&Sha256::digest(input.object)),
        certificates,
        closure,
        unverified_sections: Vec::new(),
        compact_unwind: compact_unwind::SectionReport::unavailable(
            "unsupported object architecture",
        ),
    }
}

fn blank_certificate(symbol: &str, linkage: &str) -> FunctionCertificate {
    FunctionCertificate {
        schema: CERTIFICATE_SCHEMA.into(),
        symbol: symbol.into(),
        linkage: linkage.into(),
        section: String::new(),
        extent: (0, 0),
        text_sha256: String::new(),
        producer_ir_sha256: String::new(),
        placement_sha256: BTreeMap::new(),
        abi_contracts: BTreeMap::new(),
        memory_observation: None,
        frame_inputs: None,
        frame_execution: None,
        #[cfg(feature = "frame-step-reference")]
        frame_step_subject: None,
        leaf_memory: None,
        compact_unwind: None,
        call_sites: Vec::new(),
        obligations: Obligations {
            o0_abi: ObligationGrade::not_reached(),
            o1_binding: ObligationGrade::not_reached(),
            o2_pairing: ObligationGrade::not_reached(),
            o3_events: ObligationGrade::not_reached(),
            o4_return: ObligationGrade::not_reached(),
            o5_frame: ObligationGrade::not_reached(),
        },
        assumptions: Vec::new(),
        grade: String::new(),
        original_proof: None,
        verdict: OutputVerdict::Unknown { reason: String::new() },
    }
}

/// Fold the obligation grades into the verdict: any Refuted refutes, any
/// Unknown (or obligation not reached while nothing refuted) is Unknown, and
/// only six Proven obligations are Proven, with `evidence`.
fn finish(cert: &mut FunctionCertificate, evidence: Option<ProvenEvidence>) {
    let all = cert.obligations.all();
    let refuted: Vec<String> = all
        .iter()
        .zip(["O0", "O1", "O2", "O3", "O4", "O5"])
        .filter(|(o, _)| o.grade == Grade::Refuted)
        .map(|(o, n)| format!("{n}: {}", o.detail))
        .collect();
    let undecided: Vec<String> = all
        .iter()
        .zip(["O0", "O1", "O2", "O3", "O4", "O5"])
        .filter(|(o, _)| matches!(o.grade, Grade::Unknown))
        .map(|(o, n)| format!("{n}: {}", o.detail))
        .collect();
    let all_proven = all.iter().all(|o| o.grade == Grade::Proven);
    cert.verdict = if !refuted.is_empty() {
        OutputVerdict::Refuted {
            detail: format!(
                "call-event refinement of `{}` refuted — {}",
                cert.symbol,
                refuted.join("; ")
            ),
        }
    } else if all_proven {
        OutputVerdict::Proven { evidence: evidence.unwrap_or(ProvenEvidence::AyValidated) }
    } else {
        OutputVerdict::Unknown {
            reason: if undecided.is_empty() {
                format!("call-event refinement of `{}` did not reach every obligation", cert.symbol)
            } else {
                format!(
                    "call-event refinement of `{}` undecided — {}",
                    cert.symbol,
                    undecided.join("; ")
                )
            },
        }
    };
    cert.grade = match &cert.verdict {
        OutputVerdict::Proven { .. } if cert.verdict.is_kernel_proved() => "[PROVED]".into(),
        OutputVerdict::Proven { .. } => "[VALIDATED]".into(),
        OutputVerdict::Refuted { .. } => "Refuted".into(),
        _ => "Unknown".into(),
    };
}

/// A source-memory leaf proof does not establish the M5 premises at its callers.
/// Derive this frontier from actual source evaluation and the authenticated
/// call graph. Diagnostics and favorable callee grades cannot discharge it.
fn refuse_unproved_memory_calls(
    certificates: &mut [FunctionCertificate],
    source_memory_roots: &BTreeSet<String>,
) -> BTreeSet<String> {
    let mut pending_callers = BTreeSet::new();
    if source_memory_roots.is_empty() {
        return pending_callers;
    }
    let mut callers: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for certificate in certificates.iter() {
        for assumption in &certificate.assumptions {
            let (Assumption::CoEmitted(callee) | Assumption::External(callee)) = assumption;
            callers.entry(callee.clone()).or_default().push(certificate.symbol.clone());
        }
    }
    let mut memory = source_memory_roots.clone();
    let mut pending: std::collections::VecDeque<String> = memory.iter().cloned().collect();
    while let Some(callee) = pending.pop_front() {
        for caller in callers.get(&callee).into_iter().flatten() {
            if memory.insert(caller.clone()) {
                pending.push_back(caller.clone());
            }
        }
    }
    for certificate in certificates {
        let blocked: Vec<_> = certificate
            .assumptions
            .iter()
            .filter_map(|assumption| {
                let (Assumption::CoEmitted(callee) | Assumption::External(callee)) = assumption;
                memory.contains(callee).then_some(callee.as_str())
            })
            .collect();
        // Preserve concrete refutations and existing unknown reasons. This only
        // prevents favorable callers from borrowing an unproved memory rely.
        if !blocked.is_empty() && certificate.verdict.is_proven() {
            certificate.obligations.o5_frame = ObligationGrade::unknown(format!(
                "M5 memory-call premises are unproved for [{}]: a callee leaf proof does not \
                 establish caller pre-call memory equality or private-frame separation",
                blocked.join(", ")
            ));
            finish(certificate, None);
            pending_callers.insert(certificate.symbol.clone());
        }
    }
    pending_callers
}

/// The greatest fixpoint: a function is closed when it is Proven at the grade
/// and every co-emitted callee is closed.
pub(crate) fn closure_report(certs: &[FunctionCertificate]) -> ClosureReport {
    let fixpoint = |admit: &dyn Fn(&FunctionCertificate) -> bool| -> BTreeSet<String> {
        let mut closed: BTreeSet<String> =
            certs.iter().filter(|c| admit(c)).map(|c| c.symbol.clone()).collect();
        loop {
            let before = closed.len();
            let snapshot = closed.clone();
            closed.retain(|s| {
                // `closed` is drawn from `certs`, so the lookup always finds one;
                // a symbol with no certificate would close nothing, so it leaves.
                let Some(c) = certs.iter().find(|c| &c.symbol == s) else {
                    return false;
                };
                c.assumptions.iter().all(|a| match a {
                    Assumption::CoEmitted(g) => snapshot.contains(g),
                    Assumption::External(_) => true,
                })
            });
            // A co-emitted callee with no certificate in this object can never
            // close (it is not in `closed`), which the retain above enforces.
            if closed.len() == before {
                return closed;
            }
        }
    };
    let closed_kernel = fixpoint(&|c: &FunctionCertificate| c.verdict.is_kernel_proved());
    let closed_proven = fixpoint(&|c: &FunctionCertificate| c.verdict.is_proven());
    let unclosed = certs
        .iter()
        .filter(|c| !closed_kernel.contains(&c.symbol))
        .map(|c| Unclosed {
            symbol: c.symbol.clone(),
            grade: c.grade.clone(),
            blocked_by: c
                .assumptions
                .iter()
                .filter_map(|a| match a {
                    Assumption::CoEmitted(g) if !closed_kernel.contains(g) && g != &c.symbol => {
                        Some(g.clone())
                    }
                    _ => None,
                })
                .collect(),
        })
        .collect();
    ClosureReport {
        closed_kernel: closed_kernel.into_iter().collect(),
        closed_proven: closed_proven.into_iter().collect(),
        unclosed,
    }
}

// ===========================================================================
// ONE FUNCTION
// ===========================================================================

/// A stable IR call-site key: (block id, instruction index) in the producer body.
type SiteKey = (u32, usize);

fn site_name(k: SiteKey) -> String {
    format!("bb{}.{}", k.0, k.1)
}

/// One IR call site of the producer body.
#[derive(Debug, Clone)]
struct IrSite {
    key: SiteKey,
    callee_symbol: String,
    callee: FuncId,
}

/// What the gate does with one IR call site.
#[derive(Debug, Clone)]
enum SiteDecision {
    /// A real call: an event whose result is a fresh shared variable.
    Called { symbol: String, place: FnPlacement, result_width: Option<u32> },
    /// OPT-4 inlined it: interpret the callee's own producer IR.
    Inlined { producer: usize, func: FuncId },
}

/// PKG-C5c S2a (docs/DECISION_QUEUE.md PKG-C5c-DEAD-TAIL-1): the dead panic
/// tails of one function. A tail admitted here is admitted UNEXECUTED: nothing
/// checks its entry call or its Location record. Soundness rests on O4 alone
/// (`spec_reach ⇒ machine_reach`, and the machine side scores every path into
/// a trap tail `reach = false`) and (4b) (no check of the producer fails on a
/// reached path), both items of the step-(4) conjunction: together they say
/// that no execution on which the IR returns enters a tail. Those items are
/// decided by ay, and kernel-checked only when the function grades [PROVED];
/// at [VALIDATED] the deadness rests on ay's UNSAT alone. The admission is
/// granted only for the whole run: the exact pair, the record named by a
/// sited `Assert` of the function, exactly one pair and exactly one site in
/// the run, that site a `bl` to the entry of an `Assert` located at that
/// record, the word after it the run's trap. Those shape conditions are SCOPE
/// POLICY, not soundness: they keep the admission to the one lowering
/// trust-cg emits for a sited check.
#[derive(Debug, Default)]
struct DeadTails {
    pairs: Vec<DeadPair>,
}

/// One admitted Location pair, `adrp` at `adrp`, `add` at `adrp + 4`.
#[derive(Debug)]
struct DeadPair {
    adrp: u64,
    symbol: String,
    /// The entry symbols of every sited `Assert` of the body located at `symbol`.
    entries: BTreeSet<String>,
    /// The two lines the walk put in `window.unknown` for the halves.
    lines: [String; 2],
    /// The trap run holding both halves: (first word, the trap).
    tail: (u64, u64),
}

/// The trap run of `window` holding `at`: its first word and its trap, or
/// `None` when `at` is in no run. A run is read off [`FunctionWindow::trap_tail`]:
/// from `at` forward to the first trap, and back while the word before is in
/// the set and not itself a trap (every non-trap word of the set falls only to
/// the next word, which is in the set).
fn trap_run(window: &FunctionWindow, at: u64) -> Option<(u64, u64)> {
    use crate::compiled_object::{InsnClass, classify_insn};
    let is_trap = |o: u64| classify_insn(word(window, o)) == InsnClass::Trap;
    if !window.trap_tail.contains(&at) {
        return None;
    }
    let mut end = at;
    while !is_trap(end) {
        end += 4;
        if !window.trap_tail.contains(&end) {
            return None;
        }
    }
    let mut start = at;
    while start >= window.start + 4
        && window.trap_tail.contains(&(start - 4))
        && !is_trap(start - 4)
    {
        start -= 4;
    }
    Some((start, end))
}

impl DeadTails {
    /// The admitted pairs of `window`: an `adrp` at `o` and an `add` at `o + 4`,
    /// both in one trap run, relocated Mach-O `PAGE21` (pc-relative, length 2)
    /// then `PAGEOFF12` (not pc-relative, length 2), or ELF
    /// `R_AARCH64_ADR_PREL_PG_HI21` then `R_AARCH64_ADD_ABS_LO12_NC` (same
    /// flags), against ONE symbol entry (never a section) with addend 0, the
    /// in-word immediates 0 and the `add`'s shift 0, `adrp.Rd == add.Rn`; the
    /// symbol a LOCAL, non-weak data object of this object in
    /// `layout.verified_globals`, the uniquely named, immutable, non-TLS,
    /// Internal or Private `M_cg` global some sited `Assert` of the function's
    /// own `M_cg` body names as its `PanicLocation::Global`; and the pair the
    /// only one of its run, whose one site is its [`entry_call`].
    fn read(input: &CerInput<'_>, layout: &ObjectLayout, window: &FunctionWindow) -> DeadTails {
        use trust_ir::inst::PanicLocation;

        use crate::compiled_object::{
            InsnClass, RelocKind, RelocTarget, SymbolBinding, SymbolKind,
        };
        let mut out = DeadTails::default();
        let m_cg = input.m_cg;
        let mut bodies =
            m_cg.functions.iter().filter(|f| f.name == window.symbol && !f.blocks.is_empty());
        let (Some(f), None) = (bodies.next(), bodies.next()) else {
            return out;
        };
        let mut located: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for node in f.blocks.iter().flat_map(|block| &block.body) {
            let Inst::Assert { site: Some(site), .. } = &node.inst else {
                continue;
            };
            let PanicLocation::Global(gid) = site.location else {
                continue;
            };
            let (Some(g), Some(entry)) =
                (m_cg.globals.get(gid.as_usize()), m_cg.function_by_id(site.entry))
            else {
                continue;
            };
            let unique = m_cg.globals.iter().filter(|x| x.name == g.name).count() == 1
                && !m_cg.functions.iter().any(|x| x.name == g.name);
            if unique
                && !g.mutable
                && g.tls.is_none()
                && matches!(g.linkage, trust_ir::Linkage::Internal | trust_ir::Linkage::Private)
            {
                located.entry(g.name.clone()).or_default().insert(entry.name.clone());
            }
        }
        let object = &layout.object;
        let (page, page_off) = match object.format {
            ObjectFormat::MachO => (RelocKind::Page21, RelocKind::PageOff12),
            ObjectFormat::Elf => (RelocKind::AdrPrelPgHi21, RelocKind::AddAbsLo12Nc),
        };
        for (&at, hi) in &window.page_halves {
            let Some(lo) = window.page_halves.get(&(at + 4)) else {
                continue;
            };
            let Some(tail) = trap_run(window, at) else {
                continue;
            };
            let shape = trap_run(window, at + 4) == Some(tail)
                && hi.class == InsnClass::Adrp
                && hi.kind == page
                && hi.pc_relative
                && hi.length == 2
                && lo.class == InsnClass::AddImm64
                && lo.kind == page_off
                && !lo.pc_relative
                && lo.length == 2
                && hi.addend == 0
                && lo.addend == 0
                && hi.imm == 0
                && lo.imm == 0
                && lo.shift == 0
                && hi.rd == lo.rn
                && hi.target == lo.target;
            if !shape {
                continue;
            }
            let RelocTarget::Symbol(index) = hi.target else {
                continue;
            };
            let Some(s) = object.symbols.get(index) else {
                continue;
            };
            if s.kind != SymbolKind::Object
                || s.section.is_none()
                || s.binding != SymbolBinding::Local
                || s.weak
                || !layout.verified_globals.contains(&s.name)
            {
                continue;
            }
            let Some(entries) = located.get(&s.name) else {
                continue;
            };
            out.pairs.push(DeadPair {
                adrp: at,
                symbol: s.name.clone(),
                entries: entries.clone(),
                lines: [hi.unknown_line.clone(), lo.unknown_line.clone()],
                tail,
            });
        }
        // The whole run, or nothing: a run holding one pair and its one entry
        // call keeps it; any other run (no call, a second pair or site, a call
        // elsewhere or to another symbol) admits none of its pairs, so their
        // lines keep O1 Unknown.
        let per_run: BTreeMap<(u64, u64), usize> =
            out.pairs.iter().fold(BTreeMap::new(), |mut n, p| {
                *n.entry(p.tail).or_default() += 1;
                n
            });
        out.pairs.retain(|p| per_run[&p.tail] == 1 && entry_call(window, p).is_some());
        out
    }

    /// The lines of `window.unknown` the admitted pairs account for.
    fn lines(&self) -> BTreeSet<&str> {
        self.pairs.iter().flat_map(|p| p.lines.iter().map(String::as_str)).collect()
    }

    /// The `adrp` offsets of the admitted pairs.
    fn adrps(&self) -> BTreeSet<u64> {
        self.pairs.iter().map(|p| p.adrp).collect()
    }

    /// The trap run of the trap-tail site `site`, when it is admitted: the
    /// run of an admitted pair, and `site` that run's [`entry_call`].
    fn admit_call(
        &self,
        window: &FunctionWindow,
        site: &crate::compiled_object::MachineSite,
    ) -> Option<(u64, u64)> {
        let tail = trap_run(window, site.offset)?;
        let pair = self.pairs.iter().find(|p| p.tail == tail)?;
        (entry_call(window, pair) == Some(site.offset)).then_some(tail)
    }
}

/// The offset of the one call of `pair`'s trap run, when the run holds
/// exactly one site, that site is a `bl` naming the entry of an `Assert`
/// located at `pair`'s record, and the word after it is the run's trap.
fn entry_call(window: &FunctionWindow, pair: &DeadPair) -> Option<u64> {
    let (start, trap) = pair.tail;
    let mut here = window.sites.iter().filter(|s| (start..=trap).contains(&s.offset));
    let (Some(site), None) = (here.next(), here.next()) else {
        return None;
    };
    let callee = site.callee.as_ref().filter(|_| site.kind == MachineSiteKind::Call)?;
    (site.offset + 4 == trap && pair.entries.contains(callee)).then_some(site.offset)
}

fn verify_function(
    input: &CerInput<'_>,
    splits: &SplitIndex<'_>,
    layout: &ObjectLayout,
    window: &FunctionWindow,
    x18_reserved: bool,
    observer_object: &Result<crate::cer_memory_machine::BoundObject, String>,
    source_memory_roots: &mut BTreeSet<String>,
    unwind_inventory: &Result<compact_unwind::Inventory, String>,
    checked_unwind: &mut Vec<compact_unwind::CheckedRecord>,
    replay: Option<&BTreeMap<String, OriginalReplayWireRow>>,
    retain_scalar_original: bool,
    leaf_proofs: Option<&mut BTreeMap<String, leaf_call_instance::ActualLeafProof>>,
    observe_only: bool,
) -> FunctionCertificate {
    let mut cert = blank_certificate(&window.symbol, &window.expected.linkage);
    cert.section =
        layout.object.section(window.section).map(|s| s.name.clone()).unwrap_or_default();
    cert.extent = (window.start, window.end);
    cert.text_sha256 = window.text_sha256();
    let mode = match replay {
        None => OriginalMode::Produce,
        Some(packets) => {
            match packets.get(&window.symbol).filter(|row| row.original_proof.is_some()) {
                Some(row) => OriginalMode::Replay(row),
                None => {
                    cert.obligations.o4_return = ObligationGrade::unknown(
                        "no retained original CIC packet: legacy/missing evidence is outside this replay scope",
                    );
                    finish(&mut cert, None);
                    return cert;
                }
            }
        }
    };
    let mut closed_leaf = None;
    let mut dead_tails: Vec<(u64, u64)> = Vec::new();
    let mut evidence = analyze(
        input,
        splits,
        layout,
        window,
        x18_reserved,
        &mut cert,
        observer_object,
        source_memory_roots,
        unwind_inventory,
        checked_unwind,
        mode,
        retain_scalar_original,
        &mut closed_leaf,
        observe_only,
        &mut dead_tails,
    );
    if let Some(ProvenEvidence::KernelInstantiated { original: Some(checked), .. }) = &evidence {
        match crate::original_conjunction_certificate::OriginalConjunctionCertificate::bind(
            checked, input, &cert,
        ) {
            Ok(packet) => cert.original_proof = Some(packet),
            Err(reason) => {
                cert.obligations.o4_return = ObligationGrade::unknown(reason);
                evidence = None;
            }
        }
    }
    // PKG-C5c S2a: O2's account names the tails it admitted unexecuted, and
    // claims them unreachable only where O4 (reach and (4b)) is Proven, read
    // after the original-conjunction binding may have reopened O4.
    if !dead_tails.is_empty() && cert.obligations.o2_pairing.grade != Grade::NotReached {
        let tails = dead_tails
            .iter()
            .map(|(start, trap)| format!("{start:#x}..={trap:#x}"))
            .collect::<Vec<_>>()
            .join(", ");
        cert.obligations.o2_pairing.detail.push_str(&if cert.obligations.o4_return.grade
            == Grade::Proven
        {
            format!(
                "; panic tails at [{tails}] are unreachable wherever the IR returns (O4 reach + \
                 (4b), decided by ay; kernel-checked only at [PROVED]); entry and Location \
                 unverified (PKG-C5c S2)"
            )
        } else {
            format!(
                "; panic tails at [{tails}] admitted unexecuted on the condition that O4 reach + \
                 (4b) hold, which this certificate does not establish; entry and Location \
                 unverified (PKG-C5c S2)"
            )
        });
    }
    finish(&mut cert, evidence);
    if let (Some(proofs), Some(closed)) = (leaf_proofs, closed_leaf) {
        if let Ok(proof) = leaf_call_instance::ActualLeafProof::from_closed(input, &cert, closed) {
            proofs.insert(cert.symbol.clone(), proof);
        }
    }
    cert
}

/// Fill `cert`'s obligations; return the [PROVED]/[VALIDATED] evidence when
/// every obligation was discharged.
fn analyze(
    input: &CerInput<'_>,
    splits: &SplitIndex<'_>,
    layout: &ObjectLayout,
    window: &FunctionWindow,
    x18_reserved: bool,
    cert: &mut FunctionCertificate,
    observer_object: &Result<crate::cer_memory_machine::BoundObject, String>,
    source_memory_roots: &mut BTreeSet<String>,
    unwind_inventory: &Result<compact_unwind::Inventory, String>,
    checked_unwind: &mut Vec<compact_unwind::CheckedRecord>,
    original_mode: OriginalMode<'_>,
    retain_scalar_original: bool,
    closed_leaf: &mut Option<leaf_memory::Closed>,
    observe_only: bool,
    admitted_tails: &mut Vec<(u64, u64)>,
) -> Option<ProvenEvidence> {
    let symbol = window.symbol.clone();
    let ob = &mut cert.obligations;

    // ---- BLOCKED: a variadic split the producer does not state -------------
    if block_unknown_variadic_split(input, splits, &symbol, ob) {
        return None;
    }

    // ---- O1: the object-level reasons this function is Unknown -------------
    // PKG-C5c S2a: the lines of admitted dead-tail Location pairs are set
    // aside; any other line keeps O1 Unknown, with the walk's whole account.
    let dead = DeadTails::read(input, layout, window);
    let set_aside = dead.lines();
    if window.unknown.iter().any(|line| !set_aside.contains(line.as_str())) {
        ob.o1_binding = ObligationGrade::unknown(window.unknown.join("; "));
        return None;
    }
    ob.o1_binding = ObligationGrade::proven(format!(
        "one symbol, binding {:?}/{:?}, extent [{:#x}, {:#x}) covered, {} relocation(s) consumed{}",
        window.expected.binding,
        window.expected.symbol_visibility,
        window.start,
        window.end,
        window.relocations.len(),
        if dead.pairs.is_empty() {
            String::new()
        } else {
            format!(
                "; {} dead panic-tail Location pair(s) admitted unexecuted (PKG-C5c S2a), their \
                 lines set aside: {}",
                dead.pairs.len(),
                dead.pairs
                    .iter()
                    .map(|p| format!(
                        "adrp {:#x}/add {:#x} -> `{}` [{}; {}]",
                        p.adrp,
                        p.adrp + 4,
                        p.symbol,
                        p.lines[0],
                        p.lines[1]
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    ));

    // ---- the producer body and P(f) ---------------------------------------
    let Some(body) = input.bodies.get(&symbol) else {
        ob.o4_return = ObligationGrade::unknown("no producer body was supplied for this symbol");
        return None;
    };
    let Some(producer) = input.producers.get(body.producer) else {
        ob.o4_return =
            ObligationGrade::unknown("the producer body names a missing producer module");
        return None;
    };
    let module: &Module = &producer.module;
    let Some(func) = module.function_by_id(body.func) else {
        ob.o4_return = ObligationGrade::unknown("the producer module has no function with that id");
        return None;
    };
    cert.producer_ir_sha256 = hex(&Sha256::digest(serde_json::to_vec(func).unwrap_or_default()));
    let Some(place) = input.placements.get(&symbol) else {
        ob.o4_return = ObligationGrade::unknown("P has no placement for this function");
        return None;
    };
    cert.placement_sha256.insert(symbol.clone(), place.digest());
    // The prior field borrow ends here. Validate the wire subject against this
    // freshly object-bound certificate BEFORE replay can call the kernel.
    if let OriginalMode::Replay(row) = original_mode {
        if row.symbol != cert.symbol
            || row.linkage != cert.linkage
            || row.section != cert.section
            || row.extent != cert.extent
            || row.text_sha256 != cert.text_sha256
            || row.producer_ir_sha256 != cert.producer_ir_sha256
            || row.placement_sha256 != cert.placement_sha256
        {
            cert.obligations.o4_return = ObligationGrade::unknown(
                "retained sidecar metadata differs from fresh actual object/source/P identity",
            );
            return None;
        }
        let Some(packet) = row.original_proof.as_ref() else {
            cert.obligations.o4_return =
                ObligationGrade::unknown("retained original proof is missing");
            return None;
        };
        if let Err(reason) = packet.require_subject(input, cert) {
            cert.obligations.o4_return = ObligationGrade::unknown(reason);
            return None;
        }
        if let Err(reason) = leaf_memory::replay_source_shape(func) {
            cert.obligations.o4_return = ObligationGrade::unknown(reason);
            return None;
        }
    }
    let ob = &mut cert.obligations;
    let own_sig = match signature_of(module, func.ty) {
        Ok(s) => s,
        Err(e) => {
            ob.o4_return = ObligationGrade::unknown(e);
            return None;
        }
    };
    if let Err(e) = check_placement(module, &own_sig, func.calling_conv, place, true) {
        ob.o4_return = e.grade(&format!("`{symbol}` itself"), |e| {
            format!("P(`{symbol}`) disagrees with its producer signature: {e}")
        });
        return None;
    }

    let own_abi = match abi_extensions::Plan::new(
        module,
        func.calling_conv,
        &own_sig.0,
        &own_sig.1,
        place,
        true,
    ) {
        Ok(plan) => plan,
        Err(reason) => {
            ob.o4_return = ObligationGrade::unknown(reason);
            return None;
        }
    };
    if let Some(record) = own_abi.record() {
        let codegen_authority =
            input.m_cg.functions.iter().find(|function| function.name == symbol).is_some_and(
                |function| {
                    function.calling_conv == func.calling_conv
                        && input.m_cg.func_type(function.ty).is_some_and(|signature| {
                            signature.abi.is_none()
                                && !signature.is_vararg
                                && signature.params == own_sig.0
                                && signature.returns == own_sig.1
                        })
                },
            );
        if !abi_extensions::qualified_target(input.m_cg)
            || !codegen_authority
            || module.func_type(func.ty).is_none_or(|signature| signature.abi.is_some())
        {
            ob.o4_return = ObligationGrade::unknown(
                "C-u8 producer/codegen target, convention or signature authority disagrees",
            );
            return None;
        }
        cert.abi_contracts.insert(symbol.clone(), record);
    }

    // ---- IR call sites ----------------------------------------------------
    let mut ir_sites: Vec<IrSite> = Vec::new();
    for block in &func.blocks {
        for (index, node) in block.body.iter().enumerate() {
            match &node.inst {
                Inst::Call { callee, .. } => {
                    let Some(callee_symbol) = producer.symbols.get(callee) else {
                        ob.o2_pairing = ObligationGrade::unknown(format!(
                            "S has no symbol for the callee of {}",
                            site_name((block.id.index(), index))
                        ));
                        return None;
                    };
                    ir_sites.push(IrSite {
                        key: (block.id.index(), index),
                        callee_symbol: callee_symbol.clone(),
                        callee: *callee,
                    });
                }
                Inst::CallIndirect { .. } => {
                    ob.o2_pairing = ObligationGrade::unknown(
                        "an indirect IR call (CallIndirect) is Unknown until step 5.9",
                    );
                    return None;
                }
                _ => {}
            }
        }
    }

    // ---- site decisions (O2, first half) -----------------------------------
    // PKG-C5c S2a: a trap-tail call is admitted, unpaired and with no event,
    // only as `DeadTails::admit_call` reads it; any other keeps O2 Unknown.
    for s in window.sites.iter().filter(|s| s.in_trap_tail) {
        match dead.admit_call(window, s) {
            Some(tail) => admitted_tails.push(tail),
            None => {
                admitted_tails.clear();
                ob.o2_pairing = ObligationGrade::unknown(format!(
                    "the call at {:#x} lies in an assert's failure tail: a divergent call event, \
                     modeled at step 5.7 (callee {:?})",
                    s.offset, s.callee
                ));
                return None;
            }
        }
    }
    let mach_sites: Vec<_> = window.sites.iter().filter(|s| !s.in_trap_tail).collect();
    let mut by_callee_m: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for s in &mach_sites {
        let Some(callee) = s.callee.as_ref().filter(|_| s.kind != MachineSiteKind::Indirect) else {
            ob.o2_pairing = ObligationGrade::unknown(format!(
                "machine call at {:#x} names no symbol",
                s.offset
            ));
            return None;
        };
        by_callee_m.entry(callee.clone()).or_default().push(s.offset);
    }
    let mut by_callee_ir: BTreeMap<String, Vec<&IrSite>> = BTreeMap::new();
    for s in &ir_sites {
        by_callee_ir.entry(s.callee_symbol.clone()).or_default().push(s);
    }
    for (g, offs) in &by_callee_m {
        if !by_callee_ir.contains_key(g) {
            ob.o2_pairing = ObligationGrade::unknown(format!(
                "machine call(s) at {} to `{g}` have no IR counterpart (a duplicated site or a runtime \
                 helper)",
                offs.iter().map(|o| format!("{o:#x}")).collect::<Vec<_>>().join(", ")
            ));
            return None;
        }
    }
    let mut decisions: BTreeMap<SiteKey, SiteDecision> = BTreeMap::new();
    let mut assumptions: BTreeSet<Assumption> = BTreeSet::new();
    for (g, sites) in &by_callee_ir {
        let n_m = by_callee_m.get(g).map_or(0, Vec::len);
        if n_m == 0 {
            // OPT-4 inlined every site of `g` (there is no call to it anywhere in
            // the extent outside the dead tails PKG-C5c S2a admitted: a tail's
            // `bl` is not in `mach_sites`, so a sited `Assert` whose entry is a
            // co-emitted `g` the IR also calls explicitly still lands here when
            // trust-cg inlines that explicit call; O3/O4 bind the inlined
            // semantics and the tail is unreachable wherever O4 holds):
            // interpret g's OWN producer IR — only if g is a co-emitted body we
            // hold.
            let Some(gb) = input.bodies.get(g) else {
                ob.o2_pairing = ObligationGrade::unknown(format!(
                    "the IR calls `{g}` but the bytes never do, and `{g}` has no producer body to \
                     interpret (a dropped call, or an inlined body the gate cannot see)"
                ));
                return None;
            };
            if !layout.windows.get(g).is_some_and(|w| w.expected.non_preemptible) {
                ob.o2_pairing = ObligationGrade::unknown(format!(
                    "the IR calls `{g}` but the bytes never do, and `{g}` is not a non-preemptible body \
                     co-emitted in this object (its local IR need not be what the symbol binds to)"
                ));
                return None;
            }
            for s in sites {
                decisions
                    .insert(s.key, SiteDecision::Inlined { producer: gb.producer, func: gb.func });
            }
        } else if n_m == sites.len() {
            let Some(gp) = input.placements.get(g) else {
                ob.o3_events =
                    ObligationGrade::unknown(format!("P has no placement for the callee `{g}`"));
                return None;
            };
            // The callee's signature as THIS caller's module sees it.
            let Some(callee_decl) = module.function_by_id(sites[0].callee) else {
                ob.o3_events = ObligationGrade::unknown("callee id missing");
                return None;
            };
            let caller_view = match signature_of(module, callee_decl.ty) {
                Ok(s) => s,
                Err(e) => {
                    ob.o3_events = ObligationGrade::unknown(e);
                    return None;
                }
            };
            for site in sites.iter().skip(1) {
                let view = module
                    .function_by_id(site.callee)
                    .map(|f| f.ty)
                    .ok_or_else(|| "callee id missing".to_string())
                    .and_then(|ty| signature_of(module, ty));
                if view.as_ref() != Ok(&caller_view) {
                    ob.o3_events = ObligationGrade::unknown(format!(
                        "`{g}` is called at {} under another signature than at {} (the same symbol \
                         under two signatures)",
                        site_name(site.key),
                        site_name(sites[0].key)
                    ));
                    return None;
                }
            }
            if caller_view.0.iter().any(|ty| matches!(ty, IrTy::Closure(_))) {
                let non_preemptible =
                    layout.windows.get(g).is_some_and(|w| w.expected.non_preemptible);
                for site in sites {
                    if let Err(detail) = closure_values::direct_call_boundary(
                        input,
                        *body,
                        site.callee,
                        g,
                        non_preemptible,
                    ) {
                        ob.o3_events = ObligationGrade::unknown(detail);
                        return None;
                    }
                }
            }
            // Trust (2026-10-02, KNOWN_HAZARDS "producer C-ABI residuals after S2/S3"): an
            // edge whose variadic split is unknown — a `(...)` declaration with NO fixed
            // parameter (the producer's UNSIGNED callee: a variadic `fcntl`, or a
            // non-variadic `posix_spawn_file_actions_adddup2` whose parameter it cannot
            // type), or a variadic one under a convention with no variadic form (the Rust
            // ABI, fastcc, coldcc, swiftcall, vectorcall) — is BLOCKED under every policy. It
            // was already refuted above, before P was read (`block_unknown_variadic_split`);
            // `check_placement` blocks it again here, so no path grades it Unknown for
            // `AllowUnknown` to ship. A variadic callee that states its fixed prefix stays
            // Unknown.
            if let Err(e) =
                check_placement(module, &caller_view, callee_decl.calling_conv, gp, false)
            {
                ob.o3_events = e.grade(&format!("the callee `{g}`"), |e| {
                    format!(
                        "the callee `{g}` is called under a signature P(`{g}`) does not place: {e} \
                         (the same symbol under two signatures)"
                    )
                });
                return None;
            }
            let callee_abi = match abi_extensions::Plan::new(
                module,
                callee_decl.calling_conv,
                &caller_view.0,
                &caller_view.1,
                gp,
                false,
            ) {
                Ok(plan) => plan,
                Err(reason) => {
                    ob.o3_events = ObligationGrade::unknown(reason);
                    return None;
                }
            };
            if let Some(record) = callee_abi.record() {
                let codegen_authority =
                    input.m_cg.functions.iter().find(|function| function.name == *g).is_some_and(
                        |function| {
                            function.calling_conv == callee_decl.calling_conv
                                && input.m_cg.func_type(function.ty).is_some_and(|signature| {
                                    signature.abi.is_none()
                                        && !signature.is_vararg
                                        && signature.params == caller_view.0
                                        && signature.returns == caller_view.1
                                })
                        },
                    );
                if !abi_extensions::qualified_target(input.m_cg)
                    || !codegen_authority
                    || module
                        .func_type(callee_decl.ty)
                        .is_none_or(|signature| signature.abi.is_some())
                {
                    ob.o3_events = ObligationGrade::unknown(
                        "C-u8 call lacks codegen target/convention/signature authority",
                    );
                    return None;
                }
                if let Some(body) = input.bodies.get(g) {
                    let correct = input.producers.get(body.producer).is_some_and(|producer| {
                        abi_extensions::qualified_target(&producer.module)
                            && producer.module.function_by_id(body.func).is_some_and(|function| {
                                function.calling_conv == callee_decl.calling_conv
                            })
                    });
                    if !correct {
                        ob.o3_events = ObligationGrade::unknown(
                            "C-u8 callee body convention/target differs from its call declaration",
                        );
                        return None;
                    }
                }
                cert.abi_contracts.insert(g.clone(), record);
            }
            // ... and as g's own producer body declares it, when we hold one.
            if let Some(gb) = input.bodies.get(g) {
                let own = input
                    .producers
                    .get(gb.producer)
                    .and_then(|p| p.module.function_by_id(gb.func).map(|f| (p, f.ty)))
                    .ok_or_else(|| "callee body missing".to_string())
                    .and_then(|(p, ty)| signature_of(&p.module, ty));
                match own {
                    Ok(own) if own == caller_view => {}
                    Ok(own) => {
                        ob.o3_events = ObligationGrade::unknown(format!(
                            "`{g}` is called as {caller_view:?} but its body declares {own:?} (the same \
                             symbol under two signatures)"
                        ));
                        return None;
                    }
                    Err(e) => {
                        ob.o3_events = ObligationGrade::unknown(e);
                        return None;
                    }
                }
            }
            let result_width = match &gp.ret {
                ReturnPlace::Void => None,
                ReturnPlace::Scalar(s) => Some(s.width),
                ReturnPlace::Indirect => {
                    ob.o5_frame = ObligationGrade::unknown(format!(
                        "`{g}` returns through sret: Unknown until step 5.10"
                    ));
                    return None;
                }
            };
            cert.placement_sha256.insert(g.clone(), gp.digest());
            let co_emitted = layout.windows.get(g).is_some_and(|w| w.expected.non_preemptible);
            assumptions.insert(if co_emitted {
                Assumption::CoEmitted(g.clone())
            } else {
                Assumption::External(g.clone())
            });
            for s in sites {
                decisions.insert(
                    s.key,
                    SiteDecision::Called { symbol: g.clone(), place: gp.clone(), result_width },
                );
            }
        } else {
            ob.o2_pairing = ObligationGrade::unknown(format!(
                "`{g}` has {} IR call site(s) but {n_m} machine call(s): mixed inlined/called sites of \
                 one callee, or a duplicated call",
                sites.len()
            ));
            return None;
        }
    }
    cert.assumptions = assumptions.into_iter().collect();

    // ---- the spec side -----------------------------------------------------
    let spec = match eval_spec(input, module, func, &own_sig, place, &decisions) {
        Ok(s) => s,
        Err(e) => {
            ob.o4_return = ObligationGrade::unknown(format!("spec side: {e}"));
            return None;
        }
    };
    if !spec.memory.accesses.is_empty() {
        source_memory_roots.insert(symbol.clone());
    }

    // ---- the machine side --------------------------------------------------
    let mut callee_places: BTreeMap<u64, FnPlacement> = BTreeMap::new();
    for s in &mach_sites {
        // Every site here names its callee (the O2 site decisions above refuse
        // one that does not); a site that did not would be unpaired below.
        let p =
            s.callee.as_ref().and_then(|g| by_callee_ir.get(g)).and_then(|v| v.first()).and_then(
                |site| match decisions.get(&site.key) {
                    Some(SiteDecision::Called { place, .. }) => Some(place.clone()),
                    _ => None,
                },
            );
        match p {
            Some(p) => {
                callee_places.insert(s.offset, p);
            }
            None => {
                ob.o2_pairing = ObligationGrade::unknown(format!(
                    "machine call at {:#x} is not paired to a placement",
                    s.offset
                ));
                return None;
            }
        }
    }
    let mut entry_state = MachineState::symbolic();
    // M1 is explicit on both executors. A common array is not a validity or
    // frame premise, and the pending-memory guard below still prevents a grade.
    entry_state.memory = spec.memory.entry.clone();
    own_abi.apply_entry(&mut entry_state);
    let bound_observer =
        observer_object.as_ref().map_err(Clone::clone).and_then(|object| object.function(&symbol));
    let mut exec = CerExec::new(window, &callee_places, &place.ret, x18_reserved);
    exec.dead_tail_adrp = dead.adrps();
    let memory_frontier = spec.memory.missing_integration();
    // Zero observed source memory is a genuine complete M0 -> M0 case, not a
    // reason to omit the full-memory theorem. The same sealed source census,
    // actual trace and entire original q64/ABI goal must still check. Retention
    // remains optional for the existing legacy scalar production scope only.
    let optional_scalar_original = retain_scalar_original
        && memory_frontier.is_none()
        && ir_sites.is_empty()
        && mach_sites.is_empty();
    let leaf_source = (memory_frontier.is_some() || optional_scalar_original)
        .then(|| leaf_memory::Source::read(module, func, &spec, input.m_cg, &symbol));
    match &bound_observer {
        Ok(bound) => match bound.begin_for_window(window, &entry_state) {
            Ok(session) => exec.memory_observer = Some(session),
            Err(reason) => exec.observation_incomplete.push(reason),
        },
        Err(reason) => exec.observation_incomplete.push(format!("observer binding: {reason}")),
    }
    if matches!(leaf_source, Some(Ok(_)))
        || unwind_inventory.as_ref().is_ok_and(|inventory| inventory.supports(&symbol))
    {
        match &bound_observer {
            Ok(bound) => match leaf_memory::Trace::begin(bound, window, &entry_state) {
                Ok(trace) => exec.leaf_trace = Some(trace),
                Err(reason) => exec.leaf_refusal = Some(reason),
            },
            Err(reason) => exec.leaf_refusal = Some(reason.clone()),
        }
    }
    let result = exec.run(window.start, entry_state, Vec::new(), 0, false, Formula::Bool(true));
    if let Err(reason) = &result {
        exec.observation_incomplete.push(format!("CER traversal stopped: {reason}"));
    }
    let (memory_observation, frame_execution) = exec.take_memory_diagnostics();
    cert.memory_observation = Some(memory_observation);
    cert.frame_execution = frame_execution;
    // A fresh conditional-step replay reconstructs actual source/P/spec/entry
    // and decoded effects, then stops BEFORE any proof/solver producer. It
    // cannot earn a function or metadata grade and performs no caller compose.
    if observe_only {
        ob.o4_return = ObligationGrade::unknown("conditional frame replay: observation only");
        return None;
    }
    let outcome = match result {
        Ok(o) => o,
        Err(e) => {
            ob.o4_return = ObligationGrade::unknown(format!("machine side: {e}"));
            return None;
        }
    };

    let actual_trace = match exec.leaf_refusal.take() {
        Some(reason) => Err(reason),
        None => exec
            .leaf_trace
            .take()
            .ok_or("complete ordinary trace unavailable".to_string())
            .and_then(leaf_memory::Trace::finish),
    };
    if let (Ok(inventory), Ok(trace)) = (unwind_inventory, &actual_trace) {
        let retained = match original_mode {
            OriginalMode::Produce => None,
            OriginalMode::Replay(row) => Some(row.compact_unwind.as_ref()),
        };
        match inventory.check(input, cert, trace, retained) {
            Ok(checked) => {
                cert.compact_unwind = Some(checked.certificate().clone());
                checked_unwind.push(checked);
            }
            Err(_reason) => {}
        }
    }
    let ob = &mut cert.obligations;

    // Sealed leaf inputs can authorize only the bounded original-statement
    // joint kernel consumer below. Diagnostics are not admission authority.
    let leaf_kernel_inputs = leaf_source.and_then(|source| {
        let inputs = source.and_then(|source| {
            let execution = actual_trace.clone()?;
            match original_mode {
                OriginalMode::Produce => leaf_memory::KernelInputs::derive(source, execution),
                OriginalMode::Replay(row) => leaf_memory::KernelInputs::derive_replay(
                    source,
                    execution,
                    row.original_proof.as_ref().ok_or("retained leaf packet missing")?,
                ),
            }
        });
        match inputs {
            Ok(inputs) => {
                cert.leaf_memory = Some(inputs.diagnostic().clone());
                Some(inputs)
            }
            Err(reason) => {
                let mut diagnostic = leaf_memory::Diagnostic::refused(reason.clone());
                if optional_scalar_original {
                    diagnostic.status = format!("complete original retention unavailable ({reason}); legacy scalar verification only");
                }
                cert.leaf_memory = Some(diagnostic);
                None
            }
        }
    });

    // The bounded leaf has no private frame/calls/path debt and consumes ALL
    // original O0/O4/source-byte/whole-array equations in ONE Clean goal. Every
    // missing witness or declined proof retains the old Unknown boundary;
    // no memory countermodel becomes a new Refuted verdict here.
    if memory_frontier.is_some() || optional_scalar_original {
        let required =
            memory_frontier.is_some() || matches!(original_mode, OriginalMode::Replay(_));
        let reason = memory_frontier.as_deref().unwrap_or("complete scalar original retention");
        if let Some(inputs) = leaf_kernel_inputs {
            if !ir_sites.is_empty() || !mach_sites.is_empty() || !cert.assumptions.is_empty() {
                ob.o4_return = ObligationGrade::unknown("leaf call inventory is not empty");
                return None;
            }
            match inputs.close(
                place,
                &own_abi,
                &outcome,
                x18_reserved,
                match original_mode {
                    OriginalMode::Produce => None,
                    OriginalMode::Replay(row) => row.original_proof.as_ref(),
                },
            ) {
                Ok(closed) => {
                    cert.leaf_memory = Some(closed.diagnostic().clone());
                    ob.o0_abi = ObligationGrade::proven(
                        "every original ABI location is preserved in the same kernel conjunction; X18 is never written",
                    );
                    ob.o2_pairing = ObligationGrade::proven(
                        "the actual typed source and bound straight-line bytes have no calls or tails",
                    );
                    ob.o3_events = ObligationGrade::proven(
                        "no call events; every actual machine byte has a kernel-checked original source-coverage equality",
                    );
                    ob.o4_return = ObligationGrade::proven(
                        "the physical scalar return and entire exit arrays agree in one original-statement kernel conjunction",
                    );
                    ob.o5_frame = ObligationGrade::proven(
                        "complete actual effects establish an empty private frame and no calls; every non-frame byte is source-covered",
                    );
                    *closed_leaf = Some(closed.clone());
                    return Some(closed.into_evidence());
                }
                Err(detail) => {
                    if let Some(diagnostic) = cert.leaf_memory.as_mut() {
                        diagnostic.status = if optional_scalar_original && !required {
                            format!(
                                "complete original retention unavailable ({detail}); legacy scalar verification only"
                            )
                        } else {
                            format!("{detail}; no memory grade granted")
                        };
                    }
                    if required {
                        ob.o4_return = ObligationGrade::unknown(format!("{reason}; {detail}"));
                    }
                }
            }
        } else if required {
            ob.o4_return = ObligationGrade::unknown(reason);
        }
        if required {
            return None;
        }
    }

    // Original-proof replay is a bounded leaf verifier. It never invokes the
    // legacy scalar solver/proof producer to replace unavailable evidence.
    if matches!(original_mode, OriginalMode::Replay(_)) {
        ob.o4_return = ObligationGrade::unknown(
            "the actual function is outside retained original leaf replay",
        );
        return None;
    }

    // ---- O5 ---------------------------------------------------------------
    ob.o5_frame = if !exec.o5_refuted.is_empty() {
        ObligationGrade::refuted(exec.o5_refuted.join("; "))
    } else if !exec.o5_unknown.is_empty() {
        ObligationGrade::unknown(exec.o5_unknown.join("; "))
    } else {
        ObligationGrade::proven(
            "every store is in the function's own frame; no call receives an SP-derived argument",
        )
    };

    // ---- O0 ---------------------------------------------------------------
    let residue = abi_guarantee_residue(&outcome, x18_reserved);
    let abi = match discharge_abi_guarantee(&symbol, &residue, &[]) {
        AbiDischarge::Verdict(OutputVerdict::Refuted { .. })
            if residue
                .iter()
                .any(|condition| abi_extensions::observes_callee_padding(&condition.claim)) =>
        {
            AbiDischarge::Verdict(OutputVerdict::Unknown {
                reason: "O0 counterexample depends on unspecified callee result padding".into(),
            })
        }
        other => other,
    };
    ob.o0_abi = match &abi {
        AbiDischarge::Structural => {
            ObligationGrade::proven("every location reads back as its entry value (structural)")
        }
        AbiDischarge::SolverValidated => ObligationGrade::proven(format!(
            "{} residual conjunct(s) discharged by ay",
            residue.len()
        )),
        AbiDischarge::Verdict(OutputVerdict::Refuted { detail }) => {
            ObligationGrade::refuted(detail.clone())
        }
        AbiDischarge::Verdict(OutputVerdict::Unknown { reason }) => {
            ObligationGrade::unknown(reason.clone())
        }
        AbiDischarge::Verdict(_) => {
            ObligationGrade::unknown("O0 discharge returned an unexpected verdict")
        }
    };

    // ---- O2 (second half): structural pairing candidates -------------------
    let ir_succ = ir_successors(func);
    let called: Vec<&IrSite> = ir_sites
        .iter()
        .filter(|s| matches!(decisions.get(&s.key), Some(SiteDecision::Called { .. })))
        .collect();
    let mut groups: Vec<(Vec<SiteKey>, Vec<u64>)> = Vec::new();
    for (g, sites) in &by_callee_ir {
        if let Some(offs) = by_callee_m.get(g) {
            groups.push((sites.iter().map(|s| s.key).collect(), offs.clone()));
        }
    }
    let candidates = match enumerate_bijections(&groups, 5040) {
        Some(c) => c,
        None => {
            ob.o2_pairing =
                ObligationGrade::unknown("too many candidate pairings (more than 5040)");
            return None;
        }
    };
    let total = candidates.len();
    let valid: Vec<BTreeMap<SiteKey, u64>> = candidates
        .into_iter()
        .filter(|pi| {
            called.iter().all(|s1| {
                called.iter().all(|s2| {
                    s1.key == s2.key
                        || ir_precedes(&ir_succ, s1.key, s2.key)
                            == window.precedes(pi[&s1.key], pi[&s2.key])
                })
            })
        })
        .collect();
    if valid.is_empty() {
        // Structural precedence ignores path feasibility, so a mismatch is a
        // REFUTATION only when it cannot be an infeasible path: the pairing is
        // forced (one candidate) and every paired site is reached
        // unconditionally — once, on every execution — on both sides. Then
        // both executions perform every call, in two different orders.
        let unconditional = |insts: Option<&Vec<EventInstance>>| matches!(insts.map(Vec::as_slice), Some([one]) if one.path == Formula::Bool(true));
        let forced_and_unconditional = total == 1
            && called.iter().all(|s| unconditional(spec.events.get(&s.key)))
            && mach_sites.iter().all(|m| unconditional(exec.events.get(&m.offset)));
        ob.o2_pairing = if forced_and_unconditional {
            ObligationGrade::refuted(
                "every call is made unconditionally on both sides and the only pairing by callee \
                 symbol orders them differently from the IR: the machine calls in another order",
            )
        } else if total == 1 {
            ObligationGrade::unknown(
                "the only pairing by callee symbol disagrees with the IR's call order on the \
                 structural CFG (which may include infeasible paths)",
            )
        } else {
            ObligationGrade::unknown(format!(
                "none of the {total} candidate pairings agrees with the IR's call order"
            ))
        };
        return None;
    }

    // ---- O3/O4 under each valid pairing ------------------------------------
    let mut refutation: Option<(String, String)> = None;
    let mut undecided: Option<(String, String)> = None;
    for pi in &valid {
        match discharge_under(
            &symbol, &spec, &exec, &outcome, pi, &decisions, &residue, &abi, &own_abi,
        ) {
            PairOutcome::Proven { o3, o4, evidence } => {
                ob.o2_pairing = ObligationGrade::proven(format!(
                    "{} paired call site(s){}",
                    pi.len(),
                    if valid.len() > 1 {
                        format!(" (one of {} structurally valid pairings)", valid.len())
                    } else {
                        String::new()
                    }
                ));
                ob.o3_events = ObligationGrade::proven(o3);
                ob.o4_return = ObligationGrade::proven(o4);
                cert.call_sites = call_site_records(&ir_sites, &decisions, pi, window);
                return evidence;
            }
            PairOutcome::Refuted { which, detail } => {
                refutation.get_or_insert((which, detail));
            }
            PairOutcome::Unknown { which, detail } => {
                undecided.get_or_insert((which, detail));
            }
        }
    }
    cert.call_sites = call_site_records(&ir_sites, &decisions, &valid[0], window);
    ob.o2_pairing =
        ObligationGrade::proven(format!("{} structurally valid pairing(s)", valid.len()));
    let assign = |ob: &mut Obligations, which: &str, g: ObligationGrade| match which {
        "O3" => ob.o3_events = g,
        "O4" => ob.o4_return = g,
        _ => ob.o4_return = g,
    };
    match (refutation, undecided) {
        (Some((which, detail)), _) if valid.len() == 1 => {
            assign(ob, &which, ObligationGrade::refuted(detail))
        }
        (Some((which, detail)), _) => assign(
            ob,
            &which,
            ObligationGrade::unknown(format!(
                "a counterexample exists under one of {} candidate pairings, which is not evidence \
                 against the bytes: {detail}",
                valid.len()
            )),
        ),
        (None, Some((which, detail))) => assign(ob, &which, ObligationGrade::unknown(detail)),
        (None, None) => ob.o4_return = ObligationGrade::unknown("no pairing was discharged"),
    }
    None
}

fn call_site_records(
    ir_sites: &[IrSite],
    decisions: &BTreeMap<SiteKey, SiteDecision>,
    pi: &BTreeMap<SiteKey, u64>,
    window: &FunctionWindow,
) -> Vec<CallSiteRecord> {
    ir_sites
        .iter()
        .map(|s| match decisions.get(&s.key) {
            Some(SiteDecision::Called { symbol, .. }) => {
                let off = pi.get(&s.key).copied();
                let m = off.and_then(|o| window.site_at(o));
                CallSiteRecord {
                    offset: off,
                    reloc: m.and_then(|m| m.reloc).map(|r| r.name()),
                    symbol: symbol.clone(),
                    ir_site: site_name(s.key),
                    kind: if m.is_some_and(|m| m.kind == MachineSiteKind::Tail) {
                        CallSiteKind::Tail
                    } else {
                        CallSiteKind::Direct
                    },
                }
            }
            _ => CallSiteRecord {
                offset: None,
                reloc: None,
                symbol: s.callee_symbol.clone(),
                ir_site: site_name(s.key),
                kind: CallSiteKind::InterpretedInline,
            },
        })
        .collect()
}

/// Every bijection pairing each group's IR sites with its machine sites (equal
/// counts per group), or `None` past `limit`.
fn enumerate_bijections(
    groups: &[(Vec<SiteKey>, Vec<u64>)],
    limit: usize,
) -> Option<Vec<BTreeMap<SiteKey, u64>>> {
    let mut out: Vec<BTreeMap<SiteKey, u64>> = vec![BTreeMap::new()];
    for (ir, m) in groups {
        let perms = permutations(m);
        let mut next = Vec::new();
        for base in &out {
            for p in &perms {
                let mut pi = base.clone();
                for (k, o) in ir.iter().zip(p) {
                    pi.insert(*k, *o);
                }
                next.push(pi);
                if next.len() > limit {
                    return None;
                }
            }
        }
        out = next;
    }
    Some(out)
}

fn permutations(v: &[u64]) -> Vec<Vec<u64>> {
    if v.len() <= 1 {
        return vec![v.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..v.len() {
        let mut rest = v.to_vec();
        let head = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, head);
            out.push(p);
        }
    }
    out
}

/// Producer CFG successors, by block id.
fn ir_successors(func: &trust_ir::Function) -> BTreeMap<u32, Vec<u32>> {
    let mut succ = BTreeMap::new();
    for block in &func.blocks {
        let mut s = Vec::new();
        if let Some(term) = block.body.last() {
            match &term.inst {
                Inst::Br { target, .. } => s.push(target.index()),
                Inst::CondBr { then_target, else_target, .. } => {
                    s.push(then_target.index());
                    s.push(else_target.index());
                }
                Inst::Switch { default, cases, .. } => {
                    s.push(default.index());
                    s.extend(cases.iter().map(|c| c.target.index()));
                }
                _ => {}
            }
        }
        succ.insert(block.id.index(), s);
    }
    succ
}

/// Whether IR site `a` precedes `b` on some path.
fn ir_precedes(succ: &BTreeMap<u32, Vec<u32>>, a: SiteKey, b_: SiteKey) -> bool {
    if a.0 == b_.0 && a.1 < b_.1 {
        return true;
    }
    let mut seen = BTreeSet::new();
    let mut work: Vec<u32> = succ.get(&a.0).cloned().unwrap_or_default();
    while let Some(n) = work.pop() {
        if n == b_.0 {
            return true;
        }
        if seen.insert(n) {
            work.extend(succ.get(&n).cloned().unwrap_or_default());
        }
    }
    false
}

// ---- signatures and P ------------------------------------------------------

/// A signature as the gate compares it.
type Signature = (Vec<IrTy>, Vec<IrTy>, bool);

fn signature_of(module: &Module, ty: trust_ir::value::FuncTyId) -> Result<Signature, String> {
    let t = module
        .func_types
        .get(ty.as_usize())
        .ok_or_else(|| "a FuncTy the module lacks".to_string())?;
    Ok((t.params.clone(), t.returns.clone(), t.is_vararg))
}

/// Why P does not place a signature ([`check_placement`]).
#[derive(Debug, Clone, PartialEq, Eq)]
enum PlacementRefusal {
    /// A variadic signature whose split between fixed and anonymous arguments
    /// is not established ([`variadic_split`]): BLOCKED, Refuted under every
    /// policy. The string completes "<the signature's owner> is …".
    UnknownSplit(String),
    /// A signature P does not place (yet): Unknown.
    Unplaced(String),
}

impl PlacementRefusal {
    /// The grade: Refuted for an unknown split (`owner` names the signature's
    /// owner), Unknown otherwise (`unplaced` words the reason).
    fn grade(self, owner: &str, unplaced: impl FnOnce(String) -> String) -> ObligationGrade {
        match self {
            PlacementRefusal::UnknownSplit(why) => {
                ObligationGrade::refuted(format!("{owner} is {why}"))
            }
            PlacementRefusal::Unplaced(e) => ObligationGrade::unknown(unplaced(e)),
        }
    }
}

/// Whether `conv` has a variadic form: an ABI that says where an anonymous
/// argument goes. rustc admits `...` under exactly these (`C`, `C-unwind`,
/// `sysv64`, `win64`, `aapcs`, `efiapi`: `ExternAbi::supports_varargs`). The
/// others have none: the Rust ABI (`Rust`, `RustCold`), fastcc and coldcc
/// (LLVM LangRef: "This calling convention does not support varargs"), and
/// swiftcall and vectorcall (clang admits no variadic call under either). The
/// match names every convention, so a new one is a compile error here until it
/// is classified.
fn conv_has_variadic_form(conv: CallingConv) -> bool {
    match conv {
        CallingConv::C
        | CallingConv::CUnwind
        | CallingConv::SysV64
        | CallingConv::Win64
        | CallingConv::Aapcs
        | CallingConv::EfiApi => true,
        CallingConv::Rust
        | CallingConv::RustCold
        | CallingConv::Fast
        | CallingConv::Cold
        | CallingConv::Swift
        | CallingConv::VectorCall => false,
    }
}

/// The split between `sig`'s fixed and anonymous arguments under the
/// convention `conv` its owner declares (a callee, a definition, or an indirect
/// call's own signature). `Ok` when `sig` is not variadic. A variadic signature
/// that states its fixed prefix (`params`) under a convention with a variadic
/// form ([`conv_has_variadic_form`]) is `Unplaced`, Unknown as it always was: P
/// places no anonymous argument before step 5.10. One that does not is
/// `UnknownSplit`:
///
/// * NO fixed parameter, `(...)`: the producer's spelling of a callee it could
///   not sign (a variadic `fcntl`, or a non-variadic
///   `posix_spawn_file_actions_adddup2` whose parameter it has no type for).
///   No C prototype before C23 has that shape, and trust-ir cannot tell a C23
///   `f(...)` from it.
/// * the Rust ABI (`Rust`, `RustCold`): it has no variadic form, so the fixed
///   prefix is a producer placeholder.
/// * any other convention with no variadic form (fastcc, coldcc, swiftcall,
///   vectorcall): no ABI defines the split, and trust-cg lowers fastcc and
///   coldcc through the C register ABI, i.e. it would guess C's.
///
/// The ABI passes fixed and anonymous arguments differently (Apple arm64 puts
/// every anonymous one on the stack; x86-64 SysV also counts vector registers
/// in AL), so a guessed split miscompiles without a trace: measured, `fcntl(fd,
/// F_SETFD, FD_CLOEXEC)` through `(...)` ran as `F_DUPFD` (KNOWN_HAZARDS
/// "producer C-ABI residuals after S2/S3"). trust-cg's adapter refuses the
/// first two shapes by name (`trust_cg_lower::reject_unsigned_variadic_callee`,
/// decision OD-55, which names `Rust` alone); this predicate is its own, in the
/// frozen file, so a dependency cannot widen what the gate accepts.
fn variadic_split(sig: &Signature, conv: CallingConv) -> Result<(), PlacementRefusal> {
    let (params, _, vararg) = sig;
    if !*vararg {
        return Ok(());
    }
    if params.is_empty() {
        return Err(PlacementRefusal::UnknownSplit(
            "declared `(...)` with no fixed parameter: an unsigned signature, whose fixed/anonymous \
             split no call can establish (a variadic call places its arguments on the stack where \
             a callee with a fixed parameter does not read them)"
                .into(),
        ));
    }
    if matches!(conv, CallingConv::Rust | CallingConv::RustCold) {
        return Err(PlacementRefusal::UnknownSplit(format!(
            "declared variadic under the `{conv:?}` convention: the Rust ABI has no variadic form, \
             so its {} fixed parameter(s) are a producer placeholder, not a split",
            params.len()
        )));
    }
    if !conv_has_variadic_form(conv) {
        return Err(PlacementRefusal::UnknownSplit(format!(
            "declared variadic under the `{conv:?}` convention, which has no variadic form: its {} \
             fixed parameter(s) are not a split any ABI defines (trust-cg lowers fastcc and coldcc \
             through the C register ABI, so it would guess C's split)",
            params.len()
        )));
    }
    Err(PlacementRefusal::Unplaced("variadic".into()))
}

// ---- the variadic-split block ----------------------------------------------
//
// A variadic split is UNKNOWN, and the function that carries it BLOCKED, when
// no reading of the modules the gate reads (every producer, and `M_cg`, the
// module trust-cg compiled) establishes that a call places its arguments the
// way its callee reads them:
//
//   * a signature `variadic_split` refuses (`(...)`, a convention with no
//     variadic form), the function's own or any edge's;
//   * a signature the gate cannot read, or a callee FuncId the module lacks;
//   * a direct call with fewer arguments than its variadic callee's stated
//     fixed prefix;
//   * a variadic callee of an instruction that places its arguments by its own
//     fixed rule (a SeqMap element function, drop glue, a panic entry);
//   * an indirect call through ANY variadic signature: the edge cannot
//     establish that its target declares the same split (trust-cg refuses every
//     variadic CallIndirect);
//   * the ADDRESS of a function some module declares variadic (or cannot
//     read), taken by a constant in a body or in a data initializer: a pointer
//     to it is called only through an indirect edge, and the gate does not
//     trace a pointer to its calls (trust-cg refuses an indirect call through
//     a pointer to a variadic declaration, [TCG-VARARG-ABI]);
//   * a symbol two modules declare with different splits, one of them variadic
//     or unreadable: a call placed by one declaration is read by another.

/// One function's split as one module declares it: its fixed parameters and
/// whether it is variadic, or `None` when the module's FuncTy table lacks the
/// signature (whether it is variadic is then unknown).
type DeclaredSplit = Option<(Vec<IrTy>, bool)>;

/// A symbol's distinct declared splits, each with the first module declaring it.
type Declarations = Vec<(DeclaredSplit, String)>;

fn declared_split(module: &Module, ty: FuncTyId) -> DeclaredSplit {
    module.func_types.get(ty.as_usize()).map(|t| (t.params.clone(), t.is_vararg))
}

/// A split that is variadic, or unknown.
fn maybe_variadic(split: &DeclaredSplit) -> bool {
    !matches!(split, Some((_, false)))
}

fn show_split(split: &DeclaredSplit) -> String {
    match split {
        None => "an unreadable signature".into(),
        Some((params, vararg)) => {
            let mut shown: Vec<String> = params.iter().map(|t| format!("{t:?}")).collect();
            if *vararg {
                shown.push("...".into());
            }
            format!("`({})`", shown.join(", "))
        }
    }
}

fn show_declarations(decls: &Declarations) -> String {
    decls.iter().map(|(s, by)| format!("{} by {by}", show_split(s))).collect::<Vec<_>>().join(", ")
}

/// The link symbol of `f`: S's name for it in a producer, its own name in `M_cg`.
fn symbol_of<'m>(
    f: &'m trust_ir::Function,
    symbols: Option<&'m BTreeMap<FuncId, String>>,
) -> &'m str {
    symbols.and_then(|s| s.get(&f.id)).map_or(f.name.as_str(), String::as_str)
}

/// One module the gate reads: a producer (with its S) or `M_cg`.
#[derive(Clone, Copy)]
struct GateModule<'a> {
    module: &'a Module,
    symbols: Option<&'a BTreeMap<FuncId, String>>,
    /// The producer's index, `None` for `M_cg`.
    producer: Option<usize>,
}

impl GateModule<'_> {
    fn label(&self) -> String {
        match self.producer {
            Some(i) => format!("producer {i}"),
            None => "M_cg".into(),
        }
    }
}

/// Every producer, in order, then `M_cg`.
fn gate_modules<'a>(input: &CerInput<'a>) -> Vec<GateModule<'a>> {
    let mut out: Vec<GateModule<'a>> = input
        .producers
        .iter()
        .enumerate()
        .map(|(i, p)| GateModule {
            module: &p.module,
            symbols: Some(&p.symbols),
            producer: Some(i),
        })
        .collect();
    out.push(GateModule { module: input.m_cg, symbols: None, producer: None });
    out
}

/// What the variadic-split block reads across every module, built once per object.
struct SplitIndex<'a> {
    /// Each function symbol's distinct declared splits.
    by_symbol: BTreeMap<&'a str, Declarations>,
    /// `M_cg`'s bodies, by symbol.
    m_cg_bodies: BTreeMap<&'a str, &'a trust_ir::Function>,
    /// Per module of [`gate_modules`] (producers in order, `M_cg` last): why a
    /// data initializer it holds blocks every body it holds.
    data_blocks: Vec<Option<String>>,
}

impl<'a> SplitIndex<'a> {
    fn new(input: &CerInput<'a>) -> Self {
        let modules = gate_modules(input);
        let mut by_symbol: BTreeMap<&'a str, Declarations> = BTreeMap::new();
        for gm in &modules {
            for f in &gm.module.functions {
                let split = declared_split(gm.module, f.ty);
                let decls = by_symbol.entry(symbol_of(f, gm.symbols)).or_default();
                if !decls.iter().any(|(s, _)| *s == split) {
                    decls.push((split, gm.label()));
                }
            }
        }
        let m_cg_bodies = input
            .m_cg
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .map(|f| (f.name.as_str(), f))
            .collect();
        let mut index = SplitIndex { by_symbol, m_cg_bodies, data_blocks: Vec::new() };
        let data_blocks = modules
            .iter()
            .map(|gm| {
                gm.module.globals.iter().find_map(|g| {
                    let why = index.address_block(gm, g.initializer.as_ref()?)?;
                    Some(format!(
                        "the initializer of the global `{}` in {} {why}",
                        g.name,
                        gm.label()
                    ))
                })
            })
            .collect();
        index.data_blocks = data_blocks;
        index
    }

    /// `Some(account)` when the modules the gate reads declare `symbol` with
    /// more than one split, one of them variadic or unreadable.
    fn conflict(&self, symbol: &str) -> Option<String> {
        let decls = self.by_symbol.get(symbol)?;
        (decls.len() > 1 && decls.iter().any(|(s, _)| maybe_variadic(s)))
            .then(|| show_declarations(decls))
    }

    /// `Some(why)` (completing "<the constant> …") when `constant`, or a
    /// constant inside it, is the address of a function that `gm`, or any module
    /// the gate reads, declares variadic or cannot read.
    fn address_block(&self, gm: &GateModule<'_>, constant: &Constant) -> Option<String> {
        constant
            .try_visit_constants(|c| {
                let (name, local) = match c {
                    Constant::FnDef(g) | Constant::Closure { func: g, .. } => {
                        let Some(f) = gm.module.function_by_id(*g) else {
                            return ControlFlow::Break(format!(
                                "takes the address of FuncId({}), which the module lacks: whether it \
                                 is variadic, and its split, are unknown",
                                g.index()
                            ));
                        };
                        (symbol_of(f, gm.symbols), Some(f))
                    }
                    Constant::SymbolAddr { symbol, .. } => (symbol.as_str(), None),
                    _ => return ControlFlow::Continue(()),
                };
                let local_why = local.and_then(|f| match signature_of(gm.module, f.ty) {
                    Err(e) => Some(format!("whose signature the gate cannot read ({e})")),
                    Ok(sig) => match variadic_split(&sig, f.calling_conv) {
                        Err(PlacementRefusal::UnknownSplit(why)) => Some(format!("which is {why}")),
                        _ if sig.2 => Some(format!(
                            "which is declared variadic ({} fixed parameter(s))",
                            sig.0.len()
                        )),
                        _ => None,
                    },
                });
                let why = local_why.or_else(|| {
                    let decls = self.by_symbol.get(name)?;
                    decls
                        .iter()
                        .any(|(s, _)| maybe_variadic(s))
                        .then(|| format!("which is declared {}", show_declarations(decls)))
                });
                match why {
                    Some(why) => ControlFlow::Break(format!(
                        "takes the address of `{name}`, {why}: a pointer to a variadic function is \
                         called only through an indirect edge, which cannot establish its split \
                         (trust-cg refuses every variadic indirect call, and a fixed-arity one \
                         through a pointer to a variadic declaration, [TCG-VARARG-ABI]), and the \
                         gate does not trace a pointer to its calls"
                    )),
                    None => ControlFlow::Continue(()),
                }
            })
            .break_value()
    }
}

/// What the block found, and which obligation carries it.
enum SplitBlock {
    /// The function's own signature or symbol (O4).
    Own(String),
    /// An edge, an address, or data the function's module holds (O3).
    Edge(String),
}

/// One body of the function the block reads: its producer body, or its `M_cg` body.
struct SplitView<'a> {
    gm: GateModule<'a>,
    func: &'a trust_ir::Function,
}

/// BLOCK `symbol` when any reading of it has an unknown variadic split (the
/// list above this function's helpers): Refuted, before anything else about the
/// function is read, so neither a missing P, nor another obligation's Unknown,
/// nor an inlined site, nor an x86-64 object grades it Unknown for
/// `AllowUnknown` to ship. Both of the function's bodies are read, its producer
/// body and its `M_cg` body; each is read on its own first, then against every
/// other module's declarations. Returns whether it blocked; a symbol with
/// neither body is left to the caller.
fn block_unknown_variadic_split(
    input: &CerInput<'_>,
    index: &SplitIndex<'_>,
    symbol: &str,
    ob: &mut Obligations,
) -> bool {
    let producer_view = input.bodies.get(symbol).and_then(|body| {
        let p = input.producers.get(body.producer)?;
        let func = p.module.function_by_id(body.func)?;
        let gm = GateModule {
            module: &p.module,
            symbols: Some(&p.symbols),
            producer: Some(body.producer),
        };
        Some(SplitView { gm, func })
    });
    let m_cg_view = index.m_cg_bodies.get(symbol).map(|func| SplitView {
        gm: GateModule { module: input.m_cg, symbols: None, producer: None },
        func,
    });
    let views: Vec<SplitView<'_>> = producer_view.into_iter().chain(m_cg_view).collect();
    let found = views
        .iter()
        .find_map(|v| local_split_block(v, index, symbol))
        .or_else(|| views.iter().find_map(|v| conflict_split_block(v, index, symbol)));
    match found {
        Some(SplitBlock::Own(detail)) => {
            ob.o4_return = ObligationGrade::refuted(detail);
            true
        }
        Some(SplitBlock::Edge(detail)) => {
            ob.o3_events = ObligationGrade::refuted(detail);
            true
        }
        None => false,
    }
}

/// The functions `inst` calls by FuncId, each with the number of arguments the
/// call places (`None` when the instruction places them by its own fixed rule)
/// and the callee's role.
fn direct_callees(module: &Module, inst: &Inst) -> Vec<(FuncId, Option<usize>, &'static str)> {
    let mut out = Vec::new();
    match inst {
        Inst::Call { callee, args }
        | Inst::CallCannotUnwind { callee, args }
        | Inst::Invoke { callee, args, .. } => out.push((*callee, Some(args.len()), "the callee")),
        Inst::SeqMap { fwd, .. } => out.push((*fwd, None, "the SeqMap element function")),
        Inst::Drop { ty, .. } | Inst::DropInvoke { ty, .. } => {
            if let DropResolution::Resolved(glue) = module.drop_glue_for(ty) {
                out.push((glue, None, "the drop glue"));
            }
        }
        _ => {}
    }
    if let Some(site) = inst.panic_site() {
        out.push((site.entry, None, "the panic entry"));
    }
    out
}

/// A direct edge's own reading: `Some(why)` when its split is unknown.
fn direct_split_block(
    gm: &GateModule<'_>,
    callee: FuncId,
    args: Option<usize>,
    role: &str,
    site: &str,
) -> Option<String> {
    let Some(g) = gm.module.function_by_id(callee) else {
        return Some(format!(
            "{role} at {site} is FuncId({}), which the module lacks: whether it is variadic, and \
             its split, are unknown",
            callee.index()
        ));
    };
    let owner = format!("{role} `{}` at {site}", symbol_of(g, gm.symbols));
    let sig = match signature_of(gm.module, g.ty) {
        Ok(sig) => sig,
        Err(e) => {
            return Some(format!(
                "{owner} has a signature the gate cannot read ({e}): whether it is variadic, and \
                 its split, are unknown"
            ));
        }
    };
    if let Err(PlacementRefusal::UnknownSplit(why)) = variadic_split(&sig, g.calling_conv) {
        return Some(format!("{owner} is {why}"));
    }
    let (params, _, vararg) = &sig;
    match args {
        _ if !*vararg => None,
        Some(n) if n < params.len() => Some(format!(
            "{owner} is declared with {} fixed parameter(s) but called with {n} argument(s): the \
             call does not supply the split its callee states",
            params.len()
        )),
        Some(_) => None,
        None => Some(format!(
            "{owner} is declared variadic ({} fixed parameter(s)), but the instruction passes its \
             arguments by its own fixed rule, which states no split",
            params.len()
        )),
    }
}

/// An indirect edge's own reading: `Some(why)` when its split is unknown, which
/// is whenever its signature is variadic or unreadable.
fn indirect_split_block(
    module: &Module,
    sig: FuncTyId,
    conv: CallingConv,
    site: &str,
) -> Option<String> {
    let owner = format!("the signature of the indirect call at {site}");
    let sig = match signature_of(module, sig) {
        Ok(sig) => sig,
        Err(e) => {
            return Some(format!(
                "{owner} cannot be read ({e}): whether it is variadic, and its split, are unknown"
            ));
        }
    };
    match variadic_split(&sig, conv) {
        Err(PlacementRefusal::UnknownSplit(why)) => Some(format!("{owner} is {why}")),
        _ if sig.2 => Some(format!(
            "{owner} is variadic ({} fixed parameter(s)): an indirect edge cannot establish that \
             its target declares that split, and a target declared otherwise reads its arguments \
             elsewhere (trust-cg refuses every variadic CallIndirect)",
            sig.0.len()
        )),
        _ => None,
    }
}

/// One body read on its own: the function's own signature, the data its
/// module holds, and every edge and address in the body.
fn local_split_block(
    v: &SplitView<'_>,
    index: &SplitIndex<'_>,
    symbol: &str,
) -> Option<SplitBlock> {
    let read_in = |detail: String| format!("{detail} (read in {})", v.gm.label());
    match signature_of(v.gm.module, v.func.ty) {
        Err(e) => {
            return Some(SplitBlock::Own(read_in(format!(
                "`{symbol}` itself has a signature the gate cannot read ({e}): whether it is \
                 variadic, and its split, are unknown"
            ))));
        }
        Ok(sig) => {
            if let Err(PlacementRefusal::UnknownSplit(why)) =
                variadic_split(&sig, v.func.calling_conv)
            {
                return Some(SplitBlock::Own(read_in(format!("`{symbol}` itself is {why}"))));
            }
        }
    }
    let data = match v.gm.producer {
        Some(i) => index.data_blocks.get(i),
        None => index.data_blocks.last(),
    };
    if let Some(Some(why)) = data {
        return Some(SplitBlock::Edge(read_in(why.clone())));
    }
    for block in &v.func.blocks {
        for (i, node) in block.body.iter().enumerate() {
            let site = site_name((block.id.index(), i));
            let found = match &node.inst {
                Inst::CallIndirect { sig, calling_conv, .. }
                | Inst::CallIndirectCannotUnwind { sig, calling_conv, .. }
                | Inst::InvokeIndirect { sig, calling_conv, .. } => {
                    indirect_split_block(v.gm.module, *sig, *calling_conv, &site)
                }
                Inst::Const { value, .. } => index
                    .address_block(&v.gm, value)
                    .map(|why| format!("the constant at {site} {why}")),
                inst => direct_callees(v.gm.module, inst).into_iter().find_map(
                    |(callee, args, role)| direct_split_block(&v.gm, callee, args, role, &site),
                ),
            };
            if let Some(detail) = found {
                return Some(SplitBlock::Edge(read_in(detail)));
            }
        }
    }
    None
}

/// One body read against every module's declarations: the function's own
/// symbol, and every direct callee's, declared with more than one split.
fn conflict_split_block(
    v: &SplitView<'_>,
    index: &SplitIndex<'_>,
    symbol: &str,
) -> Option<SplitBlock> {
    if let Some(decls) = index.conflict(symbol) {
        return Some(SplitBlock::Own(format!(
            "`{symbol}` itself is declared with more than one split ({decls}): a call placed by one \
             declaration is read under another"
        )));
    }
    for block in &v.func.blocks {
        for (i, node) in block.body.iter().enumerate() {
            for (callee, _, role) in direct_callees(v.gm.module, &node.inst) {
                // A callee the module lacks was blocked by the body's own reading.
                let Some(g) = v.gm.module.function_by_id(callee) else { continue };
                let name = symbol_of(g, v.gm.symbols);
                if let Some(decls) = index.conflict(name) {
                    return Some(SplitBlock::Edge(format!(
                        "{role} `{name}` at {} is declared with more than one split ({decls}): the \
                         call places its arguments by one declaration and the callee reads them by \
                         another (read in {})",
                        site_name((block.id.index(), i)),
                        v.gm.label()
                    )));
                }
            }
        }
    }
    None
}

/// Check that P places exactly the producer signature `sig`, whose owner
/// declares the convention `conv`: one entry per parameter, each at the
/// producer type's declared width, and no extension on any slot except a
/// definition's own `bool` result (held to 32 bits, as the step-5.0 gate does).
/// Extension-bearing CALL EDGES are refused until 5.10. A variadic signature is
/// never placed: BLOCKED when its split is unknown, Unknown otherwise
/// ([`variadic_split`]).
fn check_placement(
    module: &Module,
    sig: &Signature,
    conv: CallingConv,
    p: &FnPlacement,
    is_definition: bool,
) -> Result<(), PlacementRefusal> {
    variadic_split(sig, conv)?;
    abi_extensions::Plan::new(module, conv, &sig.0, &sig.1, p, is_definition)
        .map_err(PlacementRefusal::Unplaced)?;
    check_fixed_placement(module, sig, conv, p, is_definition).map_err(PlacementRefusal::Unplaced)
}

/// [`check_placement`] for a signature that is not variadic.
fn check_fixed_placement(
    module: &Module,
    sig: &Signature,
    conv: CallingConv,
    p: &FnPlacement,
    is_definition: bool,
) -> Result<(), String> {
    let (params, returns, _) = sig;
    if params.len() != p.params.len() {
        return Err(format!("{} parameter(s) but P places {}", params.len(), p.params.len()));
    }
    let check_scalar = |ty: &IrTy, s: &ScalarPlace, pos: SigPosition| -> Result<(), String> {
        let w = signature_reg_width(module, ty, pos)?;
        if w != s.width {
            return Err(format!("{ty:?} is {w} bits but P says {}", s.width));
        }
        let ext_ok = match s.ext {
            AbiExt::None => true,
            AbiExt::Zext => {
                (is_definition && pos == SigPosition::Return && matches!(ty, IrTy::Bool))
                    || abi_extensions::supports_zext(module, conv, ty, s.width)
            }
            AbiExt::Sext => abi_extensions::supports_sext(module, conv, ty, s.width),
        };
        if !ext_ok {
            return Err(format!(
                "extension-bearing slot ({:?}) for {ty:?}: refused until step 5.10",
                s.ext
            ));
        }
        match (s.slot, w) {
            (Slot::Gpr(r), w) if r < 8 && w <= 64 => Ok(()),
            (Slot::GprPair { lo, hi }, 128) if hi == lo + 1 && hi < 8 => Ok(()),
            (Slot::Stack { .. }, _) => {
                Err("a stack-passed argument is Unknown (the callee owns the area; step 5.10)"
                    .into())
            }
            (Slot::Indirect, _) => {
                Err("an indirectly passed argument is Unknown until step 5.10".into())
            }
            (slot, w) => Err(format!("slot {slot:?} cannot hold a {w}-bit value")),
        }
    };
    for (ty, pp) in params.iter().zip(&p.params) {
        if let IrTy::Closure(nominal) = ty {
            closure_values::placement(module, *nominal, pp)?;
            continue;
        }
        match pp {
            ParamPlace::Ignore => {
                if !matches!(ty, IrTy::Unit) {
                    return Err(format!("P ignores a {ty:?} parameter"));
                }
            }
            ParamPlace::Scalar(s) => check_scalar(ty, s, SigPosition::Parameter)?,
            ParamPlace::Pair(a, c) => {
                let IrTy::Tuple(fields) = ty else {
                    return Err(format!("P passes a {ty:?} parameter as a Pair"));
                };
                let [f0, f1] = fields.as_slice() else {
                    return Err("a Pair needs a two-field tuple".into());
                };
                check_scalar(f0, a, SigPosition::Parameter)?;
                check_scalar(f1, c, SigPosition::Parameter)?;
            }
        }
    }
    match (returns.as_slice(), &p.ret) {
        ([], ReturnPlace::Void) => Ok(()),
        ([r], ReturnPlace::Scalar(s)) => {
            if matches!(s.slot, Slot::Gpr(0) | Slot::GprPair { lo: 0, hi: 1 }) {
                check_scalar(r, s, SigPosition::Return)
            } else {
                Err(format!("a result in {:?} is not the AAPCS64 result register", s.slot))
            }
        }
        (_, ReturnPlace::Indirect) => Err("an sret result is Unknown until step 5.10".into()),
        (r, p) => Err(format!("result {r:?} placed as {p:?}")),
    }
}

// ===========================================================================
// THE SPEC SIDE (producer IR, with events)
// ===========================================================================

/// One evaluated instance of an IR call event (a path reaching the site).
#[derive(Debug, Clone)]
struct EventInstance {
    path: Formula,
    args: Vec<Formula>,
}

struct SpecResult {
    value: Formula,
    reach: Formula,
    side: Vec<Formula>,
    /// One failure predicate per unsited runtime check the spec passed: the
    /// path condition up to the check AND the check's condition failing (for
    /// an interpreted inlined callee, one of its checks failing; its
    /// `Unreachable` arms are not failures). `reach` only
    /// drops these executions; [`discharge_under`] refuses unless each is
    /// unsatisfiable (see O4 in the header).
    checks: Vec<(String, Formula)>,
    events: BTreeMap<SiteKey, Vec<EventInstance>>,
    /// Spec result variable name per Called site, and its width.
    result_vars: BTreeMap<SiteKey, (String, u32)>,
    memory: source_memory::ResultMemory,
}

#[derive(Clone)]
struct SpecEnv {
    scalars: HashMap<ValueId, IrValue>,
    /// Register aggregates (tuples, structs, arrays) as integer lanes (`aggregate_values`).
    aggs: HashMap<ValueId, aggregate_values::AggValue>,
    pairs: HashMap<ValueId, (IrValue, IrValue)>,
    closures: HashMap<ValueId, ClosureValue>,
    memory: source_memory::State,
}

struct SpecCx<'a> {
    input: &'a CerInput<'a>,
    module: &'a Module,
    func: FuncId,
    blocks: HashMap<u32, &'a trust_ir::Block>,
    decisions: &'a BTreeMap<SiteKey, SiteDecision>,
    out_width: u32,
    evals: u32,
    side: Vec<Formula>,
    checks: Vec<(String, Formula)>,
    events: BTreeMap<SiteKey, Vec<EventInstance>>,
    result_vars: BTreeMap<SiteKey, (String, u32)>,
    roots: trust_ir::analysis::PointerRoots,
    memory: source_memory::ResultMemory,
    /// Declared SSA types of the function, read once on first use (`aggregate_values`).
    value_tys: Option<HashMap<ValueId, IrTy>>,
}

const MAX_SPEC_BLOCK_EVALS: u32 = 20_000;
const MAX_SPEC_DEPTH: u32 = 1024;

fn and2(a: &Formula, c: Formula) -> Formula {
    match (a, &c) {
        (Formula::Bool(true), _) => c,
        (_, Formula::Bool(true)) => a.clone(),
        _ => Formula::And(vec![a.clone(), c]),
    }
}

fn nonzero(v: &IrValue) -> Formula {
    Formula::Not(b(Formula::Eq(b(v.f.clone()), b(Formula::BitVec { value: 0, width: v.width }))))
}

/// The spec-side reading of one parameter slot, bit-for-bit the term the
/// machine side builds for the same register (`MachineState::read_gpr`).
fn read_slot_spec(s: &ScalarPlace) -> Result<Formula, String> {
    match (s.slot, s.width) {
        (Slot::Gpr(r), 64) => Ok(xn(u32::from(r))),
        (Slot::Gpr(r), 32) => Ok(wn(u32::from(r))),
        (Slot::Gpr(r), w) if w < 64 => {
            Ok(Formula::BvExtract { inner: b(xn(u32::from(r))), high: w - 1, low: 0 })
        }
        (Slot::GprPair { lo, hi }, 128) => {
            Ok(Formula::BvConcat(b(xn(u32::from(hi))), b(xn(u32::from(lo)))))
        }
        (slot, w) => Err(format!("slot {slot:?} at {w} bits is outside the modeled fragment")),
    }
}

fn eval_spec(
    input: &CerInput<'_>,
    module: &Module,
    func: &trust_ir::Function,
    sig: &Signature,
    place: &FnPlacement,
    decisions: &BTreeMap<SiteKey, SiteDecision>,
) -> Result<SpecResult, String> {
    let blocks: HashMap<u32, &trust_ir::Block> =
        func.blocks.iter().map(|blk| (blk.id.index(), blk)).collect();
    let entry = blocks.get(&func.entry.index()).ok_or("no entry block")?;
    if entry.params.len() != sig.0.len() {
        return Err("entry block parameters differ from the signature".into());
    }
    let out_width = match &place.ret {
        ReturnPlace::Void => 1,
        ReturnPlace::Scalar(s) => s.width,
        ReturnPlace::Indirect => return Err("sret result".into()),
    };
    let entry_abi =
        abi_extensions::Plan::new(module, func.calling_conv, &sig.0, &sig.1, place, true)?;
    let memory =
        source_memory::ResultMemory::new(&format!("{}:fn{}", module.name, func.id.index()));
    let mut env = SpecEnv {
        scalars: HashMap::new(),
        aggs: HashMap::new(),
        pairs: HashMap::new(),
        closures: HashMap::new(),
        memory: source_memory::State::entry(module, entry, memory.entry.clone())?,
    };
    for (((id, ty), sig_ty), pp) in entry.params.iter().zip(&sig.0).zip(&place.params) {
        if ty != sig_ty {
            return Err(format!(
                "entry parameter type {ty:?} differs from the signature's {sig_ty:?}"
            ));
        }
        if let IrTy::Closure(nominal) = ty {
            env.closures.insert(*id, ClosureValue::incoming(module, *nominal, *id, pp)?);
            continue;
        }
        match pp {
            ParamPlace::Ignore => {}
            ParamPlace::Scalar(s) => {
                env.scalars.insert(
                    *id,
                    IrValue { f: entry_abi.source_entry(read_slot_spec(s)?), width: s.width },
                );
            }
            ParamPlace::Pair(a, c) => {
                env.pairs.insert(
                    *id,
                    (
                        IrValue { f: entry_abi.source_entry(read_slot_spec(a)?), width: a.width },
                        IrValue { f: entry_abi.source_entry(read_slot_spec(c)?), width: c.width },
                    ),
                );
            }
        }
    }
    let mut cx = SpecCx {
        input,
        module,
        func: func.id,
        blocks,
        decisions,
        out_width,
        evals: 0,
        side: Vec::new(),
        checks: Vec::new(),
        events: BTreeMap::new(),
        result_vars: BTreeMap::new(),
        roots: trust_ir::analysis::pointer_roots(func),
        memory,
        value_tys: None,
    };
    let (value, reach) = cx.block(func.entry, env, Formula::Bool(true), Vec::new(), 0)?;
    Ok(SpecResult {
        value,
        reach,
        side: cx.side,
        checks: cx.checks,
        events: cx.events,
        result_vars: cx.result_vars,
        memory: cx.memory,
    })
}

impl SpecCx<'_> {
    fn capture(&self, env: &SpecEnv, id: ValueId) -> Result<Capture, String> {
        let function = self.module.function_by_id(self.func).ok_or("source function is missing")?;
        let declared = function
            .typed_value(self.module, id)
            .ok_or("closure capture has no declared SSA value type")?;
        Capture::checked(declared.ty.clone(), lookup(&env.scalars, id)?)
    }

    fn block(
        &mut self,
        id: BlockId,
        env: SpecEnv,
        path: Formula,
        visited: Vec<u32>,
        depth: u32,
    ) -> Result<(Formula, Formula), String> {
        if depth > MAX_SPEC_DEPTH {
            return Err("IR nesting budget exceeded (fail-closed)".into());
        }
        self.evals += 1;
        if self.evals > MAX_SPEC_BLOCK_EVALS {
            return Err("IR evaluation budget exceeded (fail-closed)".into());
        }
        if visited.contains(&id.index()) {
            return Err(format!("loop/backedge at bb{} (fail-closed)", id.index()));
        }
        let mut visited = visited;
        visited.push(id.index());
        let block = *self
            .blocks
            .get(&id.index())
            .ok_or_else(|| format!("branch to missing bb{}", id.index()))?;
        let (term, body) =
            block.body.split_last().ok_or_else(|| format!("bb{} is empty", id.index()))?;
        let mut env = env;
        let mut guards: Vec<Formula> = Vec::new();
        let mut here = path;
        // BLOCK-LOCAL SLOTS (verify_output_trust_ir `admit_local_slot`): an
        // `alloca` whose address only this block's plain loads and stores of its
        // type use is a fresh cell, not memory the frame or a caller can see, so
        // its accesses are neither memory events nor records. Every other
        // `alloca` is refused here, as the catch-all refused it before; a load or
        // store through any other pointer goes to the memory model below.
        let mut slots = LocalSlots::default();
        for (index, node) in body.iter().enumerate() {
            let key = (id.index(), index);
            if let Some(step) =
                slots.step(self.module, self.func, &self.blocks, id.index(), &mut env.scalars, node)
            {
                step?;
                continue;
            }
            match &node.inst {
                Inst::Load { ty, ptr, volatile, align } => {
                    self.memory_pointer(&env, *ptr, *volatile, *align)?;
                    let bytes = source_memory::width(ty)?;
                    let [result] = node.results.as_slice() else {
                        return Err("Load must bind exactly one scalar result".into());
                    };
                    let address = lookup(&env.scalars, *ptr)?.f;
                    let value = crate::cer_memory::load_le(&env.memory.bytes, &address, bytes)?;
                    self.memory.record(
                        key,
                        env.memory.origin(&self.roots, *ptr)?,
                        crate::cer_memory::AccessKind::Read,
                        &here,
                        &address,
                        bytes,
                    )?;
                    env.scalars.insert(*result, IrValue { f: value, width: bytes * 8 });
                }
                Inst::Store { ty, ptr, value, volatile, align } => {
                    self.memory_pointer(&env, *ptr, *volatile, *align)?;
                    if !node.results.is_empty() {
                        return Err("Store cannot bind a result".into());
                    }
                    self.declared_type(*value, ty)?;
                    let bytes = source_memory::width(ty)?;
                    let address = lookup(&env.scalars, *ptr)?.f;
                    let value = lookup(&env.scalars, *value)?;
                    env.memory.bytes = crate::cer_memory::store_le(
                        env.memory.bytes.clone(),
                        &address,
                        &value.f,
                        bytes,
                    )?;
                    self.memory.record(
                        key,
                        env.memory.origin(&self.roots, *ptr)?,
                        crate::cer_memory::AccessKind::Write,
                        &here,
                        &address,
                        bytes,
                    )?;
                }
                Inst::GEP { pointee_ty, base, indices, inbounds: _ } => {
                    // Trust-IR's GEP sums indices at ONE scale. Admit only one
                    // nonnegative constant byte index; no LLVM type walk, no
                    // inbounds/no-wrap/validity fact is inferred.
                    self.memory_pointer(&env, *base, false, None)?;
                    if !matches!(pointee_ty, IrTy::I8 | IrTy::U8) || indices.len() != 1 {
                        return Err("PTR.3b requires one constant byte GEP index".into());
                    }
                    let index = lookup(&env.scalars, indices[0])?;
                    let function = self
                        .module
                        .function_by_id(self.func)
                        .ok_or("source function is missing")?;
                    if !function.typed_value(self.module, indices[0]).is_some_and(|value| {
                        matches!(value.ty, IrTy::I64 | IrTy::U64 | IrTy::Isize | IrTy::Usize)
                    }) {
                        return Err("byte GEP index does not have an integer index type".into());
                    }
                    let offset = match index.f {
                        Formula::BitVec { value, width: 64 }
                            if value >= 0 && value <= i128::from(i64::MAX) =>
                        {
                            u64::try_from(value).map_err(|_| "byte GEP index overflows")?
                        }
                        _ => {
                            return Err(
                                "byte GEP index must be a nonnegative 64-bit constant".into()
                            );
                        }
                    };
                    let [result] = node.results.as_slice() else {
                        return Err("GEP must bind one pointer result".into());
                    };
                    let base_value = lookup(&env.scalars, *base)?;
                    let address = Formula::BvAdd(
                        b(base_value.f),
                        b(Formula::BitVec { value: i128::from(offset), width: 64 }),
                        64,
                    );
                    env.memory.gep(*base, *result, offset)?;
                    self.memory.address_computation = true;
                    env.scalars.insert(*result, IrValue { f: address, width: 64 });
                }
                // A sited assert (trust-ir v54) calls its entry on failure,
                // which this model does not: it falls to `eval_ir_inst`, which
                // refuses it as outside the modeled fragment. The kind (v52)
                // names the panic, not whether the check fails.
                Inst::Assert { cond, kind: _, site: None } => {
                    let g = nonzero(&lookup(&env.scalars, *cond)?);
                    self.checks.push((
                        format!("the unsited check at bb{}[{index}]", id.index()),
                        and2(&here, Formula::Not(b(g.clone()))),
                    ));
                    here = and2(&here, g.clone());
                    guards.push(g);
                }
                Inst::Overflow { op, ty, lhs, rhs } => {
                    for (vid, v) in eval_ir_overflow(
                        &env.scalars,
                        &node.inst,
                        *op,
                        ty,
                        *lhs,
                        *rhs,
                        &node.results,
                    )? {
                        env.scalars.insert(vid, v);
                    }
                }
                Inst::MakeClosure { ty, func, captures } => {
                    let values = captures
                        .iter()
                        .map(|id| self.capture(&env, *id))
                        .collect::<Result<Vec<_>, _>>()?;
                    let value = ClosureValue::construct(self.module, *ty, *func, values)?;
                    let [result] = node.results.as_slice() else {
                        return Err("MakeClosure must bind one result".into());
                    };
                    env.closures.insert(*result, value);
                }
                Inst::Copy { ty: IrTy::Closure(nominal), operand } => {
                    let value = env
                        .closures
                        .get(operand)
                        .cloned()
                        .ok_or("Copy closure operand has no logical environment")?;
                    if value.nominal != *nominal {
                        return Err("Copy closure nominal type differs from its operand".into());
                    }
                    let [result] = node.results.as_slice() else {
                        return Err("Copy closure must bind one result".into());
                    };
                    env.closures.insert(*result, value);
                    env.memory.copy_closure(*operand, *result);
                }
                Inst::Call { callee, args } => {
                    match self.decisions.get(&key) {
                        Some(SiteDecision::Called { place, result_width, .. }) => {
                            let mut flat = Vec::new();
                            if args.len() != place.params.len() {
                                return Err(format!(
                                    "{} passes {} argument(s) for {}",
                                    site_name(key),
                                    args.len(),
                                    place.params.len()
                                ));
                            }
                            let callee = self
                                .module
                                .function_by_id(*callee)
                                .ok_or("direct call target is missing")?;
                            let signature = self
                                .module
                                .func_type(callee.ty)
                                .ok_or("direct call target signature is missing")?;
                            if signature.params.len() != args.len() {
                                return Err(
                                    "direct call logical argument arity differs from its signature"
                                        .into(),
                                );
                            }
                            for ((a, pp), expected) in
                                args.iter().zip(&place.params).zip(&signature.params)
                            {
                                if let Some(value) = env.closures.get(a) {
                                    flat.extend(value.arguments(self.module, expected, pp)?);
                                    continue;
                                }
                                if matches!(expected, IrTy::Closure(_)) {
                                    return Err(
                                        "direct call argument has no typed logical closure value"
                                            .into(),
                                    );
                                }
                                match pp {
                                    ParamPlace::Ignore => {}
                                    ParamPlace::Scalar(s) => {
                                        let v = lookup(&env.scalars, *a)?;
                                        if v.width != s.width {
                                            return Err(format!(
                                                "{}: a {}-bit argument where P places {} bits",
                                                site_name(key),
                                                v.width,
                                                s.width
                                            ));
                                        }
                                        flat.push(abi_extensions::physical_value(s, v.f)?);
                                    }
                                    ParamPlace::Pair(x, y) => {
                                        let (v0, v1) = env.pairs.get(a).cloned().ok_or_else(|| format!("{}: a Pair argument that is not a two-field aggregate", site_name(key)))?;
                                        if v0.width != x.width || v1.width != y.width {
                                            return Err(format!(
                                                "{}: Pair field widths differ from P",
                                                site_name(key)
                                            ));
                                        }
                                        flat.push(v0.f);
                                        flat.push(v1.f);
                                    }
                                }
                            }
                            self.events
                                .entry(key)
                                .or_default()
                                .push(EventInstance { path: here.clone(), args: flat });
                            self.memory.call(key, &here, &mut env.memory);
                            match (result_width, node.results.as_slice()) {
                                (None, []) => {}
                                (Some(w), [r]) => {
                                    let name = format!("CER_S#{}", site_name(key));
                                    self.result_vars.insert(key, (name.clone(), *w));
                                    env.scalars.insert(
                                        *r,
                                        IrValue {
                                            f: Formula::Var(name, Sort::BitVec(*w)),
                                            width: *w,
                                        },
                                    );
                                }
                                _ => {
                                    return Err(format!(
                                        "{}: result count differs from P",
                                        site_name(key)
                                    ));
                                }
                            }
                        }
                        Some(SiteDecision::Inlined { producer, func }) => {
                            let vals: Vec<IrValue> = args
                                .iter()
                                .map(|a| lookup(&env.scalars, *a))
                                .collect::<Result<_, _>>()?;
                            let pm = self
                                .input
                                .producers
                                .get(*producer)
                                .ok_or("inlined callee names a missing producer")?;
                            let root =
                                std::ptr::eq(Arc::as_ptr(&pm.module), self.module as *const Module)
                                    .then_some(self.func);
                            let (v, reach, ok, side) =
                                interpret_inlined_call(&pm.module, root, *func, &vals)?;
                            self.side.extend(side);
                            let [r] = node.results.as_slice() else {
                                return Err(format!(
                                    "{}: an inlined call must bind exactly one result",
                                    site_name(key)
                                ));
                            };
                            if !matches!(ok, Formula::Bool(true)) {
                                // A check of the callee fails exactly where `ok`
                                // is false. Its `Unreachable` arms are undefined
                                // behaviour, not failed checks: they leave `ok`
                                // true and only drop executions through `reach`,
                                // as the caller's own `Unreachable` does.
                                self.checks.push((
                                    format!("a check of the inlined callee at {}", site_name(key)),
                                    and2(&here, Formula::Not(b(ok))),
                                ));
                            }
                            if !matches!(reach, Formula::Bool(true)) {
                                here = and2(&here, reach.clone());
                                guards.push(reach);
                            }
                            env.scalars.insert(*r, v);
                        }
                        None => return Err(format!("{} has no decision", site_name(key))),
                    }
                }
                Inst::ExtractField { ty, aggregate, field }
                    if env.closures.contains_key(aggregate) =>
                {
                    let value = env.closures[aggregate].project(ty, *field)?;
                    let [result] = node.results.as_slice() else {
                        return Err("ExtractField closure must bind one result".into());
                    };
                    env.scalars.insert(*result, value);
                    if *ty == IrTy::Ptr {
                        env.memory.project(*aggregate, *field, *result);
                    }
                }
                Inst::ExtractField { ty, aggregate, field }
                    if env.pairs.contains_key(aggregate) =>
                {
                    let (v0, v1) = env.pairs[aggregate].clone();
                    let v = match field {
                        0 => v0,
                        1 => v1,
                        other => return Err(format!("field {other} of a two-field aggregate")),
                    };
                    if scalar_reg_width(ty)? != v.width {
                        return Err("ExtractField width differs from the field's".into());
                    }
                    let [r] = node.results.as_slice() else {
                        return Err("ExtractField must bind one result".into());
                    };
                    env.scalars.insert(*r, v);
                    if *ty == IrTy::Ptr {
                        env.memory.project(*aggregate, *field, *r);
                    }
                }
                Inst::MakeAggregate { ty: IrTy::Tuple(tys), variant: None, fields }
                    if fields.len() == 2 && tys.len() == 2 =>
                {
                    let v0 = lookup(&env.scalars, fields[0])?;
                    let v1 = lookup(&env.scalars, fields[1])?;
                    if scalar_reg_width(&tys[0])? != v0.width
                        || scalar_reg_width(&tys[1])? != v1.width
                    {
                        return Err("MakeAggregate field widths differ from the tuple's".into());
                    }
                    let [r] = node.results.as_slice() else {
                        return Err("MakeAggregate must bind one result".into());
                    };
                    env.pairs.insert(*r, (v0, v1));
                }
                // Trust: register aggregates as integer lanes (DECISION_QUEUE AGG-SSA-1).
                inst if aggregate_values::claims(self.module, inst, &env.aggs) => {
                    self.aggregate_step(&mut env, inst, &node.results)?;
                }
                other => {
                    let v = eval_ir_inst(self.module, &env.scalars, other, &mut self.side)?;
                    let [r] = node.results.as_slice() else {
                        return Err("instruction binds a result count outside the fragment".into());
                    };
                    env.scalars.insert(*r, v);
                    if let Inst::Copy { ty: IrTy::Ptr, operand } = other {
                        self.declared_type(*operand, &IrTy::Ptr)?;
                        env.memory.copy_pointer(*operand, *r);
                    }
                }
            }
        }
        let (value, reach) = self.terminator(term, &env, here, &visited, depth)?;
        let mut all = guards;
        let reach = if all.is_empty() {
            reach
        } else {
            if !matches!(reach, Formula::Bool(true)) {
                all.push(reach);
            }
            match <[Formula; 1]>::try_from(all) {
                Ok([one]) => one,
                Err(all) => Formula::And(all),
            }
        };
        Ok((value, reach))
    }

    fn edge(
        &mut self,
        target: BlockId,
        args: &[ValueId],
        env: &SpecEnv,
        path: Formula,
        visited: &[u32],
        depth: u32,
    ) -> Result<(Formula, Formula), String> {
        if args.iter().any(|a| env.pairs.contains_key(a) || env.closures.contains_key(a)) {
            return Err(
                "an aggregate or closure passed along a block edge is outside the fragment".into(),
            );
        }
        // Trust: aggregates bind only to parameters of their exact type (AGG-SSA-1).
        let (next, aggs) = aggregate_values::bind_edge(self, target, args, env)?;
        self.block(
            target,
            SpecEnv {
                scalars: next,
                aggs,
                pairs: env.pairs.clone(),
                closures: env.closures.clone(),
                memory: env.memory.edge(&self.blocks[&target.index()].params, args),
            },
            path,
            visited.to_vec(),
            depth + 1,
        )
    }

    fn terminator(
        &mut self,
        node: &trust_ir::node::InstrNode,
        env: &SpecEnv,
        here: Formula,
        visited: &[u32],
        depth: u32,
    ) -> Result<(Formula, Formula), String> {
        match &node.inst {
            Inst::Return { values } => {
                self.memory.exits.push(source_memory::Exit {
                    path: here.clone(),
                    bytes: env.memory.bytes.clone(),
                });
                match values.as_slice() {
                    [] => Ok((Formula::BitVec { value: 0, width: 1 }, Formula::Bool(true))),
                    [v] => {
                        let v = lookup(&env.scalars, *v)?;
                        if v.width != self.out_width {
                            return Err(format!(
                                "returned {}-bit value for a {}-bit result",
                                v.width, self.out_width
                            ));
                        }
                        Ok((v.f, Formula::Bool(true)))
                    }
                    _ => Err("a multi-value return is outside the fragment".into()),
                }
            }
            Inst::Unreachable => {
                Ok((Formula::BitVec { value: 0, width: self.out_width }, Formula::Bool(false)))
            }
            Inst::Br { target, args } => self.edge(*target, args, env, here, visited, depth),
            Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                let taken = nonzero(&lookup(&env.scalars, *cond)?);
                let t = self.edge(
                    *then_target,
                    then_args,
                    env,
                    and2(&here, taken.clone()),
                    visited,
                    depth,
                )?;
                let e = self.edge(
                    *else_target,
                    else_args,
                    env,
                    and2(&here, Formula::Not(b(taken.clone()))),
                    visited,
                    depth,
                )?;
                Ok((ite_unless_same(&taken, t.0, e.0), merge_reach(taken, t.1, e.1)))
            }
            Inst::Switch { value, default, default_args, cases, .. } => {
                let sel = lookup(&env.scalars, *value)?;
                // Trust: a literal selector takes exactly one edge, the first case equal to it
                // modulo 2^width or else the default (AGG-SSA-1).
                if let Some((t, a)) =
                    aggregate_values::literal_switch_target(&sel, cases, *default, default_args)?
                {
                    return self.edge(t, a, env, here, visited, depth);
                }
                let mut is: Vec<Formula> = Vec::new();
                for case in cases {
                    let v = match &case.value {
                        Constant::Int(v) => *v,
                        Constant::Bool(v) => i128::from(*v),
                        other => {
                            return Err(format!(
                                "switch case constant {other:?} is outside the fragment"
                            ));
                        }
                    };
                    is.push(Formula::Eq(
                        b(sel.f.clone()),
                        b(Formula::BitVec { value: v, width: sel.width }),
                    ));
                }
                let none =
                    is.iter().fold(here.clone(), |acc, c| and2(&acc, Formula::Not(b(c.clone()))));
                let mut acc = self.edge(*default, default_args, env, none, visited, depth)?;
                for (k, case) in cases.iter().enumerate().rev() {
                    let mut p = here.clone();
                    for c in &is[..k] {
                        p = and2(&p, Formula::Not(b(c.clone())));
                    }
                    p = and2(&p, is[k].clone());
                    let arm = self.edge(case.target, &case.args, env, p, visited, depth)?;
                    acc = (
                        ite_unless_same(&is[k], arm.0, acc.0),
                        merge_reach(is[k].clone(), arm.1, acc.1),
                    );
                }
                Ok(acc)
            }
            _ => Err("terminator outside the fragment".into()),
        }
    }
}

// ===========================================================================
// THE MACHINE SIDE (the shipped bytes, with events)
// ===========================================================================

struct CerExec<'a> {
    sem: Aarch64Semantics,
    window: &'a FunctionWindow,
    callee_places: &'a BTreeMap<u64, FnPlacement>,
    own_ret: &'a ReturnPlace,
    trap: BTreeSet<u64>,
    steps: u32,
    x18_reserved: bool,
    events: BTreeMap<u64, Vec<EventInstance>>,
    o5_refuted: Vec<String>,
    o5_unknown: Vec<String>,
    /// Constructor laws for qualified physical call-result carriers; checked
    /// with the same function proof, never used as unproved solver premises.
    abi_model_equations: Vec<(Formula, Formula)>,
    memory_observer: Option<crate::cer_memory_machine::ObservationSession<'a>>,
    observation_incomplete: Vec<String>,
    leaf_trace: Option<leaf_memory::Trace>,
    tail_instance_trace: Option<leaf_call_instance::PrefixTrace>,
    leaf_refusal: Option<String>,
    /// PKG-C5c S2a: the `adrp` of every admitted dead-tail Location pair,
    /// which [`Self::trap_tail_writes_x18`] reads by its raw `Rd` instead of
    /// decoding (CER has no runtime placement for object-relative address
    /// data, so [`Self::decode`] refuses every `adrp`).
    dead_tail_adrp: BTreeSet<u64>,
}

const MAX_MACHINE_STEPS: u32 = 4096;
const MAX_MACHINE_DEPTH: u32 = 16;

impl<'a> CerExec<'a> {
    fn new(
        window: &'a FunctionWindow,
        callee_places: &'a BTreeMap<u64, FnPlacement>,
        own_ret: &'a ReturnPlace,
        x18_reserved: bool,
    ) -> Self {
        // The trap tails: straight-line runs into a `brk`/`udf`, from the
        // structural walk (the same set `compiled_object` marks sites with).
        let mut trap = BTreeSet::new();
        for off in &window.reachable {
            let w = word(window, *off);
            if matches!(
                crate::compiled_object::classify_insn(w),
                crate::compiled_object::InsnClass::Trap
            ) {
                let mut cur = *off;
                trap.insert(cur);
                while cur > window.start {
                    let prev = cur - 4;
                    let falls = window.successors.get(&prev).is_some_and(|s| s.as_slice() == [cur]);
                    let class = crate::compiled_object::classify_insn(word(window, prev));
                    let straight = matches!(
                        class,
                        crate::compiled_object::InsnClass::Plain
                            | crate::compiled_object::InsnClass::BranchLink { .. }
                            | crate::compiled_object::InsnClass::Adrp
                            | crate::compiled_object::InsnClass::AddImm64
                            | crate::compiled_object::InsnClass::LoadStoreUImm
                    );
                    if !(falls && straight && window.reachable.contains(&prev)) {
                        break;
                    }
                    trap.insert(prev);
                    cur = prev;
                }
            }
        }
        CerExec {
            sem: Aarch64Semantics,
            window,
            callee_places,
            own_ret,
            trap,
            steps: 0,
            x18_reserved,
            events: BTreeMap::new(),
            o5_refuted: Vec::new(),
            o5_unknown: Vec::new(),
            abi_model_equations: Vec::new(),
            memory_observer: None,
            observation_incomplete: Vec::new(),
            leaf_trace: None,
            tail_instance_trace: None,
            leaf_refusal: None,
            dead_tail_adrp: BTreeSet::new(),
        }
    }

    fn take_memory_diagnostics(
        &mut self,
    ) -> (
        crate::cer_memory_machine::ObservationDiagnostics,
        Option<crate::cer_memory_machine::PendingMachineMemory>,
    ) {
        let issues = std::mem::take(&mut self.observation_incomplete);
        match self.memory_observer.take() {
            Some(observer) => {
                let pending = observer.into_pending();
                (pending.diagnostics(issues), Some(pending))
            }
            None => (crate::cer_memory_machine::ObservationDiagnostics::unavailable(issues), None),
        }
    }

    // Observer failures invalidate observations, never alter the existing CER
    // verdict. Memory-bearing source still encounters its mandatory Unknown
    // guard before any proof grade; no observation is completeness authority.
    fn observe<T>(&mut self, result: Result<T, String>) -> Option<T> {
        match result {
            Ok(value) => Some(value),
            Err(reason) => {
                self.observation_incomplete.push(format!("observer: {reason}"));
                None
            }
        }
    }

    fn leaf_result(&mut self, result: Result<(), String>) {
        if let Err(reason) = result {
            self.leaf_refusal.get_or_insert(reason.clone());
            if let Some(trace) = self.leaf_trace.as_mut() {
                trace.reject(reason);
            }
        }
    }

    fn decode(&self, pc: u64) -> Result<trust_disasm::Instruction, String> {
        if !self.window.contains(pc) || !self.window.contains(pc + 3) {
            return Err(format!("execution left the extent at {pc:#x} (fail-closed)"));
        }
        let i = (pc - self.window.start) as usize;
        let instruction = decode_aarch64(&self.window.code[i..i + 4], pc)
            .map_err(|e| format!("decode_aarch64 failed at {pc:#x}: {e:?}"))?;
        // Both ordinary execution and trap-tail inspection pass here before
        // asking for effects. Object coordinates are not loaded addresses.
        if crate::pc_object_model::requires_runtime_placement(&instruction) {
            return Err(format!(
                "runtime placement witness is absent for object-relative address data at {pc:#x}: {:?}",
                instruction.opcode
            ));
        }
        Ok(instruction)
    }

    fn read_return(&self, state: &MachineState) -> Result<Formula, String> {
        match self.own_ret {
            ReturnPlace::Void => Ok(Formula::BitVec { value: 0, width: 1 }),
            ReturnPlace::Scalar(s) => match (s.slot, s.width) {
                (Slot::Gpr(0), w) if w <= 64 => {
                    Ok(state.read_gpr(0, abi_extensions::physical_width(s)))
                }
                (Slot::GprPair { lo: 0, hi: 1 }, 128) => {
                    Ok(Formula::BvConcat(b(state.read_gpr(1, 64)), b(state.read_gpr(0, 64))))
                }
                (slot, w) => {
                    Err(format!("result slot {slot:?} at {w} bits is outside the fragment"))
                }
            },
            ReturnPlace::Indirect => Err("sret result".into()),
        }
    }

    fn read_args(&self, state: &MachineState, place: &FnPlacement) -> Result<Vec<Formula>, String> {
        let read = |s: &ScalarPlace| -> Result<Formula, String> {
            match (s.slot, s.width) {
                (Slot::Gpr(r), w) if w <= 64 => {
                    Ok(state.read_gpr(r, abi_extensions::physical_width(s)))
                }
                (Slot::GprPair { lo, hi }, 128) => {
                    Ok(Formula::BvConcat(b(state.read_gpr(hi, 64)), b(state.read_gpr(lo, 64))))
                }
                (slot, w) => Err(format!(
                    "argument slot {slot:?} at {w} bits is Unknown (stack/indirect arguments: step 5.10)"
                )),
            }
        };
        let mut out = Vec::new();
        for pp in &place.params {
            match pp {
                ParamPlace::Ignore => {}
                ParamPlace::Scalar(s) => out.push(read(s)?),
                ParamPlace::Pair(a, c) => {
                    out.push(read(a)?);
                    out.push(read(c)?);
                }
            }
        }
        Ok(out)
    }

    /// O5 over one instruction's memory effects, before they are applied.
    fn check_memory(&mut self, pc: u64, state: &MachineState, effects: &[Effect]) {
        let Some(sp_now) = sp_offset(&state.sp).map(|o| o as i64) else {
            self.o5_unknown.push(format!("SP at {pc:#x} is not the entry SP plus a constant"));
            return;
        };
        let mut bound = sp_now;
        for e in effects {
            if let Effect::SpWrite { value } = e {
                match sp_offset(value) {
                    Some(o) => bound = bound.min(o as i64),
                    None => self
                        .o5_unknown
                        .push(format!("SP written at {pc:#x} is not the entry SP plus a constant")),
                }
            }
        }
        for e in effects {
            let (address, width, store) = match e {
                Effect::MemWrite { address, width_bytes, .. } => (address, *width_bytes, true),
                Effect::MemRead { address, width_bytes } => (address, *width_bytes, false),
                _ => continue,
            };
            match sp_offset(address).map(|o| o as i64) {
                Some(c) if c + i64::from(width) > 0 && store => self.o5_refuted.push(format!(
                    "the store at {pc:#x} writes SP_entry{c:+} ({width} bytes): the caller's frame, which \
                     the IR never writes"
                )),
                Some(c) if c + i64::from(width) > 0 => self.o5_unknown.push(format!(
                    "the load at {pc:#x} reads SP_entry{c:+}: the caller's frame or incoming stack \
                     arguments (Unknown: the callee owns that area; step 5.10)"
                )),
                Some(c) if c < bound => self.o5_unknown.push(format!(
                    "the {} at {pc:#x} touches SP_entry{c:+}, below the stack pointer",
                    if store { "store" } else { "load" }
                )),
                Some(_) => {}
                None => self.o5_unknown.push(format!(
                    "the {} at {pc:#x} addresses memory outside the function's frame",
                    if store { "store" } else { "load" }
                )),
            }
        }
    }

    /// The machine rely at a call (design §5 O3), and the shared result.
    fn rely(
        &mut self,
        pc: u64,
        state: &mut MachineState,
        place: &FnPlacement,
    ) -> Result<(), String> {
        let tag = format!("{pc:x}");
        let sp_now = sp_offset(&state.sp)
            .map(|o| o as i64)
            .ok_or_else(|| format!("SP at the call {pc:#x} is not frame-relative"))?;
        // Memory: the caller frame [SP_at_call, SP_entry) survives; every other
        // byte is fresh.
        let mut stores = Vec::new();
        let mut cur = state.memory.clone();
        loop {
            match cur {
                Formula::Store(m, a, v) => {
                    stores.push((*a, *v));
                    cur = *m;
                }
                Formula::Var(..) => break,
                other => {
                    return Err(format!("unexpected memory term at the call {pc:#x}: {other:?}"));
                }
            }
        }
        stores.reverse();
        let mut mem = source_memory::paired_post_memory(pc);
        for (a, v) in stores {
            if let Some(c) = sp_offset(&a).map(|o| o as i64)
                && c >= sp_now
                && c < 0
            {
                mem = Formula::Store(b(mem), b(a), b(v));
            }
        }
        state.memory = mem;
        let fresh64 = |n: &str| Formula::Var(format!("CER_CLOBBER@{tag}_{n}"), Sort::BitVec(64));
        for i in 0..=17usize {
            state.gpr[i] = fresh64(&format!("X{i}"));
        }
        if !self.x18_reserved {
            state.gpr[18] = fresh64("X18");
        }
        state.gpr[30] = fresh64("X30");
        state.flags = Flags {
            n: Formula::Var(format!("CER_CLOBBER@{tag}_N"), Sort::Bool),
            z: Formula::Var(format!("CER_CLOBBER@{tag}_Z"), Sort::Bool),
            c: Formula::Var(format!("CER_CLOBBER@{tag}_C"), Sort::Bool),
            v: Formula::Var(format!("CER_CLOBBER@{tag}_V"), Sort::Bool),
        };
        for i in 0..32usize {
            let fresh = |bits: u32| {
                Formula::Var(format!("CER_CLOBBER@{tag}_V{i}_{bits}"), Sort::BitVec(bits))
            };
            state.fpr[i] = if (8..=15).contains(&i) {
                Formula::BvConcat(
                    b(fresh(64)),
                    b(Formula::BvExtract { inner: b(state.fpr[i].clone()), high: 63, low: 0 }),
                )
            } else {
                fresh(128)
            };
        }
        match &place.ret {
            ReturnPlace::Void => {}
            ReturnPlace::Scalar(s) => {
                let r = Formula::Var(format!("CER_R@{tag}"), Sort::BitVec(s.width));
                match (s.slot, s.width) {
                    (Slot::Gpr(0), 64) => state.gpr[0] = r,
                    (Slot::Gpr(0), width @ (8 | 16)) if s.ext == AbiExt::Zext => {
                        let high = Formula::Var(format!("CER_RHI@{tag}"), Sort::BitVec(64));
                        let post =
                            abi_extensions::post_call_unsigned(r.clone(), high.clone(), width)?;
                        self.abi_model_equations.extend([
                            (
                                Formula::BvExtract { inner: b(post.clone()), high: 31, low: 0 },
                                Formula::BvZeroExt(b(r), 32 - width),
                            ),
                            (
                                Formula::BvExtract { inner: b(post.clone()), high: 63, low: 32 },
                                Formula::BvExtract { inner: b(high), high: 63, low: 32 },
                            ),
                        ]);
                        state.gpr[0] = post;
                    }
                    (Slot::Gpr(0), width @ (8 | 16)) if s.ext == AbiExt::Sext => {
                        let high = Formula::Var(format!("CER_RHI@{tag}"), Sort::BitVec(64));
                        let post =
                            abi_extensions::post_call_signed(r.clone(), high.clone(), width)?;
                        self.abi_model_equations.extend([
                            (
                                Formula::BvExtract { inner: b(post.clone()), high: 31, low: 0 },
                                Formula::BvSignExt(b(r), 32 - width),
                            ),
                            (
                                Formula::BvExtract { inner: b(post.clone()), high: 63, low: 32 },
                                Formula::BvExtract { inner: b(high), high: 63, low: 32 },
                            ),
                        ]);
                        state.gpr[0] = post;
                    }
                    (Slot::Gpr(0), width @ (8 | 16)) if s.ext == AbiExt::None => {
                        let high = Formula::Var(format!("CER_RHI@{tag}"), Sort::BitVec(64));
                        let post = abi_extensions::post_call_unextended_small(
                            r.clone(),
                            high.clone(),
                            width,
                        )?;
                        self.abi_model_equations.extend([
                            (
                                Formula::BvExtract {
                                    inner: b(post.clone()),
                                    high: width - 1,
                                    low: 0,
                                },
                                r,
                            ),
                            (
                                Formula::BvExtract { inner: b(post.clone()), high: 63, low: width },
                                Formula::BvExtract { inner: b(high), high: 63, low: width },
                            ),
                        ]);
                        state.gpr[0] = post;
                    }
                    (Slot::Gpr(0), w) if w < 64 => {
                        state.gpr[0] = Formula::BvConcat(
                            b(Formula::Var(format!("CER_RHI@{tag}"), Sort::BitVec(64 - w))),
                            b(r),
                        );
                    }
                    (Slot::GprPair { lo: 0, hi: 1 }, 128) => {
                        state.gpr[0] = Formula::BvExtract { inner: b(r.clone()), high: 63, low: 0 };
                        state.gpr[1] = Formula::BvExtract { inner: b(r), high: 127, low: 64 };
                    }
                    (slot, w) => {
                        return Err(format!(
                            "callee result slot {slot:?} at {w} bits is outside the fragment"
                        ));
                    }
                }
            }
            ReturnPlace::Indirect => return Err("sret callee".into()),
        }
        Ok(())
    }

    fn event(
        &mut self,
        pc: u64,
        state: &MachineState,
        path: &Formula,
    ) -> Result<FnPlacement, String> {
        let place = self
            .callee_places
            .get(&pc)
            .cloned()
            .ok_or_else(|| format!("machine call at {pc:#x} has no paired placement"))?;
        let args = self.read_args(state, &place)?;
        for (i, a) in args.iter().enumerate() {
            if mentions_sp(a) {
                self.o5_unknown.push(format!(
                    "argument {i} of the call at {pc:#x} holds an SP-derived value: the frame escapes \
                     (Unknown)"
                ));
            }
        }
        self.events.entry(pc).or_default().push(EventInstance { path: path.clone(), args });
        Ok(place)
    }

    fn trap_tail_writes_x18(&self, start: u64, state: &MachineState) -> Result<bool, String> {
        let mut pc = start;
        loop {
            if matches!(
                crate::compiled_object::classify_insn(word(self.window, pc)),
                crate::compiled_object::InsnClass::Trap
            ) {
                return Ok(false);
            }
            if self.dead_tail_adrp.contains(&pc) {
                // An admitted Location `adrp` (PKG-C5c S2a) writes exactly its Rd.
                if word(self.window, pc) & 0x1f == 18 {
                    return Ok(true);
                }
            } else {
                let insn = self.decode(pc)?;
                let effects = self
                    .sem
                    .effects(state, &insn)
                    .map_err(|e| format!("effects failed in the trap tail at {pc:#x}: {e:?}"))?;
                if effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 18, .. })) {
                    return Ok(true);
                }
            }
            if !self.trap.contains(&(pc + 4)) {
                return Ok(false);
            }
            pc += 4;
        }
    }

    #[allow(clippy::too_many_lines)]
    fn run(
        &mut self,
        mut pc: u64,
        mut state: MachineState,
        mut visited: Vec<u64>,
        depth: u32,
        mut x18_written: bool,
        path: Formula,
    ) -> Result<PathOutcome, String> {
        if depth > MAX_MACHINE_DEPTH {
            return Err("fork-depth budget exceeded (fail-closed)".into());
        }
        loop {
            if self.trap.contains(&pc) {
                self.leaf_result(Err("leaf traversal skipped a trap prefix".into()));
                self.observation_incomplete.push(format!(
                    "skipped trap tail at {pc:#x}: instruction/memory census incomplete"
                ));
                let tail = self.trap_tail_writes_x18(pc, &state)?;
                return Ok(PathOutcome {
                    value: Formula::BitVec { value: 0, width: own_width(self.own_ret) },
                    reach: Formula::Bool(false),
                    abi: AbiExit::entry(),
                    x18_written: Formula::Bool(x18_written || tail),
                    arrivals: Vec::new(),
                });
            }
            if visited.contains(&pc) {
                return Err(format!("loop/backedge at {pc:#x} (fail-closed)"));
            }
            visited.push(pc);
            self.steps += 1;
            if self.steps > MAX_MACHINE_STEPS {
                return Err("instruction-step budget exceeded (fail-closed)".into());
            }
            let insn = self.decode(pc)?;
            let opcode = insn.opcode;
            let effects = self
                .sem
                .effects(&state, &insn)
                .map_err(|e| format!("Aarch64Semantics::effects failed at {pc:#x}: {e:?}"))?;
            if let Some(trace) = self.tail_instance_trace.as_mut() {
                trace.before(pc, &path, &state, &effects)?;
            }
            if let Some(trace) = self.leaf_trace.as_mut() {
                let result = trace.before(pc, &path, &state, &effects);
                self.leaf_result(result);
            }
            let observed = match self.memory_observer.as_mut() {
                Some(observer) => {
                    let result = observer.before_step(pc, &path, &state, &effects);
                    self.observe(result)
                }
                None => None,
            };
            if effects.iter().any(|e| matches!(e, Effect::RegWrite { index: 18, .. })) {
                x18_written = true;
            }
            self.check_memory(pc, &state, &effects);

            if opcode == Opcode::Ret {
                let value = self.read_return(&state)?;
                let target = effects
                    .iter()
                    .find_map(|e| match e {
                        Effect::Return { target } => Some(target.clone()),
                        _ => None,
                    })
                    .ok_or_else(|| format!("RET at {pc:#x} produced no Return effect"))?;
                if let (Some(observer), Some(handle)) =
                    (self.memory_observer.as_mut(), observed.as_ref())
                {
                    let result = observer.at_return(handle, &state);
                    let _ = self.observe(result);
                }
                if let Some(trace) = self.leaf_trace.as_mut() {
                    let result = trace.after(&state);
                    self.leaf_result(result);
                }
                return Ok(PathOutcome {
                    value,
                    reach: Formula::Bool(true),
                    abi: AbiExit::at(&state, target),
                    x18_written: Formula::Bool(x18_written),
                    arrivals: Vec::new(),
                });
            }

            let mut cond_branch = None;
            let mut uncond_target: Option<Formula> = None;
            let mut pc_update: Option<Formula> = None;
            let mut is_call = false;
            let pc_advance = Formula::BvAdd(
                Box::new(state.pc.clone()),
                Box::new(Formula::BitVec { value: 4, width: 64 }),
                64,
            );
            let mut plain: Vec<&Effect> = Vec::new();
            for e in &effects {
                match e {
                    Effect::ConditionalBranch { condition, target, .. } => {
                        cond_branch = Some((*condition, target.clone()))
                    }
                    Effect::Branch { target } => uncond_target = Some(target.clone()),
                    Effect::PcUpdate { value } if *value == pc_advance => {}
                    Effect::PcUpdate { value } => pc_update = Some(value.clone()),
                    Effect::Return { .. } => {}
                    Effect::Call { .. } => is_call = true,
                    Effect::Aarch64SyncBoundary { .. } | Effect::Aarch64AtomicAccess { .. } => {
                        return Err(format!("unsupported atomic/sync at {pc:#x} (fail-closed)"));
                    }
                    other => plain.push(other),
                }
            }

            if is_call {
                match self.window.site_at(pc) {
                    Some(site) if site.kind == MachineSiteKind::Call && site.callee.is_some() => {}
                    _ => {
                        return Err(format!(
                            "call at {pc:#x} is not a named structural call site (fail-closed)"
                        ));
                    }
                }
                let place = self.event(pc, &state, &path)?;
                self.rely(pc, &mut state, &place)?;
                if let (Some(observer), Some(handle)) =
                    (self.memory_observer.as_mut(), observed.as_ref())
                {
                    let result = observer.after_call(handle, &state);
                    let _ = self.observe(result);
                }
                pc += 4;
                continue;
            }

            for e in &plain {
                state.apply_effect(e).map_err(|er| {
                    format!("apply_effects rejected {opcode:?} at {pc:#x}: {er:?}")
                })?;
            }
            if let Some(trace) = self.tail_instance_trace.as_mut() {
                trace.after(&state)?;
            }
            if let Some(trace) = self.leaf_trace.as_mut() {
                let result = trace.after(&state);
                self.leaf_result(result);
            }
            if let (Some(observer), Some(handle)) =
                (self.memory_observer.as_mut(), observed.as_ref())
            {
                let result = observer.after_step(handle, &state);
                let _ = self.observe(result);
            }

            let fork = if let Some((condition, target)) = cond_branch {
                let c = condition_to_formula(&state, condition).map_err(|e| e.to_string())?;
                let t = const_addr(&target)
                    .ok_or_else(|| format!("indirect conditional branch at {pc:#x}"))?;
                Some((c, t))
            } else if uncond_target.is_some() {
                None
            } else if let Some(value) = pc_update.clone() {
                match value {
                    Formula::Ite(c, taken, _) => {
                        let t = const_addr(&taken)
                            .ok_or_else(|| format!("indirect conditional branch at {pc:#x}"))?;
                        Some((*c, t))
                    }
                    other => {
                        let t = const_addr(&other)
                            .ok_or_else(|| format!("unmodeled pc-update at {pc:#x}"))?;
                        if visited.contains(&t) {
                            return Err(format!("backedge at pc-update {pc:#x}"));
                        }
                        pc = t;
                        continue;
                    }
                }
            } else {
                None
            };

            if let Some((c, target_pc)) = fork {
                let fall_pc = pc + 4;
                if visited.contains(&target_pc) || visited.contains(&fall_pc) {
                    return Err(format!(
                        "loop/backedge at conditional branch {pc:#x} (fail-closed)"
                    ));
                }
                let taken = self.run(
                    target_pc,
                    state.clone(),
                    visited.clone(),
                    depth + 1,
                    x18_written,
                    and2(&path, c.clone()),
                )?;
                let fall = self.run(
                    fall_pc,
                    state.clone(),
                    visited.clone(),
                    depth + 1,
                    x18_written,
                    and2(&path, Formula::Not(b(c.clone()))),
                )?;
                let reach = match (&taken.reach, &fall.reach) {
                    (Formula::Bool(true), Formula::Bool(true)) => Formula::Bool(true),
                    _ => Formula::Ite(b(c.clone()), b(taken.reach), b(fall.reach)),
                };
                return Ok(PathOutcome {
                    value: ite_unless_same(&c, taken.value, fall.value),
                    reach,
                    abi: AbiExit::merge(&c, taken.abi, fall.abi),
                    x18_written: ite_unless_same(&c, taken.x18_written, fall.x18_written),
                    arrivals: Vec::new(),
                });
            }

            if let Some(target) = uncond_target {
                if let Some(site) = self.window.site_at(pc) {
                    if site.kind != MachineSiteKind::Tail || site.callee.is_none() {
                        return Err(format!(
                            "branch at {pc:#x} is an unnamed call site (fail-closed)"
                        ));
                    }
                    // TAIL CALL = call-then-return (3dc08e8b1b): the callee returns
                    // through X30 straight to OUR caller and hands back the
                    // callee-saved state it was given — so O0 reads THIS state.
                    let abi = AbiExit::at(&state, state.read_gpr(30, 64));
                    let place = self.event(pc, &state, &path)?;
                    abi_extensions::check_tail_transport(self.own_ret, &place.ret)?;
                    self.rely(pc, &mut state, &place)?;
                    if let (Some(observer), Some(handle)) =
                        (self.memory_observer.as_mut(), observed.as_ref())
                    {
                        let result = observer.after_tail_call(handle, &state);
                        let _ = self.observe(result);
                    }
                    let value = self.read_return(&state)?;
                    return Ok(PathOutcome {
                        value,
                        reach: Formula::Bool(true),
                        abi,
                        x18_written: Formula::Bool(x18_written),
                        arrivals: Vec::new(),
                    });
                }
                let t = const_addr(&target)
                    .ok_or_else(|| format!("indirect branch at {pc:#x} (fail-closed)"))?;
                if visited.contains(&t) {
                    return Err(format!("backedge at unconditional branch {pc:#x} (fail-closed)"));
                }
                pc = t;
                continue;
            }
            pc += 4;
        }
    }
}

fn own_width(ret: &ReturnPlace) -> u32 {
    match ret {
        ReturnPlace::Scalar(s) => abi_extensions::physical_width(s),
        _ => 1,
    }
}

fn word(window: &FunctionWindow, off: u64) -> u32 {
    let i = (off - window.start) as usize;
    u32::from_le_bytes([window.code[i], window.code[i + 1], window.code[i + 2], window.code[i + 3]])
}

fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

fn mentions_sp(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |n| {
        if matches!(n, Formula::Var(name, _) if name == "SP") {
            found = true;
        }
    });
    found
}

// ===========================================================================
// O3 + O4 UNDER ONE PAIRING
// ===========================================================================

enum PairOutcome {
    Proven { o3: String, o4: String, evidence: Option<ProvenEvidence> },
    Refuted { which: String, detail: String },
    Unknown { which: String, detail: String },
}

fn substitute(f: &Formula, map: &HashMap<String, Formula>) -> Formula {
    if map.is_empty() {
        return f.clone();
    }
    f.clone().map(&mut |n| {
        if let Formula::Var(name, _) = &n
            && let Some(replacement) = map.get(name)
        {
            return replacement.clone();
        }
        n
    })
}

/// `reach` as a disjunction of instance paths, and each argument slot as the
/// `Ite` cascade over them (the last instance is the default arm).
fn merge_instances(inst: &[EventInstance], widths: &[u32]) -> (Formula, Vec<Formula>) {
    match inst {
        [] => (
            Formula::Bool(false),
            widths.iter().map(|w| Formula::BitVec { value: 0, width: *w }).collect(),
        ),
        [one] => (one.path.clone(), one.args.clone()),
        [init @ .., last] => {
            let reach = Formula::Or(inst.iter().map(|i| i.path.clone()).collect());
            let mut args = last.args.clone();
            for i in init.iter().rev() {
                args = args
                    .into_iter()
                    .zip(&i.args)
                    .map(|(acc, a)| ite_unless_same(&i.path, a.clone(), acc))
                    .collect();
            }
            (reach, args)
        }
    }
}

/// `x` where `r` holds and 0 elsewhere: the ITE-merged (unconditional) form of
/// "`x` under `r`".
fn guard(r: &Formula, x: Formula, width: u32) -> Formula {
    match r {
        Formula::Bool(true) => x,
        _ => Formula::Ite(b(r.clone()), b(x), b(Formula::BitVec { value: 0, width })),
    }
}

#[allow(clippy::too_many_arguments)]
fn discharge_under(
    symbol: &str,
    spec: &SpecResult,
    exec: &CerExec<'_>,
    outcome: &PathOutcome,
    pi: &BTreeMap<SiteKey, u64>,
    decisions: &BTreeMap<SiteKey, SiteDecision>,
    residue: &[AbiConjunct],
    abi: &AbiDischarge,
    entry_abi: &abi_extensions::Plan,
) -> PairOutcome {
    // Bind each IR site's result variable to its paired machine site's.
    let mut map: HashMap<String, Formula> = HashMap::new();
    for (key, (name, w)) in &spec.result_vars {
        let Some(off) = pi.get(key) else {
            return PairOutcome::Unknown {
                which: "O3".into(),
                detail: format!("{} is unpaired", site_name(*key)),
            };
        };
        map.insert(name.clone(), Formula::Var(format!("CER_R@{off:x}"), Sort::BitVec(*w)));
    }
    match spec.memory.paired_variables(pi) {
        Ok(memory_vars) => map.extend(memory_vars),
        Err(detail) => return PairOutcome::Unknown { which: "O3".into(), detail },
    }
    let spec_value = substitute(&spec.value, &map);
    let spec_reach = substitute(&spec.reach, &map);
    let side: Vec<Formula> = spec.side.iter().map(|f| substitute(f, &map)).collect();

    // Domain/model laws are obligations about the renderer, not assumptions
    // about the bytes. A failed one makes the model Unknown, never Refuted.
    let mut model_equations = entry_abi.entry_equations();
    model_equations.extend(exec.abi_model_equations.clone());
    for (index, (left, right)) in model_equations.iter().enumerate() {
        if !matches!(discharge_equal_pre(left, right, None), Discharge::Proven) {
            return PairOutcome::Unknown {
                which: "O4".into(),
                detail: format!("physical ABI model equation {index} did not close"),
            };
        }
    }

    // (1) VACUITY FIREWALL — unchanged rule.
    if !matches!(spec_reach, Formula::Bool(true)) {
        match discharge_valid(&Formula::Not(b(spec_reach.clone()))) {
            Discharge::Proven => {
                return PairOutcome::Unknown {
                    which: "O4".into(),
                    detail: format!(
                        "VACUOUS obligation for `{symbol}`: the IR's own assert guards are unsatisfiable"
                    ),
                };
            }
            Discharge::CounterExample => {}
            Discharge::Unknown(r) => {
                return PairOutcome::Unknown {
                    which: "O4".into(),
                    detail: format!("vacuity check: {r}"),
                };
            }
        }
    }
    // (2) spec-side modeling preconditions, implied by spec_reach.
    for (i, c) in side.iter().enumerate() {
        match discharge_valid(&Formula::Or(vec![Formula::Not(b(spec_reach.clone())), c.clone()])) {
            Discharge::Proven => {}
            Discharge::CounterExample => {
                return PairOutcome::Unknown {
                    which: "O4".into(),
                    detail: format!("modeling precondition #{i} is not implied by the IR's guards"),
                };
            }
            Discharge::Unknown(r) => {
                return PairOutcome::Unknown {
                    which: "O4".into(),
                    detail: format!("modeling precondition #{i}: {r}"),
                };
            }
        }
    }

    // (3) The conjunction items: (name, which, lhs = machine, rhs = spec).
    let mut items: Vec<(String, &'static str, Formula, Formula)> = Vec::new();
    let mut o3_count = 0usize;
    for (key, off) in pi {
        let Some(SiteDecision::Called { symbol: callee, place, .. }) = decisions.get(key) else {
            continue;
        };
        // The observable width of each argument slot, read off P(callee).
        let widths: Vec<u32> = place
            .params
            .iter()
            .flat_map(|pp| match pp {
                ParamPlace::Ignore => vec![],
                ParamPlace::Scalar(s) => vec![abi_extensions::physical_width(s)],
                ParamPlace::Pair(a, c) => vec![a.width, c.width],
            })
            .collect();
        let s_inst: Vec<EventInstance> = spec
            .events
            .get(key)
            .map(|v| {
                v.iter()
                    .map(|i| EventInstance {
                        path: substitute(&i.path, &map),
                        args: i.args.iter().map(|a| substitute(a, &map)).collect(),
                    })
                    .collect()
            })
            .unwrap_or_default();
        let m_inst: &[EventInstance] = exec.events.get(off).map(Vec::as_slice).unwrap_or(&[]);
        let arity = widths.len();
        if s_inst.iter().chain(m_inst).any(|i| i.args.len() != arity) {
            return PairOutcome::Unknown {
                which: "O3".into(),
                detail: format!("{} reads an argument count P does not place", site_name(*key)),
            };
        }
        let (rs, as_) = merge_instances(&s_inst, &widths);
        let (rm, am) = merge_instances(m_inst, &widths);
        if as_.len() != am.len() {
            return PairOutcome::Unknown {
                which: "O3".into(),
                detail: format!(
                    "{} and its machine site read different argument counts",
                    site_name(*key)
                ),
            };
        }
        let tag = format!("{} -> `{callee}` @ {off:#x}", site_name(*key));
        items.push((
            format!("reach({tag})"),
            "O3",
            pred_to_int(rm.clone(), 1),
            pred_to_int(rs.clone(), 1),
        ));
        for (j, ((m, s), w)) in am.into_iter().zip(as_).zip(&widths).enumerate() {
            items.push((format!("arg{j}({tag})"), "O3", guard(&rs, m, *w), guard(&rs, s, *w)));
        }
        o3_count += 1;
    }
    // O4.
    let has_value = !matches!(exec.own_ret, ReturnPlace::Void);
    let machine_reach = outcome.reach.clone();
    if !matches!(machine_reach, Formula::Bool(true)) {
        // spec_reach ⇒ machine_reach, as the 1-bit equation (spec ∧ ¬machine) == 0.
        items.push((
            "reach(return)".into(),
            "O4",
            pred_to_int(
                Formula::And(vec![spec_reach.clone(), Formula::Not(b(machine_reach.clone()))]),
                1,
            ),
            Formula::BitVec { value: 0, width: 1 },
        ));
    }
    if has_value {
        let w = own_width(exec.own_ret);
        items.push((
            "value(return)".into(),
            "O4",
            guard(&spec_reach, outcome.value.clone(), w),
            guard(
                &spec_reach,
                match exec.own_ret {
                    ReturnPlace::Scalar(s) => {
                        match abi_extensions::physical_value(s, spec_value.clone()) {
                            Ok(value) => value,
                            Err(reason) => {
                                return PairOutcome::Unknown { which: "O4".into(), detail: reason };
                            }
                        }
                    }
                    _ => spec_value.clone(),
                },
                w,
            ),
        ));
    }

    // The structural reading of `abi_fold` — EXACT identities only (SP-relative
    // select-over-store, SP offset arithmetic, little-endian byte reassembly,
    // the low part of a widened or re-paired register) — so a value the bytes
    // spill and reload across a call reads as the value itself.
    let items: Vec<(String, &'static str, Formula, Formula)> =
        items.into_iter().map(|(n, w, m, s)| (n, w, abi_fold(&m), abi_fold(&s))).collect();

    // (4) ay decides each item: a counterexample is Refuted, undecided Unknown.
    // CONSTDIV-1 (DECISION_QUEUE): a machine side whose magic-multiply quotients
    // the hook replaced by `x / d`, each replacement kernel-admitted, is decided
    // on that rewrite (ay still refutes a wrong one); otherwise as before.
    let mut const_div_note = String::new();
    for (name, which, m, s) in &items {
        #[cfg(feature = "kernel-recheck")]
        let rewrite = crate::verify_output_instantiate::const_div_step4(name, m);
        #[cfg(not(feature = "kernel-recheck"))]
        let rewrite: Option<(Formula, String)> = None;
        let decided = match &rewrite {
            Some((rewritten, note)) => {
                const_div_note.push_str(note);
                rewritten
            }
            None => m,
        };
        match discharge_equal_pre(decided, s, None) {
            Discharge::Proven => {}
            // A counterexample that reads memory may rest on an aliasing model
            // (a non-frame store the solver lets overlap a frame slot), which is
            // not evidence against the bytes — the same rule O0 applies.
            Discharge::CounterExample
                if abi_extensions::observes_callee_padding(m)
                    || abi_extensions::observes_callee_padding(s) =>
            {
                return PairOutcome::Unknown {
                    which: (*which).into(),
                    detail: format!("{name} depends on unspecified callee result padding"),
                };
            }
            Discharge::CounterExample if formula_reads_memory(m) || formula_reads_memory(s) => {
                return PairOutcome::Unknown {
                    which: (*which).into(),
                    detail: format!(
                        "{name} has a counterexample only through memory (fail-closed: neither a \
                         miscompile nor a proof)"
                    ),
                };
            }
            Discharge::CounterExample => {
                return PairOutcome::Refuted {
                    which: (*which).into(),
                    detail: format!(
                        "emitted bytes for fn `{symbol}` violate {name}: ay found a counterexample input"
                    ),
                };
            }
            Discharge::Unknown(r) => {
                return PairOutcome::Unknown {
                    which: (*which).into(),
                    detail: format!("{name} did not conclude: {r}"),
                };
            }
        }
    }

    // (4b) NO CHECK FAILS ON A REACHED PATH. A failed unsited check only
    // drops the execution from `spec_reach`, and O4 states `spec_reach ⇒
    // machine_reach` alone, so where a check fails no item constrains the
    // bytes: code that returns normally there, instead of panicking as Rust
    // does, would discharge every item. Until the failure path is modeled (the
    // panic entry as a divergent event, step 5.7), a function holding a check
    // that can fail is Unknown. It runs after (4), so a counterexample on an
    // item inside `spec_reach` (a real execution the check lets through) is
    // still Refuted. A check that cannot fail passes, and joins the kernel
    // conjunction (5) as `fail == 0`, so [PROVED] never rests on ay alone for
    // it. A faithful sited lowering is Unknown at O2 (its `bl` lies in a trap
    // tail) unless PKG-C5c S2a admits the tail unexecuted, which this item and
    // O4's reach are what make sound: no check fails where the IR returns, and
    // the machine reaches no tail there.
    let checks: Vec<(&str, Formula)> =
        spec.checks.iter().map(|(what, c)| (what.as_str(), substitute(c, &map))).collect();
    for (what, c) in &checks {
        match discharge_valid(&Formula::Not(b(c.clone()))) {
            Discharge::Proven => {}
            Discharge::CounterExample => {
                return PairOutcome::Unknown {
                    which: "O4".into(),
                    detail: format!(
                        "{what} can fail on a reached path; the failure path is not modeled, so \
                         nothing checks that the bytes panic there (fail-closed)"
                    ),
                };
            }
            Discharge::Unknown(r) => {
                return PairOutcome::Unknown { which: "O4".into(), detail: format!("{what}: {r}") };
            }
        }
    }

    // (5) The kernel re-checks the ONE conjunction: O0's residue (when the
    // structural reading left one), O3, O4 and (4b).
    let mut conj: Vec<(Formula, Formula)> =
        items.iter().map(|(_, _, m, s)| (m.clone(), s.clone())).collect();
    for (_, c) in checks {
        conj.push((pred_to_int(c, 1), Formula::BitVec { value: 0, width: 1 }));
    }
    conj.extend(model_equations);
    let mut abi_lowerable = true;
    for c in residue {
        match &c.claim {
            Formula::Eq(l, r) => conj.push(((**l).clone(), (**r).clone())),
            Formula::Not(w) => {
                conj.push((pred_to_int((**w).clone(), 1), Formula::BitVec { value: 0, width: 1 }))
            }
            _ => abi_lowerable = false,
        }
    }
    let kernel_eligible =
        side.is_empty() && abi_lowerable && !matches!(abi, AbiDischarge::Verdict(_));
    let evidence = if kernel_eligible {
        // One retry with closed branches (ground-condition Ites) folded and two identities
        // applied, each fold's condition and each identity instance a kernel-checked side
        // condition (call_event/closed_branch.rs, DECISION_QUEUE AGG-SSA-2). Then the branch
        // split: one kernel-checked atom case split over the branching reflection of `conj`
        // (verify_output_instantiate/branch_split.rs, DECISION_QUEUE BRANCH-SPLIT-1), after the
        // retry declines or in place of a non-kernel first evidence. Kernel evidence is never
        // replaced.
        let branch = |c: &[(Formula, Formula)]| -> Option<ProvenEvidence> {
            #[cfg(feature = "kernel-recheck")]
            {
                crate::verify_output_instantiate::try_branch_split_conjunction(c)
            }
            #[cfg(not(feature = "kernel-recheck"))]
            {
                let _ = c;
                None
            }
        };
        match try_kernel_recheckable_conjunction(&conj) {
            Some(e) if e.is_kernel() => Some(e),
            None => closed_branch::retry(&conj)
                .or_else(|| branch(&conj))
                .or(Some(ProvenEvidence::AyValidated)),
            other => branch(&conj).or(other),
        }
    } else {
        Some(ProvenEvidence::AyValidated)
    };
    // CONSTDIV-1: after a rewrite only kernel evidence of the ORIGINAL conjunction
    // stands; otherwise [VALIDATED], with O4 naming the rewrite and its theorems.
    let evidence = if const_div_note.is_empty() {
        evidence
    } else {
        evidence.filter(ProvenEvidence::is_kernel).or(Some(ProvenEvidence::AyValidated))
    };
    PairOutcome::Proven {
        o3: format!("{o3_count} event(s): reach and arguments equal through P"),
        o4: format!(
            "{}{const_div_note}",
            if has_value {
                "the result equals the IR's wherever the IR returns"
            } else {
                "no result; the machine returns wherever the IR does"
            }
        ),
        evidence,
    }
}

#[cfg(test)]
#[path = "call_event/dead_tail_tests.rs"]
mod dead_tail_tests;
#[cfg(test)]
mod variadic_split_tests;
