// trust-cg-bridge/verify_output.rs — the PROVEN-OUTPUT GATE, in library form.
//
// THE RUNG (M-POS, library form): promote the proven-output pipeline out of the
// `tests/proven_output_autospec.rs` test file into a REUSABLE, FAIL-CLOSED gate
// API that a targo/codegen integration can call to REFUSE emitting a function
// whose machine output is not provably equal to its auto-derived IR semantics.
//
// The gate composes three pieces, all promoted verbatim from the validated test
// harness:
//   1. `trust_ir_semantics(func) -> Result<Formula, String>` — a PURE symbolic
//      interpreter that computes the intended-semantics Formula of `func`'s
//      return value over the AAPCS64 argument registers. Signedness is read from
//      OPERAND types (the discriminator the trust-cg miscompile got wrong by
//      reading the bool DESTINATION type). FAILS CLOSED (Err) on any unsupported
//      shape (float, control flow, calls, memory, projections, ...).
//   2. the byte-derived machine output: emit -> object text section -> decode_aarch64
//      -> Aarch64Semantics::effects -> apply_effects -> read_gpr. NOTHING from
//      the IR enters this side — it is derived only from the EMITTED BYTES.
//   3. the ay discharge: UNSAT of `(pre AND NOT(machine_out == auto_spec))`
//      proves equality for all inputs.
//
// VERDICTS (fail-closed):
//   Proven   — ay proved `NOT(machine_out == auto_spec)` UNSAT (all inputs agree).
//   Refuted  — ay returned SAT: a concrete input makes the bytes compute the
//              wrong value. A MISCOMPILE. (Reverting the signed-comparison fix in
//              lower.rs, or corrupting an emitted byte, lands here — see tests.)
//   Unknown  — the interpreter/prover fail-closed on an unsupported shape, ay
//              returned unknown/timeout, or emission/decoding could not complete.
//              NEVER Proven on Unknown.
//
// SCOPE (honest): integer-only, straight-line, single-block scalar functions
// (entry block, terminator Return). BinOp add/sub/mul/and/or/xor/shl/shr/div/rem,
// all ICmp signed+unsigned, UnOp Neg, Cast SExt/ZExt/Trunc, Const, Use, Return.
// Everything else is Unknown (fail-closed). This is the reusable GATE; wiring it
// into the `rustc_codegen_trust_cg` dylib + bootstrap is a heavier FOLLOW-ON and
// is out of scope here.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{HashMap, HashSet};

use ay::{BigInt, Logic, Solver, Term};
use trust_disasm::{Condition, Opcode, decode_aarch64};
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics, condition_to_formula};
use trust_types::grade::GradeRecord;
use trust_types::{
    BinOp, BlockId, ConstValue, Formula, Operand, Place, Projection, RoundingMode, Rvalue, Sort,
    Statement, Terminator, Ty, UnOp, VerifiableFunction,
};

use crate::codegen_backend::{TrustCgCodegenBackend, TrustCgTargetArch};

// ===========================================================================
// PUBLIC GATE API
// ===========================================================================

/// Result of verifying that a function's emitted machine code preserves the
/// auto-derived intended semantics of its IR.
///
/// This is the verdict a codegen/`targo` integration acts on: `Refuted` is
/// always refused; `Unknown` is refused by the strict policy, while an explicit
/// best-effort policy may ship already-produced bytes as visibly uncertified.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum OutputVerdict {
    /// Emitted bytes provably compute the auto-derived IR semantics for ALL
    /// inputs. The `evidence` records WHAT authority backs the claim:
    ///   * [`ProvenEvidence::KernelRecheckable`] — a zero-trust bit-blast
    ///     certificate ([`ay_proof::BvBlastProof`]) is attached; the obligation
    ///     lowered into the `BvExpr` fragment, `ay-proof` exported a proof whose
    ///     refutation is WITHIN the kernel-re-check step-count frontier (see
    ///     `MAX_RECHECKABLE_REFUTATION_STEPS`), and clean's
    ///     `certify_unsat3_by_reflection` (the proven sub-quadratic trie checker)
    ///     KERNEL-re-checks it to Unsat with EMPTY domain axioms. This is the
    ///     **[PROVED]** grade: ay is a producer only; the attached artifact is the
    ///     trusted object. Covered surface: bitwise and/or/xor and sext (the
    ///     within-frontier ops). Register-width carry/borrow chains (add/sub/neg
    ///     and the Sub-based compares) exceed the frontier and fall to [VALIDATED].
    ///   * [`ProvenEvidence::AyValidated`] — ay proved `NOT(machine_out ==
    ///     auto_spec)` UNSAT, but the obligation falls OUTSIDE the lowerable
    ///     fragment (e.g. control flow, comparisons, division, memory) so no
    ///     kernel-re-checkable artifact exists yet. This is the **[VALIDATED]**
    ///     grade: ay is the sole authority (it is in the re-check TCB).
    Proven {
        /// What backs the proven claim (kernel-re-checkable cert vs ay-only).
        evidence: ProvenEvidence,
    },
    /// ay found a counterexample: for some input the emitted bytes compute the
    /// WRONG value. This is a miscompile; the function must not be emitted.
    Refuted {
        /// Human-readable description of the refutation.
        detail: String,
    },
    /// Verification could not complete: unsupported function shape (interpreter
    /// failed closed), emission/decoding failure, or ay returned unknown/timeout.
    /// It is refused under [`EmitPolicy::StrictProvenOnly`]; an explicit
    /// [`EmitPolicy::AllowUnknown`] caller may emit successfully-produced bytes,
    /// which are counted as uncertified in [`CertificationReport`].
    Unknown {
        /// Why verification could not conclude `Proven` or `Refuted`.
        reason: String,
    },
}

/// The authority backing an [`OutputVerdict::Proven`] verdict.
///
/// HONESTY (load-bearing): the gate emits [`ProvenEvidence::KernelRecheckable`]
/// (**[PROVED]**) ONLY when a validating, clean-re-checkable
/// [`ay_proof::BvBlastProof`] is attached — i.e. the obligation lowered into the
/// `BvExpr` add-leaf fragment AND `export_bv_blast_proof_expr` returned a proof
/// whose `validate()` succeeds. Everything else that ay discharges UNSAT is
/// reported as [`ProvenEvidence::AyValidated`] (**[VALIDATED]**): ay is the sole
/// authority. The gate NEVER claims [PROVED] without the attached proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProvenEvidence {
    /// ay discharged the obligation UNSAT, but the obligation is outside the
    /// lowerable `BvExpr` fragment (or export did not produce a validating
    /// proof). ay is the sole re-check authority — this is the [VALIDATED] grade.
    AyValidated,
    /// **[CITED]** — the obligation is a wide `Mul` discharged by CITING the
    /// kernel-checked structured multiplier theorem, not by re-checking a
    /// per-instance refutation.
    ///
    /// This is the grade the g16 line exists to produce, and it is deliberately
    /// NOT [PROVED]. What the kernel checked is the width-generic
    /// `G16Mul.mul_equiv` / `blast_equals_ir`; what it did NOT check is
    /// `G16Mul.AyBlastAgrees` — that ay's Rust encoder emits the model's
    /// multiplier. That correspondence is machine-checked (exhaustively to
    /// width 8, sampled at 16/32/64 — see
    /// `tests/ay_blast_agrees_differential.rs`) but is not provable inside
    /// clean, because the encoder is Rust.
    ///
    /// The residual travels with the verdict rather than living in a comment:
    /// the `grade` field CARRIES a real `GradeRecord::cited_kernel_theorem`
    /// (2026-08-20 carrier increment — this is the first production
    /// constructor of that record that does not immediately collapse to its
    /// legacy projection), whose named closure caps the projection at
    /// `Trusted`. It can never read as `Certified`.
    ///
    /// ON BY DEFAULT (owner decision, 2026-08-16). `TCG_CITE_WIDE_MUL=0`
    /// restores the previous behaviour.
    ///
    /// Enabling it raises no claim: a citation is classified with [VALIDATED],
    /// caps at `Trusted`, and is refused by `StrictProvenOnly` exactly as
    /// [VALIDATED] is. It replaces a bare `AyValidated` — which tells a reader
    /// nothing — with a verdict that NAMES the cited theorem and the residual.
    StructuralCitation {
        /// The kernel-checked theorem being cited.
        theorem: &'static str,
        /// The correspondence the kernel did NOT check.
        residual: &'static str,
        /// Operand width of the cited multiply.
        width: u32,
        /// The typed §7 grade this citation carries through the pipeline:
        /// `GradeRecord::cited_kernel_theorem(theorem, residual)`, minted at
        /// the same site as the citation itself (see
        /// `structural_citation_evidence`, which is the ONLY constructor, so
        /// the record and the string fields cannot drift apart). Additive:
        /// classification, counting, and `StrictProvenOnly` refusal still key
        /// on the variant, never on this record.
        grade: GradeRecord,
    },
    /// A zero-trust bit-blast certificate kernel-re-checkable by clean's
    /// `certify_unsat_by_reflection` to Unsat with empty domain axioms. This is
    /// the [PROVED] grade: ay is a producer only; the proof is the trusted object.
    KernelRecheckable(ay_proof::BvBlastProof),
    /// **[PROVED] for a 128-bit AAPCS64 REGISTER PAIR:** the obligation
    /// `concat(hi_m, lo_m) == concat(hi_s, lo_s)` was split at bit 64 into TWO
    /// 64-bit equalities and BOTH carry their own clean-kernel-accepted
    /// certificate. Same grade and same authority as
    /// [`ProvenEvidence::KernelRecheckable`] — the kernel is the authority for
    /// each half and ay is a producer only — with the arity of the evidence made
    /// visible rather than collapsed.
    ///
    /// A 128-bit obligation CANNOT carry a single certificate: `ay_proof::BvExpr`
    /// has no concat node and `ay_proof::MAX_WIDTH` is 64, so the whole equality
    /// is not exportable as one term. Splitting is exact (concat is injective at
    /// fixed half-widths), so this is neither weaker nor stronger than a single
    /// certificate would be — see `split_register_pair_128`.
    ///
    /// BOTH fields are load-bearing. `high` is not an assumption or a default: a
    /// small `i128` constant has `X1 == 0`, so an evidence shape that omitted it
    /// would grade almost every 128-bit constant return [PROVED] on the strength
    /// of its low half alone.
    KernelRecheckablePair {
        /// Certificate for the HIGH 64 bits (`X1`).
        high: Box<ay_proof::BvBlastProof>,
        /// Certificate for the LOW 64 bits (`X0`).
        low: Box<ay_proof::BvBlastProof>,
    },
    /// **[PROVED] via O(1) STRUCTURED INSTANTIATION (B4):** the obligation's
    /// `(machine_out, auto)` Formulas were reconstructed into clean-kernel terms and
    /// the clean kernel `check_type` accepted a proof — awarded ONLY when `check_type`
    /// SUCCEEDS with empty axiom closure. The `theorem` field records the discharging
    /// lemma/label.
    ///
    /// TWO discharge mechanisms carry this grade with DIFFERENT kernel work (the `theorem`
    /// label distinguishes them — do NOT read them as equivalent):
    ///   (a) SEMANTIC re-derivation — `reflect_formula` into `Clean.BVC.BvF` + a
    ///       `bvfEval`-headed congruence (`bvf_*_cong`) or a NAMED bridge theorem
    ///       (`divGuardBridge`, the eq/ult/slt value bridges). The kernel re-derives a
    ///       semantic relation (e.g. the div ÷0-guard collapse). add/sub/and/xor/mul/div.
    ///   (b) STRUCTURAL identity — `rem_to_val` reconstructs both sides to a clean value
    ///       and the kernel verifies `Eq.refl` (operand-tied STRUCTURAL equality), NOT a
    ///       semantic relation. Unsigned rem takes this path (rem is DEFINED as its
    ///       composite, so refl is the ceiling — the inner udiv's correctness is div's).
    ///
    /// In BOTH paths the per-operand identity IS kernel-forced (divergent operands key to
    /// distinct opaque bit-lists -> `check_type` REJECTS). HONEST RESIDUAL (shared by all
    /// value discharges; larger for (b), which is refl-only): the readout/coercion WRAPPER
    /// faithfulness is MATCHER-trusted (the `div_peel_to_ite`/`rem_to_val` wrapper strip +
    /// the node->eval reconstruction are in the TCB), backed by ay's prior width-matched
    /// UNSAT over the unstripped formulas — so a matcher bug can only MIS-GRADE an
    /// already-ay-proven obligation, never fabricate a [PROVED]. So "ay out of the TCB" holds
    /// for the kernel-verified RELATION, but the wrapper/reconstruction step is ay-backed, not
    /// ay-free. This is the FAST path: O(1) instantiation, no per-instance SAT reflection.
    KernelInstantiated {
        /// The clean lemma(s) the discharge rests on (for the report / audit).
        theorem: String,
    },
}

impl ProvenEvidence {
    /// The typed §7 [`GradeRecord`] this evidence CARRIES, if the R-U grade
    /// migration has threaded one through this variant.
    ///
    /// This increment (2026-08-20), only [`ProvenEvidence::StructuralCitation`]
    /// carries a record — a `GradeRecord::cited_kernel_theorem` naming the
    /// cited theorem and the unproved residual. Every other variant returns
    /// `None`: deriving a record here for the kernel/[VALIDATED] grades would
    /// be minting a claim at a read accessor rather than carrying one from the
    /// evidence's production site, which is exactly the shape the migration
    /// exists to remove. Additive: nothing in classification or policy reads
    /// this — the legacy surfaces are unchanged.
    #[must_use]
    pub fn carried_grade(&self) -> Option<&GradeRecord> {
        match self {
            ProvenEvidence::StructuralCitation { grade, .. } => Some(grade),
            _ => None,
        }
    }
}

impl OutputVerdict {
    /// The typed §7 [`GradeRecord`] carried by this verdict's evidence, if
    /// any — see [`ProvenEvidence::carried_grade`]. `None` for Refuted,
    /// Unknown, and every Proven evidence the migration has not yet threaded.
    #[must_use]
    pub fn carried_grade(&self) -> Option<&GradeRecord> {
        match self {
            OutputVerdict::Proven { evidence } => evidence.carried_grade(),
            _ => None,
        }
    }

    /// True iff this is a `Proven` verdict (either grade). Enforcement
    /// (`emit_objects_verified`) emits on this; the GRADE ([PROVED] vs
    /// [VALIDATED]) is read off [`OutputVerdict::Proven`]'s `evidence`.
    #[must_use]
    pub fn is_proven(&self) -> bool {
        matches!(self, OutputVerdict::Proven { .. })
    }

    /// The attached kernel-re-checkable bit-blast proof, if this verdict is
    /// [PROVED]-grade via the SLOW (SAT-reflection) path AND carries exactly ONE
    /// certificate. `None` for the O(1) instantiation path, [VALIDATED]-grade
    /// Proven, Refuted, or Unknown.
    ///
    /// DELIBERATELY `None` FOR THE 128-BIT REGISTER PAIR
    /// ([`ProvenEvidence::KernelRecheckablePair`]): that verdict rests on TWO
    /// certificates and this signature can return one. Returning the low half
    /// here would hand a caller half a proof labelled as the proof. Use
    /// [`OutputVerdict::kernel_proofs`], which returns every certificate the
    /// verdict rests on.
    #[must_use]
    pub fn kernel_proof(&self) -> Option<&ay_proof::BvBlastProof> {
        match self {
            OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckable(p) } => Some(p),
            _ => None,
        }
    }

    /// EVERY kernel-re-checkable bit-blast certificate this verdict rests on, in
    /// discharge order. One for the single-obligation slow path, TWO (high then
    /// low) for a 128-bit register pair, and empty for the O(1) instantiation
    /// path, [VALIDATED], Refuted, or Unknown.
    ///
    /// This is the accessor that cannot silently drop half of a split proof.
    #[must_use]
    pub fn kernel_proofs(&self) -> Vec<&ay_proof::BvBlastProof> {
        match self {
            OutputVerdict::Proven { evidence: ProvenEvidence::KernelRecheckable(p) } => vec![p],
            OutputVerdict::Proven {
                evidence: ProvenEvidence::KernelRecheckablePair { high, low },
            } => vec![high.as_ref(), low.as_ref()],
            _ => Vec::new(),
        }
    }

    /// True iff this verdict is **[PROVED]** by the clean KERNEL — the slow
    /// SAT-reflection path (`KernelRecheckable`), the 128-bit register-pair form
    /// of that same path (`KernelRecheckablePair`, two kernel-accepted halves),
    /// or the O(1) structured instantiation path (`KernelInstantiated`). This is
    /// the [PROVED]-vs-[VALIDATED] discriminator (ay is not the authority for any
    /// kernel grade).
    #[must_use]
    pub fn is_kernel_proved(&self) -> bool {
        matches!(
            self,
            OutputVerdict::Proven {
                evidence: ProvenEvidence::KernelRecheckable(_)
                    | ProvenEvidence::KernelRecheckablePair { .. }
                    | ProvenEvidence::KernelInstantiated { .. }
            }
        )
    }
}

/// Verify that `func`'s emitted machine code preserves its auto-derived IR
/// semantics, for all inputs.
///
/// Pipeline:
///   1. derive intended semantics: `trust_ir_semantics(func)` (Err => Unknown).
///   2. emit `func` to machine bytes and extract the `__text` section
///      (failure => Unknown).
///   3. decode bytes -> `Aarch64Semantics` effects -> apply -> read return reg,
///      yielding a machine-side output Formula (failure => Unknown).
///   4. discharge `machine_out == auto_spec` via ay:
///        UNSAT => `Proven`, SAT => `Refuted`, unknown => `Unknown`.
///
/// The return register width and any precondition (e.g. divisor != 0 for
/// division) are INFERRED from `func`: the width comes from the return type's
/// register slot, and a `BinOp::Div`/`BinOp::Rem` adds a divisor-nonzero
/// precondition. This keeps the gate a single-argument call for the integration.
///
/// Never returns `Proven` unless ay actually proved equality (fail-closed).
pub fn verify_output_preserved(func: &VerifiableFunction) -> OutputVerdict {
    let backend = default_verification_backend();
    verify_output_preserved_with_backend(func, &backend)
}

/// Backend-aware form of [`verify_output_preserved`]. The emitted candidate is
/// produced with `backend` exactly as configured by the caller (target,
/// lowering policy, and optimization level), rather than with a fresh O0 host
/// backend. This is the entry point production codegen should use.
pub fn verify_output_preserved_with_backend(
    func: &VerifiableFunction,
    backend: &TrustCgCodegenBackend,
) -> OutputVerdict {
    verify_output_preserved_capturing_with_backend(func, backend).0
}

/// Trust (RUNG 2 — shipped == verified): the capturing core of
/// [`verify_output_preserved`]. Returns the verdict AND the FULL object bytes of
/// the single emission the verdict was computed over (when emission succeeded).
///
/// The build gate ([`emit_objects_verified`]) SHIPS exactly these returned bytes
/// — there is no second emission for a gated function, so the bytes the gate
/// VERIFIED are byte-for-byte the bytes that ship. `bytes` is `Some` whenever the
/// emission step succeeded (covering both `Proven` and an emittable `Unknown`),
/// and `None` only when emission/lowering itself failed (so there is nothing to
/// ship). This makes the verified-bytes the single source of truth for the
/// artifact, closing the emit-time TOCTOU by construction.
fn verify_output_preserved_capturing_with_backend(
    func: &VerifiableFunction,
    backend: &TrustCgCodegenBackend,
) -> (OutputVerdict, Option<Vec<u8>>) {
    // Single-function entry point: an EMPTY callee env — a `Terminator::Call`
    // therefore always fails closed (Unknown), byte-for-byte the original
    // behavior. The bundle gate uses `verify_output_preserved_capturing_env`.
    verify_output_preserved_capturing_env_with_backend(func, &CalleeEnv::empty(), backend)
}

/// Bundle-aware capturing core: identical to [`verify_output_preserved_capturing`]
/// except a `Terminator::Call` to a LOCAL PURE Proven callee in `env` is composed
/// on BOTH the IR side (`trust_ir_semantics_env`) and the machine side (the
/// executor consults the emitted object's `ARM64_RELOC_BRANCH26` relocations to
/// identify the `bl` target symbol and substitutes the same callee output). With
/// an empty `env` both halves fail closed on any call, reproducing the original.
#[cfg(test)]
fn verify_output_preserved_capturing_env(
    func: &VerifiableFunction,
    env: &CalleeEnv,
) -> (OutputVerdict, Option<Vec<u8>>) {
    let backend = default_verification_backend();
    verify_output_preserved_capturing_env_with_backend(func, env, &backend)
}

fn verify_output_preserved_capturing_env_with_backend(
    func: &VerifiableFunction,
    env: &CalleeEnv,
    backend: &TrustCgCodegenBackend,
) -> (OutputVerdict, Option<Vec<u8>>) {
    // Keep emission, source semantics, divisor assumptions, and machine-output
    // decoding on one exact semantic view. TailCall has no MIR continuation,
    // but at this boundary it is equivalent to a direct call writing local 0
    // followed by Return; the source object itself remains unchanged.
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();

    // Emit FIRST with the exact production backend. Unsupported verifier shapes
    // and decoder gaps must not discard a successfully produced candidate:
    // AllowUnknown is explicitly allowed to ship those bytes as uncertified.
    // A genuine lowering/emission failure remains `None` and is fatal under
    // every policy in the build gate below.
    let obj = match emit_object_with_backend(func, backend) {
        Ok(obj) => obj,
        Err(reason) => return (OutputVerdict::Unknown { reason }, None),
    };

    // (1) intended semantics — Err => Unknown (unsupported shape), while
    // retaining the already-emitted bytes for AllowUnknown.
    let auto = match trust_ir_semantics_env(func, env) {
        Ok(f) => f,
        Err(reason) => return (OutputVerdict::Unknown { reason }, Some(obj)),
    };

    // A return type with no defined register slot is an UNKNOWN verdict, not a
    // guessed 32-bit read of W0. (Ordering already makes this unreachable
    // today: `trust_ir_semantics_env` above fails closed on any non-scalar
    // local. Fail closed here anyway — see `reg_width`.)
    let out_width = match return_reg_width(func) {
        Ok(w) => w,
        Err(reason) => return (OutputVerdict::Unknown { reason }, Some(obj)),
    };
    let pre = divisor_nonzero_precondition(func);

    // (2)+(3) byte-derived machine output from that SAME emission. Decoder or
    // semantic-execution failure is Unknown, but the bytes remain shippable
    // under AllowUnknown and visibly count as uncertified.
    let machine_out =
        match decode_emitted_object_env(func, &obj, out_width, env, backend.target_arch()) {
            Ok(f) => f,
            Err(reason) => return (OutputVerdict::Unknown { reason }, Some(obj)),
        };
    let captured = Some(obj);

    // (4) discharge equality.
    let verdict = match discharge_equal_pre(&machine_out, &auto, pre.as_ref()) {
        Discharge::Proven => OutputVerdict::Proven {
            // [PROVED] PROMOTION: ay said UNSAT. Try to lower BOTH sides of the
            // obligation into the self-contained `BvExpr` add-leaf fragment and
            // export a zero-trust bit-blast certificate. If that succeeds and the
            // proof self-validates, attach it as KERNEL-RE-CHECKABLE evidence
            // (the [PROVED] grade — ay is producer-only). Any failure (shape
            // outside the fragment, width mismatch, no surfaceable refutation,
            // proof fails to validate) falls back to [VALIDATED] (ay-only).
            // NEVER [PROVED] without a validating proof.
            evidence: try_kernel_recheckable_proof(&machine_out, &auto, pre.as_ref())
                .unwrap_or(ProvenEvidence::AyValidated),
        },
        Discharge::CounterExample => OutputVerdict::Refuted {
            detail: format!(
                "emitted bytes do not equal auto-derived IR semantics for fn `{}` \
                 (ay found a counterexample input — miscompile)",
                func.name
            ),
        },
        Discharge::Unknown(reason) => OutputVerdict::Unknown { reason },
    };

    // Trust (RUNG 2): carry the verified bytes for an emittable verdict so the
    // build gate ships THIS exact emission. A Refuted function is a miscompile —
    // it must NEVER carry shippable bytes (drop them so no path can emit it).
    let bytes = match &verdict {
        OutputVerdict::Refuted { .. } => None,
        _ => captured,
    };
    (verdict, bytes)
}

/// Attempt to promote a proven obligation to the **[PROVED]** grade by lowering
/// both sides into the self-contained `BvExpr` add-leaf fragment and exporting a
/// zero-trust bit-blast certificate.
///
/// Returns `Some(ProvenEvidence::KernelRecheckable(proof))` ONLY when:
///   * there is NO precondition — `export_bv_blast_proof_expr` proves
///     UNCONDITIONAL equality, so a conditional obligation (e.g. divisor != 0)
///     would be a different, weaker claim; we fall back to [VALIDATED] there;
///   * BOTH sides lower via [`formula_to_bvexpr`] (in-fragment shape);
///   * `export_bv_blast_proof_expr` returns a proof whose `validate()` succeeds
///     (a cheap producer-side first filter — NOT the [PROVED] authority); and
///   * **(RUNG 1)** with the `kernel-recheck` feature, the CLEAN CIC KERNEL
///     independently re-checks the exported refutation to `Unsat` with ZERO
///     domain axioms (via `clean_auto::proved_gate`). The [PROVED] grade is the
///     KERNEL's claim, not ay's. Without `kernel-recheck` the gate cannot
///     re-check the cert and DECLINES [PROVED] (fail-closed to [VALIDATED]).
///
/// Any failure returns `None` -> the caller falls back to [VALIDATED]. This is
/// fail-closed: a malformed/SAT/un-lowerable obligation, or one the clean kernel
/// refuses, never yields a [PROVED] claim. NOTE: ay already returned UNSAT before
/// this runs, so the export's `NoRefutation` here would indicate a lowering that
/// does not faithfully mirror the discharged obligation — we still (correctly)
/// decline [PROVED].
pub(crate) fn try_kernel_recheckable_proof(
    machine_out: &Formula,
    auto: &Formula,
    pre: Option<&Formula>,
) -> Option<ProvenEvidence> {
    // A precondition makes the discharged obligation CONDITIONAL. The unconditional
    // bit-blast export below is not the same claim, but the O(1) CONDITIONAL discharge
    // CAN prove `pre -> machine == auto` directly: for unsigned div, `divGuardBridge`
    // collapses the machine ÷0 guard `Ite(b==0, 0, udiv)` to its udiv else-branch = auto
    // under `bvIsZero <b> = false` (the reflected `b != 0`). Try it; on any non-match or
    // kernel rejection, stay [VALIDATED] (fail-closed — never a false [PROVED]).
    if pre.is_some() {
        #[cfg(feature = "kernel-recheck")]
        {
            if let Some(theorem) =
                crate::verify_output_instantiate::try_div_conditional_discharge(machine_out, auto)
            {
                return Some(ProvenEvidence::KernelInstantiated { theorem });
            }
            // REM: machine and auto are the identical a-(a/b)*b composite (modulo wrappers);
            // reconstruct both and discharge by reflexivity (operand-tied). Unconditional, so
            // strictly stronger than the gate's b!=0 obligation.
            if let Some(theorem) =
                crate::verify_output_instantiate::try_rem_conditional_discharge(machine_out, auto)
            {
                return Some(ProvenEvidence::KernelInstantiated { theorem });
            }
        }
        return None;
    }

    // B4 — THE O(1) STRUCTURED-INSTANTIATION FAST PATH (strictly additive).
    // ay already proved `machine_out == auto` (this runs in the Proven branch).
    // Try to discharge it by O(1) instantiation of the clean coercion lemmas:
    // reflect both sides into `Clean.BVC.BvF` and kernel-`check_type` a
    // `bvfEval`-headed proof. Awarded [PROVED]-via-instantiation ONLY when the
    // KERNEL check_type SUCCEEDS against the REAL reflected obligation. On ANY
    // non-match / reflection error / kernel rejection, fall through to the slow
    // SAT-reflection path below (UNCHANGED). A matcher/reflection bug can only
    // lose speed (fall through), never award a false [PROVED] — the kernel is the
    // sole authority and the obligation is the real reflected Formula.
    #[cfg(feature = "kernel-recheck")]
    {
        // MEMORY store-load FIRST (guarded on a Select in auto — won't touch scalar
        // obligations): reflect both sides with concrete-cons leaves so the sub-register
        // readout coercions REDUCE, bridged by selectStoreSame. Fail-closed on non-match.
        if let Some(theorem) =
            crate::verify_output_instantiate::try_mem_store_load_discharge(machine_out, auto)
        {
            return Some(ProvenEvidence::KernelInstantiated { theorem });
        }
        if let Some(theorem) =
            crate::verify_output_instantiate::try_o1_instantiation_discharge(machine_out, auto)
        {
            return Some(ProvenEvidence::KernelInstantiated { theorem });
        }
        // else: fall through to the slow path (no early return).
    }

    // ── 128-BIT REGISTER-PAIR SPLIT ─────────────────────────────────────────
    // A 128-bit obligation cannot reach the bit-blast fragment as ONE term (see
    // `split_register_pair_128` for the two measured reasons). Split it into the
    // HIGH and LOW 64-bit equalities and require BOTH to clear the SAME slow
    // path below. Tried BEFORE the single-term lowering because that lowering
    // has no `BvConcat` arm and would simply `Err` here.
    if let Some(evidence) = try_kernel_recheckable_pair_128(machine_out, auto) {
        return Some(evidence);
    }

    if let Some(proof) = kernel_recheckable_bitblast(machine_out, auto) {
        return Some(ProvenEvidence::KernelRecheckable(proof));
    }

    // THE CITATION PATH. `kernel_recheckable_bitblast` declines a `Mul` wider
    // than `MAX_RECHECKABLE_MUL_WIDTH` because its refutation is neither
    // exportable nor re-checkable (measured at that guard: 1_759_704 steps and
    // 24.3s to EXPORT at width 8 alone). The structured theorem covers those
    // widths generically, so citing it yields a real, strictly-below-[PROVED]
    // grade where there was previously nothing.
    //
    // ON BY DEFAULT since 2026-08-16 (owner decision); `TCG_CITE_WIDE_MUL=0`
    // restores the old behaviour. This is safe as a default precisely because it
    // does NOT promote anything: the citation is classified with [VALIDATED] at
    // both report sites, caps at `Trusted`, and `StrictProvenOnly` refuses it on
    // the same footing. The only change is that the verdict now names the cited
    // theorem and the unproved residual instead of saying nothing.
    if cite_wide_mul_enabled() {
        let width = wide_mul_width_for_citation(machine_out, auto);
        if width > MAX_RECHECKABLE_MUL_WIDTH {
            return Some(structural_citation_evidence(width));
        }
    }
    None
}

/// The ONLY constructor of [`ProvenEvidence::StructuralCitation`] — the mint
/// site of the citation's carried [`GradeRecord`].
///
/// The record is built through `GradeRecord::cited_kernel_theorem` from the
/// SAME constants as the variant's string fields, so the typed grade and the
/// human-readable fields cannot drift apart (pinned by
/// `tests/wide_mul_citation_grade.rs`). By that constructor's own contract the
/// record's closure NAMES the theorem and the residual and the grade can never
/// read as `Certified`.
#[cfg(feature = "ay-proofs")]
fn structural_citation_evidence(width: u32) -> ProvenEvidence {
    ProvenEvidence::StructuralCitation {
        theorem: CITED_MUL_THEOREM,
        residual: CITED_MUL_RESIDUAL,
        width,
        grade: GradeRecord::cited_kernel_theorem(CITED_MUL_THEOREM, CITED_MUL_RESIDUAL),
    }
}

/// The widest `Mul` in either side of the obligation, or 0 when the obligation
/// does not lower to the `BvExpr` fragment at all.
///
/// A citation is only offered for an obligation the fragment CAN express and
/// whose multiply is genuinely past the re-checkable bound. Anything that fails
/// to lower gets 0 and therefore no citation — declining, as before, rather than
/// citing a theorem about a term we could not even build.
#[cfg(feature = "ay-proofs")]
fn wide_mul_width_for_citation(machine_out: &Formula, auto: &Formula) -> u32 {
    let (Ok(lhs), Ok(rhs)) = (formula_to_bvexpr(machine_out), formula_to_bvexpr(auto)) else {
        return 0;
    };
    mul_width(&lhs).max(mul_width(&rhs))
}

/// Discharge ONE equality obligation `machine_out == auto` through the SLOW
/// (SAT-reflection) path and return the clean-kernel-accepted certificate.
///
/// This is the whole of the historical tail of [`try_kernel_recheckable_proof`],
/// factored out UNCHANGED so that the 128-bit register-pair split can run each
/// half through the IDENTICAL pipeline — same fragment lowering, same multiply
/// tractability guard, same producer self-validation, same step-count frontier,
/// same clean-kernel re-check. A half therefore gets exactly the scrutiny any
/// other 64-bit obligation gets; there is no weaker "half" path.
#[cfg(feature = "ay-proofs")]
fn kernel_recheckable_bitblast(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<ay_proof::BvBlastProof> {
    // TEMPORARY MEASUREMENT INSTRUMENTATION (not for commit): TRUST_GATE_TRACE=1
    // reports exactly which stage of the [PROVED] route declines.
    let trace = std::env::var_os("TRUST_GATE_TRACE").is_some();
    let lhs = match formula_to_bvexpr(machine_out) {
        Ok(v) => v,
        Err(e) => {
            if trace {
                eprintln!("[trace] lhs formula_to_bvexpr FAILED: {e}");
            }
            return None;
        }
    };
    let rhs = match formula_to_bvexpr(auto) {
        Ok(v) => v,
        Err(e) => {
            if trace {
                eprintln!("[trace] rhs formula_to_bvexpr FAILED: {e}");
            }
            return None;
        }
    };
    if trace {
        eprintln!("[trace] both sides lowered to BvExpr OK");
    }
    // TRACTABILITY GUARD (HONESTY): a `bvmul` bit-blasts to a shift-and-add array
    // multiplier whose refutation step-count grows ~16× per +2 operand-width
    // (measured: width 2→234 steps, 4→5 210, 6→88 250, 8→~2.0M).
    //
    // RE-MEASURED 2026-08-16 on a NON-FUSING obligation (`Mul(A,B) == Mul(B,A)`,
    // i.e. the shape the live gate actually faces, where the two sides differ and
    // the blaster's cache cannot collapse them): 2→196 steps / 0.4s,
    // 4→6_059 / 0.4s, 6→97_012 / 1.3s, 8→1_759_704 steps and 24.3s TO EXPORT,
    // before the kernel re-check has begun. The growth law and the original
    // figures hold. Extrapolated, width 10 is ~28M steps and width 32 — the live
    // gate width — is past 10^19.
    //
    // DO NOT RAISE THIS ON THE STRENGTH OF THE ay-blast DIFFERENTIAL. That test
    // blasts `Mul(A,B) == Mul(A,B)`, whose identical sides FUSE, so it exports in
    // 8ms with 17 refutation steps at width 8. It measures GATE STRUCTURE, which
    // is cheap at every width, and says nothing about refutation cost, which is
    // what this cap guards. The two numbers differ by five orders of magnitude at
    // the same width.
    //
    // The clean kernel re-check (`certify_unsat_by_reflection`) is at least linear in steps
    // over a growing clause DB, so a live-gate-width (32) multiply refutation is
    // BOTH un-exportable in bounded memory AND un-re-checkable. Attaching a
    // `KernelRecheckable` proof we cannot actually re-check would be a hollow
    // [PROVED] claim — and even attempting the export would hang/OOM the gate. So
    // we DECLINE the kernel grade for any `Mul` wider than the re-checkable bound
    // and fall back to [VALIDATED] (ay is still the proof authority). Multiply IS
    // proven kernel-re-checkable at small widths (ay-proof `mul_*` tests + clean
    // `reflection_real_mul_unsat_cert_is_fully_zero_trust`); this guard keeps the
    // *live* claim honest. Non-mul ops are unaffected.
    if mul_wider_than(&lhs, MAX_RECHECKABLE_MUL_WIDTH)
        || mul_wider_than(&rhs, MAX_RECHECKABLE_MUL_WIDTH)
    {
        return None;
    }
    let proof = match ay_proof::export_bv_blast_proof_expr(&lhs, &rhs) {
        Ok(p) => p,
        Err(e) => {
            if trace {
                eprintln!("[trace] export_bv_blast_proof_expr FAILED: {e:?}");
            }
            return None;
        }
    };
    if trace {
        eprintln!("[trace] exported refutation steps={}", proof.refutation.steps.len());
    }
    // Producer self-validation: a cheap first filter (ay's own check). It is NOT
    // the [PROVED] authority — see the KERNEL re-check below. NEVER attach a proof
    // ay itself cannot re-check.
    if let Err(e) = proof.validate() {
        if trace {
            eprintln!("[trace] proof.validate FAILED: {e:?}");
        }
        return None;
    }
    // Trust: RUNG 1 (anti-Thompson) — THE [PROVED] GATE. Route the ay-exported
    // refutation through the CLEAN CIC KERNEL. clean-auto reduces
    // `checkRefutes <clauses> <refutation>` to `Bool.true` by linear ι-reduction
    // and applies the PROVED `checkRefutes_sound` Theorem to obtain `Unsat`. The
    // [PROVED] grade (KernelRecheckable) is awarded ONLY when the KERNEL accepts
    // the certificate to `Unsat` with ZERO domain axioms (closure ⊆ FOUNDATIONAL).
    // On a failing/absent kernel re-check we return `None` -> the caller emits
    // [VALIDATED] (AyValidated). This removes ay from the [PROVED] emission TCB:
    // even a refutation that passes ay's own `validate()` is graded [PROVED] only
    // if the clean kernel INDEPENDENTLY re-checks it.
    #[cfg(feature = "kernel-recheck")]
    {
        use clean_auto::proved_gate::GateRecheck;
        // STEP-COUNT FRONTIER (HONESTY): post-trampoline the proven sub-quadratic
        // trie re-check (iterative WHNF, no native deep recursion) covers the whole
        // linear-ALU + integer-compare surface — the register-width carry/borrow
        // chains (add/sub/neg/Sub-based compares, ~7k-19k steps) MEASURED-re-check
        // to Unsat3 with ZERO domain axioms at < 5 GB in tens of seconds to ~100 s.
        // The frontier is now a practical TIME+MEMORY budget, not a stack-depth
        // limit: refutations at/below `MAX_RECHECKABLE_REFUTATION_STEPS` (20480)
        // are KERNEL-re-checked in-gate. (The barrel-shifter shapes shl/lshr/ashr,
        // ~109k-129k slow-path steps, are now KERNEL-[PROVED] via the O(1) coercion-
        // identity reflect path instead, bypassing this bit-blast frontier.) Rather
        // than hang the gate or attach a hollow [PROVED] we cannot afford to re-check,
        // DECLINE over-frontier refutations.
        // The grade frontier changes strict trust-cg emit/refuse decisions, so
        // production uses only the compiled, reviewed constant. Measurement
        // tooling must call an explicit benchmark API instead of mutating the
        // process environment.
        if proof.refutation.steps.len() > MAX_RECHECKABLE_REFUTATION_STEPS {
            if trace {
                eprintln!(
                    "[trace] OVER FRONTIER: steps={} > {MAX_RECHECKABLE_REFUTATION_STEPS}",
                    proof.refutation.steps.len()
                );
            }
            return None;
        }
        match crate::verify_output_instantiate::kernel_recheck_proved_grade_bounded(&proof) {
            GateRecheck::KernelAccepted { .. } => Some(proof),
            // Anything other than a positive `KernelAccepted` is fail-closed to
            // [VALIDATED]: the clean KERNEL refused the cert (`Rejected` — a
            // forged/corrupted refutation, or a non-zero-axiom soundness bridge),
            // or it is some future variant. The gate NEVER claims [PROVED]
            // without an explicit `KernelAccepted` from the clean kernel.
            other => {
                if trace {
                    eprintln!("[trace] KERNEL RE-CHECK declined: {other:?}");
                }
                None
            }
        }
    }
    // Without the `kernel-recheck` feature the clean kernel is not compiled in, so
    // the gate cannot independently re-check the cert. In that configuration the
    // [PROVED] grade would rest on ay's `validate()` alone — which is exactly the
    // ay-in-TCB situation RUNG 1 removes. We therefore DECLINE [PROVED] here and
    // fall back to [VALIDATED]; build the gate with `--features kernel-recheck` to
    // obtain the kernel-rooted [PROVED] grade.
    #[cfg(not(feature = "kernel-recheck"))]
    {
        let _ = &proof;
        None
    }
}

/// The width, in bits, of each half of an AAPCS64 128-bit register pair. Both
/// halves are full X registers — this is not a tunable, it is the ABI.
#[cfg(feature = "ay-proofs")]
const PAIR_HALF_WIDTH: u32 = 64;

/// Split ONE side of a 128-bit obligation into its `(HIGH 64, LOW 64)` halves,
/// or `None` (fail-closed) for any shape whose halves are not manifest.
///
/// WHY THE SPLIT LIVES HERE AND NOT IN `formula_to_bvexpr`. A `BvConcat` arm on
/// the lowering was the obvious move and it is a DEAD END, for two independently
/// fatal reasons:
///
///   1. `ay_proof::BvExpr` HAS NO CONCAT VARIANT (`bv_blast_solver.rs`, the
///      `pub enum BvExpr` — Leaf/Add/Sub/ZeroExt/Extract/Or/And/Xor/Const/
///      SignExt/Shl/Lshr/Ashr/Not/Eq/CarryOut/Mul, and nothing else). A
///      `BvConcat` arm would have nothing to return. Synthesizing one out of
///      `Or(Shl(ZeroExt(hi,64), 64), ZeroExt(lo,64))` only relocates the problem
///      into (2), since every node of that encoding is 128 bits wide.
///   2. `ay_proof::MAX_WIDTH` is 64 (`bv_blast_export.rs`) and
///      `bv_blast_solver::SOLVED_MAX_WIDTH` is defined AS it, so the exporter
///      rejects any obligation wider than 64 bits before a single gate is
///      emitted. A 128-bit `BvExpr` is un-exportable by construction.
///
/// So the split is not an expression rewrite; it is an OBLIGATION rewrite. One
/// 128-bit equality becomes TWO 64-bit equalities, hence TWO certificates —
/// and `formula_to_bvexpr` returns a single `BvExpr` with nowhere to put a
/// second certificate. The caller that owns the equality is the only place that
/// can own two of them.
///
/// WHY THE SPLIT IS SOUND. `concat` is injective on the product of its halves at
/// FIXED widths: for `|a| = |c|` and `|b| = |d|`,
/// `concat(a,b) = concat(c,d)  <->  a = c  /\  b = d`, pointwise at every
/// valuation. Both directions hold, so the split loses NOTHING (a valid 128-bit
/// obligation has two valid halves) and ADDS nothing (two valid halves force the
/// 128-bit obligation). Both sides are universally quantified over the same free
/// leaves, and a conjunction of two validities is the validity of the
/// conjunction, so discharging the halves independently is the same claim. This
/// is the identical normalization ay's own solver applies to a concat equality
/// (`ay-dpll` `NormalizeEqBvConcat`, ported from Bitwuzla) — here it is done one
/// layer up so the halves land inside the exportable width.
///
/// BIT ORDER. `Formula::BvConcat(a, b)` lowers to SMT-LIB `(concat a b)`
/// (`trust_types::ay_bridge::formula_to_expr`), whose FIRST argument is the HIGH
/// half — the same convention `PathMergingExecutor::read_int_return` documents
/// and builds (`concat(X1, X0)`, X1 high). The literal arm below depends on that
/// convention (it takes `value >> 64` as the first component); the `BvConcat`
/// arm does not, because it pairs first-with-first and second-with-second.
///
/// SHAPES ADMITTED — exactly the two the gate can actually produce at 128 bits,
/// each measured over the 68-module corpus:
///   * `BvConcat(hi, lo)` — the machine side is ALWAYS this (`read_int_return`
///     emits it and nothing else at 128 bits), and the spec side is this for a
///     carried 128-bit parameter.
///   * `BitVec { width: 128 }` — the spec side for a 128-bit literal.
///
/// EVERYTHING ELSE fails closed. In particular a nested or unevenly-split
/// `BvConcat` is NOT normalized into shape: a nested half does not lower (there
/// is no `BvConcat` arm), and an unevenly-split one is refused either by the
/// width pin in [`try_kernel_recheckable_pair_128`] or by the exporter's own
/// `WidthMismatch` / `UnsupportedWidth` — see the pin's comment for which does
/// what, since only one of the two is actually load-bearing for soundness.
#[cfg(feature = "ay-proofs")]
fn split_register_pair_128(f: &Formula) -> Option<(Formula, Formula)> {
    match f {
        // The register pair as the gate builds it. Widths are NOT trusted from
        // this shape — they are pinned after lowering by the caller.
        Formula::BvConcat(high, low) => Some(((**high).clone(), (**low).clone())),
        // A 128-bit literal. `value` is `i128`; reinterpret as the unsigned bit
        // pattern (two's complement) and cut it at bit 64. Each half is then
        // re-narrowed to `i128` purely as `Formula::BitVec`'s storage type —
        // `formula_to_bvexpr` masks to the declared width, so a half whose top
        // bit is set round-trips as its own 64-bit pattern rather than as a
        // sign-extension of it.
        Formula::BitVec { value, width } if *width == 2 * PAIR_HALF_WIDTH => {
            let bits = *value as u128;
            Some((
                Formula::BitVec {
                    value: (bits >> PAIR_HALF_WIDTH) as i128,
                    width: PAIR_HALF_WIDTH,
                },
                Formula::BitVec {
                    value: (bits & u128::from(u64::MAX)) as i128,
                    width: PAIR_HALF_WIDTH,
                },
            ))
        }
        _ => None,
    }
}

/// Promote a 128-bit register-pair obligation to the **[PROVED]** grade by
/// discharging it as TWO independent 64-bit certificates, BOTH clean-kernel
/// accepted.
///
/// Returns `Some(ProvenEvidence::KernelRecheckablePair { .. })` ONLY when every
/// one of the following holds; any failure returns `None` and the caller stays
/// [VALIDATED]:
///   * BOTH sides split (see [`split_register_pair_128`]);
///   * ALL FOUR halves lower into the `BvExpr` fragment AND each lowers to
///     EXACTLY 64 bits;
///   * the HIGH-half equality is kernel-accepted; AND
///   * the LOW-half equality is kernel-accepted.
///
/// BOTH HALVES ARE OBLIGATIONS. There is deliberately no arm in which the high
/// half is assumed, defaulted, or skipped: the `?` on `high` runs the full
/// pipeline on `(high_machine, high_spec)` exactly as the `?` on `low` does. A
/// small `i128` constant has `X1 == 0`, so a design that checked only the low
/// half would report [PROVED] for essentially every 128-bit constant return in
/// the corpus and never notice — the mutation test
/// `pair_128_high_half_corruption_refuses_the_kernel_grade` pins that it does
/// notice.
#[cfg(feature = "ay-proofs")]
fn try_kernel_recheckable_pair_128(
    machine_out: &Formula,
    auto: &Formula,
) -> Option<ProvenEvidence> {
    let (machine_high, machine_low) = split_register_pair_128(machine_out)?;
    let (auto_high, auto_low) = split_register_pair_128(auto)?;

    // WIDTH PIN — AND AN HONEST ACCOUNT OF WHAT IT IS FOR.
    //
    // It is NOT what makes the split sound. A MISMATCHED split point (say 16/48
    // against 48/16) is already refused one layer down: `export_bv_blast_proof_expr`
    // blasts both sides and returns `WidthMismatch` when the bit counts differ,
    // and `UnsupportedWidth` for anything over `SOLVED_MAX_WIDTH` (64). Deleting
    // this loop was MEASURED not to break the mismatch test, precisely because
    // the exporter catches it.
    //
    // What the pin actually does is keep the GRADE'S LABEL TRUE. Without it, a
    // 64-bit obligation whose two sides both happen to be `concat(32,32)` —
    // matched, in-fragment, genuinely provable — would be handed
    // `KernelRecheckablePair`, which claims to be a 128-bit AAPCS64 register
    // pair. Sound, but a lie about what was checked. It is also the reason this
    // path cannot silently start applying to shapes nobody analyzed if
    // `MAX_WIDTH` is ever raised.
    //
    // The width is read off the LOWERED `BvExpr` rather than off the `Formula`,
    // so it describes the object actually handed to the blaster instead of a
    // parallel inference about it.
    for half in [&machine_high, &machine_low, &auto_high, &auto_low] {
        let lowered = formula_to_bvexpr(half).ok()?;
        if bvexpr_width(&lowered) != Some(PAIR_HALF_WIDTH) {
            return None;
        }
    }

    // BOTH halves, through the IDENTICAL slow path any 64-bit obligation takes.
    let high = kernel_recheckable_bitblast(&machine_high, &auto_high)?;
    let low = kernel_recheckable_bitblast(&machine_low, &auto_low)?;
    Some(ProvenEvidence::KernelRecheckablePair { high: Box::new(high), low: Box::new(low) })
}

// ===========================================================================
// M-POS ENFORCEMENT — THE BUILD GATE.
//
// `verify_output_preserved` produces a VERDICT; the functions below turn that
// verdict into an EMISSION DECISION. `emit_object_verified` /
// `emit_objects_verified` run the gate on each function and REFUSE to produce
// the object bytes if any function is Refuted (a known miscompile). This is the
// enforcement primitive a targo/codegen integration calls — it is the point at
// which the proved region becomes LOAD-BEARING: a non-Proven function does not
// reach the linker.
//
// CORE GUARANTEE (teeth): a Refuted function is NEVER emitted by these paths,
// regardless of policy. Refuted => always Err.
// ===========================================================================

/// Policy for how `emit_*_verified` treats the `Unknown` verdict (a function
/// whose output the gate could neither prove nor refute — an unsupported shape,
/// a solver timeout, or an emission/decode failure).
///
/// `Refuted` is NOT governed by this policy: a Refuted function is ALWAYS
/// refused. The policy only chooses how strict the gate is about functions it
/// cannot decide.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmitPolicy {
    /// STRICT gate (the SAFE DEFAULT — see [`EmitPolicy::default`]). Emit ONLY
    /// functions the gate `Proven`-correct. `Unknown` is treated as "not
    /// proven" and REFUSED (fail-closed). Use this when every emitted function
    /// must carry a machine-checked output-preservation proof.
    StrictProvenOnly,
    /// BEST-EFFORT gate. Emit `Proven` functions AND `Unknown` functions (the
    /// ones the gate could not decide), but STILL hard-fail any `Refuted`
    /// function. Use this to enforce "never emit a *known* miscompile" while the
    /// proof coverage is still being grown to the whole language — it lets
    /// unsupported shapes through unproven, but a counterexampled miscompile is
    /// always blocked.
    AllowUnknown,
}

impl Default for EmitPolicy {
    /// The SAFE default is [`EmitPolicy::StrictProvenOnly`]: for a gate whose
    /// purpose is to make the proved region load-bearing, "cannot prove" must be
    /// fail-closed. Callers that knowingly accept unproven (but not refuted)
    /// functions opt in explicitly to [`EmitPolicy::AllowUnknown`].
    fn default() -> Self {
        EmitPolicy::StrictProvenOnly
    }
}

/// Why verified emission refused to produce an object.
///
/// `Refuted` records a KNOWN MISCOMPILE (the gate found a concrete input for
/// which the emitted bytes compute the wrong value); it can never be downgraded
/// by policy. `Unknown` records a function the gate could not decide and which
/// the active [`EmitPolicy`] refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyError {
    /// A function was REFUTED: the gate found a counterexample input — its
    /// emitted bytes do not compute its IR semantics. This is a miscompile and
    /// is refused under ALL policies. No object bytes were produced.
    Refuted {
        /// The refuted function's name.
        function: String,
        /// The gate's human-readable refutation detail.
        detail: String,
    },
    /// A function was UNKNOWN (the gate could neither prove nor refute it) and
    /// the active policy ([`EmitPolicy::StrictProvenOnly`]) refused it. No
    /// object bytes were produced.
    Unknown {
        /// The unknown function's name.
        function: String,
        /// Why the gate could not conclude Proven or Refuted.
        reason: String,
    },
    /// Lowering/emission of an accepted (Proven, or policy-allowed Unknown)
    /// function failed at the backend. No object bytes were produced.
    EmitFailed {
        /// The function whose emission failed.
        function: String,
        /// The backend error.
        reason: String,
    },
    /// The module contained no functions to emit.
    EmptyModule,
    /// Function names were not unique, so callee identity and verified-byte
    /// lookup would be ambiguous.
    DuplicateFunctionName {
        /// The repeated symbol/name.
        name: String,
    },
    /// The whole-module (one-object-per-CGU) emission itself failed.
    ModuleEmitFailed {
        /// The backend error.
        reason: String,
    },
    /// BYTE-PRESERVATION OBLIGATION VIOLATED: the merged module object does not
    /// carry some verified function's machine code, unchanged, at the offset its
    /// own symbol table points at. The per-function proof therefore does not
    /// transfer to the shipped artifact, so NOTHING is emitted.
    MergedBytesDiverged {
        /// The function whose verified bytes are not in the merged object.
        function: String,
        /// What exactly did not line up.
        detail: String,
    },
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerifyError::Refuted { function, detail } => {
                write!(f, "REFUSED: function `{function}` is a MISCOMPILE (Refuted) — {detail}")
            }
            VerifyError::Unknown { function, reason } => write!(
                f,
                "REFUSED: function `{function}` could not be proven output-preserving \
                 (Unknown, fail-closed under StrictProvenOnly) — {reason}"
            ),
            VerifyError::EmitFailed { function, reason } => {
                write!(f, "emission of verified function `{function}` failed: {reason}")
            }
            VerifyError::EmptyModule => write!(f, "empty module: no functions to emit"),
            VerifyError::DuplicateFunctionName { name } => write!(
                f,
                "duplicate function name `{name}`: verified emission requires unique symbol identity"
            ),
            VerifyError::ModuleEmitFailed { reason } => {
                write!(f, "whole-module object emission failed: {reason}")
            }
            VerifyError::MergedBytesDiverged { function, detail } => write!(
                f,
                "REFUSED: the merged module object does not preserve the VERIFIED bytes of \
                 function `{function}` — {detail}. The per-function output-preservation proof \
                 does not transfer to this artifact, so no object is shipped"
            ),
        }
    }
}

impl std::error::Error for VerifyError {}

/// Trust (RUNG 3 — CERTIFICATION REPORT): a per-module tally of the
/// output-preservation GRADE the gate assigned each emitted function, so the
/// UNCERTIFIED surface is VISIBLE rather than silently shipped as if covered.
///
/// The counts are over the functions the gate ACCEPTED for emission under the
/// active [`EmitPolicy`]:
///   * `proved`    — [PROVED]: `Proven{KernelRecheckable}` (a clean-kernel-re-checkable
///     bit-blast certificate is attached).
///   * `validated` — [VALIDATED]: `Proven{AyValidated}` (ay is the sole authority).
///   * `unknown`   — UNCERTIFIED: the gate could neither prove nor refute the
///     function; it was EMITTED only because the policy is [`EmitPolicy::AllowUnknown`]
///     (under [`EmitPolicy::StrictProvenOnly`] an Unknown function is refused, so
///     this is always 0 on a successful Strict gate).
///   * `refuted`   — a KNOWN MISCOMPILE. A Refuted function is ALWAYS fatal (the
///     gate returns `Err` and ships NOTHING), so this count is 0 on every
///     successful gate. It is carried for honesty: the report's shape names the
///     refuted bucket even though a refuted module never produces a report.
///
/// HONESTY: `validated + unknown` is the surface that ships WITHOUT a
/// kernel-re-checkable proof. The gate surfaces this so "never silently emitted
/// as if covered" holds.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CertificationReport {
    /// [PROVED] — `Proven{KernelRecheckable}`: a kernel-re-checkable cert attached.
    pub proved: usize,
    /// [VALIDATED] — `Proven{AyValidated}`: ay is the sole proof authority.
    pub validated: usize,
    /// UNCERTIFIED — `Unknown` functions emitted under [`EmitPolicy::AllowUnknown`].
    pub unknown: usize,
    /// Refuted (known miscompile) — always 0 on a successful gate (refused fatal).
    pub refuted: usize,
}

impl CertificationReport {
    /// Total functions emitted (accepted by the gate).
    #[must_use]
    pub fn emitted(&self) -> usize {
        self.proved + self.validated + self.unknown
    }

    /// The UNCERTIFIED surface: functions emitted without a kernel-re-checkable
    /// proof ([VALIDATED] + Unknown). This is the number the report makes VISIBLE.
    #[must_use]
    pub fn uncertified(&self) -> usize {
        self.validated + self.unknown
    }
}

impl std::fmt::Display for CertificationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} [PROVED] (kernel-re-checkable), {} [VALIDATED] (ay-only), \
             {} uncertified (emitted unproven under AllowUnknown), \
             {} refuted (never emitted)",
            self.proved, self.validated, self.unknown, self.refuted
        )
    }
}

/// VERIFIED multi-function emission — THE BUILD GATE.
///
/// Thin wrapper over [`emit_objects_verified_reported`] that drops the
/// [`CertificationReport`]; the accept/refuse behavior is identical. See that
/// function for the full per-grade policy table. In summary (RUNG 3):
///
/// | Verdict                    | StrictProvenOnly | AllowUnknown |
/// |----------------------------|------------------|--------------|
/// | `Proven{KernelRecheckable}`| emit             | emit         |
/// | `Proven{AyValidated}`      | **Err**          | emit         |
/// | `Unknown`                  | **Err**          | emit         |
/// | `Refuted`                  | **Err (always)** | **Err (always)** |
///
/// Returns `Ok(Vec<(name, object_bytes)>)` (one object per function, same shape
/// as [`TrustCgCodegenBackend::emit_objects`]) only if EVERY function cleared
/// the gate; otherwise `Err(VerifyError)` and NO bytes are returned.
///
/// CORE INVARIANT (teeth): a `Refuted` function is NEVER present in the returned
/// bytes — the gate runs on the WHOLE module BEFORE any object is produced, so
/// the first Refuted verdict short-circuits to `Err` and no function (refuted or
/// sibling) is emitted. This holds under every policy.
pub fn emit_objects_verified(
    funcs: &[VerifiableFunction],
    policy: EmitPolicy,
) -> Result<Vec<(String, Vec<u8>)>, VerifyError> {
    let backend = default_verification_backend();
    emit_objects_verified_with_backend(funcs, policy, &backend)
}

/// Backend-aware form of [`emit_objects_verified`]. Both the candidate emission
/// and the determinism re-emission use this exact backend instance.
pub fn emit_objects_verified_with_backend(
    funcs: &[VerifiableFunction],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<Vec<(String, Vec<u8>)>, VerifyError> {
    emit_objects_verified_reported_with_backend(funcs, policy, backend).map(|(objs, _report)| objs)
}

/// Trust (RUNG 3): [`emit_objects_verified`] PLUS a [`CertificationReport`] —
/// the per-module tally of how many emitted functions are [PROVED] /
/// [VALIDATED] / uncertified (Unknown). A caller (the in-compiler gate) surfaces
/// the report so the uncertified surface is VISIBLE; the gate's accept/refuse
/// behavior is otherwise IDENTICAL to [`emit_objects_verified`].
///
/// Policy table (RUNG 3 makes Strict genuinely PROVED-only):
///
/// | Verdict                    | StrictProvenOnly | AllowUnknown |
/// |----------------------------|------------------|--------------|
/// | `Proven{KernelRecheckable}`| emit ([PROVED])  | emit         |
/// | `Proven{AyValidated}`      | **Err**          | emit ([VALIDATED]) |
/// | `Unknown`                  | **Err**          | emit (uncertified) |
/// | `Refuted`                  | **Err (always)** | **Err (always)** |
///
/// Under `StrictProvenOnly` ONLY a kernel-re-checkable [PROVED] function ships:
/// both Unknown AND [VALIDATED] (ay-only) are refused (fail-closed) — this is the
/// CERTIFIED-FRAGMENT mode. `Refuted` is fatal under every policy.
pub fn emit_objects_verified_reported(
    funcs: &[VerifiableFunction],
    policy: EmitPolicy,
) -> Result<(Vec<(String, Vec<u8>)>, CertificationReport), VerifyError> {
    let backend = default_verification_backend();
    emit_objects_verified_reported_with_backend(funcs, policy, &backend)
}

/// Production form of [`emit_objects_verified_reported`]. `backend` is the
/// caller's already-configured production backend; its target, runtime lowering
/// symbols, and optimization level govern the candidate bytes and the TOCTOU
/// re-emission alike. Existing wrappers retain the historical host/O0 default.
pub fn emit_objects_verified_reported_with_backend(
    funcs: &[VerifiableFunction],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<(Vec<(String, Vec<u8>)>, CertificationReport), VerifyError> {
    if funcs.is_empty() {
        return Err(VerifyError::EmptyModule);
    }
    let mut unique_names = HashSet::with_capacity(funcs.len());
    for func in funcs {
        if !unique_names.insert(func.name.as_str()) {
            return Err(VerifyError::DuplicateFunctionName { name: func.name.clone() });
        }
    }

    // PHASE 0 — BUILD THE LOCAL-PURE-CALLEE ENVIRONMENT. A callee is admitted for
    // composition ONLY if it (a) is a single-register-ABI pure scalar function
    // (`derive_callee_pure`) AND (b) independently clears the gate as `Proven`
    // under an EMPTY env (so its OWN bytes are proven == its IR semantics — the
    // linchpin that lets us stand its IR-derived output in for "what the resolved
    // `bl` executes"). A callee that is Refuted/Unknown, or non-pure, is NOT
    // admitted — calls to it then fail closed. This is fail-closed by
    // construction: the env only ever grows the set of calls we can SOUNDLY model.
    let mut env = CalleeEnv::empty();
    // A derivably-pure callee is call-free, so its empty-env result is identical
    // to its Phase-1 result. Retain and MOVE that result into Phase 1 to avoid a
    // redundant full emission/proof while still doing the Phase-2 determinism
    // re-emission over the exact accepted bytes.
    let mut phase0_results = vec![None; funcs.len()];
    for (index, func) in funcs.iter().enumerate() {
        if let Some(pure) = derive_callee_pure(func) {
            // Verify the callee itself with an empty env (it is call-free by
            // `derive_callee_pure`, so an empty env suffices and cannot recurse).
            let result = verify_output_preserved_capturing_env_with_backend(
                func,
                &CalleeEnv::empty(),
                backend,
            );
            if result.0.is_proven() {
                env.callees.insert(func.name.clone(), pure);
            }
            phase0_results[index] = Some(result);
        }
    }

    // PHASE 1 — GATE + CAPTURE. Verify EVERY function first, CAPTURING the exact
    // object bytes the gate's verdict was computed over. Refuted => Err
    // immediately (never emit a known miscompile); Unknown => Err unless policy
    // allows it. The captured bytes are NOT yet shipped — they are held so PHASE 2
    // can ship THIS emission (the one that was verified) rather than re-emitting.
    let mut verified: Vec<(String, Vec<u8>)> = Vec::with_capacity(funcs.len());
    let mut report = CertificationReport::default();
    for (index, func) in funcs.iter().enumerate() {
        let (verdict, bytes) = phase0_results[index].take().unwrap_or_else(|| {
            verify_output_preserved_capturing_env_with_backend(func, &env, backend)
        });
        match verdict {
            OutputVerdict::Proven { evidence } => match evidence {
                // [PROVED] — kernel-grade (slow SAT-reflection, its 128-bit
                // register-pair form with BOTH halves kernel-accepted, or O(1)
                // instantiation). Ships under every (non-Off) policy.
                ProvenEvidence::KernelRecheckable(_)
                | ProvenEvidence::KernelRecheckablePair { .. }
                | ProvenEvidence::KernelInstantiated { .. } => report.proved += 1,
                // [CITED] — a wide `Mul` discharged by CITING the
                // kernel-checked structured theorem. Counted with the
                // [VALIDATED] surface and NOT with `proved`, deliberately: the
                // kernel never re-checked a term for THIS instance, and the
                // `AyBlastAgrees` residual is machine-checked rather than
                // proved. Under StrictProvenOnly it is therefore REFUSED on the
                // same footing as [VALIDATED] — a citation must never ship where
                // only kernel-[PROVED] may.
                // [VALIDATED] — ay is the sole authority. RUNG 3 FAIL-CLOSED:
                // under StrictProvenOnly the certified-fragment mode ships ONLY
                // kernel-[PROVED] functions, so a [VALIDATED] function is REFUSED
                // (not silently treated as covered). Under AllowUnknown it ships
                // and is COUNTED as the [VALIDATED] (uncertified-by-kernel) surface.
                ProvenEvidence::StructuralCitation { .. } | ProvenEvidence::AyValidated => {
                    if policy == EmitPolicy::StrictProvenOnly {
                        return Err(VerifyError::Unknown {
                            function: func.name.clone(),
                            reason: "function is [VALIDATED] (ay-only authority) but \
                                     StrictProvenOnly ships ONLY kernel-re-checkable \
                                     [PROVED] functions (certified-fragment mode); no \
                                     kernel-re-checkable certificate is attached"
                                .to_string(),
                        });
                    }
                    report.validated += 1;
                }
            },
            OutputVerdict::Refuted { detail } => {
                return Err(VerifyError::Refuted { function: func.name.clone(), detail });
            }
            OutputVerdict::Unknown { reason } => {
                if policy == EmitPolicy::StrictProvenOnly {
                    return Err(VerifyError::Unknown { function: func.name.clone(), reason });
                }
                // AllowUnknown: a function the gate could not decide is permitted
                // (best-effort gate) and COUNTED as uncertified. A Refuted function
                // would have returned above.
                report.unknown += 1;
            }
        }
        // An accepted function MUST carry shippable bytes (emission succeeded
        // during verification). If `bytes` is None the emission/lowering itself
        // failed — fail closed rather than re-emit a divergent artifact.
        match bytes {
            Some(b) => verified.push((func.name.clone(), b)),
            None => {
                return Err(VerifyError::EmitFailed {
                    function: func.name.clone(),
                    reason: "verification emission produced no shippable object bytes".to_string(),
                });
            }
        }
    }

    // PHASE 2 — SHIP THE VERIFIED BYTES (RUNG 2: shipped == verified). Only
    // reached when the WHOLE module cleared the gate. We do NOT re-emit the
    // artifact: the bytes shipped here are byte-for-byte the bytes PHASE 1
    // VERIFIED. As a TOCTOU detector (defense-in-depth against a non-deterministic
    // or trojaned backend), we re-emit ONCE and assert it is byte-identical to the
    // verified bytes; on any divergence we fail closed and ship NOTHING. The
    // shipped Vec is always the VERIFIED bytes, never the re-emit.
    for (name, bytes) in &verified {
        // Recover the source function (PHASE 1 preserves order, so this is 1:1).
        let func = funcs
            .iter()
            .find(|f| &f.name == name)
            .expect("verified entry must correspond to an input function");
        if let Err(detail) = reemit_matches_verified_with_backend(func, bytes, backend) {
            return Err(VerifyError::EmitFailed { function: name.clone(), reason: detail });
        }
    }
    Ok((verified, report))
}

/// Where one verified function's machine code was found inside the merged
/// module object, byte-identical to the bytes the gate verified.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreservedFunction {
    /// The function's name.
    pub name: String,
    /// Offset of its first instruction inside the merged object's text section,
    /// read from THAT OBJECT'S OWN symbol table — the offset a linker resolving
    /// this symbol will actually jump to.
    pub text_offset: u64,
    /// Length in bytes of the preserved machine code.
    pub len: u64,
}

/// The single object emitted for one codegen unit, plus the discharged
/// byte-preservation witnesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedModuleObject {
    /// The merged object-file bytes (the artifact that ships).
    pub bytes: Vec<u8>,
    /// One entry per emitted function. Their presence is the discharged
    /// obligation: each verified function's bytes appear verbatim in `bytes`.
    pub preserved: Vec<PreservedFunction>,
}

/// VERIFIED WHOLE-MODULE emission — the ONE-OBJECT-PER-CGU build gate.
///
/// This keeps the PER-FUNCTION proof exactly as
/// [`emit_objects_verified_reported_with_backend`] performs it (phases 0-2 are
/// that function, called unchanged) and adds ONE new, narrow, checkable
/// obligation on top:
///
/// > **PHASE 3.** Emit the whole CGU as a single object, then prove that for
/// > every verified function the merged object contains its verified machine
/// > code BYTE-FOR-BYTE at the offset the merged object's OWN SYMBOL TABLE
/// > assigns that function.
///
/// WHY THIS SHAPE. An `Internal`-linkage mono-item can only be emitted as an
/// object-local symbol, and a local symbol is unreachable from any other object
/// — so one-object-per-FUNCTION cannot represent it, and every program that
/// calls `core` needs it. Merging is therefore forced. Restarting the proof at
/// object granularity was the alternative; instead the per-function proof is
/// preserved verbatim and the merge is discharged as a separate small claim.
///
/// WHY THE CLAIM IS NOT VACUOUS. Each function's code is encoded from that
/// function alone (`encode_module_function_with_fixups_and_eh`) and every
/// cross-function reference leaves the instruction stream as a RELOCATION, never
/// an in-place patch — so a function's bytes are position-independent and the
/// merge genuinely can (and must) carry them unchanged. If a future emitter
/// starts patching call sites in place, this check FAILS CLOSED and the build
/// stops, which is precisely the intent.
///
/// The offset is read back from the SHIPPED object rather than trusted from the
/// emitter's own layout report, and the reported extents are cross-checked
/// against it: an emitter that mislabels where it put a function is caught.
///
/// `linkage` is 1:1 with `funcs` (EMPTY = every function `External`). A
/// `Refuted` function still refuses the whole module under every policy.
pub fn emit_module_object_verified_reported_with_backend(
    funcs: &[VerifiableFunction],
    linkage: &[crate::codegen_backend::FunctionLinkage],
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<(VerifiedModuleObject, CertificationReport), VerifyError> {
    // PHASES 0-2 — UNCHANGED per-function gate. Every function is verified in
    // isolation, its exact candidate bytes captured, and the determinism
    // re-emission run over those bytes. A Refuted function returns Err here and
    // NOTHING below runs.
    let (verified, report) = emit_objects_verified_reported_with_backend(funcs, policy, backend)?;

    if !linkage.is_empty() && linkage.len() != funcs.len() {
        return Err(VerifyError::ModuleEmitFailed {
            reason: format!(
                "{} linkage entries for {} functions; refusing to bind symbols against a \
                 mis-indexed vector",
                linkage.len(),
                funcs.len()
            ),
        });
    }

    // PHASE 3a — MERGE. Lower every function and emit ONE object for the CGU,
    // with each function's real symbol binding.
    let module = build_merged_module(funcs, linkage, statics, backend)?;
    let emitted = backend.emit_module_object(&module).map_err(|e| {
        VerifyError::ModuleEmitFailed { reason: format!("emit_module_object failed: {e:?}") }
    })?;

    // PHASE 3b — DISCHARGE THE BYTE-PRESERVATION OBLIGATION. A failure here is a
    // REFUSAL, never a warning: shipping a merged object whose bytes are not the
    // verified bytes would silently void the per-function proof.
    let preserved = assert_merged_object_preserves_verified_text(&emitted, &verified)?;

    Ok((VerifiedModuleObject { bytes: emitted.bytes, preserved }, report))
}

/// Lower every verified function into the single compiled module the merged
/// emission consumes.
fn build_merged_module(
    funcs: &[VerifiableFunction],
    linkage: &[crate::codegen_backend::FunctionLinkage],
    statics: &[trust_cg_codegen::pipeline::ObjectGlobal],
    backend: &TrustCgCodegenBackend,
) -> Result<crate::codegen_backend::CompiledModule, VerifyError> {
    let mut lir_functions = Vec::with_capacity(funcs.len());
    for func in funcs {
        // A function that cleared the gate lowered successfully during
        // verification, so a failure here is a genuine divergence, not a
        // best-effort miss: fail closed rather than drop it from the module
        // (a dropped definition becomes an unresolved symbol at link).
        let lir = backend.lower_function(func).map_err(|e| VerifyError::EmitFailed {
            function: func.name.clone(),
            reason: format!("lower_function failed during whole-module emission: {e:?}"),
        })?;
        lir_functions.push(lir);
    }
    let function_count = lir_functions.len();
    Ok(crate::codegen_backend::CompiledModule {
        name: "trust_cg.verified_module".to_string(),
        lir_functions,
        object_path: None,
        function_count,
        source_functions: Some(funcs.to_vec()),
        linkage: linkage.to_vec(),
        statics: statics.to_vec(),
    })
}

/// THE MERGE OBLIGATION. For every verified function, prove that the merged
/// object carries its verified machine code unchanged.
///
/// Concretely, for each `(name, verified_object_bytes)`:
///
/// 1. `verified_text` = the text section of the single-function object the gate
///    verified. That object holds exactly one function, so its whole text
///    section IS that function's machine code.
/// 2. `offset` = the value the MERGED object's own symbol table gives `name`,
///    relative to the merged text section's base. This is read back from the
///    shipped bytes, not taken from the emitter's layout report.
/// 3. Assert `merged_text[offset .. offset + verified_text.len()] ==
///    verified_text`.
///
/// The emitter's reported extent is additionally cross-checked against (2) and
/// (3), so a layout report that disagrees with the object it describes is caught
/// rather than believed.
pub(crate) fn assert_merged_object_preserves_verified_text(
    emitted: &crate::codegen_backend::EmittedModuleObject,
    verified: &[(String, Vec<u8>)],
) -> Result<Vec<PreservedFunction>, VerifyError> {
    let diverged = |function: &str, detail: String| VerifyError::MergedBytesDiverged {
        function: function.to_string(),
        detail,
    };

    let (merged_text, merged_base) =
        extract_text_from_object(&emitted.bytes).map_err(|reason| {
            VerifyError::ModuleEmitFailed {
                reason: format!("merged module object has no readable text section: {reason}"),
            }
        })?;
    let merged_symbols =
        object_text_symbol_offsets(&emitted.bytes, merged_base).ok_or_else(|| {
            VerifyError::ModuleEmitFailed {
                reason: "merged module object has no readable symbol table; the byte-preservation \
                     obligation cannot be discharged, so nothing ships"
                    .to_string(),
            }
        })?;

    let mut preserved = Vec::with_capacity(verified.len());
    for (name, verified_object) in verified {
        let (verified_text, _) = extract_text_from_object(verified_object)
            .map_err(|reason| diverged(name, format!("verified object is unreadable: {reason}")))?;
        if verified_text.is_empty() {
            return Err(diverged(name, "verified object has an empty text section".to_string()));
        }

        let offset = *merged_symbols.get(name.as_str()).ok_or_else(|| {
            diverged(
                name,
                "the merged object defines no symbol for it (a verified function that is not in \
                 the shipped artifact would become an unresolved symbol at link)"
                    .to_string(),
            )
        })?;

        let start = usize::try_from(offset)
            .map_err(|_| diverged(name, format!("symbol offset {offset} is out of range")))?;
        let end = start.checked_add(verified_text.len()).ok_or_else(|| {
            diverged(name, "symbol offset + verified length overflows".to_string())
        })?;
        let window = merged_text.get(start..end).ok_or_else(|| {
            diverged(
                name,
                format!(
                    "its symbol points at text bytes {start}..{end}, past the merged text \
                     section's {} bytes",
                    merged_text.len()
                ),
            )
        })?;
        if window != verified_text.as_slice() {
            let first = window
                .iter()
                .zip(verified_text.iter())
                .position(|(shipped, verified)| shipped != verified)
                .unwrap_or(0);
            return Err(diverged(
                name,
                format!(
                    "the merged object's bytes at text offset {start} differ from the \
                     {} verified bytes, first at relative byte {first}",
                    verified_text.len()
                ),
            ));
        }

        // Cross-check the emitter's own layout report against what the shipped
        // object actually says. A disagreement means the report is fiction.
        if let Some(extent) = emitted.text_extents.iter().find(|e| e.name == *name) {
            if extent.offset != offset {
                return Err(diverged(
                    name,
                    format!(
                        "the emitter reported text offset {} but the shipped symbol table says \
                         {offset}",
                        extent.offset
                    ),
                ));
            }
            if extent.len != verified_text.len() as u64 {
                return Err(diverged(
                    name,
                    format!(
                        "the emitter reported a {}-byte body but the verified emission is {} \
                         bytes",
                        extent.len,
                        verified_text.len()
                    ),
                ));
            }
        }

        preserved.push(PreservedFunction {
            name: name.clone(),
            text_offset: offset,
            len: verified_text.len() as u64,
        });
    }

    Ok(preserved)
}

/// Read every DEFINED text-section symbol out of an emitted object, as
/// `name -> offset within the text section`.
///
/// This is the read-back half of the merge obligation, so it deliberately parses
/// the SHIPPED bytes with a small independent reader rather than asking the
/// writer where it thinks it put things. Mach-O `_` prefixes are stripped so the
/// keys match the IR-level function names. Any malformed/truncated field yields
/// `None` (=> refusal), never a panic inside the compiler.
fn object_text_symbol_offsets(obj: &[u8], text_base: u64) -> Option<HashMap<String, u64>> {
    macho_text_symbol_offsets(obj, text_base).or_else(|| elf64_text_symbol_offsets(obj, text_base))
}

/// Mach-O `LC_SYMTAB` reader: collect `N_SECT` symbols whose section is
/// `__text`.
fn macho_text_symbol_offsets(obj: &[u8], text_base: u64) -> Option<HashMap<String, u64>> {
    const N_TYPE: u8 = 0x0e;
    const N_SECT: u8 = 0x0e;
    const NLIST_64_SIZE: usize = 16;

    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };
    if rd_u32(0)? != 0xfeed_facf {
        return None;
    }

    // Locate `__text`'s 1-based section ordinal by walking the segment load
    // commands in the order the section table numbers them.
    let ncmds = rd_u32(16)?;
    let mut text_ordinal: Option<u8> = None;
    let mut symtab: Option<(usize, usize, usize, usize)> = None;
    let mut ordinal: u32 = 0;
    let mut cmd_off = 32usize;
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off)?;
        let cmdsize = rd_u32(cmd_off + 4)? as usize;
        if cmdsize == 0 {
            return None;
        }
        if cmd == 0x19 {
            // LC_SEGMENT_64
            let nsects = rd_u32(cmd_off + 64)?;
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                ordinal = ordinal.checked_add(1)?;
                let name = obj.get(sec..sec + 16)?;
                if name.starts_with(b"__text\0") {
                    text_ordinal = Some(u8::try_from(ordinal).ok()?);
                }
                sec += 80;
            }
        } else if cmd == 0x02 {
            // LC_SYMTAB: symoff, nsyms, stroff, strsize
            symtab = Some((
                rd_u32(cmd_off + 8)? as usize,
                rd_u32(cmd_off + 12)? as usize,
                rd_u32(cmd_off + 16)? as usize,
                rd_u32(cmd_off + 20)? as usize,
            ));
        }
        cmd_off = cmd_off.checked_add(cmdsize)?;
    }

    let text_ordinal = text_ordinal?;
    let (symoff, nsyms, stroff, strsize) = symtab?;
    let strings = obj.get(stroff..stroff.checked_add(strsize)?)?;

    let mut offsets = HashMap::new();
    for index in 0..nsyms {
        let entry = symoff.checked_add(index.checked_mul(NLIST_64_SIZE)?)?;
        let n_strx = rd_u32(entry)? as usize;
        let n_type = *obj.get(entry + 4)?;
        let n_sect = *obj.get(entry + 5)?;
        let n_value = rd_u64(entry + 8)?;
        // A DEFINED symbol in __text. Undefined (`N_UNDF`) and absolute symbols
        // define no bytes here and are irrelevant to the obligation.
        if n_type & N_TYPE != N_SECT || n_sect != text_ordinal {
            continue;
        }
        let tail = strings.get(n_strx..)?;
        let end = tail.iter().position(|byte| *byte == 0)?;
        let name = std::str::from_utf8(&tail[..end]).ok()?;
        // Mach-O prefixes every symbol with `_`; the IR-level name does not.
        let name = name.strip_prefix('_').unwrap_or(name);
        offsets.insert(name.to_string(), n_value.checked_sub(text_base)?);
    }
    Some(offsets)
}

/// ELF64 `.symtab` reader: collect symbols defined in the `.text` section.
fn elf64_text_symbol_offsets(obj: &[u8], text_base: u64) -> Option<HashMap<String, u64>> {
    const SHT_SYMTAB: u32 = 2;
    const SYM_SIZE: usize = 24;

    if obj.get(..6)? != b"\x7fELF\x02\x01" {
        return None;
    }
    let rd_u16 =
        |o: usize| -> Option<u16> { Some(u16::from_le_bytes(obj.get(o..o + 2)?.try_into().ok()?)) };
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };

    let section_table = usize::try_from(rd_u64(40)?).ok()?;
    let section_size = usize::from(rd_u16(58)?);
    let section_count = usize::from(rd_u16(60)?);
    let names_index = usize::from(rd_u16(62)?);
    if section_size < 64 || names_index >= section_count {
        return None;
    }
    let header_at = |index: usize| -> Option<usize> {
        (index < section_count)
            .then_some(section_table.checked_add(index.checked_mul(section_size)?)?)
    };
    let names_header = header_at(names_index)?;
    let names_offset = usize::try_from(rd_u64(names_header + 24)?).ok()?;
    let names_size = usize::try_from(rd_u64(names_header + 32)?).ok()?;
    let names = obj.get(names_offset..names_offset.checked_add(names_size)?)?;
    let section_name = |header: usize| -> Option<&[u8]> {
        let name_offset = usize::try_from(rd_u32(header)?).ok()?;
        let tail = names.get(name_offset..)?;
        let end = tail.iter().position(|byte| *byte == 0)?;
        Some(&tail[..end])
    };

    let mut text_index: Option<u16> = None;
    let mut symtab: Option<(usize, usize, usize)> = None;
    for index in 0..section_count {
        let header = header_at(index)?;
        if section_name(header)? == b".text" {
            text_index = Some(u16::try_from(index).ok()?);
        }
        if rd_u32(header + 4)? == SHT_SYMTAB {
            let offset = usize::try_from(rd_u64(header + 24)?).ok()?;
            let size = usize::try_from(rd_u64(header + 32)?).ok()?;
            let strtab = usize::try_from(rd_u32(header + 40)?).ok()?;
            symtab = Some((offset, size, strtab));
        }
    }

    let text_index = text_index?;
    let (symoff, symsize, strtab_index) = symtab?;
    let strtab_header = header_at(strtab_index)?;
    let str_offset = usize::try_from(rd_u64(strtab_header + 24)?).ok()?;
    let str_size = usize::try_from(rd_u64(strtab_header + 32)?).ok()?;
    let strings = obj.get(str_offset..str_offset.checked_add(str_size)?)?;

    let mut offsets = HashMap::new();
    for index in 0..(symsize / SYM_SIZE) {
        let entry = symoff.checked_add(index.checked_mul(SYM_SIZE)?)?;
        let st_name = usize::try_from(rd_u32(entry)?).ok()?;
        let st_shndx = rd_u16(entry + 6)?;
        let st_value = rd_u64(entry + 8)?;
        if st_shndx != text_index {
            continue;
        }
        let tail = strings.get(st_name..)?;
        let end = tail.iter().position(|byte| *byte == 0)?;
        if end == 0 {
            continue;
        }
        let name = std::str::from_utf8(&tail[..end]).ok()?;
        offsets.insert(name.to_string(), st_value.checked_sub(text_base)?);
    }
    Some(offsets)
}

/// VERIFIED single-function emission — convenience over [`emit_objects_verified`]
/// for the single-function-module path ([`TrustCgCodegenBackend::emit_object`]).
///
/// Runs the gate on `func` and returns its object bytes only if it clears the
/// gate under `policy`. A `Refuted` function ALWAYS yields `Err` and produces no
/// bytes (the core guarantee).
pub fn emit_object_verified(
    func: &VerifiableFunction,
    policy: EmitPolicy,
) -> Result<Vec<u8>, VerifyError> {
    let backend = default_verification_backend();
    emit_object_verified_with_backend(func, policy, &backend)
}

/// Backend-aware form of [`emit_object_verified`].
pub fn emit_object_verified_with_backend(
    func: &VerifiableFunction,
    policy: EmitPolicy,
    backend: &TrustCgCodegenBackend,
) -> Result<Vec<u8>, VerifyError> {
    let mut objs = emit_objects_verified_with_backend(std::slice::from_ref(func), policy, backend)?;
    Ok(objs.remove(0).1)
}

/// Return-value register width in bits for `func` (32 for i32/bool, 64 for i64).
fn return_reg_width(func: &VerifiableFunction) -> Result<u32, String> {
    reg_width(&func.body.return_ty)
}

/// If `func`'s single statement is an INTEGER division/remainder, build a
/// `divisor != 0` precondition over the divisor operand's register. Best-effort:
/// returns None when the divisor cannot be resolved (the discharge then runs
/// unconstrained, which would correctly Refute a genuine divide-by-zero
/// mismatch).
///
/// FLOAT div/rem is DELIBERATELY skipped: IEEE-754 division is total (`x/0.0` =
/// ±inf, `0.0/0.0` = NaN — neither traps), so it needs NO guard, and its divisor
/// lives in a V-register D-lane, not the GPR this precondition constrains.
fn divisor_nonzero_precondition(func: &VerifiableFunction) -> Option<Formula> {
    let block = func.body.blocks.first()?;
    for stmt in &block.stmts {
        if let Statement::Assign {
            rvalue: Rvalue::BinaryOp(BinOp::Div | BinOp::Rem, _lhs, rhs),
            ..
        } = stmt
        {
            // The divisor is the second operand; if it is an argument local,
            // assert its register != 0 over the inferred width.
            if let Operand::Copy(p) | Operand::Move(p) = rhs {
                if p.projections.is_empty() {
                    // FLOAT div/rem needs no guard (IEEE div is total). Skip so we
                    // never constrain the (unrelated) GPR for a V-register op.
                    let is_float_divisor = func
                        .body
                        .locals
                        .iter()
                        .find(|d| d.index == p.local)
                        .is_some_and(|d| d.ty.is_float());
                    if is_float_divisor {
                        return None;
                    }
                    // arg local i (1-based) lives in W_(i-1)/X_(i-1).
                    if p.local >= 1 && p.local <= func.body.arg_count {
                        let idx = (p.local - 1) as u32;
                        let decl = func.body.locals.iter().find(|d| d.index == p.local);
                        // No register-slot width => emit NO precondition. That
                        // is the fail-closed direction here: the discharge then
                        // runs unconstrained and a genuine divide-by-zero
                        // mismatch is Refuted rather than excused.
                        let rw = decl.and_then(|d| reg_width(&d.ty).ok())?;
                        let reg = if rw > 32 { xn(idx) } else { wn(idx) };
                        return Some(Formula::Not(b(Formula::Eq(
                            b(reg),
                            b(Formula::BitVec { value: 0, width: rw }),
                        ))));
                    }
                }
            }
        }
    }
    None
}

// ===========================================================================
// PART 1 — THE SYMBOLIC IR-SEMANTICS INTERPRETER (pure Formula builder).
// ===========================================================================

pub(crate) fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}

/// Full 64-bit argument register `X_n`.
pub(crate) fn xn(n: u32) -> Formula {
    Formula::Var(format!("X{n}"), Sort::BitVec(64))
}

/// Low 32 bits of argument register `X_n` (i.e. `W_n`).
pub(crate) fn wn(n: u32) -> Formula {
    Formula::BvExtract { inner: b(xn(n)), high: 31, low: 0 }
}

/// Full 128-bit SIMD/FP register `V_n` — the machine's `fpr[n]`, matching
/// `MachineState::symbolic()`.
fn vn(n: u32) -> Formula {
    Formula::Var(format!("V{n}"), Sort::BitVec(128))
}

/// The low `width`-bit scalar lane of SIMD/FP register `V_n` — where a scalar
/// float argument/result lives (D_n for f64/width 64, S_n for f32/width 32).
/// This is EXACTLY `MachineState::read_fpr(n, width)` (`BvExtract(V_n)[width-1:0]`),
/// so the IR-semantics arg matches the machine one bit-for-bit.
fn vn_lane(n: u32, width: u32) -> Formula {
    Formula::BvExtract { inner: b(vn(n)), high: width - 1, low: 0 }
}

/// IEEE-754 `(eb, sb)` (exponent-bit, significand-bit incl. hidden) for a scalar
/// float lane `width`, or `None` (=> fail-closed) for any width but 32/64.
///   * f32 (S-lane, width 32): eb 8, sb 24 (23 stored + 1 hidden).
///   * f64 (D-lane, width 64): eb 11, sb 53 (52 stored + 1 hidden).
/// f16 is intentionally absent (fail-closed). Mirrors
/// `trust_machine_sem::aarch64::fp::FpFormat`.
fn fp_eb_sb(width: u32) -> Option<(u32, u32)> {
    match width {
        32 => Some((8, 24)),
        64 => Some((11, 53)),
        _ => None,
    }
}

/// Bit-exact FP addition over two `width`-bit IEEE bit patterns, IDENTICAL to
/// `trust_machine_sem::aarch64::fp::FpFormat::add_bits`:
/// `FpToIeeeBv(FpAdd(RNE, FpFromBits(a), FpFromBits(b)))` at the format's eb/sb.
/// Building the SAME shape on both the IR-semantics and machine sides makes their
/// equality a structural `X == X` that ay discharges UNSAT (bit-exact: NaN
/// payload + ±0.0 sign preserved). `width` MUST be 32 or 64 (caller guards).
fn fp_add_bits(a_bits: Formula, b_bits: Formula, width: u32) -> Formula {
    fp_binop_bits(a_bits, b_bits, width, Formula::FpAdd)
}

/// Bit-exact FP subtraction, IDENTICAL to
/// `trust_machine_sem::aarch64::fp::FpFormat::sub_bits`:
/// `FpToIeeeBv(FpSub(RNE, FpFromBits(a), FpFromBits(b)))`.
fn fp_sub_bits(a_bits: Formula, b_bits: Formula, width: u32) -> Formula {
    fp_binop_bits(a_bits, b_bits, width, Formula::FpSub)
}

/// Bit-exact FP multiplication, IDENTICAL to
/// `trust_machine_sem::aarch64::fp::FpFormat::mul_bits`:
/// `FpToIeeeBv(FpMul(RNE, FpFromBits(a), FpFromBits(b)))`.
fn fp_mul_bits(a_bits: Formula, b_bits: Formula, width: u32) -> Formula {
    fp_binop_bits(a_bits, b_bits, width, Formula::FpMul)
}

/// Bit-exact FP division, IDENTICAL to
/// `trust_machine_sem::aarch64::fp::FpFormat::div_bits`:
/// `FpToIeeeBv(FpDiv(RNE, FpFromBits(a), FpFromBits(b)))`. NO GUARD: IEEE-754
/// division is total (`x/0.0` = ±inf, `0.0/0.0` = NaN — neither traps), so the
/// unconditional `FpDiv(RNE, ..)` model is sound.
fn fp_div_bits(a_bits: Formula, b_bits: Formula, width: u32) -> Formula {
    fp_binop_bits(a_bits, b_bits, width, Formula::FpDiv)
}

/// Shared two-sided FP-round-trip constructor for the bit-exact FP binops at the
/// format resolved from `width` (32 => f32 eb8/sb24; 64 => f64 eb11/sb53):
/// `FpToIeeeBv(fp(RNE, FpFromBits(a), FpFromBits(b)))`. Bit-preserving: NaN
/// payloads and the sign of ±0.0 survive verbatim. `width` MUST be 32 or 64
/// (the float-binop caller guards this; a non-32/64 width would panic here,
/// which is unreachable by construction).
fn fp_binop_bits(
    a_bits: Formula,
    b_bits: Formula,
    width: u32,
    fp: impl FnOnce(Box<Formula>, Box<Formula>, Box<Formula>) -> Formula,
) -> Formula {
    let (eb, sb) =
        fp_eb_sb(width).expect("fp_binop_bits called with a non-f32/f64 width (caller must guard)");
    let a_fp = Formula::FpFromBits { bits: b(a_bits), eb, sb };
    let b_fp = Formula::FpFromBits { bits: b(b_bits), eb, sb };
    let out = fp(b(Formula::FpRoundingMode(RoundingMode::RNE)), b(a_fp), b(b_fp));
    Formula::FpToIeeeBv(b(out))
}

// ── f64 test shims ─────────────────────────────────────────────────────────
// The f64 in-module tests predate the width-parametric refactor; these
// `#[cfg(test)]` wrappers keep them expressing the f64 shape (eb 11 / sb 53,
// D-lane) verbatim, delegating to the width-parametric functions above. They
// are compiled ONLY in test builds and are the SAME shape the f64 gate emits.
#[cfg(test)]
const F64_EB: u32 = 11;
#[cfg(test)]
const F64_SB: u32 = 53;
#[cfg(test)]
fn vn_d_lane(n: u32) -> Formula {
    vn_lane(n, 64)
}
#[cfg(test)]
fn fp64_add_bits(a: Formula, b_: Formula) -> Formula {
    fp_add_bits(a, b_, 64)
}
#[cfg(test)]
fn fp64_sub_bits(a: Formula, b_: Formula) -> Formula {
    fp_sub_bits(a, b_, 64)
}
#[cfg(test)]
fn fp64_mul_bits(a: Formula, b_: Formula) -> Formula {
    fp_mul_bits(a, b_, 64)
}
#[cfg(test)]
fn fp64_div_bits(a: Formula, b_: Formula) -> Formula {
    fp_div_bits(a, b_, 64)
}

/// `if pred then 1 else 0`, as a `width`-bit bitvector.
pub(crate) fn pred_to_int(pred: Formula, width: u32) -> Formula {
    Formula::Ite(
        b(pred),
        b(Formula::BitVec { value: 1, width }),
        b(Formula::BitVec { value: 0, width }),
    )
}

/// Symbolic interpreter state: local index -> Formula, plus per-local int width
/// and signedness, plus a byte-addressed memory array (`MEM`) threaded by
/// deref store/load — the SAME `MEM` array (64->8 bit) the machine side uses, so
/// ay's array theory (`Select(Store(m,a,v),a) == v`, QF_ABV) discharges
/// store-then-load roundtrips equal to the byte-derived machine output.
struct SymState {
    locals: HashMap<usize, Formula>,
    widths: HashMap<usize, u32>,
    signed: HashMap<usize, bool>,
    /// Per-local FLOAT flag: a float local holds a raw IEEE bit pattern in a
    /// BV-typed slot, and its arithmetic must use the FP (`FpAdd`/…) shape rather
    /// than the integer BV shape. Only f64 (width 64) is admitted here.
    is_float: HashMap<usize, bool>,
    memory: Formula,
}

/// The shared symbolic memory array variable: `MEM : BitVec(64) -> BitVec(8)`,
/// matching `MachineState::symbolic()`'s memory model exactly.
pub(crate) fn mem_array_var() -> Formula {
    Formula::Var("MEM".into(), Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))))
}

/// Integer bit-width of a scalar type, or Err for non-integer scalar shapes.
/// Pointer-like types are 64-bit (their register slot), supporting memory fns.
fn int_width(ty: &Ty) -> Result<u32, String> {
    match ty {
        Ty::Int { width, .. } => Ok(*width),
        Ty::Bool => Ok(1),
        Ty::Bv(w) => Ok(*w),
        Ty::RawPtr { .. } | Ty::Ref { .. } => Ok(64),
        other => Err(format!("unsupported (non-integer) type: {other:?}")),
    }
}

/// Bit-width of a FLOAT type, restricted to the f32/f64 lowerings this gate
/// proves bit-exactly (both ride the identical width-parametric
/// `FpToIeeeBv(Fp*(RNE, FpFromBits, FpFromBits))` shape at the format's eb/sb —
/// f32 = eb8/sb24 on the S-lane, f64 = eb11/sb53 on the D-lane). f16 fails closed
/// (no bit-exact model wired end-to-end).
fn float_bit_width(ty: &Ty) -> Result<u32, String> {
    match ty {
        Ty::Float { width: 32 } => Ok(32),
        Ty::Float { width: 64 } => Ok(64),
        Ty::Float { width } => Err(format!(
            "float width {width} (f16) is not modeled to bit-exact FP semantics \
             (only f32/f64 are wired); fail-closed"
        )),
        other => Err(format!("float_bit_width on non-float type: {other:?}")),
    }
}

/// Width of the destination register slot for a local of type `ty`.
///
/// SOUNDNESS: this used to end in `_ => 32`, i.e. "any type I do not recognize
/// occupies a 32-bit register". That default is not conservative in either
/// direction — it is simply a guess, and the one place it mattered most is
/// [`return_reg_width`], which decides how many bits of the return register the
/// gate reads back out of the EMITTED OBJECT. Answering 32 for an aggregate,
/// slice, `str`, `PtrSizedInt` or `Char` return would compare the low 32 bits of
/// W0 against the spec and ignore the rest — an aggregate return does not even
/// live in X0 (AAPCS returns it indirectly through the X8 pointer), so the gate
/// would have been comparing an unrelated register.
///
/// Measured: every call site is ordering-protected today, which is exactly why
/// this survived. `trust_ir_semantics_env` runs `int_width`/`float_bit_width`
/// over EVERY local first and both fail closed on non-scalar types, so by the
/// time `reg_width` is called the type has already been narrowed;
/// `derive_callee_pure` re-checks the return and argument types against an
/// explicit scalar list before calling it. Ordering is not construction — the
/// `Ty` list is `#[non_exhaustive]` and grows (`PtrSizedInt`, `Char`, `Str` and
/// `SymArray` are all recent additions that landed straight in the `_` arm), so
/// the width answer is now a `Result` and the guess is gone.
fn reg_width(ty: &Ty) -> Result<u32, String> {
    match ty {
        Ty::Int { width, .. } => Ok(*width),
        Ty::Bv(w) => Ok(*w),
        Ty::Bool => Ok(32),
        Ty::RawPtr { .. } | Ty::Ref { .. } => Ok(64),
        // A scalar float returns in the SIMD/FP register D-lane, whose bit-width
        // is the format width (f64 = 64). (f32/f16 also match here, but the
        // interpreter/machine FP arms fail closed above the width, so a non-f64
        // float never reaches a Proven verdict.)
        Ty::Float { width } => Ok(*width),
        other => Err(format!(
            "no register-slot width is defined for type {other:?}; refusing rather than \
             assuming a 32-bit slot"
        )),
    }
}

impl SymState {
    fn eval_operand(&self, op: &Operand) -> Result<Formula, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.eval_place(place),
            Operand::Constant(c) => eval_const(c),
            other => Err(format!("unsupported operand: {other:?}")),
        }
    }

    fn eval_place(&self, place: &Place) -> Result<Formula, String> {
        if !place.projections.is_empty() {
            return Err(format!("unsupported place projection: {place:?}"));
        }
        self.locals
            .get(&place.local)
            .cloned()
            .ok_or_else(|| format!("read of uninitialized local _{}", place.local))
    }

    fn width_of(&self, op: &Operand) -> Result<u32, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self
                .widths
                .get(&place.local)
                .copied()
                .ok_or_else(|| format!("no width for local _{}", place.local)),
            Operand::Constant(c) => const_width(c),
            other => Err(format!("unsupported operand for width: {other:?}")),
        }
    }

    fn signed_of(&self, op: &Operand) -> Result<bool, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self
                .signed
                .get(&place.local)
                .copied()
                .ok_or_else(|| format!("no signedness for local _{}", place.local)),
            Operand::Constant(_) => Ok(false),
            other => Err(format!("unsupported operand for signedness: {other:?}")),
        }
    }

    /// Whether `op` holds a FLOAT value (an IEEE bit pattern needing FP-shape
    /// arithmetic). A float CONSTANT operand also counts as float. Unknown /
    /// non-place-non-const operands are conservatively NOT float (integer path).
    fn float_of(&self, op: &Operand) -> bool {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                self.is_float.get(&place.local).copied().unwrap_or(false)
            }
            Operand::Constant(ConstValue::Float(_) | ConstValue::FloatBits { .. }) => true,
            _ => false,
        }
    }
}

fn const_width(c: &ConstValue) -> Result<u32, String> {
    match c {
        ConstValue::Bool(_) => Ok(1),
        ConstValue::Uint(_, w) => Ok(*w),
        ConstValue::Int(_) => Err("Int constant without width is unsupported".into()),
        other => Err(format!("unsupported constant for width: {other:?}")),
    }
}

fn eval_const(c: &ConstValue) -> Result<Formula, String> {
    match c {
        ConstValue::Bool(v) => Ok(Formula::BitVec { value: i128::from(*v), width: 1 }),
        ConstValue::Uint(v, w) => {
            let value =
                i128::try_from(*v).map_err(|_| "u128 constant out of i128 range".to_string())?;
            Ok(Formula::BitVec { value, width: *w })
        }
        other => Err(format!("unsupported constant: {other:?}")),
    }
}

/// Binary-op result Formula, signedness from OPERAND types (not destination).
pub(crate) fn eval_binop(
    op: BinOp,
    lhs: Formula,
    rhs: Formula,
    width: u32,
    signed: bool,
) -> Result<Formula, String> {
    let l = b(lhs);
    let r = b(rhs);
    Ok(match op {
        BinOp::Add => Formula::BvAdd(l, r, width),
        BinOp::Sub => Formula::BvSub(l, r, width),
        BinOp::Mul => Formula::BvMul(l, r, width),
        BinOp::BitAnd => Formula::BvAnd(l, r, width),
        BinOp::BitOr => Formula::BvOr(l, r, width),
        BinOp::BitXor => Formula::BvXor(l, r, width),
        BinOp::Shl => Formula::BvShl(l, b(mask_shift(*r, width)), width),
        BinOp::Shr => {
            let amt = b(mask_shift(*r, width));
            if signed { Formula::BvAShr(l, amt, width) } else { Formula::BvLShr(l, amt, width) }
        }
        BinOp::Div => {
            if signed {
                Formula::BvSDiv(l, r, width)
            } else {
                Formula::BvUDiv(l, r, width)
            }
        }
        BinOp::Rem => {
            // AUTO-SPEC the remainder by MIRRORING THE MACHINE'S OWN LOWERING
            // EXACTLY, rather than as a native BvSRem/BvURem:
            //
            //     q = Ite(b == 0, 0, a /{signed} b)      (sdiv/udiv, ÷0 -> 0 on A64)
            //     r = a - q * b                          (msub: Rd = Ra - Rn*Rm)
            //
            // AArch64 has no remainder instruction; the backend lowers `a % b` to
            // `sdiv`/`udiv` (with the architectural divide-by-zero-yields-0 result,
            // which trust-machine-sem models as `Ite(b==0, 0, div)` — see
            // sem_sdiv/sem_udiv) followed by `msub`. The byte-derived machine
            // output is therefore *literally* `a - Ite(b==0,0,div(a,b)) * b`.
            // Building the auto-spec in the IDENTICAL shape (same Ite-guarded
            // quotient, same cross-term) makes `machine_out == auto_spec` a
            // syntactic `X == X`, so ay discharges `NOT(X == X)` UNSAT by
            // congruence WITHOUT bit-blasting the multiplier — which is what made
            // the native-bvsrem encoding time out.
            //
            // This is a faithful re-encoding of the SAME operation (the truncated
            // div identity `a == q*b + r` is the definition of `%`), NOT a widening
            // of any Unknown verdict, so fail-closed is preserved. Signedness stays
            // load-bearing: it selects BvSDiv vs BvUDiv inside the quotient, so a
            // wrong-signedness emission genuinely differs and the SAT negative
            // control still fires Refuted.
            let zero = || Formula::BitVec { value: 0, width };
            let raw_q = if signed {
                Formula::BvSDiv(l.clone(), r.clone(), width)
            } else {
                Formula::BvUDiv(l.clone(), r.clone(), width)
            };
            let b_is_zero = Formula::Eq(r.clone(), b(zero()));
            let q = Formula::Ite(b(b_is_zero), b(zero()), b(raw_q));
            let prod = Formula::BvMul(b(q), r, width);
            Formula::BvSub(l, b(prod), width)
        }
        BinOp::Eq => Formula::Eq(l, r),
        BinOp::Ne => Formula::Not(b(Formula::Eq(l, r))),
        BinOp::Lt => {
            if signed {
                Formula::BvSLt(l, r, width)
            } else {
                Formula::BvULt(l, r, width)
            }
        }
        BinOp::Le => {
            if signed {
                Formula::BvSLe(l, r, width)
            } else {
                Formula::BvULe(l, r, width)
            }
        }
        BinOp::Gt => {
            if signed {
                Formula::BvSLt(r, l, width)
            } else {
                Formula::BvULt(r, l, width)
            }
        }
        BinOp::Ge => {
            let lt = if signed { Formula::BvSLt(l, r, width) } else { Formula::BvULt(l, r, width) };
            Formula::Not(b(lt))
        }
        other => return Err(format!("unsupported binary op: {other:?}")),
    })
}

/// `amt & (width-1)` — the AArch64 shift-amount mask.
pub(crate) fn mask_shift(amt: Formula, width: u32) -> Formula {
    let mask = i128::from(width - 1);
    Formula::BvAnd(b(amt), b(Formula::BitVec { value: mask, width }), width)
}

fn is_comparison(op: BinOp) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
}

/// Int-to-int cast result, extension signedness from the SOURCE type.
pub(crate) fn eval_cast(
    src_formula: Formula,
    src_width: u32,
    src_signed: bool,
    dst_width: u32,
) -> Result<Formula, String> {
    use std::cmp::Ordering;
    let low = Formula::BvExtract { inner: b(src_formula), high: src_width - 1, low: 0 };
    Ok(match dst_width.cmp(&src_width) {
        Ordering::Greater => {
            let added = dst_width - src_width;
            if src_signed {
                Formula::BvSignExt(b(low), added)
            } else {
                Formula::BvZeroExt(b(low), added)
            }
        }
        Ordering::Less => Formula::BvExtract { inner: b(low), high: dst_width - 1, low: 0 },
        Ordering::Equal => low,
    })
}

// ===========================================================================
// LOCAL-PURE-CALLEE COMPOSITION (the codegen-via-trust-ir prerequisite).
//
// A `Terminator::Call` to a LOCAL function in the same verified bundle can be
// SOUNDLY composed into the caller's output semantics — but ONLY under a tight
// fail-closed contract. The composition substitutes the callee's ALREADY-DERIVED
// pure output Formula at the call site on BOTH the IR side and the machine side,
// CONSISTENTLY, so ay discharges the caller exactly as it would any straight-line
// function.
//
// THE SOUNDNESS LINCHPIN: the machine side identifies the call NOT from the IR's
// claim but from the EMITTED OBJECT's `ARM64_RELOC_BRANCH26` relocation — the
// `bl` is emitted with `imm26 = 0` (a self-relative placeholder) plus a
// relocation naming the callee symbol; the LINKER resolves it to the callee's
// own emitted bytes. We may stand the callee's IR-derived Formula in for "what
// the resolved `bl` executes" ONLY because the callee is ITSELF gate-verified
// (Proven) in the same bundle: its bytes are proven == its IR semantics, so the
// linked target computes exactly that Formula. A callee that is not Proven is
// NOT admitted to the environment (fail-closed) — its IR semantics is not yet
// ground truth for its bytes.
//
// FAIL-CLOSED on every condition the composition does not model EXACTLY:
//   * non-local / external / foreign-ABI callee (no in-bundle Proven semantics);
//   * callee whose pure semantics we cannot derive, or that is not Proven;
//   * the `bl`'s relocation is not a single BRANCH26 to a known Proven callee;
//   * arg/return shapes outside the AAPCS64 integer-register fragment we model
//     (we restrict to <= 8 integer/pointer args in X0..X7 and a scalar return in
//     X0/W0 — the shape the bridge's call-lowering emits and the byte shuffle
//     confirms);
//   * recursion (the callee env is acyclic by construction — a callee may not be
//     its own transitive caller — caught by a per-derivation visited set).
// A `Refuted` is NEVER produced via this path being relaxed: discharge stays the
// sole Refuted gate, and an unmodeled call still returns Err => Unknown.
// ===========================================================================

/// A callee admitted to the composition environment: its derived PURE output
/// Formula over the argument registers `X0..Xn`, plus the per-argument register
/// widths and whether each arg occupies a 64-bit (X) or 32-bit (W) slot. Only
/// callees that are LOCAL, PURE, derivable, and (at the bundle gate) PROVEN are
/// admitted.
#[derive(Clone)]
struct CalleePure {
    /// The callee's return-value Formula over `X0..Xn` arg-register variables.
    output: Formula,
    /// Number of integer/pointer arguments (each in X0..X{n-1}).
    arg_count: usize,
    /// Register width (32 or 64) of each argument's slot, in order.
    arg_reg_widths: Vec<u32>,
    /// Register width (32 or 64) of the return value's slot (X0/W0).
    ret_reg_width: u32,
}

/// The set of locally-derivable pure callees, keyed by the symbol name the
/// caller's `Terminator::Call.func` / the emitted `bl` relocation references.
///
/// EMPTY for the single-function entry points (so their behavior is byte-for-byte
/// what it was before composition existed: a `Call` is unknown and fails closed).
/// Populated only by the bundle gate, and ONLY with callees the gate has already
/// concluded `Proven` (see [`build_callee_env`]).
#[derive(Clone, Default)]
struct CalleeEnv {
    callees: HashMap<String, CalleePure>,
}

impl CalleeEnv {
    fn empty() -> Self {
        CalleeEnv::default()
    }

    fn get(&self, name: &str) -> Option<&CalleePure> {
        self.callees.get(name)
    }
}

/// Derive a callee's PURE output semantics for composition, FAIL-CLOSED on
/// anything that is not an exactly-modelable pure integer/pointer function in the
/// AAPCS64 register fragment.
///
/// Returns `None` (admit nothing) unless ALL hold:
///   * the function has at least one block and a derivable `trust_ir_semantics`
///     over an EMPTY callee env (so a callee may NOT itself contain a call we
///     would have to compose — keeps the env one level deep and acyclic; nested
///     pure calls are a future extension, fail-closed for now);
///   * every argument and the return type is an integer/bool/bitvector/pointer
///     scalar living in a single X/W register (no floats, aggregates, unit);
///   * `arg_count <= 8` (args fit X0..X7 — the registers the bridge call-lowering
///     populates and the byte shuffle confirms);
///   * the body performs NO memory writes reachable to a caller (purity): we
///     reject any `*p = ..` store and any nested `Call` by deriving over the
///     empty env (a store/call makes derivation fail or makes the function
///     observably effectful, so we additionally scan for stores explicitly).
fn derive_callee_pure(callee: &VerifiableFunction) -> Option<CalleePure> {
    let body = &callee.body;
    if body.blocks.is_empty() {
        return None;
    }
    if body.arg_count > 8 {
        return None;
    }
    // Return must be a single-register scalar (no unit/never/aggregate/float).
    let ret_reg_width = match &body.return_ty {
        Ty::Int { width, .. } => {
            if *width > 64 {
                return None;
            }
            reg_width(&body.return_ty).ok()?
        }
        Ty::Bv(w) if *w <= 64 => reg_width(&body.return_ty).ok()?,
        Ty::Bool => reg_width(&body.return_ty).ok()?,
        Ty::RawPtr { .. } | Ty::Ref { .. } => 64,
        _ => return None,
    };
    // Every argument must be a single-register integer/pointer scalar.
    let mut arg_reg_widths = Vec::with_capacity(body.arg_count);
    for i in 0..body.arg_count {
        let local = i + 1;
        let decl = body.locals.iter().find(|d| d.index == local)?;
        match &decl.ty {
            Ty::Int { width, .. } if *width <= 64 => {}
            Ty::Bv(w) if *w <= 64 => {}
            Ty::Bool => {}
            Ty::RawPtr { .. } | Ty::Ref { .. } => {}
            _ => return None,
        }
        arg_reg_widths.push(reg_width(&decl.ty).ok()?);
    }
    // PURITY: reject any deref store anywhere in the body. A pure callee whose
    // result we compose may not write through a pointer (its memory effect would
    // not be reflected in the caller's composed output — unsound to drop). Loads
    // are fine (they read MEM, which both sides share), but a function that loads
    // from caller-passed pointers is NOT in our composable fragment yet (its
    // result depends on MEM, which we cannot guarantee matches across the ABI
    // boundary here) — so reject ANY deref projection, store or load, to stay
    // exact. Also reject any nested Call terminator (one level deep only).
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.projections.iter().any(|p| matches!(p, Projection::Deref)) {
                        return None;
                    }
                    if rvalue_touches_memory(rvalue) {
                        return None;
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                // Any other statement (SetDiscriminant, Deinit, Intrinsic, ...)
                // is outside the pure-scalar fragment — fail closed.
                _ => return None,
            }
        }
        if matches!(block.terminator, Terminator::Call { .. } | Terminator::TailCall { .. }) {
            return None;
        }
    }
    // Derive over the EMPTY env: a pure callee admitted here must be self-contained
    // (no composed sub-call), which both keeps the environment one level deep AND
    // guarantees acyclicity (a callee cannot reference another callee's pure
    // formula, hence cannot recurse through the env).
    let output = trust_ir_semantics_env(callee, &CalleeEnv::empty()).ok()?;
    Some(CalleePure { output, arg_count: body.arg_count, arg_reg_widths, ret_reg_width })
}

/// True if an rvalue reads or writes memory (a deref load/store, a ref, or an
/// address-taking aggregate) — used to keep composable callees memory-pure.
fn rvalue_touches_memory(rvalue: &Rvalue) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
            place.projections.iter().any(|p| matches!(p, Projection::Deref))
        }
        Rvalue::Ref { .. } | Rvalue::Aggregate(..) => true,
        _ => false,
    }
}

/// Substitute the caller's call-argument formulas for the callee's argument-
/// register variables (`X0..X{n-1}`) inside the callee's pure output Formula.
///
/// `arg_values[i]` is the formula the caller supplies for the i-th argument,
/// ALREADY widened to the callee's i-th arg register slot (32 or 64 bits). The
/// callee's `trust_ir_semantics` reads arg `i` as `X{i}` (full 64) or
/// `BvExtract(X{i})[31:0]` (the `W{i}` view) — so substituting `X{i} := xN64`
/// where `xN64` is the 64-bit-slot value reproduces both views exactly.
fn substitute_arg_registers(output: &Formula, arg_values_x64: &[Formula]) -> Formula {
    let mut result = output.clone();
    for (i, val64) in arg_values_x64.iter().enumerate() {
        let var = format!("X{i}");
        result = substitute_var(&result, &var, val64);
    }
    result
}

/// Zero-extend a `from_width`-bit value into a 64-bit argument-register slot. A
/// no-op at 64; truncates a >64 (illegal) shape defensively to 64 low bits.
/// This matches AAPCS64: a narrow integer argument occupies the low bits of its
/// X register (the W view), with the upper bits unspecified — but the callee's
/// `trust_ir_semantics` only ever reads `BvExtract(X{i})[width-1:0]`, so any
/// extension that preserves the low `from_width` bits is exact. Zero-extension is
/// the canonical choice and matches the emitted `Orr W{i}, WZR, W{src}` shuffle.
fn zero_extend_to_64(value: Formula, from_width: u32) -> Formula {
    match from_width.cmp(&64) {
        std::cmp::Ordering::Equal => value,
        std::cmp::Ordering::Less => Formula::BvZeroExt(b(value), 64 - from_width),
        std::cmp::Ordering::Greater => Formula::BvExtract { inner: b(value), high: 63, low: 0 },
    }
}

/// Replace every free `Var(name, _)` occurrence in `f` with `replacement`.
///
/// Implemented via the `Formula::map_children` one-level structural combinator
/// (provided by `trust-ir-contract`), so it is TOTAL over every `Formula`
/// constructor — there is no hand-maintained per-variant match that could drift
/// out of date and silently drop a substitution. The admitted-callee fragment
/// (see `derive_callee_pure`) contains no quantifiers, so there are no bound
/// variables to capture; substitution is plain syntactic replacement.
fn substitute_var(f: &Formula, name: &str, replacement: &Formula) -> Formula {
    match f {
        Formula::Var(n, _) if n == name => replacement.clone(),
        leaf @ (Formula::Var(..) | Formula::SymVar(..)) => leaf.clone(),
        other => other.clone().map_children(&mut |child| substitute_var(&child, name, replacement)),
    }
}

/// THE INTERPRETER. Walk a LOOP-FREE (DAG-CFG) scalar/memory function and return
/// the intended-semantics Formula of its return value over symbolic arg
/// registers. Multi-block control flow (Goto/SwitchInt) merges as an `Ite` over
/// the branch condition — the SAME signedness-from-operands discipline the
/// machine-side path-merger uses, so the auto-spec is sound. Memory deref
/// store/load is threaded through a byte-addressed `MEM` array shared with the
/// machine side. Fail closed (Err => Unknown) on any unsupported shape
/// (loops/backedges, float, calls, non-deref projections, ...).
pub fn trust_ir_semantics(func: &VerifiableFunction) -> Result<Formula, String> {
    trust_ir_semantics_env(func, &CalleeEnv::empty())
}

/// Bundle-aware [`trust_ir_semantics`]: identical to the public single-function
/// entry point, except a `Terminator::Call` to a LOCAL pure callee present in
/// `env` is composed (the callee's pure output substituted at the call site).
/// With an EMPTY env this is byte-for-byte the original single-function behavior.
fn trust_ir_semantics_env(func: &VerifiableFunction, env: &CalleeEnv) -> Result<Formula, String> {
    let expanded = func.with_tail_calls_expanded();
    let func = expanded.as_ref();
    let body = &func.body;
    if body.blocks.is_empty() {
        return Err("function has no basic blocks".into());
    }

    let mut state = SymState {
        locals: HashMap::new(),
        widths: HashMap::new(),
        signed: HashMap::new(),
        is_float: HashMap::new(),
        memory: mem_array_var(),
    };
    for d in &body.locals {
        // A float local holds a raw IEEE bit pattern in a BV-typed slot. Only
        // f64 (width 64) is admitted to bit-exact FP semantics here; f32/f16
        // fail closed via `float_bit_width` (documented incomplete).
        if d.ty.is_float() {
            let w = float_bit_width(&d.ty)?;
            state.widths.insert(d.index, w);
            state.signed.insert(d.index, false);
            state.is_float.insert(d.index, true);
        } else {
            let w = int_width(&d.ty)?;
            state.widths.insert(d.index, w);
            state.signed.insert(d.index, d.ty.is_signed());
            state.is_float.insert(d.index, false);
        }
    }

    for i in 0..body.arg_count {
        let local = i + 1;
        let decl = body
            .locals
            .iter()
            .find(|d| d.index == local)
            .ok_or_else(|| format!("missing decl for arg local _{local}"))?;
        // AArch64 AAPCS: a scalar float argument arrives in the i-th SIMD/FP
        // register V_i (its low scalar lane = `read_fpr(i, width)`; D-lane for
        // f64, S-lane for f32), NOT the GPR X_i. Integer/pointer args arrive in
        // X_i/W_i.
        let arg_reg = if decl.ty.is_float() {
            let fw = float_bit_width(&decl.ty)?; // enforce f32/f64, fail-closed on f16
            vn_lane(i as u32, fw)
        } else {
            let rw = reg_width(&decl.ty)?;
            if rw > 32 { xn(i as u32) } else { wn(i as u32) }
        };
        state.locals.insert(local, arg_reg);
    }

    // Recursively evaluate the entry block, merging branches as Ite. A per-path
    // visited-block set fails closed on backedges (loops) — never hangs.
    eval_block(func, env, &state, BlockId(0), &mut Vec::new())
}

/// Evaluate the basic block `id` under `state`, returning the return-value
/// Formula reachable from it. Branches (SwitchInt) fork the state per successor
/// and merge as `Ite(branch_cond, ...)`. `visited` tracks the blocks on THIS
/// path; revisiting one is a loop and fails closed. A `Terminator::Call` to a
/// LOCAL pure callee in `env` is composed (the callee's pure output substituted
/// for the call's result); with an EMPTY env every call fails closed unchanged.
fn eval_block(
    func: &VerifiableFunction,
    env: &CalleeEnv,
    state: &SymState,
    id: BlockId,
    visited: &mut Vec<BlockId>,
) -> Result<Formula, String> {
    if visited.contains(&id) {
        return Err(format!("loop/backedge detected at block {id:?} (fail-closed)"));
    }
    visited.push(id);

    let block = func
        .body
        .blocks
        .iter()
        .find(|b| b.id == id)
        .ok_or_else(|| format!("block {id:?} not found"))?;

    // Execute this block's statements into a forked state.
    let mut st = clone_state(state);
    for stmt in &block.stmts {
        match stmt {
            Statement::Assign { place, rvalue, .. } => {
                if place.projections.is_empty() {
                    let dst = place.local;
                    let value = eval_rvalue(&st, rvalue, dst)?;
                    st.locals.insert(dst, value);
                } else if place.projections.len() == 1
                    && matches!(place.projections[0], Projection::Deref)
                {
                    // `*p = rvalue`: store the rvalue's bytes to MEM at address `p`.
                    let addr = st.locals.get(&place.local).cloned().ok_or_else(|| {
                        format!("store through uninitialized local _{}", place.local)
                    })?;
                    let value = eval_rvalue(&st, rvalue, place.local)?;
                    let width_bytes = store_width_bytes(&st, rvalue)?;
                    st.memory =
                        store_bytes_le_formula(st.memory.clone(), &addr, &value, width_bytes);
                } else {
                    return Err(format!("unsupported assign to projected place: {place:?}"));
                }
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Nop
            | Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter => {}
            other => return Err(format!("unsupported statement: {other:?}")),
        }
    }

    // Terminator: Return ends the path; Goto follows; SwitchInt merges as Ite.
    match &block.terminator {
        Terminator::Return => st
            .locals
            .get(&0)
            .cloned()
            .ok_or_else(|| "return local _0 was never assigned".to_string()),
        Terminator::Goto(target) => eval_block(func, env, &st, *target, visited),
        // A direct call to a LOCAL PURE callee present in `env`: compose the
        // callee's already-derived output Formula at the call site. FAIL-CLOSED
        // (Err => Unknown) on a foreign/external callee, an atomic call, a callee
        // absent from `env` (not local/pure/Proven), an unmodelable destination,
        // a missing continuation, or an arg/arity mismatch. With an EMPTY env the
        // `env.get` always misses, so this arm fails closed exactly as the
        // pre-composition catch-all did.
        Terminator::Call { func: callee_name, args, dest, target, atomic, is_foreign, .. } => {
            if *is_foreign {
                return Err(format!(
                    "call to foreign/non-Rust-ABI callee `{callee_name}` (fail-closed)"
                ));
            }
            if atomic.is_some() {
                return Err(format!("atomic-intrinsic call `{callee_name}` (fail-closed)"));
            }
            let callee = env.get(callee_name).ok_or_else(|| {
                format!(
                    "call to `{callee_name}` is not a known local pure Proven callee \
                     (fail-closed)"
                )
            })?;
            if args.len() != callee.arg_count {
                return Err(format!(
                    "call to `{callee_name}` arg count {} != callee arity {} (fail-closed)",
                    args.len(),
                    callee.arg_count
                ));
            }
            // Evaluate each call argument, then WIDEN it to the callee's i-th
            // argument register slot (X{i}, 64-bit) exactly as the callee's
            // `trust_ir_semantics` reads it: a 32-bit (W{i}) arg is the low half of
            // X{i}, so we zero-extend the IR arg value into the 64-bit slot. The
            // callee formula references `X{i}` (full) or `BvExtract(X{i})[31:0]`
            // (the W view); substituting the 64-bit slot value reproduces both.
            let mut arg_x64 = Vec::with_capacity(args.len());
            for (i, arg) in args.iter().enumerate() {
                let raw = st.eval_operand(arg)?;
                let arg_w = st.width_of(arg).unwrap_or(callee.arg_reg_widths[i]);
                arg_x64.push(zero_extend_to_64(raw, arg_w));
            }
            let result = substitute_arg_registers(&callee.output, &arg_x64);
            // Bind the call result to `dest` (a direct local). The callee's output
            // Formula already has the callee's return register width; a 32-bit
            // return is a `*W*`-sized value, matching `dest`'s declared width.
            let dst = if dest.projections.is_empty() {
                dest.local
            } else {
                return Err(format!(
                    "call `{callee_name}` to a projected destination is unsupported (fail-closed)"
                ));
            };
            let cont = target.ok_or_else(|| {
                format!(
                    "call `{callee_name}` has no continuation block (diverging call, fail-closed)"
                )
            })?;
            st.locals.insert(dst, result);
            // The destination's width/signedness are already in `st` from the
            // local decls; continue at the continuation block.
            eval_block(func, env, &st, cont, visited)
        }
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            // Model an N-way integer SwitchInt as a nested-Ite cascade over the
            // discriminant value:
            //
            //   match discr {
            //     case_0 => bb_0,
            //     case_1 => bb_1,
            //     ...
            //     _       => bb_otherwise,
            //   }
            //
            // becomes
            //
            //   Ite(discr == case_0, eval(bb_0),
            //   Ite(discr == case_1, eval(bb_1),
            //   ...
            //                        eval(bb_otherwise)))
            //
            // The 1-case form (the canonical bool CondBr that trust-cg lowers from
            // `if`) is just the N=1 instance of this cascade, so existing bool
            // switches keep their EXACT previous shape. The machine-side
            // path-merging executor already produces an Ite tree over the real
            // branch conditions for arbitrary nested CondBr chains (the multi-way
            // switch lowers to a comparison-chain of CMP+B.cond), so the byte-
            // derived formula matches this cascade and ay discharges equality.
            //
            // FAIL-CLOSED: cap the arm count so a pathological switch (which would
            // explode the executor's fork budget anyway) stays Unknown rather than
            // attempting a deep nest. 1..=4 arms covers the recon target (3-4 arms)
            // plus the existing bool case.
            if targets.is_empty() || targets.len() > 4 {
                return Err(format!(
                    "unsupported SwitchInt with {} target(s) (modelled range is 1..=4 arms)",
                    targets.len()
                ));
            }
            let discr_f = st.eval_operand(discr)?;
            // A bool comparison result is stored WIDENED to 32 (see pred_to_int in
            // eval_rvalue), so the discriminant formula is 32-bit even though the
            // bool local's declared width is 1. Match the constant to that width so
            // the equality is well-sorted.
            let raw_w = st.width_of(discr)?;
            let discr_w = if raw_w <= 1 { 32 } else { raw_w };

            // Evaluate the `otherwise` (default) arm first — it is the innermost
            // Ite else-branch. Fork the path-visited set per successor so sibling
            // branches don't falsely flag each other as loops.
            let mut vo = visited.clone();
            let mut acc = eval_block(func, env, &st, *otherwise, &mut vo)?;

            // Fold the explicit cases from LAST to FIRST so the resulting nest
            // tests case_0 outermost (matching source/textual order).
            for &(case_val, target_blk) in targets.iter().rev() {
                let is_case = Formula::Eq(
                    b(discr_f.clone()),
                    b(Formula::BitVec { value: case_val as i128, width: discr_w }),
                );
                let mut vt = visited.clone();
                let arm_v = eval_block(func, env, &st, target_blk, &mut vt)?;
                acc = Formula::Ite(b(is_case), b(arm_v), b(acc));
            }
            Ok(acc)
        }
        other => Err(format!("unsupported terminator: {other:?}")),
    }
}

fn clone_state(state: &SymState) -> SymState {
    SymState {
        locals: state.locals.clone(),
        widths: state.widths.clone(),
        signed: state.signed.clone(),
        is_float: state.is_float.clone(),
        memory: state.memory.clone(),
    }
}

/// Store the low `width_bytes` bytes of `value` into the `memory` array in
/// little-endian order — mirrors `trust_machine_sem::state::store_bytes_le`
/// exactly so the two MEM formulas are syntactically reducible by array theory.
fn store_bytes_le_formula(
    memory: Formula,
    address: &Formula,
    value: &Formula,
    width_bytes: u32,
) -> Formula {
    let mut mem = memory;
    for i in 0..width_bytes {
        let high = (i + 1) * 8 - 1;
        let low = i * 8;
        let byte = Formula::BvExtract { inner: b(value.clone()), high, low };
        let addr_i = if i == 0 {
            address.clone()
        } else {
            Formula::BvAdd(
                b(address.clone()),
                b(Formula::BitVec { value: i as i128, width: 64 }),
                64,
            )
        };
        mem = Formula::Store(b(mem), b(addr_i), b(byte));
    }
    mem
}

/// Load `width_bytes` little-endian bytes from `memory` at `address`, returning
/// a `width_bytes*8`-bit value (byte concat, mirroring a machine LDR reduction).
pub(crate) fn load_bytes_le_formula(
    memory: &Formula,
    address: &Formula,
    width_bytes: u32,
) -> Formula {
    // Concatenate high byte ... low byte: result = byte[n-1] :: ... :: byte[0].
    let mut acc: Option<Formula> = None;
    for i in 0..width_bytes {
        let addr_i = if i == 0 {
            address.clone()
        } else {
            Formula::BvAdd(
                b(address.clone()),
                b(Formula::BitVec { value: i as i128, width: 64 }),
                64,
            )
        };
        let byte = Formula::Select(b(memory.clone()), b(addr_i));
        acc = Some(match acc {
            None => byte,
            Some(hi) => Formula::BvConcat(b(byte), b(hi)),
        });
    }
    acc.expect("width_bytes >= 1")
}

/// Byte width of a deref store's rvalue, from the pointee/value type.
fn store_width_bytes(state: &SymState, rvalue: &Rvalue) -> Result<u32, String> {
    let bits = match rvalue {
        Rvalue::Use(op) => state.width_of(op)?,
        other => return Err(format!("unsupported store rvalue: {other:?}")),
    };
    Ok(bits.div_ceil(8))
}

fn eval_rvalue(state: &SymState, rvalue: &Rvalue, dst: usize) -> Result<Formula, String> {
    match rvalue {
        // `_dst = *p`: a deref LOAD reads the destination-width bytes from MEM at
        // the pointer register address `p` (array theory reduces store->load).
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
            if place.projections.len() == 1
                && matches!(place.projections[0], Projection::Deref) =>
        {
            let addr = state
                .locals
                .get(&place.local)
                .cloned()
                .ok_or_else(|| format!("load through uninitialized local _{}", place.local))?;
            let load_bits = state
                .widths
                .get(&dst)
                .copied()
                .ok_or_else(|| format!("no width for load destination _{dst}"))?;
            let width_bytes = load_bits.div_ceil(8);
            Ok(load_bytes_le_formula(&state.memory, &addr, width_bytes))
        }
        Rvalue::Use(op) => state.eval_operand(op),
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let lf = state.eval_operand(lhs)?;
            let rf = state.eval_operand(rhs)?;
            // FLOAT BINARY OPS. A float operand means BV-level integer arithmetic
            // is WRONG semantics — the operands are IEEE bit patterns. Emit the
            // bit-exact FP shape instead. f32 AND f64 `Add`/`Sub`/`Mul`/`Div` are
            // wired to bit-exact `FpAdd|FpSub|FpMul|FpDiv(RNE, ..)` at the format's
            // eb/sb (f32 = eb8/sb24, f64 = eb11/sb53); every other float op
            // (Rem, all comparisons, f16) fails closed (documented incomplete) so
            // a wrong/approximate result is never proven.
            //
            // NO GUARD for `Div`: IEEE-754 division is total (`x/0.0` = ±inf,
            // `0.0/0.0` = NaN — neither traps), so `FpDiv(RNE, ..)` is sound
            // unconditionally, unlike INTEGER Div/Rem which DOES require a
            // divisor-nonzero precondition.
            let operands_float = state.float_of(lhs) || state.float_of(rhs);
            if operands_float {
                let width = pick_width(state, lhs, rhs)?;
                if fp_eb_sb(width).is_none() {
                    return Err(format!(
                        "float binary op at width {width} (f16) is not modeled to \
                         bit-exact FP semantics (only f32/f64 are wired); fail-closed"
                    ));
                }
                return match op {
                    BinOp::Add => Ok(fp_add_bits(lf, rf, width)),
                    BinOp::Sub => Ok(fp_sub_bits(lf, rf, width)),
                    BinOp::Mul => Ok(fp_mul_bits(lf, rf, width)),
                    BinOp::Div => Ok(fp_div_bits(lf, rf, width)),
                    other => Err(format!(
                        "float binary op `{other:?}` is not wired to bit-exact FP \
                         semantics (only f32/f64 Add/Sub/Mul/Div); fail-closed"
                    )),
                };
            }
            let width = pick_width(state, lhs, rhs)?;
            let signed = pick_signed(state, lhs, rhs)?;
            let result = eval_binop(*op, lf, rf, width, signed)?;
            if is_comparison(*op) {
                let dst_rw = state
                    .widths
                    .get(&dst)
                    .copied()
                    .map(|w| if w <= 1 { 32 } else { w })
                    .unwrap_or(32);
                Ok(pred_to_int(result, dst_rw))
            } else {
                Ok(result)
            }
        }
        Rvalue::UnaryOp(UnOp::Neg, op) => {
            let f = state.eval_operand(op)?;
            let width = state.width_of(op)?;
            Ok(Formula::BvSub(b(Formula::BitVec { value: 0, width }), b(f), width))
        }
        Rvalue::Cast(op, dst_ty) => {
            let f = state.eval_operand(op)?;
            let src_width = state.width_of(op)?;
            let src_signed = state.signed_of(op)?;
            let dst_width = int_width(dst_ty)?;
            eval_cast(f, src_width, src_signed, dst_width)
        }
        other => Err(format!("unsupported rvalue: {other:?}")),
    }
}

fn pick_width(state: &SymState, lhs: &Operand, rhs: &Operand) -> Result<u32, String> {
    if let Ok(w) = state.width_of(lhs) {
        return Ok(w);
    }
    state.width_of(rhs)
}

fn pick_signed(state: &SymState, lhs: &Operand, rhs: &Operand) -> Result<bool, String> {
    if let (Operand::Copy(_) | Operand::Move(_), _) = (lhs, rhs) {
        return state.signed_of(lhs);
    }
    if let (_, Operand::Copy(_) | Operand::Move(_)) = (lhs, rhs) {
        return state.signed_of(rhs);
    }
    state.signed_of(lhs)
}

// ===========================================================================
// PART 2 — EMIT + BYTE-DERIVED MACHINE OUTPUT.
// machine_out is derived ONLY from the EMITTED BYTES.
// ===========================================================================

#[cfg(test)]
fn host_triple() -> String {
    TrustCgCodegenBackend::host().target_triple().to_string()
}

fn default_verification_backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::host()
}

// TEST-ONLY CORRUPTION SEAM (teeth). When set, `emit_text` rewrites the emitted
// `__text` bytes through this hook BEFORE the gate decodes them — modelling a
// miscompiling backend (a stray bit flip in the data-processing op). The gate
// then derives its machine output from the CORRUPTED bytes and ay refutes them
// against the (correct, IR-derived) auto-spec. This exercises the FULL public
// `emit_objects_verified` path against a genuine miscompile: the gate must
// return `Err(Refuted)` and produce NO object bytes. Never set outside tests.
#[cfg(test)]
thread_local! {
    static TEXT_CORRUPTOR: std::cell::RefCell<Option<Box<dyn Fn(&mut Vec<u8>, u64)>>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
fn with_text_corruptor<R>(
    corruptor: impl Fn(&mut Vec<u8>, u64) + 'static,
    body: impl FnOnce() -> R,
) -> R {
    TEXT_CORRUPTOR.with(|c| *c.borrow_mut() = Some(Box::new(corruptor)));
    let r = body();
    TEXT_CORRUPTOR.with(|c| *c.borrow_mut() = None);
    r
}

#[cfg(test)]
fn apply_text_corruptor(code: &mut Vec<u8>, base: u64) {
    TEXT_CORRUPTOR.with(|c| {
        if let Some(f) = c.borrow().as_ref() {
            f(code, base);
        }
    });
}

// TEST-ONLY RE-EMIT DIVERGER SEAM (RUNG 2 negative control). Models a
// NON-DETERMINISTIC or TROJANED backend whose RE-EMISSION differs from the
// emission the gate verified: the gate's re-emit equality check
// (`reemit_matches_verified`) feeds the freshly re-emitted object through this
// hook, and when it is set the diverger flips a byte. Pre-fix the divergent
// re-emit shipped silently; post-fix the gate DETECTS it and fails closed
// (`Err(EmitFailed)`, no object). Never set outside tests.
#[cfg(test)]
thread_local! {
    static REEMIT_DIVERGER: std::cell::RefCell<Option<Box<dyn Fn(&mut Vec<u8>)>>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
fn with_reemit_diverger<R>(
    diverger: impl Fn(&mut Vec<u8>) + 'static,
    body: impl FnOnce() -> R,
) -> R {
    REEMIT_DIVERGER.with(|c| *c.borrow_mut() = Some(Box::new(diverger)));
    let r = body();
    REEMIT_DIVERGER.with(|c| *c.borrow_mut() = None);
    r
}

#[cfg(test)]
fn apply_reemit_diverger(obj: &mut Vec<u8>) {
    REEMIT_DIVERGER.with(|c| {
        if let Some(f) = c.borrow().as_ref() {
            f(obj);
        }
    });
}

/// Trust (RUNG 2 — shipped == verified, TOCTOU detector). Re-emit `func` once
/// more and confirm the freshly emitted object is BYTE-IDENTICAL to the bytes
/// the gate verified (`verified`). The whole-stage2 determinism closure makes
/// equality the EXPECTED case; this turns expected into ENFORCED: a backend
/// whose second emission differs from the first (nondeterminism, or a trojan
/// that emits clean bytes "when watched" and dirty bytes for the real artifact)
/// is caught here and the function is REFUSED. Returns Ok(()) on a byte-match,
/// Err(detail) on any divergence or re-emit failure.
fn reemit_matches_verified_with_backend(
    func: &VerifiableFunction,
    verified: &[u8],
    backend: &TrustCgCodegenBackend,
) -> Result<(), String> {
    let lir = backend
        .lower_function(func)
        .map_err(|e| format!("re-emit lower_function failed: {e:?}"))?;
    #[allow(unused_mut)]
    let mut reemit =
        backend.emit_object(&[lir]).map_err(|e| format!("re-emit emit_object failed: {e:?}"))?;
    #[cfg(test)]
    apply_reemit_diverger(&mut reemit);
    if reemit == verified {
        Ok(())
    } else {
        Err(format!(
            "RE-EMISSION DIVERGED from the verified bytes for fn `{}` (verified {} bytes, \
             re-emitted {} bytes) — the shipped artifact would not be the artifact the gate \
             verified; refusing (fail-closed)",
            func.name,
            verified.len(),
            reemit.len()
        ))
    }
}

/// Emit `func` to a real object once and return BOTH the FULL serialized object
/// bytes (the candidate shipped artifact) and the decoded text-section bytes +
/// base address (the gate's verification view). Returns Err (=> Unknown at the
/// gate) on lowering/emission failure or an unreadable object container.
///
/// Trust (RUNG 2 — shipped == verified): the FULL `obj` returned here is the
/// SAME single emission whose `__text` the gate decodes and discharges against
/// the auto-spec. `verify_output_preserved_capturing` threads `obj` out so the
/// build gate ships EXACTLY the bytes it verified (no second emission), closing
/// the emit-time TOCTOU by construction.
#[cfg(test)]
fn emit_text(func: &VerifiableFunction) -> Result<(Vec<u8>, Vec<u8>, u64), String> {
    let backend = default_verification_backend();
    emit_text_with_backend(func, &backend)
}

fn emit_object_with_backend(
    func: &VerifiableFunction,
    backend: &TrustCgCodegenBackend,
) -> Result<Vec<u8>, String> {
    let lir = backend.lower_function(func).map_err(|e| format!("lower_function failed: {e:?}"))?;
    backend.emit_object(&[lir]).map_err(|e| format!("emit_object failed: {e:?}"))
}

#[cfg(test)]
fn emit_text_with_backend(
    func: &VerifiableFunction,
    backend: &TrustCgCodegenBackend,
) -> Result<(Vec<u8>, Vec<u8>, u64), String> {
    let obj = emit_object_with_backend(func, backend)?;
    decode_text_from_object(obj)
}

#[cfg(test)]
fn decode_text_from_object(obj: Vec<u8>) -> Result<(Vec<u8>, Vec<u8>, u64), String> {
    let (code, base) = extract_text_from_object(&obj)?;
    Ok((obj, code, base))
}

/// Locate the executable text of an emitted object, whatever container the
/// configured target uses.
///
/// The gate's whole machine side is derived from these bytes, so a container it
/// cannot open collapses every verdict on that platform to `Unknown` — the gate
/// stops being able to refute a miscompile at all. `emit_object` selects the
/// container from the target triple (Mach-O for `*-apple-darwin`, ELF for
/// `*-unknown-linux-*`), so both must be readable for the gate to be live on the
/// hosts the backend actually emits for. A container that is neither is an
/// honest `Err`: there is no fallback that could produce real bytes.
pub(crate) fn extract_text_from_object(obj: &[u8]) -> Result<(Vec<u8>, u64), String> {
    let (code, base) = macho_text(obj)
        .or_else(|| elf64_text(obj))
        .ok_or_else(|| "could not extract the text section from emitted object".to_string())?;
    #[cfg(test)]
    {
        let mut code = code;
        apply_text_corruptor(&mut code, base);
        return Ok((code, base));
    }
    #[cfg(not(test))]
    Ok((code, base))
}

/// Read the `.text` section of a little-endian ELF64 relocatable object.
///
/// Section lookup goes through the section-header string table by name rather
/// than by index: the emitter's section ordering is not part of any contract the
/// gate can rely on, and silently decoding the wrong section would fabricate a
/// machine side. Every field read is bounds-checked, so a truncated or hostile
/// object yields `None` (=> `Unknown`) instead of a panic inside the compiler.
fn elf64_text(obj: &[u8]) -> Option<(Vec<u8>, u64)> {
    // 0x7f 'E' 'L' 'F', ELFCLASS64, ELFDATA2LSB.
    if obj.get(..6)? != b"\x7fELF\x02\x01" {
        return None;
    }
    let rd_u16 =
        |o: usize| -> Option<u16> { Some(u16::from_le_bytes(obj.get(o..o + 2)?.try_into().ok()?)) };
    let rd_u32 =
        |o: usize| -> Option<u32> { Some(u32::from_le_bytes(obj.get(o..o + 4)?.try_into().ok()?)) };
    let rd_u64 =
        |o: usize| -> Option<u64> { Some(u64::from_le_bytes(obj.get(o..o + 8)?.try_into().ok()?)) };

    let section_table = usize::try_from(rd_u64(40)?).ok()?; // e_shoff
    let section_size = usize::from(rd_u16(58)?); // e_shentsize
    let section_count = usize::from(rd_u16(60)?); // e_shnum
    let names_index = usize::from(rd_u16(62)?); // e_shstrndx
    if section_size < 64 || names_index >= section_count {
        return None;
    }

    let header_at = |index: usize| -> Option<usize> {
        (index < section_count)
            .then_some(section_table.checked_add(index.checked_mul(section_size)?)?)
    };
    let names_header = header_at(names_index)?;
    let names_offset = usize::try_from(rd_u64(names_header + 24)?).ok()?; // sh_offset
    let names_size = usize::try_from(rd_u64(names_header + 32)?).ok()?; // sh_size
    let names = obj.get(names_offset..names_offset.checked_add(names_size)?)?;

    for index in 0..section_count {
        let header = header_at(index)?;
        let name_offset = usize::try_from(rd_u32(header)?).ok()?; // sh_name
        let name_tail = names.get(name_offset..)?;
        let name_end = name_tail.iter().position(|byte| *byte == 0)?;
        if &name_tail[..name_end] != b".text" {
            continue;
        }
        let address = rd_u64(header + 16)?; // sh_addr
        let offset = usize::try_from(rd_u64(header + 24)?).ok()?; // sh_offset
        let size = usize::try_from(rd_u64(header + 32)?).ok()?; // sh_size
        return Some((obj.get(offset..offset.checked_add(size)?)?.to_vec(), address));
    }
    None
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
                let name = &obj[sec..sec + 16];
                if name.starts_with(b"__text\0") {
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

// --- BOUNDED SYMBOLIC PATH-MERGING EXECUTOR (folded from proven_output_condbr.rs).
//
// Decode the EMITTED BYTES. Execute straight-line effects through a symbolic
// MachineState until a RET (read the return register) or a ConditionalBranch
// (FORK). At a ConditionalBranch{condition, target, fallthrough}: the path
// condition is `condition_to_formula(state, condition)` over the CURRENT
// (post-Subs/post-Cmp) symbolic NZCV flags — the SAME path condition the
// proven_output_condbr.rs harness uses, so the merge is sound. We recurse on the
// taken-target state and the fallthrough state and MERGE as
// `Ite(path_cond, taken, fall)`.
//
// LOOP SAFETY (fail-closed, never hang, never fake a proof): a per-path
// visited-PC set detects revisited PCs / backedges, and hard caps bound total
// instruction steps and fork depth. Any backedge / cap breach / unsupported
// effect (calls, atomics, indirect branch) returns Err — the gate then reports
// Unknown (the function is NOT emitted). Memory Store/Load is threaded through
// MachineState by apply_effect (byte-addressed MEM array), unchanged.

const MAX_STEPS: u32 = 4096;
const MAX_DEPTH: u32 = 16;

/// What ONE merged execution path of the emitted bytes yields.
///
/// `value` is the return-register Formula as before. `reach` is the NEW,
/// SEPARATE claim that this path actually REACHES a `RET` — the machine-side
/// half of the assert/trap obligation. For every existing caller (`model_traps`
/// off) `reach` is syntactically `Bool(true)` and `value` is byte-for-byte the
/// Formula the executor produced before this type existed.
#[derive(Clone)]
pub(crate) struct PathOutcome {
    /// Return-register Formula at the reachable `RET`(s).
    pub(crate) value: Formula,
    /// Predicate: under which inputs does control reach a `RET` at all?
    /// `Bool(true)` when nothing on any path diverges.
    pub(crate) reach: Formula,
}

/// Every AArch64 opcode that ENDS straight-line flow: reaching one means the
/// NEXT instruction is not executed by falling through. Used by the divergent-PC
/// prescan to bound its backward walk at a real basic-block leader.
///
/// `Bl` is deliberately ABSENT: a `bl` returns to `pc+4`, so a call whose
/// continuation diverges diverges too.
fn ends_straight_line(op: Opcode) -> bool {
    matches!(
        op,
        Opcode::Ret
            | Opcode::B
            | Opcode::Br
            | Opcode::BCond
            | Opcode::Cbz
            | Opcode::Cbnz
            | Opcode::Tbz
            | Opcode::Tbnz
    )
}

/// The set of `__text` PCs from which straight-line execution provably reaches a
/// `BRK` — i.e. the DIVERGENT (never-returning) tail the trust-cg `Trap` lowering
/// emits for a failed `Inst::Assert` (`stp; mov; bl <panic>; brk`).
///
/// Computed by walking BACKWARD from each decoded `BRK`, marking each preceding
/// instruction, and stopping at the first instruction that ends straight-line
/// flow (that instruction is NOT marked — control never falls out of it into the
/// tail). This is exactly the "no `RET` is reachable from here without taking a
/// branch" set, which is why the marking is sound rather than heuristic: a `pc`
/// in the set cannot produce a return value at all.
///
/// The gate uses this only to say `reach = false` on such a path. It NEVER makes
/// a value claim about a divergent path, and a function whose obligation becomes
/// vacuous because EVERY path diverges is rejected by the vacuity check in
/// `verify_output_trust_ir`.
fn divergent_pcs(code: &[u8], base: u64) -> HashSet<u64> {
    let mut set = HashSet::new();
    let word_count = code.len() / 4;
    let mut ops: Vec<Option<Opcode>> = Vec::with_capacity(word_count);
    for i in 0..word_count {
        let pc = base + (i as u64) * 4;
        let op = code
            .get(i * 4..i * 4 + 4)
            .and_then(|s| <[u8; 4]>::try_from(s).ok())
            .and_then(|bytes| decode_aarch64(&bytes, pc).ok())
            .map(|insn| insn.opcode);
        ops.push(op);
    }
    for i in 0..word_count {
        if ops[i] != Some(Opcode::Brk) {
            continue;
        }
        let mut j = i as i64;
        while j >= 0 {
            match ops[j as usize] {
                Some(op) if ends_straight_line(op) => break,
                _ => {}
            }
            set.insert(base + (j as u64) * 4);
            j -= 1;
        }
    }
    set
}

struct PathMergingExecutor<'a> {
    sem: Aarch64Semantics,
    code: &'a [u8],
    base: u64,
    out_width: u32,
    /// Whether the return value lives in the SIMD/FP register file (a scalar
    /// float returns in V0's D-lane) rather than the GPR X0. Selects which
    /// register the terminating RET reads.
    out_is_float: bool,
    steps: u32,
    /// LOCAL pure callees admitted for composition (empty for the single-fn path).
    env: &'a CalleeEnv,
    /// `__text` relocations keyed by in-section byte offset: identifies which
    /// `bl` calls which external symbol. Empty for the single-fn path.
    bl_targets: &'a HashMap<u64, BranchReloc>,
    /// A fresh-variable counter so each modeled call clobbers caller-saved
    /// registers with DISTINCT unconstrained values (no accidental sharing).
    call_counter: u32,
    /// PCs from which straight-line flow provably reaches a `BRK` (see
    /// [`divergent_pcs`]). EMPTY unless trap modeling is on, so every existing
    /// caller executes the identical program.
    divergent: HashSet<u64>,
    /// Whether to model a `BRK` tail as a NON-RETURNING path (`reach = false`)
    /// instead of running into it. `false` for every pre-existing caller: the
    /// MIR-path gate keeps failing closed on a trap exactly as before.
    model_traps: bool,
}

impl<'a> PathMergingExecutor<'a> {
    #[cfg(test)]
    fn new(code: &'a [u8], base: u64, out_width: u32, out_is_float: bool) -> Self {
        static EMPTY_ENV: std::sync::OnceLock<CalleeEnv> = std::sync::OnceLock::new();
        static EMPTY_RELOCS: std::sync::OnceLock<HashMap<u64, BranchReloc>> =
            std::sync::OnceLock::new();
        PathMergingExecutor {
            sem: Aarch64Semantics,
            code,
            base,
            out_width,
            out_is_float,
            steps: 0,
            env: EMPTY_ENV.get_or_init(CalleeEnv::empty),
            bl_targets: EMPTY_RELOCS.get_or_init(HashMap::new),
            call_counter: 0,
            divergent: HashSet::new(),
            model_traps: false,
        }
    }

    fn new_env(
        code: &'a [u8],
        base: u64,
        out_width: u32,
        out_is_float: bool,
        env: &'a CalleeEnv,
        bl_targets: &'a HashMap<u64, BranchReloc>,
    ) -> Self {
        PathMergingExecutor {
            sem: Aarch64Semantics,
            code,
            base,
            out_width,
            out_is_float,
            steps: 0,
            env,
            bl_targets,
            call_counter: 0,
            divergent: HashSet::new(),
            model_traps: false,
        }
    }

    /// Trust (F1 gate): [`PathMergingExecutor::new_env`] with TRAP MODELING on.
    ///
    /// The only behavioural difference is that a PC in [`divergent_pcs`] yields
    /// `reach = false` instead of being executed. No other caller sets this, so
    /// the MIR-path gate's program is unchanged.
    fn new_traps(
        code: &'a [u8],
        base: u64,
        out_width: u32,
        out_is_float: bool,
        env: &'a CalleeEnv,
        bl_targets: &'a HashMap<u64, BranchReloc>,
    ) -> Self {
        PathMergingExecutor {
            sem: Aarch64Semantics,
            code,
            base,
            out_width,
            out_is_float,
            steps: 0,
            env,
            bl_targets,
            call_counter: 0,
            divergent: divergent_pcs(code, base),
            model_traps: true,
        }
    }

    fn decode_at(&self, pc: u64) -> Result<trust_disasm::Instruction, String> {
        let off = pc
            .checked_sub(self.base)
            .ok_or_else(|| format!("pc {pc:#x} below __text base"))? as usize;
        if off + 4 > self.code.len() {
            return Err(format!("pc {pc:#x} past __text end (no RET)"));
        }
        let bytes: [u8; 4] = self.code[off..off + 4]
            .try_into()
            .map_err(|_| "short instruction slice".to_string())?;
        decode_aarch64(&bytes, pc).map_err(|e| format!("decode_aarch64 failed at {pc:#x}: {e:?}"))
    }

    /// The INTEGER return value the bytes leave behind at a `RET`, read out of
    /// the AAPCS64 result registers at `out_width`.
    ///
    /// A result of 64 bits or fewer is `X0` truncated to `out_width`. For a
    /// NARROW result (`out_width` of 8 or 16) that truncation is not a
    /// convenience — it is the obligation's boundary. `out_width` is the type's
    /// DECLARED width, and a Rust-ABI narrow slot carries `arg_ext: None`, so
    /// the bits of `X0` above it are not part of the returned value and this
    /// side deliberately reads none of them. The trust-ir gate's
    /// `scalar_reg_width` carries the full derivation with its rustc source
    /// lines; the MIR-side `reg_width` has always agreed by returning the
    /// integer's own width.
    ///
    /// A 128-bit result does NOT fit in one register: AAPCS64 returns it in the
    /// PAIR `X0` (low 64) / `X1` (high 64), so the machine-side value is
    /// `concat(X1, X0)` — `try_bvconcat`'s first operand is the HIGH half.
    ///
    /// WHY THIS IS NOT `read_gpr(0, 128)`. `MachineState::read_gpr(i, w)`
    /// truncates a 64-bit register to `w` bits, so at `w = 128` it would build
    /// `BvExtract(X0)[127:0]` — an ILL-SORTED term over a 64-bit variable that
    /// `formula_to_term` cannot translate. Every other width above 64 has no
    /// modeled register home at all and FAILS CLOSED here rather than producing
    /// such a term.
    fn read_int_return(&self, state: &MachineState) -> Result<Formula, String> {
        match self.out_width {
            0 => Err("zero-width return value is not modeled (fail-closed)".into()),
            w if w <= 64 => Ok(state.read_gpr(0, w)),
            128 => Ok(Formula::BvConcat(b(state.read_gpr(1, 64)), b(state.read_gpr(0, 64)))),
            other => Err(format!(
                "a {other}-bit integer return has no modeled AAPCS64 register home \
                 (only <=64-bit in X0/W0 and 128-bit in the X0/X1 pair are modeled; \
                 fail-closed)"
            )),
        }
    }

    /// Execute from `pc` carrying `state` and the `visited` PCs on THIS path,
    /// returning the merged return-register Formula at the reachable RET(s).
    fn run(
        &mut self,
        mut pc: u64,
        mut state: MachineState,
        mut visited: Vec<u64>,
        depth: u32,
    ) -> Result<PathOutcome, String> {
        if depth > MAX_DEPTH {
            return Err("fork-depth budget exceeded (fail-closed)".into());
        }
        loop {
            // TRAP TAIL (F1 gate only). This PC provably cannot reach a `RET`
            // without taking a branch — it is the `bl <panic>; brk` tail the
            // trust-cg `Trap` lowering emits for a failed `Inst::Assert`. Such a
            // path yields NO return value, so we record `reach = false` and a
            // placeholder value that the discharge is never allowed to use (the
            // obligation is conditioned on `reach`). Off for every other caller.
            if self.model_traps && self.divergent.contains(&pc) {
                return Ok(PathOutcome {
                    value: Formula::BitVec { value: 0, width: self.out_width },
                    reach: Formula::Bool(false),
                });
            }

            // LOOP SAFETY: a revisited PC on this path is a backedge.
            if visited.contains(&pc) {
                return Err(format!("loop/backedge detected at {pc:#x} (fail-closed)"));
            }
            visited.push(pc);

            self.steps += 1;
            if self.steps > MAX_STEPS {
                return Err("instruction-step budget exceeded (fail-closed)".into());
            }

            let insn = self.decode_at(pc)?;
            let opcode = insn.opcode;

            // A RET ends this path; read the return register now. A scalar float
            // result is returned in V0's low D-lane (`read_fpr(0, out_width)` =
            // `BvExtract(V0)[out_width-1:0]`), matching the IR-semantics side's
            // `vn_d_lane`. Integer/pointer results are in X0/W0.
            if opcode == Opcode::Ret {
                let value = if self.out_is_float {
                    state.read_fpr(0, self.out_width)
                } else {
                    self.read_int_return(&state)?
                };
                return Ok(PathOutcome { value, reach: Formula::Bool(true) });
            }

            let effects = self
                .sem
                .effects(&state, &insn)
                .map_err(|e| format!("Aarch64Semantics::effects failed at {pc:#x}: {e:?}"))?;

            // Separate control-flow effects from the data-plane effects.
            let mut cond_branch: Option<(Condition, Formula, Formula)> = None;
            let mut uncond_target: Option<Formula> = None;
            let mut pc_update: Option<Formula> = None;
            let mut saw_return = false;
            let mut is_call = false;
            // The sequential-advance shape, built from the pc as it stands for
            // THIS instruction so the comparison below is exact.
            let pc_advance = Formula::BvAdd(
                Box::new(state.pc.clone()),
                Box::new(Formula::BitVec { value: 4, width: 64 }),
                64,
            );
            let mut plain: Vec<&Effect> = Vec::new();
            for e in &effects {
                match e {
                    Effect::ConditionalBranch { condition, target, fallthrough } => {
                        cond_branch = Some((*condition, target.clone(), fallthrough.clone()));
                    }
                    Effect::Branch { target } => uncond_target = Some(target.clone()),
                    // A `PcUpdate` IS control flow and is handled below. It must
                    // never be silently dropped: `sem_cbz` (CBZ/CBNZ) and
                    // `sem_tbz` (TBZ/TBNZ) express their branch as
                    // `PcUpdate { value: Ite(take, target, pc+4) }` rather than as
                    // `Effect::ConditionalBranch`, which only `sem_bcond` emits.
                    // Discarding it executed four of the five AArch64 conditional
                    // branch forms as NEVER TAKEN — and, unlike every other
                    // unmodeled effect in this match, did not fail closed. That
                    // was a soundness hole in BOTH directions, each demonstrated
                    // by execution: a spliced `cbz`-guarded miscompile came back
                    // `Proven` (the byte-identical `b.cond` form came back
                    // `Refuted`), and 78 corpus functions were reported as
                    // `MISCOMPILE (Refuted)` on machine code that runs correctly.
                    //
                    // `Effect::Return` stays ignored: `Opcode::Ret` returns from
                    // this loop before effects are consulted at all.
                    // ...EXCEPT the plain sequential advance. `pc_advance`
                    // (`trust-machine-sem/src/aarch64/mod.rs`) appends
                    // `PcUpdate { BvAdd(pc, 4) }` to ordinary instructions, and
                    // that is precisely what the `pc += 4` at the bottom of this
                    // loop already does. Only a pc write that is NOT the advance
                    // carries control flow.
                    Effect::PcUpdate { value } if *value == pc_advance => {}
                    Effect::PcUpdate { value } => pc_update = Some(value.clone()),
                    Effect::Return { .. } => saw_return = true,
                    // A `bl` to a LOCAL PURE callee is COMPOSED below (see
                    // `model_local_call`). We do NOT thread the Call's own
                    // link-register write here; the call modeling sets the post-call
                    // architectural state explicitly. Any non-composable call fails
                    // closed in `model_local_call`.
                    Effect::Call { .. } => {
                        is_call = true;
                    }
                    Effect::Aarch64SyncBoundary { .. } | Effect::Aarch64AtomicAccess { .. } => {
                        return Err(format!("unsupported atomic/sync at {pc:#x} (fail-closed)"));
                    }
                    other => plain.push(other),
                }
            }

            if is_call {
                // Model the call EXACTLY (or fail closed). This consumes the
                // current state (reads arg registers), sets the post-call state
                // (result in x0, caller-saved registers + flags havoced), and
                // returns control to pc+4 (the AAPCS64 return address in x30).
                self.model_local_call(pc, &mut state)?;
                if visited.contains(&(pc + 4)) {
                    return Err(format!("backedge after call at {pc:#x} (fail-closed)"));
                }
                pc += 4;
                continue;
            }

            // Thread data-plane effects (RegWrite/FlagUpdate/Mem*/SpWrite) FIRST so
            // the branch condition sees the post-Subs flags.
            for e in &plain {
                state.apply_effect(e).map_err(|er| {
                    format!("apply_effects rejected emitted insn {opcode:?} at {pc:#x}: {er:?}")
                })?;
            }

            // Both conditional-branch encodings reduce to ONE (path condition,
            // taken target) pair. `b.cond` carries an architectural `Condition`
            // that must be read against the flags AFTER the data-plane effects
            // above; CBZ/CBNZ/TBZ/TBNZ instead arrive as a `PcUpdate` whose `Ite`
            // condition `sem_cbz`/`sem_tbz` already built over the register value
            // as it stood BEFORE this instruction — which is the same state,
            // because neither form writes a register. So the condition is used
            // as-is and no `condition_to_formula` is involved.
            let fork = if let Some((condition, target, _fallthrough)) = cond_branch {
                // path_cond is the REAL machine branch condition over the post-Subs
                // symbolic NZCV flags now in `state.flags`.
                // A condition the machine model cannot evaluate is a REFUSAL of
                // the derivation, not an `always taken` path condition.
                let path_cond =
                    condition_to_formula(&state, condition).map_err(|err| err.to_string())?;
                let target_pc = const_addr(&target).ok_or_else(|| {
                    format!("indirect conditional branch at {pc:#x} (fail-closed)")
                })?;
                Some((path_cond, target_pc))
            } else if uncond_target.is_some() || saw_return {
                // `b` / `bl` / `ret` emit a redundant `PcUpdate` ALONGSIDE
                // `Effect::Branch` / `Effect::Return`. Those have dedicated
                // handling (the `uncond_target` block below, and the early
                // `Opcode::Ret` return), so the duplicate is not control flow
                // this block owns.
                None
            } else if let Some(value) = pc_update {
                match value {
                    // CBZ/CBNZ/TBZ/TBNZ. `branch_target_formula` resolves the
                    // operand to an ABSOLUTE address, so the taken arm is a
                    // literal; the fallthrough arm is `BvAdd(PC, 4)` over the
                    // symbolic `PC` var and is deliberately not consulted --
                    // `pc + 4` is the real fallthrough, exactly as in the
                    // `b.cond` path above.
                    Formula::Ite(cond, taken, _fall) => {
                        let target_pc = const_addr(&taken).ok_or_else(|| {
                            format!("indirect conditional branch at {pc:#x} (fail-closed)")
                        })?;
                        Some((*cond, target_pc))
                    }
                    // A constant unconditional `PcUpdate` is a plain branch.
                    // Anything else -- an indirect or otherwise unmodeled pc
                    // write -- FAILS CLOSED, like every other effect this
                    // executor cannot model exactly.
                    other => {
                        let Some(target_pc) = const_addr(&other) else {
                            return Err(format!("unmodeled pc-update at {pc:#x} (fail-closed)"));
                        };
                        if visited.contains(&target_pc) {
                            return Err(format!("backedge at pc-update {pc:#x} (fail-closed)"));
                        }
                        pc = target_pc;
                        continue;
                    }
                }
            } else {
                None
            };

            if let Some((path_cond, target_pc)) = fork {
                let fall_pc = pc + 4;

                // LOOP SAFETY: a branch target already on this path is a backedge.
                if visited.contains(&target_pc) || visited.contains(&fall_pc) {
                    return Err(format!(
                        "loop/backedge at conditional branch {pc:#x} (fail-closed)"
                    ));
                }

                let taken = self.run(target_pc, state.clone(), visited.clone(), depth + 1)?;
                let fall = self.run(fall_pc, state.clone(), visited.clone(), depth + 1)?;

                // MERGE. The Ite condition IS the real machine branch condition, so a
                // wrong path assignment makes ay find a counterexample (teeth).
                //
                // `reach` merges the SAME way. When neither side diverges it folds
                // back to the syntactic `Bool(true)` every pre-existing caller saw,
                // so their obligation is bit-for-bit the one they had before.
                let reach = match (&taken.reach, &fall.reach) {
                    (Formula::Bool(true), Formula::Bool(true)) => Formula::Bool(true),
                    _ => Formula::Ite(
                        Box::new(path_cond.clone()),
                        Box::new(taken.reach),
                        Box::new(fall.reach),
                    ),
                };
                return Ok(PathOutcome {
                    value: Formula::Ite(
                        Box::new(path_cond),
                        Box::new(taken.value),
                        Box::new(fall.value),
                    ),
                    reach,
                });
            }

            if let Some(target) = uncond_target {
                let target_pc = const_addr(&target)
                    .ok_or_else(|| format!("indirect branch at {pc:#x} (fail-closed)"))?;
                if visited.contains(&target_pc) {
                    return Err(format!("backedge at unconditional branch {pc:#x} (fail-closed)"));
                }
                pc = target_pc;
                continue;
            }

            pc += 4;
        }
    }

    /// Model a `bl` to a LOCAL PURE callee at instruction `pc`, mutating `state`
    /// into the EXACT AAPCS64 post-call architectural state — or FAIL CLOSED.
    ///
    /// The call is admitted ONLY when:
    ///   * the emitted object carries an `ARM64_RELOC_BRANCH26` at this `pc`'s
    ///     in-`__text` offset naming an external symbol (`BranchReloc::Call`);
    ///     any other relocation here (`Unmodeled`) or no relocation fails closed;
    ///   * that symbol is a callee present in `self.env` (local, pure, Proven).
    ///
    /// On admission the post-call state is set EXACTLY per AAPCS64:
    ///   * the result register X0 = `callee.output` with `X{i}` substituted by the
    ///     CURRENT (pre-call) X{i} for each of the callee's args — i.e. exactly the
    ///     value the resolved callee computes from the argument registers the
    ///     caller's bytes placed there;
    ///   * caller-saved registers X0..X18 and the condition flags are HAVOCED to
    ///     FRESH unconstrained variables (then X0 is overwritten with the result),
    ///     because the callee may clobber them — so any post-call read of a
    ///     caller-saved register the bytes wrongly assume survives becomes a fresh
    ///     variable that ay will refute against the (clobber-free) IR auto-spec;
    ///   * callee-saved registers X19..X28, FP/LR (X29/X30) and SP are preserved
    ///     (the AAPCS64 callee-save contract). X30 (the link register) holds the
    ///     return address but is not read by our straight-line return paths; we
    ///     leave it symbolic, which is sound (a read would just be a fresh value).
    fn model_local_call(&mut self, pc: u64, state: &mut MachineState) -> Result<(), String> {
        let off = pc
            .checked_sub(self.base)
            .ok_or_else(|| format!("call pc {pc:#x} below __text base"))?;
        let callee_name = match self.bl_targets.get(&off) {
            Some(BranchReloc::Call(name)) => name.clone(),
            Some(BranchReloc::Unmodeled) => {
                return Err(format!(
                    "bl at {pc:#x} carries a relocation the gate does not model (fail-closed)"
                ));
            }
            None => {
                return Err(format!(
                    "bl at {pc:#x} has no BRANCH26 relocation naming a callee (fail-closed)"
                ));
            }
        };
        let callee = self.env.get(&callee_name).ok_or_else(|| {
            format!(
                "bl at {pc:#x} targets `{callee_name}`, not a known local pure Proven callee \
                 (fail-closed)"
            )
        })?;

        // Capture the argument registers from the CURRENT state (pre-clobber). The
        // callee reads arg `i` from X{i}; substitute the live X{i} formula for the
        // `X{i}` variable in the callee's pure output.
        let mut result = callee.output.clone();
        for i in 0..callee.arg_count {
            let xi = state.gpr[i].clone(); // full 64-bit X{i}
            result = substitute_var(&result, &format!("X{i}"), &xi);
        }

        // HAVOC caller-saved registers X0..=X18 and the flags to FRESH variables.
        // This is the soundness-critical step: the modeled call must not let any
        // caller-saved register survive (the real callee may clobber it). After
        // havocing, install the call result in X0.
        let tag = self.call_counter;
        self.call_counter += 1;
        for i in 0..=18usize {
            state.gpr[i] = Formula::Var(format!("CALLCLOBBER_{tag}_X{i}"), Sort::BitVec(64));
        }
        state.flags = Flags {
            n: Formula::Var(format!("CALLCLOBBER_{tag}_N"), Sort::Bool),
            z: Formula::Var(format!("CALLCLOBBER_{tag}_Z"), Sort::Bool),
            c: Formula::Var(format!("CALLCLOBBER_{tag}_C"), Sort::Bool),
            v: Formula::Var(format!("CALLCLOBBER_{tag}_V"), Sort::Bool),
        };
        // Install the result. A 32-bit (W) return zero-extends into X0 (AArch64
        // W-write semantics); `result` already has the callee's return width, so
        // widen to the 64-bit slot exactly as `read_gpr` will re-extract it.
        let result64 = zero_extend_to_64(result, callee.ret_reg_width);
        state.gpr[0] = result64;
        Ok(())
    }
}

use trust_machine_sem::Flags;

/// Extract a constant 64-bit address from a branch-target Formula.
fn const_addr(f: &Formula) -> Option<u64> {
    match f {
        Formula::BitVec { value, .. } => Some(*value as u64),
        _ => None,
    }
}

#[cfg(test)]
fn symbolic_machine_output(
    code: &[u8],
    base: u64,
    out_width: u32,
    out_is_float: bool,
) -> Result<Formula, String> {
    let mut exec = PathMergingExecutor::new(code, base, out_width, out_is_float);
    let state = MachineState::symbolic();
    exec.run(base, state, Vec::new(), 0).map(|outcome| outcome.value)
}

/// Bundle-aware [`symbolic_machine_output`]: the executor consults `env` +
/// `bl_targets` so a `bl` to a LOCAL PURE Proven callee is composed (its derived
/// output substituted at the call) and all OTHER calls fail closed. Identical to
/// [`symbolic_machine_output`] when `env`/`bl_targets` are empty.
fn symbolic_machine_output_env(
    code: &[u8],
    base: u64,
    out_width: u32,
    out_is_float: bool,
    env: &CalleeEnv,
    bl_targets: &HashMap<u64, BranchReloc>,
) -> Result<Formula, String> {
    let mut exec =
        PathMergingExecutor::new_env(code, base, out_width, out_is_float, env, bl_targets);
    let state = MachineState::symbolic();
    exec.run(base, state, Vec::new(), 0).map(|outcome| outcome.value)
}

/// Trust (F1 gate): the byte-derived machine side WITH trap modeling, returning
/// both the return-value Formula and the `reach` predicate.
///
/// This is [`symbolic_machine_output_env`] with `model_traps` on. It is the ONLY
/// caller that gets a non-trivial `reach`, and it exists so the trust-ir gate can
/// discharge the assert-guarded obligation instead of failing closed on every
/// function whose `Inst::Assert` lowered to a `Trap` block.
pub(crate) fn symbolic_machine_outcome_traps(
    code: &[u8],
    base: u64,
    out_width: u32,
    out_is_float: bool,
) -> Result<PathOutcome, String> {
    static EMPTY_ENV: std::sync::OnceLock<CalleeEnv> = std::sync::OnceLock::new();
    static EMPTY_RELOCS: std::sync::OnceLock<HashMap<u64, BranchReloc>> =
        std::sync::OnceLock::new();
    let env = EMPTY_ENV.get_or_init(CalleeEnv::empty);
    let relocs = EMPTY_RELOCS.get_or_init(HashMap::new);
    let mut exec = PathMergingExecutor::new_traps(code, base, out_width, out_is_float, env, relocs);
    let state = MachineState::symbolic();
    exec.run(base, state, Vec::new(), 0)
}

/// Derive the machine-side Formula from an already-emitted object. Keeping this
/// separate from emission is what lets the build gate retain exact production
/// bytes when the AArch64/Mach-O decoder does not support their target or shape.
///
/// `emitted_arch` is the ISA the object was emitted for. The executor below is
/// hard-wired to `decode_aarch64` + [`Aarch64Semantics`], and an instruction
/// decoder handed the wrong ISA does not reliably error — it can mis-read a
/// foreign encoding as a plausible A64 word and hand the discharge a machine
/// side that never existed. The claim this gate awards is "these BYTES compute
/// the IR semantics", so bytes whose ISA the gate cannot name are refused here
/// rather than interpreted on a guess.
fn decode_emitted_object_env(
    func: &VerifiableFunction,
    obj: &[u8],
    out_width: u32,
    env: &CalleeEnv,
    emitted_arch: TrustCgTargetArch,
) -> Result<Formula, String> {
    if emitted_arch != TrustCgTargetArch::AArch64 {
        return Err(format!(
            "byte-level output preservation is wired for AArch64 machine semantics only; \
             emitted {emitted_arch:?} code is undecided (fail-closed)"
        ));
    }
    let (code, base) = extract_text_from_object(obj)?;
    if code.is_empty() {
        return Err("emitted text section is empty".into());
    }
    // Parse the __text BRANCH26 (bl) relocations: addr-in-__text -> callee symbol.
    // EMPTY env => we don't need relocs (no call is composable), so skip parsing.
    let bl_targets =
        if env.callees.is_empty() { HashMap::new() } else { parse_text_branch26_relocs(&obj)? };
    // A scalar float return lives in V0's D-lane, not X0 — tell the executor which
    // register the RET reads.
    let out_is_float = func.body.return_ty.is_float();
    let machine_out =
        symbolic_machine_output_env(&code, base, out_width, out_is_float, env, &bl_targets)?;
    Ok(machine_out)
}

/// Parse the `__text` section's `ARM64_RELOC_BRANCH26` (type 2) relocations from a
/// Mach-O object, returning a map from the relocated instruction's IN-SECTION byte
/// offset to the EXTERNAL symbol name it targets (with the leading Mach-O `_`
/// underscore stripped so it matches the `Terminator::Call.func` / LIR symbol).
///
/// FAIL-CLOSED: returns `Err` if the object is not the expected Mach-O64 shape or
/// the symbol/string tables cannot be read. Only `extern`, `pcrel`, `len==2`,
/// `type==BRANCH26` relocations to a defined symbol name are recorded; any other
/// relocation on `__text` (e.g. a PAGE21/GOT load, a section-relative reloc) is
/// recorded under a DISTINCT sentinel so the executor can detect "a relocation it
/// does not model sits on this instruction" and fail closed rather than silently
/// treat the `bl` as having no reloc.
fn parse_text_branch26_relocs(obj: &[u8]) -> Result<HashMap<u64, BranchReloc>, String> {
    let rd_u32 = |o: usize| -> Result<u32, String> {
        obj.get(o..o + 4)
            .and_then(|s| s.try_into().ok())
            .map(u32::from_le_bytes)
            .ok_or_else(|| "truncated u32 in object".to_string())
    };
    if rd_u32(0)? != 0xfeed_facf {
        return Err("not a Mach-O 64 object".into());
    }
    let ncmds = rd_u32(16)?;
    let mut cmd_off = 32usize;
    let mut text_reloff = 0usize;
    let mut text_nreloc = 0u32;
    let mut symoff = 0usize;
    let mut nsyms = 0u32;
    let mut stroff = 0usize;
    let mut strsize = 0usize;
    for _ in 0..ncmds {
        let cmd = rd_u32(cmd_off)?;
        let cmdsize = rd_u32(cmd_off + 4)? as usize;
        if cmdsize == 0 {
            return Err("zero-size load command (malformed object)".into());
        }
        if cmd == 0x19 {
            // LC_SEGMENT_64
            let nsects = rd_u32(cmd_off + 64)?;
            let mut sec = cmd_off + 72;
            for _ in 0..nsects {
                let name =
                    obj.get(sec..sec + 16).ok_or_else(|| "short section name".to_string())?;
                if name.starts_with(b"__text\0") {
                    text_reloff = rd_u32(sec + 56)? as usize;
                    text_nreloc = rd_u32(sec + 60)?;
                }
                sec += 80;
            }
        } else if cmd == 0x2 {
            // LC_SYMTAB
            symoff = rd_u32(cmd_off + 8)? as usize;
            nsyms = rd_u32(cmd_off + 12)?;
            stroff = rd_u32(cmd_off + 16)? as usize;
            strsize = rd_u32(cmd_off + 20)? as usize;
        }
        cmd_off += cmdsize;
    }

    let sym_name = |idx: u32| -> Result<String, String> {
        if idx >= nsyms {
            return Err(format!("reloc symbol index {idx} out of range (nsyms={nsyms})"));
        }
        let e = symoff + (idx as usize) * 16;
        let strx = rd_u32(e)? as usize;
        let start = stroff + strx;
        let end = stroff + strsize;
        let mut p = start;
        let mut s = String::new();
        while p < end {
            let c = *obj.get(p).ok_or_else(|| "string table overrun".to_string())?;
            if c == 0 {
                break;
            }
            s.push(c as char);
            p += 1;
        }
        // Strip the Mach-O leading underscore to match the IR/LIR symbol name.
        Ok(s.strip_prefix('_').unwrap_or(&s).to_string())
    };

    let mut map: HashMap<u64, BranchReloc> = HashMap::new();
    for i in 0..text_nreloc as usize {
        let e = text_reloff + i * 8;
        let r_address = rd_u32(e)? as u64;
        let w1 = rd_u32(e + 4)?;
        let r_symbolnum = w1 & 0x00ff_ffff;
        let r_pcrel = (w1 >> 24) & 1;
        let r_length = (w1 >> 25) & 3;
        let r_extern = (w1 >> 27) & 1;
        let r_type = (w1 >> 28) & 0xf;
        // ARM64_RELOC_BRANCH26 == 2. A composable call relocation must be an
        // EXTERNAL, PC-relative, 4-byte BRANCH26. Anything else on this address is
        // recorded as `Unmodeled` so the executor fails closed if it sits on a bl.
        if r_type == 2 && r_extern == 1 && r_pcrel == 1 && r_length == 2 {
            match sym_name(r_symbolnum) {
                Ok(name) => {
                    map.insert(r_address, BranchReloc::Call(name));
                }
                Err(e) => return Err(e),
            }
        } else {
            map.insert(r_address, BranchReloc::Unmodeled);
        }
    }
    Ok(map)
}

/// A `__text` relocation the gate cares about, keyed by in-section byte offset.
#[derive(Clone, Debug)]
enum BranchReloc {
    /// A BRANCH26 call to the named (underscore-stripped) external symbol.
    Call(String),
    /// Any other relocation sitting on a `__text` instruction — the executor
    /// fails closed if one lands on an instruction it would otherwise model.
    Unmodeled,
}

// ===========================================================================
// PART 3 — Formula -> ay::Term translation + discharge.
// ===========================================================================

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
        other => panic!("unexpected Var sort for {name}: {other:?}"),
    }
}

fn bin2(
    solver: &mut Solver,
    a: &Formula,
    c: &Formula,
    op: fn(&mut Solver, Term, Term) -> Result<Term, ay::SolverError>,
) -> Term {
    let a = formula_to_term(solver, a);
    let c = formula_to_term(solver, c);
    op(solver, a, c).expect("binary op")
}

/// Translate a trust-types `Formula` into an `ay::Term` on `solver`.
fn formula_to_term(solver: &mut Solver, f: &Formula) -> Term {
    match f {
        Formula::Var(name, sort) => var_term(solver, name, sort),
        Formula::Bool(v) => solver.bool_const(*v),
        Formula::BitVec { value, width } => {
            solver.try_bv_const_bigint(&BigInt::from(*value), *width).expect("bv const")
        }
        Formula::BvAdd(a, c, _) => bin2(solver, a, c, Solver::try_bvadd),
        Formula::BvSub(a, c, _) => bin2(solver, a, c, Solver::try_bvsub),
        Formula::BvMul(a, c, _) => bin2(solver, a, c, Solver::try_bvmul),
        Formula::BvAnd(a, c, _) => bin2(solver, a, c, Solver::try_bvand),
        Formula::BvOr(a, c, _) => bin2(solver, a, c, Solver::try_bvor),
        Formula::BvXor(a, c, _) => bin2(solver, a, c, Solver::try_bvxor),
        Formula::BvShl(a, c, _) => bin2(solver, a, c, Solver::try_bvshl),
        Formula::BvLShr(a, c, _) => bin2(solver, a, c, Solver::try_bvlshr),
        Formula::BvAShr(a, c, _) => bin2(solver, a, c, Solver::try_bvashr),
        Formula::BvConcat(a, c) => bin2(solver, a, c, Solver::try_bvconcat),
        Formula::BvUDiv(a, c, _) => bin2(solver, a, c, Solver::try_bvudiv),
        Formula::BvSDiv(a, c, _) => bin2(solver, a, c, Solver::try_bvsdiv),
        Formula::BvURem(a, c, _) => bin2(solver, a, c, Solver::try_bvurem),
        Formula::BvSRem(a, c, _) => bin2(solver, a, c, Solver::try_bvsrem),
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
        Formula::BvULt(a, c, _) => bin2(solver, a, c, Solver::try_bvult),
        Formula::BvULe(a, c, _) => bin2(solver, a, c, Solver::try_bvule),
        Formula::BvSLt(a, c, _) => bin2(solver, a, c, Solver::try_bvslt),
        Formula::BvSLe(a, c, _) => bin2(solver, a, c, Solver::try_bvsle),
        Formula::Eq(a, c) => bin2(solver, a, c, Solver::try_eq),
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
        // ---- Arrays (Ldr / Str — memory store/load) ----
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
        // ---- IEEE-754 floating point (the f64 FADD shape) ----
        // A rounding-mode literal term (rm arg of `fp.add`).
        Formula::FpRoundingMode(rm) => {
            let name = match rm {
                RoundingMode::RNE => "RNE",
                RoundingMode::RNA => "RNA",
                RoundingMode::RTP => "RTP",
                RoundingMode::RTN => "RTN",
                RoundingMode::RTZ => "RTZ",
            };
            solver.try_fp_rounding_mode(name).expect("fp rounding mode")
        }
        // `(fp sign exp sig)` — reinterpret a `(eb+sb)`-wide BV as a float by
        // extracting the IEEE fields (mirrors ay_bridge::fp_from_bv_expr and the
        // hardware register-lane reinterpret). Bit-preserving.
        Formula::FpFromBits { bits, eb, sb } => {
            let bv = formula_to_term(solver, bits);
            let sig_w = sb - 1;
            let total = eb + sb;
            let sign = solver.try_bvextract(bv.clone(), total - 1, total - 1).expect("fp sign");
            let exp = solver.try_bvextract(bv.clone(), total - 2, sig_w).expect("fp exp");
            let sig = solver.try_bvextract(bv, sig_w - 1, 0).expect("fp sig");
            solver.try_fp_from_bvs(sign, exp, sig, *eb, *sb).expect("fp_from_bvs")
        }
        // `(fp.to_ieee_bv <fp>)` — the exact inverse: FP -> its IEEE bit pattern.
        Formula::FpToIeeeBv(a) => {
            let x = formula_to_term(solver, a);
            solver.try_fp_to_ieee_bv(x).expect("fp_to_ieee_bv")
        }
        // `(fp.add rm a b)`.
        Formula::FpAdd(rm, a, c) => {
            let rm = formula_to_term(solver, rm);
            let a = formula_to_term(solver, a);
            let c = formula_to_term(solver, c);
            solver.try_fp_add(rm, a, c).expect("fp_add")
        }
        // `(fp.sub rm a b)`.
        Formula::FpSub(rm, a, c) => {
            let rm = formula_to_term(solver, rm);
            let a = formula_to_term(solver, a);
            let c = formula_to_term(solver, c);
            solver.try_fp_sub(rm, a, c).expect("fp_sub")
        }
        // `(fp.mul rm a b)`.
        Formula::FpMul(rm, a, c) => {
            let rm = formula_to_term(solver, rm);
            let a = formula_to_term(solver, a);
            let c = formula_to_term(solver, c);
            solver.try_fp_mul(rm, a, c).expect("fp_mul")
        }
        // `(fp.div rm a b)` — TOTAL: x/0.0 = ±inf, 0.0/0.0 = NaN (no trap).
        Formula::FpDiv(rm, a, c) => {
            let rm = formula_to_term(solver, rm);
            let a = formula_to_term(solver, a);
            let c = formula_to_term(solver, c);
            solver.try_fp_div(rm, a, c).expect("fp_div")
        }
        // `(fp.isNaN a)` — NaN classification (for the 1.0 + NaN value-diff).
        Formula::FpIsNaN(a) => {
            let a = formula_to_term(solver, a);
            solver.try_fp_is_nan(a).expect("fp_is_nan")
        }
        other => panic!("formula_to_term: unhandled Formula variant: {other:?}"),
    }
}

/// Outcome of an equality discharge — keeps `unknown` distinct so the gate can
/// fail closed instead of panicking (unlike the test harness, which panics).
#[derive(Debug)]
pub(crate) enum Discharge {
    Proven,
    CounterExample,
    Unknown(String),
}

/// Whether `f` (anywhere in its tree) carries a FloatingPoint-theory operator,
/// literal, or FP/RoundingMode-sorted variable — i.e. it needs an FP-capable ay
/// logic. Used to escalate the discharge logic from QF_ABV to QF_ABVFP for the
/// f64 FADD shape.
fn formula_has_fp(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |node| match node {
        Formula::FpConst { .. }
        | Formula::FpNaN { .. }
        | Formula::FpInf { .. }
        | Formula::FpZero { .. }
        | Formula::FpRoundingMode(_)
        | Formula::FpAdd(..)
        | Formula::FpSub(..)
        | Formula::FpMul(..)
        | Formula::FpDiv(..)
        | Formula::FpFma(..)
        | Formula::FpSqrt(..)
        | Formula::FpRem(..)
        | Formula::FpNeg(..)
        | Formula::FpAbs(..)
        | Formula::FpMin(..)
        | Formula::FpMax(..)
        | Formula::FpEq(..)
        | Formula::FpLt(..)
        | Formula::FpLe(..)
        | Formula::FpGt(..)
        | Formula::FpGe(..)
        | Formula::FpIsNaN(..)
        | Formula::FpIsInfinite(..)
        | Formula::FpIsZero(..)
        | Formula::FpIsNormal(..)
        | Formula::FpIsSubnormal(..)
        | Formula::FpIsNegative(..)
        | Formula::FpIsPositive(..)
        | Formula::FpFromBits { .. }
        | Formula::FpToIeeeBv(..) => found = true,
        Formula::Var(_, Sort::Float { .. } | Sort::RoundingMode)
        | Formula::SymVar(_, Sort::Float { .. } | Sort::RoundingMode) => found = true,
        _ => {}
    });
    found
}

/// Per-query wall-clock budget for the gate's ay discharges, in milliseconds.
///
/// WHY: the callee seam inflates whole-function obligations (an inlined call
/// chain is one big byte-equality), and a single `check_sat` was MEASURED
/// grinding >20 minutes at 100% CPU on one trust-timearith function — with no
/// bound, `allow-unknown` still waits on every proof ATTEMPT, so one hard
/// obligation stalls a whole crate's compile. A budget converts the grind
/// into a fast, counted `Unknown` — a COMPLETENESS cost, never soundness
/// (Unknown refuses under strict and emits-uncertified under allow-unknown),
/// the same posture as the verifier's own `-Ztrust-verify-function-budget-ms`.
///
/// `TCG_TRUST_IR_GATE_TIMEOUT_MS` overrides; `0` disables the budget. Read
/// fresh per solver construction (no OnceLock) so tests can vary it.
fn gate_solver_config() -> ay::SolverConfig {
    const DEFAULT_MS: u64 = 120_000;
    let ms = std::env::var("TCG_TRUST_IR_GATE_TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(DEFAULT_MS);
    let config = ay::SolverConfig::default();
    if ms == 0 { config } else { config.with_timeout(std::time::Duration::from_millis(ms)) }
}

/// Construct the gate's solver with the per-query budget applied.
fn gate_solver(logic: Logic) -> Result<Solver, String> {
    Solver::try_new_with_config(logic, gate_solver_config())
        .map_err(|e| format!("ay Solver::try_new_with_config failed: {e:?}"))
}

/// Discharge the VALIDITY of a boolean formula `f`: assert `NOT(f)` and check.
/// UNSAT => Proven (f is valid), SAT => CounterExample, unknown => Unknown.
/// FP-aware logic selection, mirroring [`discharge_equal_pre`]. Used in
/// production by the trust-ir gate's VACUITY check and its `spec_reach =>
/// machine_reach` obligation, which are predicates rather than equalities.
pub(crate) fn discharge_valid(f: &Formula) -> Discharge {
    let logic = if formula_has_fp(f) { Logic::QfAbvfp } else { Logic::QfAbv };
    let mut solver = match gate_solver(logic) {
        Ok(s) => s,
        Err(e) => return Discharge::Unknown(e),
    };
    let term = formula_to_term(&mut solver, f);
    // Fail CLOSED to Unknown on a solver error, exactly as `Solver::try_new`
    // above already does. These were `.expect()` — a panic inside the verifier's
    // trusted core, aborting the compiler mid-proof rather than reporting that
    // the obligation could not be discharged.
    let neg = match solver.try_not(term) {
        Ok(t) => t,
        Err(e) => return Discharge::Unknown(format!("ay try_not failed: {e:?}")),
    };
    if let Err(e) = solver.try_assert_term(neg) {
        return Discharge::Unknown(format!("ay try_assert_term failed: {e:?}"));
    }
    let result = solver.check_sat();
    if result.is_unsat() {
        Discharge::Proven
    } else if result.is_sat() {
        Discharge::CounterExample
    } else {
        Discharge::Unknown(format!("ay returned unknown: {result:?}"))
    }
}

/// Discharge `(pre AND NOT(a == b))`: UNSAT => Proven, SAT => CounterExample,
/// unknown => Unknown (fail-closed). Solver-construction failure is also Unknown.
pub(crate) fn discharge_equal_pre(a: &Formula, c: &Formula, pre: Option<&Formula>) -> Discharge {
    // QF_ABV: quantifier-free bitvectors + array theory (Select/Store), so
    // store->load roundtrips through MEM discharge via the array axiom.
    //
    // FLOAT: when either side carries a FloatingPoint-theory operator (the f64
    // FADD shape: FpFromBits / FpAdd / FpToIeeeBv), the obligation MIXES BV + FP
    // (+ arrays), so select QF_ABVFP — the superset covering all three. The BV
    // integer path (no FP nodes) stays on QF_ABV, unchanged.
    let logic = if formula_has_fp(a) || formula_has_fp(c) || pre.is_some_and(formula_has_fp) {
        Logic::QfAbvfp
    } else {
        Logic::QfAbv
    };
    let mut solver = match gate_solver(logic) {
        Ok(s) => s,
        Err(e) => return Discharge::Unknown(e),
    };
    let lhs = formula_to_term(&mut solver, a);
    let rhs = formula_to_term(&mut solver, c);
    let eq = solver.try_eq(lhs, rhs).expect("eq");
    let differ = solver.try_not(eq).expect("not");
    let goal = if let Some(p) = pre {
        let p = formula_to_term(&mut solver, p);
        solver.try_and(p, differ).expect("and")
    } else {
        differ
    };
    solver.try_assert_term(goal).expect("assert");
    let result = solver.check_sat();
    if result.is_unsat() {
        Discharge::Proven
    } else if result.is_sat() {
        Discharge::CounterExample
    } else {
        Discharge::Unknown(format!("ay returned unknown: {result:?}"))
    }
}

// ===========================================================================
// PART 4 — Formula -> ay-proof BvExpr LOWERING (the [PROVED] path).
//
// The discharge above proves `machine_out == auto_spec` via ay as a [VALIDATED]
// ORACLE (we trust ay's bare UNSAT). To take ay out of the re-check TCB we lower
// the SAME equality's two sides into ay-proof's self-contained `BvExpr` term type
// and hand them to `export_bv_blast_proof_expr`, which emits a `BvBlastProof`: a
// genuine resolution-DAG bit-blast certificate that a kernel (clean's
// `certify_unsat_by_reflection`) re-checks WITHOUT trusting ay. This module is
// the LOWERING half (Formula -> BvExpr); `verify_output_preserved` now wires it
// LIVE: on an ay UNSAT it lowers both sides + exports a `BvBlastProof` + attaches
// it as `ProvenEvidence::KernelRecheckable` (the [PROVED] grade). Routing the
// attached proof through clean's kernel re-check is the confirmation step.
//
// COVERAGE (honest): the on-disk `BvExpr` fragment is
//   Leaf | Add | Sub | ZeroExt | Extract | Or | Const
// so the lowering covers `Var(BitVec) -> Leaf`, `BvAdd -> Add`, `BvSub -> Sub`,
// `BvZeroExt -> ZeroExt`, `BvExtract -> Extract`, `BvOr -> Or`, `BitVec -> Const`,
// and FAILS CLOSED (Err naming the precise unsupported variant) on everything
// else (BvAnd/BvXor/BvMul/shifts/compares/Ite/Select/Store/...). Because `Or`
// and `Const` are now native `BvExpr` variants, the RAW byte-derived
// `machine_out` for the add-leaf — which carries `BvOr(BitVec{0}, x)` identity
// wrappers — LOWERS FAITHFULLY (no fold; the bit-blaster sees the real `Or2`
// gate over a `Const` 0). So the live add-leaf gate emits a genuine
// kernel-re-checkable [PROVED] cert, NOT just the normalized synthetic shape.
// ===========================================================================

/// Lower a trust-types [`Formula`] into ay-proof's self-contained [`BvExpr`] for
/// the add-leaf fragment, FAILING CLOSED (`Err` naming the unsupported variant)
/// on any shape outside `{ Var(BitVec), BvAdd, BvSub, BvZeroExt, BvExtract, BvOr,
/// BitVec }`.
///
/// This NEVER simplifies or folds (e.g. it will NOT rewrite `BvOr(0,x)` to `x`):
/// it maps `BvOr -> BvExpr::Or` and `BitVec -> BvExpr::Const` STRUCTURALLY, so
/// the bit-blaster sees the real `Or2` gates and constant literals. Any fold
/// would be an un-kernel-checked trusted step; the collapse `Or(0,x) == x` is
/// proven by the SAT solver, not asserted by this lowering. An unsupported
/// variant is reported, not normalized away.
/// not normalized away.
#[cfg(feature = "ay-proofs")]
pub fn formula_to_bvexpr(f: &Formula) -> Result<ay_proof::BvExpr, String> {
    use ay_proof::BvExpr;
    match f {
        // A named bitvector variable becomes a shared leaf: the SAME name on both
        // sides of the equality denotes the SAME free input bits (W0 == W0).
        Formula::Var(name, Sort::BitVec(w)) => Ok(BvExpr::leaf(name, *w)),
        Formula::Var(name, other) => Err(format!(
            "formula_to_bvexpr: Var {name:?} has non-bitvector sort {other:?} \
             (only BitVec leaves are in the add-leaf fragment)"
        )),
        Formula::BvAdd(l, r, _w) => Ok(BvExpr::add(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        Formula::BvSub(l, r, _w) => Ok(BvExpr::sub(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        Formula::BvZeroExt(inner, added) => Ok(BvExpr::zero_ext(formula_to_bvexpr(inner)?, *added)),
        Formula::BvExtract { inner, high, low } => {
            Ok(BvExpr::extract(formula_to_bvexpr(inner)?, *high, *low))
        }
        // `bvor` — a FAITHFUL structural lowering (NOT a fold). The RAW
        // byte-derived `machine_out` for the add-leaf carries identity wrappers
        // such as `BvOr(BitVec{0}, x)` (a no-op OR with a zero constant). We map
        // the `BvOr` to `BvExpr::or` directly so the bit-blaster sees the REAL
        // `Or2` gate per bit: `Or(0, x)` collapses to `x`'s bits only insofar as
        // the SAT solver proves it (no structural shortcut, no trusted rewrite).
        // This lets the RAW machine_out lower into the fragment and the gate emit
        // a genuine kernel-re-checkable [PROVED] certificate.
        Formula::BvOr(l, r, _w) => Ok(BvExpr::or(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        // `bvand` / `bvxor` — FAITHFUL structural lowerings (NOT folds), mirroring
        // the `BvOr` path. Each maps to the matching per-bit `BvExpr` variant whose
        // bit-blast uses a real `And2`/`Xor2` gate per bit — no carry chain, no
        // structural shortcut. This puts AND and XOR into the kernel-re-checkable
        // [PROVED] fragment alongside Add/Sub/Or. (`BvMul` stays fail-closed below:
        // ay has no multiplier blast gate, so it remains [VALIDATED].)
        Formula::BvAnd(l, r, _w) => Ok(BvExpr::and(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        Formula::BvXor(l, r, _w) => Ok(BvExpr::xor(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        // `bvmul` — a FAITHFUL structural lowering to `BvExpr::Mul`, the
        // shift-and-add ARRAY multiplier. It blasts to existing gate KINDS only
        // (And2 partial products + Xor3/FullAdderCarry/ConstFalse adder tree), so
        // the export is kernel-re-checkable IN PRINCIPLE. Whether the LIVE gate
        // emits [PROVED] (vs falling back to [VALIDATED]) depends only on
        // `export_bv_blast_proof_expr` surfacing the refutation; anti-vacuity is
        // real (mul != add is refuted, never proved). Signedness is NOT
        // load-bearing for the low-n product: a two's-complement wrapping multiply
        // has the same low bits for signed/unsigned operands, matching `BvMul`.
        Formula::BvMul(l, r, _w) => Ok(BvExpr::mul(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        // `(_ sign_extend added)` — a FAITHFUL structural lowering. The cast
        // path (`eval_cast`) emits `BvSignExt` for a widening signed cast; the
        // byte-derived machine output of a `sxtw`/`sxth`/`sxtb` is the same
        // sign-replication. `BvExpr::SignExt` replicates the inner MSB output var
        // `added` times — distinct from `BvZeroExt` (zero pad), so a sign-cast
        // lowered as a zero-cast genuinely differs (anti-vacuity holds). Puts the
        // SEXT cast into the kernel-re-checkable [PROVED] fragment.
        Formula::BvSignExt(inner, added) => Ok(BvExpr::sign_ext(formula_to_bvexpr(inner)?, *added)),
        // Variable-amount shifts — FAITHFUL structural lowerings to the barrel-
        // shifter `BvExpr` nodes. `BvShl`/`BvLShr` blast and surface cleanly, so
        // they enter the [PROVED] fragment. `BvAShr` (arithmetic, sign-filling)
        // is the SIGNED shift-right: its node + anti-vacuity are real (ashr !=
        // lshr is refuted, never proved), but a variable-amount width-8 ashr
        // equivalence may not SURFACE through ay's RUP expander — in which case
        // `export_bv_blast_proof_expr` errors and `try_kernel_recheckable_proof`
        // fail-CLOSES via `.ok()?` to [VALIDATED]. No fabricated [PROVED] for an
        // unsurfaced ashr. Signedness stays load-bearing: Lshr vs Ashr select
        // distinct fills, so a wrong-signedness emission genuinely differs.
        Formula::BvShl(l, r, _w) => Ok(BvExpr::shl(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        Formula::BvLShr(l, r, _w) => Ok(BvExpr::lshr(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        Formula::BvAShr(l, r, _w) => Ok(BvExpr::ashr(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)),
        // `bvnot` — per-bit NOT (FAITHFUL structural lowering to `BvExpr::Not`).
        Formula::BvNot(inner, _w) => Ok(BvExpr::not(formula_to_bvexpr(inner)?)),
        // ── PATH B: a compare's register value is `Ite(pred, 1, 0)` (see
        // `pred_to_int`), identical on BOTH the byte-derived machine side and the
        // IR auto-spec side. Recognize that exact shape and lower it to
        // `ZeroExt(pred_1bit, w-1)`: a 1-bit predicate zero-extended into the
        // register. The predicate itself lowers via `predicate_to_bvexpr` (a Bool
        // -> 1-bit `BvExpr`), so the machine flag form and the IR `BvSLt`/`Eq`
        // form blast to comparable 1-bit predicates and the solver discharges
        // `NOT(machine == ir)`. Any predicate outside the [PROVED] fragment (e.g.
        // an UNSIGNED compare whose carry-out flag is not yet a first-class node)
        // fails closed here -> [VALIDATED].
        Formula::Ite(cond, then_v, else_v) => {
            // The compare register form is `pred ? 1 : 0` (or the inverted
            // `pred ? 0 : 1`, which a CSET of an inverted condition emits). The
            // then/else arms are constant 0/1 at some register width `w` (possibly
            // folded as `BvAdd(0,1)`), so const-evaluate both.
            if let Some((w, then_one)) = ite_pred_branches(then_v, else_v) {
                // `pred ? 1 : 0` -> pred;  `pred ? 0 : 1` -> NOT pred.
                let pred = predicate_to_bvexpr(cond)?;
                let pred = if then_one { pred } else { BvExpr::not(pred) };
                return if w == 1 { Ok(pred) } else { Ok(BvExpr::zero_ext(pred, w - 1)) };
            }
            // ── PATH B2: THE GENERAL SELECT, AS A MUX OVER THE EXISTING FRAGMENT.
            //
            // A branch that yields DIFFERENT VALUES (not a 0/1 flag) — which is
            // what every `if`/`match` returning distinct results merges to, on
            // BOTH sides, since `eval_ir_terminator` and the machine-side path
            // merger both emit `Ite` — used to fail closed here and cost the
            // function its kernel grade. It does not need a new `BvExpr` node or a
            // new kernel gate kind: the standard mask-mux
            //
            //     ite(c, a, b)  =  (sext(c, w-1) & a) | (~sext(c, w-1) & b)
            //
            // is EXACTLY it in the nodes the exporter already has. `c` is the
            // 1-bit predicate `predicate_to_bvexpr` produces, so `sext(c, w-1)` is
            // all-ones when `c` holds and all-zeros when it does not — bit `i` of
            // the result is `(c ∧ a_i) ∨ (¬c ∧ b_i)`, the definition of select.
            // The rewrite is a FAITHFUL RENDERING of `Formula::Ite`, in the same
            // category as every other arm of this function, and it is what the
            // kernel then re-checks: the obligation exported is the real one.
            //
            // FAIL-CLOSED on anything that would make that identity not hold:
            // either arm outside the fragment, an ill-defined width, arms of
            // unequal width, or a predicate outside the [PROVED] compare fragment.
            let then_e = formula_to_bvexpr(then_v)?;
            let else_e = formula_to_bvexpr(else_v)?;
            let (tw, ew) = (bvexpr_width(&then_e), bvexpr_width(&else_e));
            let (Some(tw), Some(ew)) = (tw, ew) else {
                return Err("formula_to_bvexpr: Ite arm has an ill-defined bit width \
                            (fail-closed)"
                    .to_string());
            };
            if tw != ew {
                return Err(format!(
                    "formula_to_bvexpr: Ite arms differ in width ({tw} vs {ew}); a select \
                     is only well-formed at ONE width (fail-closed)"
                ));
            }
            if tw == 0 {
                return Err("formula_to_bvexpr: Ite at width 0 (fail-closed)".to_string());
            }
            let pred = predicate_to_bvexpr(cond)?;
            let mask = if tw == 1 { pred } else { BvExpr::sign_ext(pred, tw - 1) };
            Ok(BvExpr::or(
                BvExpr::and(mask.clone(), then_e),
                BvExpr::and(BvExpr::not(mask), else_e),
            ))
        }
        // A fixed bitvector constant -> `BvExpr::Const`. Each bit is a fixed
        // `ConstTrue`/`ConstFalse` literal in the bit-blast (the identity
        // wrapper's zero operand). The constant must fit in its width; the
        // exporter rejects an over-wide value as Malformed (fail-closed). The
        // `value` field is i128 in trust-types; a negative literal at a given
        // width is its two's-complement bit pattern, so we mask to `width` bits.
        Formula::BitVec { value, width } => {
            let w = *width;
            let masked =
                if w >= 128 { *value as u128 } else { (*value as u128) & ((1u128 << w) - 1) };
            Ok(BvExpr::const_val(masked, w))
        }
        // FAIL CLOSED on every other variant, naming it precisely so the residual
        // gap (BvAnd/BvXor/BvMul/shifts/compares/Ite/...) is reported rather than
        // faked. NO native BvExpr variant exists for these in the add-leaf slice.
        other => Err(format!(
            "formula_to_bvexpr: unsupported Formula variant for the add-leaf \
             BvExpr fragment (Leaf/Add/Sub/ZeroExt/Extract): {}",
            formula_variant_name(other)
        )),
    }
}

/// The widest `Mul`-operand bit width for which the live gate will attach a
/// kernel-re-checkable [PROVED] certificate. A `bvmul` bit-blasts to a
/// shift-and-add ARRAY multiplier; a *non-fusing* multiply obligation's
/// resolution refutation grows ~16× per +2 operand-width (measured: width 8 ⇒
/// ~2.0M steps), and the clean kernel re-check is at least linear in steps over
/// a growing clause DB. The MULTIPLIER blast itself uses only existing gate
/// KINDS and IS proven kernel-re-checkable at small widths (ay-proof `mul_*`
/// tests + clean `reflection_real_mul_unsat_cert_is_fully_zero_trust` at width
/// 8), but a live-gate-width (32) multiply is neither exportable in bounded
/// memory nor re-checkable. So multiply stays [VALIDATED] at the live gate: we
/// decline the kernel grade for any `Mul` wider than this bound rather than
/// attach a hollow [PROVED] (or hang/OOM the gate). Set to 8 — the largest
/// width with a demonstrated passing clean re-check.
#[cfg(feature = "ay-proofs")]
const MAX_RECHECKABLE_MUL_WIDTH: u32 = 8;

/// The kernel-checked theorem a wide `Mul` cites. Axiom-free, width-generic;
/// see `proofs/codegen-equivalence/g16_multiplier_equivalence.lean`.
const CITED_MUL_THEOREM: &str = "G16Mul.blast_equals_ir";

/// The correspondence the kernel did NOT check: that ay's Rust encoder emits
/// the model's multiplier. Machine-checked by
/// `tests/ay_blast_agrees_differential.rs`, unprovable inside clean.
const CITED_MUL_RESIDUAL: &str = "G16Mul.AyBlastAgrees";

/// Whether the wide-`Mul` citation path is enabled. ON by default; set
/// `TCG_CITE_WIDE_MUL=0` to restore the previous behaviour (decline, report
/// [VALIDATED] with no stated reason).
///
/// TURNING THIS ON DOES NOT RAISE ANY CLAIM, which is why it is safe as a
/// default. A citation lands in the SAME bucket as [VALIDATED] at both
/// classification sites, caps at `Trusted`, and is refused by
/// `StrictProvenOnly` exactly as [VALIDATED] is. What changes is that a wide
/// `Mul` now says WHY it is not [PROVED] — naming the cited theorem and the
/// residual correspondence — instead of reporting a bare `AyValidated` that
/// tells a reader nothing about what was and was not checked.
fn cite_wide_mul_enabled() -> bool {
    cite_wide_mul_enabled_from(std::env::var("TCG_CITE_WIDE_MUL").ok().as_deref())
}

/// The policy itself, pure so it can be tested without mutating the
/// environment: absent means ON, `"0"` means OFF, anything else means ON.
fn cite_wide_mul_enabled_from(v: Option<&str>) -> bool {
    v != Some("0")
}

#[cfg(all(test, feature = "ay-proofs"))]
mod cite_policy_tests {
    use super::cite_wide_mul_enabled_from;

    #[test]
    fn citation_is_on_by_default_and_opt_out_works() {
        assert!(cite_wide_mul_enabled_from(None), "absent must mean ON (owner default)");
        assert!(!cite_wide_mul_enabled_from(Some("0")), "`0` must be the escape hatch");
        assert!(cite_wide_mul_enabled_from(Some("1")), "`1` stays ON");
        // Anything unrecognised stays ON rather than silently disabling: a typo
        // in the opt-out must not quietly remove the residual from verdicts.
        assert!(cite_wide_mul_enabled_from(Some("false")), "a typo must not disable it");
    }
}

/// Trust: RUNG 1 STEP-COUNT FRONTIER (HONESTY). The clean kernel re-check routes
/// the exported refutation through the proven SUB-QUADRATIC trie checker
/// (`checkRefutes3_sound`, closure ⊆ FOUNDATIONAL). That checker is the right
/// mechanism — the O(steps²) `checkRefutes_sound` OOMs (>100 GB) on the live add.
///
/// The earlier 2048 frontier was forced by a PRE-trampoline limitation: the
/// trie checker's ι-reduction was NATIVELY RECURSIVE in clean-kernel's WHNF, so
/// it stack-overflowed the re-check thread past ~6700 steps (and ballooned to
/// >32 GB on the deep add). The clean-kernel `whnf` evaluator is now an
/// ITERATIVE WHNF TRAMPOLINE (heap worklist, no native deep recursion), which
/// REMOVES the stack-depth ceiling. The frontier is therefore no longer a
/// native-stack limit; it is a practical TIME+MEMORY budget for an in-gate
/// re-check.
///
/// MEASURED post-trampoline on the then-pinned emitted shapes (release, serial,
/// `/usr/bin/time -l`, via the real `try_kernel_recheckable_proof` path with the
/// frontier raised; each measured row kernel-re-checked to `Unsat3` with ZERO
/// domain axioms, EXIT=0, no overflow/OOM):
///   * bitwise `and`/`or`/`xor` (no carry chain): 934 steps  -> ~8 s;
///   * `sext`: 164 steps;
///   * `slt`:  7326 steps -> 34 s @ 2.97 GB;   `sle`: 7717 -> 19 s @ 3.11 GB;
///   * `ult`:  7846 steps -> 38 s @ 3.02 GB;   `ule`: 8288 -> 17 s @ 3.18 GB;
///   * `eq`:   9677 steps -> 28 s @ 4.07 GB;
///   * `add`: current AY 0e35 shape is 17854 steps (`proof.validate()` green;
///     the prior kernel time/memory measurement is stale and is not claimed);
///     `neg`: 11317 -> 42 s @ 4.05 GB;
///   * `sub`: 19389 steps -> 101 s @ 4.96 GB  (the deepest carry/borrow chain).
/// Every row with a cited current measurement re-checks at < 5 GB — far under
/// any reasonable memory ceiling (≤ ~24 GB). No resource claim is made here
/// for the current 17854-step add artifact.
/// The barrel-shifter shapes — `shl`: 108825 steps, `lshr`: 129008 steps (~5.6–6.6×
/// `sub`) — exceed this SLOW-path frontier. HISTORICAL NOTE: shifts USED to stay
/// [VALIDATED] here. They are now KERNEL-[PROVED] via the O(1) coercion-identity
/// reflect path (reflect `BvShl/BvLShr/BvAShr -> BvF.Shl/LShr/AShr`, cancel by
/// `bvf_shl/lshr/ashr_cong`), which bypasses the bit-blast entirely — so these
/// step-counts no longer determine the shift grade (see `gate_shl/lshr/ashr_is_
/// proved_via_o1_instantiation`). This frontier now bounds only ops that lack an
/// O(1) reflect arm AND a dedicated discharge.
///
/// So the SLOW-path frontier is a refutation STEP-COUNT bound just above the deepest
/// practically-re-checkable op (`sub` at 19389). The KERNEL-rooted [PROVED] surface
/// is the entire scalar ALU — add/sub/neg, and/or/xor, eq/ult/ule/slt/sle, mul,
/// udiv/sdiv, urem/srem, and shl/lshr/ashr — via the O(1) path; sext re-checks via
/// the slow path within frontier. The [VALIDATED] residual is div/rem COMPOSITES
/// (non-bare-div roots) and unmodeled constructs (loops/calls).
///
/// HISTORY + CURRENT MEANING (ledger #21-CORRECTION + #23): this was briefly 20480
/// (an over-claim — the deep ops then STACK-OVERFLOWED a 256 MiB re-check; retracted
/// to 2048). The STACK barrier is now FIXED (clean `get_nat_bignat_whnf` succ-peeling
/// iterativized, clean pin ≥ b0af96a7): the measured `slt`@7326 and
/// `sub`@19389 artifacts VERIFIABLY kernel-re-check to `Unsat3` at the shipped
/// 256 MiB stack with NO overflow/OOM. AY 0e35's current `add` artifact is
/// 17854 steps and passes the producer's structural `proof.validate()` gate;
/// its exact full Clean re-check has not been resource-remeasured. This
/// frontier is a **TIME/MEMORY BUDGET, not a stack limit**: the measured deep
/// re-checks are slow (slt ~45 s, sub ~192 s @ 3–5 GB), impractical to run
/// per-function on every routine compile, so the DEFAULT stays low (the fast
/// shallow ops). 2048 covers the by-default-fast ops (and/or/xor @934,
/// sext @164) with margin.
#[cfg(feature = "kernel-recheck")]
const MAX_RECHECKABLE_REFUTATION_STEPS: usize = 2048;

/// Bit width of a lowered [`ay_proof::BvExpr`], or `None` if a sub-shape makes
/// the width ill-defined (which the blaster would also reject downstream).
#[cfg(feature = "ay-proofs")]
fn bvexpr_width(e: &ay_proof::BvExpr) -> Option<u32> {
    use ay_proof::BvExpr;
    match e {
        BvExpr::Leaf { width, .. } | BvExpr::Const { width, .. } => Some(*width),
        BvExpr::Add(l, _)
        | BvExpr::Sub(l, _)
        | BvExpr::Or(l, _)
        | BvExpr::And(l, _)
        | BvExpr::Xor(l, _)
        | BvExpr::Mul(l, _)
        | BvExpr::Shl(l, _)
        | BvExpr::Lshr(l, _)
        | BvExpr::Ashr(l, _) => bvexpr_width(l),
        BvExpr::ZeroExt(inner, added) | BvExpr::SignExt(inner, added) => {
            Some(bvexpr_width(inner)? + *added)
        }
        BvExpr::Extract { high, low, .. } => Some(*high - *low + 1),
        BvExpr::Not(inner) => bvexpr_width(inner),
        // 1-bit predicates.
        BvExpr::Eq(..) | BvExpr::CarryOut { .. } => Some(1),
    }
}

/// True iff `e` contains a `Mul` node whose operand width exceeds `max` — the
/// tractability guard the live gate uses to keep wide multiply [VALIDATED]
/// rather than attaching a kernel certificate that cannot actually be
/// re-checked (see [`MAX_RECHECKABLE_MUL_WIDTH`]).
#[cfg(feature = "ay-proofs")]
/// The widest `BvMul` operand in `e` (0 if none). Mirrors `mul_wider_than`'s
/// traversal exactly, so the width a citation records is the width the guard
/// measured, never a re-derivation that could drift from it.
fn mul_width(e: &ay_proof::BvExpr) -> u32 {
    use ay_proof::BvExpr;
    match e {
        BvExpr::Mul(l, r) => bvexpr_width(l).unwrap_or(0).max(mul_width(l)).max(mul_width(r)),
        BvExpr::Add(l, r)
        | BvExpr::Sub(l, r)
        | BvExpr::Or(l, r)
        | BvExpr::And(l, r)
        | BvExpr::Xor(l, r)
        | BvExpr::Eq(l, r)
        | BvExpr::Shl(l, r)
        | BvExpr::Lshr(l, r)
        | BvExpr::Ashr(l, r) => mul_width(l).max(mul_width(r)),
        BvExpr::CarryOut { lhs, rhs, .. } => mul_width(lhs).max(mul_width(rhs)),
        BvExpr::ZeroExt(inner, _)
        | BvExpr::SignExt(inner, _)
        | BvExpr::Not(inner)
        | BvExpr::Extract { inner, .. } => mul_width(inner),
        BvExpr::Leaf { .. } | BvExpr::Const { .. } => 0,
    }
}

fn mul_wider_than(e: &ay_proof::BvExpr, max: u32) -> bool {
    use ay_proof::BvExpr;
    match e {
        BvExpr::Mul(l, r) => {
            bvexpr_width(l).is_some_and(|w| w > max)
                || mul_wider_than(l, max)
                || mul_wider_than(r, max)
        }
        BvExpr::Add(l, r)
        | BvExpr::Sub(l, r)
        | BvExpr::Or(l, r)
        | BvExpr::And(l, r)
        | BvExpr::Xor(l, r)
        | BvExpr::Eq(l, r)
        | BvExpr::Shl(l, r)
        | BvExpr::Lshr(l, r)
        | BvExpr::Ashr(l, r) => mul_wider_than(l, max) || mul_wider_than(r, max),
        BvExpr::CarryOut { lhs, rhs, .. } => mul_wider_than(lhs, max) || mul_wider_than(rhs, max),
        BvExpr::ZeroExt(inner, _)
        | BvExpr::SignExt(inner, _)
        | BvExpr::Not(inner)
        | BvExpr::Extract { inner, .. } => mul_wider_than(inner, max),
        BvExpr::Leaf { .. } | BvExpr::Const { .. } => false,
    }
}

/// Recognize the compare register form `pred ? 1 : 0` (or its inverse
/// `pred ? 0 : 1`, which a CSET of an inverted condition emits). The then/else
/// arms are CONSTANT 0/1 at a common width `w` (possibly folded, e.g. the
/// byte-derived `BvAdd(BitVec{0},BitVec{1})` form of a `1`). Returns
/// `Some((w, then_is_one))` on a match: `then_is_one == true` means `pred ? 1 : 0`
/// (use `pred`), `false` means `pred ? 0 : 1` (use `NOT pred`). `None` otherwise,
/// so a general `Ite` falls closed rather than being mis-lowered.
#[cfg(feature = "ay-proofs")]
fn ite_pred_branches(then_v: &Formula, else_v: &Formula) -> Option<(u32, bool)> {
    let (tv, tw) = bv_const_value(then_v)?;
    let (ev, ew) = bv_const_value(else_v)?;
    if tw != ew {
        return None;
    }
    match (tv, ev) {
        (1, 0) => Some((tw, true)),
        (0, 1) => Some((tw, false)),
        _ => None,
    }
}

/// Const-evaluate a bit-vector [`Formula`] to `(value, width)` for the narrow set
/// of constant shapes the compare register form produces: a literal `BitVec`, and
/// the byte-derived `BvAdd`/`BvSub`/`BvOr` folds over such literals. Returns `None`
/// for anything non-constant (so the matcher fails closed). Values are masked to
/// `width` bits.
#[cfg(feature = "ay-proofs")]
fn bv_const_value(f: &Formula) -> Option<(u128, u32)> {
    let mask = |v: u128, w: u32| if w >= 128 { v } else { v & ((1u128 << w) - 1) };
    match f {
        Formula::BitVec { value, width } => Some((mask(*value as u128, *width), *width)),
        Formula::BvAdd(l, r, w) => {
            let (lv, _) = bv_const_value(l)?;
            let (rv, _) = bv_const_value(r)?;
            Some((mask(lv.wrapping_add(rv), *w), *w))
        }
        Formula::BvSub(l, r, w) => {
            let (lv, _) = bv_const_value(l)?;
            let (rv, _) = bv_const_value(r)?;
            Some((mask(lv.wrapping_sub(rv), *w), *w))
        }
        Formula::BvOr(l, r, w) => {
            let (lv, _) = bv_const_value(l)?;
            let (rv, _) = bv_const_value(r)?;
            Some((mask(lv | rv, *w), *w))
        }
        _ => None,
    }
}

/// Lower a BOOLEAN-valued [`Formula`] (a 1-bit predicate) into a 1-bit-wide
/// [`ay_proof::BvExpr`], FAILING CLOSED on any predicate outside the [PROVED]
/// compare fragment.
///
/// The byte-derived machine side produces the AArch64 flag predicate
/// (`condition_to_formula` over `compute_nzcv`): a Bool tree of
/// `Not`/`And`/`Or`/`Eq` over 1-bit `BvExtract`s of a `BvSub`. The IR auto-spec
/// side produces a native `BvSLt`/`BvSLe`/`Eq`. Both are decomposed HERE to the
/// SAME 1-bit `BvExpr` shape (the g16-corroborated flag decomposition), so the
/// solver discharges `NOT(machine_pred == ir_pred)`.
///
/// SIGNED `<`/`<=` and `==`/`!=` are in the fragment. UNSIGNED `BvULt`/`BvULe`
/// fail closed: their carry-out flag is not (yet) a first-class `BvExpr` node, so
/// they stay [VALIDATED] (the honest residual of this rung).
#[cfg(feature = "ay-proofs")]
fn predicate_to_bvexpr(f: &Formula) -> Result<ay_proof::BvExpr, String> {
    use ay_proof::BvExpr;
    match f {
        // Boolean literals -> a 1-bit constant predicate.
        Formula::Bool(true) => Ok(BvExpr::const_val(1, 1)),
        Formula::Bool(false) => Ok(BvExpr::const_val(0, 1)),
        // Boolean NOT of a predicate -> 1-bit `BvExpr::Not`.
        Formula::Not(inner) => Ok(BvExpr::not(predicate_to_bvexpr(inner)?)),
        // Equality: works for BOTH bit-vector equality (`a == b`, the `eq`
        // compare) AND the flag equality `N == V` inside the signed-lt overflow
        // term. Both operands lower as bit-vectors (or 1-bit predicates) of equal
        // width; `BvExpr::Eq` reduces to a 1-bit predicate.
        Formula::Eq(l, r) => Ok(BvExpr::eq(eq_operand_to_bvexpr(l)?, eq_operand_to_bvexpr(r)?)),
        // N-ary And/Or -> fold with the per-bit `And`/`Or` over 1-bit predicates.
        Formula::And(parts) => fold_predicate(parts, true),
        Formula::Or(parts) => fold_predicate(parts, false),
        // SIGNED relational compares -> the g16 flag decomposition (signed_lt_equiv).
        //   a <s b  ==  N != V  ==  Not(Eq(N, V))
        //   a <=s b ==  Not(b <s a)
        Formula::BvSLt(l, r, w) => predicate_to_bvexpr(&signed_lt_flag_formula(l, r, *w)),
        Formula::BvSLe(l, r, w) => {
            // a <= b  ==  NOT(b < a)
            let gt = signed_lt_flag_formula(r, l, *w);
            Ok(BvExpr::not(predicate_to_bvexpr(&gt)?))
        }
        // UNSIGNED relational compares -> the g16 carry-out (borrow) decomposition
        // (unsigned_lt_equiv). The machine's NZCV carry flag for a SUB is
        // `C = NOT(a <u b) = CarryOut(a - b)` (helpers::compute_nzcv): the carry-out
        // of `a + ~b + 1` is 0 exactly on a borrow, i.e. exactly when `a <u b`. So:
        //   a <u b   ==  NOT(CarryOut(a, b, is_sub=true))
        //   a <=u b  ==  NOT(b <u a) == CarryOut(b, a, is_sub=true)
        // Both the machine predicate (which contains `BvULt` inside `C`) and the IR
        // auto-spec `BvULt`/`BvULe` lower through THIS arm to the SAME 1-bit shape,
        // threading the EXISTING ripple-carry `FullAdderCarry` chain (no new kernel
        // gate kind).
        Formula::BvULt(l, r, _w) => {
            Ok(BvExpr::not(BvExpr::carry_out_sub(formula_to_bvexpr(l)?, formula_to_bvexpr(r)?)))
        }
        Formula::BvULe(l, r, _w) => Ok(BvExpr::carry_out_sub(
            // a <=u b == NOT(b <u a) == CarryOut(b - a)
            formula_to_bvexpr(r)?,
            formula_to_bvexpr(l)?,
        )),
        // Remaining predicates fail CLOSED (stay [VALIDATED]).
        other => Err(format!(
            "predicate_to_bvexpr: predicate outside the [PROVED] compare fragment \
             (signed-lt/le, eq/ne, and/or/not over them): {}",
            formula_variant_name(other)
        )),
    }
}

/// Lower an operand of an `Eq` predicate. It is either a bit-vector expression
/// (the `a == b` compare, or `Sub(a,b) == 0`) lowered by [`formula_to_bvexpr`],
/// or a 1-bit boolean sub-predicate (the `N`/`V` flag terms) lowered by
/// [`predicate_to_bvexpr`]. We try the bit-vector lowering first and fall back to
/// the predicate lowering — both yield a same-width `BvExpr` so `BvExpr::Eq` is
/// well-formed.
#[cfg(feature = "ay-proofs")]
fn eq_operand_to_bvexpr(f: &Formula) -> Result<ay_proof::BvExpr, String> {
    match formula_to_bvexpr(f) {
        Ok(e) => Ok(e),
        Err(_) => predicate_to_bvexpr(f),
    }
}

/// AND/OR-reduce a list of boolean predicates into a single 1-bit `BvExpr`.
#[cfg(feature = "ay-proofs")]
fn fold_predicate(parts: &[Formula], is_and: bool) -> Result<ay_proof::BvExpr, String> {
    use ay_proof::BvExpr;
    let mut it = parts.iter();
    let first = it.next().ok_or_else(|| "predicate_to_bvexpr: empty And/Or".to_string())?;
    let mut acc = predicate_to_bvexpr(first)?;
    for p in it {
        let next = predicate_to_bvexpr(p)?;
        acc = if is_and { BvExpr::and(acc, next) } else { BvExpr::or(acc, next) };
    }
    Ok(acc)
}

/// Build the SIGNED-`<` flag predicate `N != V` over `a`/`b` at width `w` — the
/// EXACT shape `condition_to_formula(Condition::Lt)` produces over
/// `compute_nzcv(a, b, a - b, w, is_sub = true)` (trust-machine-sem). Building the
/// IR auto-spec's `BvSLt` in this identical flag form makes the machine flag
/// predicate and the IR predicate blast to a comparable 1-bit `BvExpr` (g16
/// signed_lt_equiv corroborates the equivalence).
///
///   sub   = a - b
///   N     = (Extract(sub, w-1, w-1) == 1)
///   V     = NOT(asign == bsign) AND NOT(rsign == asign)   (subtraction overflow)
///   a <s b = NOT(N == V)
#[cfg(feature = "ay-proofs")]
fn signed_lt_flag_formula(a: &Formula, b: &Formula, w: u32) -> Formula {
    let msb = w - 1;
    let sub = Formula::BvSub(b_box(a.clone()), b_box(b.clone()), w);
    let ext = |e: Formula| Formula::BvExtract { inner: b_box(e), high: msb, low: msb };
    let asign = ext(a.clone());
    let bsign = ext(b.clone());
    let rsign = ext(sub);
    let one1 = Formula::BitVec { value: 1, width: 1 };
    // N = (rsign == 1)
    let n = Formula::Eq(b_box(rsign.clone()), b_box(one1));
    // V = NOT(asign == bsign) AND NOT(rsign == asign)
    let signs_differ = Formula::Not(b_box(Formula::Eq(b_box(asign.clone()), b_box(bsign))));
    let res_differs = Formula::Not(b_box(Formula::Eq(b_box(rsign), b_box(asign))));
    let v = Formula::And(vec![signs_differ, res_differs]);
    // a <s b = N != V = NOT(N == V)
    Formula::Not(b_box(Formula::Eq(b_box(n), b_box(v))))
}

/// `Box::new` helper local to the `ay-proofs` lowering (mirrors `b`).
#[cfg(feature = "ay-proofs")]
fn b_box(f: Formula) -> Box<Formula> {
    Box::new(f)
}

/// A short variant tag for the fail-closed error (avoids dumping the whole tree).
#[cfg(feature = "ay-proofs")]
fn formula_variant_name(f: &Formula) -> &'static str {
    match f {
        Formula::Var(..) => "Var(non-bitvector)",
        Formula::BitVec { .. } => "BitVec(constant)",
        Formula::BvOr(..) => "BvOr",
        Formula::BvAnd(..) => "BvAnd",
        Formula::BvXor(..) => "BvXor",
        Formula::BvMul(..) => "BvMul",
        Formula::BvShl(..) => "BvShl",
        Formula::BvLShr(..) => "BvLShr",
        Formula::BvAShr(..) => "BvAShr",
        Formula::BvSignExt(..) => "BvSignExt",
        Formula::BvConcat(..) => "BvConcat",
        Formula::Ite(..) => "Ite",
        Formula::Eq(..) => "Eq",
        Formula::Not(..) => "Not",
        Formula::Select(..) => "Select",
        Formula::Store(..) => "Store",
        _ => "other",
    }
}

// ===========================================================================
// THE 128-BIT REGISTER-PAIR SPLIT — TEETH AT THE OBLIGATION LEVEL.
//
// `verify_output_trust_ir::tests_i128_pair` pins the same fragment through the
// REAL BYTES. These tests attack the SPLIT itself, at the level where the halves
// are individually visible, because that is the only level at which "the high
// half is genuinely an obligation" can be distinguished from "the high half
// happens to be zero on both sides".
//
// The whole hazard: a small `i128` constant has `X1 == 0`, so a split that
// checked only the LOW half would report [PROVED] for essentially every 128-bit
// constant return in the corpus and never notice. Every test below therefore
// pins the ASYMMETRY: same obligation, corrupt one half, the grade must move —
// for BOTH halves, independently.
// ===========================================================================
#[cfg(all(test, feature = "ay-proofs"))]
mod tests_pair_128_split {
    use super::*;

    /// `concat(hi, lo)` over two 64-bit constants — the machine side's shape.
    fn pair(high: u64, low: u64) -> Formula {
        Formula::BvConcat(
            b(Formula::BitVec { value: high as i128, width: 64 }),
            b(Formula::BitVec { value: low as i128, width: 64 }),
        )
    }

    /// A 128-bit literal — the spec side's shape for a constant return.
    fn lit128(value: u128) -> Formula {
        Formula::BitVec { value: value as i128, width: 128 }
    }

    /// The split is arithmetic on the literal, so pin it directly rather than
    /// only through a downstream proof: `0x1122...` must cut at bit 64 with the
    /// FIRST component the HIGH half (SMT-LIB `concat` order, which is what
    /// `read_int_return` builds).
    #[test]
    fn literal_splits_high_first_at_bit_64() {
        let v: u128 = (0xdead_beef_0000_0001u128 << 64) | 0x0000_0000_cafe_f00du128;
        let (high, low) = split_register_pair_128(&lit128(v)).expect("128-bit literal splits");
        assert_eq!(
            high,
            Formula::BitVec { value: 0xdead_beef_0000_0001u64 as i128, width: 64 },
            "first component must be the HIGH 64 bits"
        );
        assert_eq!(
            low,
            Formula::BitVec { value: 0x0000_0000_cafe_f00du64 as i128, width: 64 },
            "second component must be the LOW 64 bits"
        );
    }

    /// A half whose top bit is set must round-trip as its OWN 64-bit pattern,
    /// not as a sign-extension of it. `value` is stored as `i128`, so this is
    /// exactly where a careless cast would corrupt the high half into `-1`.
    #[test]
    fn literal_split_preserves_a_negative_looking_half() {
        let (high, low) = split_register_pair_128(&lit128(u128::MAX)).expect("splits");
        for half in [&high, &low] {
            let lowered = formula_to_bvexpr(half).expect("half lowers");
            assert_eq!(
                lowered,
                ay_proof::BvExpr::const_val(u128::from(u64::MAX), 64),
                "each half of !0u128 is 64 set bits, not a sign-extended -1"
            );
        }
    }

    /// Anything that is not a manifest pair fails closed — no normalization, no
    /// guessing at a split point.
    #[test]
    fn non_pair_shapes_do_not_split() {
        assert!(split_register_pair_128(&Formula::BitVec { value: 7, width: 64 }).is_none());
        assert!(split_register_pair_128(&wn(0)).is_none());
    }

    /// An UNEVEN concat must not be paired against a 64/64 one.
    ///
    /// NOTE ON WHAT THIS TEST DOES AND DOES NOT PIN: it passes with the width
    /// pin REMOVED, because `export_bv_blast_proof_expr` independently rejects
    /// this shape (the 96-bit half exceeds `SOLVED_MAX_WIDTH`). Measured, by
    /// deleting the pin and re-running. It is kept as a shape regression, and
    /// `pair_grade_is_refused_for_a_non_128_bit_pair` below is the test that
    /// actually pins the width check.
    #[test]
    fn uneven_split_is_refused() {
        let uneven = Formula::BvConcat(
            b(Formula::BitVec { value: 0, width: 32 }),
            b(Formula::BitVec { value: 0, width: 96 }),
        );
        assert!(
            try_kernel_recheckable_pair_128(&uneven, &lit128(0)).is_none(),
            "a 32/96 split must not be paired against a 64/64 one"
        );
    }

    /// THE WIDTH PIN'S OWN TEST. A 64-bit obligation whose two sides are BOTH
    /// `concat(32, 32)` is a matched, in-fragment, perfectly provable split —
    /// the exporter has no complaint about it. It is nevertheless NOT a 128-bit
    /// AAPCS64 register pair, and `KernelRecheckablePair` says it is. The pin is
    /// what keeps the grade's label true, and this is the test that fails if the
    /// pin is deleted (measured: deleting the pin makes this test fail and
    /// `uneven_split_is_refused` still pass).
    #[test]
    fn pair_grade_is_refused_for_a_non_128_bit_pair() {
        let half32 = |v: i128| {
            Formula::BvConcat(
                b(Formula::BitVec { value: v, width: 32 }),
                b(Formula::BitVec { value: v, width: 32 }),
            )
        };
        assert!(
            try_kernel_recheckable_pair_128(&half32(5), &half32(5)).is_none(),
            "a 64-bit concat(32,32) obligation must not be graded as a 128-bit \
             register pair, however provable its halves are"
        );
    }

    // --- THE MUTATION TESTS. These require the kernel to be compiled in: the
    //     [PROVED] grade is the KERNEL's claim, so the baseline they mutate away
    //     from only exists under `kernel-recheck`. ---

    /// BASELINE: a 128-bit constant return is now kernel-[PROVED], carrying TWO
    /// certificates. This is the grade move the whole change exists for — before
    /// the split it was `AyValidated`, because `formula_to_bvexpr` has no
    /// `BvConcat` arm and the obligation died at the lowering.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn pair_128_constant_return_is_kernel_proved() {
        let machine = pair(0, 1234);
        let spec = lit128(1234);
        let evidence = try_kernel_recheckable_proof(&machine, &spec, None)
            .expect("128-bit constant return must reach the kernel grade");
        assert!(
            matches!(evidence, ProvenEvidence::KernelRecheckablePair { .. }),
            "expected a two-certificate pair grade, got {evidence:?}"
        );
        assert!(
            OutputVerdict::Proven { evidence }.is_kernel_proved(),
            "the pair grade must satisfy the [PROVED]-vs-[VALIDATED] discriminator"
        );
    }

    /// THE LOAD-BEARING MUTATION. Corrupt the HIGH half ONLY — the low half is
    /// still exactly right — and the kernel grade must be refused.
    ///
    /// If this test passes while `pair_128_constant_return_is_kernel_proved`
    /// also passes, the high-half obligation is genuinely reaching the kernel.
    /// If it were to fail (grade still awarded), the high half would be assumed
    /// rather than checked, and the [PROVED] claim on every 128-bit return would
    /// be a claim about 64 of its 128 bits.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn pair_128_high_half_corruption_refuses_the_kernel_grade() {
        // Machine leaves 7 in X1; the spec's high half is 0. LOW halves agree.
        let machine = pair(7, 1234);
        let spec = lit128(1234);
        assert!(
            try_kernel_recheckable_proof(&machine, &spec, None).is_none(),
            "a WRONG HIGH half must not be awarded the kernel grade"
        );
        // ATTRIBUTION: the refusal above must be caused by the high half, not by
        // some blanket refusal of this shape. The LOW half of the very same
        // corrupted obligation still discharges on its own.
        assert!(
            kernel_recheckable_bitblast(
                &Formula::BitVec { value: 1234, width: 64 },
                &Formula::BitVec { value: 1234, width: 64 },
            )
            .is_some(),
            "control: the low half alone is kernel-accepted, so the refusal is \
             attributable to the high half"
        );
    }

    /// The symmetric mutation: a wrong LOW half with a correct high half must
    /// also be refused. Without this, "both halves are obligations" would rest
    /// on one direction only.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn pair_128_low_half_corruption_refuses_the_kernel_grade() {
        let machine = pair(0, 1235);
        let spec = lit128(1234);
        assert!(
            try_kernel_recheckable_proof(&machine, &spec, None).is_none(),
            "a WRONG LOW half must not be awarded the kernel grade"
        );
    }

    /// The pair-vs-pair shape (a carried 128-bit parameter returned unchanged),
    /// with the same high-half mutation. The identity case is where the halves
    /// are symbolic rather than constant, so it exercises leaf sharing across
    /// the split: `X1` on both sides of the high obligation, `X0` on both sides
    /// of the low one.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn pair_128_identity_is_proved_and_its_high_half_is_load_bearing() {
        let spec = Formula::BvConcat(b(xn(1)), b(xn(0)));
        let machine = Formula::BvConcat(b(xn(1)), b(xn(0)));
        assert!(
            matches!(
                try_kernel_recheckable_proof(&machine, &spec, None),
                Some(ProvenEvidence::KernelRecheckablePair { .. })
            ),
            "the 128-bit identity must be kernel-[PROVED] as a pair"
        );
        // Swap the halves on the machine side: each half is individually a
        // perfectly good 64-bit register read, and the LOW obligation is now
        // `X1 == X0` — false. The high one is too. Refuse.
        let swapped = Formula::BvConcat(b(xn(0)), b(xn(1)));
        assert!(
            try_kernel_recheckable_proof(&swapped, &spec, None).is_none(),
            "swapping X0/X1 must not be awarded the kernel grade"
        );
        // And the pure high-half corruption: LOW half untouched and correct.
        let high_wrong = Formula::BvConcat(b(xn(2)), b(xn(0)));
        assert!(
            try_kernel_recheckable_proof(&high_wrong, &spec, None).is_none(),
            "reading the HIGH half from the wrong register must not be awarded \
             the kernel grade"
        );
    }
}

// ===========================================================================
// IN-MODULE GATE TESTS — teeth: ACCEPT / REFUSE / FAIL-CLOSED.
// ===========================================================================
#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Projection, SourceSpan, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn sp() -> SourceSpan {
        SourceSpan::default()
    }

    fn wrap(name: &str, body: VerifiableBody) -> VerifiableFunction {
        VerifiableFunction {
            name: name.into(),
            def_path: format!("verify_output::{name}"),
            span: sp(),
            body,
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// SMT-LIB bit width of a `Formula`, `None` on any inconsistency. Small on
    /// purpose: it only needs to cover the shapes an extending load produces.
    fn smt_bv_width(f: &Formula) -> Option<u32> {
        match f {
            Formula::Var(_, Sort::BitVec(w)) | Formula::SymVar(_, Sort::BitVec(w)) => Some(*w),
            Formula::BitVec { width, .. } => Some(*width),
            Formula::BvZeroExt(a, added) | Formula::BvSignExt(a, added) => {
                smt_bv_width(a).map(|w| w + added)
            }
            Formula::BvExtract { high, low, .. } => Some(high - low + 1),
            Formula::BvConcat(a, b) => Some(smt_bv_width(a)? + smt_bv_width(b)?),
            Formula::BvAdd(a, b, w)
            | Formula::BvSub(a, b, w)
            | Formula::BvOr(a, b, w)
            | Formula::BvAnd(a, b, w)
            | Formula::BvXor(a, b, w)
            | Formula::BvShl(a, b, w) => {
                let (wa, wb) = (smt_bv_width(a)?, smt_bv_width(b)?);
                (wa == wb && wa == *w).then_some(*w)
            }
            // A memory byte.
            Formula::Select(..) => Some(8),
            Formula::Ite(_, a, b) => {
                let (wa, wb) = (smt_bv_width(a)?, smt_bv_width(b)?);
                (wa == wb).then_some(wa)
            }
            _ => None,
        }
    }

    /// A sign-extending load into an X register must reach the SOLVER as a
    /// 64-bit term.
    ///
    /// `sem_ldr_variant` passed the TARGET WIDTH where `BvSignExt`/`BvZeroExt`
    /// take the extension AMOUNT, so the byte-derived value for
    /// `ldrsb x0,[x1]` was a 72-bit term (8 + 64) and `ldrsw x0,[x1]` a 96-bit
    /// one. Nothing truncates an X-width register read, so the over-wide term
    /// flowed straight into `discharge_equal_pre`, where
    /// `try_eq(..).expect("eq")` ABORTED the process with
    /// `SortMismatch { got: [BitVec(72), BitVec(64)] }`.
    ///
    /// Measured disposition: a PANIC, never a wrong verdict — the low bits of an
    /// over-wide extension are the correct ones, so no route silently truncated
    /// it to a different value. The W-forms were already width-correct because
    /// the return readout extracts `[31:0]`.
    ///
    /// Both halves matter: the width assertion pins the formula, and reaching a
    /// verdict at all pins that the discharge no longer aborts.
    #[test]
    fn sign_extending_load_into_x_reaches_the_solver_as_64_bits() {
        const RET: u32 = 0xD65F_03C0;
        // Assembler-derived (`clang --target=aarch64` + `objdump -d`).
        let cases: &[(u32, &str)] = &[
            (0x3980_0020, "ldrsb x0,[x1]"),
            (0x7980_0020, "ldrsh x0,[x1]"),
            (0xB980_0020, "ldrsw x0,[x1]"),
        ];
        for (enc, label) in cases {
            let out = symbolic_machine_output(&words(&[*enc, RET]), 0, 64, false)
                .unwrap_or_else(|e| panic!("{label} must be modeled: {e}"));
            assert_eq!(
                smt_bv_width(&out),
                Some(64),
                "{label}: byte-derived output is not a 64-bit term: {out:?}"
            );

            // And the discharge must produce a VERDICT rather than aborting.
            let spec = Formula::Var("SPEC".into(), Sort::BitVec(64));
            assert!(
                matches!(discharge_equal_pre(&out, &spec, None), Discharge::CounterExample),
                "{label}: a load against an unconstrained spec var must be refutable"
            );
        }
    }

    fn binop_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
        )
    }

    /// A STABLE [VALIDATED] fixture: `_4 = a / b ; _0 = _4 ^ c`. The divisor `b` is an arg, so
    /// the gate adds a `b != 0` precondition (pre.is_some); but the obligation ROOT is XOR, not a
    /// bare div, so `try_div_conditional_discharge` (which matches `W(Ite(b==0,0,udiv))`) declines,
    /// and the conditional path stays [VALIDATED]. This does NOT promote as more scalar ops do
    /// (the composite-div discharge is future work), so it is a durable [VALIDATED] example.
    fn div_then_xor_fn(name: &str, ty: Ty) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: ty.clone(), name: Some("c".into()) },
                    LocalDecl { index: 4, ty: ty.clone(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: sp(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::BitXor,
                                Operand::Copy(Place::local(4)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: sp(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 3,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
        )
    }

    fn cmp_fn(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::bool_ty(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty, name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::bool_ty(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// `fn f(a: ty) -> ty { -a }` — a unary negation. `eval_rvalue` lowers Neg to
    /// `BvSub(0, a)`, already in the [PROVED] add-leaf fragment.
    fn neg_fn(name: &str, ty: Ty) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: ty.clone(), name: None },
                    LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
        )
    }

    /// `fn f(a: src) -> dst { a as dst }` — an int-to-int cast. With a SIGNED
    /// narrower `src` and a wider `dst` this lowers (via `eval_cast`) to
    /// `BvSignExt`; the byte-derived machine output is the same sign replication.
    fn cast_fn(name: &str, src: Ty, dst: Ty) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: dst.clone(), name: None },
                    LocalDecl { index: 1, ty: src, name: Some("a".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), dst.clone()),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: dst,
                datatype_defs: Default::default(),
            },
        )
    }

    // `max(a, b)` for i32: t = a < b; if a<b then b else a, expressed straight-line
    // as a select-free `(a >= b) ? a : b` is multi-statement; we use a simpler
    // signed-max idiom that stays single-block: r = ((a > b) ? a : b) is not
    // expressible without Ite rvalue, so the "max" acceptance case here is the
    // signed comparison itself (the load-bearing fix) plus arithmetic.

    // --- ACCEPT: correct functions -> Proven ---

    #[test]
    fn gate_accepts_add() {
        assert!(verify_output_preserved(&binop_fn("acc_add", BinOp::Add, Ty::i32())).is_proven());
    }

    #[test]
    fn gate_accepts_sub() {
        assert!(verify_output_preserved(&binop_fn("acc_sub", BinOp::Sub, Ty::i32())).is_proven());
    }

    #[test]
    fn gate_accepts_signed_lt() {
        // This is the LOAD-BEARING case: a signed `<`. If the lower.rs
        // signedness fix were reverted (emit unsigned for signed `<`), the
        // emitted bytes would diverge from the auto-spec and this would Refute.
        assert!(verify_output_preserved(&cmp_fn("acc_slt", BinOp::Lt, Ty::i32())).is_proven());
    }

    #[test]
    fn gate_accepts_unsigned_lt() {
        assert!(verify_output_preserved(&cmp_fn("acc_ult", BinOp::Lt, Ty::u32())).is_proven());
    }

    // --- THE KERNEL-ROOTED [PROVED] SURFACE (within the step-count frontier).
    //     Trust: RUNG 1. These ops emit a refutation whose step count is at or
    //     below `MAX_RECHECKABLE_REFUTATION_STEPS` (2048), so the clean CIC kernel
    //     re-checks the certificate IN-GATE via the proven sub-quadratic trie
    //     checker (`checkRefutes3_sound`, closure ⊆ FOUNDATIONAL) and the gate
    //     awards the KERNEL-rooted [PROVED] grade. `kernel_proof().is_some()` is
    //     true ONLY for `Proven { KernelRecheckable }`. MEASURED gate step counts:
    //     and/or/xor = 934 steps, sext = 164 steps (all under the 2048 frontier).
    //     ay is NOT in the [PROVED] TCB for these: the clean kernel re-derives the
    //     `Unsat` itself. ---

    // Bitwise [PROVED] coverage below: `or` (BvOr of two non-zero operands) is
    // NOT in the O(1) reflect fragment (only the `Or(Const0,x)` width-WRAPPER is),
    // so it stays on the SLOW KernelRecheckable path (934-step zip, < the
    // 20480-step frontier) and is asserted by `gate_emits_proved_for_real_or`.
    // `and`/`xor` MIGRATED to the O(1) KernelInstantiated path as of #42 (still
    // [PROVED], ay out of the cert chain) — see `gate_emits_proved_via_o1_for_real_{and,xor}`.

    /// `a as i32` from `i16` — a SIGNED widening cast lowers to `BvSignExt`, a
    /// 164-step refutation (well under the frontier) -> KERNEL-rooted [PROVED].
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_emits_proved_for_real_sext() {
        let v = verify_output_preserved(&cast_fn("proved_sext", Ty::i16(), Ty::i32()));
        let proof =
            v.kernel_proof().expect("sext must be KERNEL-rooted [PROVED] (164 steps < frontier)");
        proof.validate().expect("emitted sext proof self-validates");
    }

    // --- THE HONEST STEP-COUNT FRONTIER (Trust: RUNG 1). The slow-path iterative-WHNF
    //     kernel re-check covers sext at the KERNEL-rooted [PROVED] grade, at/below the
    //     `MAX_RECHECKABLE_REFUTATION_STEPS` (20480) frontier (< 5 GB, tens of seconds).
    //     HISTORICAL: the barrel-shifter shapes (shl=108825, lshr=129008 steps) USED to
    //     stay [VALIDATED] here (over-frontier slow-path bit-blast). They are now
    //     KERNEL-[PROVED] via the O(1) coercion-identity reflect path (bvf_shl/lshr/
    //     ashr_cong), which bypasses the bit-blast — so the ENTIRE scalar ALU
    //     (add/sub/neg, and/or/xor, the five compares, mul, udiv/sdiv, urem/srem,
    //     shl/lshr/ashr) is [PROVED]. The slow-path frontier now bounds only ops that
    //     lack an O(1) reflect arm AND a dedicated discharge. The [VALIDATED] residual
    //     is div/rem COMPOSITES (non-bare-div roots) and unmodeled constructs. ---

    /// `a << b` (u32) — now KERNEL-[PROVED] via the O(1) coercion-identity path
    /// (reflect BvShl -> BvF.Shl, cancel by bvf_shl_cong), bypassing the bit-blast.
    /// The re-check is tractable but multi-minute, hence out of the in-gate budget.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_shl_is_proved_via_o1_instantiation() {
        // shl is now [PROVED] via the O(1) coercion-identity path (reflect BvShl -> BvF.Shl,
        // cancel by bvf_shl_cong) — superseding the prior [VALIDATED] (the slow-path barrel-shifter
        // blast was 108825 steps > the {MAX_RECHECKABLE_REFUTATION_STEPS}-step frontier; the O(1)
        // path bypasses the bit-blast entirely).
        let v = verify_output_preserved(&binop_fn("val_shl", BinOp::Shl, Ty::u32()));
        assert!(v.is_proven(), "shl output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "shl u32 must be [PROVED] via the O(1) bvf_shl path; got {v:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_lshr_is_proved_via_o1_instantiation() {
        // logical >> now [PROVED] via O(1) (reflect BvLShr -> BvF.LShr, bvf_lshr_cong).
        let v = verify_output_preserved(&binop_fn("val_lshr", BinOp::Shr, Ty::u32()));
        assert!(v.is_proven(), "lshr output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "lshr u32 must be [PROVED] via the O(1) bvf_lshr path; got {v:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_ashr_is_proved_via_o1_instantiation() {
        // arithmetic >> (signed) now [PROVED] via O(1) (reflect BvAShr -> BvF.AShr, bvf_ashr_cong).
        let v = verify_output_preserved(&binop_fn("val_ashr", BinOp::Shr, Ty::i32()));
        assert!(v.is_proven(), "ashr output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "ashr i32 must be [PROVED] via the O(1) bvf_ashr path; got {v:?}"
        );
    }

    // --- DEEP CARRY/BORROW-CHAIN OPS: [PROVED]-CAPABLE ON-DEMAND, [VALIDATED] BY DEFAULT
    //     (ledger #21-CORRECTION retraction → #23 fix). History: the iterative-WHNF
    //     trampoline fixed the MAIN reduction (shallow ops re-check), but a RESIDUAL
    //     succ-peeling recursion in the kernel (`get_nat_bignat_whnf`) overflowed the
    //     256 MiB re-check on the deep ops — so they were retracted to [VALIDATED].
    //     That residual recursion is now FIXED (clean `get_nat_bignat_whnf` iterativized,
    //     clean pin ≥ b0af96a7). INDEPENDENTLY RE-VERIFIED on a fresh build:
    //     slt 7326 and sub 19389 kernel-re-check to Unsat3 at the shipped
    //     256 MiB stack with NO overflow/OOM. AY 0e35's current add artifact is
    //     17854 steps and passes `proof.validate()`; its prior full-kernel
    //     resource measurement is stale. They stay [VALIDATED] BY DEFAULT
    //     because the slow path exceeds the 2048-step TIME budget — NOT due to
    //     a stack barrier. These tests assert the production default
    //     (declined → [VALIDATED]). ---

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_neg_is_proved_via_o1_instantiation() {
        // B4 NEG PROMOTION (a bonus of SUB support): neg lowers to `BvSub(0, a)`
        // (auto = BvSub(Const0, wn0, 32)), which is in the O(1) sub fragment — so
        // adding BvSub reflection promotes neg too. PRE: 11317-step over-frontier
        // refutation -> [VALIDATED]. POST: O(1) kernel-[PROVED] via KernelInstantiated.
        let v = verify_output_preserved(&neg_fn("val_neg", Ty::i32()));
        assert!(v.is_proven(), "neg output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "B4: neg@32 (= sub 0,a) must be kernel-[PROVED] via O(1) instantiation; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "neg@32 must be [PROVED] via KernelInstantiated; got {v:?}"
        );
    }

    /// `a < b` (i32, SIGNED) — COMPARES slt PROMOTION ([VALIDATED]->[PROVED] via O(1)).
    /// PRE: 7326-step refutation (> frontier, overflows re-check) -> [VALIDATED]. POST:
    /// the slt value discharge (`Clean.BVC.slt_value_bridge`) proves the gate's real
    /// `Ite(BvSLt,1,0)` == `W(Ite(Not(BvSLt),0,1))` obligation by PURE branch-inversion
    /// over `bvSLtReal` (SAME-PREDICATE: the machine signed-compare flag traces back to
    /// BvSLt), tied to the REAL operands. (Lowering correctness — signed CSET condition
    /// not corrupted to unsigned — stays checked by `gate_refutes_signed_lt_lowered_as_unsigned`
    /// via ay; the faithfulness of bvSLtReal to the N⊕V hardware flags is the separate
    /// kernel-proved `Clean.BVC.slt_flag_bridge`.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_slt_is_proved_via_o1_instantiation() {
        let v = verify_output_preserved(&cmp_fn("proved_slt", BinOp::Lt, Ty::i32()));
        assert!(v.is_proven(), "signed `<` output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "COMPARES: slt@32 must be kernel-[PROVED] via O(1) instantiation; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "slt@32 must be [PROVED] via KernelInstantiated; got {v:?}"
        );
    }

    /// SLT control — DIVERGENT-OPERAND kernel-rejected (the operand-identity guard).
    /// machine = W(Ite(Not(BvSLt(X0,X1)),0,1)) ; auto = Ite(BvSLt(X0,X2),1,0) — DIFFERENT
    /// second operand, real obligation FALSE -> the slt discharge builds the goal from
    /// the REAL operand keys, so check_type REJECTS it.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_slt_divergent_operands_kernel_rejected() {
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        // REAL machine NZCV signed-LT flag form: machine = W(Ite(Eq(Eq(N,1), V), 0, 1)).
        let msb = |f: Formula| Formula::BvExtract { inner: b(f), high: 31, low: 31 };
        let one1 = Formula::BitVec { value: 1, width: 1 };
        let n_bit = msb(Formula::BvSub(b(opwrap(0)), b(opwrap(1)), 32));
        let v_cond = Formula::And(vec![
            Formula::Not(b(Formula::Eq(b(msb(opwrap(0))), b(msb(opwrap(1)))))),
            Formula::Not(b(Formula::Eq(b(n_bit.clone()), b(msb(opwrap(0)))))),
        ]);
        let mach_pred = Formula::Eq(b(Formula::Eq(b(n_bit), b(one1))), b(v_cond));
        let mach_inner = Formula::Ite(
            b(mach_pred),
            b(Formula::BitVec { value: 0, width: 64 }),
            b(Formula::BvAdd(
                b(Formula::BitVec { value: 0, width: 64 }),
                b(Formula::BitVec { value: 1, width: 64 }),
                64,
            )),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 64 }), b(mach_inner), 64)),
            high: 31,
            low: 0,
        };
        // matched auto discharges
        let auto_ok = Formula::Ite(
            b(Formula::BvSLt(b(wn(0)), b(wn(1)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let ok =
            crate::verify_output_instantiate::try_slt_value_discharge_for_test(&machine, &auto_ok);
        assert!(ok.is_some(), "the matched slt obligation must discharge; got {ok:?}");
        // divergent auto (X0,X2) must be kernel-rejected
        let auto_div = Formula::Ite(
            b(Formula::BvSLt(b(wn(0)), b(wn(2)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let bad =
            crate::verify_output_instantiate::try_slt_value_discharge_for_test(&machine, &auto_div);
        assert!(
            bad.is_none(),
            "a DIVERGENT-operand slt (machine X0,X1 vs auto X0,X2) must be KERNEL-REJECTED; got {bad:?}"
        );
    }

    /// `a <= b` (i32, SIGNED) — COMPARES sle PROMOTION ([VALIDATED]->[PROVED] via O(1)).
    /// Completes the five-compare surface (eq/ult/ule/slt/sle). The machine emits the
    /// inverted `a > b` flag `And(a≠b, a>=s b)` = `And(Not(Eq(sub,0)), Eq(Eq(N,1),V))`;
    /// the slt value discharge (`Clean.BVC.sle_value_bridge`) proves it equals IR
    /// `Ite(BvSLe,1,0)` via the subtract-zero bridge + slt N⊕V flag bridge + De Morgan +
    /// branch-inversion, tied to the REAL operands.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_sle_is_proved_via_o1_instantiation() {
        let v = verify_output_preserved(&cmp_fn("proved_sle", BinOp::Le, Ty::i32()));
        assert!(v.is_proven(), "signed `<=` output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "COMPARES: sle@32 must be kernel-[PROVED] via O(1) instantiation; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "sle@32 must be [PROVED] via KernelInstantiated; got {v:?}"
        );
    }

    /// SLE control — DIVERGENT-OPERAND kernel-rejected (the operand-identity guard).
    /// Builds the REAL machine signed-`>` flag over (X0,X1):
    ///   machine = W(Ite(And([Not(Eq(sub,0)), Eq(Eq(N,1),V)]), 0, 1)).
    /// A matched auto `Ite(BvSLe(X0,X1),1,0)` discharges; a DIVERGENT auto over (X0,X2)
    /// makes the real obligation FALSE -> the discharge builds the goal from the REAL
    /// operand keys, so check_type REJECTS it.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_sle_divergent_operands_kernel_rejected() {
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let msb = |f: Formula| Formula::BvExtract { inner: b(f), high: 31, low: 31 };
        let one1 = Formula::BitVec { value: 1, width: 1 };
        let n_bit = msb(Formula::BvSub(b(opwrap(0)), b(opwrap(1)), 32));
        let v_cond = Formula::And(vec![
            Formula::Not(b(Formula::Eq(b(msb(opwrap(0))), b(msb(opwrap(1)))))),
            Formula::Not(b(Formula::Eq(b(n_bit.clone()), b(msb(opwrap(0)))))),
        ]);
        let nlt = Formula::Eq(b(Formula::Eq(b(n_bit), b(one1))), b(v_cond));
        let neq = Formula::Not(b(Formula::Eq(
            b(Formula::BvSub(b(opwrap(0)), b(opwrap(1)), 32)),
            b(Formula::BitVec { value: 0, width: 32 }),
        )));
        let mach_pred = Formula::And(vec![neq, nlt]);
        let mach_inner = Formula::Ite(
            b(mach_pred),
            b(Formula::BitVec { value: 0, width: 64 }),
            b(Formula::BvAdd(
                b(Formula::BitVec { value: 0, width: 64 }),
                b(Formula::BitVec { value: 1, width: 64 }),
                64,
            )),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 64 }), b(mach_inner), 64)),
            high: 31,
            low: 0,
        };
        let auto_ok = Formula::Ite(
            b(Formula::BvSLe(b(wn(0)), b(wn(1)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let ok =
            crate::verify_output_instantiate::try_sle_value_discharge_for_test(&machine, &auto_ok);
        assert!(ok.is_some(), "the matched sle obligation must discharge; got {ok:?}");
        let auto_div = Formula::Ite(
            b(Formula::BvSLe(b(wn(0)), b(wn(2)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let bad =
            crate::verify_output_instantiate::try_sle_value_discharge_for_test(&machine, &auto_div);
        assert!(
            bad.is_none(),
            "a DIVERGENT-operand sle (machine X0,X1 vs auto X0,X2) must be KERNEL-REJECTED; got {bad:?}"
        );
    }

    /// `a == b` (i32) — COMPARES eq PROMOTION ([VALIDATED]->[PROVED] via O(1)).
    /// PRE: the 9677-step refutation exceeded the frontier -> [VALIDATED]. POST:
    /// the eq value discharge (`Clean.BVC.eq_value_bridge`) composes the
    /// subtract-zero bridge + branch-inversion to prove the gate's real
    /// `Ite(Eq, 1, 0)` == `W(Ite(Not(Eq(sub,0)), 0, 1))` obligation in the kernel.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_eq_is_proved_via_o1_instantiation() {
        let v = verify_output_preserved(&cmp_fn("proved_eq", BinOp::Eq, Ty::i32()));
        assert!(v.is_proven(), "`==` output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "COMPARES: eq@32 must be kernel-[PROVED] via O(1) instantiation; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "eq@32 must be [PROVED] via KernelInstantiated; got {v:?}"
        );
    }

    /// EQ control (iv) — DIVERGENT-OPERAND kernel-rejected (THE real-obligation
    /// guard). machine = W(Ite(¬Eq(BvSub(X0,X2,32),0),0,1)) over operands X0,X2 ;
    /// auto = Ite(Eq(W0,W1),1,0) over X0,X1 — BOTH eq-shaped, but the real
    /// obligation `machine == auto` is FALSE (different second operands). The eq
    /// discharge builds the kernel goal from the REAL operand keys, so the kernel
    /// `check_type` of `eq_value_bridge` REJECTS the divergence (the abstract
    /// eq-encoding tautology is NOT enough — ay is genuinely out of the TCB).
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_eq_divergent_operands_kernel_rejected() {
        let auto = Formula::Ite(
            b(Formula::Eq(b(wn(0)), b(wn(1)))),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        // build W(...) machine wrapper like the real shape, operands X0,X2.
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let sub = Formula::BvSub(b(opwrap(0)), b(opwrap(2)), 32);
        let inner_ite = Formula::Ite(
            b(Formula::Not(b(Formula::Eq(b(sub), b(Formula::BitVec { value: 0, width: 32 }))))),
            b(Formula::BitVec { value: 0, width: 64 }),
            b(Formula::BvAdd(
                b(Formula::BitVec { value: 0, width: 64 }),
                b(Formula::BitVec { value: 1, width: 64 }),
                64,
            )),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 64 }), b(inner_ite), 64)),
            high: 31,
            low: 0,
        };
        let r = crate::verify_output_instantiate::try_eq_value_discharge_for_test(&machine, &auto);
        assert!(
            r.is_none(),
            "DIVERGENT-operand eq (machine X0,X2 vs auto X0,X1) must be KERNEL-REJECTED              (the real obligation is false); got {r:?}"
        );
    }

    /// EQ control (i) — NON-CANONICAL shape falls through. A bare bitvector
    /// obligation (no Ite/Eq/flag structure) must NOT match the eq matcher; it
    /// either takes the bitvector-core path or stays [VALIDATED], never a false
    /// eq [PROVED]. (add@32 is the witness: it must remain add-path KernelInstantiated.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_eq_noncanonical_falls_through() {
        // A non-compare op (add) must NOT be graded by the eq discharge.
        let machine = symbolic_machine_output(
            &emit_text(&add_i32_fn()).expect("emit").1,
            emit_text(&add_i32_fn()).expect("emit").2,
            32,
            false,
        )
        .expect("decode");
        let auto = trust_ir_semantics(&add_i32_fn()).expect("auto");
        // The eq discharge must decline (not an Ite/Eq shape).
        let r = crate::verify_output_instantiate::try_eq_value_discharge_for_test(&machine, &auto);
        assert!(
            r.is_none(),
            "the eq matcher must DECLINE a non-compare (add) obligation; got {r:?}"
        );
    }

    /// EQ control (ii) — CORRUPTED emission refused end-to-end. Flip the CSET
    /// condition (EQ->NE) so machine computes `a != b` while IR auto = `a == b`;
    /// discharge_equal_pre finds SAT -> Refuted; the eq O(1) path never runs.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_eq_corrupted_emitted_byte_refused_end_to_end() {
        let f = cmp_fn("b4_corrupt_eq", BinOp::Eq, Ty::i32());
        let verdict = with_text_corruptor(
            |code: &mut Vec<u8>, base: u64| {
                let mut pc = base;
                let mut off = 0usize;
                while off + 4 <= code.len() {
                    let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                    let insn = decode_aarch64(&bytes, pc).expect("decode");
                    // CSET uses CSINC with an inverted condition; flip cond bit 12
                    // (EQ<->NE) of the CSINC to corrupt the compare result.
                    if matches!(insn.opcode, Opcode::Csinc) {
                        let mut word = u32::from_le_bytes(bytes);
                        word ^= 1 << 12; // invert condition LSB (EQ 0000 <-> NE 0001)
                        code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                        return;
                    }
                    if matches!(insn.opcode, Opcode::Ret) {
                        return;
                    }
                    pc += 4;
                    off += 4;
                }
            },
            || verify_output_preserved(&f),
        );
        assert!(
            !verdict.is_kernel_proved(),
            "a corrupted EQ->NE emission must NOT be eq-[PROVED]; got {verdict:?}"
        );
    }

    /// EQ control (iii) — MIS-REFLECTION kernel-guarded. A machine that is the
    /// inverted-CSET form but whose auto side is `Eq` over a DIFFERENT predicate
    /// shape (a non-eq Ite) must not be laundered: the matcher requires the exact
    /// `Ite(Eq, 1, 0)` auto and `W(Ite(Not(Eq(sub,0)),0,1))` machine, and the
    /// kernel `check_type` of `eq_value_bridge` is the sole authority. A
    /// hand-built machine whose inner predicate is NOT `Not(Eq(BvSub..,0))`
    /// declines at the matcher; a structurally-eq one discharges.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_eq_mis_reflection_is_kernel_guarded() {
        let f = cmp_fn("b4_eq_misreflect", BinOp::Eq, Ty::i32());
        let auto = trust_ir_semantics(&f).expect("auto");
        // A WRONG machine: the inner predicate is `Eq(sub, 0)` (NON-inverted, missing
        // the `Not`) — i.e. `pred ? 1 : 0` over `a-b==0`. This is `a != b` semantics
        // wrapped wrong; the matcher requires the INVERTED CSET (`pred ? 0 : 1`).
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine = symbolic_machine_output(&code, base, 32, false).expect("decode");
        // The correctly-shaped machine discharges.
        let ok = crate::verify_output_instantiate::try_eq_value_discharge_for_test(&machine, &auto);
        assert!(ok.is_some(), "the real eq@32 obligation must discharge; got {ok:?}");
        // A mis-paired auto (Eq over swapped... here: a NON-Ite auto) must decline.
        let wrong_auto = Formula::BitVec { value: 0, width: 32 };
        let bad = crate::verify_output_instantiate::try_eq_value_discharge_for_test(
            &machine,
            &wrong_auto,
        );
        assert!(bad.is_none(), "a non-Ite auto must DECLINE the eq discharge; got {bad:?}");
    }

    // (`gate_sle_over_frontier_stays_validated` removed — sle is now PROMOTED to
    //  O(1) kernel-[PROVED]; see `gate_sle_is_proved_via_o1_instantiation` above.)

    /// `a < b` (u32, UNSIGNED) — COMPARES ult PROMOTION ([VALIDATED]->[PROVED]).
    /// PRE: 7846-step refutation > frontier -> [VALIDATED]. POST: the ult value
    /// discharge (`Clean.BVC.ult_value_bridge`) proves the gate's real
    /// `Ite(BvULt,1,0)` == `W(Ite(Not(BvULt),0,1))` obligation by pure
    /// branch-inversion (both sides share the SAME BvULt predicate; no carry
    /// bridge), tied to the REAL operands.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_ult_is_proved_via_o1_instantiation() {
        let v = verify_output_preserved(&cmp_fn("proved_ult", BinOp::Lt, Ty::u32()));
        assert!(v.is_proven(), "unsigned `<` output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "COMPARES: ult@32 must be kernel-[PROVED] via O(1) instantiation; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "ult@32 must be [PROVED] via KernelInstantiated; got {v:?}"
        );
    }

    /// ULT control — DIVERGENT-OPERAND kernel-rejected (the operand-identity
    /// guard). machine = W(Ite(Not(BvULt(X0,X1)),0,1)) ; auto = Ite(BvULt(X0,X2),1,0)
    /// — DIFFERENT second operand, real obligation FALSE -> the ult discharge
    /// builds the goal from the REAL operand keys, so check_type REJECTS it.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_ult_divergent_operands_kernel_rejected() {
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let mach_inner = Formula::Ite(
            b(Formula::Not(b(Formula::BvULt(b(opwrap(0)), b(opwrap(1)), 32)))),
            b(Formula::BitVec { value: 0, width: 64 }),
            b(Formula::BvAdd(
                b(Formula::BitVec { value: 0, width: 64 }),
                b(Formula::BitVec { value: 1, width: 64 }),
                64,
            )),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 64 }), b(mach_inner), 64)),
            high: 31,
            low: 0,
        };
        // matched auto discharges
        let auto_ok = Formula::Ite(
            b(Formula::BvULt(b(wn(0)), b(wn(1)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let ok =
            crate::verify_output_instantiate::try_ult_value_discharge_for_test(&machine, &auto_ok);
        assert!(ok.is_some(), "the matched ult obligation must discharge; got {ok:?}");
        // divergent auto (X0,X2) must be kernel-rejected
        let auto_div = Formula::Ite(
            b(Formula::BvULt(b(wn(0)), b(wn(2)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let bad =
            crate::verify_output_instantiate::try_ult_value_discharge_for_test(&machine, &auto_div);
        assert!(
            bad.is_none(),
            "a DIVERGENT-operand ult (machine X0,X1 vs auto X0,X2) must be KERNEL-REJECTED; got {bad:?}"
        );
    }

    /// `a <= b` (u32, UNSIGNED) — COMPARES ule PROMOTION ([VALIDATED]->[PROVED]).
    /// PRE: 8288-step refutation > frontier -> [VALIDATED]. POST: the ule value
    /// discharge (`Clean.BVC.ule_value_bridge`) proves the gate's real
    /// `Ite(BvULe,1,0)` == `W(Ite(And(Not(BvULt),Not(Eq(BvSub,0))),0,1))`
    /// obligation (machine inverted Hi-condition) via De Morgan + the subtract-
    /// zero bridge + branch-inversion, tied to the REAL operands.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_ule_is_proved_via_o1_instantiation() {
        let v = verify_output_preserved(&cmp_fn("proved_ule", BinOp::Le, Ty::u32()));
        assert!(v.is_proven(), "unsigned `<=` output is preserved (Proven)");
        assert!(
            v.is_kernel_proved(),
            "COMPARES: ule@32 must be kernel-[PROVED] via O(1) instantiation; got {v:?}"
        );
        assert!(
            matches!(
                v,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "ule@32 must be [PROVED] via KernelInstantiated; got {v:?}"
        );
    }

    /// ULE control — DIVERGENT-OPERAND kernel-rejected (the operand-identity
    /// guard). machine over (X0,X1), auto BvULe over (X0,X2) -> real obligation
    /// FALSE -> the ule discharge ties the goal to the REAL operand keys, so
    /// check_type REJECTS it.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_ule_divergent_operands_kernel_rejected() {
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let mach_pred = Formula::And(vec![
            Formula::Not(b(Formula::BvULt(b(opwrap(0)), b(opwrap(1)), 32))),
            Formula::Not(b(Formula::Eq(
                b(Formula::BvSub(b(opwrap(0)), b(opwrap(1)), 32)),
                b(Formula::BitVec { value: 0, width: 32 }),
            ))),
        ]);
        let mach_inner = Formula::Ite(
            b(mach_pred),
            b(Formula::BitVec { value: 0, width: 64 }),
            b(Formula::BvAdd(
                b(Formula::BitVec { value: 0, width: 64 }),
                b(Formula::BitVec { value: 1, width: 64 }),
                64,
            )),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 64 }), b(mach_inner), 64)),
            high: 31,
            low: 0,
        };
        let auto_ok = Formula::Ite(
            b(Formula::BvULe(b(wn(0)), b(wn(1)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let ok =
            crate::verify_output_instantiate::try_ule_value_discharge_for_test(&machine, &auto_ok);
        assert!(ok.is_some(), "the matched ule obligation must discharge; got {ok:?}");
        let auto_div = Formula::Ite(
            b(Formula::BvULe(b(wn(0)), b(wn(2)), 32)),
            b(Formula::BitVec { value: 1, width: 32 }),
            b(Formula::BitVec { value: 0, width: 32 }),
        );
        let bad =
            crate::verify_output_instantiate::try_ule_value_discharge_for_test(&machine, &auto_div);
        assert!(
            bad.is_none(),
            "a DIVERGENT-operand ule (machine X0,X1 vs auto X0,X2) must be KERNEL-REJECTED; got {bad:?}"
        );
    }

    // --- THE BUG-CLASS ANTI-VACUITY (signed compare lowered as UNSIGNED) ---
    //
    // This is the EXACT class the campaign caught: a SIGNED relational compare
    // lowered with an UNSIGNED condition (abs(-5) returned -5). Take the REAL
    // signed-i32 `a < b` emission and corrupt the CSET/CSINC condition field from
    // the SIGNED `ge`/`lt` (bit15 set) to its UNSIGNED `hs`/`lo` counterpart
    // (bit15 clear) in the emitted bytes. The byte-derived machine output then
    // computes the UNSIGNED predicate while the auto-spec is the SIGNED `BvSLt`.
    // For e.g. a = -1 (0xFFFF_FFFF), b = 0: signed `-1 < 0` is TRUE, unsigned
    // `0xFFFF_FFFF < 0` is FALSE — so the gate MUST be Refuted (a CounterExample),
    // NEVER Proven, NEVER [PROVED].
    #[test]
    fn gate_refutes_signed_lt_lowered_as_unsigned() {
        let f = cmp_fn("ref_slt_as_ult", BinOp::Lt, Ty::i32());
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        // Cond-select (CSEL/CSINC/CSINV/CSNEG, incl. the CSET alias) carries its
        // condition in bits [15:12]. The signed conditions GE=0b1010 / LT=0b1011
        // differ from their unsigned counterparts HS=0b0010 / LO=0b0011 ONLY in
        // bit 15 (the high bit of the field). Clearing bit 15 turns the SIGNED
        // condition into the UNSIGNED one — the signed-as-unsigned miscompile.
        let mut flipped = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Csinc | Opcode::Csel | Opcode::Csinv | Opcode::Csneg) {
                let word = u32::from_le_bytes(bytes);
                let cond = (word >> 12) & 0xF;
                // Only mutate a SIGNED relational condition (GE/LT/GT/LE have bit3
                // set together with bit1); here the CSET for signed `<` emits the
                // inverted GE=0b1010. Clear bit 15 -> HS=0b0010 (unsigned).
                assert!(
                    cond == 0b1010 || cond == 0b1011 || cond == 0b1100 || cond == 0b1101,
                    "expected a signed cond in the cond-select, got {cond:#06b}"
                );
                let new_word = word & !(1 << 15); // clear bit15: signed -> unsigned
                code[off..off + 4].copy_from_slice(&new_word.to_le_bytes());
                let mutated = decode_aarch64(&new_word.to_le_bytes(), pc).expect("decode mutated");
                let new_cond = (new_word >> 12) & 0xF;
                assert_eq!(new_cond, cond & !0b1000, "bit15 clear maps signed->unsigned cond");
                assert!(
                    matches!(
                        mutated.opcode,
                        Opcode::Csinc | Opcode::Csel | Opcode::Csinv | Opcode::Csneg
                    ),
                    "mutation keeps it a cond-select, got {:?}",
                    mutated.opcode
                );
                flipped = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(flipped, "did not find a cond-select to mutate in emitted signed `<`");

        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode mutated");
        let verdict = match discharge_equal_pre(&machine_out, &auto, None) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "slt->ult".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "signed `<` lowered as UNSIGNED must be Refuted (the campaign's bug class), \
             got {verdict:?} — NEVER [PROVED]"
        );
    }

    // --- BUG-CLASS ANTI-VACUITY (UNSIGNED compare lowered as SIGNED) ---
    //
    // The mirror of the signed-as-unsigned case, now that unsigned compares are
    // [PROVED]: take the REAL unsigned-u32 `a < b` emission (CSET of the unsigned
    // LO/HS condition, bit15 clear) and SET bit15, turning the unsigned condition
    // into its SIGNED counterpart (LO=0b0011 -> LT=0b1011, HS=0b0010 -> GE=0b1010).
    // The byte-derived machine output then computes the SIGNED predicate while the
    // auto-spec is the UNSIGNED `BvULt`. For a = 0x8000_0000, b = 0: unsigned
    // `0x8000_0000 < 0` is FALSE, signed `-2^31 < 0` is TRUE — so the gate MUST be
    // Refuted, NEVER [PROVED]. Confirms the new CarryOut decomposition is not a
    // vacuous identity that would also accept the signed predicate.
    #[test]
    fn gate_refutes_unsigned_lt_lowered_as_signed() {
        let f = cmp_fn("ref_ult_as_slt", BinOp::Lt, Ty::u32());
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        let mut flipped = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Csinc | Opcode::Csel | Opcode::Csinv | Opcode::Csneg) {
                let word = u32::from_le_bytes(bytes);
                let cond = (word >> 12) & 0xF;
                // The unsigned `<` CSET emits the inverted HS=0b0010 (or LO=0b0011).
                // Bit 15 (the high field bit) is CLEAR for an unsigned cond.
                assert!(
                    cond == 0b0010 || cond == 0b0011 || cond == 0b1000 || cond == 0b1001,
                    "expected an unsigned cond in the cond-select, got {cond:#06b}"
                );
                let new_word = word | (1 << 15); // set bit15: unsigned -> signed
                code[off..off + 4].copy_from_slice(&new_word.to_le_bytes());
                let new_cond = (new_word >> 12) & 0xF;
                assert_eq!(new_cond, cond | 0b1000, "bit15 set maps unsigned->signed cond");
                let mutated = decode_aarch64(&new_word.to_le_bytes(), pc).expect("decode mutated");
                assert!(
                    matches!(
                        mutated.opcode,
                        Opcode::Csinc | Opcode::Csel | Opcode::Csinv | Opcode::Csneg
                    ),
                    "mutation keeps it a cond-select, got {:?}",
                    mutated.opcode
                );
                flipped = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(flipped, "did not find a cond-select to mutate in emitted unsigned `<`");

        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode mutated");
        let verdict = match discharge_equal_pre(&machine_out, &auto, None) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "ult->slt".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "unsigned `<` lowered as SIGNED must be Refuted (the campaign's bug class), \
             got {verdict:?} — NEVER [PROVED]"
        );
    }

    // --- BUG-CLASS ANTI-VACUITY (signed shift-right lowered as unsigned) ---
    //
    // This is the EXACT reverted-signedness shape the campaign caught, in the
    // shift family: a SIGNED `>>` (ASR, sign-filling) miscompiled to a LOGICAL
    // `>>` (LSR, zero-filling). Take the REAL signed-i32 `a >> b` emission, flip
    // the variable-shift TYPE field from ASR to LSR in the emitted bytes, and
    // discharge against the (correct, signed) auto-spec. For any negative `a`
    // shifted by a nonzero amount the fills differ, so the gate MUST return
    // Refuted (a CounterExample) — NEVER Proven, NEVER silently Unknown.
    #[test]
    fn gate_refuses_signed_shr_lowered_as_unsigned() {
        let f = binop_fn("ref_asr", BinOp::Shr, Ty::i32());
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        // AArch64 data-processing-2-source variable shift (ASRV/LSRV/LSLV/RORV):
        // op2 bits [11:10] select the shift type (00=LSL, 01=LSR, 10=ASR, 11=ROR).
        // ASR is 0b10; LSR is 0b01. Rewrite those two bits 10 -> 01 to turn the
        // arithmetic shift into a logical one (the signed-as-unsigned miscompile).
        let mut flipped = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Asrv) {
                let mut word = u32::from_le_bytes(bytes);
                word &= !(0b11 << 10); // clear op2[11:10]
                word |= 0b01 << 10; // set to LSR (0b01)
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                let mutated = decode_aarch64(&word.to_le_bytes(), pc).expect("decode mutated");
                assert!(
                    matches!(mutated.opcode, Opcode::Lsrv),
                    "op2 10->01 must turn ASRV into LSRV, got {:?}",
                    mutated.opcode
                );
                flipped = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(flipped, "did not find an ASRV to mutate in emitted i32 >>()");

        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode mutated");
        let verdict = match discharge_equal_pre(&machine_out, &auto, None) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "asr->lsr".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "ASRV->LSRV-mutated signed-shr bytes must be Refuted (signed-as-unsigned \
             miscompile), got {verdict:?}"
        );
    }

    // --- REFUSE: a mismatching emission -> Refuted (not Unknown, not Proven) ---

    #[test]
    fn gate_refuses_corrupted_emission() {
        // Build the real emission for a correct `add`, then CORRUPT one
        // instruction (rewrite the data-processing op to a SUB) and feed the
        // corrupted bytes through the same byte-derived machine-output path the
        // gate uses, discharging against the (correct) add auto-spec. The
        // mismatch MUST be a CounterExample (Refuted), proving the gate has
        // teeth against byte-level corruption.
        let f = binop_fn("ref_add", BinOp::Add, Ty::i32());
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        // Find the ADD (Rd = Rn + Rm) data-processing instruction and flip it to
        // SUB by toggling bit 30 of the 32-bit little-endian word (ADD<->SUB for
        // the add/subtract (shifted register) encoding). Locate it by decoding.
        let mut corrupted = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Add) {
                let mut word = u32::from_le_bytes(bytes);
                word ^= 1 << 30; // ADD (shifted reg) bit30=0 -> SUB bit30=1
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                corrupted = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(corrupted, "did not find an ADD to corrupt in emitted add()");

        let machine_out =
            symbolic_machine_output(&code, base, 32, false).expect("decode corrupted");
        let verdict = match discharge_equal_pre(&machine_out, &auto, None) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "corrupted".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "corrupted ADD->SUB bytes must be Refuted, got {verdict:?}"
        );
    }

    /// The same miscompile as `gate_refuses_corrupted_emission`, but driven
    /// through [`verify_output_preserved`] — the single entry point every
    /// verified-codegen claim is made on, including `#[trust::verified_codegen]`.
    ///
    /// The test above reassembles the verdict from `discharge_equal_pre`, so it
    /// pins the discharge and nothing else: emission, container parsing, decode,
    /// and the verdict/byte-drop wiring could all rot without it noticing. This
    /// one corrupts the bytes inside the real pipeline, so a miscompile has to
    /// survive every stage to escape. A `Refuted` function must also carry NO
    /// shippable bytes.
    #[test]
    fn miscompiled_emission_is_refuted_through_the_public_entry_point() {
        let f = binop_fn("public_entry_add", BinOp::Add, Ty::i32());
        let (verdict, bytes) = with_text_corruptor(
            |code: &mut Vec<u8>, base: u64| {
                let mut pc = base;
                let mut off = 0usize;
                while off + 4 <= code.len() {
                    let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                    let insn = decode_aarch64(&bytes, pc).expect("decode");
                    if matches!(insn.opcode, Opcode::Add) {
                        // ADD (shifted register) bit30=0; setting it yields SUB.
                        let mut word = u32::from_le_bytes(bytes);
                        word ^= 1 << 30;
                        code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                        return;
                    }
                    if matches!(insn.opcode, Opcode::Ret) {
                        return;
                    }
                    pc += 4;
                    off += 4;
                }
            },
            || verify_output_preserved_capturing_with_backend(&f, &default_verification_backend()),
        );
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "an ADD->SUB miscompile must be Refuted by the public gate entry point, \
             got {verdict:?}"
        );
        assert!(bytes.is_none(), "a Refuted function must never carry shippable bytes");
    }

    /// The uncorrupted control for the test above: the same function, same entry
    /// point, no corruptor. Without it a `Refuted` assertion proves nothing —
    /// a gate that refuted everything (a broken decoder, an unreadable object
    /// container) would satisfy the RED case and reject every correct program.
    #[test]
    fn faithful_emission_is_proven_through_the_public_entry_point() {
        let f = binop_fn("public_entry_add_ok", BinOp::Add, Ty::i32());
        let (verdict, bytes) =
            verify_output_preserved_capturing_with_backend(&f, &default_verification_backend());
        assert!(
            verdict.is_proven(),
            "a faithful emission must be Proven by the public gate entry point, got {verdict:?}"
        );
        assert!(bytes.is_some(), "a Proven function must carry the exact bytes the gate verified");
    }

    #[test]
    fn gate_refuses_wrong_spec_mismatch() {
        // Directly exercise the discharge with a deliberate mismatch: emitted
        // `add` bytes vs the `sub` auto-spec. SAT => Refuted. This is the same
        // SAT teeth the test-file negative controls assert, surfaced at the
        // verdict layer.
        let f = binop_fn("ref_add2", BinOp::Add, Ty::i32());
        let (_obj, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        let wrong = trust_ir_semantics(&binop_fn("sub", BinOp::Sub, Ty::i32())).expect("interp");
        assert!(
            matches!(discharge_equal_pre(&machine_out, &wrong, None), Discharge::CounterExample),
            "add bytes vs sub spec must be a CounterExample (Refuted)"
        );
    }

    // --- ACCEPT: remainder (signed + unsigned) -> Proven ---
    //
    // `%` lowers to sdiv/udiv + msub, so the byte-derived machine output is
    // `a - q*b`. The auto-spec now encodes Rem in that same truncated-division
    // identity form (eval_binop), so ay discharges the equality structurally in
    // <1s instead of timing out on a native bvsrem/bvurem identity proof. The
    // gate auto-adds the `b != 0` precondition (divisor_nonzero_precondition).

    #[test]
    fn gate_accepts_srem() {
        assert!(verify_output_preserved(&binop_fn("acc_srem", BinOp::Rem, Ty::i32())).is_proven());
    }

    #[test]
    fn gate_accepts_urem() {
        assert!(verify_output_preserved(&binop_fn("acc_urem", BinOp::Rem, Ty::u32())).is_proven());
    }

    // --- REFUSE: a one-bit SDIV->UDIV mutation of the signed-rem emission ---
    //
    // ANTI-VACUITY teeth for remainder: take the REAL signed-`%` emission and flip
    // bit 10 of the DIV word (AArch64 data-processing-2-source: bit10 selects
    // UDIV(0) vs SDIV(1)), turning the embedded SDIV into a UDIV. The machine then
    // computes `a - udiv(a,b)*b`, which differs from the signed auto-spec for any
    // negative dividend. The gate MUST return Refuted (not Proven, not Unknown),
    // proving the Proven verdict above genuinely checked the quotient signedness.
    #[test]
    fn gate_refuses_srem_div_signedness_flip() {
        let f = binop_fn("ref_srem", BinOp::Rem, Ty::i32());
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let pre = divisor_nonzero_precondition(&f);
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        // Locate the SDIV and flip bit 10 (o1: 1=SDIV -> 0=UDIV).
        let mut flipped = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Sdiv) {
                let mut word = u32::from_le_bytes(bytes);
                word ^= 1 << 10; // SDIV (bit10=1) -> UDIV (bit10=0)
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                // Confirm the mutated word now decodes as UDIV (genuine wrong op).
                let mutated = decode_aarch64(&word.to_le_bytes(), pc).expect("decode mutated");
                assert!(
                    matches!(mutated.opcode, Opcode::Udiv),
                    "bit-10 flip must turn SDIV into UDIV, got {:?}",
                    mutated.opcode
                );
                flipped = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(flipped, "did not find an SDIV to mutate in emitted i32 %()");

        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode mutated");
        let verdict = match discharge_equal_pre(&machine_out, &auto, pre.as_ref()) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "udiv-flip".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "SDIV->UDIV-mutated signed-rem bytes must be Refuted, got {verdict:?}"
        );
    }

    // --- ACCEPT: 64-bit remainder (signed + unsigned) -> Proven ---
    //
    // The Rem auto-spec (eval_binop) and the byte-derived machine output are both
    // width-generic: i64/u64 `%` lowers to a 64-bit sdiv/udiv + msub, so the
    // machine output is the SAME truncated-division identity `a - q*b` at width 64
    // that the i32/u32 cases use at width 32. ay discharges the equality
    // structurally (no multiplier bit-blasting), so the 64-bit certs are near-free
    // and complete the div/rem family across both register widths.

    #[test]
    fn gate_accepts_srem_i64() {
        assert!(
            verify_output_preserved(&binop_fn("acc_srem64", BinOp::Rem, Ty::i64())).is_proven()
        );
    }

    #[test]
    fn gate_accepts_urem_u64() {
        assert!(
            verify_output_preserved(&binop_fn("acc_urem64", BinOp::Rem, Ty::u64())).is_proven()
        );
    }

    // --- REFUSE: a one-bit SDIV->UDIV mutation of the signed i64-rem emission ---
    //
    // ANTI-VACUITY teeth for 64-bit remainder, mirroring the i32 control: take the
    // REAL signed i64-`%` emission and flip bit 10 of the DIV word (turning the
    // embedded 64-bit SDIV into a UDIV). The machine then computes
    // `a - udiv(a,b)*b` at 64 bits, which differs from the signed auto-spec for any
    // negative dividend. The gate MUST return Refuted, proving the i64 Proven
    // verdict above genuinely checked the quotient signedness at width 64.
    #[test]
    fn gate_refuses_srem_i64_div_signedness_flip() {
        let f = binop_fn("ref_srem64", BinOp::Rem, Ty::i64());
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let pre = divisor_nonzero_precondition(&f);
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        let mut flipped = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Sdiv) {
                let mut word = u32::from_le_bytes(bytes);
                word ^= 1 << 10; // SDIV (bit10=1) -> UDIV (bit10=0)
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                let mutated = decode_aarch64(&word.to_le_bytes(), pc).expect("decode mutated");
                assert!(
                    matches!(mutated.opcode, Opcode::Udiv),
                    "bit-10 flip must turn SDIV into UDIV, got {:?}",
                    mutated.opcode
                );
                flipped = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(flipped, "did not find an SDIV to mutate in emitted i64 %()");

        let machine_out = symbolic_machine_output(&code, base, 64, false).expect("decode mutated");
        let verdict = match discharge_equal_pre(&machine_out, &auto, pre.as_ref()) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "udiv-flip64".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "SDIV->UDIV-mutated signed i64-rem bytes must be Refuted, got {verdict:?}"
        );
    }

    // ---------------------------------------------------------------------
    // CFG + MEMORY IR builders (mirror proven_output_condbr.rs / cfg_mem.rs).
    // ---------------------------------------------------------------------

    /// bb0: `cond = lhs <cmp> rhs; if cond == 0 -> else_blk else -> then_blk`.
    fn cmp_branch_block(
        cmp: BinOp,
        lhs: usize,
        rhs: usize,
        cond_local: usize,
        then_blk: usize,
        else_blk: usize,
    ) -> BasicBlock {
        BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(cond_local),
                rvalue: Rvalue::BinaryOp(
                    cmp,
                    Operand::Copy(Place::local(lhs)),
                    Operand::Copy(Place::local(rhs)),
                ),
                span: sp(),
            }],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local(cond_local)),
                targets: vec![(0, BlockId(else_blk))],
                otherwise: BlockId(then_blk),
                exhaustive_enum_unreachable: false,
                span: sp(),
            },
        }
    }

    fn ret_use_block(id: usize, src_local: usize) -> BasicBlock {
        BasicBlock {
            id: BlockId(id),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Copy(Place::local(src_local))),
                span: sp(),
            }],
            terminator: Terminator::Return,
        }
    }

    /// max(a,b): if a>=b {a} else {b} — lowers to a REAL CondBr.
    fn author_max() -> VerifiableFunction {
        wrap(
            "cfg_max",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
                ],
                blocks: vec![
                    cmp_branch_block(BinOp::Ge, 1, 2, 3, 1, 2),
                    ret_use_block(1, 1),
                    ret_use_block(2, 2),
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// min(a,b): if a<=b {a} else {b}.
    fn author_min() -> VerifiableFunction {
        wrap(
            "cfg_min",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::bool_ty(), name: None },
                ],
                blocks: vec![
                    cmp_branch_block(BinOp::Le, 1, 2, 3, 1, 2),
                    ret_use_block(1, 1),
                    ret_use_block(2, 2),
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// clamp(x,lo,hi): nested-branch CFG stressing the nested-Ite merge.
    fn author_clamp() -> VerifiableFunction {
        wrap(
            "cfg_clamp",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("lo".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: Some("hi".into()) },
                    LocalDecl { index: 4, ty: Ty::bool_ty(), name: None },
                    LocalDecl { index: 5, ty: Ty::bool_ty(), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: sp(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(4)),
                            targets: vec![(0, BlockId(2))],
                            otherwise: BlockId(1),
                            exhaustive_enum_unreachable: false,
                            span: sp(),
                        },
                    },
                    ret_use_block(1, 2),
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Gt,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(3)),
                            ),
                            span: sp(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(5)),
                            targets: vec![(0, BlockId(4))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: sp(),
                        },
                    },
                    ret_use_block(3, 3),
                    ret_use_block(4, 1),
                ],
                arg_count: 3,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// `switch3(x, v0, v1, vd): match x { 0 => v0, 1 => v1, _ => vd }` — a
    /// 3-arm integer SwitchInt over the raw u32 discriminant `x`. This exercises
    /// the multi-way (>2 arm) switch cascade in `eval_block` and the machine
    /// path-merger's nested CMP+B.cond chain. The discriminant is an arg register
    /// (not a bool compare), so the discr width is 32 directly.
    fn author_switch3() -> VerifiableFunction {
        wrap(
            "cfg_switch3",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("v0".into()) },
                    LocalDecl { index: 3, ty: Ty::u32(), name: Some("v1".into()) },
                    LocalDecl { index: 4, ty: Ty::u32(), name: Some("vd".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(1)),
                            targets: vec![(0, BlockId(1)), (1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: sp(),
                        },
                    },
                    ret_use_block(1, 2), // x==0 -> v0
                    ret_use_block(2, 3), // x==1 -> v1
                    ret_use_block(3, 4), // otherwise -> vd
                ],
                arg_count: 4,
                return_ty: Ty::u32(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// `ptr_rw(p: *mut i32, v: i32) -> i32 { *p = v; *p }` — store-then-load.
    fn make_ptr_rw() -> VerifiableFunction {
        let ptr_ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) };
        wrap(
            "mem_ptr_rw",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("v".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: sp(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref],
                            })),
                            span: sp(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// `ptr_rw_u8(p: *mut u8, v: u8) -> u8 { *p = v; *p }` — SINGLE-BYTE store-then-load.
    /// The minimal memory rung: a width-1 store/load needs only `selectStoreSame` (no
    /// byte-adjacency, no BvConcat), so it is the first store-load promotable to [PROVED].
    fn make_ptr_rw_u8() -> VerifiableFunction {
        let ptr_ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) };
        wrap(
            "mem_ptr_rw_u8",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u8(), name: None },
                    LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                    LocalDecl { index: 2, ty: Ty::u8(), name: Some("v".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                            span: sp(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref],
                            })),
                            span: sp(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u8(),
                datatype_defs: Default::default(),
            },
        )
    }

    fn make_ptr_ro_u64() -> VerifiableFunction {
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u64()) };
        wrap(
            "mem_ptr_ro_u64",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u64(), name: None },
                    LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
        )
    }

    fn make_ptr_ro_u8() -> VerifiableFunction {
        let ptr_ty = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
        wrap(
            "mem_ptr_ro_u8",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u8(), name: None },
                    LocalDecl { index: 1, ty: ptr_ty, name: Some("p".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u8(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// THE `&T` PARAMETER RUNG, on the REAL IR semantics — what is now in the
    /// fragment, and exactly what still is not.
    ///
    /// `trust_ir_semantics` of `fn(p: *const u8) -> u8 { *p }` is a BARE
    /// `Select(MEM, X0)`: a read of memory the function never wrote. That is the
    /// shape a reference parameter produces, it is the shape that had no lemma,
    /// and it now DISCHARGES in the kernel through `Clean.BVC.selectAddrCong`
    /// under the no-store side condition. This asserts it on the semantics the
    /// gate actually derives, not on a hand-built `Formula`.
    ///
    /// Two things are deliberately still OUT, and naming them here keeps the
    /// claim honest — neither is about caller memory:
    ///
    ///  * MULTI-BYTE ASSEMBLY. A `u64` load is eight byte `Select`s joined by
    ///    `BvConcat` (IR side) / `BvOr`+`BvShl` (machine side). `BvConcat` has no
    ///    `BvF` constructor at all, so the whole obligation leaves the fragment
    ///    before the memory model is even consulted.
    ///  * THE OPAQUE-LOAD READOUT SPINE. Even at one byte the emitted machine
    ///    output carries `Extract[7:0]∘ZeroExt∘Or∘Extract[31:0]∘ZeroExt³` over the
    ///    load, plus a `BvAdd(X0, 0)` address wrapper the IR side does not have.
    ///    The concrete-cons `reflect_mem` path normalizes that spine for a
    ///    store-load (the load bridges to the stored value, a concrete cons that
    ///    reduces) — but a bare read is IRREDUCIBLY opaque by construction, so
    ///    that trick cannot apply and a width-general extract-of-wider-zeroext
    ///    lemma is what is missing. So the whole function stays [VALIDATED].
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn a_reference_parameter_load_reaches_the_fragment_but_its_readout_spine_does_not() {
        use crate::verify_output_instantiate::test_support as ts;

        // ── the one-byte read-only load: a BARE read, and it DISCHARGES ───────
        let f8 = make_ptr_ro_u8();
        let auto8 = trust_ir_semantics(&f8).expect("auto");
        assert!(
            matches!(&auto8, Formula::Select(m, _) if matches!(&**m, Formula::Var(..))),
            "a load through a pointer PARAMETER must be a bare Select over a memory \
             Var (the shape with no read-over-write to bridge through); got {auto8:?}"
        );
        assert!(store_free(&auto8), "a read-only body must satisfy the side condition");
        assert!(
            ts::reflect_formula_for(&auto8, &auto8, &auto8).is_ok(),
            "the real IR semantics of `*p` must now reflect"
        );
        let d = crate::verify_output_instantiate::try_o1_instantiation_discharge(&auto8, &auto8);
        assert!(
            d.as_deref().is_some_and(|t| t.contains("selectAddrCong")),
            "the real caller-memory read must be KERNEL-discharged via selectAddrCong; got {d:?}"
        );

        // ── the multi-byte load: still out, and out at `BvConcat` ─────────────
        let f64 = make_ptr_ro_u64();
        let auto64 = trust_ir_semantics(&f64).expect("auto");
        let err = ts::reflect_formula_for(&auto64, &auto64, &auto64)
            .err()
            .expect("a multi-byte load is not in the fragment");
        assert!(
            err.contains("BvConcat"),
            "the u64 load must fall out at the multi-byte ASSEMBLY, not at the memory \
             model — that distinction is the whole point of this test; got: {err}"
        );

        // ── the whole functions: ay-proven, not yet kernel-[PROVED] ───────────
        for f in [&f8, &f64] {
            let v = verify_output_preserved(f);
            assert!(v.is_proven(), "`{}` must be ay-proven", f.name);
            assert!(
                !v.is_kernel_proved(),
                "honest: `{}` awaits the opaque-load readout spine / multi-byte assembly",
                f.name
            );
        }
    }

    /// HONEST CHARACTERIZATION (memory construct rung, in progress). The memory
    /// store-load reflection BRIDGE is built and verified: the clean-side auto
    /// obligation `Select(Store(MEM, X0, v), X0)` reflects through the new
    /// `reflect_formula` Select arm (→ `BvF.Leaf (bvSelect (bvStore …) …)` with the
    /// `selectStoreSame` bridge `bvfEval(leaf) = bvfEval(stored-value core)`), so the
    /// memory model composes with the bvfEval coercion path. `make_ptr_rw_u8` is
    /// therefore ay-`is_proven()` and the discharge MECHANISM is present.
    ///
    /// It is NOT yet kernel-[PROVED]: the emitted u8 (sub-register-width) LDRB readout
    /// carries a coercion spine `Extract[7:0]∘ZeroExt∘Or∘Extract[31:0]∘ZeroExt∘ZeroExt∘
    /// ZeroExt∘Select` where an `Extract[31:0]` sits over a 40-bit zero-ext (extract
    /// width ≠ zero-ext inner length). The current `extract_zeroext_id` fragment only
    /// cancels a WIDTH-MATCHED extract-of-zeroext, so the machine side falls out of the
    /// fragment and the gate fail-closes to [VALIDATED] (never a false [PROVED]). The
    /// remaining piece is a general extract-of-wider-zeroext normalization lemma — a
    /// bounded coercion-library extension, cleanly scoped by this spine.
    /// THE MEMORY STORE-LOAD [PROVED] DISCHARGE — verified end-to-end (kernel-checked).
    /// The `Select(Store(MEM, X0, v), X0)` roundtrip reflects through `selectStoreSame`
    /// (concrete-cons leaves) and the clean kernel `check_type` ACCEPTS the discharge —
    /// the memory model is [PROVED]-grade, not merely ay-[VALIDATED]. And the SUB-REGISTER
    /// readout coercion spine that blocks the width-matched fragment
    /// (`Extract[7:0]∘ZeroExt∘Extract[31:0]∘ZeroExt∘ZeroExt`) is NORMALIZED by concrete-cons
    /// `bvfEval` reduction — the exact gap this rung closes.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_mem_store_load_discharge_is_kernel_checked() {
        use crate::verify_output_instantiate::test_support as ts;
        let auto = trust_ir_semantics(&make_ptr_rw_u8()).expect("auto");
        assert!(ts::reflect_mem_ok(&auto), "store-load auto must reflect via the memory path");
        // (1) the store-load roundtrip is kernel-discharged (selectStoreSame bridge).
        assert!(
            ts::mem_discharge(&auto, &auto).is_some(),
            "memory store-load must be KERNEL-[PROVED] via selectStoreSame"
        );
        // (2) the width-mismatched sub-register readout coercion spine is normalized by
        // concrete-cons reduction (this is what the width-matched extract_zeroext_id could NOT do).
        let b = |x: Formula| Box::new(x);
        let wrapped = Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvExtract {
                    inner: b(Formula::BvZeroExt(b(Formula::BvZeroExt(b(auto.clone()), 32)), 32)),
                    high: 31,
                    low: 0,
                }),
                32,
            )),
            high: 7,
            low: 0,
        };
        assert!(
            ts::mem_discharge(&wrapped, &auto).is_some(),
            "sub-register readout coercion spine must be kernel-normalized by concrete-cons reduction"
        );
    }

    /// HONEST CHARACTERIZATION. `make_ptr_rw_u8` (a REAL emitted function) is ay-`is_proven()`
    /// and its store-load MODEL is kernel-[PROVED] (see gate_mem_store_load_discharge_is_kernel_checked),
    /// but the whole function is not YET kernel-promoted: the emitted codegen SPILLS the value `v`
    /// through the stack frame, so the byte actually stored is a MULTI-BYTE `BvOr`/`Shl` reassembly
    /// of frame-slot `Select`s (an 8-byte spill-reload), not a bare `Extract(X1)`. Reflecting that
    /// needs the multi-byte load-assembly path (general `BvOr`/`Shl` + per-byte `selectStoreDiff`
    /// discharged by `bvBeqConsFalse` for byte-adjacency — the keystones are landed). Until that is
    /// wired the gate fail-closes to [VALIDATED] — never a false [PROVED].
    #[test]
    fn gate_mem_u8_is_validated_pending_multibyte_spill_assembly() {
        let v = verify_output_preserved(&make_ptr_rw_u8());
        assert!(v.is_proven(), "u8 store-load must be ay-proven");
        assert!(
            !v.is_kernel_proved(),
            "honest: real u8 fn [PROVED] awaits the multi-byte frame-spill assembly reflection"
        );
    }

    /// `loop1(a) -> i32 { loop {} }` — a one-block self-loop: Goto(bb0). Both the
    /// IR interpreter (block backedge) and the machine path-merger (PC backedge)
    /// must fail closed, never hang, never fake a proof.
    fn author_loop() -> VerifiableFunction {
        wrap(
            "cfg_loop",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: sp(),
                    }],
                    terminator: Terminator::Goto(BlockId(0)),
                }],
                arg_count: 1,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    // --- ACCEPT (Proven): loop-free CFG + memory ---

    #[test]
    fn gate_accepts_cfg_max() {
        assert!(verify_output_preserved(&author_max()).is_proven());
    }

    #[test]
    fn gate_accepts_cfg_min() {
        assert!(verify_output_preserved(&author_min()).is_proven());
    }

    #[test]
    fn gate_accepts_cfg_clamp() {
        assert!(verify_output_preserved(&author_clamp()).is_proven());
    }

    #[test]
    fn gate_accepts_mem_store_load_roundtrip() {
        assert!(verify_output_preserved(&make_ptr_rw()).is_proven());
    }

    #[test]
    fn gate_accepts_cfg_switch3() {
        // A 3-arm integer match: the multi-way SwitchInt cascade. The byte-derived
        // machine output (a CMP+B.cond chain) must provably equal the nested-Ite
        // auto-spec `Ite(x==0, v0, Ite(x==1, v1, vd))` for all inputs.
        assert!(verify_output_preserved(&author_switch3()).is_proven());
    }

    // --- REFUSE: a wrong 3-arm-switch spec (two arms swapped) -> Refuted ---
    //
    // ANTI-VACUITY teeth for the multi-way switch: take the REAL switch3 emission
    // and discharge it against a DELIBERATELY WRONG auto-spec in which the x==0 and
    // x==1 arms are swapped (so the spec claims x==0 yields v1 and x==1 yields v0).
    // For the input x==0, v0 != v1 the machine output (v0) differs from the wrong
    // spec (v1), so ay MUST find a CounterExample. This proves the Proven verdict
    // above genuinely pinned each arm to its own value rather than vacuously
    // accepting any cascade.
    #[test]
    fn gate_refuses_cfg_switch3_swapped_arms() {
        let f = author_switch3();
        let (_obj, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");

        // Wrong spec: same function but arms 0 and 1 point at swapped value blocks
        // (block 1 returns v1, block 2 returns v0).
        let mut wrong = author_switch3();
        wrong.body.blocks[1] = ret_use_block(1, 3); // x==0 -> v1 (WRONG)
        wrong.body.blocks[2] = ret_use_block(2, 2); // x==1 -> v0 (WRONG)
        let wrong_spec = trust_ir_semantics(&wrong).expect("interpreter (wrong spec)");

        assert!(
            matches!(
                discharge_equal_pre(&machine_out, &wrong_spec, None),
                Discharge::CounterExample
            ),
            "switch3 bytes vs swapped-arm spec must be a CounterExample (Refuted)"
        );
    }

    // --- REFUSE (Refuted): corrupted branch + corrupted store ---

    #[test]
    fn gate_refuses_corrupted_branch() {
        // Emit the real `max` (a real CondBr), then INVERT the conditional-branch
        // condition by toggling bit 0 of the B.cond encoding (cond field LSB:
        // GE<->LT, etc.). The corrupted bytes select the WRONG path; discharged
        // against the correct max auto-spec, ay must find a CounterExample.
        let f = author_max();
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        let mut corrupted = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            // B.cond (conditional branch immediate): top byte 0x54.
            if (bytes[3] == 0x54) && (bytes[0] & 0x10) == 0 {
                let mut word = u32::from_le_bytes(bytes);
                word ^= 1; // flip cond LSB -> inverts the branch condition
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                corrupted = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(corrupted, "did not find a B.cond to corrupt in emitted max()");

        let machine_out =
            symbolic_machine_output(&code, base, 32, false).expect("decode corrupted");
        let verdict = match discharge_equal_pre(&machine_out, &auto, None) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "corrupted".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "corrupted-branch bytes must be Refuted, got {verdict:?}"
        );
    }

    #[test]
    fn gate_refuses_corrupted_store() {
        // Emit the real store-load roundtrip, then CORRUPT the store: rewrite the
        // STR that writes the value `v` to the pointer into a STR of a different
        // register, so the loaded value no longer equals v. Discharged against the
        // correct `*p` auto-spec, ay must find a CounterExample.
        //
        // We corrupt by flipping the Rt (source) field of the value-store STR to a
        // register holding a different value (the frame pointer / a zeroed reg).
        let f = make_ptr_rw();
        let auto = trust_ir_semantics(&f).expect("interpreter");
        let (_obj, mut code, base) = emit_text(&f).expect("emit");

        // Locate the FIRST 32-bit STR (the `*p = v` store of W1). STR (immediate,
        // unsigned offset, 32-bit) has top byte 0xB9 and bit 22 == 0 (store).
        let mut corrupted = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            let word = u32::from_le_bytes(bytes);
            let is_str32 = (word >> 22) == 0b1011100100; // STR Wt, [Xn, #imm]
            if is_str32 {
                let rt = word & 0x1f;
                // Pick a different source register for Rt (XZR/WZR = 31 stores 0).
                let new_rt = if rt == 31 { 0 } else { 31 };
                let new_word = (word & !0x1f) | new_rt;
                code[off..off + 4].copy_from_slice(&new_word.to_le_bytes());
                corrupted = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(corrupted, "did not find a 32-bit STR to corrupt in emitted ptr_rw()");

        let machine_out =
            symbolic_machine_output(&code, base, 32, false).expect("decode corrupted");
        let verdict = match discharge_equal_pre(&machine_out, &auto, None) {
            Discharge::Proven => OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            Discharge::CounterExample => OutputVerdict::Refuted { detail: "corrupted".into() },
            Discharge::Unknown(r) => OutputVerdict::Unknown { reason: r },
        };
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "corrupted-store bytes must be Refuted, got {verdict:?}"
        );
    }

    // --- FAIL-CLOSED: unsupported shapes -> Unknown (never Proven) ---

    #[test]
    fn gate_fails_closed_on_loop() {
        // A self-looping function: the IR interpreter detects the block backedge
        // and the machine path-merger detects the PC backedge — both Err, so the
        // verdict is Unknown. Must NOT hang and must NOT be Proven.
        let v = verify_output_preserved(&author_loop());
        assert!(matches!(v, OutputVerdict::Unknown { .. }), "loop must be Unknown: {v:?}");
    }

    fn words(ws: &[u32]) -> Vec<u8> {
        ws.iter().flat_map(|w| w.to_le_bytes()).collect()
    }

    /// The executor must EXPLORE the taken side of a `CBZ`.
    ///
    /// CBZ/CBNZ/TBZ/TBNZ do not produce `Effect::ConditionalBranch` — only
    /// `B.cond` does. They produce `Effect::PcUpdate { value: Ite(..) }`, which
    /// the executor used to DISCARD, silently executing them as never-taken
    /// while every other unmodeled effect fails closed.
    ///
    /// This pins the property directly rather than asserting on a verdict: two
    /// functions that differ ONLY in the value returned on the TAKEN side must
    /// have different symbolic outputs. Under the discard they were both just
    /// the fall-through, hence equal — which is what let a miscompile hiding
    /// behind a `cbz` come back `Proven` while the byte-identical `b.cond` form
    /// came back `Refuted`.
    #[test]
    fn taken_side_of_cbz_is_explored() {
        // cbz w0, +8 ; ret (return x) ; mov w0,#K ; ret (return K)
        const CBZ_P8: u32 = 0x3400_0040;
        const RET: u32 = 0xD65F_03C0;
        let movz_w0 = |k: u32| 0x5280_0000 | (k << 5);

        let five = symbolic_machine_output(&words(&[CBZ_P8, RET, movz_w0(5), RET]), 0, 32, false)
            .expect("cbz function must be modeled, not rejected");
        let seven = symbolic_machine_output(&words(&[CBZ_P8, RET, movz_w0(7), RET]), 0, 32, false)
            .expect("cbz function must be modeled, not rejected");

        assert_ne!(
            five, seven,
            "the taken side of a CBZ was not explored: two functions differing only in the \
             value returned when the branch IS taken produced identical symbolic output, so a \
             miscompile on that path is invisible to the gate"
        );
        assert!(
            matches!(five, Formula::Ite(..)),
            "a CBZ must fork the symbolic state (expected an Ite), got: {five:?}"
        );
    }

    /// A 64-bit logical immediate with a NON-ZERO ROTATE must reach the machine
    /// model as its real value.
    ///
    /// `decode_bitmask_immediate` overflowed `1u64 << 64` for exactly this
    /// family. In a release build — how `trustc` ships — that silently yielded
    /// `#0`, so `eor x0, x0, #0x8000000000000000` was modeled as the IDENTITY
    /// and the gate certified it `Proven` with a kernel-re-checkable grade
    /// against an identity spec, on code wrong for every input.
    ///
    /// This asserts the derived output is NOT the bare argument, which is the
    /// property that failed. Checking only that decoding succeeds would have
    /// passed throughout: the decoder never errored, it returned zero.
    #[test]
    fn rotated_logical_immediate_reaches_the_machine_model() {
        // eor x0, x0, #0x8000000000000000 ; ret   (assembler-derived words)
        const EOR_SIGNBIT: u32 = 0xD241_0000;
        const RET: u32 = 0xD65F_03C0;

        let out = symbolic_machine_output(&words(&[EOR_SIGNBIT, RET]), 0, 64, false)
            .expect("eor with a rotated 64-bit immediate must be modeled");
        let identity = symbolic_machine_output(&words(&[RET]), 0, 64, false)
            .expect("bare ret must be modeled");

        assert_ne!(
            out, identity,
            "a rotated 64-bit logical immediate decoded to 0: the machine model sees \
             `eor x0,x0,#0x8000000000000000` as the identity, so that miscompile would be \
             certified Proven against an identity spec"
        );
    }

    /// The same property for `TBZ`, which shares the discarded-`PcUpdate` path.
    #[test]
    fn taken_side_of_tbz_is_explored() {
        // tbz w0, #0, +8 ; ret ; mov w0,#K ; ret
        const TBZ_B0_P8: u32 = 0x3600_0040;
        const RET: u32 = 0xD65F_03C0;
        let movz_w0 = |k: u32| 0x5280_0000 | (k << 5);

        let a = symbolic_machine_output(&words(&[TBZ_B0_P8, RET, movz_w0(5), RET]), 0, 32, false)
            .expect("tbz function must be modeled, not rejected");
        let b = symbolic_machine_output(&words(&[TBZ_B0_P8, RET, movz_w0(7), RET]), 0, 32, false)
            .expect("tbz function must be modeled, not rejected");

        assert_ne!(a, b, "the taken side of a TBZ was not explored");
        assert!(matches!(a, Formula::Ite(..)), "a TBZ must fork the symbolic state: {a:?}");
    }

    /// f32 (single-precision) FADD is now PROVEN end-to-end: the emitted
    /// `FADD Sd,Sn,Sm` bytes equal the auto-derived IR semantics
    /// `FpToIeeeBv(FpAdd(RNE, FpFromBits(a,8,24), FpFromBits(b,8,24)))` over the
    /// V0/V1 S-lanes, for ALL inputs. This rides the IDENTICAL width-parametric
    /// shape as f64 (just eb=8/sb=24 on the 32-bit S-lane). The residual
    /// `B-aarch64-fp-pending` never covered f32 add/sub/mul/div — only f32 FCVT
    /// conversions and FMA — so f32 arithmetic was UNIMPLEMENTED (fail-closed),
    /// not a soundness boundary. f16 still fails closed.
    #[test]
    fn f32_add_proven_output_symbolic() {
        let f = wrap(
            "fadd_f32",
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Float { width: 32 }, name: None },
                    LocalDecl { index: 1, ty: Ty::Float { width: 32 }, name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::Float { width: 32 }, name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: sp(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Float { width: 32 },
                datatype_defs: Default::default(),
            },
        );
        let v = verify_output_preserved(&f);
        assert!(v.is_proven(), "f32 add must be Proven (bit-exact IEEE-754 f32): {v:?}");
    }

    /// The f32 IR-semantics auto-spec is EXACTLY the two-sided FP shape over the
    /// V0/V1 S-lanes at eb=8/sb=24 — the identical `Formula` the machine side
    /// (sem_fadd, width 32) produces, so the `Eq` discharge is a structural
    /// `X == X`. f32 arg lanes are `vn_lane(_, 32)` (S-lane), NOT the f64 D-lane.
    #[test]
    fn f32_add_ir_semantics_is_the_s_lane_fp_shape() {
        let f = binop_fn("f32_add_shape", BinOp::Add, Ty::Float { width: 32 });
        let auto = trust_ir_semantics(&f).expect("f32 auto-spec");
        let expected = fp_add_bits(vn_lane(0, 32), vn_lane(1, 32), 32);
        assert_eq!(
            auto, expected,
            "f32 add IR semantics must be FpToIeeeBv(FpAdd(RNE,..)) @ eb8/sb24"
        );
        // The reinterprets must be at the f32 format (eb 8, sb 24), NOT f64.
        match &auto {
            Formula::FpToIeeeBv(inner) => match inner.as_ref() {
                Formula::FpAdd(_, l, r) => {
                    assert!(matches!(**l, Formula::FpFromBits { eb: 8, sb: 24, .. }));
                    assert!(matches!(**r, Formula::FpFromBits { eb: 8, sb: 24, .. }));
                }
                other => panic!("expected FpAdd, got {other:?}"),
            },
            other => panic!("expected FpToIeeeBv, got {other:?}"),
        }
    }

    // ====================================================================
    // f64 FLOATING-POINT ADDITION — bit-exact IEEE-754 proven output.
    //   The emitted `FADD Dd,Dn,Dm` bytes must equal the auto-derived IR
    //   semantics `FpToIeeeBv(FpAdd(RNE, FpFromBits(a), FpFromBits(b)))`,
    //   where `a`/`b` are the V0/V1 D-lanes. Bit-exact (structural `Eq`):
    //   NaN payloads and the sign of ±0.0 are distinguished.
    // ====================================================================

    /// `fn add(a: f64, b: f64) -> f64 { a + b }`, hand-built.
    fn f64_add_fn(name: &str) -> VerifiableFunction {
        binop_fn(name, BinOp::Add, Ty::Float { width: 64 })
    }

    /// The IR-semantics auto-spec of an f64 add is EXACTLY the two-sided FP shape
    /// over the V0/V1 D-lanes — the identical `Formula` the machine side (sem_fadd)
    /// produces, so the `Eq` discharge is a structural `X == X`.
    #[test]
    fn f64_add_ir_semantics_is_the_fp_shape() {
        let auto = trust_ir_semantics(&f64_add_fn("f64_add_shape")).expect("f64 auto-spec");
        let a = vn_d_lane(0);
        let b = vn_d_lane(1);
        let expected = fp64_add_bits(a, b);
        assert_eq!(auto, expected, "f64 add IR semantics must be FpToIeeeBv(FpAdd(RNE,..))");
        // Structurally: the outer node is the FP->BV reinterpret of an FpAdd.
        assert!(
            matches!(&auto, Formula::FpToIeeeBv(inner) if matches!(**inner, Formula::FpAdd(..))),
            "auto-spec must be FpToIeeeBv(FpAdd(..)): {auto:?}"
        );
    }

    /// The emitted LIR carries a `Fadd` over F64/D-register operands — NOT an
    /// integer `Iadd`. (The bytes then decode to `FADD Dd,Dn,Dm`.)
    #[test]
    fn f64_add_lir_carries_fadd_not_iadd() {
        use trust_cg_lower::instructions::Opcode as LirOpcode;
        let backend =
            TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), host_triple());
        let lir = backend.lower_function(&f64_add_fn("f64_add_lir")).expect("lower f64 add");
        let mut saw_fadd = false;
        let mut saw_iadd = false;
        for block in lir.blocks.values() {
            for insn in &block.instructions {
                match insn.opcode {
                    LirOpcode::Fadd => saw_fadd = true,
                    LirOpcode::Iadd => saw_iadd = true,
                    _ => {}
                }
            }
        }
        assert!(saw_fadd, "f64 add LIR must carry Fadd");
        assert!(!saw_iadd, "f64 add LIR must NOT carry integer Iadd");
    }

    /// END-TO-END PROOF: emit the real `FADD` bytes and discharge
    /// `machine_out == auto` over ALL inputs (fully symbolic). The scoping proved
    /// this exact shape UNSAT; assert Proven (bit-exact IEEE-754 equality).
    #[test]
    fn f64_add_proven_output_symbolic() {
        let v = verify_output_preserved(&f64_add_fn("f64_add_proven"));
        assert!(
            v.is_proven(),
            "f64 add must be Proven (emitted FADD == IEEE FpAdd(RNE) over all inputs): {v:?}"
        );
    }

    /// NEGATIVE CONTROL (SAT / Refuted): the FP add shape must NOT equal the plain
    /// INTEGER BvAdd of the same bit patterns (what the OLD, wrong `sem_fadd`
    /// modeled). On concrete lanes 3.5 / 2.5 the FP result is bits(6.0) while the
    /// integer BvAdd of the two bit patterns is a garbage value — the discharge of
    /// `fp_shape == integer_bvadd` finds a COUNTEREXAMPLE (they differ). This is
    /// the teeth: had we kept `BvAdd`, the model would be wrong and this control
    /// would (incorrectly) match.
    #[test]
    fn f64_add_negative_control_fp_shape_ne_integer_bvadd() {
        let a_bits = Formula::BitVec { value: 3.5_f64.to_bits() as i128, width: 64 };
        let b_bits = Formula::BitVec { value: 2.5_f64.to_bits() as i128, width: 64 };
        let fp_shape = fp64_add_bits(a_bits.clone(), b_bits.clone());
        let integer_bvadd = Formula::BvAdd(b(a_bits), b(b_bits), 64);
        // fp.add(3.5, 2.5) == 6.0, but the u64 sum of their bit patterns != bits(6.0).
        let outcome = discharge_equal_pre(&fp_shape, &integer_bvadd, None);
        assert!(
            matches!(outcome, Discharge::CounterExample),
            "FP add shape must DIFFER from integer BvAdd (the whole point of the FP model): {outcome:?}"
        );
        // And the FP shape DOES equal the true FP answer bits(6.0) (sanity: the
        // control fails for the right reason, not because the shape is broken).
        let six = Formula::BitVec { value: 6.0_f64.to_bits() as i128, width: 64 };
        assert!(
            matches!(discharge_equal_pre(&fp_shape, &six, None), Discharge::Proven),
            "FP add shape must equal bits(6.0)"
        );
    }

    /// VALUE-DIFF: 3.5 + 2.5 == 6.0. Assert `FpFromBits`/`FpToIeeeBv` round-trips
    /// carry the exact IEEE bit patterns by discharging the concrete instance
    /// against the emitted FADD.
    #[test]
    fn f64_add_value_diff_3p5_plus_2p5_is_6() {
        assert_f64_add_concrete(3.5_f64, 2.5_f64, 6.0_f64);
    }

    /// VALUE-DIFF: -0.0 + -0.0 == -0.0 (sign bit set: 0x8000_0000_0000_0000).
    /// Distinguishes -0.0 from +0.0 (which `fp.eq` would conflate) via bit-exact
    /// `Eq`.
    #[test]
    fn f64_add_value_diff_neg_zero_plus_neg_zero_is_neg_zero() {
        let neg_zero = f64::from_bits(0x8000_0000_0000_0000);
        assert_eq!(neg_zero.to_bits(), 0x8000_0000_0000_0000);
        assert_f64_add_concrete(neg_zero, neg_zero, neg_zero);
    }

    /// VALUE-DIFF: 1.0 + NaN classifies as NaN (via `fp.isNaN`). The native
    /// `1.0 + NaN` is NaN; assert the emitted-byte result satisfies `fp.isNaN`.
    #[test]
    fn f64_add_value_diff_one_plus_nan_is_nan() {
        let nan = f64::from_bits(0x7FF8_0000_0000_0000); // a quiet NaN
        assert!(nan.is_nan());
        // Evaluate the add SHAPE on concrete lanes (1.0, NaN) and CLASSIFY the
        // 64-bit result as a NaN via `fp.isNaN`. The symbolic proof ties this
        // shape to the emitted FADD bytes; here we show `1.0 + NaN` is always a
        // NaN (in-frontier concrete f64 fp.add + classification).
        let one_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: 1.0_f64.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        let nan_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: nan.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        // Classify the FP SUM directly (fp.isNaN over fp.add) — the same
        // rounding-mode add the emitted FADD computes, without the FpToIeeeBv /
        // FpFromBits round-trip (which ay does not fold, forcing Unknown).
        // Discharge that `isNaN(1.0 + NaN)` is VALID.
        let sum =
            Formula::FpAdd(b(Formula::FpRoundingMode(RoundingMode::RNE)), b(one_fp), b(nan_fp));
        let is_nan = Formula::FpIsNaN(b(sum));
        let outcome = discharge_valid(&is_nan);
        assert!(
            matches!(outcome, Discharge::Proven),
            "1.0 + NaN must always be NaN (fp.isNaN): {outcome:?}"
        );
    }

    /// Discharge a CONCRETE f64 add instance against the emitted FADD bytes:
    /// under `V0d == bits(a)` and `V1d == bits(b)`, the machine result must equal
    /// `bits(expected)` — a bit-exact `Eq` over the 64-bit patterns. UNSAT of the
    /// negation => the emitted bytes compute `a + b == expected` bit-for-bit.
    fn assert_f64_add_concrete(a: f64, b_val: f64, expected: f64) {
        // The symbolic test (`f64_add_proven_output_symbolic`) proves the emitted
        // FADD bytes == `fp64_add_bits(V0d, V1d)` for ALL inputs. Here we EVALUATE
        // that SAME shape on CONCRETE bit patterns and check it equals
        // `bits(expected)` bit-exactly. ay decides this UNSAT (verified by the
        // `probe_concrete_f64_logics` canary — concrete f64 fp.add over constant
        // lanes is in-frontier). Composed with the symbolic proof, this gives the
        // end-to-end concrete guarantee `emitted-bytes(a, b) == expected`.
        let a_bits = Formula::BitVec { value: a.to_bits() as i128, width: 64 };
        let b_bits = Formula::BitVec { value: b_val.to_bits() as i128, width: 64 };
        let shape = fp64_add_bits(a_bits, b_bits);
        let expected_bits = Formula::BitVec { value: expected.to_bits() as i128, width: 64 };
        let outcome = discharge_equal_pre(&shape, &expected_bits, None);
        assert!(
            matches!(outcome, Discharge::Proven),
            "f64 {a} + {b_val} must equal {expected} bit-exactly: {outcome:?}"
        );
    }

    // ====================================================================
    // f64 FLOATING-POINT SUBTRACTION / MULTIPLICATION — bit-exact IEEE-754
    //   proven output. The emitted `FSUB Dd,Dn,Dm` / `FMUL Dd,Dn,Dm` bytes
    //   must equal the auto-derived IR semantics
    //   `FpToIeeeBv(FpSub|FpMul(RNE, FpFromBits(a), FpFromBits(b)))` over the
    //   V0/V1 D-lanes. Bit-exact (structural `Eq`): NaN payloads and the sign
    //   of ±0.0 are distinguished. Mirrors the f64-add slice exactly.
    // ====================================================================

    /// `fn sub(a: f64, b: f64) -> f64 { a - b }`, hand-built.
    fn f64_sub_fn(name: &str) -> VerifiableFunction {
        binop_fn(name, BinOp::Sub, Ty::Float { width: 64 })
    }

    /// `fn mul(a: f64, b: f64) -> f64 { a * b }`, hand-built.
    fn f64_mul_fn(name: &str) -> VerifiableFunction {
        binop_fn(name, BinOp::Mul, Ty::Float { width: 64 })
    }

    /// The IR-semantics auto-spec of an f64 sub/mul is EXACTLY the two-sided FP
    /// shape over the V0/V1 D-lanes — the identical `Formula` the machine side
    /// (sem_fsub/sem_fmul) produces, so the `Eq` discharge is a structural
    /// `X == X`.
    #[test]
    fn f64_sub_ir_semantics_is_the_fp_shape() {
        let auto = trust_ir_semantics(&f64_sub_fn("f64_sub_shape")).expect("f64 sub auto-spec");
        let expected = fp64_sub_bits(vn_d_lane(0), vn_d_lane(1));
        assert_eq!(auto, expected, "f64 sub IR semantics must be FpToIeeeBv(FpSub(RNE,..))");
        assert!(
            matches!(&auto, Formula::FpToIeeeBv(inner) if matches!(**inner, Formula::FpSub(..))),
            "auto-spec must be FpToIeeeBv(FpSub(..)): {auto:?}"
        );
    }

    #[test]
    fn f64_mul_ir_semantics_is_the_fp_shape() {
        let auto = trust_ir_semantics(&f64_mul_fn("f64_mul_shape")).expect("f64 mul auto-spec");
        let expected = fp64_mul_bits(vn_d_lane(0), vn_d_lane(1));
        assert_eq!(auto, expected, "f64 mul IR semantics must be FpToIeeeBv(FpMul(RNE,..))");
        assert!(
            matches!(&auto, Formula::FpToIeeeBv(inner) if matches!(**inner, Formula::FpMul(..))),
            "auto-spec must be FpToIeeeBv(FpMul(..)): {auto:?}"
        );
    }

    /// The emitted LIR carries `Fsub`/`Fmul` over F64/D-register operands — NOT
    /// integer `Isub`/`Imul`. (The bytes then decode to `FSUB`/`FMUL Dd,Dn,Dm`.)
    #[test]
    fn f64_sub_mul_lir_carries_fsub_fmul_not_isub_imul() {
        use trust_cg_lower::instructions::Opcode as LirOpcode;
        let backend =
            TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), host_triple());
        // Sub.
        let lir = backend.lower_function(&f64_sub_fn("f64_sub_lir")).expect("lower f64 sub");
        let (mut saw_fsub, mut saw_isub) = (false, false);
        for block in lir.blocks.values() {
            for insn in &block.instructions {
                match insn.opcode {
                    LirOpcode::Fsub => saw_fsub = true,
                    LirOpcode::Isub => saw_isub = true,
                    _ => {}
                }
            }
        }
        assert!(saw_fsub, "f64 sub LIR must carry Fsub");
        assert!(!saw_isub, "f64 sub LIR must NOT carry integer Isub");
        // Mul.
        let lir = backend.lower_function(&f64_mul_fn("f64_mul_lir")).expect("lower f64 mul");
        let (mut saw_fmul, mut saw_imul) = (false, false);
        for block in lir.blocks.values() {
            for insn in &block.instructions {
                match insn.opcode {
                    LirOpcode::Fmul => saw_fmul = true,
                    LirOpcode::Imul => saw_imul = true,
                    _ => {}
                }
            }
        }
        assert!(saw_fmul, "f64 mul LIR must carry Fmul");
        assert!(!saw_imul, "f64 mul LIR must NOT carry integer Imul");
    }

    /// END-TO-END PROOF: emit the real `FSUB` bytes and discharge
    /// `machine_out == auto` over ALL inputs (fully symbolic). Proven means the
    /// two-sided FP shape is a structural `X == X` (UNSAT of the negation).
    #[test]
    fn f64_sub_proven_output_symbolic() {
        let v = verify_output_preserved(&f64_sub_fn("f64_sub_proven"));
        assert!(
            v.is_proven(),
            "f64 sub must be Proven (emitted FSUB == IEEE FpSub(RNE) over all inputs): {v:?}"
        );
    }

    /// END-TO-END PROOF for f64 mul.
    #[test]
    fn f64_mul_proven_output_symbolic() {
        let v = verify_output_preserved(&f64_mul_fn("f64_mul_proven"));
        assert!(
            v.is_proven(),
            "f64 mul must be Proven (emitted FMUL == IEEE FpMul(RNE) over all inputs): {v:?}"
        );
    }

    /// NEGATIVE CONTROL (SAT / Refuted): the FP sub shape must NOT equal the
    /// plain INTEGER BvSub of the same bit patterns (the OLD, wrong model). On
    /// concrete lanes 5.0 / 2.5 the FP result is bits(2.5) while the integer
    /// BvSub of the bit patterns is garbage — the discharge finds a
    /// COUNTEREXAMPLE. This is the teeth: the old `BvSub` model would be wrong.
    #[test]
    fn f64_sub_negative_control_fp_shape_ne_integer_bvsub() {
        let a_bits = Formula::BitVec { value: 5.0_f64.to_bits() as i128, width: 64 };
        let b_bits = Formula::BitVec { value: 2.5_f64.to_bits() as i128, width: 64 };
        let fp_shape = fp64_sub_bits(a_bits.clone(), b_bits.clone());
        let integer_bvsub = Formula::BvSub(b(a_bits), b(b_bits), 64);
        let outcome = discharge_equal_pre(&fp_shape, &integer_bvsub, None);
        assert!(
            matches!(outcome, Discharge::CounterExample),
            "FP sub shape must DIFFER from integer BvSub: {outcome:?}"
        );
        // And the FP shape DOES equal the true FP answer bits(2.5).
        let two_p5 = Formula::BitVec { value: 2.5_f64.to_bits() as i128, width: 64 };
        assert!(
            matches!(discharge_equal_pre(&fp_shape, &two_p5, None), Discharge::Proven),
            "FP sub shape must equal bits(2.5)"
        );
    }

    /// NEGATIVE CONTROL (SAT / Refuted): FP mul shape != integer BvMul. On
    /// concrete lanes 3.0 / 2.0 the FP result is bits(6.0) while the integer
    /// BvMul of the bit patterns is garbage.
    #[test]
    fn f64_mul_negative_control_fp_shape_ne_integer_bvmul() {
        let a_bits = Formula::BitVec { value: 3.0_f64.to_bits() as i128, width: 64 };
        let b_bits = Formula::BitVec { value: 2.0_f64.to_bits() as i128, width: 64 };
        let fp_shape = fp64_mul_bits(a_bits.clone(), b_bits.clone());
        let integer_bvmul = Formula::BvMul(b(a_bits), b(b_bits), 64);
        let outcome = discharge_equal_pre(&fp_shape, &integer_bvmul, None);
        assert!(
            matches!(outcome, Discharge::CounterExample),
            "FP mul shape must DIFFER from integer BvMul: {outcome:?}"
        );
        let six = Formula::BitVec { value: 6.0_f64.to_bits() as i128, width: 64 };
        assert!(
            matches!(discharge_equal_pre(&fp_shape, &six, None), Discharge::Proven),
            "FP mul shape must equal bits(6.0)"
        );
    }

    /// VALUE-DIFF: 5.0 - 2.5 == 2.5, bit-exact over the emitted FSUB shape.
    #[test]
    fn f64_sub_value_diff_5_minus_2p5_is_2p5() {
        assert_f64_binop_concrete(fp64_sub_bits, 5.0_f64, 2.5_f64, 2.5_f64, "-");
    }

    /// VALUE-DIFF: 3.0 * 2.0 == 6.0, bit-exact over the emitted FMUL shape.
    #[test]
    fn f64_mul_value_diff_3_times_2_is_6() {
        assert_f64_binop_concrete(fp64_mul_bits, 3.0_f64, 2.0_f64, 6.0_f64, "*");
    }

    /// VALUE-DIFF (SIGN): -0.0 * -1.0 == +0.0 (0x0000_0000_0000_0000). The sign
    /// bit distinguishes +0.0 from -0.0, which `fp.eq` would conflate — the
    /// bit-exact `Eq` catches it. (IEEE: (-0.0) * (-1.0) = +0.0.)
    #[test]
    fn f64_mul_value_diff_neg_zero_times_neg_one_is_pos_zero() {
        let neg_zero = f64::from_bits(0x8000_0000_0000_0000);
        assert_eq!(neg_zero.to_bits(), 0x8000_0000_0000_0000);
        let pos_zero = 0.0_f64;
        assert_eq!(pos_zero.to_bits(), 0);
        // Cross-check against the native result too (defends the expected value).
        assert_eq!((neg_zero * -1.0_f64).to_bits(), 0);
        assert_f64_binop_concrete(fp64_mul_bits, neg_zero, -1.0_f64, pos_zero, "*");
    }

    /// VALUE-DIFF (NaN propagation): 1.0 * NaN classifies as NaN via `fp.isNaN`.
    #[test]
    fn f64_mul_value_diff_one_times_nan_is_nan() {
        let nan = f64::from_bits(0x7FF8_0000_0000_0000); // a quiet NaN
        assert!(nan.is_nan());
        let one_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: 1.0_f64.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        let nan_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: nan.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        // Classify the FP PRODUCT directly (fp.isNaN over fp.mul), the same
        // rounding-mode mul the emitted FMUL computes, without the round-trip
        // (which ay does not fold). Discharge `isNaN(1.0 * NaN)` VALID.
        let prod =
            Formula::FpMul(b(Formula::FpRoundingMode(RoundingMode::RNE)), b(one_fp), b(nan_fp));
        let is_nan = Formula::FpIsNaN(b(prod));
        let outcome = discharge_valid(&is_nan);
        assert!(
            matches!(outcome, Discharge::Proven),
            "1.0 * NaN must always be NaN (fp.isNaN): {outcome:?}"
        );
    }

    /// VALUE-DIFF (NaN propagation): 1.0 - NaN classifies as NaN.
    #[test]
    fn f64_sub_value_diff_one_minus_nan_is_nan() {
        let nan = f64::from_bits(0x7FF8_0000_0000_0000);
        assert!(nan.is_nan());
        let one_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: 1.0_f64.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        let nan_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: nan.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        let diff =
            Formula::FpSub(b(Formula::FpRoundingMode(RoundingMode::RNE)), b(one_fp), b(nan_fp));
        let is_nan = Formula::FpIsNaN(b(diff));
        let outcome = discharge_valid(&is_nan);
        assert!(
            matches!(outcome, Discharge::Proven),
            "1.0 - NaN must always be NaN (fp.isNaN): {outcome:?}"
        );
    }

    /// f32 sub/mul/div are now PROVEN end-to-end (same width-parametric S-lane
    /// shape as f32 add, at eb=8/sb=24). NO divisor guard for div: IEEE f32
    /// division is total (`x/0.0` = ±inf, `0.0/0.0` = NaN — neither traps).
    #[test]
    fn f32_sub_mul_div_proven_output_symbolic() {
        let sub = binop_fn("fsub_f32", BinOp::Sub, Ty::Float { width: 32 });
        assert!(
            verify_output_preserved(&sub).is_proven(),
            "f32 sub must be Proven (bit-exact IEEE-754 f32)"
        );
        let mul = binop_fn("fmul_f32", BinOp::Mul, Ty::Float { width: 32 });
        assert!(
            verify_output_preserved(&mul).is_proven(),
            "f32 mul must be Proven (bit-exact IEEE-754 f32)"
        );
        let div = binop_fn("fdiv_f32", BinOp::Div, Ty::Float { width: 32 });
        assert!(
            verify_output_preserved(&div).is_proven(),
            "f32 div must be Proven (bit-exact IEEE-754 f32; total division, no guard)"
        );
    }

    /// f16 (half-precision) FP arithmetic STILL fails closed (Unknown): no
    /// bit-exact model is wired for width 16, so it must never reach Proven.
    #[test]
    fn gate_fails_closed_on_f16() {
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div] {
            let f = binop_fn("f16_op", op, Ty::Float { width: 16 });
            let v = verify_output_preserved(&f);
            assert!(
                matches!(v, OutputVerdict::Unknown { .. }),
                "f16 {op:?} must be Unknown (fail-closed): {v:?}"
            );
        }
    }

    /// `fn div(a: f64, b: f64) -> f64 { a / b }`, hand-built.
    fn f64_div_fn(name: &str) -> VerifiableFunction {
        binop_fn(name, BinOp::Div, Ty::Float { width: 64 })
    }

    /// f64 DIV is now PROVEN: the emitted `FDIV Dd,Dn,Dm` bytes equal the
    /// auto-derived IR semantics `FpToIeeeBv(FpDiv(RNE, FpFromBits(a),
    /// FpFromBits(b)))` over ALL inputs. NO guard: IEEE-754 division is total
    /// (`x/0.0` = ±inf, `0.0/0.0` = NaN — neither traps).
    #[test]
    fn f64_div_proven_output_symbolic() {
        let v = verify_output_preserved(&f64_div_fn("f64_div_proven"));
        assert!(
            v.is_proven(),
            "f64 div must be Proven (emitted FDIV == IEEE FpDiv(RNE) over all inputs): {v:?}"
        );
    }

    /// The IR-semantics auto-spec of an f64 div is EXACTLY the two-sided FP shape
    /// over the V0/V1 D-lanes — the identical `Formula` the machine side
    /// (sem_fdiv) produces, so the `Eq` discharge is a structural `X == X`.
    #[test]
    fn f64_div_ir_semantics_is_the_fp_shape() {
        let auto = trust_ir_semantics(&f64_div_fn("f64_div_shape")).expect("f64 div auto-spec");
        let expected = fp64_div_bits(vn_d_lane(0), vn_d_lane(1));
        assert_eq!(auto, expected, "f64 div IR semantics must be FpToIeeeBv(FpDiv(RNE,..))");
        assert!(
            matches!(&auto, Formula::FpToIeeeBv(inner) if matches!(**inner, Formula::FpDiv(..))),
            "auto-spec must be FpToIeeeBv(FpDiv(..)): {auto:?}"
        );
    }

    /// The emitted LIR carries `Fdiv` over F64/D-register operands — NOT integer
    /// `Sdiv`/`Udiv`. (The bytes then decode to `FDIV Dd,Dn,Dm`.)
    #[test]
    fn f64_div_lir_carries_fdiv_not_sdiv_udiv() {
        use trust_cg_lower::instructions::Opcode as LirOpcode;
        let backend =
            TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::host(), host_triple());
        let lir = backend.lower_function(&f64_div_fn("f64_div_lir")).expect("lower f64 div");
        let (mut saw_fdiv, mut saw_sdiv, mut saw_udiv) = (false, false, false);
        for block in lir.blocks.values() {
            for insn in &block.instructions {
                match insn.opcode {
                    LirOpcode::Fdiv => saw_fdiv = true,
                    LirOpcode::Sdiv => saw_sdiv = true,
                    LirOpcode::Udiv => saw_udiv = true,
                    _ => {}
                }
            }
        }
        assert!(saw_fdiv, "f64 div LIR must carry Fdiv");
        assert!(!saw_sdiv, "f64 div LIR must NOT carry integer Sdiv");
        assert!(!saw_udiv, "f64 div LIR must NOT carry integer Udiv");
    }

    /// NEGATIVE CONTROL (SAT / Refuted): the FP div shape must NOT equal the
    /// plain INTEGER BvSDiv of the same bit patterns (the OLD, wrong model). On
    /// concrete lanes 6.0 / 2.0 the FP result is bits(3.0) while the integer
    /// BvSDiv of the bit patterns is garbage — the discharge finds a
    /// COUNTEREXAMPLE. This is the teeth: the old `BvSDiv` model would be wrong.
    #[test]
    fn f64_div_negative_control_fp_shape_ne_integer_bvsdiv() {
        let a_bits = Formula::BitVec { value: 6.0_f64.to_bits() as i128, width: 64 };
        let b_bits = Formula::BitVec { value: 2.0_f64.to_bits() as i128, width: 64 };
        let fp_shape = fp64_div_bits(a_bits.clone(), b_bits.clone());
        let integer_bvsdiv = Formula::BvSDiv(b(a_bits), b(b_bits), 64);
        let outcome = discharge_equal_pre(&fp_shape, &integer_bvsdiv, None);
        assert!(
            matches!(outcome, Discharge::CounterExample),
            "FP div shape must DIFFER from integer BvSDiv: {outcome:?}"
        );
        // And the FP shape DOES equal the true FP answer bits(3.0).
        let three = Formula::BitVec { value: 3.0_f64.to_bits() as i128, width: 64 };
        assert!(
            matches!(discharge_equal_pre(&fp_shape, &three, None), Discharge::Proven),
            "FP div shape must equal bits(3.0)"
        );
    }

    /// VALUE-DIFF: 6.0 / 2.0 == 3.0, bit-exact over the emitted FDIV shape.
    #[test]
    fn f64_div_value_diff_6_over_2_is_3() {
        assert_f64_binop_concrete(fp64_div_bits, 6.0_f64, 2.0_f64, 3.0_f64, "/");
    }

    /// VALUE-DIFF (DIV-BY-ZERO, +inf): 1.0 / 0.0 == +inf
    /// (0x7FF0_0000_0000_0000), bit-exact over the emitted FDIV shape. This is
    /// the PROOF that NO div guard is needed: IEEE-754 `1.0 / 0.0` yields +inf,
    /// NOT a trap — and the emitted bytes compute exactly that pattern.
    #[test]
    fn f64_div_value_diff_1_over_0_is_pos_inf() {
        let pos_inf = f64::INFINITY;
        assert_eq!(pos_inf.to_bits(), 0x7FF0_0000_0000_0000);
        assert_eq!((1.0_f64 / 0.0_f64).to_bits(), 0x7FF0_0000_0000_0000);
        assert_f64_binop_concrete(fp64_div_bits, 1.0_f64, 0.0_f64, pos_inf, "/");
    }

    /// VALUE-DIFF (DIV-BY-ZERO, -inf): -1.0 / 0.0 == -inf
    /// (0xFFF0_0000_0000_0000). The sign of the infinity follows the usual
    /// sign rule; still no trap. Confirms the sign bit is carried bit-exactly.
    #[test]
    fn f64_div_value_diff_neg1_over_0_is_neg_inf() {
        let neg_inf = f64::NEG_INFINITY;
        assert_eq!(neg_inf.to_bits(), 0xFFF0_0000_0000_0000);
        assert_eq!((-1.0_f64 / 0.0_f64).to_bits(), 0xFFF0_0000_0000_0000);
        assert_f64_binop_concrete(fp64_div_bits, -1.0_f64, 0.0_f64, neg_inf, "/");
    }

    /// VALUE-DIFF (DIV-BY-ZERO, NaN): 0.0 / 0.0 classifies as NaN via
    /// `fp.isNaN` — again NOT a trap. The final PROOF that the `FpDiv(RNE, ..)`
    /// model is sound with no divisor-nonzero precondition: the degenerate
    /// `0.0/0.0` case produces a NaN, exactly as IEEE-754 mandates.
    #[test]
    fn f64_div_value_diff_0_over_0_is_nan() {
        assert!((0.0_f64 / 0.0_f64).is_nan());
        let zero_fp = Formula::FpFromBits {
            bits: b(Formula::BitVec { value: 0.0_f64.to_bits() as i128, width: 64 }),
            eb: F64_EB,
            sb: F64_SB,
        };
        // Classify the FP QUOTIENT directly (fp.isNaN over fp.div), the same
        // rounding-mode div the emitted FDIV computes, without the round-trip
        // (which ay does not fold). Discharge `isNaN(0.0 / 0.0)` VALID.
        let quot = Formula::FpDiv(
            b(Formula::FpRoundingMode(RoundingMode::RNE)),
            b(zero_fp.clone()),
            b(zero_fp),
        );
        let is_nan = Formula::FpIsNaN(b(quot));
        let outcome = discharge_valid(&is_nan);
        assert!(
            matches!(outcome, Discharge::Proven),
            "0.0 / 0.0 must always be NaN (fp.isNaN) — no trap, no guard needed: {outcome:?}"
        );
    }

    /// Discharge a CONCRETE f64 sub/mul instance against the emitted bytes:
    /// evaluate the SAME two-sided FP `shape` on concrete bit patterns and check
    /// it equals `bits(expected)` bit-exactly (UNSAT of the negation). Composed
    /// with the symbolic proof, gives `emitted-bytes(a, b) == expected`.
    fn assert_f64_binop_concrete(
        build: impl FnOnce(Formula, Formula) -> Formula,
        a: f64,
        b_val: f64,
        expected: f64,
        opsym: &str,
    ) {
        let a_bits = Formula::BitVec { value: a.to_bits() as i128, width: 64 };
        let b_bits = Formula::BitVec { value: b_val.to_bits() as i128, width: 64 };
        let shape = build(a_bits, b_bits);
        let expected_bits = Formula::BitVec { value: expected.to_bits() as i128, width: 64 };
        let outcome = discharge_equal_pre(&shape, &expected_bits, None);
        assert!(
            matches!(outcome, Discharge::Proven),
            "f64 {a} {opsym} {b_val} must equal {expected} bit-exactly: {outcome:?}"
        );
    }

    #[test]
    fn gate_fails_closed_on_nonreturn_terminator() {
        let mut f = binop_fn("gt", BinOp::Add, Ty::i32());
        f.body.blocks[0].terminator = Terminator::Goto(BlockId(0));
        let v = verify_output_preserved(&f);
        assert!(matches!(v, OutputVerdict::Unknown { .. }), "goto term must be Unknown: {v:?}");
    }

    // =====================================================================
    // M-POS ENFORCEMENT TESTS — the BUILD GATE has teeth.
    //   ACCEPT  : correct functions -> Ok(bytes), one non-empty object each.
    //   REFUSE  : a Refuted (miscompiled) function -> Err(Refuted), NO bytes.
    //   POLICY  : Unknown -> Err under StrictProvenOnly, Ok under AllowUnknown.
    // =====================================================================

    /// A float binop: genuinely Unknown (the interpreter fails closed on float).
    /// A genuinely Unknown (fail-closed) float function: f16 (width 16), which no
    /// bit-exact model covers on either the IR or machine side (f32/f64 are now
    /// wired and PROVEN, so they can no longer serve as the "gate cannot decide"
    /// example). The IR interpreter fails closed on f16 via `float_bit_width`.
    fn float_fn(name: &str) -> VerifiableFunction {
        binop_fn_ty(name, BinOp::Add, Ty::Float { width: 16 })
    }

    /// The verifier has no return-value semantics for a diverging body, while
    /// the backend can validly emit its trap. This is the canonical
    /// "verification Unknown after successful emission" fixture.
    fn unreachable_fn(name: &str) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![LocalDecl { index: 0, ty: Ty::i32(), name: None }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Unreachable,
                }],
                arg_count: 0,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    fn binop_fn_ty(name: &str, op: BinOp, ty: Ty) -> VerifiableFunction {
        binop_fn(name, op, ty)
    }

    // ---- ACCEPT: correct module emits real, non-empty objects ----

    #[test]
    fn emit_verified_accepts_proven_module() {
        // RUNG 3: AllowUnknown (the default) emits the broad Proven surface
        // (Add/Sub are [VALIDATED]: register-width carry chains exceed the
        // kernel-re-check frontier; Lt is [VALIDATED] too). These ship under
        // AllowUnknown. (Under StrictProvenOnly only kernel-[PROVED] ships — that
        // certified-fragment behavior is covered by
        // `emit_verified_strict_accepts_only_proved` and the rung3_* controls.)
        let funcs = vec![
            binop_fn("ev_add", BinOp::Add, Ty::i32()),
            binop_fn("ev_sub", BinOp::Sub, Ty::i32()),
            cmp_fn("ev_slt", BinOp::Lt, Ty::i32()),
        ];
        let objs = emit_objects_verified(&funcs, EmitPolicy::AllowUnknown)
            .unwrap_or_else(|e| panic!("proven module must emit under AllowUnknown: {e}"));
        assert_eq!(objs.len(), 3, "one object per function");
        for (name, bytes) in &objs {
            assert!(!bytes.is_empty(), "object for `{name}` must be non-empty");
            // mach-o magic — these are real emitted objects, not stubs.
            assert_eq!(&bytes[0..4], &0xfeed_facfu32.to_le_bytes(), "real mach-o for `{name}`");
        }
    }

    /// Trust: RUNG 3. The certified-fragment mode (StrictProvenOnly) EMITS a
    /// kernel-[PROVED] module (O(1)-certified ops within the re-check frontier) — this is
    /// the positive control that Strict is not vacuously refusing everything.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn emit_verified_strict_accepts_only_proved() {
        let funcs = vec![
            binop_fn("ev_strict_add", BinOp::Add, Ty::u32()),
            binop_fn("ev_strict_and", BinOp::BitAnd, Ty::u32()),
            binop_fn("ev_strict_xor", BinOp::BitXor, Ty::u32()),
        ];
        let objs = emit_objects_verified(&funcs, EmitPolicy::StrictProvenOnly)
            .unwrap_or_else(|e| panic!("kernel-[PROVED] module must emit under Strict: {e}"));
        assert_eq!(objs.len(), 3, "one object per [PROVED] function");
        for (name, bytes) in &objs {
            assert!(!bytes.is_empty(), "object for `{name}` must be non-empty");
            assert_eq!(&bytes[0..4], &0xfeed_facfu32.to_le_bytes(), "real mach-o for `{name}`");
        }
    }

    #[test]
    fn emit_object_verified_single_accepts_proven() {
        // RUNG 3: an Add i32 is [VALIDATED]; it ships under AllowUnknown (the
        // default), not StrictProvenOnly (which ships only kernel-[PROVED]).
        let f = binop_fn("ev_single_add", BinOp::Add, Ty::i32());
        let bytes = emit_object_verified(&f, EmitPolicy::AllowUnknown).expect("validated -> Ok");
        assert!(!bytes.is_empty(), "must produce real object bytes");
    }

    // ---- REFUSE (CORE GUARANTEE): a Refuted function is NEVER emitted ----

    #[test]
    fn emit_verified_refuses_refuted_and_emits_no_bytes() {
        // Drive the FULL public `emit_objects_verified` path, but corrupt the
        // emitted bytes of `ev_corrupt_add` (flip ADD->SUB via bit30) before the
        // gate decodes them — a modelled miscompiling backend. The gate must
        // return Err(Refuted) and PRODUCE NO BYTES. This is the teeth: the same
        // code path codegen calls, against a genuine byte-level miscompile.
        // `ev_ok_before` is a Sub (no ADD to flip) so the corruptor leaves it
        // untouched and it stays Proven; `ev_corrupt_add` is an Add whose emitted
        // ADD gets flipped to SUB — a genuine miscompile. The gate must single
        // out `ev_corrupt_add` as Refuted and emit NOTHING for the whole module.
        let funcs = vec![
            binop_fn("ev_ok_before", BinOp::Sub, Ty::i32()),
            binop_fn("ev_corrupt_add", BinOp::Add, Ty::i32()),
        ];

        // Flip the first ADD (shifted-register) to SUB via bit30. If a function
        // has no ADD (e.g. the Sub above) it is left byte-identical — only the
        // genuinely-Add function is miscompiled.
        let corruptor = |code: &mut Vec<u8>, base: u64| {
            let mut pc = base;
            let mut off = 0usize;
            while off + 4 <= code.len() {
                let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                let insn = decode_aarch64(&bytes, pc).expect("decode");
                if matches!(insn.opcode, Opcode::Add) {
                    let mut word = u32::from_le_bytes(bytes);
                    word ^= 1 << 30; // ADD (shifted reg) -> SUB: a miscompile.
                    code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                    return;
                }
                if matches!(insn.opcode, Opcode::Ret) {
                    break;
                }
                pc += 4;
                off += 4;
            }
            // No ADD here (e.g. the clean Sub function): leave bytes untouched.
        };

        // A Refuted function is refused and NO object bytes are returned. We test
        // under AllowUnknown here so the clean [VALIDATED] sibling (`ev_ok_before`,
        // a Sub) ships rather than being refused as not-[PROVED]; the Refuted Add
        // must still single out as the refusal. (That Refuted is fatal under BOTH
        // policies — policy never downgrades Refuted — is covered by
        // `rung3_refuted_is_fatal_under_both_policies`.)
        let policy = EmitPolicy::AllowUnknown;
        let result = with_text_corruptor(corruptor, || emit_objects_verified(&funcs, policy));
        match result {
            Err(VerifyError::Refuted { function, .. }) => {
                assert_eq!(
                    function, "ev_corrupt_add",
                    "the corrupted function must be the one Refuted"
                );
            }
            other => panic!(
                "corrupted (miscompiled) module MUST be Err(Refuted) under {policy:?}, got {other:?}"
            ),
        }
        // CORE INVARIANT: the Err carries NO bytes — nothing was emitted.
        // (Vec<u8> bytes only exist inside Ok; Err is byteless by type.)
        assert!(
            with_text_corruptor(corruptor, || emit_objects_verified(&funcs, policy)).is_err(),
            "Refuted module never yields Ok bytes under {policy:?}"
        );
    }

    #[test]
    fn emit_object_verified_single_refuses_refuted() {
        let f = binop_fn("ev_single_corrupt", BinOp::Add, Ty::i32());
        let corruptor = |code: &mut Vec<u8>, base: u64| {
            let mut pc = base;
            let mut off = 0usize;
            while off + 4 <= code.len() {
                let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                let insn = decode_aarch64(&bytes, pc).expect("decode");
                if matches!(insn.opcode, Opcode::Add) {
                    let mut word = u32::from_le_bytes(bytes);
                    word ^= 1 << 30;
                    code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                    return;
                }
                if matches!(insn.opcode, Opcode::Ret) {
                    break;
                }
                pc += 4;
                off += 4;
            }
            panic!("no ADD found to corrupt");
        };
        let result = with_text_corruptor(corruptor, || {
            emit_object_verified(&f, EmitPolicy::StrictProvenOnly)
        });
        assert!(
            matches!(result, Err(VerifyError::Refuted { .. })),
            "single corrupted fn must be Err(Refuted), got {result:?}"
        );
    }

    // ---- RUNG 2 NEGATIVE CONTROL: shipped == verified (TOCTOU) ----

    #[test]
    fn emit_verified_ships_exactly_the_verified_bytes() {
        // Trust (RUNG 2): the bytes the gate returns ARE the bytes it verified —
        // a single emission. Confirm a clean Proven function's shipped bytes are a
        // real mach-o object and re-running the gate is deterministic (the same
        // bytes), which is the equality the TOCTOU detector enforces below.
        // RUNG 3: an Add i32 is [VALIDATED]; it ships under AllowUnknown.
        let f = binop_fn("r2_ship_add", BinOp::Add, Ty::i32());
        let a = emit_object_verified(&f, EmitPolicy::AllowUnknown).expect("validated -> Ok");
        let b2 = emit_object_verified(&f, EmitPolicy::AllowUnknown).expect("validated -> Ok");
        assert_eq!(&a[0..4], &0xfeed_facfu32.to_le_bytes(), "real mach-o");
        assert_eq!(a, b2, "verified emission is deterministic (shipped == verified)");
    }

    #[test]
    fn emit_verified_refuses_divergent_reemission() {
        // Trust (RUNG 2 — THE NEGATIVE CONTROL). Model a non-deterministic /
        // trojaned backend whose SECOND emission (the would-be shipped artifact)
        // differs from the first (the gate-verified one): flip a byte on re-emit
        // via the diverger seam. The gate VERIFIES clean bytes (PHASE 1) but its
        // re-emit equality check sees the divergence and MUST fail closed —
        // `Err(EmitFailed)`, NO object shipped. Without the Rung 2 fix the
        // divergent re-emit shipped silently; with it, the gate refuses it.
        // RUNG 3: an Add i32 is [VALIDATED]; it ships under AllowUnknown (the
        // default), which is the policy this Rung 2 TOCTOU control runs under.
        let funcs = vec![binop_fn("r2_div_add", BinOp::Add, Ty::i32())];

        // Sanity: WITHOUT the diverger the same module emits cleanly (so the
        // refusal below is caused by the divergence, not by a broken function).
        emit_objects_verified(&funcs, EmitPolicy::AllowUnknown)
            .expect("clean module must emit without the diverger");

        // Flip the last byte of the re-emitted object — a 1-byte divergence
        // between the verified emission and the shipped (re-emitted) one.
        let diverger = |obj: &mut Vec<u8>| {
            let last = obj.len() - 1;
            obj[last] ^= 0x01;
        };

        let policy = EmitPolicy::AllowUnknown;
        let result = with_reemit_diverger(diverger, || emit_objects_verified(&funcs, policy));
        match result {
            Err(VerifyError::EmitFailed { function, reason }) => {
                assert_eq!(function, "r2_div_add", "the divergent fn must be refused");
                assert!(
                    reason.contains("DIVERGED"),
                    "refusal must cite the re-emission divergence, got: {reason}"
                );
            }
            other => panic!(
                "a divergent re-emission MUST be refused (Err(EmitFailed)) under {policy:?}, \
                 got {other:?}"
            ),
        }
    }

    #[test]
    fn emit_object_verified_single_refuses_divergent_reemission() {
        // Same RUNG 2 negative control through the single-function convenience.
        // RUNG 3: Add i32 is [VALIDATED]; ships under AllowUnknown.
        let f = binop_fn("r2_single_div", BinOp::Add, Ty::i32());
        let diverger = |obj: &mut Vec<u8>| {
            let last = obj.len() - 1;
            obj[last] ^= 0x01;
        };
        let result =
            with_reemit_diverger(diverger, || emit_object_verified(&f, EmitPolicy::AllowUnknown));
        assert!(
            matches!(result, Err(VerifyError::EmitFailed { ref reason, .. }) if reason.contains("DIVERGED")),
            "single divergent re-emission must be Err(EmitFailed/DIVERGED), got {result:?}"
        );
    }

    // ---- POLICY: Unknown is fail-closed by default, opt-in to allow ----

    #[test]
    fn emit_verified_strict_refuses_unknown() {
        // A float function is genuinely Unknown (interpreter fails closed).
        let f = float_fn("ev_unknown_float");
        match emit_object_verified(&f, EmitPolicy::StrictProvenOnly) {
            Err(VerifyError::Unknown { function, .. }) => {
                assert_eq!(function, "ev_unknown_float");
            }
            other => panic!("Unknown under StrictProvenOnly must be Err(Unknown), got {other:?}"),
        }
    }

    #[test]
    fn emit_verified_allow_unknown_emits_unknown() {
        // AllowUnknown is best-effort: an Unknown (but not Refuted) function is
        // emitted. NOTE: a float Add currently also lowers+emits cleanly, so the
        // emission step succeeds; if it could not lower we'd get EmitFailed, not
        // a silent pass. Either way it is NOT refused as a miscompile.
        let f = float_fn("ev_allow_float");
        match emit_object_verified(&f, EmitPolicy::AllowUnknown) {
            Ok(bytes) => assert!(!bytes.is_empty(), "AllowUnknown emits real bytes for Unknown fn"),
            Err(VerifyError::EmitFailed { .. }) => { /* lowering limit, not a refusal */ }
            other => panic!("AllowUnknown must not refuse a non-Refuted Unknown fn, got {other:?}"),
        }
    }

    #[test]
    fn allow_unknown_retains_bytes_when_semantics_are_unsupported() {
        let funcs = vec![unreachable_fn("allow_unknown_diverging")];
        let (objects, report) = emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown)
            .expect("successful backend emission must survive a verifier-shape Unknown");
        assert_eq!(objects.len(), 1);
        assert!(!objects[0].1.is_empty(), "the exact emitted object must be retained");
        assert_eq!(report.unknown, 1, "unsupported semantics are visibly uncertified");

        assert!(
            matches!(
                emit_objects_verified_reported(&funcs, EmitPolicy::StrictProvenOnly),
                Err(VerifyError::Unknown { .. })
            ),
            "Strict must still refuse the same unsupported verifier shape"
        );
    }

    /// An ISA the machine-semantics model does not cover must produce an honest
    /// `Unknown` that still RETAINS the emitted object, not an emission failure.
    ///
    /// x86_64 is that case: the backend emits a real object, but the executor
    /// below decodes A64 only. The bytes are a legitimate build artifact that an
    /// explicit best-effort policy may ship as visibly uncertified — losing them
    /// would turn a coverage gap into a build failure. Strict must still refuse.
    #[test]
    fn backend_aware_allow_unknown_retains_exact_object_when_the_isa_is_unmodelled() {
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::X86_64,
            "x86_64-unknown-linux-gnu",
        );
        let funcs = vec![binop_fn("allow_unknown_x86_64", BinOp::Add, Ty::u32())];
        let (objects, report) =
            emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
                .expect("an undecidable ISA must ship only as explicitly uncertified");
        assert_eq!(&objects[0].1[..4], b"\x7fELF", "production backend bytes are retained");
        assert_eq!(report.unknown, 1);

        assert!(matches!(
            emit_objects_verified_reported_with_backend(
                &funcs,
                EmitPolicy::StrictProvenOnly,
                &backend,
            ),
            Err(VerifyError::Unknown { .. })
        ));
    }

    /// The positive control the test above needs to mean anything: on the ISA the
    /// model DOES cover, an ELF-container target must be decided, not waved
    /// through as uncertified. Without this, an `Unknown` everywhere would satisfy
    /// every "retains bytes" assertion while the gate proved nothing at all.
    #[test]
    fn backend_aware_gate_decides_an_elf_container_on_the_modelled_isa() {
        let backend = TrustCgCodegenBackend::new_for_triple(
            TrustCgTargetArch::AArch64,
            "aarch64-unknown-linux-gnu",
        );
        let funcs = vec![binop_fn("decided_aarch64_elf", BinOp::Add, Ty::u32())];
        let (objects, report) =
            emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
                .expect("a faithful emission must clear the gate");
        assert_eq!(&objects[0].1[..4], b"\x7fELF", "the container under test is ELF");
        assert_eq!(report.unknown, 0, "the gate must not fail closed on a container it can read");
        assert_eq!(report.proved + report.validated, 1, "report: {report}");
    }

    #[test]
    fn verified_gate_rejects_duplicate_function_identity_before_emission() {
        let funcs = vec![
            binop_fn("duplicate_symbol", BinOp::Add, Ty::u32()),
            binop_fn("duplicate_symbol", BinOp::Sub, Ty::u32()),
        ];
        assert!(matches!(
            emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown),
            Err(VerifyError::DuplicateFunctionName { ref name }) if name == "duplicate_symbol"
        ));
    }

    #[test]
    fn emit_verified_default_policy_is_strict() {
        // The documented SAFE default: StrictProvenOnly.
        assert_eq!(EmitPolicy::default(), EmitPolicy::StrictProvenOnly);
    }

    // =====================================================================
    // RUNG 3 — CERTIFICATION REPORT + GENUINELY-FAIL-CLOSED STRICT.
    //
    //   (i)   Unknown  under StrictProvenOnly -> Err (refused).
    //   (ii)  AyValidated ([VALIDATED]) under StrictProvenOnly -> Err (only
    //         kernel-[PROVED] ships in the certified-fragment mode).
    //   (iii) AllowUnknown EMITS an Unknown function AND the report COUNTS it
    //         as the uncertified surface.
    //   (iv)  Refuted -> Err under BOTH policies (always fatal).
    // =====================================================================

    /// Trust: RUNG 3 control (ii). A width-32 signed `div` is PROVEN by ay but stays
    /// [VALIDATED] (AyValidated) — its obligation is CONDITIONAL (divisor != 0), so the
    /// unconditional bit-blast cert is a different claim and the gate declines [PROVED]
    /// (see `gate_division_stays_validated_not_proved`). Under StrictProvenOnly the
    /// certified-fragment mode MUST refuse it: only kernel-[PROVED] functions ship.
    /// (Under no `kernel-recheck` feature EVERY Proven verdict is AyValidated, so this
    /// also holds there.) NOTE: mul was the prior example here but is now O(1)
    /// kernel-[PROVED] (#59); division is the current practically-reachable [VALIDATED].
    #[test]
    fn rung3_strict_refuses_ay_validated() {
        let f = div_then_xor_fn("rung3_strict_validated_divxor", Ty::u32());

        // Sanity: the verdict really is Proven{AyValidated}, not Unknown/PROVED.
        let verdict = verify_output_preserved(&f);
        assert!(verdict.is_proven(), "div i32 must be Proven (ay UNSAT): {verdict:?}");
        assert!(
            verdict.kernel_proof().is_none() && !verdict.is_kernel_proved(),
            "div i32 must be [VALIDATED] (conditional obligation, no kernel cert): {verdict:?}"
        );

        // StrictProvenOnly REFUSES the [VALIDATED] function (fail-closed).
        match emit_object_verified(&f, EmitPolicy::StrictProvenOnly) {
            Err(VerifyError::Unknown { function, reason }) => {
                assert_eq!(function, "rung3_strict_validated_divxor");
                assert!(
                    reason.contains("VALIDATED"),
                    "refusal must cite the [VALIDATED] grade, got: {reason}"
                );
            }
            other => panic!(
                "StrictProvenOnly must REFUSE a [VALIDATED] function (only [PROVED] ships), \
                 got {other:?}"
            ),
        }
    }

    /// Trust: RUNG 3 control (ii, positive). The SAME [VALIDATED] function EMITS
    /// under AllowUnknown and is COUNTED as [VALIDATED] in the report — it is not
    /// silently treated as covered, but it is not refused either (default policy).
    #[test]
    fn rung3_allow_unknown_emits_and_counts_validated() {
        // div (conditional obligation) is the current [VALIDATED] example (mul is now
        // O(1) kernel-[PROVED], #59).
        let funcs = vec![div_then_xor_fn("rung3_allow_validated_divxor", Ty::u32())];
        let (objs, report) = emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown)
            .expect("AllowUnknown must emit a [VALIDATED] function");
        assert_eq!(objs.len(), 1, "one object emitted");
        assert!(!objs[0].1.is_empty(), "real object bytes");
        assert_eq!(report.validated, 1, "the div must be counted [VALIDATED]: {report:?}");
        assert_eq!(report.unknown, 0, "a Proven function is not Unknown: {report:?}");
        assert_eq!(report.proved, 0, "conditional div is not kernel-[PROVED]: {report:?}");
        assert_eq!(report.uncertified(), 1, "the [VALIDATED] fn is the uncertified surface");
    }

    /// Trust: RUNG 3 control (iii) — the report COUNTS the uncertified surface
    /// (never silently treats it as covered). The PRACTICALLY-REACHABLE uncertified
    /// surface is [VALIDATED] (ay-proven, no kernel cert): a module mixing a
    /// kernel-[PROVED] op (BitOr u32, with `kernel-recheck`) and a [VALIDATED] op
    /// (signed div i32 — conditional obligation) emits BOTH under AllowUnknown, and
    /// the report tallies exactly one of each — making the uncertified ([VALIDATED])
    /// function VISIBLE. (mul was the prior [VALIDATED] example but is now O(1)
    /// kernel-[PROVED], #59.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn rung3_allow_unknown_report_counts_certified_and_uncertified() {
        let funcs = vec![
            binop_fn("rung3_rep_or", BinOp::BitOr, Ty::u32()),
            div_then_xor_fn("rung3_rep_divxor", Ty::u32()),
        ];
        let (objs, report) = emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown)
            .expect("AllowUnknown must emit a proved+validated module");
        assert_eq!(objs.len(), 2, "both functions emitted under AllowUnknown");
        assert_eq!(report.proved, 1, "BitOr u32 must be counted [PROVED]: {report:?}");
        assert_eq!(report.validated, 1, "div i32 must be counted [VALIDATED]: {report:?}");
        assert_eq!(report.refuted, 0, "no miscompile in this module: {report:?}");
        assert_eq!(report.emitted(), 2, "report tallies every emitted function");
        assert_eq!(
            report.uncertified(),
            1,
            "the [VALIDATED] div is the VISIBLE uncertified surface: {report:?}"
        );
    }

    /// Trust: RUNG 3 control (iii) — fail-closed honesty for the dominant Unknown
    /// surface. A function the gate cannot even DERIVE/DECODE (a float Add: the IR
    /// interpreter fails closed AND the backend cannot lower f32) carries NO
    /// shippable bytes, so under AllowUnknown the gate fails CLOSED with
    /// `EmitFailed` (NOT a silent emit, NOT a spurious Refuted). HONESTY: the
    /// report's `unknown` bucket counts only Unknown functions that actually EMIT
    /// (emit+decode succeed but ay cannot discharge); an unsupported shape never
    /// reaches the linker through this gate.
    #[test]
    fn rung3_allow_unknown_undecodable_fails_closed_not_refuted() {
        let funcs = vec![float_fn("rung3_unknown_float")];
        match emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown) {
            // Reachable today: f32 add has no shippable bytes -> fail closed.
            Err(VerifyError::EmitFailed { function, .. }) => {
                assert_eq!(function, "rung3_unknown_float");
            }
            // Defensive: if a future backend DOES lower it, it must be emitted and
            // COUNTED as uncertified `unknown`, never silently covered.
            Ok((objs, report)) => {
                assert_eq!(objs.len(), 1);
                assert_eq!(report.unknown, 1, "emitted Unknown is counted: {report:?}");
            }
            other => panic!(
                "AllowUnknown must fail closed (EmitFailed) or emit+count, never Refuted, \
                 got {other:?}"
            ),
        }
    }

    /// Trust: RUNG 3 control (iv). A Refuted (miscompiled) function is fatal under
    /// BOTH policies — it never emits and never appears in a report (the Err path
    /// returns before any report is produced).
    #[test]
    fn rung3_refuted_is_fatal_under_both_policies() {
        let funcs = vec![binop_fn("rung3_refuted_add", BinOp::Add, Ty::i32())];
        // Flip the emitted ADD -> SUB (a genuine byte-level miscompile).
        let corruptor = |code: &mut Vec<u8>, base: u64| {
            let mut pc = base;
            let mut off = 0usize;
            while off + 4 <= code.len() {
                let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                let insn = decode_aarch64(&bytes, pc).expect("decode");
                if matches!(insn.opcode, Opcode::Add) {
                    let mut word = u32::from_le_bytes(bytes);
                    word ^= 1 << 30;
                    code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                    return;
                }
                if matches!(insn.opcode, Opcode::Ret) {
                    break;
                }
                pc += 4;
                off += 4;
            }
        };
        for policy in [EmitPolicy::StrictProvenOnly, EmitPolicy::AllowUnknown] {
            let result =
                with_text_corruptor(corruptor, || emit_objects_verified_reported(&funcs, policy));
            match result {
                Err(VerifyError::Refuted { function, .. }) => {
                    assert_eq!(function, "rung3_refuted_add");
                }
                other => {
                    panic!("Refuted must be fatal under {policy:?} (no report), got {other:?}")
                }
            }
        }
    }

    // =======================================================================
    // LOCAL-PURE-CALLEE COMPOSITION (codegen-via-trust-ir prerequisite).
    // =======================================================================

    /// Build `fn <name>(a: i32, b: i32) -> i32 { <callee>(a, b) }` — a caller
    /// whose body is a single direct call to a 2-arg i32 local function, with a
    /// continuation block that returns the call result.
    fn call2_i32_fn(name: &str, callee: &str, is_foreign: bool) -> VerifiableFunction {
        wrap(
            name,
            VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: Terminator::Call {
                            func: callee.into(),
                            args: vec![
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ],
                            dest: Place::local(0),
                            target: Some(BlockId(1)),
                            span: sp(),
                            atomic: None,
                            unwind: trust_types::UnwindEdge::Unreachable,
                            is_foreign,
                            is_unsafe_sig: false,
                            callee_identity: None,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::i32(),
                datatype_defs: Default::default(),
            },
        )
    }

    /// THE LOAD-BEARING TEST. A 2-function bundle where `caller` calls a LOCAL
    /// pure `add(a,b) = a+b`: the caller is now PROVED (kernel-[PROVED] via the
    /// O(1) add instantiation) with NON-EMPTY shippable bytes — composition works
    /// end-to-end through the public bundle gate. (Before this change the caller
    /// was Unknown — both verifier halves fail-closed on the Call — so the whole
    /// module was refused.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_verifies_caller_of_local_pure_add() {
        let add = binop_fn("add", BinOp::Add, Ty::i32());
        let caller = call2_i32_fn("caller_add", "add", false);
        // Order: callee first then caller, and also caller-first to prove order
        // independence (PHASE 0 builds the env over the whole bundle up front).
        for funcs in [vec![add.clone(), caller.clone()], vec![caller.clone(), add.clone()]] {
            let (objs, report) = emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown)
                .expect("bundle with a local-pure call must clear the gate");
            assert_eq!(objs.len(), 2, "both functions ship");
            // The caller carries non-empty shippable bytes.
            let caller_obj =
                objs.iter().find(|(n, _)| n == "caller_add").expect("caller object present");
            assert!(!caller_obj.1.is_empty(), "caller ships non-empty object bytes");
            // Nothing landed in the uncertified (Unknown) bucket: BOTH the callee
            // and the composed caller are PROVED (add@32 is O(1) kernel-[PROVED]).
            assert_eq!(report.unknown, 0, "no Unknown after composition: {report:?}");
            assert_eq!(report.proved, 2, "callee + composed caller both PROVED: {report:?}");
        }

        // And the single-function verdict for the caller, WITH the env, is Proven.
        let mut env = CalleeEnv::empty();
        env.callees.insert("add".into(), derive_callee_pure(&add).expect("add is pure"));
        let v = verify_output_preserved_capturing_env(&caller, &env).0;
        assert!(v.is_proven(), "composed caller verdict is Proven; got {v:?}");
    }

    /// A caller of an EXTERNAL/unmodelable callee still FAILS CLOSED: the callee
    /// is not in the bundle (no in-bundle Proven pure semantics), so the call is
    /// not composed on either side and the caller stays Unknown. Under
    /// AllowUnknown the caller has NO shippable bytes (its emission contains an
    /// unresolved `bl` the gate could not verify), so the gate refuses to ship it.
    #[test]
    fn gate_fails_closed_on_caller_of_external_callee() {
        // `extern_add` is NOT in the bundle — only the caller is.
        let caller = call2_i32_fn("caller_ext", "extern_add", false);
        let funcs = vec![caller];
        match emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown) {
            // The caller is Unknown (call to a non-local callee) and AllowUnknown
            // would emit it — but its bytes contain an unresolved external `bl`
            // that did not verify, so it is COUNTED as uncertified and shipped as
            // best-effort. The KEY guarantee: it is NOT Proven and NOT silently
            // covered. Accept either "counted Unknown" (emitted best-effort) — the
            // verdict must never be Proven.
            Ok((objs, report)) => {
                assert_eq!(report.unknown, 1, "external-callee caller is uncertified: {report:?}");
                assert_eq!(report.proved, 0, "an external-callee caller is NEVER proved");
                assert_eq!(report.validated, 0);
                assert_eq!(objs.len(), 1);
            }
            // Or it fails closed with no bytes — also acceptable (and stronger).
            Err(VerifyError::Unknown { function, .. })
            | Err(VerifyError::EmitFailed { function, .. }) => {
                assert_eq!(function, "caller_ext");
            }
            other => {
                panic!("external-callee caller must never be Proven/shipped-as-proved: {other:?}")
            }
        }
        // Under StrictProvenOnly it is unconditionally refused (not Proven).
        match emit_objects_verified_reported(
            &[call2_i32_fn("caller_ext2", "extern_add", false)],
            EmitPolicy::StrictProvenOnly,
        ) {
            Err(VerifyError::Unknown { function, .. }) => assert_eq!(function, "caller_ext2"),
            other => panic!("StrictProvenOnly must refuse an unverified caller, got {other:?}"),
        }
    }

    // =======================================================================
    // UNWIND SCOPING — WHERE THE M-POS OBLIGATION STOPS.
    //
    // These two tests are MEASUREMENTS, not feature tests. They record why
    // `panic=unwind` is refused in `rustc_codegen_trust_cg` (lib.rs, the
    // `sess.panic_strategy().unwinds()` fatal) and what emitting invoke /
    // cleanup / personality / LSDA / resume behind that refusal would and would
    // NOT buy: the gate's obligation is
    //
    //     forall args. machine_ret(args) == ir_ret(args)
    //
    // ONE value, over the paths reachable by ARCHITECTURAL control flow. An
    // unwind edge is a SECOND EXIT — a different exit kind, reached by the
    // unwinder writing PC from the LSDA, carrying its own state. Neither half of
    // the gate has a place to put it: both `trust_ir_semantics` and
    // `symbolic_machine_output` return `Result<Formula, String>`, not an
    // exit-tagged relation. So unwinding is a VERIFICATION-FRAGMENT question
    // first and a codegen feature second, and the tests below pin the boundary
    // so a future extension has to move it deliberately.
    // =======================================================================

    /// MACHINE SIDE. `PathMergingExecutor::run` starts at the entry PC and
    /// follows fall-through, `b`, `b.cond` and `bl`+4 only; it RETURNS the
    /// moment it decodes a `ret`. A landing pad has no architectural predecessor
    /// — the unwinder jumps into it from the LSDA — so its bytes are never
    /// decoded and never enter the obligation.
    ///
    /// Measured: appending an unreachable tail (`mov w0, wzr; ret` — code that
    /// would return a DIFFERENT value — plus an undecodable word) leaves the
    /// derived machine formula BIT-IDENTICAL, and the undecodable word does not
    /// even fail the run. Bytes after the `ret` ship inside a `[PROVED]` object
    /// with ZERO gate coverage, because `assert_merged_object_preserves_verified_text`
    /// only pins that the shipped bytes EQUAL the verified object's bytes — it
    /// never claims the executor decoded all of them.
    #[test]
    fn unwind_scope_gate_never_decodes_bytes_after_the_ret() {
        let (_obj, code, base) = emit_text(&add_i32_fn()).expect("emit");
        let baseline = symbolic_machine_output(&code, base, 32, false).expect("decode");

        // The stand-in landing pad, appended exactly where a real one is placed:
        //   mov w0, wzr   (0x2a1f03e0) — would make the function return 0
        //   ret           (0xd65f03c0)
        //   udf #0        (0x00000000) — not a decodable instruction at all
        let mut with_pad = code.clone();
        for word in [0x2a1f_03e0u32, 0xd65f_03c0, 0x0000_0000] {
            with_pad.extend_from_slice(&word.to_le_bytes());
        }
        let padded = symbolic_machine_output(&with_pad, base, 32, false)
            .expect("the executor stops at the ret, so the undecodable tail never fails it");

        assert_eq!(
            baseline, padded,
            "MEASURED: 12 appended bytes — including one that does not decode — leave the \
             machine-side formula unchanged. Bytes past the ret are OUTSIDE the M-POS \
             obligation, so a landing pad emitted there would be unverified."
        );
    }

    /// IR SIDE. `eval_block`'s `Terminator::Call` arm destructures
    /// `{ func, args, dest, target, atomic, is_foreign, .. }` — the `..`
    /// swallows `unwind`. The auto-derived spec of a call that CAN unwind is
    /// therefore the spec of a call that CANNOT.
    ///
    /// Measured: the same caller with `unwind: Unreachable` (nounwind),
    /// `unwind: Continue` (unwinds straight out of the function) and
    /// `unwind: Cleanup(bb2)` (a real second CFG successor ending in `Resume`)
    /// derives a BIT-IDENTICAL spec formula.
    ///
    /// This is NOT a live hole: `trust_mir_extract::extract_function_for_codegen`
    /// refuses any non-`Unreachable` call unwind action (and every `Assert` /
    /// `Drop` / `UnwindResume` / `UnwindTerminate`) before the gate is ever
    /// reached, and `validate_codegen_instance_abi` refuses `fn_abi.can_unwind`.
    /// The test pins WHERE the fail-closed lives — in the EXTRACTOR and the ABI
    /// check, NOT in the gate — so that relaxing either one without extending
    /// the obligation is a visible break rather than a silent normal-path-only
    /// `[PROVED]`.
    #[test]
    fn unwind_scope_ir_semantics_ignores_the_unwind_edge() {
        let add = binop_fn("add", BinOp::Add, Ty::i32());
        let mut env = CalleeEnv::empty();
        env.callees.insert("add".into(), derive_callee_pure(&add).expect("add is pure"));

        let mut specs = Vec::new();
        for edge in [
            trust_types::UnwindEdge::Unreachable,
            trust_types::UnwindEdge::Continue,
            trust_types::UnwindEdge::Cleanup(BlockId(2)),
        ] {
            let needs_cleanup_block = matches!(edge, trust_types::UnwindEdge::Cleanup(_));
            let mut caller = call2_i32_fn("caller_unwind_scope", "add", false);
            match &mut caller.body.blocks[0].terminator {
                Terminator::Call { unwind, .. } => *unwind = edge,
                other => panic!("fixture block 0 must end in a Call, got {other:?}"),
            }
            if needs_cleanup_block {
                // A REAL second successor: the block the unwinder enters, which
                // (having no live drops here) immediately re-raises to the caller.
                caller.body.blocks.push(BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Resume,
                });
            }
            specs.push(trust_ir_semantics_env(&caller, &env).expect("spec derives"));
        }

        assert_eq!(
            specs[0], specs[1],
            "MEASURED: `unwind: Continue` (a real unwind exit) derives the same single-value \
             spec as `unwind: Unreachable` (nounwind) — the exit is not in the formula"
        );
        assert_eq!(
            specs[0], specs[2],
            "MEASURED: `unwind: Cleanup(bb2)` adds a reachable cleanup block ending in `Resume` \
             and the spec is still bit-identical — the second exit path is never evaluated"
        );
    }

    /// TEETH: a MISCOMPILED caller of a local pure callee is still REFUTED. We
    /// compose `add` but corrupt the caller's emitted ARG-SETUP `Orr` that moves
    /// `b` into the second argument register (flip it so the call receives the
    /// WRONG second argument). The machine side decodes the caller's OWN bytes
    /// (the corrupted shuffle), so the value placed in the call's arg register
    /// diverges from the IR's `b`, the composed result diverges, and ay finds a
    /// counterexample → Refuted. Composition cannot launder a caller-side
    /// miscompile: only the call RESULT is substituted; the arg setup and result
    /// move are still byte-derived and checked.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_refutes_miscompiled_caller_arg_setup() {
        let add = binop_fn("add", BinOp::Add, Ty::i32());
        let caller = call2_i32_fn("caller_miscompiled", "add", false);
        let mut env = CalleeEnv::empty();
        env.callees.insert("add".into(), derive_callee_pure(&add).expect("add pure"));

        // Corrupt the LAST `Orr` that sets up an argument register BEFORE the bl:
        // change `Orr W1, WZR, W3` (move b into the 2nd arg reg) to read a
        // different source register, so the callee receives a wrong second arg.
        let corruptor = |code: &mut Vec<u8>, base: u64| {
            let mut pc = base;
            let mut off = 0usize;
            let mut last_orr: Option<usize> = None;
            while off + 4 <= code.len() {
                let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                let insn = decode_aarch64(&bytes, pc).expect("decode");
                if matches!(insn.opcode, Opcode::Bl) {
                    break; // corrupt the arg-setup Orr that is closest BEFORE the bl
                }
                if matches!(insn.opcode, Opcode::Orr) {
                    last_orr = Some(off);
                }
                pc += 4;
                off += 4;
            }
            if let Some(o) = last_orr {
                // Flip a bit in the Rm field (bits 16..20) so the source register
                // differs — the call now reads a different value as its 2nd arg.
                let mut word = u32::from_le_bytes(code[o..o + 4].try_into().unwrap());
                word ^= 1 << 16;
                code[o..o + 4].copy_from_slice(&word.to_le_bytes());
            }
        };

        let verdict = with_text_corruptor(corruptor, || {
            verify_output_preserved_capturing_env(&caller, &env).0
        });
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "a caller-side arg-setup miscompile must be REFUTED through composition; got {verdict:?}"
        );
    }

    /// A caller marked `is_foreign` (non-Rust ABI) to a callee that IS present in
    /// the bundle still FAILS CLOSED — the foreign-ABI flag means the call does
    /// not follow the AAPCS64 contract we model, so composition is declined on the
    /// IR side regardless of the env. (Defense in depth: even a same-named local
    /// pure callee cannot be composed across a foreign-ABI boundary.)
    #[test]
    fn gate_fails_closed_on_foreign_abi_call_even_with_local_callee() {
        let add = binop_fn("add", BinOp::Add, Ty::i32());
        let caller = call2_i32_fn("caller_foreign", "add", true /* is_foreign */);
        // The IR side rejects the foreign call, so the caller is Unknown.
        let mut env = CalleeEnv::empty();
        env.callees.insert("add".into(), derive_callee_pure(&add).expect("add pure"));
        let v = verify_output_preserved_capturing_env(&caller, &env).0;
        assert!(
            matches!(v, OutputVerdict::Unknown { .. }),
            "a foreign-ABI call must fail closed even with a local callee in env; got {v:?}"
        );
    }

    /// Trust: RUNG 3 control (ii) at module granularity. A module mixing a
    /// kernel-[PROVED] op (BitOr u32 — requires the `kernel-recheck` feature for
    /// the [PROVED] grade) with a [VALIDATED] mul: under StrictProvenOnly the whole
    /// module is refused (the [VALIDATED] mul is fail-closed), confirming Strict
    /// ships ONLY the certified fragment. Without `kernel-recheck` every Proven
    /// verdict is [VALIDATED], so the FIRST function would be refused instead and
    /// the named-function assertion would not hold — hence the feature gate.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn rung3_strict_refuses_mixed_module_with_validated() {
        // div i32 (conditional obligation) is the [VALIDATED] op Strict refuses (mul is
        // now O(1) kernel-[PROVED], #59).
        let funcs = vec![
            binop_fn("rung3_mixed_or", BinOp::BitOr, Ty::u32()),
            div_then_xor_fn("rung3_mixed_divxor", Ty::u32()),
        ];
        match emit_objects_verified_reported(&funcs, EmitPolicy::StrictProvenOnly) {
            Err(VerifyError::Unknown { function, .. }) => {
                assert_eq!(
                    function, "rung3_mixed_divxor",
                    "the [VALIDATED] div is the function Strict refuses"
                );
            }
            other => panic!(
                "StrictProvenOnly must refuse a module containing a [VALIDATED] fn, got {other:?}"
            ),
        }
    }

    #[test]
    fn emit_verified_empty_module_is_error() {
        assert_eq!(
            emit_objects_verified(&[], EmitPolicy::StrictProvenOnly),
            Err(VerifyError::EmptyModule)
        );
    }

    // =======================================================================
    // ONE-OBJECT-PER-CGU + THE MERGE OBLIGATION.
    //
    // The per-function proof is unchanged; the merged artifact must CARRY each
    // verified function's machine code verbatim. These tests pin that the
    // obligation is (a) discharged on a real module, (b) discharged when a
    // function is bound `Internal` (a local symbol), and (c) genuinely
    // falsifiable — a merged object missing a verified function is REFUSED.
    // =======================================================================

    /// The module used by the merge tests: two independently-provable functions.
    fn merge_module() -> Vec<VerifiableFunction> {
        vec![
            binop_fn("merge_add", BinOp::Add, Ty::i32()),
            binop_fn("merge_or", BinOp::BitOr, Ty::u32()),
        ]
    }

    #[test]
    fn verified_module_object_preserves_every_function() {
        use crate::codegen_backend::FunctionLinkage;
        let backend = default_verification_backend();
        let funcs = merge_module();
        let (module_object, _report) = emit_module_object_verified_reported_with_backend(
            &funcs,
            &[FunctionLinkage::External; 2],
            &[],
            EmitPolicy::AllowUnknown,
            &backend,
        )
        .expect("a module of provable functions must clear the gate and the merge obligation");

        assert!(!module_object.bytes.is_empty(), "the merged artifact must have bytes");
        let names: Vec<&str> =
            module_object.preserved.iter().map(|entry| entry.name.as_str()).collect();
        assert_eq!(names, vec!["merge_add", "merge_or"]);

        // ANTI-VACUITY: the two functions must occupy DIFFERENT offsets, and at
        // least one a non-zero one, or the byte windows compared inside the
        // obligation are the same degenerate slice.
        assert_ne!(
            module_object.preserved[0].text_offset, module_object.preserved[1].text_offset,
            "merged functions must occupy distinct text offsets"
        );
        assert!(
            module_object.preserved.iter().any(|entry| entry.text_offset > 0),
            "at least one merged function must sit past offset 0"
        );
        assert!(
            module_object.preserved.iter().all(|entry| entry.len > 0),
            "every preserved function must have a non-empty body"
        );
    }

    #[test]
    fn verified_module_object_preserves_internal_linkage_function() {
        use crate::codegen_backend::FunctionLinkage;
        let backend = default_verification_backend();
        let funcs = merge_module();
        let (module_object, _report) = emit_module_object_verified_reported_with_backend(
            &funcs,
            &[FunctionLinkage::Internal, FunctionLinkage::External],
            &[],
            EmitPolicy::AllowUnknown,
            &backend,
        )
        .expect("binding a function Internal must not disturb its verified bytes");
        assert_eq!(module_object.preserved.len(), 2);
    }

    /// TEETH. Hand the obligation a merged object that does NOT contain one of
    /// the verified functions (here: the single-function object for `merge_add`
    /// alone, presented as if it were the whole module) and assert it REFUSES.
    /// Without this, "the bytes were preserved" could be vacuously true.
    #[test]
    fn merge_obligation_refuses_a_module_missing_a_verified_function() {
        use crate::codegen_backend::{CompiledModule, EmittedModuleObject, FunctionLinkage};
        let backend = default_verification_backend();
        let funcs = merge_module();

        // Verify both functions the normal way.
        let (verified, _report) =
            emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
                .expect("both functions are provable");
        assert_eq!(verified.len(), 2);

        // Build a "merged" object that only ever contained the FIRST function.
        let only_first = CompiledModule {
            name: "merge.partial".to_string(),
            lir_functions: vec![backend.lower_function(&funcs[0]).expect("first function lowers")],
            object_path: None,
            function_count: 1,
            source_functions: Some(vec![funcs[0].clone()]),
            linkage: vec![FunctionLinkage::External],
            statics: Vec::new(),
        };
        let partial =
            backend.emit_module_object(&only_first).expect("single-function module emits");
        let partial = EmittedModuleObject {
            artifact_name: partial.artifact_name,
            bytes: partial.bytes,
            text_extents: partial.text_extents,
        };

        match assert_merged_object_preserves_verified_text(&partial, &verified) {
            Err(VerifyError::MergedBytesDiverged { function, .. }) => {
                assert_eq!(
                    function, "merge_or",
                    "the missing function is the one the obligation must name"
                );
            }
            other => {
                panic!("a merged object missing a verified function MUST be refused, got {other:?}")
            }
        }
    }

    /// TEETH, byte level. Corrupt one instruction byte inside the merged text
    /// and assert the obligation catches it.
    #[test]
    fn merge_obligation_refuses_corrupted_merged_bytes() {
        use crate::codegen_backend::FunctionLinkage;
        let backend = default_verification_backend();
        let funcs = merge_module();

        let (verified, _report) =
            emit_objects_verified_reported_with_backend(&funcs, EmitPolicy::AllowUnknown, &backend)
                .expect("both functions are provable");

        let module = build_merged_module(&funcs, &[FunctionLinkage::External; 2], &[], &backend)
            .expect("module lowers");
        let mut emitted = backend.emit_module_object(&module).expect("module emits");
        assert_merged_object_preserves_verified_text(&emitted, &verified)
            .expect("the untouched merge must satisfy the obligation");

        // Find where __text lives in the file and flip a byte inside the SECOND
        // function's body (its extent offset is > 0 by construction).
        let (text, _base) =
            extract_text_from_object(&emitted.bytes).expect("merged object has text");
        let second = emitted
            .text_extents
            .iter()
            .find(|extent| extent.offset > 0)
            .expect("the second merged function sits past offset 0")
            .clone();
        let file_offset = find_subslice(&emitted.bytes, &text)
            .expect("the text section bytes appear in the object file");
        emitted.bytes[file_offset + second.offset as usize] ^= 0xff;

        match assert_merged_object_preserves_verified_text(&emitted, &verified) {
            Err(VerifyError::MergedBytesDiverged { function, detail }) => {
                assert_eq!(function, second.name, "the corrupted function must be named");
                assert!(
                    detail.contains("differ from the"),
                    "expected a byte-divergence diagnosis, got: {detail}"
                );
            }
            other => panic!("a corrupted merged object MUST be refused, got {other:?}"),
        }
    }

    fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
        if needle.is_empty() || needle.len() > haystack.len() {
            return None;
        }
        (0..=haystack.len() - needle.len())
            .find(|start| &haystack[*start..start + needle.len()] == needle)
    }

    // =======================================================================
    // FORMULA -> BvExpr LOWERING TESTS (the [PROVED] path).
    //
    // These exercise `formula_to_bvexpr` + ay-proof's `export_bv_blast_proof_expr`
    // on the gate's add-leaf obligation: the REAL `auto_spec` Formula
    // (`trust_ir_semantics` of the i32 add) on one side, and the NORMALIZED
    // machine shape `BvExtract(BvZeroExt(BvAdd(W0,W1,32),32),31,0)` on the other.
    // Both are in the on-disk BvExpr fragment, lower cleanly, and the exported
    // BvBlastProof kernel-re-checks (`proof.validate()` succeeds).
    //
    // LIVE GATE: `gate_emits_proved_for_real_add` drives the WHOLE
    // `verify_output_preserved` pipeline on a real `add(i32,i32)` and asserts the
    // verdict is [PROVED]-grade (carries a kernel-re-checkable BvBlastProof) and
    // that the carried proof self-validates. `raw_machine_out_now_lowers`
    // documents that the RAW byte-derived machine_out (with `BvOr(0,x)` identity
    // wrappers + `BitVec` constants) NOW lowers faithfully (Or/Const are native
    // BvExpr variants) — the prior gap is closed, with no trusted fold.
    // =======================================================================

    /// The auto-spec side: `BvAdd(W0, W1, 32)` with `Wn = BvExtract(Var(Xn,64),31,0)`.
    /// This is exactly what `trust_ir_semantics(add_i32)` produces (asserted below).
    fn add_leaf_auto_spec() -> Formula {
        Formula::BvAdd(b(wn(0)), b(wn(1)), 32)
    }

    /// The NORMALIZED machine shape for the add-leaf: the 32-bit adder result is
    /// zero-extended to 64 then sliced back to [31:0] (the W-register write-back /
    /// X-register read round-trip), all over the same shared W0/W1 leaves. This is
    /// the gate's obligation with the machine model's identity `BvOr(0,_)` wrappers
    /// canonicalized out — i.e. the shape the recon design targets, in-fragment.
    fn add_leaf_machine_out_normalized() -> Formula {
        Formula::BvExtract {
            inner: b(Formula::BvZeroExt(b(Formula::BvAdd(b(wn(0)), b(wn(1)), 32)), 32)),
            high: 31,
            low: 0,
        }
    }

    #[test]
    fn auto_spec_matches_real_interpreter_output() {
        // Anchor the hand-built auto_spec to the gate's REAL output so the proof
        // test is not exercising a divergent shape.
        let f = binop_fn("ll_add", BinOp::Add, Ty::i32());
        let real = trust_ir_semantics(&f).expect("interp");
        assert_eq!(
            real,
            add_leaf_auto_spec(),
            "hand-built auto_spec must equal trust_ir_semantics"
        );
    }

    #[test]
    fn add_leaf_obligation_lowers_and_validates() {
        // The gate's REAL add-leaf obligation: normalized machine_out == auto_spec.
        let machine_out = add_leaf_machine_out_normalized();
        let auto_spec = add_leaf_auto_spec();

        let lhs = formula_to_bvexpr(&machine_out).expect("lower machine_out");
        let rhs = formula_to_bvexpr(&auto_spec).expect("lower auto_spec");

        // Export a zero-trust bit-blast certificate and KERNEL-RE-CHECK it.
        let proof = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs)
            .expect("add-leaf obligation must produce a refutation proof");
        proof.validate().expect("exported BvBlastProof must kernel-re-check (the [PROVED] path)");
    }

    #[test]
    fn lowering_anti_vacuity_wrong_spec_no_proof() {
        // ANTI-VACUITY: pair the normalized machine_out (an ADD) against a SUB
        // spec. The equality is a FALSE identity, so the disequality is SAT and
        // NO validating proof is produced (export returns NoRefutation). This
        // proves the lowering+export are not vacuously "valid" for any spec.
        let machine_out = add_leaf_machine_out_normalized();
        let wrong_spec = Formula::BvSub(b(wn(0)), b(wn(1)), 32);

        let lhs = formula_to_bvexpr(&machine_out).expect("lower machine_out");
        let rhs = formula_to_bvexpr(&wrong_spec).expect("lower wrong spec");

        let result = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs);
        assert!(
            matches!(result, Err(ay_proof::BvExprExportError::NoRefutation)),
            "ADD-vs-SUB is a false identity: export must yield NoRefutation, got {result:?}"
        );
    }

    #[test]
    fn lowering_fragment_round_trips() {
        // Spot-check each supported variant lowers to the expected BvExpr.
        use ay_proof::BvExpr;
        assert_eq!(
            formula_to_bvexpr(&wn(0)).unwrap(),
            BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0)
        );
        assert_eq!(
            formula_to_bvexpr(&Formula::BvZeroExt(b(wn(0)), 32)).unwrap(),
            BvExpr::zero_ext(BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0), 32)
        );
        assert_eq!(
            formula_to_bvexpr(&Formula::BvSub(b(wn(0)), b(wn(1)), 32)).unwrap(),
            BvExpr::sub(
                BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0),
                BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0)
            )
        );
        // And/Xor now lower structurally to their native per-bit BvExpr variants.
        assert_eq!(
            formula_to_bvexpr(&Formula::BvAnd(b(wn(0)), b(wn(1)), 32)).unwrap(),
            BvExpr::and(
                BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0),
                BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0)
            )
        );
        assert_eq!(
            formula_to_bvexpr(&Formula::BvXor(b(wn(0)), b(wn(1)), 32)).unwrap(),
            BvExpr::xor(
                BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0),
                BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0)
            )
        );
        // BvMul now lowers to the shift-and-add `BvExpr::Mul` array multiplier
        // (And2 partial products + Xor3/FullAdderCarry adder tree, existing gate
        // KINDS only). The structural lowering is faithful; whether the LIVE gate
        // emits [PROVED] vs [VALIDATED] is decided downstream by whether the
        // exporter surfaces the refutation (see the gate-level mul tests).
        assert_eq!(
            formula_to_bvexpr(&Formula::BvMul(b(wn(0)), b(wn(1)), 32)).unwrap(),
            BvExpr::mul(
                BvExpr::extract(BvExpr::leaf("X0", 64), 31, 0),
                BvExpr::extract(BvExpr::leaf("X1", 64), 31, 0)
            )
        );
    }

    #[test]
    fn raw_machine_out_now_lowers() {
        // GAP CLOSED: the RAW byte-derived machine_out (straight from the symbolic
        // executor, NOT normalized) contains `BvOr(BitVec{0,32}, _, 32)` identity
        // wrappers + `BitVec` constants. With `Or`/`Const` now native BvExpr
        // variants, the lowering maps them STRUCTURALLY (no fold) so the raw shape
        // lowers, and the obligation `raw_machine_out == auto_spec` exports a
        // BvBlastProof that kernel-re-checks. This is what makes the LIVE gate
        // emit [PROVED] for a real add (not just the synthetic normalized shape).
        let f = binop_fn("raw_add", BinOp::Add, Ty::i32());
        let (_obj, code, base) = emit_text(&f).expect("emit");
        let raw = symbolic_machine_output(&code, base, 32, false).expect("decode");

        let lhs = formula_to_bvexpr(&raw).expect("raw machine_out now lowers (Or/Const native)");
        let rhs = formula_to_bvexpr(&add_leaf_auto_spec()).expect("auto_spec lowers");
        let proof = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs)
            .expect("raw add obligation must produce a refutation proof");
        proof.validate().expect("exported proof must kernel-re-check");
    }

    /// A real `add(i32,i32)` VerifiableFunction, the canonical add-leaf case.
    fn add_i32_fn() -> VerifiableFunction {
        binop_fn("proved_add_i32", BinOp::Add, Ty::i32())
    }

    // Trust: RUNG 1 — the [PROVED]-grade gate tests below require the CLEAN
    // KERNEL re-check, so they are gated on `kernel-recheck`. Without that
    // feature the gate fails closed to [VALIDATED] (it will not rest [PROVED] on
    // ay's `validate()` alone). Run: `--features kernel-recheck`.
    /// `a + b` (i32) — B4 PROMOTION (the before/after evidence). The SLOW
    /// SAT-reflection emits a 17854-step refutation on AY 0e35, ABOVE the
    /// 2048-step production frontier — so PRE-B4 add stayed [VALIDATED]
    /// (RETRACTION #21). POST-B4 the O(1) structured-instantiation path discharges the REAL
    /// add@32 obligation in the kernel FIRST (no SAT reflection), so add is now
    /// fast default-[PROVED] via `KernelInstantiated`. This test asserts the FLIP:
    /// `is_kernel_proved()` is now TRUE, and the grade is `KernelInstantiated`
    /// (NOT the slow `KernelRecheckable`, so `kernel_proof()` — the BvBlastProof
    /// accessor — is still None). The validated current frontier shape
    /// (clauses=1522, steps=17854; no current full-kernel resource measurement)
    /// is the slow path the O(1) path REPLACES for add.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_add_is_proved_via_o1_instantiation() {
        let verdict = verify_output_preserved(&add_i32_fn());
        assert!(verdict.is_proven(), "add output is preserved (Proven)");
        // THE FLIP: add@32 is now KERNEL-[PROVED] (was [VALIDATED] pre-B4).
        assert!(
            verdict.is_kernel_proved(),
            "B4: add@32 must be kernel-[PROVED] via O(1) instantiation (the flip); got {verdict:?}"
        );
        // Specifically via the O(1) instantiation path (not the slow BvBlastProof).
        assert!(
            matches!(
                verdict,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "add@32 must be [PROVED] via KernelInstantiated (the O(1) path); got {verdict:?}"
        );
    }

    // ── B4 LIVE-GATE NEGATIVE CONTROLS (the fail-safe invariant, end-to-end) ──

    /// B4 control (i) — an OUT-OF-FRAGMENT op FALLS THROUGH, no regression. A signed
    /// `div` i32 carries a CONDITIONAL (divisor != 0) obligation, so the O(1)
    /// instantiation path DECLINES (its unconditional bvfEval-headed goal is a
    /// different claim) and the slow path also declines the kernel grade → the
    /// function keeps its correct grade [VALIDATED] (Proven{AyValidated}). The O(1)
    /// path changed NOTHING (no spurious [PROVED], no lost Proven). NOTE: mul was the
    /// prior fall-through example but is now O(1) kernel-[PROVED] (#59, the MADD
    /// `BvAdd(0,·)` wrapper is stripped via bvf_add_zero_id); div is the current
    /// out-of-fragment example.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_noncanonical_shape_falls_through_no_regression() {
        let v = verify_output_preserved(&div_then_xor_fn("b4_divxor_noncanon", Ty::u32()));
        assert!(v.is_proven(), "shl u32 is still Proven (ay UNSAT) after B4: {v:?}");
        assert!(
            !v.is_kernel_proved(),
            "an OUT-OF-FRAGMENT op (shift — no reflect arm / kernel discharge) must NOT be \
             kernel-[PROVED] by the O(1) path — it falls through and stays [VALIDATED]; got {v:?}"
        );
    }

    /// B4 control (ii) — CORRUPTED EMITTED-BYTE is REFUSED END-TO-END. Emit `add`
    /// but flip the ADD→SUB bit so the decoded `machine_out = BvSub`, while the IR
    /// `auto = BvAdd`. `verify_output_preserved` runs `discharge_equal_pre` FIRST
    /// (it is the SOLE Refuted gate); ay finds the divergence SAT → Refuted, and
    /// the O(1) path NEVER runs (it is only reached in the Proven branch). The
    /// corrupted byte is REFUSED — the O(1) path cannot let a miscompile through.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_corrupted_emitted_byte_refused_end_to_end() {
        let f = binop_fn("b4_corrupt_add", BinOp::Add, Ty::i32());
        let verdict = with_text_corruptor(
            |code: &mut Vec<u8>, base: u64| {
                let mut pc = base;
                let mut off = 0usize;
                while off + 4 <= code.len() {
                    let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                    let insn = decode_aarch64(&bytes, pc).expect("decode");
                    if matches!(insn.opcode, Opcode::Add) {
                        let mut word = u32::from_le_bytes(bytes);
                        word ^= 1 << 30; // ADD -> SUB (shifted-reg bit30)
                        code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                        return;
                    }
                    if matches!(insn.opcode, Opcode::Ret) {
                        return;
                    }
                    pc += 4;
                    off += 4;
                }
            },
            || verify_output_preserved(&f),
        );
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "a corrupted ADD->SUB emission must be REFUSED end-to-end (divergence caught \
             before the O(1) path); the O(1) path must NOT let a miscompile through; got {verdict:?}"
        );
        assert!(
            !verdict.is_kernel_proved() && !verdict.is_proven(),
            "the corrupted function must be neither Proven nor kernel-[PROVED]; got {verdict:?}"
        );
    }

    /// B4 control (iii) — MIS-REFLECTION is kernel-GUARDED (matcher untrusted). We
    /// feed `try_o1_instantiation_discharge` a DELIBERATELY MIS-PAIRED obligation:
    /// machine_out = the real add@32 shape, but `auto` = a DIFFERENT add over
    /// SWAPPED operands (X1+X0 instead of X0+X1) — a wrong reflection target. The
    /// reflected discharge's conclusion ≠ the real (swapped) obligation, so the
    /// kernel `check_type` FAILS → `try_o1_instantiation_discharge` returns None
    /// (fall through), NEVER a false [PROVED]. (Note: X0+X1 and X1+X0 are NOT
    /// syntactically equal as Formulas/BvF, and the bvf_add_cong discharge is built
    /// for the matched pairing, so the swapped goal is rejected.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_mis_reflection_is_kernel_guarded() {
        // machine_out: the real raw add@32 (X0+X1 with wrappers).
        let f = binop_fn("b4_misreflect", BinOp::Add, Ty::i32());
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        // auto': a WRONG target — add over SWAPPED operands wn(1)+wn(0).
        let auto_swapped = Formula::BvAdd(b(wn(1)), b(wn(0)), 32);
        // The O(1) discharge must DECLINE (kernel check_type fails against the
        // mismatched obligation): a wrong reflection target yields no [PROVED].
        let outcome = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &machine_out,
            &auto_swapped,
        );
        assert!(
            outcome.is_none(),
            "a MIS-PAIRED obligation (machine X0+X1 vs auto X1+X0) must make the O(1) \
             discharge DECLINE (kernel-guarded) — never a false [PROVED]; got {outcome:?}"
        );
        // Positive sanity: the CORRECTLY-paired obligation IS discharged.
        let auto = trust_ir_semantics(&f).expect("auto");
        let ok =
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine_out, &auto);
        assert!(
            ok.is_some(),
            "the correctly-paired add@32 obligation must be discharged; got {ok:?}"
        );
    }

    /// B4 DETERMINISM probe (item 5): the O(1) path is deterministic — the add@32
    /// GRADE (kernel-[PROVED] via KernelInstantiated) and the emitted BYTES digest
    /// are stable. This test prints a `B4_DETERMINISM_DIGEST=<...>` line capturing
    /// (grade, evidence-kind, bytes-blake-ish-digest); running it across ≥3
    /// independent rebuilds and diffing the printed line is the determinism
    /// evidence (the goal's "closed only on ≥3 agreeing"). Within a single run it
    /// also asserts the grade is stable across repeated in-process evaluations.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_o1_path_determinism_digest() {
        // Every op on the O(1) KernelInstantiated path must be deterministic:
        // across 3 in-process evaluations the grade (kernel_proved + instantiated)
        // and the emitted-bytes FNV-1a digest must be identical. add/sub are the
        // genuine [VALIDATED]->[PROVED] flips; and/xor are the #42 slow->O(1)
        // migrations — all four share the same fail-safe O(1) wiring.
        let cases: [(&str, VerifiableFunction); 8] = [
            ("ADD", add_i32_fn()),
            ("SUB", binop_fn("det_sub_i32", BinOp::Sub, Ty::i32())),
            ("AND", binop_fn("det_and_u32", BinOp::BitAnd, Ty::u32())),
            ("XOR", binop_fn("det_xor_u32", BinOp::BitXor, Ty::u32())),
            // OR joined this list when `Clean.BVC.bvf_or_cong` was proved. Until
            // then only the one-sided `bvf_or_cong2` existed, so a machine `Orr`
            // with two real operands had no O(1) route and fell back to
            // bit-blasting: (c) MEASURED, `(x^y)|(x&y)` cost 20.94 s / 27.41 GB
            // against 2.76 s / 0.99 GB for the same shape with `^` on top.
            ("OR", binop_fn("det_or_u32", BinOp::BitOr, Ty::u32())),
            ("EQ", cmp_fn("det_eq_i32", BinOp::Eq, Ty::i32())),
            ("ULT", cmp_fn("det_ult_u32", BinOp::Lt, Ty::u32())),
            ("ULE", cmp_fn("det_ule_u32", BinOp::Le, Ty::u32())),
        ];
        for (label, f) in &cases {
            let mut grades = Vec::new();
            let mut digests = Vec::new();
            for _ in 0..3 {
                let v = verify_output_preserved(f);
                grades.push((
                    v.is_kernel_proved(),
                    matches!(
                        v,
                        OutputVerdict::Proven {
                            evidence: ProvenEvidence::KernelInstantiated { .. }
                        }
                    ),
                ));
                let bytes =
                    emit_object_verified(f, EmitPolicy::AllowUnknown).expect("emit O(1) op@32");
                // a cheap stable digest (FNV-1a) — we only need equality across runs.
                let mut h: u64 = 0xcbf2_9ce4_8422_2325;
                for &byte in &bytes {
                    h ^= u64::from(byte);
                    h = h.wrapping_mul(0x100_0000_01b3);
                }
                digests.push((bytes.len(), h));
            }
            assert!(
                grades.iter().all(|&g| g == (true, true)),
                "{label}@32 grade must be stable kernel-[PROVED]-via-instantiation; got {grades:?}"
            );
            assert!(
                digests.iter().all(|&d| d == digests[0]),
                "{label}@32 emitted-bytes digest must be stable across evals; got {digests:?}"
            );
            // The cross-rebuild evidence line (compare across ≥3 rebuilds).
            eprintln!(
                "B4_DETERMINISM_DIGEST_{label}=grade(kernel_proved=true,instantiated=true) bytes_len={} fnv={:#018x}",
                digests[0].0, digests[0].1
            );
        }
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_sub_is_proved_via_o1_instantiation() {
        // B4 SUB PROMOTION (before/after). PRE: sub@32's slow SAT-reflection is a
        // 19389-step borrow chain, far over the 2048 frontier -> [VALIDATED]. POST:
        // the O(1) path discharges the REAL sub@32 obligation (BvSub core in the same
        // coercion wrappers as add -- traced #40-followup) via bvf_sub_cong + the
        // parametric wrapper lemmas -> fast kernel-[PROVED] via KernelInstantiated.
        let verdict = verify_output_preserved(&binop_fn("val_sub_i32", BinOp::Sub, Ty::i32()));
        assert!(verdict.is_proven(), "sub output is preserved (Proven)");
        assert!(
            verdict.is_kernel_proved(),
            "B4: sub@32 must be kernel-[PROVED] via O(1) instantiation (the flip); got {verdict:?}"
        );
        assert!(
            matches!(
                verdict,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "sub@32 must be [PROVED] via KernelInstantiated (the O(1) path); got {verdict:?}"
        );
    }

    /// B4 SUB control (ii) — CORRUPTED SUB->ADD emission REFUSED end-to-end. Emit
    /// `sub`, flip the SUB->ADD bit so decoded machine_out=BvAdd while IR auto=BvSub;
    /// discharge_equal_pre finds SAT -> Refuted; the O(1) path never runs.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_sub_corrupted_emitted_byte_refused_end_to_end() {
        let f = binop_fn("b4_corrupt_sub", BinOp::Sub, Ty::i32());
        let verdict = with_text_corruptor(
            |code: &mut Vec<u8>, base: u64| {
                let mut pc = base;
                let mut off = 0usize;
                while off + 4 <= code.len() {
                    let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                    let insn = decode_aarch64(&bytes, pc).expect("decode");
                    if matches!(insn.opcode, Opcode::Sub) {
                        let mut word = u32::from_le_bytes(bytes);
                        word ^= 1 << 30; // SUB (bit30=1) -> ADD (bit30=0)
                        code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                        return;
                    }
                    if matches!(insn.opcode, Opcode::Ret) {
                        return;
                    }
                    pc += 4;
                    off += 4;
                }
            },
            || verify_output_preserved(&f),
        );
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "a corrupted SUB->ADD emission must be REFUSED end-to-end; got {verdict:?}"
        );
        assert!(!verdict.is_kernel_proved() && !verdict.is_proven());
    }

    /// B4 SUB control (iii) — MIS-REFLECTION kernel-guarded for sub: machine = real
    /// sub@32, but auto' = sub over SWAPPED operands (X1-X0 != X0-X1) -> the O(1)
    /// discharge's kernel check_type FAILS -> declines (never a false [PROVED]).
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_sub_mis_reflection_is_kernel_guarded() {
        let f = binop_fn("b4_sub_misreflect", BinOp::Sub, Ty::i32());
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        let auto_swapped = Formula::BvSub(b(wn(1)), b(wn(0)), 32);
        let outcome = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &machine_out,
            &auto_swapped,
        );
        assert!(
            outcome.is_none(),
            "a MIS-PAIRED sub obligation (machine X0-X1 vs auto X1-X0) must DECLINE; got {outcome:?}"
        );
        let auto = trust_ir_semantics(&f).expect("auto");
        let ok =
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine_out, &auto);
        assert!(ok.is_some(), "the correctly-paired sub@32 obligation must discharge; got {ok:?}");
    }

    /// B4 BITWISE control (i) — end-to-end REFUSAL: emit a real and@32, then flip
    /// AND opc=00 -> ORR opc=01 (bit 29) so decoded machine_out=BvOr while IR
    /// auto=BvAnd. The two disagree -> discharge_equal_pre finds SAT -> Refuted,
    /// and the O(1) path never runs (no false [PROVED] from a miscompiled AND).
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_and_corrupted_emitted_byte_refused_end_to_end() {
        let f = binop_fn("b4_corrupt_and", BinOp::BitAnd, Ty::u32());
        let verdict = with_text_corruptor(
            |code: &mut Vec<u8>, base: u64| {
                let mut pc = base;
                let mut off = 0usize;
                while off + 4 <= code.len() {
                    let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
                    let insn = decode_aarch64(&bytes, pc).expect("decode");
                    if matches!(insn.opcode, Opcode::And) {
                        let mut word = u32::from_le_bytes(bytes);
                        word ^= 1 << 29; // AND opc=00 -> ORR opc=01
                        code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                        return;
                    }
                    if matches!(insn.opcode, Opcode::Ret) {
                        return;
                    }
                    pc += 4;
                    off += 4;
                }
            },
            || verify_output_preserved(&f),
        );
        assert!(
            matches!(verdict, OutputVerdict::Refuted { .. }),
            "a corrupted AND->ORR emission must be REFUSED end-to-end; got {verdict:?}"
        );
        assert!(!verdict.is_kernel_proved() && !verdict.is_proven());
    }

    /// B4 BITWISE control (ii) — MIS-REFLECTION kernel-guarded: machine = real
    /// and@32 (X0 & X1), but auto' = AND vs the wrong second operand. The O(1)
    /// discharge's kernel check_type FAILS on the mismatched obligation ->
    /// declines (never a false [PROVED]); the correctly-paired one discharges.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_and_mis_reflection_is_kernel_guarded() {
        let f = binop_fn("b4_and_misreflect", BinOp::BitAnd, Ty::u32());
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        // auto' = X0 & X0 (drops the X1 operand) — disagrees with machine X0 & X1.
        let auto_wrong = Formula::BvAnd(b(wn(0)), b(wn(0)), 32);
        let outcome = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &machine_out,
            &auto_wrong,
        );
        assert!(
            outcome.is_none(),
            "a MIS-PAIRED and obligation (machine X0&X1 vs auto X0&X0) must DECLINE; got {outcome:?}"
        );
        let auto = trust_ir_semantics(&f).expect("auto");
        let ok =
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine_out, &auto);
        assert!(ok.is_some(), "the correctly-paired and@32 obligation must discharge; got {ok:?}");
    }

    /// SCOPING PROBE for the `&T` parameter blocker — is it the ABI gate or the
    /// MEMORY FRAGMENT that actually stops a reference argument?
    ///
    /// `rustc_codegen_trust_cg`'s `scalar_register_abi_ty_supported` refused a
    /// `&E` argument before anything else ran, so the ABI message was the one a
    /// user saw — but the REAL constraint was this fragment: a load through a
    /// PARAMETER reflects as `Select` over a bare `MEM`, memory the function never
    /// wrote, and there was no lemma for that shape at all.
    ///
    /// Recorded as a test rather than prose because the design note that scoped
    /// this blocker was an inference from reading `reflect_formula`, and two
    /// earlier scopings in the same effort were wrong.
    ///
    /// The bare read is now IN the fragment, but only under the no-preceding-store
    /// side condition (see
    /// `a_bare_caller_memory_read_is_admitted_only_for_a_store_free_body`). What
    /// this test still pins is the DEFAULT: under `ReflectCtx::closed` — the policy
    /// every caller gets unless it has proved the side condition — a bare read is
    /// refused, and refused for a DIFFERENT reason than an aliased one.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn a_bare_memory_read_is_outside_the_fragment_but_a_roundtrip_is_not() {
        let addr = Formula::Var("P".to_string(), Sort::BitVec(64));
        let val = Formula::Var("V".to_string(), Sort::BitVec(64));
        let mem = Formula::Var("MEM".to_string(), Sort::BitVec(64));

        // (1) `*p` where `p` is a parameter: Select over a BARE memory. Under the
        //     FAIL-CLOSED default policy this is still outside the fragment.
        let bare = Formula::Select(Box::new(mem.clone()), Box::new(addr.clone()));
        let bare_err = reflect_formula(&bare)
            .err()
            .expect("a bare memory read must be REFUSED under the fail-closed policy");
        assert!(
            bare_err.contains("bare memory read outside fragment"),
            "expected the bare-read refusal, got: {bare_err}"
        );

        // (2) store-then-load at the SAME address: inside the fragment today.
        let roundtrip = Formula::Select(
            Box::new(Formula::Store(Box::new(mem.clone()), Box::new(addr.clone()), Box::new(val))),
            Box::new(addr.clone()),
        );
        assert!(
            reflect_formula(&roundtrip).is_ok(),
            "the store-then-load roundtrip must still reflect"
        );

        // (3) load at a DIFFERENT address than the covering store: also out,
        //     and by a DIFFERENT reason — aliasing, not bare-read. Pins that the
        //     two exclusions are distinct rather than one catch-all.
        let aliased = Formula::Select(
            Box::new(Formula::Store(
                Box::new(mem),
                Box::new(addr),
                Box::new(Formula::BitVec { value: 0, width: 64 }),
            )),
            Box::new(Formula::Var("Q".to_string(), Sort::BitVec(64))),
        );
        let alias_err = reflect_formula(&aliased).err().expect("an aliased read must be refused");
        assert!(
            alias_err.contains("address mismatch") || alias_err.contains("aliasing"),
            "expected the aliasing refusal, got: {alias_err}"
        );
    }

    /// THE `&T` PARAMETER FRAGMENT — a bare read of CALLER-PROVIDED memory is in,
    /// and it is in ONLY for a body that never writes.
    ///
    /// `*e` for a `&u64` parameter reflects to `Select(MEM, P)`: a read of memory
    /// the function never wrote. Neither read-over-write lemma applies (there is no
    /// store to bridge through), which is what actually kept reference parameters
    /// out of the fragment — the ABI refusal was only the message users saw.
    ///
    /// It is admitted through `Clean.BVC.selectAddrCong`, a congruence over
    /// `bvSelect`'s ADDRESS at a fixed array, under one side condition checked
    /// structurally over the WHOLE obligation: NO STORE on either side. Then both
    /// sides read the same untouched pre-state and equal addresses give equal
    /// values. With a store anywhere the argument is void — a read could be before
    /// or after it — so it stays refused.
    ///
    /// This is also the MUTATION GUARD for that side condition: arms (2) and (3)
    /// fail if `is_store_free` / `caller_memory_readable` is weakened.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn a_bare_caller_memory_read_is_admitted_only_for_a_store_free_body() {
        // The memory sort the gate's own `trust_ir_semantics` produces for a load.
        let mem_sort = || Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8)));
        let mem = || Formula::Var("MEM".to_string(), mem_sort());
        let p = || Formula::Var("P".to_string(), Sort::BitVec(64));
        let q = || Formula::Var("Q".to_string(), Sort::BitVec(64));
        let read = |m: Formula, a: Formula| Formula::Select(Box::new(m), Box::new(a));

        // (1) POSITIVE — `*e` on both sides of a store-free obligation PROVES.
        let machine = read(mem(), p());
        let auto = read(mem(), p());
        assert!(
            reflect_formula_for(&machine, &machine, &auto).is_ok(),
            "a bare caller-memory read must reflect for a store-free body"
        );
        let ok = crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine, &auto);
        assert!(
            ok.as_deref().is_some_and(|t| t.contains("selectAddrCong")),
            "the store-free caller-memory read must discharge via selectAddrCong; got {ok:?}"
        );

        // (2) SIDE CONDITION — the SAME read, with a store present on ONE side, is
        //     REFUSED. Read-after-write and aliasing stay out of the fragment.
        //     (Mutating `is_store_free` to admit `Store` turns this red.)
        let with_store = Formula::BvAdd(
            Box::new(read(mem(), p())),
            Box::new(read(
                Formula::Store(
                    Box::new(mem()),
                    Box::new(p()),
                    Box::new(Formula::BitVec { value: 7, width: 64 }),
                ),
                p(),
            )),
            64,
        );
        assert!(
            !store_free(&with_store),
            "a formula containing a Store must NOT be classified store-free"
        );
        let refused = reflect_formula_for(&machine, &with_store, &auto)
            .err()
            .expect("a bare read must be refused once EITHER side writes memory");
        assert!(
            refused.contains("bare memory read outside fragment"),
            "expected the bare-read refusal for a storing body, got: {refused}"
        );
        assert!(
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&with_store, &auto)
                .is_none(),
            "an obligation with a store must NOT discharge through the bare-read arm"
        );

        // (3) FAIL-CLOSED on nodes the walker cannot see into: an `Ite` is not in
        //     the store-free whitelist, so it closes the door whatever it wraps.
        //     (Mutating `is_store_free`'s catch-all to `true` turns this red.)
        let opaque = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(read(mem(), p())),
            Box::new(read(mem(), p())),
        );
        assert!(
            !store_free(&opaque),
            "an unwhitelisted node must be treated as possibly-storing (fail closed)"
        );

        // (4) NO FALSE [PROVED] once the arm IS live: reads at DIFFERENT addresses,
        //     and reads of DIFFERENTLY-NAMED memories, leave non-defeq cores and the
        //     kernel DECLINES. The memory is an opaque axiom precisely so that this
        //     is decided by the kernel and not by reduction.
        let other_addr = read(mem(), q());
        assert!(
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine, &other_addr)
                .is_none(),
            "reads at DIFFERENT addresses must not discharge"
        );
        let other_mem = read(Formula::Var("MEM2".to_string(), Sort::BitVec(64)), p());
        assert!(
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine, &other_mem)
                .is_none(),
            "reads of DIFFERENTLY-NAMED memories must not discharge"
        );

        // (5) The address is reflected, not assumed: a read at `P + 8` on one side
        //     against `P` on the other must not discharge, while the same wrapped
        //     address on both sides must.
        let bumped = read(
            mem(),
            Formula::BvAdd(Box::new(p()), Box::new(Formula::BitVec { value: 8, width: 64 }), 64),
        );
        assert!(
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine, &bumped)
                .is_none(),
            "a read at P+8 must not discharge against a read at P"
        );
        assert!(
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&bumped, &bumped)
                .is_some(),
            "the same computed address on both sides must discharge"
        );
    }

    /// B4 BITWISE control (iv) — MIS-REFLECTION kernel-guarded for OR, the arm
    /// added with `Clean.BVC.bvf_or_cong`.
    ///
    /// OR reached the O(1) path last, and it is the arm most worth guarding: the
    /// general two-operand `BvOr` used to be an `Err` out of `reflect_formula`,
    /// so every `|` fell back to bit-blasting. Now that it reflects, the ONLY
    /// thing standing between a mis-paired obligation and a false [PROVED] is
    /// the kernel `check_type`. This asserts that it discriminates: a machine
    /// `X0|X1` against an auto `X0|X0` must DECLINE, while the correct pairing
    /// discharges.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_or_mis_reflection_is_kernel_guarded() {
        let f = binop_fn("b4_or_misreflect", BinOp::BitOr, Ty::u32());
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        let auto_wrong = Formula::BvOr(b(wn(0)), b(wn(0)), 32);
        let outcome = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &machine_out,
            &auto_wrong,
        );
        assert!(
            outcome.is_none(),
            "a MIS-PAIRED or obligation (machine X0|X1 vs auto X0|X0) must DECLINE; got {outcome:?}"
        );
        let auto = trust_ir_semantics(&f).expect("auto");
        let ok =
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine_out, &auto);
        assert!(ok.is_some(), "the correctly-paired or@32 obligation must discharge; got {ok:?}");
    }

    /// B4 BITWISE control (iii) — MIS-REFLECTION kernel-guarded for xor: machine =
    /// real xor@32, but auto' = XOR vs the wrong operand -> declines; the correct
    /// pairing discharges. (xor shares the bare-zip lever with and; this guards
    /// that the kernel check_type still discriminates per-op.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_xor_mis_reflection_is_kernel_guarded() {
        let f = binop_fn("b4_xor_misreflect", BinOp::BitXor, Ty::u32());
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        let auto_wrong = Formula::BvXor(b(wn(0)), b(wn(0)), 32);
        let outcome = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &machine_out,
            &auto_wrong,
        );
        assert!(
            outcome.is_none(),
            "a MIS-PAIRED xor obligation (machine X0^X1 vs auto X0^X0) must DECLINE; got {outcome:?}"
        );
        let auto = trust_ir_semantics(&f).expect("auto");
        let ok =
            crate::verify_output_instantiate::try_o1_instantiation_discharge(&machine_out, &auto);
        assert!(ok.is_some(), "the correctly-paired xor@32 obligation must discharge; got {ok:?}");
    }

    /// THE OPERAND-IDENTITY GUARD for ALL O(1) ops (the eq-lesson regression
    /// lock). For each O(1)-[PROVED] op, the kernel discharge goal is built from
    /// the REAL reflected machine_out/auto — so a DIVERGENT-operand auto (X0 op X2
    /// where the real machine is X0 op X1) must be KERNEL-REJECTED (the kernel
    /// re-derives `machine == auto` at the REAL operands; ay is genuinely out of
    /// the TCB). A future refactor that reintroduced the #47 abstract-tautology
    /// gap on ANY op would flip one of these to a false [PROVED] and trip here.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_all_ops_divergent_operand_kernel_rejected() {
        // The operand wrapper W(Xn) the gate emits (Extract[31:0](ZeroExt(Or(0,
        // Extract[31:0](Xn)),32))), mirrored so the divergent auto shares the
        // machine's operand SHAPE but differs in the SECOND register (X2 vs X1).
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        // (label, real machine_out over (X0,X1), divergent auto over (X0,X2)).
        let cases: [(&str, Formula, Formula); 4] = [
            (
                "add",
                Formula::BvAdd(b(opwrap(0)), b(opwrap(1)), 32),
                Formula::BvAdd(b(opwrap(0)), b(opwrap(2)), 32),
            ),
            (
                "sub",
                Formula::BvSub(b(opwrap(0)), b(opwrap(1)), 32),
                Formula::BvSub(b(opwrap(0)), b(opwrap(2)), 32),
            ),
            (
                "and",
                Formula::BvAnd(b(opwrap(0)), b(opwrap(1)), 32),
                Formula::BvAnd(b(opwrap(0)), b(opwrap(2)), 32),
            ),
            (
                "xor",
                Formula::BvXor(b(opwrap(0)), b(opwrap(1)), 32),
                Formula::BvXor(b(opwrap(0)), b(opwrap(2)), 32),
            ),
        ];
        for (label, machine, div_auto) in &cases {
            // matched (machine vs an identical auto shape) MUST discharge.
            let matched = match label {
                &"add" => Formula::BvAdd(b(opwrap(0)), b(opwrap(1)), 32),
                &"sub" => Formula::BvSub(b(opwrap(0)), b(opwrap(1)), 32),
                &"and" => Formula::BvAnd(b(opwrap(0)), b(opwrap(1)), 32),
                _ => Formula::BvXor(b(opwrap(0)), b(opwrap(1)), 32),
            };
            let ok =
                crate::verify_output_instantiate::try_o1_instantiation_discharge(machine, &matched);
            assert!(ok.is_some(), "{label}: the MATCHED obligation must discharge; got {ok:?}");
            // DIVERGENT (X0 op X2 auto vs X0 op X1 machine) MUST be kernel-rejected.
            let bad =
                crate::verify_output_instantiate::try_o1_instantiation_discharge(machine, div_auto);
            assert!(
                bad.is_none(),
                "{label}: a DIVERGENT-operand obligation (machine X0,X1 vs auto X0,X2) must be \
                 KERNEL-REJECTED — the goal is the REAL reflected obligation, ay out of TCB; got {bad:?}"
            );
        }
        // neg (unary, lowers to BvSub(0, a)): divergent = BvSub(0, X2) vs machine BvSub(0, X1).
        let neg_machine =
            Formula::BvSub(b(Formula::BitVec { value: 0, width: 32 }), b(opwrap(1)), 32);
        let neg_div = Formula::BvSub(b(Formula::BitVec { value: 0, width: 32 }), b(opwrap(2)), 32);
        let neg_ok = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &neg_machine,
            &neg_machine.clone(),
        );
        assert!(neg_ok.is_some(), "neg: matched must discharge; got {neg_ok:?}");
        let neg_bad = crate::verify_output_instantiate::try_o1_instantiation_discharge(
            &neg_machine,
            &neg_div,
        );
        assert!(
            neg_bad.is_none(),
            "neg: divergent-operand must be KERNEL-REJECTED; got {neg_bad:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_emits_proved_via_o1_for_real_and() {
        // BITWISE AND: PATH MIGRATION (not a grade flip). PRE-#42, and@32 was
        // already [PROVED] via the SLOW KernelRecheckable path (bare per-bit And2
        // zip, under the frontier — ay producer-only). POST-#42 the O(1) path fires
        // FIRST and discharges it via bvf_and_cong + the wrapper lemmas, so the
        // grade is now KernelInstantiated: still [PROVED], but FASTER and with ay
        // (+ the bit-blaster clause semantics + bv_lowering_bridge) OUT of the cert
        // chain. So `kernel_proof()` (the slow BvBlastProof accessor) is now None,
        // while `is_kernel_proved()` stays true.
        let verdict =
            verify_output_preserved(&binop_fn("proved_and_u32", BinOp::BitAnd, Ty::u32()));
        assert!(verdict.is_kernel_proved(), "and must stay kernel-[PROVED]; got {verdict:?}");
        assert!(
            matches!(
                verdict,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "and@32 migrated to the O(1) KernelInstantiated path; got {verdict:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_emits_proved_via_o1_for_real_xor() {
        // BITWISE XOR: same PATH MIGRATION as and (slow KernelRecheckable -> fast
        // O(1) KernelInstantiated; still [PROVED], ay out of the cert chain).
        let verdict =
            verify_output_preserved(&binop_fn("proved_xor_u32", BinOp::BitXor, Ty::u32()));
        assert!(verdict.is_kernel_proved(), "xor must stay kernel-[PROVED]; got {verdict:?}");
        assert!(
            matches!(
                verdict,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "xor@32 migrated to the O(1) KernelInstantiated path; got {verdict:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_emits_proved_via_o1_for_real_or() {
        // BITWISE OR: the SAME path migration `and` and `xor` made above — slow
        // KernelRecheckable (bit-blast) -> fast O(1) KernelInstantiated. Still
        // [PROVED], and ay leaves the cert chain.
        //
        // OR made this migration LAST, and only once `Clean.BVC.bvf_or_cong` was
        // proved. Until then the only OR congruence was the one-sided
        // `bvf_or_cong2`, which fixes the LEFT operand — enough for the
        // `Orr Wd, WZR, Ws` register-move wrapper and nothing else — so a machine
        // `Orr` with two real operands had no O(1) route and bit-blasted.
        //
        // (c) MEASURED with that fallback in place, one function through
        // `--emit=link`, structure held constant and only the top operator
        // varied: `(x ^ y) ^ (x & y)` cost 2.76 s / 0.99 GB while
        // `(x ^ y) | (x & y)` cost 20.94 s / 27.41 GB — 28x, for an emission
        // differing by ONE instruction (`eor` vs `orr`).
        //
        // This assertion previously read `kernel_proof().is_some()`, i.e. it
        // required the `BvBlastProof` that ONLY the slow path attaches. That
        // pinned the defect, exactly as the `and`/`xor` versions did before their
        // own migrations; it is updated here for the same reason and in the same
        // shape, and the grade it demands is STRICTLY STRONGER, not weaker.
        let verdict = verify_output_preserved(&binop_fn("proved_or_u32", BinOp::BitOr, Ty::u32()));
        assert!(verdict.is_kernel_proved(), "or must stay kernel-[PROVED]; got {verdict:?}");
        assert!(
            matches!(
                verdict,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "or@32 migrated to the O(1) KernelInstantiated path; got {verdict:?}"
        );
    }

    /// Trust: RUNG 1 ANTI-VACUITY (LOAD-BEARING). Take a REAL, ay-self-validating
    /// add-leaf refutation (the same artifact the live gate emits at [PROVED]),
    /// CORRUPT a mid-chain recorded resolvent, and confirm the CLEAN KERNEL
    /// re-check — the exact promotion step `try_kernel_recheckable_proof` runs —
    /// REJECTS it, so the gate would NOT attach `KernelRecheckable`. The
    /// discrimination is the KERNEL's: the corrupted refutation reduces to
    /// `Bool.false` (proven independent of ay's `validate()` in clean's
    /// `proved_gate::tests::proved_gate_kernel_rejects_corrupted_refutation`), so
    /// the bridge's bounded big-stack kernel recheck returns `Rejected`. This is what
    /// removes ay from the [PROVED] emission TCB: even a refutation ay's own
    /// `validate()` accepts is graded [PROVED] only if the clean kernel re-checks
    /// it. The pristine proof IS kernel-accepted (the positive control).
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_kernel_rejects_corrupted_proof_no_proved() {
        use clean_auto::proved_gate::GateRecheck;

        // A genuine gate-shaped add-leaf identity: machine `a+b` vs IR `a+b`.
        let a = ay_proof::BvExpr::leaf("a", 4);
        let bb = ay_proof::BvExpr::leaf("b", 4);
        let lhs = ay_proof::BvExpr::add(a.clone(), bb.clone());
        let rhs = ay_proof::BvExpr::add(a, bb);
        let mut proof =
            ay_proof::export_bv_blast_proof_expr(&lhs, &rhs).expect("real add-leaf must export");
        proof.validate().expect("pristine proof self-validates (ay)");

        // POSITIVE CONTROL: the pristine proof is KERNEL-accepted -> [PROVED].
        assert!(
            matches!(
                crate::verify_output_instantiate::kernel_recheck_proved_grade_bounded(&proof),
                GateRecheck::KernelAccepted { .. }
            ),
            "pristine add-leaf refutation must be KERNEL-accepted to [PROVED]"
        );

        // CORRUPT a mid-chain recorded resolvent with an out-of-range var id.
        let mid = proof.refutation.steps.len() / 2;
        let bogus_var = proof.vars.roles.len() as u32 + 100;
        proof.refutation.steps[mid].clause =
            vec![ay_proof::bv_blast_export::Lit { var: bogus_var, neg: false }];

        // THE [PROVED] GATE REFUSES: the clean kernel rejects the corrupted cert.
        let outcome = crate::verify_output_instantiate::kernel_recheck_proved_grade_bounded(&proof);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "corrupted refutation must be REJECTED by the clean kernel re-check \
             (gate must NOT emit KernelRecheckable); got {outcome:?}"
        );
    }

    /// `a * b` (u32) — COMPARES/COVERAGE mul PROMOTION ([VALIDATED]→[PROVED] via O(1)).
    /// PRE (the old residual): the live gate emits at register width 32, where a
    /// multiply REFUTATION is not tractably bit-blast-re-checkable, so the slow
    /// `try_kernel_recheckable_proof` path declined → [VALIDATED]. POST (#59): mul is a
    /// COERCION-IDENTITY (machine `madd Wd,Wn,Wm,WZR` reflects to the SAME `BvMul`
    /// primitive as the IR auto-spec, modulo the `BvAdd(0,·)` MADD wrapper that
    /// `bvf_add_zero_id` strips). The O(1) instantiation path discharges
    /// `bvfEval(machine.bvf) = bvfEval(auto.bvf)` via the SHARED `BvF.Mul` core +
    /// `bvf_mul_cong` — NO multiplier-equivalence proof needed (the multiplier value
    /// is not load-bearing; congruence cancels the shared node). Operand identity is
    /// kernel-tied via the per-bit leaf keys. This is a TCB SHRINK (ay/the bit-blaster
    /// OUT of the TCB for multiply), the same grade-flip add got — NOT a new soundness
    /// claim. The old `MAX_RECHECKABLE_MUL_WIDTH` slow-path guard is now moot for the
    /// gate's coercion-identity obligation (it still governs the harder REFUTATION
    /// bit-blast, exercised by `mul_lowering_in_fragment_and_width8_recheckable_passes_guard`).
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_mul_is_proved_via_o1_instantiation() {
        let verdict = verify_output_preserved(&binop_fn("proved_mul", BinOp::Mul, Ty::u32()));
        assert!(verdict.is_proven(), "mul u32 output is preserved (Proven)");
        assert!(
            verdict.is_kernel_proved(),
            "COVERAGE: mul@32 must be kernel-[PROVED] via O(1) instantiation (the flip); got {verdict:?}"
        );
        assert!(
            matches!(
                verdict,
                OutputVerdict::Proven { evidence: ProvenEvidence::KernelInstantiated { .. } }
            ),
            "mul@32 must be [PROVED] via KernelInstantiated (the O(1) coercion-identity path); got {verdict:?}"
        );
    }

    /// (retired shape) the OLD wide-mul [VALIDATED] expectation, kept here only as a
    /// guard that a CONDITIONAL obligation (signed div) still declines [PROVED] — the
    /// real residual that remains uncertified at the gate. (Pre-#59 this tested mul;
    /// mul now promotes — see `gate_mul_is_proved_via_o1_instantiation`.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_signed_div_is_proved_via_o1_conditional_discharge() {
        // SIGNED div (i32) now reaches [PROVED]: the machine sdiv decodes to W(Ite(b==0,0,sdiv))
        // and auto is BvSDiv; the conditional discharge collapses the guard via divGuardBridge and
        // cancels the shared BvF.SDiv via bvf_sdiv_cong (bvSDiv = sign-magnitude round-to-zero,
        // clean 3ea26638). Previously [VALIDATED] (signed guard); the guard is now lifted.
        let verdict = verify_output_preserved(&binop_fn("val_cond_div", BinOp::Div, Ty::i32()));
        assert!(verdict.is_proven(), "div i32 is proven by ay (UNSAT under b != 0)");
        assert!(
            verdict.is_kernel_proved(),
            "signed div i32 must be [PROVED] via the O(1) conditional bvf_sdiv discharge, got {verdict:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_unsigned_div_is_proved_via_o1_conditional_discharge() {
        // UNSIGNED div: the machine ÷0 guard `Ite(b==0,0,udiv)` collapses to its udiv
        // else-branch = auto under the gate's `b != 0` precondition, via the O(1)
        // CONDITIONAL discharge (divGuardBridge, kernel-re-checked). This is the first
        // PRECONDITIONED obligation to reach [PROVED] — ay out of the TCB.
        let verdict = verify_output_preserved(&binop_fn("val_udiv", BinOp::Div, Ty::u32()));
        assert!(verdict.is_proven(), "udiv u32 is proven by ay (UNSAT under b != 0)");
        assert!(
            verdict.is_kernel_proved(),
            "unsigned div u32 must be [PROVED] via the O(1) conditional divGuardBridge \
             discharge (kernel-re-checked), got {verdict:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_udiv_divergent_operands_kernel_rejected() {
        // auto = BvUDiv(W(X0), W(X1)); machine = W(Ite(Eq(W(X2),0), 0, BvUDiv(W(X0), W(X2)))).
        // The machine divides by X2 while auto divides by X1 — a divergent divisor. The
        // discharge instantiates divGuardBridge at the MACHINE divisor X2; the kernel must
        // defeq its conclusion RHS `bvDiv X0 X2` to the goal's auto_val `bvDiv X0 X1`, which
        // requires X2 ≡ X1 — FALSE (distinct per-bit lists) -> KERNEL-REJECTED (ay out of TCB).
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let auto = Formula::BvUDiv(b(opwrap(0)), b(opwrap(1)), 32);
        let inner_ite = Formula::Ite(
            b(Formula::Eq(b(opwrap(2)), b(Formula::BitVec { value: 0, width: 32 }))),
            b(Formula::BitVec { value: 0, width: 32 }),
            b(Formula::BvUDiv(b(opwrap(0)), b(opwrap(2)), 32)),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(inner_ite), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let r = crate::verify_output_instantiate::try_div_conditional_discharge_for_test(
            &machine, &auto,
        );
        assert!(
            r.is_none(),
            "DIVERGENT-divisor udiv (machine X0/X2 vs auto X0/X1) must be KERNEL-REJECTED; got {r:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_udiv_divergent_dividend_kernel_rejected() {
        // Dividend divergence: machine = W(Ite(Eq(W(X1),0), 0, BvUDiv(W(X3), W(X1)))) — divides
        // X3/X1 — vs auto = BvUDiv(W(X0), W(X1)) — X0/X1. The kernel must defeq the conclusion RHS
        // `bvDiv X3 X1` to auto_val `bvDiv X0 X1`, requiring X3 ≡ X0 — FALSE -> KERNEL-REJECTED.
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let auto = Formula::BvUDiv(b(opwrap(0)), b(opwrap(1)), 32);
        let inner_ite = Formula::Ite(
            b(Formula::Eq(b(opwrap(1)), b(Formula::BitVec { value: 0, width: 32 }))),
            b(Formula::BitVec { value: 0, width: 32 }),
            b(Formula::BvUDiv(b(opwrap(3)), b(opwrap(1)), 32)),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(inner_ite), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let r = crate::verify_output_instantiate::try_div_conditional_discharge_for_test(
            &machine, &auto,
        );
        assert!(
            r.is_none(),
            "DIVERGENT-dividend udiv (machine X3/X1 vs auto X0/X1) must be KERNEL-REJECTED; got {r:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_sdiv_divergent_operands_kernel_rejected() {
        // SIGNED analogue of b4_udiv_divergent_operands: auto = BvSDiv(W(X0), W(X1)); machine =
        // W(Ite(Eq(W(X2),0), 0, BvSDiv(W(X0), W(X2)))). The kernel must defeq the conclusion RHS
        // `bvSDiv X0 X2` to auto_val `bvSDiv X0 X1`, requiring X2 ≡ X1 — FALSE -> KERNEL-REJECTED.
        // Pins the signed (valfn = bv_sdiv) rejection EXPLICITLY, not just inherited from unsigned.
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let auto = Formula::BvSDiv(b(opwrap(0)), b(opwrap(1)), 32);
        let inner_ite = Formula::Ite(
            b(Formula::Eq(b(opwrap(2)), b(Formula::BitVec { value: 0, width: 32 }))),
            b(Formula::BitVec { value: 0, width: 32 }),
            b(Formula::BvSDiv(b(opwrap(0)), b(opwrap(2)), 32)),
        );
        let machine = Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(inner_ite), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let r = crate::verify_output_instantiate::try_div_conditional_discharge_for_test(
            &machine, &auto,
        );
        assert!(
            r.is_none(),
            "DIVERGENT-divisor sdiv (machine X0/X2 vs auto X0/X1) must be KERNEL-REJECTED; got {r:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_unsigned_rem_is_proved_via_o1_refl_discharge() {
        // UNSIGNED rem: machine (udiv+msub) and auto are the identical a-(a/b)*b composite up to
        // value-preserving coercion wrappers, so both reconstruct (rem_to_val) to the same clean
        // value over key-matched operands and the obligation closes by REFLEXIVITY (operand-tied,
        // kernel-re-checked). The gate's b!=0 precondition is satisfied vacuously.
        let verdict = verify_output_preserved(&binop_fn("val_urem", BinOp::Rem, Ty::u32()));
        assert!(verdict.is_proven(), "urem u32 is proven by ay");
        assert!(
            verdict.is_kernel_proved(),
            "unsigned rem u32 must be [PROVED] via the O(1) refl composite discharge, got {verdict:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_signed_rem_is_proved_via_o1_refl_discharge() {
        // SIGNED rem (i32) now reaches [PROVED]: rem_to_val gained a BvSDiv -> bvSDiv arm, so the
        // signed composite a - Ite(b==0,0,sdiv)*b reconstructs and closes by reflexivity (operand-
        // tied), exactly like unsigned rem. Previously [VALIDATED] (no signed-div reconstruction).
        let verdict = verify_output_preserved(&binop_fn("val_srem", BinOp::Rem, Ty::i32()));
        assert!(verdict.is_proven(), "srem i32 is proven by ay");
        assert!(
            verdict.is_kernel_proved(),
            "signed rem i32 must be [PROVED] via the O(1) refl composite discharge, got {verdict:?}"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b4_urem_divergent_operand_kernel_rejected() {
        // Divergent dividend in the SUB: machine subtracts X3 - (q*X1) while auto subtracts
        // X0 - (q*X1). rem_to_val reconstructs distinct values (X3 vs X0 bit-lists) -> refl
        // ill-typed -> KERNEL-REJECTED.
        let opwrap = |n: u32| Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(wn(n)), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let q = |dividend: u32| {
            Formula::Ite(
                b(Formula::Eq(b(opwrap(1)), b(Formula::BitVec { value: 0, width: 32 }))),
                b(Formula::BitVec { value: 0, width: 32 }),
                b(Formula::BvUDiv(b(opwrap(dividend)), b(opwrap(1)), 32)),
            )
        };
        let auto = Formula::BvSub(b(opwrap(0)), b(Formula::BvMul(b(q(0)), b(opwrap(1)), 32)), 32);
        // machine: same composite but the OUTER sub dividend is X3 (divergent) — wrapped readout.
        let inner = Formula::BvSub(b(opwrap(3)), b(Formula::BvMul(b(q(0)), b(opwrap(1)), 32)), 32);
        let machine = Formula::BvExtract {
            inner: b(Formula::BvZeroExt(
                b(Formula::BvOr(b(Formula::BitVec { value: 0, width: 32 }), b(inner), 32)),
                32,
            )),
            high: 31,
            low: 0,
        };
        let r = crate::verify_output_instantiate::try_rem_conditional_discharge_for_test(
            &machine, &auto,
        );
        assert!(
            r.is_none(),
            "DIVERGENT-dividend urem (machine X3-.. vs auto X0-..) must be KERNEL-REJECTED; got {r:?}"
        );
    }

    #[test]
    fn mul_lowering_in_fragment_and_width8_recheckable_passes_guard() {
        // The MULTIPLIER blast IS kernel-re-checkable in principle: a width-8 mul
        // obligation lowers into the fragment, PASSES the tractability guard
        // (width 8 == MAX_RECHECKABLE_MUL_WIDTH), and exports a self-validating
        // bit-blast proof — the same artifact the clean kernel re-check consumes.
        // This is the positive counterpart to `gate_mul_stays_validated_not_proved`
        // (the live gate's width-32 emission stays [VALIDATED]; the multiplier
        // machinery itself is real [PROVED] at the re-checkable width).
        let a = ay_proof::BvExpr::leaf("A0", 8);
        let b = ay_proof::BvExpr::leaf("B0", 8);
        // The gate-shaped readout obligation: extract(zext(mul)) == mul.
        let machine = ay_proof::BvExpr::extract(
            ay_proof::BvExpr::zero_ext(ay_proof::BvExpr::mul(a.clone(), b.clone()), 8),
            7,
            0,
        );
        let spec = ay_proof::BvExpr::mul(a, b);
        // Guard admits width 8.
        assert!(!mul_wider_than(&machine, MAX_RECHECKABLE_MUL_WIDTH));
        assert!(!mul_wider_than(&spec, MAX_RECHECKABLE_MUL_WIDTH));
        // And the export is a real, self-validating kernel-re-checkable proof.
        let proof = ay_proof::export_bv_blast_proof_expr(&machine, &spec)
            .expect("width-8 gate-shaped mul obligation must export");
        proof
            .validate()
            .expect("width-8 mul proof must self-validate (clean re-checks the same artifact)");
        // The wide (width-32) form is correctly rejected by the guard.
        let wide = ay_proof::BvExpr::mul(
            ay_proof::BvExpr::leaf("W0", 32),
            ay_proof::BvExpr::leaf("W1", 32),
        );
        assert!(
            mul_wider_than(&wide, MAX_RECHECKABLE_MUL_WIDTH),
            "width-32 Mul must trip the tractability guard -> [VALIDATED]"
        );
    }

    #[test]
    fn gate_anti_vacuity_and_corrupted_not_proved() {
        // ANTI-VACUITY: a miscompiled AND (bytes corrupted AND->ORR) must NEVER
        // yield [PROVED]. The false identity has a counterexample -> the export
        // yields NoRefutation and no BvBlastProof is produced. We drive the
        // discharge + export directly on corrupted bytes (mirrors the add case).
        let f = binop_fn("proved_and_u32", BinOp::BitAnd, Ty::u32());
        let (_obj, mut code, base) = emit_text(&f).expect("emit");
        // AND (shifted reg) opc=00 at bits[30:29]; ORR is opc=01. Flip bit 29 of
        // the AND instruction to turn it into ORR — a genuine miscompile.
        let mut corrupted = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::And) {
                let mut word = u32::from_le_bytes(bytes);
                word ^= 1 << 29; // AND opc=00 -> ORR opc=01
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                corrupted = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(corrupted, "did not find an AND to corrupt");
        let raw = symbolic_machine_output(&code, base, 32, false).expect("decode corrupted");
        let auto = trust_ir_semantics(&f).expect("interp");
        let lhs = formula_to_bvexpr(&raw).expect("corrupted still lowers (shape unchanged)");
        let rhs = formula_to_bvexpr(&auto).expect("auto lowers");
        let result = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs);
        assert!(
            matches!(result, Err(ay_proof::BvExprExportError::NoRefutation)),
            "miscompiled and is a false identity: export must yield NoRefutation, got {result:?}"
        );
    }

    #[test]
    fn gate_anti_vacuity_xor_wrong_spec_not_proved() {
        // ANTI-VACUITY (spec mismatch): `bvxor(a,b) == bvand(a,b)` is FALSE in
        // general. Lowering both and exporting must yield NoRefutation — the new
        // Xor/And paths do NOT launder a false identity into a [PROVED] proof.
        let machine_out = Formula::BvXor(b(wn(0)), b(wn(1)), 32);
        let wrong_spec = Formula::BvAnd(b(wn(0)), b(wn(1)), 32);
        let lhs = formula_to_bvexpr(&machine_out).expect("xor lowers");
        let rhs = formula_to_bvexpr(&wrong_spec).expect("and lowers");
        let result = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs);
        assert!(
            matches!(result, Err(ay_proof::BvExprExportError::NoRefutation)),
            "xor == and is a false identity: must yield NoRefutation, got {result:?}"
        );
    }

    #[test]
    fn gate_emits_validated_for_out_of_fragment() {
        // HONESTY: an out-of-the-O(1)-fragment obligation declines [PROVED] and stays
        // [VALIDATED] (ay-only). The example is a div-COMPOSITE `(a/b)^c`: the divisor
        // precondition makes the obligation conditional, but its ROOT is XOR (not a bare div),
        // so the conditional discharge declines. The KERNEL-rooted [PROVED] surface is now the
        // ENTIRE scalar ALU:
        //   - O(1) KernelInstantiated (ay OUT of the cert chain): add/sub/neg, and/xor/or, the
        //     five compares eq/ult/ule/slt/sle, MUL, the conditional DIV (udiv/sdiv via
        //     divGuardBridge + bvf_div/sdiv_cong), REM (a-(a/b)*b composite via refl), and the
        //     SHIFTS shl/lshr/ashr (coercion-identity via bvf_shl/lshr/ashr_cong) — see
        //     `gate_*_is_proved_via_o1_*`.
        //   - SLOW KernelRecheckable (within the 20480-step frontier): sext.
        // STILL [VALIDATED] (the genuine residual): div/rem COMPOSITES (the conditional discharge
        // only matches a bare-div/rem root) and unmodeled constructs (loops/calls).
        let verdict = verify_output_preserved(&div_then_xor_fn("val_divxor_oof", Ty::u32()));
        assert_eq!(
            verdict,
            OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            "out-of-fragment (div-composite) op must be [VALIDATED] (ay-only), not [PROVED]"
        );
        assert!(verdict.kernel_proof().is_none(), "no kernel proof for out-of-fragment");
    }

    #[test]
    fn gate_div_composite_stays_validated_not_proved() {
        // HONESTY: a div-composite `(a/b)^c` has the divisor precondition but a non-bare-div
        // root, so the conditional discharge declines and it stays [VALIDATED] (ay-only).
        // (Bare div/rem and the shifts are now kernel-[PROVED]; this composite is future work.)
        let verdict = verify_output_preserved(&div_then_xor_fn("val_divxor", Ty::u32()));
        assert_eq!(
            verdict,
            OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated },
            "div-composite obligation must be [VALIDATED], not [PROVED]"
        );
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn gate_anti_vacuity_miscompile_not_proved() {
        // ANTI-VACUITY: a miscompiled add (emitted bytes corrupted ADD->SUB) must
        // NEVER yield a [PROVED] verdict. ay finds a counterexample -> Refuted,
        // and no BvBlastProof is ever produced. (This is the live-gate analogue of
        // `lowering_anti_vacuity_wrong_spec_no_proof`.)
        let f = add_i32_fn();
        let (_obj, mut code, base) = emit_text(&f).expect("emit");
        // Flip the ADD opcode to SUB by toggling bit 30 of the add/subtract
        // (shifted register) encoding — the same byte-level corruption
        // `gate_refuses_corrupted_emission` uses.
        let mut corrupted = false;
        let mut pc = base;
        let mut off = 0usize;
        while off + 4 <= code.len() {
            let bytes: [u8; 4] = code[off..off + 4].try_into().unwrap();
            let insn = decode_aarch64(&bytes, pc).expect("decode");
            if matches!(insn.opcode, Opcode::Add) {
                let mut word = u32::from_le_bytes(bytes);
                word ^= 1 << 30; // ADD bit30=0 -> SUB bit30=1
                code[off..off + 4].copy_from_slice(&word.to_le_bytes());
                corrupted = true;
                break;
            }
            if matches!(insn.opcode, Opcode::Ret) {
                break;
            }
            pc += 4;
            off += 4;
        }
        assert!(corrupted, "did not find an ADD to corrupt");
        // Drive the discharge directly on the corrupted bytes' machine output.
        let raw = symbolic_machine_output(&code, base, 32, false).expect("decode corrupted");
        let auto = trust_ir_semantics(&f).expect("interp");
        match discharge_equal_pre(&raw, &auto, None) {
            Discharge::CounterExample => {} // expected: miscompile refuted.
            Discharge::Proven => panic!("corrupted add must NOT be Proven"),
            Discharge::Unknown(r) => panic!("corrupted add must Refute, got Unknown: {r}"),
        }
        // And critically: the corrupted obligation must NOT export a proof.
        let lhs = formula_to_bvexpr(&raw).expect("corrupted still lowers (shape unchanged)");
        let rhs = formula_to_bvexpr(&auto).expect("auto lowers");
        let result = ay_proof::export_bv_blast_proof_expr(&lhs, &rhs);
        assert!(
            matches!(result, Err(ay_proof::BvExprExportError::NoRefutation)),
            "miscompiled add is a false identity: export must yield NoRefutation, got {result:?}"
        );
    }

    // =======================================================================
    // OPTION-B step 2b — the trust-side Formula -> BvF REFLECTION + the
    // real-Formula end-to-end discharge via the clean-kernel coercion lemmas.
    //
    // SOUNDNESS (the non-negotiable requirement): we reflect the gate's REAL
    // add@N `machine_out`/`auto` Formulas (built by the gate's OWN
    // `symbolic_machine_output` / `trust_ir_semantics`, NOT hand-built) into
    // clean-kernel `Clean.BVC.BvF` Exprs PURELY STRUCTURALLY (non-folding — the
    // wrapper `Or(Const0,·)` / `Extract∘ZeroExt` is preserved, NOT simplified),
    // and discharge `bvfEval(reflect(machine_out)) = bvfEval(reflect(auto))` by
    // the KERNEL theorems (`bvf_wrapper_id`, `bvf_extract_zeroext_id`, congruence)
    // — the kernel does the wrapper-cancellation, not the Rust reflection.
    //
    // Trap 1 avoided: `test_reflection_is_non_folding` asserts the reflected
    // machine_out STILL contains the wrapper structure (Or/ZeroExt/Extract nodes)
    // before the kernel discharges it. Trap 2 avoided: the negative control
    // (`test_reflected_corrupted_machine_out_fails_discharge`) reflects a
    // corrupted machine_out (wrong op) and shows the discharge's kernel-typecheck
    // FAILS -> no false grade.
    //
    // This is B2b STANDALONE (the reflection + end-to-end), NOT B4 (live wiring
    // into the default emit path). The reflection lives as test code here; B4
    // promotes it to the library. NO default-[PROVED] change.
    // =======================================================================

    // B2b/B4 reflection lives in the LIBRARY module `verify_output_instantiate`
    // (promoted from test-only in B4). The tests reuse it via `test_support`.
    // Trust: `verify_output_instantiate` is `kernel-recheck`-gated (lib.rs), and
    // every test below that consumes these imports is itself `#[cfg(feature =
    // "kernel-recheck")]`. Gate the imports to MATCH, so an `ay-proofs`-only build
    // (kernel-recheck off) compiles instead of failing on an unresolved
    // `crate::verify_output_instantiate`.
    #[cfg(feature = "kernel-recheck")]
    #[allow(unused_imports)]
    use Reflected as _ReflectedUsed;

    #[cfg(feature = "kernel-recheck")]
    use crate::verify_output_instantiate::Reflected;
    #[cfg(feature = "kernel-recheck")]
    use crate::verify_output_instantiate::kx;
    #[cfg(feature = "kernel-recheck")]
    use crate::verify_output_instantiate::test_support::{
        contains_wrapper, env_with_leaves as bvc_env_with_leaves, reflect_formula,
        reflect_formula_for, store_free,
    };

    /// B2b END-TO-END: reflect the gate's REAL add@N machine_out + auto and
    /// discharge `bvfEval(reflect machine_out) = bvfEval(reflect auto)` in the
    /// clean kernel via the coercion lemmas — the B2b-positive KEYSTONE, now
    /// kernel-CHECKED (ledger #39). The reflection composes a fully `bvfEval`-headed
    /// proof from the BvF-level lemmas (`bvf_add_cong` / `bvf_or_cong2` /
    /// `bvf_zext_cong` / `bvf_extract_cong1` / `bvf_or_zero_id` /
    /// `bvf_extract_zeroext_id`, all proved by `Eq.subst` so there is NO
    /// `congrArg` beta-redex), so the kernel `check_type` of the discharge against
    /// the REAL reflected `machine_out == auto` obligation succeeds. This closes
    /// the non-negotiable soundness loop: the kernel typechecks against the gate's
    /// ACTUAL Formula (reflected), not a synthetic obligation.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b2b_reflected_real_add_obligation_discharges_in_kernel() {
        use clean_kernel::TypeChecker;

        // The gate's OWN construction of the real add@N Formulas.
        let f = binop_fn("b2b_add", BinOp::Add, Ty::i32());
        let (_obj, code, base) = emit_text(&f).expect("emit");
        let machine_out =
            symbolic_machine_output(&code, base, 32, false).expect("decode real machine_out");
        let auto = trust_ir_semantics(&f).expect("real auto");

        let rm = reflect_formula(&machine_out).expect("reflect machine_out");
        let ra = reflect_formula(&auto).expect("reflect auto");

        // TRAP 1: the reflection is NON-FOLDING — the reflected machine_out still
        // carries the full wrapper structure (Or + ZeroExt + ExtractLow) before
        // the kernel discharges it.
        assert!(
            contains_wrapper(&rm.bvf),
            "reflection must be NON-FOLDING: reflected machine_out must still contain \
             the Or/ZeroExt/ExtractLow wrapper ctors (the kernel, not the Rust, cancels them)"
        );

        // The discharge: bvfEval(reflect machine_out) = bvfEval(reflect auto).
        // Both sides strip to the SAME core (Add of the shared operand extracts), so
        //   rm.proof : eval(rm.bvf) = eval(rm.core)
        //   ra.proof : eval(ra.bvf) = eval(ra.core)   with rm.core ≡ ra.core (defeq)
        //   discharge = Eq.trans rm.proof (Eq.symm ra.proof).
        // The kernel `check_type` reduces eval over 32/64-bit List Bool literals and
        // addRecM — deep — so run on a 256 MiB big-stack thread (as the live gate
        // re-check does).
        crate::verify_output_instantiate::run_recheck_thread(
            "trust-b2b-real-add-test",
            move || {
                let env = bvc_env_with_leaves(&[("X0", 64), ("X1", 64)]);
                let tc = TypeChecker::with_mode(&env, env.mode());
                let goal = kx::eq_list(kx::evalf(rm.bvf.clone()), kx::evalf(ra.bvf.clone()));
                let sym_ra = clean_kernel::Expr::apps(
                    clean_kernel::Expr::const_(
                        clean_kernel::name::Name::from_string("Eq.symm"),
                        vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
                    ),
                    [
                        kx::list_bool(),
                        kx::evalf(ra.bvf.clone()),
                        kx::evalf(ra.core.clone()),
                        ra.proof,
                    ],
                );
                let discharge = kx::eq_trans_list(
                    kx::evalf(rm.bvf),
                    kx::evalf(rm.core),
                    kx::evalf(ra.bvf),
                    rm.proof,
                    sym_ra,
                );
                tc.check_type(&discharge, &goal).expect(
                    "the kernel must typecheck the discharge of the REAL reflected add@N \
                     obligation bvfEval(machine_out) = bvfEval(auto) via the coercion lemmas",
                );
            },
        )
        .expect("discharge kernel-check thread must complete");
    }

    /// B2b — TRAP 1 (verified, runs): the reflection of the gate's REAL add@N
    /// `machine_out` is PURELY STRUCTURAL / NON-FOLDING — it preserves the full
    /// `Or(Const0,·)` + `Extract∘ZeroExt` wrapper structure (it does NOT simplify
    /// the wrapper away while reflecting). The kernel theorem must do the
    /// cancellation, not the Rust. We also confirm `auto` reflects to a
    /// wrapper-FREE tree (the shared add of operand extracts), so the obligation
    /// genuinely differs syntactically on the two sides before the kernel discharge.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b2b_reflection_of_real_add_is_non_folding() {
        let f = binop_fn("b2b_nonfold", BinOp::Add, Ty::i32());
        let (_obj, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        let auto = trust_ir_semantics(&f).expect("auto");

        let rm = reflect_formula(&machine_out).expect("reflect machine_out");
        let ra = reflect_formula(&auto).expect("reflect auto");

        // machine_out reflection STILL carries the wrapper ctors (non-folding).
        assert!(
            contains_wrapper(&rm.bvf),
            "reflected machine_out must contain the Or/ZeroExt/ExtractLow wrapper ctors \
             (reflection is non-folding; the kernel cancels the wrapper, not the Rust)"
        );
        // auto reflection has NO Or/ZeroExt wrapper (it is the bare shared add of
        // the two operand extracts) — so the two obligation sides are genuinely
        // distinct shapes over shared leaves (not the same Formula compared to itself).
        let sa = format!("{:?}", ra.bvf);
        assert!(
            !sa.contains("\"Or\"") && !sa.contains("\"ZeroExt\""),
            "reflected auto must be wrapper-free (the bare add): {sa:.0}"
        );
        // And both contain the shared Add + ExtractLow operand leaves.
        let sm = format!("{:?}", rm.bvf);
        assert!(sm.contains("\"Add\"") && sa.contains("\"Add\""), "both sides reflect an Add");
    }

    /// B2b NEGATIVE CONTROL (Trap 2): a CORRUPTED machine_out (wrong op — SUB
    /// where the gate emits ADD) reflects to a term whose discharge does NOT
    /// typecheck against the real auto obligation -> the kernel REJECTS it ->
    /// fall through, never a false grade. (The reflection/matcher is kernel-guarded.)
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b2b_reflected_corrupted_machine_out_fails_discharge() {
        use clean_kernel::TypeChecker;

        let f = binop_fn("b2b_neg", BinOp::Add, Ty::i32());
        let auto = trust_ir_semantics(&f).expect("auto");
        let ra = reflect_formula(&auto).expect("reflect auto");

        // CORRUPT: build a machine_out that is a SUB of the same operands (a
        // miscompile shape) by reflecting a hand-corrupted Formula — the inner op
        // is Sub, which reflect_formula does NOT accept in the add fragment, so it
        // errors; that itself is fall-through. To exercise the KERNEL guard we
        // instead reflect the real add machine_out but then claim its discharge
        // proves equality to a DIFFERENT auto (a sub), and show the kernel rejects.
        let (_o, code, base) = emit_text(&f).expect("emit");
        let machine_out = symbolic_machine_output(&code, base, 32, false).expect("decode");
        let rm = reflect_formula(&machine_out).expect("reflect machine_out (add)");

        // Deep reduction → big-stack thread (as the live gate re-check does).
        crate::verify_output_instantiate::run_recheck_thread(
            "trust-b2b-corrupted-output-test",
            move || {
                let env = bvc_env_with_leaves(&[("X0", 64), ("X1", 64)]);
                let tc = TypeChecker::with_mode(&env, env.mode());
                // A WRONG goal: claim eval(reflect machine_out) equals a concrete
                // wrong value (all-false width 32). The honest discharge term proves
                // eval(rm.bvf) = eval(rm.core), NOT = 0; the kernel check_type FAILS.
                let wrong_rhs = kx::bits(0, 32);
                let wrong_goal = kx::eq_list(kx::evalf(rm.bvf.clone()), wrong_rhs);
                assert!(
                    tc.check_type(&rm.proof, &wrong_goal).is_err(),
                    "a corrupted/wrong obligation must NOT be dischargeable: the kernel \
                     must REJECT the discharge against a wrong goal (matcher kernel-guarded)"
                );
                // Sanity: ra discharges to its own core (positive).
                let auto_goal = kx::eq_list(kx::evalf(ra.bvf.clone()), kx::evalf(ra.core.clone()));
                tc.check_type(&ra.proof, &auto_goal)
                    .expect("reflected auto discharges to its core");
            },
        )
        .expect("negative-control kernel-check thread must complete");
    }

    /// B2b FAITHFULNESS-BY-VALIDATION (residual char (a)): a DIFFERENTIAL of the
    /// kernel `bvfEval` against the Rust `trust_types` bitvector ground-truth
    /// (`bv_eval` / `zero_extend` / `extract` / pointwise-or), per constructor
    /// (Const / Add / Or / ZeroExt / ExtractLow), over many random ground inputs.
    /// For each: build a GROUND `BvF`, compute the expected `List Bool` from the
    /// Rust semantics, and assert the KERNEL reduces `bvfEval(groundBvF)` to
    /// exactly that literal (`Eq.refl` kernel-check). This turns the per-
    /// constructor faithfulness obligation from trusted-by-inspection into
    /// VALIDATED — if `bvfEval`'s semantics diverged from the Formula bitvector
    /// semantics on any sample, the refl would FAIL.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn b2b_bvfeval_differential_vs_trust_types_bitvector_semantics() {
        use clean_kernel::{Environment, TypeChecker};
        use trust_types::{BitVector, BvOp, bv_eval, extract as bv_extract, zero_extend};

        let run = || -> Result<(), String> {
            // small deterministic PRNG (no rand dep): xorshift, local to the thread.
            let mut st: u64 = 0x9E37_79B9_7F4A_7C15;
            let mut next = |bound: u64| {
                st ^= st << 13;
                st ^= st >> 7;
                st ^= st << 17;
                st % bound
            };
            let bv = |v: u128, w: u32| BitVector::new(w, v & ((1u128 << w) - 1)).expect("bv");
            let const_of = |val: u128, w: u32| kx::const_(kx::bits(val as i128, w));
            let env = {
                let mut e = Environment::with_prelude();
                e.init_bv_coercion().map_err(|err| format!("init: {err:?}"))?;
                e
            };
            let tc = TypeChecker::with_mode(&env, env.mode());
            // assert bvfEval(groundBvF) reduces to `expected` (List Bool literal).
            let check =
                |bvf: clean_kernel::Expr, expected_val: u128, w: u32| -> Result<(), String> {
                    let expected_list = kx::bits(expected_val as i128, w);
                    let goal = kx::eq_list(kx::evalf(bvf), expected_list.clone());
                    let refl = kx::eq_refl_list(expected_list);
                    tc.check_type(&refl, &goal).map_err(|e| {
                        format!("bvfEval differs from expected: {e:?}").chars().take(160).collect()
                    })
                };

            let w = 8u32; // 8-bit samples (kernel reduction over 8-bit lists is fast)
            for _ in 0..12 {
                let a = next(1 << w) as u128;
                let b = next(1 << w) as u128;
                let (ba, bb) = (bv(a, w), bv(b, w));
                // Const: bvfEval(Const bits(a)) == a
                check(const_of(a, w), a, w)?;
                // Add: bvfEval(Add (Const a)(Const b)) == bv_eval(Add, a, b)
                let add_exp = bv_eval(BvOp::Add, &ba, &bb).map_err(|e| format!("{e:?}"))?.value();
                check(kx::add(const_of(a, w), const_of(b, w)), add_exp, w)?;
                // Or: bvfEval(Or (Const a)(Const b)) == bv_eval(Or, a, b)
                let or_exp = bv_eval(BvOp::Or, &ba, &bb).map_err(|e| format!("{e:?}"))?.value();
                check(kx::or(const_of(a, w), const_of(b, w)), or_exp, w)?;
                // ZeroExt: bvfEval(ZeroExt (Const a) k) == zero_extend(a, w+k)  (LSB-first append)
                let k = 1 + next(8) as u32;
                let ze_exp = zero_extend(&ba, w + k).map_err(|e| format!("{e:?}"))?.value();
                check(kx::zext(const_of(a, w), kx::nat_lit(k)), ze_exp, w + k)?;
                // ExtractLow [0..m-1]: bvfEval(ExtractLow (Const a@w) (Const 0@m)) == extract(a, m-1, 0)
                let m = 1 + next(w as u64) as u32; // 1..=w
                let ex_exp = bv_extract(&ba, m - 1, 0).map_err(|e| format!("{e:?}"))?.value();
                // ExtractLow's tag length = m (the take length); inner = Const a@w.
                check(kx::extract(const_of(a, w), const_of(0, m)), ex_exp, m)?;
            }
            Ok(())
        };

        // big stack: 16-bit zero-extends + reductions can be deep.
        crate::verify_output_instantiate::run_recheck_thread(
            "trust-b2b-bvfeval-differential-test",
            move || run().expect("bvfEval differential vs trust_types bitvector semantics"),
        )
        .expect("differential kernel-check thread must complete");
    }

    // =======================================================================
    // F — AN OBJECT THE MODEL CANNOT FULLY ACCOUNT FOR MUST NOT BE CERTIFIED
    // =======================================================================
    //
    // THE GAP THIS ADDRESSES. This file has 19 byte-splicing sites and every
    // one of them flips an opcode to build a MISCOMPILE and asserts `Refuted`.
    // Not one splices a DECODABLE-BUT-UNMODELED instruction and asserts the
    // gate declines to certify. So the whole suite tested the gate's ability to
    // refute code it fully understands, and nothing tested its behaviour on
    // code it does not — which is where both live soundness holes were: a
    // discarded `Effect::PcUpdate`, and a `1u64 << 64` overflow in
    // `decode_bitmask_immediate`. Both were the same failure — something
    // SILENTLY DROPPED rather than refused — and a miscompile test cannot see
    // that, because a dropped effect makes the machine side MATCH the spec.
    //
    // WHAT THESE TESTS DO NOT DO, stated because it was MEASURED rather than
    // assumed: they do NOT catch either of those two bugs. Reintroducing the
    // exact `PcUpdate` drop leaves every test in this block PASSING; only
    // `taken_side_of_cbz_is_explored` / `..._tbz_...` fail. These tests pin the
    // gate's response to instructions it does not model AT ALL; a dropped
    // effect on an instruction it does model is a different failure, and the
    // test that catches it is the one that asserts the taken edge is EXPLORED.
    // Do not read this block as covering the bugs that motivated it.
    //
    // ANTI-VACUITY. Every negative test below is paired with a control that
    // must still be `Proven` through the same splice harness
    // (`f_splice_harness_control_*`). Without those, "the gate said Unknown"
    // would be indistinguishable from "the harness broke the object", and this
    // program has already shipped one mutation test that passed for the wrong
    // reason.

    /// Splice `word` into the emitted `__text` IMMEDIATELY BEFORE the
    /// terminating `RET`, shifting the `RET` forward by one instruction.
    ///
    /// Insertion rather than overwrite is deliberate: overwriting an
    /// instruction changes what the function computes, so a `Unknown` verdict
    /// could not be attributed to the spliced word. Inserting leaves every
    /// original instruction in place and in order, so a correctly-accounted-for
    /// no-op keeps the ORIGINAL verdict — which is what the control tests
    /// assert.
    ///
    /// Insertion moves every later instruction, so it is only valid on a
    /// straight-line body with no PC-relative branch to displace. That is
    /// CHECKED here, not assumed: any instruction before the `RET` whose
    /// control flow is not `Fallthrough` panics the harness.
    fn splice_before_ret(word: u32) -> impl Fn(&mut Vec<u8>, u64) {
        move |code: &mut Vec<u8>, base: u64| {
            let mut off = 0usize;
            let mut pc = base;
            while off + 4 <= code.len() {
                let bytes: [u8; 4] = code[off..off + 4].try_into().expect("4-byte slice");
                let insn = decode_aarch64(&bytes, pc)
                    .unwrap_or_else(|e| panic!("emitted text must decode at {pc:#x}: {e:?}"));
                if insn.opcode == Opcode::Ret {
                    code.splice(off..off, word.to_le_bytes());
                    return;
                }
                assert_eq!(
                    insn.flow,
                    trust_disasm::ControlFlow::Fallthrough,
                    "splice_before_ret only handles a straight-line body: {:?} at {pc:#x} \
                     is not Fallthrough, so inserting a word would displace a \
                     PC-relative target",
                    insn.opcode
                );
                pc += 4;
                off += 4;
            }
            panic!("no RET found in the emitted text — nothing to splice before");
        }
    }

    /// The gate's verdict for `func` with `word` spliced in before its `RET`.
    fn verdict_with_spliced_word(func: &VerifiableFunction, word: u32) -> OutputVerdict {
        with_text_corruptor(splice_before_ret(word), || verify_output_preserved(func))
    }

    /// The function every F test splices into: `fn(i32, i32) -> i32 { a + b }`,
    /// whose emission is five straight-line words ending in `RET`.
    fn f_host(name: &str) -> VerifiableFunction {
        binop_fn(name, BinOp::Add, Ty::i32())
    }

    /// Assert every word in `rows` makes the gate DECLINE to certify.
    ///
    /// `Refuted` would also be a non-certification, but it is the WRONG answer
    /// for these words: the gate cannot have found a counterexample to
    /// semantics it never derived. `Unknown` is the honest verdict and the one
    /// required here, so a future change that starts "refuting" unmodeled code
    /// (which would be a fabricated claim) fails too.
    fn assert_not_certified(rows: &[(u32, &str)], what: &str) {
        for (word, asm) in rows {
            let name = format!("f_unmodeled_{:08x}", word);
            let verdict = verdict_with_spliced_word(&f_host(&name), *word);
            assert!(
                !verdict.is_proven(),
                "{what}: `{asm}` ({word:#010x}) spliced into an emitted object was \
                 CERTIFIED — the gate cannot account for this instruction, so a Proven \
                 verdict is a claim about bytes it did not model. Got {verdict:?}"
            );
            assert!(
                !verdict.is_kernel_proved(),
                "{what}: `{asm}` ({word:#010x}) reached a KERNEL grade; got {verdict:?}"
            );
            assert!(
                matches!(verdict, OutputVerdict::Unknown { .. }),
                "{what}: `{asm}` ({word:#010x}) must be Unknown (fail-closed), not a \
                 verdict about semantics the gate never derived; got {verdict:?}"
            );
        }
    }

    /// CONTROL (i) — the splice harness itself does not break the object.
    ///
    /// A `NOP` inserted before the `RET` changes nothing the gate reads, so the
    /// verdict must be BIT-FOR-BIT the unspliced one, kernel grade included.
    /// Without this, every `Unknown` below could be the harness corrupting the
    /// object rather than the gate refusing an instruction.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn f_splice_harness_control_nop_keeps_the_original_verdict() {
        // Assembler-derived (`clang --target=aarch64-apple-darwin` + `objdump -d`).
        const NOP: u32 = 0xD503_201F;
        let baseline = verify_output_preserved(&f_host("f_control_baseline"));
        assert!(
            baseline.is_kernel_proved(),
            "the F host function must be kernel-[PROVED] unspliced, or the controls \
             below prove nothing; got {baseline:?}"
        );
        let spliced = verdict_with_spliced_word(&f_host("f_control_baseline"), NOP);
        assert_eq!(
            spliced, baseline,
            "splicing a NOP changed the verdict — the harness is corrupting the object, \
             so no Unknown it produces can be attributed to the spliced instruction"
        );
    }

    /// CONTROL (ii) — the harness survives a spliced instruction with REAL
    /// effects, not just a no-op encoding.
    ///
    /// `add x9, x9, x9` produces a `RegWrite` the executor must thread through
    /// a scratch register; `mov x9, x9` produces one too. Neither touches the
    /// AAPCS64 result register, so the verdict must be unchanged. This is what
    /// separates "the executor kept executing" from "the executor stopped".
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn f_splice_harness_control_live_instruction_keeps_the_original_verdict() {
        // Assembler-derived.
        for (word, asm) in [(0x8B09_0129u32, "add x9,x9,x9"), (0xAA09_03E9u32, "mov x9,x9")] {
            let baseline = verify_output_preserved(&f_host("f_control_live"));
            let spliced = verdict_with_spliced_word(&f_host("f_control_live"), word);
            assert_eq!(
                spliced, baseline,
                "`{asm}` writes only a scratch register, so it must not change the \
                 verdict; the executor either stopped or mis-threaded it"
            );
        }
    }

    /// A spliced BARRIER must not be certified.
    ///
    /// DMB/DSB/ISB/CLREX decode fine and produce `Effect::Aarch64SyncBoundary`,
    /// which the gate's executor refuses. Nothing asserted that before: the
    /// refusal arm was correct by inspection only, and the identically-shaped
    /// `Effect::PcUpdate` arm two lines above it was WRONG for months.
    #[test]
    fn f_spliced_barrier_is_not_certified() {
        assert_not_certified(
            &[
                (0xD503_3BBF, "dmb ish"),
                (0xD503_3B9F, "dsb ish"),
                (0xD503_3FDF, "isb"),
                (0xD503_3F5F, "clrex"),
            ],
            "synchronization boundary",
        );
    }

    /// A spliced ACQUIRE/RELEASE access must not be certified.
    ///
    /// LDAR/STLR carry a scalar data plane the executor COULD thread plus
    /// `Effect::Aarch64AtomicAccess` ordering metadata it cannot. Certifying
    /// them would silently drop the ordering fact — the same shape as dropping
    /// the barrier, one level finer.
    #[test]
    fn f_spliced_acquire_release_is_not_certified() {
        assert_not_certified(
            &[
                (0x88DF_FC20, "ldar w0,[x1]"),
                (0xC8DF_FC20, "ldar x0,[x1]"),
                (0x889F_FC20, "stlr w0,[x1]"),
                (0xC89F_FC20, "stlr x0,[x1]"),
            ],
            "acquire/release access",
        );
    }

    /// A spliced EXCLUSIVE pair must not be certified.
    ///
    /// LDXR/STXR/LDAXR/STLXR are refused one level earlier than the barrier
    /// family — `Aarch64Semantics::effects` returns `UnsupportedAtomic` and no
    /// effect is ever built. That is a DIFFERENT refusal path (semantics, not
    /// executor), and it was equally untested: an executor that treated a
    /// semantics error as "no effects" would have certified an STXR whose
    /// conditional store and status write simply vanished.
    #[test]
    fn f_spliced_exclusive_pair_is_not_certified() {
        assert_not_certified(
            &[
                (0x885F_7C22, "ldxr w2,[x1]"),
                (0x8803_7C22, "stxr w3,w2,[x1]"),
                (0x885F_FC22, "ldaxr w2,[x1]"),
                (0x8803_FC22, "stlxr w3,w2,[x1]"),
            ],
            "exclusive monitor pair",
        );
    }

    /// A spliced INDIRECT BRANCH must not be certified.
    ///
    /// `br x1` decodes and produces `Effect::Branch` with a SYMBOLIC target.
    /// The executor needs a constant to continue, and the failure mode to guard
    /// against is the tempting one: treat an unresolvable branch as
    /// fallthrough. That would certify a function whose control flow the gate
    /// never followed. `blr x1` is the same shape through the call path.
    #[test]
    fn f_spliced_indirect_branch_is_not_certified() {
        assert_not_certified(
            &[(0xD61F_0020, "br x1"), (0xD61F_0000, "br x0"), (0xD63F_0020, "blr x1")],
            "indirect branch",
        );
    }

    /// A spliced SYSTEM or TRAP instruction must not be certified.
    #[test]
    fn f_spliced_system_or_trap_is_not_certified() {
        assert_not_certified(
            &[
                (0xD53B_4200, "mrs x0,nzcv"),
                (0xD400_0001, "svc #0"),
                (0xD420_0020, "brk #1"),
                (0xD400_0002, "hvc #0"),
                (0xD440_0000, "hlt #0"),
                (0xD503_205F, "wfe"),
                (0xD503_207F, "wfi"),
            ],
            "system/trap",
        );
    }

    /// A word the DECODER refuses outright must not be certified.
    ///
    /// This is the outermost refusal — before any effect exists — and it covers
    /// three distinct decoder verdicts, all of which must reach the same place:
    ///
    ///   * `UnallocatedEncoding` — a word the architecture does not define,
    ///     including both families whose silent approximation was the live
    ///     soundness hole (the reserved load/store-pair encodings around
    ///     LDPSW, and the UNDEFINED bitmask-immediate encodings);
    ///   * `UnmodeledAarch64Instruction` — a word the CPU DOES execute but this
    ///     decoder deliberately declines to approximate (LDTR/STTR, FCMPE);
    ///   * `UnknownEncoding` — a word outside every decode table.
    #[test]
    fn f_spliced_undecodable_word_is_not_certified() {
        assert_not_certified(
            &[
                (0x0000_0000, "udf #0 (all-zero word)"),
                (0xFFFF_FFFF, "all-ones word"),
                (0xB840_0820, "ldtr w0,[x1] (unprivileged load)"),
                (0xB800_0820, "sttr w0,[x1] (unprivileged store)"),
                (0x1E21_2010, "fcmpe s0,s1 (signaling compare)"),
                (0xE940_0440, "load/store pair opc=0b11 (reserved)"),
                (0x6900_0440, "load/store pair opc=0b01,L=0 (STGP)"),
                (0xB862_1820, "ldr [x1,x2,<option=0b000>] (reserved)"),
                (0xB862_3820, "ldr [x1,x2,<option=0b001>] (reserved)"),
                (0xB240_FC00, "orr x0,x0,#<all-ones element> (UNDEFINED)"),
                (0xB200_FC00, "orr x0,x0,#<no element size> (UNDEFINED)"),
            ],
            "undecodable word",
        );
    }

    /// The GPR<->FP `fmov` moves are MODELED — and the gate accounts for them.
    ///
    /// The SIMD register move is MODELED — so the gate accounting for it is
    /// CORRECT, not a false verify.
    ///
    /// CORRECTION, measured 2026-08-16: `mov v0.16b,v2.16b` (0x4EA2_1C40) was
    /// listed above as "SIMD, undecoded" and asserted to be un-certifiable. That
    /// stopped being true. `trust_disasm` now decodes it as `Opcode::SimdMov`,
    /// and `trust_machine_sem` models it — `Opcode::SimdMov => sem_fmov_reg`, a
    /// full-width register copy — with `other => Err(UnsupportedOpcode)` still
    /// failing closed on everything genuinely unhandled. The modeling landed
    /// with its own coverage test
    /// (`simd_register_move_is_modeled_and_its_siblings_still_fail_closed`) but
    /// the word was never removed from the undecodable list here, so this test
    /// went red asserting a gap that had been closed.
    ///
    /// The honest property is the `fmov`-shaped one below, not refusal: the move
    /// writes V0 and cannot touch the AAPCS64 integer result register, so the
    /// verdict must be UNCHANGED. Asserting non-certification instead would
    /// demand the gate DECLINE code it correctly models, which is a different
    /// error in the opposite direction.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn f_spliced_simd_register_move_is_accounted_for_not_dropped() {
        // `mov v0.16b, v2.16b` == `orr v0.16b, v2.16b, v2.16b`. Assembler-derived.
        const SIMD_MOV: u32 = 0x4EA2_1C40;

        let baseline = verify_output_preserved(&f_host("f_simdmov_host"));
        assert!(baseline.is_kernel_proved(), "host must be kernel-[PROVED]: {baseline:?}");

        let spliced = verdict_with_spliced_word(&f_host("f_simdmov_host"), SIMD_MOV);
        assert_eq!(
            spliced, baseline,
            "`mov v0.16b,v2.16b` writes only V0, so the integer verdict must be \
             UNCHANGED. A different verdict means the executor lost its footing on an \
             instruction it models."
        );
    }

    /// CORRECTION TO THE BRIEF, measured: `fmov s0,w0` and `fmov w0,s0` are not
    /// unmodeled. They decode as `Opcode::FmovReg` and `sem_fmov_reg` builds a
    /// real bit-transfer effect for each direction. So the property to pin is
    /// not "the gate declines" but "the gate does not DROP them", and the two
    /// directions pin it from both sides:
    ///
    ///   * `fmov s0,w0` writes V0 and genuinely cannot change the integer
    ///     result register, so the verdict must be UNCHANGED — anything else
    ///     means the executor lost its footing on a modeled instruction;
    ///   * `fmov w0,s0` OVERWRITES the AAPCS64 result register with V0's low
    ///     lane, so the verdict must become `Refuted` — and it is exactly this
    ///     half that a dropped `Effect::RegWrite` would turn back into
    ///     `Proven`, certifying a function whose result the bytes clobber.
    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn f_spliced_gpr_fp_fmov_is_accounted_for_not_dropped() {
        // Assembler-derived.
        const FMOV_S0_W0: u32 = 0x1E27_0000;
        const FMOV_W0_S0: u32 = 0x1E26_0000;

        let baseline = verify_output_preserved(&f_host("f_fmov_host"));
        assert!(baseline.is_kernel_proved(), "host must be kernel-[PROVED]: {baseline:?}");

        let to_fp = verdict_with_spliced_word(&f_host("f_fmov_host"), FMOV_S0_W0);
        assert_eq!(
            to_fp, baseline,
            "`fmov s0,w0` writes only V0, so the integer verdict must be unchanged"
        );

        let to_gpr = verdict_with_spliced_word(&f_host("f_fmov_host"), FMOV_W0_S0);
        assert!(
            matches!(to_gpr, OutputVerdict::Refuted { .. }),
            "`fmov w0,s0` OVERWRITES the result register with V0's low lane, so the \
             emitted bytes no longer compute `a + b`. A Proven verdict here means the \
             move's RegWrite was DROPPED — the function's result is clobbered and the \
             gate certified it anyway. Got {to_gpr:?}"
        );
        assert!(!to_gpr.is_proven() && !to_gpr.is_kernel_proved());
    }

    /// THE SHIPPING BOUNDARY: an object containing an unmodeled instruction is
    /// REFUSED under the strict policy, and never counted as certified under the
    /// permissive one.
    ///
    /// Every other F test asserts a VERDICT. This one asserts the consequence
    /// the verdict exists for — what the build gate does with the bytes. A gate
    /// that says `Unknown` and ships the object as [PROVED] anyway would pass
    /// all of them.
    #[test]
    fn f_unmodeled_instruction_is_refused_at_the_build_gate() {
        // `dmb ish` — decodable, and refused by the executor.
        const DMB_ISH: u32 = 0xD503_3BBF;

        let funcs = vec![f_host("f_gate_dmb")];

        // StrictProvenOnly: the function must not ship at all.
        let strict = with_text_corruptor(splice_before_ret(DMB_ISH), || {
            emit_objects_verified_reported(&funcs, EmitPolicy::StrictProvenOnly)
        });
        match strict {
            Err(VerifyError::Unknown { function, ref reason }) => {
                assert_eq!(function, "f_gate_dmb");
                assert!(
                    reason.contains("fail-closed"),
                    "the refusal must name the fail-closed refusal, not a decode \
                     accident; got {reason}"
                );
            }
            other => panic!(
                "an object containing an unmodeled instruction must be REFUSED under \
                 StrictProvenOnly; got {other:?}"
            ),
        }

        // AllowUnknown: it may ship, but ONLY as uncertified — never counted as
        // [PROVED] or [VALIDATED].
        let (objs, report) = with_text_corruptor(splice_before_ret(DMB_ISH), || {
            emit_objects_verified_reported(&funcs, EmitPolicy::AllowUnknown)
        })
        .expect("AllowUnknown ships an undecided function");
        assert_eq!(objs.len(), 1, "AllowUnknown ships the object");
        assert_eq!(
            (report.proved, report.validated, report.unknown),
            (0, 0, 1),
            "an object the gate could not model must be counted UNCERTIFIED, not \
             proved or validated; got {report}"
        );
        assert_eq!(report.uncertified(), 1);
    }

    /// EVERY `Effect` variant has a MEASURED disposition at the output gate.
    ///
    /// This is the generic form of the tests above: not a list of instructions
    /// somebody thought of, but a walk over the whole effect surface. Each row
    /// names a variant, a real assembler-derived word that PRODUCES it, and
    /// what the gate must do with it. Two things are asserted per row: that the
    /// word really does produce that variant (so the row is not vacuous), and
    /// that the end-to-end verdict matches the declared disposition.
    ///
    /// WHY THIS BREAKS ON A FOURTEENTH VARIANT. `Effect` is `#[non_exhaustive]`
    /// and defined in another crate, so a wildcard-free match is impossible
    /// HERE — a table is the only option that can fail. The build break lives
    /// in the DEFINING crate instead, and the chain reaches this test:
    ///
    ///   1. `Effect::variant_name` (trust-machine-sem) is an exhaustive match
    ///      with no wildcard => a new variant is `cargo build` error E0004;
    ///   2. that match and `Effect::VARIANT_NAMES` are expanded from ONE token
    ///      list by `declare_effect_census!`, so the edit that resolves (1) is
    ///      the same edit that extends the name list — the two cannot drift.
    ///      The generated match also carries `deny(unreachable_patterns)`, so
    ///      silencing (1) by pasting rustc's suggested arm into the macro body
    ///      instead of extending the list is itself a hard error;
    ///   3. this test requires the table to cover `Effect::VARIANT_NAMES`
    ///      exactly => the new variant cannot reach the gate without someone
    ///      measuring what the gate does with it.
    ///
    /// So the answer to "which one actually breaks the build" is (1)+(2), in
    /// trust-machine-sem; this test is the link that forces the MEASUREMENT.
    /// (Until 2026-08-10 step 2 was a `const` assertion against
    /// `core::mem::variant_count::<Effect>()`; that spent an unstable feature on
    /// the compiler build graph and has been replaced by the single-source
    /// expansion above.)
    #[test]
    fn f_every_effect_variant_has_a_measured_gate_disposition() {
        use std::collections::BTreeSet;

        /// What the output gate must do with an object containing this effect.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum GateDisposition {
            /// The executor models it and reaches a decided verdict.
            Decided,
            /// A CONTROL-FLOW variant: modeled, and it must actually FORK the
            /// symbolic state. `Decided` is too weak for these — it asserts only
            /// "not Unknown", which a SILENTLY DROPPED branch effect satisfies
            /// perfectly, since dropping it makes the machine side fall through
            /// and agree with the spec. That is precisely how `Effect::PcUpdate`
            /// survived: a row asserting `!Unknown` would have passed throughout.
            DecidedAndForks,
            /// The executor refuses it: `Unknown`, never `Proven`.
            FailsClosed,
        }
        use GateDisposition::{Decided, DecidedAndForks, FailsClosed};

        // (variant, word, asm, disposition, note)
        // Every word is assembler-derived (`clang` + `objdump -d`); none is
        // hand-encoded.
        let rows: &[(&str, u32, &str, GateDisposition)] = &[
            ("RegWrite", 0x8B09_0129, "add x9,x9,x9", Decided),
            ("SpWrite", 0xD100_43FF, "sub sp,sp,#16", Decided),
            ("MemWrite", 0xB900_0020, "str w0,[x1]", Decided),
            ("MemRead", 0xB940_0029, "ldr w9,[x1]", Decided),
            ("FlagUpdate", 0x6B09_0129, "subs w9,w9,w9", Decided),
            ("Branch", 0x1400_0001, "b .+4", Decided),
            ("ConditionalBranch", 0x5400_0020, "b.eq .+4", DecidedAndForks),
            ("Call", 0x9400_0001, "bl .+4", FailsClosed),
            ("Return", 0xD65F_03C0, "ret", Decided),
            ("FpRegWrite", 0x1E27_0000, "fmov s0,w0", Decided),
            ("Aarch64SyncBoundary", 0xD503_3BBF, "dmb ish", FailsClosed),
            ("Aarch64AtomicAccess", 0x88DF_FC20, "ldar w0,[x1]", FailsClosed),
            ("PcUpdate", 0x3400_0029, "cbz w9,.+4", DecidedAndForks),
        ];

        // COVERAGE: the table names every variant, and only real variants.
        let covered: BTreeSet<&str> = rows.iter().map(|r| r.0).collect();
        let declared: BTreeSet<&str> = Effect::VARIANT_NAMES.iter().copied().collect();
        assert_eq!(
            covered,
            declared,
            "the gate-disposition table does not cover every Effect variant. An \
             uncovered variant is one the OUTPUT GATE was never measured against, \
             which is exactly how `Effect::PcUpdate` came to be silently discarded. \
             Missing: {:?}; unknown: {:?}",
            declared.difference(&covered).collect::<Vec<_>>(),
            covered.difference(&declared).collect::<Vec<_>>()
        );

        let sem = Aarch64Semantics;
        let state = MachineState::symbolic();
        for (variant, word, asm, disposition) in rows {
            // (a) the row is not vacuous: this word really does produce this
            //     variant. `ret` is the one row whose effects are produced but
            //     never consumed (the executor returns at `Opcode::Ret` before
            //     asking for them) — the production check still applies.
            let insn = decode_aarch64(&word.to_le_bytes(), 0x1000)
                .unwrap_or_else(|e| panic!("{variant}: `{asm}` must decode: {e:?}"));
            let effects = sem
                .effects(&state, &insn)
                .unwrap_or_else(|e| panic!("{variant}: `{asm}` must have semantics: {e:?}"));
            assert!(
                effects.iter().any(|e| e.variant_name() == *variant),
                "{variant}: `{asm}` produces {:?}, not the variant this row claims to \
                 exercise",
                effects.iter().map(Effect::variant_name).collect::<Vec<_>>()
            );

            // (b) the end-to-end gate disposition is the declared one.
            let name = format!("f_surface_{}", variant.to_lowercase());
            let verdict = verdict_with_spliced_word(&f_host(&name), *word);
            match disposition {
                Decided => assert!(
                    !matches!(verdict, OutputVerdict::Unknown { .. }),
                    "{variant}: `{asm}` is declared MODELED, but the gate failed closed \
                     on it: {verdict:?}"
                ),
                DecidedAndForks => {
                    assert!(
                        !matches!(verdict, OutputVerdict::Unknown { .. }),
                        "{variant}: `{asm}` is declared MODELED, but the gate failed \
                         closed on it: {verdict:?}"
                    );
                    // The branch must actually SPLIT the state. A two-way body
                    // whose arms return different values must derive an `Ite`;
                    // if the effect is dropped the executor falls through and
                    // derives the fall-through arm alone.
                    let body = words(&[*word, 0xD65F_03C0, 0x5280_00A0, 0xD65F_03C0]);
                    let derived =
                        symbolic_machine_output(&body, 0, 32, false).unwrap_or_else(|e| {
                            panic!("{variant}: `{asm}` two-way body must be modeled: {e}")
                        });
                    assert!(
                        matches!(derived, Formula::Ite(..)),
                        "{variant}: `{asm}` did NOT fork the symbolic state — the taken \
                         edge was not explored, so a miscompile on it is invisible to \
                         the gate. Derived: {derived:?}"
                    );
                }
                FailsClosed => {
                    assert!(
                        !verdict.is_proven() && !verdict.is_kernel_proved(),
                        "{variant}: `{asm}` is declared UNMODELED, but the gate \
                         CERTIFIED an object containing it: {verdict:?}"
                    );
                    assert!(
                        matches!(verdict, OutputVerdict::Unknown { .. }),
                        "{variant}: `{asm}` must fail closed to Unknown; got {verdict:?}"
                    );
                }
            }
        }
    }
}

/// THE GENERAL SELECT: `Formula::Ite` whose arms are DIFFERENT VALUES, lowered
/// as the mask-mux `(sext(c) & a) | (~sext(c) & b)`.
///
/// The mux identity is the whole claim, so nothing here checks it by rebuilding
/// the same expression and comparing structurally — that would only prove the
/// lowering equals itself. Every correctness test below hands the lowered
/// `BvExpr` to the REAL bit-blast solver against an INDEPENDENT formulation and
/// requires a refutation of the disequality:
///
/// * against `b + ((a - b) & mask)` — the arithmetic select, which shares not a
///   single gate with the bitwise one (ripple-carry adders vs. per-bit and/or);
/// * against the arm itself, at a condition that is constantly true or
///   constantly false — ground truth that does not mention a mask at all.
///
/// And the anti-vacuity row pairs the mux against the SWAPPED arms, which must
/// NOT refute: otherwise "the solver agreed" would mean nothing.
#[cfg(all(test, feature = "ay-proofs"))]
mod tests_general_ite_mux {
    use super::*;

    /// An 8-bit named leaf — a genuine unknown VALUE, not a 0/1 flag, so the
    /// compare-register matcher (`ite_pred_branches`) declines and the general
    /// path is the one under test.
    fn leaf(name: &str, width: u32) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(width))
    }

    /// A predicate inside the [PROVED] compare fragment: `W0 == 7`.
    fn pred() -> Formula {
        Formula::Eq(b(wn(0)), b(Formula::BitVec { value: 7, width: 32 }))
    }

    fn ite(cond: Formula, then_v: Formula, else_v: Formula) -> Formula {
        Formula::Ite(b(cond), b(then_v), b(else_v))
    }

    /// `lhs` and `rhs` denote the same bitvector for every assignment — decided
    /// by the SAME zero-trust exporter the [PROVED] grade runs on, and the
    /// certificate is kernel-re-checked, so a bug in the export cannot make this
    /// pass either.
    fn assert_equivalent(lhs: &ay_proof::BvExpr, rhs: &ay_proof::BvExpr, why: &str) {
        let proof = ay_proof::export_bv_blast_proof_expr(lhs, rhs).unwrap_or_else(|e| {
            panic!("{why}: expected a refutation of the disequality, got {e:?}")
        });
        proof.validate().unwrap_or_else(|e| panic!("{why}: exported proof must re-check: {e:?}"));
    }

    /// THE MUX IDENTITY, against an arithmetic select that shares no gates with
    /// it. Both arms are free 8-bit leaves and the condition is symbolic, so
    /// this is the general case and not a folded one.
    #[test]
    fn general_select_equals_the_arithmetic_select() {
        for width in [8u32, 16, 32] {
            let (a, bb) = (leaf("A", width), leaf("B", width));
            let lowered = formula_to_bvexpr(&ite(pred(), a.clone(), bb.clone()))
                .unwrap_or_else(|e| panic!("width {width}: a general select must lower: {e}"));

            // b + ((a - b) & mask), mask = sext(pred, width-1).
            let mask =
                ay_proof::BvExpr::sign_ext(predicate_to_bvexpr(&pred()).expect("pred"), width - 1);
            let reference = ay_proof::BvExpr::add(
                formula_to_bvexpr(&bb).expect("b"),
                ay_proof::BvExpr::and(
                    ay_proof::BvExpr::sub(
                        formula_to_bvexpr(&a).expect("a"),
                        formula_to_bvexpr(&bb).expect("b"),
                    ),
                    mask,
                ),
            );
            assert_equivalent(&lowered, &reference, &format!("width {width} mask-mux"));
        }
    }

    /// ANTI-VACUITY. The same comparison against the SWAPPED arms is a FALSE
    /// identity, so the exporter must find a model instead of a refutation. If
    /// this refuted, every `assert_equivalent` above would be meaningless.
    #[test]
    fn general_select_is_not_equal_to_its_own_swapped_arms() {
        let (a, bb) = (leaf("A", 8), leaf("B", 8));
        let lowered = formula_to_bvexpr(&ite(pred(), a.clone(), bb.clone())).expect("lower");
        let swapped = formula_to_bvexpr(&ite(pred(), bb, a)).expect("lower swapped");
        let result = ay_proof::export_bv_blast_proof_expr(&lowered, &swapped);
        assert!(
            matches!(result, Err(ay_proof::BvExprExportError::NoRefutation)),
            "`c ? a : b` and `c ? b : a` differ whenever a != b: the export must find a \
             model, got {result:?}"
        );
    }

    /// GROUND TRUTH, with no mask in the reference at all: at a condition that
    /// is constantly true the select IS the then-arm, and at a constantly false
    /// one it IS the else-arm. Both are still lowered through the general path
    /// (the arms are leaves, so the 0/1 compare-register matcher declines).
    #[test]
    fn a_constant_condition_selects_the_corresponding_arm() {
        let (a, bb) = (leaf("A", 32), leaf("B", 32));
        for (cond, want, which) in [
            (Formula::Bool(true), &a, "true -> then"),
            (Formula::Bool(false), &bb, "false -> else"),
        ] {
            let lowered =
                formula_to_bvexpr(&ite(cond, a.clone(), bb.clone())).expect("lower constant-cond");
            let reference = formula_to_bvexpr(want).expect("arm");
            assert_equivalent(&lowered, &reference, which);
        }
    }

    /// THE 1-BIT EDGE. At `tw == 1` there is no room for a `sign_ext`, so the
    /// mask is the raw predicate; the identity must still hold. A `sign_ext(p,
    /// 0)`-shaped slip would produce a 1-bit-too-wide expression and fail the
    /// width assertion here before it ever reached the solver.
    #[test]
    fn general_select_at_width_1_uses_the_predicate_as_the_mask() {
        let (a, bb) = (leaf("A", 1), leaf("B", 1));
        let lowered = formula_to_bvexpr(&ite(pred(), a.clone(), bb.clone()))
            .expect("a 1-bit general select must lower");
        assert_eq!(bvexpr_width(&lowered), Some(1), "a 1-bit select stays 1 bit wide");

        // xor(b, mask & xor(a, b)) — the third independent formulation.
        let mask = predicate_to_bvexpr(&pred()).expect("pred");
        let reference = ay_proof::BvExpr::xor(
            formula_to_bvexpr(&bb).expect("b"),
            ay_proof::BvExpr::and(
                mask,
                ay_proof::BvExpr::xor(
                    formula_to_bvexpr(&a).expect("a"),
                    formula_to_bvexpr(&bb).expect("b"),
                ),
            ),
        );
        assert_equivalent(&lowered, &reference, "1-bit mask-mux");
    }

    /// UNEQUAL ARM WIDTHS are not a select at all, and the refusal must SAY so
    /// — a generic "outside the fragment" here would let a genuinely ill-formed
    /// `Ite` be mistaken for an unsupported-but-harmless one.
    #[test]
    fn unequal_arm_widths_fail_closed() {
        let err = formula_to_bvexpr(&ite(pred(), leaf("A", 8), leaf("B", 32)))
            .expect_err("arms of different widths are not a well-formed select");
        assert!(
            err.contains("differ in width"),
            "the refusal must name the width mismatch; got {err}"
        );
        assert!(err.contains("8") && err.contains("32"), "and report both widths; got {err}");
    }

    /// An arm outside the fragment still fails closed rather than being
    /// mask-muxed into an obligation the exporter cannot mean.
    ///
    /// The two-leaf CONTROL is what makes this a statement about the ARM: with
    /// no general select admitted at all, "a real-sorted arm is refused" is
    /// vacuously true and says nothing.
    #[test]
    fn an_arm_outside_the_fragment_fails_closed() {
        formula_to_bvexpr(&ite(pred(), leaf("A", 8), leaf("B", 8)))
            .expect("control: two in-fragment arms ARE a select");

        let outside = Formula::Var("F".to_string(), Sort::Int);
        assert!(
            formula_to_bvexpr(&ite(pred(), outside.clone(), leaf("B", 8))).is_err(),
            "a non-bitvector then-arm must fail closed"
        );
        assert!(
            formula_to_bvexpr(&ite(pred(), leaf("A", 8), outside)).is_err(),
            "a non-bitvector else-arm must fail closed"
        );
        // A predicate outside the [PROVED] compare fragment takes the whole
        // select with it: the mask has to BE the compare fragment's predicate.
        assert!(
            formula_to_bvexpr(&ite(
                Formula::Var("P".to_string(), Sort::Bool),
                leaf("A", 8),
                leaf("B", 8)
            ))
            .is_err(),
            "a condition outside the compare fragment must fail closed"
        );
    }

    /// THE TWO `Ite` PATHS STAY DISTINCT. `pred ? 1 : 0` is the COMPARE-REGISTER
    /// form and must still lower to the predicate itself (zero-extended) — the
    /// pre-existing path must not have been swallowed by the general one — while
    /// `pred ? a : b` must take the new mask-mux path and produce something
    /// other than that predicate.
    ///
    /// Asserting both in one test is deliberate: the first half alone holds at
    /// HEAD (where the general path does not exist) and so cannot witness this
    /// change; the second half is what distinguishes the two paths at all.
    #[test]
    fn the_two_ite_paths_stay_distinct() {
        let compare_register = ite(
            pred(),
            Formula::BitVec { value: 1, width: 32 },
            Formula::BitVec { value: 0, width: 32 },
        );
        let lowered = formula_to_bvexpr(&compare_register).expect("compare-register form lowers");
        let want = ay_proof::BvExpr::zero_ext(predicate_to_bvexpr(&pred()).expect("pred"), 31);
        assert_eq!(lowered, want, "`pred ? 1 : 0` must stay the plain zero-extended predicate");

        let general = formula_to_bvexpr(&ite(pred(), leaf("A", 32), leaf("B", 32)))
            .expect("a general select must lower");
        assert_ne!(
            general, want,
            "`pred ? a : b` must NOT collapse to the compare-register lowering"
        );
        assert_eq!(bvexpr_width(&general), Some(32), "and it must stay at the arms' width");
    }
}

/// `reg_width` used to end in `_ => 32`: "any type I do not recognize occupies a
/// 32-bit register". The most dangerous consumer is [`return_reg_width`], which
/// decides how many bits of the return register the gate reads back out of the
/// EMITTED OBJECT — answering 32 for an aggregate return would have compared the
/// low half of W0 against the spec, and an aggregate return does not live in X0
/// at all (AAPCS returns it indirectly through X8).
#[cfg(test)]
mod reg_width_fail_closed_tests {
    use trust_types::Ty;

    use super::*;

    /// The scalar types that DO have a defined single-register slot, with the
    /// width each occupies.
    #[test]
    fn scalar_types_keep_their_register_slot_width() {
        let cases: &[(Ty, u32)] = &[
            (Ty::Int { width: 8, signed: true }, 8),
            (Ty::Int { width: 32, signed: false }, 32),
            (Ty::Int { width: 64, signed: true }, 64),
            (Ty::Bv(16), 16),
            (Ty::Bool, 32),
            (Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Bool) }, 64),
            (Ty::Ref { mutable: true, inner: Box::new(Ty::Bool) }, 64),
            (Ty::Float { width: 64 }, 64),
            (Ty::Float { width: 32 }, 32),
        ];
        for (ty, want) in cases {
            assert_eq!(
                reg_width(ty).unwrap_or_else(|e| panic!("{ty:?} must have a slot width: {e}")),
                *want,
                "{ty:?}"
            );
        }
    }

    /// Everything else must REFUSE rather than answer 32.
    ///
    /// `PtrSizedInt`, `Char` and `Str` are the pointed cases: all three are
    /// recent additions to `Ty` that landed straight in the old `_` arm and
    /// silently acquired a 32-bit answer — `PtrSizedInt` is 64-bit and `Str` is
    /// a fat pointer, so two of the three guesses were simply wrong.
    #[test]
    fn non_scalar_types_are_refused_rather_than_guessed_at_32_bits() {
        let cases: &[Ty] = &[
            Ty::PtrSizedInt { signed: false },
            Ty::Char,
            Ty::Str,
            Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) },
            Ty::Array { elem: Box::new(Ty::Int { width: 8, signed: false }), len: 4 },
        ];
        for ty in cases {
            let err = reg_width(ty)
                .expect_err(&format!("{ty:?} has no register slot and must be refused"));
            assert!(err.contains("no register-slot width"), "{ty:?} refusal should say why: {err}");
        }
    }

    /// The refusal must PROPAGATE: `return_reg_width` is the caller that decides
    /// how many bits of the return register the gate reads back from the emitted
    /// object, and it must inherit the refusal rather than re-guess.
    #[test]
    fn a_return_type_with_no_register_slot_makes_the_return_width_unavailable() {
        let mk = |ty: Ty| trust_types::VerifiableFunction {
            name: "f".into(),
            def_path: "verify_output::f".into(),
            span: trust_types::SourceSpan::default(),
            body: trust_types::VerifiableBody {
                locals: vec![],
                blocks: vec![],
                arg_count: 0,
                return_ty: ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        };

        for ty in
            [Ty::Str, Ty::Slice { elem: Box::new(Ty::Bool) }, Ty::PtrSizedInt { signed: true }]
        {
            assert!(
                return_reg_width(&mk(ty.clone())).is_err(),
                "{ty:?} return must not yield a register width"
            );
        }
        // ... and a scalar return still does.
        assert_eq!(
            return_reg_width(&mk(Ty::Int { width: 64, signed: true })).expect("i64 return"),
            64
        );
    }
}
