// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **I5 — the Clean-origin CALL lane.**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! Rust calling a Clean `def`. This is the ONE direction in Trust that can
//! **produce a value**: every other gate is refutation-shaped and a
//! disagreement costs a failed build, whereas a disagreement here is a **wrong
//! binary**. The two decisions that stand between a Clean declaration and an
//! emitted call live in this crate, and both fail closed:
//!
//! * [`mint::decide_mint`] — may a `DefId` be minted at all? Requires
//!   `KernelChecked` **and** an audited-empty axiom closure **and** a total
//!   carrier. Any missing precondition means no `DefId`, hence `E0425` at the
//!   call site, carrying a v7/D3 note that names the reason and the options.
//! * [`gate::check_faithful`] — does the lowered body agree with the Clean
//!   `def`? Decided by kernel definitional equality or a closed, axiom-free
//!   structural-induction proof, **admitted at the carrier type**, against a
//!   declaration that entered the environment through a full kernel check.
//!
//! Since 2026-08-22 a third module carries a decision both of those rest on:
//! [`closure`], the crate's ONE axiom-closure audit, extended from
//! DECLARATIONS to arbitrary TERMS. It exists because the machinery that
//! preceded it was name-keyed and therefore structurally unable to see side
//! B — see that module's header, and `tests/r2_axiom_closure_probes.rs` c0
//! for the measurement. **No RECURSIVE [`gate::Faithful`] may be minted while
//! the closure is non-empty or unaudited**, on any of the three lanes: on a
//! well-founded spine the kernel's typing rule is the termination evidence,
//! and one assumed decrease switches it off (probe c1 reproduces exactly
//! that, at the kernel, as an ADMIT).
//!
//! **R2 — [`gate::check_faithful_wf_functional`] — is now a WIRED lane**
//! (2026-08-22). [`reflect_wf::reflect_wf_functional`] is the
//! MIR→[`gate::ReflectedWfFunctional`] producer, `emit.rs` routes a
//! `WellFounded.fix` declaration to it through
//! [`emit::CleanOriginShape::WellFoundedNatRec`], and the compiler emits the
//! body. **Two boundaries stay exactly where they were, and neither is a
//! formality:**
//!
//! * [`gate::FaithfulnessMethod::WellFoundedFunctionalDefeq`] still has NO
//!   wire tag, deliberately — see [`admission::mint_encoded_digest_for_export`]
//!   — so a WF verdict cannot leave its crate and a cross-crate call to a
//!   well-founded Clean def refuses. That is the same
//!   accounting R1's per-equation verdicts get, for the same reason: the
//!   verdict rests on a BORROW and a CLOSURE AUDIT taken in this crate's
//!   environment, and the wire unit carries no field for either.
//!   **Where it refuses moved on 2026-09-16; the boundary did not.** The
//!   export seam used to be FATAL, so a crate that merely DEFINED such a def
//!   could not be built as a library at all. The seam now exports an
//!   [`export_notice::NonExportableNotice`] in the certificate's place — a
//!   refusal-only row, no tag, no evidence — and the IMPORTER refuses the
//!   call at its readmission chokepoint with the notice's v7/D3 note.
//! * **R3a, 2026-08-26 — the well-founded fragment is no longer
//!   single-parameter.** It is ANY NUMBER of `Nat` parameters with a
//!   ONE-PARAMETER measure: the measure is guarded by `if h : 0 < a`, there is
//!   exactly one self-call whose measure argument is `a - 1`, its other
//!   arguments and both branch values are built from the parameters, `Nat`
//!   numerals, `+` and `*`, and no parameter is named twice in one branch (the
//!   emitted body moves the non-Copy bignums and the emitter has no clone).
//!   `def addAcc (a b : Nat) := if h : 0 < a then addAcc (a - 1) (b + 1) else b
//!   termination_by a` and `def dbl (a b : Nat) := if h : 0 < a then dbl (a - 1)
//!   (b * 2) else b termination_by a` both plan, emit and RUN
//!   (`tests/ui/trust/clean_origin_wf_rec_arity.rs`). The measure position may
//!   be any parameter — `r7_arity_widening_probes` q1 measures both.
//!
//!   It needed no pin move and no `compiler/**` edit: `first-party/clean`
//!   gained two-parameter well-founded recursion with a one-parameter measure
//!   in R3/R4, both already in the pin, and the arity limit was THIS CRATE's
//!   (`check_wf_nat_signature` plus readers written for the one-parameter fix
//!   spine). Per v7/D2 a measured fragment boundary is a statement of where we
//!   are, never a design.
//!
//!   **`gcd` is still not callable, and neither remaining reason is arity** —
//!   TRUE UNTIL §R3d, 2026-08-27; see the correction below the next paragraph.
//!   The modulo `gcd`'s measure-slot argument is `a % b` with a SYMBOLIC
//!   divisor, which commit `fa788aab89` refuses on purpose: Clean's `Nat.mod`
//!   is TOTAL where Rust's `%` PANICS, and the faithfulness gate is blind to
//!   the divergence because the panic lives in MIR the kernel never sees. A
//!   SUBTRACTIVE `gcd` decreases only in `a + b`, and a two-parameter MEASURE
//!   is refused island-side by name (`r6_nat_mul_probes` q2).
//!
//!   **THE SECOND HALF OF THAT SENTENCE EXPIRED 2026-08-27 — corrected, not
//!   deleted, because the stale version is what a reader would search for.**
//!   `first-party/clean` `6adb7beeb` carries `wf_recursion::sum_measure`, so a
//!   multi-parameter measure IS lowered now — as a course-of-values recursion
//!   on the measure's VALUE (WF "phase 3"). Two consequences, and they are
//!   different: (1) what refuses the subtractive `gcd` at the island is no
//!   longer the measure's ARITY but the DECREASE — the cascade has no lemma
//!   for `((a-b)+(b-a)) + 2*(a-(a-b)) < a + 2*b` given `0 < b`
//!   (`gcd_formulation_probes`, re-ranked); (2) a measure the cascade CAN
//!   discharge produces a spine none of this crate's readers could parse, and
//!   R3c taught them to — see [`emit::read_wf_sum_measure_anatomy`] and
//!   `tests/phase3_spine_reader_probes.rs`. Reading is not emitting: the
//!   call lane still refuses phase 3, now with a refusal that names it.
//!
//!   **BOTH HALVES OF (1) AND (2) HAVE NOW MOVED AGAIN — §R3d, 2026-08-27, and
//!   this is where `gcd` stops being an exception.** The pin advanced to
//!   `first-party/clean` `4f7bdab766`, whose cascade gained three general,
//!   axiom-free tiers, and `termination_by a + 2*b` DISCHARGES — so (1) is
//!   retired: what blocked the subtractive `gcd` at the island no longer
//!   blocks it, and `gcd_formulation_probes` p3 is re-ranked a second time to
//!   say so. (2) is closed too: this crate now EMITS phase 3.
//!
//!   ```text
//!   def gcdB (a b : Nat) : Nat :=
//!     if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a
//!   termination_by a + 2*b
//!   ```
//!
//!   plans, materializes, reads back, reflects, passes
//!   [`gate::check_faithful_wf_functional`] and RUNS from Rust with **two
//!   arguments and no fuel wrapper**
//!   (`tests/ui/trust/clean_origin_wf_rec_gcd_direct.rs`). The fuel form
//!   `gcdF f a b` still works and is still tested, but its two-argument surface
//!   was a Rust wrapper supplying `a + 2b` and therefore carried no proof claim
//!   about the recursion; this one's two-argument surface IS the recursion.
//!
//!   **What R3d costs in checking power, stated because "more shapes admit"
//!   reads like less checking.** One thing, and it is the plumbing: MIR
//!   contains no MEASURE, so side B cannot author the three positions the
//!   sum-measure lowering states in terms of one — the `rec` binder's type, the
//!   `hm` binder's type, and each self-call's major premise. Side B writes
//!   [`MEASURE_SLOT_SENTINEL`] in each and the gate substitutes side A's own
//!   term at the same position, exactly as it already did for the decrease
//!   proof, and for the same reason: the measure is not a value the emitted
//!   body computes, not an argument it passes and not a branch it takes.
//!   Everything the emitted body DOES determine — the guarded parameter, both
//!   branch values, the self-call's source arguments — is still decided by the
//!   type check at side A's functional type and the kernel defeq.
//!   `tests/control_18_wf_sum_measure_emitter_mutation.rs` is the measurement:
//!   swapped self-call operands, the guard on the wrong parameter, a wrong
//!   threaded index and the `|a-b|` / `min a b` legs' own operands transposed
//!   are all REFUSED, structurally and at the kernel.
//!
//! **The sentence above was TRUE OF THE DESIGN and FALSE OF THE COMPILER
//! between 2026-08-22 and 2026-08-22.** As landed, `recognise_wf_nat_rec` read
//! `Nat.lt` / `Nat.decLt` / `Nat.sub` where the elaborator emits `LT.lt` /
//! `instDecidableNatLt` / `HSub.hSub`, so no source program reached the lane at
//! all and `tests/ui/trust/clean_origin_wf_rec.rs` failed with `E0425`
//! (`docs/audits/2026-08-22-r2-wf-call-lane-unreachable.md`). Every check in
//! this crate's suite was green, because every well-founded side A in it was
//! hand-built. The three readings are re-derived from the elaborator now, and
//! `tests/r2_session_probes.rs` is the file that holds them to it: p1
//! elaborates the fixture above through
//! `trust_certify::clean_island::CleanIslandSession` and asserts it PLANS, p4
//! takes it through [`gate::check_faithful_wf_functional`] and asserts
//! FAITHFUL. **Do not add an elaborator claim to `r2_wf_equation_probes.rs`** —
//! that file measures the kernel, which is a different question and was never
//! wrong.
//!
//! Since I7 the crate also carries the cross-crate half's DECISIONS:
//! [`admission`] defines the verdict digest (the wire unit — kernel version,
//! environment digest, axiom closure, carrier decision, faithfulness evidence; never
//! a source hash) and [`admission::readmit`], the fail-closed re-admission of
//! an imported certificate. Of the rustc metadata transport, the **ENCODE half
//! is wired** (2026-08-19): the compiler's export provider mints the wire
//! bytes through the one seam [`admission::mint_encoded_digest_for_export`]
//! (re-earning a fresh [`gate::Faithful`] against the exact body rmeta
//! serializes), and rmeta carries a per-def digest table plus two crate-root
//! fields — the island sources (transport, never authority: the importer
//! re-elaborates them under its OWN kernel) and the Clean-origin export list
//! (the digest table's second, independent encoding, so row-absence cannot
//! demote a Clean-origin def to ordinary Rust). The IMPORT half is wired too:
//! extern `optimized_mir`/`mir_for_ctfe` pass through the versioned digest
//! decode, cheap local preflight, local declaration re-elaboration, a fresh
//! MIR re-gate, and only then final [`admission::readmit`] before an imported
//! body can escape.
//!
//! # THE STATE OF THIS CRATE — READ BEFORE CITING IT
//!
//! A Clean-origin `DefId` IS minted and a Clean-origin `Body` IS emitted, for
//! the direct/inductively-proved **parameter-projection**, **single wrapping
//! binop**, **composed wrapping tree**, **parameter-select**,
//! **select-vs-literal**, — §6f landing 7, 2026-08-23 — **single raw binary
//! operator** (`a &&& b`, `a ||| b`, and `a / K` / `a % K` at a STRICTLY
//! POSITIVE numeral `K` only — Clean's `UInt{N}.div`/`.mod` are TOTAL where
//! Rust's `/`/`%` PANIC, so a variable or zero divisor is refused on side A,
//! on the sealed plan, and again by the frozen producer; and, since clean
//! `bf31976f48` (2026-09-23), `a ^^^ b` and `a >>> K` at a numeral `K` below
//! the width — `a <<< K` elaborates too and is not planned at any amount: the
//! gate identifies the frozen producer's reading of it only at `K = 1`, a
//! function `a * 2` already emits; see `tests/landing7_selection_probes.rs`),
//! — R1, 2026-08-21 —
//! **structural-Nat-recursion** and — R2, 2026-08-22 —
//! **well-founded-Nat-recursion** (`def countdownSum (n : Nat) : Nat :=
//! if h : 0 < n then n + countdownSum (n - 1) else 0` + `termination_by n`,
//! one self-call at `n - 1`, gated by the F-LAYER judgment
//! [`gate::check_faithful_wf_functional`] over an audited-empty axiom closure)
//! fragments —
//! `fun a b => a`, `fun a b => a + b`, `fun a b => (a + b) * a`,
//! `fun a b => if a < b then a else b`, `fun a b => if a < 10 then a else b`
//! and `def tozero : Nat -> Nat | 0 => 0 | n + 1 => tozero n`
//! (add/sub/mul with `Param` or in-range numeral operands; `<`/`<=`/`==`
//! selects over bare parameter arms, the comparison parameter-vs-parameter or
//! parameter-vs-numeral with the numeral strictly on the right; one unsigned
//! machine width across the signature, at most [`COMPOSED_MAX_OPS`] ops per
//! body; the recursive fragment single-parameter at the `Nat` bignum carrier,
//! one recursive use per step, gated per defining equation under the §6e
//! IMPLEMENTATION AMENDMENT — [`gate::check_faithful_equations`]). A
//! structural `Nat.rec` fold extensionally equal to its input is additionally
//! emitted as the exact bignum projection, but only after kernel-checked
//! structural induction (the inductive-projection lane).
//!
//! **§R6 (2026-08-25) adds `*` to the recursion-arm value vocabulary** (the
//! `nat.mul` row), which makes FACTORIAL — `def fact (n : Nat) : Nat :=
//! if h : 0 < n then n * fact (n - 1) else 1` + `termination_by n` — plan,
//! reflect and pass the F-layer gate against the REAL elaborated side A
//! (`tests/r6_nat_mul_probes.rs` q6/q9), and run from Rust
//! (`tests/ui/trust/clean_origin_wf_rec_mul.rs`). It adds no MIR shape and no
//! gate route: the emitted body is `nat.add`'s call chain with one
//! authenticated callee changed, and the kernel identification it rests on
//! (`a * b ≡ Nat.mul a b`, with `a * b ≢ Nat.add a b`) was measured BEFORE the
//! producer was written (q7).
//!
//! Citing
//! this crate as evidence that `let g = gcd(12, 18);` works would STILL be
//! false — but **CORRECTED 2026-08-25, not for the reason this paragraph used
//! to give.** It said `gcd`'s recursion was "refused in `first-party/clean`'s
//! elaborator itself (`RecursionOutsideFragment`)". Re-measured at the current
//! pin (`r6_nat_mul_probes` q1), `gcd` ELABORATES and kernel-checks; what
//! refuses it is this crate's single-parameter fix-spine reader. The R1 lane
//! covers the tozero class, the inductive-projection lane only
//! recursions provably equal to a parameter, and fib waits on the pair
//! carrier (its `.cov` equations are measured green at the kernel,
//! `tests/r1_equation_probes.rs` e4; the boundary rows are pinned in
//! `tests/control_7_structural_rec_emitter_mutation.rs`).
//! `let v = m::pick(41, 7);`, `wsum(u64::MAX, 1) == 0`,
//! `wmix(u64::MAX, 1) == 0`, `tozero(Nat::from_u64(3)) == 0` and the
//! recursive identity control are what run.
//! Cross-crate: a per-equation verdict cannot leave its crate — wire format
//! v2 carries the `Nat` (unbounded-exact) carrier honestly, so the mint's
//! refusal is now explicit rather than a width accident: a [`Faithful`]
//! whose method has no wire tag refuses at
//! [`admission::DigestMintRefusal::UnencodableFaithfulness`], which covers
//! the whole R1 slice; a [`FaithfulnessEvidence`] spelling for per-equation
//! verdicts is its own reviewed wire change, deliberately not smuggled in
//! here.
//!
//! What HAS landed, and is wired:
//!
//! * [`emit::plan_clean_origin_body`] and [`emit::admit_lowering`] — the body
//!   plan and **the round trip that feeds the gate its side B**, through the
//!   pre-existing E6 Rust→Clean path (`recognize_admissible_body` →
//!   `admit_projection_function`). `tests/control_3_clean_origin_emitter_mutation.rs`
//!   injects a wrong-parameter emission and requires a refusal, and separately
//!   confirms the KERNEL itself distinguishes the two bodies — so the catch is
//!   not merely structural.
//! * `compiler/rustc_mir_transform/src/clean_origin_mir.rs` — the **sole
//!   constructor** of a Clean-origin `Body`, which cannot return one without a
//!   [`gate::Faithful`], called from the top of `optimized_mir` and
//!   `mir_for_ctfe`, with `mir_keys` and `promoted_mir` taught the new origin.
//!   Not behind any verification switch.
//!
//! **The MINT has now landed too** (2026-08-19), so the lane is reached: a
//! `clean { … }` declaration that passes [`mint::decide_mint`] acquires a
//! `DefId`, is planted in the ENCLOSING module's value namespace, and is called
//! from Rust. The four blockers below are all **resolved**; they are kept
//! because the corrections they record are still true of the design doc's §7
//! text, and because two of them describe why the shape is what it is.
//!
//! 1. **RESOLVED — `fn_sig` is now `feedable`, WITH a feeder.** It used to be
//!    declared in `rustc_middle/src/queries.rs` with `cache_on_disk`,
//!    `handle_cycle_error` and `separate_provide_extern` but **no `feedable`**,
//!    and its provider in `rustc_hir_analysis/src/collect.rs` opens by
//!    destructuring real HIR (`tcx.hir_node(hir_id)`). Typeck of a call goes
//!    `Res::Def(DefKind::Fn, did)` -> `type_of` -> `FnDef` -> `fn_sig(did)`, so
//!    minting the `DefId` without answering `fn_sig` converted a clean `E0425`
//!    into an ICE. The modifier was added together with its ONLY feeder —
//!    `rustc_resolve`'s `trust_mint_clean_island_decls`, which derives the
//!    signature from this crate's `CarrierSignature` (which cannot exist with a
//!    partial position). `fn_arg_idents` needed the same treatment, for the
//!    same reason: the metadata encoder calls it for every local `DefKind::Fn`
//!    and its provider `span_bug!`s on a synthetic HIR owner.
//! 2. **RESOLVED — the preconditions are evaluated at a NEW seam.**
//!    `def_collector` runs during expansion, and the only producer of
//!    `KernelStatus::KernelChecked` in the tree is
//!    `trust_certify::clean_island`, previously driven only from HIR inside the
//!    `TrustVerify` MIR pass — hundreds of phases later. The fix is not to move
//!    the mint but to run the whole-crate island check EARLIER:
//!    `rustc_resolve/src/trust_clean_mint.rs` checks every island of the ROOT
//!    `AstFragment::Crate` as one header-first batch inside
//!    `Resolver::visit_ast_fragment_with_placeholders`, i.e. immediately before
//!    `collect_definitions`, and `def_collector` consults its verdicts. Islands
//!    introduced by LATER macro expansion mint nothing and fail closed.
//!    Cost, stated: `rustc_resolve` now names the whole Clean closure, where §8
//!    budgeted only `trust-symbols`.
//! 3. **RESOLVED — but not the way §7 said.** "No trust-ir `Module` -> `Body`
//!    constructor exists" was true, and the trust-ir route is dead at BOTH
//!    ends: `lower_ir_to_mir` needs HIR three independent ways, and there is no
//!    Clean → trust-ir producer anywhere in the tree. The route that works uses
//!    only pre-existing, independently-authored paths and is spelled out in
//!    [`emit`]. The `Body` is originated directly in
//!    `rustc_mir_transform::clean_origin_mir`, and every DECISION about it
//!    lives here.
//! 4. **RESOLVED as a design-doc correction.** Provider overrides installed
//!    from `rustc_interface` are fatally rejected by Trust's own anti-tamper
//!    gate (`changed_trust_critical_query_provider` address-compares
//!    `mir_keys`, `mir_built`, `mir_borrowck`, `mir_for_ctfe`,
//!    `optimized_mir`). §7's *"`trust-clean-origin` installs the provider
//!    overrides"* is therefore not implementable as written. `clean_origin_mir`
//!    is **called from inside `rustc_mir_transform`'s own provider functions**,
//!    making this crate a dependency of `rustc_mir_transform` rather than a
//!    provider installer. That is strictly better: both call sites are inside
//!    the crate that owns MIR construction, so there is no override to audit.
//!
//!    **Scope of that rejection, measured 2026-08-19 (adversarial review of
//!    the I7 plan):** the anti-tamper gate runs only while Trust query
//!    semantics are ACTIVE — `rustc_interface/src/passes.rs` gates the whole
//!    check on `trust_query_semantics_active`, and `-Ztrust-verify=off`
//!    switches that off — so in non-verify modes a replaced provider is
//!    refused by NOTHING. What does not vanish with it is the gate itself:
//!    `clean_origin_mir` and the export digest mint live INSIDE the default
//!    providers, so every in-tree path is gated in every mode, including
//!    `-Ztrust-verify=off`. The honest boundary statement is therefore:
//!    compiler-owned providers are part of the TCB; an embedder's
//!    `override_queries` is an API outside it, and the address-compare
//!    ratchet extends over it only in trust-semantics-active modes. Do not
//!    cite the ratchet as tamper protection for the other modes.
//!
//! The sequencing rule that produced this order, recorded because it is the
//! reusable part: **until `fn_sig` could be answered for a HIR-less def,
//! minting was a regression rather than progress** — a mint without it trades a
//! correct diagnostic for a compiler crash. The modifier and its feeder
//! therefore landed in the same change, never separately.
//!
//! # What IS established here
//!
//! The three decisions, as total functions, with the controls that prove they
//! are not decoration:
//!
//! * `tests/control_1_mint_preconditions.rs` — every missing precondition
//!   refuses, and every refusal carries at least two options (v7/D3);
//! * `tests/control_2_frozen_r_mutation.rs` — a one-construct mistranslation
//!   handed straight to the gate must be caught, against the **real**
//!   `clean_kernel::TypeChecker`;
//! * `tests/control_3_clean_origin_emitter_mutation.rs` — the same, injected
//!   into the **emitted body** and routed through the real E6 producers, plus
//!   the independent check that the kernel itself separates the two terms.
//!
//! # Why the gate needs BOTH the kernel and the carrier
//!
//! I4's `control_b_defeq_insufficiency` executes the proof that kernel defeq
//! does **not** subsume representation faithfulness:
//! `UInt64.toNat (UInt64.ofNat (2^64))` is definitionally equal to `0`, so a
//! defeq-only gate admits a term whose emitted value wrapped. The carrier
//! obligation catches that without consulting the kernel. Conversely the
//! carrier says nothing about whether the lowering mistranslated. The gate
//! demands both, which is what "admitted at the CARRIER type, never the Clean
//! type" means operationally.

pub mod admission;
pub mod closure;
mod direct_source;
pub mod emit;
pub mod export_notice;
pub mod gate;
mod implemented_by;
pub mod materialize;
pub mod mint;
mod named_calls;
pub mod reflect;
pub mod reflect_rec;
pub mod reflect_rust_call;
pub mod reflect_wf;
pub mod symbol;
pub mod table;

pub use admission::{
    CarrierDecision, CarrierPosition, DecodeRefusal, DigestMintRefusal, EnvironmentDigest,
    EnvironmentDigestRefusal, ExportDigestRefusal, FaithfulnessEvidence, LocalBodyRecheckRefusal,
    LocallyRechecked, ReadmissionPreflight, ReadmissionRefusal, Readmitted, VerdictDigest,
    WirePreflight, bind_readmission, environment_digest_for, local_kernel_version,
    locally_recheck_imported_body, mint_encoded_digest_for_export,
    mint_encoded_digest_for_export_for_name, mint_verdict_digest, preflight_wire, readmit,
};
pub use closure::{ClosureAudit, audit_proof_closure, audit_term_closure};
pub use emit::{
    BOOL_EXPRESSION_MAX_OPS, BoolExpr, COMPOSED_MAX_OPS, CleanOriginPlan, CleanOriginShape,
    EmitRefusal, RustCallArg, RustCallLiteral, RustCallNode, RustCalleeRef,
    UINT_CONDITIONAL_MAX_DECISIONS, UIntConditional, WfLowering, WfSumMeasureAnatomy,
    WfSumMeasureCall, admit_lowering, check_rust_call_chain_for, plan_clean_origin_body,
    plan_clean_origin_body_with_rust_callees, plan_clean_origin_body_with_rust_callees_for_name,
    read_wf_sum_measure_anatomy,
};
pub use export_notice::{
    NON_EXPORTABLE_NOTICE_FORMAT_V1, NON_EXPORTABLE_NOTICE_MAGIC, NonExportableNotice,
    NonExportableReason, NoticeDecodeRefusal,
};
pub use gate::{
    DECREASE_SLOT_SENTINEL, Faithful, FaithfulnessMethod, GateRefusal, MEASURE_SLOT_SENTINEL,
    ReflectedCase, ReflectedStructuralRec, ReflectedWfFunctional, check_faithful,
    check_faithful_equations, check_faithful_wf_functional,
};
pub use materialize::{
    BodyTemplate, TemplateBlock, TemplateCallee, TemplateLocal, TemplateOperand, TemplateRefusal,
    TemplateRvalue, TemplateStatement, TemplateTerminator, TemplateTy, TemplateUnwind,
    body_template, zero_test_rec_template,
};
pub use mint::{
    MintGrant, MintRefusal, decide_mint, decide_mint_from_signature, leading_type_variable_binders,
    nested_island_definitions,
};
pub use reflect_rec::reflect_structural_rec;
pub use reflect_rust_call::reflect_rust_call_chain;
pub use reflect_wf::reflect_wf_functional;
pub use table::{
    AnchoredCarriers, CalleeSelector, CarrierAnchor, CarrierClass, DEMANDS, DemandStatus,
    ElabToken, GateRouting, KernelSelector, MirAliasing, MirShape, ROWS, ReflectSpec, RowContext,
    SelectionDemand, SelectionRow, TotalityDemand, UnwindDiscipline, coverage_basis_points,
    covered_demands, missing_demands, no_selection_row, row, rows_selecting_head,
    whole_body_refusal,
};
// The caller-obligation vocabulary, re-exported so a consumer of a
// `CleanOriginPlan`/`MintGrant` does not have to reach past this crate for the
// type its own accessors return.
pub use trust_clean_carrier::{CleanOriginPrecondition, PreconditionOperand, PreconditionRelation};

/// The planner's side-A expansion of transparent Lean helper calls, with no Rust
/// callees in scope: every application whose head is a fully kernel-checked
/// `Definition` at a carrier signature is unfolded, within the planner's work
/// envelope. `Ok(None)` when nothing was unfolded.
///
/// Trust (2026-09-28): exported for the kernel-TV SOURCE side
/// (`rustc_mir_transform::clean_origin_ir::mint_kernel_tv`). A `def` whose body
/// is a call to another island `def` (`def viaId x := idA x`) plans through this
/// expansion as a projection, so it is a carrier-gate target, and a target must
/// carry a TV companion. The source denotation read only the unexpanded
/// declaration, refused the `idA` head, and every `-Ztrust-verify=on` build of
/// the crate died on "the expected kernel-TV companion is missing", even with
/// the `def` uncalled. Like every use of this expansion it is a reading, never
/// evidence: the carrier gate still compares the emitted body with the ORIGINAL
/// declaration by kernel definitional equality.
///
/// # Errors
///
/// The expansion's own refusals: a work-envelope overrun, a helper without a
/// full kernel check, or a recursive helper.
pub fn expand_named_lean_calls(
    env: &clean_kernel::Environment,
    declaration: &clean_kernel::Name,
    body: &clean_kernel::Expr,
) -> Result<Option<clean_kernel::Expr>, String> {
    named_calls::expand_named_calls(env, declaration, body, &[])
}
