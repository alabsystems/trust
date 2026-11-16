//! trust_ir_frontend: the F1 consumer of finalized direct Trust-IR
//! (`-Ztrust-cg-frontend=trust-ir`).
//!
//! # What this is, and what it is not
//!
//! The source -> TrustIR PRODUCER already ships and is on: `trust_ir_of` is a
//! registered rustc query (`rustc_mir_build::provide`) with a first-class
//! `--emit=trust-ir` artifact lane. What did not exist was a CONSUMER: nothing
//! in codegen ever asked for it, so the trust-cg backend built its
//! `VerifiableFunction`s from MIR and the "source -> TrustIR -> object" path
//! (F1) had never been executed end to end, only measured offline on dumped
//! modules.
//!
//! `trust_ir_of` still creates the per-body inputs during analysis. Crate
//! finalization validates, collision-renames and call-links those bodies, then
//! stores the resulting Module together with an exact definition-to-FuncId
//! handoff. This module is the codegen consumer. For each reachable monomorphic
//! function it:
//!
//! 1. resolves the item's non-generic local `LocalDefId`,
//! 2. selects its assembled FuncId through the conjunctive
//!    `(DefIndex, DefPathHash)` handoff — never through `def_path_str`,
//! 3. renames that selected function to the item's MANGLED SYMBOL NAME, and
//! 4. routes the module through `trust_cg_bridge::lower_module_to_lir`, whose
//!    LIR feeds the SAME object emitter the MIR path uses.
//!
//! It is NOT a second inventory. The mono-item collection, the linkage /
//! visibility gate and the instance ABI validation are the exact functions the
//! production path calls, so the two paths compile the same set of symbols and
//! differ only in where each function's IR came from.
//!
//! # Fail-closed contract
//!
//! Every step above is a REFUSAL, never a fallback:
//!
//! * an instance whose body is in an upstream crate — refused (THIR is a
//!   local-only query), unless `-Ztrust-ir-upstream-mir` routes it through the
//!   upstream-instance MIR lane;
//! * an instance with no source body at all (shim / drop glue / intrinsic /
//!   virtual entry / constructor shim) — refused;
//! * an instance carrying a real (non-lifetime-only) monomorphization — refused;
//! * an instance whose definition is not a local, non-generic body — refused;
//! * an absent assembled handoff or absent exact definition entry — refused;
//! * a handoff whose selected function or function type is absent — refused;
//! * `lower_module_to_lir` returning any `ModuleLirError` — refused.
//!
//! Refusals are CLASSIFIED ([`RefusalClass`]) and every message carries its
//! class tag, so a refusal list is aggregatable; [`RefusalCensus`] is the
//! aggregate form, and the design note on `local_body_def` is where the two
//! large classes are measured and the fix for each is spelled out.
//!
//! A refusal is `Err` here and `sess.dcx().fatal` at the call site. There is
//! deliberately no fallback to MIR or to the per-body artifact. The latter has
//! local callees only as bodyless declarations, and retrying it used to hide an
//! assembled-selection miss until conversion happened to fail later.
//!
//! # How this path IS verified
//!
//! The M-POS proven-output gate now has a trust-ir entry point:
//! `trust_cg_bridge::verify_output_trust_ir`. Its spec side is derived from the
//! selected function in the producer's finalized assembled Module, BEFORE any
//! LIR lowering, while its machine side is the unchanged
//! `PathMergingExecutor` over the EMITTED BYTES. So this module carries the
//! producer Module alongside the LIR ([`TrustIrLoweredFunction::gate_source`])
//! and hands it to the gate at emission time.
//!
//! `source_functions` on the assembled `CompiledModule` stays `None` and that is
//! still the honest value: there is no `VerifiableFunction` behind these bytes.
//! What changed is that the trust-ir gate does not need one, and `lib.rs` no
//! longer treats `None` as "nothing to check" — the F1 emission path refuses
//! outright unless it has a 1:1 trust-ir work list to verify.
//!
//! # TWO MODES (gap G2, reconciled with the F1 callee seam)
//!
//! Everything above describes the ASSEMBLED-HANDOFF mode ([`lower_instance`]),
//! which `lib.rs` step (5) drives: each item is selected by exact identity from
//! the finalize-assembled crate module (`AssembledCrateModuleForCodegen`), so
//! intra-module callees resolve there too. Its refusals are recorded into one
//! [`RefusalCensus`].
//!
//! [`lower_crate_module`] is the second mode, and it IS SELECTABLE — by
//! `-Ztrust-ir-crate-module`, which `lib.rs` step (5) reads. It takes the
//! lowering context from the crate module the producer PUBLISHES
//! (`trust_thir_lower::crate_module::with_published_crate_module`) and adds the
//! codegen-license NEGATIVE GATE below. Until the producer stamped
//! `Function::body_gate` this mode could not be selected at all: every body in
//! every published module carried no licensing claim, so it refused all of them
//! as `unlicensed-body`. `trust_thir_lower::crate_module::stamp_codegen_license`
//! closed that, and this is the lane that reads what it wrote.
//!
//! It is OFF BY DEFAULT, and the default is not the weaker gate. The two modes
//! differ in SELECTION: [`lower_instance`] picks a body by exact
//! `(DefIndex, DefPathHash)` identity out of the assembled handoff, while this
//! one resolves it by the producer's DISPLAY path, which is documented as not
//! being identity — a collision-renamed body (two macro-expanded definitions
//! with one `def_path_str`) is therefore refused here and admitted there. What
//! this mode ADDS is the license: every body in the lowering context must carry
//! a positive gate from a RECOGNIZED authority, which is what makes an appended
//! below-tier definition refuse the whole crate instead of being reachable
//! through `inline_local_pure_leaf_calls`.
//!
//! It is not a second inventory either: the work list is still the production
//! mono-item collection, and every instance still goes through
//! [`local_body_def`], so `upstream-body` / `synthesized-instance` /
//! `generic-instance` refuse identically. Its refusals go into the SAME
//! [`RefusalCensus`], and it has no MIR fallback anywhere in it.
//!
//! ## The codegen license binds in that mode
//!
//! Before anything is lowered from a published module, the v41 codegen license
//! ([`trust_ir::BodyGate`], carried on `Function::body_gate`) is read as a
//! NEGATIVE gate: it can only WITHHOLD authority, never grant it. `Ungated` is
//! refused because it is an affirmative "no gate ran"; an ABSENT claim is
//! refused too, as a SEPARATE class, because this consumer's input is a module
//! assembled in-process at a v41 pin rather than a legacy artifact, so
//! grandfathering it would buy no compatibility and would make dropping the
//! field the cheapest way to launder a body. See [`body_gate_verdict`] for the
//! full argument and [`prepare_crate_module`] for why the gate is applied
//! whole-module rather than per-function. What actually PERMITS emission is the
//! producer's separately-computed `PublishedCrateModule::codegen_inventory`,
//! and a gated body outside it is still refused.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use trust_cg_bridge::codegen_backend as bridge_backend;
use trust_ir::value::FuncId;

// Trust (step 2 increment 3): the instance-keyed codegen module. FROZEN
// (scripts/frozen-files.txt, owner ruling D17): it computes a splice decision.
pub(crate) mod instance_assembly;
// Trust (D39/D40): sealed strict-only upstream R input; frozen at landing.
mod upstream_entry;
// Trust (step 2 increment 4c): drop glue as trust-ir and the resolution of every `Inst::Drop` to
// a call of it. FROZEN (scripts/frozen-files.txt, owner ruling D18 OD-2 under D17's rule): it
// computes a splice decision.
pub(crate) mod drop_glue_lane;
// Trust (plan step 3.0, docs/design/2026-10-02-step3-lean-through-trust-ir.md §9): names every
// refusal F1 makes because of a Clean-origin body under one class, `[clean-below-gate]`. NOT
// frozen: it classifies refusals and admits nothing.
pub(crate) mod clean_below_gate;
// Trust (plan step 3.3): the F1 inventory reads a Clean-origin item's neighbours from its
// published trust-ir row instead of `clean_origin_mir`'s MIR. NOT frozen: it decides only which
// items the collector visits, and every visited item is still lowered and gated as before.
pub(crate) mod clean_inventory;
// Trust (step 2 increment 5, sub-step 5.4.2): rustc's `FnAbi`, read once into plain data for the
// compiler lane. NOT frozen (an unfrozen residual of `codegen_module.rs`).
pub(crate) mod abi_shape;
// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's codegen module (M_cg, S, P),
// PURE. Frozen BYTE-IDENTICAL at sub-step 5.4.4, not before (INC5.4-FREEZE): opt-in until then.
pub(crate) mod codegen_module;
// Trust: unchanged source signatures after exact native ABI and conservation checks.
pub(crate) mod native_source_module;
// Trust (PKG-CP, R-8 item P): the compiler lane folds constant-true checks and routes every other
// check of an admitted kind to rustc's panic entry with rustc's `Location` record. NOT frozen.
pub(crate) mod panic_sites;

/// The stable CLASS a refusal belongs to — the axis a census counts on.
///
/// A message names ONE symbol; a class names a SHAPE OF GAP, and the shape is
/// what tells a user whether their crate is one producer increment away from
/// compiling or a whole architecture away. Every class therefore carries
/// [`RefusalClass::retired_by`] — the one change that would stop it happening —
/// so a census reads as a work list rather than a complaint.
///
/// The tag is printed in EVERY per-item refusal message (see the `Display` impl
/// below), which makes even an unaggregated refusal list classifiable with
/// nothing but `grep -o '\[[a-z-]*\]' | sort | uniq -c`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RefusalClass {
    /// The body is in another crate. THIR is a local-only query, so no amount
    /// of producer work inside this crate reaches it.
    UpstreamBody,
    /// The instance has no source body at all (shim, intrinsic, virtual entry).
    SynthesizedInstance,
    /// A real monomorphization of a local body.
    GenericInstance,
    /// rustc's `FnAbi` for the instance is outside the emitted fragment.
    UnsupportedAbi,
    /// The producer had a local, non-generic body and still declined it.
    ProducerDeclined,
    /// The producer returned a Module this consumer cannot read.
    MalformedProducerModule,
    /// The Module -> LIR converter refused.
    ConverterRefused,
    /// CRATE-MODULE MODE: this compilation has no usable published crate
    /// module at all, so nothing in it can be lowered against one. Covers
    /// "never published", "publication refused", and "published but the
    /// whole-module preconditions did not hold".
    CrateModuleUnavailable,
    /// CRATE-MODULE MODE: the body carries an AFFIRMATIVE
    /// `BodyGate::Ungated` — the producer states that no verification gate was
    /// applied to it.
    UngatedBody,
    /// CRATE-MODULE MODE: the body makes NO licensing claim at all
    /// (`body_gate` absent). Deliberately NOT the same class as
    /// [`RefusalClass::UngatedBody`]: see [`GateVerdict`].
    UnlicensedBody,
    /// CRATE-MODULE MODE: the body is gated, but the PRODUCER's own
    /// deny-by-default codegen inventory does not list it.
    UnlicensedByProducer,
    /// A local constructor shim (no THIR body), or an upstream instance the
    /// `-Ztrust-ir-upstream-mir` lane could not extract or bridge.
    NotALocalItem,
    /// Trust (step 2 increment 3): the INSTANCE LANE could not assemble this
    /// item's codegen module — a callee it must splice is refused, unresolved,
    /// recursive, table-bearing, drop-bearing or signature-mismatched. Every
    /// refusal names what it met (`instance_assembly`).
    InstanceAssembly,
    /// Trust (step 2 increment 3): the instance-keyed producer refused a DROP-BEARING instance.
    /// The producer elides implicit drops until increment 4, so such a body's module is not the
    /// instance's semantics.
    ElidedDrop,
    /// Trust (R-8 ledger item 1, plan §5): the function's trust-ir can reach a runtime CHECK
    /// (`Inst::Assert`: overflow, shift, negation, division, bounds) in its own body or in any
    /// function it calls, which F1 lowers to a bare trap — no panic message, no
    /// `#[track_caller]` location, no panic hook, SIGTRAP instead of the abort MIR->LLVM's panic
    /// path takes, so the emitted object would behave differently from Rust. Refused under EVERY
    /// output-gate policy, on the handoff, instance and crate-module lanes, until the panic path
    /// is faithful (ledger item P). On the handoff, instance and crate-module lanes one refusal,
    /// [`refuse_unfaithful_panic`], refuses every reachable check. On the compiler lane
    /// (`-Ztrust-cg-f1-backend=compiler`) [`panic_sites`] folds a constant-true check and sites
    /// every other check of an admitted kind at rustc's panic entry and `Location` record, and
    /// refuses with this class only a function holding a check it cannot site faithfully.
    UnfaithfulPanic,
    /// Trust (effect conservation, D28, 2026-10-01): the body's trust-ir does not carry every
    /// effect rustc's MIR has (a call, a store through an escaping pointer, a panic check, a
    /// drop, asm), or it carries a value abstraction (`undef`, an opaque placeholder lane). Such
    /// a body is a model, not the program, and is never code
    /// (`trust_thir_lower::effect_conservation`). A dropped panic check matters here although
    /// this frontend refuses every `Assert` it SEES ([`Self::UnfaithfulPanic`]): a body whose
    /// producer dropped the check has none left to see.
    EffectNotConserved,
    /// Trust (plan step 3.0, docs/design/2026-10-02-step3-lean-through-trust-ir.md §9): the item is
    /// a Clean-origin (Lean) `def`, or a Rust body refused because it reaches one. F1 admits no
    /// `Producer::Clean` body yet, whatever its tier: since step 3.4 a tier-`gate` Function
    /// carries an authenticated `clean-carrier-gate` license beside its session-ledger entry, and
    /// the license is honored only on the `Compiler::compile` lane at step 3.6 (D36, D37). Every refusal names the def, its tier and
    /// shape as the Clean recorder disclosed them (or that nothing was recorded on this lane),
    /// why, and the options ([`clean_below_gate`]).
    CleanBelowGate,
    /// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's codegen module
    /// (`codegen_module.rs`) refused a body: a function reference other than a direct call, a
    /// reachable declaration with no real link symbol, inventory residue it cannot name, a body
    /// of another producer, a broken postcondition. The refusal names its rule.
    CodegenModule,
    /// Trust (step 2 increment 5, sub-step 5.4.2): trust-cg's own preflight census (or its
    /// residual compile error) refused a function of the compiler lane's codegen module; each
    /// sample prints `[trust-cg-refused:<variant>]`.
    TrustCgRefused,
    /// Trust (step 2 increment 5, sub-step 5.4.2; dormant until 5.6): a callee declaration whose
    /// signature is not rustc's FnAbi-legalized one.
    CalleeAbiMismatch,
    /// A dependency entry failed identity, protocol, target or semantic admission.
    UpstreamEntry,
}

/// The number of [`RefusalClass`] variants.
///
/// Spelled explicitly rather than as `RefusalClass::ALL.len()` so the array
/// lengths below do not depend on const-evaluating an associated const in type
/// position; `class_list_is_complete_and_indexable` executes the agreement.
const CLASS_COUNT: usize = 21;

impl RefusalClass {
    /// Declaration order is the report's TIE-BREAK order. The census sorts by
    /// count first, so this only has to be stable, not meaningful.
    #[allow(dead_code)] // Trust (G1): read by `RefusalCensus`, which is INERT — see below.
    pub(crate) const ALL: [RefusalClass; CLASS_COUNT] = [
        RefusalClass::UpstreamBody,
        RefusalClass::SynthesizedInstance,
        RefusalClass::GenericInstance,
        RefusalClass::UnsupportedAbi,
        RefusalClass::ProducerDeclined,
        RefusalClass::MalformedProducerModule,
        RefusalClass::ConverterRefused,
        RefusalClass::CrateModuleUnavailable,
        RefusalClass::UngatedBody,
        RefusalClass::UnlicensedBody,
        RefusalClass::UnlicensedByProducer,
        RefusalClass::NotALocalItem,
        RefusalClass::InstanceAssembly,
        RefusalClass::ElidedDrop,
        RefusalClass::UnfaithfulPanic,
        RefusalClass::EffectNotConserved,
        RefusalClass::CleanBelowGate,
        RefusalClass::CodegenModule,
        RefusalClass::TrustCgRefused,
        RefusalClass::CalleeAbiMismatch,
        RefusalClass::UpstreamEntry,
    ];

    /// Stable machine-readable tag. Changing one of these strings changes a
    /// user-visible contract, so treat them like wire tags.
    pub(crate) const fn tag(self) -> &'static str {
        match self {
            Self::UpstreamBody => "upstream-body",
            Self::SynthesizedInstance => "synthesized-instance",
            Self::GenericInstance => "generic-instance",
            Self::UnsupportedAbi => "unsupported-abi",
            Self::ProducerDeclined => "producer-declined",
            Self::MalformedProducerModule => "malformed-producer-module",
            Self::ConverterRefused => "converter-refused",
            Self::CrateModuleUnavailable => "crate-module-unavailable",
            Self::UngatedBody => "ungated-body",
            Self::UnlicensedBody => "unlicensed-body",
            Self::UnlicensedByProducer => "unlicensed-by-producer",
            Self::NotALocalItem => "not-a-local-item",
            Self::InstanceAssembly => "instance-assembly",
            Self::ElidedDrop => "elided-drop",
            Self::UnfaithfulPanic => "unfaithful-panic",
            Self::EffectNotConserved => "effect-not-conserved",
            Self::CleanBelowGate => "clean-below-gate",
            Self::CodegenModule => "codegen-module",
            Self::TrustCgRefused => "trust-cg-refused",
            Self::CalleeAbiMismatch => "callee-abi-mismatch",
            Self::UpstreamEntry => "upstream-entry",
        }
    }

    /// The index of this class in [`RefusalClass::ALL`].
    ///
    /// A `match` rather than a search, so the two lists cannot drift apart
    /// without the compiler noticing.
    #[allow(dead_code)] // Trust (G1): read by `RefusalCensus`, which is INERT — see below.
    pub(crate) const fn slot(self) -> usize {
        match self {
            Self::UpstreamBody => 0,
            Self::SynthesizedInstance => 1,
            Self::GenericInstance => 2,
            Self::UnsupportedAbi => 3,
            Self::ProducerDeclined => 4,
            Self::MalformedProducerModule => 5,
            Self::ConverterRefused => 6,
            Self::CrateModuleUnavailable => 7,
            Self::UngatedBody => 8,
            Self::UnlicensedBody => 9,
            Self::UnlicensedByProducer => 10,
            Self::NotALocalItem => 11,
            Self::InstanceAssembly => 12,
            Self::ElidedDrop => 13,
            Self::UnfaithfulPanic => 14,
            Self::EffectNotConserved => 15,
            Self::CleanBelowGate => 16,
            Self::CodegenModule => 17,
            Self::TrustCgRefused => 18,
            Self::CalleeAbiMismatch => 19,
            Self::UpstreamEntry => 20,
        }
    }

    /// The ONE change that retires this class. Deliberately names a mechanism,
    /// not an aspiration: a census line a reader cannot act on is noise.
    #[allow(dead_code)] // Trust (G1): read by `RefusalCensus`, which is INERT — see below.
    pub(crate) const fn retired_by(self) -> &'static str {
        match self {
            Self::UpstreamBody => {
                "a cross-crate producer input: `tcx.instance_mir(instance.def)` has a body here \
                 (MEASURED available for 100% of this class), but THIR does not exist off-crate, \
                 so this is a SECOND producer, not a wider key"
            }
            // Trust (step 2 increment 4d, sub-step 4d.0a): reworded from "lowering rustc's
            // synthesized bodies (`mir_shims`) or emitting them from the MIR path in a mixed
            // unit", which named the MIR route the drops design (§5) rules out for a shim.
            // tests.rs `no_f1_path_takes_the_mir_route_for_a_shim` pins this text.
            Self::SynthesizedInstance => {
                "per-kind trust-ir synthesis on the frozen shim lane (step 2 increment 4d), as \
                 drop glue is on the frozen glue lane (4c), under D18 OD-2; never rustc's shim \
                 MIR or any MIR route (design §5)"
            }
            Self::GenericInstance => {
                "the instance lane, which keys concrete local instances on `ty::Instance` on the \
                 DEFAULT lane since step 2 increment 3; this class remains only for an instance \
                 that is not concrete, and in `-Ztrust-ir-crate-module` mode, whose published \
                 module is pre-monomorphization"
            }
            Self::UnsupportedAbi => "backend ABI coverage; identical on the MIR path",
            Self::ProducerDeclined => {
                "producer coverage for the shapes in this body (`Lowered::unsupported`); the \
                 per-body tag list is the work item"
            }
            Self::MalformedProducerModule => {
                "a producer/consumer contract break — investigate rather than schedule; the \
                 assembled handoff selected a function or FuncTy the Module does not carry"
            }
            Self::ConverterRefused => "trust-ir -> LIR converter coverage (`trust_cg_bridge`)",
            Self::CrateModuleUnavailable => {
                "a crate finalization that reaches `crate_module::publish_crate_module` AND a \
                 published module that passes `validate_module_for_codegen` and the whole-module \
                 negative gate; the refusal detail names which of those failed"
            }
            Self::UngatedBody => {
                "GATING THE BODY. This is a producer ASSERTION that no gate ran, not an \
                 omission. A Clean-origin row below tier `gate` is affirmatively ungated on the \
                 Function itself; since plan step 3.4 a tier-`gate` row carries \
                 `Gated { clean-carrier-gate }` instead, honored only beside its session-ledger \
                 entry (D36, D37)"
            }
            Self::UnlicensedBody => {
                "the in-process producer STAMPING `trust_ir::Function::body_gate` (v41) — DONE: \
                 `trust_thir_lower::crate_module::stamp_codegen_license` stamps every function of \
                 the assembled module, so a body reaching this class now means the stamp did not \
                 run for it at all (a module that never went through crate finalization), not \
                 that the producer is silent"
            }
            Self::UnlicensedByProducer => {
                "widening `crate_module::compute_codegen_license` — its own refusal string says \
                 which of its four legs declined; this consumer never widens it from here"
            }
            Self::NotALocalItem => {
                "a real source adapter for a compiler-synthesized constructor or other \
                 instance the source producer does not represent"
            }
            Self::InstanceAssembly => {
                "real call edges on trust-cg `Compiler::compile` (step 2 increment 5) for \
                 recursive, closure, dyn, fn-pointer, foreign and unresolved edges; the table \
                 remap for struct/enum/global/tuple-layout instance bodies; the crate finalizer's \
                 pending-const patch at the instance seam; signable callee declarations; the \
                 strict output gate for a generic body (D17); drops (increment 4) for a \
                 drop-bearing leaf callee. The refusal detail names which"
            }
            Self::ElidedDrop => {
                "step 2 increment 4 (drops, faithfully): the producer emits `Inst::Drop` for every \
                 implicit drop; until then an instance with a drop-bearing parameter, local or \
                 temporary is refused"
            }
            Self::EffectNotConserved => {
                "the producer lowering every effect of the body (each `EffectNotConserved` tag \
                 names the MIR call, store, panic check, drop or asm it lost) and modelling no \
                 value by abstraction (each `Abstracted` tag names the lane); this consumer \
                 never admits a tagged body, whatever the tag (docs/DECISION_QUEUE.md D28)"
            }
            Self::CleanBelowGate => {
                "plan step 3 (docs/design/2026-10-02-step3-lean-through-trust-ir.md): a row at \
                 tier `gate` reaches F1 through the authenticated `clean-carrier-gate` carrier \
                 and its session ledger (step 3.4) on the `Compiler::compile` lane (step 3.6, \
                 D36/D37); a row below `gate` first needs the carrier gate to cover its shape \
                 (step 3.1); a local def with no row was not published by this compile's \
                 finalization (the recorder runs on every F1 compile since step 3.5); an \
                 imported Clean-origin body needs cross-crate Clean bodies (increment 6). Until \
                 then the MIR lane is the value-producing path for Clean-origin bodies"
            }
            Self::UnfaithfulPanic => {
                "R-8 ledger item P (plan §5, PKG-CP): a failed check lowers to Rust's panic entry \
                 points with rustc's `Location` record. The compiler lane \
                 (`-Ztrust-cg-f1-backend=compiler`) does this for the admitted check kinds and \
                 refuses a function only for a check it cannot site (a kind not yet admitted, no \
                 span, a `#[track_caller]` body); the other F1 lanes still refuse every function \
                 whose trust-ir can reach a runtime check, under every output-gate policy (under \
                 `-Ztrust-verify=off`, `-Coverflow-checks=off` removes the overflow checks; \
                 division and bounds checks remain)"
            }
            Self::CodegenModule => {
                "the compiler lane's codegen module (`codegen_module.rs`, step 2 increment 5): each \
                 refusal names its rule and the sub-step that lifts it — function references other \
                 than a direct call (5.9, 5.11), declarations with no real link symbol (5.6), \
                 inventory residue the instance lane spliced (5.4.4, increment 7), bodies of other \
                 producers (step 3 for Clean)"
            }
            Self::TrustCgRefused => {
                "trust-cg's own coverage of the shape its preflight census names (each sample \
                 prints the `CompileError` variant); widened in the trust-cg sibling and moved in \
                 by a pin, never relaxed here"
            }
            Self::CalleeAbiMismatch => {
                "step 5.6: callee declarations signed from rustc's FnAbi for the callee instance, \
                 so the declared signature IS the legalized one"
            }
            Self::UpstreamEntry => {
                "a schema/mode/identity-bound metadata body whose actual types, target, callees and rederived effects pass the sealed D39 consumer; templates require 6.6"
            }
        }
    }
}

impl RefusalClass {
    /// What a user can do NOW about a refusal of this class, printed ONCE per class by
    /// [`RefusalCensus::report`] under its `retired by:` line; `None` for a class whose census
    /// lines carry no options. Trust (plan step 3.0, step-3 review 2026-10-05): before, the
    /// `[clean-below-gate]` options lived only in the per-refusal `Display`, which no production
    /// path formats, so no output carried them.
    pub(crate) const fn options(self) -> Option<&'static str> {
        match self {
            Self::CleanBelowGate => Some(clean_below_gate::CLASS_OPTIONS),
            _ => None,
        }
    }
}

/// Why the trust-ir frontend refused a reachable mono-item.
///
/// Every variant is a compile error at the call site. None of them is a reason
/// to compile the item some other way.
#[derive(Debug)]
pub(crate) enum FrontendRefusal {
    /// The instance IS a plain item, but its body lives in an upstream crate,
    /// so no `LocalDefId` keys the `trust_ir_of` query for it.
    ///
    /// Split out from the synthesized case below because the two have NOTHING
    /// in common as work items: this one is retired by a cross-crate producer
    /// input and is, measurably, the largest class on every real crate; that
    /// one is retired by lowering compiler-synthesized bodies. Counting them
    /// together hides the only number that matters.
    UpstreamBody { symbol: String, def_path: String, krate: String },
    /// The instance is not a plain item body at all (drop glue, vtable/fn-ptr
    /// shims, intrinsics, virtual entries). It is compiler-synthesized: there
    /// is no source body, so there is nothing for `trust_ir_of` to have
    /// produced and nothing to fall back to.
    SynthesizedInstance { symbol: String, detail: String },
    /// A local constructor used as a function value (a compiler-synthesized
    /// shim with no THIR body), or an upstream instance the
    /// `-Ztrust-ir-upstream-mir` lane could not extract or bridge. `detail`
    /// says which.
    NotALocalItem { symbol: String, detail: String },
    /// The instance carries generic arguments. `trust_ir_of` is keyed on
    /// `LocalDefId` and lowers the body PRE-MONOMORPHIZATION, so its Module is
    /// not this instance's IR and must not be emitted under this symbol.
    GenericInstance { symbol: String, args: String },
    /// The item's ABI is outside the fragment the backend emits. This is the
    /// same check the production path runs; it is a property of the instance,
    /// not of the IR, so both frontends must apply it.
    UnsupportedAbi { symbol: String, detail: String },
    /// Finalization did not install the assembled crate-module handoff.
    AssembledHandoffUnavailable { symbol: String },
    /// The handoff exists but carries no entry for the exact local definition.
    ExactAssembledBodyAbsent { symbol: String, def_index: u32, definition: String },
    /// A `#[custom_mir]` body: rustc's MIR-authoring dialect, whose THIR is a
    /// script the MIR builder interprets, not Rust to run. The producer declines
    /// it by name (plan 2026-09-29, step 2), and so does this frontend, on both
    /// lanes, before any module lookup.
    CustomMirBody { symbol: String },
    /// The checked handoff selected a FuncId the Module no longer carries.
    SelectedFunctionMissing { symbol: String, func_id: u32, functions: usize },
    /// The body function references a `FuncTy` the Module does not carry, so
    /// its parameter count — which the ABI cross-check needs — is unknowable.
    MissingFuncType { symbol: String, ty: u32 },
    /// `lower_module_to_lir` refused the module.
    ConverterRefused { symbol: String, detail: String },
    /// Trust (step 2 increment 3): the instance lane could not assemble this
    /// item's module. `detail` names the callee, edge or check that refused.
    InstanceAssembly { symbol: String, detail: String },
    /// Trust (step 2 increment 3): the instance-keyed PRODUCER
    /// (`trust_thir_lower::trust_ir_of_instance_body`) refused this item's own
    /// instance body. Classified BY VARIANT (see [`FrontendRefusal::class`]).
    InstanceProducerRefused {
        symbol: String,
        reason: String,
        refusal: trust_thir_lower::InstanceRefusal,
    },
    /// Trust (R-8 ledger item 1): the item's trust-ir can reach a runtime check
    /// (its own body or any function it calls) that F1 lowers to a bare trap.
    /// `detail` names the function, the check and its source location. Built by
    /// [`refuse_unfaithful_panic`] (the handoff, instance and crate-module lanes) and by
    /// [`panic_sites`] (the compiler lane: a check it cannot site faithfully).
    UnfaithfulPanic { symbol: String, detail: String },

    // -- crate-module mode (gap G2) ------------------------------------------
    /// There is no lowering context: no crate module was published for this
    /// Session, publication was refused, or the published module failed a
    /// WHOLE-MODULE precondition. `detail` is the producer's or this module's
    /// own reason, verbatim.
    CrateModuleUnavailable { symbol: String, detail: String },
    /// The published crate module carries no function under this item's
    /// `def_path_str`. The producer assembled a module and this body is not in
    /// it — the crate-module spelling of `ProducerDeclined`.
    NotInCrateModule { symbol: String, def_path: String },
    /// The published crate module carries this `def_path_str` as a BODYLESS
    /// declaration. A declaration is an opaque external symbol; there is no
    /// body to emit.
    DeclarationOnlyInCrateModule { symbol: String, def_path: String },
    /// More than one function in the published module holds this
    /// `def_path_str`, so it is resolvable by no one
    /// (`PublishedCrateModule::ambiguous_symbols`).
    AmbiguousInCrateModule { symbol: String, def_path: String },
    /// THE NEGATIVE GATE, affirmative arm: `body_gate: Some(Ungated)`.
    UngatedBody { symbol: String, func: u32 },
    /// THE NEGATIVE GATE, absent arm: `body_gate: None` — no licensing claim
    /// at all. Kept as a SEPARATE variant from [`Self::UngatedBody`]; see the
    /// policy note on [`body_gate_verdict`].
    UnlicensedBody { symbol: String, func: u32 },
    /// The gate is structurally malformed — `Gated` with a blank authority is
    /// a positive license naming no gate.
    MalformedBodyGate { symbol: String, func: u32, detail: String },
    /// The body is gated, but the PRODUCER's deny-by-default codegen inventory
    /// (`PublishedCrateModule::codegen_inventory`) does not list it. Metadata
    /// on the body never grants what the inventory withholds.
    UnlicensedByProducer { symbol: String, func: u32 },
    /// The function admitted for this mangled symbol carries a different
    /// link-time name. Emitting it would ship one function under another's
    /// symbol.
    LinkNameMismatch { symbol: String, func: u32, found: String },
    /// Trust (effect conservation, D28): the effect-conservation check refused the body, or did
    /// not run. `detail` is its rendered tag list (or why there is no verdict).
    EffectNotConserved { symbol: String, detail: String },
    /// Trust (step 2 increment 4c): the drop-glue lane (`drop_glue_lane`) refused a glue item, or
    /// a drop the item reaches did not resolve to glue. `class` is the gap's own class (an
    /// upstream `Drop` impl is `upstream-body`, an unsynthesized shape `synthesized-instance`, a
    /// destructor with no admitted body `producer-declined`); `detail` names the drop and why.
    DropGlue { symbol: String, class: RefusalClass, detail: String },
    /// Trust (plan step 3.0): F1 refused this item because of a Clean-origin body — the item IS
    /// one, of this crate or imported (`role` = [`clean_below_gate::CleanRole::Own`]), a Rust
    /// body that reaches one. Built only by [`clean_below_gate`]: from the refusal the lane
    /// made (kept verbatim in `why`) or actual exported Clean-origin identities, without MIR.
    CleanBelowGate { symbol: String, row: clean_below_gate::CleanRowRefusal },
    /// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's codegen module refused a
    /// body; `detail` names the rule.
    CodegenModule { symbol: String, detail: String },
    /// Trust (step 2 increment 5, sub-step 5.4.2): trust-cg's preflight census refused a
    /// function of the codegen module. `variant` is the `CompileError` variant
    /// (`Adapter::<variant>` for an adapter refusal); `symbol` is empty when the refusal names
    /// no function.
    TrustCgRefused { symbol: String, variant: String, detail: String },
    /// Trust (step 2 increment 5, sub-step 5.4.2; dormant until 5.6): a callee declaration's
    /// signature is not rustc's FnAbi-legalized one.
    CalleeAbiMismatch { symbol: String, detail: String },
    /// Trust (D39): absent entries keep upstream-body; malformed inputs name the failed check.
    UpstreamEntry { symbol: String, check: &'static str, detail: String },
}

impl FrontendRefusal {
    /// The class this refusal counts under. Total by construction — a new
    /// variant does not compile until it names its class, which is the point.
    pub(crate) fn class(&self) -> RefusalClass {
        match self {
            Self::UpstreamBody { .. } => RefusalClass::UpstreamBody,
            Self::UpstreamEntry { check: "absent", .. } => RefusalClass::UpstreamBody,
            Self::UpstreamEntry { .. } => RefusalClass::UpstreamEntry,
            Self::SynthesizedInstance { .. } => RefusalClass::SynthesizedInstance,
            Self::GenericInstance { .. } => RefusalClass::GenericInstance,
            Self::UnsupportedAbi { .. } => RefusalClass::UnsupportedAbi,
            Self::NotALocalItem { .. } => RefusalClass::NotALocalItem,
            // The assembled handoff IS the crate-module lowering context on the
            // selected path, so its absence is the unusable-crate-module class.
            Self::AssembledHandoffUnavailable { .. } => RefusalClass::CrateModuleUnavailable,
            // The producer assembled a module and this exact body is not in it.
            Self::ExactAssembledBodyAbsent { .. } => RefusalClass::ProducerDeclined,
            Self::CustomMirBody { .. } => RefusalClass::ProducerDeclined,
            Self::SelectedFunctionMissing { .. } | Self::MissingFuncType { .. } => {
                RefusalClass::MalformedProducerModule
            }
            Self::ConverterRefused { .. } => RefusalClass::ConverterRefused,
            Self::InstanceAssembly { .. } => RefusalClass::InstanceAssembly,
            // By variant: an elided drop is increment 4's work item; a module the instance lane
            // cannot make self-contained (pending const, unsignable callee, standalone
            // validation) is the lane's own gap; everything else is producer coverage.
            Self::InstanceProducerRefused { refusal, .. } => match refusal {
                trust_thir_lower::InstanceRefusal::LaneRefused("drop-bearing") => {
                    RefusalClass::ElidedDrop
                }
                trust_thir_lower::InstanceRefusal::PendingConsts
                | trust_thir_lower::InstanceRefusal::UnsignableCallee(_)
                | trust_thir_lower::InstanceRefusal::NotSelfContained(_)
                | trust_thir_lower::InstanceRefusal::CalleeMisresolved(_) => {
                    RefusalClass::InstanceAssembly
                }
                _ => RefusalClass::ProducerDeclined,
            },
            Self::UnfaithfulPanic { .. } => RefusalClass::UnfaithfulPanic,
            Self::EffectNotConserved { .. } => RefusalClass::EffectNotConserved,
            Self::DropGlue { class, .. } => *class,
            Self::CleanBelowGate { .. } => RefusalClass::CleanBelowGate,
            Self::CrateModuleUnavailable { .. } => RefusalClass::CrateModuleUnavailable,
            Self::NotInCrateModule { .. } | Self::DeclarationOnlyInCrateModule { .. } => {
                RefusalClass::ProducerDeclined
            }
            Self::AmbiguousInCrateModule { .. }
            | Self::MalformedBodyGate { .. }
            | Self::LinkNameMismatch { .. } => RefusalClass::MalformedProducerModule,
            Self::UngatedBody { .. } => RefusalClass::UngatedBody,
            Self::UnlicensedBody { .. } => RefusalClass::UnlicensedBody,
            Self::UnlicensedByProducer { .. } => RefusalClass::UnlicensedByProducer,
            Self::CodegenModule { .. } => RefusalClass::CodegenModule,
            Self::TrustCgRefused { .. } => RefusalClass::TrustCgRefused,
            Self::CalleeAbiMismatch { .. } => RefusalClass::CalleeAbiMismatch,
        }
    }

    /// The per-item half of a census sample: the mangled symbol plus ONLY the
    /// detail that distinguishes this item from its classmates.
    ///
    /// Deliberately NOT `to_string()`. The class explanation is printed once per
    /// class by [`RefusalCensus::report`], so a sample that repeated it would
    /// print one sentence three times and bury the symbol — which is the whole
    /// failure mode the census exists to fix, reproduced inside the fix.
    #[allow(dead_code)] // Trust (G1): read by `RefusalCensus`, which is INERT — see below.
    pub(crate) fn sample_line(&self) -> String {
        match self {
            Self::UpstreamBody { symbol, def_path, .. } => format!("`{symbol}` = {def_path}"),
            Self::SynthesizedInstance { symbol, detail } => format!("`{symbol}` = {detail}"),
            Self::GenericInstance { symbol, args } => format!("`{symbol}` args {args}"),
            Self::UnsupportedAbi { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::NotALocalItem { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::AssembledHandoffUnavailable { symbol } => format!("`{symbol}`"),
            Self::ExactAssembledBodyAbsent { symbol, def_index, definition } => {
                format!("`{symbol}` = DefIndex({def_index}), {definition}")
            }
            Self::CustomMirBody { symbol } => {
                format!("`{symbol}`: a `#[custom_mir]` dialect body, not Rust (refused by name)")
            }
            Self::SelectedFunctionMissing { symbol, func_id, functions } => {
                format!("`{symbol}`: FuncId({func_id}) of {functions} function(s)")
            }
            Self::MissingFuncType { symbol, ty } => {
                format!("`{symbol}`: FuncTyId({ty}) not in the Module")
            }
            Self::ConverterRefused { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::InstanceAssembly { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::InstanceProducerRefused { symbol, reason, .. } => {
                format!("`{symbol}`: instance producer refused: {reason}")
            }
            Self::UnfaithfulPanic { symbol, detail } => format!(
                "`{symbol}`: {detail}; a failed check would lower to a bare trap (no panic \
                 message, location or hook, SIGTRAP instead of abort)"
            ),
            Self::CrateModuleUnavailable { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::EffectNotConserved { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::DropGlue { symbol, detail, .. } => format!("`{symbol}`: drop glue: {detail}"),
            Self::CleanBelowGate { symbol, row } => format!("`{symbol}`: {}", row.sample()),
            Self::NotInCrateModule { symbol, def_path } => format!("`{symbol}` = {def_path}"),
            Self::DeclarationOnlyInCrateModule { symbol, def_path } => {
                format!("`{symbol}` = {def_path} (declaration only)")
            }
            Self::AmbiguousInCrateModule { symbol, def_path } => {
                format!("`{symbol}` = {def_path}")
            }
            Self::UngatedBody { symbol, func } => format!("`{symbol}` = FuncId({func})"),
            Self::UnlicensedBody { symbol, func } => format!("`{symbol}` = FuncId({func})"),
            Self::MalformedBodyGate { symbol, func, detail } => {
                format!("`{symbol}` = FuncId({func}): {detail}")
            }
            Self::UnlicensedByProducer { symbol, func } => {
                format!("`{symbol}` = FuncId({func})")
            }
            Self::LinkNameMismatch { symbol, func, found } => {
                format!("`{symbol}` = FuncId({func}) is named `{found}`")
            }
            Self::CodegenModule { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::TrustCgRefused { symbol, variant, detail } => {
                format!("`{symbol}`: [trust-cg-refused:{variant}] {detail}")
            }
            Self::CalleeAbiMismatch { symbol, detail } => format!("`{symbol}`: {detail}"),
            Self::UpstreamEntry { symbol, check, detail } => {
                format!("`{symbol}`: {check}: {detail}")
            }
        }
    }
}

impl std::fmt::Display for FrontendRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The class tag leads EVERY message. It is the only thing that makes an
        // unaggregated refusal list — which is what a caller that does not
        // assemble a `RefusalCensus` still prints — classifiable at all.
        write!(f, "[{}] ", self.class().tag())?;
        match self {
            Self::UpstreamEntry { symbol, check, detail } => {
                write!(f, "`{symbol}`: {check}: {detail}")
            }
            Self::UpstreamBody { symbol, def_path, krate } => write!(
                f,
                "`{symbol}`: the trust-ir frontend has no artifact for this instance (body lives \
                 in upstream crate `{krate}`, `{def_path}`); `trust_ir_of` is keyed on a local \
                 body's `LocalDefId` and THIR is a local-only query"
            ),
            Self::SynthesizedInstance { symbol, detail } => write!(
                f,
                "`{symbol}`: the trust-ir frontend has no artifact for this instance \
                 (compiler-synthesized instance kind {detail}); it has no source body for \
                 `trust_ir_of` to have lowered"
            ),
            Self::NotALocalItem { symbol, detail } => write!(
                f,
                "`{symbol}`: the trust-ir frontend has no artifact for this instance ({detail}); \
                 `trust_ir_of` is keyed on a local body's `LocalDefId`"
            ),
            Self::GenericInstance { symbol, args } => write!(
                f,
                "`{symbol}`: instance carries generic arguments `{args}`, but `trust_ir_of` \
                 lowers the body pre-monomorphization; emitting that Module under this symbol \
                 would ship IR that was never instantiated"
            ),
            Self::UnsupportedAbi { symbol, detail } => {
                write!(f, "`{symbol}`: unsupported definition ABI: {detail}")
            }
            Self::AssembledHandoffUnavailable { symbol } => write!(
                f,
                "`{symbol}`: finalization installed no validated assembled Trust-IR module; \
                 refusing to retry a per-body artifact"
            ),
            Self::ExactAssembledBodyAbsent { symbol, def_index, definition } => write!(
                f,
                "`{symbol}`: the assembled Trust-IR handoff has no body for exact identity \
                 (DefIndex({def_index}), {definition}); refusing display-name selection and \
                 per-body fallback"
            ),
            Self::CustomMirBody { symbol } => write!(
                f,
                "`{symbol}`: a `#[custom_mir]` body is rustc's MIR-authoring dialect, not Rust; \
                 the trust-ir path refuses it, and its tests stay on the MIR test oracle"
            ),
            Self::SelectedFunctionMissing { symbol, func_id, functions } => write!(
                f,
                "`{symbol}`: the assembled Trust-IR handoff selected missing FuncId({func_id}); \
                 the Module carries {functions} function(s)"
            ),
            Self::MissingFuncType { symbol, ty } => write!(
                f,
                "`{symbol}`: the body function names `FuncTyId({ty})`, which the produced Module \
                 does not carry"
            ),
            Self::ConverterRefused { symbol, detail } => write!(
                f,
                "`{symbol}`: `lower_module_to_lir` refused the source-derived Module: {detail}"
            ),
            Self::InstanceAssembly { symbol, detail } => write!(
                f,
                "`{symbol}`: the instance lane could not assemble this item's codegen module: \
                 {detail}"
            ),
            Self::InstanceProducerRefused { symbol, reason, .. } => write!(
                f,
                "`{symbol}`: the instance-keyed producer (`trust_ir_of_instance_body`) refused \
                 this instance: {reason}"
            ),
            Self::UnfaithfulPanic { symbol, detail } => write!(
                f,
                "`{symbol}`: {detail}; a failed check would lower to a bare trap (no panic \
                 message, location or hook, SIGTRAP instead of abort), where MIR->LLVM panics, so \
                 the function is refused under every output-gate policy until the panic path is \
                 faithful (R-8 ledger item P)"
            ),
            Self::CrateModuleUnavailable { symbol, detail } => {
                write!(f, "`{symbol}`: no usable published crate module to lower against: {detail}")
            }
            Self::EffectNotConserved { symbol, detail } => write!(
                f,
                "`{symbol}`: the body's trust-ir is not the program — the effect-conservation \
                 check refused it against rustc's own MIR: {detail}"
            ),
            Self::DropGlue { symbol, detail, .. } => write!(
                f,
                "`{symbol}`: the drop-glue lane (step 2 increment 4c) cannot resolve this item's \
                 drops to synthesized glue: {detail}"
            ),
            Self::CleanBelowGate { symbol, row } => write!(f, "`{symbol}`: {}", row.message()),
            Self::NotInCrateModule { symbol, def_path } => write!(
                f,
                "`{symbol}` (`{def_path}`): the published crate module carries no function under \
                 this def path, so the producer never lowered this body"
            ),
            Self::DeclarationOnlyInCrateModule { symbol, def_path } => write!(
                f,
                "`{symbol}` (`{def_path}`): the published crate module carries this def path as \
                 a BODYLESS declaration; a declaration is an opaque external symbol and there is \
                 no body to emit"
            ),
            Self::AmbiguousInCrateModule { symbol, def_path } => write!(
                f,
                "`{symbol}` (`{def_path}`): more than one function in the published crate module \
                 holds this def path, so it is resolvable by no one; refusing rather than taking \
                 the first match"
            ),
            Self::UngatedBody { symbol, func } => write!(
                f,
                "`{symbol}` (FuncId {func}): the body carries `body_gate: ungated` — an \
                 AFFIRMATIVE producer claim that no verification gate was applied to it. A \
                 codegen consumer must refuse it. This is not the absent-claim state; see \
                 [{}]",
                RefusalClass::UnlicensedBody.tag()
            ),
            Self::UnlicensedBody { symbol, func } => write!(
                f,
                "`{symbol}` (FuncId {func}): the body makes NO licensing claim at all \
                 (`body_gate` absent — the pre-v41 grandfather state). Refused: this consumer's \
                 input is a module assembled IN THIS PROCESS at a submodule pin that has v41, so \
                 there is no legacy artifact to grandfather, and permitting an absent interlock \
                 would make dropping the field the cheapest way to launder a body that \
                 `ungated` is refused for. Distinct from [{}], which is an assertion rather than \
                 an absence",
                RefusalClass::UngatedBody.tag()
            ),
            Self::MalformedBodyGate { symbol, func, detail } => write!(
                f,
                "`{symbol}` (FuncId {func}): the v41 codegen license is malformed: {detail}"
            ),
            Self::UnlicensedByProducer { symbol, func } => write!(
                f,
                "`{symbol}` (FuncId {func}): the producer's deny-by-default codegen inventory \
                 (`PublishedCrateModule::codegen_inventory`) does not list this function. The \
                 body's own `body_gate` does not grant what the inventory withholds"
            ),
            Self::LinkNameMismatch { symbol, func, found } => write!(
                f,
                "`{symbol}` (FuncId {func}): the admitted function's link-time name is \
                 `{found}`; refusing to emit one function under another's symbol"
            ),
            Self::CodegenModule { symbol, detail } => {
                write!(f, "`{symbol}`: the compiler lane's codegen module refused it: {detail}")
            }
            Self::TrustCgRefused { symbol, variant, detail } => write!(
                f,
                "`{symbol}`: [trust-cg-refused:{variant}] trust-cg's preflight census refused it \
                 on the compiler lane: {detail}"
            ),
            Self::CalleeAbiMismatch { symbol, detail } => write!(
                f,
                "`{symbol}`: a callee declaration's signature is not rustc's FnAbi-legalized \
                 one: {detail}"
            ),
        }
    }
}

/// How many example symbols a census prints per class.
///
/// Bounded ON PURPOSE. The unaggregated list this replaces prints one line per
/// refused item, which on a real crate is hundreds of mangled symbols — MEASURED
/// 159 lines for a nine-line `Vec<u64>` + `HashMap<String, u64>` program. A wall
/// of symbols is not a measurement; the counts are, and three names per class is
/// enough to go look at one.
#[allow(dead_code)] // Trust (G1): read by `RefusalCensus`, which is INERT — see below.
const CENSUS_SAMPLES_PER_CLASS: usize = 3;

/// The aggregate picture of one compilation's refusals.
///
/// # Why an aggregate, and why it is not a softening
///
/// The refusal set is already accumulated rather than short-circuited, so a user
/// does get every item in one compile. What they do not get is the SHAPE: which
/// classes, in what proportion, and what would retire each. Those are different
/// questions with different answers — on the nine-line program above, the class
/// that dominates (`upstream-body`, 137/160) cannot be retired by any change to
/// the local producer, while the class the design conversation is about
/// (`generic-instance`) measures ZERO on that same program. A flat list of 159
/// mangled symbols hides exactly that.
///
/// Nothing here changes what is admitted. The census counts refusals; it never
/// produces one, never suppresses one, and the compilation still fails. This is
/// a REPORTING change, and it is the only kind of change that can be made here
/// without weakening the fail-closed contract: adding a fallback would.
///
/// # WIRED
///
/// `lib.rs` (`codegen_crate_from_trust_ir`, step 5) records every
/// [`lower_instance`] refusal here and `fatal`s with [`RefusalCensus::report`];
/// the per-item class tag on `FrontendRefusal`'s `Display` still leads every
/// individual message.
#[allow(dead_code)] // Trust (G1): INERT until `lib.rs` step 5 records into it — see above.
#[derive(Debug, Default)]
pub(crate) struct RefusalCensus {
    /// Parallel to [`RefusalClass::ALL`]: counts, then bounded samples.
    counts: [usize; CLASS_COUNT],
    samples: [Vec<String>; CLASS_COUNT],
    total: usize,
}

#[allow(dead_code)] // Trust (G1): INERT until `lib.rs` step 5 records into it — see above.
impl RefusalCensus {
    /// Record one refusal. Consumes it: the census is the only owner of the
    /// message, so nothing can report a refusal twice.
    pub(crate) fn record(&mut self, refusal: FrontendRefusal) {
        let slot = refusal.class().slot();
        self.counts[slot] += 1;
        self.total += 1;
        if self.samples[slot].len() < CENSUS_SAMPLES_PER_CLASS {
            self.samples[slot].push(refusal.sample_line());
        }
    }

    /// Total refusals recorded.
    pub(crate) const fn len(&self) -> usize {
        self.total
    }

    /// Whether anything was refused. `false` is the only value that may reach
    /// the linker.
    pub(crate) const fn is_empty(&self) -> bool {
        self.total == 0
    }

    /// Count for one class, for callers that want to assert on the shape rather
    /// than parse the report.
    pub(crate) fn count(&self, class: RefusalClass) -> usize {
        self.counts[class.slot()]
    }

    /// The full census, rendered for `dcx().fatal`.
    ///
    /// Classes are ordered by DESCENDING count so the first line is the binding
    /// constraint, with [`RefusalClass::ALL`] order as the tie-break; empty
    /// classes are omitted entirely.
    ///
    /// # The call-site wiring this expects (`lib.rs`, `codegen_crate_from_trust_ir`)
    ///
    /// ```text
    /// -   let mut refusals: Vec<String> = Vec::new();
    /// +   let mut census = trust_ir_frontend::RefusalCensus::default();
    ///
    /// -           Err(refusal) => refusals.push(refusal.to_string()),
    /// +           Err(refusal) => census.record(refusal),
    ///
    /// -   if !refusals.is_empty() {
    /// -       let listed = refusals.iter().map(|r| format!("  {r}")).collect::<Vec<_>>().join("\n");
    /// -       tcx.dcx().fatal(format!(
    /// -           "-Ztrust-cg-frontend=trust-ir refused {} of {reachable} reachable function(s); \
    /// -            this frontend never falls back to the MIR path:\n{listed}",
    /// -           refusals.len()
    /// -       ));
    /// -   }
    /// +   if !census.is_empty() {
    /// +       tcx.dcx().fatal(census.report(reachable));
    /// +   }
    /// ```
    ///
    /// The `refused` field of the existing `tracing::info!` becomes
    /// `census.len()`. Nothing else moves, and the `fatal` stays a `fatal`.
    pub(crate) fn report(&self, reachable: usize) -> String {
        let mut order: Vec<usize> = (0..CLASS_COUNT).filter(|i| self.counts[*i] > 0).collect();
        order.sort_by_key(|i| (std::cmp::Reverse(self.counts[*i]), *i));

        let mut out = format!(
            "-Ztrust-cg-frontend=trust-ir refused {} of {reachable} reachable function(s); \
             this frontend never falls back to the MIR path.\n\n\
             REFUSAL CENSUS (by class, largest first) — each line names what would retire it:\n",
            self.total
        );
        for i in order {
            let class = RefusalClass::ALL[i];
            let count = self.counts[i];
            // Integer permille, so a class that is 0.5% does not print as 0%
            // and read as "empty".
            let permille =
                if reachable == 0 { 0 } else { (count.saturating_mul(1000)) / reachable };
            out.push_str(&format!(
                "\n  {count:>6}  ({}.{}%)  [{}]\n            retired by: {}\n",
                permille / 10,
                permille % 10,
                class.tag(),
                class.retired_by()
            ));
            // Trust (plan step 3.0): the class's options, once, not once per sample.
            if let Some(options) = class.options() {
                out.push_str(&format!("            until then: {options}\n"));
            }
            for sample in &self.samples[i] {
                out.push_str(&format!("            e.g. {sample}\n"));
            }
            if count > self.samples[i].len() {
                out.push_str(&format!(
                    "            ... and {} more in this class (samples are capped at {})\n",
                    count - self.samples[i].len(),
                    CENSUS_SAMPLES_PER_CLASS
                ));
            }
        }
        out.push_str(
            "\nThe refusals above are the measurement this flag exists to produce. Adding a \
             per-item MIR fallback would make the flag compile everything and measure nothing, \
             which is precisely why the earlier log-only probe was worthless; do not add one.",
        );
        out
    }
}

/// Whether [`local_body_def`] admits a local item that carries type or const
/// arguments.
///
/// Trust (step 2 increment 3): the DEFAULT lane admits it
/// ([`GenericPolicy::AdmitConcrete`]) because the instance lane
/// (`instance_assembly`) lowers the concrete instance itself, keyed on
/// `ty::Instance`. Crate-module mode keeps [`GenericPolicy::Refuse`]: its
/// published module is PRE-monomorphization, so a real monomorphization is no
/// more emittable from it than it ever was.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GenericPolicy {
    Refuse,
    AdmitConcrete,
}

/// Resolve the `LocalDefId` whose body IS this instance's body, or say
/// precisely why there is none.
///
/// # THE DESIGN, AS IMPLEMENTED (step 2 increment 3)
///
/// `trust_ir_of(tcx, def: LocalDefId)` is a per-BODY, PRE-monomorphization THIR
/// query; the inventory this frontend compiles
/// (`collect_and_partition_mono_items`) is per-`ty::Instance` and
/// POST-monomorphization. This function projects the one onto the other, and
/// under [`GenericPolicy::Refuse`] it can only do that by refusing everything
/// that does not project.
///
/// The producer is now keyed on the instance, as this note used to propose:
/// `trust_thir_lower::trust_ir_of_instance_body(tcx, instance)` lowers the
/// local body's THIR with `instance.args` threaded through the type mapper and
/// every callee-resolution site (normalizing at
/// `TypingEnv::fully_monomorphized()`, so `map_ty`'s `ty::Param` arm is never
/// reached and `T` is never spelled `Ty::Unit`), names the body
/// `tcx.symbol_name(instance)`, and appends one signed declaration per callee
/// edge, named by that callee instance's mangled symbol. The codegen-time
/// assembler (`instance_assembly`) keys its slots on `ty::Instance`, so
/// `pick::<u8>` and `pick::<u16>` are two bodies, and splices each concrete
/// generic instance into a private copy of the assembled crate module. Under
/// [`GenericPolicy::AdmitConcrete`] this function therefore admits a local item
/// with concrete type/const arguments and leaves it to that lane.
///
/// The monomorphic-first choice this note used to flag as an open owner
/// question is settled by R-4 of the sole-compile-path plan: trust-ir stays
/// first-order and each instantiation is its own body; generic templates travel
/// in metadata (increment 6) and are instantiated by the consumer.
///
/// # The upstream half is still a SECOND producer input
///
/// Measured over `collect_and_partition_mono_items` on a stock nightly: on a
/// nine-line `Vec<u64>` + `HashMap<String,u64>` program, 137 of 160 reachable
/// items are `upstream-body` and 0 are `generic-instance`. THIR does not exist
/// off-crate at all (`thir_body` is keyed on `LocalDefId`), while
/// `tcx.instance_mir` has a body for 100% of that class — so it is retired by
/// trust-ir in metadata (increment 6), not by a wider key here.
///
/// # The lifetime-only carve-out
///
/// A region argument substitutes nothing that exists at runtime: codegen erases
/// regions and rustc mangles ONE symbol for the family, so the
/// pre-monomorphization body IS that instance's body. Under
/// [`GenericPolicy::Refuse`] that is the end of what the `LocalDefId` key can
/// admit; one type or const argument is a real monomorphization, whose `T = u8`
/// and `T = String` differ in layout, drop behaviour and symbol, and emitting
/// the identity body for it would spell `T` as `Ty::Unit` — the
/// manufactured-agreement failure `param_opaque` exists to prevent. The generic
/// class is retired by changing the KEY (the instance lane), never by widening
/// this carve-out.
fn local_body_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    policy: GenericPolicy,
) -> Result<rustc_span::def_id::LocalDefId, FrontendRefusal> {
    // Only a plain item body has a THIR the producer lowers. Every other
    // `InstanceKind` (drop glue, vtable/fn-ptr shims, `#[no_mangle]` re-exports
    // of foreign definitions, intrinsics) is compiler-synthesized: it has no
    // source body at all, so there is nothing for `trust_ir_of` to have
    // produced and nothing to fall back to.
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return Err(FrontendRefusal::SynthesizedInstance {
            symbol: symbol.to_string(),
            detail: format!("{:?}", instance.def),
        });
    };
    let Some(local) = def_id.as_local() else {
        return Err(FrontendRefusal::UpstreamBody {
            symbol: symbol.to_string(),
            def_path: tcx.def_path_str(def_id),
            krate: tcx.crate_name(def_id.krate).to_string(),
        });
    };
    // A CONSTRUCTOR used as a function value (`map(Value::Number)`) is a
    // compiler-synthesized shim: the variant/struct declaration owns no THIR
    // body, so forcing `trust_ir_of` on it ICEs inside `thir_body`
    // (`has no associated body`). Refuse it by name instead — it is the same
    // no-source-body class as the InstanceKind shims above.
    if matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Ctor(..)) {
        return Err(FrontendRefusal::NotALocalItem {
            symbol: symbol.to_string(),
            detail: format!(
                "constructor shim `{}` has no source body (compiler-synthesized)",
                tcx.def_path_str(def_id)
            ),
        });
    }
    // A LIFETIME-ONLY instantiation is not a monomorphization.
    //
    // The refusal below exists because `trust_ir_of` lowers a body BEFORE
    // monomorphization, so its Module is not the IR of an instance that
    // substituted types or consts. A region argument substitutes neither: regions
    // have no runtime representation at all, codegen erases them (every arg here
    // is `'{erased}` by the time an `Instance` reaches codegen), and rustc mangles
    // ONE symbol for the whole family — which is why `<Input<'_> as Debug>::fmt`
    // arrives with `args = ['{erased}]` and a single mangled name. For such an
    // instance the pre-monomorphization body IS this instance's body, so admitting
    // it does not emit IR that was never instantiated; it emits the only IR there
    // is.
    //
    // Kept as narrow as the claim: EVERY argument must be a region. One type or
    // const argument and this is a real monomorphization again, refused as before.
    // MEASURED: 526 of the 1,677 generic refusals across the 277 real crates that
    // reach this frontend are lifetime-only.
    if !instance.args.is_empty() && !instance.args.iter().all(|arg| arg.as_region().is_some()) {
        // Trust (step 2 increment 3): a CONCRETE monomorphization is the instance
        // lane's to lower. Anything still carrying a parameter or an inference
        // variable has no concrete instance and is refused on every policy.
        let concrete = !instance.args.has_non_region_param() && !instance.args.has_infer();
        if policy == GenericPolicy::AdmitConcrete && concrete {
            return Ok(local);
        }
        return Err(FrontendRefusal::GenericInstance {
            symbol: symbol.to_string(),
            args: format!("{:?}", instance.args),
        });
    }
    Ok(local)
}

/// Lower ONE reachable mono-item through source -> assembled Trust-IR -> LIR.
///
/// `validate_abi` is the production path's instance-ABI check
/// (`validate_codegen_instance_abi`), threaded in so the two frontends admit
/// exactly the same symbols. Its third argument is "how many arguments the
/// executable IR exposes", which rustc's `FnAbi` is cross-checked against; on
/// the MIR path that is `mir::Body::arg_count`, and here it is the produced
/// `FuncTy`'s parameter count — the same question asked of the IR that will
/// actually be emitted, which is what makes the check meaningful on this path
/// rather than decorative.
///
/// Trust (step 2 increment 3): WHERE the item's IR comes from was decided once,
/// before any item is lowered, by [`instance_assembly::plan`] over the whole
/// inventory: a HANDOFF item lowers from the finalize-assembled module exactly
/// as before (selected by exact `(DefIndex, DefPathHash)` identity, the shared
/// module never mutated), and an INSTANCE item lowers from the instance-keyed
/// codegen module, whose extra bodies the instance lane spliced. The lane is
/// chosen on a structural predicate, never by retrying after a failure, and
/// there is still no MIR fallback anywhere.
///
/// Returns the LIR function on success. `Err` is a compile error; it is never a
/// reason to lower this item from MIR instead.
pub(crate) fn lower_instance<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    plan: &mut instance_assembly::Plan<'tcx>,
    glue: &mut drop_glue_lane::GlueLane<'tcx>,
    index: usize,
    validate_abi: V,
) -> Result<TrustIrLoweredFunction, FrontendRefusal>
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    let symbol = tcx.symbol_name(instance).name.to_string();
    // Trust (merged with main's 4be07f9b01): a `#[custom_mir]` body is refused by
    // name before any module lookup, on this lane as on the crate-module lane. The
    // plan has no `local_body_def` call here (its lane predicate classifies the
    // item); a `#[custom_mir]` CALLEE is declined by the producer itself.
    if let ty::InstanceKind::Item(def_id) = instance.def {
        refuse_custom_mir(tcx, def_id, &symbol)?;
    }

    // The assembled module is the only artifact whose local call edges name
    // real bodies. Selection is by the producer's exact identity handoff, not
    // by `Function.name`: collision-renamed macro definitions intentionally no
    // longer equal `tcx.def_path_str(def)`. Any missing handoff/identity or any
    // lowering failure is final. Retrying the single-body artifact would both
    // reintroduce display-name ambiguity and turn its local callees back into
    // bodyless declarations.
    //
    // Trust (step 2 increment 4c): a DROP-GLUE item takes its IR from the drop-glue lane — its
    // synthesized body in the drop-resolved copy of the assembled module — and only when the lane
    // is active (the strict output gate, D18 OD-2 under D17's rule). Every other item, and every
    // glue item when the lane is not active, takes its IR from the plan as before.
    let glue_owned;
    let (module, func_id) = match glue.glue_item(tcx, instance, &symbol) {
        Some(source) => {
            let (module, func_id) = source?;
            glue_function_is_this_instance(&symbol, &module, func_id)?;
            glue_owned = module;
            (&*glue_owned, func_id)
        }
        None => {
            let spliced = template_oracle_rows(tcx, plan);
            let (module, func_id) = plan.source(index, instance, &symbol)?;
            selected_function_is_this_instance(tcx, instance, &symbol, module, func_id)?;
            observe_template_oracle(tcx, instance, &symbol, &spliced, module, func_id);
            (module, func_id)
        }
    };
    lower_from_module(tcx, instance, &symbol, module, func_id, &validate_abi, Some(glue))
}

/// Trust (PKG-C2d2 slice 1): the splice rows the template-instance TEST-ORACLE matches, read
/// BEFORE `Plan::source` borrows the plan. Empty, and never read, unless the oracle was requested.
fn template_oracle_rows(
    tcx: TyCtxt<'_>,
    plan: &instance_assembly::Plan<'_>,
) -> Vec<(String, FuncId, instance_assembly::Spliced)> {
    if tcx.sess.opts.unstable_opts.trust_ir_template_instance_oracle {
        plan.spliced()
    } else {
        Vec::new()
    }
}

/// Trust (PKG-C2d2 slice 1; INC6.5-NO-AUTHORITY in docs/DECISION_QUEUE.md): the ONLY codegen
/// reader of a level-S template, the default-off, driver-fenced template-instance equivalence
/// TEST-ORACLE. It runs only for a body D17 spliced whose per-instance MIR seam TEST-ORACLE
/// agreed (`Spliced::AppendedMirCompared`, matched by symbol and FuncId), only READS the selected
/// body, and returns nothing: agreement and a named refusal are notes; a mismatch, or any
/// negative-control outcome, ends the session before an artifact is written. It changes no plan,
/// module, selection, admission or output.
fn observe_template_oracle<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    spliced: &[(String, FuncId, instance_assembly::Spliced)],
    module: &trust_ir::Module,
    func_id: FuncId,
) {
    if !tcx.sess.opts.unstable_opts.trust_ir_template_instance_oracle
        || !spliced.iter().any(|(name, id, kind)| {
            name == symbol
                && *id == func_id
                && *kind == instance_assembly::Spliced::AppendedMirCompared
        })
    {
        return;
    }
    match trust_thir_lower::template_metadata::oracle::compare(tcx, instance, module, func_id) {
        Ok(outcome) => tcx.dcx().note(outcome.note(symbol)),
        Err(detail) => tcx
            .dcx()
            .fatal(format!("template-instance TEST-ORACLE disagreed for `{symbol}`: {detail}")),
    }
}

/// Trust (step 2 increment 5, sub-step 5.4.2): the compiler lane's SELECTION of one reachable
/// item's body — the order [`lower_instance`] takes, without its lowering tail:
///
/// 1. a `#[custom_mir]` body, refused by name;
/// 2. a drop-glue item, refused by name: D31(a) licenses exactly the direct and instance
///    lanes, so the drop-glue lane's authority is not recognized here (INC5.4-GLUE);
/// 3. the plan's source ([`instance_assembly::Plan::source`]) — the ONE source of every other
///    item's body, including admitted upstream R entries;
/// 4. the selected function is this instance ([`selected_function_is_this_instance`]).
///
/// A runtime check does not refuse here (PKG-CP): once M_cg is built, [`panic_sites`] folds
/// each constant-true check and sites every other check at rustc's panic entry, and refuses by
/// name a function holding a check it cannot site.
///
/// Returns the body's `FuncId` in the planned module and the item's symbol. It never clones a
/// module and never lowers anything: `codegen_module.rs` builds the one codegen module from
/// these selections.
pub(crate) fn select_for_codegen_module<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    plan: &mut instance_assembly::Plan<'tcx>,
    glue: &mut drop_glue_lane::GlueLane<'tcx>,
    index: usize,
) -> Result<(FuncId, String), FrontendRefusal> {
    let symbol = tcx.symbol_name(instance).name.to_string();
    if let ty::InstanceKind::Item(def_id) = instance.def {
        refuse_custom_mir(tcx, def_id, &symbol)?;
    }
    if glue.glue_item(tcx, instance, &symbol).is_some() {
        return Err(FrontendRefusal::DropGlue {
            symbol,
            class: RefusalClass::UnlicensedBody,
            detail:
                "the compiler lane licenses exactly the direct and instance lanes (owner ruling \
                     D31(a)); the drop-glue lane's `trust-drop-glue-lane-structural` authority is \
                     not recognized there (INC5.4-GLUE)"
                    .to_string(),
        });
    }
    let spliced = template_oracle_rows(tcx, plan);
    let (module, func_id) = plan.source(index, instance, &symbol)?;
    selected_function_is_this_instance(tcx, instance, &symbol, module, func_id)?;
    observe_template_oracle(tcx, instance, &symbol, &spliced, module, func_id);
    Ok((func_id, symbol))
}

/// Trust (step 2 increment 5, sub-step 5.4.2; design §3.1 rule 2): the identity of each
/// reachable body that rustc's inventory does not name. A body the instance lane spliced is
/// [`codegen_module::ResidueIdentity::InstanceSpliced`]; a finalize-assembled handoff body of a
/// local, non-generic definition is `Local`, under `tcx.symbol_name(Instance::mono(def))`, with
/// rustc's `FnAbi` read after the old lane's preconditions; anything else has no identity.
pub(crate) fn residue_identities<'tcx>(
    tcx: TyCtxt<'tcx>,
    producer: &trust_ir::Module,
    residue: &std::collections::BTreeSet<FuncId>,
    spliced: &[(String, FuncId, instance_assembly::Spliced)],
) -> std::collections::BTreeMap<FuncId, codegen_module::ResidueIdentity> {
    use codegen_module::ResidueIdentity;
    let mut out = std::collections::BTreeMap::new();
    if residue.is_empty() {
        return out;
    }
    let handoff: std::collections::BTreeMap<FuncId, u32> = tcx
        .sess
        .with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.codegen_body_ids(),
        )
        .into_iter()
        .map(|(def_index, func_id)| (func_id, def_index))
        .collect();
    for id in residue {
        if let Some((symbol, _, _)) = spliced.iter().find(|(_, func, _)| func == id) {
            out.insert(*id, ResidueIdentity::InstanceSpliced { symbol: symbol.clone() });
            continue;
        }
        let Some(def_index) = handoff.get(id) else {
            out.insert(
                *id,
                ResidueIdentity::Unidentified {
                    detail: "it is neither a finalize-assembled handoff body nor a body the \
                             instance lane spliced"
                        .to_string(),
                },
            );
            continue;
        };
        let def_id = rustc_span::def_id::LocalDefId {
            local_def_index: rustc_span::def_id::DefIndex::from_u32(*def_index),
        }
        .to_def_id();
        if tcx.generics_of(def_id).requires_monomorphization(tcx) {
            out.insert(
                *id,
                ResidueIdentity::Unidentified {
                    detail: format!(
                        "its definition `{}` is generic, so the identity-lowered handoff body is \
                         no instance's",
                        tcx.def_path_str(def_id)
                    ),
                },
            );
            continue;
        }
        let instance = ty::Instance::mono(tcx, def_id);
        let symbol = tcx.symbol_name(instance).name.to_string();
        let param_count = producer
            .function_by_id(*id)
            .and_then(|f| producer.func_types.get(f.ty.as_usize()))
            .map_or(0, |ty| ty.params.len());
        let identity = match abi_shape::abi_shape_of(tcx, instance, param_count) {
            Ok(abi) => ResidueIdentity::Local {
                symbol,
                abi,
                never_inline: crate::instance_is_never_inline(tcx, instance),
            },
            Err(detail) => ResidueIdentity::LocalAbiRefused { symbol, detail },
        };
        out.insert(*id, identity);
    }
    out
}

/// Trust (step 2 increment 4c): the function the drop-glue lane selected for a glue item must
/// already carry the item's symbol — the lane names every glue body by
/// `symbol_name(resolve_drop_glue(T))` — so `lower_from_module` never renames it.
fn glue_function_is_this_instance(
    symbol: &str,
    module: &trust_ir::Module,
    func_id: FuncId,
) -> Result<(), FrontendRefusal> {
    match module.function_by_id(func_id) {
        Some(function) if function.name == symbol => Ok(()),
        Some(function) => Err(FrontendRefusal::DropGlue {
            symbol: symbol.to_string(),
            class: RefusalClass::MalformedProducerModule,
            detail: format!(
                "internal: the lane selected FuncId({}) `{}` for this glue item",
                func_id.index(),
                function.name
            ),
        }),
        None => Err(FrontendRefusal::SelectedFunctionMissing {
            symbol: symbol.to_string(),
            func_id: func_id.index(),
            functions: module.functions.len(),
        }),
    }
}

/// Trust (step 2 increment 3): the function the plan selected must BE this instance before
/// `lower_from_module` lowers it. Either it already carries that symbol (an instance body the
/// frozen admission stamped, re-checked by the assembler), or it is the handoff's exact body for
/// this instance — the same `FuncId` in the module `star` extends, since a relink keeps its slot.
/// Anything else is a selection error, refused, never renamed. Trust (WS5.2): nothing renames it
/// afterwards either — `lower_from_module` refuses a selected function whose `Function.name` is
/// not `symbol` ([`FrontendRefusal::LinkNameMismatch`]).
fn selected_function_is_this_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    module: &trust_ir::Module,
    func_id: FuncId,
) -> Result<(), FrontendRefusal> {
    let Some(function) = module.function_by_id(func_id) else {
        return Err(FrontendRefusal::SelectedFunctionMissing {
            symbol: symbol.to_string(),
            func_id: func_id.index(),
            functions: module.functions.len(),
        });
    };
    if function.name == symbol {
        return Ok(());
    }
    let handoff =
        tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.exact_instance_body(tcx, instance),
        );
    match handoff {
        Ok(selected) if selected.func_id == func_id => Ok(()),
        _ => Err(FrontendRefusal::InstanceAssembly {
            symbol: symbol.to_string(),
            detail: format!(
                "internal: the selected FuncId({}) `{}` is neither named `{symbol}` nor the \
                 handoff's exact body for this instance; refusing to rename it",
                func_id.index(),
                function.name
            ),
        }),
    }
}

/// Trust: apply the same identity and custom-MIR refusals to a typed local dependency that
/// rustc's optimized mono inventory omitted. Its runtime checks are the compiler lane's
/// panic-site pass's ([`panic_sites`], PKG-CP), as every compiler-lane body's are.
pub(crate) fn validate_native_source_dependency<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    module: &trust_ir::Module,
    func_id: FuncId,
) -> Result<(), FrontendRefusal> {
    if let ty::InstanceKind::Item(def_id) = instance.def {
        refuse_custom_mir(tcx, def_id, symbol)?;
    }
    selected_function_is_this_instance(tcx, instance, symbol, module, func_id)
}

/// Trust (R-8 ledger item 1, plan §5): the first runtime CHECK the item's
/// trust-ir can reach, or `None`. PURE.
///
/// F1 lowers `Inst::Assert` — every overflow, shift, negation, division and
/// bounds check the producer emits — to a branch to a bare trap (`brk`): no
/// panic message, no `#[track_caller]` location, no panic hook, SIGTRAP instead
/// of the abort MIR->LLVM's panic path takes. That is a fail-OPEN behaviour
/// difference, so a function that can reach one is refused until the panic
/// path is faithful (ledger item P). "Reach" is the dependency census from the
/// item: the leaf inliner splices every reached callee body into the emitted
/// function, so a check in a callee is a check in the item. The converter's
/// other trap, `Inst::Unreachable`, is not a panic: it stands only where MIR has
/// `Unreachable` (or right after a trapping `Assert`), and reaching it is UB on
/// both paths, so it opens no behaviour difference to refuse.
///
/// SYNTACTIC: every reachable `Assert` refuses, including a check that can
/// never fail (a constant divisor, shift amount or in-bounds index) and one the
/// verifier PROVED. Item P retires the refusal, not a smarter scan.
pub(crate) fn reachable_runtime_check(module: &trust_ir::Module, root: FuncId) -> Option<String> {
    use trust_ir::function_dependencies::{DependencyNode, inspect_function_dependencies};
    let census = inspect_function_dependencies(module, root);
    for node in census.nodes() {
        let DependencyNode::Function(id) = node else { continue };
        let Some(function) = module.function_by_id(*id) else { continue };
        for block in &function.blocks {
            for (index, node) in block.body.iter().enumerate() {
                // Trust (trust-ir v54): an `AssertInvoke` is the same check (its failure
                // enters an in-frame landing pad); it is refused the same way.
                if matches!(
                    node.inst,
                    trust_ir::Inst::Assert { .. } | trust_ir::Inst::AssertInvoke { .. }
                ) {
                    let checks =
                        node.proofs.iter().map(|p| format!("{p:?}")).collect::<Vec<_>>().join(", ");
                    let at = node.span.as_ref().map_or_else(String::new, |span| {
                        format!(
                            " at {}:{}:{}",
                            module.file_name(span.file).unwrap_or("<unknown file>"),
                            span.line,
                            span.col
                        )
                    });
                    return Some(format!(
                        "reaches a runtime check (`Assert`{}) in `{}` (block {}, instruction \
                         {index}){at}",
                        if checks.is_empty() { String::new() } else { format!(" {checks}") },
                        // Trust (WS5.2): the def path the user wrote, not the link-time symbol.
                        function.display_path.as_deref().unwrap_or(&function.name),
                        block.id.index()
                    ));
                }
            }
        }
    }
    None
}

/// The assembled lowering tail: ABI cross-check, symbol stamping on a private
/// clone, `lower_module_to_lir`, and the gate source.
fn lower_from_module<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    produced: &trust_ir::Module,
    func_id: FuncId,
    validate_abi: &V,
    glue: Option<&mut drop_glue_lane::GlueLane<'tcx>>,
) -> Result<TrustIrLoweredFunction, FrontendRefusal>
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    let ir_param_count = {
        let function =
            produced.function_by_id(func_id).ok_or(FrontendRefusal::SelectedFunctionMissing {
                symbol: symbol.to_string(),
                func_id: func_id.index(),
                functions: produced.functions.len(),
            })?;
        // Trust (WS5.2): the producer names the selected body by its LINK-TIME
        // SYMBOL (`Function.name`, trust-ir v41). This path used to stamp
        // `symbol` onto a private clone; it now CHECKS that the producer's name
        // IS the symbol this compilation mangled for the exact instance, and
        // refuses by name on a split — emitting one function under another's
        // symbol is the silent corruption `compiled_module` guards at the far end.
        if function.name != symbol {
            return Err(FrontendRefusal::LinkNameMismatch {
                symbol: symbol.to_string(),
                func: func_id.index(),
                found: function.name.clone(),
            });
        }
        produced
            .func_types
            .get(function.ty.as_usize())
            .ok_or(FrontendRefusal::MissingFuncType {
                symbol: symbol.to_string(),
                ty: function.ty.index(),
            })?
            .params
            .len()
    };

    validate_abi(tcx, instance, ir_param_count)
        .map_err(|detail| FrontendRefusal::UnsupportedAbi { symbol: symbol.to_string(), detail })?;

    // Trust (step 2 increment 4c): every `Inst::Drop` this item reaches is resolved to a call of
    // synthesized glue (`drop_glue_lane`, frozen) in a private copy of the module, or the item is
    // refused naming the drop. An item that reaches no drop, or a session whose output-gate policy
    // is not strict (the lane is inactive), lowers from `produced` exactly as before, and the
    // converter refuses a reached `Inst::Drop` by name (the floor).
    let resolved;
    let produced: &trust_ir::Module = match glue {
        Some(lane) => match lane.resolve_for(tcx, produced, func_id, symbol)? {
            Some(module) => {
                resolved = module;
                &resolved
            }
            None => produced,
        },
        None => produced,
    };

    // Trust (R-8 ledger item 1): a function that can reach a runtime check is
    // refused, whatever the output-gate policy, until the panic path is faithful.
    refuse_unfaithful_panic(produced, func_id, symbol)?;

    // THE PASS-MODE CROSS-CHECK, minted exactly where it was earned. The call
    // above is the F1 ABI validator: it walks rustc's OWN `FnAbi` for this
    // instance and refuses every argument slot and the return slot whose
    // `PassMode` is outside the audited set (`PassMode::Indirect` is never
    // admitted), so the aggregates that reach the converter below have been
    // classified against the target's real ABI and not by a size rule.
    //
    // The producer stamps `StructPassingPolicy::Unclassified`
    // (`trust_thir_lower::stamp_target_info_if_vacuous`) — an honest declaration
    // that it performed NO aggregate classification — and trust-ir's contract
    // for that value says a backend needing a classification must refuse the
    // module rather than pick one. `lower_module_to_lir` therefore refuses such
    // a module BY NAME. This token is what lifts the refusal for this lane, and
    // it is minted only on the success path of the check that earns it.
    // WS7.13: the CALLER-OWED EXTENSION facts of this instance's parameter
    // slots ride on the same token, minted from the same `FnAbi` the validator
    // just walked plus the session target. They are what the proven-output
    // gate consults before it models a `bool` parameter; nothing else reads
    // them, and a failure to mint them is a refusal, never a silent `None`.
    let param_extensions = crate::instance_param_extensions(tcx, instance, ir_param_count)
        .map_err(|detail| FrontendRefusal::UnsupportedAbi { symbol: symbol.to_string(), detail })?;
    let abi_cross_check = trust_cg_bridge::AbiPassModeCrossCheck::attested_by(
        "rustc_codegen_trust_cg: validate_codegen_instance_abi_* over rustc's FnAbi PassMode \
         for this exact instance, immediately before lowering",
    )
    .with_param_extensions(param_extensions);

    // Trust (WS5.2): no rename. The selected function's name was checked above
    // to BE `symbol` (the producer names every body by its link-time symbol),
    // so the lowering context is the producer's module as published.
    //
    // PLAN ITEM K (2026-10-01): a private clone per function cost one
    // whole-module clone per admitted function, kept alive in every gate source
    // until emission (3,200 one-line functions: 23.6 GB RSS, 38 s). The shared
    // context is ONE copy of the module per session, used only when it still
    // names this function `symbol` and has the module's function count;
    // anything else takes the per-function clone exactly as before.
    let shared = shared_lowering_context(tcx, produced);
    let module: std::sync::Arc<trust_ir::Module> = match shared {
        Some(shared)
            if shared.functions.len() == produced.functions.len()
                && shared
                    .function_by_id(func_id)
                    .is_some_and(|function| function.name == symbol) =>
        {
            shared
        }
        _ => std::sync::Arc::new(produced.clone()),
    };

    let lir = trust_cg_bridge::lower_module_to_lir_with_abi_cross_check(
        &module,
        func_id,
        &abi_cross_check,
    )
    .map_err(|e| converter_refused(symbol, &module, e))?;

    let instructions: usize = lir.blocks.values().map(|block| block.instructions.len()).sum();
    tracing::debug!(
        symbol = %symbol,
        lir_instructions = instructions,
        "[trust_cg] trust-ir frontend lowered a function assembled Trust-IR -> LIR"
    );

    // The gate's SPEC INPUT: the producer Module, carried whole. This is
    // the same value `lower_module_to_lir` was just handed, so the specification
    // and the shipped bytes provably describe one function — the gate re-lowers
    // from it and refuses if the resulting symbol is not `symbol`.
    let gate_source = trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource {
        symbol: symbol.to_string(),
        module,
        func_id,
        // The gate EMITS the bytes this codegen unit ships, so it is a codegen
        // boundary too and must clear the same `struct_passing` admission the
        // converter above just cleared — on the same evidence, not a weaker one.
        abi_cross_check: Some(abi_cross_check),
    };

    Ok(TrustIrLoweredFunction { symbol: symbol.to_string(), lir, gate_source })
}

/// The converter's refusal for `symbol`. Trust (plan step 3.0): its
/// `CleanOriginBelowCodegenGate` — a `Producer::Clean` function was being lowered or would have
/// been inlined or called — is named `[clean-below-gate]` with the row's disclosed tier and
/// shape ([`clean_below_gate::converter_refusal`]); every other converter refusal stays
/// `[converter-refused]`. The converter's message is kept verbatim either way.
fn converter_refused(
    symbol: &str,
    module: &trust_ir::Module,
    error: trust_cg_bridge::ModuleLirError,
) -> FrontendRefusal {
    match &error {
        trust_cg_bridge::ModuleLirError::CleanOriginBelowCodegenGate { name, .. } => {
            clean_below_gate::converter_refusal(symbol, module, name, error.to_string())
        }
        _ => FrontendRefusal::ConverterRefused {
            symbol: symbol.to_string(),
            detail: error.to_string(),
        },
    }
}
/// One function that completed assembled Trust-IR -> `lower_module_to_lir`.
pub(crate) struct TrustIrLoweredFunction {
    /// The mangled symbol this function is emitted under.
    pub(crate) symbol: String,
    /// The LIR the shared object emitter consumes.
    pub(crate) lir: trust_cg_bridge::codegen_backend::LirFunction,
    /// The producer's trust-ir, kept so the proven-output gate has a
    /// specification for these bytes that was NOT derived from the lowering.
    pub(crate) gate_source: trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource,
}

/// Trust (owner ruling D17): the per-function COVERAGE DISCLOSURE of the
/// instance lane — one row per spliced body that reaches EMITTED code. Built at
/// codegen from the plan and the items that actually lowered; printed and
/// written (`<out-dir>/<output filestem>.trust-instance-coverage.json`) only after the
/// proven-output gate accepted the object, with the gate's verdict.
#[derive(Debug, Clone, Default)]
pub(crate) struct InstanceCoverage {
    pub(crate) rows: Vec<InstanceCoverageRow>,
}

/// Trust (step 2 increment 4c): what kind of spliced body a coverage row discloses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CoverageKind {
    /// A body the instance lane spliced (D17).
    Instance(instance_assembly::Spliced),
    /// A drop-glue body the drop-glue lane synthesized (D18 OD-2 under D17's rule): no source
    /// body, no per-instance MIR seam differential.
    DropGlue,
    /// Trust (step 2 increment 5, sub-step 5.4.2; design §3.1 rule 2): a local handoff body an
    /// emitted item reaches that rustc's inventory does not name (the MIR inliner removed it at
    /// -O), emitted `Internal` under its own symbol by the compiler lane.
    InventoryResidueLocal,
}

/// One spliced body that reaches emitted code.
#[derive(Debug, Clone)]
pub(crate) struct InstanceCoverageRow {
    /// The body's link-time symbol.
    pub(crate) symbol: String,
    /// Its id in the codegen module it was spliced into (the instance-keyed module, or a
    /// drop-resolved copy of the module an item lowered from).
    pub(crate) func_id: u32,
    /// Appended generic body (D17, no MIR seam differential), relinked handoff body, or
    /// synthesized drop glue (D18 OD-2).
    pub(crate) kind: CoverageKind,
    /// It is itself an emitted item.
    pub(crate) emitted_as_own_symbol: bool,
    /// Emitted items (other than itself) whose code inlines it.
    pub(crate) inlined_into: Vec<String>,
}

/// The coverage rows for the plan's spliced bodies, given the instance-lane
/// items that LOWERED (`(symbol, FuncId in the instance-keyed module)`). A
/// spliced body no emitted item reaches gets no row. `None` when no
/// instance-keyed module exists (the output is then byte-identical to a crate
/// with no instance lane, and no artifact is written).
pub(crate) fn instance_coverage(
    plan: &instance_assembly::Plan<'_>,
    emitted: &[(String, FuncId)],
    glue_rows: Vec<InstanceCoverageRow>,
) -> Option<InstanceCoverage> {
    use trust_ir::function_dependencies::{DependencyNode, inspect_function_dependencies};
    let Some(star) = plan.instance_module() else {
        // Trust (step 2 increment 4c): drop-glue rows are disclosed whether or not an
        // instance-keyed module exists.
        return (!glue_rows.is_empty()).then_some(InstanceCoverage { rows: glue_rows });
    };
    let reached: Vec<(&str, FuncId, std::collections::BTreeSet<FuncId>)> = emitted
        .iter()
        .map(|(symbol, root)| {
            let nodes = inspect_function_dependencies(star, *root)
                .nodes()
                .iter()
                .filter_map(|node| match node {
                    DependencyNode::Function(id) => Some(*id),
                    _ => None,
                })
                .collect();
            (symbol.as_str(), *root, nodes)
        })
        .collect();
    let mut rows = Vec::new();
    for (symbol, id, kind) in plan.spliced() {
        let emitted_as_own_symbol = reached.iter().any(|(_, root, _)| *root == id);
        let inlined_into: Vec<String> = reached
            .iter()
            .filter(|(_, root, nodes)| *root != id && nodes.contains(&id))
            .map(|(caller, _, _)| caller.to_string())
            .collect();
        if emitted_as_own_symbol || !inlined_into.is_empty() {
            rows.push(InstanceCoverageRow {
                symbol,
                func_id: id.index(),
                kind: CoverageKind::Instance(kind),
                emitted_as_own_symbol,
                inlined_into,
            });
        }
    }
    rows.extend(glue_rows);
    Some(InstanceCoverage { rows })
}

/// Where one M_cg body's code ships on the compiler lane (the coverage row's two placement
/// fields).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CodePlacement {
    /// The object defines the body under its own symbol (it has a certificate).
    pub(crate) emitted_as_own_symbol: bool,
    /// The emitted functions (other than the body itself) whose bytes contain its code, sorted.
    pub(crate) inlined_into: Vec<String>,
}

/// Trust (step 2 increment 5, sub-step 5.4.2; review must-fix): WHERE each body of the compiler
/// lane's codegen module `m_cg` ships, read off what the call-event gate certified rather than
/// assumed. `certified` holds, for every function the object defines (one per certificate), the
/// callee symbols of its call sites trust-cg's OPT-4 INLINED (`CallSiteKind::InterpretedInline`).
///
/// A body `X` is inlined into an emitted `F != X` when `F` inlined a callee `G` and `X` is `G` or
/// in `G`'s call closure in `m_cg`: the gate interprets an inlined callee's WHOLE producer body,
/// its own calls included, so under a closed certificate every function `G` reaches is inlined
/// too (a `bl` left in `F`'s bytes would have no IR site of `F` to pair with). Under an unclosed
/// certificate this over-approximates, never omits: a disclosure of where code ships may name a
/// caller whose bytes call `X` instead, never leave out one that contains it. The default lane
/// computes the same field from the dependency closure of each emitted item (`instance_coverage`),
/// because there every callee is inlined.
pub(crate) fn compiler_lane_code_placement(
    m_cg: &trust_ir::Module,
    certified: &[(String, Vec<String>)],
) -> std::collections::BTreeMap<String, CodePlacement> {
    use std::collections::{BTreeMap, BTreeSet};

    use trust_ir::function_dependencies::{DependencyNode, inspect_function_dependencies};
    let closure = |callee: &str| -> BTreeSet<String> {
        let mut reached = BTreeSet::from([callee.to_string()]);
        if let Some(function) = m_cg.functions.iter().find(|f| f.name == callee) {
            for node in inspect_function_dependencies(m_cg, function.id).nodes() {
                if let DependencyNode::Function(id) = node
                    && let Some(f) = m_cg.function_by_id(*id)
                {
                    reached.insert(f.name.clone());
                }
            }
        }
        reached
    };
    let mut placed: BTreeMap<String, CodePlacement> = BTreeMap::new();
    for (function, inlined) in certified {
        placed.entry(function.clone()).or_default().emitted_as_own_symbol = true;
        let mut contained: BTreeSet<String> = BTreeSet::new();
        for callee in inlined {
            contained.extend(closure(callee));
        }
        contained.remove(function);
        for body in contained {
            let row = placed.entry(body).or_default();
            if !row.inlined_into.contains(function) {
                row.inlined_into.push(function.clone());
            }
        }
    }
    for row in placed.values_mut() {
        row.inlined_into.sort();
    }
    placed
}

/// Trust (step 2 increment 4c): the coverage rows of the drop-glue lane — one per synthesized
/// glue body that reaches EMITTED code: emitted under its own symbol (a glue item that lowered),
/// or reached by the call census of an emitted function's own lowering context (the leaf inliner
/// splices what it reaches). Read off what actually lowered, so a glue body no emitted function
/// reaches gets no row.
pub(crate) fn glue_coverage_rows(lowered: &[TrustIrLoweredFunction]) -> Vec<InstanceCoverageRow> {
    let mut rows: Vec<InstanceCoverageRow> = Vec::new();
    for function in lowered {
        let module = &function.gate_source.module;
        for id in drop_glue_lane::reached_glue(module, function.gate_source.func_id) {
            let Some(glue) = module.function_by_id(id) else { continue };
            let row = match rows.iter_mut().position(|row| row.symbol == glue.name) {
                Some(i) => &mut rows[i],
                None => {
                    rows.push(InstanceCoverageRow {
                        symbol: glue.name.clone(),
                        func_id: id.index(),
                        kind: CoverageKind::DropGlue,
                        emitted_as_own_symbol: false,
                        inlined_into: Vec::new(),
                    });
                    rows.last_mut().expect("just pushed")
                }
            };
            if function.symbol == glue.name {
                row.emitted_as_own_symbol = true;
            } else if !row.inlined_into.contains(&function.symbol) {
                row.inlined_into.push(function.symbol.clone());
            }
        }
    }
    rows
}

fn json_string(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl InstanceCoverage {
    /// The note for each row, with the gate verdict every emitted function got.
    pub(crate) fn notes(&self, verdict: &str) -> Vec<String> {
        self.rows
            .iter()
            .map(|row| {
                let mut placement = Vec::new();
                if row.emitted_as_own_symbol {
                    placement.push("emitted under its own symbol".to_string());
                }
                if !row.inlined_into.is_empty() {
                    placement.push(format!(
                        "inlined into {}",
                        row.inlined_into.iter().map(|s| format!("`{s}`")).collect::<Vec<_>>().join(", ")
                    ));
                }
                match row.kind {
                    CoverageKind::Instance(instance_assembly::Spliced::UpstreamEntry(disclosure)) => format!(
                        "trust-cg trust-ir frontend: upstream entry `{}` (FuncId {}) {}; gate verdict {verdict}; {}",
                        row.symbol, row.func_id, placement.join(", "), disclosure.describe(),
                    ),
                    CoverageKind::InventoryResidueLocal => format!(
                        "trust-cg trust-ir frontend: inventory-residue-local: `{}` (FuncId {}) {}, \
                         Internal; gate verdict {verdict}; a local helper rustc's mono-item \
                         inventory does not name (the MIR inliner removed it), emitted from its \
                         finalize-assembled body by the compiler lane (design §3.1 rule 2)",
                        row.symbol,
                        row.func_id,
                        placement.join(", ")
                    ),
                    CoverageKind::DropGlue => format!(
                        "trust-cg trust-ir frontend: drop-glue coverage: SYNTHESIZED drop glue \
                         `{}` (FuncId {}) {}; gate verdict {verdict}; synthesized from rustc's \
                         layout and `Drop` impls and spliced on structural admission with NO \
                         per-instance MIR seam differential (owner ruling D18 OD-2, under D17); \
                         its test oracle is rustc's drop shim, over a corpus",
                        row.symbol,
                        row.func_id,
                        placement.join(", ")
                    ),
                    CoverageKind::Instance(instance_assembly::Spliced::AppendedMirCompared) => format!(
                        "trust-cg trust-ir frontend: instance-lane coverage: GENERIC instance body \
                         `{}` (FuncId {}) {}; gate verdict {verdict}; structural admission; \
                         per-instance MIR seam TEST-ORACLE agreed (symbolic comparator fragment; \
                         no proof authority)",
                        row.symbol, row.func_id, placement.join(", ")
                    ),
                    CoverageKind::Instance(instance_assembly::Spliced::Appended) => format!(
                        "trust-cg trust-ir frontend: instance-lane coverage: GENERIC instance body \
                         `{}` (FuncId {}) {}; gate verdict {verdict}; spliced on structural \
                         admission with NO per-instance MIR seam differential (owner ruling D17)",
                        row.symbol,
                        row.func_id,
                        placement.join(", ")
                    ),
                    CoverageKind::Instance(instance_assembly::Spliced::Relinked) => format!(
                        "trust-cg trust-ir frontend: instance-lane coverage: RELINKED the call \
                         edges of monomorphic `{}` (FuncId {}) {}; gate verdict {verdict}; the body \
                         is the finalize-assembled one, whose seam verdict does not cover the \
                         retargeted call sites",
                        row.symbol,
                        row.func_id,
                        placement.join(", ")
                    ),
                }
            })
            .collect()
    }

    /// The per-crate coverage artifact (D17's per-function disclosure), BOUND to
    /// what it describes: the compiler that wrote it and, for every object it
    /// describes, `(file name, byte length, lowercase hex SHA-256)` — the length
    /// because an archive may pad a member (Darwin `ar` pads to 8 bytes with
    /// newlines), so a consumer hashes the member's first `bytes` bytes — and can
    /// reject a file left beside an object it does not describe (an LLVM or later
    /// rebuild into the same directory).
    pub(crate) fn to_json(
        &self,
        crate_name: &str,
        policy: &str,
        verdict: &str,
        compiler: &str,
        objects: &[(String, usize, String)],
    ) -> String {
        let mut out = String::from("{\n");
        out.push_str(&format!("  \"crate\": {},\n", json_string(crate_name)));
        out.push_str(&format!("  \"compiler\": {},\n", json_string(compiler)));
        out.push_str(&format!(
            "  \"objects\": [{}],\n",
            objects
                .iter()
                .map(|(name, bytes, sha256)| format!(
                    "{{\"file\": {}, \"bytes\": {bytes}, \"sha256\": {}}}",
                    json_string(name),
                    json_string(sha256)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        out.push_str(&format!("  \"output_gate_policy\": {},\n", json_string(policy)));
        out.push_str("  \"rows\": [");
        for (i, row) in self.rows.iter().enumerate() {
            let (kind, evidence) = match row.kind {
                CoverageKind::Instance(instance_assembly::Spliced::UpstreamEntry(_)) => (
                    "upstream-entry",
                    "P-TIR dependency body; actual owner/mode/target/types/callees checked; D28 rederived; strict-only structural admission under D17/D39; no MIR seam differential",
                ),
                CoverageKind::InventoryResidueLocal => (
                    "inventory-residue-local",
                    "finalize-assembled local body an emitted item calls but rustc's mono-item \
                     inventory does not name; emitted Internal under \
                     tcx.symbol_name(Instance::mono(def)) by the compiler lane, its bytes verified \
                     by the call-event gate like every other body (design §3.1 rule 2)",
                ),
                CoverageKind::DropGlue => (
                    "drop-glue",
                    "synthesized from rustc's layout and Drop impls; structural admission + the \
                     strict proven-output gate; no source body and no per-instance MIR seam \
                     differential (owner ruling D18 OD-2, under D17); test oracle: rustc's drop \
                     shim over a corpus (drop_glue_oracle.rs)",
                ),
                CoverageKind::Instance(instance_assembly::Spliced::AppendedMirCompared) => (
                    "generic-instance",
                    "structural admission + the strict proven-output gate; per-instance MIR seam \
                     TEST-ORACLE agreed (symbolic comparator fragment; no proof authority)",
                ),
                CoverageKind::Instance(instance_assembly::Spliced::Appended) => (
                    "generic-instance",
                    "structural admission + the strict proven-output gate; no MIR seam \
                     differential (owner ruling D17)",
                ),
                CoverageKind::Instance(instance_assembly::Spliced::Relinked) => (
                    "relinked-monomorphic",
                    "finalize-assembled body, call edges retargeted; its seam verdict does not \
                     cover the retargeted call sites",
                ),
            };
            let upstream_detail;
            let evidence =
                if let CoverageKind::Instance(instance_assembly::Spliced::UpstreamEntry(d)) =
                    row.kind
                {
                    upstream_detail = d.describe();
                    upstream_detail.as_str()
                } else {
                    evidence
                };
            out.push_str(if i == 0 { "\n" } else { ",\n" });
            out.push_str(&format!(
                "    {{\"symbol\": {}, \"func_id\": {}, \"kind\": {}, \
                 \"emitted_as_own_symbol\": {}, \"inlined_into\": [{}], \"gate_verdict\": {}, \
                 \"evidence\": {}}}",
                json_string(&row.symbol),
                row.func_id,
                json_string(kind),
                row.emitted_as_own_symbol,
                row.inlined_into.iter().map(|s| json_string(s)).collect::<Vec<_>>().join(", "),
                json_string(verdict),
                json_string(evidence),
            ));
        }
        out.push_str(if self.rows.is_empty() { "]\n}\n" } else { "\n  ]\n}\n" });
        out
    }

    /// Whether any row is a body that splices only under the STRICT gate: an appended GENERIC
    /// body (D17), an admitted upstream R body (D39), or synthesized drop glue (D18 OD-2).
    pub(crate) fn has_strict_only_rows(&self) -> bool {
        self.rows.iter().any(|row| {
            matches!(
                row.kind,
                CoverageKind::Instance(instance_assembly::Spliced::Appended)
                    | CoverageKind::Instance(instance_assembly::Spliced::AppendedMirCompared)
                    | CoverageKind::Instance(instance_assembly::Spliced::UpstreamEntry(_))
                    | CoverageKind::DropGlue
            )
        })
    }
}

/// Assemble the codegen unit's LIR into the bridge module shape the object
/// emitter consumes.
///
/// `source_functions` is `None` BY CONSTRUCTION and that is still the honest
/// value: there is no `VerifiableFunction` behind these bytes. The gate work
/// list is returned SEPARATELY, as `Vec<TrustIrGateSource>`, 1:1 and in the same
/// order as `lir_functions`. The caller must not let a `None` here read as
/// "nothing to check": on this path the thing to check is the trust-ir list.
///
/// Two tripwires are CHECKED here rather than assumed, because both would be
/// silent corruptions of the emitted symbol table:
///
/// * `linkage` is consumed index-aligned with `lir_functions` by
///   `emit_module_object`, so a length mismatch would bind symbols against a
///   mis-indexed vector;
/// * each LIR function must carry the MANGLED SYMBOL the item is emitted under.
///   The converter takes the name from the trust-ir function, and the producer
///   names it by that symbol (WS5.2; checked, never renamed, by
///   `lower_from_module`) — the only thing standing between this object and a
///   symbol table full of producer operational labels.
pub(crate) fn compiled_module(
    crate_name: &str,
    lowered: Vec<TrustIrLoweredFunction>,
    linkage: Vec<bridge_backend::FunctionLinkage>,
    statics: Vec<bridge_backend::ObjectGlobal>,
) -> Result<
    (
        bridge_backend::CompiledModule,
        Vec<trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource>,
    ),
    String,
> {
    let function_count = lowered.len();
    if linkage.len() != function_count {
        return Err(format!(
            "{function_count} trust-ir function(s) carry {} linkage entries",
            linkage.len()
        ));
    }
    for function in &lowered {
        if function.lir.name != function.symbol {
            return Err(format!(
                "lowered LIR for `{}` carries the name `{}`; the mangled symbol did not survive \
                 conversion",
                function.symbol, function.lir.name
            ));
        }
        if function.gate_source.symbol != function.symbol {
            return Err(format!(
                "gate source for `{}` is labelled `{}`; refusing to verify one function and \
                 ship another",
                function.symbol, function.gate_source.symbol
            ));
        }
    }
    let mut lir_functions = Vec::with_capacity(function_count);
    let mut gate_sources = Vec::with_capacity(function_count);
    for function in lowered {
        lir_functions.push(function.lir);
        gate_sources.push(function.gate_source);
    }
    Ok((
        bridge_backend::CompiledModule {
            name: format!("{crate_name}.codegen_unit.0"),
            lir_functions,
            object_path: None,
            function_count,
            source_functions: None,
            linkage,
            statics,
        },
        gate_sources,
    ))
}

// ===========================================================================
// GAP G2: THE CRATE-MODULE CODEGEN EXIT
//
// # What was missing
//
// `trust_thir_lower::crate_module::finalize_and_dump` assembles ONE
// `trust_ir::Module` per crate and (since the producing half of this gap
// landed) PUBLISHES it into Session state, with a symbol -> `FuncId` map and a
// deny-by-default codegen license. Nothing consumed it. This consumer forced
// the PER-BODY `trust_ir_of` query and handed `lower_module_to_lir` a
// single-function module, which has three consequences:
//
//  1. an intra-module callee is not in the module, so `inline_local_pure_leaf_calls`
//     cannot resolve it and the converter fail-closes on the `Call`;
//  2. the cross-producer call edges `link_clean_origin_edges` re-pointed inside
//     the crate module are dead weight at codegen;
//  3. nothing in codegen ever sees the crate-level license.
//
// [`lower_crate_module`] is the other mode: it takes the LOWERING CONTEXT from
// the published module and lowers each admitted function AGAINST THE WHOLE
// MODULE, so an intra-module callee resolves.
//
// # It is NOT a second inventory either
//
// The work list is still `collect_production_mono_items`, and every instance
// still goes through [`local_body_def`] first — so `upstream-body`,
// `synthesized-instance` and `generic-instance` refuse exactly as they do on
// the per-body path, for exactly the same reasons (the crate module is
// PRE-MONOMORPHIZATION, so a real monomorphization is no more emittable from it
// than from `trust_ir_of`). What changes is where the IR comes from and what
// context it is lowered in.
//
// # There is still no MIR fallback anywhere in this mode
//
// Every joint below is `Err(FrontendRefusal)`, every refusal is CLASSIFIED, and
// [`lower_crate_module`] records all of them into the SAME [`RefusalCensus`].
// A whole-module refusal does not short-circuit into a bare error: it is
// attributed to every reachable item, so the census still reports
// `refused == reachable` and names the one reason.
// ===========================================================================

/// How a CODEGEN consumer must read one body's `trust_ir::Function::body_gate`.
///
/// # The direction of the gate
///
/// This is a NEGATIVE gate. Producer-supplied metadata never GRANTS authority
/// here, it only WITHHOLDS it: [`GateVerdict::NotWithheld`] means the producer
/// declined to withhold, and the actual permission to emit comes from the
/// separately-computed `PublishedCrateModule::codegen_inventory` (and, beyond
/// this module, from the M-POS proven-output gate over the emitted bytes).
/// [`admit_from_crate_module`] therefore checks BOTH and refuses on either.
///
/// # The three states, and the policy for each
///
/// * `Some(Gated { authority })` — proceed (nothing withheld). Recognition of
///   `authority` is deliberately NOT made a precondition, because that would
///   turn the field into a grant; it is recorded and reported instead.
/// * `Some(Ungated)` — REFUSED. An affirmative producer claim that no gate ran.
/// * `None` — REFUSED, as a SEPARATE class.
///
/// ## Why `None` is refused, when it is the documented grandfather state
///
/// `trust_ir::BodyGate`'s own doc says a consumer *may* permit `None`, because
/// refusing it refuses every module written before v41. That argument is about
/// STORED ARTIFACTS. This consumer's input is not one: it is a
/// `trust_ir::Module` assembled in THIS process, this compilation, by a
/// producer built against a submodule pin that HAS v41. There is no legacy blob
/// in the path, so grandfathering buys no compatibility here — and it costs the
/// interlock: a producer that simply never sets the field would obtain, by
/// omission, exactly the permission `Ungated` is refused for, making "drop the
/// field" the cheapest way to launder an ungated body. `trust-ir-build`'s
/// `validate_module_for_codegen` reaches the same conclusion for the same
/// reason and reports it as its own distinct variant.
///
/// The two are never collapsed: separate variants, separate
/// [`RefusalClass`]es, separate counts in the census, and separate
/// `retired_by` lines — because they have completely different fixes (gate the
/// body vs. stamp the field).
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub(crate) enum GateVerdict {
    /// `Some(BodyGate::Gated { authority })` with a non-blank authority.
    NotWithheld { authority: String },
    /// `Some(BodyGate::Ungated)` — an affirmative "no gate ran".
    Ungated,
    /// `None` — no licensing claim at all.
    NoClaim,
    /// `Some(BodyGate::Gated { authority })` with a BLANK authority: a positive
    /// license naming no gate.
    BlankAuthority,
}

impl GateVerdict {
    /// Stable tag for messages.
    pub(crate) const fn tag(&self) -> &'static str {
        match self {
            Self::NotWithheld { .. } => "gated",
            Self::Ungated => "ungated",
            Self::NoClaim => "no-claim",
            Self::BlankAuthority => "blank-authority",
        }
    }

    /// True for every verdict that WITHHOLDS. The only false case is
    /// [`Self::NotWithheld`].
    pub(crate) const fn withholds(&self) -> bool {
        !matches!(self, Self::NotWithheld { .. })
    }
}

/// Read one body's gate.
///
/// Deliberately STRICTER than `trust_ir::BodyGate::is_gated`, which reads the
/// discriminant alone: a `Gated` whose authority is blank names no gate at all,
/// and a positive license that names nothing is not a license. (`validate_module`
/// independently reports that shape as `ValidationError::InvalidBodyGate`.)
pub(crate) fn body_gate_verdict(gate: Option<&trust_ir::BodyGate>) -> GateVerdict {
    match gate {
        Some(trust_ir::BodyGate::Gated { authority, .. }) if !authority.trim().is_empty() => {
            GateVerdict::NotWithheld { authority: authority.clone() }
        }
        Some(trust_ir::BodyGate::Gated { .. }) => GateVerdict::BlankAuthority,
        Some(trust_ir::BodyGate::Ungated) => GateVerdict::Ungated,
        None => GateVerdict::NoClaim,
    }
}

/// How many offending functions a whole-module gate refusal names.
const GATE_SAMPLES: usize = 3;

/// The ONE gate authority this consumer recognizes: the Rust producer's own
/// structural direct-lane gate.
///
/// Taken from the producer's constant rather than re-spelled as a literal, so
/// a rename cannot silently make this consumer recognize nothing. Compare
/// `trust_cg_lower::CodegenLicensePolicy`, which mirrors Clean's
/// `clean-kernel-tv` as a string because it consumes STORED artifacts from a
/// producer it does not link; this consumer's input is a module assembled in
/// THIS process by the crate it names here.
///
/// Recognizing it is not treating it as a verification claim: what it asserts
/// (and what it explicitly does not) is documented on
/// [`trust_thir_lower::crate_module::TRUST_DIRECT_LANE_AUTHORITY`]. This
/// consumer's emission is verified downstream by the M-POS proven-output gate
/// over the EMITTED BYTES, which is the semantic check the structural gate does
/// not make.
const RECOGNIZED_GATE_AUTHORITY: &str = trust_thir_lower::crate_module::TRUST_DIRECT_LANE_AUTHORITY;

/// The module-wide reading of every body's gate.
#[derive(Debug, Default)]
pub(crate) struct ModuleGateReport {
    /// `(FuncId index, name)` of every affirmatively-`Ungated` body.
    pub(crate) ungated: Vec<(u32, String)>,
    /// `(FuncId index, name)` of every body making no claim at all.
    pub(crate) no_claim: Vec<(u32, String)>,
    /// `(FuncId index, name)` of every `Gated` naming no authority.
    pub(crate) blank_authority: Vec<(u32, String)>,
    /// Bodies that withhold nothing.
    pub(crate) gated: usize,
    /// Bodyless declarations, which are never codegen subjects.
    pub(crate) declarations: usize,
}

impl ModuleGateReport {
    /// Walk every function once.
    pub(crate) fn of(module: &trust_ir::Module) -> Self {
        let mut report = Self::default();
        for function in &module.functions {
            // A declaration produces no code, so it needs no license. Same
            // predicate the format crate uses (`is_declaration`, blocks empty
            // and linkage-agnostic).
            if function.is_declaration() {
                report.declarations += 1;
                continue;
            }
            let row = (function.id.index(), function_label(function));
            match body_gate_verdict(function.body_gate.as_ref()) {
                GateVerdict::NotWithheld { .. } => report.gated += 1,
                GateVerdict::Ungated => report.ungated.push(row),
                GateVerdict::NoClaim => report.no_claim.push(row),
                GateVerdict::BlankAuthority => report.blank_authority.push(row),
            }
        }
        report
    }

    /// True iff NOTHING in the module withholds.
    pub(crate) fn is_positive(&self) -> bool {
        self.ungated.is_empty() && self.no_claim.is_empty() && self.blank_authority.is_empty()
    }

    fn sample(rows: &[(u32, String)]) -> String {
        let listed = rows
            .iter()
            .take(GATE_SAMPLES)
            .map(|(id, label)| format!("FuncId {id} {label}"))
            .collect::<Vec<_>>()
            .join(", ");
        if rows.len() > GATE_SAMPLES {
            format!("{listed}, ... and {} more", rows.len() - GATE_SAMPLES)
        } else {
            listed
        }
    }

    /// The whole-module refusal text.
    ///
    /// The withholding verdicts get SEPARATE lines, separate counts and
    /// separate `retired by` clauses. Collapsing `ungated` and `no-claim` into
    /// one line is the specific thing this must never do: one is a producer
    /// assertion that the gate did not run, the other is the absence of any
    /// assertion, and they are retired by different work.
    pub(crate) fn refusal(&self) -> String {
        let bodies =
            self.gated + self.ungated.len() + self.no_claim.len() + self.blank_authority.len();
        let mut out = format!(
            "the published crate module is NOT positively licensed for codegen: of {bodies} \
             body-bearing function(s) ({} bodyless declaration(s) need no license), {} carry a \
             positive gate.",
            self.declarations, self.gated
        );
        if !self.ungated.is_empty() {
            out.push_str(&format!(
                "\n  {} AFFIRMATIVELY UNGATED (`body_gate: ungated` — the producer states that \
                 no verification gate was applied): {}\n    retired by: {}",
                self.ungated.len(),
                Self::sample(&self.ungated),
                RefusalClass::UngatedBody.retired_by()
            ));
        }
        if !self.no_claim.is_empty() {
            out.push_str(&format!(
                "\n  {} MAKE NO LICENSING CLAIM AT ALL (`body_gate` absent — the pre-v41 \
                 grandfather state, which this consumer refuses; see `body_gate_verdict`): \
                 {}\n    retired by: {}",
                self.no_claim.len(),
                Self::sample(&self.no_claim),
                RefusalClass::UnlicensedBody.retired_by()
            ));
        }
        if !self.blank_authority.is_empty() {
            out.push_str(&format!(
                "\n  {} carry `body_gate: gated` with a BLANK AUTHORITY — a positive license \
                 naming no gate: {}\n    retired by: naming the gate's owner \
                 (`ValidationError::InvalidBodyGate` reports the same defect structurally)",
                self.blank_authority.len(),
                Self::sample(&self.blank_authority)
            ));
        }
        out
    }
}

/// Cross-check this consumer's own gate walk against the FORMAT CRATE's
/// independent statement of the same rule
/// (`trust_ir_build::validate::codegen_license_errors`, reached here through
/// `validate_module_for_codegen`).
///
/// Two independent readings of one field; a disagreement is a REFUSAL, never a
/// tie-break. This is the same shape as `compute_codegen_license`'s leg 3 on
/// the producer side, and it is what stops the walk above from silently
/// drifting from the format's definition when `BodyGate` grows a variant.
pub(crate) fn cross_check_license(
    report: &ModuleGateReport,
    license_errors: &[trust_ir_build::validate::ValidationError],
) -> Result<(), String> {
    use trust_ir_build::validate::ValidationError;
    let mut theirs_ungated: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    let mut theirs_no_claim: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for error in license_errors {
        match error {
            ValidationError::UngatedBodyForCodegen { function, .. } => {
                theirs_ungated.insert(*function);
            }
            ValidationError::UnlicensedBodyForCodegen { function, .. } => {
                theirs_no_claim.insert(*function);
            }
            _ => {}
        }
    }
    let mine_ungated: std::collections::BTreeSet<u32> =
        report.ungated.iter().map(|(i, _)| *i).collect();
    let mine_no_claim: std::collections::BTreeSet<u32> =
        report.no_claim.iter().map(|(i, _)| *i).collect();
    if mine_ungated != theirs_ungated || mine_no_claim != theirs_no_claim {
        return Err(format!(
            "codegen-license DISAGREEMENT between this consumer's own `body_gate` walk and \
             `trust_ir_build::validate::validate_module_for_codegen`: ungated \
             mine={mine_ungated:?} theirs={theirs_ungated:?}; no-claim mine={mine_no_claim:?} \
             theirs={theirs_no_claim:?}. Two independent readings of one field disagree, so \
             NOTHING is lowered."
        ));
    }
    Ok(())
}

/// A published crate module that has passed every WHOLE-MODULE precondition,
/// with every function this compilation can name CHECKED to carry its LINK-TIME
/// identity (WS5.2: the producer names functions by their link-time symbol; this
/// consumer no longer renames anything).
///
/// Constructing one is not a license to emit anything: [`admit_from_crate_module`]
/// is still consulted per item.
#[derive(Debug)]
pub(crate) struct PreparedCrateModule {
    /// The crate the producer assembled this for.
    pub(crate) crate_name: String,
    /// THE LOWERING CONTEXT — the whole module, so an intra-module callee
    /// resolves for `inline_local_pure_leaf_calls`. Shared (`Arc`) with every
    /// admitted function's gate source (plan item K).
    pub(crate) module: std::sync::Arc<trust_ir::Module>,
    /// `display_path` (the producer's `def_path_str`) -> `FuncId`, ambiguity
    /// already removed by the producer.
    by_def_path: std::collections::BTreeMap<String, FuncId>,
    /// Names held by more than one function, resolvable by no one.
    ambiguous: std::collections::BTreeSet<String>,
    /// The producer's deny-by-default codegen inventory.
    licensed: std::collections::BTreeSet<FuncId>,
    /// `FuncId` -> mangled symbol, for every function this compilation can name.
    link_names: std::collections::BTreeMap<FuncId, String>,
}

impl PreparedCrateModule {
    /// How many functions the producer licensed.
    pub(crate) fn licensed_count(&self) -> usize {
        self.licensed.len()
    }

    /// The link-time name this compilation assigned to `id`, if any.
    pub(crate) fn link_name(&self, id: FuncId) -> Option<&str> {
        self.link_names.get(&id).map(String::as_str)
    }
}

/// Build the lowering context from a published crate module, or say why this
/// crate has none.
///
/// PURE — no `TyCtxt`, no `Session`, no rustc type anywhere in the signature —
/// so every decision it makes is executable outside a compiler session. That is
/// not an aesthetic choice: this crate needs `rustc_private` and cannot be built
/// from the plain `crates/` workspace, so the amount of this change that can be
/// covered by a running test is exactly the amount that stays out of rustc's
/// types.
///
/// `link_names` is `(def_path_str, mangled symbol)` for every reachable
/// mono-instance whose body is local — INCLUDING ones the caller will refuse
/// for other reasons, because the map is what every function this compilation
/// can name is CHECKED against. `by_def_path` is the producer's `display_path`
/// index (`PublishedCrateModule::display_paths`).
///
/// # The legs, each fail-closed
///
/// 1. The producer REFUSED the codegen license -> nothing is lowered. An empty
///    license with no refusal is not this case: that publishes fine and every
///    item is refused individually as `unlicensed-by-producer`.
/// 2. `validate_module_for_codegen` reports a STRUCTURAL error -> nothing is
///    lowered. A module this consumer cannot validate is a module it does not
///    lower. (The two license variants are partitioned out here and handled by
///    leg 3; they are not structural findings.)
/// 3. THE NEGATIVE GATE, whole-module — and cross-checked against the format
///    crate's independent verdict first.
/// 4. LINK-TIME IDENTITY, CHECKED (WS5.2): the row this compilation's inventory
///    names by def path must already carry the symbol this compilation mangles
///    for it — the producer names every function by its link-time symbol — and
///    two functions may not claim one mangled symbol, nor one function two. A
///    disagreement is a producer/frontend identity split, and nothing is lowered.
///
/// After leg 2 (plan step 3.4, owner ruling D37), every `Producer::Clean`
/// body becomes a bodyless declaration in this consumer's private clone
/// ([`without_clean_bodies`]), which legs 3-4 and the lowering read: this lane
/// never emits a Clean body, and the converter refuses a call to one by name,
/// so a Clean row — stamped `clean-carrier-gate` or `Ungated` — no longer
/// withdraws the Rust bodies. Leg 2 validates the module as published.
///
/// # Why leg 3 is whole-module and not per-function
///
/// `lower_module_to_lir` INLINES a local pure leaf callee into the caller it
/// lowers (`inline_local_pure_leaf_calls`). An ungated callee spliced into a
/// gated caller is emitted code for an ungated body. Deciding "can this caller
/// reach an ungated body" needs a walker over every `FuncId`-bearing construct
/// in `Inst` and `Constant`; an exhaustive `match` would catch a new VARIANT at
/// compile time but not a new `FuncId` FIELD on an existing one, and an
/// under-collecting walker OVER-licenses, silently. Requiring every body in the
/// lowering context to be positively gated makes that question VACUOUS instead
/// of answering it with a walker whose completeness nobody can check — the same
/// move `crate_module::compute_codegen_license`'s leg 4 makes on the producer
/// side, and it costs the same stated thing: one ungated body refuses the whole
/// crate.
pub(crate) fn prepare_crate_module(
    crate_name: &str,
    module: &trust_ir::Module,
    by_def_path: &std::collections::BTreeMap<String, FuncId>,
    ambiguous: &[String],
    licensed: &[FuncId],
    license_refusal: Option<&str>,
    link_names: &[(String, String)],
) -> Result<PreparedCrateModule, String> {
    use std::collections::{BTreeMap, BTreeSet};

    use trust_ir_build::validate::{ValidationError, validate_module_for_codegen};

    // Leg 1.
    if let Some(reason) = license_refusal {
        return Err(format!(
            "the producer REFUSED the codegen license for `{crate_name}`, so nothing in the \
             published module may be emitted: {reason}"
        ));
    }

    // Leg 2 (and the license half of leg 3), in one pass over the module.
    let (license_errors, structural): (Vec<_>, Vec<_>) =
        validate_module_for_codegen(module).into_iter().partition(|e| {
            matches!(
                e,
                ValidationError::UngatedBodyForCodegen { .. }
                    | ValidationError::UnlicensedBodyForCodegen { .. }
            )
        });
    if !structural.is_empty() {
        let sample = structural
            .iter()
            .take(GATE_SAMPLES)
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("; ");
        return Err(format!(
            "`validate_module_for_codegen` reported {} structural error(s) on the published \
             module for `{crate_name}`; a module this consumer cannot validate is a module it \
             does not lower: {sample}{}",
            structural.len(),
            if structural.len() > GATE_SAMPLES { ", ..." } else { "" }
        ));
    }

    // Trust (plan step 3.4, owner ruling D37): THIS LANE EMITS NO CLEAN-ORIGIN BODY. The
    // producer's leg 4 is per function since 3.4, so a Clean-island crate now publishes a
    // granted direct license beside its Clean rows (a `gate` row stamped `clean-carrier-gate`,
    // every other one `Ungated`), where before it withheld the whole module. A Clean row's
    // license is honored only by F1's Clean admission on the `Compiler::compile` lane (plan
    // step 3.6), never by this lane, which lowers through `module_to_lir` (no new coverage,
    // plan R-5). So, once leg 2 has validated the module AS PUBLISHED, every `Producer::Clean`
    // body is turned into a bodyless declaration in this consumer's PRIVATE clone, and legs
    // 3-4 and the lowering read that clone. (Leg 2 reads the published module: the clone's
    // clean-origin disclosure rows name the now-bodyless functions, which `validate_module`
    // rejects, and the license errors of the Clean bodies are dropped with them.) Nothing is
    // admitted by this: the Clean body has no bytes left to emit or inline, the inventory never
    // listed it, its own item is refused by name (`[clean-below-gate]`), and a Rust caller's
    // call to it is refused by name by the converter, which refuses every `Producer::Clean`
    // callee whether or not it has a body (`ModuleLirError::CleanOriginBelowCodegenGate`). What
    // it removes is a Clean row's power to withdraw the Rust bodies' license through legs 3
    // and 3b; a body of any other producer withholds exactly as before.
    let published = module;
    let module = without_clean_bodies(published);
    let module: &trust_ir::Module = &module;
    let stripped: BTreeSet<u32> = published
        .functions
        .iter()
        .filter(|f| !f.is_declaration() && f.producer == Some(trust_ir::Producer::Clean))
        .map(|f| f.id.index())
        .collect();
    let license_errors: Vec<ValidationError> = license_errors
        .into_iter()
        .filter(|error| match error {
            ValidationError::UngatedBodyForCodegen { function, .. }
            | ValidationError::UnlicensedBodyForCodegen { function, .. } => {
                !stripped.contains(function)
            }
            _ => true,
        })
        .collect();

    // Leg 3.
    let report = ModuleGateReport::of(module);
    cross_check_license(&report, &license_errors)?;
    if !report.is_positive() {
        return Err(report.refusal());
    }

    // Leg 3b: RECOGNITION, whole-module. [`body_gate_verdict`] deliberately
    // treats ANY non-blank authority as "nothing withheld", so that the field
    // cannot become a grant — and that is the right reading for ONE ITEM,
    // because what permits emission is the inventory. It is NOT sufficient for
    // the LOWERING CONTEXT: `lower_module_to_lir` splices a local pure leaf
    // callee into the caller it lowers, so a body in this module can reach the
    // object file WITHOUT ever being an admitted item the inventory was
    // consulted for. A foreign authority in the context is therefore a foreign
    // gate licensing code this consumer emits, and the per-item check can never
    // see it.
    //
    // So every gated body here must name an authority this consumer RECOGNIZES.
    // The recognized set is exactly one name — the producer's own constant, not
    // a re-spelled literal, so the two cannot drift — and recognition only ever
    // WITHHOLDS: it adds no permission, the inventory still is the permission.
    // Today this is vacuous for any module this repo's producer assembled (its
    // stamp uses that one authority and marks everything else `Ungated`, which
    // leg 3 already refused). It stops being vacuous the moment a module is
    // assembled from two producers, which is exactly what tier `gate` would
    // introduce.
    let unrecognized: Vec<String> = module
        .functions
        .iter()
        .filter(|function| !function.is_declaration())
        .filter_map(|function| match function.body_gate.as_ref() {
            Some(trust_ir::BodyGate::Gated { authority, .. })
                if authority != RECOGNIZED_GATE_AUTHORITY =>
            {
                Some(format!(
                    "FuncId {} {} gated by {authority:?}",
                    function.id.index(),
                    function_label(function)
                ))
            }
            _ => None,
        })
        .collect();
    if !unrecognized.is_empty() {
        let sample = unrecognized.iter().take(GATE_SAMPLES).cloned().collect::<Vec<_>>().join("; ");
        return Err(format!(
            "{} body/bodies in the published module for `{crate_name}` carry a positive gate \
             from an authority this consumer does not recognize (it recognizes only \
             {RECOGNIZED_GATE_AUTHORITY:?}). An unrecognized authority is a REFUSAL, never a \
             pass, and the lowering context is whole-module because a leaf callee is spliced \
             into the caller: {sample}{}",
            unrecognized.len(),
            if unrecognized.len() > GATE_SAMPLES { ", ..." } else { "" }
        ));
    }

    // Leg 4. LINK-TIME IDENTITY, CHECKED (WS5.2, F-087). The producer names every
    // function by its link-time symbol (`Function.name`, ratified by trust-ir v41)
    // and carries the human def path in `display_path`. This compilation mangles
    // every reachable item itself; the two MUST agree. This leg used to RENAME a
    // private clone from `def_path_str` to the symbol — which is exactly what made
    // the producer's own artifact name functions by a display label. Now it is a
    // check, and a disagreement refuses the whole module, naming both spellings.
    let ambiguous: BTreeSet<String> = ambiguous.iter().cloned().collect();
    let mut names: BTreeMap<FuncId, String> = BTreeMap::new();
    let mut claimed: BTreeMap<String, FuncId> = BTreeMap::new();
    for (def_path, symbol) in link_names {
        if ambiguous.contains(def_path) {
            continue;
        }
        let Some(&id) = by_def_path.get(def_path) else { continue };
        let Some(function) = module.function_by_id(id) else {
            return Err(format!(
                "FuncId {} of `{crate_name}` is indexed by display path `{def_path}` but is not \
                 in the module; nothing is lowered.",
                id.index()
            ));
        };
        if &function.name != symbol {
            return Err(format!(
                "FuncId {} of `{crate_name}` (`{def_path}`) carries link-time symbol `{}`, but \
                 this compilation mangles `{def_path}` as `{symbol}`. `Function.name` is the \
                 link-time symbol, so the producer and this frontend disagree about the item's \
                 identity; nothing is lowered.",
                id.index(),
                function.name
            ));
        }
        if let Some(previous) = names.insert(id, symbol.clone()) {
            if &previous != symbol {
                return Err(format!(
                    "FuncId {} of `{crate_name}` is claimed by two link-time symbols \
                     (`{previous}` and `{symbol}`); nothing is lowered.",
                    id.index()
                ));
            }
        }
        if let Some(previous) = claimed.insert(symbol.clone(), id) {
            if previous != id {
                return Err(format!(
                    "link-time symbol `{symbol}` is claimed by FuncId {} and FuncId {} of \
                     `{crate_name}`; nothing is lowered.",
                    previous.index(),
                    id.index()
                ));
            }
        }
    }

    Ok(PreparedCrateModule {
        crate_name: crate_name.to_string(),
        module: std::sync::Arc::new(module.clone()),
        by_def_path: by_def_path.clone(),
        ambiguous,
        licensed: licensed.iter().copied().collect(),
        link_names: names,
    })
}

/// Plan step 3.4: `module` with every `Producer::Clean` body turned into a bodyless external
/// declaration (producer kept, no licensing claim, no value names or scopes), for the
/// crate-module lane's private lowering context. Borrowed unchanged when there is none. PURE.
pub(crate) fn without_clean_bodies(
    module: &trust_ir::Module,
) -> std::borrow::Cow<'_, trust_ir::Module> {
    let is_clean_body = |f: &trust_ir::Function| {
        !f.is_declaration() && f.producer == Some(trust_ir::Producer::Clean)
    };
    if !module.functions.iter().any(is_clean_body) {
        return std::borrow::Cow::Borrowed(module);
    }
    let mut stripped = module.clone();
    for function in &mut stripped.functions {
        if is_clean_body(function) {
            function.blocks.clear();
            function.value_names = None;
            function.scopes = None;
            function.body_gate = None;
            // A body-required linkage would make the declaration structurally invalid
            // (`EmptyFunction`); a declaration is an external symbol.
            function.linkage = trust_ir::Linkage::External;
        }
    }
    std::borrow::Cow::Owned(stripped)
}

/// Admit ONE item against a prepared crate module, or classify why not.
///
/// Every gate check here is ALSO implied by a whole-module precondition in
/// [`prepare_crate_module`], and that is deliberate rather than redundant: the
/// whole-module gate is what closes the inlined-callee hole, and this is what
/// makes a refusal ATTRIBUTABLE to one mangled symbol and one
/// [`RefusalClass`], which is what the census counts on.
pub(crate) fn admit_from_crate_module(
    prepared: &PreparedCrateModule,
    def_path: &str,
    symbol: &str,
) -> Result<FuncId, FrontendRefusal> {
    if prepared.ambiguous.contains(def_path) {
        return Err(FrontendRefusal::AmbiguousInCrateModule {
            symbol: symbol.to_string(),
            def_path: def_path.to_string(),
        });
    }
    let Some(&id) = prepared.by_def_path.get(def_path) else {
        return Err(FrontendRefusal::NotInCrateModule {
            symbol: symbol.to_string(),
            def_path: def_path.to_string(),
        });
    };
    let Some(function) = prepared.module.function_by_id(id) else {
        return Err(FrontendRefusal::NotInCrateModule {
            symbol: symbol.to_string(),
            def_path: def_path.to_string(),
        });
    };
    if function.is_declaration() {
        return Err(FrontendRefusal::DeclarationOnlyInCrateModule {
            symbol: symbol.to_string(),
            def_path: def_path.to_string(),
        });
    }
    // THE NEGATIVE GATE. Refuse on absence. Reaching the `NotWithheld` arm is
    // not permission — it is only the absence of a withholding.
    match body_gate_verdict(function.body_gate.as_ref()) {
        GateVerdict::NotWithheld { .. } => {}
        GateVerdict::Ungated => {
            return Err(FrontendRefusal::UngatedBody {
                symbol: symbol.to_string(),
                func: id.index(),
            });
        }
        GateVerdict::NoClaim => {
            return Err(FrontendRefusal::UnlicensedBody {
                symbol: symbol.to_string(),
                func: id.index(),
            });
        }
        GateVerdict::BlankAuthority => {
            return Err(FrontendRefusal::MalformedBodyGate {
                symbol: symbol.to_string(),
                func: id.index(),
                detail: "`body_gate: gated` with a blank authority names no gate at all"
                    .to_string(),
            });
        }
    }
    // THE PERMISSION, which does not come from the body's own metadata.
    if !prepared.licensed.contains(&id) {
        return Err(FrontendRefusal::UnlicensedByProducer {
            symbol: symbol.to_string(),
            func: id.index(),
        });
    }
    match prepared.link_names.get(&id) {
        Some(name) if name == symbol => Ok(id),
        Some(name) => Err(FrontendRefusal::LinkNameMismatch {
            symbol: symbol.to_string(),
            func: id.index(),
            found: name.clone(),
        }),
        None => Err(FrontendRefusal::LinkNameMismatch {
            symbol: symbol.to_string(),
            func: id.index(),
            found: "<unnamed>".to_string(),
        }),
    }
}

/// Lower ONE admitted item against the WHOLE published crate module.
///
/// The only difference from [`lower_instance`] is the second argument to
/// `lower_module_to_lir`: the context is the crate module rather than a
/// single-function one, so `inline_local_pure_leaf_calls` can resolve an
/// intra-module callee. Everything else — the ABI cross-check against the IR's
/// own parameter count, the gate source carried alongside the LIR — is the same
/// contract.
///
/// KNOWN COST, stated rather than hidden: `TrustIrGateSource` owns its
/// `trust_ir::Module`, so the crate module is cloned once per admitted
/// function. That is O(functions x module size). It is the gate's API, not a
/// choice made here, and correctness comes first; an `Arc`-shared spec is a
/// `trust-cg-bridge` change.
pub(crate) fn lower_from_crate_module<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    prepared: &PreparedCrateModule,
    instance: ty::Instance<'tcx>,
    symbol: &str,
    def_path: &str,
    validate_abi: V,
) -> Result<TrustIrLoweredFunction, FrontendRefusal>
where
    V: FnOnce(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    if let ty::InstanceKind::Item(def_id) = instance.def {
        refuse_custom_mir(tcx, def_id, symbol)?;
    }
    let func_id = admit_from_crate_module(prepared, def_path, symbol)?;

    let ir_param_count = {
        // `admit_from_crate_module` just proved this resolves.
        let function =
            prepared.module.function_by_id(func_id).ok_or(FrontendRefusal::NotInCrateModule {
                symbol: symbol.to_string(),
                def_path: def_path.to_string(),
            })?;
        prepared
            .module
            .func_types
            .get(function.ty.as_usize())
            .ok_or(FrontendRefusal::MissingFuncType {
                symbol: symbol.to_string(),
                ty: function.ty.index(),
            })?
            .params
            .len()
    };

    validate_abi(tcx, instance, ir_param_count)
        .map_err(|detail| FrontendRefusal::UnsupportedAbi { symbol: symbol.to_string(), detail })?;

    // Trust (R-8 ledger item 1): the same refusal `lower_from_module` makes.
    refuse_unfaithful_panic(&prepared.module, func_id, symbol)?;

    // The same PASS-MODE CROSS-CHECK token `lower_from_module` mints, on the same
    // evidence: `validate_abi` above just walked rustc's `FnAbi` for this instance.
    let param_extensions = crate::instance_param_extensions(tcx, instance, ir_param_count)
        .map_err(|detail| FrontendRefusal::UnsupportedAbi { symbol: symbol.to_string(), detail })?;
    let abi_cross_check = trust_cg_bridge::AbiPassModeCrossCheck::attested_by(
        "rustc_codegen_trust_cg: validate_codegen_instance_abi_* over rustc's FnAbi PassMode \
         for this exact instance, immediately before lowering",
    )
    .with_param_extensions(param_extensions);
    let lir = trust_cg_bridge::lower_module_to_lir_with_abi_cross_check(
        &prepared.module,
        func_id,
        &abi_cross_check,
    )
    .map_err(|e| converter_refused(symbol, &prepared.module, e))?;

    let instructions: usize = lir.blocks.values().map(|block| block.instructions.len()).sum();
    tracing::debug!(
        symbol = %symbol,
        crate_name = %prepared.crate_name,
        lir_instructions = instructions,
        "[trust_cg] trust-ir frontend lowered a function against the PUBLISHED CRATE MODULE"
    );

    let gate_source = trust_cg_bridge::verify_output_trust_ir::TrustIrGateSource {
        symbol: symbol.to_string(),
        module: std::sync::Arc::clone(&prepared.module),
        func_id,
        abi_cross_check: Some(abi_cross_check),
    };

    Ok(TrustIrLoweredFunction { symbol: symbol.to_string(), lir, gate_source })
}

/// The result of one crate-module compilation attempt.
///
/// `lowered` and `linkage` are 1:1 and index-aligned, exactly as
/// [`compiled_module`] requires. `census` holds EVERY refusal, classified —
/// including the whole-module ones, which are attributed to each reachable item
/// rather than short-circuited, so `census.len() == reachable` really does mean
/// "nothing compiled" and the report still names the one reason.
pub(crate) struct CrateModuleOutcome {
    /// Functions that completed crate module -> LIR.
    pub(crate) lowered: Vec<TrustIrLoweredFunction>,
    /// Linkage, index-aligned with `lowered`.
    pub(crate) linkage: Vec<bridge_backend::FunctionLinkage>,
    /// Every refusal, classified.
    pub(crate) census: RefusalCensus,
}

/// CRATE-MODULE MODE (gap G2): compile the reachable inventory against the
/// PUBLISHED crate module.
///
/// `instances` is the production inventory, unchanged — same collection, same
/// linkage/visibility gate, same order. Each item still goes through
/// [`local_body_def`] first, so the pre-existing classes refuse identically.
///
/// # The call site
///
/// `lib.rs`'s `codegen_crate_from_trust_ir` step (5) selects between this and
/// [`lower_instance`] on `sess.trust_ir_crate_module()`
/// (`-Ztrust-ir-crate-module`), hands this one the production inventory as
/// `(instance, linkage)` pairs, and feeds the resulting [`CrateModuleOutcome`]
/// into the SAME `census.report(reachable)` `fatal` the other mode uses. The
/// selection is made there rather than here: which producer input a compilation
/// uses is a session decision, not a property of this function.
pub(crate) fn lower_crate_module<'tcx, V>(
    tcx: TyCtxt<'tcx>,
    instances: Vec<(ty::Instance<'tcx>, bridge_backend::FunctionLinkage)>,
    validate_abi: V,
) -> CrateModuleOutcome
where
    V: Fn(TyCtxt<'tcx>, ty::Instance<'tcx>, usize) -> Result<(), String>,
{
    // (1) Project each instance onto a local body EXACTLY as the per-body path
    // does. `upstream-body` / `synthesized-instance` / `generic-instance` are
    // refused here, for reasons that do not change just because the IR now
    // comes from a crate module: it is still lowered PRE-MONOMORPHIZATION, so a
    // real monomorphization is no more emittable from it than from
    // `trust_ir_of`. The lifetime-only carve-out and its "does NOT generalize"
    // argument carry over verbatim.
    enum Item<'a> {
        Admissible {
            symbol: String,
            def_path: String,
            def: rustc_span::def_id::LocalDefId,
            instance: ty::Instance<'a>,
            linkage: bridge_backend::FunctionLinkage,
        },
        Refused(Box<FrontendRefusal>),
    }

    let mut items: Vec<Item<'tcx>> = Vec::with_capacity(instances.len());
    for (instance, linkage) in instances {
        let symbol = tcx.symbol_name(instance).name.to_string();
        // Crate-module mode keeps refusing concrete generic instances: its
        // published module is pre-monomorphization (see `GenericPolicy`).
        match local_body_def(tcx, instance, &symbol, GenericPolicy::Refuse) {
            Ok(def) => {
                // The producer's `display_path` is the UNTRIMMED path
                // (`crate_module.rs` wraps every `def_path_str` in
                // `with_no_trimmed_paths!`); a trimmed one would silently miss.
                let def_path = rustc_middle::ty::print::with_no_trimmed_paths!(
                    tcx.def_path_str(def.to_def_id())
                );
                items.push(Item::Admissible { symbol, def_path, def, instance, linkage });
            }
            Err(refusal) => {
                items.push(Item::Refused(Box::new(clean_below_gate::name(tcx, instance, refusal))))
            }
        }
    }

    let link_names: Vec<(String, String)> = items
        .iter()
        .filter_map(|item| match item {
            Item::Admissible { symbol, def_path, .. } => Some((def_path.clone(), symbol.clone())),
            Item::Refused(_) => None,
        })
        .collect();

    // (2) THE CONSUMPTION. This is the call that did not exist anywhere in
    // codegen before: the backend asking the crate-level producer for the
    // module it assembled. The borrow cannot escape the Session-state closure,
    // so the whole-module preconditions run inside it and what comes out is
    // owned — which also keeps the state lock held for preparation only, not
    // for the whole lowering.
    let prepared =
        trust_thir_lower::crate_module::with_published_crate_module(tcx.sess, |published| {
            match published {
                // Trust (WS5.2): the def-path index is the producer's
                // `display_path` map; `symbols()` is keyed by link-time symbol.
                Ok(published) => prepare_crate_module(
                    published.crate_name(),
                    published.module(),
                    published.display_paths(),
                    published.ambiguous_display_paths(),
                    published.codegen_inventory(),
                    published.codegen_license_refusal(),
                    &link_names,
                ),
                Err(reason) => Err(reason.to_string()),
            }
        });

    let mut census = RefusalCensus::default();

    // (3) A WHOLE-MODULE refusal is attributed to EVERY reachable item rather
    // than short-circuited, so the census still reports the true refused count
    // and the report still names the one reason. This is the same contract the
    // per-item path has: no fallback, and the compilation fails.
    // Trust (effect conservation, D28): a body the conservation check did not judge conserved
    // is not code, and must not be reachable as LOWERING CONTEXT either — the converter inlines
    // intra-module pure leaves, so a conserved caller could otherwise pull a refused callee's
    // body into its own bytes. Such bodies are turned into declarations in this consumer's own
    // clone; a check that never ran refuses the whole module.
    let prepared = prepared.and_then(|mut prepared| {
        let conserved = trust_thir_lower::effect_conservation::conserved_function_ids(tcx.sess)?;
        trust_thir_lower::effect_conservation::strip_unconserved_bodies(
            std::sync::Arc::make_mut(&mut prepared.module),
            &conserved,
        );
        Ok(prepared)
    });
    let prepared = match prepared {
        Ok(prepared) => prepared,
        Err(detail) => {
            for item in items {
                match item {
                    // An item the INVENTORY PROJECTION already refused keeps
                    // its own class. Re-attributing an `upstream-body` to
                    // `crate-module-unavailable` would hide the largest class
                    // on every real crate behind whichever whole-module
                    // precondition happened to fail first.
                    Item::Refused(refusal) => census.record(*refusal),
                    Item::Admissible { symbol, instance, .. } => {
                        census.record(clean_below_gate::name(
                            tcx,
                            instance,
                            FrontendRefusal::CrateModuleUnavailable {
                                symbol,
                                detail: detail.clone(),
                            },
                        ));
                    }
                }
            }
            return CrateModuleOutcome { lowered: Vec::new(), linkage: Vec::new(), census };
        }
    };

    tracing::debug!(
        crate_name = %prepared.crate_name,
        functions = prepared.module.functions.len(),
        licensed = prepared.licensed_count(),
        named = prepared.link_names.len(),
        "[trust_cg] trust-ir frontend: prepared the published crate module as lowering context"
    );

    // (4) Per item, in inventory order.
    let mut lowered = Vec::new();
    let mut linkage = Vec::new();
    for item in items {
        match item {
            Item::Refused(refusal) => census.record(*refusal),
            Item::Admissible { symbol, def_path, def, instance, linkage: item_linkage } => {
                if let Err(detail) =
                    trust_thir_lower::effect_conservation::admit_for_codegen(tcx.sess, def)
                {
                    census.record(clean_below_gate::name(
                        tcx,
                        instance,
                        FrontendRefusal::EffectNotConserved { symbol, detail },
                    ));
                    continue;
                }
                match lower_from_crate_module(
                    tcx,
                    &prepared,
                    instance,
                    &symbol,
                    &def_path,
                    &validate_abi,
                ) {
                    Ok(function) => {
                        lowered.push(function);
                        linkage.push(item_linkage);
                    }
                    Err(refusal) => census.record(clean_below_gate::name(tcx, instance, refusal)),
                }
            }
        }
    }

    CrateModuleOutcome { lowered, linkage, census }
}

/// The per-session cache behind [`shared_lowering_context`].
#[derive(Default)]
struct SharedLoweringContexts {
    /// `(address of the producer's module, its shared copy)`.
    entries: Vec<(usize, std::sync::Arc<trust_ir::Module>)>,
}

/// How many distinct lowering contexts one session keeps a shared copy of.
/// The handoff lane lowers every function against one module; a miss past this
/// bound falls back to the per-function clone instead of growing the cache.
const SHARED_LOWERING_CONTEXTS: usize = 4;

/// One copy of `produced`, shared by every function lowered against it (plan
/// item K). `None` when there is no assembled handoff or the cache is full.
/// Keyed by the module's address: the lowering context is the plan's module,
/// which lives for the whole codegen pass of this session.
///
/// Trust (WS5.2): the copy is NOT renamed. The producer names every assembled
/// body by its link-time symbol and `lower_from_module` checks the selected
/// function's name against `symbol` before it gets here, so the copy is the
/// producer's module as published (this used to stamp each body's mono symbol
/// onto the copy; that rename is now the producer's job, at production).
fn shared_lowering_context(
    tcx: TyCtxt<'_>,
    produced: &trust_ir::Module,
) -> Option<std::sync::Arc<trust_ir::Module>> {
    let key = std::ptr::from_ref(produced) as usize;
    let cached = tcx.sess.with_trust_compiler_state::<SharedLoweringContexts, _>(|cache| {
        cache.entries.iter().find(|(address, _)| *address == key).map(|(_, module)| module.clone())
    });
    if cached.is_some() {
        return cached;
    }
    let has_handoff =
        tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| !handoff.codegen_body_ids().is_empty(),
        );
    if !has_handoff {
        return None;
    }
    let module = std::sync::Arc::new(produced.clone());
    tcx.sess.with_trust_compiler_state::<SharedLoweringContexts, _>(|cache| {
        if cache.entries.len() < SHARED_LOWERING_CONTEXTS {
            cache.entries.push((key, module.clone()));
            Some(module)
        } else {
            None
        }
    })
}

/// Trust (WS5.2): how a refusal names a function of the published module: its `Function.name`
/// — the link-time symbol — then, when it differs, the def path the user wrote
/// (`display_path`): "`_RNvCs..._1k1g` (`k::g`)". A row with no display path is its name alone.
fn function_label(function: &trust_ir::Function) -> String {
    match function.display_path.as_deref() {
        Some(path) if path != function.name => format!("`{}` (`{path}`)", function.name),
        _ => format!("`{}`", function.name),
    }
}

/// [`FrontendRefusal::CustomMirBody`] for a `#[custom_mir]` item.
fn refuse_custom_mir(
    tcx: TyCtxt<'_>,
    def_id: rustc_span::def_id::DefId,
    symbol: &str,
) -> Result<(), FrontendRefusal> {
    if rustc_attr_ir::find_attr!(tcx, def_id, CustomMir(..)) {
        Err(FrontendRefusal::CustomMirBody { symbol: symbol.to_string() })
    } else {
        Ok(())
    }
}

/// Trust (R-8 ledger item 1): THE unfaithful-panic refusal of the `lir` consumer's lanes — the
/// handoff and instance lanes (`lower_from_module`) and the crate-module lane
/// (`lower_from_crate_module`); the compiler lane sites its checks instead ([`panic_sites`]).
/// Refuses the function `func_id` of `module` when
/// [`reachable_runtime_check`] finds an `Inst::Assert` in its own body or in any
/// function its call census reaches (a callee the leaf inliner would splice), since
/// the converter lowers a failed `Assert` to a bare trap. SYNTACTIC: an `Assert`
/// the verifier proved never fails is refused too, until item P.
fn refuse_unfaithful_panic(
    module: &trust_ir::Module,
    func_id: trust_ir::FuncId,
    symbol: &str,
) -> Result<(), FrontendRefusal> {
    match reachable_runtime_check(module, func_id) {
        None => Ok(()),
        Some(detail) => {
            Err(FrontendRefusal::UnfaithfulPanic { symbol: symbol.to_string(), detail })
        }
    }
}

/// Plan step 3.5 (docs/design/2026-10-02-step3-lean-through-trust-ir.md §5.7): the line F1 prints
/// on every compile of a crate with a Clean-origin def — who read a `clean_origin_mir` body in
/// this compilation, by lane (`trust_thir_lower::clean_origin_reach`). `None` for a crate with no
/// Clean-origin def (nothing to count, nothing printed). Disclosure, never a gate.
pub(crate) fn clean_origin_reach_note(tcx: TyCtxt<'_>) -> Option<String> {
    if tcx.resolutions(()).clean_origin_defs.is_empty() {
        return None;
    }
    Some(format!(
        "trust-cg trust-ir frontend: {}",
        trust_thir_lower::clean_origin_reach::snapshot(tcx.sess).render()
    ))
}

#[cfg(test)]
mod tests;
