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
//!   `def`? Decided by kernel definitional equality, **admitted at the carrier
//!   type**, against a declaration that must itself have entered the
//!   environment through a full kernel check.
//!
//! Since I7 the crate also carries the cross-crate half's DECISIONS:
//! [`admission`] defines the verdict digest (the wire unit — kernel version,
//! environment digest, axiom closure, carrier decision, defeq evidence; never
//! a source hash) and [`admission::readmit`], the fail-closed re-admission of
//! an imported certificate. Of the rustc metadata transport, the **ENCODE half
//! is wired** (2026-08-19): the compiler's export provider mints the wire
//! bytes through the one seam [`admission::mint_encoded_digest_for_export`]
//! (re-earning a fresh [`gate::Faithful`] against the exact body rmeta
//! serializes), and rmeta carries a per-def digest table plus two crate-root
//! fields — the island sources (transport, never authority: the importer
//! re-elaborates them under its OWN kernel) and the Clean-origin export list
//! (the digest table's second, independent encoding, so row-absence cannot
//! demote a Clean-origin def to ordinary Rust). The IMPORT half —
//! re-admission at the extern `optimized_mir`/`mir_for_ctfe` decode
//! chokepoint, plus the local re-gate — is **not wired yet**; until it lands,
//! [`admission::readmit`] remains exercised only crate-side.
//!
//! # THE STATE OF THIS CRATE — READ BEFORE CITING IT
//!
//! A Clean-origin `DefId` IS minted and a Clean-origin `Body` IS emitted, for
//! the **parameter-projection**, **single wrapping binop** and **composed
//! wrapping tree** fragments — `fun a b => a`, `fun a b => a + b` and
//! `fun a b => (a + b) * a` (add/sub/mul, `Param` or in-range numeral
//! operands, one unsigned machine width across the signature, at most
//! [`COMPOSED_MAX_OPS`] ops per body). Citing this crate as evidence that
//! `let g = gcd(12, 18);` works would still be false: `gcd` needs recursion,
//! which no shape provides. `let v = m::pick(41, 7);`,
//! `wsum(u64::MAX, 1) == 0` and `wmix(u64::MAX, 1) == 0` are what run.
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
pub mod emit;
pub mod gate;
pub mod mint;

pub use admission::{
    environment_digest_for, local_kernel_version, mint_encoded_digest_for_export,
    mint_verdict_digest, readmit, CarrierDecision, CarrierPosition, DecodeRefusal, DefeqEvidence,
    DigestMintRefusal, EnvironmentDigest, EnvironmentDigestRefusal, ExportDigestRefusal,
    Readmitted, ReadmissionRefusal, UnencodableCarrierWidth, VerdictDigest,
};
pub use emit::{
    admit_lowering, plan_clean_origin_body, CleanOriginPlan, CleanOriginShape, EmitRefusal,
    COMPOSED_MAX_OPS,
};
pub use gate::{check_faithful, Faithful, GateRefusal};
pub use mint::{decide_mint, MintGrant, MintRefusal};
