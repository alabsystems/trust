// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The Beyond-TLA executable presentation as Clean source text, with its identity.
//!
//! ONE COPY. Every module is `include_str!`ed from `trust-spec-temporal/clean/Trust`,
//! the files that crate kernel-checks (`model_prelude_kernel`, `model_statement_pins`,
//! `clean_semantics_probes`), so what ty consumes and what trust certifies cannot
//! differ. Nothing here is trusted: every declaration is elaborated and
//! kernel-checked by whoever serves it.
//!
//! Identity (ty design `31-coverage-grades-and-trust.md`, "Identity"):
//! * [`PRELUDE_DIGEST`] binds the source bytes: SHA-256 over `(name NUL source NUL)*`
//!   in [`MODULES`] order (B1A-D35). `tests::digest::source_digest_matches`
//!   recomputes it in the debug unit tests, and trust's push lane runs that test on
//!   every push that edits `crates/trust-spec-temporal/clean/Trust/`
//!   (`scripts/check_crates_tests_scoped.py`, `CROSS_CRATE_INSTRUMENTS`). An edit to
//!   ANY served module, `Temporal.lean` and `FiniteModel.lean` included, must
//!   re-bless it: `targo --unverified test -p trust-model-prelude --lib --
//!   --ignored --exact tests::digest::print_source_digest --nocapture` prints the
//!   new literal.
//! * [`PRELUDE_TERM_DIGEST`] binds the elaborated prelude terms (B1A-D34).
//! * [`EP_VERSION`] mirrors `Trust.Model.epVersion`; [`check_ep_version`] refuses a
//!   presentation that is not complete (B1A-D03).

/// `Trust.Temporal`: behaviours, `Always`/`Eventually`/`LeadsTo`, `StateMachine`,
/// fairness. The temporal lane's file, served unchanged.
pub const TEMPORAL: &str = include_str!("../../trust-spec-temporal/clean/Trust/Temporal.lean");

/// `Trust.FiniteModel` (namespace `Trust.Temporal.FiniteModel`): the finite-model
/// vocabulary and its `Member` inductive. The temporal lane's file, served unchanged.
pub const FINITE_MODEL: &str =
    include_str!("../../trust-spec-temporal/clean/Trust/FiniteModel.lean");

/// `Trust.List` (namespace `Trust.Temporal`): `Member`, the reducible alias of
/// FiniteModel's `Member` (B1A-D04), `Distinct`, and the reducible Bool list helpers.
pub const LIST: &str = include_str!("../../trust-spec-temporal/clean/Trust/List.lean");

/// `Trust.Graph` (namespace `Trust.Temporal`): the raw state-graph vocabulary of design
/// 40:28-68, `Terminal`, `Reach`, `Star`, `MaxPath`, `Chain`, `lastOf`, `FirstAtEnd` and
/// `WitnessPath` (B1A-D05).
pub const GRAPH: &str = include_str!("../../trust-spec-temporal/clean/Trust/Graph.lean");

/// `Trust.Thm.Ports`: shared theorems over the model vocabulary, beginning with
/// `Trust.Temporal.reach_least`. Consumers explicitly elaborate this suffix after
/// [`MODULES`]. It is outside the executable presentation and its identities;
/// `trust-spec-temporal`'s `model_theorems` harness binds these exact bytes and each
/// checked theorem's statement closure.
pub const PORTS: &str = include_str!("../../trust-spec-temporal/clean/Trust/Thm/Ports.lean");

/// `Trust.Model.Value` (namespace `Trust.Model`): the presentation's values and
/// `epVersion`.
pub const MODEL_VALUE: &str =
    include_str!("../../trust-spec-temporal/clean/Trust/Model/Value.lean");

/// `Trust.Model.Syntax` (namespace `Trust.Model`): `QKind`, `PrimOp` (the value-semantic
/// K2 rows plus the B1a additions, B1A-D10), the mutual `Expr`/`Act`, the Boolean
/// encoding definitions (B1A-D11), and de Bruijn shifting, substitution and
/// instantiation (B1A-D15).
pub const MODEL_SYNTAX: &str =
    include_str!("../../trust-spec-temporal/clean/Trust/Model/Syntax.lean");

/// `Trust.Model.Spec` (namespace `Trust.Model`): `FairEntry`, `ChoiceMode`, the fifteen-field
/// `Spec` (B1A-D43), `Spec.StateWf`, `Spec.fuel` (B1A-D16), `Spec.wf` (B1A-D15, B1A-D17),
/// `Action`, `Act.split` (B1A-D18), `Spec.actions` and `Action.toAct`.
pub const MODEL_SPEC: &str = include_str!("../../trust-spec-temporal/clean/Trust/Model/Spec.lean");

/// `Trust.Model.Tlc` (namespace `Trust.Model`): the executable values `Ctx`, `SetGen` and
/// `XVal` with their well-formedness, the six forcing rules `Tlc.rule.*` (B1A-D36), and the
/// block of B1A-D07: `Job`, `Out`, `Tlc.step`, `Tlc.run` and the nine design functions
/// (`evalX` ... `tlcHoldsF`) at their design signatures. B1A-14a's skeleton: every case of
/// the block answers `unmodeled todo` until rows 14b-19 fill it.
pub const MODEL_TLC: &str = include_str!("../../trust-spec-temporal/clean/Trust/Model/Tlc.lean");

/// The modules served, in the dependency order of B1A-D50: `(module, depends on,
/// source)`. Elaborating them in this order elaborates `FiniteModel.lean` exactly as
/// `trust-temporal-prelude` serves it. The full order, as modules arrive, is
/// [`MODULE_ORDER`].
pub const MODULES: &[(&str, &[&str], &str)] = &[
    ("Trust.Temporal", &[], TEMPORAL),
    ("Trust.FiniteModel", &["Trust.Temporal"], FINITE_MODEL),
    ("Trust.List", &["Trust.FiniteModel"], LIST),
    ("Trust.Graph", &["Trust.Temporal"], GRAPH),
    ("Trust.Model.Value", &[], MODEL_VALUE),
    ("Trust.Model.Syntax", &["Trust.Model.Value"], MODEL_SYNTAX),
    ("Trust.Model.Spec", &["Trust.List", "Trust.Model.Syntax"], MODEL_SPEC),
    ("Trust.Model.Tlc", &["Trust.Model.Spec"], MODEL_TLC),
];

/// The complete module order of B1A-D50. [`MODULES`] is always a subsequence of it.
pub const MODULE_ORDER: &[&str] = &[
    "Trust.Temporal",
    "Trust.FiniteModel",
    "Trust.List",
    "Trust.Graph",
    "Trust.Model.Value",
    "Trust.Model.Syntax",
    "Trust.Model.Spec",
    "Trust.Model.Tlc",
    "Trust.Model.Claims",
    "Trust.Model.Gen",
    "Trust.Model.Shape",
    "Trust.Model.FiniteModel",
];

/// The executable presentation's version: `Trust.Model.epVersion` (design 10:526).
pub const EP_VERSION: u32 = 1;

/// Whether the presentation is complete. It stays false until the B1a lane lands
/// (B1A-54), so a checkpoint landing can never be consumed as a finished
/// presentation (B1A-D03, B1A-D63). It is in neither digest.
pub const EP_COMPLETE: bool = false;

/// The registry refusal [`check_ep_version`] returns (ty design 50, `model.ep-version`).
pub const REFUSAL_EP_VERSION: &str = "model.ep-version";

/// SHA-256 over `(name NUL source NUL)*` for [`MODULES`], lower-case hex (B1A-D35).
/// Re-bless with `tests::digest::print_source_digest` after any edit to a served
/// module; `tests::digest::source_digest_matches` fails until then.
pub const PRELUDE_DIGEST: &str = "e6b56953d16f3bb52f6505dbf9e2281806614ccf8f6243a7d3774c24dedc4064";

/// SHA-256 over the elaborated terms of the constants the prelude adds (B1A-D34),
/// lower-case hex. UNBLESSED until lane row B1A-25 computes it: the 64 zero digits
/// are not the digest of any environment, so a term check against this literal
/// refuses every environment (`model.prelude-terms`), which is fail-closed
/// (B1A-D78).
pub const PRELUDE_TERM_DIGEST: &str =
    "0000000000000000000000000000000000000000000000000000000000000000";

/// One `Fail.unmodeled` code of `Trust.Model.Code` (ty design 10:109, B1A-D13).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnmodeledCode {
    /// The `Nat` that `Fail.unmodeled` carries.
    pub number: u32,
    /// The design's code, e.g. `int.div-wrap`.
    pub code: &'static str,
    /// The Lean constant holding [`Self::number`], e.g. `Trust.Model.Code.intDivWrap`.
    pub lean: &'static str,
    /// The registry refusal it is reported as (ty design 50), or `-` for the
    /// development placeholder `todo`, which B1A-25 deletes.
    pub refusal: &'static str,
}

/// The `Fail.unmodeled` code table of `Trust.Model.Code`, mirrored line by line from
/// `Trust/Model/Value.lean` (B1A-D13). `tests::unmodeled_codes_mirror_the_lean_table`
/// checks this mirror against the Lean source text; trust-spec-temporal's
/// `model_prelude_kernel` checks every number in the kernel.
pub const UNMODELED_CODES: &[UnmodeledCode] = &[
    UnmodeledCode {
        number: 0,
        code: "int.div-wrap",
        lean: "Trust.Model.Code.intDivWrap",
        refusal: "model.int-div-wrap",
    },
    UnmodeledCode {
        number: 1,
        code: "lazy.arg",
        lean: "Trust.Model.Code.lazyArg",
        refusal: "model.lazy-unpinned",
    },
    UnmodeledCode {
        number: 2,
        code: "lazy.except",
        lean: "Trust.Model.Code.lazyExcept",
        refusal: "model.lazy-unpinned",
    },
    UnmodeledCode {
        number: 3,
        code: "lazy.refused-force",
        lean: "Trust.Model.Code.lazyRefusedForce",
        refusal: "model.lazy-unpinned",
    },
    UnmodeledCode {
        number: 4,
        code: "lazy.mem-kind",
        lean: "Trust.Model.Code.lazyMemKind",
        refusal: "model.lazy-unpinned",
    },
    UnmodeledCode {
        number: 5,
        code: "lazy.soa-elem",
        lean: "Trust.Model.Code.lazySoaElem",
        refusal: "model.lazy-unpinned",
    },
    UnmodeledCode {
        number: 6,
        code: "lazy.enabled-assign",
        lean: "Trust.Model.Code.lazyEnabledAssign",
        refusal: "model.lazy-unpinned",
    },
    UnmodeledCode {
        number: 7,
        code: "cmp.unpinned",
        lean: "Trust.Model.Code.cmpUnpinned",
        refusal: "model.cmp-unpinned",
    },
    UnmodeledCode { number: 999, code: "todo", lean: "Trust.Model.Code.todo", refusal: "-" },
];

/// Why [`check_ep_version`] refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EpVersionRefusal {
    /// The version the consumer was built against.
    pub requested: u32,
    /// [`EP_COMPLETE`] when the check ran.
    pub complete: bool,
}

impl EpVersionRefusal {
    /// The registry refusal code, always [`REFUSAL_EP_VERSION`].
    #[must_use]
    pub fn code(&self) -> &'static str {
        REFUSAL_EP_VERSION
    }
}

impl std::fmt::Display for EpVersionRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.complete {
            write!(
                f,
                "{}: built for executable presentation {}, this prelude is version {EP_VERSION}",
                REFUSAL_EP_VERSION, self.requested
            )
        } else {
            write!(
                f,
                "{}: executable presentation {EP_VERSION} is not complete (EP_COMPLETE is false); \
                 version {} refused",
                REFUSAL_EP_VERSION, self.requested
            )
        }
    }
}

impl std::error::Error for EpVersionRefusal {}

/// Accept a consumer built for presentation `version` only when the presentation
/// is complete and `version` is [`EP_VERSION`]; otherwise refuse with
/// `model.ep-version` (B1A-D03).
pub fn check_ep_version(version: u32) -> Result<(), EpVersionRefusal> {
    check_ep_version_with(version, EP_COMPLETE)
}

fn check_ep_version_with(version: u32, complete: bool) -> Result<(), EpVersionRefusal> {
    if complete && version == EP_VERSION {
        Ok(())
    } else {
        Err(EpVersionRefusal { requested: version, complete })
    }
}

#[cfg(test)]
mod tests;
