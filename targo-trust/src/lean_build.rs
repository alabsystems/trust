// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Standalone Lean library artifacts, not executable or cross-crate authority.
//!
//! The LIBRARY output is a versioned JSON envelope containing canonical binary
//! Trust-IR and the exact checked local sources. `--census` writes one further
//! file beside it — a diagnostic `trust.lean.check-kernel-roster/v1` report with
//! no Trust-IR in it, written BEFORE lowering and deliberately retained when the
//! library refuses, so on a refusing build it is the only output there is.
//! Every computational declaration
//! in the accepted environment delta must pass the independent actual-SSA gate.
//! Serialized bindings are disclosures: import must recheck sources and re-earn
//! the gate, as `decode_and_revalidate` does with an accepted source context.
//!
//! Everything above is the `--emit=trust-ir` lane. `--emit=diagnostic-runtime-trust-ir`
//! is a SECOND lane, owned by [`runtime`]: it publishes a raw tMBC module for one
//! selected entry and the call/PAP closure it reaches, earns no gate, and is not
//! a library. It REQUIRES `--census`, and writes that census AFTER lowering —
//! the census carries the lowering's own diagnostic record — but still before
//! the module is published, so a refusal there also leaves the census as the
//! only output.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clean_kernel::{Name, TypeChecker};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_certify::lean_source_batch::AcceptedLeanSourceContext;
use trust_clean_ir_gate::standalone::admit_standalone_scalar;
use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::ty::FuncTy;
use trust_ir::value::{FuncId, FuncTyId};
use trust_ir::{Function, Module, Producer};

mod runtime;

const SCHEMA: &str = "trust.lean.ir-library/v1";
const AUTHORITY: &str = "recheck-sources-and-re-earn-gate-on-import";
const LIMITATIONS: &[&str] = &[
    "Only local-source computational declarations admitted by the independent wrapping-binop gate are supported.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
const PROJECTION_LIMITATIONS: &[&str] = &[
    "Only local-source wrapping binops and ordinary UInt8/16/32/64 parameter projections admitted by the independent actual-SSA gate are supported.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
const LITERAL_LIMITATIONS: &[&str] = &[
    "Only local-source wrapping binops, ordinary UInt8/16/32/64 parameter projections and in-range UInt literal returns admitted by the independent actual-SSA gate are supported; literal parameters must share the result width.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
const MIXED_LITERAL_LIMITATIONS: &[&str] = &[
    "Only local-source wrapping binops, ordinary UInt8/16/32/64 parameter projections and in-range UInt literal returns admitted by the independent actual-SSA gate are supported; literal parameters may use distinct exact UInt8/16/32/64 carriers.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
const EXPRESSION_LIMITATIONS: &[&str] = &[
    "Only local-source wrapping binops, ordinary UInt8/16/32/64 parameter projections, in-range UInt literal returns and homogeneous wrapping expression trees of 2..=32 Add/Sub/Mul nodes admitted by the independent actual-SSA gate are supported; expression leaves are parameters or in-range numerals, and literal parameters may use distinct exact UInt carriers.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
/// Trust (WS5.20): appended to whichever disclosure a population selects when a
/// literal return's SOURCE numeral was out of range and was emitted as its
/// residue, so the "in-range UInt literal returns" wording never describes a
/// body whose source spelling was not in range.
const LITERAL_RESIDUE_DISCLOSURE: &str = "A UInt literal written outside 0..2^w is emitted as its Lean OfNat residue modulo 2^w and admitted only because the kernel decides that in-range residue definitionally equal to the source numeral at the exact carrier.";
/// Trust (WS5.20): a population that includes the standalone SCALAR vocabulary.
const SCALAR_LIMITATIONS: &[&str] = &[
    "Only local-source wrapping binops, ordinary UInt8/16/32/64 parameter projections, in-range UInt literal returns, homogeneous wrapping expression trees of 2..=32 Add/Sub/Mul nodes, unsigned comparisons (<, <=, ==) of two parameters returned as Bool, parameter selects (if a < b / a <= b / a == b then x else y), connectives (&&, ||) of two such comparisons, &&&/||| trees of up to 32 operators, and total unsigned division of two parameters (x / 0 = 0, emitted with an explicit zero guard) admitted by the independent actual-SSA gate are supported; expression leaves are parameters or in-range numerals, and literal parameters may use distinct exact UInt carriers.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
/// Trust (WS5.20): a population that includes the scalar DECISION family.
const DECISION_LIMITATIONS: &[&str] = &[
    "Only local-source wrapping binops, ordinary UInt8/16/32/64 parameter projections, in-range UInt literal returns, homogeneous wrapping expression trees of 2..=32 Add/Sub/Mul nodes, unsigned comparisons (<, <=, ==) of two parameters returned as Bool, and parameter selects (if a < b / a <= b / a == b then x else y) admitted by the independent actual-SSA gate are supported; expression leaves are parameters or in-range numerals, and literal parameters may use distinct exact UInt carriers.",
    "External .olean packages, general runtime-body completeness, mixed-language linking and native codegen remain unavailable.",
    "Serialized gate bindings are not transferable proof authority or G1-G8 completion evidence.",
];
const USAGE: &str = "Usage: targo trust build FILE.lean --emit=trust-ir --out NEW_PATH [--census NEW_PATH] [--verbose]\n\
    Write a trust.lean.ir-library/v1 JSON library envelope containing canonical\n\
    binary Trust-IR, checked local-source snapshots and per-body gate bindings.\n\
    The output must not exist. Unsupported computational siblings refuse the\n\
    whole artifact. This does not emit an executable or a raw .tir file.\n\
    Use `targo trust check FILE.lean` for kernel checking without lowering.\n\
    --verbose includes full underlying refusal details; it does not change admission.\n\
    --census records the independent source/kernel inventory before lowering, even\n\
    when a computational sibling refuses. It is not runtime or completion authority.\n\
    --census-olean-path DIR (repeatable, requires --census) inventories external\n\
    dependencies only; it does NOT enable external imports or kernel authority.";

#[derive(Debug, PartialEq)]
pub(crate) struct Request {
    input: PathBuf,
    output: PathBuf,
    verbose: bool,
    census_output: Option<PathBuf>,
    olean_paths: Vec<PathBuf>,
}

pub(crate) fn parse(args: &[String]) -> Result<Request, String> {
    let mut input = None;
    let mut output = None;
    let mut emit = None;
    let mut verbose = false;
    let mut census_output = None;
    let mut olean_paths = Vec::new();
    let mut index = 0;
    while index < args.len() {
        // Trust (2026-11-13): Cargo's job count is accepted and ignored, as the
        // `check` route's parser does (`cli::cargo_jobs_hint_width`): this route
        // shares its lane selection, and aterm's build admission appends
        // `--jobs=N` to every admitted command line.
        if let Some(width) = crate::cli::cargo_jobs_hint_width(args, index) {
            index += width;
            continue;
        }
        let arg = &args[index];
        if arg == "--verbose" {
            if verbose {
                return Err("duplicate --verbose".into());
            }
            verbose = true;
            index += 1;
            continue;
        }
        let (kind, value) = if arg == "--out"
            || arg == "--emit"
            || arg == "--census"
            || arg == "--census-olean-path"
        {
            index += 1;
            let value = args.get(index).ok_or_else(|| format!("{arg} requires a value"))?;
            (arg.as_str(), value.as_str())
        } else if let Some(value) = arg.strip_prefix("--out=") {
            ("--out", value)
        } else if let Some(value) = arg.strip_prefix("--emit=") {
            ("--emit", value)
        } else if let Some(value) = arg.strip_prefix("--census=") {
            ("--census", value)
        } else if let Some(value) = arg.strip_prefix("--census-olean-path=") {
            ("--census-olean-path", value)
        } else if !arg.starts_with('-') && Path::new(arg).extension().is_some_and(|s| s == "lean") {
            if input.replace(PathBuf::from(arg)).is_some() {
                return Err(
                    "one root .lean file is required; local imports form its source closure".into(),
                );
            }
            index += 1;
            continue;
        } else {
            return Err(format!("unsupported Lean build argument `{arg}`"));
        };
        if value.is_empty() || value.starts_with('-') {
            return Err(format!("{kind} requires a nonempty value that does not start with `-`"));
        }
        match kind {
            "--census-olean-path" => olean_paths.push(PathBuf::from(value)),
            "--out" if output.replace(PathBuf::from(value)).is_some() => {
                return Err("duplicate --out".into());
            }
            "--emit" if emit.replace(value.to_owned()).is_some() => {
                return Err("duplicate --emit".into());
            }
            "--census" if census_output.replace(PathBuf::from(value)).is_some() => {
                return Err("duplicate --census".into());
            }
            _ => {}
        }
        index += 1;
    }
    let input = input.ok_or_else(|| "a root .lean source file is required".to_owned())?;
    if emit.as_deref() != Some("trust-ir") {
        return Err("standalone Lean executable codegen is not implemented; explicitly request \
            `--emit=trust-ir --out NEW_PATH` for the independently gated library-artifact lane, \
            or use `targo trust check FILE.lean`"
            .into());
    }
    let output =
        output.ok_or_else(|| "--out NEW_PATH is required for a library artifact".to_owned())?;
    if !olean_paths.is_empty() && census_output.is_none() {
        return Err("--census-olean-path requires --census; it inventories dependencies but does not enable external imports".into());
    }
    Ok(Request { input, output, verbose, census_output, olean_paths })
}

/// Keep the actual typed failure until presentation. In particular, an origin
/// refusal's legacy MIR-oriented prose is not a standalone capability taxonomy.
#[derive(Debug)]
enum BodyRefusal {
    Source(Box<trust_clean_origin::emit::EmitRefusal>),
    Carrier(trust_clean_ir::CleanIrRefusal),
    Emitter(trust_clean_ir::CleanIrRefusal),
    Gate(trust_clean_ir_gate::GateRefusal),
    Capacity(std::num::TryFromIntError),
}

impl BodyRefusal {
    fn source(error: trust_clean_origin::emit::EmitRefusal) -> Self {
        Self::Source(Box::new(error))
    }

    fn summary(&self) -> String {
        use trust_clean_origin::emit::EmitRefusal;
        match self {
            Self::Source(error) => {
                let (category, message) = match error.as_ref() {
                    EmitRefusal::NotEmittable { .. } => (
                        "source-shape/not-emittable",
                        "checked source body has no supported standalone lowering",
                    ),
                    EmitRefusal::NoTotalCarrier { .. } => (
                        "carrier/no-total-carrier",
                        "checked source signature has no complete faithful carrier",
                    ),
                    EmitRefusal::CarrierDomainNotReflectable { .. } => (
                        "carrier/domain-not-reflectable",
                        "compiler reflection does not support this checked source carrier",
                    ),
                    EmitRefusal::LoweringUnrecognised { .. } => (
                        "source-plan/lowering-unrecognised",
                        "compiler lowering cannot be independently recognized",
                    ),
                    EmitRefusal::LoweringShapeMismatch { .. } => (
                        "source-plan/lowering-shape-mismatch",
                        "compiler lowering differs from its checked source plan",
                    ),
                    EmitRefusal::ReflectionRejected { .. } => (
                        "source-plan/reflection-rejected",
                        "compiler lowering could not be reflected into a kernel term",
                    ),
                    // Trust (W5 increment 7): a `let`-bound Rust call the planner
                    // could not carry as a value temporary, or its once-evaluation
                    // cross-check (a planner defect). A standalone `.lean` unit has
                    // no Rust callees, so this lane reaches it only through a
                    // defect; it is categorised rather than swallowed.
                    EmitRefusal::LetSpine { .. } => (
                        "source-shape/let-spine",
                        "checked source body binds a Rust call the standalone lowering cannot carry as a value temporary",
                    ),
                    // Trust (Clean R80; docs/DECISION_QUEUE.md R80-CONSUMERS-1):
                    // compiled code runs an `@[implemented_by]` implementation, not
                    // the kernel value this lane would emit, or a late
                    // `attribute [implemented_by]` command left an order record that
                    // refuses every declaration of the unit. The user's, not a defect.
                    EmitRefusal::ImplementedBy { .. } => (
                        "source-semantics/implemented-by",
                        "compiled code does not run this checked source body: an @[implemented_by] binding, or a late `attribute [implemented_by]` command",
                    ),
                    // Trust (Clean R80 item 5; docs/DECISION_QUEUE.md
                    // R80-CONSUMERS-1): compiled code calls an `@[extern]` symbol,
                    // not the kernel value this lane would emit. The user's.
                    EmitRefusal::Extern { .. } => (
                        "source-semantics/extern",
                        "compiled code does not run this checked source body: an @[extern] binding calls an external symbol",
                    ),
                    EmitRefusal::Gate(_) => {
                        ("source-plan/gate", "the source planner's independent gate refused")
                    }
                };
                format!(
                    "[{category}]: {message}{}",
                    if error.is_compiler_defect() {
                        "; compiler inconsistency, please report it"
                    } else {
                        ""
                    }
                )
            }
            Self::Carrier(error) => Self::ir_summary("carrier", error),
            Self::Emitter(error) => Self::ir_summary("emitter", error),
            // The gate currently uses this stage for both completed mismatch
            // and inconclusive resource refusal. Do not infer which from prose.
            Self::Gate(error) if error.stage() == "kernel-disagreement" => format!(
                "[gate/{}]: kernel could not establish source/SSA agreement; compiler check failed, please report it",
                error.stage()
            ),
            Self::Gate(error) => {
                format!("[gate/{}]: independent source/SSA gate refused this body", error.stage())
            }
            Self::Capacity(_) => "[emitter/capacity]: too many computational declarations".into(),
        }
    }

    fn ir_summary(phase: &str, error: &trust_clean_ir::CleanIrRefusal) -> String {
        use trust_clean_ir::CleanIrRefusal;
        let (category, detail) = match error {
            CleanIrRefusal::CarrierHasNoTrustIrType { position, clean } => (
                "unrepresented-type",
                format!(
                    "{clean:?} has no exact Trust-IR carrier at {}",
                    position.map_or_else(|| "result".into(), |index| format!("argument {index}"))
                ),
            ),
            CleanIrRefusal::ShapeNotYetSpelled { shape } => {
                ("unsupported-shape", format!("no Trust-IR lowering for {shape}"))
            }
            CleanIrRefusal::ProjectionOutOfRange { projected, arity } => (
                "invalid-projection",
                format!("compiler plan selects argument {projected} of {arity}; please report it"),
            ),
            CleanIrRefusal::InvalidUnsignedConditional => (
                "invalid-unsigned-conditional",
                "compiler plan's unsigned conditional tree disagrees with its sealed decision bound; please report it"
                    .to_owned(),
            ),
            CleanIrRefusal::RecursionAtUnboundedNatCarrier { shape } => {
                ("unbounded-recursion", format!("{shape} requires an unbounded Nat carrier"))
            }
            CleanIrRefusal::RecursionNeedsNatRuntime { shape } => {
                ("missing-runtime", format!("{shape} requires explicit Nat runtime identities"))
            }
            // A DECLARATION-level carrier refusal, not a compiler-internal
            // one: the author wrote `Nat` in a signature position of a body
            // that COMPUTES, and the fix is a machine-width carrier. So it
            // reads like `CarrierHasNoTrustIrType` above and asks for no
            // report.
            //
            // Unreachable from THIS lane today, and deliberately still
            // rendered: `assemble` lowers through
            // `emit_standalone_clean_origin_function`, which threads no
            // `NatRuntime`, so a `Nat` here refuses earlier as
            // `CarrierHasNoTrustIrType`. The day this lane threads a runtime
            // -- which is what would ADMIT a `Nat` -- this is the message an
            // author must get, and a `todo!()` or a swallowing wildcard would
            // be the wrong thing to discover then.
            CleanIrRefusal::ShapeMayNotCarryNat { shape, position } => (
                "nat-carrier",
                format!(
                    "{shape} carries Nat at {}, and {shape} computes on its carrier rather \
                     than only transporting it; a Nat position is emitted at the unbounded \
                     runtime carrier, so the body would either compute on an opaque runtime \
                     handle or wrap an unbounded value at a machine width; give the \
                     declaration a machine-width carrier (UInt8/UInt16/UInt32/UInt64, \
                     BitVec w) in every position, express it as one of the two recursion \
                     shapes, whose bignum arithmetic this producer does emit, or keep the \
                     declaration proof-only so no value is produced for it",
                    position
                        .map_or_else(|| "the result".into(), |index| format!("argument {index}"))
                ),
            ),
            CleanIrRefusal::RecursionArgIsNotPred { shape } => (
                "recursion-argument",
                format!("{shape} is outside the supported predecessor recursion"),
            ),
            CleanIrRefusal::PartialOpWithoutDivisorEvidence { op } => {
                ("missing-divisor-evidence", format!("{op} has no nonzero-divisor evidence"))
            }
            CleanIrRefusal::ConstantOutOfRange { value, width } => (
                "invalid-constant",
                format!("compiler plan's literal {value} exceeds UInt{width}; please report it"),
            ),
            // The wiring refusals below are compiler-internal invariants,
            // not anything the author of a `.lean` file can spell wrong, so each
            // asks for a report rather than offering a source-level fix. Every
            // one of them describes a body that would typecheck and validate
            // while computing something the declaration does not say, so the
            // detail names the two identities that disagree — that is what a
            // report needs to be actionable.
            //
            // The `Nat` CARRIER refusals are the v43 handle adoption's half of
            // the same class. The carrier is a nominal opaque handle pinned to
            // `trust_bignum::Nat`, so a carrier that is not that handle, or a
            // callee that is not that runtime's pinned shim, is a miswiring
            // between the producer and the validator's pin — again nothing a
            // `.lean` author can cause.
            CleanIrRefusal::NatRuntimeIsNotPinnedByTheValidator { name, runtime } => (
                "runtime-identity",
                format!(
                    "the Trust-IR validator pins no handle runtime ({name}, {runtime}), so a \
                     Nat value would have no trusted origin; please report it"
                ),
            ),
            CleanIrRefusal::NatRuntimeRoleIsNotPinned { role } => (
                "runtime-identity",
                format!(
                    "the pinned Nat runtime declares no `{role}` entry point, and the emitted \
                     recursion calls it; please report it"
                ),
            ),
            CleanIrRefusal::NatRuntimeDeclarationRefused { detail } => (
                "runtime-identity",
                format!(
                    "the pinned Nat runtime declarations could not be written into the module: \
                     {detail}; please report it"
                ),
            ),
            CleanIrRefusal::NatCarrierIsNotThePinnedHandle { carrier } => (
                "nat-carrier",
                format!(
                    "a Nat value would be carried at {carrier} where the pinned opaque handle \
                     is required; a machine or pointer carrier can be dereferenced, cast and \
                     exchanged with another runtime; please report it"
                ),
            ),
            CleanIrRefusal::NatCarrierIsAForeignHandle { name, runtime } => (
                "nat-carrier",
                format!(
                    "a Nat value would be carried at the handle ({name}, {runtime}), owned by a \
                     different runtime than the one this body calls; two opaque runtimes do not \
                     exchange handles; please report it"
                ),
            ),
            CleanIrRefusal::NatSubstituteCarrierIsThePinnedHandle => (
                "nat-carrier",
                "an executable substitute Nat carrier was declared as the pinned opaque handle, \
                 which nothing can compute on; please report it"
                    .to_owned(),
            ),
            CleanIrRefusal::NatRuntimeCalleeIsNotInTheModule { role, id } => (
                "runtime-identity",
                format!(
                    "the Nat runtime names function {id} for `{role}` and the module has no such \
                     function; please report it"
                ),
            ),
            CleanIrRefusal::NatRuntimeCalleeIsNotThePinnedShim { role, expected, actual, id } => (
                "runtime-identity",
                format!(
                    "the Nat runtime names function {id} for `{role}`, which is `{actual}` and \
                     not the pinned shim `{expected}`; the emitted body would call another \
                     function under the spelling of bignum arithmetic; please report it"
                ),
            ),
            CleanIrRefusal::NatRuntimeSelfIdIsNotTheEmittedFunction { self_id, emitted } => (
                "runtime-identity",
                format!(
                    "the Nat runtime names function {self_id} for the self-call while this \
                     declaration is being emitted as {emitted}; recursion would call a \
                     different function; please report it"
                ),
            ),
            CleanIrRefusal::NatRuntimeIdsAlias { first, second, id } => (
                "runtime-identity",
                format!(
                    "the Nat runtime entries `{first}` and `{second}` both name function \
                     {id}; they are distinct primitives and every call to one would be a \
                     call to the other; please report it"
                ),
            ),
            CleanIrRefusal::NatRuntimeIdAliasesTheEmittedFunction { runtime, id } => (
                "runtime-identity",
                format!(
                    "the Nat runtime entry `{runtime}` names function {id}, which is this \
                     declaration itself; a Clean declaration is not one of its own Nat \
                     primitives; please report it"
                ),
            ),
            CleanIrRefusal::RustCallEmissionRefused { reason } => (
                "rust-call-emission",
                format!("Rust call emission refused: {reason}; please report it"),
            ),
            CleanIrRefusal::CallEdgeWithoutOwningModuleIdentity { callee } => (
                "unanchored-call",
                format!(
                    "the call-free emission path produced a body calling function {callee}; \
                     that path runs at a placeholder id and may not embed a function \
                     identity; please report it"
                ),
            ),
        };
        format!("[{phase}/{category}]: {detail}")
    }

    fn detail(&self) -> String {
        match self {
            Self::Source(error) => error.note(),
            Self::Carrier(error) | Self::Emitter(error) => error.to_string(),
            Self::Gate(error) => error.note(),
            Self::Capacity(error) => format!("too many computational declarations: {error}"),
        }
    }
}

/// A refusal is one finished sentence plus, where one exists, the underlying
/// observation that sentence summarizes. `detail` is `None` for a refusal whose
/// own message already carries the whole underlying error (an io error, a
/// kernel error, a validator's error list): manufacturing a detail block there
/// would advertise information that does not exist. Only `detail: Some` earns
/// the `--verbose` disclosure, and only it advertises the rerun hint.
#[derive(Debug)]
enum BuildError {
    Message { message: String, detail: Option<String> },
    Incomplete { total: usize, refusals: Vec<(Name, BodyRefusal)> },
}

impl From<String> for BuildError {
    fn from(message: String) -> Self {
        Self::Message { message, detail: None }
    }
}

impl BuildError {
    /// A message refusal that really does have more underlying detail to show.
    fn detailed(message: String, detail: String) -> Self {
        Self::Message { message, detail: Some(detail) }
    }

    fn render(&self, verbose: bool) -> String {
        match self {
            Self::Message { message, detail: None } => message.clone(),
            Self::Message { message, detail: Some(detail) } => {
                if verbose {
                    format!("{message}\n  Full underlying refusal details:\n{detail}")
                } else {
                    format!("{message}\nFor full underlying refusal details, rerun with --verbose.")
                }
            }
            Self::Incomplete { total, refusals } => {
                let mut lines = vec![format!(
                    "no library artifact was emitted; {} of {total} computational declaration(s) refused:",
                    refusals.len()
                )];
                for (name, error) in refusals {
                    lines.push(format!("  `{name}` {}", error.summary()));
                    if verbose {
                        lines.push(format!(
                            "    Full underlying refusal details:\n{}",
                            error.detail()
                        ));
                    }
                }
                lines.push("The whole artifact was refused; no sibling was omitted.".into());
                lines.push("Kernel-only checking: `targo trust check FILE.lean`. Build help: `targo trust build FILE.lean --help`.".into());
                if !verbose {
                    lines.push("For full underlying refusal details, rerun with --verbose.".into());
                }
                lines.join("\n")
            }
        }
    }
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.render(false))
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceRecord {
    module: String,
    path: String,
    source: String,
    sha256: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BodyBinding {
    declaration: Name,
    function_id: u32,
    kernel_payload_sha256: String,
    subject_digest: String,
    carrier: String,
    method: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LibraryEnvelope {
    schema: String,
    authority: String,
    native_codegen: String,
    source_closure_sha256: String,
    owned_declarations_sha256: String,
    sources: Vec<SourceRecord>,
    owned_declarations: Vec<Name>,
    kernel_only_declarations: Vec<Name>,
    bodies: Vec<BodyBinding>,
    module_binary_hex: String,
    module_sha256: String,
    module_stable_digest: String,
    limitations: Vec<String>,
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push(DIGITS[(byte >> 4) as usize] as char);
        result.push(DIGITS[(byte & 15) as usize] as char);
    }
    result
}

fn unhex(text: &str) -> Result<Vec<u8>, String> {
    if !text.len().is_multiple_of(2)
        || !text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("module_binary_hex must contain an even number of lowercase hex digits".into());
    }
    let nibble = |b: u8| if b <= b'9' { b - b'0' } else { b - b'a' + 10 };
    Ok(text.as_bytes().as_chunks::<2>().0.iter().map(|pair| nibble(pair[0]) * 16 + nibble(pair[1])).collect())
}

fn sources(context: &AcceptedLeanSourceContext<'_>) -> Vec<SourceRecord> {
    context
        .sources()
        .iter()
        .map(|source| SourceRecord {
            module: source.module.clone(),
            path: source.path.clone(),
            source: source.source.clone(),
            sha256: sha256(source.source.as_bytes()),
        })
        .collect()
}

/// Classify the complete kernel-owned delta, never the emitter's admitted list.
/// Even a generated constructor/recursor with no ordinary value participates.
/// Only a type that the kernel determines inhabits Prop is proof-only; unknown
/// classification and every remaining declaration require a computational body.
fn partition(context: &AcceptedLeanSourceContext<'_>) -> Result<(Vec<Name>, Vec<Name>), String> {
    let env = context.environment();
    let mut computational = Vec::new();
    let mut kernel_only = Vec::new();
    for name in context.owned_declarations() {
        let info = env.get_const(name).ok_or_else(|| {
            format!("owned declaration `{name}` is absent from its kernel environment")
        })?;
        let sort = TypeChecker::new(env).infer_sort(&info.type_).map_err(|error| {
            format!("cannot classify `{name}` as proof-only or computational: {error}")
        })?;
        if sort.is_zero() {
            kernel_only.push(name.clone());
        } else {
            computational.push(name.clone());
        }
    }
    Ok((computational, kernel_only))
}

fn file_table_refusal(path: &str, error: trust_ir::IdSpaceExhausted) -> String {
    format!("cannot record checked Lean source `{path}` in the Trust-IR file table: {error}")
}

// Keep the fallible source-identity boundary checked even before warning ratchets run.
#[deny(unused_must_use)]
fn module_shell(context: &AcceptedLeanSourceContext<'_>) -> Result<Module, String> {
    let mut module = Module::new(format!("lean-library:{}", context.source_closure_sha256()));
    for source in context.sources() {
        module
            .intern_file(&source.path)
            .map_err(|error| file_table_refusal(&source.path, error))?;
    }
    Ok(module)
}

fn validate(module: &Module) -> Result<(), String> {
    let errors = trust_ir_build::validate_module(module);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!("assembled Trust-IR module is invalid: {errors:?}"))
    }
}

fn binding(
    context: &AcceptedLeanSourceContext<'_>,
    name: &Name,
    signature: &FuncTy,
    original: &Function,
    published: &Function,
) -> Result<BodyBinding, String> {
    checked_binding(context, name, signature, original, published).map_err(|error| error.note())
}

fn checked_binding(
    context: &AcceptedLeanSourceContext<'_>,
    name: &Name,
    signature: &FuncTy,
    original: &Function,
    published: &Function,
) -> Result<BodyBinding, trust_clean_ir_gate::GateRefusal> {
    // The gate independently derives side A and reads actual decoded side-B SSA.
    let token = admit_standalone_scalar(context, name, signature, original)?;
    let final_token =
        token.authenticate_published(context, name, signature, original, published)?;
    Ok(BodyBinding {
        declaration: name.clone(),
        function_id: published.id.index(),
        kernel_payload_sha256: final_token.identity().kernel_payload_sha256().to_owned(),
        subject_digest: final_token.subject_digest().to_string(),
        carrier: final_token.carrier_tag().into(),
        method: final_token.method_tag().into(),
    })
}

/// Choose a truthful disclosure from the checked source population AFTER every
/// actual function has independently earned its gate. This classification never
/// admits a body and never reads a serialized limitations claim. Preserve exact
/// historical v1 bytes for wrapping-only and empty computational populations.
fn limitations(
    context: &AcceptedLeanSourceContext<'_>,
    computational: &[Name],
) -> Result<Vec<String>, String> {
    let mut has_projection = false;
    let mut has_literal = false;
    let mut has_mixed_literal = false;
    let mut has_expression = false;
    let mut has_decision = false;
    let mut has_scalar = false;
    let mut has_residue = false;
    for name in computational {
        let plan = match trust_clean_origin::emit::plan_standalone_clean_origin_body_for_name(
            context.environment(),
            name,
        ) {
            Ok(plan) => plan,
            // Trust (WS5.20): the standalone SCALAR vocabulary (a connective of
            // two comparisons, a `&&&`/`|||` tree, total division) — consulted
            // exactly where `assemble` and the gate consult it.
            Err(error) => {
                trust_clean_origin::emit::plan_standalone_scalar_body_for_name(
                    context.environment(),
                    name,
                )
                .map_err(|_| error.note())?;
                has_scalar = true;
                continue;
            }
        };
        has_residue |= plan.reduces_out_of_range_literal();
        match plan.shape() {
            trust_clean_origin::CleanOriginShape::WrappingBinOp { .. } => {}
            trust_clean_origin::CleanOriginShape::Projection { .. } => has_projection = true,
            trust_clean_origin::CleanOriginShape::Composed { .. } => has_expression = true,
            trust_clean_origin::CleanOriginShape::ConstantUint { .. } => {
                has_literal = true;
                has_mixed_literal |= plan
                    .signature()
                    .arguments()
                    .iter()
                    .any(|arg| arg.clean() != plan.signature().result().clean());
            }
            trust_clean_origin::CleanOriginShape::DecideComparison { .. }
            | trust_clean_origin::CleanOriginShape::Select { .. } => has_decision = true,
            _ => return Err(format!("no supported artifact disclosure for `{name}`")),
        }
    }
    let selected = if has_scalar {
        SCALAR_LIMITATIONS
    } else if has_decision {
        DECISION_LIMITATIONS
    } else if has_expression {
        EXPRESSION_LIMITATIONS
    } else if has_mixed_literal {
        MIXED_LITERAL_LIMITATIONS
    } else if has_literal {
        LITERAL_LIMITATIONS
    } else if has_projection {
        PROJECTION_LIMITATIONS
    } else {
        LIMITATIONS
    };
    let mut disclosed: Vec<String> = selected.iter().map(|s| (*s).to_owned()).collect();
    if has_residue {
        disclosed.push(LITERAL_RESIDUE_DISCLOSURE.to_owned());
    }
    Ok(disclosed)
}

fn assemble(context: &AcceptedLeanSourceContext<'_>) -> Result<LibraryEnvelope, BuildError> {
    let (computational, kernel_only) = partition(context)?;
    let mut module = module_shell(context)?;
    let mut bodies = Vec::new();
    let mut refusals = Vec::new();
    for name in &computational {
        let lower = || -> Result<(FuncTy, Function, BodyBinding), BodyRefusal> {
            let (signature, original) =
                match trust_clean_origin::emit::plan_standalone_clean_origin_body_for_name(
                    context.environment(),
                    name,
                ) {
                    Ok(plan) => (
                        trust_clean_ir::trust_ir_func_ty(plan.signature())
                            .map_err(BodyRefusal::Carrier)?,
                        trust_clean_ir::emit_standalone_clean_origin_function(
                            &plan,
                            FuncId::new(0),
                            FuncTyId::new(0),
                        )
                        .map_err(BodyRefusal::Emitter)?,
                    ),
                    // Trust (WS5.20): the standalone SCALAR vocabulary, consulted
                    // only when the shared planner declines; when both decline,
                    // the shared planner's refusal is the one reported.
                    Err(error) => {
                        let scalar =
                            trust_clean_origin::emit::plan_standalone_scalar_body_for_name(
                                context.environment(),
                                name,
                            )
                            .map_err(|_| BodyRefusal::source(error))?;
                        (
                            trust_clean_ir::trust_ir_func_ty(scalar.signature())
                                .map_err(BodyRefusal::Carrier)?,
                            trust_clean_ir::emit_standalone_scalar_function(
                                &scalar,
                                FuncId::new(0),
                                FuncTyId::new(0),
                            )
                            .map_err(BodyRefusal::Emitter)?,
                        )
                    }
                };
            let index = u32::try_from(module.functions.len()).map_err(BodyRefusal::Capacity)?;
            let mut published = original.clone();
            published.id = FuncId::new(index);
            published.ty = FuncTyId::new(index);
            published.producer = Some(Producer::Clean);
            let body = checked_binding(context, name, &signature, &original, &published)
                .map_err(BodyRefusal::Gate)?;
            Ok((signature, published, body))
        };
        match lower() {
            Ok((signature, function, body)) => {
                module.func_types.push(signature);
                module.try_add_function(function).map_err(|refusal| refusal.to_string())?;
                bodies.push(body);
            }
            Err(error) => refusals.push((name.clone(), error)),
        }
    }
    if !refusals.is_empty() {
        return Err(BuildError::Incomplete { total: computational.len(), refusals });
    }
    validate(&module)?;
    let binary = serialize_module(&module).map_err(|refusal| refusal.to_string())?;
    let envelope = LibraryEnvelope {
        schema: SCHEMA.into(),
        authority: AUTHORITY.into(),
        native_codegen: "unavailable".into(),
        source_closure_sha256: context.source_closure_sha256().into(),
        owned_declarations_sha256: context.owned_declarations_sha256().into(),
        sources: sources(context),
        owned_declarations: context.owned_declarations().iter().cloned().collect(),
        kernel_only_declarations: kernel_only,
        bodies,
        module_binary_hex: hex(&binary),
        module_sha256: sha256(&binary),
        module_stable_digest: module.stable_digest().to_string(),
        limitations: limitations(context, &computational)?,
    };
    Ok(envelope)
}

/// Decode actual binary IR and independently re-earn every gate against an
/// already rechecked immutable source context. No serialized field grants a
/// verdict, and no extra module item or missing/generated declaration is ignored.
pub(crate) fn decode_and_revalidate(
    context: &AcceptedLeanSourceContext<'_>,
    bytes: &[u8],
) -> Result<Module, String> {
    let envelope: LibraryEnvelope = serde_json::from_slice(bytes)
        .map_err(|error| format!("invalid Lean IR-library envelope: {error}"))?;
    if envelope.schema != SCHEMA
        || envelope.authority != AUTHORITY
        || envelope.native_codegen != "unavailable"
    {
        return Err("unsupported IR-library schema or authority/limitations claim".into());
    }
    if envelope.source_closure_sha256 != context.source_closure_sha256()
        || envelope.owned_declarations_sha256 != context.owned_declarations_sha256()
        || envelope.sources != sources(context)
        || envelope.owned_declarations
            != context.owned_declarations().iter().cloned().collect::<Vec<_>>()
    {
        return Err(
            "artifact source closure or owned kernel declarations differ from the checked sources"
                .into(),
        );
    }
    let (computational, kernel_only) = partition(context)?;
    if envelope.kernel_only_declarations != kernel_only
        || envelope.bodies.len() != computational.len()
    {
        return Err("artifact declaration partition is incomplete or changed".into());
    }
    let binary = unhex(&envelope.module_binary_hex)?;
    if sha256(&binary) != envelope.module_sha256 {
        return Err("module binary digest mismatch".into());
    }
    let module =
        deserialize_module(&binary).map_err(|error| format!("invalid binary Trust-IR: {error}"))?;
    // A decoded module the writer refuses to re-encode (trust-ir D1b) is no
    // canonical image either.
    let canonical = serialize_module(&module)
        .map_err(|error| format!("module binary is noncanonical: {error}"))?;
    if canonical != binary || module.stable_digest().to_string() != envelope.module_stable_digest {
        return Err("module binary is noncanonical or its stable digest changed".into());
    }
    validate(&module)?;
    if module.functions.len() != computational.len()
        || module.func_types.len() != computational.len()
    {
        return Err(
            "module computational population differs from the full checked declaration roster"
                .into(),
        );
    }
    let mut shell = module_shell(context)?;
    shell.functions = module.functions.clone();
    shell.func_types = module.func_types.clone();
    if shell != module {
        return Err("module contains changed source identity, target, runtime, proof or other out-of-scope data".into());
    }
    for (index, ((name, function), claimed)) in
        computational.iter().zip(&module.functions).zip(&envelope.bodies).enumerate()
    {
        let id = u32::try_from(index).map_err(|_| "too many computational declarations")?;
        if function.id != FuncId::new(id) || function.ty != FuncTyId::new(id) {
            return Err(format!("noncanonical function placement for `{name}`"));
        }
        let mut original = function.clone();
        original.id = FuncId::new(0);
        original.ty = FuncTyId::new(0);
        // The emitter's producer stamp is not computational or proof authority.
        // Re-earning the token below reads all other decoded Function fields.
        original.producer = None;
        let actual = binding(context, name, &module.func_types[index], &original, function)?;
        if &actual != claimed {
            return Err(format!(
                "gate binding changed for `{name}`; serialized labels are not authority"
            ));
        }
    }
    if envelope.limitations != limitations(context, &computational)? {
        return Err(
            "artifact limitations differ from the independently gated source population".into()
        );
    }
    Ok(module)
}

/// Pretty-print an observed diagnostic value for a verbose refusal block,
/// indented under its label. A value that will not serialize is disclosed as
/// the serializer's own error rather than silently dropped.
fn render_json_detail(value: &serde_json::Value) -> String {
    serde_json::to_string_pretty(value)
        .unwrap_or_else(|error| format!("<unrenderable observation: {error}>"))
        .lines()
        .map(|line| format!("    {line}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The observations behind a refused source closure that its compact rendering
/// drops. Acceptance needs every source read, every file accepted, every import
/// resolved, a finished kernel session AND a consistent source/verdict/outcome
/// roster (`CheckedLeanBatch::accepted_context`), so a closure can be refused
/// with no per-file diagnostic at all and the compact message is then only its
/// own header. These rows report what was observed; none of them claims to name
/// the clause that refused.
fn closure_detail(checked: &crate::lean_cli::CheckedLeanBatch) -> String {
    let mut lines = vec![format!("  checked source roster ({} file(s)):", checked.sources().len())];
    for source in checked.sources() {
        lines.push(match source.source() {
            Ok(text) => format!(
                "    `{}` module `{}`: read {} source byte(s)",
                source.path().display(),
                source.module(),
                text.len()
            ),
            Err(error) => format!(
                "    `{}` module `{}`: unreadable: {error}",
                source.path().display(),
                source.module()
            ),
        });
    }
    lines.push(format!("  per-file verdicts ({}):", checked.verdicts().len()));
    for verdict in checked.verdicts() {
        lines.push(format!(
            "    `{}`: {}",
            verdict.path().display(),
            if verdict.accepted() {
                "accepted with no diagnostic".to_owned()
            } else {
                format!("refused with {} diagnostic(s)", verdict.diagnostics().len())
            }
        ));
    }
    lines.push(format!("  unresolved imports ({}):", checked.unresolved_imports().len()));
    for import in checked.unresolved_imports() {
        lines.push(format!(
            "    `{}` imports `{}`: {}",
            import.source_path().display(),
            import.module(),
            import.diagnostic()
        ));
    }
    lines.join("\n")
}

fn ensure_new_output(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => Err(format!(
            "output `{}` already exists; choose a new path (nothing was overwritten)",
            path.display()
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("cannot inspect output `{}`: {error}", path.display())),
    }
}

fn build(request: &Request) -> Result<usize, BuildError> {
    ensure_new_output(&request.output)?;
    let tool_before = if let Some(path) = &request.census_output {
        crate::lean_cli::preflight_census(path)?;
        crate::lean_cli::census::distinct_outputs(path, &request.output)?;
        Some(crate::lean_cli::census::tool_identity()?)
    } else {
        None
    };
    // Accepted-source ownership/byte binding is unconditional in the core;
    // the additional attempted-roster history is diagnostic and opt-in only.
    let checked = crate::lean_cli::check_batch(
        std::slice::from_ref(&request.input),
        request.census_output.is_some(),
    );
    if let Some(path) = &request.census_output {
        let external = crate::lean_cli::census::observe_external(
            &checked,
            &request.olean_paths,
            &[path, &request.output],
        )?;
        let tool_after = crate::lean_cli::census::tool_identity()
            .unwrap_or_else(|error| serde_json::json!({"error": error}));
        let tool_before = tool_before.as_ref().expect("requested observation");
        let mut report = crate::lean_cli::census::report(
            &checked,
            std::slice::from_ref(&request.input),
            "build",
            tool_before,
            &tool_after,
        );
        if let Some(external) = external {
            report["external_olean_observation"] = external;
        }
        // This independent observation is retained even if the source closure
        // or subsequent all-owned computational assembly refuses. It says
        // nothing about a successful build or the producer's denominator.
        crate::lean_cli::write_census(path, &report)?;
        if tool_before != &tool_after {
            return Err(BuildError::detailed(
                "census tool image changed or became unreadable; report retained and no library emitted".to_owned(),
                format!(
                    "  tool image observed before the source check:\n{}\n  tool image observed after the source check:\n{}",
                    render_json_detail(tool_before),
                    render_json_detail(&tool_after),
                ),
            ));
        }
    }
    let context = checked.accepted_context().ok_or_else(|| {
        let diagnostics: Vec<_> = checked
            .verdicts()
            .iter()
            .flat_map(|verdict| {
                let prefix = format!("{}:", verdict.path().display());
                verdict.diagnostics().iter().map(move |diagnostic| {
                    if diagnostic.starts_with(&prefix) {
                        diagnostic.clone()
                    } else {
                        format!("{prefix} {diagnostic}")
                    }
                })
            })
            .collect();
        BuildError::detailed(
            format!(
                "Lean source closure was not accepted; no artifact emitted:\n{}",
                diagnostics.join("\n")
            ),
            closure_detail(&checked),
        )
    })?;
    let envelope = assemble(&context)?;
    let mut bytes = serde_json::to_vec_pretty(&envelope).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let module = decode_and_revalidate(&context, &bytes)?;
    for source in context.sources() {
        let current = std::fs::read(&source.path).map_err(|error| {
            format!("checked source `{}` can no longer be read: {error}", source.path)
        })?;
        if current != source.source.as_bytes() {
            return Err(BuildError::detailed(
                format!(
                    "checked source `{}` changed before publication; rerun the build",
                    source.path
                ),
                format!(
                    "  checked snapshot: {} byte(s), sha256 {}\n  file on disk now: {} byte(s), sha256 {}",
                    source.source.len(),
                    sha256(source.source.as_bytes()),
                    current.len(),
                    sha256(&current),
                ),
            ));
        }
    }
    let parent = request
        .output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let mut temporary = tempfile::NamedTempFile::new_in(parent).map_err(|error| {
        format!("cannot create artifact beside `{}`: {error}", request.output.display())
    })?;
    temporary.write_all(&bytes).map_err(|error| format!("cannot write artifact: {error}"))?;
    temporary.as_file().sync_all().map_err(|error| format!("cannot flush artifact: {error}"))?;
    temporary.persist_noclobber(&request.output).map_err(|error| {
        format!(
            "cannot publish new output `{}` (existing output preserved): {}",
            request.output.display(),
            error.error
        )
    })?;
    Ok(module.functions.len())
}

/// The help for `targo trust build FILE.lean`: BOTH lanes, always together.
///
/// `--entry` and `--entry-json` are real options of this command, defined by
/// `runtime`'s own parser. The library parser refuses them by name, so the usage
/// printed beside that refusal must not be one that hides the lane defining
/// them — which is why the refusal path prints this and not `USAGE` alone.
fn full_usage() -> String {
    format!("{USAGE}\n\n{}", runtime::USAGE)
}

pub(crate) fn run(args: &[String]) -> ExitCode {
    if runtime::requested(args) {
        return runtime::run(args);
    }
    if args.iter().any(|arg| matches!(arg.as_str(), "--help" | "-h")) {
        println!("{}", full_usage());
        return ExitCode::SUCCESS;
    }
    let request = match parse(args) {
        Ok(request) => request,
        Err(error) => {
            eprintln!("error: {error}\n\n{}", full_usage());
            return ExitCode::from(2);
        }
    };
    match build(&request) {
        Ok(count) => {
            println!(
                "wrote {}: {count} carrier-gated computational declaration(s) in a {SCHEMA} JSON library envelope; no executable emitted",
                request.output.display()
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("error: {}", error.render(request.verbose));
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use trust_certify::lean_source_batch::{CheckedLeanSourceBatch, LeanSourceInput};
    use trust_ir::ty::Ty;
    use trust_ir::{BinOp, Inst, InterpretValue, Interpreter};

    use super::*;

    const ADD: &str = "def add8 (a b : UInt8) : UInt8 := a + b";
    // Identity projections and literal returns are now supported. Preserve the previous
    // two-declaration refusal population with a real, still-unsupported shape,
    // rather than removing the sibling control when its old fixture turns green.
    // Composed wrapping bodies are now supported. Keep this same-population
    // negative as a real unsupported branch, rather than dropping its sibling.
    // Trust (WS5.20): the parameter select (`if a < b then a else b`) is admitted
    // now; the still-unsupported sibling is the literal-comparison select, whose
    // plan the emitter spells but no standalone reader admits (`[gate/target-shape]`).
    const UNSUPPORTED: &str = "def branch8 (a b : UInt8) : UInt8 := if a < 3 then a else b";

    // The stand-in fixtures below import `Lean`, the eligible stand-in, as
    // trust-certify's disclosure controls have since TG8-REFERENCE-ISLANDS-2
    // (6411a62394, 7d407f631b, f477b4ece7): the `Mathlib` stand-in installs a
    // structural `IsClosed` record, an ineligible reference base, so its source
    // closure is refused before the build can reach a census disclosure. That
    // refusal is pinned by
    // `library_build_refuses_every_mathlib_standin_spelling_before_assembly`.
    #[test]
    fn library_build_census_discloses_transitive_public_standin_import() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&input, format!("import Helper\n{ADD}\n")).unwrap();
        std::fs::write(&helper, "module\npublic import Lean\ndef helper8 (x : UInt8) : UInt8 := x\n")
            .unwrap();
        let mut request = Request {
            input,
            output: dir.path().join("library.json"),
            verbose: false,
            census_output: Some(dir.path().join("census.json")),
            olean_paths: Vec::new(),
        };
        let checked = crate::lean_cli::check_batch(std::slice::from_ref(&request.input), true);
        assert!(checked.accepted_context().is_some(), "the stand-in is kernel-accepted");
        let error = build(&request).unwrap_err().to_string();
        assert!(
            error.contains("The whole artifact was refused; no sibling was omitted."),
            "{error}"
        );
        assert!(!request.output.exists());
        let report: serde_json::Value = serde_json::from_slice(
            &std::fs::read(request.census_output.as_ref().unwrap()).unwrap(),
        )
        .unwrap();
        assert_eq!(report["source_graph"]["source_closure_accepted"], true);
        assert!(report["check_report"]["files"].as_array().unwrap().iter().any(|row| {
            row["path"] == helper.display().to_string()
                && row["standin_imports"] == serde_json::json!(["Lean"])
        }));

        std::fs::write(&helper, "def helper8 (x : UInt8) : UInt8 := x\n").unwrap();
        request.output = dir.path().join("local-library.json");
        request.census_output = Some(dir.path().join("local-census.json"));
        assert_eq!(build(&request).unwrap(), 2);
        assert!(request.output.exists());
    }

    #[test]
    fn library_build_census_discloses_transitive_late_standin_import() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&input, format!("import Helper\n{ADD}\n")).unwrap();
        std::fs::write(&helper, "def helper8 (x : UInt8) : UInt8 := x\nimport Lean\n").unwrap();
        let mut request = Request {
            input,
            output: dir.path().join("library.json"),
            verbose: false,
            census_output: Some(dir.path().join("census.json")),
            olean_paths: Vec::new(),
        };
        let error = build(&request).unwrap_err().to_string();
        assert!(error.contains("The whole artifact was refused; no sibling was omitted."), "{error}");
        assert!(!request.output.exists());
        let report: serde_json::Value = serde_json::from_slice(
            &std::fs::read(request.census_output.as_ref().unwrap()).unwrap(),
        )
        .unwrap();
        assert_eq!(report["source_graph"]["source_closure_accepted"], true);
        assert!(report["check_report"]["files"].as_array().unwrap().iter().any(|row| {
            row["path"] == helper.display().to_string()
                && row["standin_imports"] == serde_json::json!(["Lean"])
        }));

        std::fs::write(&helper, "def helper8 (x : UInt8) : UInt8 := x\n").unwrap();
        request.output = dir.path().join("local-library.json");
        request.census_output = Some(dir.path().join("local-census.json"));
        assert_eq!(build(&request).unwrap(), 2);
    }

    #[test]
    fn library_build_census_discloses_transitive_wrapped_imports() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&input, format!("import Helper\n{ADD}\n")).unwrap();
        let mut request = Request {
            input,
            output: dir.path().join("library.json"),
            verbose: false,
            census_output: Some(dir.path().join("census.json")),
            olean_paths: Vec::new(),
        };
        for (label, wrapper) in [
            ("set-option", "set_option maxHeartbeats 400000 in import Lean"),
            ("open", "open Nat in import Lean"),
        ] {
            std::fs::write(&helper, format!("def helper8 (x : UInt8) : UInt8 := x\n{wrapper}\n"))
                .unwrap();
            request.output = dir.path().join(format!("{label}-library.json"));
            request.census_output = Some(dir.path().join(format!("{label}-census.json")));
            let error = build(&request).unwrap_err().to_string();
            assert!(
                error.contains("The whole artifact was refused; no sibling was omitted."),
                "{label}: {error}"
            );
            assert!(!request.output.exists());
            let report: serde_json::Value = serde_json::from_slice(
                &std::fs::read(request.census_output.as_ref().unwrap()).unwrap(),
            )
            .unwrap();
            assert_eq!(report["source_graph"]["source_closure_accepted"], true);
            assert!(report["check_report"]["files"].as_array().unwrap().iter().any(|row| {
                row["path"] == helper.display().to_string()
                    && row["standin_imports"] == serde_json::json!(["Lean"])
            }));
        }

        std::fs::write(
            &helper,
            "/- set_option maxHeartbeats 400000 in import Lean -/\n\
             -- open Nat in import Lean\ndef helper8 (x : UInt8) : UInt8 := x\n",
        )
        .unwrap();
        request.output = dir.path().join("local-library.json");
        request.census_output = Some(dir.path().join("local-census.json"));
        assert_eq!(build(&request).unwrap(), 2);
        let report: serde_json::Value = serde_json::from_slice(
            &std::fs::read(request.census_output.as_ref().unwrap()).unwrap(),
        )
        .unwrap();
        assert!(
            report["check_report"]["files"]
                .as_array()
                .unwrap()
                .iter()
                .all(|row| { row["standin_imports"] == serde_json::json!([]) })
        );
    }

    /// The negative twin of the `Lean` census fixtures above
    /// (TG8-REFERENCE-ISLANDS-2): each `Mathlib` helper spelling they used to
    /// carry is still REFUSED, now because the `Mathlib` stand-in is an
    /// ineligible reference base, so the source closure is refused before
    /// assembly; no artifact is written and the retained census discloses no
    /// stand-in, because a refused row reports no green to qualify.
    #[test]
    fn library_build_refuses_every_mathlib_standin_spelling_before_assembly() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        std::fs::write(&input, format!("import Helper\n{ADD}\n")).unwrap();
        for (label, source) in [
            ("public", "module\npublic import Mathlib\ndef helper8 (x : UInt8) : UInt8 := x\n"),
            ("late", "def helper8 (x : UInt8) : UInt8 := x\nimport Mathlib\n"),
            (
                "set-option",
                "def helper8 (x : UInt8) : UInt8 := x\n\
                 set_option maxHeartbeats 400000 in import Mathlib\n",
            ),
            ("open", "def helper8 (x : UInt8) : UInt8 := x\nopen Nat in import Mathlib\n"),
        ] {
            std::fs::write(&helper, source).unwrap();
            let request = Request {
                input: input.clone(),
                output: dir.path().join(format!("{label}-library.json")),
                verbose: false,
                census_output: Some(dir.path().join(format!("{label}-census.json"))),
                olean_paths: Vec::new(),
            };
            let checked = crate::lean_cli::check_batch(std::slice::from_ref(&request.input), true);
            assert!(checked.accepted_context().is_none(), "{label}: the Mathlib base was accepted");
            let error = build(&request).unwrap_err().to_string();
            assert!(
                error.contains("Lean source closure was not accepted; no artifact emitted"),
                "{label}: {error}"
            );
            assert!(
                error.contains("reference base refused") && error.contains("StructuralProvenance"),
                "{label}: {error}"
            );
            assert!(!request.output.exists(), "{label}");
            let report: serde_json::Value = serde_json::from_slice(
                &std::fs::read(request.census_output.as_ref().unwrap()).unwrap(),
            )
            .unwrap();
            assert_eq!(report["source_graph"]["source_closure_accepted"], false, "{label}");
            assert!(
                report["check_report"]["files"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|row| row["standin_imports"] == serde_json::json!([])),
                "{label}: {report}"
            );
        }
    }

    #[test]
    fn olean_census_build_paths_require_census_and_keep_order() {
        let base = ["Main.lean", "--emit=trust-ir", "--out=new.json"];
        let args =
            |extra: &[&str]| base.iter().chain(extra).map(|s| s.to_string()).collect::<Vec<_>>();
        assert!(parse(&args(&["--census-olean-path", "one"])).is_err());
        let request = parse(&args(&[
            "--census=new-census.json",
            "--census-olean-path",
            "one",
            "--census-olean-path=two",
        ]))
        .unwrap();
        assert_eq!(request.olean_paths, vec![PathBuf::from("one"), PathBuf::from("two")]);
        assert!(USAGE.contains("does NOT enable external imports"));
    }

    #[test]
    fn olean_census_build_keeps_success_bytes_and_external_refusal() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        std::fs::write(&input, ADD).unwrap();
        let mut request = Request {
            input: input.clone(),
            output: dir.path().join("plain.json"),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        assert_eq!(build(&request).unwrap(), 1);
        let bytes = std::fs::read(&request.output).unwrap();
        request.output = dir.path().join("measured.json");
        request.census_output = Some(dir.path().join("census.json"));
        request.olean_paths.push(dir.path().into());
        assert_eq!(build(&request).unwrap(), 1);
        assert_eq!(std::fs::read(&request.output).unwrap(), bytes);
        std::fs::write(&input, "import Missing\ndef ordinary : UInt8 := 1").unwrap();
        request.output = dir.path().join("refused.json");
        request.census_output = Some(dir.path().join("refused-census.json"));
        assert!(build(&request).is_err());
        assert!(!request.output.exists());
        let report: serde_json::Value = serde_json::from_slice(
            &std::fs::read(request.census_output.as_ref().unwrap()).unwrap(),
        )
        .unwrap();
        assert_eq!(report["external_olean_observation"]["modules"][0]["status"], "missing");
        assert_eq!(report["source_graph"]["source_closure_accepted"], false);
        request.output = dir.path().join("Missing.olean");
        request.census_output = Some(dir.path().join("alias-census.json"));
        let error = build(&request).unwrap_err().to_string();
        assert!(error.contains("aliases an observed"), "{error}");
        assert!(!request.output.exists() && !request.census_output.as_ref().unwrap().exists());
    }

    #[test]
    fn olean_census_build_protects_quoted_ir_companion_from_both_outputs() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        std::fs::write(&input, "import «Quoted.Mod»\ndef ordinary : UInt8 := 1").unwrap();
        let ir = dir.path().join("Quoted.Mod.ir");
        let mut request = Request {
            input,
            output: ir.clone(),
            verbose: false,
            census_output: Some(dir.path().join("census.json")),
            olean_paths: vec![dir.path().into()],
        };
        let error = build(&request).unwrap_err().to_string();
        assert!(error.contains("aliases an observed"), "{error}");
        assert!(!ir.exists() && !request.census_output.as_ref().unwrap().exists());
        request.output = dir.path().join("library.json");
        request.census_output = Some(ir.clone());
        let error = build(&request).unwrap_err().to_string();
        assert!(error.contains("aliases an observed"), "{error}");
        assert!(!ir.exists() && !request.output.exists());
    }

    #[test]
    fn build_census_precedes_production_and_retains_refused_siblings() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        let helper = dir.path().join("Helper.lean");
        let census = dir.path().join("census.json");
        std::fs::write(&input, format!("import Helper\n{ADD}\n")).unwrap();
        std::fs::write(&helper, format!("{UNSUPPORTED}\ntheorem proof : True := True.intro\n"))
            .unwrap();
        let request = Request {
            input,
            output: dir.path().join("library.json"),
            verbose: false,
            census_output: Some(census.clone()),
            olean_paths: Vec::new(),
        };
        let error = build(&request).unwrap_err().to_string();
        assert!(error.contains("1 of 2 computational"), "{error}");
        assert!(error.contains("no sibling was omitted"));
        assert!(!request.output.exists());
        let observed: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&census).unwrap()).unwrap();
        assert_eq!(observed["source_graph"]["operation"], "build");
        assert_eq!(observed["source_graph"]["source_closure_accepted"], true);
        assert_eq!(observed["source_graph"]["tool_path_bytes_stable"], true);
        assert_eq!(observed["source_graph"]["sources"].as_array().unwrap().len(), 2);
        let rows = observed["kernel_roster"]["declarations"].as_array().unwrap();
        for name in ["add8", "branch8", "proof"] {
            assert!(rows.iter().any(|row| row["name"] == name), "missing {name}");
        }
        assert!(rows.iter().all(|row| row["runtime_classification"] == "unmeasured"));
        assert_eq!(observed["kernel_roster"]["denominator_status"], "denominator_unverified");
    }

    #[test]
    fn build_census_success_bytes_match_no_census_and_failed_source_stays_measured() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Main.lean");
        std::fs::write(&input, ADD).unwrap();
        let mut plain = Request {
            input: input.clone(),
            output: dir.path().join("plain.json"),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        assert_eq!(build(&plain).unwrap(), 1);
        let bytes = std::fs::read(&plain.output).unwrap();
        plain.output = dir.path().join("measured.json");
        plain.census_output = Some(dir.path().join("good-census.json"));
        assert_eq!(build(&plain).unwrap(), 1);
        assert_eq!(std::fs::read(&plain.output).unwrap(), bytes);
        std::fs::write(input, "import MissingLocalModule\ndef value : Nat := 1").unwrap();
        plain.output = dir.path().join("refused.json");
        plain.census_output = Some(dir.path().join("bad-census.json"));
        assert!(build(&plain).is_err());
        assert!(!plain.output.exists());
        let observed: serde_json::Value =
            serde_json::from_slice(&std::fs::read(plain.census_output.unwrap()).unwrap()).unwrap();
        assert_eq!(observed["source_graph"]["source_closure_accepted"], false);
        assert_eq!(
            observed["source_graph"]["unresolved_imports"][0]["module"],
            "MissingLocalModule"
        );
        assert_eq!(observed["kernel_roster"]["check_rejected"], true);
    }

    #[test]
    fn build_census_preserves_existing_outputs_and_refuses_alias_before_check() {
        let dir = tempfile::tempdir().unwrap();
        let output = dir.path().join("output.json");
        let census = dir.path().join("census.json");
        let mut request = Request {
            input: dir.path().join("Missing.lean"),
            output: output.clone(),
            verbose: false,
            census_output: Some(census.clone()),
            olean_paths: Vec::new(),
        };
        std::fs::write(&census, "previous census").unwrap();
        assert!(build(&request).unwrap_err().to_string().contains("already exists"));
        assert_eq!(std::fs::read_to_string(&census).unwrap(), "previous census");
        assert!(!output.exists());
        request.census_output = Some(dir.path().join("./output.json"));
        assert!(build(&request).unwrap_err().to_string().contains("distinct new files"));
        assert!(!output.exists());
        std::fs::write(&output, "previous library").unwrap();
        request.census_output = Some(dir.path().join("new-census.json"));
        assert!(build(&request).is_err());
        assert_eq!(std::fs::read_to_string(output).unwrap(), "previous library");
        assert!(!request.census_output.unwrap().exists());
    }

    #[test]
    fn build_census_option_is_explicit_and_help_discloses_its_boundary() {
        let args = |extra: &[&str]| {
            ["Main.lean", "--emit=trust-ir", "--out=out.json"]
                .into_iter()
                .chain(extra.iter().copied())
                .map(str::to_string)
                .collect::<Vec<_>>()
        };
        assert_eq!(
            parse(&args(&["--census", "census.json"])).unwrap().census_output,
            Some("census.json".into())
        );
        assert_eq!(
            parse(&args(&["--census=census.json"])).unwrap().census_output,
            Some("census.json".into())
        );
        for extra in [
            &["--census"][..],
            &["--census="],
            &["--census", "--verbose"],
            &["--census=a", "--census=b"],
        ] {
            assert!(parse(&args(extra)).is_err());
        }
        assert!(USAGE.contains("--census NEW_PATH"));
        assert!(USAGE.contains("before lowering"));
        assert!(USAGE.contains("not runtime or completion authority"));
    }

    fn checked(source: &str) -> CheckedLeanSourceBatch {
        CheckedLeanSourceBatch::check(
            vec![LeanSourceInput {
                module: "Demo".into(),
                path: "/checked/Demo.lean".into(),
                source: source.into(),
            }],
            true,
        )
    }

    fn encode(envelope: &LibraryEnvelope) -> Vec<u8> {
        serde_json::to_vec(envelope).unwrap()
    }

    fn rewrite_binary(envelope: &mut LibraryEnvelope, module: &Module) {
        let binary = serialize_module(module).expect("serialize_module: test fixture");
        envelope.module_binary_hex = hex(&binary);
        envelope.module_sha256 = sha256(&binary);
        envelope.module_stable_digest = module.stable_digest().to_string();
    }

    // Exercise the allocator's real refusal without constructing 2^32 resident
    // source strings. No production allocation limit or injected result is added.
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn source_file_capacity_refusal_keeps_path_and_allocator_reason() {
        assert_eq!(
            trust_ir::value::table_index(u32::MAX as usize, "files"),
            Ok(u32::MAX)
        );
        let exhausted = trust_ir::value::table_index(u32::MAX as usize + 1, "files")
            .expect_err("the first index without a u32 identity must refuse");
        let path = "/checked/source with spaces.lean";
        let message = file_table_refusal(path, exhausted);
        assert_eq!(
            message,
            format!("cannot record checked Lean source `{path}` in the Trust-IR file table: {exhausted}")
        );
        assert!(message.contains("the files id space is exhausted"));
        let refusal = BuildError::from(message.clone());
        assert_eq!(refusal.render(false), message);
        assert_eq!(refusal.render(true), message);
    }

    #[test]
    fn source_file_population_is_preserved_and_changed_file_tables_refuse_import() {
        let batch = CheckedLeanSourceBatch::check(
            vec![
                LeanSourceInput {
                    module: "Helper".into(),
                    path: "/checked/Helper with spaces.lean".into(),
                    source: "def helper8 (a : UInt8) : UInt8 := a".into(),
                },
                LeanSourceInput {
                    module: "Demo".into(),
                    path: "/checked/Demo.lean".into(),
                    source: ADD.into(),
                },
            ],
            true,
        );
        let context = batch.accepted_context().expect("both checked sources accepted");
        let shell = module_shell(&context).expect("small complete file population fits");
        assert_eq!(shell.files, ["/checked/Helper with spaces.lean", "/checked/Demo.lean"]);
        let envelope = assemble(&context).expect("both computational declarations admitted");
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.files, shell.files);
        assert_eq!(module.functions.len(), 2);
        let changed_tables = [
            vec![module.files[0].clone()],
            vec![module.files[1].clone(), module.files[0].clone()],
            vec![module.files[0].clone(), "/unaccepted/Other.lean".into()],
        ];
        for files in changed_tables {
            let mut changed_module = module.clone();
            changed_module.files = files;
            let mut changed = envelope.clone();
            rewrite_binary(&mut changed, &changed_module);
            assert!(
                decode_and_revalidate(&context, &encode(&changed)).is_err(),
                "changed file identity cannot be authorized by recomputing module digests"
            );
        }
    }

    #[test]
    fn add8_is_real_valid_roundtripped_ir_and_wraps_255_plus_1() {
        let batch = checked(ADD);
        let context = batch.accepted_context().expect("source accepted");
        let envelope = assemble(&context).expect("gate admits add8");
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].producer, Some(Producer::Clean));
        assert!(module.proof_certificates.is_empty());
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert_eq!(
            deserialize_module(&serialize_module(&module).expect("serialize_module: test fixture"))
                .unwrap(),
            module
        );
        let result = Interpreter::new()
            .execute_function(
                &module.functions[0],
                vec![
                    InterpretValue::int(Ty::U8, 255).unwrap(),
                    InterpretValue::int(Ty::U8, 1).unwrap(),
                ],
            )
            .unwrap();
        assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), 0);
    }

    #[test]
    fn quoted_dot_and_namespace_names_keep_distinct_library_bodies() {
        let batch = checked(
            "namespace A\n\
             def b (left right : UInt8) : UInt8 := left\n\
             end A\n\
             def «A.b» (left right : UInt8) : UInt8 := right\n",
        );
        let context = batch.accepted_context().expect("distinct Lean names must both check");
        let qualified = Name::anon().str("A").str("b");
        let quoted = Name::anon().str("A.b");
        assert_ne!(qualified, quoted);
        let envelope = assemble(&context).expect("both UInt projections earn their gates");
        assert_eq!(envelope.owned_declarations.len(), 2);
        assert_eq!(envelope.bodies.len(), 2);
        assert!(envelope.kernel_only_declarations.is_empty());
        assert_ne!(envelope.bodies[0].function_id, envelope.bodies[1].function_id);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 2);
        assert_ne!(module.functions[0].name, module.functions[1].name);
        assert!(trust_ir_build::validate_module(&module).is_empty());
        for (name, expected) in [(qualified.clone(), 17), (quoted.clone(), 231)] {
            assert!(envelope.owned_declarations.contains(&name));
            let body = envelope.bodies.iter().find(|body| body.declaration == name).unwrap();
            let function = module
                .functions
                .iter()
                .find(|function| function.id.index() == body.function_id)
                .unwrap();
            let result = Interpreter::new()
                .execute_function(
                    function,
                    vec![
                        InterpretValue::int(Ty::U8, 17).unwrap(),
                        InterpretValue::int(Ty::U8, 231).unwrap(),
                    ],
                )
                .unwrap();
            assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), expected);
        }
        // Neither a retained token nor a freshly minted binding may give this
        // function the other structural declaration's identity or symbol.
        let plan = trust_clean_origin::emit::plan_standalone_clean_origin_body_for_name(
            context.environment(),
            &qualified,
        )
        .unwrap();
        let signature = trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap();
        let function = trust_clean_ir::emit_standalone_clean_origin_function(
            &plan,
            FuncId::new(0),
            FuncTyId::new(0),
        )
        .unwrap();
        let token = trust_clean_ir_gate::standalone::admit_standalone_scalar(
            &context, &qualified, &signature, &function,
        )
        .unwrap();
        assert!(token.authenticate(&context, &quoted, &signature, &function).is_err());
        let refusal = trust_clean_ir_gate::standalone::admit_standalone_scalar(
            &context, &quoted, &signature, &function,
        )
        .expect_err("a fresh binding must reject the other declaration's symbol");
        assert_eq!(refusal.stage(), "subject-name");
        let mut aliased = envelope.clone();
        aliased.bodies[0].declaration = aliased.bodies[1].declaration.clone();
        assert!(decode_and_revalidate(&context, &encode(&aliased)).is_err());
    }

    #[test]
    fn structured_names_preserve_literal_wrapping_and_expression_bodies() {
        let mut source = String::new();
        for (namespace, left, right) in
            [("L", "5", "9"), ("W", "a + b", "a - b"), ("E", "a + b + a", "a - b - b")]
        {
            source.push_str(&format!(
                "namespace {namespace}\ndef f (a b : UInt8) : UInt8 := {left}\nend {namespace}\n\
                 def «{namespace}.f» (a b : UInt8) : UInt8 := {right}\n"
            ));
        }
        let batch = checked(&source);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.owned_declarations.len(), 6);
        assert_eq!(envelope.bodies.len(), 6);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        for (namespace, first, second) in [("L", 5, 9), ("W", 18, 8), ("E", 31, 3)] {
            for (name, expected) in [
                (Name::anon().str(namespace).str("f"), first),
                (Name::anon().str(format!("{namespace}.f")), second),
            ] {
                let binding = envelope.bodies.iter().find(|b| b.declaration == name).unwrap();
                let function =
                    module.functions.iter().find(|f| f.id.index() == binding.function_id).unwrap();
                let result = Interpreter::new()
                    .execute_function(
                        function,
                        vec![
                            InterpretValue::int(Ty::U8, 13).unwrap(),
                            InterpretValue::int(Ty::U8, 5).unwrap(),
                        ],
                    )
                    .unwrap();
                assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), expected);
            }
        }
    }

    #[test]
    fn ordinary_uint_projections_roundtrip_and_return_the_exact_parameter() {
        let mut source = String::new();
        for width in [8, 16, 32, 64] {
            source.push_str(&format!(
                "def keep{width} (a : UInt{width}) : UInt{width} := a\n\
                 def first{width} (a b : UInt{width}) : UInt{width} := a\n\
                 def second{width} (a b : UInt{width}) : UInt{width} := b\n"
            ));
        }
        let batch = checked(&source);
        let context = batch.accepted_context().expect("all twelve source declarations check");
        let envelope = assemble(&context).expect("every ordinary UInt projection earns its gate");
        assert_eq!(envelope.owned_declarations.len(), 12);
        assert_eq!(envelope.bodies.len(), 12);
        assert!(envelope.kernel_only_declarations.is_empty());
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 12);
        assert!(module.proof_certificates.is_empty());
        for (width, ty) in [(8, Ty::U8), (16, Ty::U16), (32, Ty::U32), (64, Ty::U64)] {
            let maximum = (1_i128 << width) - 1;
            for (prefix, inputs, expected) in [
                ("keep", vec![maximum], maximum),
                ("first", vec![maximum, 1], maximum),
                ("second", vec![maximum, 1], 1),
            ] {
                let name = format!("{prefix}{width}");
                let function = module.functions.iter().find(|f| f.name == name).unwrap();
                let result = Interpreter::new()
                    .execute_function(
                        function,
                        inputs
                            .into_iter()
                            .map(|value| InterpretValue::int(ty.clone(), value).unwrap())
                            .collect::<Vec<_>>(),
                    )
                    .unwrap();
                assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), expected as u128);
            }
        }
    }

    #[test]
    fn mixed_uint_projection_preserves_each_parameter_carrier() {
        let batch = checked(
            "def chooseWide (a : UInt8) (b : UInt64) : UInt64 := b\n\
             def chooseNarrow (a : UInt8) (b : UInt64) : UInt8 := a",
        );
        let context = batch.accepted_context().expect("mixed UInt sources check");
        let envelope = assemble(&context).expect("selected parameter has the exact return carrier");
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 2);
        for function in &module.functions {
            let signature = &module.func_types[function.ty.index() as usize];
            assert_eq!(signature.params, vec![Ty::U8, Ty::U64]);
            let wide = function.name == "chooseWide";
            assert_eq!(signature.returns, vec![if wide { Ty::U64 } else { Ty::U8 }]);
            let result = Interpreter::new()
                .execute_function(
                    function,
                    vec![
                        InterpretValue::int(Ty::U8, 255).unwrap(),
                        InterpretValue::int(Ty::U64, i128::from(u64::MAX)).unwrap(),
                    ],
                )
                .unwrap();
            let expected = if wide { u128::from(u64::MAX) } else { 255 };
            assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), expected);
        }
    }

    #[test]
    fn composed_wrapping_library_roundtrips_all_carriers_and_retains_existing_shapes() {
        let mut source =
            format!("{ADD}\ndef keep8 (a : UInt8) : UInt8 := a\ndef literal8 : UInt8 := 7\n");
        for width in [8, 16, 32, 64] {
            source.push_str(&format!(
                "def composed{width} (a b : UInt{width}) : UInt{width} := ((a + b) - a) * (b + 3)\n"
            ));
        }
        let batch = checked(&source);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.owned_declarations.len(), 7);
        assert_eq!(envelope.bodies.len(), 7);
        assert!(envelope.kernel_only_declarations.is_empty());
        assert_eq!(envelope.limitations, EXPRESSION_LIMITATIONS);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 7);
        for (width, ty) in [(8, Ty::U8), (16, Ty::U16), (32, Ty::U32), (64, Ty::U64)] {
            let function =
                module.functions.iter().find(|f| f.name == format!("composed{width}")).unwrap();
            let result = Interpreter::new()
                .execute_function(
                    function,
                    vec![
                        InterpretValue::int(ty.clone(), (1_i128 << width) - 1).unwrap(),
                        InterpretValue::int(ty, 2).unwrap(),
                    ],
                )
                .unwrap();
            assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), 10);
        }
    }

    /// Trust (WS5.20): `STANDALONE.p01_bool_result` / `p02_if_select` and
    /// `a.lean.standalone.{bool_cmp,select}` — the decision family builds a
    /// library whose every gate re-earns on `decode_and_revalidate`, and the
    /// decoded bodies compute the Lean values.
    #[test]
    fn decision_library_reearns_on_import_and_computes_the_lean_values() {
        let batch = checked(
            "def isLt (a b : UInt64) : Bool := a < b\n\
             def min2 (a b : UInt64) : UInt64 := if a < b then a else b\n\
             def keep8 (a : UInt8) : UInt8 := a\n",
        );
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.bodies.len(), 3);
        assert_eq!(envelope.limitations, DECISION_LIMITATIONS);
        assert!(envelope.bodies.iter().any(|body| body.carrier == "Bool"));
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let run = |name: &str, a: u64, b: u64| {
            let function = module.functions.iter().find(|f| f.name == name).unwrap();
            Interpreter::new()
                .execute_function(
                    function,
                    vec![
                        InterpretValue::int(Ty::U64, i128::from(a)).unwrap(),
                        InterpretValue::int(Ty::U64, i128::from(b)).unwrap(),
                    ],
                )
                .unwrap()
                .returns
        };
        assert_eq!(run("isLt", 3, 9)[0].as_bool(), Some(true));
        assert_eq!(run("isLt", 9, 3)[0].as_bool(), Some(false));
        assert_eq!(run("min2", 9, 3)[0].as_int().unwrap().as_unsigned(), 3);
        assert_eq!(run("min2", u64::MAX, 7)[0].as_int().unwrap().as_unsigned(), 7);
        // The disclosure is recomputed, never read from the wire.
        for previous in [EXPRESSION_LIMITATIONS, PROJECTION_LIMITATIONS, LIMITATIONS] {
            let mut changed = envelope.clone();
            changed.limitations = previous.iter().map(|s| (*s).to_owned()).collect();
            assert!(
                decode_and_revalidate(&context, &encode(&changed))
                    .unwrap_err()
                    .contains("limitations differ")
            );
        }
    }

    /// Trust (WS5.20): `STANDALONE.p13_division`, `p15_bitwise` and
    /// `p20_bool_connective` — the standalone SCALAR vocabulary builds a library
    /// whose gates re-earn on import; the decoded bodies compute Lean's values,
    /// including Lean's `x / 0 = 0`; the disclosure names the vocabulary.
    #[test]
    fn scalar_library_reearns_on_import_and_computes_the_lean_values() {
        let batch = checked(
            "def both (a b c : UInt64) : Bool := a < b && b < c\n\
             def mask (a b : UInt64) : UInt64 := (a &&& b) ||| 1\n\
             def quot (a b : UInt64) : UInt64 := a / b\n",
        );
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.bodies.len(), 3);
        assert_eq!(envelope.limitations, SCALAR_LIMITATIONS);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let run = |name: &str, args: &[u64]| {
            let function = module.functions.iter().find(|f| f.name == name).unwrap();
            Interpreter::new()
                .execute_function(
                    function,
                    args.iter()
                        .map(|a| InterpretValue::int(Ty::U64, i128::from(*a)).unwrap())
                        .collect::<Vec<_>>(),
                )
                .unwrap()
                .returns
        };
        assert_eq!(run("both", &[3, 4, 5])[0].as_bool(), Some(true));
        assert_eq!(run("both", &[u64::MAX, 0, 1])[0].as_bool(), Some(false));
        assert_eq!(run("mask", &[12, 10])[0].as_int().unwrap().as_unsigned(), 9);
        assert_eq!(run("quot", &[7, 2])[0].as_int().unwrap().as_unsigned(), 3);
        assert_eq!(run("quot", &[7, 0])[0].as_int().unwrap().as_unsigned(), 0);
        let mut changed = envelope.clone();
        changed.limitations = DECISION_LIMITATIONS.iter().map(|s| (*s).to_owned()).collect();
        assert!(
            decode_and_revalidate(&context, &encode(&changed))
                .unwrap_err()
                .contains("limitations differ")
        );
    }

    /// Trust (WS5.20) MUTATION: a stored division whose zero guard was dropped
    /// (`q = udiv x y; ret q`) still validates structurally — UB at a zero
    /// divisor is not a validator error — and is refused on import by the
    /// division reader.
    #[test]
    fn a_division_import_without_its_zero_guard_is_refused() {
        let batch = checked("def quot (a b : UInt64) : UInt64 := a / b");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let mut changed = envelope.clone();
        let mut changed_module = module.clone();
        {
            let function = &mut changed_module.functions[0];
            let x = function.blocks[0].params[0].0;
            let y = function.blocks[0].params[1].0;
            let q = trust_ir::value::ValueId::new(2);
            function.blocks[0].body = vec![
                trust_ir::node::InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::UDiv,
                    ty: Ty::U64,
                    lhs: x,
                    rhs: y,
                })
                .with_results(vec![q]),
                trust_ir::node::InstrNode::new(Inst::Return { values: vec![q] }),
            ];
        }
        validate(&changed_module).expect("an unguarded UDiv still validates structurally");
        rewrite_binary(&mut changed, &changed_module);
        let published = &changed_module.functions[0];
        let mut original = published.clone();
        original.producer = None;
        let refused = binding(
            &context,
            &envelope.bodies[0].declaration,
            &changed_module.func_types[0],
            &original,
            published,
        )
        .unwrap_err();
        assert!(refused.contains("division-body"), "{refused}");
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
    }

    /// Trust (WS5.20) MUTATION: the stored select with its arms swapped still
    /// validates structurally, and is refused on import because its fresh
    /// kernel re-earn disagrees with the source.
    #[test]
    fn a_decision_import_with_swapped_select_arms_is_refused_by_the_kernel() {
        let batch = checked("def min2 (a b : UInt64) : UInt64 := if a < b then a else b");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let mut changed = envelope.clone();
        let mut changed_module = module.clone();
        for node in &mut changed_module.functions[0].blocks[0].body {
            if let Inst::Select { then_val, else_val, .. } = &mut node.inst {
                std::mem::swap(then_val, else_val);
            }
        }
        validate(&changed_module).expect("the swapped select still validates structurally");
        rewrite_binary(&mut changed, &changed_module);
        let published = &changed_module.functions[0];
        let mut original = published.clone();
        original.producer = None;
        let refused = binding(
            &context,
            &envelope.bodies[0].declaration,
            &changed_module.func_types[0],
            &original,
            published,
        )
        .unwrap_err();
        assert!(refused.contains("kernel-disagreement"), "{refused}");
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
    }

    #[test]
    fn expression_import_rejects_recomputed_digests_and_fresh_wrong_body_bindings() {
        let batch = checked("def composed8 (a b c : UInt8) : UInt8 := (a - b) * c");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        for mutation in 0..4 {
            let mut changed = envelope.clone();
            let mut changed_module = module.clone();
            if mutation >= 2 {
                let mut dead = changed_module.functions[0].blocks[0].body[0].clone();
                dead.results[0] = trust_ir::value::ValueId::new(90);
                if mutation == 3 {
                    dead.inst = Inst::Fence { ordering: trust_ir::inst::Ordering::SeqCst };
                    dead.results.clear();
                }
                changed_module.functions[0].blocks[0].body.insert(0, dead);
            } else {
                let Inst::BinOp { op, lhs, rhs, .. } =
                    &mut changed_module.functions[0].blocks[0].body[0].inst
                else {
                    panic!()
                };
                if mutation == 0 {
                    std::mem::swap(lhs, rhs);
                } else {
                    *op = trust_ir::BinOp::Add;
                }
            }
            validate(&changed_module).expect("mutated body still validates structurally");
            rewrite_binary(&mut changed, &changed_module);
            let published = &changed_module.functions[0];
            let mut original = published.clone();
            original.producer = None;
            let refused = binding(
                &context,
                &envelope.bodies[0].declaration,
                &changed_module.func_types[0],
                &original,
                published,
            )
            .unwrap_err();
            assert!(
                refused.contains(match mutation {
                    2 => "expression-tree",
                    3 => "instruction",
                    _ => "kernel-disagreement",
                }),
                "{refused}"
            );
            assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        }
    }

    #[test]
    fn expression_disclosure_cannot_be_replaced_by_old_wire_claims() {
        let batch = checked("def composed8 (a b : UInt8) : UInt8 := (a + b) + a");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.limitations, EXPRESSION_LIMITATIONS);
        for previous in
            [LIMITATIONS, PROJECTION_LIMITATIONS, LITERAL_LIMITATIONS, MIXED_LITERAL_LIMITATIONS]
        {
            let mut changed = envelope.clone();
            changed.limitations = previous.iter().map(|s| (*s).to_owned()).collect();
            assert!(
                decode_and_revalidate(&context, &encode(&changed))
                    .unwrap_err()
                    .contains("limitations differ")
            );
        }
    }

    #[test]
    fn transparent_local_calls_keep_both_bodies_and_reearn_their_gates() {
        let batch = checked(
            "def helper8 (a b : UInt8) : UInt8 := a + b\ndef call8 (a b : UInt8) : UInt8 := helper8 a b",
        );
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).expect("checked transparent helper calls are supported");
        assert_eq!(envelope.owned_declarations.len(), 2);
        assert_eq!(envelope.bodies.len(), 2);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 2);
        for body in &envelope.bodies {
            let function = module
                .functions
                .iter()
                .find(|function| function.id.index() == body.function_id)
                .unwrap();
            for (a, b) in [(0, 0), (17, 231), (255, 1), (255, 255)] {
                let result = Interpreter::new()
                    .execute_function(
                        function,
                        vec![
                            InterpretValue::int(Ty::U8, a).unwrap(),
                            InterpretValue::int(Ty::U8, b).unwrap(),
                        ],
                    )
                    .unwrap();
                assert_eq!(
                    result.returns[0].as_int().unwrap().as_unsigned(),
                    u128::try_from((a + b) & 255).unwrap()
                );
            }
        }
    }

    #[test]
    fn opaque_local_call_sibling_is_not_silently_inlined_or_omitted() {
        let batch = checked(
            "opaque helper8 (a b : UInt8) : UInt8 := a + b\ndef call8 (a b : UInt8) : UInt8 := helper8 a b",
        );
        let context = batch.accepted_context().unwrap();
        assert_eq!(partition(&context).unwrap().0.len(), 2);
        let refused = assemble(&context).unwrap_err().to_string();
        assert!(
            refused.contains("call8") && refused.contains("no sibling was omitted"),
            "{refused}"
        );
    }

    #[test]
    fn uint_literal_boundaries_roundtrip_and_execute_with_every_decl_retained() {
        let mut source = String::new();
        for width in [8, 16, 32, 64] {
            for (tag, value) in [("zero", 0_u128), ("max", (1_u128 << width) - 1)] {
                source.push_str(&format!(
                    "def {tag}{width} : UInt{width} := {value}\n\
                     def unused{tag}{width} (a b c : UInt{width}) : UInt{width} := {value}\n"
                ));
            }
        }
        let batch = checked(&source);
        let context = batch.accepted_context().expect("all sixteen source bodies check");
        let envelope = assemble(&context).expect("all boundary literals earn actual-SSA gates");
        assert_eq!(envelope.owned_declarations.len(), 16);
        assert_eq!(envelope.bodies.len(), 16);
        assert!(envelope.kernel_only_declarations.is_empty());
        assert_eq!(envelope.limitations, LITERAL_LIMITATIONS);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.functions.len(), 16);
        assert!(module.proof_certificates.is_empty());
        for (width, ty) in [(8, Ty::U8), (16, Ty::U16), (32, Ty::U32), (64, Ty::U64)] {
            let maximum = (1_i128 << width) - 1;
            for (tag, expected) in [("zero", 0), ("max", maximum)] {
                for prefix in ["", "unused"] {
                    let name = format!("{prefix}{tag}{width}");
                    let function = module.functions.iter().find(|f| f.name == name).unwrap();
                    let inputs = if prefix.is_empty() { vec![] } else { vec![maximum, 1, 0] };
                    let result = Interpreter::new()
                        .execute_function(
                            function,
                            inputs
                                .into_iter()
                                .map(|value| InterpretValue::int(ty.clone(), value).unwrap())
                                .collect::<Vec<_>>(),
                        )
                        .unwrap();
                    assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), expected as u128);
                }
            }
        }
    }

    #[test]
    fn literals_compose_a_full_library_population_with_wrapping_and_projection() {
        let batch =
            checked(&format!("{ADD}\ndef keep (n : UInt8) : UInt8 := n\ndef zero8 : UInt8 := 0"));
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.bodies.len(), 3);
        assert_eq!(envelope.owned_declarations.len(), 3);
        assert_eq!(envelope.limitations, LITERAL_LIMITATIONS);
        assert_eq!(decode_and_revalidate(&context, &encode(&envelope)).unwrap().functions.len(), 3);
    }

    #[test]
    fn mixed_unused_uint_literal_parameters_roundtrip_with_exact_telescope_and_values() {
        let mut source = String::new();
        for width in [8, 16, 32, 64] {
            let maximum = (1_u128 << width) - 1;
            source.push_str(&format!(
                "def mixed{width} (a : UInt8) (b : UInt16) (c : UInt32) (d : UInt64) : UInt{width} := {maximum}\n\
                 def nullary{width} : UInt{width} := 0\n"
            ));
        }
        let batch = checked(&source);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.owned_declarations.len(), 8);
        assert_eq!(envelope.bodies.len(), 8);
        assert_eq!(envelope.limitations, MIXED_LITERAL_LIMITATIONS);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        for width in [8, 16, 32, 64] {
            for prefix in ["mixed", "nullary"] {
                let function =
                    module.functions.iter().find(|f| f.name == format!("{prefix}{width}")).unwrap();
                let signature = &module.func_types[function.ty.index() as usize];
                let mixed = prefix == "mixed";
                assert_eq!(
                    signature.params,
                    if mixed { vec![Ty::U8, Ty::U16, Ty::U32, Ty::U64] } else { vec![] }
                );
                let inputs = if mixed {
                    [
                        (Ty::U8, 255),
                        (Ty::U16, 65535),
                        (Ty::U32, 4_294_967_295),
                        (Ty::U64, i128::from(u64::MAX)),
                    ]
                    .into_iter()
                    .map(|(ty, value)| InterpretValue::int(ty, value).unwrap())
                    .collect::<Vec<_>>()
                } else {
                    vec![]
                };
                let result = Interpreter::new().execute_function(function, inputs).unwrap();
                assert_eq!(
                    result.returns[0].as_int().unwrap().as_unsigned(),
                    if mixed { (1_u128 << width) - 1 } else { 0 }
                );
            }
        }
    }

    #[test]
    fn mixed_literal_disclosure_is_recomputed_without_changing_old_literal_envelopes() {
        let uniform = checked("def literal8 (a b : UInt8) : UInt8 := 7");
        let uniform_context = uniform.accepted_context().unwrap();
        let envelope = assemble(&uniform_context).unwrap();
        assert_eq!(envelope.limitations, LITERAL_LIMITATIONS);
        decode_and_revalidate(&uniform_context, &encode(&envelope)).unwrap();
        let mixed = checked("def literal8 (a : UInt16) (b : UInt8) : UInt8 := 7");
        let context = mixed.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.limitations, MIXED_LITERAL_LIMITATIONS);
        for old in [LIMITATIONS, PROJECTION_LIMITATIONS, LITERAL_LIMITATIONS] {
            let mut changed = envelope.clone();
            changed.limitations = old.iter().map(|s| (*s).to_owned()).collect();
            assert!(
                decode_and_revalidate(&context, &encode(&changed))
                    .unwrap_err()
                    .contains("limitations differ")
            );
        }
    }

    #[test]
    fn imported_mixed_literal_rechecks_unused_parameter_types_and_actual_constant() {
        let batch = checked("def mixed (a : UInt8) (b : UInt64) : UInt8 := 7");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        for change_telescope in [true, false] {
            let mut changed = envelope.clone();
            let mut changed_module = module.clone();
            if change_telescope {
                changed_module.func_types[0].params.swap(0, 1);
                changed_module.functions[0].blocks[0].params[0].1 = Ty::U64;
                changed_module.functions[0].blocks[0].params[1].1 = Ty::U8;
            } else {
                changed_module.functions[0].blocks[0].body[0].inst =
                    Inst::Const { ty: Ty::U8, value: trust_ir::Constant::Int(8) };
            }
            validate(&changed_module).expect("modified SSA remains structurally valid");
            rewrite_binary(&mut changed, &changed_module);
            let published = &changed_module.functions[0];
            let mut original = published.clone();
            original.producer = None;
            let remint = binding(
                &context,
                &envelope.bodies[0].declaration,
                &changed_module.func_types[0],
                &original,
                published,
            );
            assert!(remint.is_err(), "a fresh body binding cannot erase typed source differences");
            let error = decode_and_revalidate(&context, &encode(&changed)).unwrap_err();
            assert!(
                !error.contains("gate binding changed"),
                "fresh kernel/carrier rejection, not stale hash: {error}"
            );
        }
    }

    #[test]
    fn literal_import_cannot_borrow_older_disclosures_or_changed_source() {
        let batch = checked("def literal8 (a b : UInt8) : UInt8 := 7");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        for legacy in [LIMITATIONS, PROJECTION_LIMITATIONS] {
            let mut changed = envelope.clone();
            changed.limitations = legacy.iter().map(|s| (*s).to_owned()).collect();
            let error = decode_and_revalidate(&context, &encode(&changed)).unwrap_err();
            assert!(error.contains("limitations differ"), "{error}");
        }
        let changed = checked("def literal8 (a b : UInt8) : UInt8 := 8");
        assert!(
            decode_and_revalidate(&changed.accepted_context().unwrap(), &encode(&envelope))
                .is_err()
        );
        // A wire-authored broader disclosure also cannot alter the old accepted
        // population's expected bytes or activate a different admission shape.
        let legacy_batch = checked(ADD);
        let legacy_context = legacy_batch.accepted_context().unwrap();
        let mut legacy = assemble(&legacy_context).unwrap();
        legacy.limitations = LITERAL_LIMITATIONS.iter().map(|s| (*s).to_owned()).collect();
        assert!(
            decode_and_revalidate(&legacy_context, &encode(&legacy))
                .unwrap_err()
                .contains("limitations differ")
        );
    }

    #[test]
    fn changed_literal_value_or_return_refuses_even_after_hashes_and_fresh_binding_attempt() {
        let batch = checked("def literal8 (a b : UInt8) : UInt8 := 7");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        for wrong_return in [false, true] {
            let mut changed = envelope.clone();
            let mut changed_module = module.clone();
            if wrong_return {
                changed_module.functions[0].blocks[0].body[1].inst =
                    Inst::Return { values: vec![trust_ir::value::ValueId::new(0)] };
            } else {
                changed_module.functions[0].blocks[0].body[0].inst =
                    Inst::Const { ty: Ty::U8, value: trust_ir::Constant::Int(8) };
            }
            validate(&changed_module)
                .expect("wrong in-range literal/parameter is structurally valid SSA");
            rewrite_binary(&mut changed, &changed_module);
            let published = &changed_module.functions[0];
            let mut original = published.clone();
            original.id = FuncId::new(0);
            original.ty = FuncTyId::new(0);
            original.producer = None;
            let remint = binding(
                &context,
                &envelope.bodies[0].declaration,
                &module.func_types[0],
                &original,
                published,
            );
            if let Ok(binding) = &remint {
                changed.bodies[0] = binding.clone();
            }
            assert!(remint.is_err(), "actual wrong SSA must not earn new permission");
            let error = decode_and_revalidate(&context, &encode(&changed)).unwrap_err();
            assert!(
                !error.contains("gate binding changed"),
                "stale digest must not be the refusal: {error}"
            );
        }
    }

    #[test]
    fn unsupported_parameter_or_out_of_range_literal_siblings_refuse_the_entire_library() {
        // The former mixed-UInt negative is now a positive; keep two source
        // bodies and the nearest unsupported parameter-carrier control.
        // Trust (WS5.20): `256 : UInt8` is Lean's residue 0 now (admitted,
        // `literal_residue_library_*`); the out-of-range control moves to the
        // numeral reader's own bound, 2^64, whose residue this lane does not compute.
        for sibling in
            ["def nonUInt (n : Bool) : UInt8 := 7", "def oversized : UInt8 := 18446744073709551616"]
        {
            let batch = checked(&format!("{ADD}\n{sibling}"));
            let context = batch.accepted_context().expect("source kernel semantics are valid");
            assert_eq!(partition(&context).unwrap().0.len(), 2);
            assert!(assemble(&context).unwrap_err().to_string().contains("no library artifact"));
        }
    }

    /// Trust (WS5.20, `STANDALONE.p18_literal_out_of_range`): the probe builds a
    /// library whose gate re-earns on import; the body returns Lean's residue
    /// (`(300 : UInt8)` IS 44) and the disclosure says so. An envelope that
    /// drops the residue line is refused.
    #[test]
    fn literal_residue_library_reearns_and_discloses_the_residue() {
        let batch = checked("def lit300 : UInt8 := 300");
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let mut expected: Vec<String> =
            LITERAL_LIMITATIONS.iter().map(|s| (*s).to_owned()).collect();
        expected.push(LITERAL_RESIDUE_DISCLOSURE.to_owned());
        assert_eq!(envelope.limitations, expected);
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let result = Interpreter::new().execute_function(&module.functions[0], Vec::new()).unwrap();
        assert_eq!(result.returns[0].as_int().unwrap().as_unsigned(), 44);
        let mut hidden = envelope.clone();
        hidden.limitations.pop();
        assert!(
            decode_and_revalidate(&context, &encode(&hidden))
                .unwrap_err()
                .contains("limitations differ")
        );
        // An in-range literal population keeps its historical disclosure bytes.
        let batch = checked("def lit44 : UInt8 := 44");
        let context = batch.accepted_context().unwrap();
        let limitations: Vec<String> =
            LITERAL_LIMITATIONS.iter().map(|s| (*s).to_owned()).collect();
        assert_eq!(assemble(&context).unwrap().limitations, limitations);
    }

    #[test]
    fn historical_wrapping_disclosure_is_preserved_but_cannot_label_projections() {
        let legacy: Vec<String> = LIMITATIONS.iter().map(|s| (*s).to_owned()).collect();
        for source in [ADD, "theorem refl (n : Nat) : Nat.le n n := Nat.le.refl"] {
            let batch = checked(source);
            let context = batch.accepted_context().unwrap();
            let envelope = assemble(&context).unwrap();
            assert_eq!(envelope.limitations, legacy);
            decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        }
        let batch = checked("def keep (n : UInt8) : UInt8 := n");
        let context = batch.accepted_context().unwrap();
        let mut envelope = assemble(&context).unwrap();
        assert_eq!(envelope.limitations, PROJECTION_LIMITATIONS);
        decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        envelope.limitations = legacy;
        let error = decode_and_revalidate(&context, &encode(&envelope)).unwrap_err();
        assert!(error.contains("limitations differ"), "{error}");
    }

    #[test]
    fn changed_projection_return_refuses_even_after_binary_hash_and_binding_remint() {
        let batch = checked(
            "def first8 (a b : UInt8) : UInt8 := a\n\
             def second8 (a b : UInt8) : UInt8 := b",
        );
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        for index in 0..module.functions.len() {
            let mut changed = envelope.clone();
            let mut changed_module = module.clone();
            let function = &mut changed_module.functions[index];
            let returned = match &mut function.blocks[0].body[0].inst {
                Inst::Return { values } => &mut values[0],
                other => panic!("projection must contain one actual Return, got {other:?}"),
            };
            *returned = trust_ir::value::ValueId::new(1 - returned.index());
            validate(&changed_module).expect("wrong same-width parameter is valid SSA");
            rewrite_binary(&mut changed, &changed_module);
            let published = &changed_module.functions[index];
            let mut original = published.clone();
            original.id = FuncId::new(0);
            original.ty = FuncTyId::new(0);
            original.producer = None;
            // An attacker may recompute every public hash and try the real
            // gate against authentic sources. A stale digest must not be the
            // only reason this semantically wrong function is refused.
            let remint = binding(
                &context,
                &envelope.bodies[index].declaration,
                &module.func_types[index],
                &original,
                published,
            );
            if let Ok(binding) = &remint {
                changed.bodies[index] = binding.clone();
            }
            let error = decode_and_revalidate(&context, &encode(&changed)).unwrap_err();
            assert!(!error.contains("gate binding changed"), "{error}");
            assert!(remint.is_err(), "wrong parameter must not earn a fresh source judgment");
        }
    }

    #[test]
    fn inductive_projection_is_not_promoted_to_the_ordinary_uint_gate() {
        let batch = checked(
            "def foldIdentity (n : Nat) : Nat := @Nat.rec.{1} (fun _ => Nat) Nat.zero (fun _ ih => Nat.succ ih) n",
        );
        let context = batch.accepted_context().expect("kernel accepts the recursive identity");
        let plan =
            trust_clean_origin::plan_clean_origin_body(context.environment(), "foldIdentity")
                .expect("inductive projection planning remains separate from ordinary projection");
        assert!(matches!(
            plan.shape(),
            trust_clean_origin::CleanOriginShape::InductiveProjection { .. }
        ));
        let error = assemble(&context).unwrap_err().to_string();
        assert!(error.contains("foldIdentity"), "{error}");
        assert!(error.contains("no library artifact"), "{error}");
    }

    #[test]
    fn proof_only_declaration_stays_kernel_side() {
        let batch =
            checked(&format!("{ADD}\ntheorem refl (n : Nat) : Nat.le n n := Nat.le.refl"));
        let context = batch.accepted_context().expect("proof accepted");
        let envelope = assemble(&context).unwrap();
        assert_eq!(envelope.bodies.len(), 1);
        assert!(envelope.kernel_only_declarations.contains(&Name::from_string("refl")));
        decode_and_revalidate(&context, &encode(&envelope)).unwrap();
    }

    #[test]
    fn unsupported_computational_sibling_is_never_dropped() {
        let batch = checked(&format!("{ADD}\n{UNSUPPORTED}"));
        let context = batch.accepted_context().expect("kernel accepts branch sibling");
        assert_eq!(partition(&context).unwrap().0.len(), 2);
        let error = assemble(&context).unwrap_err().to_string();
        assert!(error.contains("branch8"), "{error}");
        assert!(error.contains("no library artifact"), "{error}");
    }

    #[test]
    fn generated_constructor_and_recursor_are_not_silently_skipped() {
        let batch =
            checked("inductive LocalChoice where\n| first : LocalChoice\n| second : LocalChoice");
        let context = batch.accepted_context().expect("kernel accepts inductive");
        let (computational, _) = partition(&context).unwrap();
        assert!(computational.iter().any(|n| context.environment().get_constructor(n).is_some()));
        assert!(computational.iter().any(|n| context.environment().get_recursor(n).is_some()));
        assert!(assemble(&context).is_err());
    }

    #[test]
    fn changed_source_or_source_digest_cannot_reuse_artifact() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let changed = checked("def add8 (a b : UInt8) : UInt8 := a - b");
        assert!(
            decode_and_revalidate(&changed.accepted_context().unwrap(), &encode(&envelope))
                .is_err()
        );
        let mut changed = envelope.clone();
        changed.sources[0].source.push(' ');
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut changed = envelope;
        changed.source_closure_sha256 = "0".repeat(64);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
    }

    #[test]
    fn changed_actual_function_refuses_even_with_recomputed_module_digests() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let mut envelope = assemble(&context).unwrap();
        let mut module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let mut changed = false;
        for node in &mut module.functions[0].blocks[0].body {
            if let Inst::BinOp { op, .. } = &mut node.inst {
                *op = BinOp::Sub;
                changed = true;
            }
        }
        assert!(changed);
        rewrite_binary(&mut envelope, &module);
        assert!(decode_and_revalidate(&context, &encode(&envelope)).is_err());
    }

    #[test]
    fn function_identity_gate_digest_and_roster_mutations_refuse() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let mut changed = envelope.clone();
        changed.bodies[0].subject_digest = "0".repeat(64);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut changed = envelope.clone();
        changed.owned_declarations.clear();
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut changed = envelope.clone();
        changed.bodies.clear();
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut changed = envelope.clone();
        changed.module_sha256 = "0".repeat(64);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        module.functions[0].name = "other".into();
        let mut changed = envelope;
        rewrite_binary(&mut changed, &module);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
    }

    #[test]
    fn malformed_and_unknown_envelope_fields_refuse() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let mut value = serde_json::to_value(envelope).unwrap();
        value["passed"] = serde_json::json!(true);
        assert!(decode_and_revalidate(&context, &serde_json::to_vec(&value).unwrap()).is_err());
        assert!(decode_and_revalidate(&context, b"{}").is_err());
        assert!(decode_and_revalidate(&context, b"{\"schema\":1,\"schema\":2}").is_err());
    }

    #[test]
    fn recomputed_binary_hash_cannot_hide_lost_or_extra_module_items() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        assert_eq!(module.files, vec!["/checked/Demo.lean"]);
        for files in [Vec::new(), vec!["/unrelated/Demo.lean".to_owned()]] {
            let mut changed_module = module.clone();
            changed_module.files = files;
            let mut changed = envelope.clone();
            rewrite_binary(&mut changed, &changed_module);
            assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        }
        let mut missing = module.clone();
        missing.functions.clear();
        missing.func_types.clear();
        let mut changed = envelope.clone();
        rewrite_binary(&mut changed, &missing);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut duplicate = module.clone();
        duplicate.functions.push(module.functions[0].clone());
        rewrite_binary(&mut changed, &duplicate);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
        let mut unrelated_type = module;
        unrelated_type.types.push(Ty::U8);
        rewrite_binary(&mut changed, &unrelated_type);
        assert!(decode_and_revalidate(&context, &encode(&changed)).is_err());
    }

    #[test]
    fn fresh_binding_remint_cannot_authorize_injected_proof_metadata() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let mut claimed_summary = module.functions[0].clone();
        claimed_summary.summary = Some(trust_ir::FunctionSummary {
            params: vec!["a".into(), "b".into()],
            requires: Vec::new(),
            ensures: vec![trust_ir::ProofFormula::smtlib2("false", "Bool")],
            proved: true,
            // This forged summary carries no descent claim or imported backing.
            decreases: Vec::new(),
            backed_by: None,
            effects: None,
        });
        let mut claimed_proof = module.functions[0].clone();
        claimed_proof.proofs.push(trust_ir::ProofAnnotation::NoPanic);
        let mut claimed_attrs = module.functions[0].clone();
        claimed_attrs.attrs.readnone = true;
        let mut claimed_node_proof = module.functions[0].clone();
        claimed_node_proof.blocks[0].body[0].proofs.push(trust_ir::ProofAnnotation::NoOverflow);
        for changed_function in [claimed_summary, claimed_proof, claimed_attrs, claimed_node_proof]
        {
            let mut changed = envelope.clone();
            let mut changed_module = module.clone();
            changed_module.functions[0] = changed_function.clone();
            rewrite_binary(&mut changed, &changed_module);
            let mut original = changed_function.clone();
            original.id = FuncId::new(0);
            original.ty = FuncTyId::new(0);
            original.producer = None;
            // The attacker controls EVERY serialized digest and can call the
            // public mint with authentic sources. A stale-row-digest refusal
            // alone would not catch this attack: try to obtain a fresh row.
            let remint = binding(
                &context,
                &Name::from_string("add8"),
                &module.func_types[0],
                &original,
                &changed_function,
            );
            if let Ok(binding) = &remint {
                changed.bodies[0] = binding.clone();
            }
            assert!(
                decode_and_revalidate(&context, &encode(&changed)).is_err(),
                "injected metadata must refuse even after fresh binding remint"
            );
            assert!(remint.unwrap_err().contains("standalone-metadata"));
        }
    }

    #[cfg(unix)]
    #[test]
    fn existing_and_dangling_output_symlinks_are_preserved() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        let sentinel = dir.path().join("sentinel");
        std::fs::write(&input, ADD).unwrap();
        std::fs::write(&sentinel, b"original").unwrap();
        for (label, target) in
            [("existing", sentinel.clone()), ("dangling", dir.path().join("absent"))]
        {
            let output = dir.path().join(label);
            std::os::unix::fs::symlink(&target, &output).unwrap();
            assert!(
                build(&Request {
                    input: input.clone(),
                    output: output.clone(),
                    verbose: false,
                    census_output: None,
                    olean_paths: Vec::new(),
                })
                .is_err()
            );
            assert_eq!(std::fs::read_link(output).unwrap(), target);
        }
        assert_eq!(std::fs::read(sentinel).unwrap(), b"original");
        assert!(!dir.path().join("absent").exists());
    }

    #[test]
    fn actual_cli_build_and_existing_output_preservation() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        let output = dir.path().join("Demo.lean-ir.json");
        std::fs::write(&input, ADD).unwrap();
        let request = Request {
            input,
            output: output.clone(),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        assert_eq!(build(&request).unwrap(), 1);
        let original = std::fs::read(&output).unwrap();
        assert!(build(&request).unwrap_err().to_string().contains("already exists"));
        assert_eq!(std::fs::read(&output).unwrap(), original);
    }

    #[test]
    fn false_theorem_import_failure_and_missing_source_emit_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        let output = dir.path().join("Demo.lean-ir.json");
        let request = Request {
            input: input.clone(),
            output: output.clone(),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        assert!(build(&request).is_err());
        assert!(!output.exists());
        for source in [
            "theorem bogus : Nat.le 1 0 := Nat.le.refl",
            "import MissingLocalModule\ndef add8 (a b : UInt8) : UInt8 := a + b",
        ] {
            std::fs::write(&input, source).unwrap();
            assert!(build(&request).is_err());
            assert!(!output.exists());
        }
    }

    #[test]
    fn imported_computational_sibling_is_in_artifact_or_refuses_whole_build() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        let imported = dir.path().join("Helper.lean");
        let output = dir.path().join("Demo.lean-ir.json");
        std::fs::write(&input, "import Helper\ndef add8 (a b : UInt8) : UInt8 := a + b").unwrap();
        std::fs::write(&imported, "def sub8 (a b : UInt8) : UInt8 := a - b").unwrap();
        let request = Request {
            input,
            output: output.clone(),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        assert_eq!(build(&request).unwrap(), 2);
        let envelope: LibraryEnvelope =
            serde_json::from_slice(&std::fs::read(&output).unwrap()).unwrap();
        assert_eq!(envelope.sources.len(), 2);
        assert_eq!(envelope.bodies.len(), 2);
        std::fs::write(&imported, UNSUPPORTED).unwrap();
        let refused = Request {
            input: request.input,
            output: dir.path().join("refused.json"),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        assert!(build(&refused).unwrap_err().to_string().contains("branch8"));
        assert!(!refused.output.exists());
    }

    #[test]
    fn explicit_artifact_cli_only_and_duplicate_options_refuse() {
        let strings = |items: &[&str]| items.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
        assert_eq!(
            parse(&strings(&["Demo.lean", "--emit=trust-ir", "--out", "Demo.json"])).unwrap(),
            Request {
                input: "Demo.lean".into(),
                output: "Demo.json".into(),
                verbose: false,
                census_output: None,
                olean_paths: Vec::new(),
            }
        );
        assert!(
            parse(&strings(&["Demo.lean"]))
                .unwrap_err()
                .contains("executable codegen is not implemented")
        );
        for args in [
            vec!["Demo.lean", "--emit=trust-ir", "--emit=trust-ir", "--out", "a"],
            vec!["Demo.lean", "--emit=trust-ir", "--out", "a", "--out", "b"],
            vec!["Demo.lean", "--emit=trust-ir", "--out"],
            vec!["Demo.lean", "--emit=trust-ir", "--out", "a", "--release"],
            vec!["Demo.lean", "Other.lean", "--emit=trust-ir", "--out", "a"],
        ] {
            assert!(parse(&strings(&args)).is_err());
        }
        assert_eq!(run(&strings(&["Missing.lean", "--help"])), ExitCode::SUCCESS);
    }

    #[test]
    fn refusal_verbosity_is_an_explicit_lean_build_option_only() {
        let base = ["Demo.lean", "--emit=trust-ir", "--out", "Demo.json"];
        for position in [0, 1, base.len()] {
            let mut args: Vec<String> = base.iter().map(|s| (*s).into()).collect();
            args.insert(position, "--verbose".into());
            assert!(parse(&args).unwrap().verbose);
        }
        for extra in [vec!["--verbose", "--verbose"], vec!["--verbose=true"], vec!["-v"]] {
            let args: Vec<String> = base.iter().copied().chain(extra).map(String::from).collect();
            assert!(parse(&args).is_err());
            assert_eq!(run(&args), ExitCode::from(2));
        }
        assert!(USAGE.contains("[--verbose]"));
        assert!(USAGE.contains("does not change admission"));
    }

    #[test]
    fn a_refused_argument_is_answered_with_the_help_for_both_build_lanes() {
        // `--entry` IS an option of `targo trust build`; only the diagnostic
        // lane's parser defines it. The library parser refuses it by name, so
        // the usage printed beside that refusal must not be one in which the
        // lane that defines it does not appear.
        let args: Vec<String> = ["Demo.lean", "--emit=trust-ir", "--out", "a", "--entry", "twice"]
            .iter()
            .map(|s| (*s).to_owned())
            .collect();
        assert!(parse(&args).is_err());
        assert_eq!(run(&args), ExitCode::from(2));
        let help = full_usage();
        assert!(help.starts_with(USAGE), "{help}");
        assert!(help.ends_with(runtime::USAGE), "{help}");
        for clause in [
            "--emit=trust-ir",
            "--emit=diagnostic-runtime-trust-ir",
            "--entry NAME",
            "--entry-json",
        ] {
            assert!(help.contains(clause), "{clause} missing from\n{help}");
        }
    }

    #[test]
    fn compact_refusals_retain_every_typed_error_and_verbose_detail() {
        // Transparent helper calls now lower and re-earn their gates. Keep the
        // three-body diagnostic population and its source/gate refusal pair by
        // making this negative control explicitly opaque.
        let batch = checked(&format!(
            "{ADD}\n{UNSUPPORTED}\nopaque call8 (a b : UInt8) : UInt8 := add8 a b"
        ));
        let context = batch.accepted_context().expect("all three source bodies kernel-check");
        let error = assemble(&context).unwrap_err();
        let BuildError::Incomplete { total, refusals } = &error else {
            panic!("expected typed body refusals: {error:?}");
        };
        assert_eq!(*total, 3);
        assert_eq!(refusals.len(), 2);
        let compact = error.render(false);
        let verbose = error.render(true);
        for output in [&compact, &verbose] {
            assert!(output.contains("2 of 3 computational declaration(s) refused"));
            assert!(output.contains("no library artifact was emitted"));
            assert!(output.contains("no sibling was omitted"));
            assert!(output.contains("targo trust check FILE.lean"));
            assert!(output.contains("targo trust build FILE.lean --help"));
            for name in ["branch8", "call8"] {
                assert!(output.contains(&format!("`{name}`")), "{output}");
            }
        }
        for (name, refusal) in refusals {
            if name == &Name::from_string("call8") {
                assert!(matches!(refusal, BodyRefusal::Source(_)), "{refusal:?}");
            } else {
                assert!(
                    matches!(refusal, BodyRefusal::Gate(error) if error.stage() == "target-shape"),
                    "{refusal:?}"
                );
            }
            assert!(compact.contains(&refusal.summary()));
            assert!(verbose.contains(&refusal.detail()), "full original note is not truncated");
        }
        assert!(compact.contains("[source-shape/not-emittable]"));
        assert!(compact.contains("[gate/target-shape]"));
        assert!(compact.contains("rerun with --verbose"));
        assert!(!compact.contains("MIR"));
        assert!(!compact.contains("Rust code"));
        assert!(!compact.contains("restat"));
        assert!(compact.len() < 1_000, "compact summary: {compact}");
        assert!(verbose.len() > compact.len());
    }

    #[test]
    fn refusal_categories_use_types_not_legacy_reason_text() {
        let source = BodyRefusal::source(trust_clean_origin::emit::EmitRefusal::NotEmittable {
            name: "source".into(),
            reason: "kernel-disagreement: pretend compiler defect\nMIR legacy advice".into(),
        });
        assert!(source.summary().contains("source-shape/not-emittable"));
        assert!(!source.summary().contains("compiler inconsistency"));
        assert!(source.detail().contains("pretend compiler defect"));
        let unreflectable = BodyRefusal::source(
            trust_clean_origin::emit::EmitRefusal::CarrierDomainNotReflectable {
                name: "source".into(),
                position: "argument 0".into(),
                clean: "BitVec 8".into(),
                rust: "u8".into(),
            },
        );
        assert_eq!(
            unreflectable.summary(),
            "[carrier/domain-not-reflectable]: compiler reflection does not support this checked source carrier"
        );
        assert!(!unreflectable.summary().contains("compiler inconsistency"));
        assert!(unreflectable.detail().contains("argument 0"));
        let compiler =
            BodyRefusal::source(trust_clean_origin::emit::EmitRefusal::ReflectionRejected {
                name: "source".into(),
                detail: "exact compiler failure".into(),
            });
        assert!(compiler.summary().contains("compiler inconsistency, please report it"));
        assert!(compiler.detail().contains("exact compiler failure"));
        let batch = checked("def keepNat (n : Nat) : Nat := n");
        let context = batch.accepted_context().unwrap();
        let plan = trust_clean_origin::emit::plan_standalone_clean_origin_body(
            context.environment(),
            "keepNat",
        )
        .unwrap();
        let carrier =
            BodyRefusal::Carrier(trust_clean_ir::trust_ir_func_ty(plan.signature()).unwrap_err());
        assert!(carrier.summary().contains("[carrier/unrepresented-type]"));
        assert!(carrier.summary().contains("argument 0"));
        let emitter = BodyRefusal::Emitter(trust_clean_ir::CleanIrRefusal::ShapeNotYetSpelled {
            shape: "FutureShape",
        });
        assert_eq!(
            emitter.summary(),
            "[emitter/unsupported-shape]: no Trust-IR lowering for FutureShape"
        );
    }

    #[test]
    fn invalid_unsigned_conditional_refusal_retains_phase_and_no_artifact_result() {
        for (phase, refusal) in [
            (
                "carrier",
                BodyRefusal::Carrier(trust_clean_ir::CleanIrRefusal::InvalidUnsignedConditional),
            ),
            (
                "emitter",
                BodyRefusal::Emitter(trust_clean_ir::CleanIrRefusal::InvalidUnsignedConditional),
            ),
        ] {
            let summary = format!(
                "[{phase}/invalid-unsigned-conditional]: compiler plan's unsigned conditional \
                 tree disagrees with its sealed decision bound; please report it"
            );
            assert_eq!(refusal.summary(), summary);
            let detail = refusal.detail();
            let error = BuildError::Incomplete {
                total: 1,
                refusals: vec![(Name::from_string("conditional"), refusal)],
            };
            for verbose in [false, true] {
                let rendered = error.render(verbose);
                assert!(rendered.contains("no library artifact was emitted; 1 of 1"));
                assert!(rendered.contains(&summary));
                if verbose {
                    assert!(rendered.contains(&detail));
                }
            }
        }
    }

    #[test]
    fn rust_call_emission_refusal_retains_category_reason_and_no_artifact_result() {
        let reason = "missing exact module-owned callee identity for rust::helper";
        let refusal =
            BodyRefusal::Emitter(trust_clean_ir::CleanIrRefusal::RustCallEmissionRefused {
                reason: reason.into(),
            });
        assert_eq!(
            refusal.summary(),
            format!(
                "[emitter/rust-call-emission]: Rust call emission refused: {reason}; please report it"
            )
        );
        let detail = refusal.detail();
        let error = BuildError::Incomplete {
            total: 1,
            refusals: vec![(Name::from_string("caller"), refusal)],
        };
        for verbose in [false, true] {
            let rendered = error.render(verbose);
            assert!(rendered.contains("no library artifact was emitted; 1 of 1"));
            assert!(rendered.contains("`caller` [emitter/rust-call-emission]"));
            assert!(rendered.contains(reason));
            if verbose {
                assert!(rendered.contains(&detail));
            }
        }
    }

    #[test]
    fn actual_kernel_disagreement_is_a_compiler_issue_not_source_repair() {
        let batch = checked(ADD);
        let context = batch.accepted_context().unwrap();
        let envelope = assemble(&context).unwrap();
        let module = decode_and_revalidate(&context, &encode(&envelope)).unwrap();
        let mut original = module.functions[0].clone();
        original.producer = None;
        let mut changed = false;
        for node in &mut original.blocks[0].body {
            if let Inst::BinOp { op, .. } = &mut node.inst {
                *op = BinOp::Sub;
                changed = true;
            }
        }
        assert!(changed, "mutate the emitted actual Add, not a digest");
        let gate = checked_binding(
            &context,
            &envelope.bodies[0].declaration,
            &module.func_types[0],
            &original,
            &module.functions[0],
        )
        .unwrap_err();
        assert_eq!(gate.stage(), "kernel-disagreement");
        let detail = gate.note();
        let error = BuildError::Incomplete {
            total: 1,
            refusals: vec![(Name::from_string("add8"), BodyRefusal::Gate(gate))],
        };
        assert!(error.render(false).contains("kernel could not establish source/SSA agreement"));
        assert!(error.render(false).contains("compiler check failed, please report it"));
        assert!(!error.render(false).contains("SSA disagrees"));
        assert!(!error.render(false).contains("restat"));
        assert!(error.render(true).contains(&detail));
    }

    #[test]
    fn verbose_success_has_identical_bytes_and_preserves_existing_outputs() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        std::fs::write(&input, ADD).unwrap();
        let mut outputs = Vec::new();
        for verbose in [false, true] {
            let request = Request {
                input: input.clone(),
                output: dir.path().join(format!("{verbose}.json")),
                verbose,
                census_output: None,
                olean_paths: Vec::new(),
            };
            assert_eq!(build(&request).unwrap(), 1);
            let original = std::fs::read(&request.output).unwrap();
            let error = build(&request).unwrap_err();
            assert!(matches!(error, BuildError::Message { detail: None, .. }));
            assert!(error.render(verbose).contains("already exists"));
            assert_eq!(std::fs::read(&request.output).unwrap(), original);
            outputs.push(original);
        }
        assert_eq!(outputs[0], outputs[1], "verbosity must not enter the artifact");
    }

    #[test]
    fn verbose_and_default_refusals_have_same_exit_and_publish_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        std::fs::write(&input, format!("{ADD}\n{UNSUPPORTED}")).unwrap();
        for verbose in [false, true] {
            let output = dir.path().join(format!("{verbose}.json"));
            let mut args = vec![
                input.to_string_lossy().into_owned(),
                "--emit=trust-ir".into(),
                "--out".into(),
                output.to_string_lossy().into_owned(),
            ];
            if verbose {
                args.push("--verbose".into());
            }
            assert_eq!(run(&args), ExitCode::FAILURE);
            assert!(!output.exists());
        }
    }

    #[test]
    fn message_detail_is_verbose_only_and_detail_free_messages_stay_byte_identical() {
        let plain = BuildError::from("a refusal that already carries its own error".to_owned());
        assert_eq!(plain.render(false), "a refusal that already carries its own error");
        assert_eq!(plain.render(false), plain.render(true));
        assert!(!plain.render(false).contains("--verbose"), "no detail, so no hint");

        let detailed = BuildError::detailed(
            "a refusal with more beneath it".to_owned(),
            "  observed: 7".to_owned(),
        );
        assert_eq!(
            detailed.render(false),
            "a refusal with more beneath it\nFor full underlying refusal details, rerun with --verbose."
        );
        assert_eq!(
            detailed.render(true),
            "a refusal with more beneath it\n  Full underlying refusal details:\n  observed: 7"
        );
    }

    #[test]
    fn source_closure_refusal_discloses_its_roster_only_under_verbose() {
        let dir = tempfile::tempdir().unwrap();
        let input = dir.path().join("Demo.lean");
        std::fs::write(&input, "import MissingLocalModule\ndef ordinary : UInt8 := 1").unwrap();
        let request = Request {
            input,
            output: dir.path().join("library.json"),
            verbose: false,
            census_output: None,
            olean_paths: Vec::new(),
        };
        let error = build(&request).unwrap_err();
        let compact = error.render(false);
        let verbose = error.render(true);
        for output in [&compact, &verbose] {
            assert!(output.contains("Lean source closure was not accepted"), "{output}");
            assert!(output.contains("MissingLocalModule"), "{output}");
        }
        assert!(compact.contains("rerun with --verbose"), "{compact}");
        assert!(!compact.contains("checked source roster"), "{compact}");
        assert!(verbose.contains("Full underlying refusal details"), "{verbose}");
        assert!(verbose.contains("checked source roster (1 file(s))"), "{verbose}");
        assert!(verbose.contains("per-file verdicts (1)"), "{verbose}");
        assert!(verbose.contains("imports `MissingLocalModule`"), "{verbose}");
        assert!(!verbose.contains("rerun with --verbose"), "{verbose}");
        assert!(verbose.len() > compact.len());
        assert!(!request.output.exists(), "a refusal publishes nothing at either verbosity");

        // An existing output refuses with a complete io fact of its own. It
        // must not grow an invented detail block, or advertise one it lacks.
        std::fs::write(&request.output, "previous library").unwrap();
        let existing = build(&request).unwrap_err();
        assert!(matches!(existing, BuildError::Message { detail: None, .. }));
        assert_eq!(existing.render(false), existing.render(true));
        assert!(!existing.render(true).contains("--verbose"));
        assert_eq!(std::fs::read_to_string(&request.output).unwrap(), "previous library");
    }
}
