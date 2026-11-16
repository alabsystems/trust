//! The named refusal catalog (design 2026-10-01 §2.8, plus the Critique's
//! P0 codes and the census's own fail-closed codes).
//!
//! Every construct the census does not translate exactly — and every
//! verdict condition the host cannot establish — is one of these, with a
//! stable `PC-*` code printed in diagnostics and TRUST_JSON. A site that
//! carries one can never read "not refuted" ([`crate::verdict`]).

/// One named refusal. The payload says what, the code says which rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Refusal {
    /// §2.8: the site's enclosing body was refused by the producer.
    BodyNotLowered { path: String },
    /// §2.8: a callee on the root's path was refused by the producer.
    CalleeNotLowered { path: String },
    /// §2.8: `trust_platform::symbols` names no clause, or names a gap.
    Unmodeled { symbol: String, reason: String },
    /// §2.8: a std function not in the std table (and not on the census's
    /// audited effect-free list).
    UnknownStd { path: String },
    /// §2.8: a non-std upstream function with no exported fragment.
    Upstream { krate: String, path: String },
    /// §2.8: an fn pointer or `dyn` call on the root's path.
    IndirectCall { at: String },
    /// §2.8: an fd operand (or a descriptor-loop bound) the census lost.
    UntrackedFd { symbol: String, arg: String },
    /// §2.8: a command, flag, status or limit operand that is not constant.
    NonConstArg { symbol: String, arg: String },
    /// §2.8: an fd carrier escaped into memory or a callee the census does
    /// not model.
    FdEscape { what: String },
    /// §2.8: a truncating cast of a value that reaches a descriptor operand.
    FdTrunc { at: String },
    /// §2.8: a `posix_spawn` builder handle the census cannot follow (every
    /// builder until C5).
    SpawnBuilderEscape { symbol: String },
    /// §2.8: a `Command` method with no row.
    CommandShape { method: String },
    /// §2.8: a `spawn` of a `Command` the census did not see built (every
    /// std spawn until C4).
    CommandUnknown { method: String },
    /// §2.8: a `pre_exec` closure not bound to a body.
    PreExecUnresolved { why: String },
    /// §2.8: a `thread::spawn` closure not bound to a body (every dynamic
    /// thread until the census translates one to M2's `SpawnThread`, which
    /// the derivation has since `land/m2-census`).
    ThreadUnresolved { why: String },
    /// §2.8: a drop of a type containing an fd carrier, with no row —
    /// widened (the review's F2): any drop whose glue is not certainly
    /// empty (a `Drop` impl, a type the census does not audit).
    DropUnmodeled { ty: String },
    /// §2.8: a recursive call cycle on the root's path.
    Recursion { cycle: Vec<String> },
    /// §2.8: the inlining, body or block budget was exceeded.
    Size { what: String, limit: usize },
    /// §2.8: the derivation's state budget was exceeded (X4).
    Budget { detail: String },
    /// §2.8: ty refuted, but the replay failed: the diagnostic is withheld
    /// and the failure is a Trust defect.
    Replay { detail: String },
    /// §2.8: a site the HIR site census sees that trust-ir does not carry.
    SiteNotInIr { body: String, callee: String, at: String },
    /// §2.8: a census site with no site-census twin (or a count mismatch).
    CensusSkew { detail: String },
    /// §2.8: ambiguous or missing identity.
    Resolve { name: String, why: String },
    /// Critique C-4: no analysed root reaches the site.
    NoRoot,
    /// Critique C-16 (I-EFFECTS-COVERED): a HIR call to a foreign or std
    /// callee is missing from the body's trust-ir (or the HIR list is
    /// unavailable, so the check could not run).
    ProducerErased { body: String, detail: String },
    /// Critique C-2 (widened by the review's F2): a body on the root's path
    /// holds a value whose drop glue may have a platform effect — an fd
    /// carrier, a `Drop` impl — and the producer elides drops (no
    /// `Inst::Drop` until Step-2 increment 4b); or typeck's drop facts are
    /// missing, so the gate could not run.
    DropElided { body: String, ty: String },
    /// Critique C-9: the refutation relies on an over-approximating choice
    /// (`Cond::Nondet`), so it may follow a path the program cannot take.
    Overapprox { choices: Vec<String> },
    /// Critique C-1: "no counterexample" without exhaustive exploration, or
    /// without a refuted per-site non-vacuity check.
    Incomplete { why: String },
    /// Critique C-1: the derivation's own exploration and ty disagree.
    EngineDisagree { detail: String },
    /// Critique C-7: a shipped site with no checked counterpart.
    CfgSkew { detail: String },
    /// Census: a trust-ir instruction the census does not translate.
    IrUnsupported { inst: String },
    /// Census: a raw-`fork` child's continuation can return from the
    /// function that forked, into caller code the child would run.
    ForkChildReturns { func: String },
    /// Census: the census or the derivation's static check produced
    /// something malformed — a Trust defect, never a pass.
    Internal { detail: String },
}

/// One catalog row: a stable code and its one-line meaning.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CatalogRow {
    pub code: &'static str,
    pub meaning: &'static str,
    /// Where the code comes from: the design's §2.8 table, a Critique item,
    /// or the census's own fail-closed rules.
    pub source: &'static str,
}

/// Every code, in a stable order (the refusal catalog test checks that each
/// has a fixture producing it).
pub const CATALOG: &[CatalogRow] = &[
    row("PC-BODY-NOT-LOWERED", "the site's enclosing body was refused by the producer", "§2.8"),
    row("PC-CALLEE-NOT-LOWERED", "a callee on the root's path was refused by the producer", "§2.8"),
    row(
        "PC-UNMODELED",
        "trust_platform::symbols names no clause, or names a gap (NAMED_GAPS)",
        "§2.8",
    ),
    row("PC-UNKNOWN-STD", "a std function not in the std table", "§2.8"),
    row("PC-UPSTREAM", "a non-std upstream function with no exported fragment", "§2.8"),
    row("PC-INDIRECT-CALL", "an fn pointer or dyn call on the root's path", "§2.8"),
    row("PC-UNTRACKED-FD", "an fd operand the census lost", "§2.8"),
    row("PC-NONCONST-ARG", "a command, flag or limit operand that is not constant", "§2.8"),
    row(
        "PC-FD-ESCAPE",
        "an fd carrier escaped into memory or a container the census does not model",
        "§2.8",
    ),
    row("PC-FD-TRUNC", "a truncating cast of an fd", "§2.8"),
    row("PC-SPAWN-BUILDER-ESCAPE", "a posix_spawn builder handle the census cannot follow", "§2.8"),
    row("PC-COMMAND-SHAPE", "a Command builder method with no row", "§2.8"),
    row("PC-COMMAND-UNKNOWN", "a spawn of a Command the census did not see built", "§2.8"),
    row("PC-PRE-EXEC-UNRESOLVED", "a pre_exec closure not bound to a body", "§2.8"),
    row("PC-THREAD-UNRESOLVED", "a thread::spawn closure not bound to a body", "§2.8"),
    row(
        "PC-DROP-UNMODELED",
        "a drop of a type containing an fd carrier (or with any glue not certainly empty), with \
         no row",
        "§2.8",
    ),
    row("PC-RECURSION", "a recursive call cycle on the root's path", "§2.8"),
    row("PC-SIZE", "the inlining, body or block budget was exceeded", "§2.8"),
    row("PC-BUDGET", "the derivation's state budget was exceeded", "§2.8"),
    row(
        "PC-REPLAY",
        "ty refuted, but the replay failed; the diagnostic is withheld (a Trust defect)",
        "§2.8",
    ),
    row("PC-SITE-NOT-IN-IR", "a site the site census sees that trust-ir does not carry", "§2.8"),
    row("PC-CENSUS-SKEW", "a census site with no site-census twin", "§2.8"),
    row("PC-RESOLVE", "ambiguous or missing identity", "§2.8"),
    row("PC-NO-ROOT", "no analysed root reaches the site", "Critique C-4"),
    row(
        "PC-PRODUCER-ERASED",
        "a HIR foreign/std call is missing from the body's trust-ir (I-EFFECTS-COVERED)",
        "Critique C-16",
    ),
    row(
        "PC-DROP-ELIDED",
        "a value on the root's path whose drop glue may have an effect (an fd carrier, a Drop \
         impl) and the producer elides drops (before inc 4b), or no typeck drop facts",
        "Critique C-2",
    ),
    row(
        "PC-OVERAPPROX",
        "the refutation takes an over-approximating choice; it may not be a real path",
        "Critique C-9",
    ),
    row(
        "PC-INCOMPLETE",
        "no counterexample, but not exhaustively, or per-site non-vacuity was not refuted",
        "Critique C-1",
    ),
    row("PC-ENGINE-DISAGREE", "the derivation's exploration and ty disagree", "Critique C-1"),
    row("PC-CFG-SKEW", "a shipped site with no checked counterpart", "Critique C-7"),
    row("PC-IR-UNSUPPORTED", "a trust-ir instruction the census does not translate", "census"),
    row(
        "PC-FORK-CHILD-RETURNS",
        "a raw fork child's continuation returns into caller code the census does not follow",
        "census",
    ),
    row("PC-INTERNAL", "the census produced something malformed (a Trust defect)", "census"),
];

const fn row(code: &'static str, meaning: &'static str, source: &'static str) -> CatalogRow {
    CatalogRow { code, meaning, source }
}

impl Refusal {
    /// The stable code.
    #[must_use]
    pub fn code(&self) -> &'static str {
        match self {
            Refusal::BodyNotLowered { .. } => "PC-BODY-NOT-LOWERED",
            Refusal::CalleeNotLowered { .. } => "PC-CALLEE-NOT-LOWERED",
            Refusal::Unmodeled { .. } => "PC-UNMODELED",
            Refusal::UnknownStd { .. } => "PC-UNKNOWN-STD",
            Refusal::Upstream { .. } => "PC-UPSTREAM",
            Refusal::IndirectCall { .. } => "PC-INDIRECT-CALL",
            Refusal::UntrackedFd { .. } => "PC-UNTRACKED-FD",
            Refusal::NonConstArg { .. } => "PC-NONCONST-ARG",
            Refusal::FdEscape { .. } => "PC-FD-ESCAPE",
            Refusal::FdTrunc { .. } => "PC-FD-TRUNC",
            Refusal::SpawnBuilderEscape { .. } => "PC-SPAWN-BUILDER-ESCAPE",
            Refusal::CommandShape { .. } => "PC-COMMAND-SHAPE",
            Refusal::CommandUnknown { .. } => "PC-COMMAND-UNKNOWN",
            Refusal::PreExecUnresolved { .. } => "PC-PRE-EXEC-UNRESOLVED",
            Refusal::ThreadUnresolved { .. } => "PC-THREAD-UNRESOLVED",
            Refusal::DropUnmodeled { .. } => "PC-DROP-UNMODELED",
            Refusal::Recursion { .. } => "PC-RECURSION",
            Refusal::Size { .. } => "PC-SIZE",
            Refusal::Budget { .. } => "PC-BUDGET",
            Refusal::Replay { .. } => "PC-REPLAY",
            Refusal::SiteNotInIr { .. } => "PC-SITE-NOT-IN-IR",
            Refusal::CensusSkew { .. } => "PC-CENSUS-SKEW",
            Refusal::Resolve { .. } => "PC-RESOLVE",
            Refusal::NoRoot => "PC-NO-ROOT",
            Refusal::ProducerErased { .. } => "PC-PRODUCER-ERASED",
            Refusal::DropElided { .. } => "PC-DROP-ELIDED",
            Refusal::Overapprox { .. } => "PC-OVERAPPROX",
            Refusal::Incomplete { .. } => "PC-INCOMPLETE",
            Refusal::EngineDisagree { .. } => "PC-ENGINE-DISAGREE",
            Refusal::CfgSkew { .. } => "PC-CFG-SKEW",
            Refusal::IrUnsupported { .. } => "PC-IR-UNSUPPORTED",
            Refusal::ForkChildReturns { .. } => "PC-FORK-CHILD-RETURNS",
            Refusal::Internal { .. } => "PC-INTERNAL",
        }
    }

    /// The catalog row of this refusal's code.
    #[must_use]
    pub fn row(&self) -> &'static CatalogRow {
        let code = self.code();
        CATALOG.iter().find(|r| r.code == code).unwrap_or(&CATALOG[CATALOG.len() - 1])
    }
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: ", self.code())?;
        match self {
            Refusal::BodyNotLowered { path } => write!(f, "the producer refused `{path}`"),
            Refusal::CalleeNotLowered { path } => write!(
                f,
                "callee `{path}` was refused by the producer (run with -Ztrust-dump=ir: for its \
                 tags)"
            ),
            Refusal::Unmodeled { symbol, reason } => write!(f, "`{symbol}`: {reason}"),
            Refusal::UnknownStd { path } => write!(f, "`{path}` is not in the std table"),
            Refusal::Upstream { krate, path } => {
                write!(f, "`{path}` (crate `{krate}`) has no exported fragment")
            }
            Refusal::IndirectCall { at } => write!(f, "indirect call at {at}"),
            Refusal::UntrackedFd { symbol, arg } => {
                write!(f, "{arg} of `{symbol}` is a value the census did not track")
            }
            Refusal::NonConstArg { symbol, arg } => {
                write!(f, "{arg} of `{symbol}` is not a constant")
            }
            Refusal::FdEscape { what } => write!(f, "{what}"),
            Refusal::FdTrunc { at } => {
                write!(f, "a truncating cast at {at} reaches a descriptor operand")
            }
            Refusal::SpawnBuilderEscape { symbol } => {
                write!(f, "`{symbol}`: posix_spawn builder objects are not followed (C5)")
            }
            Refusal::CommandShape { method } => write!(f, "`{method}` has no Command row"),
            Refusal::CommandUnknown { method } => write!(
                f,
                "`{method}` of a Command the census did not see built (Command objects are C4)"
            ),
            Refusal::PreExecUnresolved { why } => write!(f, "{why}"),
            Refusal::ThreadUnresolved { why } => write!(f, "{why}"),
            Refusal::DropUnmodeled { ty } => write!(
                f,
                "drop of `{ty}` runs drop glue the census does not model (an fd carrier's close \
                 is X3's STD-DROP-FD; a Drop impl is user code)"
            ),
            Refusal::Recursion { cycle } => write!(f, "recursion: {}", cycle.join(" -> ")),
            Refusal::Size { what, limit } => write!(f, "{what} exceeds {limit}"),
            Refusal::Budget { detail }
            | Refusal::Replay { detail }
            | Refusal::CensusSkew { detail }
            | Refusal::EngineDisagree { detail }
            | Refusal::CfgSkew { detail }
            | Refusal::Internal { detail } => write!(f, "{detail}"),
            Refusal::SiteNotInIr { body, callee, at } => {
                write!(f, "`{callee}` at {at} in `{body}` is not in the body's trust-ir")
            }
            Refusal::Resolve { name, why } => write!(f, "`{name}`: {why}"),
            Refusal::NoRoot => write!(f, "no analysed root reaches this site"),
            Refusal::ProducerErased { body, detail } => write!(f, "`{body}`: {detail}"),
            Refusal::DropElided { body, ty } => write!(
                f,
                "`{body}` holds `{ty}`, whose drop glue (a close, or a Drop impl) trust-ir \
                 elides until Step-2 inc 4b"
            ),
            Refusal::Overapprox { choices } => {
                write!(f, "the trace takes over-approximating choices: {}", choices.join("; "))
            }
            Refusal::Incomplete { why } => write!(f, "{why}"),
            Refusal::IrUnsupported { inst } => write!(f, "{inst}"),
            Refusal::ForkChildReturns { func } => write!(
                f,
                "the child of the fork in `{func}` can return from it into code the census does \
                 not follow"
            ),
        }
    }
}

/// Every variant, one each (the catalog test's coverage set).
#[must_use]
pub fn one_of_each() -> Vec<Refusal> {
    let s = String::new;
    vec![
        Refusal::BodyNotLowered { path: s() },
        Refusal::CalleeNotLowered { path: s() },
        Refusal::Unmodeled { symbol: s(), reason: s() },
        Refusal::UnknownStd { path: s() },
        Refusal::Upstream { krate: s(), path: s() },
        Refusal::IndirectCall { at: s() },
        Refusal::UntrackedFd { symbol: s(), arg: s() },
        Refusal::NonConstArg { symbol: s(), arg: s() },
        Refusal::FdEscape { what: s() },
        Refusal::FdTrunc { at: s() },
        Refusal::SpawnBuilderEscape { symbol: s() },
        Refusal::CommandShape { method: s() },
        Refusal::CommandUnknown { method: s() },
        Refusal::PreExecUnresolved { why: s() },
        Refusal::ThreadUnresolved { why: s() },
        Refusal::DropUnmodeled { ty: s() },
        Refusal::Recursion { cycle: Vec::new() },
        Refusal::Size { what: s(), limit: 0 },
        Refusal::Budget { detail: s() },
        Refusal::Replay { detail: s() },
        Refusal::SiteNotInIr { body: s(), callee: s(), at: s() },
        Refusal::CensusSkew { detail: s() },
        Refusal::Resolve { name: s(), why: s() },
        Refusal::NoRoot,
        Refusal::ProducerErased { body: s(), detail: s() },
        Refusal::DropElided { body: s(), ty: s() },
        Refusal::Overapprox { choices: Vec::new() },
        Refusal::Incomplete { why: s() },
        Refusal::EngineDisagree { detail: s() },
        Refusal::CfgSkew { detail: s() },
        Refusal::IrUnsupported { inst: s() },
        Refusal::ForkChildReturns { func: s() },
        Refusal::Internal { detail: s() },
    ]
}
