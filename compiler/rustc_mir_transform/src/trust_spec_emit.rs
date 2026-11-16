// Trust (v6/D1): the `targo trust spec --emit clean` session-artifact writer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

//! COMPILER-AUTHORITATIVE spec-goal and clause-denotation emission (standing
//! ruling v6/D1, two-language W3).
//!
//! `targo trust spec --emit clean` prints "the Clean goal the compiler
//! actually elaborated and the kernel actually checked". An offline
//! re-elaboration in targo-trust was considered and REJECTED by the ruling: it
//! can print a different proposition than the kernel saw, precisely when
//! someone is debugging a failure. So the goals are published from INSIDE the
//! verification session — this module is the writer. The discharge lanes in
//! `trust_verify.rs` publish `goal` rows at the exact point where a grade
//! verdict for a cited ensures clause is in hand. Separately, the completed
//! post-walk contract inventory publishes `denotation` rows for uncited
//! `requires`/`ensures` clauses. A denotation is explicitly zero-authority: it
//! exposes the canonical Lean/Clean proposition the typed compiler query
//! denotes, but it is not a proof, verdict, assumption, or discharge.
//!
//! ## What "the goal the kernel checked" means here, precisely
//!
//! The grade call is `trust_certify::clean_island::
//! kernel_discharge_ensures_citation(env, theorem, clause, params, self_fn,
//! facets)`, which internally computes `trust_spec_elab::elaborate_ensures(
//! clause, params, self_fn, facets)` and grades the cited proof term against
//! that expression. The verdict comes back, but the goal `Expr` does not.
//! This module therefore calls THE SAME elaborator entry point with THE SAME
//! argument values, in THE SAME compiler session, and renders the result with
//! the kernel `Expr`'s own `Display` — the identical rendering the
//! `TRUST_E9_DEBUG GOAL` stand-in prints (see the comment block in
//! `trust-certify/src/clean_island.rs::kernel_discharge_ensures_citation`,
//! which names this subcommand as the thing it stands in for).
//!
//! This is NOT the rejected offline re-elaboration: nothing here runs outside
//! the session, on other inputs, or through other code. The only divergence
//! channel left is nondeterminism inside `elaborate_ensures` itself, and the
//! byte-identity controls pin that shut
//! (`crates/trust-spec-elab/tests/spec_emit_render_determinism.rs`,
//! `crates/trust-certify/tests/spec_emit_goal_render_identity.rs`). The moment
//! `kernel_discharge_ensures_citation` grows a variant that returns its goal
//! alongside the verdict, swap the recomputation for the returned `Expr` and
//! delete this paragraph.
//!
//! ## Activation
//!
//! Two spellings, both explicit, neither able to change a verdict (the
//! artifact is disclosure of what the kernel already graded — it gates
//! nothing and proves nothing by itself):
//!
//! * `-Ztrust-dump=spec-clean:<dir>` — the canonical knob, one more sink in
//!   the closed `-Ztrust-dump` verification-artifact set (the same shape as
//!   `native-bundle:`/`ir:`). Direct trustc invocations and ui fixtures use
//!   this.
//! * `TRUST_SPEC_EMIT_DIR=<abs dir>` — the driver transport for Cargo crate
//!   mode. It exists because the graph-wide rustflags channel is a CLOSED
//!   host-policy protocol (`VERIFIED_TARGO_HOST_POLICY_OPTIONS`, mirrored in
//!   the sibling targo's `target_info.rs`): `-Ztrust-dump` deliberately cannot
//!   ride it, and per-unit `-Z` injection is targo-internal. targo-trust
//!   stages this variable on the child it spawns, AFTER its ambient-authority
//!   scrub, and scrubs any inherited value — so in a verified crate run only
//!   the driver's deliberate value survives. A relative path is refused here
//!   (never write an artifact relative to ambient cwd — the same rule
//!   `trust-proof-artifact-root` enforces).
//!
//! ## Artifact
//!
//! `<dir>/<crate_name>-<stable_crate_id_hex>.spec-clean.jsonl`, one JSON
//! object per line, every line self-describing (`"format":
//! "trust-spec-clean", "v": 2`):
//!
//! * `row: "goal"` — one kernel-graded ensures obligation: `def_path`, dense
//!   authored `contract_index`,
//!   `origin` (`ensures-citation` in-walk / `ensures-citation-deferred`
//!   post-walk / `ensures-island-defeq` for an UNCITED clause that names a
//!   Clean island definition and is judged by definitional equality — its
//!   `theorem` slot then reads `defeq:<island def>`, the same referent the
//!   sealed row authority records), the authored `clause` text exactly as
//!   graded (post-rewrite),
//!   the cited `theorem`, `goal_clean` (kernel `Display` of the elaborated
//!   goal; `null` with `elab_error` set when elaboration refused — the same
//!   refusal the verdict reports), the `verdict`, optional `detail`, and
//!   `view` — `null` for an ordinary goal, and `"frozen-shared-erased"` when
//!   the goal's binders name a frozen shared pointee's field VALUES through the
//!   borrow-erased E6 parameter view, which is graded BELOW `Certified` (owner
//!   ruling R1, `docs/TCB.md`). Three OR-A1 members follow it (owner ruling
//!   2026-09-27): `rung` — WHICH goal the row describes, not whether a grade
//!   ran: `"unconditional"` on every graded-goal row whose `goal_clean` /
//!   `elab_error` is the unconditional goal `G0` (including a row whose grade
//!   never ran, e.g. `session-tainted` — its goal is still `G0`),
//!   `"under-requires"` when it is the CONDITIONAL goal a cited theorem was
//!   credited on, and `null` only on a preparation-refusal row, where no goal
//!   was built at all;
//!   `requires_link` — `null`, or `"kernel-canonical"` / `"allow-listed"` for an
//!   under-requires row (which reading of the function's own `requires` the
//!   hypotheses took; both are graded `Trusted`, `docs/TCB.md`'s
//!   `EnsuresCitationUnderRequiresDischarge` row); `hypotheses` — `null`, or the
//!   carried hypotheses of an under-requires row in binder order, each
//!   `{binder, contract_index, canonical, graded}`. Like `view`, the keys are
//!   written on every goal row, so their PRESENCE marks an artifact written
//!   after OR-A1 without moving the schema version. If the
//!   compiler cannot recover either authored or query-owned clause text, the
//!   row remains counted with null `clause`/`goal_clean` and an explicit
//!   `clause-outside-fragment` preparation refusal; it is never described as a
//!   kernel grade.
//! * `row: "denotation"` — one uncited function-level `requires`/`ensures`
//!   clause from the compiler query inventory. It carries the dense authored
//!   `contract_index`, kind/source, canonical clause spelling, the elaborated
//!   Clean proposition (or an explicit refusal), and the immutable labels
//!   `authority: "none"`, `verdict: "ungraded"`, plus the same `view` key the
//!   goal rows carry — a zero-authority row whose binders name a frozen shared
//!   pointee's field values still rests on owner ruling R1, and a reader
//!   grepping for `"view"` must not have to know which populations disclose.
//!   It can never mint proof authority. Citation-bearing clauses are outside this uncited population;
//!   cited `ensures` retain their separately graded `goal` rows. An uncited
//!   island-defeq clause is BOTH: it stays in this inventory as a
//!   zero-authority denotation AND carries an `ensures-island-defeq` goal row
//!   when the defeq lane graded it — the two populations are sealed with
//!   independent counts and the reader keys them separately.
//! * `row: "session"` — the completion seal, written once at the end of
//!   `trust_ensure_whole_crate_verification`'s enabled path, carrying the
//!   independent `goals` and `denotations` counts written by this process. The
//!   reader treats a missing seal or either physical row-count mismatch as a
//!   torn artifact and REFUSES — which is what makes the subcommand fail closed
//!   when no live session actually completed. These counters authenticate
//!   completed writes; producer-completeness is established separately by the
//!   compiler-boundary inventory tests, not inferred from a self-reported seal.

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LOCAL_CRATE;

/// The driver-staged environment transport (see module docs for why the
/// `-Ztrust-dump` spelling cannot ride the graph-wide rustflags channel).
pub const TRUST_SPEC_EMIT_ENV: &str = "TRUST_SPEC_EMIT_DIR";

/// Artifact format tag, present on every line.
pub const SPEC_CLEAN_FORMAT: &str = "trust-spec-clean";

/// Artifact format version, present on every line. The reader refuses any
/// other value rather than guessing at unknown semantics.
pub const SPEC_CLEAN_VERSION: u64 = 2;

/// Per-unit artifact filename suffix.
pub const SPEC_CLEAN_FILE_SUFFIX: &str = ".spec-clean.jsonl";

/// Goal rows written by this compiler process; sealed into the session row so
/// the reader can detect a torn artifact.
static GOAL_ROWS_WRITTEN: AtomicU64 = AtomicU64::new(0);

/// Zero-authority denotation rows written by this compiler process; sealed
/// independently so their physical completeness is not conflated with the
/// graded-goal count.
static DENOTATION_ROWS_WRITTEN: AtomicU64 = AtomicU64::new(0);

/// The requested emission directory, or `None` when this session was not
/// asked to publish spec goals. The typed `-Ztrust-dump=spec-clean:` sink
/// wins; the env transport is consulted only in its absence and only accepts
/// an absolute path (ambient-cwd hygiene; a relative value is ignored rather
/// than resolved).
fn spec_emit_destination(tcx: TyCtxt<'_>) -> Option<PathBuf> {
    if let Some(dir) = tcx.sess.opts.unstable_opts.trust_dump.spec_clean.as_deref() {
        return Some(dir.to_path_buf());
    }
    let env_dir = std::env::var_os(TRUST_SPEC_EMIT_ENV)?;
    if env_dir.is_empty() {
        return None;
    }
    let dir = PathBuf::from(env_dir);
    if !dir.is_absolute() {
        return None;
    }
    Some(dir)
}

/// Whether this compiler session requested the spec-clean artifact. Consumers
/// use this only to avoid an observational denotation walk on ordinary builds;
/// the writer still rechecks the destination before every append.
pub fn emission_requested(tcx: TyCtxt<'_>) -> bool {
    spec_emit_destination(tcx).is_some()
}

/// One file per compilation unit: crate name plus the stable crate id, so two
/// targets of one package (lib and bin share a crate name but never a
/// `-Cmetadata`) publish side by side instead of interleaving.
fn artifact_path(tcx: TyCtxt<'_>, dir: &std::path::Path) -> PathBuf {
    let crate_name = tcx.crate_name(LOCAL_CRATE);
    let stable_id = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    dir.join(format!("{crate_name}-{stable_id:016x}{SPEC_CLEAN_FILE_SUFFIX}"))
}

/// Append one JSON line. A requested artifact that cannot be published is a
/// hard error, exactly like the other `-Ztrust-dump` sinks
/// (`publish_native_bundle_dump` precedent): silently dropping rows would
/// hand the reader a seal whose count disagrees, or worse, a clean-looking
/// truncation.
fn append_row(tcx: TyCtxt<'_>, dir: &std::path::Path, row: &serde_json::Value) {
    std::fs::create_dir_all(dir).unwrap_or_else(|error| {
        tcx.dcx().fatal(format!(
            "failed to create trust spec-clean emission directory `{}`: {error}",
            dir.display()
        ))
    });
    let path = artifact_path(tcx, dir);
    let mut file =
        std::fs::OpenOptions::new().create(true).append(true).open(&path).unwrap_or_else(|error| {
            tcx.dcx().fatal(format!(
                "failed to open trust spec-clean artifact `{}`: {error}",
                path.display()
            ))
        });
    writeln!(file, "{row}").unwrap_or_else(|error| {
        tcx.dcx().fatal(format!(
            "failed to append to trust spec-clean artifact `{}`: {error}",
            path.display()
        ))
    });
}

/// Stable, reader-facing rendering of a grade verdict. Exhaustive on purpose:
/// a new `CitationVerdict` variant must decide its artifact spelling here
/// rather than inherit a lossy default.
fn verdict_fields(
    verdict: &trust_certify::clean_island::CitationVerdict,
) -> (&'static str, Option<String>) {
    use trust_certify::clean_island::CitationVerdict;
    match verdict {
        CitationVerdict::KernelStatementMatchCertified => ("certified", None),
        CitationVerdict::KernelStatementMatchTrusted { closure } => {
            ("trusted", Some(closure.join(", ")))
        }
        CitationVerdict::SessionTainted => ("session-tainted", None),
        CitationVerdict::TheoremNotFound => ("theorem-not-found", None),
        CitationVerdict::DeclarationNotTheorem { kind } => {
            ("declaration-not-theorem", Some(kind.clone()))
        }
        CitationVerdict::UnsafeTheorem => ("unsafe-theorem", None),
        CitationVerdict::PartialTheorem => ("partial-theorem", None),
        CitationVerdict::NoProofTerm => ("no-proof-term", None),
        CitationVerdict::ClauseOutsideFragment { reason } => {
            ("clause-outside-fragment", Some(reason.clone()))
        }
        CitationVerdict::StatementOrCertificationRejected { detail } => {
            ("statement-or-certification-rejected", Some(detail.clone()))
        }
    }
}

/// Trust (OR-A1, owner ruling 2026-09-27): the disclosure a goal row carries
/// when its graded goal is a CONDITIONAL one — the cited theorem was credited
/// on the under-`requires` rung. Built by the compiler from the ladder that
/// certified it, so the row prints the goal the kernel actually graded (`G1★`
/// or `G1`) rather than re-elaborating the unconditional one.
pub struct ConditionalGoalRow {
    /// `"kernel-canonical"` or `"allow-listed"`
    /// (`trust_certify::clean_island::RequiresLink::as_str`).
    pub requires_link: &'static str,
    /// Kernel `Display` of the conditional goal that certified.
    pub goal_clean: String,
    /// The carried hypotheses in BINDER order:
    /// `(binder, contract_index, canonical text, graded text)`. The graded text
    /// is the lifted `T_j` on the kernel-canonical link and the canonical text
    /// itself on the allow-listed one.
    pub hypotheses: Vec<(usize, u64, String, String)>,
}

/// The `rung`/`requires_link`/`hypotheses` members of a graded-goal row. They
/// are written on EVERY goal row so the KEY'S PRESENCE marks a post-OR-A1
/// artifact (the schema version does not move, exactly as for `view`). `rung`
/// names the goal `goal_clean` prints — `"unconditional"` for `G0` whether or
/// not its grade ran (a `session-tainted` row still describes `G0`),
/// `"under-requires"` for a credited conditional goal. The only `null` rung is
/// the preparation-refusal row, which builds no goal and writes its members
/// itself (`record_ensures_citation_preparation_refusal`).
fn rung_fields(
    conditional: Option<&ConditionalGoalRow>,
) -> (serde_json::Value, serde_json::Value, serde_json::Value) {
    match conditional {
        Some(row) => (
            serde_json::Value::from("under-requires"),
            serde_json::Value::from(row.requires_link),
            serde_json::Value::Array(
                row.hypotheses
                    .iter()
                    .map(|(binder, contract_index, canonical, graded)| {
                        serde_json::json!({
                            "binder": binder,
                            "contract_index": contract_index,
                            "canonical": canonical,
                            "graded": graded,
                        })
                    })
                    .collect(),
            ),
        ),
        None => (
            serde_json::Value::from("unconditional"),
            serde_json::Value::Null,
            serde_json::Value::Null,
        ),
    }
}

/// Publish one kernel-graded cited-ensures goal row.
///
/// Called by the discharge lanes immediately after their
/// `kernel_discharge_ensures_citation` grade call, with THE SAME argument
/// values that call received — `clause` is the post-prime-rewrite snippet,
/// `params` the filtered parameter/type pairs, `self_fn_name` the bare
/// function name, `facets` the same table. Rows are written for EVERY grade
/// verdict, not only `Certified`: the ruling's whole point is that the goal is
/// most valuable when the citation FAILED and the author needs to see the
/// proposition the kernel was actually asked to close (v7/D3).
///
/// No-op unless this session was asked to emit. Never touches results,
/// verdicts, or authorities.
#[allow(clippy::too_many_arguments)]
pub fn record_ensures_citation_goal(
    tcx: TyCtxt<'_>,
    def_path: &str,
    contract_index: u64,
    origin: &str,
    clause: &str,
    params: &[(&str, &str)],
    self_fn_name: &str,
    facets: &trust_spec_elab::FacetTable,
    theorem: &str,
    verdict: &trust_certify::clean_island::CitationVerdict,
    // Trust (nat-lift §5.6): the clause mode the grade call ran with. "Same
    // inputs as the grade call" is the property this row's honesty rests on,
    // and after the nat-lift work the mode is one of those inputs.
    inputs: &trust_spec_elab::ProofClauseInputs,
    // Trust (ref-self I1): `Some(marker)` when this goal's binders name a
    // frozen shared pointee's field VALUES — the borrow-erased E6 PARAMETER
    // VIEW. The key is written on EVERY goal row (null otherwise), so the
    // KEY'S PRESENCE — not the schema version, which does not move — is what
    // distinguishes an artifact written before this increment (no `view` key at
    // all) from one that disclosed no view (`"view": null`). A row carrying a
    // marker is graded below `Certified` (owner ruling R1, `docs/TCB.md`).
    view: Option<&str>,
    // Trust (OR-A1): `Some` when the grade this row records is a CREDITED
    // conditional one; the row then prints the conditional goal the kernel
    // graded, with its link and hypotheses, instead of re-elaborating `G0`.
    conditional: Option<&ConditionalGoalRow>,
) {
    let Some(dir) = spec_emit_destination(tcx) else {
        return;
    };
    // Same session, same entry point, same inputs as the grade call — see the
    // module docs for why this is not the rejected offline re-elaboration and
    // for the byte-identity controls that pin it. A conditional row carries the
    // goal the ladder RETURNED, which is the swap those docs ask for.
    let (goal_clean, elab_error) = match conditional {
        Some(row) => (Some(row.goal_clean.clone()), None),
        None => match trust_spec_elab::elaborate_ensures_in(
            clause,
            params,
            self_fn_name,
            facets,
            inputs,
        ) {
            Ok(elaborated) => (Some(elaborated.goal.to_string()), None),
            Err(reason) => (None, Some(reason)),
        },
    };
    let (rung, requires_link, hypotheses) = rung_fields(conditional);
    let (verdict_tag, detail) = verdict_fields(verdict);
    let row = serde_json::json!({
        "format": SPEC_CLEAN_FORMAT,
        "v": SPEC_CLEAN_VERSION,
        "row": "goal",
        "crate": tcx.crate_name(LOCAL_CRATE).to_string(),
        "session": tcx.sess.opts.unstable_opts.trust_verify_session.clone().unwrap_or_default(),
        "def_path": def_path,
        "contract_index": contract_index,
        "origin": origin,
        "clause": clause,
        "theorem": theorem,
        "goal_clean": goal_clean,
        "elab_error": elab_error,
        "verdict": verdict_tag,
        "detail": detail,
        "view": view,
        "rung": rung,
        "requires_link": requires_link,
        "hypotheses": hypotheses,
    });
    append_row(tcx, &dir, &row);
    GOAL_ROWS_WRITTEN.fetch_add(1, Ordering::Relaxed);
}

/// Publish one counted cited-clause preparation refusal.
///
/// This is the honest fallback when neither the authored span nor the
/// compiler-query predicate retains usable clause text. No elaborator or
/// kernel grade ran, so both proposition fields are null/refusal-shaped and
/// the closed verdict says only that the clause is outside the gradeable
/// fragment. Keeping `detail == elab_error` gives the strict reader one
/// unambiguous explanation rather than two independently mutable stories.
pub fn record_ensures_citation_preparation_refusal(
    tcx: TyCtxt<'_>,
    def_path: &str,
    contract_index: u64,
    origin: &str,
    theorem: &str,
    reason: &str,
) {
    let Some(dir) = spec_emit_destination(tcx) else {
        return;
    };
    let row = serde_json::json!({
        "format": SPEC_CLEAN_FORMAT,
        "v": SPEC_CLEAN_VERSION,
        "row": "goal",
        "crate": tcx.crate_name(LOCAL_CRATE).to_string(),
        "session": tcx.sess.opts.unstable_opts.trust_verify_session.clone().unwrap_or_default(),
        "def_path": def_path,
        "contract_index": contract_index,
        "origin": origin,
        "clause": serde_json::Value::Null,
        "theorem": theorem,
        "goal_clean": serde_json::Value::Null,
        "elab_error": reason,
        "verdict": "clause-outside-fragment",
        "detail": reason,
        // Trust (ref-self I1): no grade ran, so nothing rests on a view.
        "view": serde_json::Value::Null,
        // Trust (OR-A1): no goal was built, so the row describes no rung.
        "rung": serde_json::Value::Null,
        "requires_link": serde_json::Value::Null,
        "hypotheses": serde_json::Value::Null,
    });
    append_row(tcx, &dir, &row);
    GOAL_ROWS_WRITTEN.fetch_add(1, Ordering::Relaxed);
}

/// Publish one zero-authority canonical clause denotation.
///
/// `goal` is computed by the completed compiler verification session from its
/// query-owned typed predicate. This writer never parses source and never
/// decides whether a clause is admissible. A refusal remains a row with a null
/// `goal_clean`, so unsupported compatibility syntax cannot disappear from the
/// inventory. The fixed `authority`/`verdict` labels are deliberately not
/// parameters: no caller can promote a denotation through this API.
#[allow(clippy::too_many_arguments)]
pub fn record_uncited_contract_denotation(
    tcx: TyCtxt<'_>,
    def_path: &str,
    contract_index: u64,
    kind: &str,
    source: &str,
    clause: Option<&str>,
    goal: Result<String, String>,
    // Trust (ref-self I1): this ZERO-AUTHORITY population needs the disclosure
    // too. A frozen shared parameter contributes `self.<field>` clause binders,
    // so an uncited `ensures self.x <= 5` on a `&self` method prints an
    // elaborated proposition whose binders name pointee values at entry — which
    // rests on owner ruling R1 exactly as a graded row does. The row grants
    // nothing (`authority: "none"`, `verdict: "ungraded"`), and that is
    // precisely why the marker must be on it: a reader who greps spec-clean for
    // `"view"` must not have to know which populations disclose and which do
    // not.
    view: Option<&str>,
) {
    let Some(dir) = spec_emit_destination(tcx) else {
        return;
    };
    let (goal_clean, elab_error) = match goal {
        Ok(goal) => (Some(goal), None),
        Err(reason) => (None, Some(reason)),
    };
    let row = serde_json::json!({
        "format": SPEC_CLEAN_FORMAT,
        "v": SPEC_CLEAN_VERSION,
        "row": "denotation",
        "crate": tcx.crate_name(LOCAL_CRATE).to_string(),
        "session": tcx.sess.opts.unstable_opts.trust_verify_session.clone().unwrap_or_default(),
        "def_path": def_path,
        "contract_index": contract_index,
        "kind": kind,
        "source": source,
        "clause": clause,
        "goal_clean": goal_clean,
        "elab_error": elab_error,
        "authority": "none",
        "verdict": "ungraded",
        "view": view,
    });
    append_row(tcx, &dir, &row);
    DENOTATION_ROWS_WRITTEN.fetch_add(1, Ordering::Relaxed);
}

/// Seal the session artifact. Called once, at the tail of
/// `trust_ensure_whole_crate_verification`'s ENABLED path — after the eager
/// walk, the post-walk deferred-citation adjudication, and the transport
/// summary — so a seal row is present exactly when a verification session ran
/// to completion with emission requested. The `-Ztrust-verify=off` early
/// return never reaches this, which is what lets the reader treat "no seal"
/// as "no live verification session", fail closed, and say so.
///
/// No-op unless this session was asked to emit.
pub fn seal_session(tcx: TyCtxt<'_>) {
    let Some(dir) = spec_emit_destination(tcx) else {
        return;
    };
    let row = serde_json::json!({
        "format": SPEC_CLEAN_FORMAT,
        "v": SPEC_CLEAN_VERSION,
        "row": "session",
        "crate": tcx.crate_name(LOCAL_CRATE).to_string(),
        "session": tcx.sess.opts.unstable_opts.trust_verify_session.clone().unwrap_or_default(),
        "goals": GOAL_ROWS_WRITTEN.load(Ordering::Relaxed),
        "denotations": DENOTATION_ROWS_WRITTEN.load(Ordering::Relaxed),
    });
    append_row(tcx, &dir, &row);
}
