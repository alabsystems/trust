//! Trust (T3 C05, 2026-10-11): the proven-overflow-check elision audit.
//!
//! `TRUST_ELIDE_AUDIT=<dir>` appends tab-separated rows to `<dir>/elide-audit-<pid>.tsv`,
//! one file per compiler process, so the `.stderr` a UI test compares is untouched and
//! parallel compiles never share a file. Unset or empty, nothing is computed or written.
//!
//! Every row starts with the same five columns, which name the function across two
//! compilers built from different commits: the row kind, the input file's stem, the
//! leaf of the output directory (compiletest gives each revision its own), the crate
//! name, and the function's def path. Then:
//!
//! * `ELIDED  ... bb<N>  <op>  <location>  <key>` — one per overflow `Assert` that
//!   `elide_kernel_certified_checks` rewrote to a `Goto`. `<location>` is the certified
//!   row's span and `<key>` the digest of its exact identity ([`key_digest`]). The
//!   multiset of these rows is the elided-Assert set the T3 L3 gate compares against
//!   the parent.
//! * `KEPT  ... <reason>  <op>  <location>  <key>` — one per Add/Sub/Mul overflow row of
//!   the function's results that the seam did not elide, with the first gate that kept
//!   it: `uncertified` (no `KernelCertified` authority), `stale` (the authority does not
//!   re-bind to the row), `absent` (the origin table has no entry for the key),
//!   `ambiguous` (two blocks produced it), `statement` (only an arithmetic statement
//!   produced it, never an overflow `Assert`; since C05's site tagging), `moved` (the
//!   origin block no longer ends in that `Assert`) or `twin` (the hardened twin is not
//!   proved). A block one compiler elides and the other keeps is attributed by the
//!   `<key>` the two rows share.
//! * `ORIGINS ... <source>  <state>  unique=<u>  ambiguous=<a>` — one per function whose
//!   origin table was built, saying where it came from and whether it is complete. A
//!   function whose table is not complete elides nothing.
//! * `VERDICT ... <obligation key>  <status>  <stop>  <kind>  <location>  <audit key>` —
//!   one per published obligation row, in either output mode: the T9 stable key
//!   (`<def path>#<local id>`, `-` when the function's ids could not be minted), the
//!   published status and its `StopCause::of_outcome`. The sorted multiset of
//!   `(key, status, stop)` is the verdict vector `measure_ever_init_ladder.py` and
//!   targo-trust compute from the `TRUST_JSON` transport; kind and location only help a
//!   reader attribute a row. The sixth column (T3 L4, C06a; L4-AUDIT-8) is the AUDIT KEY:
//!   T9's key minted over the rows' descriptions as
//!   `trust_types::audit_ledger::build_independent` spells them, so that a row whose
//!   description renders a build's crate identities (and T9 anchors a row with no span on
//!   its description) has one key under the compilers of two commits. Only the L4
//!   comparison reads it; the T9 key stays the published one.
//!
//!
//! T3 L4 (C06a, 2026-10-11; `docs/design/2026-10-11-t3-l4-commit-plan.md` C06a, §3.3) adds
//! the rows the native L4 differential reads (`targo trust gate compare-audit --l4`):
//!
//! * `ROWDIGEST ... <index>  <kind tag>  <location>  <sha256>` — one per row of the
//!   function's `artifacts.results`, written at the publication seam beside `VERDICT`:
//!   the row's index, `VcKind::transport_tag`, its span, and the full SHA-256 of
//!   `canonical_exact_vc_payload` of the row's VC (`-` when it has none), as
//!   `trust_types::audit_ledger::build_independent` spells the function's payloads: every
//!   crate identity renamed by first appearance across the function, a `dyn` type's
//!   hash-ordered predicates put in path order, and the SC-8 disclosure reduced to its
//!   count of causes (L4-AUDIT-7: a crate's `StableCrateId` hashes the compiler's version,
//!   so two commits' compilers spell one row differently).
//!   Compared per function as a multiset of (kind tag, location, digest); the index only
//!   helps a reader. A published row with no VC (a gap, synthetic or policy row) is
//!   covered by `VERDICT` alone. The digest is not the claim digest.
//! * `STOP ... <lane>  <cause>` — each stop `trust_types::determinism::note_stop` or
//!   `note_item` recorded (the lane carries `[<item>]` for a named stop).
//! * `CERTIFY-STOP ... <index>  <cause>` — a certification run a stop reached: a run whose
//!   own work a clock or budget stopped (`trust_certify::certify_vc_reporting_stop`), or a
//!   `Proved` row `certify_all_until`'s deadline kept from the kernel (`wall-backstop`).
//! * `CAP ... <site>` — one hit of a size refusal an L4 commit deletes or moves, named by
//!   the census's `<file>:<CONSTANT>` or a named refusal.
//! * `PARITY ... <oracle>  rows=<n>  mismatches=<m>` — an L4 oracle's count for the
//!   function. The kind is defined here; from C07 on it is written once per function per
//!   oracle, always, even when `n` is 0. From C07p a crate phase whose producers run in VC
//!   contexts of their own (`crate:r1`, `crate:inferred-return`, `crate:tinv`) writes one
//!   per oracle under that label ([`record_crate_parity`]). `rows=` counts every row
//!   compared, not every distinct row: from C07r a body's results rows are compared as they
//!   join its context (again wherever a rewrite of the carrier changed or moved one,
//!   `RowResults::rewrite`) and again at the publication seam (`RowResults::check_in`), so
//!   each is counted at least twice and `rows=` is not comparable with an earlier commit's.
//!   Compare `mismatches=` across commits, and `rows=` only between runs of the same
//!   commit. From C09 the `identity` oracle (`row_key`'s docs) writes two rows when the verify
//!   pass that consumed the body's artifacts ends ([`record_identity_parity`]): `identity`,
//!   the comparisons it judged, and [`IDENTITY_SCOPE`], those it could not place in one
//!   context, whose `mismatches=` counts the bindings C11 must give one context before the
//!   identity decides there (L4-C09-7). A body whose publication waited for its E9 amendment
//!   writes a second pair, for what was counted since; what no body's pair wrote is written
//!   with the def path `crate` at the crate accounting ([`drain_crate_level`], L4-C09-6).
//!
//! STOP, CERTIFY-STOP and CAP rows come from `trust_types::audit_ledger`, which attributes
//! an entry to the innermost scope open when it was recorded (L4-SCOPE-2, that module's
//! docs). [`BodyScope`] opens a body's scope for its whole `run_pass` and writes the body's
//! rows when the pass ends; [`CrateScope`] does the same for the R1 pre-pass (`crate:r1`)
//! and crate finalization (`crate:finalize`), whose rows carry that label in the def-path
//! column; [`drain_crate_level`] writes every unattributed entry, with the def path
//! `crate`, at the crate accounting. A scope a panic unwinds writes nothing: its entries go
//! to the crate level, so the unwinding pass renders no def path and does no I/O. Nothing
//! here reads the determinism ledger it copies.
//!
//! Measurement only: it reads the verdicts and the table and writes a file. A failed
//! write loses a row, never a verdict. No verdict, key, transport byte, `.stderr` or
//! crate accounting reads anything written here.

use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use trust_types::audit_ledger::{self, AuditEntry, Scope};
use trust_types::vc_context::{Oracle, ParityCount, ParityTally, VcContext};
use trust_types::{SourceSpan, VerificationCondition, VerificationResult};

use super::row_key::Tally;

/// Whether `TRUST_ELIDE_AUDIT` names a directory. Callers check it before building a row.
pub(super) fn enabled() -> bool {
    audit_ledger::enabled()
}

/// A row's span as one column: `file:line:col-line:col`.
pub(super) fn location(span: &SourceSpan) -> String {
    format!(
        "{}:{}:{}-{}:{}",
        span.file, span.line_start, span.col_start, span.line_end, span.col_end
    )
}

/// A row's exact identity as one column: `k` and the first 16 hex digits of the SHA-256 of
/// its canonical payload (the string a `KernelCertified` row seals). Two compilers that
/// emit the same row write the same key; `k-` when the row has no canonical payload.
pub(super) fn key_digest(canonical: Option<&str>) -> String {
    match canonical {
        Some(canonical) => {
            let digest = trust_types::stable_sha256_hex(canonical.as_bytes());
            format!("k{}", digest.get(..16).unwrap_or(&digest))
        }
        None => "k-".to_string(),
    }
}

/// The full SHA-256 of a row's canonical payload, as one column (`ROWDIGEST`); `-` when the
/// row has none.
pub(super) fn full_digest(canonical: Option<&str>) -> String {
    canonical.map_or_else(
        || "-".to_string(),
        |canonical| trust_types::stable_sha256_hex(canonical.as_bytes()),
    )
}

/// The rows of `def_id`'s function, from its def path, or the def-path column `label` names
/// (a crate scope).
enum Function<'a> {
    Def(DefId),
    Label(&'a str),
}

/// Append `rows` (kind and columns) for `function`, one write per row.
fn write(tcx: TyCtxt<'_>, function: Function<'_>, rows: &[(&str, Vec<String>)]) {
    if !enabled() || rows.is_empty() {
        return;
    }
    let io = &tcx.sess.io;
    let input = io.input.filestem().to_string();
    let output = io
        .output_dir
        .as_deref()
        .and_then(|dir| dir.file_name())
        .map(|leaf| leaf.to_string_lossy().into_owned())
        .unwrap_or_else(|| "-".to_string());
    let krate = tcx.crate_name(LOCAL_CRATE).to_string();
    let function = match function {
        // A probe line is not a diagnostic: `def_path_str` without trimming, as `probe_label`.
        Function::Def(def_id) => with_no_trimmed_paths!(tcx.def_path_str(def_id)),
        Function::Label(label) => label.to_string(),
    };
    let lines: Vec<String> = rows
        .iter()
        .map(|(kind, columns)| {
            audit_ledger::row_line(kind, &[&input, &output, &krate, &function], columns)
        })
        .collect();
    // One file per compiler process; one write per row, newline included, so rows from
    // threads auditing at once cannot interleave inside a line.
    audit_ledger::append_rows(&format!("elide-audit-{}.tsv", std::process::id()), &lines);
}

/// Append one `kind` row for `def_id` with the kind's own `columns`.
pub(super) fn record(tcx: TyCtxt<'_>, def_id: DefId, kind: &str, columns: &[String]) {
    write(tcx, Function::Def(def_id), &[(kind, columns.to_vec())]);
}

fn entry_rows(entries: &[AuditEntry]) -> Vec<(&'static str, Vec<String>)> {
    entries.iter().map(|entry| (entry.kind(), entry.columns())).collect()
}

/// One `ROWDIGEST` row per row of `def_id`'s results (module docs).
pub(super) fn record_row_digests(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    results: &[(VerificationCondition, VerificationResult)],
    canonical: impl Fn(&VerificationCondition) -> Option<String>,
) {
    if !enabled() {
        return;
    }
    let payloads: Vec<Option<String>> = results.iter().map(|(vc, _)| canonical(vc)).collect();
    // One function's payloads, spelled as a whole (module docs; L4-AUDIT-7).
    let mut spelled = audit_ledger::build_independent(
        &payloads.iter().flatten().map(String::as_str).collect::<Vec<_>>(),
    )
    .into_iter();
    let rows: Vec<(&str, Vec<String>)> = results
        .iter()
        .zip(&payloads)
        .enumerate()
        .map(|(index, ((vc, _), payload))| {
            let spelled = payload.as_ref().and_then(|_| spelled.next());
            (
                "ROWDIGEST",
                vec![
                    index.to_string(),
                    vc.kind.transport_tag(),
                    location(&vc.location),
                    full_digest(spelled.as_deref()),
                ],
            )
        })
        .collect();
    write(tcx, Function::Def(def_id), &rows);
}

/// One `PARITY` row per oracle of `oracles` for `def_id`'s function, from its body's
/// context `rows` (module docs; T3 L4, C07): written always, even when the count is 0.
pub(super) fn record_parity(tcx: TyCtxt<'_>, def_id: DefId, rows: &VcContext, oracles: &[Oracle]) {
    if !enabled() {
        return;
    }
    let counts = oracles.iter().map(|&oracle| (oracle.as_str(), rows.parity(oracle)));
    write(tcx, Function::Def(def_id), &parity_rows(counts));
}

/// The `PARITY` label of the comparisons the identity oracle could not judge (module docs;
/// `row_key`'s, TWO CLASSES; T3 L4, C09, L4-C09-7). It is no oracle's: the comparator lists
/// its mismatches and fails none of them.
pub(super) const IDENTITY_SCOPE: &str = "identity-scope";

/// The identity oracle's two `PARITY` rows, from `tally`: `identity`, what it judged, and
/// [`IDENTITY_SCOPE`], what it could not judge.
fn identity_rows(tally: Tally) -> Vec<(&'static str, Vec<String>)> {
    parity_rows([(Oracle::Identity.as_str(), tally.judged), (IDENTITY_SCOPE, tally.unjudged)])
}

/// The identity oracle's two `PARITY` rows for `def_id`'s function, from `tally` (T3 L4, C09):
/// the oracle counts in the body's oracle context (`row_key::Installed`), not in the body's
/// VC context, and writes when the pass that consumed the body's artifacts ends.
pub(super) fn record_identity_parity(tcx: TyCtxt<'_>, def_id: DefId, tally: Tally) {
    if !enabled() {
        return;
    }
    write(tcx, Function::Def(def_id), &identity_rows(tally));
}

/// One `PARITY` row per oracle of `oracles` for the crate phase `label` (`crate:r1`), from
/// `tally`, the summed counts of the short-lived VC contexts that phase ran and dropped
/// (T3 L4, C07p): written always, even when the count is 0. The def-path column is the
/// label, as a crate scope's rows carry it ([`CrateScope`]); writing it opens no scope.
pub(super) fn record_crate_parity(
    tcx: TyCtxt<'_>,
    label: &str,
    tally: &ParityTally,
    oracles: &[Oracle],
) {
    if !enabled() {
        return;
    }
    let counts = oracles.iter().map(|&oracle| (oracle.as_str(), tally.get(oracle)));
    write(tcx, Function::Label(label), &parity_rows(counts));
}

/// The `PARITY` rows of `counts`: `<oracle>  rows=<n>  mismatches=<m>`.
fn parity_rows(
    counts: impl IntoIterator<Item = (&'static str, ParityCount)>,
) -> Vec<(&'static str, Vec<String>)> {
    counts
        .into_iter()
        .map(|(oracle, count)| {
            (
                "PARITY",
                vec![
                    oracle.to_string(),
                    format!("rows={}", count.rows),
                    format!("mismatches={}", count.mismatches),
                ],
            )
        })
        .collect()
}

/// A body's audit scope for its whole pass (module docs): when it ends, the entries
/// attributed to it become the body's STOP, CERTIFY-STOP and CAP rows.
pub(super) struct BodyScope<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    scope: Option<Scope<'static>>,
}

impl<'tcx> BodyScope<'tcx> {
    /// Open `def_id`'s scope; nothing is opened when the audit is disabled.
    pub(super) fn enter(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        BodyScope { tcx, def_id, scope: Scope::enter("body") }
    }
}

impl Drop for BodyScope<'_> {
    fn drop(&mut self) {
        if let Some(scope) = self.scope.take() {
            // Unwinding: the scope's own drop hands its entries to the crate level
            // (module docs).
            if std::thread::panicking() {
                return;
            }
            let entries = scope.finish();
            write(self.tcx, Function::Def(self.def_id), &entry_rows(&entries));
        }
    }
}

/// A crate phase's audit scope (`crate:r1`, `crate:finalize`; module docs).
pub(super) struct CrateScope<'tcx> {
    tcx: TyCtxt<'tcx>,
    scope: Option<Scope<'static>>,
}

impl<'tcx> CrateScope<'tcx> {
    /// Open the scope `label`; nothing is opened when the audit is disabled.
    pub(super) fn enter(tcx: TyCtxt<'tcx>, label: &str) -> Self {
        CrateScope { tcx, scope: Scope::enter(label) }
    }
}

impl Drop for CrateScope<'_> {
    fn drop(&mut self) {
        if let Some(scope) = self.scope.take() {
            if std::thread::panicking() {
                return;
            }
            let label = scope.label().to_string();
            let entries = scope.finish();
            write(self.tcx, Function::Label(&label), &entry_rows(&entries));
        }
    }
}

/// Write every crate-level entry recorded so far (def path `crate`). Called with the crate
/// accounting; an entry recorded after it is not written. With them, always, the identity
/// oracle's two crate rows: what it counted and no body's rows wrote (T3 L4, C09; L4-C09-6).
pub(super) fn drain_crate_level(tcx: TyCtxt<'_>) {
    if !enabled() {
        return;
    }
    let entries = audit_ledger::take_crate_level();
    let mut rows = entry_rows(&entries);
    rows.extend(identity_rows(super::row_key::take_crate_level()));
    write(tcx, Function::Label("crate"), &rows);
}
