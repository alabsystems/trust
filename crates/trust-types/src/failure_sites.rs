// trust-types/failure_sites.rs: distinct-site accounting for refuted rows
//
// One MIR `Assert` terminator (an overflow, bounds, division or negation
// check) under the `unix_hardened` profile yields TWO obligations at the same
// source span:
//
//   * the L0 safety row (`arithmetic_overflow_add`, `index_out_of_bounds`, …)
//     minted by the per-statement lane — "the operation is in range";
//   * the hardened `PanicBoundary` twin (`hardened_panic_boundary`, callee
//     `mir_assert::<msg>`) minted by `trust-vcgen::hardened` — "the panic
//     this assert raises is unreachable".
//
// They are DISTINCT obligations, not a duplicate: the L0 row may be
// discharged by the surviving runtime check (`RuntimeChecked`), while the
// hardened row never can (`a_hardened_panic_boundary_is_never_downgraded_to_
// runtime_checked`), and the two lanes carry different hypothesis sets, so
// either may fail while the other proves. Both rows stay, and both stay in
// `failed`. What a reader could not see is that two failed rows are one
// refuted site; this module makes that relationship explicit.
//
// The module holds no assert-family mapping of its own: the caller classifies
// each row with the one classifier the subsumption pass already uses (targo's
// `PanicTwinFamily`), and this module applies the same unambiguous one-to-one
// rule that pass applies.
//
// It is ACCOUNTING ONLY. Nothing here feeds a gate decision, an exit code, a
// verdict, or a proof grade, and nothing here removes a row.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::{SourceSpan, VcKind};

/// Which side of a MIR-assert pair a row is on. The caller classifies; this
/// module only applies the one-to-one rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TwinRole {
    /// A hardened `PanicBoundary` twin (`mir_assert::<msg>`).
    HardenedTwin,
    /// The per-statement L0 safety row of the same assert family.
    L0Primary,
}

/// One row of the run, as the accounting sees it. Callers pass EVERY row, not
/// only the failed ones: whether a twin pairing is unambiguous depends on the
/// rows at its key that did NOT fail too.
#[derive(Debug, Clone)]
pub struct SiteRowView<'a> {
    /// The row's function identity (sites never merge across functions).
    pub function: &'a str,
    /// Stable obligation id, when the row has one. Rows sharing a non-empty id
    /// are renderings of one obligation; a row without one is its own.
    pub obligation_id: Option<&'a str>,
    /// The row's exact typed kind (for the link's labels only).
    pub kind: &'a VcKind,
    /// The row's source span. A row without one is its own site.
    pub location: Option<&'a SourceSpan>,
    /// Whether the caller's gate partition counts this row in `failed`. Only
    /// these rows are counted, so `failed_rows` reconciles with `counts.failed`.
    pub failed: bool,
    /// The MIR-assert pairing role and family key, from the CALLER's single
    /// classifier (targo's `PanicTwinFamily`, the one
    /// `subsume_hardened_panic_twins` keys on). `None` for every other row.
    pub twin_pairing: Option<(TwinRole, String)>,
}

/// Distinct-site accounting over a run's refuted rows, recorded on the
/// verification gate as `failure_sites`. Informational: `counts.failed` stays
/// the row count and the only number any gate decision reads.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailureSiteAccounting {
    /// Failed rows (equals the gate's `counts.failed`).
    pub failed_rows: usize,
    /// Distinct `(function, exact source span)` sites among those rows; a row
    /// without a span counts as its own site.
    pub distinct_sites: usize,
    /// Failed hardened `PanicBoundary` twins linked one-to-one, in
    /// `twin_links`, to a failed L0 safety row of the same operation at the same
    /// site. `failed_rows - hardened_twin_rows` is the failed-row count with
    /// every such pair read as one refuted site.
    pub hardened_twin_rows: usize,
    /// One entry per linked pair.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub twin_links: Vec<FailureTwinLink>,
}

/// A failed L0 safety row and the failed hardened panic-boundary twin paired
/// with it: the same function, a byte-identical span, the same assert
/// operation, and no other candidate on either side at that key. Spans are
/// resolved per call site, so this is a same-span, same-operation pairing, not
/// proof that both rows come from one assert. Both rows are still reported and
/// both are still failed.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FailureTwinLink {
    /// The function both rows belong to.
    pub function: String,
    /// The shared exact source span.
    pub location: SourceSpan,
    /// The L0 row's report kind tag (e.g. `arithmetic_overflow_add`).
    pub primary_kind: String,
    /// The L0 row's obligation id, when it has one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub primary_obligation_id: Option<String>,
    /// The twin's hardened callee (e.g. `mir_assert::Overflow(Add)`).
    pub hardened_callee: String,
    /// The twin's obligation id, when it has one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hardened_obligation_id: Option<String>,
}

impl FailureSiteAccounting {
    /// Whether the site view says anything the row count does not.
    #[must_use]
    pub fn differs_from_row_count(&self) -> bool {
        self.distinct_sites != self.failed_rows || self.hardened_twin_rows > 0
    }

    /// The one-line human rendering, or `None` when there is no failed row.
    #[must_use]
    pub fn terminal_line(&self) -> Option<String> {
        if self.failed_rows == 0 {
            return None;
        }
        Some(format!(
            "Failed sites: {} failed row(s) at {} distinct source site(s); {} row(s) are hardened \
             panic-boundary twins of a failed overflow/bounds row at the same MIR assert (distinct \
             obligations: panic-freedom vs. L0 safety; both stay failed)",
            self.failed_rows, self.distinct_sites, self.hardened_twin_rows
        ))
    }
}

fn kind_tag(kind: &VcKind) -> String {
    crate::annotation::vc_kind_tag(kind)
}

fn hardened_callee(kind: &VcKind) -> String {
    match kind {
        VcKind::HardenedBoundary { callee, .. } => callee.clone(),
        other => kind_tag(other),
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum RowIdentity<'a> {
    Obligation(&'a str),
    Row(usize),
}

/// Every rendering of one candidate obligation at a pairing key.
#[derive(Clone, Copy)]
struct Candidate {
    first_row: usize,
    all_failed: bool,
}

#[derive(Default)]
struct PairingGroup<'a> {
    twins: HashMap<RowIdentity<'a>, Candidate>,
    primaries: HashMap<RowIdentity<'a>, Candidate>,
}

/// Account the distinct sites of a run's failed rows and link each failed
/// MIR-assert panic-boundary twin to the failed L0 row it pairs with.
///
/// The pairing rule is the one `subsume_hardened_panic_twins` applies: same
/// function, byte-identical span, the same family key from the caller's
/// classifier, and EXACTLY ONE twin obligation and ONE primary obligation at
/// that key across ALL rows, whatever their outcome. More than one candidate on
/// either side is ambiguous (two asserts expanded from one macro call site
/// share a span) and links nothing. A link also requires every rendering of
/// both obligations to have failed. Ambiguity leaves both rows unlinked and
/// counted, which is the over-count direction.
#[must_use]
pub fn account_failure_sites<'a>(
    rows: impl IntoIterator<Item = SiteRowView<'a>>,
) -> FailureSiteAccounting {
    let rows: Vec<SiteRowView<'a>> = rows.into_iter().collect();

    let mut failed_rows = 0usize;
    let mut sites: HashSet<(&str, &SourceSpan)> = HashSet::new();
    let mut unlocated = 0usize;
    // Pairing groups in first-seen row order, so `twin_links` is deterministic.
    let mut group_index: HashMap<(&str, &SourceSpan, &str), usize> = HashMap::new();
    let mut groups: Vec<PairingGroup<'a>> = Vec::new();

    for (index, row) in rows.iter().enumerate() {
        if row.failed {
            failed_rows += 1;
            match row.location {
                Some(span) => {
                    sites.insert((row.function, span));
                }
                None => unlocated += 1,
            }
        }
        let (Some(span), Some((role, family))) = (row.location, row.twin_pairing.as_ref()) else {
            continue;
        };
        let slot = *group_index.entry((row.function, span, family.as_str())).or_insert_with(|| {
            groups.push(PairingGroup::default());
            groups.len() - 1
        });
        let identity = match row.obligation_id.filter(|id| !id.trim().is_empty()) {
            Some(id) => RowIdentity::Obligation(id),
            None => RowIdentity::Row(index),
        };
        let side = match role {
            TwinRole::HardenedTwin => &mut groups[slot].twins,
            TwinRole::L0Primary => &mut groups[slot].primaries,
        };
        side.entry(identity)
            .and_modify(|candidate| candidate.all_failed &= row.failed)
            .or_insert(Candidate { first_row: index, all_failed: row.failed });
    }

    let mut twin_links = Vec::new();
    for group in &groups {
        if group.twins.len() != 1 || group.primaries.len() != 1 {
            continue;
        }
        let (Some(twin), Some(primary)) =
            (group.twins.values().next(), group.primaries.values().next())
        else {
            continue;
        };
        if !twin.all_failed || !primary.all_failed {
            continue;
        }
        let (twin_row, primary_row) = (&rows[twin.first_row], &rows[primary.first_row]);
        let Some(span) = twin_row.location else {
            continue;
        };
        twin_links.push(FailureTwinLink {
            function: twin_row.function.to_string(),
            location: span.clone(),
            primary_kind: kind_tag(primary_row.kind),
            primary_obligation_id: primary_row.obligation_id.map(str::to_string),
            hardened_callee: hardened_callee(twin_row.kind),
            hardened_obligation_id: twin_row.obligation_id.map(str::to_string),
        });
    }

    FailureSiteAccounting {
        failed_rows,
        distinct_sites: sites.len() + unlocated,
        hardened_twin_rows: twin_links.len(),
        twin_links,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinOp, HardenedVcCategory, Ty};

    fn span(line: u32, col: u32) -> SourceSpan {
        SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: line,
            col_start: col,
            line_end: line,
            col_end: col + 5,
        }
    }

    fn add() -> VcKind {
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::u32(), Ty::u32()) }
    }

    fn twin(msg: &str) -> VcKind {
        VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: format!("mir_assert::{msg}"),
            detail: "MIR arithmetic assert can panic".to_string(),
        }
    }

    fn pair(role: TwinRole, family: &str) -> Option<(TwinRole, String)> {
        Some((role, family.to_string()))
    }

    fn row<'a>(
        id: &'a str,
        kind: &'a VcKind,
        at: Option<&'a SourceSpan>,
        failed: bool,
        twin_pairing: Option<(TwinRole, String)>,
    ) -> SiteRowView<'a> {
        SiteRowView {
            function: "f",
            obligation_id: Some(id),
            kind,
            location: at,
            failed,
            twin_pairing,
        }
    }

    fn primary<'a>(
        id: &'a str,
        kind: &'a VcKind,
        at: &'a SourceSpan,
        failed: bool,
    ) -> SiteRowView<'a> {
        row(id, kind, Some(at), failed, pair(TwinRole::L0Primary, "add"))
    }

    fn hardened<'a>(
        id: &'a str,
        kind: &'a VcKind,
        at: &'a SourceSpan,
        failed: bool,
    ) -> SiteRowView<'a> {
        row(id, kind, Some(at), failed, pair(TwinRole::HardenedTwin, "add"))
    }

    /// The survey shape (astream-wire `subject.rs:21`): one refuted `+` is an
    /// overflow row AND its panic-boundary twin. Both rows are counted; the
    /// accounting names them as one site and links them.
    #[test]
    fn a_failed_overflow_and_its_hardened_twin_are_one_site_and_two_rows() {
        let (a, t, s) = (add(), twin("Overflow(Add)"), span(21, 43));
        let acc = account_failure_sites([primary("p", &a, &s, true), hardened("h", &t, &s, true)]);
        assert_eq!(acc.failed_rows, 2, "both rows stay failed");
        assert_eq!(acc.distinct_sites, 1);
        assert_eq!(acc.hardened_twin_rows, 1);
        assert_eq!(acc.twin_links.len(), 1);
        let link = &acc.twin_links[0];
        assert_eq!(link.primary_kind, "arithmetic_overflow_add");
        assert_eq!(link.primary_obligation_id.as_deref(), Some("p"));
        assert_eq!(link.hardened_callee, "mir_assert::Overflow(Add)");
        assert_eq!(link.hardened_obligation_id.as_deref(), Some("h"));
        assert!(acc.differs_from_row_count());
    }

    /// A twin whose primary did NOT fail (proved, or runtime-checked under
    /// overflow checks) is a failure in its own right — the panic is
    /// reachable — and is never linked away. Nor is a twin with no primary.
    #[test]
    fn a_twin_without_a_failed_primary_is_its_own_unlinked_site() {
        let (a, t, s) = (add(), twin("Overflow(Add)"), span(5, 5));
        let alone = FailureSiteAccounting {
            failed_rows: 1,
            distinct_sites: 1,
            hardened_twin_rows: 0,
            twin_links: vec![],
        };
        let acc = account_failure_sites([primary("p", &a, &s, false), hardened("h", &t, &s, true)]);
        assert_eq!(acc, alone);
        assert!(!acc.differs_from_row_count());
        assert_eq!(account_failure_sites([hardened("h", &t, &s, true)]), alone);
        // And the converse: a failed L0 row whose twin proved stands alone.
        let acc = account_failure_sites([primary("p", &a, &s, true), hardened("h", &t, &s, false)]);
        assert_eq!(acc, alone);
    }

    #[test]
    fn pairing_never_crosses_a_span_a_function_or_a_family() {
        let (a, t) = (add(), twin("Overflow(Add)"));
        let (s1, s2) = (span(1, 1), span(1, 2));
        let acc =
            account_failure_sites([primary("p", &a, &s1, true), hardened("h", &t, &s2, true)]);
        assert_eq!((acc.distinct_sites, acc.hardened_twin_rows), (2, 0));
        let mut other_fn = hardened("h", &t, &s1, true);
        other_fn.function = "g";
        let acc = account_failure_sites([primary("p", &a, &s1, true), other_fn]);
        assert_eq!((acc.distinct_sites, acc.hardened_twin_rows), (2, 0));
        let acc = account_failure_sites([
            primary("p", &a, &s1, true),
            row("h", &t, Some(&s1), true, pair(TwinRole::HardenedTwin, "mul")),
        ]);
        assert_eq!((acc.distinct_sites, acc.hardened_twin_rows), (1, 0));
    }

    /// Review defect 1 (2026-10-02): two asserts of one operation expanded from
    /// one macro call site share a span. A: L0 proved, twin failed. B: L0
    /// failed, twin proved. Two refuted asserts, so nothing links — the
    /// ambiguity is visible only from the rows that did NOT fail.
    #[test]
    fn twins_of_different_asserts_at_one_span_are_never_linked() {
        let (a, t, s) = (add(), twin("Overflow(Add)"), span(7, 3));
        let acc = account_failure_sites([
            primary("a0", &a, &s, false),
            hardened("a1", &t, &s, true),
            primary("b0", &a, &s, true),
            hardened("b1", &t, &s, false),
        ]);
        assert_eq!((acc.failed_rows, acc.distinct_sites, acc.hardened_twin_rows), (2, 1, 0));
    }

    /// Two distinct bounds checks can share one span (measured: astream-wire
    /// `hash.rs:38:8-21`, two `index_out_of_bounds` rows with different
    /// counterexamples). More than one candidate on either side is ambiguous:
    /// nothing links, every row stays counted.
    #[test]
    fn more_than_one_candidate_on_either_side_links_nothing() {
        let (b, t, s) = (VcKind::IndexOutOfBounds, twin("BoundsCheck"), span(38, 8));
        let acc = account_failure_sites([
            primary("b1", &b, &s, true),
            primary("b2", &b, &s, true),
            hardened("h", &t, &s, true),
        ]);
        assert_eq!((acc.failed_rows, acc.distinct_sites, acc.hardened_twin_rows), (3, 1, 0));
        let acc = account_failure_sites([
            primary("b", &b, &s, true),
            hardened("h1", &t, &s, true),
            hardened("h2", &t, &s, true),
        ]);
        assert_eq!((acc.failed_rows, acc.distinct_sites, acc.hardened_twin_rows), (3, 1, 0));
    }

    /// Repeated renderings of one obligation id are one candidate, as in the
    /// subsumption pass; the link then needs EVERY rendering to have failed.
    /// Rows without an id are each a distinct candidate.
    #[test]
    fn renderings_of_one_obligation_are_one_candidate() {
        let (a, t, s) = (add(), twin("Overflow(Add)"), span(2, 2));
        let acc = account_failure_sites([
            primary("p", &a, &s, true),
            primary("p", &a, &s, true),
            hardened("h", &t, &s, true),
        ]);
        assert_eq!((acc.failed_rows, acc.hardened_twin_rows), (3, 1));
        let acc = account_failure_sites([
            primary("p", &a, &s, true),
            primary("p", &a, &s, false),
            hardened("h", &t, &s, true),
        ]);
        assert_eq!((acc.failed_rows, acc.hardened_twin_rows), (2, 0));
        // Blank ids are no identity: two such rows are two candidates.
        let acc = account_failure_sites([
            primary(" ", &a, &s, true),
            primary(" ", &a, &s, true),
            hardened("h", &t, &s, true),
        ]);
        assert_eq!(acc.hardened_twin_rows, 0);
        let mut x = primary("", &a, &s, true);
        x.obligation_id = None;
        let mut y = primary("", &a, &s, true);
        y.obligation_id = None;
        let acc = account_failure_sites([x, y, hardened("h", &t, &s, true)]);
        assert_eq!(acc.hardened_twin_rows, 0);
    }

    /// Rows the caller gives no pairing role never pair; rows without a span
    /// are each their own site and never pair.
    #[test]
    fn unclassified_rows_never_pair_and_unlocated_rows_never_merge() {
        let s = span(9, 9);
        let unwrap = VcKind::HardenedBoundary {
            category: HardenedVcCategory::PanicBoundary,
            callee: "std::option::Option::<T>::unwrap".to_string(),
            detail: String::new(),
        };
        let a = add();
        let t = twin("Overflow(Add)");
        let acc = account_failure_sites([
            primary("p", &a, &s, true),
            row("u", &unwrap, Some(&s), true, None),
            row("x", &a, None, true, pair(TwinRole::L0Primary, "add")),
            row("y", &t, None, true, pair(TwinRole::HardenedTwin, "add")),
        ]);
        assert_eq!(acc.failed_rows, 4);
        assert_eq!(acc.distinct_sites, 3);
        assert_eq!(acc.hardened_twin_rows, 0);
    }

    #[test]
    fn no_failed_rows_renders_nothing() {
        let acc = account_failure_sites(std::iter::empty());
        assert_eq!(acc, FailureSiteAccounting::default());
        assert!(acc.terminal_line().is_none());
        let (a, s) = (add(), span(1, 1));
        let acc = account_failure_sites([primary("p", &a, &s, false)]);
        assert_eq!(acc, FailureSiteAccounting::default());
    }

    #[test]
    fn accounting_serde_round_trips_and_omits_empty_links() {
        let acc = FailureSiteAccounting {
            failed_rows: 1,
            distinct_sites: 1,
            hardened_twin_rows: 0,
            twin_links: vec![],
        };
        let json = serde_json::to_string(&acc).unwrap();
        assert!(!json.contains("twin_links"));
        let back: FailureSiteAccounting = serde_json::from_str(&json).unwrap();
        assert_eq!(back, acc);
    }
}
