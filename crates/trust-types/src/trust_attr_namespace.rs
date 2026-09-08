// trust-types/trust_attr_namespace.rs: the reserved `trust::` attribute vocabulary
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
//! E5 CONSERVATION — the reserved `trust::` attribute namespace.
//!
//! # The defect this closes
//!
//! `trust` is registered as a rustc TOOL namespace (`#![register_tool(trust)]`).
//! Tool attributes are INERT in rustc: once the tool module resolves, nothing
//! validates the name after it. Measured on the sealed toolchain `trust-e26541e3`:
//!
//! ```text
//! #[trust::totally_made_up_clause(whatever @@ nonsense)]
//! pub fn add(a: u32, b: u32) -> u32 { a.wrapping_add(b) }
//! ```
//!
//! compiles with ZERO diagnostics under `-Ztrust-verify=on`, and its verification
//! ledger is identical — row for row, solver for solver — to the same file with no
//! attribute at all. So does `#[trust::assume_totall]`, one keystroke away from a
//! real annotation. The author believes a property was stated and checked; nothing
//! was stated and nothing was checked. That is the fake-proof class, reached
//! without writing a single false predicate.
//!
//! # The rule (campaign amendment E5)
//!
//! Any attribute in the reserved `trust::` namespace that **no consumer claims** is
//! a HARD ERROR naming the attribute. Never silence.
//!
//! # How this table was derived, and why the direction matters
//!
//! The vocabulary below is enumerated from the code that CONSUMES each name, not
//! from a grep of usage. That direction is load-bearing, and skipping it was
//! measured to be a real mistake rather than a theoretical one: an earlier draft of
//! this table listed the seventeen names that appear as exact `[trust, name]` path
//! matches, and would therefore have REJECTED six spellings that a real program can
//! write today and that the compiler really reads —
//!
//! ```text
//! contracts_requires  trust_requires
//! contracts_ensures   trust_ensures
//!                     trust_invariant
//!                     trust_decreases
//! ```
//!
//! — because their consumer, `contract_kind_from_name` in
//! `crates/trust-mir-extract/src/lib.rs`, keys on `attr.path().last()` and so never
//! mentions the `trust` namespace at all. Measured on the sealed toolchain:
//! `#[trust::contracts_requires(a > 0)]` produces a real lowered precondition
//! obligation row, while `#[trust::totally_made_up_clause(..)]` beside it produces
//! `no_obligations`. Every row here therefore carries the consumer that reads it,
//! by file and function. If you add a `trust::` attribute anywhere in the compiler,
//! add its row here in the same commit — `consumer` is the justification, not a
//! comment.
//!
//! # What this module deliberately does NOT decide
//!
//! * **Payloads.** This is a NAME check. `#[trust::skip(garbage @@ here)]` has a
//!   claimed name and is accepted here; whether the payload is well formed is the
//!   consumer's business (`contract_panic`, for one, already hard-errors on a
//!   malformed payload inside `trust-mir-extract`, and `var`/`action` reject
//!   unknown keys inside `trust-thir-lower`). A name check that pretended to
//!   validate payloads would be claiming more than it checks.
//! * **The OTHER surface's vocabulary.** `cite` is the sharp case, and it is live:
//!   `first-party/ny` writes `#[trust::cite(crownproof::<thm>)]` on fourteen real
//!   functions (e.g. `ny-cert/src/branch.rs:304`), and `cite` is deliberately NOT
//!   in the table below. That is safe only because of HOW ny resolves it —
//!   `ny-cert/Cargo.toml` takes `trust = { package = "ny-contracts" }`, a
//!   proc-macro crate whose lib is named `trust` and which exports `requires`,
//!   `ensures`, `invariant` and `cite`. Those attributes resolve to
//!   `Res::Def(DefKind::Macro(..), ..)`, not to a tool attribute, so the
//!   register_tool rule never sees them. **If any crate ever writes
//!   `#[trust::cite(..)]` under `#![register_tool(trust)]`, this table must gain a
//!   `cite` row in the same commit, or that crate stops compiling.** The name is
//!   left out rather than admitted because no register_tool-surface consumer reads
//!   it, and admitting an unread name is precisely the silence E5 removes.
//!   (Worth recording separately: on ny's surface `cite` is a PASSTHROUGH no-op, so
//!   a citation naming a kernel-checked theorem contributes nothing to the
//!   compiler's verdict. ny's own `cite_check` + `proofs/cite-map.json` keep the
//!   citation honest; the compiler does not. That is the same defect class as E5,
//!   on the surface E5 does not cover.)
//! * **The PRE-RESOLUTION loop-clause spellings.** `loop_invariant` is
//!   deliberately absent even though it is live (29 occurrences fleet-wide, all in
//!   this repo's `tests/ui/trust/loop_clause_attr_*.rs`, `rustc_expand`, and the
//!   `run-make/trust-loop-clause-attribute-transport` fixture). Its consumer,
//!   `ast::trust_contract::trust_loop_clause_attr_kind`, matches
//!   `sym::loop_invariant` on a `while`/`loop` HEADER *before* name resolution and
//!   REMOVES the attribute, so a correctly placed one never reaches this rule at
//!   all. One that DOES reach the rule is by construction one the recognizer
//!   refused — wrong position, generic args, inner-attribute style — and that
//!   function's own doc states the invariant it relies on: "a spelling this
//!   function does not recognize is never silently accepted — it stays on the
//!   expression, reaches attribute-macro collection, and dies as an unresolved
//!   attribute." Predefining `trust` as a tool turns that death into INERTNESS, so
//!   leaving `loop_invariant` unclaimed here is what restores the fail-closed
//!   property the loop-clause surface was built on. (`decreases` is a different
//!   case and IS claimed: it has a real item-position consumer in
//!   `contract_kind_from_name`, so a misplaced loop `decreases` falls into the
//!   open POSITIONS gap below rather than into this one.)
//! * **Positions.** A claimed name in a position no consumer reads —
//!   `#[trust::requires(x > 0)]` on a `struct`, `impl`, or `mod`, all three measured
//!   silent — is NOT rejected here. Which positions each name claims is per-name
//!   knowledge: several names are read by an ANCESTOR walk
//!   (`item_has_trust_attr`), so `mod` and `impl` really are claimed positions for
//!   them, and a blanket position rule would reject working code. It stays recorded
//!   as an open silent acceptance rather than guessed at.

/// One name in the reserved `trust::` namespace, with the code that claims it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClaimedTrustAttr {
    /// The attribute name, i.e. the second segment of `trust::<name>`.
    pub name: &'static str,
    /// The consumer that READS this name, cited by file and function so the claim
    /// is checkable. A row without a live consumer is a bug in this table.
    pub consumer: &'static str,
}

/// The complete reserved vocabulary: twenty-four names, each with a live consumer.
///
/// Sorted by name so the rendered diagnostic is stable and a duplicate is easy to
/// spot; [`vocabulary_is_sorted_and_unique`] proves both.
pub const TRUST_ATTR_VOCABULARY: &[ClaimedTrustAttr] = &[
    ClaimedTrustAttr {
        name: "action",
        consumer: "crates/trust-thir-lower/src/crate_module.rs — \
                   `is_trust_attr(attr, \"action\")`; temporal machine transition owner",
    },
    ClaimedTrustAttr {
        name: "assume_total",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"assume_total\")`, ancestor-walking; \
                   also read by trust_verify/dyn_dispatch_reliance.rs",
    },
    ClaimedTrustAttr {
        name: "backing",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"backing\")`; \
                   relational buffer+length invariant",
    },
    ClaimedTrustAttr {
        name: "contract_panic",
        consumer: "crates/trust-mir-extract/src/lib.rs — `trust_contract_panic_body` strips the \
                   literal `trust::contract_panic` prefix off the attribute SNIPPET; \
                   `extract_contract_panic_annotations` consumes the result",
    },
    ClaimedTrustAttr {
        name: "contracts_ensures",
        consumer: "crates/trust-mir-extract/src/lib.rs — `contract_kind_from_name` via \
                   `attr.path().last()`; upstream-`core::contracts` alias spelling of `ensures`",
    },
    ClaimedTrustAttr {
        name: "contracts_requires",
        consumer: "crates/trust-mir-extract/src/lib.rs — `contract_kind_from_name` via \
                   `attr.path().last()`; upstream-`core::contracts` alias spelling of `requires`",
    },
    ClaimedTrustAttr {
        name: "decreases",
        consumer: "crates/trust-mir-extract/src/lib.rs `contract_kind_from_name` and \
                   compiler/rustc_mir_transform/src/trust_verify/dyn_dispatch_reliance.rs \
                   `def_may_have_contracts`, both via `attr.path().last()`",
    },
    ClaimedTrustAttr {
        name: "ensures",
        consumer: "compiler/rustc_resolve/src/macros.rs \
                   `trust_spec_contract_builtin_name_from_symbols` maps `ensures` onto \
                   `sym::trust_contracts_ensures`; on the register_tool surface \
                   crates/trust-mir-extract `contract_kind_from_name` lowers it — measured to \
                   produce a `postcond` obligation row",
    },
    ClaimedTrustAttr {
        name: "invariant",
        consumer: "crates/trust-mir-extract/src/lib.rs `contract_kind_from_name`; also read by \
                   trust_verify/trait_panic_free.rs `check_declaration` (refuses a conditional \
                   panic-freedom contract) — measured to produce an `invariant` obligation row",
    },
    ClaimedTrustAttr {
        name: "must_consume",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"must_consume\")`; linear-ownership lane",
    },
    ClaimedTrustAttr {
        name: "paired",
        consumer: "crates/trust-mir-extract/src/lib.rs — \
                   `local_item_has_direct_trust_attr(tcx, def_id, \"paired\")`; \
                   whole-crate condvar/mutex pairing certificate",
    },
    ClaimedTrustAttr {
        name: "panic_free",
        consumer: "compiler/rustc_mir_transform/src/trust_verify/trait_panic_free.rs — \
                   the `PANIC_FREE` path match; trait-level panic-freedom contract",
    },
    ClaimedTrustAttr {
        name: "panic_free_drop",
        consumer: "compiler/rustc_mir_transform/src/trust_verify/panic_free_drop.rs — \
                   `PANIC_FREE_DROP` (line 97) matched as `[tool, name]` with \
                   `tool == \"trust\"` (line 114); `Drop::drop` panic-freedom contract",
    },
    ClaimedTrustAttr {
        name: "reachable",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"reachable\")` in `verify_terminating_attr`",
    },
    ClaimedTrustAttr {
        name: "requires",
        consumer: "compiler/rustc_resolve/src/macros.rs \
                   `trust_spec_contract_builtin_name_from_symbols` maps `requires` onto \
                   `sym::trust_contracts_requires`; on the register_tool surface \
                   crates/trust-mir-extract `contract_kind_from_name` lowers it — measured to \
                   produce a lowered precondition obligation row",
    },
    ClaimedTrustAttr {
        name: "single_writer",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"single_writer\")`; mmap temporal policy \
                   (DECLARED evidence only — see the hazard note in CLAUDE.md)",
    },
    ClaimedTrustAttr {
        name: "skip",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — `item_has_trust_skip_attr`; \
                   under strict verification the skip is itself a hard error, never a silent pass",
    },
    ClaimedTrustAttr {
        name: "terminating",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"terminating\")` in \
                   `verify_terminating_attr`",
    },
    ClaimedTrustAttr {
        name: "trust_decreases",
        consumer: "crates/trust-mir-extract/src/lib.rs `contract_kind_from_name` via \
                   `attr.path().last()`; explicit-prefix alias spelling of `decreases`",
    },
    ClaimedTrustAttr {
        name: "trust_ensures",
        consumer: "crates/trust-mir-extract/src/lib.rs `contract_kind_from_name` via \
                   `attr.path().last()`; explicit-prefix alias — measured to produce a \
                   `postcond` obligation row",
    },
    ClaimedTrustAttr {
        name: "trust_invariant",
        consumer: "crates/trust-mir-extract/src/lib.rs `contract_kind_from_name` via \
                   `attr.path().last()`; explicit-prefix alias — measured to produce an \
                   `invariant` obligation row",
    },
    ClaimedTrustAttr {
        name: "trust_requires",
        consumer: "crates/trust-mir-extract/src/lib.rs `contract_kind_from_name` via \
                   `attr.path().last()`; explicit-prefix alias — measured to produce a lowered \
                   precondition obligation row",
    },
    ClaimedTrustAttr {
        name: "var",
        consumer: "crates/trust-thir-lower/src/crate_module.rs — `is_trust_attr(attr, \"var\")`; \
                   temporal state variable",
    },
    ClaimedTrustAttr {
        name: "verified_codegen",
        consumer: "compiler/rustc_mir_transform/src/trust_verify.rs — \
                   `item_has_trust_attr(tcx, def_id, \"verified_codegen\")`; trust-cg opt-in",
    },
];

/// Verdict for one attribute path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustAttrVerdict {
    /// The path does not live in the reserved namespace at all. Not this rule's
    /// business — say nothing.
    NotInNamespace,
    /// `trust::<name>` where `<name>` is claimed by the consumer recorded here.
    Claimed(ClaimedTrustAttr),
    /// `trust::<name>` where nothing claims `<name>`. HARD ERROR.
    ///
    /// `nearest` is a spelling suggestion when the written name is within a small
    /// edit distance of a claimed one — a typo is the common case and naming the
    /// intended attribute is the whole point of refusing loudly.
    Unclaimed { nearest: Option<&'static str> },
}

/// Classify an attribute PATH, given as its segments.
///
/// The caller passes the attribute's path segments verbatim (`["trust", "skip"]`
/// for `#[trust::skip]`). Deliberately total and deliberately strict:
///
/// * `["trust"]` alone is [`TrustAttrVerdict::NotInNamespace`] — a bare `#[trust]`
///   is not a tool attribute at all, and rustc already refuses it with
///   "cannot find attribute `trust` in this scope" (measured). A second diagnostic
///   for an already-loud case is noise.
/// * `["trust", "a", "b"]` — three or more segments — is UNCLAIMED, and so is
///   `["trust", "skip", "garbage"]` even though segment two is a claimed name.
///   Every consumer in the table matches EXACTLY two segments or the LAST segment;
///   none reads a claimed name from a longer `trust::` path, and `#[trust::a::b]`
///   is measured silent today.
/// * A path whose first segment is not exactly `trust` is
///   [`TrustAttrVerdict::NotInNamespace`]. `trustx::foo` is somebody else's tool.
#[must_use]
pub fn classify_trust_attr_path(segments: &[&str]) -> TrustAttrVerdict {
    let Some((&first, rest)) = segments.split_first() else {
        return TrustAttrVerdict::NotInNamespace;
    };
    if first != "trust" {
        return TrustAttrVerdict::NotInNamespace;
    }
    let [name] = rest else {
        if rest.is_empty() {
            // A bare `#[trust]` never resolves as a tool attribute; leave it to rustc.
            return TrustAttrVerdict::NotInNamespace;
        }
        // `trust::a::b` and deeper: reserved namespace, no consumer, refuse.
        return TrustAttrVerdict::Unclaimed { nearest: None };
    };
    match TRUST_ATTR_VOCABULARY.iter().find(|claimed| claimed.name == *name) {
        Some(claimed) => TrustAttrVerdict::Claimed(*claimed),
        None => TrustAttrVerdict::Unclaimed { nearest: nearest_claimed_name(name) },
    }
}

/// The claimed name closest to `written`, when the two are near enough that a typo
/// is the likely explanation.
///
/// Threshold: edit distance at most `1 + written.len() / 4`, capped at 3. Chosen so
/// `assume_totall` -> `assume_total` (distance 1) suggests, while an invented name
/// like `totally_made_up_clause` suggests nothing rather than pointing at whichever
/// real attribute happens to be least unlike it — a confidently wrong suggestion is
/// worse than none when the author's intent is not a typo.
#[must_use]
pub fn nearest_claimed_name(written: &str) -> Option<&'static str> {
    let budget = (1 + written.len() / 4).min(3);
    let mut best: Option<(usize, &'static str)> = None;
    for claimed in TRUST_ATTR_VOCABULARY {
        let distance = levenshtein(written, claimed.name);
        if distance > budget {
            continue;
        }
        match best {
            Some((best_distance, _)) if best_distance <= distance => {}
            _ => best = Some((distance, claimed.name)),
        }
    }
    best.map(|(_, name)| name)
}

/// The vocabulary rendered for a diagnostic, comma separated in table order.
#[must_use]
pub fn vocabulary_list() -> String {
    TRUST_ATTR_VOCABULARY
        .iter()
        .map(|claimed| claimed.name)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Plain Levenshtein distance over `char`s, two-row DP.
fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    if a.is_empty() {
        return b.len();
    }
    if b.is_empty() {
        return a.len();
    }
    let mut previous: Vec<usize> = (0..=b.len()).collect();
    let mut current = vec![0usize; b.len() + 1];
    for (i, &ai) in a.iter().enumerate() {
        current[0] = i + 1;
        for (j, &bj) in b.iter().enumerate() {
            let substitution = previous[j] + usize::from(ai != bj);
            let deletion = previous[j + 1] + 1;
            let insertion = current[j] + 1;
            current[j + 1] = substitution.min(deletion).min(insertion);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[b.len()]
}

/// Table hygiene: sorted (so the diagnostic is stable) and duplicate-free (so two
/// rows can never disagree about who consumes a name).
#[must_use]
pub fn vocabulary_is_sorted_and_unique() -> bool {
    TRUST_ATTR_VOCABULARY.windows(2).all(|pair| pair[0].name < pair[1].name)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn claimed(segments: &[&str]) -> bool {
        matches!(classify_trust_attr_path(segments), TrustAttrVerdict::Claimed(_))
    }

    fn unclaimed(segments: &[&str]) -> bool {
        matches!(classify_trust_attr_path(segments), TrustAttrVerdict::Unclaimed { .. })
    }

    #[test]
    fn table_is_sorted_unique_and_every_row_cites_a_consumer() {
        assert!(vocabulary_is_sorted_and_unique(), "vocabulary must be sorted and duplicate-free");
        for row in TRUST_ATTR_VOCABULARY {
            assert!(!row.name.is_empty(), "empty attribute name in the vocabulary");
            assert!(
                row.consumer.contains(".rs"),
                "row `{}` must cite the consuming FILE, got {:?}",
                row.name,
                row.consumer
            );
        }
    }

    /// The twenty-four names derived from consuming code, pinned. Adding or
    /// removing one is a deliberate act that must edit this list too, because
    /// either direction is a correctness-relevant change: a deletion REJECTS a
    /// working program, an addition RE-OPENS a silent acceptance.
    #[test]
    fn vocabulary_is_exactly_the_consumer_derived_names() {
        let names: Vec<&str> = TRUST_ATTR_VOCABULARY.iter().map(|c| c.name).collect();
        assert_eq!(
            names,
            vec![
                "action",
                "assume_total",
                "backing",
                "contract_panic",
                "contracts_ensures",
                "contracts_requires",
                "decreases",
                "ensures",
                "invariant",
                "must_consume",
                "paired",
                "panic_free",
                "panic_free_drop",
                "reachable",
                "requires",
                "single_writer",
                "skip",
                "terminating",
                "trust_decreases",
                "trust_ensures",
                "trust_invariant",
                "trust_requires",
                "var",
                "verified_codegen",
            ]
        );
    }

    /// REGRESSION GUARD for the mistake this table actually made. These six are
    /// claimed by `contract_kind_from_name`, whose match is on `attr.path().last()`
    /// and therefore never mentions the `trust` namespace — so an enumeration that
    /// only looked for exact `[trust, name]` path matches missed all six and would
    /// have rejected six working spellings. Measured: `#[trust::contracts_requires(
    /// a > 0)]` produces a real lowered precondition obligation.
    #[test]
    fn the_last_segment_alias_spellings_are_claimed() {
        for alias in [
            "contracts_requires",
            "contracts_ensures",
            "trust_requires",
            "trust_ensures",
            "trust_invariant",
            "trust_decreases",
        ] {
            assert!(
                claimed(&["trust", alias]),
                "`trust::{alias}` is read by `contract_kind_from_name`; rejecting it breaks a \
                 working program"
            );
        }
    }

    #[test]
    fn every_claimed_name_classifies_as_claimed() {
        for row in TRUST_ATTR_VOCABULARY {
            assert!(
                claimed(&["trust", row.name]),
                "`trust::{}` is in the table but did not classify as Claimed",
                row.name
            );
        }
    }

    /// The measured defect: the exact spelling that compiles clean today.
    #[test]
    fn the_measured_silent_acceptance_is_now_unclaimed() {
        assert!(unclaimed(&["trust", "totally_made_up_clause"]));
    }

    /// Names that LOOK like Trust vocabulary but are reachable only through the
    /// source-snippet parser's UN-namespaced item forms. `safe_attr_span` hands the
    /// snippet parser the full `#[trust::boundary]` text, which matches neither
    /// `"boundary"` nor `"trust_boundary"`, so nothing consumes the tool spelling.
    /// Measured: `#[trust::boundary]`, `#[trust::model]` and `#[trust::assume(..)]`
    /// leave the ledger identical to the un-annotated control. Admitting them would
    /// preserve exactly the silent no-op E5 exists to remove.
    #[test]
    fn snippet_only_vocabulary_is_not_admitted_under_the_tool_namespace() {
        for snippet_only in ["boundary", "trust_boundary", "model", "assume", "trust_assume"] {
            assert!(
                unclaimed(&["trust", snippet_only]),
                "`trust::{snippet_only}` has no tool-path consumer and must not be admitted"
            );
        }
    }

    /// `cite` is LIVE in `first-party/ny` (fourteen sites) and is deliberately not
    /// in the tool vocabulary, because ny resolves `trust::` through the
    /// `ny-contracts` proc-macro crate rather than through `register_tool`. This
    /// test exists so that admitting it becomes a deliberate, reviewed act: if a
    /// crate ever writes `#[trust::cite(..)]` under `#![register_tool(trust)]`, this
    /// assertion is the thing that has to be edited, and editing it forces someone
    /// to say which register_tool-surface consumer reads the name.
    #[test]
    fn cite_is_the_other_surfaces_name_and_stays_out_of_the_tool_vocabulary() {
        assert!(unclaimed(&["trust", "cite"]));
    }

    /// `panic_free_drop` is claimed by its OWN module, not by an
    /// `item_has_trust_attr` call site, which is why a call-site-only enumeration
    /// missed it. It is live in this repo (21 occurrences, five of them in
    /// `tests/ui/trust/panic_free_drop_*.rs`), so rejecting it would have broken
    /// the compiler's own UI suite.
    #[test]
    fn the_drop_panic_freedom_contract_is_claimed_by_its_own_module() {
        assert!(claimed(&["trust", "panic_free_drop"]));
        assert!(claimed(&["trust", "panic_free"]));
    }

    /// `loop_invariant` is LIVE (29 occurrences) and deliberately UNCLAIMED, and
    /// that is the fail-closed answer rather than an omission — see the
    /// module-level bullet. Its consumer, `trust_loop_clause_attr_kind`, matches
    /// on a `while`/`loop` header BEFORE name resolution and removes the
    /// attribute, so a correctly placed one never reaches this classifier. One
    /// that does reach it is one the recognizer refused, and that used to die as
    /// an unresolved attribute — predefining the `trust` tool would otherwise
    /// turn exactly that death into silence.
    #[test]
    fn the_loop_header_only_clause_stays_unclaimed_so_a_misplaced_one_is_refused() {
        assert!(unclaimed(&["trust", "loop_invariant"]));
        // `decreases` is the contrasting case: it has a real ITEM-position
        // consumer, so it is claimed and a misplaced loop `decreases` falls into
        // the open POSITIONS gap instead. Pinned so the asymmetry is deliberate.
        assert!(claimed(&["trust", "decreases"]));
    }

    /// A typo of a real annotation is the common case and must name its target.
    #[test]
    fn a_one_keystroke_typo_suggests_the_intended_attribute() {
        assert_eq!(nearest_claimed_name("assume_totall"), Some("assume_total"));
        assert_eq!(nearest_claimed_name("skipp"), Some("skip"));
        assert_eq!(nearest_claimed_name("require"), Some("requires"));
        assert_eq!(nearest_claimed_name("panicfree"), Some("panic_free"));
        assert_eq!(nearest_claimed_name("verified_codegen_"), Some("verified_codegen"));
    }

    /// ...and an invented name must NOT be given a confidently wrong suggestion.
    #[test]
    fn an_invented_name_suggests_nothing() {
        assert_eq!(nearest_claimed_name("totally_made_up_clause"), None);
        assert_eq!(nearest_claimed_name("proves_everything"), None);
        assert_eq!(nearest_claimed_name("frobnicate"), None);
    }

    /// NON-VACUITY, the shape this campaign keeps failing on. A check whose
    /// rejected set is empty (accept everything) or whose accepted set is empty
    /// (reject everything) would still pass a one-sided "it errors on nonsense"
    /// test. Pin BOTH sides, and pin the size so a silent shrink is caught.
    #[test]
    fn the_check_is_not_vacuous_in_either_direction() {
        assert!(claimed(&["trust", "skip"]), "accepted set must be non-empty");
        assert!(
            unclaimed(&["trust", "not_a_trust_attribute_at_all"]),
            "rejected set must be non-empty"
        );
        assert_eq!(
            TRUST_ATTR_VOCABULARY.len(),
            24,
            "vocabulary size changed; a deletion rejects working code and an addition re-opens a \
             silent acceptance — update the pinned list test deliberately"
        );
    }

    /// Neighbouring namespaces are none of this rule's business.
    #[test]
    fn other_tool_namespaces_are_untouched() {
        for path in [
            vec!["trustx", "foo"],
            vec!["rustfmt", "skip"],
            vec!["clippy", "allow"],
            vec!["trust_vc", "requires"],
            vec!["my_trust", "skip"],
            vec!["diagnostic", "on_unimplemented"],
        ] {
            assert_eq!(
                classify_trust_attr_path(&path),
                TrustAttrVerdict::NotInNamespace,
                "{path:?} must not be judged by the trust:: rule"
            );
        }
    }

    /// A bare `#[trust]` is already refused by rustc ("cannot find attribute
    /// `trust` in this scope", measured); a second diagnostic here would be noise.
    #[test]
    fn a_bare_trust_path_is_left_to_rustc() {
        assert_eq!(classify_trust_attr_path(&["trust"]), TrustAttrVerdict::NotInNamespace);
        assert_eq!(classify_trust_attr_path(&[]), TrustAttrVerdict::NotInNamespace);
    }

    /// Measured silent today: `#[trust::a::b]` compiles with zero diagnostics.
    /// Nothing reads a claimed name out of a longer `trust::` path either, so
    /// `#[trust::skip::garbage]` must not inherit `skip`'s claim.
    #[test]
    fn a_deeper_path_in_the_namespace_is_unclaimed() {
        assert!(unclaimed(&["trust", "a", "b"]));
        assert!(unclaimed(&["trust", "skip", "garbage"]));
        assert!(unclaimed(&["trust", "requires", "extra", "more"]));
    }

    /// A claimed name with a nonsense PAYLOAD is still a claimed NAME. This is a
    /// name check and says so; the payload is the consumer's business. Asserted so
    /// the boundary is stated rather than assumed.
    #[test]
    fn payloads_are_explicitly_out_of_scope() {
        assert!(claimed(&["trust", "skip"]));
        assert!(claimed(&["trust", "var"]));
    }

    #[test]
    fn rendered_vocabulary_is_stable_and_lists_every_name() {
        let rendered = vocabulary_list();
        for row in TRUST_ATTR_VOCABULARY {
            assert!(rendered.contains(row.name), "`{}` missing from the rendered list", row.name);
        }
        assert!(rendered.starts_with("action, assume_total, backing, contract_panic, "));
    }

    #[test]
    fn levenshtein_is_a_metric_on_the_cases_we_rely_on() {
        assert_eq!(levenshtein("", ""), 0);
        assert_eq!(levenshtein("skip", "skip"), 0);
        assert_eq!(levenshtein("skip", ""), 4);
        assert_eq!(levenshtein("", "skip"), 4);
        assert_eq!(levenshtein("skip", "skipp"), 1);
        assert_eq!(levenshtein("assume_totall", "assume_total"), 1);
        assert_eq!(levenshtein("kitten", "sitting"), 3);
    }
}
