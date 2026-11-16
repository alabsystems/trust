//! M2 SET-PARITY comparator (docs/design/DIRECT-LANE-PROOF-AUTHORITY.md, M2):
//! per site, does EACH lane mint an obligation row AT ALL — with every
//! asymmetry enumerated by reason, never averaged, and fail-closed on any
//! asymmetry the taxonomy below does not name.
//!
//! # THE COMPAREE — stated and justified
//!
//! The MIR lane's side of the set is **the per-site multiset of
//! `Terminator::Assert` instances in the `VerifiableFunction` dumps** (the
//! `-Ztrust-dump=mir-only` / fixture-corpus format), keyed per site and
//! classified by `AssertMessage`. It is deliberately NOT trust-vcgen's public
//! row multiset and NOT the bridge's obligation table. Grounds:
//!
//! 1. **vcgen's row multiset is not per-site.** `generate_vcs_impl`
//!    (`crates/trust-vcgen/src/generate/entry.rs`) assembles (a) a TERMINATOR
//!    lane (`safety.rs` "1. VCs from rustc Assert terminators", ~:499) — at
//!    most one row per assert, and FEWER when
//!    `v2_assert_failure_is_known_false` / the provably-cannot-fire
//!    suppressions apply; (b) a STATEMENT lane (`safety.rs` ~:972 walks
//!    `block.stmts` and mints div/rem/shift/add/sub/mul rows per `Rvalue`),
//!    whose duplicate-vs-terminator suppression is explicitly fail-open
//!    toward duplication — "anything non-canonical keeps both rows"
//!    (`checked_vcs.rs` ~:1004) — so the public per-site count is 1 or 2
//!    depending on MIR canonicality, a property of the dedup heuristic, not
//!    of the program; (c) a HARDENED panic-boundary TWIN
//!    (`entry.rs` ~:401-407, on by default under `targo trust check`) — a
//!    second per-assert row set; (d) FUNCTION-LEVEL rows (typed CHC function
//!    admission, contract/termination/unsupported rows, the bridge's
//!    "{fn}: all assertions hold" aggregates) that are about no site at all.
//!    Grading against that multiset would grade the dedup/twin/suppression
//!    heuristics, not lane coverage.
//! 2. **The raw assert set is the vocabulary both lanes already treat as
//!    semantic ground truth.** The #57 ruling (safety.rs BoundsCheck arm):
//!    every BoundsCheck assert mints an obligation, because "an obligation
//!    that is never emitted is SILENT, and silence is indistinguishable from
//!    success". Step 6's `grade_real_records` already pairs dumped direct
//!    records against `Terminator::Assert` instances in the same dumps, and
//!    both lanes' occ ordinals are defined over assert emission order. M2
//!    extends the SAME comparee from the formula axis to the set axis.
//! 3. **Per-def, not per-mono** — pairing scope is `{crate}::{def_path}` ==
//!    `VerifiableFunction.def_path`; a corpus holding one `def_path` twice is
//!    refused as ambiguous (the `grade_real_records` discipline). Per-mono
//!    set parity is Step-6/7 material.
//! 4. **No filtering**: EVERY assert terminator is a comparee element. The
//!    six direct classes pair; every other `AssertMessage` variant is
//!    ENUMERATED as a named non-coverage row (never skipped the way the
//!    formula graders' `slug_for_assert_message == None` skip does — correct
//!    for formula parity, wrong for set parity). Classes that exist only as
//!    vcgen/bridge ROW KINDS and never as MIR asserts (unwrap panic-freedom
//!    on `Call` terminators, drop-glue PanicFreedom, UnsupportedMir,
//!    contract rows) exit the per-site comparison surface by construction
//!    under this comparee; they belong in the M2 doc's remaining-gap ladder
//!    as row-kind non-coverage, NOT as per-site rows — do not read "set
//!    parity" as covering them.
//!
//! # THE DIRECT SIDE OF THE SET
//!
//! One `TRUST_DIRECT_FORMULA_DUMP` JSONL record == one direct set row,
//! REGARDLESS of its formula outcome: `DirectFormulaOutcome` is formula-axis
//! session state ("NOT identity, NOT row content"), and row birth proceeds
//! identically on all three outcome arms — verified on the real probe, where
//! `withheld` records pair as set rows against their MIR asserts. The dump
//! hook fires before every withhold path and unspliced bodies are not
//! dumped, so for a compilation that PRODUCED an artifact, dumped set ==
//! installed set over spliced bodies. A `not_minted` record is still a set
//! row and is surfaced in the scorecard (a capture regression must be
//! visible, expected 0 in production dumps).
//!
//! **The one silent drop, and the input it forces:** bodies whose def never
//! spliced are skipped with a disclosure count only — no dump rows. A def
//! with MIR asserts and zero JSONL records is therefore AMBIGUOUS between
//! (i) body-not-lowered/unspliced and (ii) body lowered clean but the site
//! mints nothing. The comparator takes a THIRD input to split them: the
//! direct-lane FUNCTION CENSUS (the `coverage.json` sidecar,
//! `trust.thir-lower.crate-module.coverage.v2` — per-body `lowered` /
//! `spliced` / `unsupported`). Census present-with-clean-body -> the
//! per-site shape classes apply; refused/unspliced -> `C3`; census
//! unavailable for a scope -> the comparator REFUSES rather than guessing a
//! reason class.
//!
//! # REASON TAXONOMY (every per-site row lands in exactly one class)
//!
//! * **A. pairing axis** — the five slugs over the six direct classes
//!   (`slug_for_assert_message`), reported on the eight `class_label`s.
//! * **B. named non-coverage (MIR-only by KIND)** — coroutine resume,
//!   misaligned/null pointer deref, invalid enum construction, custom
//!   asserts, `Overflow(other-binop)`; enumerated per assert instance.
//!   `AssertMessage` is `#[non_exhaustive]`: an unknown variant is a hard
//!   error, never a bucket.
//! * **C. MIR-only at six-class sites** (consulted ONLY when the direct side
//!   has no record at the site): `C1` missing-const-index-bounds (the M2 top
//!   gap — closed at the lowering by the const-arm bounds emission, this
//!   class must measure zero on post-fix artifacts), `C2`
//!   oob-const-index-body-refused (deliberate #191 refusal, census-confirmed,
//!   must never move), `C3` function-outside-direct-fragment
//!   (census-confirmed refused/unspliced body). A six-class assert with no
//!   record in a lowered-clean body that matches NO shape predicate is a
//!   HARD ERROR — a new missing-row class enters this taxonomy in a reviewed
//!   change, or not at all. In particular, an OOB-shaped const-index site in
//!   a lowered-clean body is a hard error: it is exactly the state deleting
//!   the #191 refusal would produce, so the comparator is a tripwire for
//!   that mutation.
//! * **D. discharge annotations** (bridge behavior, shape-derived) —
//!   `discharged-at-bridge:literal-shift-in-range` (mirror of
//!   `lower.rs::is_literal_shift_in_range_overflow_assert`) and
//!   `discharged-at-bridge:arbitrary-precision` (mirror of
//!   `is_arbitrary_precision_overflow_assert`, reachable-shape subset).
//!   These ANNOTATE rows, they never excuse a missing one: the direct lane
//!   does not discharge literal shifts (it always asserts on checks-ON int
//!   shifts), so D1-annotated sites with a lowered body pair "both"; bignum
//!   bodies are outside the direct fragment, so D2 sites classify C3 by
//!   census. NOTE the D2 mirror is structurally INERT over serde-loaded
//!   corpora: `Ty::Adt::arbitrary_precision` is `#[serde(skip)]` in both
//!   directions, so a JSON fixture never carries the stamp — the annotation
//!   can fire only over in-process modules. Stated here so a zero count is
//!   read as "unobservable", not "absent".
//! * **E. direct-only at six-class sites** — NO legitimate class is known:
//!   every direct recording site mirrors a built-MIR assert by construction.
//!   A record pairing no MIR assert, a partial collision group, or a record
//!   whose scope has no corpus function is a HARD ERROR (fail closed). If a
//!   genuine direct-only class ever appears it enters this taxonomy in the
//!   same reviewed change that explains it.
//! * **F. formula-axis exclusions do not transfer**: the signed div/rem
//!   MIR-shape exclusion (`no-divrem-op-found`) is a property of formula
//!   RECONSTRUCTION; on the set axis both lanes mint at those sites and they
//!   pair "both".
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_types::{
    AdtAuth, ArbPrecKind, AssertMessage, BasicBlock, BinOp, ConstValue, LocalDecl, Operand, Rvalue,
    Statement, Terminator, Ty, VerifiableFunction,
};

use crate::direct_formula_dump::{DIRECT_FORMULA_DUMP_VERSION, DumpedDirectRecord, DumpedOutcome};
use crate::direct_record_grading::{class_label, slug_for_assert_message};
use crate::lower::find_block_shift_assign;

/// C1 — the M2 top gap: built MIR emits the bounds assert even for a
/// constant in-bounds index; the direct constant arm minted no row (fixed at
/// the lowering in the same increment that added this comparator; this class
/// must measure ZERO on artifacts of the fixed driver).
pub const REASON_MISSING_CONST_INDEX_BOUNDS: &str = "missing-const-index-bounds";
/// C2 — the deliberate #191 refusal: a constant OOB index refuses the WHOLE
/// body, so the per-site row is function-level absent. Census-confirmed.
/// Must never move.
pub const REASON_OOB_CONST_INDEX_BODY_REFUSED: &str = "oob-const-index-body-refused";
/// C3 — the def has six-class MIR asserts and the census says the body never
/// lowered clean / never spliced into the direct module.
pub const REASON_OUTSIDE_DIRECT_FRAGMENT: &str = "function-outside-direct-fragment";

/// B — named non-coverage codes (MIR-only by KIND; the direct lane births no
/// such row today).
pub const NONCOVERAGE_COROUTINE_RESUME: &str = "noncoverage:coroutine-resume";
pub const NONCOVERAGE_MISALIGNED_PTR: &str = "noncoverage:misaligned-ptr-deref";
pub const NONCOVERAGE_NULL_PTR: &str = "noncoverage:null-ptr-deref";
pub const NONCOVERAGE_INVALID_ENUM: &str = "noncoverage:invalid-enum-construction";
pub const NONCOVERAGE_CUSTOM_ASSERT: &str = "noncoverage:custom-assert";
/// Unreached today (every current overflow binop maps to a slug); the arm
/// exists so a new rustc binop fails CLOSED into a named bucket, not a skip.
pub const NONCOVERAGE_OVERFLOW_OTHER: &str = "noncoverage:overflow-other";

/// D — discharge annotation codes.
pub const DISCHARGE_LITERAL_SHIFT: &str = "discharged-at-bridge:literal-shift-in-range";
pub const DISCHARGE_ARBITRARY_PRECISION: &str = "discharged-at-bridge:arbitrary-precision";

/// THE enumerated MIR-only reason vocabulary. A classification outside this
/// slice is a comparator bug (belt-checked at tally time); a site that fits
/// no class is a hard error at classification time. New classes enter here
/// in the same reviewed change that explains them — the
/// `ENUMERATED_WITHHELD_REASONS` discipline applied to set reasons.
pub const ENUMERATED_SET_REASONS: &[&str] = &[
    REASON_MISSING_CONST_INDEX_BOUNDS,
    REASON_OOB_CONST_INDEX_BODY_REFUSED,
    REASON_OUTSIDE_DIRECT_FRAGMENT,
    NONCOVERAGE_COROUTINE_RESUME,
    NONCOVERAGE_MISALIGNED_PTR,
    NONCOVERAGE_NULL_PTR,
    NONCOVERAGE_INVALID_ENUM,
    NONCOVERAGE_CUSTOM_ASSERT,
    NONCOVERAGE_OVERFLOW_OTHER,
];

/// The per-site verdict of the set comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SiteDisposition {
    /// Both lanes mint a row at this site.
    Both,
    /// Only the MIR lane holds an assert here, for the named enumerated
    /// reason (a B or C code from [`ENUMERATED_SET_REASONS`]).
    MirOnly(&'static str),
}

/// One enumerated per-site row.
#[derive(Debug, Clone)]
pub struct SiteRow {
    /// `{crate}::{def_path}`.
    pub scope: String,
    /// The reporting class label (`class_label`), or `"non-safety"` for
    /// B-class asserts.
    pub class_label: &'static str,
    pub line: u32,
    pub col: u32,
    pub occ: u32,
    pub disposition: SiteDisposition,
    /// D-code annotation: the MIR lane's own bridge discharges this assert's
    /// obligation, so its public row set is smaller than its assert set here.
    /// Never an excuse for a missing direct row.
    pub discharge: Option<&'static str>,
    pub detail: String,
}

/// The tallied set-parity outcome. Counts are ENUMERATED per class — there
/// is deliberately no ratio or average anywhere on this struct.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct SetParityScorecard {
    /// All MIR assert terminators seen (six-class + non-coverage).
    pub mir_asserts_total: usize,
    /// Sites where both lanes mint a row.
    pub both: usize,
    /// `both` broken out by the eight reporting class labels.
    pub both_per_class: BTreeMap<&'static str, usize>,
    /// MIR-only sites by enumerated C-reason.
    pub mir_only: BTreeMap<&'static str, usize>,
    /// MIR-only-by-kind (B-class) asserts by enumerated code.
    pub noncoverage: BTreeMap<&'static str, usize>,
    /// D-code annotations over all rows (disclosure).
    pub discharge_annotated: BTreeMap<&'static str, usize>,
    /// Direct set rows consumed (== dumped records; every one must pair).
    pub direct_rows: usize,
    /// Of those, records with a `not_minted` formula outcome — still set
    /// rows, surfaced so a capture regression is visible (expected 0).
    pub direct_not_minted: usize,
}

/// Tally rows into a scorecard, belt-checking every MirOnly reason against
/// the enumerated vocabulary (a foreign reason panics: it is a comparator
/// bug, not a corpus property).
pub fn tally_site_rows(rows: &[SiteRow]) -> SetParityScorecard {
    let mut card = SetParityScorecard::default();
    for row in rows {
        card.mir_asserts_total += 1;
        match &row.disposition {
            SiteDisposition::Both => {
                card.both += 1;
                *card.both_per_class.entry(row.class_label).or_default() += 1;
            }
            SiteDisposition::MirOnly(reason) => {
                assert!(
                    ENUMERATED_SET_REASONS.contains(reason),
                    "MirOnly reason {reason:?} is outside ENUMERATED_SET_REASONS — \
                     comparator bug (fail closed)"
                );
                if reason.starts_with("noncoverage:") {
                    *card.noncoverage.entry(reason).or_default() += 1;
                } else {
                    *card.mir_only.entry(reason).or_default() += 1;
                }
            }
        }
        if let Some(code) = row.discharge {
            *card.discharge_annotated.entry(code).or_default() += 1;
        }
    }
    card
}

pub fn print_set_parity_scorecard(label: &str, card: &SetParityScorecard) {
    println!("== M2 SET-PARITY SCORECARD ({label}) ==");
    println!("   MIR assert terminators (the comparee): {}", card.mir_asserts_total);
    println!("   both lanes mint a row: {}", card.both);
    println!("   both, per class: {:?}", card.both_per_class);
    println!("   MIR-only (reason-enumerated): {:?}", card.mir_only);
    println!("   named non-coverage (by kind): {:?}", card.noncoverage);
    println!("   discharge annotations (disclosure): {:?}", card.discharge_annotated);
    println!(
        "   direct set rows: {} (not_minted surfaced: {})",
        card.direct_rows, card.direct_not_minted
    );
}

// ---------------------------------------------------------------------------
// Function census (the third input).
// ---------------------------------------------------------------------------

/// One body row of the direct-lane function census.
#[derive(Debug, Clone)]
pub struct CensusBody {
    pub lowered: bool,
    pub spliced: bool,
    pub unsupported: Vec<String>,
}

impl CensusBody {
    /// Lowered clean AND spliced: the per-site shape classes apply. Anything
    /// else is the C3 side of the split.
    pub fn clean_and_spliced(&self) -> bool {
        self.lowered && self.spliced && self.unsupported.is_empty()
    }
}

/// The direct-module function census, keyed by scope (`{crate}::{def_path}`).
#[derive(Debug, Default)]
pub struct DirectFunctionCensus {
    pub bodies: BTreeMap<String, CensusBody>,
}

/// The coverage-sidecar schema this loader understands. Any other schema
/// string refuses — never a guess over an unknown layout.
pub const COVERAGE_SCHEMA_V2: &str = "trust.thir-lower.crate-module.coverage.v2";

/// Load the census from a `coverage.json` sidecar (fail-closed reader).
pub fn load_census_from_coverage_json(text: &str) -> Result<DirectFunctionCensus, String> {
    let value: serde_json::Value =
        serde_json::from_str(text).map_err(|e| format!("coverage json does not parse: {e}"))?;
    let schema = value
        .get("schema")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "coverage json carries no schema field".to_string())?;
    if schema != COVERAGE_SCHEMA_V2 {
        return Err(format!(
            "coverage schema {schema:?} is not the understood {COVERAGE_SCHEMA_V2:?} — \
             refusing to guess census semantics"
        ));
    }
    let krate = value
        .get("crate")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "coverage json carries no crate field".to_string())?;
    let bodies = value
        .get("bodies")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "coverage json carries no bodies array".to_string())?;
    let mut census = DirectFunctionCensus::default();
    for (i, body) in bodies.iter().enumerate() {
        let def_path = body
            .get("def_path")
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("coverage body[{i}] has no def_path"))?;
        let lowered = body
            .get("lowered")
            .and_then(|v| v.as_bool())
            .ok_or_else(|| format!("coverage body[{i}] has no lowered flag"))?;
        let spliced = body
            .get("spliced")
            .and_then(|v| v.as_bool())
            .ok_or_else(|| format!("coverage body[{i}] has no spliced flag"))?;
        let unsupported = body
            .get("unsupported")
            .and_then(|v| v.as_array())
            .ok_or_else(|| format!("coverage body[{i}] has no unsupported array"))?
            .iter()
            .map(|entry| {
                // Entries are either plain tag strings or [span, tag] pairs.
                entry
                    .as_str()
                    .map(str::to_string)
                    .or_else(|| {
                        entry.as_array().and_then(|pair| {
                            pair.last().and_then(|t| t.as_str()).map(str::to_string)
                        })
                    })
                    .ok_or_else(|| format!("coverage body[{i}] unsupported entry unreadable"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        census
            .bodies
            .insert(format!("{krate}::{def_path}"), CensusBody { lowered, spliced, unsupported });
    }
    Ok(census)
}

// ---------------------------------------------------------------------------
// Shape predicates.
// ---------------------------------------------------------------------------

/// The resolved constant-index bounds shape of a `BoundsCheck` assert.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstIndexShape {
    InBounds { k: u128, n: u128 },
    OutOfBounds { k: u128, n: u128 },
}

/// Find the compare defining the assert's boolean condition local, with its
/// statement index — the same resolution discipline as
/// `lower::find_condition_binary_operands` (first projection-free
/// `BinaryOp` assign to the cond local), plus the index the reaching-def
/// scan below needs.
fn condition_compare<'a>(
    block: &'a BasicBlock,
    cond: &Operand,
) -> Option<(usize, BinOp, &'a Operand, &'a Operand)> {
    let cond_local = match cond {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
        _ => return None,
    };
    block.stmts.iter().enumerate().find_map(|(i, stmt)| {
        let Statement::Assign { place, rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } = stmt else {
            return None;
        };
        if place.local == cond_local && place.projections.is_empty() {
            Some((i, *op, lhs, rhs))
        } else {
            None
        }
    })
}

/// Resolve an index operand to a compile-time constant `K`, fail-closed:
/// * a `Uint`/non-negative `Int` constant resolves directly;
/// * a `Copy`/`Move` of a projection-free NON-PARAM local resolves iff the
///   function's ONLY write to that local (all blocks — cross-block defs and
///   later rewrites fail closed) is a `Use(Constant …)` in `block` BEFORE
///   the compare statement;
/// * everything else (params, casts, projections, derived locals, multiple
///   defs) is `None` — the dynamic-index answer.
fn const_index_operand_value(
    func: &VerifiableFunction,
    block: &BasicBlock,
    compare_index: usize,
    operand: &Operand,
) -> Option<u128> {
    match operand {
        Operand::Constant(ConstValue::Uint(k, _)) => Some(*k),
        Operand::Constant(ConstValue::Int(k)) if *k >= 0 => Some(*k as u128),
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
            let local = p.local;
            // A param's value is caller-supplied — never a constant def.
            if (1..=func.body.arg_count).contains(&local) {
                return None;
            }
            let writes_to_local = |stmts: &[Statement]| {
                stmts
                    .iter()
                    .enumerate()
                    .filter(|(_, stmt)| {
                        matches!(stmt, Statement::Assign { place, .. } if place.local == local)
                    })
                    .map(|(i, _)| i)
                    .collect::<Vec<_>>()
            };
            // Exactly one write in the WHOLE function, and it must be the
            // in-block constant def before the compare.
            let mut writes_elsewhere = 0usize;
            for other in &func.body.blocks {
                if other.id != block.id {
                    writes_elsewhere += writes_to_local(&other.stmts).len();
                }
            }
            if writes_elsewhere != 0 {
                return None;
            }
            let in_block = writes_to_local(&block.stmts);
            let [def_index] = in_block.as_slice() else { return None };
            if *def_index >= compare_index {
                return None;
            }
            match &block.stmts[*def_index] {
                Statement::Assign {
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(k, _))),
                    ..
                } => Some(*k),
                Statement::Assign {
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(k))),
                    ..
                } if *k >= 0 => Some(*k as u128),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The C1/C2 shape predicate: a `BoundsCheck` assert whose condition is
/// `Lt(K, N)` for compile-time constants `K` (resolved fail-closed above)
/// and `N` (the length operand MIR spells as a `Uint` constant).
pub fn const_index_bounds_shape(
    func: &VerifiableFunction,
    block: &BasicBlock,
    cond: &Operand,
    msg: &AssertMessage,
) -> Option<ConstIndexShape> {
    if !matches!(msg, AssertMessage::BoundsCheck) {
        return None;
    }
    let (compare_index, op, lhs, rhs) = condition_compare(block, cond)?;
    if op != BinOp::Lt {
        return None;
    }
    let n = match rhs {
        Operand::Constant(ConstValue::Uint(n, _)) => *n,
        _ => return None,
    };
    let k = const_index_operand_value(func, block, compare_index, lhs)?;
    Some(if k < n {
        ConstIndexShape::InBounds { k, n }
    } else {
        ConstIndexShape::OutOfBounds { k, n }
    })
}

/// Walk a place's declared type through `Field` projections over tuples —
/// the reachable-shape subset of the bridge's `place_type` that the D1
/// mirror needs (checked-shift destinations). Everything else fails closed.
fn dump_place_type(locals: &[LocalDecl], place: &trust_types::Place) -> Option<Ty> {
    let mut ty = locals.iter().find(|d| d.index == place.local)?.ty.clone();
    for projection in &place.projections {
        ty = match (projection, ty) {
            (trust_types::Projection::Field(i), Ty::Tuple(fields)) => fields.get(*i)?.clone(),
            _ => return None,
        };
    }
    Some(ty)
}

/// D1 mirror of `lower.rs::is_literal_shift_in_range_overflow_assert` over
/// dump parts: `Overflow(Shl|Shr)` whose shift AMOUNT is a compile-time
/// integer literal strictly below the shiftee's positively-recovered bit
/// width. Annotation-only — a miss under-annotates, it never mis-classifies.
pub fn literal_shift_in_range_annotation(
    locals: &[LocalDecl],
    blocks: &[BasicBlock],
    source_block: trust_types::BlockId,
    target: trust_types::BlockId,
    msg: &AssertMessage,
) -> bool {
    let op = match msg {
        AssertMessage::Overflow(op @ (BinOp::Shl | BinOp::Shr)) => *op,
        _ => return false,
    };
    let block_by_id = |id| blocks.iter().find(|b| b.id == id);
    let Some((dest, checked, value, amount)) = block_by_id(source_block)
        .and_then(|b| find_block_shift_assign(b, op))
        .or_else(|| block_by_id(target).and_then(|b| find_block_shift_assign(b, op)))
    else {
        return false;
    };
    let amount_val: u128 = match amount {
        Operand::Constant(ConstValue::Uint(v, _)) => *v,
        Operand::Constant(ConstValue::Int(v)) if *v >= 0 => *v as u128,
        _ => return false,
    };
    let value_width: u32 = match value {
        Operand::Copy(place) | Operand::Move(place) => match dump_place_type(locals, place) {
            Some(Ty::Int { width, .. }) => width,
            _ => return false,
        },
        Operand::Constant(ConstValue::Uint(_, width)) => *width,
        Operand::Constant(ConstValue::Int(_)) => {
            let Some(dest_ty) = dump_place_type(locals, dest) else { return false };
            let value_ty = if checked {
                match dest_ty {
                    Ty::Tuple(fields) if fields.len() == 2 => fields[0].clone(),
                    _ => return false,
                }
            } else {
                dest_ty
            };
            match value_ty {
                Ty::Int { width, .. } => width,
                _ => return false,
            }
        }
        _ => return false,
    };
    amount_val < u128::from(value_width)
}

/// D2 mirror of `lower.rs::is_arbitrary_precision_overflow_assert` over the
/// reachable dump shapes (projection-free local LHS, `Ref`/`RawPtr` peeled).
/// INERT over serde-loaded corpora — `Ty::Adt::arbitrary_precision` is
/// `#[serde(skip)]` — see the module docs.
pub fn arbitrary_precision_overflow_annotation(
    locals: &[LocalDecl],
    blocks: &[BasicBlock],
    source_block: trust_types::BlockId,
    target: trust_types::BlockId,
    msg: &AssertMessage,
) -> bool {
    let op = match msg {
        AssertMessage::Overflow(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul)) => *op,
        _ => return false,
    };
    let block_by_id = |id| blocks.iter().find(|b| b.id == id);
    let Some((lhs, _rhs)) = block_by_id(source_block)
        .and_then(|b| crate::lower::find_block_binary_operands(b, op))
        .or_else(|| {
            block_by_id(target).and_then(|b| crate::lower::find_block_binary_operands(b, op))
        })
    else {
        return false;
    };
    let place = match lhs {
        Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p,
        _ => return false,
    };
    let Some(decl) = locals.iter().find(|d| d.index == place.local) else { return false };
    let mut governing = &decl.ty;
    loop {
        match governing {
            Ty::Ref { inner, .. } => governing = inner,
            Ty::RawPtr { pointee, .. } => governing = pointee,
            other => {
                return match other {
                    Ty::Adt { arbitrary_precision: Some(AdtAuth::ArbPrec(kind)), .. } => {
                        if op == BinOp::Sub {
                            matches!(kind, ArbPrecKind::Signed)
                        } else {
                            matches!(kind, ArbPrecKind::Signed | ArbPrecKind::Unsigned)
                        }
                    }
                    _ => false,
                };
            }
        }
    }
}

/// Classify a NON-six-class assert message into its named non-coverage code.
/// `Err` on an unknown variant — `AssertMessage` is `#[non_exhaustive]` and
/// an unclassified kind must fail closed, never land in a wildcard bucket.
fn noncoverage_code(msg: &AssertMessage) -> Result<&'static str, String> {
    Ok(match msg {
        AssertMessage::ResumedAfterReturn
        | AssertMessage::ResumedAfterPanic
        | AssertMessage::ResumedAfterDrop => NONCOVERAGE_COROUTINE_RESUME,
        AssertMessage::MisalignedPointerDereference => NONCOVERAGE_MISALIGNED_PTR,
        AssertMessage::NullPointerDereference => NONCOVERAGE_NULL_PTR,
        AssertMessage::InvalidEnumConstruction => NONCOVERAGE_INVALID_ENUM,
        AssertMessage::Custom(_) => NONCOVERAGE_CUSTOM_ASSERT,
        AssertMessage::Overflow(_) => NONCOVERAGE_OVERFLOW_OTHER,
        other => {
            return Err(format!(
                "unknown AssertMessage variant {other:?} — AssertMessage is #[non_exhaustive]; \
                 extend the set-parity taxonomy in a reviewed change (fail closed)"
            ));
        }
    })
}

// ---------------------------------------------------------------------------
// Mode 1: MIR-set census (no direct side — the comparee enumerated).
// ---------------------------------------------------------------------------

/// The enumeration-mode output: what the comparee looks like over a corpus
/// with NO direct-lane artifacts (the 61-fixture measurement). It classifies
/// nothing as missing — it names what a set-parity run over these bodies
/// would have to pair, and where the shape predicates fire.
#[derive(Debug, Default)]
pub struct MirSetCensus {
    pub asserts_total: usize,
    pub six_class: usize,
    /// Six-class asserts by the eight reporting labels.
    pub per_class: BTreeMap<&'static str, usize>,
    /// B-class asserts by enumerated code.
    pub noncoverage: BTreeMap<&'static str, usize>,
    /// Enumerated const-index shape hits (`scope L{l}C{c}: K<N` strings).
    pub const_index_in_bounds: Vec<String>,
    pub const_index_out_of_bounds: Vec<String>,
    /// D-code annotation counts.
    pub discharge_annotated: BTreeMap<&'static str, usize>,
}

/// Enumerate the comparee over a corpus (fail-closed on unknown assert
/// kinds and duplicate def_paths).
pub fn classify_mir_assert_set(
    corpus: &[(String, VerifiableFunction)],
) -> Result<MirSetCensus, Vec<String>> {
    let mut errors: Vec<String> = Vec::new();
    let mut seen_scopes: BTreeSet<&str> = BTreeSet::new();
    for (_, func) in corpus {
        if !seen_scopes.insert(func.def_path.as_str()) {
            errors.push(format!(
                "corpus def_path {:?} appears twice — enumeration would double-count",
                func.def_path
            ));
        }
    }
    let mut census = MirSetCensus::default();
    for (_, func) in corpus {
        let locals = &func.body.locals;
        for block in &func.body.blocks {
            let Terminator::Assert { cond, msg, target, span, .. } = &block.terminator else {
                continue;
            };
            census.asserts_total += 1;
            if slug_for_assert_message(msg).is_none() {
                match noncoverage_code(msg) {
                    Ok(code) => *census.noncoverage.entry(code).or_default() += 1,
                    Err(err) => errors.push(format!("{}: {err}", func.def_path)),
                }
                continue;
            }
            census.six_class += 1;
            *census.per_class.entry(class_label(msg)).or_default() += 1;
            let site = format!("{} L{}C{}", func.def_path, span.line_start, span.col_start);
            match const_index_bounds_shape(func, block, cond, msg) {
                Some(ConstIndexShape::InBounds { k, n }) => {
                    census.const_index_in_bounds.push(format!("{site}: {k}<{n}"));
                }
                Some(ConstIndexShape::OutOfBounds { k, n }) => {
                    census.const_index_out_of_bounds.push(format!("{site}: {k}>={n}"));
                }
                None => {}
            }
            if literal_shift_in_range_annotation(locals, &func.body.blocks, block.id, *target, msg)
            {
                *census.discharge_annotated.entry(DISCHARGE_LITERAL_SHIFT).or_default() += 1;
            }
            if arbitrary_precision_overflow_annotation(
                locals,
                &func.body.blocks,
                block.id,
                *target,
                msg,
            ) {
                *census.discharge_annotated.entry(DISCHARGE_ARBITRARY_PRECISION).or_default() += 1;
            }
        }
    }
    if errors.is_empty() { Ok(census) } else { Err(errors) }
}

pub fn print_mir_set_census(label: &str, census: &MirSetCensus) {
    println!("== M2 MIR-SET CENSUS ({label}) ==");
    println!("   assert terminators: {}", census.asserts_total);
    println!("   six-class (pairing-eligible): {}", census.six_class);
    println!("   per-class: {:?}", census.per_class);
    println!("   named non-coverage: {:?}", census.noncoverage);
    println!(
        "   const-index shapes: in-bounds {:?}, out-of-bounds {:?}",
        census.const_index_in_bounds, census.const_index_out_of_bounds
    );
    println!("   discharge annotations: {:?}", census.discharge_annotated);
}

// ---------------------------------------------------------------------------
// Mode 2: full set parity (records + corpus + census).
// ---------------------------------------------------------------------------

/// Compare the direct set (dumped records) against the MIR assert set
/// (corpus) per site, consulting the function census to split C1 from C3.
/// `Err` on ANY unclassifiable asymmetry — see the module docs' taxonomy.
pub fn set_parity(
    records: &[DumpedDirectRecord],
    corpus: &[(String, VerifiableFunction)],
    census: &DirectFunctionCensus,
) -> Result<(SetParityScorecard, Vec<SiteRow>), Vec<String>> {
    let mut errors: Vec<String> = Vec::new();

    // Version belt (the parser refuses too; re-checked so a hand-built list
    // cannot bypass it).
    for record in records {
        if record.v != DIRECT_FORMULA_DUMP_VERSION {
            errors.push(format!(
                "record {} carries unknown version {:?}",
                record.assertion_id, record.v
            ));
        }
    }
    // Duplicate identity belts (assertion_id and the positional key).
    let mut seen_ids: BTreeSet<(&str, &str)> = BTreeSet::new();
    for record in records {
        if !seen_ids.insert((record.krate.as_str(), record.assertion_id.as_str())) {
            errors.push(format!(
                "duplicate dumped identity ({}, {})",
                record.krate, record.assertion_id
            ));
        }
    }
    // (scope, slug, line, col) -> occ -> record index.
    let mut index: BTreeMap<(String, String, u32, u32), BTreeMap<u32, usize>> = BTreeMap::new();
    for (i, record) in records.iter().enumerate() {
        let scope = format!("{}::{}", record.krate, record.def_path);
        let group = index.entry((scope, record.slug.clone(), record.line, record.col)).or_default();
        if group.insert(record.occ, i).is_some() {
            errors.push(format!(
                "duplicate dumped identity: two records at ({}::{}, {}, L{}C{}, o{})",
                record.krate, record.def_path, record.slug, record.line, record.col, record.occ
            ));
        }
    }
    // Corpus scope uniqueness (per-def comparee; per-mono is Step-6/7).
    let mut by_scope: BTreeMap<&str, &VerifiableFunction> = BTreeMap::new();
    for (_, func) in corpus {
        if by_scope.insert(func.def_path.as_str(), func).is_some() {
            errors.push(format!(
                "corpus def_path {:?} appears twice — pairing would be ambiguous",
                func.def_path
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    let mut rows: Vec<SiteRow> = Vec::new();
    let mut consumed: BTreeSet<usize> = BTreeSet::new();

    for (scope, func) in &by_scope {
        let locals = &func.body.locals;
        // Six-class groups at SLUG granularity in block order (the dumped
        // occ is used VERBATIM against this ordinal).
        let mut groups: BTreeMap<(&'static str, u32, u32), Vec<&BasicBlock>> = BTreeMap::new();
        for block in &func.body.blocks {
            let Terminator::Assert { msg, span, target, .. } = &block.terminator else {
                continue;
            };
            let Some(slug) = slug_for_assert_message(msg) else {
                // B-class: MIR-only by KIND — enumerated per instance.
                match noncoverage_code(msg) {
                    Ok(code) => rows.push(SiteRow {
                        scope: (*scope).to_string(),
                        class_label: class_label(msg),
                        line: span.line_start,
                        col: span.col_start,
                        occ: 0,
                        disposition: SiteDisposition::MirOnly(code),
                        discharge: discharge_annotation(
                            locals,
                            &func.body.blocks,
                            block.id,
                            *target,
                            msg,
                        ),
                        detail: String::new(),
                    }),
                    Err(err) => errors.push(format!("{scope}: {err}")),
                }
                continue;
            };
            groups.entry((slug, span.line_start, span.col_start)).or_default().push(block);
        }

        for ((slug, line, col), asserts) in groups {
            let record_group = index.get(&((*scope).to_string(), slug.to_string(), line, col));
            match record_group {
                Some(record_group) => {
                    consumed.extend(record_group.values());
                    if record_group.len() != asserts.len() {
                        // Collision-group partial pairing: guessing which
                        // assert lacks a row is exactly what the
                        // non-injectivity pin forbids.
                        errors.push(format!(
                            "collision-group size mismatch at ({scope}, {slug}, L{line}C{col}): \
                             {} dumped record(s) vs {} MIR assert(s) — refusing to guess a \
                             partial pairing",
                            record_group.len(),
                            asserts.len()
                        ));
                        continue;
                    }
                    for (mir_occ, block) in asserts.iter().enumerate() {
                        let mir_occ = u32::try_from(mir_occ).expect("occ fits u32");
                        if !record_group.contains_key(&mir_occ) {
                            errors.push(format!(
                                "collision-group occ skew at ({scope}, {slug}, L{line}C{col}): \
                                 no dumped record carries o{mir_occ} though the group sizes \
                                 match — the dumped occ is used verbatim, never re-derived"
                            ));
                            continue;
                        }
                        let Terminator::Assert { msg, target, .. } = &block.terminator else {
                            continue;
                        };
                        rows.push(SiteRow {
                            scope: (*scope).to_string(),
                            class_label: class_label(msg),
                            line,
                            col,
                            occ: mir_occ,
                            disposition: SiteDisposition::Both,
                            discharge: discharge_annotation(
                                locals,
                                &func.body.blocks,
                                block.id,
                                *target,
                                msg,
                            ),
                            detail: String::new(),
                        });
                    }
                }
                None => {
                    // No direct row at this site: the census splits the
                    // reasons, fail-closed.
                    let Some(body) = census.bodies.get(*scope) else {
                        errors.push(format!(
                            "no census body row for {scope} — cannot split \
                             body-outside-fragment from a per-site gap; supply the \
                             coverage.json census of the same compilation (fail closed)"
                        ));
                        continue;
                    };
                    for (mir_occ, block) in asserts.iter().enumerate() {
                        let mir_occ = u32::try_from(mir_occ).expect("occ fits u32");
                        let Terminator::Assert { cond, msg, target, .. } = &block.terminator else {
                            continue;
                        };
                        let shape = const_index_bounds_shape(func, block, cond, msg);
                        let discharge =
                            discharge_annotation(locals, &func.body.blocks, block.id, *target, msg);
                        if body.clean_and_spliced() {
                            match shape {
                                Some(ConstIndexShape::InBounds { k, n }) => rows.push(SiteRow {
                                    scope: (*scope).to_string(),
                                    class_label: class_label(msg),
                                    line,
                                    col,
                                    occ: mir_occ,
                                    disposition: SiteDisposition::MirOnly(
                                        REASON_MISSING_CONST_INDEX_BOUNDS,
                                    ),
                                    discharge,
                                    detail: format!("const index {k} < len {n}"),
                                }),
                                Some(ConstIndexShape::OutOfBounds { k, n }) => {
                                    // The state deleting the #191 refusal
                                    // would produce: an OOB const index in a
                                    // body the direct lane claims it lowered
                                    // clean. Hard error — this is the
                                    // comparator's refusal tripwire.
                                    errors.push(format!(
                                        "({scope}, {slug}, L{line}C{col}, o{mir_occ}): OOB \
                                         const-index site ({k} >= {n}) inside a lowered-clean \
                                         body — the #191 OOB refusal did not fire; a constant \
                                         OOB index must refuse the whole body, never lower \
                                         (fail closed)"
                                    ));
                                }
                                None => {
                                    errors.push(format!(
                                        "({scope}, {slug}, L{line}C{col}, o{mir_occ}): \
                                         six-class MIR assert with no direct record in a \
                                         lowered-clean body matches NO enumerated shape \
                                         predicate — a new missing-row class must enter the \
                                         set-parity taxonomy in a reviewed change (fail \
                                         closed)"
                                    ));
                                }
                            }
                        } else {
                            // Not clean/spliced: function-level absence.
                            let reason = match shape {
                                Some(ConstIndexShape::OutOfBounds { .. }) => {
                                    REASON_OOB_CONST_INDEX_BODY_REFUSED
                                }
                                _ => REASON_OUTSIDE_DIRECT_FRAGMENT,
                            };
                            rows.push(SiteRow {
                                scope: (*scope).to_string(),
                                class_label: class_label(msg),
                                line,
                                col,
                                occ: mir_occ,
                                disposition: SiteDisposition::MirOnly(reason),
                                discharge,
                                detail: format!(
                                    "census: lowered={} spliced={} unsupported={:?}",
                                    body.lowered, body.spliced, body.unsupported
                                ),
                            });
                        }
                    }
                }
            }
        }
    }

    // E-class: a direct set row pairing no MIR assert is a hard error.
    for (i, record) in records.iter().enumerate() {
        if !consumed.contains(&i) {
            errors.push(format!(
                "direct-only set row: ({}::{}, {}, L{}C{}, o{}) pairs no MIR assert in the \
                 corpus — every direct recording site mirrors a built-MIR assert by \
                 construction, so this is a hard error (fail closed)",
                record.krate, record.def_path, record.slug, record.line, record.col, record.occ
            ));
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    let mut card = tally_site_rows(&rows);
    card.direct_rows = records.len();
    card.direct_not_minted =
        records.iter().filter(|r| matches!(r.outcome, DumpedOutcome::NotMinted(_))).count();
    Ok((card, rows))
}

/// Both D annotations folded to at most one code (they are disjoint by
/// message class: D1 is `Shl|Shr`, D2 is `Add|Sub|Mul`).
fn discharge_annotation(
    locals: &[LocalDecl],
    blocks: &[BasicBlock],
    source_block: trust_types::BlockId,
    target: trust_types::BlockId,
    msg: &AssertMessage,
) -> Option<&'static str> {
    if literal_shift_in_range_annotation(locals, blocks, source_block, target, msg) {
        return Some(DISCHARGE_LITERAL_SHIFT);
    }
    if arbitrary_precision_overflow_annotation(locals, blocks, source_block, target, msg) {
        return Some(DISCHARGE_ARBITRARY_PRECISION);
    }
    None
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use trust_types::{
        BasicBlock, BlockId, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
        UnwindEdge, VerifiableBody, VerifiableFunction,
    };

    use super::*;
    use crate::direct_formula_dump::parse_direct_formula_dump;
    use crate::direct_record_grading::{count_six_class_asserts, load_corpus_dir};

    fn span(line: u32, col: u32) -> SourceSpan {
        SourceSpan {
            file: "m2.rs".to_string(),
            line_start: line,
            col_start: col,
            line_end: line,
            col_end: col + 4,
        }
    }

    /// The measured cpick MIR shape: `fn f(a: [i32; N]) -> i32 { a[K] }` —
    /// `_2 = const K; _3 = Lt(_2, const N); assert(BoundsCheck)`.
    fn const_index_read_func(k: u128, n: u128) -> VerifiableFunction {
        VerifiableFunction {
            name: "cpick".to_string(),
            def_path: "m2crate::cpick".to_string(),
            span: span(2, 35),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: true }, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Array {
                            elem: Box::new(Ty::Int { width: 32, signed: true }),
                            len: 7,
                        },
                        name: Some("a".to_string()),
                    },
                    LocalDecl { index: 2, ty: Ty::Int { width: 64, signed: false }, name: None },
                    LocalDecl { index: 3, ty: Ty::Bool, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            Statement::Assign {
                                place: Place::local(2),
                                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(k, 64))),
                                span: span(2, 37),
                            },
                            Statement::Assign {
                                place: Place::local(3),
                                rvalue: Rvalue::BinaryOp(
                                    BinOp::Lt,
                                    Operand::Copy(Place::local(2)),
                                    Operand::Constant(ConstValue::Uint(n, 64)),
                                ),
                                span: span(2, 35),
                            },
                        ],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::BoundsCheck,
                            target: BlockId(1),
                            span: span(2, 35),
                            unwind: UnwindEdge::Continue,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Int { width: 32, signed: true },
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    /// The dpick shape: dynamic index (the compare LHS is a named param —
    /// no in-block constant def).
    fn dynamic_index_func() -> VerifiableFunction {
        let mut func = const_index_read_func(0, 7);
        func.name = "dpick".to_string();
        func.def_path = "m2crate::dpick".to_string();
        func.body.arg_count = 2;
        func.body.locals[2].name = Some("i".to_string());
        func.body.blocks[0].stmts.remove(0); // drop the const def
        func
    }

    fn coroutine_func() -> VerifiableFunction {
        let mut func = const_index_read_func(0, 7);
        func.name = "coro".to_string();
        func.def_path = "m2crate::coro".to_string();
        func.body.blocks[0].stmts.clear();
        func.body.blocks[0].terminator = Terminator::Assert {
            cond: Operand::Move(Place::local(3)),
            expected: true,
            msg: AssertMessage::ResumedAfterReturn,
            target: BlockId(1),
            span: span(9, 1),
            unwind: UnwindEdge::Continue,
        };
        func
    }

    fn clean_census(scopes: &[&str]) -> DirectFunctionCensus {
        let mut census = DirectFunctionCensus::default();
        for scope in scopes {
            census.bodies.insert(
                (*scope).to_string(),
                CensusBody { lowered: true, spliced: true, unsupported: vec![] },
            );
        }
        census
    }

    fn refused_census(scope: &str, tag: &str) -> DirectFunctionCensus {
        let mut census = DirectFunctionCensus::default();
        census.bodies.insert(
            scope.to_string(),
            CensusBody { lowered: false, spliced: false, unsupported: vec![tag.to_string()] },
        );
        census
    }

    fn bounds_record(def_path: &str, line: u32, col: u32, occ: u32) -> DumpedDirectRecord {
        DumpedDirectRecord {
            v: DIRECT_FORMULA_DUMP_VERSION.to_string(),
            krate: "m2crate".to_string(),
            def_path: def_path.to_string(),
            def_index: 0,
            slug: "bounds_check".to_string(),
            line,
            col,
            occ,
            assertion_id: format!("m2crate::{def_path}#L{line}C{col}#bounds_check#o{occ}"),
            block: 0,
            inst_index: 2,
            outcome: DumpedOutcome::NotMinted(true),
        }
    }

    fn corpus_of(funcs: Vec<VerifiableFunction>) -> Vec<(String, VerifiableFunction)> {
        funcs.into_iter().map(|f| (f.name.clone(), f)).collect()
    }

    /// BASELINE C1: the cpick shape with no direct record in a lowered-clean
    /// body classifies missing-const-index-bounds — the M2 top gap, per
    /// site, enumerated.
    #[test]
    fn const_index_site_with_no_record_classifies_c1() {
        let corpus = corpus_of(vec![const_index_read_func(3, 7)]);
        let census = clean_census(&["m2crate::cpick"]);
        let (card, rows) = set_parity(&[], &corpus, &census).expect("classifies");
        assert_eq!(card.mir_only.get(REASON_MISSING_CONST_INDEX_BOUNDS), Some(&1));
        assert_eq!(card.both, 0);
        assert_eq!(rows.len(), 1);
        assert!(rows[0].detail.contains("const index 3 < len 7"), "{:?}", rows[0].detail);
    }

    /// POST-FIX: the same site WITH the bounds record the fixed constant arm
    /// mints pairs "both" — the C1 class goes to zero on the fixtures that
    /// exercise it. This is the crate-level half of the fix's proof; the
    /// driver re-measure in the main loop re-takes it on real artifacts.
    #[test]
    fn const_index_site_with_the_fixed_arms_record_pairs_both_and_c1_is_zero() {
        let corpus = corpus_of(vec![const_index_read_func(3, 7)]);
        let census = clean_census(&["m2crate::cpick"]);
        let records = vec![bounds_record("cpick", 2, 35, 0)];
        let (card, _) = set_parity(&records, &corpus, &census).expect("pairs");
        assert_eq!(card.mir_only.get(REASON_MISSING_CONST_INDEX_BOUNDS), None);
        assert_eq!(card.both, 1);
        assert_eq!(card.both_per_class.get("bounds-check"), Some(&1));
        // The record is a set row regardless of its formula outcome.
        assert_eq!(card.direct_rows, 1);
        assert_eq!(card.direct_not_minted, 1);
    }

    /// C2: the OOB shape under a census that confirms the #191 refusal.
    #[test]
    fn oob_const_index_with_refused_census_classifies_c2() {
        let corpus = corpus_of(vec![const_index_read_func(9, 7)]);
        let census = refused_census("m2crate::cpick", "Index(const index out of bounds)");
        let (card, _) = set_parity(&[], &corpus, &census).expect("classifies");
        assert_eq!(card.mir_only.get(REASON_OOB_CONST_INDEX_BODY_REFUSED), Some(&1));
    }

    /// THE REFUSAL TRIPWIRE: an OOB const-index site inside a body the
    /// census says lowered CLEAN is exactly the state deleting the #191 OOB
    /// refusal would produce — the comparator hard-errors instead of
    /// classifying, so the mutation cannot pass a set-parity run.
    #[test]
    fn oob_const_index_in_a_lowered_clean_body_is_a_hard_error() {
        let corpus = corpus_of(vec![const_index_read_func(9, 7)]);
        let census = clean_census(&["m2crate::cpick"]);
        let errs = set_parity(&[], &corpus, &census).expect_err("must refuse");
        assert!(errs.iter().any(|e| e.contains("the #191 OOB refusal did not fire")), "{errs:?}");
    }

    /// FAIL-CLOSED ON NEW CLASSES: a six-class assert with no record in a
    /// lowered-clean body that matches NO shape predicate refuses — a
    /// missing-row class silently dropped from the taxonomy cannot grade.
    #[test]
    fn unclassifiable_missing_row_fails_closed() {
        let corpus = corpus_of(vec![dynamic_index_func()]);
        let census = clean_census(&["m2crate::dpick"]);
        let errs = set_parity(&[], &corpus, &census).expect_err("must refuse");
        assert!(
            errs.iter().any(|e| e.contains("matches NO enumerated shape predicate")),
            "{errs:?}"
        );
    }

    /// C3: the same dynamic shape under a refused census is function-level
    /// absence, enumerated.
    #[test]
    fn dynamic_site_under_refused_census_classifies_c3() {
        let corpus = corpus_of(vec![dynamic_index_func()]);
        let census = refused_census("m2crate::dpick", "Index(borrow ptr base)");
        let (card, rows) = set_parity(&[], &corpus, &census).expect("classifies");
        assert_eq!(card.mir_only.get(REASON_OUTSIDE_DIRECT_FRAGMENT), Some(&1));
        assert!(rows[0].detail.contains("Index(borrow ptr base)"), "{:?}", rows[0].detail);
    }

    /// E-class: a fabricated direct-only row must FAIL — no legitimate
    /// direct-only class exists.
    #[test]
    fn a_fabricated_direct_only_row_fails() {
        let corpus = corpus_of(vec![const_index_read_func(3, 7)]);
        let census = clean_census(&["m2crate::cpick"]);
        // Same function, a site no MIR assert occupies.
        let records = vec![bounds_record("cpick", 40, 1, 0)];
        let errs = set_parity(&records, &corpus, &census).expect_err("must refuse");
        assert!(errs.iter().any(|e| e.contains("direct-only set row")), "{errs:?}");
        // And a record naming a function the corpus does not hold.
        let records = vec![bounds_record("nosuch", 2, 35, 0)];
        let errs = set_parity(&records, &corpus, &census).expect_err("must refuse");
        assert!(errs.iter().any(|e| e.contains("direct-only set row")), "{errs:?}");
    }

    /// Collision-group partial pairing refuses (never guesses which assert
    /// lacks a row).
    #[test]
    fn partial_collision_group_fails_closed() {
        // Two same-(slug,line,col) asserts, one record.
        let mut func = const_index_read_func(3, 7);
        let mut twin_block = func.body.blocks[0].clone();
        twin_block.id = BlockId(2);
        if let Terminator::Assert { target, .. } = &mut twin_block.terminator {
            *target = BlockId(1);
        }
        func.body.blocks.push(twin_block);
        let corpus = corpus_of(vec![func]);
        let census = clean_census(&["m2crate::cpick"]);
        let records = vec![bounds_record("cpick", 2, 35, 0)];
        let errs = set_parity(&records, &corpus, &census).expect_err("must refuse");
        assert!(errs.iter().any(|e| e.contains("collision-group size mismatch")), "{errs:?}");
    }

    /// A missing census row refuses rather than guessing C1 vs C3.
    #[test]
    fn missing_census_row_fails_closed() {
        let corpus = corpus_of(vec![const_index_read_func(3, 7)]);
        let errs =
            set_parity(&[], &corpus, &DirectFunctionCensus::default()).expect_err("must refuse");
        assert!(errs.iter().any(|e| e.contains("no census body row")), "{errs:?}");
    }

    /// B-class asserts are enumerated per instance, never skipped.
    #[test]
    fn noncoverage_asserts_are_enumerated_never_skipped() {
        let corpus = corpus_of(vec![coroutine_func()]);
        // Deliberately NO census row for coro: B-class classification is by
        // KIND and must not require one.
        let (card, rows) =
            set_parity(&[], &corpus, &DirectFunctionCensus::default()).expect("classifies");
        assert_eq!(card.noncoverage.get(NONCOVERAGE_COROUTINE_RESUME), Some(&1));
        assert_eq!(card.mir_asserts_total, 1);
        assert_eq!(rows.len(), 1);
    }

    /// D1 annotation: a literal in-range shift annotates its row without
    /// excusing anything.
    #[test]
    fn literal_shift_discharge_annotates_the_row() {
        let func = VerifiableFunction {
            name: "shl".to_string(),
            def_path: "m2crate::shl".to_string(),
            span: span(5, 1),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: false }, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: false },
                        name: Some("x".to_string()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Tuple(vec![Ty::Int { width: 32, signed: false }, Ty::Bool]),
                        name: None,
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Shl,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(3, 32)),
                            ),
                            span: span(5, 9),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Move(Place {
                                local: 2,
                                projections: vec![trust_types::Projection::Field(1)],
                            }),
                            expected: false,
                            msg: AssertMessage::Overflow(BinOp::Shl),
                            target: BlockId(1),
                            span: span(5, 9),
                            unwind: UnwindEdge::Continue,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Int { width: 32, signed: false },
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        let corpus = corpus_of(vec![func]);
        // A record exists (the direct lane does NOT discharge literal
        // shifts): the site pairs both, and the annotation discloses the
        // bridge-side discharge.
        let mut record = bounds_record("shl", 5, 9, 0);
        record.slug = "overflow".to_string();
        record.assertion_id = "m2crate::shl#L5C9#overflow#o0".to_string();
        let census = clean_census(&["m2crate::shl"]);
        let (card, rows) = set_parity(&[record], &corpus, &census).expect("pairs");
        assert_eq!(card.both, 1);
        assert_eq!(card.discharge_annotated.get(DISCHARGE_LITERAL_SHIFT), Some(&1));
        assert_eq!(rows[0].discharge, Some(DISCHARGE_LITERAL_SHIFT));
    }

    /// The census-mode enumeration over the same synthetic bodies.
    #[test]
    fn census_mode_enumerates_shapes_and_kinds() {
        let corpus =
            corpus_of(vec![const_index_read_func(3, 7), dynamic_index_func(), coroutine_func()]);
        let census = classify_mir_assert_set(&corpus).expect("enumerates");
        assert_eq!(census.asserts_total, 3);
        assert_eq!(census.six_class, 2);
        assert_eq!(census.noncoverage.get(NONCOVERAGE_COROUTINE_RESUME), Some(&1));
        assert_eq!(census.const_index_in_bounds.len(), 1);
        assert!(census.const_index_in_bounds[0].contains("3<7"));
        assert_eq!(census.const_index_out_of_bounds.len(), 0);
    }

    /// The coverage.json loader: fail-closed on schema, faithful on the v2
    /// shape.
    #[test]
    fn census_loader_is_fail_closed() {
        let good = r#"{"schema":"trust.thir-lower.crate-module.coverage.v2","crate":"c",
            "bodies":[{"def_path":"f","lowered":true,"spliced":true,"unsupported":[]}]}"#;
        let census = load_census_from_coverage_json(good).expect("loads");
        assert!(census.bodies.get("c::f").expect("body").clean_and_spliced());

        let unknown_schema = good.replace("coverage.v2", "coverage.v99");
        let err = load_census_from_coverage_json(&unknown_schema).expect_err("must refuse");
        assert!(err.contains("refusing to guess census semantics"), "{err}");

        let refused = r#"{"schema":"trust.thir-lower.crate-module.coverage.v2","crate":"c",
            "bodies":[{"def_path":"g","lowered":true,"spliced":false,
                       "unsupported":[["span","Index(const index out of bounds)"]]}]}"#;
        let census = load_census_from_coverage_json(refused).expect("loads");
        let body = census.bodies.get("c::g").expect("body");
        assert!(!body.clean_and_spliced());
        assert_eq!(body.unsupported, vec!["Index(const index out of bounds)".to_string()]);
    }

    /// THE M2 CORPUS MEASUREMENT: the 61-fixture vcgen corpus, enumerated in
    /// census mode (no direct artifacts exist for these bodies — the
    /// comparee is what a set-parity run would have to pair). Ratchets, not
    /// snapshots: fixture additions may grow the numbers, never shrink them;
    /// the zero const-index count is the measured fact that the corpus does
    /// NOT exercise the C1 class (the probe artifacts do).
    #[test]
    fn m2_corpus_census_ratchet() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-vcgen/tests/data");
        let corpus = load_corpus_dir(&dir);
        let census = classify_mir_assert_set(&corpus).expect("the corpus must enumerate");
        print_mir_set_census("61-fixture vcgen corpus", &census);
        assert_eq!(census.six_class, count_six_class_asserts(&corpus));
        assert!(census.asserts_total >= 142, "total {}", census.asserts_total);
        assert!(census.six_class >= 136, "six-class {}", census.six_class);
        assert!(
            census.noncoverage.get(NONCOVERAGE_COROUTINE_RESUME).copied().unwrap_or(0) >= 6,
            "{:?}",
            census.noncoverage
        );
        // Measured: every corpus BoundsCheck is dynamic — exercising C1
        // needs the probe fixtures.
        assert_eq!(census.const_index_in_bounds, Vec::<String>::new());
        assert_eq!(census.const_index_out_of_bounds, Vec::<String>::new());
        // The B/six-class split is exhaustive: nothing was skipped.
        let noncoverage_total: usize = census.noncoverage.values().sum();
        assert_eq!(census.asserts_total, census.six_class + noncoverage_total);
    }

    /// M2/Step-6 continuity: the FIXED constant arm records via
    /// `record_direct_assert_typed` with a `Bounds` shape whose index is the
    /// open-block `Const` the train just pushed, which the capture resolves
    /// to a LITERAL operand — so the typed-formula lane MINTS for the fixed
    /// arm (never a withhold by construction). Pins the minted bytes the
    /// post-fix projection artifacts embed.
    #[test]
    fn fixed_const_arm_lit_index_bounds_shape_mints() {
        use crate::safety_formulas::{
            DirectFormulaClass, DirectFormulaOperand, mint_direct_safety_formula,
        };
        let minted = mint_direct_safety_formula(
            &DirectFormulaClass::BoundsCheck { len: 7 },
            64,
            false,
            &[DirectFormulaOperand::Lit(3)],
        )
        .expect("a literal in-bounds index must mint");
        println!("lit-3-len-7 formula_json: {}", minted.formula_json);
        println!("lit-3-len-7 smtlib: {}", minted.smtlib);
        let minted_write = mint_direct_safety_formula(
            &DirectFormulaClass::BoundsCheck { len: 5 },
            64,
            false,
            &[DirectFormulaOperand::Lit(2)],
        )
        .expect("a literal in-bounds index must mint");
        println!("lit-2-len-5 formula_json: {}", minted_write.formula_json);
        println!("lit-2-len-5 smtlib: {}", minted_write.smtlib);
    }

    /// Env-keyed driver: TRUST_DIRECT_SET_RECORDS_JSONL +
    /// TRUST_DIRECT_SET_MIR_CORPUS + TRUST_DIRECT_SET_COVERAGE_JSON run the
    /// full set-parity comparison over real artifacts. `#[ignore]`d, and it
    /// panics when any of the three is unset, so a bare `--ignored` run cannot
    /// pass having compared nothing.
    #[test]
    #[ignore = "measurement driver: set TRUST_DIRECT_SET_RECORDS_JSONL, \
                TRUST_DIRECT_SET_MIR_CORPUS and TRUST_DIRECT_SET_COVERAGE_JSON and run with \
                --ignored --nocapture"]
    fn set_parity_env_driver() {
        const RECIPE: &str = "TRUST_DIRECT_SET_RECORDS_JSONL=<a *.direct-formulas.jsonl> \
             TRUST_DIRECT_SET_MIR_CORPUS=<dir of VerifiableFunction json> \
             TRUST_DIRECT_SET_COVERAGE_JSON=<the same compilation's coverage.json> \
             targo --unverified test --manifest-path crates/Cargo.toml -p trust-ir-bridge \
             --lib -- --ignored --exact direct_set_parity::tests::set_parity_env_driver \
             --nocapture";
        fn unset(var: &str) -> ! {
            panic!(
                "set_parity_env_driver is a measurement driver and {var} is unset, so it \
                 compared nothing. Run: {RECIPE}"
            )
        }
        let Some(records_path) = std::env::var_os("TRUST_DIRECT_SET_RECORDS_JSONL") else {
            unset("TRUST_DIRECT_SET_RECORDS_JSONL");
        };
        let Some(corpus_dir) = std::env::var_os("TRUST_DIRECT_SET_MIR_CORPUS") else {
            unset("TRUST_DIRECT_SET_MIR_CORPUS");
        };
        let Some(coverage_path) = std::env::var_os("TRUST_DIRECT_SET_COVERAGE_JSON") else {
            unset("TRUST_DIRECT_SET_COVERAGE_JSON");
        };
        let text = std::fs::read_to_string(PathBuf::from(&records_path))
            .expect("TRUST_DIRECT_SET_RECORDS_JSONL must be readable");
        let records = parse_direct_formula_dump(&text)
            .unwrap_or_else(|errs| panic!("dump refused (fail closed): {errs:#?}"));
        let corpus = load_corpus_dir(Path::new(&corpus_dir));
        let coverage = std::fs::read_to_string(PathBuf::from(&coverage_path))
            .expect("TRUST_DIRECT_SET_COVERAGE_JSON must be readable");
        let census = load_census_from_coverage_json(&coverage)
            .unwrap_or_else(|err| panic!("census refused (fail closed): {err}"));
        match set_parity(&records, &corpus, &census) {
            Ok((card, rows)) => {
                print_set_parity_scorecard("REAL artifacts", &card);
                for row in &rows {
                    println!(
                        "   row: {} [{}] L{}C{} o{} {:?} discharge={:?} {}",
                        row.scope,
                        row.class_label,
                        row.line,
                        row.col,
                        row.occ,
                        row.disposition,
                        row.discharge,
                        row.detail
                    );
                }
            }
            Err(errs) => panic!("set parity refused (fail closed): {errs:#?}"),
        }
    }
}
