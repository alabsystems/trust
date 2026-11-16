//! The SHARED Step-6 parity grading core (increment 2, item 1 —
//! docs/design/DIRECT-LANE-PROOF-AUTHORITY.md): one `Grade` vocabulary, one
//! `Scorecard`, one `grade_pair`, consumed by BOTH graders —
//!
//! * the in-situ model oracle (`safety_formulas::parity_oracle`), whose
//!   direct-lane side is a stated MODEL of the capture; and
//! * [`grade_real_records`], which feeds REAL dumped
//!   `DirectFormulaOutcome` records (the installer's
//!   `TRUST_DIRECT_FORMULA_DUMP` seam, `direct_formula_dump.rs`) to the SAME
//!   graders — the executable answer to increment 1's disclosed
//!   model-vs-real gap.
//!
//! Hoisted out of `#[cfg(test)] mod parity_oracle` verbatim where possible;
//! the oracle keeps `model_direct_case` and its battery and calls this core,
//! and its 41/41 + per-class-floor pins passing unchanged is the refactor's
//! own gate.
//!
//! FAIL-CLOSED DISCIPLINE of the real grader:
//! * unpaired dumped record, collision-group size mismatch (the
//!   `(slug, line, col)` non-injectivity pin), duplicate identity, unknown
//!   reason, unknown version — all hard errors, never skipped rows;
//! * a MIR six-class assert with NO dumped record lands in the enumerated
//!   `uncovered-by-direct-lane` bucket, never silently dropped;
//! * dumped formula bytes that parse to the bridge's own AST but differ from
//!   its canonical render are REFUSED as `non-canonical-formula-bytes`
//!   (a torn/tamper signal), not graded;
//! * the dumped `occ` is used VERBATIM — the MIR-side ordinal is grouped at
//!   SLUG granularity (slug `overflow` covers ALL `Overflow(binop)`
//!   messages; grouping by class label would skew the ordinal).
//!
//! Once real records exist they ARE the direct side: [`grade_real_records`]
//! calls no model code — the model survives only in the oracle tests and the
//! differential harness that proves the two graders agree.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::path::Path;

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{AssertMessage, BinOp, Formula, LocalDecl, Terminator, VerifiableFunction};

use crate::direct_formula_dump::{
    DIRECT_FORMULA_DUMP_VERSION, DumpedDirectRecord, DumpedOutcome, ENUMERATED_WITHHELD_REASONS,
};
use crate::flip::formula_eq_modulo_versions;
use crate::lower::{SafetyPredicate, reconstruct_assert_safety_predicate};
use crate::safety_formulas::MintedDirectFormula;

/// The grade one assert receives. `Unclassified` fails the master tests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Grade {
    /// Both lanes produced a formula and the ASTs are byte-identical
    /// (json/smtlib derivatives coherence-checked).
    ByteIdentical,
    /// Equal only modulo SSA version tokens — reported separately,
    /// expected 0 (neither lane's builders emit version tokens).
    VersionStrippedOnly,
    /// The direct side declined (by enumerated reason code); the bridge had a
    /// formula.
    MintDeclined(&'static str),
    /// The bridge declined; the direct side produced a formula nobody
    /// installs.
    BridgeDeclined,
    BothDeclined,
    /// The pinned structural known-mismatch class: a non-param local shadows
    /// a param name, so the MIR lane falls back to `_N` while the direct
    /// lane's param ledger keeps the name.
    KnownMismatchShadowedParamName,
    /// KNOWN MISMATCH `const-folded-operand` (M2 corpus, 2026-09-01): at a
    /// site whose checked operand is a compile-time constant, the direct lane
    /// mints the folded `Int(k)` while the bridge's block reconstruction
    /// names the materialized MIR temp `Var("_N", Int)`. The direct side
    /// carries strictly MORE information; folding on the bridge side would
    /// change production MIR-lane formula bytes. Neither lane is wrong;
    /// pinned rather than normalized away, exactly as shadowed-param-name.
    KnownMismatchConstFoldedOperand,
    /// KNOWN MISMATCH `literal-range-width` (M2 corpus, 2026-09-01): both
    /// lanes range-clamp a LITERAL operand with `lo <= k && k <= hi`, but
    /// assume different integer widths for the literal, so the (lo, hi)
    /// bounds differ while both conjuncts are vacuously true of the same k.
    KnownMismatchLiteralRangeWidth,
    /// KNOWN MISMATCH `let-bound-checked-intermediate` (M2 corpus,
    /// 2026-09-01, surfaced by Step 7 convergence Band A): at a site whose
    /// operand is the VALUE of a checked intermediate that the source
    /// LET-BINDS but rustc ELIDES (`let s = a + b; s - a` — no MIR local
    /// named `s` exists; the value flows as `_N.0`), the direct lane's
    /// value ledger spells the operand by its BINDING NAME (`Var("s")`)
    /// while the bridge's checked-pair chase composes the DEFINING op
    /// (`Add(a, b)`). The two spellings denote the same value by the
    /// binding's own definition; the name is unrecoverable bridge-side (it
    /// exists only in THIR) and the composition is what byte-mirrors the
    /// MIR lane. Neither lane is wrong; pinned rather than normalized,
    /// exactly as shadowed-param-name and const-folded-operand.
    KnownMismatchLetBoundCheckedIntermediate,
    /// The direct lane structurally holds NO comparable case here (model/site
    /// envelope, `uncovered-by-direct-lane` for real records, a `not_minted`
    /// record) — an exclusion, never a mismatch.
    Excluded(&'static str),
    Unclassified,
}

pub struct AssertReport {
    pub fixture: String,
    pub class_label: &'static str,
    pub grade: Grade,
    pub detail: String,
}

/// The tallied outcome. `PartialEq` + `Eq` so the model-vs-real differential
/// can assert field-for-field equality.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Scorecard {
    pub byte_identical: usize,
    pub version_stripped_only: usize,
    pub mint_declined: BTreeMap<&'static str, usize>,
    pub bridge_declined: usize,
    pub both_declined: usize,
    pub known_mismatch_shadowed_param_name: usize,
    pub known_mismatch_const_folded_operand: usize,
    pub known_mismatch_literal_range_width: usize,
    pub known_mismatch_let_bound_checked_intermediate: usize,
    pub excluded: BTreeMap<&'static str, usize>,
    pub unclassified: Vec<String>,
    /// class label -> (compared, byte_identical).
    pub per_class: BTreeMap<&'static str, (usize, usize)>,
}

impl Scorecard {
    /// Rows where BOTH lanes produced a formula (the "compared" number the
    /// design of record tracks: it must RISE with every envelope widening).
    pub fn compared(&self) -> usize {
        self.byte_identical
            + self.version_stripped_only
            + self.known_mismatch_shadowed_param_name
            + self.known_mismatch_const_folded_operand
            + self.known_mismatch_literal_range_width
            + self.known_mismatch_let_bound_checked_intermediate
            + self.unclassified.len()
    }
}

pub fn tally(reports: &[AssertReport]) -> Scorecard {
    let mut card = Scorecard::default();
    for report in reports {
        match &report.grade {
            Grade::ByteIdentical => {
                card.byte_identical += 1;
                let e = card.per_class.entry(report.class_label).or_default();
                e.0 += 1;
                e.1 += 1;
            }
            Grade::VersionStrippedOnly => {
                card.version_stripped_only += 1;
                card.per_class.entry(report.class_label).or_default().0 += 1;
            }
            Grade::MintDeclined(code) => *card.mint_declined.entry(code).or_default() += 1,
            Grade::BridgeDeclined => card.bridge_declined += 1,
            Grade::BothDeclined => card.both_declined += 1,
            Grade::KnownMismatchConstFoldedOperand => {
                card.known_mismatch_const_folded_operand += 1;
            }
            Grade::KnownMismatchLiteralRangeWidth => {
                card.known_mismatch_literal_range_width += 1;
            }
            Grade::KnownMismatchLetBoundCheckedIntermediate => {
                card.known_mismatch_let_bound_checked_intermediate += 1;
            }
            Grade::KnownMismatchShadowedParamName => {
                card.known_mismatch_shadowed_param_name += 1;
                card.per_class.entry(report.class_label).or_default().0 += 1;
            }
            Grade::Excluded(reason) => *card.excluded.entry(reason).or_default() += 1,
            Grade::Unclassified => card
                .unclassified
                .push(format!("{} [{}]\n{}", report.fixture, report.class_label, report.detail)),
        }
    }
    card
}

#[inline]
fn is_mir_temp(name: &str) -> bool {
    name.strip_prefix('_')
        .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
}

/// `const-folded-operand` recognizer: the two ASTs are equal at every position
/// EXCEPT positions where `ours` is a folded integer literal and `bridge` is a
/// materialized MIR temp `Var("_N", Int)` — and at least one such position
/// exists. Any other divergence disqualifies (stays Unclassified).
fn const_folded_operand_only(ours: &Formula, bridge: &Formula) -> bool {
    fn walk(a: &Formula, b: &Formula, hits: &mut usize) -> bool {
        use trust_types::Sort;
        if a == b {
            return true;
        }
        match (a, b) {
            (Formula::Int(_) | Formula::UInt(_), Formula::Var(name, Sort::Int))
                if is_mir_temp(name) =>
            {
                *hits += 1;
                true
            }
            (Formula::Not(x), Formula::Not(y)) => walk(x, y, hits),
            (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| walk(x, y, hits))
            }
            (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
            | (Formula::Eq(a1, a2), Formula::Eq(b1, b2))
            | (Formula::Lt(a1, a2), Formula::Lt(b1, b2))
            | (Formula::Le(a1, a2), Formula::Le(b1, b2))
            | (Formula::Gt(a1, a2), Formula::Gt(b1, b2))
            | (Formula::Ge(a1, a2), Formula::Ge(b1, b2))
            | (Formula::Add(a1, a2), Formula::Add(b1, b2))
            | (Formula::Sub(a1, a2), Formula::Sub(b1, b2))
            | (Formula::Mul(a1, a2), Formula::Mul(b1, b2))
            | (Formula::Div(a1, a2), Formula::Div(b1, b2))
            | (Formula::Rem(a1, a2), Formula::Rem(b1, b2)) => {
                walk(a1, b1, hits) && walk(a2, b2, hits)
            }
            _ => false,
        }
    }
    let mut hits = 0usize;
    walk(ours, bridge, &mut hits) && hits > 0
}

/// `literal-range-width` recognizer: the ASTs are equal EXCEPT at `Le` bounds
/// of a literal's range clamp — `Le(lo, k)` / `Le(k, hi)` with the SAME
/// literal `k` on both sides and both bounds drawn from the integer-type
/// extreme set (iN::MIN/MAX, uN::MAX, 0). At least one divergent bound must
/// exist; anything else disqualifies.
fn literal_range_width_only(ours: &Formula, bridge: &Formula) -> bool {
    fn is_type_extreme(v: i128) -> bool {
        matches!(
            v,
            0 | -0x80
                | 0x7f
                | -0x8000
                | 0x7fff
                | -0x8000_0000
                | 0x7fff_ffff
                | -0x8000_0000_0000_0000
                | 0x7fff_ffff_ffff_ffff
                | 0xff
                | 0xffff
                | 0xffff_ffff
                | 0xffff_ffff_ffff_ffff
        ) || v == i128::MIN
            || v == i128::MAX
    }
    fn walk(a: &Formula, b: &Formula, hits: &mut usize) -> bool {
        if a == b {
            return true;
        }
        match (a, b) {
            // Le(lo_a, k) vs Le(lo_b, k): divergent LOWER bounds of one literal.
            (Formula::Le(alo, ak), Formula::Le(blo, bk)) => {
                let lower_diverges = matches!((&**alo, &**blo),
                        (Formula::Int(x), Formula::Int(y))
                            if x != y && is_type_extreme(*x) && is_type_extreme(*y))
                    && ak == bk
                    && matches!(&**ak, Formula::Int(_) | Formula::UInt(_));
                let upper_diverges = matches!((&**ak, &**bk),
                        (Formula::Int(x), Formula::Int(y))
                            if x != y && is_type_extreme(*x) && is_type_extreme(*y))
                    && alo == blo
                    && matches!(&**alo, Formula::Int(_) | Formula::UInt(_));
                if lower_diverges || upper_diverges {
                    *hits += 1;
                    true
                } else {
                    walk(alo, blo, hits) && walk(ak, bk, hits)
                }
            }
            (Formula::Not(x), Formula::Not(y)) => walk(x, y, hits),
            (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| walk(x, y, hits))
            }
            (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
            | (Formula::Eq(a1, a2), Formula::Eq(b1, b2))
            | (Formula::Lt(a1, a2), Formula::Lt(b1, b2))
            | (Formula::Gt(a1, a2), Formula::Gt(b1, b2))
            | (Formula::Ge(a1, a2), Formula::Ge(b1, b2)) => {
                walk(a1, b1, hits) && walk(a2, b2, hits)
            }
            _ => false,
        }
    }
    let mut hits = 0usize;
    walk(ours, bridge, &mut hits) && hits > 0
}

/// `let-bound-checked-intermediate` recognizer: the two ASTs are equal at
/// every position EXCEPT positions where `ours` is a SOURCE-NAMED variable
/// (not a MIR temp / fallback `_N` shape) and `bridge` is a checked-trio
/// binop (`Add`/`Sub`/`Mul`) whose leaves are variables or integer literals
/// only — the composed defining op of an elided `let` binding, exactly what
/// the Band A chase renders where the direct ledger keeps the binding name.
/// CONSISTENCY is required: every divergent position must map the SAME name
/// to the SAME composed term (one binding, one definition), and at least one
/// such position must exist. Any other divergence disqualifies (stays
/// Unclassified).
fn let_bound_checked_intermediate_only(ours: &Formula, bridge: &Formula) -> bool {
    fn is_leaf(f: &Formula) -> bool {
        matches!(f, Formula::Var(..) | Formula::Int(_) | Formula::UInt(_))
    }
    fn composed_trio(f: &Formula) -> bool {
        match f {
            Formula::Add(a, b) | Formula::Sub(a, b) | Formula::Mul(a, b) => {
                is_leaf(a) && is_leaf(b)
            }
            _ => false,
        }
    }
    fn walk(a: &Formula, b: &Formula, map: &mut Vec<(String, Formula)>) -> bool {
        use trust_types::Sort;
        if a == b {
            return true;
        }
        match (a, b) {
            (Formula::Var(name, Sort::Int), composed)
                if !is_mir_temp(name) && composed_trio(composed) =>
            {
                match map.iter().find(|(n, _)| n == name) {
                    Some((_, term)) => term == composed,
                    None => {
                        map.push((name.clone(), composed.clone()));
                        true
                    }
                }
            }
            (Formula::Not(x), Formula::Not(y)) => walk(x, y, map),
            (Formula::And(xs), Formula::And(ys)) | (Formula::Or(xs), Formula::Or(ys)) => {
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| walk(x, y, map))
            }
            (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
            | (Formula::Eq(a1, a2), Formula::Eq(b1, b2))
            | (Formula::Lt(a1, a2), Formula::Lt(b1, b2))
            | (Formula::Le(a1, a2), Formula::Le(b1, b2))
            | (Formula::Gt(a1, a2), Formula::Gt(b1, b2))
            | (Formula::Ge(a1, a2), Formula::Ge(b1, b2))
            | (Formula::Add(a1, a2), Formula::Add(b1, b2))
            | (Formula::Sub(a1, a2), Formula::Sub(b1, b2))
            | (Formula::Mul(a1, a2), Formula::Mul(b1, b2))
            | (Formula::Div(a1, a2), Formula::Div(b1, b2))
            | (Formula::Rem(a1, a2), Formula::Rem(b1, b2)) => {
                walk(a1, b1, map) && walk(a2, b2, map)
            }
            _ => false,
        }
    }
    let mut map: Vec<(String, Formula)> = Vec::new();
    walk(ours, bridge, &mut map) && !map.is_empty()
}

pub fn print_scorecard(label: &str, card: &Scorecard, total: usize) {
    println!("== STEP 6 PARITY SCORECARD ({label}) ==");
    println!("   asserts in the six classes: {total}");
    println!(
        "   compared (both lanes produced a formula): {}  byte-identical: {}",
        card.compared(),
        card.byte_identical
    );
    println!("   version-stripped-only: {}", card.version_stripped_only);
    println!("   mint-declined: {:?}", card.mint_declined);
    println!("   bridge-declined: {}  both-declined: {}", card.bridge_declined, card.both_declined);
    println!(
        "   known-mismatch shadowed-param-name: {} const-folded-operand: {} \
         literal-range-width: {} let-bound-checked-intermediate: {}",
        card.known_mismatch_shadowed_param_name,
        card.known_mismatch_const_folded_operand,
        card.known_mismatch_literal_range_width,
        card.known_mismatch_let_bound_checked_intermediate
    );
    println!("   excluded (model/site envelope): {:?}", card.excluded);
    println!("   per-class (compared, byte-identical): {:?}", card.per_class);
    for unclassified in &card.unclassified {
        println!("   UNCLASSIFIED MISMATCH: {unclassified}");
    }
}

/// Class label for reporting/floors — EIGHT labels over the six slugs
/// (the human axis; the pairing axis is [`slug_for_assert_message`]).
pub const fn class_label(msg: &AssertMessage) -> &'static str {
    match msg {
        AssertMessage::Overflow(BinOp::Add | BinOp::Sub) => "overflow-add-sub",
        AssertMessage::Overflow(BinOp::Mul) => "overflow-mul",
        AssertMessage::Overflow(BinOp::Div | BinOp::Rem) => "divrem-min-overflow",
        AssertMessage::Overflow(BinOp::Shl | BinOp::Shr) => "shift-in-range",
        AssertMessage::Overflow(_) => "overflow-other",
        AssertMessage::OverflowNeg => "overflow-neg",
        AssertMessage::DivisionByZero => "div-by-zero",
        AssertMessage::RemainderByZero => "rem-by-zero",
        AssertMessage::BoundsCheck => "bounds-check",
        _ => "non-safety",
    }
}

/// The direct lane's identity slug for a MIR assert message — FIVE slugs over
/// the six classes, mirroring `trust-thir-lower/src/direct_obligations.rs`'s
/// consts and the frontend's `assert_obligation_class` verbatim: slug
/// `overflow` covers ALL `Overflow(binop)` messages (measured: 5 slugs vs 8
/// class labels — grouping the occ ordinal by class label would skew it).
/// `None` = not one of the six direct classes (skipped entirely, both
/// graders).
pub fn slug_for_assert_message(msg: &AssertMessage) -> Option<&'static str> {
    Some(match msg {
        AssertMessage::Overflow(
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::Shl
            | BinOp::Shr,
        ) => "overflow",
        AssertMessage::OverflowNeg => "overflow_neg",
        AssertMessage::DivisionByZero => "div_by_zero",
        AssertMessage::RemainderByZero => "rem_by_zero",
        AssertMessage::BoundsCheck => "bounds_check",
        _ => return None,
    })
}

/// One side of a graded pair: the oracle's MODEL mint, or a REAL dumped
/// record's outcome fields.
pub(crate) enum DirectSide<'a> {
    ModelMinted(Result<MintedDirectFormula, &'static str>),
    RealDumped {
        formula_raw: Option<&'a str>,
        smtlib: Option<&'a str>,
        withheld_reason: Option<&'a str>,
        not_minted: bool,
    },
}

/// Grade ONE (bridge, direct) pair. `Err` is a REFUSAL (incoherent model
/// derivatives, `non-canonical-formula-bytes`, an out-of-vocabulary reason) —
/// a tamper/torn/invariant signal that must not be graded; `Ok((grade,
/// detail))` is an honest grade, including `Unclassified` for a real
/// mismatch (wrong bytes are a REPORTED mismatch, never a crash).
pub(crate) fn grade_pair(
    bridge: &SafetyPredicate,
    direct: DirectSide<'_>,
    shadowed: bool,
) -> Result<(Grade, String), String> {
    match direct {
        DirectSide::ModelMinted(mint) => Ok(match (bridge, mint) {
            (SafetyPredicate::Reconstructed(bf), Ok(minted)) => {
                if minted.formula == *bf {
                    // Coherence of the once-rendered derivatives.
                    let canonical = serde_json::to_string(bf)
                        .map_err(|e| format!("bridge formula failed to render: {e}"))?;
                    if minted.formula_json != canonical {
                        return Err(format!(
                            "model minted formula_json is not the once-rendered serde of its \
                             own formula: {} vs {canonical}",
                            minted.formula_json
                        ));
                    }
                    if minted.smtlib != bf.to_smtlib() {
                        return Err(
                            "model minted smtlib is not the once-rendered smtlib".to_string()
                        );
                    }
                    if shadowed {
                        (
                            Grade::Unclassified,
                            "shadow premise broke: formulas EQUAL under a shadowed param name"
                                .to_string(),
                        )
                    } else {
                        (Grade::ByteIdentical, String::new())
                    }
                } else if shadowed {
                    (Grade::KnownMismatchShadowedParamName, String::new())
                } else if formula_eq_modulo_versions(&minted.formula, bf) {
                    (Grade::VersionStrippedOnly, String::new())
                } else if const_folded_operand_only(&minted.formula, bf) {
                    (Grade::KnownMismatchConstFoldedOperand, String::new())
                } else if literal_range_width_only(&minted.formula, bf) {
                    (Grade::KnownMismatchLiteralRangeWidth, String::new())
                } else if let_bound_checked_intermediate_only(&minted.formula, bf) {
                    (Grade::KnownMismatchLetBoundCheckedIntermediate, String::new())
                } else {
                    (Grade::Unclassified, format!("mint={:?}\nbridge={bf:?}", minted.formula))
                }
            }
            (SafetyPredicate::Reconstructed(_), Err(code)) => {
                (Grade::MintDeclined(code), String::new())
            }
            (SafetyPredicate::NotReconstructed(_), Ok(_)) => (Grade::BridgeDeclined, String::new()),
            (SafetyPredicate::NotReconstructed(_), Err(_)) => (Grade::BothDeclined, String::new()),
        }),
        DirectSide::RealDumped { formula_raw, smtlib, withheld_reason, not_minted } => {
            if not_minted {
                // No mint was attempted (pre-Step-6 recording path): the
                // direct side holds nothing comparable — enumerated, never
                // silently dropped.
                return Ok((Grade::Excluded("not-minted"), String::new()));
            }
            if let Some(reason) = withheld_reason {
                let Some(stable) =
                    ENUMERATED_WITHHELD_REASONS.iter().copied().find(|r| *r == reason)
                else {
                    return Err(format!(
                        "withheld reason {reason:?} is outside the enumerated vocabulary \
                         (fail closed — extend ENUMERATED_WITHHELD_REASONS in the same \
                         reviewed change that mints it)"
                    ));
                };
                return Ok(match bridge {
                    SafetyPredicate::Reconstructed(_) => {
                        (Grade::MintDeclined(stable), String::new())
                    }
                    SafetyPredicate::NotReconstructed(_) => (Grade::BothDeclined, String::new()),
                });
            }
            let (Some(raw), Some(smt)) = (formula_raw, smtlib) else {
                return Err(
                    "dumped record carries neither a minted formula, a withheld reason, nor \
                     not_minted — malformed outcome"
                        .to_string(),
                );
            };
            match bridge {
                SafetyPredicate::NotReconstructed(_) => Ok((Grade::BridgeDeclined, String::new())),
                SafetyPredicate::Reconstructed(bf) => {
                    let canonical = serde_json::to_string(bf)
                        .map_err(|e| format!("bridge formula failed to render: {e}"))?;
                    if raw == canonical && smt == bf.to_smtlib() {
                        return Ok(if shadowed {
                            (
                                Grade::Unclassified,
                                "shadow premise broke: formulas EQUAL under a shadowed param \
                                 name"
                                    .to_string(),
                            )
                        } else {
                            (Grade::ByteIdentical, String::new())
                        });
                    }
                    match serde_json::from_str::<Formula>(raw) {
                        Err(err) => Ok((
                            Grade::Unclassified,
                            format!(
                                "dumped formula bytes do not parse as a Formula: {err}; \
                                 raw={raw}"
                            ),
                        )),
                        Ok(dumped) => {
                            if dumped == *bf {
                                Err(format!(
                                    "non-canonical-formula-bytes: the dumped bytes parse to \
                                     the bridge's own AST but differ from its canonical \
                                     render (or the smtlib differs) — a torn/tampered dump, \
                                     refused rather than graded; raw={raw} \
                                     canonical={canonical}"
                                ))
                            } else if shadowed {
                                Ok((Grade::KnownMismatchShadowedParamName, String::new()))
                            } else if formula_eq_modulo_versions(&dumped, bf) {
                                Ok((Grade::VersionStrippedOnly, String::new()))
                            } else if const_folded_operand_only(&dumped, bf) {
                                Ok((Grade::KnownMismatchConstFoldedOperand, String::new()))
                            } else if literal_range_width_only(&dumped, bf) {
                                Ok((Grade::KnownMismatchLiteralRangeWidth, String::new()))
                            } else if let_bound_checked_intermediate_only(&dumped, bf) {
                                Ok((Grade::KnownMismatchLetBoundCheckedIntermediate, String::new()))
                            } else {
                                Ok((
                                    Grade::Unclassified,
                                    format!("dumped={dumped:?}\nbridge={bf:?}"),
                                ))
                            }
                        }
                    }
                }
            }
        }
    }
}

/// The MIR lane's `_N` fallback base of a possibly-BV-prefixed var name —
/// mirrors `safety_formulas::sweep_no_guessed_mir_index`'s extraction.
fn bv_base_name(name: &str) -> &str {
    ["lhs", "rhs", "neg"]
        .into_iter()
        .find_map(|role| {
            name.strip_prefix("__trust_ovf_bv_")
                .and_then(|rest| rest.strip_prefix(role))
                .and_then(|rest| rest.strip_prefix('_'))
        })
        .unwrap_or(name)
}

/// Recompute `shadowed` from the MIR body (a body property — no minted-once
/// violation): true iff the bridge formula names a PARAM through the `_N`
/// fallback namespace where that param's declared source name is duplicated
/// among the body's named locals — exactly the shape the pinned
/// known-mismatch class describes.
pub(crate) fn bridge_formula_names_a_shadowed_param(
    formula: &Formula,
    locals: &[LocalDecl],
    arg_count: usize,
) -> bool {
    trust_types::any_formula_node(formula, &mut |node| {
        let name = match node {
            Formula::Var(name, _) => Some(name.as_str()),
            Formula::SymVar(sym, _) => Some(sym.as_str()),
            _ => None,
        };
        if let Some(name) = name {
            let base = bv_base_name(name);
            if let Some(index) =
                base.strip_prefix('_').and_then(|digits| digits.parse::<usize>().ok())
                && (1..=arg_count).contains(&index)
                && let Some(decl_name) = locals
                    .get(index)
                    .filter(|d| d.index == index)
                    .or_else(|| locals.iter().find(|d| d.index == index))
                    .and_then(|d| d.name.as_deref())
            {
                return locals.iter().filter(|d| d.name.as_deref() == Some(decl_name)).nth(1).is_some();
            }
        }
        false
    })
}

/// Load a directory of `VerifiableFunction` json fixtures (the mir-only dump
/// format), sorted by filename. Test/measurement instrument: panics on an
/// unreadable directory or an undeserializable fixture, exactly like the
/// oracle's in-situ loader this parameterizes.
pub fn load_corpus_dir(dir: &Path) -> Vec<(String, VerifiableFunction)> {
    let mut out = Vec::new();
    let mut failures = Vec::new();
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|err| panic!("MIR corpus dir {} must be readable: {err}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "json"))
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(&path).expect("fixture readable");
        match serde_json::from_str::<VerifiableFunction>(&text) {
            Ok(func) => out.push((name, func)),
            Err(err) => failures.push(format!("{name}: {err}")),
        }
    }
    assert_eq!(
        failures,
        Vec::<String>::new(),
        "every corpus fixture must deserialize as a VerifiableFunction"
    );
    out
}

/// Count the corpus' six-class asserts (the scorecard's `total` axis).
pub fn count_six_class_asserts(corpus: &[(String, VerifiableFunction)]) -> usize {
    corpus
        .iter()
        .flat_map(|(_, func)| func.body.blocks.iter())
        .filter(|block| {
            matches!(&block.terminator, Terminator::Assert { msg, .. }
                if slug_for_assert_message(msg).is_some())
        })
        .count()
}

/// Grade REAL dumped records against a MIR corpus — the item-(1) entry point.
///
/// Pairing key: `({crate}::{def_path}` == `VerifiableFunction.def_path`,
/// slug, LO line, col, occ)`. The fixture `def_path` is the crate-qualified
/// identity (measured over the checked-in corpus: `name` is the bare
/// function name, `def_path` the `{crate}::{fn}` spelling the dump's
/// `{krate}::{def_path}` reassembles). Dumped `occ` is used VERBATIM; the
/// MIR ordinal is derived per function at slug granularity in block order.
pub fn grade_real_records(
    records: &[DumpedDirectRecord],
    corpus: &[(String, VerifiableFunction)],
) -> Result<Scorecard, Vec<String>> {
    let mut errors: Vec<String> = Vec::new();

    // Version belt (the parser already refuses; re-checked so a hand-built
    // record list cannot bypass it).
    for record in records {
        if record.v != DIRECT_FORMULA_DUMP_VERSION {
            errors.push(format!(
                "record {} carries unknown version {:?}",
                record.assertion_id, record.v
            ));
        }
    }

    // Duplicate dumped identity (assertion_id is the minted identity).
    let mut seen_ids: FxHashSet<(&str, &str)> =
        FxHashSet::with_capacity_and_hasher(records.len(), Default::default());
    for record in records {
        if !seen_ids.insert((record.krate.as_str(), record.assertion_id.as_str())) {
            errors.push(format!(
                "duplicate dumped identity ({}, {})",
                record.krate, record.assertion_id
            ));
        }
    }

    // Index records by scope -> (slug, line, col) -> occ -> record index.
    let mut index: FxHashMap<String, FxHashMap<(&str, u32, u32), FxHashMap<u32, usize>>> =
        FxHashMap::default();
    for (i, record) in records.iter().enumerate() {
        let scope = format!("{}::{}", record.krate, record.def_path);
        let group = index
            .entry(scope)
            .or_default()
            .entry((record.slug.as_str(), record.line, record.col))
            .or_default();
        if group.insert(record.occ, i).is_some() {
            errors.push(format!(
                "duplicate dumped identity: two records at ({}::{}, {}, L{}C{}, o{})",
                record.krate, record.def_path, record.slug, record.line, record.col, record.occ
            ));
        }
    }

    // Corpus scope uniqueness (pairing would otherwise be ambiguous).
    let mut by_scope: BTreeMap<&str, (&str, &VerifiableFunction)> = BTreeMap::new();
    for (name, func) in corpus {
        if by_scope.insert(func.def_path.as_str(), (name.as_str(), func)).is_some() {
            errors.push(format!(
                "corpus def_path {:?} appears twice — pairing would be ambiguous",
                func.def_path
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }

    let mut reports: Vec<AssertReport> = Vec::new();
    let mut consumed: Vec<bool> = vec![false; records.len()];

    for (scope, (fixture_name, func)) in &by_scope {
        let locals = &func.body.locals;
        let arg_count = func.body.arg_count;
        // (slug, line, col) -> asserts in emission order.
        let mut groups: BTreeMap<(&'static str, u32, u32), Vec<&trust_types::BasicBlock>> =
            BTreeMap::new();
        for block in &func.body.blocks {
            let Terminator::Assert { msg, span, .. } = &block.terminator else { continue };
            let Some(slug) = slug_for_assert_message(msg) else { continue };
            let key = (slug, span.line_start, span.col_start);
            groups.entry(key).or_default().push(block);
        }

        let by_site = index.get(*scope);
        for ((slug, line, col), asserts) in groups {
            let record_group = by_site.and_then(|site_map| site_map.get(&(slug, line, col)));
            let Some(record_group) = record_group else {
                for block in &asserts {
                    let Terminator::Assert { msg, .. } = &block.terminator else { continue };
                    reports.push(AssertReport {
                        fixture: format!("{fixture_name}::{}", func.name),
                        class_label: class_label(msg),
                        grade: Grade::Excluded("uncovered-by-direct-lane"),
                        detail: String::new(),
                    });
                }
                continue;
            };
            for &record_idx in record_group.values() {
                consumed[record_idx] = true;
            }
            if record_group.len() != asserts.len() {
                errors.push(format!(
                    "collision-group size mismatch at ({scope}, {slug}, L{line}C{col}): \
                     {} dumped record(s) vs {} MIR assert(s) — the (slug, line, col) \
                     non-injectivity pin; refusing to guess a pairing",
                    record_group.len(),
                    asserts.len()
                ));
                continue;
            }
            for (mir_occ, block) in asserts.iter().enumerate() {
                let mir_occ = u32::try_from(mir_occ).expect("occ fits u32");
                let Some(&record_index) = record_group.get(&mir_occ) else {
                    errors.push(format!(
                        "collision-group occ skew at ({scope}, {slug}, L{line}C{col}): no \
                         dumped record carries o{mir_occ} though the group sizes match — \
                         the dumped occ is used verbatim, never re-derived"
                    ));
                    continue;
                };
                let record = &records[record_index];
                let Terminator::Assert { cond, msg, target, .. } = &block.terminator else {
                    continue;
                };
                let Some(bridge) = reconstruct_assert_safety_predicate(
                    locals,
                    &func.body.blocks,
                    block.id,
                    *target,
                    cond,
                    msg,
                ) else {
                    errors.push(format!(
                        "grader invariant broke: six-class assert at ({scope}, {slug}, \
                         L{line}C{col}, o{mir_occ}) has no bridge disposition"
                    ));
                    continue;
                };
                let shadowed = match &bridge {
                    SafetyPredicate::Reconstructed(bf) => {
                        bridge_formula_names_a_shadowed_param(bf, locals, arg_count)
                    }
                    SafetyPredicate::NotReconstructed(_) => false,
                };
                let direct = DirectSide::RealDumped {
                    formula_raw: match &record.outcome {
                        DumpedOutcome::Minted { formula, .. } => Some(formula.get()),
                        _ => None,
                    },
                    smtlib: match &record.outcome {
                        DumpedOutcome::Minted { smtlib, .. } => Some(smtlib.as_str()),
                        _ => None,
                    },
                    withheld_reason: match &record.outcome {
                        DumpedOutcome::Withheld { reason } => Some(reason.as_str()),
                        _ => None,
                    },
                    not_minted: matches!(&record.outcome, DumpedOutcome::NotMinted(_)),
                };
                match grade_pair(&bridge, direct, shadowed) {
                    Ok((grade, detail)) => reports.push(AssertReport {
                        fixture: format!("{fixture_name}::{}", func.name),
                        class_label: class_label(msg),
                        grade,
                        detail,
                    }),
                    Err(refusal) => errors
                        .push(format!("({scope}, {slug}, L{line}C{col}, o{mir_occ}): {refusal}")),
                }
            }
        }
    }

    for (i, record) in records.iter().enumerate() {
        if !consumed[i] {
            errors.push(format!(
                "unpaired dumped record: ({}::{}, {}, L{}C{}, o{}) matches no MIR assert in \
                 the corpus",
                record.krate, record.def_path, record.slug, record.line, record.col, record.occ
            ));
        }
    }

    if errors.is_empty() { Ok(tally(&reports)) } else { Err(errors) }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use trust_types::{
        BasicBlock, BlockId, Operand, Place, Rvalue, SourceSpan, Statement, Ty, UnwindEdge,
        VerifiableBody,
    };

    use super::*;
    use crate::direct_formula_dump::parse_direct_formula_dump;
    use crate::safety_formulas::{
        AddSubOp, DirectFormulaClass, DirectFormulaOperand, mint_direct_safety_formula,
    };

    fn span() -> SourceSpan {
        SourceSpan {
            file: "real.rs".to_string(),
            line_start: 3,
            col_start: 8,
            line_end: 3,
            col_end: 15,
        }
    }

    /// `fn f(a: u32, b: u32)` with one checked `a + b` assert — the minimal
    /// body whose bridge side reconstructs.
    fn add_func() -> VerifiableFunction {
        VerifiableFunction {
            name: "f".to_string(),
            def_path: "realcrate::f".to_string(),
            span: span(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Int { width: 32, signed: false }, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Int { width: 32, signed: false },
                        name: Some("a".to_string()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Int { width: 32, signed: false },
                        name: Some("b".to_string()),
                    },
                    LocalDecl { index: 3, ty: Ty::Int { width: 32, signed: false }, name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::CheckedBinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: span(),
                        }],
                        terminator: Terminator::Assert {
                            cond: Operand::Copy(Place::local(3)),
                            expected: true,
                            msg: AssertMessage::Overflow(BinOp::Add),
                            target: BlockId(1),
                            span: span(),
                            unwind: UnwindEdge::Unreachable,
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn minted_add() -> MintedDirectFormula {
        mint_direct_safety_formula(
            &DirectFormulaClass::OverflowAddSub { op: AddSubOp::Add },
            32,
            false,
            &[
                DirectFormulaOperand::Named { name: "a".to_string() },
                DirectFormulaOperand::Named { name: "b".to_string() },
            ],
        )
        .expect("named add pair mints")
    }

    fn dump_record(outcome: DumpedOutcome) -> DumpedDirectRecord {
        DumpedDirectRecord {
            v: DIRECT_FORMULA_DUMP_VERSION.to_string(),
            krate: "realcrate".to_string(),
            def_path: "f".to_string(),
            def_index: 0,
            slug: "overflow".to_string(),
            line: 3,
            col: 8,
            occ: 0,
            assertion_id: "realcrate::f#L3C8#overflow#o0".to_string(),
            block: 0,
            inst_index: 0,
            outcome,
        }
    }

    fn corpus() -> Vec<(String, VerifiableFunction)> {
        vec![("add_func".to_string(), add_func())]
    }

    /// End-to-end through the PRODUCTION writer and parser: a real minted
    /// record grades ByteIdentical against the matching MIR body.
    #[test]
    fn a_verbatim_minted_record_grades_byte_identical() {
        let minted = minted_add();
        let rows =
            vec![dump_record(DumpedOutcome::minted_verbatim(&minted.formula_json, &minted.smtlib))];
        let dir = std::env::temp_dir()
            .join(format!("direct-grading-{}-byte-identical", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = crate::direct_formula_dump::write_direct_formula_dump(&dir, "realcrate", &rows)
            .expect("write");
        let text = std::fs::read_to_string(&path).unwrap();
        let records = parse_direct_formula_dump(&text).expect("parse");
        let card = grade_real_records(&records, &corpus()).expect("grade");
        assert_eq!(card.byte_identical, 1);
        assert_eq!(card.compared(), 1);
        assert_eq!(card.per_class.get("overflow-add-sub"), Some(&(1, 1)));
        assert_eq!(card.unclassified, Vec::<String>::new());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Deliberately CORRUPTED formula bytes (a different AST): a REPORTED
    /// mismatch — the scorecard carries it as Unclassified — never a crash.
    #[test]
    fn corrupted_formula_bytes_are_a_reported_mismatch_not_a_crash() {
        let wrong = serde_json::to_string(&Formula::Var("zzz".to_string(), trust_types::Sort::Int))
            .unwrap();
        let rows = vec![dump_record(DumpedOutcome::minted_verbatim(&wrong, "(bogus)"))];
        let text =
            crate::direct_formula_dump::render_direct_formula_dump("realcrate", &rows).unwrap();
        let records = parse_direct_formula_dump(&text).expect("parse");
        let card = grade_real_records(&records, &corpus()).expect("grades, does not crash");
        assert_eq!(card.byte_identical, 0);
        assert_eq!(card.unclassified.len(), 1, "the corruption must be REPORTED");
        assert!(card.unclassified[0].contains("overflow-add-sub"), "{:?}", card.unclassified);
    }

    /// Bytes that parse to the bridge's own AST but differ from its canonical
    /// render: REFUSED as non-canonical (torn/tamper), not graded.
    #[test]
    fn non_canonical_formula_bytes_are_refused_not_graded() {
        let minted = minted_add();
        // Same JSON value, whitespace-perturbed: parses to the same AST.
        let perturbed = minted.formula_json.replacen(":", ": ", 1);
        assert_ne!(perturbed, minted.formula_json, "perturbation must change bytes");
        let rows = vec![dump_record(DumpedOutcome::minted_verbatim(&perturbed, &minted.smtlib))];
        let text =
            crate::direct_formula_dump::render_direct_formula_dump("realcrate", &rows).unwrap();
        let records = parse_direct_formula_dump(&text).expect("parse");
        let errs =
            grade_real_records(&records, &corpus()).expect_err("non-canonical bytes must refuse");
        assert!(errs.iter().any(|e| e.contains("non-canonical-formula-bytes")), "{errs:?}");
    }

    /// The fail-closed pairing errors: unpaired record, collision-group size
    /// mismatch, duplicate identity; and the uncovered MIR assert bucket.
    #[test]
    fn pairing_fails_closed_and_uncovered_asserts_are_enumerated() {
        // No records at all: the assert lands in uncovered-by-direct-lane.
        let card = grade_real_records(&[], &corpus()).expect("empty records grade");
        assert_eq!(card.excluded.get("uncovered-by-direct-lane"), Some(&1));

        // A record naming a function the corpus does not hold: unpaired.
        let mut foreign = dump_record(DumpedOutcome::NotMinted(true));
        foreign.def_path = "nosuch".to_string();
        foreign.assertion_id = "realcrate::nosuch#L3C8#overflow#o0".to_string();
        let errs =
            grade_real_records(&[foreign], &corpus()).expect_err("unpaired record must refuse");
        assert!(errs.iter().any(|e| e.contains("unpaired dumped record")), "{errs:?}");

        // Two records for a one-assert group: collision-group size mismatch.
        let mut second = dump_record(DumpedOutcome::NotMinted(true));
        second.occ = 1;
        second.assertion_id = "realcrate::f#L3C8#overflow#o1".to_string();
        let errs =
            grade_real_records(&[dump_record(DumpedOutcome::NotMinted(true)), second], &corpus())
                .expect_err("size mismatch must refuse");
        assert!(errs.iter().any(|e| e.contains("collision-group size mismatch")), "{errs:?}");

        // Duplicate identity.
        let errs = grade_real_records(
            &[
                dump_record(DumpedOutcome::NotMinted(true)),
                dump_record(DumpedOutcome::NotMinted(true)),
            ],
            &corpus(),
        )
        .expect_err("duplicate identity must refuse");
        assert!(errs.iter().any(|e| e.contains("duplicate dumped identity")), "{errs:?}");

        // Unknown withheld reason reaching the grader directly (parser
        // bypassed): still refused.
        let errs = grade_real_records(
            &[dump_record(DumpedOutcome::Withheld { reason: "novel-unreviewed".into() })],
            &corpus(),
        )
        .expect_err("unknown reason must refuse");
        assert!(errs.iter().any(|e| e.contains("enumerated vocabulary")), "{errs:?}");
    }

    /// A withheld record grades MintDeclined under its enumerated reason.
    #[test]
    fn a_withheld_record_grades_mint_declined() {
        let records =
            vec![dump_record(DumpedOutcome::Withheld { reason: "opaque-operand".into() })];
        let card = grade_real_records(&records, &corpus()).expect("grade");
        assert_eq!(card.mint_declined.get("opaque-operand"), Some(&1));
        assert_eq!(card.compared(), 0);
    }

    /// The env-keyed driver: TRUST_DIRECT_RECORDS_JSONL +
    /// TRUST_DIRECT_MIR_CORPUS feed real records to this grader; skips
    /// LOUDLY when unset (the main loop's driver rebuild wires it).
    #[test]
    fn const_folded_operand_is_a_pinned_known_class_and_its_negatives_stay_unclassified() {
        use trust_types::Sort;
        // The exact measured shape (p06 `first`): dumped folds the const index,
        // the bridge names the materialized temp.
        let dumped = Formula::Ge(Box::new(Formula::Int(0)), Box::new(Formula::Int(4)));
        let bridge =
            Formula::Ge(Box::new(Formula::Var("_2".into(), Sort::Int)), Box::new(Formula::Int(4)));
        assert!(const_folded_operand_only(&dumped, &bridge));
        // NEGATIVE 1: the var is a PARAM name, not a MIR temp — a param-vs-const
        // divergence is a real disagreement, never this class.
        let bridge_param =
            Formula::Ge(Box::new(Formula::Var("i".into(), Sort::Int)), Box::new(Formula::Int(4)));
        assert!(!const_folded_operand_only(&dumped, &bridge_param));
        // NEGATIVE 2: any OTHER divergence alongside the fold disqualifies.
        let bridge_other_len =
            Formula::Ge(Box::new(Formula::Var("_2".into(), Sort::Int)), Box::new(Formula::Int(5)));
        assert!(!const_folded_operand_only(&dumped, &bridge_other_len));
        // NEGATIVE 3: identical formulas are NOT this class (hits == 0).
        assert!(!const_folded_operand_only(&bridge, &bridge));
    }

    #[test]
    fn literal_range_width_is_a_pinned_known_class_and_its_negatives_stay_unclassified() {
        // The exact measured shape (p05 `shl_lit`): both clamp the literal 3,
        // one at i32 extremes, the other at i64 extremes; the semantic core
        // (`3 < 0 || 3 >= 16`) is identical.
        let core = Formula::Or(vec![
            Formula::Lt(Box::new(Formula::Int(3)), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(Formula::Int(3)), Box::new(Formula::Int(16))),
        ]);
        let clamp = |lo: i128, hi: i128| {
            Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(lo)), Box::new(Formula::Int(3))),
                Formula::Le(Box::new(Formula::Int(3)), Box::new(Formula::Int(hi))),
            ])
        };
        let dumped = Formula::And(vec![clamp(-0x8000_0000, 0x7fff_ffff), core.clone()]);
        let bridge =
            Formula::And(vec![clamp(-0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff), core.clone()]);
        assert!(literal_range_width_only(&dumped, &bridge));
        // NEGATIVE 1: a bound that is NOT a type extreme is a real disagreement.
        let bridge_weird = Formula::And(vec![clamp(-12345, 0x7fff_ffff_ffff_ffff), core.clone()]);
        assert!(!literal_range_width_only(&dumped, &bridge_weird));
        // NEGATIVE 2: differing LITERALS under the clamp are a real disagreement.
        let clamp_other = Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(-0x8000_0000_0000_0000)), Box::new(Formula::Int(4))),
            Formula::Le(Box::new(Formula::Int(4)), Box::new(Formula::Int(0x7fff_ffff_ffff_ffff))),
        ]);
        let bridge_lit = Formula::And(vec![clamp_other, core]);
        assert!(!literal_range_width_only(&dumped, &bridge_lit));
        // NEGATIVE 3: identity is not this class.
        assert!(!literal_range_width_only(&bridge, &bridge));
    }

    #[test]
    fn let_bound_checked_intermediate_is_a_pinned_known_class_and_negatives_stay_unclassified() {
        use trust_types::Sort;
        let var = |n: &str| Formula::Var(n.to_string(), Sort::Int);
        // The exact measured shape (p12 `l`, `let s = a + b; s - a`): dumped
        // spells the elided binding `s`, the bridge's chase composes Add(a, b).
        let composed = Formula::Add(Box::new(var("a")), Box::new(var("b")));
        let dumped = Formula::Gt(
            Box::new(Formula::Sub(Box::new(var("s")), Box::new(var("a")))),
            Box::new(Formula::Int(2147483647)),
        );
        let bridge = Formula::Gt(
            Box::new(Formula::Sub(Box::new(composed.clone()), Box::new(var("a")))),
            Box::new(Formula::Int(2147483647)),
        );
        assert!(let_bound_checked_intermediate_only(&dumped, &bridge));
        // CONSISTENCY across positions: the same name must map to the same
        // composed term everywhere.
        let dumped2 = Formula::And(vec![
            dumped.clone(),
            Formula::Lt(Box::new(var("s")), Box::new(Formula::Int(0))),
        ]);
        let bridge2 = Formula::And(vec![
            bridge.clone(),
            Formula::Lt(Box::new(composed.clone()), Box::new(Formula::Int(0))),
        ]);
        assert!(let_bound_checked_intermediate_only(&dumped2, &bridge2));
        let bridge2_skewed = Formula::And(vec![
            bridge.clone(),
            Formula::Lt(
                Box::new(Formula::Sub(Box::new(var("a")), Box::new(var("b")))),
                Box::new(Formula::Int(0)),
            ),
        ]);
        assert!(
            !let_bound_checked_intermediate_only(&dumped2, &bridge2_skewed),
            "one name mapping to two different composed terms is a REAL disagreement"
        );
        // NEGATIVE 1: a MIR-temp-shaped dumped var is never this class (that
        // is the `_N` vocabulary wall, not an elided binding).
        let dumped_temp = Formula::Gt(
            Box::new(Formula::Sub(Box::new(var("_3")), Box::new(var("a")))),
            Box::new(Formula::Int(2147483647)),
        );
        assert!(!let_bound_checked_intermediate_only(&dumped_temp, &bridge));
        // NEGATIVE 2: a bridge side that is NOT a checked-trio composition
        // (Div, or a nested non-leaf) is a real disagreement.
        let bridge_div = Formula::Gt(
            Box::new(Formula::Sub(
                Box::new(Formula::Div(Box::new(var("a")), Box::new(var("b")))),
                Box::new(var("a")),
            )),
            Box::new(Formula::Int(2147483647)),
        );
        assert!(!let_bound_checked_intermediate_only(&dumped, &bridge_div));
        // NEGATIVE 3: identity is not this class (no divergent position).
        assert!(!let_bound_checked_intermediate_only(&bridge, &bridge));
        // NEGATIVE 4: any OTHER divergence alongside the substitution
        // disqualifies.
        let bridge_other = Formula::Gt(
            Box::new(Formula::Sub(Box::new(composed), Box::new(var("b")))),
            Box::new(Formula::Int(2147483647)),
        );
        assert!(!let_bound_checked_intermediate_only(&dumped, &bridge_other));
    }

    /// Env-keyed driver: grades real direct-formula records against a MIR
    /// corpus. `#[ignore]`d, and it panics when either input is unset, so a bare
    /// `--ignored` run cannot pass having graded nothing.
    #[test]
    #[ignore = "measurement driver: set TRUST_DIRECT_RECORDS_JSONL and \
                TRUST_DIRECT_MIR_CORPUS and run with --ignored --nocapture"]
    fn grade_real_records_env_driver() {
        const RECIPE: &str = "TRUST_DIRECT_RECORDS_JSONL=<a *.direct-formulas.jsonl written \
             under TRUST_DIRECT_FORMULA_DUMP> TRUST_DIRECT_MIR_CORPUS=<dir of \
             VerifiableFunction json> targo --unverified test --manifest-path crates/Cargo.toml \
             -p trust-ir-bridge --lib -- --ignored --exact \
             direct_record_grading::tests::grade_real_records_env_driver --nocapture";
        let Some(records_path) = std::env::var_os("TRUST_DIRECT_RECORDS_JSONL") else {
            panic!(
                "grade_real_records_env_driver is a measurement driver and \
                 TRUST_DIRECT_RECORDS_JSONL is unset, so it graded nothing. Run: {RECIPE}"
            );
        };
        let Some(corpus_dir) = std::env::var_os("TRUST_DIRECT_MIR_CORPUS") else {
            panic!(
                "grade_real_records_env_driver: TRUST_DIRECT_MIR_CORPUS is unset, so it \
                 graded nothing. Run: {RECIPE}"
            );
        };
        let text = std::fs::read_to_string(PathBuf::from(&records_path))
            .expect("TRUST_DIRECT_RECORDS_JSONL must be readable");
        let records = parse_direct_formula_dump(&text)
            .unwrap_or_else(|errs| panic!("dump refused (fail closed): {errs:#?}"));
        let corpus = load_corpus_dir(Path::new(&corpus_dir));
        let total = count_six_class_asserts(&corpus);
        match grade_real_records(&records, &corpus) {
            Ok(card) => {
                print_scorecard("REAL records vs MIR corpus", &card, total);
                assert_eq!(
                    card.unclassified,
                    Vec::<String>::new(),
                    "every real-record mismatch must be a pinned known class"
                );
            }
            Err(errs) => panic!("real-record grading refused (fail closed): {errs:#?}"),
        }
    }
}
