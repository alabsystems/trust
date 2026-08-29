// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 14 — a lane whose only evidence is a hand-built `Expr` is a lane
//! with no evidence about the compiler.**
//!
//! # The class this control closes
//!
//! Three shipped lanes have now been caught keyed to a kernel spelling the
//! ELABORATOR does not produce. Each was locally green — the crate's own tests
//! passed, the kernel accepted the terms, the gate was satisfied — and each was
//! found months later by a human running a real build:
//!
//! | landing | the reader demanded | a real source elaborates to |
//! |---|---|---|
//! | 3 | `Expr::nat_lit(5)` | `OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)` |
//! | 5 | `Nat.beq a b` | `BEq.beq … instBEqOfDecidableEq …` lifted by `= Bool.true` |
//! | R2 | `Nat.lt 0 n`, `Nat.decLt 0 n`, `Nat.sub n 1` | `@LT.lt.{0} Nat instLTNat …`, `instDecidableNatLt …`, `@HSub.hSub.{0,0,0} … instHSubNat …` |
//!
//! The common cause is one methodological hole, not three coding mistakes: the
//! side A those lanes were developed against was **assembled by the test**.
//! A hand-built `Expr` proves what the KERNEL accepts. It proves nothing
//! whatever about what the elaborator EMITS, and the emit lane only ever sees
//! the latter. R2's `recognise_wf_nat_rec` was covered by twelve mutation
//! controls and nine equation probes, all green, while the lane was
//! unreachable from any program a user could write
//! (`docs/audits/2026-08-22-r2-wf-call-lane-unreachable.md`).
//!
//! # What this control demands
//!
//! For every row of the selection table — the table IS the enumeration of
//! emittable lanes, so a new lane cannot dodge this by not being listed —
//! there must exist an island source that
//!
//! 1. elaborates and kernel-checks through
//!    [`trust_certify::clean_island::CleanIslandSession::check_all`], the exact
//!    pipeline `clean_origin_mir` drives, and
//! 2. **plans** — `plan_clean_origin_body` returns a shape that exercises that
//!    row.
//!
//! The control does not check that such a probe exists somewhere by reading a
//! `measured_by` string. It **runs the sources itself**, so it cannot be
//! satisfied by a stale citation.
//!
//! Two grains, because the defect lives at the finer one:
//!
//! * **[`every_row_has_a_real_session_witness`] — LANE grain.** Each row is
//!   reached from a real source. This catches "the lane does not work at all",
//!   which is what R2 was.
//! * **[`every_constant_side_a_spelling_is_witnessed`] — SPELLING grain.**
//!   Each side-A selector that names a CONSTANT is found in the elaborated term
//!   of a witness that selects its row. This is the grain all three defects
//!   actually lived at: R2's `nat.sub` row (then named `nat.pred`) listed `Nat.sub`, no source emits
//!   `Nat.sub`, and the row was still marked measured.
//!
//! Both grains ratchet. A lane or spelling with no real-session evidence is
//! recorded as a NAMED gap with a reason; the counts may fall, never rise, and
//! a gap that has been closed must be DELETED from the list — the control fails
//! while a closed gap is still declared, so retirement is executable rather
//! than a comment (the `dyn_carrier_corpus_coverage` waiver convention).
//!
//! # What it does NOT prove
//!
//! Planning is not compiling. This control runs entirely inside the fast lane
//! and reaches `plan_clean_origin_body`; it does not build a driver, does not
//! run `x.py`, and says nothing about the MIR round trip or the ui fixtures.
//! A row that is green here can still fail end to end — but a row that is RED
//! here cannot possibly work end to end, which is the whole point: R2 would
//! have been red here from the day it landed.

#![allow(clippy::doc_markdown)]

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use clean_kernel::{Environment, Expr, ExprKind};
use trust_clean_origin::emit::{CleanOriginShape, plan_clean_origin_body};
use trust_clean_origin::table::{KernelSelector, ROWS, RowContext};
use trust_types::admissible_body::{ArithBinOp, ArithExpr, RecBodyExpr};

// ═══════════════════════════════════════════════════════════════════════════
// The witnesses. Every one is a source string, not a term.
// ═══════════════════════════════════════════════════════════════════════════

/// One real-session witness: an island source, the `def` in it to plan, and a
/// note on what it is here to measure.
struct Witness {
    /// Stable label, cited by this control's failure text.
    label: &'static str,
    /// The island source. **Must be source text.** A `Witness` whose side A is
    /// assembled in Rust would defeat the entire control, which is why this
    /// field is a `&str` and there is no `Expr` variant.
    source: &'static str,
    /// The `def` inside `source` to plan.
    def: &'static str,
}

/// The witness corpus.
///
/// Deliberately small and deliberately ORDINARY: every source here is a
/// program someone would plausibly write. A witness contrived to hit a reader's
/// internal branch is the hand-built-`Expr` failure wearing a source costume.
static WITNESSES: &[Witness] = &[
    // ── whole-body lanes ──────────────────────────────────────────────────
    Witness {
        label: "projection",
        source: "def fst (a : UInt64) (b : UInt64) : UInt64 := a",
        def: "fst",
    },
    Witness { label: "constant", source: "def six : UInt64 := 6", def: "six" },
    Witness {
        label: "add",
        source: "def sum (a : UInt64) (b : UInt64) : UInt64 := a + b",
        def: "sum",
    },
    // The `-` witness. Until 2026-08-22 NO real-session source in this crate
    // contained a `-` at all — the phase-1 hazard survey flagged `uint.sub` as
    // latent for exactly that reason, and `nat.sub`'s surface spelling was the
    // R2 defect. A subtraction now appears at both carriers.
    Witness {
        label: "sub",
        source: "def dif (a : UInt64) (b : UInt64) : UInt64 := a - b",
        def: "dif",
    },
    Witness {
        label: "mul",
        source: "def prod (a : UInt64) (b : UInt64) : UInt64 := a * b",
        def: "prod",
    },
    // A COMPOSITION, so the composed lane is reached from a source too and not
    // only through the single-op rungs.
    Witness {
        label: "composed",
        source: "def wmix (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a",
        def: "wmix",
    },
    // A narrower width than the u64 every other arithmetic witness uses: the
    // survey flagged UInt8/16/32 arithmetic as having no real-session source.
    Witness {
        label: "add-u8",
        source: "def s8 (a : UInt8) (b : UInt8) : UInt8 := a + b",
        def: "s8",
    },
    Witness {
        label: "sub-u32",
        source: "def s32 (a : UInt32) (b : UInt32) : UInt32 := a - b",
        def: "s32",
    },
    // ── §6f landing 7: the raw binary operators ───────────────────────────
    //
    // Ordinary programs, and each is the ONLY thing that makes its row's
    // `Covered` honest: the four `H*.h*` surface spellings this lane reads are
    // read BECAUSE these four sources produce them, measured here rather than
    // asserted in a `measured_by` string.
    Witness {
        label: "bitand",
        source: "def band (a : UInt64) (b : UInt64) : UInt64 := a &&& b",
        def: "band",
    },
    Witness {
        label: "bitor",
        source: "def bor (a : UInt64) (b : UInt64) : UInt64 := a ||| b",
        def: "bor",
    },
    // The divisor is a strictly positive NUMERAL, and it has to be: this lane
    // emits `/` and `%` nowhere else, because Clean's `UInt{N}.div`/`.mod` are
    // TOTAL and Rust's are not. A witness written `a / b` would not plan, and
    // `measure()`'s panic would say so — which is the control working, not the
    // witness being wrong.
    Witness {
        label: "div-literal",
        source: "def third (a : UInt64) : UInt64 := a / 3",
        def: "third",
    },
    Witness {
        label: "mod-literal",
        source: "def rem3 (a : UInt64) : UInt64 := a % 3",
        def: "rem3",
    },
    // A NARROWER width for the same family, for the reason the `add-u8`
    // witness exists: the phase-1 survey's lesson was that a lane believed
    // width-uniform is only width-uniform where a source was written.
    Witness {
        label: "bitand-u8",
        source: "def band8 (a : UInt8) (b : UInt8) : UInt8 := a &&& b",
        def: "band8",
    },
    // ── selects ───────────────────────────────────────────────────────────
    Witness {
        label: "select-lt",
        source: "def lt (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b",
        def: "lt",
    },
    Witness {
        label: "select-le",
        source: "def le (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else b",
        def: "le",
    },
    Witness {
        label: "select-eq",
        source: "def eq (a : UInt64) (b : UInt64) : UInt64 := if a = b then a else b",
        def: "eq",
    },
    Witness {
        label: "select-beq",
        source: "def eqbeq (a : UInt64) (b : UInt64) : UInt64 := if a == b then a else b",
        def: "eqbeq",
    },
    Witness {
        label: "select-literal",
        source: "def capped (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b",
        def: "capped",
    },
    // ── recursion ─────────────────────────────────────────────────────────
    Witness {
        label: "structural-rec",
        source: "def tozero : Nat -> Nat\n  | 0 => 0\n  | n + 1 => tozero n",
        def: "tozero",
    },
    // The structural arm vocabulary, from a source: `+`, a literal, the
    // predecessor binder and the recursive occurrence in one body.
    Witness {
        label: "structural-rec-sum",
        source: "def natsum : Nat -> Nat\n  | 0 => 0\n  | n + 1 => (n + 1) + natsum n",
        def: "natsum",
    },
    // R2's canonical fixture, verbatim from `tests/ui/trust/clean_origin_wf_rec.rs`.
    // This is the row that was marked `Covered` while being unreachable.
    Witness {
        label: "wf-rec",
        source: "def countdownSum (n : Nat) : Nat := \
                 if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                 termination_by n",
        def: "countdownSum",
    },
    // The RAW spellings, written out in source. `r2_session_probes` p2/p3
    // measure that these still plan; here they additionally supply the
    // `Nat.lt` / `Nat.sub` constants to the spelling grain, which is what makes
    // those selectors witnessed rather than waived.
    Witness {
        label: "wf-rec-raw-spellings",
        source: "def rawDown (n : Nat) : Nat := \
                 if h : Nat.lt 0 n then Nat.add n (rawDown (Nat.sub n 1)) else 0\n\
                 termination_by n",
        def: "rawDown",
    },
    // §R6's row — FACTORIAL, verbatim from
    // `tests/ui/trust/clean_origin_wf_rec_mul.rs`. It supplies the SURFACE
    // `HMul.hMul` spelling to both grains.
    Witness {
        label: "wf-rec-mul",
        source: "def fact (n : Nat) : Nat := \
                 if h : 0 < n then n * fact (n - 1) else 1\n\
                 termination_by n",
        def: "fact",
    },
    // And the RAW `Nat.mul` spelling, for the same reason `wf-rec-raw-spellings`
    // exists: the `nat.mul` row's `ConstantHead("Nat.mul")` selector must be
    // witnessed by a term that actually carries `Nat.mul`, not waived.
    Witness {
        label: "wf-rec-mul-raw",
        source: "def rawFact (n : Nat) : Nat := \
                 if h : Nat.lt 0 n then Nat.mul n (rawFact (Nat.sub n 1)) else 1\n\
                 termination_by n",
        def: "rawFact",
    },
    // §R8's row — the TEXTBOOK MODULO `gcd`, verbatim from
    // `tests/ui/trust/clean_origin_wf_rec_modulo_gcd.rs`. It supplies the
    // SURFACE `HMod.hMod` spelling to both grains, and it is the only witness
    // in this corpus that reaches `nat.mod`.
    //
    // The `+ a * 0` measure is load-bearing, not decoration: phase 3
    // (`OnMeasureValue`) is reached only by a measure naming both parameters,
    // and it is what puts `a % b` in a self-call argument at all.
    Witness {
        label: "wf-rec-modulo-gcd",
        source: "def gcd (a b : Nat) : Nat := \
                 if h : 0 < b then gcd b (a % b) else a\n\
                 termination_by b + a * 0",
        def: "gcd",
    },
    // And the RAW `Nat.mod` spelling, for the reason `wf-rec-mul-raw` exists:
    // the `nat.mod` row's `ConstantHead("Nat.mod")` selector must be witnessed
    // by a term that actually carries `Nat.mod`, not waived.
    Witness {
        label: "wf-rec-modulo-gcd-raw",
        source: "def rawGcd (a b : Nat) : Nat := \
                 if h : Nat.lt 0 b then rawGcd b (Nat.mod a b) else a\n\
                 termination_by b + a * 0",
        def: "rawGcd",
    },
];

// ═══════════════════════════════════════════════════════════════════════════
// The one side-A source. Nothing in this file builds a term.
// ═══════════════════════════════════════════════════════════════════════════

/// Elaborate and kernel-check one witness, and hand back both the environment
/// the planner reads and the elaborated body.
///
/// The island assertion is half the control: a source that never elaborated is
/// not evidence about the CALL lane, and silently counting one would reproduce
/// the exact bookkeeping error this file exists to prevent.
fn elaborate(witness: &Witness) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[witness.source]);
    assert!(
        !batch.is_rejected(),
        "witness `{}` must elaborate and kernel-check before it is evidence about \
         anything: {batch:?}",
        witness.label
    );
    session.environment().expect("an untainted session has an environment").clone()
}

/// Every constant name occurring anywhere in a term.
///
/// This is the SPELLING measurement: it reads the term the elaborator actually
/// produced, so a selector naming a constant that never appears is a selector
/// no source can select.
fn constant_heads(expr: &Expr, out: &mut BTreeSet<String>) {
    match expr.kind() {
        ExprKind::Const(name, _) => {
            out.insert(name.to_string());
        }
        ExprKind::App(f, a) => {
            constant_heads(f, out);
            constant_heads(a, out);
        }
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            constant_heads(t, out);
            constant_heads(b, out);
        }
        ExprKind::Let(_, t, v, b, _) => {
            constant_heads(t, out);
            constant_heads(v, out);
            constant_heads(b, out);
        }
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => constant_heads(inner, out),
        _ => {}
    }
}

/// The elaborated value of a `def`, or `None` for a declaration with no value.
fn definition_value(env: &Environment, name: &str) -> Option<Expr> {
    env.get_const(&clean_kernel::Name::from_string(name))?.value.clone()
}

// ═══════════════════════════════════════════════════════════════════════════
// Which rows a plan exercises
// ═══════════════════════════════════════════════════════════════════════════

/// Every table row a planned shape exercises — the whole-body/scheme row from
/// [`trust_clean_origin::table::ladder_row`], PLUS the recursion-arm node rows
/// and every operator of a composition.
///
/// The arm rows are the reason this cannot just call `ladder_row`: five of the
/// sixteen rows (`nat.param`, `nat.sub`, `nat.self`, `nat.lit`, `nat.add`) are
/// `RowContext::RecursionArm` and are reachable ONLY inside a scheme, so a
/// coverage claim that stopped at the scheme row would mark them covered
/// without ever having seen one.
fn rows_exercised(shape: &CleanOriginShape) -> BTreeSet<&'static str> {
    let mut out = BTreeSet::new();
    if let Some(row) = trust_clean_origin::table::ladder_row(shape) {
        out.insert(row.name);
    }
    match shape {
        CleanOriginShape::Composed { expr } => arith_rows(expr, &mut out),
        CleanOriginShape::StructuralNatRec { base, step, rec_arg } => {
            for node in [base, step, rec_arg] {
                rec_rows(node, &mut out);
            }
        }
        CleanOriginShape::WellFoundedNatRec { zero_value, nonzero_value, rec_args, .. } => {
            for node in [zero_value, nonzero_value].into_iter().chain(rec_args) {
                rec_rows(node, &mut out);
            }
        }
        _ => {}
    }
    out
}

fn arith_rows(expr: &ArithExpr, out: &mut BTreeSet<&'static str>) {
    if let ArithExpr::Bin { op, left, right } = expr {
        out.insert(match op {
            ArithBinOp::Add => "uint.add",
            ArithBinOp::Sub => "uint.sub",
            ArithBinOp::Mul => "uint.mul",
        });
        arith_rows(left, out);
        arith_rows(right, out);
    }
}

fn rec_rows(expr: &RecBodyExpr, out: &mut BTreeSet<&'static str>) {
    match expr {
        // R3a: BOTH parameter spellings select `nat.param`. A row says which
        // constant a node names, never at which binder index it sits, so the
        // measure and a threaded parameter are one row at two `Site` indices.
        RecBodyExpr::Decreasing | RecBodyExpr::Param(_) => {
            out.insert("nat.param");
        }
        // R3b: the predecessor and the GENERAL `-` are one row, for the reason
        // the two parameter spellings are — one constant, one MIR realization,
        // two operand shapes. The row was renamed `nat.pred` -> `nat.sub` when
        // it stopped being predecessor-only.
        RecBodyExpr::Pred => {
            out.insert("nat.sub");
        }
        RecBodyExpr::Rec => {
            out.insert("nat.self");
        }
        RecBodyExpr::NatConst(_) => {
            out.insert("nat.lit");
        }
        RecBodyExpr::Add(left, right) => {
            out.insert("nat.add");
            rec_rows(left, out);
            rec_rows(right, out);
        }
        RecBodyExpr::Mul(left, right) => {
            out.insert("nat.mul");
            rec_rows(left, out);
            rec_rows(right, out);
        }
        RecBodyExpr::Sub(left, right) => {
            out.insert("nat.sub");
            rec_rows(left, out);
            rec_rows(right, out);
        }
        // R8: `%` gets its OWN row, unlike the pairs above — it names a
        // different kernel constant (`Nat.mod`) through a different runtime
        // callee (`Nat::rem`), so sharing one would be MIR aliasing.
        RecBodyExpr::Rem(left, right) => {
            out.insert("nat.mod");
            rec_rows(left, out);
            rec_rows(right, out);
        }
    }
}

/// The measurement, computed ONCE per test binary.
///
/// Elaborating the corpus is the expensive part (a real Clean session per
/// source), and all four tests want the same answer. Sharing it is not a
/// micro-optimisation: a control that takes half a minute is a control people
/// stop running, and this one is only useful if it runs on every fast lane.
///
/// A panic inside `get_or_init` leaves the cell uninitialised, so a failing
/// corpus fails every test with its own message rather than one test with the
/// message and three with a poisoned lock.
type Measurement = BTreeMap<&'static str, (BTreeSet<&'static str>, BTreeSet<String>)>;

fn measured() -> &'static Measurement {
    static CACHE: OnceLock<Measurement> = OnceLock::new();
    CACHE.get_or_init(measure)
}

/// Plan every witness once: label -> (rows exercised, constants in side A).
fn measure() -> Measurement {
    let mut measured = BTreeMap::new();
    for witness in WITNESSES {
        let env = elaborate(witness);
        let plan = plan_clean_origin_body(&env, witness.def).unwrap_or_else(|refusal| {
            panic!(
                "witness `{}` is declared real-session evidence for a lane but does NOT \
                 plan. Either the lane is unreachable from source — which is the defect \
                 this control exists to catch, and the fix is the EMITTER moving to meet \
                 the reader — or this witness is wrong and should be replaced with a \
                 source that does plan.\n  refusal: {}",
                witness.label,
                refusal.note()
            )
        });
        let mut constants = BTreeSet::new();
        if let Some(value) = definition_value(&env, witness.def) {
            constant_heads(&value, &mut constants);
        }
        measured.insert(witness.label, (rows_exercised(plan.shape()), constants));
    }
    measured
}

// ═══════════════════════════════════════════════════════════════════════════
// GRAIN 1 — every lane is reached from a real source
// ═══════════════════════════════════════════════════════════════════════════

/// RATCHET. Rows with no real-session witness. **May fall, never rise.**
///
/// Raising this number means a lane shipped whose only evidence is a hand-built
/// term — which is the defect class itself, not a re-pin.
const LANE_GAP_CEILING: usize = 0;

/// The named lane gaps, each with the reason no source reaches it.
///
/// EMPTY, measured 2026-08-22. Every one of the sixteen rows is reached by an
/// ordinary source. That is a stronger result than expected going in: the
/// phase-1 hazard survey predicted five latent rows, and four of those five
/// (`uint.sub` at u64, `uint.sub` at a narrow width, `add` at UInt8, the
/// structural arm vocabulary) turned out to be reachable by a source nobody had
/// written down. Only the belief that they were unreachable was load-bearing.
static DECLARED_LANE_GAPS: &[(&str, &str)] = &[];

#[test]
fn every_row_has_a_real_session_witness() {
    let measured = measured();
    let covered: BTreeSet<&'static str> =
        measured.values().flat_map(|(rows, _)| rows.iter().copied()).collect();

    let gaps: Vec<&'static str> =
        ROWS.iter().map(|row| row.name).filter(|name| !covered.contains(name)).collect();

    // A declared gap that is no longer a gap must be DELETED, not left to rot.
    for (name, reason) in DECLARED_LANE_GAPS {
        assert!(
            gaps.contains(name),
            "`{name}` is declared a lane gap ({reason}) but a real-session witness now \
             reaches it. DELETE the row — a stale waiver is how a closed gap goes on \
             looking open."
        );
    }
    let declared: BTreeSet<&str> = DECLARED_LANE_GAPS.iter().map(|(n, _)| *n).collect();
    let undeclared: Vec<&&str> = gaps.iter().filter(|name| !declared.contains(*name)).collect();
    assert!(
        undeclared.is_empty(),
        "these emittable lanes have NO real-session evidence: {undeclared:?}\n\
         A lane whose only evidence is a hand-built `Expr` is a lane with no evidence \
         about the compiler — that is how R2's well-founded lane shipped unreachable. \
         Add a `Witness` (a SOURCE, never a term) that plans onto the row, or declare \
         the gap in `DECLARED_LANE_GAPS` with the reason and raise nothing."
    );

    assert!(
        gaps.len() <= LANE_GAP_CEILING,
        "LANE_GAP_CEILING is a ratchet: {} lanes lack real-session evidence, ceiling is \
         {LANE_GAP_CEILING}. It may fall, never rise.",
        gaps.len()
    );

    eprintln!(
        "CONTROL-14 | lanes {}/{} reached from a real island source | gaps {} (ceiling {})",
        covered.len(),
        ROWS.len(),
        gaps.len(),
        LANE_GAP_CEILING
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// GRAIN 2 — every constant SPELLING is one a source actually produces
// ═══════════════════════════════════════════════════════════════════════════

/// The constant a selector names, for the selectors that name one.
///
/// The others (`BoundVariable`, `NatLiteral`, `CarrierNumeral`, `IteAt`,
/// `RecursiveOccurrence`, `InductiveProjectionProof`) are structural positions,
/// not constants; grain 1 is their evidence and this grain says nothing about
/// them. Stating that boundary here is the point — an unstated exemption is how
/// a coverage number becomes a claim it does not support.
fn selector_spelling(
    selector: KernelSelector,
    carrier_prefixes: &[&str],
) -> Option<(String, Vec<String>)> {
    match selector {
        KernelSelector::ConstantHead(head) => Some((head.to_owned(), vec![head.to_owned()])),
        KernelSelector::SurfaceClass { class, projection } => {
            let name = format!("{class}.{projection}");
            Some((name.clone(), vec![name]))
        }
        // `{C}.add` is carrier-RELATIVE: the row is stated over a class of
        // widths, so any one of them witnesses the spelling, and the reported
        // name keeps the `{C}` rather than naming a width the row does not fix.
        KernelSelector::CarrierMethod { suffix } => Some((
            format!("{{C}}.{suffix}"),
            carrier_prefixes.iter().map(|c| format!("{c}.{suffix}")).collect(),
        )),
        _ => None,
    }
}

/// RATCHET. Constant side-A spellings no source is measured to produce.
/// **May fall, never rise.**
const SPELLING_GAP_CEILING: usize = 3;

/// The named spelling gaps — measured 2026-08-22, and all three are the SAME
/// one fact about arithmetic.
///
/// A spelling this crate reads but no source emits is not automatically a
/// defect. It is a defect exactly when it is the ONLY spelling read, which is
/// what R2 was and what grain 1 catches. These three are the benign case, and
/// the reason is checkable rather than asserted: side B's producer builds
/// `{carrier}.{op}` literally — `Domain::op` in `crates/trust-spec-elab`
/// (`Domain::Machine(width) => format!("{}.{which}", width.carrier())`) — so
/// the raw reading is what the GATE compares against, while side A only ever
/// arrives in the `HAdd.hAdd`/`instHAddUInt{w}` surface form. Both are read;
/// each is reached from a different side.
///
/// Recorded rather than waived silently, because "the reader reads a spelling
/// nothing produces" is the sentence that preceded all three defects, and the
/// difference between benign and fatal is only ever visible when both halves
/// are written down.
static DECLARED_SPELLING_GAPS: &[(&str, &str, &str)] = &[
    (
        "uint.add",
        "{C}.add",
        "the raw carrier method. Source spells `a + b`, which elaborates through \
         `HAdd.hAdd`/`instHAddUInt{w}`; side B RENDERS `{C}.add`, so the raw reading is \
         exercised from the reflection side and the surface one from source.",
    ),
    ("uint.sub", "{C}.sub", "as `uint.add`, for `-`."),
    ("uint.mul", "{C}.mul", "as `uint.add`, for `*`."),
];

#[test]
fn every_constant_side_a_spelling_is_witnessed() {
    let measured = measured();

    // For each row, the constants seen in any witness that selects it.
    let mut seen_for_row: BTreeMap<&'static str, BTreeSet<String>> = BTreeMap::new();
    for (rows, constants) in measured.values() {
        for row in rows {
            seen_for_row.entry(row).or_default().extend(constants.iter().cloned());
        }
    }

    // Every unsigned width the witness corpus exercises.
    let carriers = ["UInt8", "UInt16", "UInt32", "UInt64"];

    let mut gaps: Vec<(&'static str, String)> = Vec::new();
    for row in ROWS {
        let seen = seen_for_row.get(row.name);
        for selector in row.side_a {
            let Some((display, candidates)) = selector_spelling(*selector, &carriers) else {
                continue;
            };
            let witnessed =
                seen.is_some_and(|set| candidates.iter().any(|name| set.contains(name)));
            if !witnessed {
                gaps.push((row.name, display));
            }
        }
    }

    // Retirement is executable: a declared gap that is now witnessed must go.
    for (row, spelling, reason) in DECLARED_SPELLING_GAPS {
        assert!(
            gaps.iter().any(|(r, s)| r == row && s == spelling),
            "`{row}` / `{spelling}` is declared an unwitnessed spelling ({reason}) but a \
             real source now emits it. DELETE the row from `DECLARED_SPELLING_GAPS`."
        );
    }
    let undeclared: Vec<&(&str, String)> = gaps
        .iter()
        .filter(|(row, spelling)| {
            !DECLARED_SPELLING_GAPS.iter().any(|(r, s, _)| r == row && s == spelling)
        })
        .collect();
    assert!(
        undeclared.is_empty(),
        "these side-A spellings are read by the compiler but produced by NO measured \
         source: {undeclared:?}\n\
         This is the exact grain landings 3, 5 and R2 all failed at. Either add a \
         `Witness` whose source emits the spelling, or declare it in \
         `DECLARED_SPELLING_GAPS` with the reason it is read anyway (side-B rendering is \
         a legitimate reason; \"the reader wants it\" is not)."
    );

    assert!(
        gaps.len() <= SPELLING_GAP_CEILING,
        "SPELLING_GAP_CEILING is a ratchet: {} spellings are unwitnessed, ceiling is \
         {SPELLING_GAP_CEILING}. It may fall, never rise.",
        gaps.len()
    );

    eprintln!(
        "CONTROL-14 | constant side-A spellings unwitnessed by any source: {} (ceiling {})",
        gaps.len(),
        SPELLING_GAP_CEILING
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// The control's own integrity
// ═══════════════════════════════════════════════════════════════════════════

/// The recursion-arm rows are reachable ONLY under a scheme, so a coverage
/// count that never entered a scheme body would mark them covered by accident.
/// Pin that at least one witness really does descend into arm nodes.
#[test]
fn arm_rows_are_reached_through_a_scheme_and_not_by_accident() {
    let measured = measured();
    let arm_rows: BTreeSet<&'static str> = ROWS
        .iter()
        .filter(|row| row.context == RowContext::RecursionArm)
        .map(|row| row.name)
        .collect();
    assert!(!arm_rows.is_empty(), "the table must still have recursion-arm rows");

    let from_schemes: BTreeSet<&'static str> = measured
        .values()
        .filter(|(rows, _)| rows.contains("nat.rec.structural") || rows.contains("nat.wf.fix"))
        .flat_map(|(rows, _)| rows.iter().copied())
        .collect();

    let unreached: Vec<&&str> =
        arm_rows.iter().filter(|name| !from_schemes.contains(*name)).collect();
    assert!(
        unreached.is_empty(),
        "these recursion-arm rows are never reached from inside a real scheme body: \
         {unreached:?} — grain 1 would be counting them without evidence"
    );

    eprintln!(
        "CONTROL-14 | {} recursion-arm rows, all reached from inside a real scheme body",
        arm_rows.len()
    );
}

/// Every witness must be a SOURCE, and every witness must be used.
///
/// The first half is what keeps this control from decaying into the thing it
/// polices; the second stops the corpus accumulating sources that measure
/// nothing.
#[test]
fn the_witness_corpus_is_source_only_and_fully_used() {
    for witness in WITNESSES {
        assert!(
            witness.source.contains("def "),
            "witness `{}` does not look like island source text",
            witness.label
        );
        assert!(
            witness.source.contains(witness.def),
            "witness `{}` does not contain its own `def` name `{}`",
            witness.label,
            witness.def
        );
    }

    let measured = measured();
    for witness in WITNESSES {
        let (rows, _) = &measured[witness.label];
        assert!(
            !rows.is_empty(),
            "witness `{}` plans but exercises no table row — either `ladder_row` has a \
             hole or this witness measures nothing and should be deleted",
            witness.label
        );
    }

    eprintln!("CONTROL-14 | {} witnesses, all source-only, all exercising rows", WITNESSES.len());
}
