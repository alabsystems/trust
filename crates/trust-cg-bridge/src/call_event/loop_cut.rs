//! PKG-C5c-L0: a loop function's cut-point segments, MEASURED and recorded for
//! a test. Compiled only with the `test-hooks` feature, which the compiler
//! never enables (compiler/rustc_codegen_trust_cg/Cargo.toml enables
//! `ay-proofs` and `kernel-recheck` only). Detail document:
//! docs/design/2026-11-15-pkg-c5c-loop-cut-points.md.
//!
//! # What it does
//!
//! analyze's spec `Err` arm calls [`record_if_installed`] when the spec side
//! refused a backedge, the gate is not observe-only and the mode is
//! `Produce`. Unless a test installed [`record_loop_segments`] on THIS thread
//! it returns at once. Otherwise [`measure`]:
//!
//! - cuts the IR at one block `B` (the loop header first, then every other
//!   non-entry block, so a rotated loop's body block is found) and evaluates
//!   two segments with the frozen `SpecCx`: the entry segment (from the
//!   function entry, ending at each edge into `B`) and the loop segment (from
//!   `B` with its shared variables fresh `CUT_bb{B}_v{id}`, ending at each
//!   edge back into `B`). `SpecCx::block`'s own backedge refusal, unchanged,
//!   rejects a `B` some cycle avoids;
//! - cuts the bytes at their one backward-branch target `h` and runs the
//!   frozen `CerExec` twice the same way (entry run from the function start,
//!   loop run from `h`), each run stopping at `h`;
//! - locates each IR shared variable in a register X0-X17 (X18 off Darwin) by
//!   structural equality at the entry arrival, pins a register the loop reads
//!   and never writes to its entry-arrival value, and havocs the rest;
//! - decides every segment item: structurally equal sides first (`refl`),
//!   then ay, under DETERMINISTIC caps only (a solver-query cap, a total
//!   machine-step cap and a per-query term-size cap; no wall clock decides
//!   anything, PKG-DET). Each ay query runs under the output gate's one
//!   deterministic effort count (`verify_output::gate_query_effort`,
//!   DECISION_QUEUE BUDGET-1: `:rlimit` sized to the query) and no wall clock;
//!   a query the count ends is Unknown `[stop:effort]`. The count bounds each
//!   SAT solve, not ay's preprocessing, so liveness is still a test's concern
//!   here;
//! - records the outcome. Nothing reaches a grade, a certificate, a
//!   refusal or the O4 text, which stays `spec side: loop/backedge at bb{N}
//!   (fail-closed)`.
//!
//! The cut map is untrusted: a wrong map gives a counterexample, which here
//! is a recorded outcome only. A counterexample is never a Refuted.
//!
//! No input-derived indexing, `unwrap` or `expect`: a panic here would fail
//! the gate thread (PKG-C5c-L2 inherits the rule).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};

use trust_ir::Module;
use trust_ir::value::{BlockId, ValueId};
use trust_machine_sem::{Aarch64Semantics, Effect, Flags, MachineState, Semantics};
use trust_types::{Formula, Sort};

use super::{
    CerExec, CerInput, FnPlacement, ParamPlace, ReturnPlace, Signature, SiteDecision, SiteKey,
    Slot, abi_extensions, spec_entry, substitute,
};
use crate::compiled_object::FunctionWindow;
use crate::verify_output::{
    Discharge, PathOutcome, abi_fold, b, backward_branch_targets, formula_to_term, gate_check_sat,
    gate_query_effort, ite_unless_same,
};
use crate::verify_output_trust_ir::{IrValue, live_in_sets, loop_headers};

/// Cut-block candidates tried per function (the header first).
const MAX_CUT_CANDIDATES: usize = 8;
/// Live-in register assignments tried per candidate.
const MAX_ASSIGNMENTS: usize = 24;
/// Solver queries per function (refl items do not count).
pub(crate) const MAX_L0_QUERIES: u32 = 256;
/// Machine instruction steps per function, summed over every run. A run
/// starts only when its worst case ([`RUN_STEPS`]) still fits, so the total
/// never exceeds it.
const MAX_L0_MACHINE_STEPS: u32 = 65_536;
/// The most steps one `CerExec` run takes: it counts a step, then refuses past
/// its own `MAX_MACHINE_STEPS`.
const RUN_STEPS: u32 = super::MAX_MACHINE_STEPS + 1;
/// Formula nodes per solver query (both sides); a larger item is Unknown.
const MAX_QUERY_NODES: usize = 50_000;
/// The longest recorded text, in bytes.
const MAX_TEXT_BYTES: usize = 512;
/// Every measured text's ending.
pub(crate) const SUFFIX: &str = "; cut-point induction not kernel-checked (fail-closed)";
/// Every measured text's beginning.
pub(crate) const PREFIX: &str = "loop cut points: ";

// ===========================================================================
// the record
// ===========================================================================

/// How one segment item was decided.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemOutcome {
    /// Both sides structurally equal after `abi_fold` and ground folding.
    Refl,
    /// ay: UNSAT of the sides' difference.
    Proven,
    /// ay: SAT (not evidence against the bytes in this slice).
    CounterExample,
    /// ay did not conclude, or the item was not posed (its reason).
    Unknown(String),
}

impl ItemOutcome {
    /// Discharged: refl or ay-proved.
    #[must_use]
    pub fn discharged(&self) -> bool {
        matches!(self, ItemOutcome::Refl | ItemOutcome::Proven)
    }
}

/// What a machine register is at the cut (the unit test's adapter to L1's
/// `loop_sim::Role`; `Pinned` is new in L0, PKG-C5c-L2 gap (a)).
#[derive(Clone, Debug, PartialEq)]
pub enum SegRole {
    /// Holds IR shared variable `j`.
    Coupled(usize),
    /// A callee-saved register; `entry` names its entry leaf.
    Frame { arch: String, entry: String },
    /// Read, never written: its entry-arrival value.
    Pinned(Formula),
    /// Scratch.
    Havoc,
}

/// One machine register at the cut: the name the loop segment reads it by.
#[derive(Clone, Debug, PartialEq)]
pub struct SegReg {
    pub name: String,
    pub width: u32,
    pub role: SegRole,
}

/// The discharged (or reported) pair's segment Formulas, field for field in
/// L1's `LoopPair` shape (docs/design/2026-11-15-pkg-c5c-loop-cut-points.md §4).
#[derive(Clone, Debug, PartialEq)]
pub struct LoopSegments {
    pub ir_vars: Vec<(String, u32)>,
    pub entry_ir: Vec<Formula>,
    pub step_ir: Vec<Formula>,
    pub reach_ret_ir: Formula,
    pub ret_ir: Formula,
    pub regs: Vec<SegReg>,
    pub entry_m: Vec<Formula>,
    pub step_m: Vec<Formula>,
    pub reach_ret_m: Formula,
    pub ret_m: Formula,
    /// Per frame register (in `regs` order), its value at `ret` on the exit path.
    pub exit_frame_m: Vec<Formula>,
    pub entry_reach_ir: Formula,
    pub entry_reach_m: Formula,
    pub entry_ret_ir: Formula,
    pub entry_ret_m: Formula,
    /// Per frame register (in `regs` order), its value at the entry segment's `ret`.
    pub entry_frame_m: Vec<Formula>,
}

/// One measurement (L0 text; never a certificate's).
#[derive(Clone, Debug)]
pub struct Measurement {
    /// `loop cut points: … ; cut-point induction not kernel-checked (fail-closed)`.
    pub text: String,
    /// The IR loop header `loop_headers` found.
    pub header: u32,
    /// The reported IR cut block and machine cut address.
    pub cut: Option<(u32, u64)>,
    /// The bytes' backward-branch targets inside the window.
    pub backward_targets: Vec<u64>,
    /// The reported pair's live-ins: (IR value id, register).
    pub live_ins: Vec<(u32, u8)>,
    /// The reported pair's pinned registers.
    pub pinned: Vec<u8>,
    /// The reported pair's items, in order, with how each was decided.
    pub items: Vec<(String, ItemOutcome)>,
    /// Items discharged structurally (over the whole measurement).
    pub refl: u32,
    /// Solver queries (over the whole measurement).
    pub queries: u32,
    /// Machine instruction steps (over every run of the measurement).
    pub machine_steps: u32,
    /// The reported pair's IR and machine loop-segment arrival paths.
    pub ir_loop_arrivals: usize,
    pub machine_loop_arrivals: usize,
    /// Every (cut block, assignment) pair tried, in order.
    pub tried: Vec<String>,
    /// Wall-clock milliseconds, RECORDED for the test to print; nothing reads
    /// it to decide (the caps above are the only bounds).
    pub ms: u128,
    /// The reported pair's segments.
    pub segments: Option<LoopSegments>,
    /// Every formed pair with every item decided, in the order tried. Filled
    /// only under the unit tests' exhaustive hook; empty otherwise.
    pub pairs: Vec<PairRecord>,
}

/// One formed (cut block, assignment) pair with every item decided.
#[derive(Clone, Debug)]
pub struct PairRecord {
    pub block: u32,
    pub live_ins: Vec<(u32, u8)>,
    pub pinned: Vec<u8>,
    pub items: Vec<(String, ItemOutcome)>,
}

impl Measurement {
    /// Whether every item of the reported pair was discharged.
    #[must_use]
    pub fn all_discharged(&self) -> bool {
        !self.items.is_empty() && self.items.iter().all(|(_, o)| o.discharged())
    }
}

/// A measurement, or the reason the function is outside L0's fragment.
#[derive(Clone, Debug)]
pub enum LoopOutcome {
    /// Outside the fragment before any segment pair was formed.
    Declined(String),
    Measured(Box<Measurement>),
}

/// One `measure` call on the recording thread.
#[derive(Clone, Debug)]
pub struct LoopRecord {
    pub symbol: String,
    pub outcome: LoopOutcome,
}

thread_local! {
    static RECORDS: RefCell<Option<Vec<LoopRecord>>> = const { RefCell::new(None) };
    static QUERY_CAP: Cell<u32> = const { Cell::new(MAX_L0_QUERIES) };
    static STEP_CAP: Cell<u32> = const { Cell::new(MAX_L0_MACHINE_STEPS) };
    static NODE_CAP: Cell<usize> = const { Cell::new(MAX_QUERY_NODES) };
    static EXHAUSTIVE: Cell<bool> = const { Cell::new(false) };
}

/// Run `body` with `cell` set to `value` on THIS thread (restored on return or
/// unwind).
fn with_cell<T: Copy + 'static, R>(
    cell: &'static std::thread::LocalKey<Cell<T>>,
    value: T,
    body: impl FnOnce() -> R,
) -> R {
    struct Restore<T: Copy + 'static>(&'static std::thread::LocalKey<Cell<T>>, T);
    impl<T: Copy + 'static> Drop for Restore<T> {
        fn drop(&mut self) {
            self.0.set(self.1);
        }
    }
    let _restore = Restore(cell, cell.replace(value));
    body()
}

/// TEST HOOK (`test-hooks` only): run `body` and return, with its result,
/// every loop measurement the call-event gate recorded on THIS thread while it
/// ran. It observes; it grants nothing and changes no verdict or text.
#[doc(hidden)]
pub fn record_loop_segments<R>(body: impl FnOnce() -> R) -> (R, Vec<LoopRecord>) {
    struct Restore(Option<Option<Vec<LoopRecord>>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            if let Some(outer) = self.0.take() {
                RECORDS.with(|r| *r.borrow_mut() = outer);
            }
        }
    }
    let mut restore = Restore(Some(RECORDS.with(|r| r.borrow_mut().replace(Vec::new()))));
    let result = body();
    let outer = restore.0.take().unwrap_or_default();
    let records = RECORDS.with(|r| std::mem::replace(&mut *r.borrow_mut(), outer));
    (result, records.unwrap_or_default())
}

/// TEST HOOK (`test-hooks` only): run `body` with the per-function solver-query
/// cap set to `cap` on THIS thread (restored on return or unwind).
#[doc(hidden)]
pub fn with_loop_cut_query_cap<R>(cap: u32, body: impl FnOnce() -> R) -> R {
    with_cell(&QUERY_CAP, cap, body)
}

/// Unit tests: the total machine-step cap set to `cap` on THIS thread.
#[cfg(all(test, feature = "kernel-recheck"))]
fn with_loop_cut_step_cap<R>(cap: u32, body: impl FnOnce() -> R) -> R {
    with_cell(&STEP_CAP, cap, body)
}

/// Unit tests: the per-query node cap set to `cap` on THIS thread.
#[cfg(all(test, feature = "kernel-recheck"))]
fn with_loop_cut_node_cap<R>(cap: usize, body: impl FnOnce() -> R) -> R {
    with_cell(&NODE_CAP, cap, body)
}

/// Unit tests: every formed pair is decided item by item past its first
/// failure and recorded in [`Measurement::pairs`] (more queries, same report).
#[cfg(all(test, feature = "kernel-recheck"))]
fn with_loop_cut_exhaustive<R>(body: impl FnOnce() -> R) -> R {
    with_cell(&EXHAUSTIVE, true, body)
}

/// analyze's locals at the spec `Err` arm.
pub(super) struct Subject<'a> {
    pub(super) input: &'a CerInput<'a>,
    pub(super) module: &'a Module,
    pub(super) func: &'a trust_ir::Function,
    pub(super) sig: &'a Signature,
    pub(super) place: &'a FnPlacement,
    pub(super) decisions: &'a BTreeMap<SiteKey, SiteDecision>,
    pub(super) window: &'a FunctionWindow,
    pub(super) x18_reserved: bool,
    /// No IR call site, no machine call site (trap tails included), no
    /// admitted dead tail and no trap tail.
    pub(super) call_free: bool,
}

/// Measure and record when a recorder is installed on this thread; otherwise
/// return at once without building the subject.
pub(super) fn record_if_installed<'a>(make: impl FnOnce() -> Subject<'a>) {
    if !RECORDS.with(|r| r.borrow().is_some()) {
        return;
    }
    let subject = make();
    let record = LoopRecord { symbol: subject.window.symbol.clone(), outcome: measure(&subject) };
    RECORDS.with(|r| {
        if let Some(records) = r.borrow_mut().as_mut() {
            records.push(record);
        }
    });
}

// ===========================================================================
// the cut on each side (set only here, on loop_cut's own SpecCx / CerExec)
// ===========================================================================

/// `SpecCx::cut`: the cut block, its shared variables and the arrivals.
pub(super) struct SpecCut {
    pub(super) block: u32,
    pub(super) shared: Vec<ValueId>,
    pub(super) arrivals: Vec<(Formula, Vec<IrValue>)>,
}

/// One machine path that reached the cut address.
pub(super) struct MachineCutArrival {
    pub(super) path: Formula,
    pub(super) state: MachineState,
}

// ===========================================================================
// measure
// ===========================================================================

fn measure(s: &Subject<'_>) -> LoopOutcome {
    // Recorded for printing only; no decision reads it.
    let started = std::time::Instant::now();
    match measure_inner(s) {
        Err(reason) => LoopOutcome::Declined(reason),
        Ok(mut m) => {
            m.ms = started.elapsed().as_millis();
            m.text = cap_text(&m.text);
            LoopOutcome::Measured(Box::new(m))
        }
    }
}

fn bv(value: i128, width: u32) -> Formula {
    Formula::BitVec { value, width }
}

fn var64(name: String) -> Formula {
    Formula::Var(name, Sort::BitVec(64))
}

fn cut_var(block: u32, v: ValueId) -> Formula {
    var64(format!("CUT_bb{block}_v{}", v.index()))
}

fn havoc_gpr(block: u32, r: usize) -> Formula {
    var64(format!("X{r}@bb{block}_HAVOC"))
}

fn bit(c: &Formula) -> Formula {
    Formula::Ite(b(c.clone()), b(bv(1, 1)), b(bv(0, 1)))
}

fn any_of(paths: &[Formula]) -> Formula {
    if paths.iter().any(|p| matches!(p, Formula::Bool(true))) {
        return Formula::Bool(true);
    }
    match paths {
        [] => Formula::Bool(false),
        [one] => one.clone(),
        many => Formula::Or(many.to_vec()),
    }
}

/// `Ite(p1, v1, Ite(p2, v2, … vn))`; `None` when there is no arm.
fn cascade(arms: &[(Formula, Formula)]) -> Option<Formula> {
    let ((_, last), rest) = arms.split_last()?;
    let mut acc = last.clone();
    for (p, v) in rest.iter().rev() {
        acc = ite_unless_same(p, v.clone(), acc);
    }
    Some(acc)
}

/// The callee-saved registers the loop run seeds by a `CUT_M_` name. Read
/// out of a state by [`frame_values`] in `AbiExit`'s slot order: X19-X29, SP,
/// D8-D15, then X30 (the return target).
const FRAME_GPRS: [usize; 12] = [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30];
const FRAME_DREGS: [usize; 8] = [8, 9, 10, 11, 12, 13, 14, 15];

fn frame_name(slot: &str) -> String {
    format!("CUT_M_{slot}")
}

/// The frame slots read out of a machine state: `(slot, value)`.
fn frame_values(st: &MachineState) -> Vec<(String, Formula)> {
    let mut out: Vec<(String, Formula)> = Vec::new();
    for r in FRAME_GPRS.iter().copied().filter(|r| *r != 30) {
        if let Some(v) = st.gpr.get(r) {
            out.push((format!("X{r}"), v.clone()));
        }
    }
    out.push(("SP".to_string(), st.sp.clone()));
    for r in FRAME_DREGS {
        if let Ok(i) = u8::try_from(r) {
            out.push((format!("D{r}"), abi_fold(&st.read_fpr(i, 64))));
        }
    }
    if let Some(v) = st.gpr.get(30) {
        out.push(("X30".to_string(), v.clone()));
    }
    out
}

/// abi_fold, then every ground bit-vector subterm folded to its literal.
fn norm(f: &Formula) -> Formula {
    fold_ground(&abi_fold(f))
}

fn mask(width: u32) -> Option<u128> {
    match width {
        1..=64 => Some(if width == 64 { u64::MAX.into() } else { (1u128 << width) - 1 }),
        _ => None,
    }
}

fn lit(f: &Formula) -> Option<(u128, u32)> {
    match f {
        Formula::BitVec { value, width } => {
            let m = mask(*width)?;
            Some(((*value as u128) & m, *width))
        }
        _ => None,
    }
}

/// The literal a node with literal children denotes (widths 1-64 only).
fn ground(f: &Formula) -> Option<(u128, u32)> {
    let two = |l: &Formula, r: &Formula, w: u32| -> Option<(u128, u128, u128)> {
        let (a, wa) = lit(l)?;
        let (c, wc) = lit(r)?;
        (wa == w && wc == w).then_some((a, c, mask(w)?))
    };
    Some(match f {
        Formula::BitVec { .. } => lit(f)?,
        Formula::BvAdd(l, r, w) => {
            let (a, c, m) = two(l, r, *w)?;
            (a.wrapping_add(c) & m, *w)
        }
        Formula::BvSub(l, r, w) => {
            let (a, c, m) = two(l, r, *w)?;
            (a.wrapping_sub(c) & m, *w)
        }
        Formula::BvMul(l, r, w) => {
            let (a, c, m) = two(l, r, *w)?;
            (a.wrapping_mul(c) & m, *w)
        }
        Formula::BvAnd(l, r, w) => {
            let (a, c, _) = two(l, r, *w)?;
            (a & c, *w)
        }
        Formula::BvOr(l, r, w) => {
            let (a, c, _) = two(l, r, *w)?;
            (a | c, *w)
        }
        Formula::BvXor(l, r, w) => {
            let (a, c, _) = two(l, r, *w)?;
            (a ^ c, *w)
        }
        Formula::BvShl(l, r, w) => {
            let (a, c, m) = two(l, r, *w)?;
            (if c >= u128::from(*w) { 0 } else { (a << c) & m }, *w)
        }
        Formula::BvLShr(l, r, w) => {
            let (a, c, _) = two(l, r, *w)?;
            (if c >= u128::from(*w) { 0 } else { a >> c }, *w)
        }
        Formula::BvNot(x, w) => {
            let (a, wa) = lit(x)?;
            (wa == *w).then_some(())?;
            (!a & mask(*w)?, *w)
        }
        Formula::BvZeroExt(x, k) => {
            let (a, wa) = lit(x)?;
            let w = wa.checked_add(*k)?;
            mask(w)?;
            (a, w)
        }
        Formula::BvSignExt(x, k) => {
            let (a, wa) = lit(x)?;
            let w = wa.checked_add(*k)?;
            let m = mask(w)?;
            let negative = (a >> (wa - 1)) & 1 == 1;
            (if negative { (a | (m & !mask(wa)?)) & m } else { a }, w)
        }
        Formula::BvExtract { inner, high, low } => {
            let (a, wa) = lit(inner)?;
            (*high < wa && low <= high).then_some(())?;
            let w = high - low + 1;
            ((a >> low) & mask(w)?, w)
        }
        Formula::BvConcat(h, l) => {
            let (a, wa) = lit(h)?;
            let (c, wc) = lit(l)?;
            let w = wa.checked_add(wc)?;
            mask(w)?;
            ((a << wc) | c, w)
        }
        _ => return None,
    })
}

/// The operand a node with an identity literal operand denotes (`x | 0`, `x ^ 0`,
/// `x + 0`, `x - 0`, `x & ones`, `x << 0`, `x >> 0`, operands of the node's width):
/// `mov xd, xn` is `orr xd, xzr, xn`, so a copied register is `BvOr(0, x)` until
/// this folds it.
fn identity(f: &Formula) -> Option<Formula> {
    let is = |x: &Formula, want: u128, w: u32| lit(x) == Some((want, w));
    match f {
        Formula::BvOr(l, r, w) | Formula::BvXor(l, r, w) | Formula::BvAdd(l, r, w) => {
            if is(l, 0, *w) {
                Some((**r).clone())
            } else if is(r, 0, *w) {
                Some((**l).clone())
            } else {
                None
            }
        }
        Formula::BvSub(l, r, w) | Formula::BvShl(l, r, w) | Formula::BvLShr(l, r, w) => {
            is(r, 0, *w).then(|| (**l).clone())
        }
        Formula::BvAnd(l, r, w) => {
            let ones = mask(*w)?;
            if is(l, ones, *w) {
                Some((**r).clone())
            } else if is(r, ones, *w) {
                Some((**l).clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Every ground bit-vector subterm folded to its literal, and every identity
/// operation ([`identity`]) to its operand, bottom-up.
fn fold_ground(f: &Formula) -> Formula {
    f.clone().map(&mut |node| match ground(&node) {
        Some((value, width)) => bv(value as i128, width),
        None => identity(&node).unwrap_or(node),
    })
}

fn nodes(f: &Formula) -> usize {
    let mut n = 0usize;
    f.visit(&mut |_| n += 1);
    n
}

fn var_names(f: &Formula) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    f.visit(&mut |node| {
        if let Formula::Var(name, _) = node {
            names.insert(name.clone());
        }
    });
    names
}

/// A name that is not a register: a flag, memory or high-half havoc leaf.
fn non_register_leaf(name: &str) -> bool {
    name.contains("_HAVOC_") || name.starts_with("MEM@") || name.ends_with("_HI_HAVOC")
}

/// Cap a text at [`MAX_TEXT_BYTES`], keeping the suffix and ending the body `…`.
fn cap_text(text: &str) -> String {
    if text.len() <= MAX_TEXT_BYTES {
        return text.to_string();
    }
    let body = text.strip_suffix(SUFFIX).unwrap_or(text);
    let room = MAX_TEXT_BYTES.saturating_sub(SUFFIX.len() + '…'.len_utf8());
    let mut end = room.min(body.len());
    while end > 0 && !body.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…{SUFFIX}", body.get(..end).unwrap_or(""))
}

// ---------------------------------------------------------------------------
// the spec segments for one cut block
// ---------------------------------------------------------------------------

struct SpecSegs {
    block: u32,
    shared: Vec<ValueId>,
    entry_arrivals: Vec<(Formula, Vec<Formula>)>,
    entry_value: Formula,
    entry_reach: Formula,
    loop_arrivals: Vec<(Formula, Vec<Formula>)>,
    loop_value: Formula,
    loop_reach: Formula,
    entry_memory: Formula,
}

fn shape_guard(cx: &super::SpecCx<'_>, segment: &str) -> Result<(), String> {
    if !cx.side.is_empty()
        || !cx.checks.is_empty()
        || !cx.events.is_empty()
        || !cx.result_vars.is_empty()
        || !cx.memory.accesses.is_empty()
    {
        return Err(format!(
            "checks: the {segment} segment has side conditions, checks, events, results or \
             memory accesses ({}, {}, {}, {}, {})",
            cx.side.len(),
            cx.checks.len(),
            cx.events.len(),
            cx.result_vars.len(),
            cx.memory.accesses.len()
        ));
    }
    Ok(())
}

fn arrivals_of(
    cut: Option<SpecCut>,
    segment: &str,
) -> Result<Vec<(Formula, Vec<Formula>)>, String> {
    let cut = cut.ok_or_else(|| format!("the {segment} segment lost its cut"))?;
    let mut out = Vec::new();
    for (path, values) in cut.arrivals {
        let mut fs = Vec::new();
        for (v, value) in cut.shared.iter().zip(values) {
            if value.width != 64 {
                return Err(format!(
                    "width: shared variable %{} is {}-bit at bb{} (64-bit scalars only)",
                    v.index(),
                    value.width,
                    cut.block
                ));
            }
            fs.push(value.f);
        }
        out.push((path, fs));
    }
    Ok(out)
}

/// Whether `f` mentions only entry leaves (`X{n}`, `V{n}`, `SP`).
fn entry_leaves_only(f: &Formula) -> bool {
    var_names(f).iter().all(|n| {
        n == "SP"
            || n.strip_prefix('X')
                .or_else(|| n.strip_prefix('V'))
                .is_some_and(|d| !d.is_empty() && d.chars().all(|c| c.is_ascii_digit()))
    })
}

/// Every entry arrival's path and values mention entry leaves only. In the
/// call-free fragment no fixture reaches the refusal (the spec side's only
/// other leaves are call results, `CER_S#…`, which `call_free` and
/// [`shape_guard`] exclude); it is pinned by a unit test.
fn entry_arrivals_closed(arrivals: &[(Formula, Vec<Formula>)]) -> Result<(), String> {
    for (path, values) in arrivals {
        if !values.iter().chain([path]).all(entry_leaves_only) {
            return Err("entry: an entry-arrival value mentions a non-entry variable".into());
        }
    }
    Ok(())
}

fn spec_segments(
    s: &Subject<'_>,
    blocks: &HashMap<u32, &trust_ir::Block>,
    live: &HashMap<u32, Vec<ValueId>>,
    block: u32,
) -> Result<SpecSegs, String> {
    let blk = blocks.get(&block).ok_or_else(|| format!("bb{block} missing"))?;
    let mut shared: Vec<ValueId> = blk.params.iter().map(|(v, _)| *v).collect();
    shared.sort_by_key(|v| v.index());
    let mut others: Vec<ValueId> = live
        .get(&block)
        .ok_or_else(|| format!("live-in: bb{block} has no live-in set"))?
        .iter()
        .copied()
        .filter(|v| !shared.contains(v))
        .collect();
    others.sort_by_key(|v| v.index());
    shared.extend(others);

    // The entry segment: from the function entry to each edge into `block`.
    let (mut cx, env) = spec_entry(s.input, s.module, s.func, s.sig, s.place, s.decisions)?;
    let entry_memory = cx.memory.entry.clone();
    cx.cut = Some(SpecCut { block, shared: shared.clone(), arrivals: Vec::new() });
    let (entry_value, entry_reach) =
        cx.block(s.func.entry, env, Formula::Bool(true), Vec::new(), 0)?;
    shape_guard(&cx, "entry")?;
    let entry_arrivals = arrivals_of(cx.cut.take(), "entry")?;
    if entry_arrivals.is_empty() {
        return Err("arrivals: the entry segment never arrives at the cut".into());
    }
    entry_arrivals_closed(&entry_arrivals)?;

    // The loop segment: from `block`, its shared variables fresh.
    let (mut cx, mut env) = spec_entry(s.input, s.module, s.func, s.sig, s.place, s.decisions)?;
    // Cut variables currently model 64-bit scalar lanes only. Do not turn
    // Unit live-ins into arbitrary bits or reuse entry definedness at the cut.
    for value in &shared {
        let ty = s.func.typed_value(s.module, *value).ok_or("cut value has no declared type")?;
        if ty.ty == trust_ir::Ty::Unit {
            return Err("Unit live-in at a scalar loop cut is outside the fragment".into());
        }
    }
    env.units.clear();
    env.scalars =
        shared.iter().map(|v| (*v, IrValue { f: cut_var(block, *v), width: 64 })).collect();
    env.aggs.clear();
    env.pairs.clear();
    env.closures.clear();
    cx.cut = Some(SpecCut { block, shared: shared.clone(), arrivals: Vec::new() });
    let (loop_value, loop_reach) =
        cx.block(BlockId::new(block), env, Formula::Bool(true), Vec::new(), 0)?;
    shape_guard(&cx, "loop")?;
    let loop_arrivals = arrivals_of(cx.cut.take(), "loop")?;
    if loop_arrivals.is_empty() {
        return Err("arrivals: the loop segment never arrives at the cut".into());
    }
    Ok(SpecSegs {
        block,
        shared,
        entry_arrivals,
        entry_value,
        entry_reach,
        loop_arrivals,
        loop_value,
        loop_reach,
        entry_memory,
    })
}

// ---------------------------------------------------------------------------
// the machine runs
// ---------------------------------------------------------------------------

struct MachineRun {
    out: PathOutcome,
    arrivals: Vec<MachineCutArrival>,
}

/// Budgeted machine runs (a fresh `CerExec` per run: `steps` never resets).
struct Machine<'s, 'a> {
    s: &'s Subject<'a>,
    h: u64,
    steps: u32,
    /// The total cap ([`MAX_L0_MACHINE_STEPS`] outside the unit tests).
    cap: u32,
}

/// The machine-step cap was reached.
struct Stop;

impl Machine<'_, '_> {
    fn run(&mut self, start: u64, state: MachineState) -> Result<Result<MachineRun, String>, Stop> {
        // A run starts only when its worst case still fits: `steps` never
        // passes `cap`.
        if self.steps.saturating_add(RUN_STEPS) > self.cap {
            return Err(Stop);
        }
        let no_callees = BTreeMap::new();
        let mut ex =
            CerExec::new(self.s.window, &no_callees, &self.s.place.ret, self.s.x18_reserved);
        ex.cut_addrs.insert(self.h);
        let out = ex.run(start, state, Vec::new(), 0, false, Formula::Bool(true));
        self.steps = self.steps.saturating_add(ex.steps);
        Ok(out.map(|out| MachineRun { out, arrivals: std::mem::take(&mut ex.cut_arrivals) }))
    }
}

/// The first reachable word that accesses memory, calls, or is atomic.
fn memory_access(window: &FunctionWindow) -> Option<u64> {
    let sem = Aarch64Semantics;
    let probe = MachineState::symbolic();
    for off in &window.reachable {
        let at = usize::try_from(off.checked_sub(window.start)?).ok()?;
        let Some(bytes) = window.code.get(at..at + 4).and_then(|w| <[u8; 4]>::try_from(w).ok())
        else {
            continue;
        };
        let Ok(insn) = trust_disasm::decode_aarch64(&bytes, *off) else { continue };
        let Ok(effects) = sem.effects(&probe, &insn) else { continue };
        if effects.iter().any(|e| {
            matches!(
                e,
                Effect::MemRead { .. }
                    | Effect::MemWrite { .. }
                    | Effect::Call { .. }
                    | Effect::Aarch64SyncBoundary { .. }
                    | Effect::Aarch64AtomicAccess { .. }
            )
        }) {
            return Some(*off);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// items and their decision
// ---------------------------------------------------------------------------

struct Item {
    name: String,
    m: Formula,
    s: Formula,
    in_loop: bool,
}

/// One (cut block, assignment) pair, ready to decide.
struct Pair {
    block: u32,
    assign: Vec<(u32, u8)>,
    pinned: Vec<u8>,
    items: Vec<Item>,
    outcomes: Vec<ItemOutcome>,
    segments: LoopSegments,
    ir_arrivals: usize,
    m_arrivals: usize,
}

struct Decider {
    cap: u32,
    /// The per-query node cap ([`MAX_QUERY_NODES`] outside the unit tests).
    nodes: usize,
    queries: u32,
    refl: u32,
}

enum Decided {
    /// Every item decided (first-fail may have stopped early: see `complete`).
    Done,
    /// The query cap was reached.
    Effort,
}

impl Decider {
    fn decide_one(&mut self, item: &Item) -> Option<ItemOutcome> {
        let (m, s) = (norm(&item.m), norm(&item.s));
        if m == s {
            self.refl += 1;
            return Some(ItemOutcome::Refl);
        }
        if item.in_loop
            && let Some(leaf) =
                var_names(&m).into_iter().chain(var_names(&s)).find(|n| non_register_leaf(n))
        {
            return Some(ItemOutcome::Unknown(format!("reads the non-register leaf {leaf}")));
        }
        let size = nodes(&m) + nodes(&s);
        if size > self.nodes {
            return Some(ItemOutcome::Unknown(format!(
                "the query has {size} nodes, over the cap of {}",
                self.nodes
            )));
        }
        if self.queries >= self.cap {
            return None;
        }
        self.queries += 1;
        Some(solve(&m, &s))
    }

    /// Decide `pair`'s items from where its outcomes stop; with `first_fail`,
    /// stop at the first item not discharged.
    fn decide(&mut self, pair: &mut Pair, first_fail: bool) -> Decided {
        while let Some(item) = pair.items.get(pair.outcomes.len()) {
            let Some(outcome) = self.decide_one(item) else { return Decided::Effort };
            let stop = first_fail && !outcome.discharged();
            pair.outcomes.push(outcome);
            if stop {
                break;
            }
        }
        Decided::Done
    }
}

/// ay on `NOT (m == s)` in QF_ABV under the gate's effort count and no wall
/// clock (PKG-DET; DECISION_QUEUE BUDGET-1): UNSAT is Proven, SAT a
/// counterexample, anything else (an FP node, a spent count) Unknown. Never
/// authority: its result is a record.
fn solve(m: &Formula, s: &Formula) -> ItemOutcome {
    crate::original_conjunction_certificate::require_production_allowed();
    let goal = Formula::Not(b(Formula::Eq(b(m.clone()), b(s.clone()))));
    let effort = match gate_query_effort(&goal) {
        Ok(effort) => effort,
        Err(e) => return ItemOutcome::Unknown(e),
    };
    let mut solver =
        match ay::Solver::try_new_with_config(ay::Logic::QfAbv, ay::SolverConfig::default()) {
            Ok(solver) => solver,
            Err(e) => return ItemOutcome::Unknown(format!("ay solver: {e:?}")),
        };
    let term = match formula_to_term(&mut solver, &goal) {
        Ok(term) => term,
        Err(e) => return ItemOutcome::Unknown(e),
    };
    if let Err(e) = solver.try_assert_term(term) {
        return ItemOutcome::Unknown(format!("ay assert: {e:?}"));
    }
    match gate_check_sat(&mut solver, effort, None) {
        Discharge::Proven => ItemOutcome::Proven,
        Discharge::CounterExample => ItemOutcome::CounterExample,
        Discharge::Unknown(why) => ItemOutcome::Unknown(why),
    }
}

// ---------------------------------------------------------------------------
// one pair
// ---------------------------------------------------------------------------

/// The entry arrival on the machine side, merged over its paths.
struct MachineEntry {
    reach: Formula,
    gpr: Vec<Formula>,
    frame: Vec<(String, Formula)>,
    out: PathOutcome,
}

fn machine_entry(run: MachineRun) -> MachineEntry {
    let paths: Vec<Formula> = run.arrivals.iter().map(|a| a.path.clone()).collect();
    let reach = any_of(&paths);
    let gpr = (0..31)
        .map(|r| {
            let arms: Vec<(Formula, Formula)> = run
                .arrivals
                .iter()
                .filter_map(|a| a.state.gpr.get(r).map(|v| (a.path.clone(), v.clone())))
                .collect();
            cascade(&arms).unwrap_or_else(|| bv(0, 64))
        })
        .collect();
    let mut frame: Vec<(String, Formula)> = Vec::new();
    if let Some(first) = run.arrivals.first() {
        for (k, (slot, _)) in frame_values(&first.state).into_iter().enumerate() {
            let arms: Vec<(Formula, Formula)> = run
                .arrivals
                .iter()
                .filter_map(|a| {
                    frame_values(&a.state).get(k).map(|(_, v)| (a.path.clone(), v.clone()))
                })
                .collect();
            if let Some(v) = cascade(&arms) {
                frame.push((slot, v));
            }
        }
    }
    MachineEntry { reach, gpr, frame, out: run.out }
}

/// The candidate registers of each shared variable at the entry arrival.
fn locate(seg: &SpecSegs, me: &MachineEntry, x18_reserved: bool) -> Result<Vec<Vec<u8>>, ValueId> {
    let top: u8 = if x18_reserved { 17 } else { 18 };
    let mut out = Vec::new();
    for (j, v) in seg.shared.iter().enumerate() {
        let arms: Vec<(Formula, Formula)> = seg
            .entry_arrivals
            .iter()
            .filter_map(|(p, vals)| vals.get(j).map(|x| (p.clone(), x.clone())))
            .collect();
        let want = cascade(&arms).map(|f| norm(&f));
        let regs: Vec<u8> = (0..=top)
            .filter(|r| {
                me.gpr.get(usize::from(*r)).is_some_and(|g| want.as_ref() == Some(&norm(g)))
            })
            .collect();
        if regs.is_empty() {
            return Err(*v);
        }
        out.push(regs);
    }
    Ok(out)
}

/// Injective assignments in candidate order, at most [`MAX_ASSIGNMENTS`].
fn assignments(cands: &[Vec<u8>]) -> Vec<Vec<u8>> {
    fn go(cands: &[Vec<u8>], cur: &mut Vec<u8>, out: &mut Vec<Vec<u8>>) {
        if out.len() >= MAX_ASSIGNMENTS {
            return;
        }
        let Some(here) = cands.get(cur.len()) else {
            out.push(cur.clone());
            return;
        };
        for r in here {
            if !cur.contains(r) {
                cur.push(*r);
                go(cands, cur, out);
                cur.pop();
            }
        }
    }
    let mut out = Vec::new();
    go(cands, &mut Vec::new(), &mut out);
    out
}

/// The loop run's entry state at `h` for cut block `block`.
fn cut_state(
    s: &Subject<'_>,
    seg: &SpecSegs,
    assign: &[u8],
    pins: &BTreeMap<u8, Formula>,
) -> MachineState {
    let block = seg.block;
    let mut st = MachineState::symbolic();
    for (r, slot) in st.gpr.iter_mut().enumerate() {
        *slot = havoc_gpr(block, r);
    }
    for r in FRAME_GPRS {
        if let Some(slot) = st.gpr.get_mut(r) {
            *slot = var64(frame_name(&format!("X{r}")));
        }
    }
    if s.x18_reserved
        && let Some(slot) = st.gpr.get_mut(18)
    {
        *slot = var64("X18".into());
    }
    for (v, r) in seg.shared.iter().zip(assign) {
        if let Some(slot) = st.gpr.get_mut(usize::from(*r)) {
            *slot = cut_var(block, *v);
        }
    }
    for (r, psi) in pins {
        if let Some(slot) = st.gpr.get_mut(usize::from(*r)) {
            *slot = psi.clone();
        }
    }
    st.sp = var64(frame_name("SP"));
    for (r, slot) in st.fpr.iter_mut().enumerate() {
        *slot = if FRAME_DREGS.contains(&r) {
            Formula::BvConcat(
                b(var64(format!("D{r}@bb{block}_HI_HAVOC"))),
                b(var64(frame_name(&format!("D{r}")))),
            )
        } else {
            Formula::Var(format!("V{r}@bb{block}_HAVOC"), Sort::BitVec(128))
        };
    }
    st.flags = Flags::symbolic(&format!("bb{block}_HAVOC"));
    st.memory = Formula::Var(
        format!("MEM@bb{block}_HAVOC"),
        Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
    );
    st
}

/// Arrival-merged register values of a loop run.
fn arrival_gpr(run: &MachineRun, r: usize) -> Option<Formula> {
    let arms: Vec<(Formula, Formula)> = run
        .arrivals
        .iter()
        .filter_map(|a| a.state.gpr.get(r).map(|v| (a.path.clone(), v.clone())))
        .collect();
    cascade(&arms)
}

/// Pinned registers: not coupled, never written by the loop segment, and read
/// by a value the items compare.
fn find_pins(
    s: &Subject<'_>,
    seg: &SpecSegs,
    assign: &[u8],
    run: &MachineRun,
    me: &MachineEntry,
) -> BTreeMap<u8, Formula> {
    let top: u8 = if s.x18_reserved { 17 } else { 18 };
    let paths: Vec<Formula> = run.arrivals.iter().map(|a| a.path.clone()).collect();
    let mut read = var_names(&any_of(&paths));
    read.extend(var_names(&run.out.value));
    read.extend(var_names(&run.out.reach));
    for r in assign {
        if let Some(v) = arrival_gpr(run, usize::from(*r)) {
            read.extend(var_names(&v));
        }
    }
    let mut pins = BTreeMap::new();
    for r in (0..=top).filter(|r| !assign.contains(r)) {
        let me_self = havoc_gpr(seg.block, usize::from(r));
        let name = match &me_self {
            Formula::Var(n, _) => n.clone(),
            _ => continue,
        };
        let unchanged = run
            .arrivals
            .iter()
            .all(|a| a.state.gpr.get(usize::from(r)).is_some_and(|v| abi_fold(v) == me_self));
        if unchanged
            && read.contains(&name)
            && let Some(psi) = me.gpr.get(usize::from(r))
        {
            pins.insert(r, norm(psi));
        }
    }
    pins
}

fn eq_items(
    items: &mut Vec<Item>,
    prefix: &str,
    pairs: Vec<(String, Formula, Formula)>,
    psi: &HashMap<String, Formula>,
    in_loop: bool,
) {
    for (slot, end, start) in pairs {
        items.push(Item {
            name: format!("{prefix}({slot})"),
            m: substitute(&end, psi),
            s: start,
            in_loop,
        });
    }
}

#[allow(clippy::too_many_lines)]
fn build_pair(
    s: &Subject<'_>,
    seg: &SpecSegs,
    me: &MachineEntry,
    plan: &abi_extensions::Plan,
    assign: &[u8],
    machine: &mut Machine<'_, '_>,
) -> Result<Result<Pair, String>, Stop> {
    let block = seg.block;
    let h = machine.h;
    // First run, no pins; then pinned registers seeded with Ψ.
    let first = match machine.run(h, cut_state(s, seg, assign, &BTreeMap::new()))? {
        Ok(run) => run,
        Err(e) => return Ok(Err(format!("machine loop segment: {e}"))),
    };
    let pins = find_pins(s, seg, assign, &first, me);
    let run = if pins.is_empty() {
        first
    } else {
        match machine.run(h, cut_state(s, seg, assign, &pins))? {
            Ok(run) => run,
            Err(e) => return Ok(Err(format!("machine loop segment: {e}"))),
        }
    };

    // Ψ: each CUT_M_ frame name -> its entry-arrival value.
    let psi: HashMap<String, Formula> =
        me.frame.iter().map(|(slot, v)| (frame_name(slot), v.clone())).collect();

    // IR merges.
    let ir_entry_paths: Vec<Formula> = seg.entry_arrivals.iter().map(|(p, _)| p.clone()).collect();
    let reach_arr_ir = any_of(&ir_entry_paths);
    let ir_entry_val = |j: usize| {
        let arms: Vec<(Formula, Formula)> = seg
            .entry_arrivals
            .iter()
            .filter_map(|(p, v)| v.get(j).map(|x| (p.clone(), x.clone())))
            .collect();
        cascade(&arms).unwrap_or_else(|| bv(0, 64))
    };
    let ir_loop_paths: Vec<Formula> = seg.loop_arrivals.iter().map(|(p, _)| p.clone()).collect();
    let c_ir = any_of(&ir_loop_paths);
    let ir_loop_val = |j: usize| {
        let arms: Vec<(Formula, Formula)> = seg
            .loop_arrivals
            .iter()
            .filter_map(|(p, v)| v.get(j).map(|x| (p.clone(), x.clone())))
            .collect();
        cascade(&arms).unwrap_or_else(|| bv(0, 64))
    };
    // Machine merges.
    let m_loop_paths: Vec<Formula> = run.arrivals.iter().map(|a| a.path.clone()).collect();
    let c_m = any_of(&m_loop_paths);
    let zero = bv(0, 64);
    let guard = |c: &Formula, x: Formula| Formula::Ite(b(c.clone()), b(x), b(zero.clone()));
    let masked = |c: &Formula, x: Formula| Formula::Ite(b(c.clone()), b(zero.clone()), b(x));

    let mut items: Vec<Item> = Vec::new();
    let push = |items: &mut Vec<Item>, name: String, m: Formula, s: Formula, in_loop: bool| {
        items.push(Item { name, m, s, in_loop });
    };
    // ---- the entry segment ----
    for (side, arr, ret) in
        [("ir", &reach_arr_ir, &seg.entry_reach), ("m", &me.reach, &me.out.reach)]
    {
        let both = [arr.clone(), ret.clone()];
        push(
            &mut items,
            format!("entry.cover.{side}(or)"),
            bit(&Formula::Or(both.to_vec())),
            bv(1, 1),
            false,
        );
        push(
            &mut items,
            format!("entry.cover.{side}(and)"),
            bit(&Formula::And(both.to_vec())),
            bv(0, 1),
            false,
        );
    }
    push(&mut items, "entry.reach".into(), bit(&me.reach), bit(&reach_arr_ir), false);
    push(
        &mut items,
        "entry.return".into(),
        masked(&me.reach, me.out.value.clone()),
        masked(&reach_arr_ir, seg.entry_value.clone()),
        false,
    );
    for (j, (v, r)) in seg.shared.iter().zip(assign).enumerate() {
        let g = me.gpr.get(usize::from(*r)).cloned().unwrap_or_else(|| bv(0, 64));
        push(
            &mut items,
            format!("entry.couple(%{} in X{r})", v.index()),
            guard(&reach_arr_ir, g),
            guard(&reach_arr_ir, ir_entry_val(j)),
            false,
        );
    }
    eq_items(&mut items, "entry.frame", me.out.abi.original_equations(), &HashMap::new(), false);
    if s.x18_reserved {
        push(&mut items, "entry.x18".into(), bit(&me.out.x18_written), bv(0, 1), false);
    }
    for (k, (l, r)) in plan.entry_equations().into_iter().enumerate() {
        push(&mut items, format!("entry.model({k})"), l, r, false);
    }
    // ---- the loop segment ----
    for (j, (v, r)) in seg.shared.iter().zip(assign).enumerate() {
        let selfv = cut_var(block, *v);
        let m = arrival_gpr(&run, usize::from(*r)).unwrap_or_else(|| selfv.clone());
        push(
            &mut items,
            format!("step(%{} in X{r})", v.index()),
            ite_unless_same(&c_m, m, selfv.clone()),
            ite_unless_same(&c_ir, ir_loop_val(j), selfv),
            true,
        );
    }
    for (r, p) in &pins {
        let m = arrival_gpr(&run, usize::from(*r)).unwrap_or_else(|| p.clone());
        push(
            &mut items,
            format!("step.pinned(X{r})"),
            ite_unless_same(&c_m, m, p.clone()),
            p.clone(),
            true,
        );
    }
    let first_arrival_frame: Vec<(String, Formula)> = match run.arrivals.first() {
        Some(a) => frame_values(&a.state),
        None => Vec::new(),
    };
    for (k, (slot, _)) in first_arrival_frame.iter().enumerate() {
        let arms: Vec<(Formula, Formula)> = run
            .arrivals
            .iter()
            .filter_map(|a| frame_values(&a.state).get(k).map(|(_, v)| (a.path.clone(), v.clone())))
            .collect();
        let selfv = var64(frame_name(slot));
        let value = cascade(&arms).unwrap_or_else(|| selfv.clone());
        let want = psi.get(&frame_name(slot)).cloned().unwrap_or_else(|| selfv.clone());
        push(
            &mut items,
            format!("step.frame({slot})"),
            substitute(&ite_unless_same(&c_m, value, selfv), &psi),
            want,
            true,
        );
    }
    push(&mut items, "exit.cond".into(), bit(&c_m), bit(&c_ir), true);
    push(
        &mut items,
        "exit.return".into(),
        masked(&c_m, run.out.value.clone()),
        masked(&c_ir, seg.loop_value.clone()),
        true,
    );
    eq_items(&mut items, "exit.frame", run.out.abi.original_equations(), &psi, true);
    for (side, c, ret) in [("ir", &c_ir, &seg.loop_reach), ("m", &c_m, &run.out.reach)] {
        let both = [c.clone(), ret.clone()];
        push(
            &mut items,
            format!("cover.{side}(or)"),
            bit(&Formula::Or(both.to_vec())),
            bv(1, 1),
            true,
        );
        push(
            &mut items,
            format!("cover.{side}(and)"),
            bit(&Formula::And(both.to_vec())),
            bv(0, 1),
            true,
        );
    }
    if s.x18_reserved {
        push(&mut items, "x18".into(), bit(&run.out.x18_written), bv(0, 1), true);
    }

    // A loop item over a non-register leaf ends the pair (L1's `within`
    // would reject it): flags, memory or a D register's high half.
    for item in items.iter().filter(|i| i.in_loop) {
        let (m, sv) = (norm(&substitute(&item.m, &psi)), norm(&item.s));
        if let Some(leaf) =
            var_names(&m).into_iter().chain(var_names(&sv)).find(|n| non_register_leaf(n))
        {
            return Ok(Err(format!("`{}` reads the non-register leaf {leaf}", item.name)));
        }
    }

    let segments = segments_of(s, seg, assign, &pins, me, &run, &c_m, &c_ir, &reach_arr_ir);
    Ok(Ok(Pair {
        block,
        assign: seg.shared.iter().zip(assign).map(|(v, r)| (v.index(), *r)).collect(),
        pinned: pins.keys().copied().collect(),
        items,
        outcomes: Vec::new(),
        segments,
        ir_arrivals: seg.loop_arrivals.len(),
        m_arrivals: run.arrivals.len(),
    }))
}

#[allow(clippy::too_many_arguments)]
fn segments_of(
    s: &Subject<'_>,
    seg: &SpecSegs,
    assign: &[u8],
    pins: &BTreeMap<u8, Formula>,
    me: &MachineEntry,
    run: &MachineRun,
    c_m: &Formula,
    c_ir: &Formula,
    reach_arr_ir: &Formula,
) -> LoopSegments {
    let block = seg.block;
    let ir_vars: Vec<(String, u32)> =
        seg.shared.iter().map(|v| (format!("CUT_bb{block}_v{}", v.index()), 64)).collect();
    let pick = |arms: &[(Formula, Vec<Formula>)], j: usize| {
        let a: Vec<(Formula, Formula)> =
            arms.iter().filter_map(|(p, v)| v.get(j).map(|x| (p.clone(), x.clone()))).collect();
        cascade(&a).unwrap_or_else(|| bv(0, 64))
    };
    let entry_ir: Vec<Formula> =
        (0..seg.shared.len()).map(|j| pick(&seg.entry_arrivals, j)).collect();
    let step_ir: Vec<Formula> = seg
        .shared
        .iter()
        .enumerate()
        .map(|(j, v)| ite_unless_same(c_ir, pick(&seg.loop_arrivals, j), cut_var(block, *v)))
        .collect();
    let mut regs = Vec::new();
    let mut entry_m = Vec::new();
    let mut step_m = Vec::new();
    let top: usize = if s.x18_reserved { 17 } else { 18 };
    for r in 0..=top {
        let Ok(r8) = u8::try_from(r) else { continue };
        let (name, role, selfv) = if let Some(j) = assign.iter().position(|x| *x == r8) {
            let v = seg.shared.get(j).copied().unwrap_or(ValueId::new(0));
            (format!("CUT_bb{block}_v{}", v.index()), SegRole::Coupled(j), cut_var(block, v))
        } else if let Some(p) = pins.get(&r8) {
            (format!("X{r}@bb{block}_PINNED"), SegRole::Pinned(p.clone()), p.clone())
        } else {
            (format!("X{r}@bb{block}_HAVOC"), SegRole::Havoc, havoc_gpr(block, r))
        };
        let value = arrival_gpr(run, r).unwrap_or_else(|| selfv.clone());
        regs.push(SegReg { name, width: 64, role });
        entry_m.push(me.gpr.get(r).cloned().unwrap_or_else(|| bv(0, 64)));
        step_m.push(abi_fold(&ite_unless_same(c_m, value, selfv)));
    }
    let mut exit_frame_m = Vec::new();
    let mut entry_frame_m = Vec::new();
    let exits = run.out.abi.original_equations();
    let entries = me.out.abi.original_equations();
    for (k, (slot, entry_value)) in me.frame.iter().enumerate() {
        let arch = slot.clone();
        let entry_leaf = if slot.starts_with('D') { format!("{slot}_ENTRY") } else { slot.clone() };
        regs.push(SegReg {
            name: frame_name(slot),
            width: 64,
            role: SegRole::Frame { arch, entry: entry_leaf },
        });
        entry_m.push(entry_value.clone());
        let selfv = var64(frame_name(slot));
        let value = run
            .arrivals
            .iter()
            .map(|a| (a.path.clone(), frame_values(&a.state).get(k).map(|(_, v)| v.clone())))
            .filter_map(|(p, v)| v.map(|v| (p, v)))
            .collect::<Vec<_>>();
        step_m.push(abi_fold(&ite_unless_same(
            c_m,
            cascade(&value).unwrap_or_else(|| selfv.clone()),
            selfv,
        )));
        // `frame_values` is in `AbiExit::original_equations`' slot order.
        exit_frame_m.push(exits.get(k).map(|(_, e, _)| abi_fold(e)).unwrap_or_else(|| bv(0, 64)));
        entry_frame_m
            .push(entries.get(k).map(|(_, e, _)| abi_fold(e)).unwrap_or_else(|| bv(0, 64)));
    }
    LoopSegments {
        ir_vars,
        entry_ir,
        step_ir,
        reach_ret_ir: seg.loop_reach.clone(),
        ret_ir: seg.loop_value.clone(),
        regs,
        entry_m,
        step_m,
        reach_ret_m: run.out.reach.clone(),
        ret_m: run.out.value.clone(),
        exit_frame_m,
        entry_reach_ir: reach_arr_ir.clone(),
        entry_reach_m: me.reach.clone(),
        entry_ret_ir: seg.entry_value.clone(),
        entry_ret_m: me.out.value.clone(),
        entry_frame_m,
    }
}

// ---------------------------------------------------------------------------
// the measurement
// ---------------------------------------------------------------------------

fn head(header: u32, pair: &Pair, h: u64) -> String {
    let mut t = format!("{PREFIX}IR bb{}", pair.block);
    if pair.block != header {
        t.push_str(&format!(" (loop header bb{header})"));
    }
    t.push_str(&format!(" at {h:#x}; live-ins "));
    t.push_str(
        &pair.assign.iter().map(|(v, r)| format!("%{v} in X{r}")).collect::<Vec<_>>().join(", "),
    );
    if !pair.pinned.is_empty() {
        t.push_str("; pinned ");
        t.push_str(&pair.pinned.iter().map(|r| format!("X{r}")).collect::<Vec<_>>().join(", "));
    }
    t
}

fn counts(pair: &Pair) -> (usize, usize, usize, usize) {
    let (mut pe, mut e, mut pl, mut l) = (0, 0, 0, 0);
    for (k, item) in pair.items.iter().enumerate() {
        let ok = pair.outcomes.get(k).is_some_and(ItemOutcome::discharged);
        if item.in_loop {
            l += 1;
            pl += usize::from(ok);
        } else {
            e += 1;
            pe += usize::from(ok);
        }
    }
    (pe, e, pl, l)
}

#[allow(clippy::too_many_lines)]
fn measure_inner(s: &Subject<'_>) -> Result<Measurement, String> {
    // ---- declines (the function is outside L0's fragment) ----
    if !s.call_free {
        return Err(
            "call-free: the function has an IR call site, a machine call site, a trap tail or an \
             admitted dead tail"
                .into(),
        );
    }
    match &s.place.ret {
        ReturnPlace::Scalar(p) if p.slot == Slot::Gpr(0) && p.width == 64 => {}
        _ => return Err("width: the result is not a 64-bit X0 scalar".into()),
    }
    if s.place.params.iter().any(|pp| {
        !matches!(pp, ParamPlace::Scalar(p) if matches!(p.slot, Slot::Gpr(_)) && p.width == 64)
    }) {
        return Err("width: a parameter is not a 64-bit GPR scalar".into());
    }
    let blocks: HashMap<u32, &trust_ir::Block> =
        s.func.blocks.iter().map(|blk| (blk.id.index(), blk)).collect();
    let entry = s.func.entry.index();
    let headers = loop_headers(&blocks, entry).map_err(|e| format!("headers: {e}"))?;
    let [header] = headers.as_slice() else {
        return Err(format!("headers: {} loop header(s), not one", headers.len()));
    };
    let header = *header;
    if header == entry {
        return Err("entry: the loop header is the function's entry block".into());
    }
    let live = live_in_sets(&blocks)
        .ok_or_else(|| "live-in: the live-in analysis could not be completed".to_string())?;
    let mut cands = vec![header];
    let mut others: Vec<u32> =
        blocks.keys().copied().filter(|b| *b != entry && *b != header).collect();
    others.sort_unstable();
    cands.extend(others);
    cands.truncate(MAX_CUT_CANDIDATES);
    let mut segs: Vec<SpecSegs> = Vec::new();
    let mut spec_errors: Vec<String> = Vec::new();
    for block in cands {
        match spec_segments(s, &blocks, &live, block) {
            Ok(seg) => segs.push(seg),
            Err(e) => spec_errors.push(format!("bb{block}: {e}")),
        }
    }
    let Some(first) = segs.first() else {
        return Err(format!(
            "segments: no candidate cut block yields both segments: {}",
            spec_errors.join("; ")
        ));
    };

    // ---- from here on, every outcome is a measurement ----
    let mut m = Measurement {
        text: String::new(),
        header,
        cut: None,
        backward_targets: Vec::new(),
        live_ins: Vec::new(),
        pinned: Vec::new(),
        items: Vec::new(),
        refl: 0,
        queries: 0,
        machine_steps: 0,
        ir_loop_arrivals: 0,
        machine_loop_arrivals: 0,
        tried: Vec::new(),
        ms: 0,
        segments: None,
        pairs: Vec::new(),
    };
    let targets: Vec<u64> = backward_branch_targets(&s.window.code, s.window.start)
        .into_iter()
        .filter(|t| s.window.reachable.contains(t))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    m.backward_targets.clone_from(&targets);
    let [h] = targets.as_slice() else {
        m.text = format!(
            "{PREFIX}IR loop header bb{header}: the bytes have {} backward-branch target(s) [{}], \
             not one{SUFFIX}",
            targets.len(),
            targets.iter().map(|t| format!("{t:#x}")).collect::<Vec<_>>().join(", ")
        );
        return Ok(m);
    };
    let h = *h;
    if h == s.window.start {
        m.text = format!(
            "{PREFIX}IR bb{}: the machine cut {h:#x} is the function's first instruction{SUFFIX}",
            first.block
        );
        return Ok(m);
    }
    if let Some(pc) = memory_access(s.window) {
        m.text = format!(
            "{PREFIX}the bytes access memory at {pc:#x} (L0 locates live-ins in registers \
             only){SUFFIX}"
        );
        return Ok(m);
    }
    let plan =
        abi_extensions::Plan::new(s.module, s.func.calling_conv, &s.sig.0, &s.sig.1, s.place, true)
            .map_err(|e| format!("abi: {e}"))?;
    let mut machine = Machine { s, h, steps: 0, cap: STEP_CAP.get() };
    let step_cap = machine.cap;
    let effort = |m: &mut Measurement, queries: u32, cap: u32, steps: u32| {
        m.text = format!(
            "{PREFIX}effort bound reached ({queries} solver queries of {cap}, {steps} machine \
             steps of {step_cap}){SUFFIX}"
        );
    };
    let mut decider = Decider { cap: QUERY_CAP.get(), nodes: NODE_CAP.get(), queries: 0, refl: 0 };
    let exhaustive = EXHAUSTIVE.get();

    // The machine entry segment (independent of the IR cut block).
    let mut entry_state = MachineState::symbolic();
    entry_state.memory = first.entry_memory.clone();
    plan.apply_entry(&mut entry_state);
    let me = match machine.run(s.window.start, entry_state) {
        Err(Stop) => {
            effort(&mut m, decider.queries, decider.cap, machine.steps);
            m.machine_steps = machine.steps;
            return Ok(m);
        }
        Ok(Err(e)) => {
            m.text = format!(
                "{PREFIX}IR bb{} at {h:#x}: machine entry segment: {e}{SUFFIX}",
                first.block
            );
            m.machine_steps = machine.steps;
            return Ok(m);
        }
        Ok(Ok(run)) => machine_entry(run),
    };

    // Every (cut block, assignment) pair, first-fail; the first to discharge
    // every item is reported. Otherwise the formed pair with the longest
    // discharged prefix is re-decided with every item and reported (a pair that
    // could not be formed is reported only when none was).
    let mut reported: Option<Result<Pair, String>> = None;
    for seg in &segs {
        let cands = match locate(seg, &me, s.x18_reserved) {
            Ok(c) => c,
            Err(v) => {
                let text = format!(
                    "{PREFIX}IR bb{} at {h:#x}: %{} is in no register X0-X{} at the entry \
                     arrival{SUFFIX}",
                    seg.block,
                    v.index(),
                    if s.x18_reserved { 17 } else { 18 }
                );
                m.tried.push(format!("bb{}: no location", seg.block));
                reported.get_or_insert(Err(text));
                continue;
            }
        };
        for assign in assignments(&cands) {
            let label = format!(
                "bb{} [{}]",
                seg.block,
                seg.shared
                    .iter()
                    .zip(&assign)
                    .map(|(v, r)| format!("%{} in X{r}", v.index()))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            m.tried.push(label);
            let mut pair = match build_pair(s, seg, &me, &plan, &assign, &mut machine) {
                Err(Stop) => {
                    effort(&mut m, decider.queries, decider.cap, machine.steps);
                    m.machine_steps = machine.steps;
                    m.refl = decider.refl;
                    m.queries = decider.queries;
                    return Ok(m);
                }
                Ok(Err(text)) => {
                    reported.get_or_insert(Err(format!(
                        "{PREFIX}IR bb{} at {h:#x}: {text}{SUFFIX}",
                        seg.block
                    )));
                    continue;
                }
                Ok(Ok(pair)) => pair,
            };
            // The exhaustive hook decides past the first failure; the
            // discharged prefix, and so the report, is the same.
            let decided = match decider.decide(&mut pair, true) {
                Decided::Done if exhaustive => decider.decide(&mut pair, false),
                d => d,
            };
            if let Decided::Effort = decided {
                fill(&mut m, &pair, h);
                effort(&mut m, decider.queries, decider.cap, machine.steps);
                m.machine_steps = machine.steps;
                m.refl = decider.refl;
                m.queries = decider.queries;
                return Ok(m);
            }
            if exhaustive {
                m.pairs.push(PairRecord {
                    block: pair.block,
                    live_ins: pair.assign.clone(),
                    pinned: pair.pinned.clone(),
                    items: items_of(&pair),
                });
            }
            let all = pair.outcomes.len() == pair.items.len()
                && pair.outcomes.iter().all(ItemOutcome::discharged);
            if all {
                let (_, e, _, l) = counts(&pair);
                let refl = pair.outcomes.iter().filter(|o| **o == ItemOutcome::Refl).count();
                let ay = pair.outcomes.len() - refl;
                fill(&mut m, &pair, h);
                m.text = format!(
                    "{}: entry segment {e}/{e} and loop segment {l}/{l} items discharged ({refl} \
                     by refl, {ay} by ay){SUFFIX}",
                    head(header, &pair, h)
                );
                m.machine_steps = machine.steps;
                m.refl = decider.refl;
                m.queries = decider.queries;
                return Ok(m);
            }
            // Report the pair whose first-fail run discharged the longest prefix (the
            // first such pair on a tie): with candidate registers that coincide at the
            // entry, the first assignment is often one the loop clobbers.
            let reach = discharged_prefix(&pair);
            if !matches!(&reported, Some(Ok(best)) if discharged_prefix(best) >= reach) {
                reported = Some(Ok(pair));
            }
        }
    }
    m.machine_steps = machine.steps;
    match reported {
        None => {
            m.text = format!(
                "{PREFIX}IR bb{} at {h:#x}: no live-in assignment was formed{SUFFIX}",
                first.block
            );
        }
        Some(Err(text)) => m.text = text,
        Some(Ok(mut pair)) => {
            let effort_hit = matches!(decider.decide(&mut pair, false), Decided::Effort);
            fill(&mut m, &pair, h);
            if effort_hit {
                effort(&mut m, decider.queries, decider.cap, machine.steps);
            } else {
                let (pe, e, pl, l) = counts(&pair);
                let named = |want: &dyn Fn(&ItemOutcome) -> bool| {
                    pair.items
                        .iter()
                        .zip(&pair.outcomes)
                        .find(|(_, o)| want(o))
                        .map(|(i, o)| (i.name.clone(), o.clone()))
                };
                let mut t = format!(
                    "{}: entry segment {pe}/{e} and loop segment {pl}/{l} items discharged",
                    head(header, &pair, h)
                );
                if let Some((name, _)) = named(&|o| *o == ItemOutcome::CounterExample) {
                    t.push_str(&format!(
                        "; `{name}` has a counterexample (not evidence against the bytes in this \
                         slice)"
                    ));
                }
                if let Some((name, ItemOutcome::Unknown(why))) =
                    named(&|o| matches!(o, ItemOutcome::Unknown(_)))
                {
                    t.push_str(&format!(" | `{name}` did not conclude: {why}"));
                }
                let also: Vec<String> = segs
                    .iter()
                    .map(|g| g.block)
                    .filter(|b| *b != pair.block)
                    .map(|b| format!("bb{b}"))
                    .collect();
                if !also.is_empty() {
                    t.push_str(&format!("; also tried {}", also.join(", ")));
                }
                t.push_str(SUFFIX);
                m.text = t;
            }
        }
    }
    m.refl = decider.refl;
    m.queries = decider.queries;
    Ok(m)
}

/// How many leading items a first-fail run discharged.
fn discharged_prefix(pair: &Pair) -> usize {
    pair.outcomes.iter().take_while(|o| o.discharged()).count()
}

/// The pair's items with their outcomes (`not decided` past a first failure).
fn items_of(pair: &Pair) -> Vec<(String, ItemOutcome)> {
    pair.items
        .iter()
        .enumerate()
        .map(|(k, i)| {
            let o = pair
                .outcomes
                .get(k)
                .cloned()
                .unwrap_or_else(|| ItemOutcome::Unknown("not decided (first-fail)".into()));
            (i.name.clone(), o)
        })
        .collect()
}

fn fill(m: &mut Measurement, pair: &Pair, h: u64) {
    m.cut = Some((pair.block, h));
    m.live_ins.clone_from(&pair.assign);
    m.pinned.clone_from(&pair.pinned);
    m.items = items_of(pair);
    m.ir_loop_arrivals = pair.ir_arrivals;
    m.machine_loop_arrivals = pair.m_arrivals;
    m.segments = Some(pair.segments.clone());
}

#[cfg(all(test, feature = "kernel-recheck"))]
mod tests;
