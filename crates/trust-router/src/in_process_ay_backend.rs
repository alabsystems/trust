// ignore-tidy-file-filelength -- pre-existing size, recorded 2026-10-17; do not grow casually
// trust-router/in_process_ay_backend.rs: In-process ay-dpll SMT backend.
//
// Trust: This backend replaces the subprocess SMT path (incremental_ay.rs,
// smtlib_backend.rs) for L0 safety obligations. Instead of serializing the VC
// formula to textual SMT-LIB2 and shelling out to the `ay` binary — which
// discards ay's in-process proof artifacts — this backend solves the VC
// directly against the linked ay-dpll library and captures ay's real
// `UnsatProofArtifact`.
//
// ## Soundness boundary (the one load-bearing rule)
//
// `verify()` returns `VerificationResult::Proved` IF AND ONLY IF:
//   1. ay reports the violation formula UNSAT (`ExecuteTypedResult::Verified`), AND
//   2. there is an `unsat_proof` whose `strict_verdict` is
//      `StrictProofVerdict::Verified(_)`.
//
// In every other case (UNSAT but artifact `None`, UNSAT but strict verdict
// `Rejected`, `Unknown`, `ExecuteError`, empty result vector, any guarded
// failure) the backend returns `Unknown` — NEVER `Proved`. A SAT result
// (`Counterexample`) returns `Failed`. This guarantees the backend can never
// false-PROVE: a reported `Proved` always carries a strict-checked ay
// refutation proof.
//
// ## VC convention
//
// The VC formula IS the violation / failure condition (the same convention the
// subprocess `smtlib_backend::parse_solver_output` uses: unsat => Proved, sat
// => Failed). We assert the formula and check satisfiability. UNSAT (no
// violation reachable) => candidate PROVED. SAT (violation witnessed) => Failed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use ay::{
    ProofAcceptanceMode, StrictProofVerdict, StrictVerdictStop, UnsatProofArtifact,
    is_reserved_symbol, panic_payload_to_string,
};
use ay_bindings::execute_direct::{
    self, CheckSatOutcome, ExecuteCounterexample, ExecuteDegradation, ExecuteDegradationKind,
    ExecuteTypedResult, ModelValue,
};

#[cfg(all(test, feature = "carcara-crosscheck"))]
#[path = "in_process_ay_backend/allocation_replay_tests.rs"]
mod allocation_replay_tests;
use ay_bindings::{AYProgram, Constraint};
use sha2::{Digest, Sha256};
use trust_types::ay_bridge::{
    AyBridgeError, DatatypeDefs, check_datatype_terms, formula_to_expr_with_datatype_defs,
    is_lowerable_formula, sort_to_ay_in, undefined_datatype_reference, unlowerable_sort_position,
};
use trust_types::determinism::{EffortScale, QueryEffort, StopCause};
use trust_types::{
    Counterexample, CounterexampleValue, Formula, ProofStrength, Sort, VcKind,
    VerificationCondition, VerificationResult, check_formula_sort,
};

// Trust: scoped suppression of solver-internal tracing diagnostics (see ay_log.rs).
use crate::ay_log::with_ay_diagnostics_policy;
use crate::backend_trait::unsupported_mir_unknown;
use crate::disjoint_components::{
    ComponentRetryBudget, collect_pred_symbols, disjoint_conjunctive_components,
    flatten_conjunction_spine_owned, timeout_within_deadline, uninterpreted_signature_conflict,
    uninterpreted_symbol_signatures,
};
use crate::{BackendRole, VerificationBackend, ay_symbol_namespace, smt2_export};

/// Stable solver name reported in every `VerificationResult` this backend emits.
const SOLVER_NAME: &str = "ay-in-process";

/// THE NATIVE LANE'S OWN LOGIC-NAME VOCABULARY, transcribed from the parser it
/// belongs to — `ay_bindings::execute_direct::logic::parse_logic` — and kept as
/// ONE list so no second copy can drift from it.
///
/// WHY THIS EXISTS. The native in-process lane does not take a logic name from
/// SMT-LIB; it takes one from `parse_logic`, which answers
/// `ExecuteError::UnsupportedLogic` for anything outside the rules below.
/// `run_with_policy` turns that error into
/// `VerificationResult::Unknown { reason: "in-process ay execution error: \
/// unsupported logic: …" }` — no verdict, no artifact, for a query ay could
/// otherwise decide. `trust_types::logic_lattice::LOGIC_LATTICE` is a table of
/// what SMT-LIB ATTESTS and deliberately does not know about this parser (see
/// its criterion note), so the narrowing belongs HERE, beside the lane, exactly
/// as `AYProgram::upgrade_logic_for_datatypes` does its own lane-side
/// adjustment two statements later in [`InProcessAyBackend::build_program`].
///
/// HOW IT WAS DERIVED, and why it is not a sample. `parse_logic` accepts a name
/// by FIVE routes, and this list is the union of the four that are LISTS, with
/// the fifth left as the RULE it is:
///
///  1. its own literal arms `ALL` / `ALL_SUPPORTED` and `QF_ABVFP` / `QF_FPLRA`;
///  2. its hardcoded quantified-logic arm (`LIA` … `ALIRA`);
///  3. everything `<ay_dpll::api::Logic as FromStr>::from_str` accepts, which is
///     the arm it falls through to — including the aliases that map two
///     spellings onto one variant (`QF_IDL`, `QF_RDL`, `QF_UFIDL`, `QF_FPBV`,
///     `QF_AFPBV`, `QF_AUFNIA`, `AUFNIA`, `DT`, `DTLIA`, `QF_BOOL`, `BOOL`, …);
///  4. `ay_bindings::execute_direct::logic::SMT_LIB_LOGICS`, a table of ATTESTED
///     SMT-LIB names consulted AFTER `from_str` fails, each mapped onto
///     `Logic::All`;
///  5. **THE RULE:** any name whose spelling `contains("DT")`, which
///     [`native_lane_parses_logic`] applies as a rule and not as a list, so a
///     `*DT*` name added to the lattice tomorrow needs no re-measurement.
///
/// ROUTE 4 IS NEW, and it is why this list grew by NINETEEN names on 2026-09-19.
/// ay `9d2cda9c8727` added `SMT_LIB_LOGICS` for exactly the defect this
/// vocabulary was written to survive: sixteen attested SMT-LIB names —
/// `QF_UFFP`, `FP`, `BVFP`, `QF_ANIA`, `FPLRA`, `ABVFP`, `UFBVFP`,
/// `QF_AUFBVFP`, `QF_BVFPLRA`, `ANIA`, `AUFBVFP`, `UFBVLIA`, `BVFPLRA`,
/// `QF_ABVFPLRA`, `QF_AUFBVNIA`, `ABVFPLRA` — fell through `from_str` into
/// `UnsupportedLogic` and aborted the whole solve. All sixteen are `LOGIC_LATTICE`
/// rows, all sixteen are measured ACCEPTED here now, and the other three the
/// table brought with them (`AX`, `QF_UFSLIA`, `UFIDL`) are attested names that
/// are not lattice rows. Mapping to `ALL` is the SAFE direction: `ALL` admits
/// MORE than the named logic, never less.
///
/// `HORN` is the one name `parse_logic` refuses in an arm of its own (it
/// requires CHC infrastructure), so it is deliberately NOT here even though
/// `AYProgram::horn()` writes it — and it is the one REAL name this lane still
/// refuses, which is why the measurement below probes it beside the fabricated
/// control rather than resting on the control alone.
///
/// MEASURED 2026-09-19 against `first-party/ay` `9d2cda9c8727`, by driving the
/// LINKED program — a native `AYProgram`, `set_logic(NAME)`, a ground `1 != 1`,
/// `execute_incremental` under `trust_types::ay_exec_lock()` — for every name
/// here, every name in `LOGIC_LATTICE`, `HORN`, and a fabricated
/// `QF_NOT_A_LOGIC` control, so the agreement cannot go vacuously green. The
/// result: 101 names accepted (these 89, plus the twelve `*DT*` spellings the
/// rule covers), and exactly TWO refused — `HORN` and the control. EVERY ONE of
/// the 75 `LOGIC_LATTICE` rows is accepted, which is the state
/// `the_native_lane_vocabulary_is_what_ay_actually_parses` pins; see
/// [`native_lane_logic`] for what that does to the guard.
const NATIVE_LANE_LOGIC_VOCABULARY: &[&str] = &[
    // parse_logic's own literal arms.
    "ALL",
    "ALL_SUPPORTED",
    "QF_ABVFP",
    "QF_FPLRA",
    // parse_logic's hardcoded quantified list.
    "LIA",
    "LRA",
    "LIRA",
    "NIA",
    "NRA",
    "NIRA",
    "UF",
    "UFLIA",
    "UFLRA",
    "UFNIA",
    "UFNRA",
    "UFNIRA",
    "UFBV",
    "AUFLIA",
    "AUFLRA",
    "AUFLIRA",
    "AUFNIA",
    "AUFNRA",
    "AUFNIRA",
    "BV",
    "ABV",
    "AUFBV",
    "ALIA",
    "ALRA",
    "ALIRA",
    // `<Logic as FromStr>::from_str`, the fall-through arm, in its own order.
    "QF_LIA",
    "QF_IDL",
    "QF_LRA",
    "QF_RDL",
    "QF_LIRA",
    "QF_UF",
    "QF_UFLIA",
    "QF_UFIDL",
    "QF_UFLRA",
    "QF_AUFLIA",
    "QF_AUFLRA",
    "QF_AUFLIRA",
    "QF_NIA",
    "QF_EIA",
    "QF_NRA",
    "QF_NIRA",
    "QF_BV",
    "QF_UFBV",
    "QF_ABV",
    "QF_AUFBV",
    "QF_UFBVLIA",
    "QF_AUFBVLIA",
    "QF_UFNIA",
    "QF_AUFNIA",
    "QF_UFNRA",
    "QF_AUFNRA",
    "QF_UFNIRA",
    "QF_AUFNIRA",
    "QF_FP",
    "QF_BVFP",
    "QF_FPBV",
    "QF_AFPBV",
    "QF_S",
    "QF_SLIA",
    "QF_SEQ",
    "QF_SEQLIA",
    "QF_AX",
    "QF_ALIA",
    "QF_SNIA",
    "QF_BOOL",
    "BOOL",
    // `SMT_LIB_LOGICS`, the attested-name table ay `9d2cda9c8727` added after
    // the `from_str` arm. Sixteen of these nineteen are the names that used to
    // abort the solve; `AX`, `QF_UFSLIA` and `UFIDL` are attested names the same
    // table brought with them and are not `LOGIC_LATTICE` rows.
    "QF_UFFP",
    "FP",
    "BVFP",
    "QF_ANIA",
    "FPLRA",
    "ABVFP",
    "UFBVFP",
    "QF_AUFBVFP",
    "QF_BVFPLRA",
    "ANIA",
    "AUFBVFP",
    "UFBVLIA",
    "BVFPLRA",
    "QF_ABVFPLRA",
    "QF_AUFBVNIA",
    "ABVFPLRA",
    "AX",
    "QF_UFSLIA",
    "UFIDL",
];

/// Whether the NATIVE in-process lane's own parser accepts the logic name
/// `name` — `parse_logic`'s rules, not a sample of its answers.
///
/// The `contains("DT")` clause is applied as the RULE it is in `parse_logic`,
/// so every `*DT*` spelling (`QF_DT`, `UFDTNIRA`, `QF_UFBVDT`, and whatever a
/// later revision of the lattice adds) is accepted without appearing in
/// [`NATIVE_LANE_LOGIC_VOCABULARY`].
#[must_use]
fn native_lane_parses_logic(name: &str) -> bool {
    name.contains("DT") || NATIVE_LANE_LOGIC_VOCABULARY.contains(&name)
}

/// The `(set-logic …)` name the NATIVE in-process lane must open with for a
/// query whose theory record is `required`.
///
/// THE SAME DECISION `trust_types::logic_lattice::select_logic_name` MAKES,
/// over the SAME table, restricted to the rows this lane's parser accepts: the
/// first row of `LOGIC_LATTICE`, in table order, that admits every required
/// theory with the fewest admitted theories overall AND satisfies
/// [`native_lane_parses_logic`]. `ALL` is a row, admits everything and is
/// accepted, so the answer is always defined; the fallback below is a totality
/// belt for the TCB gate, not a reachable branch.
///
/// # Four properties, each pinned by an exhaustive test over the 2048-set powerset
///
/// * **ACCEPTED.** The result always satisfies [`native_lane_parses_logic`], so
///   `parse_logic` can never answer `UnsupportedLogic` for a name this lane
///   installs — `the_native_lane_never_installs_a_name_its_parser_refuses`.
/// * **ADMISSIBLE.** The result admits `required`, exactly as the unrestricted
///   selector's does, so the native program is never opened with a logic line
///   narrower than its own content —
///   `the_native_lane_name_admits_everything_the_query_uses`.
/// * **A NO-OP WHERE NOTHING WAS BROKEN.** Whenever the unrestricted selector
///   already returns a name this parser accepts, this function returns THAT
///   SAME NAME. So the guard cannot move any verdict that exists today: it only
///   ever replaces a name that would have aborted the solve —
///   `the_guard_is_a_no_op_wherever_the_table_already_names_something_parseable`.
///   (The proof is one line: restricting a first-minimum scan to a subset that
///   contains the unrestricted winner cannot change the winner.)
/// * **AND IT REALLY NARROWS.** Where the vocabulary does NOT contain the
///   unrestricted winner, the answer moves off it to another admitting row —
///   `the_narrowing_is_real_under_a_restricted_vocabulary`. That one is measured
///   against a synthetic vocabulary rather than the live parser, because against
///   the live parser there is nothing left to narrow.
///
/// # THIS GUARD IS CURRENTLY A TOTAL NO-OP, MEASURED 2026-09-19 — AND IT STAYS
///
/// ay `9d2cda9c8727` taught `parse_logic` the sixteen attested names it used to
/// refuse (see [`NATIVE_LANE_LOGIC_VOCABULARY`] route 4). Every one of the 75
/// `LOGIC_LATTICE` rows is now accepted by the linked lane, so the accepted
/// sublattice IS the lattice and this function returns
/// `select_logic_name(required)` for **all 2048** feature sets — measured, over
/// the whole powerset, by
/// `the_guard_is_a_no_op_wherever_the_table_already_names_something_parseable`,
/// which pins the difference count at ZERO and the replacement map at EMPTY.
/// (Before the bump it rescued 76 of the 1024.)
///
/// THAT IS NOT A REASON TO DELETE IT. The narrowing is what keeps this lane
/// honest: `HORN` is still refused in an arm of its own, a row added to the
/// lattice tomorrow need not be a name `parse_logic` knows, and ay narrowing
/// again would silently reinstate the header abort. Kept as a no-op, a
/// narrowing shows up as that test FAILING on a non-zero count rather than as a
/// lost verdict in production.
///
/// A no-op is hard to protect, though, and this one was not protected: with the
/// accepted sublattice equal to the lattice, DELETING the filter passed every
/// test in the crate. That gap is closed at the source — the selection lives in
/// [`select_accepted_logic`], which takes the accepting predicate as an
/// argument, and `the_narrowing_is_real_under_a_restricted_vocabulary` drives it
/// with a deliberately narrower vocabulary and measures both that the answer
/// MOVES off the refused row and that the replacement still ADMITS the query.
/// The narrowing is pinned by a measurement now, not by this paragraph.
///
/// # Why this takes a feature set and not the text lane's NAME
///
/// Taking the name would mean re-deriving the requirement from
/// `logic_admits(name)`, i.e. from what the CHOSEN NAME admits rather than from
/// what the QUERY uses — a strictly larger set, which can only narrow the
/// choice of replacement. It would also couple this lane to rows that exist
/// purely for the text lane: a refused row added to the lattice could push the
/// native lane onto a wider name even though the accepted sublattice had not
/// changed at all. Selecting from the record keeps the native lane's header a
/// function of the ACCEPTED SUBLATTICE ALONE.
///
/// WHAT THAT ARGUMENT COST AND NO LONGER COSTS, re-measured 2026-09-19: the six
/// `*BVLIA`/`*BVFPLRA`/`*BVNIA` rows Lever C added moved 53 feature sets in the
/// text lane and exactly ZERO here, because this lane could not parse them.
/// It can now, so those same 53 sets move HERE TOO — the two lanes agree on
/// every header. The reasoning above is unchanged; only its arithmetic moved.
///
/// # What this guard does NOT fix, re-measured 2026-09-19
///
/// NOTHING THAT IS STILL A HEADER PROBLEM. The second, unrelated gap this
/// section used to describe — the in-process lane could not execute ANY
/// assertion carrying a binder while `:produce-proofs` was on, because ay
/// retained an assertion SOURCE, re-parsed it, and a binder had no parser
/// identity to reconstruct — WAS ALSO FIXED by ay `9d2cda9c8727`, which indexes
/// natively built quantifiers into the same alpha-sharing index the surface
/// elaborator populates. Measured at this pin, no shape aborts there any more
/// and `a_binder_survives_its_own_retained_source` establishes each shape's
/// truth independently before reading the verdict. What stops the remaining
/// shapes is ay's own quantifier INCOMPLETENESS, which is an honest `unknown`,
/// not a lost solve; `no_feature_set_loses_a_verdict_to_the_parser` records
/// which of the ten decide and, for those that do not, the reason MEASURED here
/// rather than the one inherited.
#[must_use]
pub(crate) fn native_lane_logic(required: trust_types::logic_lattice::Theories) -> &'static str {
    select_accepted_logic(required, native_lane_parses_logic)
}

/// [`native_lane_logic`]'s decision with the ACCEPTING PREDICATE as a parameter.
///
/// Split out for one reason, and it is a testing reason with teeth. Against the
/// live parser this selection is a total no-op (every `LOGIC_LATTICE` row is
/// accepted at this pin), so **deleting the `accepts` filter entirely would not
/// fail a single test** — the narrowing that is the whole point of the guard was
/// unobservable. Taking the predicate as an argument lets
/// `the_narrowing_is_real_under_a_restricted_vocabulary` hand this function a
/// DELIBERATELY NARROWER vocabulary and measure that the narrowing happens: with
/// the filter removed that test fails, so the guard's behaviour is pinned by a
/// measurement rather than by the comment above saying it matters.
///
/// `accepts` must accept `ALL`, which is the totality belt; every predicate used
/// in this crate does, and the fallback arm covers a caller that does not.
#[must_use]
fn select_accepted_logic(
    required: trust_types::logic_lattice::Theories,
    accepts: impl Fn(&str) -> bool,
) -> &'static str {
    let mut best: Option<&trust_types::logic_lattice::LogicRow> = None;
    for candidate in trust_types::logic_lattice::LOGIC_LATTICE {
        if !accepts(candidate.name) {
            continue;
        }
        if !required.is_subset_of(candidate.admits) {
            continue;
        }
        let keep_existing = match best {
            Some(current) => current.admits.len() <= candidate.admits.len(),
            None => false,
        };
        if !keep_existing {
            best = Some(candidate);
        }
    }
    match best {
        Some(chosen) => chosen.name,
        // Unreachable: `ALL` is a row, admits every feature set, and is the
        // first arm of `parse_logic`. Answering it rather than panicking keeps
        // this function total for the TCB gate.
        None => "ALL",
    }
}

/// Serializes in-process ay executions. The `ay-dpll` direct-execution path
/// carries shared/non-reentrant state, so concurrent `execute_incremental`
/// calls (e.g. parallel test threads, or a rayon-parallel router dispatch) can
/// race and produce nondeterministic verdicts. Routing the refinement-validation
/// VC class to this backend increased that concurrency and surfaced the latent
/// flakiness; serializing the actual solve keeps every verdict deterministic.
/// The lock is held only across the solve, not VC construction.
///
/// This MUST be `trust_types::ay_exec_lock()` — the ONE process-global point —
/// and not a lock private to this crate. `ay_exec_lock`'s own contract names
/// both required holders ("trust-router's `InProcessAyBackend` and
/// trust-certify's `AyProofBackend`"), because a private mutex here excludes
/// only this crate's solves: a trust-certify solve holding the shared lock and
/// a router solve holding a private one would enter ay's non-reentrant path
/// CONCURRENTLY, which is the nondeterministic-verdict (false-`Certified`)
/// race both comments describe. That is exactly what happened between
/// `9ff8ca4c54` (added the private lock here) and `62e79476cf` (made the
/// frontend parallel by default, introduced the shared lock, and migrated only
/// trust-certify).
fn ay_exec_lock() -> &'static std::sync::Mutex<()> {
    trust_types::ay_exec_lock()
}

/// A hold of [`ay_exec_lock`] taken by [`lock_ay_exec_until`]. Releasing it
/// wakes the solves waiting in [`lock_ay_exec_until`] at once.
struct AyExecHold {
    guard: Option<std::sync::MutexGuard<'static, ()>>,
}

impl Drop for AyExecHold {
    fn drop(&mut self) {
        // Release the lock first, then announce the release: a waiter that
        // reads the announcement before the release would find it held.
        drop(self.guard.take());
        let (released, waiters) = &AY_EXEC_RELEASES;
        let mut generation = released.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        *generation = generation.wrapping_add(1);
        drop(generation);
        waiters.notify_all();
    }
}

/// Release announcements of [`ay_exec_lock`] by this crate's solves: a
/// generation that every [`AyExecHold`] release bumps, and the waiters on it.
static AY_EXEC_RELEASES: (std::sync::Mutex<u64>, std::sync::Condvar) =
    (std::sync::Mutex::new(0), std::sync::Condvar::new());

/// The longest a waiter sleeps between two tries of [`ay_exec_lock`]. A hold
/// this crate releases wakes the waiters at once; this bounds how late one
/// notices a release that announces nothing (trust-certify's solves, a test's
/// raw hold).
const AY_EXEC_RETRY_INTERVAL: std::time::Duration = std::time::Duration::from_millis(20);

/// Wait for [`ay_exec_lock`] until `give_up` (`None`: as long as it takes).
/// Answers the hold and how long the wait took, or, when `give_up` came first,
/// how long it waited. A poisoned lock is recovered, as every holder does: a
/// panic in another solve must not wedge every later obligation.
///
/// ROUTER-LOCK-CLOCK-1: the in-process lane used to wait with a plain
/// `lock()`, which no bound reaches; a holder that never released would have
/// hung every waiter. This wait is bounded and yields the waited time, so the
/// caller can both stop a wait that has gone on too long and keep a wait out
/// of the query's own clock ([`ComponentRetryBudget::note_lock_wait`]).
fn lock_ay_exec_until(
    give_up: Option<Instant>,
) -> Result<(AyExecHold, std::time::Duration), std::time::Duration> {
    use std::sync::TryLockError;
    let asked = Instant::now();
    let (released, waiters) = &AY_EXEC_RELEASES;
    // Held across each try, so a release between a failed try and the sleep
    // below is not missed: the releaser bumps the generation only after the
    // sleep has begun.
    let mut generation = released.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    loop {
        let guard = match ay_exec_lock().try_lock() {
            Ok(guard) => Some(guard),
            Err(TryLockError::Poisoned(poisoned)) => Some(poisoned.into_inner()),
            Err(TryLockError::WouldBlock) => None,
        };
        if let Some(guard) = guard {
            return Ok((AyExecHold { guard: Some(guard) }, asked.elapsed()));
        }
        let now = Instant::now();
        let sleep = match give_up {
            Some(at) if now >= at => return Err(asked.elapsed()),
            Some(at) => (at - now).min(AY_EXEC_RETRY_INTERVAL),
            None => AY_EXEC_RETRY_INTERVAL,
        };
        let seen = *generation;
        generation = waiters
            .wait_timeout_while(generation, sleep, |current| *current == seen)
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .0;
    }
}

/// In-process ay-dpll SMT backend for L0 safety verification conditions.
///
/// Dispatches the VC's violation formula to the linked `ay-dpll` library via
/// [`ay_bindings::execute_direct`], with proof production enabled so an UNSAT
/// result carries a strict-checked [`ay::UnsatProofArtifact`]. The backend only
/// returns [`VerificationResult::Proved`] when that artifact's strict verdict is
/// [`StrictProofVerdict::Verified`] — see the module docs for the full
/// soundness boundary.
#[derive(Debug, Clone)]
pub struct InProcessAyBackend {
    /// Per-query wall-clock BACKSTOP (ay `:timeout`); `0` sends none.
    timeout_ms: u64,
    /// The one effort count's scale (plan §3.2a): each query gets
    /// `min(C, max(1, k · size))` conflicts as ay `:rlimit`, per SAT solve. A
    /// search the count ends stops at the same point on every host; a query
    /// that runs into one of ay's residual clocks first ends on the clock
    /// (`EffortScale`'s docs).
    scale: EffortScale,
    /// A component retry's share of its whole query's effort
    /// ([`QueryEffort::split_by_size`]); `None` for every whole query, whose
    /// effort is its own size's.
    component_effort: Option<QueryEffort>,
}

/// The one assertion this lane makes for a VC violation formula: every user
/// symbol escaped into Trust's ay namespace, the conjunction spine flattened
/// (see `flatten_conjunction_spine` for why). The program
/// ([`InProcessAyBackend::build_program`]), its transcript ([`problem_smt2`])
/// and its effort count's size all read this one formula.
fn asserted_formula(formula: &Formula) -> Formula {
    flatten_conjunction_spine_owned(ay_symbol_namespace::escape_formula_user_symbols(formula))
}

/// Canonical SMT-LIB2 rendering of the exact constraint program this backend
/// asserts for a VC violation formula: one `(set-logic ...)`, one declaration
/// per free variable / predicate symbol (same `collect_free_vars` /
/// `collect_pred_symbols` sets `build_program` declares), one `(assert ...)` of
/// the violation formula, then `(check-sat)`.
///
/// This is the textual transcript of the in-process solve: `build_program`
/// constructs the identical logical program natively (via `formula_to_expr`)
/// from the same formula, so this rendering is a faithful, reproducible record
/// of the query ay decided. Callers that hold a strict-checked ay verdict for
/// `formula` may digest these bytes as the solve's solver-transcript evidence
/// artifact (the same text the Carcara N-version cross-check replays). It is a
/// pure function of the formula — it never invents solver output.
///
/// # THE LOGIC LINE IS THE TEXT LANE'S, AND IT IS THE PRECISE ONE
///
/// This function writes `smt2_export::detect_logic(formula)`: the least name
/// `trust_types::logic_lattice` ATTESTS for the formula's theory record. The
/// native solve opens with `native_lane_logic` of that same record, which is
/// the least such name ay's in-process parser can PARSE, and for ten of the
/// lattice's rows those two differ — see the note at `build_program`'s
/// `set_logic` call for why, and why it leaves this transcript a faithful
/// record of the same question. A consumer replaying this text is not running
/// ay's linked `execute_direct` path and has no such parser; giving it the
/// wider name to keep the two strings equal would trade a precise header, which
/// is the whole evidentiary content of a `(set-logic …)` line, for nothing.
///
/// Trust: every symbol — variables, the datatype family (sorts, constructors,
/// selectors) and the `Pred`/`FnApp` symbols inside `__trust_` — is rendered in
/// Trust's ay namespace (`ay_symbol_namespace`), EXACTLY as `build_program`
/// declares it natively.
/// Both renderers apply the same pure map to the same raw formula, so the
/// transcript keeps naming the symbols ay actually decided — which is what
/// makes the Carcara cross-check (problem text vs. ay's Alethe proof) and the
/// revalidation digest agree.
#[must_use]
pub fn problem_smt2(formula: &Formula) -> String {
    use std::fmt::Write as _;

    let formula = &asserted_formula(formula);
    let body = smt2_export::formula_to_smt2(formula);
    let mut out = String::with_capacity(body.len() + 128);
    let _ = writeln!(out, "(set-logic {})", smt2_export::detect_logic(formula));
    smt2_export::write_declarations(formula, &mut out);
    out.push_str("(assert ");
    out.push_str(&body);
    out.push_str(")\n(check-sat)\n");
    out
}

/// Domain-separation tag for the revalidation problem digest, so a bare
/// `problem_smt2` hash computed elsewhere can never be mistaken for a
/// revalidation receipt's digest.
const SMT_REVALIDATION_DIGEST_DOMAIN: &[u8] = b"trust.smt-revalidation.v1\0";

/// Public revalidation requests are capped at the backend's maintained
/// per-query ceiling. This limits the AY `:timeout` value; it is not a hard
/// wall-clock deadline because formula construction and waiting for the
/// process-global AY execution lock happen outside the solver query.
const MAX_SMT_REVALIDATION_BUDGET_MS: u64 = 90_000;

/// Sealed-authority S1 (SolverReplayAuthority, SMT lane): the outcome of the
/// gate's OWN fresh strict re-solve of a violation `Formula`.
///
/// Zero-authority data cannot construct this: the fields are private, there is
/// no serde, no `Default`, and no public constructor. The ONLY producer is
/// [`revalidate_vc_unsat_strict`], which runs a fresh in-process ay solve and
/// applies the strict solver-proof bar (`StrictProofVerdict::Verified` plus
/// consumer acceptance) to the artifact of THAT solve — never to any carried
/// field. The normal backend's bounded finite-domain fallback is deliberately
/// disabled here: it is sound evidence, but it is not an AY solver-proof
/// replay. Holding a value is proof the check ran in this invocation. It
/// records only the canonical problem bytes and their domain-separated digest
/// for the mint site to bind against the row; it grants nothing on its own
/// (constitution U6: carried data is a reject-only pre-filter, authority flows
/// from the gate's own verdict).
#[derive(Debug, Clone)]
pub struct SmtRevalidationOutcome {
    canonical_problem: String,
    canonical_problem_sha256: String,
    time_ms: u64,
}

impl SmtRevalidationOutcome {
    /// The canonical `.smt2` rendering of the formula the gate re-solved.
    #[must_use]
    pub fn canonical_problem(&self) -> &str {
        &self.canonical_problem
    }

    /// Domain-separated SHA-256 of [`Self::canonical_problem`].
    #[must_use]
    pub fn canonical_problem_sha256(&self) -> &str {
        &self.canonical_problem_sha256
    }

    /// Wall time of the fresh re-solve, in milliseconds.
    #[must_use]
    pub fn time_ms(&self) -> u64 {
        self.time_ms
    }
}

/// Gate-side revalidation of a VC that some producer labeled `Proved`: re-encode
/// `formula` and run a FRESH in-process ay solve with an AY query timeout of
/// `budget_ms`, capped at `MAX_SMT_REVALIDATION_BUDGET_MS`. Zero is invalid
/// and fails closed. The timeout starts after AY's process-global execution
/// lock is acquired, so callers that require a hard end-to-end deadline must
/// enforce it outside this synchronous API.
///
/// Returns `Some` ONLY when that fresh solve independently reaches `Proved`
/// through an UNSAT result carrying a strict-checked proof. Every other outcome
/// returns `None`, which is the status quo (demotion), and is the ONLY behavior for:
/// - `Failed` — the fresh solve found the violation SATISFIABLE, i.e. the
///   producer's `Proved` was wrong; revalidation must NEVER mint here
///   (refutation immunity: authority can only be granted, never used to override
///   a real counterexample);
/// - `Unknown` / timeout / a `budget_ms` too small to finish — no mint.
///
/// Authority flows from THIS solve's verdict, never from any field the caller
/// carried in. The returned outcome is not itself an authority — it records the
/// canonical problem bytes + digest the gate checked, for the mint site to bind
/// to the exact VC row.
///
/// `scale` bounds the re-solve's search by the one count (plan §3.2a, S1 row).
/// `budget_ms` is still a clock that can decide, and the compiler keeps S1's
/// own four-second clock here (`SOLVER_REVALIDATION_BUDGET_MS`); a re-solve it
/// ends, or that any other non-reproducible stop ends, is recorded as that
/// stop. ay's strict-proof discharge inside the re-solve is counted since
/// P4a.1 (ay ffaba97f6), so the 2026-09-30 rule no longer keeps the clock for
/// that lane, nor (ay da447f9a6, P4a) for the eager-persistent arm or the
/// bit-blast solves; demoting it to a backstop is plan T2d, which still waits
/// on ay-sat's wall-capped inprocessing and lookahead in the other SAT solves.
///
/// The re-solve's count is its own query's, like every other solve's: there
/// is no per-function account a re-check could be cut by or charged to.
#[must_use]
pub fn revalidate_vc_unsat_strict(
    formula: &Formula,
    budget_ms: u64,
    scale: EffortScale,
) -> Option<SmtRevalidationOutcome> {
    revalidate_vc_unsat_strict_or_stop(formula, budget_ms, scale).ok()
}

/// [`revalidate_vc_unsat_strict`], saying why a re-solve minted nothing: the
/// stop cause of the fresh solve ([`StopCause::of_result`]), so `solved` for a
/// refuting or otherwise decided re-solve and `wall-backstop` for one its
/// clock ended. The compiler publishes an S1 row its clock withheld as a
/// clock stop rather than as an unexplained miss (determinism plan §3.7).
///
/// A zero `budget_ms` is a re-solve with no time on its clock, so it is
/// `wall-backstop` without a solve.
pub fn revalidate_vc_unsat_strict_or_stop(
    formula: &Formula,
    budget_ms: u64,
    scale: EffortScale,
) -> Result<SmtRevalidationOutcome, StopCause> {
    if budget_ms == 0 {
        return Err(StopCause::WallBackstop);
    }
    let backend = InProcessAyBackend::new()
        .with_timeout(budget_ms.min(MAX_SMT_REVALIDATION_BUDGET_MS))
        .with_effort_scale(scale);
    let start = Instant::now();
    // The gate's OWN fresh, contained solve of the row's own formula. This path
    // suppresses solver diagnostics, catches panics, and disables the normal
    // bounded-finite fallback: only a strict-checked AY proof can mint S1.
    let fresh = backend.run_strict(formula);
    if !matches!(fresh, VerificationResult::Proved { .. }) {
        return Err(StopCause::of_result(&fresh));
    }
    let canonical_problem = problem_smt2(formula);
    let mut hasher = Sha256::new();
    hasher.update(SMT_REVALIDATION_DIGEST_DOMAIN);
    hasher.update(canonical_problem.as_bytes());
    Ok(SmtRevalidationOutcome {
        canonical_problem,
        canonical_problem_sha256: format!("{:x}", hasher.finalize()),
        time_ms: start.elapsed().as_millis() as u64,
    })
}

/// The name of the first datatype `sort` mentions (descending through arrays),
/// for a declaration decline; `sort`'s debug form when it mentions none.
///
/// A decline reason that names the offending DATATYPE is the one a caller can
/// act on. Quoting the whole `Sort` debug blob instead buries the name inside a
/// recursive constructor list, so the shape that actually dangles is not
/// greppable — which is what
/// `by_name_datatype_ref_without_a_definition_is_declined_not_panicked` asserts
/// on.
fn datatype_names(sort: &Sort) -> String {
    match sort {
        // The sort handed to ay is namespaced; the reason names the SOURCE
        // datatype, which is the spelling a caller can act on.
        Sort::Datatype { name, .. } => ay_symbol_namespace::unescape_datatype_sort(name),
        Sort::Array(idx, elem) => match (idx.contains_datatype(), elem.contains_datatype()) {
            (true, _) => datatype_names(idx),
            (_, true) => datatype_names(elem),
            _ => format!("{sort:?}"),
        },
        _ => format!("{sort:?}"),
    }
}

impl InProcessAyBackend {
    /// Create a new in-process ay backend.
    #[must_use]
    pub fn new() -> Self {
        Self { timeout_ms: 90_000, scale: EffortScale::BUILTIN, component_effort: None }
    }

    /// Set the per-obligation wall-clock BACKSTOP. Zero sends no ay
    /// `:timeout`; the effort count still bounds the search.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Set the one effort count's scale `k`.
    #[must_use]
    pub fn with_effort_scale(mut self, scale: EffortScale) -> Self {
        self.scale = scale;
        self
    }

    /// The effort scale in force.
    #[must_use]
    pub fn effort_scale(&self) -> EffortScale {
        self.scale
    }

    /// The effort of the query this backend asserts for `formula`: its own
    /// size's ([`EffortScale::for_query`] over the one assertion
    /// [`Self::build_program`] makes), or a component retry's share.
    fn query_effort(&self, asserted: &Formula) -> QueryEffort {
        self.component_effort.unwrap_or_else(|| self.scale.for_query(&[asserted]))
    }

    /// The size and effort count this backend gives the query it asserts for
    /// the VC violation formula `formula`: the numbers the effort calibration
    /// (`crates/trust-vcgen/tests/effort_calibration.rs`) records per query.
    #[must_use]
    pub fn query_effort_for(&self, formula: &Formula) -> QueryEffort {
        self.query_effort(&asserted_formula(formula))
    }

    /// Build an [`AYProgram`] for the VC's violation formula with proof
    /// production enabled and every free variable declared.
    ///
    /// Trust: every VARIABLE symbol is first mapped into Trust's ay namespace
    /// (`ay_symbol_namespace`). VC variable names are raw Rust identifiers from
    /// MIR `var_debug_info`, and ay REFUSES to declare one that spells a builtin
    /// theory operator (`fp`, `default`, `select`, …) — a refusal it raises by
    /// panicking inside `declare_const`, i.e. a compiler ICE. The map is an
    /// injective relabeling applied to binders and occurrences alike, so the
    /// program ay decides is alpha-equivalent to the VC: it can neither create
    /// nor destroy a model. `problem_smt2` applies the same map, so the textual
    /// transcript names the same symbols. The same map covers the datatype
    /// family — sort, constructor and selector names are Rust type, variant and
    /// field names, just as unconstrained — and qualifies each member by its
    /// datatype, because SMT-LIB constructors and selectors are global symbols
    /// while Rust member names are only unique per type/variant (TRUST-04/05).
    ///
    /// Fails closed (`Err`, the reason ay or the bridge gave) when the formula's
    /// datatype content cannot be registered as ONE definition per name: two
    /// different full definitions of one datatype, a declaration ay refuses,
    /// or a constant whose sort carries a by-name datatype reference with no
    /// definition anywhere in the formula. The caller declines the obligation
    /// (`Unknown`) — never a stub declaration, never a panic.
    ///
    /// **KNOWN GAP (measured, deliberately not plumbed here).** The definition
    /// table is collected from the FORMULA alone. A VC whose datatype sorts are
    /// spelled by-name in every position — the shape `VerifiableBody` produces
    /// when the full definitions live only in its `datatype_defs` side table
    /// (`trust_types::model::VerifiableBody::datatype_defs`) — therefore reaches
    /// `sort_to_ay_in` with an empty table, lowers to a dangling
    /// `AYSort::datatype_ref`, and is DECLINED by `try_declare_const`. The
    /// lowering half of the fix already exists and is already used above
    /// (`formula_to_expr_with_datatype_defs` / `sort_to_ay_in` both take the
    /// table); the ONLY missing piece is transport, and it is not a small one:
    ///
    /// * [`VerificationCondition`] (trust-types `formula/vc.rs`) carries `kind`,
    ///   `function`, `location`, `formula`, `contract_metadata` and
    ///   `obligation` — no body, and no handle that reaches one. `verify` gets
    ///   nothing else, so the table cannot be recovered at this seam.
    /// * Adding a `datatype_defs` field to `VerificationCondition` is a WIDE
    ///   API change: `git grep -c "VerificationCondition {"` counts 1067
    ///   struct-literal sites across `crates/` and `first-party/`, every one of
    ///   which a new field breaks (a struct literal must name every field;
    ///   `#[serde(default)]` buys wire compatibility, not source
    ///   compatibility). `SerializableVc::from_vc`/`into_vc` and the proof
    ///   certificate/cache fixtures would move with it.
    /// * `ContractMetadata` cannot carry it: it is a `Copy` bitset-shaped
    ///   struct (`vc.contract_metadata` is copied, not cloned), and a
    ///   `BTreeMap<String, Sort>` is not `Copy`.
    ///
    /// EXACT PLAN, when that change is worth its blast radius:
    /// 1. Give `DatatypeDefs` `Serialize`/`Deserialize`/`PartialEq` (today it
    ///    derives only `Debug, Default, Clone`; its one field is a
    ///    `BTreeMap<String, Sort>`, and `Sort` already round-trips), then add
    ///    `#[serde(default)] pub datatype_defs: trust_types::ay_bridge::DatatypeDefs`
    ///    to `VerificationCondition` and to `SerializableVc`, threading it
    ///    through `from_vc`/`into_vc` (both already enumerate every field), and
    ///    mechanically add `datatype_defs: Default::default()` at the 1067
    ///    literal sites — the same shape the `VerifiableBody` field addition
    ///    already took.
    /// 2. In `trust-vcgen`, populate it from the body being lowered
    ///    (`body.datatype_defs.clone()`) at VC construction, so the table
    ///    travels with the obligation rather than being re-derived.
    /// 3. Change `build_program` (and `problem_smt2`, which must stay
    ///    byte-equivalent) to take `&DatatypeDefs` as a seed and start from
    ///    `defs = seed.clone(); defs.extend_from_formula(formula)?` instead of
    ///    `DatatypeDefs::collect(formula)?`. `extend_from_formula` already
    ///    returns `DatatypeConflict` when the seed and the formula disagree, so
    ///    the fail-closed one-definition-per-name rule is preserved for free
    ///    and a forged seed cannot silently replace a definition the formula
    ///    itself carries.
    /// 4. Thread the seed from `verify(&vc)` -> `run` -> `run_with_policy` ->
    ///    `build_program`; `run(&formula)` keeps an empty-seed wrapper so the
    ///    formula-only callers and tests are unchanged.
    ///
    /// SOUNDNESS of the plan: a seed only ever ADDS declarations, and declaring
    /// a datatype asserts no fact (see the note below), so this can only turn a
    /// decline into an honest verdict — it can never manufacture a PROVE.
    fn build_program(&self, formula: &Formula) -> Result<AYProgram, AyBridgeError> {
        // Kept in lockstep with `problem_smt2`: the same asserted formula, so
        // the transcript and the executed program stay byte-equivalent.
        self.build_program_from_asserted(&asserted_formula(formula), true, true)
    }

    fn build_program_from_asserted(
        &self,
        formula: &Formula,
        may_have_datatype: bool,
        may_have_uf: bool,
    ) -> Result<AYProgram, AyBridgeError> {
        let mut program = AYProgram::new();

        // Enable proof production. Without this option the executor produces no
        // proof artifact and `unsat_proof` is `None`, which under our soundness
        // rule degrades any UNSAT to `Unknown`. Mirrors the proof-witness path
        // exercised in ay-bindings' execute_direct tests.
        program.add_constraint(Constraint::set_option(":produce-proofs", "true"));

        // Bound every in-process check-sat with a per-obligation wall-clock
        // deadline. Without it a hard bit-vector VC (e.g. FxHash-style
        // wrapping_mul/xor/rotate over u32/u64) bit-blasts to a SAT instance
        // that runs UNBOUNDED: the solve never reaches a fixpoint, the
        // PersistentBvCache repeatedly hits its cap and full-clears (re-blast
        // thrash) and the clause trace overruns its budget, so the obligation
        // never returns a verdict and the whole `check` run is killed.
        //
        // `(set-option :timeout <ms>)` is honored by ay's executor as a real
        // per-check-sat deadline polled inside the CDCL/theory loops, which
        // degrades a non-converging solve to UNKNOWN. That is SOUND here: this
        // backend only emits `Proved` on a strict-checked UNSAT proof, so an
        // Unknown (timeout) outcome can never be reported as Proved.
        //
        if self.timeout_ms > 0 {
            // A narrower program-level timeout appended after the execution
            // lock takes precedence when the shared deadline has less left.
            program.set_option(":timeout", self.timeout_ms.to_string());
        }
        // The deterministic bound (plan §3.2a): this query's one effort count,
        // `min(C, max(1, k · size))` over the one assertion below. ay stops
        // each SAT solve at that conflict count on every host and answers
        // `unknown (resourceout)`. The `:timeout` above is the backstop for a
        // phase that stops counting; a solve it ends is `wall-backstop`.
        let (name, value) = self.query_effort(formula).smt2_option();
        program.add_constraint(Constraint::set_option(name, &value));

        // Pick the SMT logic from the formula's theory features — the SAME
        // record `problem_smt2`'s `detect_logic` reads, narrowed to the names
        // THIS lane's parser accepts (see [`native_lane_logic`]).
        //
        // THE TWO LANES MAY WRITE DIFFERENT NAMES HERE, AND THAT IS THE POINT.
        // `problem_smt2` writes the least ATTESTED name admitting the record,
        // because the transcript is read by replayers with no such parser and a
        // precise header is what makes it evidence. This lane writes the least
        // name admitting the record that `ay_bindings::execute_direct::logic::
        // parse_logic` can parse, because a name it cannot parse is
        // `ExecuteError::UnsupportedLogic` — which `run_with_policy` turns into
        // `Unknown`, losing the verdict AND the artifact for a query ay could
        // decide. Ten of the lattice's rows were in exactly that position.
        //
        // THE TRANSCRIPT IS STILL A FAITHFUL RECORD OF THE QUESTION. Both names
        // ADMIT the query (that is `native_lane_logic`'s admissibility
        // property, pinned exhaustively), and an SMT-LIB logic restricts which
        // symbols a script may MENTION — it does not change the models of a
        // formula that is well-formed under both. So the program this lane
        // solves and the transcript `problem_smt2` renders pose the same
        // question, which is what the revalidation digest and the Carcara
        // cross-check bind to. The guard also only ever fires where the solve
        // would otherwise have been ABORTED, so it cannot move an artifact that
        // exists today; it can only produce one where there was none.
        program.set_logic(native_lane_logic(smt2_export::formula_features(formula)));

        // Lever A: register every algebraic datatype BEFORE declaring consts of
        // those sorts, so ay applies the datatype theory (constructor/selector/
        // tester axioms AND the acyclicity of the term algebra).
        //
        // ONE definition table for the whole query. `DatatypeDefs::collect`
        // walks the same sort positions `visit_datatype_bearing_sorts` does (a
        // ground `Ctor`/`Sel` term carries a datatype sort no `Var` mentions,
        // so keying off free vars alone would assert a term over a datatype
        // this program never declared) and refuses two different full
        // definitions under one name. The declarations, the constants' sorts
        // and the asserted terms are all lowered from that one table
        // (`sort_to_ay_in` / `formula_to_expr_with_datatype_defs`): a by-name
        // back-edge (`App (f Expr)`) becomes ay's `datatype_ref` inside its own
        // declaration — the genuinely inductive
        // `(declare-datatype Expr ((App (f Expr) (x Expr)) …))` the text lane
        // emits — and a by-name reference in a term position is widened to the
        // table's full definition, so `AYProgram::try_declare_datatype` /
        // `try_declare_const` authenticate every descriptor against the one
        // registered under its name. A reference with no definition anywhere
        // is dangling and ay refuses it: the query is DECLINED, never declared
        // over an opaque stand-in that would silently drop the datatype theory.
        //
        // SOUNDNESS: declaring a datatype asserts NO fact and cannot make the
        // context vacuously UNSAT (a fresh datatype-sorted const is SAT), so
        // registration can only let obligations report their honest outcome.
        let defs = if may_have_datatype {
            let defs = DatatypeDefs::collect(formula)?;
            // Dependency order: a datatype follows every OTHER datatype its fields
            // name, which is what ay's one-at-a-time native declaration needs.
            for dt in defs.to_ay_declarations() {
                // The reason names the SOURCE datatype (`dt.name` is its ay image).
                let name = ay_symbol_namespace::unescape_datatype_sort(&dt.name);
                program.try_declare_datatype(dt).map_err(|source| AyBridgeError::Datatype {
                    node: "declaration",
                    datatype: name.clone(),
                    member: name,
                    source,
                })?;
            }
            program.upgrade_logic_for_datatypes();
            defs
        } else {
            DatatypeDefs::default()
        };

        let free_vars = smt2_export::collect_free_vars(formula);

        // Declare each free (non-quantifier-bound) variable exactly once before
        // the assertion, mirroring how smt2_export emits declarations. The sort
        // is lowered from the same table the declarations came from.
        for (name, sort) in free_vars {
            let ay_sort = sort_to_ay_in(&sort, &defs, &mut Vec::new());
            program.try_declare_const(&name, ay_sort).map_err(|source| {
                // Name the offending DATATYPE, not the whole `Sort` debug blob:
                // the dangling by-name reference is what the caller has to act
                // on, and a decline reason that quotes it is greppable.
                AyBridgeError::Datatype {
                    node: "variable",
                    datatype: datatype_names(&sort),
                    member: name.clone(),
                    source,
                }
            })?;
        }

        // Declare every UNINTERPRETED SYMBOL the formula applies: the `Pred`
        // predicates (result `Bool`) and the `FnApp` function symbols (result
        // sort carried on the node). The text SMT exporter emits the matching
        // declarations from this same collector; the direct AY bridge requires
        // them too, because ay's executor answers an application of an
        // undeclared symbol with `ExprTranslation("undeclared function …")` and
        // an application at a disagreeing signature inside the PANICKING
        // `uf::apply`. `uninterpreted_signature_conflict` has already declined
        // any formula whose applications of one name disagree, so declaring the
        // first application's signature declares them all.
        //
        // `FnApp` was missing here as well as in the bridge: trust-vcgen's
        // Skolem terms and the `model = reference` postconditions of the
        // recursive-datatype lanes name a second function symbol, and without
        // this loop even a correctly lowered application would reference an
        // undeclared function. The argument sorts come from the same table; a
        // dangling reference in one is refused where the argument TERM is
        // lowered (the bridge's fail-closed boundary, contained by
        // `run_with_policy`).
        //
        // A NULLARY symbol (a `Pred` or `FnApp` with no arguments) is declared
        // as a CONSTANT, because that is what the bridge lowers it to: a
        // zero-argument application executes as a different ay term than the
        // constant ay's elaborator reads its bare name as, and the
        // retained-source guard refused every assertion carrying one. See the
        // nullary arm of `trust_types::ay_bridge::formula_to_expr`. The two
        // halves are one decision: a `declare_fun(c, [], S)` beside a `Var`
        // lowering leaves `c` undeclared as a constant, and a `declare_const`
        // beside an application leaves it undeclared as a function.
        if may_have_uf {
            for (name, (arg_sorts, result_sort)) in uninterpreted_symbol_signatures(formula) {
                let ay_result = sort_to_ay_in(&result_sort, &defs, &mut Vec::new());
                if arg_sorts.is_empty() {
                    program.try_declare_const(&name, ay_result).map_err(|source| {
                        AyBridgeError::Datatype {
                            node: "constant symbol",
                            datatype: datatype_names(&result_sort),
                            member: name.clone(),
                            source,
                        }
                    })?;
                    continue;
                }
                let ay_arg_sorts = arg_sorts
                    .iter()
                    .map(|sort| sort_to_ay_in(sort, &defs, &mut Vec::new()))
                    .collect();
                program.declare_fun(name, ay_arg_sorts, ay_result);
            }
        }

        // Assert the violation formula and check satisfiability.
        // FALLIBLE: a shape the bridge cannot lower faithfully (a malformed
        // datatype term, a dangling by-name reference, a non-literal rounding
        // mode, an unlowerable sort, a future contract variant) comes back as a
        // named error and DECLINES the obligation. The gates above establish
        // each of these first, with their own diagnostics, so this is the
        // backstop — but it is a fail-closed `Err`, not a panic contained by
        // `run_with_policy`'s `catch_unwind`.
        program.assert(formula_to_expr_with_datatype_defs(formula, &defs)?);
        program.check_sat();

        Ok(program)
    }

    /// Map an UNSAT outcome's proof artifact to `Proved` only when it is
    /// strict-Verified; otherwise `Unknown`. This is the load-bearing soundness
    /// gate. Takes the artifact directly (rather than the `#[non_exhaustive]`
    /// `CheckSatOutcome`) so the `None` path is unit-testable.
    ///
    /// `formula` is the violation formula that was asserted to ay; it is used
    /// only under the `carcara-crosscheck` feature to rebuild the problem .smt2
    /// for the N-version Carcara cross-check (see [`Self::apply_carcara_gate`]).
    /// On default and single-feature builds it is unused.
    fn unsat_to_result(
        unsat_proof: Option<&UnsatProofArtifact>,
        time_ms: u64,
        formula: &Formula,
    ) -> VerificationResult {
        match unsat_proof {
            Some(artifact) => match &artifact.strict_verdict {
                StrictProofVerdict::Verified(_) => {
                    // Defense in depth: the consumer-facing acceptance check must
                    // also pass before we hand out a trust seal.
                    if artifact.accept_for_consumer(ProofAcceptanceMode::Strict).is_ok() {
                        let proved = VerificationResult::Proved {
                            solver: SOLVER_NAME.into(),
                            time_ms,
                            // The UNSAT proof passed ay's strict proof checker
                            // (StrictProofVerdict::Verified + the consumer-facing
                            // accept gate), so this earns SmtBacked assurance --
                            // strictly above the Unchecked subprocess path. It is
                            // deliberately NOT Certified: ay's checker is trusted
                            // code (and has had meta-soundness bugs), so a kernel
                            // reconstruction is required for true-proof Certified.
                            strength: ProofStrength::smt_unsat_strict_checked(),
                            proof_certificate: artifact.lrat_certificate.clone(),
                            solver_warnings: None,
                            native_proof_envelope: None,
                        };

                        // Certification transport gate (D.9).  On an `ay-certify`
                        // build this promotes to `Certified` for the fragments
                        // Clean can reconstruct — but only after the kernel has
                        // certified the refutation from this VC alone AND the
                        // packaged envelope has been replayed back to the same
                        // verdict.  ay's LRAT bytes are carried through unchanged;
                        // the kernel payload rides in the typed
                        // `native_proof_envelope` slot beside them.  Every other
                        // build, and every declining step, keeps the honest
                        // strict-checked SmtBacked result.
                        let proved = Self::promote_to_certified(proved, formula, time_ms);

                        // Track D increment 2: N-version cross-check. ay accepted
                        // this UNSAT proof under its OWN strict checker; before we
                        // surface it as Proved, re-check the SAME Alethe proof with
                        // Carcara, an independently implemented Alethe checker. The
                        // gate is MONOTONE: it may only downgrade Proved -> Unknown
                        // (on Carcara Reject), never strengthen. Carcara Unavailable
                        // is NOT disagreement and keeps ay's strict-checked Proved,
                        // so an absent Carcara never introduces a false-FAIL. On
                        // builds without the cross-check feature this is an identity.
                        Self::carcara_cross_check_proved(proved, formula, artifact, time_ms)
                    } else {
                        strict_proof_withheld(
                            time_ms,
                            "UNSAT proof artifact rejected at strict consumer boundary",
                        )
                    }
                }
                StrictProofVerdict::Rejected(reason) => strict_proof_withheld(
                    time_ms,
                    &format!("UNSAT but strict proof verdict rejected: {reason}"),
                ),
                // A stop ended the strict check before it decided: no verdict,
                // and the row says which stop (P4a.1).
                StrictProofVerdict::Stopped(stop) => strict_proof_stopped(time_ms, *stop),
                // `StrictProofVerdict` is #[non_exhaustive]. Any future verdict
                // that is not `Verified(_)` must fail closed to Unknown — never
                // a trust seal.
                _ => strict_proof_withheld(
                    time_ms,
                    "UNSAT but strict proof verdict was not Verified",
                ),
            },
            None => strict_proof_withheld(
                time_ms,
                "UNSAT but no strict-checked proof artifact was produced",
            ),
        }
    }

    /// Carcara N-version cross-check dispatcher (Track D increment 2).
    ///
    /// Identity on builds WITHOUT the `carcara-crosscheck` feature: the input
    /// `proved` (already strict-checked by ay) is returned unchanged. This arm
    /// keeps the default and single-feature builds byte-for-byte identical to
    /// the pre-increment behaviour.
    #[cfg(not(all(feature = "ay-backend", feature = "carcara-crosscheck")))]
    fn carcara_cross_check_proved(
        proved: VerificationResult,
        _formula: &Formula,
        _artifact: &UnsatProofArtifact,
        _time_ms: u64,
    ) -> VerificationResult {
        proved
    }

    /// Certification transport gate.  Builds without the experimental Clean
    /// reconstruction feature keep the strict-checked `SmtBacked` verdict.
    #[cfg(not(feature = "ay-certify"))]
    fn promote_to_certified(
        proved: VerificationResult,
        _formula: &Formula,
        _time_ms: u64,
    ) -> VerificationResult {
        proved
    }

    /// Fail-closed certification transport gate for builds with experimental
    /// Clean reconstruction enabled (D.9).
    ///
    /// This gate was an identity for as long as the result carrier had only the
    /// single opaque `proof_certificate` byte vector — already occupied by ay's
    /// LRAT bytes. Changing `strength` alone would have dropped the Clean
    /// payload on the floor and advertised replayable kernel evidence that no
    /// consumer could replay. `Proved` now carries a second, typed slot
    /// (`native_proof_envelope`), so the payload has somewhere honest to go and
    /// the LRAT bytes are preserved rather than displaced.
    ///
    /// Promotion requires ALL of:
    ///
    /// 1. the VC is the recognized fragment and the Clean kernel certifies its
    ///    refutation from the VC ALONE (`certify_lia_violation_formula` rebuilds
    ///    the context from the recognized bounds — nothing is taken on trust);
    /// 2. the payload packages into a structurally accepted envelope;
    /// 3. **the envelope replays** — we re-derive the context from the formula a
    ///    second time and watch the kernel re-accept the very bytes we are about
    ///    to ship. We refuse to stamp `Certified` on evidence that does not
    ///    reproduce the verdict, so an envelope that would fail at a downstream
    ///    consumer never leaves here labelled as proof.
    ///
    /// Any step declining returns the honest strict-checked `SmtBacked` verdict
    /// unchanged. Non-fragment formulas exit at the cheap syntactic recognizer,
    /// so the kernel work is confined to the class that can actually certify.
    #[cfg(feature = "ay-certify")]
    fn promote_to_certified(
        proved: VerificationResult,
        formula: &Formula,
        _time_ms: u64,
    ) -> VerificationResult {
        if !matches!(proved, VerificationResult::Proved { .. }) {
            return proved;
        }
        // (1) Certify from the VC itself.
        let Ok(Some(crate::ay_certify::CertifyOutcome::Certified(payload))) =
            crate::ay_certify::certify_lia_violation_formula(formula)
        else {
            return proved;
        };
        // (2) Package into the typed, zero-authority carrier.
        let Some(envelope) = crate::ay_certify::certified_envelope_for(formula, &payload) else {
            return proved;
        };
        // (3) Independently replay what we are about to ship.
        if !crate::ay_certify::replay_certified_envelope(formula, &envelope).is_replayed() {
            return proved;
        }
        // (4) Promote, PRESERVING ay's LRAT certificate and every other field.
        match proved {
            VerificationResult::Proved {
                solver,
                time_ms,
                proof_certificate,
                solver_warnings,
                ..
            } => VerificationResult::Proved {
                solver,
                time_ms,
                strength: ProofStrength::smt_unsat_certified(),
                proof_certificate,
                solver_warnings,
                native_proof_envelope: Some(envelope),
            },
            other => other,
        }
    }

    /// Carcara N-version cross-check dispatcher (Track D increment 2).
    ///
    /// With the `carcara-crosscheck` feature on: rebuild the problem .smt2 from
    /// the violation formula, hand it plus the artifact's Alethe text and
    /// residual trust-rule count to [`carcara_cross_check`], then apply the
    /// MONOTONE [`Self::apply_carcara_gate`] (which may only downgrade
    /// `Proved -> Unknown`).
    ///
    /// [`carcara_cross_check`]: crate::carcara_cross_check::carcara_cross_check
    #[cfg(all(feature = "ay-backend", feature = "carcara-crosscheck"))]
    fn carcara_cross_check_proved(
        proved: VerificationResult,
        formula: &Formula,
        artifact: &UnsatProofArtifact,
        time_ms: u64,
    ) -> VerificationResult {
        let problem_smt2 = Self::build_problem_smt2(formula);
        // D7 (2026-09-22): ay renders any strict-accepted proof and discloses
        // whether pinned Carcara can parse it. This consumer CLAIMS an external
        // check, so an unsupported surface is refused by name. `is_supported()`
        // rather than a match: `CarcaraSurface` is `#[non_exhaustive]`, and a
        // variant this crate does not know is unsupported, never checked.
        let unsupported_surface = (!artifact.carcara_surface.is_supported()).then(|| {
            artifact
                .carcara_surface
                .unsupported_reason()
                .unwrap_or("carcara_surface is not `supported`")
        });
        let cross = crate::carcara_cross_check::carcara_cross_check(
            &problem_smt2,
            &artifact.alethe,
            artifact.quality.trust_count,
            unsupported_surface,
        );
        Self::apply_carcara_gate(proved, cross, time_ms)
    }

    /// Rebuild the SMT-LIB2 problem text (set-logic + declarations + the
    /// asserted violation formula + check-sat) that was handed to ay, in the
    /// exact shape Carcara needs as the second input to its cross-check.
    ///
    /// This mirrors the assembly the subprocess SMT path uses
    /// (`incremental_ay`/`smt2_export`): one `(set-logic ...)`, one
    /// `(declare-fun ...)` per free var + predicate symbol, one `(assert ...)`
    /// of the violation formula, then `(check-sat)`.
    #[cfg(all(feature = "ay-backend", feature = "carcara-crosscheck"))]
    fn build_problem_smt2(formula: &Formula) -> String {
        problem_smt2(formula)
    }

    /// Pure, side-effect-free decision for the Carcara N-version cross-check.
    ///
    /// Track D increment 2 soundness contract — the gate is MONOTONE, it may
    /// only downgrade `Proved -> Unknown`, never strengthen:
    /// * [`CrossCheck::Reject`] -> DOWNGRADE to `Unknown` (fail-closed): ay and
    ///   Carcara disagree, or the proof carried an unreconstructed trust rule.
    /// * [`CrossCheck::SurfaceUnsupported`] -> DOWNGRADE to `Unknown`, naming
    ///   ay's disclosed `carcara_surface=unsupported(reason)` (D7): the external
    ///   check this gate claims cannot run on the document.
    /// * [`CrossCheck::Accept`] -> keep the input `proved` (both checkers agree).
    /// * [`CrossCheck::Unavailable`] -> keep the input `proved`: Carcara is not
    ///   present / there was no proof text. Unavailable is NOT disagreement, so
    ///   it must never introduce a false-FAIL — ay's own strict check (already
    ///   passed before we reach here) still gates the Proved.
    ///
    /// Factored out (taking the already-built `proved` result and the cross-check
    /// verdict) so the decision logic is unit-testable WITHOUT driving a live
    /// solver or a live Carcara binary.
    #[cfg(all(feature = "ay-backend", feature = "carcara-crosscheck"))]
    fn apply_carcara_gate(
        proved: VerificationResult,
        cross: crate::carcara_cross_check::CrossCheck,
        time_ms: u64,
    ) -> VerificationResult {
        use crate::carcara_cross_check::CrossCheck;
        match cross {
            // Disagreement (or an unreconstructed trust rule): fail closed.
            CrossCheck::Reject => strict_proof_withheld(
                time_ms,
                "carcara N-version cross-check rejected the ay UNSAT proof (or it \
                 contained unreconstructed trust rules); downgraded fail-closed",
            ),
            // D7: ay disclosed a surface pinned Carcara cannot parse. The
            // external check this gate claims does not exist for the document,
            // so fail closed and NAME the cause. (Pre-D7 the same proof reached
            // Carcara, failed to parse, and was a `Reject` — same class.)
            CrossCheck::SurfaceUnsupported { reason } => strict_proof_withheld(
                time_ms,
                &format!(
                    "carcara N-version cross-check refused: ay disclosed \
                     carcara_surface=unsupported({reason}); pinned Carcara cannot parse this \
                     proof, so no external re-check exists — downgraded fail-closed"
                ),
            ),
            // Both independent checkers agree: keep the strict-checked Proved.
            CrossCheck::Accept => proved,
            // Carcara not present / no proof text: not disagreement. Keep ay's
            // strict-checked Proved — never downgrade on Unavailable.
            CrossCheck::Unavailable => proved,
        }
    }

    /// Run the VC's violation formula in-process and classify the outcome.
    ///
    /// The whole solve, including the strict proof check, runs under
    /// [`with_ay_diagnostics_policy`]: ay's solver-internal tracing
    /// diagnostics are suppressed by default so they never leak onto the
    /// embedding compiler's stderr; `TRUST_AY_LOG` opts back in.
    fn run(&self, formula: &Formula) -> VerificationResult {
        self.run_with_policy(formula, true)
    }

    /// Run the fresh-revalidation lane under the same containment boundary as
    /// the normal backend while refusing the non-solver bounded-finite proof
    /// fallback.
    fn run_strict(&self, formula: &Formula) -> VerificationResult {
        self.run_with_policy(formula, false)
    }

    /// One component's nominal timeout, floored at 1 ms for bounded callers.
    /// The proved upper bound is per component; it does not bound their sum.
    /// `ComponentRetryBudget` caps the retry against one absolute query deadline.
    #[cfg(test)]
    fn retry_component_timeout_ms(total_ms: u64, components: usize) -> u64 {
        crate::disjoint_components::component_timeout_ms(total_ms, components)
    }

    /// Retry a whole-query `Unknown` as a component-wise REFUTATION. Yields
    /// [`ComponentRetry::Refuted`] only when EVERY variable-disjoint component
    /// is independently refuted with a model. A component ay's search decided
    /// UNSAT ends the retry on that verdict; an undecided component ends it
    /// with that component's stop cause, which the caller folds into its
    /// original verdict ([`crate::ay_stop::after_undecided_retry`]). See
    /// [`crate::disjoint_components`] for the soundness argument.
    fn try_disjoint_component_refutation(
        &self,
        formula: &Formula,
        allow_bounded_finite: bool,
        elapsed_ms: u64,
        budget: &ComponentRetryBudget,
    ) -> ComponentRetry {
        let Some(components) = disjoint_conjunctive_components(formula) else {
            return ComponentRetry::NotApplicable;
        };
        // Keep the original query's budget, including the work already spent
        // on it. A floored 1 ms split alone does not bound the aggregate retry
        // time. Each component's solve narrows the ambient deadline to that
        // budget itself, and rechecks it after waiting for AY's execution lock,
        // a wait the budget does not charge (`ComponentRetryBudget`).
        // The effort count remains split by component size, independently of
        // the wall backstop. A clock refusal is always reported as such.
        let whole = self.query_effort(&asserted_formula(formula));
        let sizes: Vec<u64> = components
            .iter()
            .map(|component| trust_types::determinism::query_size(&[&asserted_formula(component)]))
            .collect();
        let shares = whole.split_by_size(&sizes);
        let mut assignments: Vec<(String, trust_types::CounterexampleValue)> = Vec::new();
        let mut time_ms = elapsed_ms;
        for (component, share) in components.iter().zip(shares) {
            let Some(timeout_ms) = budget.component_timeout_at(components.len(), Instant::now())
            else {
                return ComponentRetry::Undecided(StopCause::WallBackstop);
            };
            let bounded = Self { timeout_ms, scale: self.scale, component_effort: Some(share) };
            let InProcessSolve { result, decided_unsat } =
                bounded.solve_and_classify_in(component, allow_bounded_finite, budget);
            // A component ay's search decided UNSAT makes the WHOLE formula
            // UNSAT (its clauses are a subset of the whole's), whatever
            // certification then made of it: proved, refused, or a strict check
            // this component's 1/n of the clock cancelled. The retry ends there
            // on that verdict, as the whole-query gate in `run_with_policy`
            // does, so that clock never chooses between them for the row. A
            // deadline ay reports as `timeout` names no decided search, and
            // stays the component's clock stop (`wall-backstop`).
            if decided_unsat {
                return ComponentRetry::Undecided(StopCause::Solved);
            }
            match result {
                VerificationResult::Failed { counterexample, time_ms: t, .. } => {
                    time_ms = time_ms.saturating_add(t);
                    // A refuted component MUST carry its witness: the composed
                    // counterexample is the union of the component models, and a
                    // missing part would hand back an incomplete witness. The
                    // component was decided, so the retry stops on a verdict.
                    let Some(counterexample) = counterexample else {
                        return ComponentRetry::Undecided(StopCause::Solved);
                    };
                    assignments.extend(counterexample.assignments);
                }
                // An undecided component, whose stop cause the caller must still
                // see: a component the clock ended could have been refuted on an
                // idle host. (A decided UNSAT ended the retry above; this lane
                // mints no trust seal from it, see the doc above.)
                other => return ComponentRetry::Undecided(StopCause::of_result(&other)),
            }
        }
        // Deterministic order for a stable, human-readable witness. Disjointness
        // means the names cannot collide, so sorting by NAME is a total order on
        // this list (the values carry no `Ord`).
        assignments.sort_by(|a, b| a.0.cmp(&b.0));
        ComponentRetry::Refuted(VerificationResult::Failed {
            solver: SOLVER_NAME.into(),
            time_ms,
            counterexample: Some(trust_types::Counterexample { assignments, trace: None }),
        })
    }

    fn run_with_policy(&self, formula: &Formula, allow_bounded_finite: bool) -> VerificationResult {
        // One budget for the query's whole work, its component retry included
        // (RETRY-QUERY-DEADLINE-1). Each solve narrows the ambient deadline to
        // it for its own work, before and after waiting for AY's execution
        // lock, and the wait itself is not charged (ROUTER-LOCK-CLOCK-1).
        let budget = ComponentRetryBudget::new(self.timeout_ms);
        // Trust (#int2bv-ice): a panic anywhere inside the in-process solve —
        // ay's bridge/translation `expect`s, the strict proof checker (the
        // `declare_fun("int2bv")` reserved-symbol ICE class), a solver-internal
        // assertion — must NOT unwind into (and abort) the embedding compiler.
        // Contain it and fail closed to Unknown: no proof, no refutation, so
        // soundness is unaffected. The panic message is preserved in the reason
        // for diagnosis. (`ay_exec_lock()` is unwind-tolerant: acquisition
        // recovers a poisoned lock via `into_inner`.)
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_ay_diagnostics_policy(|| {
                let InProcessSolve { result: first, decided_unsat } =
                    self.solve_and_classify_in(formula, allow_bounded_finite, &budget);
                // Trust: DISJOINT-COMPONENT REFUTATION (2026-08-20) — retry ONLY an
                // undecided whole-query as a component-wise refutation. Gated on
                // `Unknown` so no verdict that decides today can move, and the retry
                // can only produce `Failed` (never a trust seal) — see
                // `disjoint_conjunctive_components` for the composition argument.
                //
                // Not after ay's search DECIDED the query UNSAT and a certification
                // gate withheld it (determinism acceptance, 2026-10-01). Variable-
                // disjoint components are all satisfiable iff the whole is, so the
                // retry could refute only by contradicting that search, and the
                // gate found nothing against it: it withheld the UNSAT for want of
                // a checkable proof, never because the query is satisfiable
                // (`ay_search_decided_unsat`). All the retry could do is certify a
                // component's UNSAT again — work no count bounds, under 1/n of the
                // per-VC clock — and let that clock choose the row's stop: one
                // `unverified-trust-rule` refusal read `unclassified` idle and
                // `wall-backstop` under 36 busy loops.
                let VerificationResult::Unknown { time_ms, .. } = &first else {
                    return first;
                };
                if decided_unsat {
                    return first;
                }
                let elapsed = *time_ms;
                match self.try_disjoint_component_refutation(
                    formula,
                    allow_bounded_finite,
                    elapsed,
                    &budget,
                ) {
                    ComponentRetry::Refuted(failed) => failed,
                    ComponentRetry::Undecided(cause) => crate::ay_stop::after_undecided_retry(
                        first,
                        cause,
                        "disjoint-component refutation retry",
                    ),
                    ComponentRetry::NotApplicable => first,
                }
            })
        }));
        let result = match outcome {
            Ok(result) => result,
            Err(payload) => StopCause::SolverFault.unknown_result(
                SOLVER_NAME,
                0,
                &format!(
                    "in-process ay solve panicked ({}); failing closed",
                    panic_payload_to_string(&*payload)
                ),
            ),
        };
        // Every in-process solve ends here — the router's, S1 revalidation's,
        // the R1 harvest's, every refutation lane's. A backstop that fired, or
        // a stop nobody explained, goes to the determinism ledger whether or
        // not the caller publishes this result as a row (plan §2).
        trust_types::determinism::note_result(IN_PROCESS_AY_LANE, &result);
        result
    }

    /// [`Self::solve_and_classify_in`] as one whole query with a budget of its
    /// own: the single solve the tests drive directly.
    #[cfg(test)]
    fn solve_and_classify_with_policy(
        &self,
        formula: &Formula,
        allow_bounded_finite: bool,
    ) -> InProcessSolve {
        self.solve_and_classify_in(
            formula,
            allow_bounded_finite,
            &ComponentRetryBudget::new(self.timeout_ms),
        )
    }

    /// The actual solve + outcome classification (see [`Self::run`]), and
    /// whether ay's search decided the query UNSAT ([`InProcessSolve`]).
    ///
    /// `budget` is the whole query's ([`ComponentRetryBudget`]): this solve's
    /// work before and after it waits for AY's execution lock runs under its
    /// deadline, the wait is credited to it, and `self.timeout_ms` (this
    /// solve's nominal clock, a component's share in a retry) is capped by
    /// what is left of it when the lock is taken.
    fn solve_and_classify_in(
        &self,
        formula: &Formula,
        allow_bounded_finite: bool,
        budget: &ComponentRetryBudget,
    ) -> InProcessSolve {
        #[cfg(test)]
        tests::SOLVES.with(|solves| solves.set(solves.get() + 1));
        // The work before the lock: the decline gates and the program's
        // construction, under the query's deadline.
        let prepare_clock =
            trust_types::verify_budget::DeadlineShareGuard::narrow(budget.deadline());
        // Trust (DIAGNOSTIC ONLY, 2026-09-19): `TRUST_AY_SMT_TRACE=1` prints the
        // EXACT constraint program this backend asserts, at the solver boundary.
        //
        // Why here and not in vcgen. A trace at the end of VC generation
        // (`TRUST_SLICE_VC_TRACE`) showed a guarded slice-bounds row whose
        // formula was UNSATISFIABLE — guard `Gt(w__slice_len#s2_t, 0)`, index
        // `Eq(_14, 0)`, length `Eq(_15, w__slice_len#s2_t)`, violation
        // `Ge(_14, _15)`, one version of the length term throughout — while the
        // row was REPORTED refuted with `_14 = 1` and `_16 = true`, values that
        // formula forbids. So the program actually solved is not the one
        // generated, and only a boundary trace can show which. Set both flags to
        // see the pair.
        //
        // Verdict-neutral: no branch depends on it, and `problem_smt2` is
        // documented as a pure function of the formula that never invents solver
        // output.
        static AY_SMT_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if *AY_SMT_TRACE.get_or_init(|| std::env::var_os("TRUST_AY_SMT_TRACE").is_some()) {
            eprintln!("[aysmt] ---- program handed to ay ----\n{}", problem_smt2(formula));
        }
        // Evaluate `check_formula_sort` once first: when it returns `Ok(actual)`,
        // every comparison in `formula` already satisfied `sorts_agree`, so the
        // `O(N * D)` `formula_comparisons_well_sorted` walk is provably `true` and
        // skipped; on `Err`, run the two historical crash-class checks first so
        // their specialized diagnostics keep exact priority.
        let surface = match check_formula_sort(formula) {
            Ok(actual) => {
                let surface = FormulaSurface::of(formula);
                if surface.has_bitcast_or_fp_to_bv
                    && let Some(reason) = formula_bitcast_mismatch(formula)
                {
                    return VerificationResult::Unknown {
                        solver: SOLVER_NAME.into(),
                        time_ms: 0,
                        reason: StopCause::Unsupported
                            .stamp(&format!("in-process ay declined: {reason}")),
                    }
                    .into();
                }
                if actual != Sort::Bool {
                    return VerificationResult::Unknown {
                        solver: SOLVER_NAME.into(),
                        time_ms: 0,
                        reason: StopCause::Unsupported.stamp(&format!(
                            "in-process ay declined: VC formula has top-level sort {actual:?}, expected Bool"
                        )),
                    }
                    .into();
                }
                surface
            }
            Err(error) => {
                if !formula_comparisons_well_sorted_fallback(formula) {
                    return VerificationResult::Unknown {
                        solver: SOLVER_NAME.into(),
                        time_ms: 0,
                        reason: StopCause::Unsupported.stamp(
                            "in-process ay declined: VC formula has a sort-mismatched comparison",
                        ),
                    }
                    .into();
                }
                if let Some(reason) = formula_bitcast_mismatch(formula) {
                    return VerificationResult::Unknown {
                        solver: SOLVER_NAME.into(),
                        time_ms: 0,
                        reason: StopCause::Unsupported
                            .stamp(&format!("in-process ay declined: {reason}")),
                    }
                    .into();
                }
                return VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms: 0,
                    reason: StopCause::Unsupported.stamp(&format!(
                        "in-process ay declined: VC formula is sort-invalid: {error}"
                    )),
                }
                .into();
            }
        };
        // The sort checker above judges a datatype term by the sort the NODE
        // carries; it never asks whether that descriptor agrees with the
        // datatype's own definition. `formula_to_expr` does ask — ay-bindings
        // authenticates every constructor/selector/tester against the one
        // descriptor registered for its name — and answers a malformed term
        // with a fail-closed PANIC. Ask the same question here, fallibly, and
        // DECLINE (sound: neither a proof nor a refutation) so the malformed
        // shape never reaches the bridge: `run_with_policy`'s `catch_unwind` is
        // containment of last resort, not input validation — a caught panic
        // still runs the process-global panic hook and can leak a false
        // compiler-ICE-looking diagnostic to stderr.
        if surface.has_datatype
            && let Some(reason) = formula_datatype_defect(formula)
        {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!("in-process ay declined: {reason}")),
            }
            .into();
        }
        // The same question, asked of the UNINTERPRETED SYMBOLS: SMT-LIB and ay
        // have one declaration per symbol, so a formula that applies one
        // `Pred`/`FnApp` name at two arities, two argument sorts or two result
        // sorts has no faithful program. Handing it over anyway reaches ay's
        // `uf::apply`, whose infallible wrapper PANICS on the mismatch — the
        // translation-boundary crash class again, rescued only by
        // `catch_unwind`, which still runs the process-global panic hook.
        if surface.has_uf
            && let Some(reason) = uninterpreted_signature_conflict(formula)
        {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!("in-process ay declined: {reason}")),
            }
            .into();
        }
        // Last structural question before the bridge: is every NODE one the
        // bridge has a lowering arm for? `Formula` is `#[non_exhaustive]`, so a
        // variant added to trust-ir-contract compiles into every gate above —
        // `check_formula_sort` may even sort it perfectly — and then falls
        // through `formula_to_expr`'s fail-closed wildcard to a PANIC. That is
        // exactly how `Formula::FnApp` and the five FP conversion nodes reached
        // production. Asking `is_lowerable_formula` turns the next such variant
        // into a DECLINE (sound: neither a proof nor a refutation) instead of a
        // caught panic; the gate is vacuous for every variant of today's
        // contract, all of which the bridge lowers.
        if surface.has_rm
            && let Some(reason) = rounding_mode_position_defect(formula)
        {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!("in-process ay declined: {reason}")),
            }
            .into();
        }
        // The BINDER-SORT class. `Formula::children()` returns only the body of
        // a `Forall`/`Exists`, so every gate above — and `check_formula_sort`
        // itself — is blind to a quantifier's BINDING SORTS, while
        // `formula_to_expr_in` lowers each of them with `sort_to_ay_in` exactly
        // as it lowers a `Var`'s. This gate walks the sort positions the
        // LOWERING visits (`smt_logic::visit_sort_positions`, the same inventory
        // `DatatypeDefs::extend_from_formula` builds the table from) and
        // declines any sort ay has no faithful counterpart for: a
        // `Sort::RoundingMode`, a zero-width bitvector, or a sort variant added
        // to the contract after this audit.
        if surface.has_non_primitive_or_zero_bv_sort
            && let Some(reason) = unlowerable_sort_position(formula)
        {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!("in-process ay declined: {reason}")),
            }
            .into();
        }
        if !is_lowerable_formula(formula) {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(
                    "in-process ay declined: VC formula carries a node the ay bridge has no \
                         lowering for",
                ),
            }
            .into();
        }
        if let Some((name, first, second)) = free_variable_sort_conflict(formula) {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!(
                    "in-process ay declined: free variable `{name}` has conflicting sorts {first:?} and {second:?}"
                )),
            }.into();
        }
        if surface.has_uf
            && trust_types::any_formula_node(formula, &mut |node| {
                matches!(node, Formula::Pred(name, _) if is_reserved_symbol(name.as_str()))
            })
            && let Some(name) =
                collect_pred_symbols(formula).into_keys().find(|name| is_reserved_symbol(name))
        {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!(
                    "in-process ay declined: predicate symbol '{name}' is a reserved ay \
                     builtin theory-operator name and cannot be declared as an \
                     uninterpreted function"
                )),
            }
            .into();
        }
        // Compute the escaped + spine-flattened formula ONCE and share it across
        // `reserved_symbol_handed_to_ay` and `build_program_from_asserted`.
        let asserted = asserted_formula(formula);
        if let Some(name) = ay_symbol_namespace::reserved_symbol_handed_to_ay(&asserted) {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: StopCause::Unsupported.stamp(&format!(
                    "in-process ay declined: symbol '{name}' is a reserved ay builtin \
                     theory-operator name and cannot be declared"
                )),
            }
            .into();
        }
        // The datatype registration inside `build_program` is fail-closed: a
        // refused declaration/constant declines the obligation (sound: neither
        // a proof nor a refutation is emitted) instead of asserting over a
        // stand-in sort or panicking into the embedding compiler.
        let mut program = match self.build_program_from_asserted(
            &asserted,
            surface.has_datatype,
            surface.has_uf,
        ) {
            Ok(program) => program,
            Err(reason) => {
                return VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms: 0,
                    reason: StopCause::Unsupported
                        .stamp(&format!("in-process ay declined: {reason}")),
                }
                .into();
            }
        };
        drop(prepare_clock);

        // Serialize the solve: ay-dpll's direct path is not reentrant (see
        // ay_exec_lock). The wait for the lock is NOT this query's work
        // (ROUTER-LOCK-CLOCK-1): it is credited to the query's own clock, so a
        // query queued behind a slow one is still solved under its whole
        // budget; only the outer deadline and the lock-wait backstop stop it.
        let (hold, waited) = match lock_ay_exec_until(budget.lock_wait_give_up_at(Instant::now())) {
            Ok((hold, waited)) => (Some(hold), waited),
            Err(waited) => (None, waited),
        };
        budget.note_lock_wait(waited);
        // The wait as measured, apart from what the budget makes of it: the
        // tests' evidence that a query really outwaited its clock.
        #[cfg(test)]
        lock_clock_tests::LOCK_WAITED.with(|total| total.set(total.get().saturating_add(waited)));
        let Some(hold) = hold else {
            return lock_wait_stopped(budget, waited).into();
        };
        let start = Instant::now();
        // The work from here on (dispatch, and the reconstruction below) runs
        // under the query's deadline, moved by the wait just credited.
        let _clock = trust_types::verify_budget::DeadlineShareGuard::narrow(budget.deadline());

        // execute_incremental preserves the per-check-sat `unsat_proof` artifact
        // (execute_all / execute drop it), so it is the correct entry point for
        // capturing ay's in-process refutation proof.
        //
        // The hold is scoped to the RAW SOLVE ONLY. `ay_exec_lock`'s contract
        // requires exactly that — "held ACROSS THE RAW SOLVE ONLY, and never
        // across pure clean-kernel reconstruction — so that the dominant
        // clean-kernel certification work runs unlocked and parallelizes across
        // verification threads". Everything below (`unsat_to_result`, and on an
        // `ay-certify` build the kernel certify/replay inside
        // `promote_to_certified`) is reconstruction, so it must run unlocked.
        let outcomes = {
            let _ay_guard = hold;
            let Some(timeout_ms) =
                timeout_within_deadline(self.timeout_ms, budget.deadline(), start)
            else {
                return budget_spent_before_dispatch(budget).into();
            };
            if timeout_ms != 0 {
                program.set_option(":timeout", timeout_ms.to_string());
            }
            match execute_direct::execute_incremental(&program) {
                Ok(outcomes) => outcomes,
                Err(err) => {
                    return StopCause::SolverFault
                        .unknown_result(
                            SOLVER_NAME,
                            start.elapsed().as_millis() as u64,
                            &format!("in-process ay execution error: {err}"),
                        )
                        .into();
                }
            }
        };

        let time_ms = start.elapsed().as_millis() as u64;

        // The program has exactly one check-sat, so expect exactly one outcome.
        // An empty vector is a guarded failure: never Proved.
        let Some(outcome) = outcomes.last() else {
            return StopCause::SolverFault
                .unknown_result(SOLVER_NAME, time_ms, "in-process ay produced no check-sat outcome")
                .into();
        };

        let result = match &outcome.result {
            // UNSAT: no violation reachable. Proved only with a strict proof.
            ExecuteTypedResult::Verified => {
                let base = Self::unsat_to_result(outcome.unsat_proof.as_ref(), time_ms, formula);
                Self::finish_verified_result(base, formula, time_ms, allow_bounded_finite)
            }
            // SAT: a violation witness exists. Surface ay's concrete model as the
            // counterexample (previously discarded as `None`, leaving a refuted
            // refinement un-witnessed — the divergence was found but its inputs
            // were not reported to the driver/agent).
            ExecuteTypedResult::Counterexample(cex) => VerificationResult::Failed {
                solver: SOLVER_NAME.into(),
                time_ms,
                counterexample: Some(counterexample_from_ay_model(cex)),
            },
            // Solver could not decide: say WHY (plan §3.7).
            ExecuteTypedResult::Unknown(reason) => {
                let (stop, conflicts) = in_process_unknown_stop(outcome, reason);
                let spent = conflicts
                    .map(|conflicts| format!(" ({conflicts} conflicts)"))
                    .unwrap_or_default();
                stop.unknown_result(
                    SOLVER_NAME,
                    time_ms,
                    &format!("in-process ay returned unknown: {reason}{spent}"),
                )
            }
            // The direct path cannot execute this program shape at all.
            ExecuteTypedResult::NeedsFallback(reason) => StopCause::Unsupported.unknown_result(
                SOLVER_NAME,
                time_ms,
                &format!("in-process ay requires fallback: {reason}"),
            ),
            // `ExecuteTypedResult` is #[non_exhaustive]. Any future outcome that
            // is not an explicit Verified (UNSAT) must fail closed to Unknown —
            // only the Verified arm above can ever yield Proved.
            _ => StopCause::Unclassified.unknown_result(
                SOLVER_NAME,
                time_ms,
                "in-process ay returned an unrecognized outcome",
            ),
        };
        let decided_unsat = ay_search_decided_unsat(outcome, &result);
        InProcessSolve { result, decided_unsat }
    }

    /// Apply the ordinary backend's complete finite-domain fallback only when
    /// policy permits it. Fresh S1 revalidation passes `false`, so an AY UNSAT
    /// result without a strict-accepted AY artifact remains `Unknown` even when
    /// a separate exhaustive proof could establish the formula.
    fn finish_verified_result(
        base: VerificationResult,
        formula: &Formula,
        time_ms: u64,
        allow_bounded_finite: bool,
    ) -> VerificationResult {
        if matches!(base, VerificationResult::Proved { .. }) || !allow_bounded_finite {
            return base;
        }

        // ay decided UNSAT but produced no strict-checked proof artifact for
        // this formula. For a finite-domain violation formula the bounded
        // exhaustive enumeration is an independent complete proof. It remains
        // available to the ordinary backend but is intentionally not solver
        // replay authority.
        bounded_finite_unsat_proof(formula, time_ms).unwrap_or(base)
    }
}

/// The backstop-ledger lane in-process ay reports its non-reproducible stops
/// under ([`trust_types::determinism::note_stop`]).
pub(crate) const IN_PROCESS_AY_LANE: &str = "in-process ay";

/// The row of a query that stopped waiting for AY's execution lock, after
/// `waited`, before any solve: a clock stop (`wall-backstop`), naming the
/// wait and the bound that ended it (ROUTER-LOCK-CLOCK-1). The wait goes in
/// `time_ms`, never in the reason: a reason names only what a configuration
/// decides, so two runs that stop the same way read the same.
fn lock_wait_stopped(
    budget: &ComponentRetryBudget,
    waited: std::time::Duration,
) -> VerificationResult {
    let waited_ms = u64::try_from(waited.as_millis()).unwrap_or(u64::MAX);
    let bound = match budget.spent_by(Instant::now()) {
        Some(crate::disjoint_components::BudgetBound::Outer) => {
            "the enclosing verification deadline passed".to_string()
        }
        _ => format!("its lock-wait backstop of {} ms ran out", budget.lock_wait_backstop_ms()),
    };
    StopCause::WallBackstop.unknown_result(
        SOLVER_NAME,
        waited_ms,
        &format!(
            "stopped waiting for AY's process-global execution lock: {bound}; no solve was \
             dispatched"
        ),
    )
}

/// The row of a query whose budget was spent when it took AY's execution lock:
/// no solve is dispatched (`wall-backstop`). The wait for the lock was not
/// charged to it (ROUTER-LOCK-CLOCK-1), so the query's OWN clock is spent only
/// by its own work, its earlier solves included; the outer one is the enclosing
/// verification deadline, which every wait still spends. Both keep the reason
/// this row has always had as their prefix.
fn budget_spent_before_dispatch(budget: &ComponentRetryBudget) -> VerificationResult {
    // Named by which bound the deadline is, not by which one has passed: a
    // deadline less than a millisecond away has passed for dispatch
    // (`timeout_within_deadline`) before it has passed on the clock.
    let detail = match budget.binding_bound() {
        Some(crate::disjoint_components::BudgetBound::Outer) => {
            "shared query deadline exhausted before AY dispatch: the enclosing verification \
             deadline passed"
        }
        _ => {
            "shared query deadline exhausted before AY dispatch: the query's own work spent its \
             clock (its waits for AY's execution lock are not charged to it)"
        }
    };
    StopCause::WallBackstop.unknown_result(SOLVER_NAME, 0, detail)
}

/// An UNSAT that a proof gate withheld: never `solved`.
///
/// The withholding is decided by ay's strict-proof machinery, which discharges
/// deferred proof clauses with nested solves. Since P4a.1 (ay ffaba97f6,
/// `crates/ay-dpll/src/api/proofs.rs`, Trust's pin) those solves draw from the
/// solved query's own effort count and no clock is installed, and a stop that
/// ended the discharge is published as [`StrictProofVerdict::Stopped`]
/// ([`strict_proof_stopped`]), never as a rejection. The Carcara cross-check
/// reads the proof that machinery produced. So a rejection is the proof's:
/// `solver-incomplete`, the same on every host.
///
/// When ay's wording names the refusal (plan-critique P1 ledger items,
/// `crate::ay_stop::stop_item_of_ay_text`), the row carries that name: an
/// unverified trust rule or a strict-mode `Generic` lemma stays
/// `solver-incomplete`, a spent certification effort or an exhausted
/// proof-check envelope is `effort`, and a strict check a stop CANCELLED
/// mid-walk is `wall-backstop`.
fn strict_proof_withheld(time_ms: u64, detail: &str) -> VerificationResult {
    crate::ay_stop::AyStop::from_texts(StopCause::SolverIncomplete, &[Some(detail)]).unknown_result(
        SOLVER_NAME,
        time_ms,
        detail,
    )
}

/// An UNSAT whose strict check a stop ended before it decided (ay
/// [`StrictProofVerdict::Stopped`]): no verdict, and the row states the stop's
/// own cause — an interrupt (or a defensive clock inside a fresh solve) is
/// `wall-backstop`, the term-store ceiling (a count of TermStore bytes) is
/// `term-memory`, and a process or lane memory reading is `rss-backstop`. A
/// stop of a kind this build does not know is `unclassified`.
fn strict_proof_stopped(time_ms: u64, stop: StrictVerdictStop) -> VerificationResult {
    let cause = match stop {
        StrictVerdictStop::Interrupted => StopCause::WallBackstop,
        StrictVerdictStop::MemoryLimit { term_store: true } => StopCause::TermMemory,
        StrictVerdictStop::MemoryLimit { term_store: false } => StopCause::RssBackstop,
        // `StrictVerdictStop` is #[non_exhaustive].
        _ => StopCause::Unclassified,
    };
    cause.unknown_result(
        SOLVER_NAME,
        time_ms,
        &format!("UNSAT but strict proof validation was stopped before it decided: {stop:?}"),
    )
}

/// One in-process solve: the row it answers, and whether ay's own search
/// decided the query UNSAT ([`ay_search_decided_unsat`]).
struct InProcessSolve {
    result: VerificationResult,
    decided_unsat: bool,
}

impl From<VerificationResult> for InProcessSolve {
    /// A row with no UNSAT from ay's search behind it: a declined shape, an
    /// execution fault, a SAT answer, an undecided search.
    fn from(result: VerificationResult) -> Self {
        Self { result, decided_unsat: false }
    }
}

/// Whether ay's search decided `outcome`'s query UNSAT: the verdict ay
/// published (`Verified`), whatever Trust's strict proof gate then made of it,
/// or one ay's certification withheld for want of a checkable proof (`result`
/// is that row, [`crate::ay_stop::withheld_computed_unsat`]; a strict check a
/// clock cancelled is one, and its row says `strict-check-cancelled`). A
/// `self_check_rejected` that names no refused UNSAT proof never counts: ay
/// files SAT verdicts it refused under the same code. Nor does a `timeout`: it
/// is a search the clock ended before it decided.
fn ay_search_decided_unsat(outcome: &CheckSatOutcome, result: &VerificationResult) -> bool {
    matches!(outcome.result, ExecuteTypedResult::Verified)
        || crate::ay_stop::withheld_computed_unsat(result)
}

/// How a disjoint-component refutation retry ended.
#[derive(Debug)]
enum ComponentRetry {
    /// The formula has no variable-disjoint split: nothing was retried.
    NotApplicable,
    /// Every component was refuted with a model: the composed `Failed`.
    Refuted(VerificationResult),
    /// A component ended without a model; the retry stopped there, and this
    /// is why that component stopped.
    Undecided(StopCause),
}

/// Why an in-process check-sat ended `unknown`, and the SAT conflicts it spent.
///
/// ay's solve envelope carries the typed reason (`UnknownReason::code()`) and
/// the diagnostic that separates the term-store ceiling from process memory;
/// those decide. A solve that never produced an envelope is classified by how
/// the direct path degraded; ay's reason text is the last resort. Either way
/// ay's wording (the diagnostic detail, the degradation message, the reason
/// text) names the stop when it is one Trust counts by name.
fn in_process_unknown_stop(
    outcome: &CheckSatOutcome,
    reason_text: &str,
) -> (crate::ay_stop::AyStop, Option<u64>) {
    use crate::ay_stop::AyStop;
    let conflicts = outcome.solve_details.as_ref().map(|details| details.statistics.conflicts);
    if let Some(details) = outcome.solve_details.as_ref()
        && let Some(reason) = details.unknown_reason
    {
        let detail =
            details.unknown_diagnostic.as_ref().and_then(|diagnostic| diagnostic.detail.as_deref());
        return (
            crate::ay_stop::ay_stop_of_code(reason.code(), &[detail, Some(reason_text)]),
            conflicts,
        );
    }
    let stop = match outcome.degradation.as_ref() {
        Some(ExecuteDegradation { kind, message, .. }) => {
            let texts = [Some(message.as_str()), Some(reason_text)];
            match kind {
                ExecuteDegradationKind::ConstraintTranslationPanic
                | ExecuteDegradationKind::SolverPanic
                | ExecuteDegradationKind::ModelExtractionFailure
                | ExecuteDegradationKind::ModelExtractionPanic
                | ExecuteDegradationKind::GetValueExtractionFailure
                | ExecuteDegradationKind::GetValueExtractionPanic => {
                    AyStop::from_texts(StopCause::SolverFault, &texts)
                }
                // A SAT answer whose model did not validate: withheld by a
                // deterministic gate, and named (plan-critique P1 ledger item).
                ExecuteDegradationKind::UnvalidatedSatBoundary => AyStop {
                    cause: StopCause::SolverIncomplete,
                    item: Some(trust_types::determinism::StopItem::ModelValidationViolated),
                },
                ExecuteDegradationKind::SolverUnknown => {
                    crate::ay_stop::ay_stop_of_token(reason_text, Some(message.as_str()))
                }
                _ => AyStop::from_texts(StopCause::Unclassified, &texts),
            }
        }
        None => crate::ay_stop::ay_stop_of_token(reason_text, None),
    };
    (stop, conflicts)
}

impl Default for InProcessAyBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for InProcessAyBackend {
    fn name(&self) -> &str {
        SOLVER_NAME
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // Only the L0 safety obligations the in-process SMT path can decide,
        // and only when direct execution is actually available. UnsupportedMir
        // and all contract/temporal/L1+/L2 kinds are excluded by construction:
        // they are simply not in this match arm.
        let kind_ok = matches!(
            &vc.kind,
            VcKind::ArithmeticOverflow { .. }
                | VcKind::ShiftOverflow { .. }
                | VcKind::NegationOverflow { .. }
                | VcKind::DivisionByZero
                | VcKind::RemainderByZero
                | VcKind::IndexOutOfBounds
                | VcKind::SliceBoundsCheck
                // The unbounded-allocation (#nia-oom) obligation's failure formula
                // is `Ge(count, CEILING)` conjoined with reaching block-defs — a
                // plain QF_LIA integer comparison squarely in ay's wheelhouse.
                // Without this arm the VC routes to "no backend can handle this"
                // and returns `unknown` instead of being refuted with a witness.
                | VcKind::UnboundedAllocation { .. }
                | VcKind::Assertion { .. }
                // Trust: translation-validation refinement obligations. The
                // data-flow/return checks emit `Not(Eq(src_expr, tgt_expr))` and the
                // control-flow check a definite-violation literal — QF_BV / QF_LIA
                // formulas ay decides. Without these arms a SAT refinement (a real
                // port-vs-reference divergence, e.g. ATERM-FINDINGS class 4) routes
                // only to the constant-folder, which returns `unknown` on any
                // symbolic formula, so the divergence is MISSED (inconclusive) and a
                // genuine refinement is left at the constant-folder's `Sound` tier
                // instead of ay's strict-checked `SmtBacked`. ay's UNSAT strict gate
                // (StrictProofVerdict::Verified) keeps PROVE sound; SAT yields the
                // counterexample witness. Multi-block refinement VCs (which the
                // single-block straight-line detector never reaches) need this.
                | VcKind::RefinementViolation { .. }
                | VcKind::TranslationValidation { .. }
                // Trust (#5-PRE-A): a caller-side PRECONDITION obligation. Its violation
                // formula is `Not(P[σ])` — P with the call's actual arguments substituted
                // (e.g. `!(5 < 10)` for an established constant precondition, or `i >= 4`
                // for a free-input violation). That is exactly the QF_LIA / QF_BV fragment
                // ay decides: UNSAT ⇒ Proved (the caller established the precondition),
                // SAT ⇒ Failed (a real input violates it, e.g. `a[i]` with `i >= len`). Any
                // OPAQUE / non-linear predicate ay cannot decide stays Unknown and is
                // fail-closed by the `build_proof_results` reclassify. Without this arm the
                // caller-side precondition VC routed ONLY to trust-wp (Unsupported →
                // permanent Unknown) even when it was a decidable comparison, so an
                // ESTABLISHED linear precondition never PROVED and the reclassify would
                // over-reject valid Rust. `verify()` is kind-agnostic (`run(&vc.formula)`),
                // so admitting the kind is sufficient.
                | VcKind::Precondition { .. }
                // Trust (contract-completeness inc-1): a DEFINITION-SITE postcondition
                // obligation. `generate_v2_contract_vcs` builds this VC's `formula` as a
                // SELF-CONTAINED violation goal that already conjoins the return-value pin
                // and the body/guard/precondition facts with `Not(predicate)` — e.g.
                // `And([_0 == x + 1, x < 100, Not(_0 > x)])`. Unlike the caller-side
                // postcondition-ASSUME scenario (where `_0` needs the callee's return
                // value and is not in scope), here the function's OWN body pins `_0`, so
                // the formula is a complete ∀-inputs proof goal ay decides by strict
                // UNSAT: UNSAT ⇒ Proved (the postcondition holds for every input), a
                // strict-checked (Gate A) certificate identical to the L0 kinds above.
                //
                // SOUNDNESS: this arm only lets ay REACH `verify`; it grants no new
                // trust. `verify` mints `Proved` ONLY on a strict-checked UNSAT proof.
                // A SATisfiable violation yields `Failed`, but the postcondition VC can
                // be SAT for a *valid* contract whose body facts the formula
                // under-approximates (e.g. the `postcondition_references_mutated_param`
                // fail-closed shape emits `Not(post)` with FREE params). So the v1/ay
                // BRIDGE (`trust_verify.rs`) substitutes ONLY an ay `Proved` for the
                // Postcondition kind and leaves a SAT/Unknown fail-closed — never a false
                // REFUTE. This arm is therefore purely ADDITIVE over the fail-closed
                // backstop: it can only turn a fail-closed Unknown into a
                // strict-UNSAT-checked Proved.
                | VcKind::Postcondition
                // Trust (falsification regression 2026-08-13): the UNREACHABLE trap
                // obligation (`unreachable_unchecked` / a partial `match`'s
                // `_ => unreachable!()`). trust-vcgen emits its violation formula as the
                // ordinary reachability goal (`And([Not(Eq(x,0)), Not(Eq(x,1)), 0<=x<=255])`
                // for a `u8` match on {0,1}) — squarely the QF_LIA/QF_BV fragment ay
                // decides, and the same shape every L0 safety kind above admits. Its
                // absence here was an oversight, not a decision: every other classifier
                // already groups `Unreachable` with the L0 safety kinds
                // (`has_runtime_fallback`, `vc_kind_is_memory_safe_panic`,
                // `classify_property`).
                //
                // WHY IT MATTERS NOW: the typed-CHC lane used to be this kind's ONLY
                // refutation channel, and `fix(semantics): fail closed on unattested
                // refinement edges` correctly began demoting refutations that carry no
                // positive producer-fidelity attestation — which is every row on the
                // flattened single-formula lane, including the EXACT ACYCLIC ones. Two
                // falsification mutants (`partial_int_unreachable`,
                // `enum_partial_unreachable`) stopped being refuted as a result: real
                // reachable UB traps shipping as `runtime-checked`.
                //
                // SOUNDNESS: the v1/ay bridge substitutes ONLY a `Failed` for this kind
                // (refute-only, mirroring the `Postcondition` asymmetry in the opposite
                // direction), so it grants NO proof authority — a genuinely dead trap is
                // still discharged by `promote_structurally_dead_unreachable`, which runs
                // AFTER the bridge and only upgrades Unknown/Timeout. The two cannot
                // conflict: `promote` fires only on a propositionally-UNSAT formula, on
                // which ay cannot return SAT.
                | VcKind::Unreachable
        )
            // Trust (checked-flag alias clobber, fail-closed): the hardened MIR
            // panic-boundary TWINS of the L0 safety kinds above. trust-vcgen's
            // hardened lane emits, for each MIR `Assert` terminator, a
            // `HardenedBoundary { PanicBoundary, callee: "mir_assert::<msg>" }`
            // VC whose `formula` is the SAME violation goal as the sibling
            // per-statement arithmetic/bounds/divisor VC — squarely the QF_LIA /
            // QF_BV fragment this backend decides. The recognizer is SHARED with
            // `IntervalBackend` (`hardened_mir_assert_goal`), which already
            // routes exactly this population and whose comments describe these
            // rows as "falling through to the SMT lane" — an arm this backend
            // never had, so an interval-undischargeable twin (e.g. an
            // alias-forged overflow flag) stayed permanently Unknown instead of
            // being REFUTED. Every other PanicBoundary callee (`unwrap`/`expect`/
            // policy `Custom(..)`) and every other hardened category returns
            // `None` and is still declined. SOUNDNESS: `verify` is kind-agnostic
            // (`run(&vc.formula)`) and mints `Proved` ONLY on a strict-checked
            // UNSAT proof of the violation goal (the boundary provably cannot
            // fire — the same discharge `IntervalBackend` already mints for
            // these rows, upgraded to `SmtBacked` with an ay proof artifact);
            // SAT yields `Failed` with a concrete witness (fail-closed: the
            // boundary is not statically excluded), never a rubber-stamp.
            || crate::interval_backend::hardened_mir_assert_goal(vc).is_some();
        kind_ok && execute_direct::is_available()
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        // Defensive: UnsupportedMir must never reach a solver. can_handle already
        // excludes it, but guard here too so a direct verify() call is safe.
        if let Some(result) = unsupported_mir_unknown(vc, SOLVER_NAME, 0) {
            return result;
        }
        self.run(&vc.formula)
    }
}

/// Convert ay's SAT model into a Trust [`Counterexample`] so a refuted refinement
/// (or any refuted obligation) carries the concrete witness assignments. ay reports
/// the model in `ExecuteCounterexample::model` (with `values` as the explicitly
/// requested subset); we prefer the full model and fall back to `values`. Assignments
/// are sorted for deterministic output.
/// Trust: ay reports the model under the NAMESPACED symbol names
/// `build_program` declared, so each binding is mapped back to its source
/// spelling (`ay_symbol_namespace::unescape_model_symbol`: a variable, or a
/// nullary `Pred`/`FnApp` declared as a constant), and so is every
/// datatype constructor inside a value (`unescape_model_value`). Counterexamples
/// are read by humans and by the refutation machinery, both of which know the
/// VC's own variable and constructor names; a namespaced name would be a
/// witness nobody can match to a local or a variant.
fn counterexample_from_ay_model(cex: &ExecuteCounterexample) -> Counterexample {
    let src = if cex.model.is_empty() { &cex.values } else { &cex.model };
    let mut assignments: Vec<(String, CounterexampleValue)> = src
        .iter()
        .map(|(name, v)| {
            (
                ay_symbol_namespace::unescape_model_symbol(name),
                model_value_to_cex(&ay_symbol_namespace::unescape_model_value(v)),
            )
        })
        .collect();
    assignments.sort_by(|a, b| a.0.cmp(&b.0));
    Counterexample::new(assignments)
}

/// Map a single ay `ModelValue` to a Trust [`CounterexampleValue`] FAITHFULLY:
/// every binding renders the value ay actually found, never a stand-in.
///
/// * `Bool`/`Int`/`BitVec` take their scalar carriers. Big integers are
///   stringified-then-parsed so no `num-traits` dependency leaks in; a value
///   outside `i128`/`u128` (a >128-bit bitvector) keeps its SMT-LIB spelling
///   instead of degrading to `0`.
/// * An IEEE binary32/binary64 value (the two Rust float formats) is
///   reassembled bit-exactly into `Float`; any other format keeps ay's
///   `(fp …)` spelling.
/// * Everything else — a datatype constructor application (`(succ zero)`),
///   an array store chain, an exact rational, a string, an uninterpreted-sort
///   element, a sequence — is carried as [`CounterexampleValue::Term`] with
///   ay's own SMT-LIB rendering (`ModelValue`'s `Display`). The previous
///   `Int(0)` placeholder was a FABRICATED witness for every datatype-sorted
///   local: a person reading `m = 0` for a `Level` cannot tell it from a real
///   integer, and the refutation machinery cannot replay it.
fn model_value_to_cex(v: &ModelValue) -> CounterexampleValue {
    match v {
        ModelValue::Bool(b) => CounterexampleValue::Bool(*b),
        ModelValue::Int(i) => i
            .to_string()
            .parse()
            .map_or_else(|_| CounterexampleValue::Term(v.to_string()), CounterexampleValue::Int),
        ModelValue::BitVec { value, .. } => value
            .to_string()
            .parse()
            .map_or_else(|_| CounterexampleValue::Term(v.to_string()), CounterexampleValue::Uint),
        _ => ieee_model_value_to_float(v)
            .map_or_else(|| CounterexampleValue::Term(v.to_string()), CounterexampleValue::Float),
    }
}

/// Reassemble an ay IEEE-754 model value of the binary32 (`eb=8, sb=24`) or
/// binary64 (`eb=11, sb=53`) format bit-exactly into an `f64` (a binary32
/// widens exactly). `None` for any other format or non-float value, so the
/// caller keeps ay's spelling rather than approximating.
fn ieee_model_value_to_float(v: &ModelValue) -> Option<f64> {
    use ay::FpSpecialKind;
    let (sign, exponent, significand, eb, sb) = match v {
        ModelValue::FloatingPoint { sign, exponent, significand, eb, sb } => {
            (*sign, *exponent, u128::from(*significand), *eb, *sb)
        }
        ModelValue::FloatingPointWide { sign, exponent, significand, eb, sb } => {
            (*sign, *exponent, *significand, *eb, *sb)
        }
        ModelValue::FloatingPointSpecial { kind, eb, sb } => {
            let (neg, exponent, significand): (bool, u64, u128) = match kind {
                FpSpecialKind::PosZero => (false, 0, 0),
                FpSpecialKind::NegZero => (true, 0, 0),
                FpSpecialKind::PosInf => (false, u64::MAX, 0),
                FpSpecialKind::NegInf => (true, u64::MAX, 0),
                FpSpecialKind::NaN => (false, u64::MAX, 1),
                _ => return None,
            };
            // `u64::MAX` stands for the all-ones exponent field; it is masked
            // to the format's width below.
            (neg, exponent, significand, *eb, *sb)
        }
        _ => return None,
    };
    match (eb, sb) {
        (8, 24) => {
            let exponent = u32::try_from(exponent & 0xFF).ok()?;
            let fraction = u32::try_from(significand).ok()?;
            if fraction >= 1 << 23 {
                return None;
            }
            let bits = (u32::from(sign) << 31) | (exponent << 23) | fraction;
            Some(f64::from(f32::from_bits(bits)))
        }
        (11, 53) => {
            let exponent = exponent & 0x7FF;
            let fraction = u64::try_from(significand).ok()?;
            if fraction >= 1 << 52 {
                return None;
            }
            let bits = (u64::from(sign) << 63) | (exponent << 52) | fraction;
            Some(f64::from_bits(bits))
        }
        _ => None,
    }
}

/// True iff `formula` is GROUND — it contains no free (non-quantifier-bound)
/// variables, so every leaf is a literal/constant and its truth value is fully
/// determined with no unknown inputs.
///
/// Used by the default-lane safety-escalation gate in `rustc_mir_transform`:
/// a `Failed` verdict on a GROUND, refutable L0 safety obligation is a
/// GUARANTEED violation (e.g. `1 << 28 >= 1 << 28` for the nn OOM), so it may be
/// promoted from a warning to a hard build error. A formula with a free variable
/// (e.g. `a + b` overflow, `s[0]` bounds) is only conditionally violating and
/// must stay a warning — promoting it would over-fire on valid Rust.
pub fn formula_is_ground(formula: &Formula) -> bool {
    fn is_ground<'a>(formula: &'a Formula, bound_names: &mut Vec<&'a str>) -> bool {
        match formula {
            Formula::Var(name, _) => bound_names.contains(&name.as_str()),
            Formula::SymVar(name, _) => bound_names.contains(&name.as_str()),
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let prev = bound_names.len();
                bound_names.extend(bindings.iter().map(|(name, _)| name.as_str()));
                let ok = is_ground(body, bound_names);
                bound_names.truncate(prev);
                ok
            }
            _ => trust_types::all_formula_children(formula, |child| is_ground(child, bound_names)),
        }
    }
    let mut bound_names = Vec::new();
    is_ground(formula, &mut bound_names)
}

/// True iff no COMPARISON subformula (`Eq`/`Lt`/`Le`/`Gt`/`Ge`) is PROVEN to compare
/// two operands of different sorts. `formula_to_expr` lowers these via
/// `.eq()`/`.int_lt()`/…, which `assert` matching sorts and PANIC on a mismatch (a
/// Bool-vs-Int compare from a malformed discriminant/aggregate obligation). Checking
/// this first lets the backend DECLINE such a VC (Unknown) instead of ICE-ing — a
/// backend must never crash on an ill-typed obligation. SOUNDNESS: declining emits
/// neither a proof nor a refutation.
///
/// The gate may only decline on a PROVEN mismatch, never on ignorance: an operand
/// whose sort the checker cannot establish (`check_formula_sort` errs) is left to the
/// full-formula `check_formula_sort` gate that follows, which reports the structural
/// error with its own diagnostic. Two established sorts are compared with
/// `sorts_agree`, so a datatype's by-name and full spellings (`pred(succ l) = l`,
/// where `Sel::field_sort` is the reference and `l` carries the definition) are ONE
/// sort, exactly as the checker judges them. The earlier `infer_sort(a) !=
/// infer_sort(b)` test declined every constructor-, selector-, tester- and
/// `FnApp`-vs-variable equation: `infer_sort` had no arm for those nodes and
/// answered its `Int` sentinel, so a well-sorted `succ(l) = l` read as `Int` vs
/// `Level`.
#[derive(Default)]
struct FormulaSurface {
    has_bitcast_or_fp_to_bv: bool,
    has_datatype: bool,
    has_uf: bool,
    has_rm: bool,
    has_non_primitive_or_zero_bv_sort: bool,
}

impl FormulaSurface {
    fn sort_mentions_rm(sort: &Sort) -> bool {
        match sort {
            Sort::RoundingMode => true,
            Sort::Array(i, e) => Self::sort_mentions_rm(i) || Self::sort_mentions_rm(e),
            Sort::Datatype { constructors, .. } => constructors
                .iter()
                .flat_map(|(_, fields)| fields.iter())
                .any(|(_, fs)| Self::sort_mentions_rm(fs)),
            _ => false,
        }
    }

    fn of(formula: &Formula) -> Self {
        let mut s = Self::default();
        trust_types::visit_formula_nodes(formula, &mut |node| {
            match node {
                Formula::FpFromBits { .. }
                | Formula::BvExtract { .. }
                | Formula::FpToSbv { .. }
                | Formula::FpToUbv { .. } => {
                    s.has_bitcast_or_fp_to_bv = true;
                }
                Formula::Ctor { .. } | Formula::Sel { .. } | Formula::IsCtor { .. } => {
                    s.has_datatype = true;
                }
                Formula::Pred(..) | Formula::FnApp { .. } => {
                    s.has_uf = true;
                }
                Formula::FpRoundingMode(_) => {
                    s.has_rm = true;
                }
                _ => {}
            }
            if !s.has_rm && !trust_types::ay_bridge::rounding_mode_operand_slots(node).is_empty() {
                s.has_rm = true;
            }
            trust_types::smt_logic::visit_node_sort_positions(node, &mut |sort| {
                if !s.has_datatype && sort.contains_datatype() {
                    s.has_datatype = true;
                }
                if !s.has_rm && Self::sort_mentions_rm(sort) {
                    s.has_rm = true;
                }
                if !s.has_non_primitive_or_zero_bv_sort
                    && !matches!(
                        sort,
                        Sort::Int | Sort::Bool | Sort::Real | Sort::Float { .. } | Sort::BitVec(1..)
                    )
                {
                    s.has_non_primitive_or_zero_bv_sort = true;
                }
            });
        });
        s
    }
}

#[cfg_attr(not(test), allow(dead_code))]
fn formula_comparisons_well_sorted(formula: &Formula) -> bool {
    if check_formula_sort(formula).is_ok() {
        return true;
    }
    formula_comparisons_well_sorted_fallback(formula)
}

fn formula_comparisons_well_sorted_fallback(formula: &Formula) -> bool {
    use trust_types::smt_logic::sorts_agree;
    trust_types::all_formula_nodes(formula, &mut |sub| {
        if let Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) = sub
            && let (Ok(left), Ok(right)) = (check_formula_sort(a), check_formula_sort(b))
            && !sorts_agree(&left, &right)
        {
            return false;
        }
        true
    })
}

/// `Some(reason)` iff the VC formula's DATATYPE content is provably defective:
/// the second half of the sort pre-gate, and the one that keeps a malformed
/// datatype term away from the panicking bridge.
///
/// Three defects, all established from the formula alone:
///
/// 1. **A definition contradiction.** One datatype NAME carrying two DIFFERENT
///    full definitions. `sorts_agree` (and therefore `check_formula_sort` and
///    the comparison pre-gate) relaxes datatype equality to agreement BY NAME,
///    which is exactly what lets a by-name field reference and its definitional
///    occurrence be one sort — but by name alone `Level = zero | succ(..)` and
///    `Level = a | b` also "agree", so at the type level the contradiction
///    passes. It is refused here, with a message naming the datatype, rather
///    than only inside `build_program`/`formula_to_expr`, so no consumer of the
///    checker's verdict acts on a formula whose sorts cannot all be declared.
///    (`DatatypeDefs::collect` is the same fail-closed one-definition-per-name
///    rule the lowering applies; running it early only moves the refusal
///    earlier.)
/// 2. **A malformed datatype term** — a `Ctor` whose carried sort is not a
///    datatype, an argument whose established sort contradicts the field, a
///    `Sel` whose `field_sort` contradicts the descriptor, an undeclared
///    constructor/field, a selector/tester over a non-datatype or
///    wrong-datatype operand. ay-bindings answers each of these with a refusal
///    that the bridge turns into a fail-closed panic
///    ([`trust_types::ay_bridge::check_datatype_terms`] is its fallible
///    counterpart).
/// 3. **An undefined datatype** — a sort spelled BY NAME whose full definition
///    appears NOWHERE in the formula. `sort_to_ay_in` lowers it to ay's
///    `DatatypeRef`, which resolves only against a registered descriptor, and
///    the table consulted here is the one `build_program` registers from, so
///    the query is undeclarable. `build_program` catches this at a
///    DECLARATION (`try_declare_const`/`try_declare_datatype`), and the bridge
///    catches a reference living only in TERM positions — but the bridge can
///    only do so because it runs [`undefined_datatype_reference`] itself,
///    BEFORE lowering: ay-bindings' datatype API is infallible at a term
///    position, so the reference would otherwise meet an assertion rather than
///    an error. Reporting it at this gate keeps the bridge unentered and gives
///    the decline the gate's own diagnostic.
///
/// SOUNDNESS: declining emits neither a proof nor a refutation. And the check
/// only ever reports a PROVEN defect — an operand whose sort
/// `check_formula_sort` cannot establish is left alone, and a by-name reference
/// whose definition IS present resolves through the table exactly as the
/// lowering resolves it — so this cannot re-introduce the ignorance-based
/// decline that refused every well-sorted constructor-, selector- and
/// tester-vs-variable equation.
fn formula_datatype_defect(formula: &Formula) -> Option<String> {
    // A declaration that lists one member name twice (the raw-Rust-name
    // `Level` had four selectors spelled `0`) is ambiguous in the SOURCE: a
    // `Sel` names only `(datatype, field)`, so no renaming can say which field it
    // reads. Handing it over leaves that choice to the solver (the pinned ay
    // accepts the declaration, resolves the name to ONE field and refuses reads
    // of the others); declining here names the ambiguity instead.
    if let Some(reason) = ay_symbol_namespace::datatype_member_collision(formula) {
        return Some(format!("VC formula has an ambiguous datatype declaration: {reason}"));
    }
    let defs = match DatatypeDefs::collect(formula) {
        Ok(defs) => defs,
        Err(conflict) => {
            return Some(format!(
                "VC formula has a contradictory datatype definition: {conflict}. Sorts agree by \
                 NAME, so one name must have one definition for the query to be declarable at all"
            ));
        }
    };
    if let Some(name) = undefined_datatype_reference(formula, &defs) {
        return Some(format!(
            "VC formula references undefined datatype `{name}`: the sort is spelled BY NAME and \
             no full definition of `{name}` appears anywhere in the formula, so there is no \
             descriptor to declare it or to authenticate its terms against"
        ));
    }
    check_datatype_terms(formula, &defs)
        .err()
        .map(|error| format!("VC formula has a malformed datatype term: {error}"))
}

/// The router's qualified saturating FP-to-BV width, for both signednesses.
///
/// Historically ay's signed bound shifted a u64 and its unsigned bound clamped
/// at u64::MAX. AY 41a20c2abd06 replaced both with exact BigInt constants.
/// At the current pin, native encoding succeeds through the measured 1..=127
/// sweep and selected wider widths; pinned unsigned operands also produce the
/// exact models recorded in fp_to_bv_native_boundary_measurement.
///
/// Those finite encode/model probes do not establish native/text agreement for
/// every operand and width. Retain the existing qualified width until that
/// wider agreement is validated. This is a router qualification limit, not a
/// claim that the current solver panics or cannot encode above 64.
fn fp_to_bv_agreeing_width(signed: bool) -> u32 {
    let _ = signed;
    64
}

/// Refuse malformed bit reinterpretations/extractions before the infallible
/// AY convenience wrappers can panic on a mismatched operand sort or width.
fn formula_bitcast_mismatch(formula: &Formula) -> Option<String> {
    use trust_types::smt_logic::infer_sort;
    let mut mismatch: Option<String> = None;
    let _ = trust_types::all_formula_nodes(formula, &mut |sub| {
        match sub {
            Formula::FpFromBits { bits, eb, sb } => {
                let expected = Sort::BitVec(eb + sb);
                let actual = infer_sort(bits);
                if actual != expected {
                    mismatch = Some(format!(
                        "FpFromBits(eb={eb}, sb={sb}) requires its bits operand to be \
                         {expected:?}, but it infers to {actual:?}"
                    ));
                }
            }
            Formula::BvExtract { inner, high, low } => match infer_sort(inner) {
                Sort::BitVec(w) if low <= high && *high < w => {}
                actual => {
                    mismatch = Some(format!(
                        "BvExtract(high={high}, low={low}) requires its inner operand to be \
                         a BitVec sort with width > {high}, but it infers to {actual:?}"
                    ));
                }
            },
            // The TOTAL saturating FP -> BV conversions land in a `BitVec(width)`,
            // and there is no zero-width bitvector: ay's `bitvec_const` asserts
            // `width > 0`, so the guarded expansion the bridge builds for these
            // nodes would panic on its own clamp constants. `check_formula_sort`
            // is content with `Sort::BitVec(0)`, so this is the gate that
            // refuses it (sound: neither a proof nor a refutation).
            Formula::FpToSbv { width: 0, .. } | Formula::FpToUbv { width: 0, .. } => {
                mismatch = Some(
                    "an FP-to-bitvector conversion has width 0, which is not a bitvector sort"
                        .to_string(),
                );
            }
            // …and the UPPER bound, which is a TWO-LANE DIVERGENCE rather than
            // a refusal in one lane. See [`fp_to_bv_agreeing_width`].
            Formula::FpToSbv { width, .. } | Formula::FpToUbv { width, .. } => {
                let signed = matches!(sub, Formula::FpToSbv { .. });
                let bound = fp_to_bv_agreeing_width(signed);
                if *width > bound {
                    let op = if signed { "fp.to_sbv" } else { "fp.to_ubv" };
                    mismatch = Some(format!(
                        "a saturating {op} conversion has width {width}, above the qualified \
                         width {bound} for native/text lowering agreement. The pinned AY \
                         bit-blaster uses BigInt bounds (ay-theories/fp/src/bitblast.rs); \
                         wider encode/model samples do not qualify all operands and widths"
                    ));
                }
            }
            _ => {}
        }
        mismatch.is_none()
    });
    mismatch
}

/// Return a decline reason if a `RoundingMode`-sorted term appears anywhere
/// other than the rounding-mode OPERAND of an `fp.*` node.
///
/// ay carries the rounding mode as an ENUM ARGUMENT of each `fp.*` operation,
/// not as a first-class sorted term, so the bridge reads it with
/// `ay_rounding_mode` at the operand positions below and has no `Expr` for a
/// bare one — its arm lowers `Formula::FpRoundingMode` to `Expr::true_()`.
/// That is harmless where the node is only ever read as an operand, and a
/// SILENT MISENCODING anywhere else: `check_formula_sort` is perfectly happy
/// with `Eq(FpRoundingMode(RNE), FpRoundingMode(RTZ))` (both sides
/// `Sort::RoundingMode`), which would lower to `(= true true)` — so its
/// negation, a violation formula that is genuinely REACHABLE, becomes UNSAT
/// and the obligation is falsely PROVED.
///
/// This is the same audit as the unhandled-variant class, one step worse: a
/// variant with no arm PANICS and is caught, while this one answers. No
/// producer builds a bare rounding-mode comparison today — rounding modes are
/// minted only as the first operand of the `fp.*` nodes trust-machine-sem and
/// trust-vcgen emit — so declining the shape costs nothing and closes the hole
/// by construction rather than by inspection.
fn child_could_have_rounding_mode_sort(child: &Formula) -> bool {
    matches!(
        child,
        Formula::FpRoundingMode(_)
            | Formula::Var(_, Sort::RoundingMode)
            | Formula::SymVar(_, Sort::RoundingMode)
            | Formula::Ctor { sort: Sort::RoundingMode, .. }
            | Formula::FnApp { sort: Sort::RoundingMode, .. }
            | Formula::Sel { field_sort: Sort::RoundingMode, .. }
            | Formula::Ite(..)
            | Formula::Select(..)
    )
}

fn rounding_mode_term_out_of_position(formula: &Formula) -> Option<String> {
    // The children of `node` that ARE rounding-mode operand positions. ONE
    // list, owned by the bridge and shared with its own literal gate, so the
    // slot inventory here and the slot inventory the lowering reads cannot
    // drift apart.
    use trust_types::ay_bridge::rounding_mode_operand_slots as rounding_mode_operands;

    let has_any_rm = trust_types::any_formula_node(formula, &mut |node| {
        if matches!(node, Formula::FpRoundingMode(_)) {
            return true;
        }
        let mut rm_sort = false;
        trust_types::smt_logic::visit_node_sort_positions(node, &mut |sort| {
            if !rm_sort && FormulaSurface::sort_mentions_rm(sort) {
                rm_sort = true;
            }
        });
        rm_sort
    });
    if !has_any_rm {
        return None;
    }

    // The root is checked by the top-level `Ok(Sort::Bool)` gate; every other
    // position is some node's child, so walking children covers the tree.
    let mut out_of_position: Option<String> = None;
    let _ = trust_types::all_formula_nodes(formula, &mut |node| {
        let operands = rounding_mode_operands(node);
        trust_types::all_formula_children(node, |child| {
            if operands.iter().any(|rm| std::ptr::eq(*rm, child)) {
                return true;
            }
            if child_could_have_rounding_mode_sort(child)
                && check_formula_sort(child) == Ok(Sort::RoundingMode)
            {
                out_of_position = Some(
                    "a rounding-mode term appears outside an fp.* rounding-mode operand, where \
                     the ay bridge has no expression for it"
                        .to_string(),
                );
                return false;
            }
            true
        })
    });
    out_of_position
}

/// The WHOLE rounding-mode audit, both halves of the class.
///
/// [`rounding_mode_term_out_of_position`] closes only the half where a
/// rounding-mode term sits somewhere the bridge has no `Expr` for. The other
/// half — the FALSE PROVE this gate was extended to close — is a term that
/// occupies an `fp.*` rounding-mode slot legitimately, so the out-of-position
/// walk waves it through, and is then read by the bridge's `ay_rounding_mode`,
/// which used to answer any non-literal with `_ => AyRm::RNE`.
///
/// That default is not conservative, it is a DIFFERENT FORMULA. Demonstrated
/// solver-independently: for
/// `f = FpAdd(Var("rmv", Sort::RoundingMode), x, y)` and
/// `g = FpAdd(FpRoundingMode(RNE), x, y)` the native lowering of both was the
/// identical `(fp.add RNE vf32_0 vf32_1)`, so the violation formula
/// `Not(FpEq(f, g))` — genuinely SATISFIABLE, witnessed by any `rmv` whose
/// rounding differs from RNE on some `x + y` — decided UNSAT and the
/// obligation was reported **Proved**.
///
/// ay has NO first-class rounding-mode sort to lower to: `ay_bindings::Sort`
/// (`SortInner`) has variants for Bool/BitVec/Int/Real/Array/Datatype/String/
/// FloatingPoint/Uninterpreted/DatatypeRef/RegLan/Seq and NONE for
/// `RoundingMode`, and no `Expr` constructor mints an rm-sorted term —
/// `ay_bindings::RoundingMode` is a plain Rust enum PARAMETER of `fp_add`,
/// `fp_sqrt`, `bv_to_fp`, `fp_to_sbv`, … . So faithful support is not
/// available at this boundary, and the lane must DECLINE (sound: it emits
/// neither a proof nor a refutation) rather than pick a mode. The bridge's own
/// `ay_rounding_mode` is fallible and every call site propagates its refusal
/// as `AyBridgeError::NonLiteralRoundingMode`, so the RNE default cannot come
/// back by inspection either.
///
/// This also closes the MEDIUM sibling — a quantifier that BINDS a
/// `Sort::RoundingMode` variable. Binder sorts are not `Formula::children()`
/// (`Forall`/`Exists` return `vec![body]`), so the out-of-position walk cannot
/// reach them; but the bound variable can only DO anything by occupying an rm
/// slot, and this half reads the SLOT rather than the sort, so it sees it.
/// [`unlowerable_sort_position`] closes the binder-sort class generally.
fn rounding_mode_position_defect(formula: &Formula) -> Option<String> {
    rounding_mode_term_out_of_position(formula)
        .or_else(|| trust_types::ay_bridge::non_literal_rounding_mode_operand(formula))
}

// EVERY SORT POSITION THE ay LOWERING WILL ACTUALLY LOWER, including the ones
// no `Formula::children()`-based walk can reach, is enumerated ONCE, by
// `trust_types::smt_logic::visit_node_sort_positions`. The two gates built on
// it — `unlowerable_sort_position` and `undefined_datatype_reference` — now
// live beside the lowering they gate, in `trust_types::ay_bridge`, so the
// bridge's own fallible entry point and this router's gates cannot drift.
//
// THE BINDER-SORT HOLE, recorded here because this is where it was found.
// `Formula::children()` returns `vec![body]` for `Forall`/`Exists`
// (trust-ir-contract formula.rs), so a quantifier's BINDING SORTS are invisible
// to every recursive walk built on it — `visit`, `check_formula_sort`'s
// recursion, `rounding_mode_term_out_of_position`, `formula_sort_mismatch`,
// `is_lowerable_formula`. Meanwhile `formula_to_expr_in`'s `Forall`/`Exists`
// arms lower each binder sort with `sort_to_ay_in`, exactly like a `Var`'s. A
// sort that only ever appears in a binder therefore reached ay through a gate
// that never looked at it.
//
// That single inventory is also what `DatatypeDefs::extend_from_formula` walks
// to BUILD the definition table and what `smt2_export`'s
// `visit_datatype_bearing_sorts` walks to DECLARE and CLASSIFY, so gate,
// builder, declarer and logic line agree BY CONSTRUCTION — pinned by
// `both_lanes_declare_the_same_datatype_set`.

/// Return the first free variable name used at two different sorts. SMT-LIB and
/// AY both have one declaration per symbol, so accepting such a formula would
/// make the native program and canonical transcript ambiguous. Quantifier-local
/// shadowing is already excluded by `collect_free_vars` and remains valid.
fn free_variable_sort_conflict(formula: &Formula) -> Option<(String, Sort, Sort)> {
    fn has_conflict<'a>(
        formula: &'a Formula,
        bound_names: &mut Vec<&'a str>,
        sorts: &mut trust_types::fx::FxHashMap<&'a str, &'a Sort>,
    ) -> bool {
        match formula {
            Formula::Var(name, sort) => {
                let name = name.as_str();
                if bound_names.contains(&name) {
                    return false;
                }
                match sorts.get(name) {
                    Some(&prev) => prev != sort,
                    None => {
                        sorts.insert(name, sort);
                        false
                    }
                }
            }
            Formula::SymVar(name, sort) => {
                let name = name.as_str();
                if bound_names.contains(&name) {
                    return false;
                }
                match sorts.get(name) {
                    Some(&prev) => prev != sort,
                    None => {
                        sorts.insert(name, sort);
                        false
                    }
                }
            }
            Formula::Forall(bindings, body) | Formula::Exists(bindings, body) => {
                let prev = bound_names.len();
                bound_names.extend(bindings.iter().map(|(name, _)| name.as_str()));
                let conflict = has_conflict(body, bound_names, sorts);
                bound_names.truncate(prev);
                conflict
            }
            _ => !trust_types::all_formula_children(formula, |child| {
                !has_conflict(child, bound_names, sorts)
            }),
        }
    }

    let mut bound_names = Vec::new();
    let mut borrowed_sorts = trust_types::fx::FxHashMap::default();
    if !has_conflict(formula, &mut bound_names, &mut borrowed_sorts) {
        return None;
    }

    // Slow path (malformed input only): reproduce the exact `BTreeSet`-sorted
    // `(name, first_sort, second_sort)` witness.
    let mut sorts = BTreeMap::<String, Sort>::new();
    for (name, sort) in smt2_export::collect_free_vars(formula) {
        if let Some(previous) = sorts.insert(name.clone(), sort.clone())
            && previous != sort
        {
            return Some((name, previous, sort));
        }
    }
    None
}

/// A concrete value produced by the bounded finite-domain evaluator. Mathematical
/// `Int` covers every integer/cast/`%`/`Ite` term in an LIA violation formula (the
/// SMT `Int` theory is unbounded, matching `i128` for the small magnitudes that
/// arise from bool->int casts and their sums); `Bool` covers the propositional
/// skeleton and the free bool inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
enum EnumValue {
    Bool(bool),
    Int(i128),
}

/// Bounded exhaustive-enumeration proof for a FINITE-domain violation formula.
///
/// This is the bounded-model-check route for finite functional asserts: when ay
/// decides the violation formula UNSAT but cannot emit a strict-checked proof
/// artifact (an LIA `%`/`Ite`/bool-eq mix its in-process proof producer does not
/// certify), and every free variable ranges over a finitely-enumerable sort, the
/// enumeration is an INDEPENDENT, complete decision procedure: it evaluates the
/// ground violation formula on EVERY assignment of the cartesian product of the
/// free-variable domains.
///
/// Returns `Proved` (`ReasoningKind::ExhaustiveFinite` / `AssuranceLevel::Sound`)
/// IFF the violation formula evaluated to `false` on the COMPLETE finite domain —
/// i.e. no input reaches the failure block, so the asserted property holds for all
/// inputs. The attached certificate records the enumerated domain and case count
/// and is strict / re-checkable by replaying the same deterministic enumeration.
///
/// Returns `None` — DECLINE, fail-closed — in every other situation:
///   * a free variable whose sort is not finitely enumerable (Int/Array/Float/…);
///   * a total domain size above `MAX_CASES` (keeps the route bounded-cost);
///   * the evaluator cannot reduce the ground formula to a definite Bool for some
///     assignment (an unsupported node), so exhaustiveness is NOT established;
///   * any assignment SATISFIES the violation formula (a model exists), so it is
///     not a proof.
///
/// SOUNDNESS: a `Proved` is returned ONLY after the ground formula was evaluated
/// to a definite `false` on the COMPLETE finite domain by a TOTAL evaluator, so it
/// is a genuine ∀-inputs refutation of the violation — never a partial result and
/// never a trusted-solver verdict. Symmetrically it never false-REFUTES: a
/// satisfying assignment declines (returns `None`) rather than emitting `Failed`.
fn bounded_mc_debug_enabled() -> bool {
    static DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DEBUG.get_or_init(|| std::env::var("TRUST_BOUNDED_MC_DEBUG").is_ok())
}

fn bounded_finite_unsat_proof(formula: &Formula, time_ms: u64) -> Option<VerificationResult> {
    // ~4.2M ground evaluations — a hard cost bound on the enumeration.
    const MAX_CASES: u128 = 1 << 22;
    let debug = bounded_mc_debug_enabled();
    let free: Vec<(String, Sort)> = smt2_export::collect_free_vars(formula).into_iter().collect();
    if debug {
        eprintln!("[BOUNDED_MC] free vars (name, sort): {free:?}");
    }

    // vcgen conjoins DEFINITIONAL equalities `var == expr` that pin each computed
    // intermediate (a bool->int `Ite` cast, a `+` sum, a `%` reduction, the xor
    // result, a checked-add overflow flag) to a function of the free inputs. Such a
    // var is FUNCTIONALLY DETERMINED: in any model the definitional conjunct forces
    // it to its defining value. So we need not (and cannot, for unbounded `Int`)
    // enumerate it — we RESOLVE it from the free-input assignment. Only the
    // truly-free, finitely-enumerable inputs are enumerated. SOUNDNESS: every model
    // assigns a defined var to its forced value (else its conjunct is false, so the
    // formula is false there anyway), so {enumerated inputs} × {forced defs} covers
    // the ENTIRE model space — all-false over it is a complete UNSAT proof.
    let defs = collect_conjunct_definitions(formula);

    // Partition the free vars: enumerate the finitely-enumerable ones WITHOUT a
    // definition; the rest must be resolvable from `defs`. A free var that is
    // neither finitely enumerable NOR defined is an unbounded free input we cannot
    // exhaust — decline (fail-closed).
    let mut domains: Vec<(String, Vec<EnumValue>)> = Vec::new();
    let mut total: u128 = 1;
    for (name, sort) in &free {
        if defs.contains_key(name) {
            continue; // resolved from its definition during evaluation
        }
        let Some(dom) = finite_domain(sort) else {
            if debug {
                eprintln!(
                    "[BOUNDED_MC] declined: free var `{name}` has non-finite sort {sort:?} and no definition"
                );
            }
            return None;
        };
        total = total.checked_mul(dom.len() as u128)?;
        if total > MAX_CASES {
            if debug {
                eprintln!("[BOUNDED_MC] declined: domain {total} exceeds budget {MAX_CASES}");
            }
            return None;
        }
        domains.push((name.clone(), dom));
    }
    if debug {
        let enumerated: Vec<&String> = domains.iter().map(|(n, _)| n).collect();
        eprintln!(
            "[BOUNDED_MC] enumerating {enumerated:?} ({total} cases); resolving {} defined vars",
            defs.len()
        );
    }

    // Mixed-radix enumeration of the full cartesian product of the enumerated
    // free-input domains.
    let n = domains.len();
    let mut idx = vec![0usize; n];
    let mut cases: u64 = 0;
    loop {
        let mut assignment: BTreeMap<String, EnumValue> = BTreeMap::new();
        for (i, (name, dom)) in domains.iter().enumerate() {
            assignment.insert(name.clone(), dom[idx[i]].clone());
        }
        // Resolve every defined var to its forced value by fixpoint (handles
        // dependency order; a cycle or an unresolvable dependency simply leaves the
        // var unbound, which makes `eval_ground` return `None` below -> decline).
        resolve_definitions(&defs, &mut assignment);

        match eval_ground(formula, &assignment) {
            // No violation in this case — continue enumerating.
            Some(EnumValue::Bool(false)) => {}
            // A satisfying assignment: the violation IS reachable, so this is not a
            // proof. Decline (fail-closed) rather than emit a refutation here — the
            // refute direction stays with ay's strict-checked SAT path.
            Some(EnumValue::Bool(true)) => {
                if debug {
                    eprintln!("[BOUNDED_MC] declined: found a satisfying assignment (not a proof)");
                }
                return None;
            }
            // A non-Bool top value or an unsupported/unresolved node: exhaustiveness
            // cannot be established for this formula. Decline.
            _ => {
                if debug {
                    eprintln!("[BOUNDED_MC] declined: formula did not reduce to a definite Bool");
                }
                return None;
            }
        }
        cases += 1;

        // Advance the mixed-radix counter; break when it wraps past the last digit.
        if n == 0 {
            break; // ground formula: the single empty assignment is the whole domain.
        }
        let mut pos = 0usize;
        let mut wrapped = false;
        loop {
            idx[pos] += 1;
            if idx[pos] < domains[pos].1.len() {
                break;
            }
            idx[pos] = 0;
            pos += 1;
            if pos == n {
                wrapped = true;
                break;
            }
        }
        if wrapped {
            break;
        }
    }

    let enumerated_free: Vec<(String, Sort)> =
        free.iter().filter(|(name, _)| !defs.contains_key(name)).cloned().collect();
    let certificate = bounded_finite_certificate(&enumerated_free, total, cases);
    if debug {
        eprintln!("[BOUNDED_MC] PROVED by exhaustion: {cases} cases all-false (domain={total})");
    }
    Some(VerificationResult::Proved {
        solver: SOLVER_NAME.into(),
        time_ms,
        strength: trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::ExhaustiveFinite(cases),
            // Complete + sound for the finite domain: the property holds for ALL
            // inputs. `Sound` (strength_order 2, == SmtBacked) satisfies the
            // static-trust bar (`proof_strength_satisfies_static_trust`:
            // !bounded && reasoning.is_complete() && assurance >= Sound).
            assurance: trust_types::AssuranceLevel::Sound,
        },
        proof_certificate: Some(certificate.into_bytes()),
        solver_warnings: None,
        native_proof_envelope: None,
    })
}

/// The finitely-enumerable value domain for a sort, or `None` when the sort is not
/// finite-and-enumerable here (so the caller declines, fail-closed). `Bool` is the
/// only sort enumerated: it covers the free inputs / flags of a bounded functional
/// assert. Other sorts (`Int`, `Array`, `Float`, datatypes, …) are NOT enumerated —
/// an unbounded `Int` cannot be exhausted, and the rest are out of this route's
/// scope — so the proof is declined rather than risk an incomplete domain.
fn finite_domain(sort: &Sort) -> Option<Vec<EnumValue>> {
    match sort {
        Sort::Bool => Some(vec![EnumValue::Bool(false), EnumValue::Bool(true)]),
        _ => None,
    }
}

/// Evaluate a GROUND formula (every leaf either a literal or a variable bound in
/// `env`) to a concrete [`EnumValue`]. Returns `None` for any node this evaluator
/// does not handle, or any sub-term that is not well-typed for the operator — the
/// caller treats `None` as "cannot establish exhaustiveness" and declines, so a
/// gap here can only LOSE a proof, never manufacture a false one.
///
/// Integer arithmetic uses checked `i128` ops (`%`/`/` reject a zero divisor):
/// an overflow or division-by-zero yields `None` (decline) rather than a wrong
/// value. Mathematical `Int` semantics match the SMT `Int` theory the LIA
/// violation formula is built in.
fn eval_ground(formula: &Formula, env: &BTreeMap<String, EnumValue>) -> Option<EnumValue> {
    use EnumValue::{Bool, Int};
    Some(match formula {
        Formula::Bool(b) => Bool(*b),
        Formula::Int(v) => Int(*v),
        Formula::UInt(v) => Int(i128::try_from(*v).ok()?),
        Formula::BitVec { value, .. } => Int(*value),
        Formula::Var(name, _) => env.get(name)?.clone(),
        Formula::SymVar(sym, _) => env.get(sym.as_str())?.clone(),
        Formula::Not(a) => Bool(!eval_bool(a, env)?),
        Formula::And(terms) => {
            let mut acc = true;
            for t in terms {
                acc &= eval_bool(t, env)?;
            }
            Bool(acc)
        }
        Formula::Or(terms) => {
            let mut acc = false;
            for t in terms {
                acc |= eval_bool(t, env)?;
            }
            Bool(acc)
        }
        Formula::Implies(a, b) => Bool(!eval_bool(a, env)? || eval_bool(b, env)?),
        Formula::Eq(a, b) => Bool(eval_equal(&eval_ground(a, env)?, &eval_ground(b, env)?)?),
        Formula::Lt(a, b) => Bool(eval_int(a, env)? < eval_int(b, env)?),
        Formula::Le(a, b) => Bool(eval_int(a, env)? <= eval_int(b, env)?),
        Formula::Gt(a, b) => Bool(eval_int(a, env)? > eval_int(b, env)?),
        Formula::Ge(a, b) => Bool(eval_int(a, env)? >= eval_int(b, env)?),
        Formula::Add(a, b) => Int(eval_int(a, env)?.checked_add(eval_int(b, env)?)?),
        Formula::Sub(a, b) => Int(eval_int(a, env)?.checked_sub(eval_int(b, env)?)?),
        Formula::Mul(a, b) => Int(eval_int(a, env)?.checked_mul(eval_int(b, env)?)?),
        Formula::Div(a, b) => {
            let d = eval_int(b, env)?;
            if d == 0 {
                return None;
            }
            Int(eval_int(a, env)?.checked_div(d)?)
        }
        Formula::Rem(a, b) => {
            let d = eval_int(b, env)?;
            if d == 0 {
                return None;
            }
            Int(eval_int(a, env)?.checked_rem(d)?)
        }
        Formula::Neg(a) => Int(eval_int(a, env)?.checked_neg()?),
        Formula::Ite(c, t, e) => {
            if eval_bool(c, env)? {
                eval_ground(t, env)?
            } else {
                eval_ground(e, env)?
            }
        }
        // Any other node (Bv*, Fp*, Select/Store, Pred, quantifiers, …) is outside
        // this evaluator: decline so the caller cannot claim a partial exhaustion.
        _ => return None,
    })
}

fn eval_bool(formula: &Formula, env: &BTreeMap<String, EnumValue>) -> Option<bool> {
    match eval_ground(formula, env)? {
        EnumValue::Bool(b) => Some(b),
        EnumValue::Int(_) => None,
    }
}

fn eval_int(formula: &Formula, env: &BTreeMap<String, EnumValue>) -> Option<i128> {
    match eval_ground(formula, env)? {
        EnumValue::Int(v) => Some(v),
        EnumValue::Bool(_) => None,
    }
}

/// Structural equality of two evaluated values, defined only between like-typed
/// operands (`Bool`/`Bool` or `Int`/`Int`). A cross-typed `Eq` is ill-formed and
/// yields `None` (decline) rather than a silent `false`.
fn eval_equal(lhs: &EnumValue, rhs: &EnumValue) -> Option<bool> {
    match (lhs, rhs) {
        (EnumValue::Bool(a), EnumValue::Bool(b)) => Some(a == b),
        (EnumValue::Int(a), EnumValue::Int(b)) => Some(a == b),
        _ => None,
    }
}

/// Collect DEFINITIONAL equalities from the top-level conjuncts of `formula`: a
/// conjunct `Eq(Var(name), rhs)` (or the symmetric `Eq(rhs, Var(name))`) defines
/// `name := rhs`. These are the vcgen-conjoined pins of computed intermediates
/// (casts, sums, `%`, the xor result, overflow flags). A name with TWO different
/// definitions is treated as undefined (removed) — resolving via one could mask the
/// other constraint, so we fall back to enumerating/declining it (fail-closed).
///
/// Only top-level conjuncts are mined (an `And`, recursively flattened). A
/// definition nested under `Or`/`Ite`/negation is NOT unconditionally true, so it
/// is not mined — leaving its var to be enumerated or to force a decline.
fn collect_conjunct_definitions(formula: &Formula) -> BTreeMap<String, Formula> {
    fn flatten<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
        match f {
            Formula::And(terms) => {
                for t in terms {
                    flatten(t, out);
                }
            }
            other => out.push(other),
        }
    }
    let mut conjuncts = Vec::new();
    flatten(formula, &mut conjuncts);

    let mut defs: BTreeMap<String, Formula> = BTreeMap::new();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    let mut consider = |name: &str, rhs: &Formula| {
        if ambiguous.contains(name) {
            return;
        }
        match defs.get(name) {
            Some(existing) if existing == rhs => {} // identical re-definition is fine
            Some(_) => {
                defs.remove(name);
                ambiguous.insert(name.to_string());
            }
            None => {
                defs.insert(name.to_string(), rhs.clone());
            }
        }
    };
    for conjunct in conjuncts {
        if let Formula::Eq(a, b) = conjunct {
            match (a.as_ref(), b.as_ref()) {
                // `var == var` is a binding either way; bind the left to the right.
                (Formula::Var(name, _), _) if !matches!(b.as_ref(), Formula::Var(n, _) if n == name) =>
                {
                    consider(name, b);
                }
                (_, Formula::Var(name, _)) => {
                    consider(name, a);
                }
                _ => {}
            }
        }
    }
    defs
}

/// Resolve every defined var in `defs` to a concrete [`EnumValue`] under the partial
/// `env` (the enumerated free-input assignment), by fixpoint. Each pass evaluates
/// any still-unresolved definition whose dependencies are now known; iteration stops
/// at a fixpoint. A var whose definition is cyclic or depends on an unresolved var
/// is simply left unbound — `eval_ground` then returns `None` for it, so the caller
/// declines (never a false proof).
fn resolve_definitions(defs: &BTreeMap<String, Formula>, env: &mut BTreeMap<String, EnumValue>) {
    loop {
        let mut progress = false;
        for (name, rhs) in defs {
            if env.contains_key(name) {
                continue;
            }
            if let Some(value) = eval_ground(rhs, env) {
                env.insert(name.clone(), value);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
}

/// Build the strict, re-checkable certificate text for an exhaustive finite-domain
/// proof. It records the enumerated free variables, the total domain cardinality,
/// and the number of cases evaluated (which equals the cardinality on a complete
/// enumeration). Re-checking is replaying the same deterministic enumeration.
fn bounded_finite_certificate(free: &[(String, Sort)], total: u128, cases: u64) -> String {
    let mut vars: Vec<String> = free.iter().map(|(n, s)| format!("{n}:{s:?}")).collect();
    vars.sort();
    format!(
        "trust-router.bounded-finite-exhaustive.v1\n\
         method: exhaustive enumeration over the complete finite free-variable domain\n\
         free_vars: [{}]\n\
         domain_cardinality: {total}\n\
         cases_evaluated: {cases}\n\
         result: violation formula evaluated to false on every assignment (UNSAT over the finite domain)\n\
         recheck: re-run the same deterministic enumeration — complete and sound for the finite domain\n",
        vars.join(", ")
    )
}

#[cfg(test)]
mod tests {

    /// THE FALSIFIER THAT KILLED THE FIRST DESIGN (2026-08-20, adversarial round).
    ///
    /// `And([x=1, p(x), y=1, ¬p(y)])` is UNSATISFIABLE — it says `p(1) ∧ ¬p(1)`.
    /// But its VARIABLE partition is `{x}` / `{y}`, and each of those components
    /// is independently satisfiable. The first version of this lane partitioned
    /// on variables alone, so it composed those two models and reported `Failed`
    /// with a witness `{x=1, y=1}` for an obligation that HOLDS — a build error
    /// on correct code, and a counterexample that does not exist.
    ///
    /// The uninterpreted predicate `p` is invisible to a variable partition
    /// because `build_program` declares predicates from a SEPARATE walker
    /// (`collect_pred_symbols`). The fragment gate now refuses any formula
    /// carrying one. This is the same hazard `trust_cache`'s
    /// `sub_query_splitter` documented when it refused to compose SAT results at
    /// all (T11 deleted that module as dead, 2026-10-16); it pinned it with
    /// `contradictory_predicate_partitions_cannot_synthesize_failed`, and this
    /// test, its twin on the in-process lane, now carries the pin alone.
    #[test]
    fn a_shared_uninterpreted_predicate_forbids_the_split() {
        let x = int_var("x");
        let y = int_var("y");
        let p = |arg: Formula| Formula::Pred("p".into(), vec![arg]);
        let contradictory = Formula::And(vec![
            Formula::Eq(Box::new(x.clone()), Box::new(Formula::Int(1))),
            p(x),
            Formula::Eq(Box::new(y.clone()), Box::new(Formula::Int(1))),
            Formula::Not(Box::new(p(y))),
        ]);
        assert!(
            disjoint_conjunctive_components(&contradictory).is_none(),
            "a formula carrying an uninterpreted predicate must NOT split: the \
             variable partition {{x}}/{{y}} hides that both conjuncts constrain `p`, \
             and composing their models fabricates a counterexample for an UNSAT \
             obligation"
        );
        // End to end: the lane must not manufacture a refutation for it.
        let backend = InProcessAyBackend::new().with_timeout(20_000);
        assert!(
            matches!(
                backend.try_disjoint_component_refutation(
                    &contradictory,
                    true,
                    0,
                    &ComponentRetryBudget::new(20_000)
                ),
                ComponentRetry::NotApplicable
            ),
            "and the refutation lane must decline it outright"
        );
    }

    /// GROUND conjuncts were the easier version of the same hole: two conjuncts
    /// with NO free variables are never linked by a variable union-find (the
    /// inner loop never runs), so `p(0)` and `¬p(0)` would split by
    /// construction. The fragment gate refuses them for the predicate reason;
    /// this pins the variable-free case explicitly so a future relaxation of the
    /// predicate gate cannot silently reopen it.
    #[test]
    fn variable_free_conjuncts_never_manufacture_a_split() {
        let p0 = Formula::Pred("p".into(), vec![Formula::Int(0)]);
        let ground = Formula::And(vec![p0.clone(), Formula::Not(Box::new(p0))]);
        assert!(
            disjoint_conjunctive_components(&ground).is_none(),
            "variable-free contradictory conjuncts must never split"
        );
        // And a trivially-true conjunct must not manufacture a split on an
        // otherwise single-component formula (it would inflate how often the
        // retry fires without any component to refute).
        let x = int_var("x");
        let with_true = Formula::And(vec![
            Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(1))),
            Formula::Lt(Box::new(x), Box::new(Formula::Int(9))),
            Formula::Bool(true),
        ]);
        assert!(
            disjoint_conjunctive_components(&with_true).is_none(),
            "a `Bool(true)` conjunct is not a second component"
        );
    }

    /// The FUNCTION twin of [`a_shared_uninterpreted_predicate_forbids_the_split`],
    /// with the symbol where an `Int`-valued function has to sit: UNDER a
    /// comparison. `f(x) = 1 ∧ x = 0 ∧ f(y) = 2 ∧ y = 0` is UNSAT (`f(0)` cannot
    /// be both), but its variable partition is `{x}`/`{y}` and each half is
    /// satisfiable. The fragment gate walked only the connective spine and
    /// answered at the first atom, so the `FnApp` inside `=` passed it; ay
    /// answered the whole query `unknown (incomplete self-check-rejected)`, the
    /// retry split it, and the lane reported `Failed` with the fabricated
    /// witness `{x = 0, y = 0}` (measured 2026-09-24). At ay 958c7e9ed2 ay
    /// proves this query outright, so the lane reaches the retry through this
    /// shape only on a whole-query `Unknown` (a timeout is one); the retry
    /// called directly below is what pins the retry itself, and it returned
    /// that same witness with the spine-only walk restored (2026-09-29). The
    /// nullary spelling (`c = x ∧ x = 1 ∧ c = y ∧ y = 2`) and a quantifier under
    /// an `Ite` are the same hole.
    #[test]
    fn a_function_symbol_under_an_atom_forbids_the_split() {
        let x = int_var("x");
        let y = int_var("y");
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let f =
            |arg: Formula| Formula::FnApp { func: "f".into(), args: vec![arg], sort: Sort::Int };
        let contradictory = Formula::And(vec![
            eq(f(x.clone()), Formula::Int(1)),
            eq(x.clone(), Formula::Int(0)),
            eq(f(y.clone()), Formula::Int(2)),
            eq(y.clone(), Formula::Int(0)),
        ]);
        assert!(
            disjoint_conjunctive_components(&contradictory).is_none(),
            "an FnApp under a comparison must forbid the split: both halves constrain `f`"
        );
        let backend = InProcessAyBackend::new().with_timeout(20_000);
        assert!(
            matches!(
                backend.try_disjoint_component_refutation(
                    &contradictory,
                    true,
                    0,
                    &ComponentRetryBudget::new(20_000)
                ),
                ComponentRetry::NotApplicable
            ),
            "the refutation lane must decline it outright"
        );
        let verdict = backend.run(&contradictory);
        assert!(
            !matches!(verdict, VerificationResult::Failed { .. }),
            "an UNSAT formula must never come back refuted: {verdict:?}"
        );

        let c = || Formula::FnApp { func: "c".into(), args: Vec::new(), sort: Sort::Int };
        let nullary = Formula::And(vec![
            eq(c(), x.clone()),
            eq(x.clone(), Formula::Int(1)),
            eq(c(), y.clone()),
            eq(y, Formula::Int(2)),
        ]);
        assert!(
            disjoint_conjunctive_components(&nullary).is_none(),
            "a nullary FnApp is a shared constant: the split would lose it"
        );

        let quantified_under_ite = Formula::And(vec![
            Formula::Ite(
                Box::new(Formula::Forall(
                    vec![("q".into(), Sort::Int)],
                    Box::new(Formula::Ge(
                        Box::new(Formula::Var("q".into(), Sort::Int)),
                        Box::new(x.clone()),
                    )),
                )),
                Box::new(Formula::Bool(true)),
                Box::new(Formula::Bool(false)),
            ),
            Formula::Gt(Box::new(int_var("w")), Box::new(Formula::Int(0))),
        ]);
        assert!(
            disjoint_conjunctive_components(&quantified_under_ite).is_none(),
            "a quantifier below an Ite is still a quantifier"
        );
    }

    /// The nominal split divides ordinary budgets and floors tiny ones. This
    /// tests arithmetic, not elapsed-time accounting; the shared absolute
    /// deadline is tested separately with exhausted and sub-millisecond time.
    #[test]
    fn the_retry_divides_the_budget_it_was_given() {
        // N components share the ONE budget the caller granted.
        assert_eq!(InProcessAyBackend::retry_component_timeout_ms(1_000, 2), 500);
        assert_eq!(InProcessAyBackend::retry_component_timeout_ms(5_000, 25), 200);
        // Never zero (which would mean "unbounded") just because N is large.
        assert_eq!(InProcessAyBackend::retry_component_timeout_ms(10, 25), 1);
        // An unbounded caller stays unbounded.
        assert_eq!(InProcessAyBackend::retry_component_timeout_ms(0, 4), 0);
        // A non-floored split has the aggregate bound for this example.
        // The 10/25 case above sums to 25 ms and needs the shared deadline.
        let (total, n) = (5_000u64, 25usize);
        let per = InProcessAyBackend::retry_component_timeout_ms(total, n);
        assert!(
            per * n as u64 <= total,
            "N components at {per}ms must not exceed the {total}ms the caller granted"
        );
    }

    #[test]
    fn an_expired_retry_never_dispatches_a_component() {
        let _clock = trust_types::verify_budget::VerifyBudgetGuard::install(
            Some(Instant::now() - std::time::Duration::from_secs(1)),
            u64::MAX,
        );
        let budget = ComponentRetryBudget::new(1);
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("expired_x")), Box::new(Formula::Int(1))),
            Formula::Gt(Box::new(int_var("expired_y")), Box::new(Formula::Int(1))),
        ]);
        let before = SOLVES.with(std::cell::Cell::get);
        let result =
            InProcessAyBackend::new().try_disjoint_component_refutation(&formula, true, 0, &budget);
        assert!(matches!(result, ComponentRetry::Undecided(StopCause::WallBackstop)));
        assert_eq!(SOLVES.with(std::cell::Cell::get), before, "no component reaches AY");
    }

    /// FAIL-CLOSED — the grouping must be EXACT: conjuncts that SHARE a free
    /// variable are one component, so the composition argument can never be
    /// applied to a formula whose parts constrain each other. A connected
    /// formula therefore does not split at all.
    #[test]
    fn a_connected_conjunction_never_splits() {
        let x = int_var("x");
        let connected = Formula::And(vec![
            Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(x.clone()), Box::new(Formula::Int(5))),
        ]);
        assert!(
            disjoint_conjunctive_components(&connected).is_none(),
            "conjuncts sharing `x` are ONE component — splitting them would break the \
             model-composition argument"
        );
        // Transitivity: `x~y` and `y~z` put all three conjuncts in one component,
        // even though the first and last share no variable directly.
        let y = int_var("y");
        let z = int_var("z");
        let chained = Formula::And(vec![
            Formula::Eq(Box::new(x.clone()), Box::new(y.clone())),
            Formula::Eq(Box::new(y), Box::new(z.clone())),
            Formula::Gt(Box::new(z), Box::new(Formula::Int(0))),
        ]);
        assert!(
            disjoint_conjunctive_components(&chained).is_none(),
            "sharing is TRANSITIVE — a union-find, not a pairwise check"
        );
        // And a genuinely disjoint pair does split, in two.
        let w = int_var("w");
        let disjoint = Formula::And(vec![
            Formula::Gt(Box::new(x), Box::new(Formula::Int(1))),
            Formula::Gt(Box::new(w), Box::new(Formula::Int(2))),
        ]);
        assert_eq!(disjoint_conjunctive_components(&disjoint).expect("splits").len(), 2);
    }

    /// THE LOAD-BEARING NEGATIVE — this lane can NEVER mint a trust seal. A
    /// formula with one UNSAT component IS unsatisfiable (a component's clauses
    /// are a subset of the whole), so the logic would permit `Proved` — but the
    /// artifact and the kernel/Carcara gates would then describe the COMPONENT
    /// while the seal is handed to the VC. The path returns no verdict at all in
    /// that case and the caller's `Unknown` stands.
    #[test]
    fn a_refuted_component_never_becomes_proved() {
        let x = int_var("x");
        let w = int_var("w");
        // Component A is UNSAT (`x > 10 ∧ x < 5`); component B is SAT.
        let mixed = Formula::And(vec![
            Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(x), Box::new(Formula::Int(5))),
            Formula::Gt(Box::new(w), Box::new(Formula::Int(2))),
        ]);
        assert_eq!(disjoint_conjunctive_components(&mixed).expect("splits into {x}, {w}").len(), 2);
        let backend = InProcessAyBackend::new().with_timeout(20_000);
        let retry = backend.try_disjoint_component_refutation(
            &mixed,
            true,
            0,
            &ComponentRetryBudget::new(20_000),
        );
        assert!(
            matches!(retry, ComponentRetry::Undecided(StopCause::Solved)),
            "the UNSAT component ends the retry on a verdict (a deterministic stop), and the \
             decomposition lane neither proves nor refutes; got {retry:?}"
        );
        let first = StopCause::Effort.unknown_result(SOLVER_NAME, 0, "no component verdict");
        let ComponentRetry::Undecided(cause) = retry else { unreachable!() };
        let result = crate::ay_stop::after_undecided_retry(first, cause, "component retry");
        assert!(
            matches!(result, VerificationResult::Unknown { .. }),
            "the caller's Unknown stands; got {result:?}"
        );
        assert_eq!(StopCause::of_result(&result), StopCause::Effort, "{result:?}");
    }

    /// `q = a / 2 > a` for a `u32` `a`: UNSAT, and the pinned ay's proof of it
    /// opens with a trust step, so certification refuses it.
    fn halving_conjuncts() -> Vec<Formula> {
        let (a, q) = (int_var("a"), int_var("q"));
        vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(a.clone())),
            Formula::Le(Box::new(a.clone()), Box::new(Formula::Int(4_294_967_295))),
            Formula::Eq(
                Box::new(q.clone()),
                Box::new(Formula::Div(Box::new(a.clone()), Box::new(Formula::Int(2)))),
            ),
            Formula::Gt(Box::new(q), Box::new(a)),
        ]
    }

    thread_local! {
        /// How many solves this thread ran (`solve_and_classify_with_policy`).
        pub(super) static SOLVES: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    }

    /// Run `work` and count the solves it ran.
    fn counting_solves<T>(work: impl FnOnce() -> T) -> (T, u32) {
        let before = SOLVES.with(std::cell::Cell::get);
        let answer = work();
        (answer, SOLVES.with(std::cell::Cell::get) - before)
    }

    /// Determinism acceptance (2026-10-01): an UNSAT ay's search decided and
    /// strict certification withheld is never re-solved component-wise. The
    /// retry could only certify a component's UNSAT again, under 1/n of the
    /// clock, so the clock chose the row's stop. Counted, not timed: the solves
    /// the lane ran are counted.
    #[test]
    fn a_withheld_computed_unsat_is_not_retried_component_wise() {
        use trust_types::determinism::StopItem;
        let halving = halving_conjuncts();
        let flag = Formula::Var("flag".into(), Sort::Bool);
        let whole = Formula::And(halving.iter().cloned().chain([flag]).collect());
        assert_eq!(disjoint_conjunctive_components(&whole).expect("splits").len(), 2);
        let backend = InProcessAyBackend::new().with_timeout(60_000);

        let (withheld, alone) =
            counting_solves(|| backend.solve_and_classify_with_policy(&whole, true).result);
        assert_eq!(alone, 1);
        let VerificationResult::Unknown { reason, .. } = &withheld else {
            panic!(
                "the pinned ay withholds this UNSAT; pick a shape it still refuses: {withheld:?}"
            );
        };
        assert_eq!(StopItem::from_reason(reason), Some(StopItem::UnverifiedTrustRule), "{reason}");

        let (ran, solves) = counting_solves(|| backend.run(&whole));
        assert_eq!(solves, 1, "ay's search decided the query: no component was re-solved");
        let VerificationResult::Unknown { reason, .. } = &ran else {
            panic!("still withheld: {ran:?}");
        };
        assert_eq!(StopItem::from_reason(reason), Some(StopItem::UnverifiedTrustRule), "{reason}");
        assert_eq!(StopCause::of_result(&ran), StopCause::SolverIncomplete, "{ran:?}");
    }

    /// The same gate, per component (review of the 2026-10-01 fix): a whole
    /// query this lane declines, one of whose components ay's search decides
    /// UNSAT and certification refuses. The retry ends on that component's
    /// verdict, so the row keeps the whole solve's deterministic stop. Before,
    /// the component's refusal was folded into the row: `unclassified` idle,
    /// `wall-backstop` when its 1/n of the clock cancelled the strict check.
    #[test]
    fn a_withheld_computed_unsat_component_ends_the_retry_on_its_verdict() {
        use trust_types::determinism::StopItem;
        let halving = halving_conjuncts();
        // `flag = 1` compares a Bool with an Int: declined before ay runs, so
        // the whole query is `unsupported`, a deterministic stop.
        let ill_sorted = Formula::Eq(
            Box::new(Formula::Var("flag".into(), Sort::Bool)),
            Box::new(Formula::Int(1)),
        );
        let whole = Formula::And(halving.iter().cloned().chain([ill_sorted]).collect());
        assert_eq!(disjoint_conjunctive_components(&whole).expect("splits").len(), 2);
        let backend = InProcessAyBackend::new().with_timeout(60_000);

        let InProcessSolve { result: component, decided_unsat } =
            backend.solve_and_classify_with_policy(&Formula::And(halving), true);
        let VerificationResult::Unknown { reason, .. } = &component else {
            panic!(
                "the pinned ay withholds this UNSAT; pick a shape it still refuses: {component:?}"
            );
        };
        assert_eq!(StopItem::from_reason(reason), Some(StopItem::UnverifiedTrustRule), "{reason}");
        assert!(decided_unsat, "ay's search decided the component: {reason}");

        let retry = backend.try_disjoint_component_refutation(
            &whole,
            true,
            0,
            &ComponentRetryBudget::new(20_000),
        );
        assert!(matches!(retry, ComponentRetry::Undecided(StopCause::Solved)), "{retry:?}");
        let ran = backend.run(&whole);
        assert_eq!(StopCause::of_result(&ran), StopCause::Unsupported, "{ran:?}");
    }

    /// VERDICT-NEUTRALITY — the retry is gated on `Unknown`, so a query that
    /// already decides is untouched. A plainly SAT disjoint conjunction is
    /// refuted by the ordinary whole-query path and must keep that path's
    /// verdict (this also pins that the hook cannot double-count time or
    /// re-order a decided result).
    #[test]
    fn a_decided_query_is_never_retried() {
        let x = int_var("x");
        let w = int_var("w");
        let sat_disjoint = Formula::And(vec![
            Formula::Gt(Box::new(x), Box::new(Formula::Int(1))),
            Formula::Gt(Box::new(w), Box::new(Formula::Int(2))),
        ]);
        let backend = InProcessAyBackend::new().with_timeout(20_000);
        assert!(
            matches!(
                backend.run(&sat_disjoint),
                VerificationResult::Failed { .. } | VerificationResult::Unknown { .. }
            ),
            "a decided query keeps its own verdict"
        );
    }

    /// Trust: DISJOINT-COMPONENT REFUTATION — the capability proof. Rebuild the
    /// RETRACTED mixed formula (BV violation ∧ Int out-of-range core, over
    /// disjoint variable sets) and show the split refutes what the whole-query
    /// solve cannot dispatch.
    #[test]
    fn disjoint_split_refutes_the_mixed_bv_nia_mul_query() {
        let vc = umul_record_vc_from_emitter(None, None);
        // The retracted shape: conjoin the Int out-of-range core onto the BV
        // violation, exactly as the 2026-08-19 emitter did.
        let a = Formula::Var("_3".into(), Sort::Int);
        let b = Formula::Var("_5".into(), Sort::Int);
        let prod = Formula::Mul(Box::new(a), Box::new(b));
        let or_core = Formula::Or(vec![
            Formula::Lt(Box::new(prod.clone()), Box::new(Formula::Int(0))),
            Formula::Gt(Box::new(prod), Box::new(Formula::Int(4_294_967_295))),
        ]);
        let mixed = Formula::And(vec![vc.formula.clone(), or_core]);

        let components = disjoint_conjunctive_components(&mixed).expect("splits");
        assert!(components.len() >= 2, "the mixed query must split, got {}", components.len());

        let backend = InProcessAyBackend::new().with_timeout(30_000);
        let mut mixed_vc = vc.clone();
        mixed_vc.formula = mixed;
        match backend.verify(&mixed_vc) {
            VerificationResult::Failed { counterexample, .. } => {
                let cex = counterexample.expect("the composed witness");
                let names: Vec<&str> = cex.assignments.iter().map(|(n, _)| n.as_str()).collect();
                assert!(
                    names.iter().any(|n| n.starts_with("__trust_ovf_bv_")),
                    "the witness must carry the BV component's model: {names:?}"
                );
                assert!(
                    names.iter().any(|n| *n == "_3" || *n == "_5"),
                    "and the Int component's model: {names:?}"
                );
            }
            other => panic!(
                "the disjoint split must refute the mixed BV+NIA query that the \
                 whole-query solve leaves undecided (ay: incomplete, phase \
                 theory-combination, no combined decision procedure); got {other:?}"
            ),
        }
    }

    /// Trust: THE UMUL-RECORD RETRACTION EVIDENCE (2026-08-20) — the two pins that
    /// measured the cost of restating a BV-encoded obligation in Int, and that now
    /// hold the ground truth so nobody re-lands it blind.
    ///
    /// An unsigned `var*var` checked mul is emitted in the DECIDABLE BV encoding.
    /// On 2026-08-19 an emitter change conjoined the Int-reading out-of-range core
    /// `Or([Lt(a*b,0), Gt(a*b,MAX)])` onto that formula so the trust-ir/mirsem umul
    /// arms could ground an authenticated record (one corpus row certified). This
    /// pin is what measured the price: with the Int core present ay has no
    /// combined decision procedure for the mixed QF_BV + NIA query and answers
    /// `incomplete`, phase `theory-combination`, with its executor refusal as the
    /// detail (`internal-error` before ay's AD1 fix), so an unguarded overflowing
    /// mul went from `Failed` WITH A VERIFIED COUNTEREXAMPLE (118 ms) to `Unknown`
    /// — under the prime directive, from a build error to a runtime check, across
    /// the 14 emitted `ArithmeticOverflow{Mul}` VCs (11 def_paths) that take this
    /// shape in the committed corpus. The emitter change was retracted, the
    /// DISJOINT-COMPONENT REFUTATION lane was built to refute such a query
    /// component-wise, and the record was then RE-LANDED on top of it. This pin is
    /// the load-bearing half of that pair: it asserts the refutation holds WITH the
    /// Int core present. If it goes red, the emitter conjunct must come back out —
    /// see `trust_vcgen::generate::bv_rem_mul_tests::
    /// unsigned_var_var_mul_vc_carries_authenticated_record`.
    ///
    /// THE FIX THAT MADE THE RE-LAND POSSIBLE (landed 2026-08-20): the Int core and the BV violation are over
    /// DISJOINT variable sets (`_3`/`_5` at `Sort::Int` vs `__trust_ovf_bv_*` at
    /// `Sort::BitVec`), and a conjunction of pairwise variable-disjoint components
    /// is SAT iff every component is SAT. Splitting the top-level `And` by shared
    /// free variables before dispatch is a mechanical, sound transformation local
    /// to this backend — no emitter change, no spec work, and the authentication
    /// invariant is untouched. Measured against the real backend on the RETRACTED
    /// formula: unguarded splits into 4 components, all SAT -> `Failed` + witness;
    /// rem-clamped splits into 4 of which the `{_3,_5}` component (Int ranges + rem
    /// bounds + the Or-core) is UNSAT -> `Proved`, which is STRICTLY BETTER than
    /// what this lane returns today. The `Proved` half of that measurement is still
    /// future work: the split lane deliberately mints no trust seal, so the
    /// rem-clamped case stays `Unknown` (see the sibling pin).
    #[allow(rustdoc::private_intra_doc_links)]
    ///
    /// REFUTE direction (the load-bearing one): an unguarded `a * b` at u32 CAN
    /// overflow, so the violation is SAT and the backend must refute it with a
    /// concrete witness. A regression to `Unknown` here is exactly the capability
    /// the retraction protects; a `Proved` here would be a FALSE PROVE.
    #[test]
    fn umul_bare_bv_unguarded_refutes_with_counterexample() {
        let vc = umul_record_vc_from_emitter(None, None);
        // The VC carries the re-landed UMUL RECORD, i.e. the Int core IS in the
        // solved formula — exactly the shape that cost the refutation before the
        // disjoint-component lane existed. That is the point: the capability must
        // hold WITH the conjunct present.
        assert!(
            vc.obligation.is_some(),
            "precondition of this pin: the re-landed UMUL RECORD is present, so this \
             asserts the refutation SURVIVES the mixed BV+NIA query"
        );
        let backend = InProcessAyBackend::new();
        match backend.verify(&vc) {
            VerificationResult::Failed { counterexample, .. } => {
                assert!(
                    counterexample.is_some(),
                    "the refutation must carry a witness — that is the capability"
                );
            }
            other => panic!(
                "an unguarded u32 `a*b` must be REFUTED with a counterexample; got \
                 {other:?}. If this is Unknown, something re-introduced a conjunct ay \
                 cannot dispatch (the retracted Int restatement, or another theory \
                 mix) and this VC class silently degraded from build-error to \
                 runtime-check"
            ),
        }
    }

    /// PROVE direction, pinned as the HONEST NEGATIVE it is: the rem-clamped
    /// `(a % 100) * (b % 50)` at u32 provably cannot overflow (99·49 = 4851), but
    /// this lane does NOT report `Proved`.
    ///
    /// THE ROOT CAUSE IS NOT MISSING SOLVER CAPABILITY, and the first diagnosis
    /// written here (a "90 s timeout", observed in a debug build) was wrong — the
    /// correction matters because it points the follow-up at a different component.
    /// In release ay DECIDES the bare-BV query UNSAT in ~17.6 s; the verdict is then
    /// discarded by STRICT PROOF CERTIFICATION (`strict UNSAT proof validation
    /// failed: step t1 uses unsupported theory lemma kind Generic in strict mode`),
    /// surfaced as `Unknown[(incomplete self-check-rejected)]`. So the gap is in the
    /// strict Alethe proof checker's theory-lemma coverage, not in ay's solving, and
    /// the fail-closed downgrade is working exactly as designed. A future change
    /// that makes this PROVE should flip this pin deliberately rather than silently.
    #[test]
    fn umul_bare_bv_rem_clamped_is_honestly_unknown() {
        let vc = umul_record_vc_from_emitter(Some(100), Some(50));
        let backend = InProcessAyBackend::new().with_timeout(20_000);
        let result = backend.verify(&vc);
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "if the rem-clamped mul now PROVES, the BV lane gained a real capability \
             — update this pin and the retraction write-up together; got {result:?}"
        );
    }

    /// Build the REAL unsigned `var*var` checked-mul VC through trust-vcgen, mirroring
    /// `bv_rem_mul_tests::mod_mul_func`: `_3 = a % C1; _5 = b % C2; _6 = CheckedMul(_3,_5)`
    /// (a `None` divisor leaves that operand UNBOUNDED). Driving the emitter keeps this
    /// pin honest — a stand-in formula could drift from what is actually solved.
    fn umul_record_vc_from_emitter(
        lhs_div: Option<u128>,
        rhs_div: Option<u128>,
    ) -> VerificationCondition {
        use trust_types::{
            BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, Statement,
            Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
        };
        let u32_ty = || Ty::Int { width: 32, signed: false };
        let assign = |local: usize, rvalue: Rvalue| Statement::Assign {
            place: Place::local(local),
            rvalue,
            span: SourceSpan::default(),
        };
        let rem_or_copy = |src: usize, div: Option<u128>| match div {
            Some(c) => Rvalue::BinaryOp(
                BinOp::Rem,
                Operand::Copy(Place::local(src)),
                Operand::Constant(ConstValue::Uint(c, 32)),
            ),
            None => Rvalue::Use(Operand::Copy(Place::local(src))),
        };
        let func = VerifiableFunction {
            name: "mod_mul".into(),
            def_path: "test::mod_mul".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                    LocalDecl { index: 1, ty: u32_ty(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: u32_ty(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: u32_ty(), name: None },
                    LocalDecl { index: 4, ty: Ty::Bool, name: None },
                    LocalDecl { index: 5, ty: u32_ty(), name: None },
                    LocalDecl { index: 6, ty: Ty::Tuple(vec![u32_ty(), Ty::Bool]), name: None },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![
                            assign(3, rem_or_copy(1, lhs_div)),
                            assign(5, rem_or_copy(2, rhs_div)),
                            assign(
                                6,
                                Rvalue::CheckedBinaryOp(
                                    BinOp::Mul,
                                    Operand::Copy(Place::local(3)),
                                    Operand::Copy(Place::local(5)),
                                ),
                            ),
                        ],
                        // The real MIR shape: the checked mul's overflow flag
                        // `_6.1` asserted false, which is what the emitter keys on.
                        terminator: Terminator::Assert {
                            unwind: trust_types::UnwindEdge::Unreachable,
                            cond: Operand::Copy(Place {
                                local: 6,
                                projections: vec![trust_types::Projection::Field(1)],
                            }),
                            expected: false,
                            msg: trust_types::AssertMessage::Overflow(BinOp::Mul),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 2,
                return_ty: Ty::Unit,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        };
        trust_vcgen::generate_vcs(&func)
            .into_iter()
            .find(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
            .expect("the checked mul emits an ArithmeticOverflow{Mul} VC")
    }

    use ay_bindings::{Sort as AYSort, SortInner as AYSortInner};
    use trust_types::{SourceSpan, Symbol};

    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    // Lever A: a recursive `Expr`-shaped datatype sort with a `Const(c: bv32)`
    // leaf and a binary `App(f: Expr, x: Expr)` node (children are by-name refs).
    fn expr_dt_sort() -> Sort {
        let r = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("App".into(), vec![("f".into(), r.clone()), ("x".into(), r)]),
            ],
        }
    }

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    fn boxed(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    /// `b as u8` lowering used by vcgen: `Ite(b, 1, 0)` (a mathematical-`Int` term).
    fn bool_to_int(b: &str) -> Formula {
        Formula::Ite(boxed(bool_var(b)), boxed(Formula::Int(1)), boxed(Formula::Int(0)))
    }

    /// The xor_collapse parity VIOLATION formula over two bool inputs `a`, `b`, the
    /// xor result `r`, restricted to two contributions for a compact, hand-checkable
    /// case: `r == (a ^ b)` (path def) conjoined with the NEGATED assert
    /// `!(r == (((a as u8)+(b as u8)) % 2 == 1))`. It is UNSAT — the assert is a
    /// true identity — so the bounded enumeration must PROVE it (all 2^3 cases false).
    fn parity_violation_two_inputs() -> Formula {
        let r_def = Formula::Eq(
            boxed(bool_var("r")),
            boxed(Formula::Not(boxed(Formula::Eq(boxed(bool_var("a")), boxed(bool_var("b")))))),
        );
        let sum = Formula::Add(boxed(bool_to_int("a")), boxed(bool_to_int("b")));
        let parity = Formula::Eq(
            boxed(Formula::Rem(boxed(sum), boxed(Formula::Int(2)))),
            boxed(Formula::Int(1)),
        );
        let assert_holds = Formula::Eq(boxed(bool_var("r")), boxed(parity));
        Formula::And(vec![r_def, Formula::Not(boxed(assert_holds))])
    }

    /// The bounded finite-domain route PROVES the parity functional-equality assert:
    /// every assignment of the finite (3 bool) domain evaluates the violation formula
    /// to false, so it returns a `Proved` carrying an `ExhaustiveFinite`/`Sound`
    /// strength and a strict re-checkable certificate.
    #[test]
    fn bounded_finite_proves_parity_violation_unsat() {
        let result = bounded_finite_unsat_proof(&parity_violation_two_inputs(), 0)
            .expect("finite parity violation must be proved UNSAT by exhaustion");
        match result {
            VerificationResult::Proved { strength, proof_certificate, .. } => {
                // `r` is a DEFINED var (resolved from `r == a^b`), so only the two
                // truly-free bool inputs `a`, `b` are enumerated => 2^2 = 4 cases.
                assert!(matches!(
                    strength.reasoning,
                    trust_types::ReasoningKind::ExhaustiveFinite(4)
                ));
                assert_eq!(strength.assurance, trust_types::AssuranceLevel::Sound);
                // Honors the downstream static-trust bar (complete, unbounded, >=Sound).
                assert!(!strength.is_bounded() && strength.reasoning.is_complete());
                let cert = String::from_utf8(proof_certificate.expect("certificate")).unwrap();
                assert!(cert.contains("bounded-finite-exhaustive"));
                assert!(cert.contains("cases_evaluated: 4"));
            }
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    /// The route resolves FREE `Int` temporaries that carry a definitional equality
    /// (the real xor_collapse shape: bool->int `Ite` casts pinned to the inputs),
    /// enumerating only the truly-free bool inputs. Here `t == (a as int)` and the
    /// violation `!(t == t)` is UNSAT; `t` is resolved (not enumerated), `a` is the
    /// single enumerated input => 2 cases, all false => Proved.
    #[test]
    fn bounded_finite_resolves_defined_int_temps() {
        let t_def = Formula::Eq(boxed(int_var("t")), boxed(bool_to_int("a")));
        let bad = Formula::Not(boxed(Formula::Eq(boxed(int_var("t")), boxed(int_var("t")))));
        let violation = Formula::And(vec![t_def, bad]);
        let result = bounded_finite_unsat_proof(&violation, 0)
            .expect("defined Int temp must be resolved and the formula proved UNSAT");
        match result {
            VerificationResult::Proved { strength, .. } => assert!(matches!(
                strength.reasoning,
                trust_types::ReasoningKind::ExhaustiveFinite(2)
            )),
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    /// SOUNDNESS (never false-PROVE): a genuinely SATISFIABLE finite violation
    /// formula (`a` alone — reachable at `a = true`) must DECLINE, not prove.
    #[test]
    fn bounded_finite_declines_satisfiable_violation() {
        assert!(bounded_finite_unsat_proof(&bool_var("a"), 0).is_none());
    }

    /// SOUNDNESS (never claim a partial exhaustion): a free variable over a
    /// non-finite sort (`Int`) is not enumerable, so the route DECLINES even though
    /// the formula (`x != x`) is UNSAT — the strict ay path handles it instead.
    #[test]
    fn bounded_finite_declines_non_finite_domain() {
        let unsat = Formula::Not(boxed(Formula::Eq(boxed(int_var("x")), boxed(int_var("x")))));
        assert!(bounded_finite_unsat_proof(&unsat, 0).is_none());
    }

    /// An unsupported node (here `BvAdd`) makes the evaluator decline rather than
    /// claim exhaustiveness from a partial evaluation.
    #[test]
    fn bounded_finite_declines_unsupported_node() {
        // `!(bvadd(a,a) == bvadd(a,a))` is UNSAT but uses a Bv op the evaluator does
        // not model, so the route must decline (return None), not prove.
        let bv = Formula::BvAdd(boxed(int_var("a")), boxed(int_var("a")), 8);
        let unsat = Formula::Not(boxed(Formula::Eq(boxed(bv.clone()), boxed(bv))));
        assert!(bounded_finite_unsat_proof(&unsat, 0).is_none());
    }

    fn safety_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// A minimal WARN-default subscriber standing in for rustc's global one
    /// (`rustc_log::init_logger` installs a bare `LevelFilter::WARN`
    /// subscriber even without `RUSTC_LOG`): counts every WARN-or-more-severe
    /// event that reaches it.
    struct WarnCounter(std::sync::Arc<std::sync::atomic::AtomicUsize>);

    impl tracing::Subscriber for WarnCounter {
        fn enabled(&self, metadata: &tracing::Metadata<'_>) -> bool {
            *metadata.level() <= tracing::Level::WARN
        }
        fn new_span(&self, _: &tracing::span::Attributes<'_>) -> tracing::span::Id {
            tracing::span::Id::from_u64(1)
        }
        fn record(&self, _: &tracing::span::Id, _: &tracing::span::Record<'_>) {}
        fn record_follows_from(&self, _: &tracing::span::Id, _: &tracing::span::Id) {}
        fn event(&self, _: &tracing::Event<'_>) {
            self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        fn enter(&self, _: &tracing::span::Id) {}
        fn exit(&self, _: &tracing::span::Id) {}
    }

    /// Trust (#ay-log-silence): ay's solver-internal `tracing::warn!` events
    /// must NOT reach the embedding process's ambient subscriber during an
    /// in-process solve — inside trustc, rustc's global subscriber enables
    /// WARN for all targets by default, which leaked "ay_dpll WARN" spam onto
    /// every compile's stderr. Suppressed by default; `TRUST_AY_LOG` opts back
    /// in. All phases live in ONE test so the env-var toggling cannot race a
    /// parallel test's solve.
    #[test]
    #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
    fn ay_diagnostics_suppressed_by_default_and_env_opt_in() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        use crate::ay_log::with_ay_diagnostics_policy_choice;

        let count = Arc::new(AtomicUsize::new(0));

        // (1) Mechanism: a WARN emitted inside the policy scope is dropped,
        // not forwarded to the ambient (thread-default) subscriber.
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            with_ay_diagnostics_policy_choice(false, || {
                tracing::warn!("solver-internal diagnostic");
            });
            count.load(Ordering::Relaxed)
        });
        assert_eq!(n, 0, "ay diagnostics must not reach the ambient subscriber by default");

        // (2) A REAL in-process solve leaks nothing either: whatever warns
        // ay-dpll emits internally must stay inside the policy scope.
        let backend = InProcessAyBackend::new();
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
        ]);
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            let _ = with_ay_diagnostics_policy_choice(false, || {
                backend.solve_and_classify_with_policy(&formula, true)
            });
            count.load(Ordering::Relaxed)
        });
        assert_eq!(
            n, 0,
            "an in-process ay solve must not leak WARN events to the ambient subscriber"
        );

        // (3) A resolved TRUST_AY_LOG=warn decision re-enables the flow to the
        // ambient subscriber. The value parser is covered in ay_log's unit
        // tests, so this test never mutates the process environment.
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            with_ay_diagnostics_policy_choice(true, || tracing::warn!("opted-in diagnostic"));
            count.load(Ordering::Relaxed)
        });
        assert_eq!(n, 1, "TRUST_AY_LOG=warn must let ay diagnostics through");

        // (4) An explicit off decision keeps them suppressed.
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            with_ay_diagnostics_policy_choice(false, || tracing::warn!("suppressed again"));
            count.load(Ordering::Relaxed)
        });
        assert_eq!(n, 1, "TRUST_AY_LOG=off must keep diagnostics suppressed");
    }

    /// Trust #soundness (i128 add false-PROVE repro): the signed-128 overflow
    /// violation `MIN<=a<=MAX ∧ MIN<=b<=MAX ∧ (a+b<MIN ∨ a+b>MAX)` is SAT
    /// (a=b=i128::MAX overflows), so the in-process bridge must NOT prove it.
    /// If `int_const(i128::MAX)` is treated as the solver's integer ceiling
    /// (so `a+b>i128::MAX` is vacuously false), this would falsely return
    /// Proved — exactly the fuzzer-found `fn f(a:i128,b:i128){a+b}` regression.
    #[test]
    fn i128_add_overflow_violation_is_not_proved() {
        let backend = InProcessAyBackend::new();
        let min = Formula::Int(i128::MIN);
        let max = Formula::Int(i128::MAX);
        let a = int_var("a");
        let b = int_var("b");
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));
        let range = |v: &Formula| {
            Formula::And(vec![
                Formula::Le(Box::new(min.clone()), Box::new(v.clone())),
                Formula::Le(Box::new(v.clone()), Box::new(max.clone())),
            ])
        };
        let body = Formula::And(vec![
            range(&a),
            range(&b),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum.clone()), Box::new(min.clone())),
                Formula::Gt(Box::new(sum.clone()), Box::new(max.clone())),
            ]),
        ]);
        // The shape vcgen actually emits: conjoin_arg_type_ranges wraps the
        // inner overflow body with a duplicate range per int param.
        let formula = Formula::And(vec![range(&a), range(&b), body]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "signed-128 add CAN overflow (a=b=i128::MAX), so the violation is SAT and \
             must NOT be Proved; got: {result:?}"
        );
    }

    /// (1) Trivially-UNSAT violation: x > 10 AND x < 5 has no model. The
    /// backend may return Proved only if ay's strict proof checker accepts the
    /// artifact; otherwise it must degrade to Unknown instead of handing out a
    /// trust seal.
    #[test]
    fn unsat_violation_respects_strict_proof_gate() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
        ]);
        let result = backend.verify(&safety_vc(formula));

        match &result {
            VerificationResult::Proved { solver, proof_certificate, strength, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                // Without `ay-certify`: strict-checked proof => SmtBacked
                // assurance (above the Unchecked subprocess path, below
                // kernel-Certified).
                #[cfg(not(feature = "ay-certify"))]
                {
                    assert_eq!(*strength, ProofStrength::smt_unsat_strict_checked());
                    assert_eq!(strength.assurance, trust_types::AssuranceLevel::SmtBacked);
                }
                // With `ay-certify` (D.9), this fragment reconstructs and the
                // verdict IS upgraded — but only because the row now carries a
                // typed envelope that binds to this VC and replays. Assert the
                // evidence, not merely the label: a `Certified` we cannot replay
                // is exactly what the old identity gate existed to prevent.
                #[cfg(feature = "ay-certify")]
                {
                    assert_eq!(*strength, ProofStrength::smt_unsat_certified());
                    assert_eq!(strength.assurance, trust_types::AssuranceLevel::Certified);
                    let VerificationResult::Proved {
                        native_proof_envelope: Some(envelope), ..
                    } = &result
                    else {
                        panic!("a Certified row must carry replayable evidence");
                    };
                    assert_eq!(
                        crate::ay_certify::replay_certified_envelope(
                            &safety_vc(Formula::And(vec![
                                Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
                                Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
                            ]))
                            .formula,
                            envelope
                        ),
                        crate::ay_certify::ReplayOutcome::Replayed,
                        "the end-to-end Certified row's evidence must replay against its VC"
                    );
                }
                assert!(
                    proof_certificate.as_ref().is_some_and(|bytes| !bytes.is_empty()),
                    "strict-Verified Proved must carry a non-empty proof certificate"
                );
            }
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert!(
                    reason.contains("UNSAT"),
                    "UNSAT without an accepted strict proof should explain the fail-closed downgrade: {result:?}"
                );
            }
            other => {
                panic!("UNSAT violation must be Proved or fail-closed Unknown, got: {other:?}")
            }
        }
    }

    /// The mutable-collection E4 lane lowers `xs[i] = value` to the array
    /// post-state `store(xs, i, value)`. Exercise AY's proof checker on the
    /// corresponding read-after-write theorem itself: a backend verdict is not
    /// enough for this regression; the exact solve must carry an artifact whose
    /// strict checker verdict is `Verified`.
    #[test]
    fn array_store_select_uses_a_strict_verified_ay_proof_and_tampering_refutes() {
        let backend = InProcessAyBackend::new();
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let array = Formula::Var("xs".into(), array_sort);
        let index = int_var("index");
        let value = int_var("value");
        let store =
            Formula::Store(boxed(array.clone()), boxed(index.clone()), boxed(value.clone()));
        let violation = Formula::Not(boxed(Formula::Eq(
            boxed(Formula::Select(boxed(store), boxed(index.clone()))),
            boxed(value.clone()),
        )));

        let program = backend.build_program(&violation).expect("an array VC builds a program");
        let _ay_guard = ay_exec_lock().lock().unwrap_or_else(|error| error.into_inner());
        let outcomes = execute_direct::execute_incremental(&program)
            .expect("the exact array read-after-write query must execute in-process");
        let outcome = outcomes.last().expect("the program contains one check-sat");
        assert!(
            matches!(outcome.result, ExecuteTypedResult::Verified),
            "read(store(xs, index, value), index) == value must be UNSAT as a violation: \
             {outcome:?}",
        );
        let artifact =
            outcome.unsat_proof.as_ref().expect("UNSAT must carry AY's checked proof artifact");
        assert!(
            matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "the array-theory proof must pass AY's strict proof checker: {artifact:?}",
        );
        artifact
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .expect("the strict consumer gate must accept the same checked artifact");
        drop(_ay_guard);

        // Same-sorted but different locals are not interchangeable. Changing
        // either the store index or value makes the violation satisfiable, so
        // neither tampered query may retain proof authority.
        let other_index = int_var("other_index");
        let wrong_index = Formula::Not(boxed(Formula::Eq(
            boxed(Formula::Select(
                boxed(Formula::Store(
                    boxed(array.clone()),
                    boxed(other_index),
                    boxed(value.clone()),
                )),
                boxed(index.clone()),
            )),
            boxed(value.clone()),
        )));
        let wrong_value = Formula::Not(boxed(Formula::Eq(
            boxed(Formula::Select(
                boxed(Formula::Store(
                    boxed(array),
                    boxed(index.clone()),
                    boxed(int_var("other_value")),
                )),
                boxed(index),
            )),
            boxed(value),
        )));
        for tampered in [wrong_index, wrong_value] {
            let result = backend.run_strict(&tampered);
            assert!(
                result.is_failed(),
                "a satisfiable tampered Store/Select query must be refuted, never proved: \
                 {result:?}",
            );
        }
    }

    /// Trust #soundness (round-18): Rust `%` is TRUNCATED, so the violation
    /// `r == x % 256 AND r < 0` is SATISFIABLE (x = -1 => r = -1 < 0) and must NOT
    /// be Proved. The in-process backend lowers via `ay_bridge`; if that used ay's
    /// EUCLIDEAN `int_mod` (r in [0,256) so r >= 0 always), the violation would be
    /// UNSAT and `#[ensures(result >= 0)] fn f(x:i32){ x % 256 }` would be falsely
    /// Proved. The truncated lowering keeps the violation reachable.
    #[test]
    fn truncated_rem_negative_dividend_violation_is_not_proved() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::And(vec![
            Formula::Eq(
                Box::new(int_var("r")),
                Box::new(Formula::Rem(Box::new(int_var("x")), Box::new(Formula::Int(256)))),
            ),
            Formula::Lt(Box::new(int_var("r")), Box::new(Formula::Int(0))),
        ]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "truncated `x % 256` admits a negative result (x = -1), so the violation is \
             reachable and must NOT be Proved (Euclidean int_mod would wrongly prove it); \
             got {result:?}"
        );
    }

    /// (2) SAT violation: x > 0 is satisfiable, so the violation is reachable
    /// => Failed.
    #[test]
    fn sat_violation_is_failed() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let result = backend.verify(&safety_vc(formula));

        assert!(result.is_failed(), "SAT violation must be Failed (never Proved), got: {result:?}");
        assert_eq!(result.solver_name(), SOLVER_NAME);
    }

    /// (3) The mapping returns Unknown (never Proved) when there is no
    /// strict-Verified artifact: an UNSAT outcome whose `unsat_proof` is `None`
    /// must degrade to Unknown.
    #[test]
    fn unsat_without_proof_artifact_is_unknown_not_proved() {
        // An UNSAT outcome whose `unsat_proof` is None must degrade to Unknown:
        // the soundness gate only ever yields Proved with a strict-Verified
        // artifact. (We feed None directly; ay's CheckSatOutcome /
        // UnsatProofArtifact are #[non_exhaustive] and cannot be fabricated.)
        let result = InProcessAyBackend::unsat_to_result(None, 0, &Formula::Bool(false));
        assert!(
            !result.is_proved(),
            "UNSAT without a strict proof artifact must NOT be Proved, got: {result:?}"
        );
        assert!(
            matches!(result, VerificationResult::Unknown { .. }),
            "UNSAT without a strict proof artifact must be Unknown, got: {result:?}"
        );
        // Determinism plan §3.1 (review 2026-09-29): a withheld UNSAT is never
        // `solved`. ay's strict-proof machinery is counted since P4a.1, so the
        // withholding is the proof's: `solver-incomplete`.
        assert_eq!(StopCause::of_result(&result), StopCause::SolverIncomplete, "{result:?}");
    }

    /// Review finding (2026-09-29, blocker): ay's strict-proof discharge runs
    /// its nested solves under `nested_deadline()` — now + 1 s, capped by the
    /// solve's own deadline — so on a loaded host it declines a proof an idle
    /// host accepts, and the withheld-proof rows used to say `solved` (the unit
    /// `measured`). A 1 ms timeout puts every clock in the lane past its
    /// deadline. Whatever the solver then answers — on the pinned ay the solve
    /// itself stops first (`timeout`, 0 conflicts), measured 2026-09-29 — an
    /// undecided result must never read as a deterministic stop, and it must
    /// reach the backstop ledger. The decline of a COMPLETED solve by the
    /// certification funnel is pinned separately, on the FP shapes ay refuses
    /// (`strict_checker_refusals_on_fp_stay_visible`), and at the gate itself
    /// (`unsat_without_proof_artifact_is_unknown_not_proved`).
    #[test]
    fn a_clock_starved_strict_proof_never_reads_as_a_deterministic_stop() {
        let x = int_var("x");
        let lia_unsat = Formula::And(vec![
            Formula::Gt(Box::new(x.clone()), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(x), Box::new(Formula::Int(5))),
        ]);
        let holes = 6usize;
        let var = |i: usize, j: usize| Formula::Var(format!("q_{i}_{j}").into(), Sort::Bool);
        let mut conjuncts = Vec::new();
        for i in 0..=holes {
            conjuncts.push(Formula::Or((0..holes).map(|j| var(i, j)).collect()));
        }
        for j in 0..holes {
            for i in 0..=holes {
                for k in (i + 1)..=holes {
                    conjuncts.push(Formula::Or(vec![
                        Formula::Not(Box::new(var(i, j))),
                        Formula::Not(Box::new(var(k, j))),
                    ]));
                }
            }
        }
        let pigeonhole = Formula::And(conjuncts);
        let ledger_before = in_process_noted();
        let mut undecided = 0;
        for formula in [&lia_unsat, &pigeonhole] {
            let result = InProcessAyBackend::new()
                .with_timeout(1)
                .with_effort_scale(EffortScale::BUILTIN)
                .run(formula);
            if result.is_proved() || result.is_failed() {
                continue;
            }
            undecided += 1;
            let cause = StopCause::of_result(&result);
            assert_ne!(
                cause.reproducibility(),
                trust_types::determinism::Reproducibility::Deterministic,
                "a solve whose clocks had all passed must not state a deterministic stop \
                 ({cause}): {result:?}"
            );
        }
        if undecided > 0 {
            // The ledger is process-wide and only ever grows, so concurrent
            // tests can add to it but never hide these notes.
            assert!(
                in_process_noted() >= ledger_before + undecided,
                "every clock-starved in-process result reaches the backstop ledger"
            );
        }
    }

    /// Plan-critique P1 ledger items (2026-09-30): a strict check CANCELLED by
    /// a stop mid-walk is a clock stop, named; the certification refusals are
    /// named, the proof's own (`solver-incomplete`) or a count (`effort`) since
    /// P4a.1; and a strict check ay reports STOPPED states its stop.
    #[test]
    fn a_withheld_proof_names_the_refusal_ay_states() {
        use trust_types::determinism::StopItem;
        let cancelled = strict_proof_withheld(
            4,
            "UNSAT but strict proof verdict rejected: proof validation cancelled by the caller \
             (interrupt, deadline, or memory limit)",
        );
        assert_eq!(StopCause::of_result(&cancelled), StopCause::WallBackstop, "{cancelled:?}");
        let VerificationResult::Unknown { reason, .. } = &cancelled else {
            panic!("withheld, never proved: {cancelled:?}");
        };
        assert_eq!(StopItem::from_reason(reason), Some(StopItem::StrictCheckCancelled));
        for (detail, item, cause) in [
            (
                "step t5 uses unverified trust rule",
                StopItem::UnverifiedTrustRule,
                StopCause::SolverIncomplete,
            ),
            (
                "step t2 uses unsupported theory lemma kind Generic in strict mode",
                StopItem::GenericTheoryLemma,
                StopCause::SolverIncomplete,
            ),
            (
                "proof validation resource envelope exhausted",
                StopItem::ProofCheckEnvelope,
                StopCause::Effort,
            ),
            (
                "deferred-trust discharge failed: a collected trust clause is not a standalone \
                 theory tautology AND the problem assertions could not be independently \
                 re-solved as UNSAT; certification effort exhausted (spent 13 of 10)",
                StopItem::CertificationEffort,
                StopCause::Effort,
            ),
        ] {
            let withheld = strict_proof_withheld(
                4,
                &format!("UNSAT but strict proof verdict rejected: {detail}"),
            );
            assert_eq!(StopCause::of_result(&withheld), cause, "{withheld:?}");
            let VerificationResult::Unknown { reason, .. } = &withheld else { unreachable!() };
            assert_eq!(StopItem::from_reason(reason), Some(item), "{reason}");
        }
        for (stop, cause) in [
            (StrictVerdictStop::Interrupted, StopCause::WallBackstop),
            (StrictVerdictStop::MemoryLimit { term_store: false }, StopCause::RssBackstop),
            (StrictVerdictStop::MemoryLimit { term_store: true }, StopCause::TermMemory),
        ] {
            let stopped = strict_proof_stopped(4, stop);
            assert!(matches!(stopped, VerificationResult::Unknown { .. }), "{stopped:?}");
            assert_eq!(StopCause::of_result(&stopped), cause, "{stop:?}: {stopped:?}");
        }
        let unnamed = strict_proof_withheld(4, "UNSAT but strict proof verdict was not Verified");
        let VerificationResult::Unknown { reason, .. } = &unnamed else { unreachable!() };
        assert_eq!(StopItem::from_reason(reason), None);
        assert_eq!(StopCause::of_result(&unnamed), StopCause::SolverIncomplete);
    }

    fn in_process_noted() -> u64 {
        trust_types::determinism::noted_stops()
            .iter()
            .filter(|stop| stop.lane == IN_PROCESS_AY_LANE)
            .map(|stop| stop.count)
            .sum()
    }

    #[test]
    fn predicate_applications_are_declared_for_direct_execution() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Pred(Symbol::intern("dir_open"), vec![int_var("d")]);
        let program = backend.build_program(&formula).expect("a predicate VC builds a program");
        assert_eq!(program.get_logic(), Some("QF_UFLIA"));

        let result = backend.verify(&safety_vc(formula));
        assert!(
            result.is_failed(),
            "opaque predicate violation is satisfiable and should execute directly, got: {result:?}"
        );
    }

    #[test]
    fn configured_timeout_is_encoded_into_the_exact_ay_program() {
        let formula = Formula::Bool(false);
        let bounded = InProcessAyBackend::new().with_timeout(1_234);
        let bounded_program =
            bounded.build_program(&formula).expect("a Bool VC builds a program").to_string();
        assert!(
            bounded_program.contains("(set-option :timeout 1234)"),
            "tracked timeout must reach AY's executable program: {bounded_program}"
        );

        let unbounded = InProcessAyBackend::new().with_timeout(0);
        let unbounded_program =
            unbounded.build_program(&formula).expect("a Bool VC builds a program").to_string();
        assert!(
            !unbounded_program.contains(":timeout"),
            "zero deliberately disables AY's per-query timeout: {unbounded_program}"
        );
    }

    /// Plan §3.2a: every in-process program carries its OWN query's effort
    /// count, `k · size` over the one assertion it makes, with or without a
    /// wall-clock backstop — so two queries of different sizes carry
    /// different `:rlimit` values.
    #[test]
    fn the_effort_count_is_encoded_into_the_exact_ay_program() {
        let x = || Formula::Var("x".into(), Sort::Int);
        let small = Formula::Lt(Box::new(x()), Box::new(Formula::Int(1)));
        let large = Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(1))),
            Formula::Gt(Box::new(x()), Box::new(Formula::Int(5))),
            Formula::Le(Box::new(x()), Box::new(Formula::Int(9))),
        ]);
        let scale = EffortScale { conflicts_per_node: 31 };
        let configured = InProcessAyBackend::new().with_timeout(0).with_effort_scale(scale);
        assert_eq!(configured.effort_scale(), scale);
        let mut seen = Vec::new();
        for formula in [&small, &large] {
            let size = trust_types::determinism::query_size(&[&asserted_formula(formula)]);
            let program =
                configured.build_program(formula).expect("an Int VC builds a program").to_string();
            assert!(
                program.contains(&format!("(set-option :rlimit {})", 31 * size)),
                "the query's own count must reach AY even with no clock: {program}"
            );
            assert_eq!(program.matches(":rlimit").count(), 1, "{program}");
            seen.push(31 * size);
        }
        assert_ne!(seen[0], seen[1], "two sizes, two counts");
        let builtin = InProcessAyBackend::new()
            .build_program(&Formula::Bool(false))
            .expect("a Bool VC builds a program")
            .to_string();
        assert!(
            builtin.contains(&format!(
                "(set-option :rlimit {})",
                EffortScale::BUILTIN.for_size(1).conflicts
            )),
            "{builtin}"
        );
    }

    /// Pigeonhole PHP(7,6): unsatisfiable, and far more than 10 conflicts for
    /// CDCL.
    fn pigeonhole_7_6() -> Formula {
        let holes = 6usize;
        let pigeons = holes + 1;
        let var = |i: usize, j: usize| Formula::Var(format!("p_{i}_{j}").into(), Sort::Bool);
        let mut conjuncts = Vec::new();
        for i in 0..pigeons {
            conjuncts.push(Formula::Or((0..holes).map(|j| var(i, j)).collect()));
        }
        for j in 0..holes {
            for i in 0..pigeons {
                for k in (i + 1)..pigeons {
                    conjuncts.push(Formula::Or(vec![
                        Formula::Not(Box::new(var(i, j))),
                        Formula::Not(Box::new(var(k, j))),
                    ]));
                }
            }
        }
        Formula::And(conjuncts)
    }

    /// Plan §3.7, against the linked solver: a conflict-budget stop reads as
    /// `effort`, a decided solve as `solved`.
    #[test]
    fn in_process_results_name_their_stop() {
        // The smallest scale, one conflict per term, must end PHP(7,6) on the
        // count.
        let starved = InProcessAyBackend::new()
            .with_timeout(0)
            .with_effort_scale(EffortScale { conflicts_per_node: 1 })
            .run(&pigeonhole_7_6());
        assert_eq!(
            StopCause::of_result(&starved),
            StopCause::Effort,
            "one conflict per term ends PHP(7,6) on the count: {starved:?}"
        );

        let decided = InProcessAyBackend::new().run(&Formula::Bool(false));
        assert_eq!(StopCause::of_result(&decided), StopCause::Solved, "{decided:?}");
    }

    #[test]
    fn backend_identity() {
        let backend = InProcessAyBackend::new();
        assert_eq!(backend.name(), SOLVER_NAME);
        assert_eq!(backend.role(), BackendRole::SmtSolver);
    }

    #[test]
    fn can_handle_l0_safety_kinds_only() {
        let backend = InProcessAyBackend::new();

        // Accepted L0 safety kinds.
        assert!(backend.can_handle(&safety_vc(Formula::Bool(false))));

        // UnsupportedMir is L0Safety but must be rejected.
        let unsupported = VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: "Foo".into(), detail: "bar".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!backend.can_handle(&unsupported));

        // Trust (contract-completeness inc-1): the definition-site Postcondition
        // (L1) contract obligation is now ACCEPTED — its self-contained
        // body-fact-conjoined violation formula is ay-decidable by strict UNSAT.
        // (`verify` still mints Proved only on a strict-checked UNSAT; the v1/ay
        // bridge substitutes only a Proved for this kind, never a Failed.)
        let postcondition = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(backend.can_handle(&postcondition));

        // Temporal/L2 kind must be rejected.
        let deadlock = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!backend.can_handle(&deadlock));
    }

    /// UnsupportedMir reaching verify() directly must be Unknown, never Proved.
    #[test]
    fn verify_unsupported_mir_is_unknown() {
        let backend = InProcessAyBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: "Foo".into(), detail: "bar".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    /// Free-variable collection gathers Var/SymVar and excludes quantifier-bound
    /// names so we never declare a bound variable at top level.
    #[test]
    fn free_var_collection_excludes_bound_names() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
            Formula::Forall(
                vec![("q".into(), Sort::Int)],
                Box::new(Formula::Eq(
                    Box::new(Formula::Var("q".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
        ]);
        let vars = smt2_export::collect_free_vars(&formula);
        assert!(vars.contains(&("x".to_string(), Sort::Int)), "free var x must be collected");
        assert!(
            !vars.iter().any(|(name, _)| name == "q"),
            "quantifier-bound q must not be a free var"
        );
    }

    /// The element-count ceiling the vcgen recognizer flags at (`1 << 28`). Kept
    /// local to the test so the regression does not depend on a vcgen export.
    const ALLOC_CEILING: i128 = 1 << 28;

    fn unbounded_alloc_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: "Vec::with_capacity".into(),
                count: "n".into(),
                detail: "test".into(),
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// Regression: an `UnboundedAllocation` VC must be ACCEPTED by the in-process
    /// ay backend (its kind was generated + proof-level-wired but never added to
    /// any backend's `can_handle`, so it routed to "no backend can handle this" =>
    /// `unknown`). Confirm `can_handle` now claims it so the QF_LIA `Ge(count,
    /// CEILING)` formula actually reaches the solver.
    #[test]
    fn can_handle_accepts_unbounded_allocation() {
        let backend = InProcessAyBackend::new();
        let vc = unbounded_alloc_vc(Formula::Ge(
            Box::new(int_var("n")),
            Box::new(Formula::Int(ALLOC_CEILING)),
        ));
        assert!(
            backend.can_handle(&vc),
            "UnboundedAllocation must be routable to the in-process ay backend, got rejected"
        );
    }

    /// Regression (the decisive gate): an UNGUARDED bulk allocation whose element
    /// count is bound to exactly the ceiling (`n == 1 << 28`) with the failure
    /// condition `Ge(n, CEILING)` is SATISFIABLE (n = 1 << 28 witnesses it), so the
    /// obligation must be DECIDED `Failed` (refuted with a counterexample), NOT
    /// `unknown`. This is the nn-dsl OOM shape: `Vec::with_capacity(1 << 28)` with
    /// no dominating budget check.
    #[test]
    fn unbounded_allocation_at_ceiling_is_refuted_not_unknown() {
        let backend = InProcessAyBackend::new();
        // Failure formula conjoined with the block-def binding `n == 1 << 28`.
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(ALLOC_CEILING))),
            Formula::Ge(Box::new(int_var("n")), Box::new(Formula::Int(ALLOC_CEILING))),
        ]);
        let vc = unbounded_alloc_vc(formula);
        assert!(
            backend.can_handle(&vc),
            "precondition: backend must accept the UnboundedAllocation kind"
        );
        let result = backend.verify(&vc);
        assert!(
            result.is_failed(),
            "an unguarded `1 << 28`-element allocation reaches the ceiling, so the failure \
             condition is satisfiable and the obligation must be DECIDED Failed (refuted), \
             not unknown; got {result:?}"
        );
        assert_eq!(result.solver_name(), SOLVER_NAME);
    }

    /// Regression (shift binding reaches the solver): the count is symbolic
    /// `(- end start)` where `end` is bound to a SEPARATE `Shl(1, 28)` statement
    /// reconstructed into the VC as a bitvector-bridged block-def. With `start = 0`
    /// and `end == 1 << 28`, the count is `1 << 28`, so `Ge(count, CEILING)` is
    /// satisfiable and the obligation is refuted. If the shift value did NOT reach
    /// the solver, `end` would be unconstrained and the result could not be a
    /// decisive `Failed`. The shift block-def is lowered via `try_binop_to_formula`
    /// (BvShl) and the ay bridge supports `IntToBv`/`BvShl`/`BvToInt`.
    #[test]
    fn unbounded_allocation_symbolic_shift_count_is_refuted() {
        let backend = InProcessAyBackend::new();
        // end == BvToInt(BvShl(IntToBv(1, 64), IntToBv(28, 64))) == 1 << 28.
        let shl = Formula::BvToInt(
            Box::new(Formula::BvShl(
                Box::new(Formula::IntToBv(Box::new(Formula::Int(1)), 64)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(28)), 64)),
                64,
            )),
            64,
            false,
        );
        // count == end - start, with start == 0.
        let count = Formula::Sub(Box::new(int_var("end")), Box::new(int_var("start")));
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("end")), Box::new(shl)),
            Formula::Eq(Box::new(int_var("start")), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING))),
        ]);
        let vc = unbounded_alloc_vc(formula);
        let result = backend.verify(&vc);
        assert!(
            result.is_failed(),
            "the shift-derived count `(1 << 28) - 0` reaches the ceiling, so with the shift \
             binding propagated to the solver the obligation is refuted (Failed); an unknown \
             here would mean the `_3 == 1 << 28` block-def never reached the solver; got {result:?}"
        );
    }

    /// Regression (#int2bv-ice, the `wide_unsigned_accumulator.rs` falsification
    /// fixture): the per-add overflow VC of `t += (x as u128) << 4` bridges the
    /// shift through `IntToBv`/`BvShl`/`BvToInt` at width 128 and compares the
    /// sum against the `UInt(u128::MAX)` threshold. Solving this shape used to
    /// PANIC inside ay ("Failed to declare function 'int2bv': … symbol 'int2bv'
    /// is reserved") when the strict UNSAT proof checker re-declared the
    /// int<->BV bridge ops as uninterpreted functions, ICE-ing the compiler.
    /// The violation is UNSAT (`t` and `x << 4` are bounded far below
    /// `u128::MAX`), so the backend must return Proved or fail-closed Unknown —
    /// never panic, never Failed.
    #[test]
    fn wide_unsigned_accumulator_int2bv_vc_never_panics() {
        let backend = InProcessAyBackend::new();
        // x in [0, 255] (a u8 element); t bounded by 15 prior adds of (255 << 4).
        let x_range = Formula::And(vec![
            Formula::Le(boxed(Formula::Int(0)), boxed(int_var("x"))),
            Formula::Le(boxed(int_var("x")), boxed(Formula::Int(255))),
        ]);
        let t_range = Formula::And(vec![
            Formula::Le(boxed(Formula::Int(0)), boxed(int_var("t"))),
            Formula::Le(boxed(int_var("t")), boxed(Formula::Int(15 * (255 << 4)))),
        ]);
        // (x as u128) << 4, lowered the way vcgen bridges shifts into the
        // integer VC: BvToInt(BvShl(IntToBv(x, 128), IntToBv(4, 128)), unsigned).
        let shifted = Formula::BvToInt(
            boxed(Formula::BvShl(
                boxed(Formula::IntToBv(boxed(int_var("x")), 128)),
                boxed(Formula::IntToBv(boxed(Formula::Int(4)), 128)),
                128,
            )),
            128,
            false,
        );
        // Violation: the per-add sum exceeds the UInt(u128::MAX) overflow threshold.
        let violation = Formula::Gt(
            boxed(Formula::Add(boxed(int_var("t")), boxed(shifted))),
            boxed(Formula::UInt(u128::MAX)),
        );
        let formula = Formula::And(vec![x_range, t_range, violation]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            matches!(
                result,
                VerificationResult::Proved { .. } | VerificationResult::Unknown { .. }
            ),
            "the UNSAT wide-accumulator int2bv VC must be Proved or fail-closed Unknown \
             (and must never panic / ICE / be Failed), got: {result:?}"
        );
    }

    /// Regression (#int2bv-ice, Trust-side declaration lane): a `Formula::Pred`
    /// whose name collides with a reserved ay builtin theory-operator name must
    /// be DECLINED as Unknown before `build_program` declares it — the
    /// direct-execution declaration path turns the elaborator's ReservedSymbol
    /// rejection into a panic, which would ICE the compiler.
    #[test]
    fn reserved_pred_symbol_is_declined_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Pred(Symbol::intern("int2bv"), vec![int_var("x")]);
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert!(
                    reason.contains("reserved"),
                    "the decline reason must name the reserved-symbol collision: {reason}"
                );
            }
            other => panic!(
                "a reserved predicate symbol must fail closed as Unknown (never panic, \
                 never prove), got: {other:?}"
            ),
        }
    }

    /// Regression (reserved-symbol ICE, the `fp` class): a VC VARIABLE whose
    /// name spells an ay builtin theory operator must be SOLVED, not declined
    /// and not panicked on.
    ///
    /// VC variable names are raw Rust identifiers from MIR `var_debug_info`, so
    /// `let fp = …` handed ay the reserved name `fp` (SMT-LIB's FloatingPoint
    /// literal constructor); ay's refusal to declare it surfaced as a panic in
    /// `ay_dpll::api::terms::declare_const` and a full ICE report. Before the
    /// namespace map this returned Unknown ("in-process ay solve panicked …")
    /// and printed an ICE; the same formula over a variable named `x` proved.
    /// A variable name carries no semantics, so the verdict must not depend on
    /// its spelling.
    #[test]
    fn test_reserved_named_variable_is_solved_with_the_same_verdict_as_any_other_name() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();
        // Unsatisfiable: no value is both > 10 and < 5, so the violation is
        // refuted and the obligation is Proved.
        let unsat = |name: &str| {
            Formula::And(vec![
                Formula::Gt(boxed(int_var(name)), boxed(Formula::Int(10))),
                Formula::Lt(boxed(int_var(name)), boxed(Formula::Int(5))),
            ])
        };
        let baseline = backend.verify(&safety_vc(unsat("x")));
        assert!(
            matches!(baseline, VerificationResult::Proved { .. }),
            "baseline: an UNSAT violation over a plainly-named variable must be Proved, \
             got {baseline:?}"
        );
        for name in ["fp", "default", "select", "store", "concat", "extract", "repeat", "RNE"] {
            let result = backend.verify(&safety_vc(unsat(name)));
            assert!(
                matches!(result, VerificationResult::Proved { .. }),
                "a variable named `{name}` must reach the solver and get the same verdict \
                 as `x` (no panic, no decline), got {result:?}"
            );
        }
    }

    /// The ay BOUNDARY itself must never panic on a reserved name — the
    /// namespace map means Trust no longer sends one, but a declaration ay
    /// refuses is a recoverable input error for ANY embedder and must arrive as
    /// an `ExecuteError`. This bypasses the backend's own gate and hands
    /// `execute_direct` a program that declares the reserved name `fp`
    /// directly: before `ay-bindings` checked the name, this call panicked
    /// inside `ay_dpll::api::terms::declare_const` and unwound into the caller
    /// (in trustc, one ICE report per obligation).
    #[test]
    fn test_execute_direct_reserved_declaration_returns_error_not_panic() {
        if !execute_direct::is_available() {
            return;
        }
        let mut program = AYProgram::new();
        program.set_logic("QF_LIA");
        let fp = program.declare_const("fp", AYSort::int());
        program.assert(fp.eq(ay_bindings::Expr::int_const(0)));
        program.check_sat();
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            execute_direct::execute_incremental(&program)
        }));
        match outcome {
            Ok(Err(error)) => assert!(
                error.to_string().contains("reserved"),
                "the rejection must name the reserved-symbol cause: {error}"
            ),
            Ok(Ok(outcomes)) => {
                panic!("ay must refuse to declare the reserved name `fp`, got {outcomes:?}")
            }
            Err(_) => panic!(
                "declaring a reserved symbol must surface as an ExecuteError, never a panic \
                 that unwinds into the embedding compiler"
            ),
        }
    }

    /// The namespaced solve still reports a counterexample under the SOURCE
    /// variable name, not the internal `__trust_u_` spelling ay saw: a witness
    /// nobody can match back to a local is a lost witness.
    #[test]
    fn test_reserved_named_variable_counterexample_uses_the_source_spelling() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();
        // Satisfiable: 2 < fp < 9 has witnesses, so the obligation is refuted.
        let formula = Formula::And(vec![
            Formula::Gt(boxed(int_var("fp")), boxed(Formula::Int(2))),
            Formula::Lt(boxed(int_var("fp")), boxed(Formula::Int(9))),
        ]);
        match backend.verify(&safety_vc(formula)) {
            VerificationResult::Failed { counterexample: Some(cex), .. } => {
                let names: Vec<&str> =
                    cex.assignments.iter().map(|(name, _)| name.as_str()).collect();
                assert!(
                    names.contains(&"fp"),
                    "the witness must name the source variable `fp`, got {names:?}"
                );
                assert!(
                    !names
                        .iter()
                        .any(|name| name.starts_with(ay_symbol_namespace::AY_USER_SYMBOL_PREFIX)),
                    "no namespaced spelling may leak into a counterexample: {names:?}"
                );
            }
            other => panic!("a satisfiable violation over `fp` must be refuted, got {other:?}"),
        }
    }

    /// The two ay-facing renderers must agree symbol-for-symbol: the textual
    /// transcript (`problem_smt2`, which feeds the revalidation digest and the
    /// Carcara cross-check) declares exactly the namespaced symbols the native
    /// program declares. If only one of them mapped, the Alethe proof ay
    /// produced would reference symbols the transcript never declares.
    #[test]
    fn test_problem_smt2_declares_the_same_namespaced_symbol_the_program_declares() {
        let formula = Formula::Gt(boxed(int_var("fp")), boxed(Formula::Int(10)));
        let text = problem_smt2(&formula);
        let program = InProcessAyBackend::new()
            .build_program(&formula)
            .expect("an Int VC builds a program")
            .to_string();
        let namespaced = format!("{}fp", ay_symbol_namespace::AY_USER_SYMBOL_PREFIX);
        assert!(text.contains(&namespaced), "transcript must declare `{namespaced}`: {text}");
        assert!(
            !text.contains("declare-const fp ") && !text.contains("declare-fun fp "),
            "transcript must not declare the reserved bare name `fp`: {text}"
        );
        assert!(
            program.contains(&namespaced),
            "native program must declare `{namespaced}`: {program}"
        );
    }

    /// Defense in depth (#int2bv-ice): a panic ANYWHERE inside the in-process
    /// solve must be contained by `run`'s unwind boundary and degrade to
    /// fail-closed Unknown instead of aborting the embedding compiler. The
    /// ill-sorted `BvAnd(Bool, Bool)` operand shape slips past the
    /// comparison-sort pre-check (`infer_sort` takes the BV width from the
    /// variant), then panics inside `formula_to_expr`'s `.bvand` ("bvand
    /// requires same BitVec sorts") — a stand-in for the whole solver-panic
    /// class (e.g. the reserved-symbol `declare_fun` ICE).
    #[test]
    fn solver_panic_is_contained_as_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Eq(
            boxed(Formula::BvAnd(boxed(bool_var("a")), boxed(bool_var("b")), 8)),
            boxed(Formula::IntToBv(boxed(Formula::Int(0)), 8)),
        );
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                // Either the panic is caught inside the unwind boundary and surfaced
                // ("panicked"), or — as ay's sort pre-checks have grown more complete —
                // the ill-sorted shape is now DECLINED before it can panic. Both are the
                // required fail-closed Unknown (never an ICE, never a spurious prove);
                // the pre-check path is strictly the safer of the two.
                assert!(
                    reason.contains("panicked") || reason.contains("declined"),
                    "the contained panic or pre-check decline must be surfaced in the Unknown reason: {reason}"
                );
            }
            other => panic!(
                "a solve-internal panic must be contained as fail-closed Unknown, got: {other:?}"
            ),
        }
    }

    /// Regression (trust m6 census ICE #2, f128::clamp_magnitude): a
    /// `Formula::FpFromBits { bits, eb, sb }` whose `bits` operand infers to
    /// `Sort::Int` instead of the required `Sort::BitVec(eb + sb)` — the exact
    /// shape a vcgen fallback produced for f128's magnitude-bits obligation
    /// (f128 is eb=15/sb=113, so its `bits` must be a 128-wide BitVec) — must
    /// be DECLINED as Unknown by the explicit `formula_bitcast_mismatch`
    /// pre-check named in the reason, not merely caught after a panic.
    #[test]
    fn fp_from_bits_int_operand_is_declined_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        // Quad precision (f128): eb=15, sb=113, so `bits` must be BitVec(128).
        let bad_bits = Formula::FpFromBits { bits: boxed(int_var("x")), eb: 15, sb: 113 };
        let formula = Formula::FpIsNaN(boxed(bad_bits));
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert!(
                    reason.contains("FpFromBits") && reason.contains("BitVec"),
                    "the decline reason must name the FpFromBits/BitVec mismatch: {reason}"
                );
                assert!(
                    !reason.contains("panicked"),
                    "the explicit pre-check must decline BEFORE any panic is reached: {reason}"
                );
            }
            other => panic!(
                "an Int-sorted FpFromBits bits operand must fail closed as Unknown \
                 (never panic, never prove), got: {other:?}"
            ),
        }
    }

    /// Sibling of the above for `Formula::BvExtract`: an `inner` operand that
    /// infers to `Sort::Int` (rather than a BitVec wide enough for `high`) must
    /// be declined the same way — `formula_to_expr`'s `BvExtract` arm lowers via
    /// the same infallible `Expr::extract` convenience wrapper.
    #[test]
    fn bv_extract_int_operand_is_declined_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        let bad_extract = Formula::BvExtract { inner: boxed(int_var("x")), high: 7, low: 0 };
        let formula =
            Formula::Eq(boxed(bad_extract), boxed(Formula::BitVec { value: 0, width: 8 }));
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                // The BvExtract-specific bitcast pre-check names "BvExtract"/"BitVec";
                // the more general comparison-sort pre-check (which now fires first for
                // this shape, since the ill-sorted BvExtract inner poisons the Eq's
                // operand sorts) names the sort mismatch. Either declines it fail-closed
                // as Unknown — never ICE, never prove.
                assert!(
                    (reason.contains("BvExtract") && reason.contains("BitVec"))
                        || reason.contains("sort-mismatched"),
                    "the decline reason must name the BvExtract/BitVec or sort mismatch: {reason}"
                );
                assert!(
                    !reason.contains("panicked"),
                    "the explicit pre-check must decline BEFORE any panic is reached: {reason}"
                );
            }
            other => panic!(
                "an Int-sorted BvExtract inner operand must fail closed as Unknown \
                 (never panic, never prove), got: {other:?}"
            ),
        }
    }

    // -- Lever A: recursive-datatype encoding soundness (the load-bearing gate) --
    //
    // The CARDINAL risk of datatype modeling is a false-PROVE: an encoding that
    // makes the solver context vacuously UNSAT would "prove" every obligation.
    // These tests assert through the REAL ay solver that (1) declaring a
    // datatype-sorted variable does NOT vacuously prove a satisfiable violation,
    // and (2) the program still builds well-formed (the datatype is declared
    // before the const that uses it).

    /// A program with a datatype-sorted free variable plus a SATISFIABLE integer
    /// violation (`x > 0`) must be refuted (Failed), NOT proved. If declaring the
    /// recursive `Expr` datatype poisoned the context to UNSAT, this would falsely
    /// return Proved — the exact false-PROVE the guard must prevent.
    #[test]
    fn datatype_var_does_not_vacuously_prove_a_sat_violation() {
        let backend = InProcessAyBackend::new();
        // The datatype var is unused by the violation, but it IS declared (it
        // appears as a free Var), so the preamble must declare `Expr` and a
        // const of that sort without making the context UNSAT.
        let formula = Formula::And(vec![
            // touch the datatype var so it is a free var that gets declared
            Formula::Eq(
                Box::new(Formula::Var("e".into(), expr_dt_sort())),
                Box::new(Formula::Var("e".into(), expr_dt_sort())),
            ),
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
        ]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "declaring a recursive datatype var must not vacuously prove a SAT violation \
             (x>0 is satisfiable); a Proved here is the false-PROVE we guard against; got {result:?}"
        );
    }

    /// `build_program` over a datatype-sorted var must select a datatype-capable
    /// logic and register the datatype before declaring the const.
    ///
    /// LEVER A WAS RE-POINTED 2026-09-18, and this is the consumer the old
    /// rejection note named. The assertion it carried —
    /// `logic == "ALL" || logic.contains("DT")` — still holds, because every
    /// name `trust_types::logic_lattice` now reaches from a datatype-bearing
    /// feature set contains `DT`; it is kept below as the PROPERTY, and the
    /// exact name is pinned beside it so a future re-point shows up here rather
    /// than passing silently. `QF_DT` is what this shape selects: the record is
    /// `{Datatypes}` and nothing else.
    ///
    /// WHY THE RE-POINT IS NEUTRAL FOR THIS LANE, twice over:
    /// `AYProgram::upgrade_logic_for_datatypes` leaves a `DT`-spelled logic
    /// alone (it only widens a NON-datatype name to `ALL`), and
    /// `ay_bindings::execute_direct::logic::parse_logic` maps every name
    /// containing `DT` to `Logic::All` before ay routes — so the solve is
    /// byte-identical to the `ALL` it used to get, which is what the
    /// measurement found on 8 queries × 19 names.
    #[test]
    fn datatype_var_program_uses_datatype_capable_logic() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
        );
        let program = InProcessAyBackend::new()
            .build_program(&formula)
            .expect("a full recursive datatype definition registers cleanly");
        let logic = program.get_logic().expect("a logic must be set");
        assert!(
            logic == "ALL" || logic.contains("DT"),
            "a datatype-bearing VC must use a datatype-capable logic, got: {logic}"
        );
        // `expr_dt_sort()` is the FULL `Expr` definition, whose `Const` field
        // is a `(_ BitVec 32)`; `logic_lattice::sort_theories` follows a
        // datatype into its field sorts, so the record is
        // `{Datatypes, BitVectors}` and the attested SMT-LIB name for it is
        // `QF_UFBVDT`. (A BY-NAME reference carries no fields and heads
        // `QF_DT`.)
        assert_eq!(
            logic, "QF_UFBVDT",
            "Lever A re-pointed: a datatype-bearing VC heads the attested SMT-LIB name for \
             its own record, not the top"
        );
        // …and `native_lane_logic` leaves it alone, because `parse_logic`'s
        // `contains("DT")` RULE accepts every name a datatype-bearing set can
        // reach. The guard is a no-op for this whole family by construction,
        // not by measurement of each name.
        assert_eq!(logic, crate::smt2_export::detect_logic(&formula));
        assert!(
            program.is_datatype_declared(&ay_symbol_namespace::escape_datatype_sort("Expr")),
            "the Expr datatype must be registered before any const of that sort"
        );
    }

    /// A BY-NAME datatype reference (empty constructors) lowers to ay's
    /// `DatatypeRef`, never to an opaque uninterpreted sort that would silently
    /// drop the datatype theory. With no full definition ANYWHERE in the
    /// formula the reference is dangling, so `build_program` fails closed and
    /// the backend DECLINES the obligation (Unknown: neither a proof nor a
    /// refutation) instead of declaring a constant over a stand-in sort — and
    /// the decline is NAMED, not a contained panic.
    #[test]
    fn by_name_datatype_ref_without_a_definition_is_a_dangling_ref_declined_not_panicked() {
        let by_name = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let lowered = sort_to_ay_in(&by_name, &DatatypeDefs::default(), &mut Vec::new());
        assert!(
            matches!(lowered.inner(), AYSortInner::DatatypeRef(name) if name == "Expr"),
            "a by-name reference is a DatatypeRef, not an uninterpreted sort: {lowered:?}"
        );
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), by_name.clone())),
            Box::new(Formula::Var("e".into(), by_name)),
        );
        let refused = InProcessAyBackend::new()
            .build_program(&formula)
            .err()
            .expect("a dangling datatype reference must be refused, not declared opaque");
        // The refusal is NAMED, not a formatted string: ay declined the
        // variable DECLARATION, and the error carries the offending datatype
        // and the (namespaced) symbol separately, with ay's own `SortError` as
        // its `source()`.
        match &refused {
            AyBridgeError::Datatype { node, datatype, member, .. } => {
                assert_eq!(*node, "variable", "{refused:?}");
                assert_eq!(datatype, "Expr", "{refused:?}");
                assert!(member.ends_with("_e"), "the namespaced symbol is named: {member}");
            }
            other => panic!("expected a named variable-declaration refusal, got {other:?}"),
        }
        assert!(
            refused.to_string().contains("Expr"),
            "the rendered refusal names the datatype: {refused}"
        );
        let result = InProcessAyBackend::new().verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("declined"), "{reason}");
                assert!(reason.contains("Expr"), "{reason}");
                // `catch_unwind` is not the mechanism: the gate established the
                // defect and declined before the bridge was entered.
                assert!(!reason.contains("panicked"), "must not reach catch_unwind: {reason}");
            }
            other => panic!("a dangling datatype reference must decline, got {other:?}"),
        }
    }

    /// The recursive `Expr` (`App (f Expr) (x Expr)`) registers as ONE genuinely
    /// inductive ay declaration whose back-edges are `DatatypeRef`s, and the
    /// constant over it authenticates against that declaration.
    #[test]
    fn recursive_datatype_registers_one_inductive_declaration() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
        );
        let program = InProcessAyBackend::new()
            .build_program(&formula)
            .expect("a full recursive datatype definition registers cleanly");
        assert!(program.is_datatype_declared(&ay_symbol_namespace::escape_datatype_sort("Expr")));
        let defs = DatatypeDefs::collect(&formula).expect("one Expr");
        let decls = defs.to_ay_declarations();
        assert_eq!(decls.len(), 1, "{decls:?}");
        let app = decls[0]
            .constructors
            .iter()
            .find(|c| c.name == "App")
            .expect("the App constructor is declared");
        assert!(
            app.fields.iter().all(|field| matches!(
                field.sort.inner(),
                AYSortInner::DatatypeRef(name) if name == "Expr"
            )),
            "the recursive fields are back-edge references: {app:?}"
        );
    }

    /// THE CROSS-LANE DECLARATION INVARIANT. The native lane's declaration set
    /// (`DatatypeDefs::to_ay_declarations`) and the text lane's
    /// (`smt2_export::emit_sort_preamble`, via `visit_datatype_bearing_sorts`)
    /// must name the SAME datatypes for the same formula.
    ///
    /// This is an invariant the two lanes used to assert only in prose, each
    /// walking its own private `match` over sort positions — which is exactly
    /// how a `Ctor` result sort and a `Sel` field sort came to be declared by
    /// one lane and invisible to the other. Both now read the single inventory
    /// `trust_types::smt_logic::visit_node_sort_positions`, so they agree BY
    /// CONSTRUCTION; this test is the machine-checked statement of that, so the
    /// invariant cannot go quiet if either walker is re-spelled.
    #[test]
    fn both_lanes_declare_the_same_datatype_set() {
        let e = || Formula::Var("e".into(), expr_dt_sort());
        let ground =
            Formula::Ctor { ctor: "App".into(), args: vec![e(), e()], sort: expr_dt_sort() };
        // Four shapes, each of which reaches a DIFFERENT sort position: a free
        // variable, a ground constructor's result sort, a selector's field sort
        // and a quantifier BINDER (invisible to every `children()` walk).
        let shapes: Vec<(&str, Formula)> = vec![
            ("free variable", Formula::Eq(Box::new(e()), Box::new(e()))),
            ("ground constructor", Formula::Eq(Box::new(ground.clone()), Box::new(ground.clone()))),
            (
                "nested constructor",
                Formula::Not(Box::new(Formula::Eq(
                    Box::new(Formula::Ctor {
                        ctor: "App".into(),
                        args: vec![ground.clone(), e()],
                        sort: expr_dt_sort(),
                    }),
                    Box::new(ground),
                ))),
            ),
            (
                "quantifier binder",
                Formula::Forall(
                    vec![(trust_types::Symbol::from("q"), expr_dt_sort())],
                    Box::new(Formula::Bool(true)),
                ),
            ),
        ];
        for (label, formula) in shapes {
            let defs = DatatypeDefs::collect(&formula).expect("one definition per name");
            let native: BTreeSet<String> =
                defs.to_ay_declarations().into_iter().map(|d| d.name).collect();
            let text: BTreeSet<String> = smt2_export::emit_sort_preamble(&formula)
                .into_iter()
                .filter_map(|line| {
                    line.strip_prefix("(declare-datatype ")
                        .and_then(|rest| rest.split_whitespace().next())
                        .map(str::to_string)
                })
                .collect();
            assert_eq!(native, text, "{label}: the two lanes must declare the same datatypes");
            assert!(native.contains("Expr"), "{label}: {native:?}");
        }
    }

    /// `App(e, e)` over the recursive `Expr`: the by-name `Expr` children
    /// resolve to the enclosing declaration, so the constructor over them
    /// BUILDS. Before ay's `Sort::datatype_ref`, the opaque uninterpreted child
    /// made this `App` constructor panic inside `Expr::datatype_constructor`.
    #[test]
    fn recursive_datatype_constructor_builds_in_process() {
        let e = || Formula::Var("e".into(), expr_dt_sort());
        let app = Formula::Ctor { ctor: "App".into(), args: vec![e(), e()], sort: expr_dt_sort() };
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(app.clone()), Box::new(app))));
        let program = InProcessAyBackend::new()
            .build_program(&formula)
            .expect("a recursive datatype constructor must lower to ay");
        assert!(program.is_datatype_declared(&ay_symbol_namespace::escape_datatype_sort("Expr")));
    }

    /// A datatype shape that cannot be registered at all (here: a separately
    /// declared mutual-recursion back-edge, whose reference ay does not
    /// resolve) is DECLINED BY NAME — a typed `AyBridgeError` out of
    /// `build_program` and an `Unknown` carrying the bridge refusal, never a
    /// panic caught by `catch_unwind`.
    ///
    /// The `!reason.contains("panicked")` assertion is the load-bearing one: it
    /// is what distinguishes a decline the gate established from a panic the
    /// policy wrapper contained. A contained panic still runs the
    /// process-global panic hook and leaks a false compiler-ICE diagnostic, so
    /// containment is not a substitute for input validation.
    #[test]
    fn refused_datatype_node_is_declined_by_name_not_panicked() {
        let a_ref = Sort::Datatype { name: "A".into(), constructors: Vec::new() };
        let b_sort = Sort::Datatype {
            name: "B".into(),
            constructors: vec![("mk_b".into(), vec![("a".into(), a_ref.clone())])],
        };
        let mk_b = Formula::Ctor {
            ctor: "mk_b".into(),
            args: vec![Formula::Var("a0".into(), a_ref)],
            sort: b_sort,
        };
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(mk_b.clone()), Box::new(mk_b))));
        let err = InProcessAyBackend::new()
            .build_program(&formula)
            .expect_err("a dangling datatype back-edge must be refused");
        assert!(matches!(err, AyBridgeError::Datatype { node: "declaration", .. }), "{err:?}");

        let result =
            InProcessAyBackend::new().solve_and_classify_with_policy(&formula, false).result;
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(!reason.contains("panicked"), "must not reach catch_unwind: {reason}");
                assert!(reason.contains("declined"), "must be a named decline: {reason}");
            }
            other => panic!("a refused datatype node must be Unknown, got {other:?}"),
        }
    }

    /// The in-process twin of the text lane's ground-`Ctor` regression: a
    /// formula whose ONLY datatype content is a ground constructor term has no
    /// datatype-sorted free variable, so the old free-var-keyed registration
    /// declared nothing and asserted a `Const` term over a datatype ay had
    /// never seen. `build_program` must register `Expr` and keep the logic
    /// datatype-capable.
    #[test]
    fn ground_ctor_only_datatype_is_registered_by_build_program() {
        let ground = Formula::Ctor {
            ctor: "Const".into(),
            args: vec![Formula::BitVec { value: 1, width: 32 }],
            sort: expr_dt_sort(),
        };
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(ground.clone()), Box::new(ground)),
        ]);
        assert!(
            smt2_export::collect_free_vars(&formula).iter().all(|(_, s)| !s.contains_datatype()),
            "this test is only meaningful when no FREE VAR carries a datatype sort"
        );

        let program = InProcessAyBackend::new()
            .build_program(&formula)
            .expect("a ground constructor over a full definition registers cleanly");
        let logic = program.get_logic().expect("a logic must be set");
        assert!(
            logic == "ALL" || logic.contains("DT"),
            "a ground-Ctor VC must use a datatype-capable logic, got: {logic}"
        );
        // This VC carries `{Datatypes, BitVectors, Ints, WideArith}`, and
        // SMT-LIB's only names for that mix are the `A`-leading `AUFBVDT*`
        // ones, which `trust_types::logic_lattice` declines to claim for want
        // of an [S1] declaration of their array fragment — so the honest
        // answer is still the top. Pinned so the disjunction above cannot go
        // vacuously green if a later edit re-points it.
        assert_eq!(logic, "ALL", "no attested SMT-LIB name covers DT + BV + Int");
        assert_eq!(
            logic,
            crate::smt2_export::detect_logic(&formula),
            "the text lane says the same, so the guard did not move this one either"
        );
        assert!(
            program.is_datatype_declared(&ay_symbol_namespace::escape_datatype_sort("Expr")),
            "the Ctor's datatype must be registered even with no datatype-sorted free var"
        );
    }

    /// A satisfiable datatype formula must never come back Proved. `e == e` is a
    /// TAUTOLOGY, so as a *violation* formula it is trivially SAT — the honest
    /// verdict is Failed/Unknown. Gated behind `is_available` so it is skipped
    /// where the direct ay lane is absent.
    #[test]
    fn satisfiable_datatype_formula_is_never_proved() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
        );
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "a satisfiable datatype formula must not be Proved; got {result:?}"
        );
    }

    /// `Level = zero | succ(pred: Level)`, the recursive field spelled by-name
    /// as trust-ir-contract cuts it.
    fn level_sort() -> Sort {
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![
                ("zero".into(), Vec::new()),
                ("succ".into(), vec![("pred".into(), level_ref())]),
            ],
        }
    }

    fn level_ref() -> Sort {
        Sort::Datatype { name: "Level".into(), constructors: Vec::new() }
    }

    fn level_var(name: &str) -> Formula {
        Formula::Var(name.into(), level_sort())
    }

    fn succ(arg: Formula) -> Formula {
        Formula::Ctor { ctor: "succ".into(), args: vec![arg], sort: level_sort() }
    }

    fn zero() -> Formula {
        Formula::Ctor { ctor: "zero".into(), args: Vec::new(), sort: level_sort() }
    }

    /// `(pred arg)` with the by-name field sort vcgen records.
    fn pred(arg: Formula) -> Formula {
        Formula::Sel {
            datatype: "Level".into(),
            field: "pred".into(),
            field_sort: level_ref(),
            arg: Box::new(arg),
        }
    }

    fn is_succ(arg: Formula) -> Formula {
        Formula::IsCtor { datatype: "Level".into(), ctor: "succ".into(), arg: Box::new(arg) }
    }

    /// The comparison pre-gate must PASS every well-sorted datatype equation
    /// a recursive-datatype lane emits — constructor-, selector-, tester- and
    /// `FnApp`-vs-variable, plus the by-name-vs-full spelling of one datatype
    /// — and still DECLINE a proven mismatch. Before `infer_sort` had datatype
    /// arms, every one of the first group read as `Int` vs `Level` and was
    /// declined ("VC formula has a sort-mismatched comparison") before
    /// `build_program` ever saw it.
    #[test]
    fn comparison_pre_gate_passes_well_sorted_datatype_equations() {
        let l = || level_var("l");
        let well_sorted = [
            Formula::Eq(boxed(succ(l())), boxed(l())),
            Formula::Eq(boxed(pred(succ(l()))), boxed(l())),
            Formula::Eq(boxed(is_succ(l())), boxed(Formula::Bool(true))),
            Formula::Eq(
                boxed(Formula::FnApp { func: "f".into(), args: vec![l()], sort: level_sort() }),
                boxed(l()),
            ),
            Formula::Eq(boxed(Formula::Pred("p".into(), vec![l()])), boxed(bool_var("b"))),
            // The vcgen induction-step shape: by-name binder vs full IH.
            Formula::Eq(boxed(Formula::Var("__fld_Succ_0".into(), level_ref())), boxed(l())),
            Formula::Eq(boxed(succ(l())), boxed(zero())),
        ];
        for formula in &well_sorted {
            assert!(
                formula_comparisons_well_sorted(formula),
                "the pre-gate must not decline a well-sorted equation: {formula:?}"
            );
            assert_eq!(check_formula_sort(formula), Ok(Sort::Bool), "{formula:?}");
        }
        // Proven mismatches are still declined: Int vs Level, Bool vs Level,
        // and two different datatypes.
        let mismatched = [
            Formula::Eq(boxed(int_var("n")), boxed(l())),
            Formula::Eq(boxed(is_succ(l())), boxed(l())),
            Formula::Eq(boxed(Formula::Var("e".into(), expr_dt_sort())), boxed(l())),
            Formula::Lt(boxed(succ(l())), boxed(Formula::Int(0))),
        ];
        for formula in &mismatched {
            assert!(
                !formula_comparisons_well_sorted(formula),
                "the pre-gate must decline a proven mismatch: {formula:?}"
            );
            assert!(check_formula_sort(formula).is_err(), "{formula:?}");
        }
        // Ignorance is not a mismatch: an operand the checker cannot sort
        // (`not 1`) is left to the full-formula checker, which refuses it
        // with its own structural diagnostic — the pre-gate itself stays out.
        let unsortable =
            Formula::Eq(boxed(Formula::Not(boxed(Formula::Int(1)))), boxed(bool_var("b")));
        assert!(formula_comparisons_well_sorted(&unsortable));
        assert!(check_formula_sort(&unsortable).is_err());
    }

    /// End to end through `run`: the datatype equations reach ay and are
    /// never declined by the pre-gate (a `Failed`/`Proved`/solver-side
    /// `Unknown` are all acceptable; a pre-gate decline is not), while an
    /// Int-vs-Level comparison is declined with the pre-gate's reason.
    #[test]
    fn datatype_equations_reach_the_solver_and_int_vs_level_is_declined() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();
        let l = || level_var("l");
        for formula in [
            Formula::Eq(boxed(succ(l())), boxed(l())),
            Formula::Eq(boxed(is_succ(l())), boxed(Formula::Bool(true))),
        ] {
            let result = backend.verify(&safety_vc(formula.clone()));
            if let VerificationResult::Unknown { reason, .. } = &result {
                assert!(
                    !reason.contains("sort-mismatched comparison"),
                    "the pre-gate must not decline {formula:?}: {reason}"
                );
            }
        }
        let mismatch = Formula::Eq(boxed(int_var("n")), boxed(l()));
        match backend.verify(&safety_vc(mismatch)) {
            VerificationResult::Unknown { reason, .. } => assert!(
                reason.contains("sort-mismatched comparison"),
                "an Int-vs-Level comparison is a proven mismatch: {reason}"
            ),
            other => panic!("a sort-mismatched comparison must be declined, got {other:?}"),
        }
    }

    /// A SECOND, different full definition under the name `Level`.
    fn contradictory_level_sort() -> Sort {
        Sort::Datatype {
            name: "Level".into(),
            constructors: vec![("bottom".into(), Vec::new()), ("top".into(), Vec::new())],
        }
    }

    /// Every malformed datatype shape the sort checker waves through — it
    /// judges a datatype term by the descriptor the NODE carries and never asks
    /// whether that descriptor agrees with the datatype's definition — and each
    /// one is a shape `formula_to_expr` answers with a fail-closed PANIC.
    ///
    /// Each is paired with the well-sorted formula it was derived from, so the
    /// gate is shown to reject the defect and NOT the shape.
    fn malformed_datatype_formulas() -> Vec<(&'static str, Formula, Formula)> {
        let l = || level_var("l");
        vec![
            (
                // A `Sel` whose carried field sort contradicts the descriptor:
                // `pred: Level`, spelled `Int` on the term.
                "selector `pred` of datatype `Level`",
                Formula::Eq(
                    boxed(Formula::Sel {
                        datatype: "Level".into(),
                        field: "pred".into(),
                        field_sort: Sort::Int,
                        arg: boxed(l()),
                    }),
                    boxed(int_var("n")),
                ),
                Formula::Eq(boxed(pred(l())), boxed(l())),
            ),
            (
                // A `Ctor` whose carried result sort is not a datatype at all
                // (the bridge's `unreachable!`).
                "constructor term `succ` carries result sort",
                Formula::Eq(
                    boxed(Formula::Ctor { ctor: "succ".into(), args: vec![l()], sort: Sort::Int }),
                    boxed(int_var("n")),
                ),
                Formula::Eq(boxed(succ(l())), boxed(l())),
            ),
            (
                // An argument whose established sort contradicts the field.
                "argument `pred` of constructor `succ` of datatype `Level`",
                Formula::Eq(
                    boxed(Formula::Ctor {
                        ctor: "succ".into(),
                        args: vec![int_var("n")],
                        sort: level_sort(),
                    }),
                    boxed(l()),
                ),
                Formula::Eq(boxed(succ(l())), boxed(l())),
            ),
            (
                // A constructor the definition does not declare.
                "declares no constructor `nope`",
                Formula::Eq(
                    boxed(Formula::Ctor {
                        ctor: "nope".into(),
                        args: Vec::new(),
                        sort: level_sort(),
                    }),
                    boxed(l()),
                ),
                Formula::Eq(boxed(zero()), boxed(l())),
            ),
            (
                // A constructor applied to the wrong number of arguments.
                "takes 1 argument(s), applied to 2",
                Formula::Eq(
                    boxed(Formula::Ctor {
                        ctor: "succ".into(),
                        args: vec![l(), l()],
                        sort: level_sort(),
                    }),
                    boxed(l()),
                ),
                Formula::Eq(boxed(succ(l())), boxed(l())),
            ),
            (
                // A tester applied to a non-datatype operand.
                "datatype tester `succ` of `Level` is applied to an operand of sort",
                Formula::Eq(
                    boxed(Formula::IsCtor {
                        datatype: "Level".into(),
                        ctor: "succ".into(),
                        arg: boxed(int_var("n")),
                    }),
                    boxed(Formula::Bool(true)),
                ),
                Formula::Eq(boxed(is_succ(l())), boxed(Formula::Bool(true))),
            ),
            (
                // A selector naming one datatype applied to a term of another.
                "applied to a term of datatype `Level`",
                Formula::Eq(
                    boxed(Formula::Sel {
                        datatype: "Expr".into(),
                        field: "pred".into(),
                        field_sort: level_ref(),
                        arg: boxed(l()),
                    }),
                    boxed(l()),
                ),
                Formula::Eq(boxed(pred(l())), boxed(l())),
            ),
            (
                // ONE datatype name carrying two DIFFERENT full definitions.
                // `sorts_agree` relaxes datatype equality to agreement BY NAME,
                // so at the type level this equation reads as well-sorted; only
                // the lowering guarded it before.
                "contradictory datatype definition",
                Formula::Eq(
                    boxed(l()),
                    boxed(Formula::Var("other".into(), contradictory_level_sort())),
                ),
                Formula::Eq(boxed(l()), boxed(Formula::Var("other".into(), level_sort()))),
            ),
        ]
    }

    /// The datatype pre-gate DECLINES every malformed datatype term with its
    /// OWN message, before the bridge: `formula_to_expr` answers each of these
    /// with a fail-closed panic, and `run_with_policy`'s `catch_unwind` is
    /// containment of last resort, never input validation (a caught panic still
    /// runs the process-global panic hook). The well-sorted formula each defect
    /// was derived from is NOT declined, so the gate rejects the defect and not
    /// the shape.
    #[test]
    fn malformed_datatype_terms_are_declined_by_the_gate_and_never_reach_the_bridge() {
        let backend = InProcessAyBackend::new();
        for (needle, malformed, well_sorted) in malformed_datatype_formulas() {
            // The sort checker waves it through: the defect is invisible to it.
            assert_eq!(
                check_formula_sort(&malformed),
                Ok(Sort::Bool),
                "fixture must be the shape the sort checker admits: {malformed:?}"
            );
            assert!(
                formula_comparisons_well_sorted(&malformed),
                "fixture must reach the datatype gate: {malformed:?}"
            );
            // The datatype gate names the defect.
            let reason = formula_datatype_defect(&malformed)
                .unwrap_or_else(|| panic!("the gate must decline {malformed:?}"));
            assert!(reason.contains(needle), "the gate must name `{needle}`: {reason}");
            // And the well-sorted original is untouched.
            assert_eq!(
                formula_datatype_defect(&well_sorted),
                None,
                "the gate must not decline the well-sorted original: {well_sorted:?}"
            );

            // End to end: the reason is the GATE's, never the catch_unwind
            // wrapper's — i.e. the bridge was never entered.
            match backend.verify(&safety_vc(malformed.clone())) {
                VerificationResult::Unknown { reason, .. } => {
                    assert!(
                        reason.starts_with("in-process ay declined:") && reason.contains(needle),
                        "the decline must be the gate's, naming `{needle}`: {reason}"
                    );
                    assert!(
                        !reason.contains("panicked"),
                        "no panic may be caught for {malformed:?}: {reason}"
                    );
                }
                other => panic!("a malformed datatype term must be declined, got {other:?}"),
            }
        }
    }

    /// Run `body` and return its value with the number of panics raised on
    /// THIS thread while it ran.
    ///
    /// This is the direct observation that the ay bridge was never entered:
    /// `formula_to_expr`'s fail-closed refusal of a malformed or undeclarable
    /// datatype term IS a panic, and `run_with_policy`'s `catch_unwind` turns
    /// it into an `Unknown` whose reason merely mentions it. Reading the reason
    /// tests the wording; counting the hook tests the fact — and the hook is
    /// also the thing that makes a caught panic leak a false
    /// compiler-ICE-looking diagnostic to stderr, which is why "contained by
    /// catch_unwind" is not the same as "never happened".
    ///
    /// `cargo test` runs the rest of the suite CONCURRENTLY, so only panics
    /// raised on THIS thread count (the backend's `catch_unwind` never leaves
    /// it). Without that filter another test's contained panic lands in this
    /// test's count and the assertion flakes — measured: 8 foreign panics
    /// counted in one concurrent run. The counting is thread-local state read
    /// by one process-wide dispatcher ([`crate::test_panic_hook`]), NOT a swap
    /// of the global hook: this helper used to take and restore the hook
    /// itself, and interleaved with a silencing probe on another thread that
    /// swap left the silencer installed for the rest of the run, so every
    /// later failing test printed no message (TRUST-25).
    fn counting_panics<R>(body: impl FnOnce() -> R) -> (R, usize) {
        crate::test_panic_hook::count_panics(body)
    }

    /// `Level` spelled BY NAME in a *term* position, with the definition
    /// nowhere in the formula.
    fn dangling_zero() -> Formula {
        Formula::Ctor { ctor: "zero".into(), args: Vec::new(), sort: level_ref() }
    }

    /// The residual class the round-9 verifier caught: a datatype term whose
    /// sort is spelled BY NAME, with NO full definition anywhere in the formula
    /// and NO by-name-sorted free variable.
    ///
    /// The free-variable clause is what made this class survive every earlier
    /// gate. `build_program` refuses a dangling reference *fallibly* only where
    /// one reaches a DECLARATION — `try_declare_const` for a free variable,
    /// `try_declare_datatype` for a definition — and these formulas declare
    /// nothing datatype-sorted. The reference is therefore first met in a TERM
    /// position, where ay-bindings' datatype API is infallible and asserts. The
    /// bridge closes that itself now (it establishes the dangling reference
    /// before lowering), but this gate is what keeps the decline attributable:
    /// it names the undefined datatype, and the bridge is never entered.
    fn undefined_by_name_datatype_formulas() -> Vec<Formula> {
        vec![
            // A ground constructor term, the shape with no variables at all.
            Formula::Eq(boxed(dangling_zero()), boxed(dangling_zero())),
            // A nested constructor: the by-name sort is on both the outer term
            // and its argument.
            Formula::Eq(
                boxed(Formula::Ctor {
                    ctor: "succ".into(),
                    args: vec![dangling_zero()],
                    sort: level_ref(),
                }),
                boxed(dangling_zero()),
            ),
            // A selector whose field sort is the by-name reference too.
            Formula::Eq(
                boxed(Formula::Sel {
                    datatype: "Level".into(),
                    field: "pred".into(),
                    field_sort: level_ref(),
                    arg: boxed(dangling_zero()),
                }),
                boxed(dangling_zero()),
            ),
            // A tester over a by-name-sorted ground term, conjoined with a
            // plain Int obligation so the formula is not datatype-only.
            Formula::And(vec![
                Formula::Eq(boxed(int_var("n")), boxed(Formula::Int(0))),
                Formula::IsCtor {
                    datatype: "Level".into(),
                    ctor: "succ".into(),
                    arg: boxed(dangling_zero()),
                },
            ]),
        ]
    }

    /// The gate DECLINES a by-name datatype reference with no definition
    /// anywhere, naming the undefined datatype — and the bridge is never
    /// entered, proven by a counting panic hook that must see ZERO panics.
    ///
    /// Before this gate these formulas reached `formula_to_expr`, panicked, and
    /// were rescued only by `run_with_policy`'s `catch_unwind`: the obligation
    /// still ended as `Unknown`, but through containment rather than
    /// validation, with the process-global panic hook run on the way.
    #[test]
    fn undefined_by_name_datatype_is_declined_by_the_gate_and_never_reaches_the_bridge() {
        let backend = InProcessAyBackend::new();
        for formula in undefined_by_name_datatype_formulas() {
            // The fixture is exactly the residual shape: the sort checker
            // admits it, the comparison pre-gate passes it, and NO free
            // variable carries a datatype sort, so `build_program`'s fallible
            // declaration seam can never be the thing that refuses it.
            assert_eq!(
                check_formula_sort(&formula),
                Ok(Sort::Bool),
                "fixture must be a shape the sort checker admits: {formula:?}"
            );
            assert!(
                formula_comparisons_well_sorted(&formula),
                "fixture must reach the datatype gate: {formula:?}"
            );
            assert!(
                smt2_export::collect_free_vars(&formula)
                    .iter()
                    .all(|(_, sort)| !sort.contains_datatype()),
                "fixture is only the residual class when NO free var carries a datatype \
                 sort: {formula:?}"
            );
            assert!(
                DatatypeDefs::collect(&formula)
                    .expect("no definition to conflict")
                    .get("Level")
                    .is_none(),
                "fixture must carry no full definition of Level: {formula:?}"
            );

            // The gate names the undefined datatype.
            let reason = formula_datatype_defect(&formula)
                .unwrap_or_else(|| panic!("the gate must decline {formula:?}"));
            assert!(
                reason.contains("undefined datatype `Level`"),
                "the gate must name the undefined datatype: {reason}"
            );

            // End to end, under a counting panic hook: the decline is the
            // GATE's, and the bridge was never entered.
            let (result, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
            assert_eq!(
                panics, 0,
                "the bridge must never be entered for {formula:?}; got {result:?}"
            );
            match result {
                VerificationResult::Unknown { reason, .. } => {
                    assert!(
                        reason.starts_with("in-process ay declined:")
                            && reason.contains("undefined datatype `Level`"),
                        "the decline must be the gate's, naming the datatype: {reason}"
                    );
                    assert!(!reason.contains("panicked"), "no panic may be caught: {reason}");
                }
                other => panic!("an undefined datatype must be declined, got {other:?}"),
            }
        }
    }

    /// A by-name reference whose definition IS present somewhere in the formula
    /// is NOT the defect above: the gate resolves it through the same table
    /// `build_program` lowers from, so the legitimate by-name-vs-full pairing
    /// trust-ir-contract and trust-vcgen emit stays admitted.
    #[test]
    fn a_by_name_reference_with_its_definition_present_is_not_declined() {
        let paired = [
            // The vcgen induction-step shape: by-name binder vs full IH.
            Formula::Eq(
                boxed(Formula::Var("__fld_Succ_0".into(), level_ref())),
                boxed(level_var("l")),
            ),
            // `Sel::field_sort` by name, operand carrying the definition.
            Formula::Eq(boxed(pred(level_var("l"))), boxed(level_var("l"))),
            // A ground by-name constructor next to a full-spelling variable.
            Formula::Eq(boxed(dangling_zero()), boxed(level_var("l"))),
            // The recursive definition's own back-edge field is a by-name
            // reference to the datatype being defined.
            Formula::Eq(boxed(succ(level_var("l"))), boxed(zero())),
        ];
        for formula in &paired {
            assert_eq!(check_formula_sort(formula), Ok(Sort::Bool), "{formula:?}");
            assert_eq!(
                formula_datatype_defect(formula),
                None,
                "a by-name reference whose definition is present must not be declined: \
                 {formula:?}"
            );
            let defs = DatatypeDefs::collect(formula).expect("one Level");
            assert_eq!(undefined_datatype_reference(formula, &defs), None, "{formula:?}");
        }
    }

    // ── The unhandled-variant class: `Formula::FnApp` (round 10) ────────────

    /// A `(Level) -> Level` uninterpreted function application, the shape the
    /// recursive-datatype lanes emit as `Eq(_0, FnApp(reference, …))`.
    fn level_fn_app(arg: Formula) -> Formula {
        Formula::FnApp { func: "vc_ref_level".into(), args: vec![arg], sort: level_sort() }
    }

    /// THE regression. `Eq(FnApp(f, [l]), l)` is well sorted, passes the
    /// comparison pre-gate, the sort checker, the datatype gate and every
    /// reserved-symbol gate — and then had NO arm in `formula_to_expr_in`, so
    /// it fell through to `unreachable!("unhandled Formula variant")` INSIDE
    /// the bridge. The obligation still came back `Unknown`, but through
    /// `run_with_policy`'s `catch_unwind` rather than through any decision: the
    /// process-global panic hook ran on the way, which is how a contained panic
    /// leaks a false compiler-ICE-looking diagnostic to stderr.
    ///
    /// `FnApp` is CONSTRUCTED IN PRODUCTION — trust-vcgen mints it as a Skolem
    /// term and as the reference side of the `model = reference` postconditions
    /// (`fuel_outcome_functional`, `mutual_recursive_datatype_functional`,
    /// `threaded_budget_functional`), which trust-certify parses back — so this
    /// is a live path, not a hypothetical one.
    ///
    /// The outcome must now come from the LOWERING: zero panics, and the
    /// obligation must not be declined by any gate either.
    #[test]
    fn fn_app_reaches_the_solver_through_its_lowering_not_through_catch_unwind() {
        let formula = Formula::Eq(boxed(level_fn_app(level_var("l"))), boxed(level_var("l")));

        // The fixture is exactly the residual shape the verifier described:
        // every pre-gate admits it, so the bridge is what it reaches.
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "{formula:?}");
        assert!(formula_comparisons_well_sorted(&formula), "the pre-gate must pass it");
        assert_eq!(formula_datatype_defect(&formula), None, "the datatype gate must pass it");
        assert_eq!(uninterpreted_signature_conflict(&formula), None, "one signature, no conflict");
        assert!(is_lowerable_formula(&formula), "the bridge must have an arm for it now");

        // The function symbol is DECLARED — at its applied argument sorts and
        // its carried RESULT sort, not at `Bool` and not at all-`Int`.
        let (arg_sorts, result) = uninterpreted_symbol_signatures(&formula)
            .remove("vc_ref_level")
            .expect("the FnApp symbol must be collected for declaration");
        assert!(matches!(arg_sorts.as_slice(), [Sort::Datatype { name, .. }] if name == "Level"));
        assert!(matches!(&result, Sort::Datatype { name, .. } if name == "Level"));
        let smt2 = problem_smt2(&formula);
        assert!(
            smt2.contains("declare-fun") && smt2.contains("vc_ref_level"),
            "the canonical transcript must declare the function symbol too: {smt2}"
        );

        // End to end, under a counting panic hook: ZERO panics, and the verdict
        // is not a decline.
        let backend = InProcessAyBackend::new();
        let (result, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
        assert_eq!(panics, 0, "the bridge must not panic on an FnApp; got {result:?}");
        if let VerificationResult::Unknown { reason, .. } = &result {
            assert!(!reason.contains("panicked"), "no panic may be caught: {reason}");
            assert!(
                !reason.contains("in-process ay declined:"),
                "a well-sorted FnApp must not be declined: {reason}"
            );
        }
    }

    /// The declaration side of the same fix, for the sibling `Pred` shape: an
    /// out-of-vocabulary predicate applied to a DATATYPE term used to be
    /// declared `(declare-fun p (Int) Bool)` from a fabricated all-`Int`
    /// fallback and then applied to a `Level` argument — a sort mismatch ay
    /// answers inside the PANICKING `uf::apply`. Declaring what is actually
    /// applied removes the mismatch instead of catching it.
    #[test]
    fn an_out_of_vocabulary_predicate_is_declared_at_the_sorts_it_is_applied_at() {
        let formula = Formula::Eq(
            boxed(Formula::Pred("vc_level_seen".into(), vec![level_var("l")])),
            boxed(bool_var("b")),
        );
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool));
        let (arg_sorts, result) = uninterpreted_symbol_signatures(&formula)
            .remove("vc_level_seen")
            .expect("predicate symbols are declared too");
        assert!(
            matches!(arg_sorts.as_slice(), [Sort::Datatype { name, .. }] if name == "Level"),
            "the declaration must follow the APPLICATION, not a fabricated Int: {arg_sorts:?}"
        );
        assert_eq!(result, Sort::Bool, "a predicate is Bool by definition");
        assert_eq!(uninterpreted_signature_conflict(&formula), None);

        let backend = InProcessAyBackend::new();
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
        assert_eq!(panics, 0, "declaring the applied sorts must remove the panic; got {verdict:?}");
        if let VerificationResult::Unknown { reason, .. } = &verdict {
            assert!(!reason.contains("panicked"), "{reason}");
        }
    }

    /// A NULLARY uninterpreted symbol beside a free variable is DECIDED.
    ///
    /// Measured 2026-09-24 before the fix, on every one of these: `Unknown` —
    /// "constraint execution failed: invalid argument to
    /// assert_term_with_source: source does not reconstruct the native
    /// assertion". The bridge lowered `c` (a zero-argument `FnApp`, or a
    /// zero-argument `Pred`) to an ay APPLICATION with no arguments and the
    /// program declared it with `declare_fun(c, [], S)`; ay executes that as
    /// an application term, while its elaborator reads the retained source's
    /// bare `c` as the declared CONSTANT, so the two `TermId`s differed and the
    /// retained-source guard refused the assertion. Only a query that folded
    /// to a literal on both sides (`c = 1 ∧ ¬(c = 1)`) got through. The
    /// symbol is now a constant on both halves — lowered as one and declared
    /// as one — so each shape reaches the solver and gets the verdict its
    /// truth demands, worked out by hand below.
    #[test]
    fn a_nullary_symbol_beside_a_variable_is_decided() {
        let eq = |a: Formula, b: Formula| Formula::Eq(boxed(a), boxed(b));
        let y = || Formula::Var("y".into(), Sort::Int);
        let fzero = || Formula::FnApp { func: "fzero".into(), args: Vec::new(), sort: Sort::Int };
        let dropped = || Formula::Pred("priv_dropped".into(), Vec::new());
        let backend = InProcessAyBackend::new();

        // SAT: `fzero` and `y` are both free. The model binds the variable AND
        // the constant, exactly as the text lane's `(get-model)` reports every
        // 0-ary `define-fun`.
        let sat = Formula::And(vec![eq(fzero(), Formula::Int(1)), eq(y(), Formula::Int(2))]);
        match backend.run(&sat) {
            VerificationResult::Failed { counterexample: Some(cex), .. } => {
                let bound: Vec<(&str, &CounterexampleValue)> =
                    cex.assignments.iter().map(|(name, value)| (name.as_str(), value)).collect();
                assert_eq!(
                    bound,
                    [("fzero", &CounterexampleValue::Int(1)), ("y", &CounterexampleValue::Int(2))],
                    "the witness is the one model the formula admits"
                );
            }
            other => panic!("`fzero = 1 ∧ y = 2` is satisfiable and must be refuted: {other:?}"),
        }

        // UNSAT through the variable: `fzero = y ∧ y = 2 ∧ fzero ≠ 2`.
        let unsat = Formula::And(vec![
            eq(fzero(), y()),
            eq(y(), Formula::Int(2)),
            Formula::Not(boxed(eq(fzero(), Formula::Int(2)))),
        ]);
        let verdict = backend.run(&unsat);
        assert!(
            matches!(verdict, VerificationResult::Proved { .. }),
            "`fzero = y ∧ y = 2 ∧ fzero ≠ 2` is UNSAT and strict-provable: {verdict:?}"
        );

        // The nullary PREDICATE twin: `priv_dropped ∧ y = 2` is satisfiable.
        let pred_sat = Formula::And(vec![dropped(), eq(y(), Formula::Int(2))]);
        let verdict = backend.run(&pred_sat);
        assert!(
            matches!(verdict, VerificationResult::Failed { counterexample: Some(_), .. }),
            "`priv_dropped ∧ y = 2` is satisfiable and must be refuted: {verdict:?}"
        );

        // A nullary symbol at a DATATYPE result sort is declared from the one
        // definition table, like a variable of that sort.
        let base = Formula::FnApp { func: "base".into(), args: Vec::new(), sort: level_sort() };
        let level_sat = Formula::And(vec![eq(base, zero()), eq(y(), Formula::Int(2))]);
        let verdict = backend.run(&level_sat);
        assert!(
            matches!(verdict, VerificationResult::Failed { .. }),
            "`base = Zero ∧ y = 2` is satisfiable and must be refuted: {verdict:?}"
        );
    }

    /// A nullary symbol spelled like an ESCAPED variable stays a SECOND symbol:
    /// the query is refuted with a witness that binds both, never proved.
    ///
    /// `x = 1 ∧ __trust_u_x = 2` and `p ∧ ¬__trust_u_p` are both satisfiable:
    /// each pairs a variable with an independent nullary symbol. The variable
    /// escape maps `x` to `__trust_u_x`, and the nullary symbol is lowered and
    /// declared as an ay CONSTANT, in the table the escaped variables live in,
    /// where ay's native declaration is get-or-declare. So if the namespace let
    /// the function keep its spelling, the program ay solves would be
    /// `x = 1 ∧ x = 2` / `p ∧ ¬p`: UNSAT, and a false `Proved` (measured
    /// 2026-09-25, before the namespace re-prefixed `__trust_` function names).
    /// `escape_function_symbol` moves the function under `__trust_n_`, so the
    /// two stay apart, and the witness decodes both to their source spellings.
    #[test]
    fn a_nullary_symbol_spelled_like_an_escaped_variable_stays_a_second_symbol() {
        let eq = |a: Formula, b: Formula| Formula::Eq(boxed(a), boxed(b));
        let escaped_x = ay_symbol_namespace::escape_user_symbol("x");
        let int_collision = Formula::And(vec![
            eq(Formula::Var("x".into(), Sort::Int), Formula::Int(1)),
            eq(
                Formula::FnApp { func: escaped_x.clone(), args: Vec::new(), sort: Sort::Int },
                Formula::Int(2),
            ),
        ]);
        let escaped_p = ay_symbol_namespace::escape_user_symbol("p");
        let pred_collision = Formula::And(vec![
            Formula::Var("p".into(), Sort::Bool),
            Formula::Not(boxed(Formula::Pred(escaped_p.as_str().into(), Vec::new()))),
        ]);
        let backend = InProcessAyBackend::new();
        let cases = [
            (
                int_collision,
                vec![
                    (escaped_x.clone(), CounterexampleValue::Int(2)),
                    ("x".to_string(), CounterexampleValue::Int(1)),
                ],
            ),
            (
                pred_collision,
                vec![
                    (escaped_p.clone(), CounterexampleValue::Bool(false)),
                    ("p".to_string(), CounterexampleValue::Bool(true)),
                ],
            ),
        ];
        for (formula, witness) in cases {
            match backend.run(&formula) {
                VerificationResult::Failed { counterexample: Some(cex), .. } => assert_eq!(
                    cex.assignments, witness,
                    "the witness binds the variable AND the nullary symbol, each in its source \
                     spelling"
                ),
                other => panic!(
                    "a satisfiable formula whose nullary symbol is spelled like an escaped \
                     variable must be refuted with both bound, never decided as if the two \
                     were one symbol: {other:?}"
                ),
            }
        }
    }

    /// A predicate in the CLOSED VOCABULARY keeps the vocabulary's signature —
    /// that table is the authority on what a safety predicate ranges over. A VC
    /// that applies one to a term of another sort is DECLINED, never silently
    /// re-declared at the applied sort (which would let an obligation about
    /// `dir_open(fd: Int)` be discharged against a different predicate).
    #[test]
    fn a_vocabulary_predicate_applied_off_its_declared_sort_is_declined() {
        let formula = Formula::Eq(
            boxed(Formula::Pred("dir_open".into(), vec![level_var("l")])),
            boxed(bool_var("b")),
        );
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "the sort checker admits it");
        assert!(formula_comparisons_well_sorted(&formula), "and so does the pre-gate");
        let reason = uninterpreted_signature_conflict(&formula)
            .expect("the vocabulary signature and the application disagree");
        assert!(reason.contains("dir_open"), "the decline must name the symbol: {reason}");

        let backend = InProcessAyBackend::new();
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
        assert_eq!(panics, 0, "the gate must answer before the bridge; got {verdict:?}");
        match verdict {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.starts_with("in-process ay declined:"), "{reason}");
                assert!(reason.contains("dir_open"), "{reason}");
                assert!(!reason.contains("panicked"), "no panic may be caught: {reason}");
            }
            other => panic!("a signature mismatch must be declined, got {other:?}"),
        }
    }

    /// One symbol, two signatures, one program: SMT-LIB and ay have exactly one
    /// declaration per symbol, so this has no faithful encoding at all. The
    /// declaration would take the first application's signature and the second
    /// would reach ay's `uf::apply`, which PANICS on the mismatch. DECLINE.
    #[test]
    fn one_symbol_applied_at_two_signatures_is_declined_before_the_bridge() {
        let cases = [
            // Two arities.
            Formula::And(vec![
                Formula::Eq(
                    boxed(Formula::FnApp {
                        func: "vc_two".into(),
                        args: vec![int_var("n")],
                        sort: Sort::Int,
                    }),
                    boxed(Formula::Int(0)),
                ),
                Formula::Eq(
                    boxed(Formula::FnApp {
                        func: "vc_two".into(),
                        args: vec![int_var("n"), int_var("n")],
                        sort: Sort::Int,
                    }),
                    boxed(Formula::Int(0)),
                ),
            ]),
            // Two argument sorts.
            Formula::And(vec![
                Formula::Eq(
                    boxed(Formula::FnApp {
                        func: "vc_two".into(),
                        args: vec![int_var("n")],
                        sort: Sort::Int,
                    }),
                    boxed(Formula::Int(0)),
                ),
                Formula::Eq(
                    boxed(Formula::FnApp {
                        func: "vc_two".into(),
                        args: vec![level_var("l")],
                        sort: Sort::Int,
                    }),
                    boxed(Formula::Int(0)),
                ),
            ]),
            // Two result sorts.
            Formula::And(vec![
                Formula::Eq(
                    boxed(Formula::FnApp {
                        func: "vc_two".into(),
                        args: vec![int_var("n")],
                        sort: Sort::Int,
                    }),
                    boxed(Formula::Int(0)),
                ),
                Formula::Eq(
                    boxed(Formula::FnApp {
                        func: "vc_two".into(),
                        args: vec![int_var("n")],
                        sort: Sort::Bool,
                    }),
                    boxed(bool_var("b")),
                ),
            ]),
        ];
        let backend = InProcessAyBackend::new();
        for formula in &cases {
            assert_eq!(check_formula_sort(formula), Ok(Sort::Bool), "{formula:?}");
            let reason = uninterpreted_signature_conflict(formula)
                .unwrap_or_else(|| panic!("two signatures must conflict: {formula:?}"));
            assert!(reason.contains("vc_two"), "the decline names the symbol: {reason}");
            let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
            assert_eq!(panics, 0, "the gate answers before ay's uf::apply; got {verdict:?}");
            match verdict {
                VerificationResult::Unknown { reason, .. } => {
                    assert!(reason.starts_with("in-process ay declined:"), "{reason}");
                    assert!(!reason.contains("panicked"), "{reason}");
                }
                other => panic!("a signature conflict must be declined, got {other:?}"),
            }
        }
    }

    /// The four sibling variants the audit found beside `FnApp`: the FP
    /// conversion nodes trust-machine-sem mints for FCVTZS/FCVTZU, SCVTF/UCVTF
    /// and FCVT had no arm either, and reached the SAME `unreachable!`. Every
    /// one of them must now lower, and a zero-width saturating conversion (the
    /// one shape whose clamp constants have no bitvector to land in) must be
    /// DECLINED by the gate rather than panicking in `bitvec_const`.
    #[test]
    fn fp_conversion_nodes_lower_or_decline_and_never_panic() {
        let rm = || boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RTZ));
        let lane = || boxed(Formula::Var("w".into(), Sort::BitVec(32)));
        let f32v = || boxed(Formula::FpFromBits { bits: lane(), eb: 8, sb: 24 });

        let lowerable = [
            // FCVTZS / FCVTZU: the TOTAL saturating conversions.
            Formula::Eq(
                boxed(Formula::FpToSbv { rm: rm(), value: f32v(), width: 32, eb: 8, sb: 24 }),
                lane(),
            ),
            Formula::Eq(
                boxed(Formula::FpToUbv { rm: rm(), value: f32v(), width: 32, eb: 8, sb: 24 }),
                lane(),
            ),
            // SCVTF / UCVTF, pushed back to bits as the register file requires.
            Formula::Eq(
                boxed(Formula::FpToIeeeBv(boxed(Formula::FpFromSbv {
                    rm: rm(),
                    value: lane(),
                    eb: 8,
                    sb: 24,
                }))),
                lane(),
            ),
            Formula::Eq(
                boxed(Formula::FpToIeeeBv(boxed(Formula::FpFromUbv {
                    rm: rm(),
                    value: lane(),
                    eb: 8,
                    sb: 24,
                }))),
                lane(),
            ),
            // FCVT between formats.
            Formula::Eq(
                boxed(Formula::FpToIeeeBv(boxed(Formula::FpConvert {
                    rm: rm(),
                    value: f32v(),
                    eb: 8,
                    sb: 24,
                }))),
                lane(),
            ),
        ];
        let backend = InProcessAyBackend::new().with_timeout(5_000);
        for formula in &lowerable {
            assert_eq!(check_formula_sort(formula), Ok(Sort::Bool), "{formula:?}");
            assert!(is_lowerable_formula(formula), "the bridge must have an arm: {formula:?}");
            assert_eq!(formula_bitcast_mismatch(formula), None, "{formula:?}");
            let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
            assert_eq!(panics, 0, "{formula:?} must not panic in the bridge; got {verdict:?}");
            if let VerificationResult::Unknown { reason, .. } = &verdict {
                assert!(!reason.contains("panicked"), "no panic may be caught: {reason}");
                assert!(
                    !reason.contains("in-process ay declined:"),
                    "a well-sorted FP conversion must not be declined: {reason}"
                );
            }
        }

        // Width 0 has no bitvector to land in: the gate refuses it, so the
        // guarded expansion's clamp constants are never built.
        let zero_width = Formula::Eq(
            boxed(Formula::FpToSbv { rm: rm(), value: f32v(), width: 0, eb: 8, sb: 24 }),
            boxed(Formula::Var("z".into(), Sort::BitVec(0))),
        );
        assert!(
            formula_bitcast_mismatch(&zero_width).is_some_and(|r| r.contains("width 0")),
            "a zero-width conversion must be declined by the gate"
        );
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(zero_width)));
        assert_eq!(panics, 0, "the gate answers before the bridge; got {verdict:?}");
    }

    /// A BARE rounding-mode comparison is well sorted (`Sort::RoundingMode` on
    /// both sides) and reaches the bridge, whose `FpRoundingMode` arm has no ay
    /// expression to give it and lowers it to `true`. `Eq(RNE, RTZ)` would then
    /// read as `(= true true)`, so its NEGATION — a violation formula that is
    /// genuinely reachable, since the two modes differ — would come back UNSAT
    /// and be falsely PROVED. It must be DECLINED.
    ///
    /// The legitimate position is untouched: a rounding mode as the operand of
    /// an `fp.*` node is read as ay's enum argument and never lowered.
    #[test]
    fn a_rounding_mode_term_outside_an_fp_operand_is_declined_not_silently_true() {
        let rne = || boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RNE));
        let rtz = || boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RTZ));

        let bare = Formula::Not(boxed(Formula::Eq(rne(), rtz())));
        assert_eq!(
            check_formula_sort(&bare),
            Ok(Sort::Bool),
            "the sort checker admits it — which is why a gate is needed"
        );
        assert!(
            rounding_mode_term_out_of_position(&bare).is_some(),
            "a bare rounding-mode comparison must be declined"
        );
        // A rounding-mode-SORTED variable is the same hazard.
        let as_var = Formula::Eq(
            boxed(Formula::Var("mode".into(), Sort::RoundingMode)),
            boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RNE)),
        );
        assert!(rounding_mode_term_out_of_position(&as_var).is_some(), "{as_var:?}");

        let backend = InProcessAyBackend::new().with_timeout(5_000);
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(bare)));
        assert_eq!(panics, 0, "the gate answers before the bridge; got {verdict:?}");
        match verdict {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("rounding-mode term"), "{reason}");
                assert!(!reason.contains("panicked"), "{reason}");
            }
            VerificationResult::Proved { .. } => {
                panic!("a reachable violation must never be PROVED")
            }
            other => panic!("expected a decline, got {other:?}"),
        }

        // The legitimate operand position stays admitted.
        let lane = || boxed(Formula::Var("w".into(), Sort::BitVec(32)));
        let f32v = || boxed(Formula::FpFromBits { bits: lane(), eb: 8, sb: 24 });
        let in_position = Formula::Eq(
            boxed(Formula::FpToIeeeBv(boxed(Formula::FpAdd(rne(), f32v(), f32v())))),
            lane(),
        );
        assert_eq!(
            rounding_mode_term_out_of_position(&in_position),
            None,
            "an fp.* rounding-mode operand is the position the bridge reads"
        );
        let conversion = Formula::Eq(
            boxed(Formula::FpToSbv { rm: rtz(), value: f32v(), width: 32, eb: 8, sb: 24 }),
            lane(),
        );
        assert_eq!(rounding_mode_term_out_of_position(&conversion), None, "{conversion:?}");
    }

    // ── The NON-LITERAL rounding-mode operand (round-E false PROVE) ─────────

    /// A 32-bit lane variable, and the float that reinterprets it.
    fn rm_fuzz_lane(name: &str) -> Box<Formula> {
        boxed(Formula::Var(name.into(), Sort::BitVec(32)))
    }

    fn rm_fuzz_f32(name: &str) -> Box<Formula> {
        boxed(Formula::FpFromBits { bits: rm_fuzz_lane(name), eb: 8, sb: 24 })
    }

    fn rne_literal() -> Box<Formula> {
        boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RNE))
    }

    /// `!( (fp.add RM x y) == (fp.add RNE x y) )` — the violation formula whose
    /// SAT-ness the silent `_ => RNE` default destroyed.
    fn rm_violation(rm: Formula) -> Formula {
        Formula::Not(boxed(Formula::Eq(
            boxed(Formula::FpToIeeeBv(boxed(Formula::FpAdd(
                boxed(rm),
                rm_fuzz_f32("x"),
                rm_fuzz_f32("y"),
            )))),
            boxed(Formula::FpToIeeeBv(boxed(Formula::FpAdd(
                rne_literal(),
                rm_fuzz_f32("x"),
                rm_fuzz_f32("y"),
            )))),
        )))
    }

    /// THE FALSE PROVE (round E, HIGH). `ay_rounding_mode` used to end in
    /// `_ => AyRm::RNE`, so `FpAdd(Var("rmv", Sort::RoundingMode), x, y)` and
    /// `FpAdd(FpRoundingMode(RNE), x, y)` lowered to the IDENTICAL ay term
    /// `(fp.add RNE vf32_0 vf32_1)`. Their disequality — a SATISFIABLE
    /// violation formula, witnessed by any `rmv` whose rounding of `x + y`
    /// differs from RNE — therefore decided UNSAT and was reported **Proved**.
    ///
    /// Two independent assertions, so neither half can regress alone:
    /// 1. the two formulas must NOT produce the same native ay term — the
    ///    bridge now refuses the non-literal operand instead of substituting a
    ///    mode, so the lowering either fails or differs;
    /// 2. the lane must not answer `Proved` for the satisfiable violation — it
    ///    DECLINES, before the bridge, with no caught panic.
    #[test]
    fn a_non_literal_rounding_mode_operand_does_not_lower_like_rne_and_is_never_proved() {
        use trust_types::ay_bridge::formula_to_expr;

        let rm_var = || Formula::Var("rmv".into(), Sort::RoundingMode);
        let with_var = Formula::FpAdd(boxed(rm_var()), rm_fuzz_f32("x"), rm_fuzz_f32("y"));
        let with_rne = Formula::FpAdd(rne_literal(), rm_fuzz_f32("x"), rm_fuzz_f32("y"));

        // Both are well sorted — which is exactly why a gate, not the sort
        // checker, has to be the thing that catches this.
        assert_eq!(check_formula_sort(&with_var), Ok(Sort::Float { eb: 8, sb: 24 }));
        assert_eq!(check_formula_sort(&with_rne), Ok(Sort::Float { eb: 8, sb: 24 }));

        let rne_term = format!("{}", formula_to_expr(&with_rne).expect("the literal lane lowers"));
        assert!(rne_term.contains("fp.add RNE"), "the literal lane is unchanged: {rne_term}");
        // The non-literal operand must not silently become that same term. The
        // bridge now answers this by NAME (it used to substitute RNE, which is
        // what made a satisfiable formula decide UNSAT and report Proved).
        match formula_to_expr(&with_var) {
            Ok(expr) => assert_ne!(
                format!("{expr}"),
                rne_term,
                "an rm-sorted VARIABLE operand must not lower to the RNE term"
            ),
            Err(error) => assert!(
                matches!(error, AyBridgeError::NonLiteralRoundingMode(_))
                    || matches!(error, AyBridgeError::UnlowerableSort { .. }),
                "the refusal must name the rounding-mode defect, got {error:?}"
            ),
        }

        // The fallible form the router asks is the one that must answer.
        assert!(
            trust_types::ay_bridge::non_literal_rounding_mode_operand(&with_var).is_some(),
            "the bridge's own gate must report the non-literal operand"
        );
        assert_eq!(
            trust_types::ay_bridge::non_literal_rounding_mode_operand(&with_rne),
            None,
            "a literal operand is the supported shape"
        );

        // And the whole lane: a SATISFIABLE violation must never be Proved.
        let violation = rm_violation(rm_var());
        assert_eq!(check_formula_sort(&violation), Ok(Sort::Bool));
        assert_eq!(
            rounding_mode_term_out_of_position(&violation),
            None,
            "precondition (this is the half that was missing): the operand OCCUPIES an rm slot, \
             so the out-of-position audit waves it through"
        );
        assert!(rounding_mode_position_defect(&violation).is_some(), "{violation:?}");

        let backend = InProcessAyBackend::new().with_timeout(5_000);
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(violation.clone())));
        assert_eq!(panics, 0, "the gate answers before the bridge; got {verdict:?}");
        match verdict {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("rounding-mode"), "{reason}");
                assert!(!reason.contains("panicked"), "{reason}");
            }
            VerificationResult::Proved { .. } => {
                panic!("FALSE PROVE: the violation is satisfiable for rmv != RNE")
            }
            other => panic!("expected a decline, got {other:?}"),
        }
    }

    /// The OTHER lane, MEASURED. The canonical SMT-LIB transcript is the
    /// second lowering of the same formula and the evidence artifact a strict
    /// verdict is bound to (the Carcara N-version cross-check replays it; the
    /// revalidation receipt digests it), so the two lowerings must agree.
    ///
    /// The text lane does NOT rewrite: `Formula::to_smtlib` renders the rm
    /// operand by lowering the operand TERM (`(fp.add __trust_u_rmv …)`) and
    /// `emit_declarations` declares it at the real SMT-LIB `RoundingMode` sort
    /// (`sort_to_smtlib`). That makes the pre-fix state a DIVERGENCE, not a
    /// shared bug: the native program ay actually decided said `RNE` (the
    /// silent `ay_rounding_mode` default) while the transcript minted beside it
    /// said `rmv` — a strictly harder query. A `Proved` would have been carried
    /// on a transcript of a query that was never solved.
    ///
    /// Pinned both ways: the text lane keeps the operand, and the whole shape
    /// is declined before any transcript is minted.
    #[test]
    fn the_canonical_transcript_never_carries_a_rewritten_rounding_mode() {
        let with_var = rm_violation(Formula::Var("rmv".into(), Sort::RoundingMode));
        // Declined before a transcript is ever built.
        assert!(rounding_mode_position_defect(&with_var).is_some());

        let text = problem_smt2(&with_var);
        assert!(
            text.contains("() RoundingMode"),
            "the text lane declares the rm variable at its real sort: {text}"
        );
        assert!(
            text.contains("(fp.add __trust_u_rmv "),
            "the text lane keeps the operand rather than substituting RNE: {text}"
        );
        // A text lane that rewrote the mode would render both sides of the
        // disequality identically and match the all-RNE problem byte for byte.
        let rewritten_to_rne = rm_violation(*rne_literal());
        assert_ne!(
            text,
            problem_smt2(&rewritten_to_rne),
            "the SMT-LIB text lane must not rewrite a non-literal rounding mode to RNE"
        );
    }

    /// The MEDIUM sibling: a quantifier that BINDS a `Sort::RoundingMode`
    /// variable was seen by NO gate. Binder sorts are not `Formula::children()`
    /// (`Forall`/`Exists` return `vec![body]`), so the out-of-position walk
    /// could not reach them, and `sort_to_ay_in` lowered such a binder to
    /// `AYSort::bool()`. The shape below passed every gate and reached the
    /// bridge.
    ///
    /// It must now DECLINE — twice over, so either gate alone would still
    /// catch it: the bound variable occupies an `fp.*` rm SLOT (read by the
    /// slot gate), and the BINDER SORT itself is one ay cannot declare (read
    /// by the sort-position gate).
    #[test]
    fn a_quantifier_binding_a_rounding_mode_is_declined_never_proved() {
        let bound = Formula::Var("qrm".into(), Sort::RoundingMode);
        let body = rm_violation(bound);
        let exists = Formula::Exists(vec![("qrm".into(), Sort::RoundingMode)], boxed(body));

        assert_eq!(
            check_formula_sort(&exists),
            Ok(Sort::Bool),
            "well sorted — the reason a gate is needed"
        );
        assert_eq!(
            rounding_mode_term_out_of_position(&exists),
            None,
            "precondition: the children()-based walk is blind to the binder AND to the \
             slot-occupying use, which is why this shape passed"
        );
        assert!(
            rounding_mode_position_defect(&exists).is_some(),
            "the slot gate must see the non-literal operand"
        );
        assert!(
            unlowerable_sort_position(&exists).is_some(),
            "the binder-sort gate must see the RoundingMode binder"
        );

        let backend = InProcessAyBackend::new().with_timeout(5_000);
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(exists)));
        assert_eq!(panics, 0, "the gate answers before the bridge; got {verdict:?}");
        assert!(
            !matches!(verdict, VerificationResult::Proved { .. }),
            "a quantifier over rounding modes must never be PROVED: {verdict:?}"
        );
    }

    /// The binder-sort hole, audited beyond rounding modes. Each shape below
    /// puts a sort the bridge cannot lower in a QUANTIFIER BINDER, where no
    /// `children()`-based walk reaches it, and must be declined without a
    /// caught panic.
    #[test]
    fn exotic_binder_sorts_are_declined_not_lowered() {
        let backend = InProcessAyBackend::new().with_timeout(5_000);
        let ghost = || Sort::Datatype { name: "Ghost".into(), constructors: Vec::new() };
        let cases: Vec<(&str, Sort)> = vec![
            // No ay sort exists for it at all.
            ("rounding mode", Sort::RoundingMode),
            // `AYSort::bitvec` asserts width > 0 and PANICS on 0.
            ("zero-width bitvector", Sort::BitVec(0)),
            // Nested in an array, both positions.
            (
                "array over zero-width index",
                Sort::Array(Box::new(Sort::BitVec(0)), Box::new(Sort::Bool)),
            ),
            (
                "array over rounding-mode element",
                Sort::Array(Box::new(Sort::Int), Box::new(Sort::RoundingMode)),
            ),
            // A by-name datatype with no definition anywhere: already covered
            // by `undefined_datatype_reference`, and covered for BINDERS
            // because it walks the same shared position list.
            ("dangling by-name datatype", ghost()),
        ];
        for (label, sort) in cases {
            let body = Formula::Eq(
                boxed(Formula::Var("q".into(), sort.clone())),
                boxed(Formula::Var("q".into(), sort.clone())),
            );
            let formula = Formula::Exists(vec![("q".into(), sort.clone())], boxed(body));
            assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool), "{label}: {formula:?}");
            let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(formula.clone())));
            assert_eq!(panics, 0, "{label}: the gate must answer before the bridge: {verdict:?}");
            match verdict {
                VerificationResult::Unknown { reason, .. } => {
                    assert!(!reason.contains("panicked"), "{label}: {reason}");
                }
                other => panic!("{label}: expected a decline, got {other:?}"),
            }
        }
    }

    /// The same sorts in a FREE-variable position, which the gates already
    /// reached — pinned so the new sort gate and the old ones stay consistent
    /// and a zero-width bitvector declaration stops panicking inside
    /// `AYSort::bitvec`.
    #[test]
    fn a_zero_width_bitvector_declaration_is_declined_not_panicked() {
        let formula = Formula::Eq(
            boxed(Formula::Var("z".into(), Sort::BitVec(0))),
            boxed(Formula::Var("z".into(), Sort::BitVec(0))),
        );
        assert_eq!(check_formula_sort(&formula), Ok(Sort::Bool));
        assert!(unlowerable_sort_position(&formula).is_some_and(|r| r.contains("zero-width")));
        let backend = InProcessAyBackend::new().with_timeout(5_000);
        let (verdict, panics) = counting_panics(|| backend.verify(&safety_vc(formula)));
        assert_eq!(panics, 0, "the gate must answer before `AYSort::bitvec`: {verdict:?}");
        assert!(matches!(verdict, VerificationResult::Unknown { .. }), "{verdict:?}");
    }

    /// 512 well-sorted formulas that deliberately place a NON-LITERAL term in
    /// an `fp.*` rounding-mode slot and/or bind an exotic sort. Every one of
    /// them is a shape the in-process lane cannot faithfully encode, so the
    /// ONLY correct verdict for each is a DECLINE: a `Proved` would be the
    /// round-E false prove, a `Failed` would be a refutation of a query ay was
    /// never given. The panic hook counts CAUGHT panics too, so "contained by
    /// catch_unwind" does not pass as clean.
    #[test]
    fn fuzz_non_literal_rounding_modes_and_exotic_binders_never_misverdict() {
        let backend = InProcessAyBackend::new().with_timeout(2_000);
        let mut rng = FuzzRng(RM_FUZZ_SEED);

        let mut generated = 0usize;
        let mut declined = 0usize;
        let mut with_binder = 0usize;
        let (_, panics) = counting_panics(|| {
            for _ in 0..512 {
                let formula = rm_fuzz_formula(&mut rng, &mut with_binder);
                // Every corpus member is WELL SORTED: the point of the fuzz is
                // that sort-validity is not what keeps these out.
                assert_eq!(
                    check_formula_sort(&formula),
                    Ok(Sort::Bool),
                    "the corpus must be well sorted: {formula:?}"
                );
                generated += 1;
                let verdict = backend.verify(&safety_vc(formula.clone()));
                match verdict {
                    VerificationResult::Unknown { ref reason, .. } => {
                        assert!(!reason.contains("panicked"), "{reason} for {formula:?}");
                        declined += 1;
                    }
                    other => {
                        panic!("WRONG VERDICT {other:?} for an unencodable shape: {formula:?}")
                    }
                }
            }
        });
        assert_eq!(panics, 0, "no formula may reach a panicking bridge seam");
        assert_eq!(generated, 512);
        assert_eq!(declined, 512, "every unencodable shape must decline");
        assert!(with_binder > 50, "the corpus must exercise exotic binders too: {with_binder}");
    }

    /// The fuzz seed, spelled out so the corpus is replayable from it alone.
    const RM_FUZZ_SEED: u64 = 0x9e37_79b9_7f4a_7c15;

    /// One corpus member: a well-sorted Bool formula carrying a non-literal
    /// rounding-mode operand, an exotic binder sort, or both.
    fn rm_fuzz_formula(rng: &mut FuzzRng, with_binder: &mut usize) -> Formula {
        let inner = rm_fuzz_body(rng);
        if rng.below(3) == 0 {
            *with_binder += 1;
            let sort = rm_fuzz_exotic_sort(rng);
            let body = Formula::And(vec![
                inner,
                Formula::Eq(
                    boxed(Formula::Var("q".into(), sort.clone())),
                    boxed(Formula::Var("q".into(), sort.clone())),
                ),
            ]);
            if rng.below(2) == 0 {
                Formula::Exists(vec![("q".into(), sort)], boxed(body))
            } else {
                Formula::Forall(vec![("q".into(), sort)], boxed(body))
            }
        } else {
            inner
        }
    }

    /// A sort the ay bridge has no faithful lowering for.
    fn rm_fuzz_exotic_sort(rng: &mut FuzzRng) -> Sort {
        match rng.below(5) {
            0 => Sort::RoundingMode,
            1 => Sort::BitVec(0),
            2 => Sort::Array(Box::new(Sort::BitVec(0)), Box::new(Sort::Bool)),
            3 => Sort::Array(Box::new(Sort::Int), Box::new(Sort::RoundingMode)),
            _ => Sort::Datatype { name: "Ghost".into(), constructors: Vec::new() },
        }
    }

    /// A rounding-mode-sorted term that is NOT a literal — every spelling the
    /// contract admits in that position.
    fn rm_fuzz_non_literal(rng: &mut FuzzRng) -> Formula {
        match rng.below(4) {
            0 => Formula::Var("rmv".into(), Sort::RoundingMode),
            1 => Formula::SymVar(trust_types::Symbol::intern("rmsym"), Sort::RoundingMode),
            2 => Formula::Ite(
                boxed(Formula::Var("c".into(), Sort::Bool)),
                rne_literal(),
                boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RTZ)),
            ),
            _ => Formula::FnApp {
                func: "pick_rm".into(),
                args: vec![Formula::Var("c".into(), Sort::Bool)],
                sort: Sort::RoundingMode,
            },
        }
    }

    /// A Bool-sorted body with a non-literal rounding mode in one `fp.*` slot.
    /// The comparison lane's WIDTH follows the term's sort, so every corpus
    /// member type-checks — sort-validity is not what keeps these out.
    fn rm_fuzz_body(rng: &mut FuzzRng) -> Formula {
        let rm = boxed(rm_fuzz_non_literal(rng));
        let x = rm_fuzz_f32("x");
        let y = rm_fuzz_f32("y");
        // (term, bitvector width of `term`)
        let (term, width): (Formula, u32) = match rng.below(10) {
            0 => (Formula::FpToIeeeBv(boxed(Formula::FpAdd(rm, x, y))), 32),
            1 => (Formula::FpToIeeeBv(boxed(Formula::FpSub(rm, x, y))), 32),
            2 => (Formula::FpToIeeeBv(boxed(Formula::FpMul(rm, x, y))), 32),
            3 => (Formula::FpToIeeeBv(boxed(Formula::FpDiv(rm, x, y))), 32),
            4 => (Formula::FpToIeeeBv(boxed(Formula::FpFma(rm, x, y, rm_fuzz_f32("z")))), 32),
            5 => (Formula::FpToIeeeBv(boxed(Formula::FpSqrt(rm, x))), 32),
            6 => (Formula::FpToSbv { rm, value: x, width: 32, eb: 8, sb: 24 }, 32),
            7 => (Formula::FpToUbv { rm, value: x, width: 16, eb: 8, sb: 24 }, 16),
            8 => (
                Formula::FpToIeeeBv(boxed(Formula::FpFromUbv {
                    rm,
                    value: rm_fuzz_lane("v"),
                    eb: 8,
                    sb: 24,
                })),
                32,
            ),
            _ => (
                Formula::FpToIeeeBv(boxed(Formula::FpConvert { rm, value: x, eb: 11, sb: 53 })),
                64,
            ),
        };
        let lane = Formula::Var(format!("lane{width}"), Sort::BitVec(width));
        Formula::Not(boxed(Formula::Eq(boxed(term), boxed(lane))))
    }

    // ── The wide no-panic fuzz ──────────────────────────────────────────────

    /// The `Array(Int, Int)` sort the wide corpus's array terms range over.
    fn int_array_sort() -> Sort {
        Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int))
    }

    /// An array-sorted term: the free variable, or a `Store` over one.
    fn wide_array_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        if depth == 0 || rng.below(2) == 0 {
            Formula::Var("arr".into(), int_array_sort())
        } else {
            Formula::Store(
                boxed(wide_array_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
            )
        }
    }

    /// A `Level`-sorted term, with BOTH spellings at every sort position and a
    /// datatype-RETURNING `FnApp` — the `model = reference` shape.
    fn wide_level_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        let sort = rng.level_spelling();
        let arms = if depth == 0 { 3 } else { 6 };
        match rng.below(arms) {
            0 => Formula::Ctor { ctor: "zero".into(), args: Vec::new(), sort },
            1 => Formula::Var("lf".into(), level_sort()),
            2 => Formula::Var("lr".into(), level_ref()),
            3 => Formula::Ctor {
                ctor: "succ".into(),
                args: vec![wide_level_term(rng, depth - 1)],
                sort,
            },
            4 => Formula::Sel {
                datatype: "Level".into(),
                field: "pred".into(),
                field_sort: sort,
                arg: boxed(wide_level_term(rng, depth - 1)),
            },
            // The function symbol keeps ONE signature across the whole corpus
            // (`(Level) -> Level`), so a formula is never declined for the
            // unrelated reason that it applies one name at two signatures.
            _ => level_fn_app(wide_level_term(rng, depth - 1)),
        }
    }

    /// An `Int`-sorted term: arithmetic, an array read, and an `FnApp` that
    /// crosses from the datatype carrier back to `Int`.
    fn wide_int_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        let arms = if depth == 0 { 2 } else { 6 };
        match rng.below(arms) {
            0 => Formula::Int(i128::from(rng.below(9)) - 4),
            1 => int_var("n"),
            2 => Formula::Add(
                boxed(wide_int_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
            ),
            3 => Formula::Sub(
                boxed(wide_int_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
            ),
            4 => Formula::Select(
                boxed(wide_array_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
            ),
            _ => Formula::FnApp {
                func: "vc_rank".into(),
                args: vec![wide_level_term(rng, depth - 1)],
                sort: Sort::Int,
            },
        }
    }

    /// A `Bool`-sorted term — the corpus's top-level shape. Spans the
    /// connectives, datatype equations and testers, array-read comparisons,
    /// a VOCABULARY predicate at its declared `Int` sort, an out-of-vocabulary
    /// predicate over a datatype term, a `Bool`-returning `FnApp`, and a
    /// quantifier.
    fn wide_bool_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        let arms = if depth == 0 { 3 } else { 13 };
        match rng.below(arms) {
            0 => Formula::Bool(rng.below(2) == 0),
            1 => bool_var("b"),
            2 => {
                Formula::Eq(boxed(wide_level_term(rng, depth)), boxed(wide_level_term(rng, depth)))
            }
            3 => Formula::IsCtor {
                datatype: "Level".into(),
                ctor: if rng.below(2) == 0 { "zero".into() } else { "succ".into() },
                arg: boxed(wide_level_term(rng, depth - 1)),
            },
            4 => Formula::Not(boxed(wide_bool_term(rng, depth - 1))),
            5 => Formula::And(vec![wide_bool_term(rng, depth - 1), wide_bool_term(rng, depth - 1)]),
            6 => Formula::Or(vec![wide_bool_term(rng, depth - 1), wide_bool_term(rng, depth - 1)]),
            7 => Formula::Le(
                boxed(wide_int_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
            ),
            8 => Formula::Eq(
                boxed(wide_int_term(rng, depth - 1)),
                boxed(wide_int_term(rng, depth - 1)),
            ),
            // In the closed vocabulary, applied at its declared `Int` sort.
            9 => Formula::Pred("dir_open".into(), vec![wide_int_term(rng, depth - 1)]),
            // Out of vocabulary, over the datatype carrier: declared from the
            // application, which is what the all-`Int` fallback got wrong.
            10 => Formula::Pred("vc_level_seen".into(), vec![wide_level_term(rng, depth - 1)]),
            11 => Formula::FnApp {
                func: "vc_level_wf".into(),
                args: vec![wide_level_term(rng, depth - 1)],
                sort: Sort::Bool,
            },
            _ => {
                let k = trust_types::Symbol::intern("qk");
                let body = Formula::Le(
                    boxed(Formula::Var("qk".into(), Sort::Int)),
                    boxed(Formula::Add(
                        boxed(Formula::Var("qk".into(), Sort::Int)),
                        boxed(Formula::Int(1)),
                    )),
                );
                if rng.below(2) == 0 {
                    Formula::Forall(vec![(k, Sort::Int)], boxed(body))
                } else {
                    Formula::Exists(vec![(k, Sort::Int)], boxed(body))
                }
            }
        }
    }

    /// 520 well-sorted formulas spanning EVERY `Formula` family the router can
    /// be handed — `FnApp` at three different result sorts, `Pred` in and out
    /// of the closed vocabulary, datatype constructors/selectors/testers with
    /// the sort spelled BOTH ways at every position, arrays (`Select`/`Store`),
    /// quantifiers, and Int/Bool arithmetic — submitted through
    /// `InProcessAyBackend::verify` under a counting panic hook.
    ///
    /// Two things are asserted, and they are different claims:
    ///
    /// * ZERO CAUGHT PANICS. `catch_unwind` is containment of last resort, not
    ///   input validation: a contained panic still runs the process-global
    ///   panic hook. Counting the hook tests the FACT, where reading the reason
    ///   would only test the wording.
    /// * ZERO WRONG VERDICTS, with an oracle that needs no model: for a sample
    ///   of the corpus, `Or([F, true])` is VALID — a violation formula that is
    ///   satisfiable, so it may never come back `Proved` — and `And([F, false])`
    ///   is UNSATISFIABLE, so it may never come back `Failed` with a
    ///   counterexample. Those are exactly the two ways this backend's verdict
    ///   can be wrong.
    ///
    /// Before the round-10 fix the `FnApp` arms alone made this corpus panic:
    /// every one of the three `FnApp` families reached the bridge's
    /// `unreachable!`, and the out-of-vocabulary `Pred` over a `Level` term
    /// reached ay's panicking `uf::apply` through a fabricated all-`Int`
    /// declaration.
    #[test]
    fn wide_well_sorted_corpus_never_panics_and_never_returns_a_wrong_verdict() {
        let backend = InProcessAyBackend::new().with_timeout(5_000);
        let mut rng = FuzzRng(0x5eed_1e55_c0ff_ee0a);
        let corpus: Vec<Formula> = (0..520).map(|_| wide_bool_term(&mut rng, 3)).collect();
        let mut fn_app_seen = 0_usize;
        let mut pred_seen = 0_usize;
        let mut quantifier_seen = 0_usize;
        let mut array_seen = 0_usize;
        let mut datatype_seen = 0_usize;
        let mut oracle_checks = 0_usize;

        let ((), panics) = counting_panics(|| {
            for (index, formula) in corpus.iter().enumerate() {
                // Well sorted by construction, and admitted by every gate that
                // stands in front of the bridge.
                assert_eq!(
                    check_formula_sort(formula),
                    Ok(Sort::Bool),
                    "the generator must only emit well-sorted formulas: {formula:?}"
                );
                assert!(formula_comparisons_well_sorted(formula), "{formula:?}");
                assert_eq!(free_variable_sort_conflict(formula), None, "{formula:?}");
                assert_eq!(
                    uninterpreted_signature_conflict(formula),
                    None,
                    "the corpus keeps one signature per symbol: {formula:?}"
                );
                assert!(
                    is_lowerable_formula(formula),
                    "every node must have a lowering arm: {formula:?}"
                );

                formula.visit(&mut |node| match node {
                    Formula::FnApp { .. } => fn_app_seen += 1,
                    Formula::Pred(..) => pred_seen += 1,
                    Formula::Forall(..) | Formula::Exists(..) => quantifier_seen += 1,
                    Formula::Select(..) | Formula::Store(..) => array_seen += 1,
                    Formula::Ctor { .. } | Formula::Sel { .. } | Formula::IsCtor { .. } => {
                        datatype_seen += 1;
                    }
                    _ => {}
                });

                let defs = DatatypeDefs::collect(formula).expect("at most one Level definition");
                let dangling = undefined_datatype_reference(formula, &defs);

                if !execute_direct::is_available() {
                    continue;
                }
                let verdict = backend.verify(&safety_vc(formula.clone()));
                if let VerificationResult::Unknown { reason, .. } = &verdict {
                    assert!(
                        !reason.contains("panicked"),
                        "no panic may be caught for {formula:?}: {reason}"
                    );
                    if dangling.is_none() {
                        assert!(
                            !reason.contains("in-process ay declined:"),
                            "a well-sorted formula with every datatype defined must not be \
                             declined: {reason} for {formula:?}"
                        );
                    }
                }

                // The verdict oracle, on a sample (each anchored query is a
                // second and third solve, so the whole corpus would be three
                // times the wall clock for no extra coverage of the shapes).
                if index % 4 != 0 {
                    continue;
                }
                oracle_checks += 1;
                let satisfiable = Formula::Or(vec![formula.clone(), Formula::Bool(true)]);
                match backend.verify(&safety_vc(satisfiable)) {
                    VerificationResult::Proved { .. } => panic!(
                        "`F or true` is satisfiable — proving it would be a false PROVE: \
                         {formula:?}"
                    ),
                    other => assert!(
                        !matches!(&other, VerificationResult::Unknown { reason, .. }
                            if reason.contains("panicked")),
                        "{other:?}"
                    ),
                }
                let unsatisfiable = Formula::And(vec![formula.clone(), Formula::Bool(false)]);
                match backend.verify(&safety_vc(unsatisfiable)) {
                    VerificationResult::Failed { counterexample, .. } => panic!(
                        "`F and false` is unsatisfiable — refuting it would be a false \
                         REFUTATION with witness {counterexample:?}: {formula:?}"
                    ),
                    other => assert!(
                        !matches!(&other, VerificationResult::Unknown { reason, .. }
                            if reason.contains("panicked")),
                        "{other:?}"
                    ),
                }
            }
        });

        assert_eq!(panics, 0, "the corpus must produce ZERO caught panics");
        assert!(fn_app_seen > 0, "the corpus must exercise Formula::FnApp");
        assert!(pred_seen > 0, "the corpus must exercise Formula::Pred");
        assert!(quantifier_seen > 0, "the corpus must exercise quantifiers");
        assert!(array_seen > 0, "the corpus must exercise array terms");
        assert!(datatype_seen > 0, "the corpus must exercise datatype terms");
        if execute_direct::is_available() {
            assert!(oracle_checks > 100, "the verdict oracle must run on a real sample");
        }
    }

    /// One deterministic xorshift64* stream: the fuzz corpus below is identical
    /// on every run, so a failure is replayable from the seed alone.
    struct FuzzRng(u64);

    impl FuzzRng {
        fn next_u64(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_f491_4f6c_dd1d)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next_u64() % n
        }

        /// A `Level` sort spelled fully or BY NAME — the two spellings of ONE
        /// sort that trust-ir-contract and trust-vcgen actually mix. Picking
        /// per position is what makes some corpus formulas carry the definition
        /// and others reference `Level` by name only.
        fn level_spelling(&mut self) -> Sort {
            if self.below(2) == 0 { level_sort() } else { level_ref() }
        }
    }

    /// A `Level`-sorted term. The two free variables are kept at ONE spelling
    /// each (`lf` full, `lr` by name) so the corpus never trips
    /// `free_variable_sort_conflict`, which compares sorts exactly and would
    /// otherwise decline for an unrelated reason.
    fn fuzz_level_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        let sort = rng.level_spelling();
        let arms = if depth == 0 { 3 } else { 5 };
        match rng.below(arms) {
            0 => Formula::Ctor { ctor: "zero".into(), args: Vec::new(), sort },
            1 => Formula::Var("lf".into(), level_sort()),
            2 => Formula::Var("lr".into(), level_ref()),
            3 => Formula::Ctor {
                ctor: "succ".into(),
                args: vec![fuzz_level_term(rng, depth - 1)],
                sort,
            },
            _ => Formula::Sel {
                datatype: "Level".into(),
                field: "pred".into(),
                field_sort: sort,
                arg: boxed(fuzz_level_term(rng, depth - 1)),
            },
        }
    }

    /// An `Int`-sorted term.
    fn fuzz_int_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        let arms = if depth == 0 { 2 } else { 4 };
        match rng.below(arms) {
            0 => Formula::Int(i128::from(rng.below(9)) - 4),
            1 => int_var("n"),
            2 => Formula::Add(
                boxed(fuzz_int_term(rng, depth - 1)),
                boxed(fuzz_int_term(rng, depth - 1)),
            ),
            _ => Formula::Sub(
                boxed(fuzz_int_term(rng, depth - 1)),
                boxed(fuzz_int_term(rng, depth - 1)),
            ),
        }
    }

    /// A `Bool`-sorted term — the corpus's top-level shape.
    fn fuzz_bool_term(rng: &mut FuzzRng, depth: u32) -> Formula {
        let arms = if depth == 0 { 3 } else { 8 };
        match rng.below(arms) {
            0 => Formula::Bool(rng.below(2) == 0),
            1 => bool_var("b"),
            2 => {
                Formula::Eq(boxed(fuzz_level_term(rng, depth)), boxed(fuzz_level_term(rng, depth)))
            }
            3 => Formula::IsCtor {
                datatype: "Level".into(),
                ctor: if rng.below(2) == 0 { "zero".into() } else { "succ".into() },
                arg: boxed(fuzz_level_term(rng, depth - 1)),
            },
            4 => Formula::Not(boxed(fuzz_bool_term(rng, depth - 1))),
            5 => Formula::And(vec![fuzz_bool_term(rng, depth - 1), fuzz_bool_term(rng, depth - 1)]),
            6 => Formula::Or(vec![fuzz_bool_term(rng, depth - 1), fuzz_bool_term(rng, depth - 1)]),
            _ => Formula::Le(
                boxed(fuzz_int_term(rng, depth - 1)),
                boxed(fuzz_int_term(rng, depth - 1)),
            ),
        }
    }

    /// 420 well-sorted formulas over `Int`/`Bool`/`Level`, with `Level` spelled
    /// BOTH ways at every sort position, must produce ZERO caught panics — and
    /// the ONLY thing the datatype gate may decline among them is a PROVEN
    /// defect: a by-name reference with no definition anywhere in that formula.
    ///
    /// This is the regression the round-9 verifier ran: 11 of its 400 formulas
    /// were undefined-datatype references, and those 11 were 100% of the
    /// panics `catch_unwind` had to rescue.
    #[test]
    fn fuzzed_well_sorted_datatype_formulas_never_panic_and_only_proven_defects_decline() {
        let backend = InProcessAyBackend::new();
        let mut rng = FuzzRng(0x5eed_1e55_c0ff_ee01);
        let corpus: Vec<Formula> = (0..420).map(|_| fuzz_bool_term(&mut rng, 3)).collect();
        let mut dangling_seen = 0_usize;
        let mut admitted_seen = 0_usize;

        let ((), panics) = counting_panics(|| {
            for formula in &corpus {
                // Every corpus formula is well sorted by construction.
                assert_eq!(
                    check_formula_sort(formula),
                    Ok(Sort::Bool),
                    "generator must only emit well-sorted formulas: {formula:?}"
                );
                assert!(formula_comparisons_well_sorted(formula), "{formula:?}");
                assert_eq!(free_variable_sort_conflict(formula), None, "{formula:?}");

                let defs = DatatypeDefs::collect(formula).expect("at most one Level definition");
                let dangling = undefined_datatype_reference(formula, &defs);

                // Nothing the sort checker accepts is declined by the datatype
                // gate EXCEPT on a proven undefined-datatype reference.
                match formula_datatype_defect(formula) {
                    None => assert!(
                        dangling.is_none(),
                        "an undefined datatype must be declined: {formula:?}"
                    ),
                    Some(reason) => {
                        let name = dangling.clone().unwrap_or_else(|| {
                            panic!("the gate declined a formula with no proven defect: {reason}")
                        });
                        assert!(
                            reason.contains(&format!("undefined datatype `{name}`")),
                            "the decline must name the undefined datatype: {reason}"
                        );
                    }
                }

                if dangling.is_some() {
                    dangling_seen += 1;
                } else {
                    admitted_seen += 1;
                }

                // End to end. A dangling formula declines at the gate; every
                // other one reaches ay and gets an honest verdict — and in
                // neither case may a panic be caught.
                if execute_direct::is_available() {
                    let result = backend.verify(&safety_vc(formula.clone()));
                    if let VerificationResult::Unknown { reason, .. } = &result {
                        assert!(
                            !reason.contains("panicked"),
                            "no panic may be caught for {formula:?}: {reason}"
                        );
                        if dangling.is_none() {
                            assert!(
                                !reason.contains("in-process ay declined:"),
                                "a well-sorted formula with every datatype defined must not \
                                 be declined: {reason} for {formula:?}"
                            );
                        }
                    }
                }
            }
        });

        assert_eq!(panics, 0, "the corpus must produce ZERO caught panics");
        assert!(
            dangling_seen > 0,
            "the corpus must actually exercise the undefined-datatype class"
        );
        assert!(
            admitted_seen > corpus.len() / 2,
            "the corpus must be mostly well-defined formulas, not mostly declines \
             ({admitted_seen} admitted of {})",
            corpus.len()
        );
    }

    /// A refuted datatype obligation carries the witness ay found, spelled as
    /// ay spells it: `m = succ zero` as a violation formula is SAT with
    /// `m ↦ (succ zero)`, and the counterexample must say exactly that —
    /// never the old fabricated `Int(0)` placeholder.
    #[test]
    fn datatype_witness_is_rendered_as_the_solver_spells_it() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();
        let formula = Formula::Eq(boxed(level_var("m")), boxed(succ(zero())));
        match backend.verify(&safety_vc(formula)) {
            VerificationResult::Failed { counterexample: Some(cex), .. } => {
                let m = cex
                    .assignments
                    .iter()
                    .find(|(name, _)| name == "m")
                    .map(|(_, value)| value)
                    .unwrap_or_else(|| panic!("the witness must bind `m`: {cex:?}"));
                assert_eq!(
                    *m,
                    CounterexampleValue::Term("(succ zero)".to_string()),
                    "the witness must be ay's own spelling of the datatype value"
                );
                assert_eq!(cex.to_string(), "m = (succ zero)");
            }
            other => panic!("`m = succ zero` is satisfiable and must be Failed, got {other:?}"),
        }
    }

    /// `model_value_to_cex` never fabricates a scalar: every non-scalar ay
    /// model value keeps its SMT-LIB spelling, the two Rust float formats are
    /// reassembled bit-exactly, and out-of-range integers keep their digits.
    #[test]
    fn model_value_to_cex_is_faithful_for_every_variant() {
        use num_bigint::BigInt;
        let succ_zero = ModelValue::Datatype {
            constructor: "succ".into(),
            args: vec![ModelValue::Datatype { constructor: "zero".into(), args: Vec::new() }],
        };
        assert_eq!(model_value_to_cex(&succ_zero), CounterexampleValue::Term("(succ zero)".into()));
        assert_eq!(
            model_value_to_cex(&ModelValue::Datatype { constructor: "zero".into(), args: vec![] }),
            CounterexampleValue::Term("zero".into())
        );
        assert_eq!(
            model_value_to_cex(&ModelValue::Int(BigInt::from(-7))),
            CounterexampleValue::Int(-7)
        );
        let beyond_i128 = BigInt::from(i128::MAX) + BigInt::from(1);
        assert_eq!(
            model_value_to_cex(&ModelValue::Int(beyond_i128.clone())),
            CounterexampleValue::Term(ModelValue::Int(beyond_i128).to_string())
        );
        assert_eq!(
            model_value_to_cex(&ModelValue::BitVec { value: BigInt::from(255), width: 8 }),
            CounterexampleValue::Uint(255)
        );
        assert_eq!(
            model_value_to_cex(&ModelValue::Uninterpreted("elem!0".into())),
            CounterexampleValue::Term("elem!0".into())
        );
        // binary64 `-1.5`: sign 1, biased exponent 1023, fraction 0.5.
        let neg_one_point_five = ModelValue::FloatingPoint {
            sign: true,
            exponent: 1023,
            significand: 1u64 << 51,
            eb: 11,
            sb: 53,
        };
        assert_eq!(model_value_to_cex(&neg_one_point_five), CounterexampleValue::Float(-1.5));
        // binary32 `2.0`: biased exponent 128, zero fraction.
        let two_f32 =
            ModelValue::FloatingPoint { sign: false, exponent: 128, significand: 0, eb: 8, sb: 24 };
        assert_eq!(model_value_to_cex(&two_f32), CounterexampleValue::Float(2.0));
        match model_value_to_cex(&ModelValue::FloatingPointSpecial {
            kind: ay::FpSpecialKind::NaN,
            eb: 11,
            sb: 53,
        }) {
            CounterexampleValue::Float(f) => assert!(f.is_nan()),
            other => panic!("a binary64 NaN reassembles to a NaN float, got {other:?}"),
        }
        assert_eq!(
            model_value_to_cex(&ModelValue::FloatingPointSpecial {
                kind: ay::FpSpecialKind::NegInf,
                eb: 8,
                sb: 24
            }),
            CounterexampleValue::Float(f64::NEG_INFINITY)
        );
        // A non-Rust format keeps ay's spelling rather than an approximation.
        let half =
            ModelValue::FloatingPoint { sign: false, exponent: 15, significand: 0, eb: 5, sb: 11 };
        assert_eq!(model_value_to_cex(&half), CounterexampleValue::Term(half.to_string()));
    }
}

/// Fail-closed authority tests for the router certification transport seam
/// [`InProcessAyBackend::promote_to_certified`].
///
/// No live solver is required.  BV-multiply and BV-shift candidates, satisfiable
/// formulas, and out-of-fragment formulas MUST all retain the exact SmtBacked
/// verdict and ay certificate: the Clean kernel cannot certify them from the VC
/// alone, so there is nothing replayable to promote on.  Since D.9 the
/// recognized LIA candidate IS promoted on an `ay-certify` build, and the
/// batteries below pin that the promotion carries evidence which replays
/// against its own VC and is refused against any other.
// This module intentionally runs in the base `ay-backend` build as well as
// `ay-certify`: S1 is an AY replay gate, and feature placement must not hide its
// falsification battery from the configuration that exports it.
#[cfg(test)]
mod certification_transport_gate_tests {
    use trust_types::Symbol;

    use super::*;

    /// Build the strict-checked `SmtBacked` Proved the promotion seam receives.
    fn strict_proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: SOLVER_NAME.into(),
            time_ms: 3,
            strength: ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(vec![9, 9, 9]),
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn x_gt10_lt5() -> Formula {
        Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
        ])
    }

    fn assert_unchanged_smtbacked(formula: &Formula) {
        let out = InProcessAyBackend::promote_to_certified(strict_proved(), formula, 99);
        match out {
            VerificationResult::Proved {
                solver,
                time_ms,
                strength,
                proof_certificate,
                solver_warnings,
                native_proof_envelope,
            } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert_eq!(time_ms, 3, "the gate must preserve the original timing evidence");
                assert_eq!(strength, ProofStrength::smt_unsat_strict_checked());
                assert_eq!(strength.assurance, trust_types::AssuranceLevel::SmtBacked);
                assert_eq!(proof_certificate.as_deref(), Some(&[9, 9, 9][..]));
                assert_eq!(solver_warnings, None);
                assert_eq!(native_proof_envelope, None);
            }
            other => panic!("the gate must preserve Proved SmtBacked, got {other:?}"),
        }
    }

    /// Without the Clean reconstruction feature there is no kernel to certify
    /// with, so even a recognized LIA candidate keeps the honest SmtBacked
    /// verdict.
    #[cfg(not(feature = "ay-certify"))]
    #[test]
    fn recognized_lia_stays_smtbacked_without_clean_payload_transport() {
        assert_unchanged_smtbacked(&x_gt10_lt5());
    }

    /// D.9: on an `ay-certify` build the recognized LIA candidate IS promoted —
    /// and the promotion carries replayable evidence rather than a bare label.
    ///
    /// This pins the three things the old identity gate existed to prevent:
    /// ay's LRAT bytes are not displaced, the kernel payload is present in its
    /// own typed slot, and that payload independently replays against this VC.
    #[cfg(feature = "ay-certify")]
    #[test]
    fn recognized_lia_is_promoted_with_replayable_evidence() {
        let formula = x_gt10_lt5();
        let out = InProcessAyBackend::promote_to_certified(strict_proved(), &formula, 99);
        let VerificationResult::Proved {
            strength,
            proof_certificate,
            native_proof_envelope,
            time_ms,
            ..
        } = out
        else {
            panic!("promotion must stay Proved");
        };
        assert_eq!(strength, ProofStrength::smt_unsat_certified());
        assert_eq!(strength.assurance, trust_types::AssuranceLevel::Certified);
        assert_eq!(
            proof_certificate.as_deref(),
            Some(&[9, 9, 9][..]),
            "ay's LRAT certificate must be PRESERVED, not displaced by the kernel payload"
        );
        assert_eq!(time_ms, 3, "the gate must preserve the original timing evidence");
        let envelope = native_proof_envelope.expect("a Certified row must carry its evidence");
        assert!(envelope.accepted());
        assert_eq!(
            crate::ay_certify::replay_certified_envelope(&formula, &envelope),
            crate::ay_certify::ReplayOutcome::Replayed,
            "the shipped envelope must independently replay against this VC"
        );
    }

    /// D.9: the promotion is BOUND. The envelope minted for one VC does not
    /// replay against another, so a `Certified` row cannot be laundered onto a
    /// different obligation by copying its evidence across.
    #[cfg(feature = "ay-certify")]
    #[test]
    fn promoted_evidence_does_not_replay_against_another_vc() {
        let out = InProcessAyBackend::promote_to_certified(strict_proved(), &x_gt10_lt5(), 99);
        let VerificationResult::Proved { native_proof_envelope: Some(envelope), .. } = out else {
            panic!("expected a promoted row carrying an envelope");
        };
        let other = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(20))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(7))),
        ]);
        assert_eq!(
            crate::ay_certify::replay_certified_envelope(&other, &envelope),
            crate::ay_certify::ReplayOutcome::KernelRejected
        );
    }

    /// The same hard block applies to the recognized BV-multiply candidate.
    #[test]
    fn recognized_bvmul_stays_smtbacked_without_clean_payload_transport() {
        let w = 2;
        let a = Formula::Var("A0".into(), Sort::BitVec(w));
        let b = Formula::Var("B0".into(), Sort::BitVec(w));
        let product = Formula::BvMul(Box::new(a), Box::new(b), w);
        let readout = Formula::BvExtract {
            inner: Box::new(Formula::BvZeroExt(Box::new(product.clone()), w)),
            high: w - 1,
            low: 0,
        };
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(readout), Box::new(product))));
        assert_unchanged_smtbacked(&formula);
    }

    /// The same hard block applies to the recognized BV-shift candidate.
    #[test]
    fn recognized_bvshift_stays_smtbacked_without_clean_payload_transport() {
        let w = 2;
        let value = Formula::Var("V0".into(), Sort::BitVec(w));
        let amount = Formula::Var("S0".into(), Sort::BitVec(w));
        let shift = Formula::BvShl(Box::new(value), Box::new(amount), w);
        let readout = Formula::BvOr(
            Box::new(Formula::BitVec { value: 0, width: w }),
            Box::new(shift.clone()),
            w,
        );
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(readout), Box::new(shift))));
        assert_unchanged_smtbacked(&formula);
    }

    /// A SATISFIABLE formula (`x > 2 ∧ x < 9`) is NOT promoted — the honest
    /// `SmtBacked` verdict survives.
    #[test]
    fn promote_declines_satisfiable_formula_keeps_smtbacked() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9))),
        ]);
        assert_unchanged_smtbacked(&formula);
    }

    /// A formula outside the reconstruction fragment keeps `SmtBacked`.
    #[test]
    fn promote_declines_out_of_fragment_keeps_smtbacked() {
        let formula =
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        assert_unchanged_smtbacked(&formula);
    }

    // ---- Sealed-authority S1: `revalidate_vc_unsat_strict` falsification battery.
    // The cardinal property (constitution #17 anti-no-op): the gate must FIRE
    // (re-prove) rather than rubber-stamp — so a genuinely-UNSAT violation mints
    // an outcome while a SATISFIABLE one (a real counterexample) does NOT.

    /// A satisfiable violation formula (`x > 2 ∧ x < 9`): the fresh solve returns
    /// `Failed`, so revalidation refuses to mint. This is the anti-forgery /
    /// refutation-immunity heart — a producer's bare `Proved` on a false formula
    /// cannot be laundered into authority.
    #[test]
    fn revalidate_declines_satisfiable_violation() {
        let sat = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9))),
        ]);
        assert!(revalidate_vc_unsat_strict(&sat, 90_000, EffortScale::BUILTIN).is_none());
    }

    #[test]
    fn revalidate_rejects_zero_budget() {
        assert!(
            revalidate_vc_unsat_strict(&x_gt10_lt5(), 0, EffortScale::BUILTIN).is_none(),
            "zero must never disable the timeout on an authority-minting path"
        );
    }

    /// The miss names its stop: a refuting re-solve is `solved` (the clock
    /// decided nothing), a re-solve with no time on its clock is
    /// `wall-backstop`, and an UNSAT one still mints. This module is behind
    /// `ay-backend`, so only a `--features ay-backend` run compiles the test
    /// (`docs/VALIDATION_LADDER.md`, TRUST-16).
    #[test]
    fn revalidate_or_stop_names_why_nothing_was_minted() {
        let sat = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9))),
        ]);
        assert_eq!(
            revalidate_vc_unsat_strict_or_stop(&sat, 90_000, EffortScale::BUILTIN).err(),
            Some(StopCause::Solved),
        );
        assert_eq!(
            revalidate_vc_unsat_strict_or_stop(&x_gt10_lt5(), 0, EffortScale::BUILTIN).err(),
            Some(StopCause::WallBackstop),
        );
        assert!(
            revalidate_vc_unsat_strict_or_stop(&x_gt10_lt5(), 90_000, EffortScale::BUILTIN).is_ok()
        );
    }

    #[test]
    fn revalidate_rejects_malformed_ite_before_translation() {
        // AY's ITE constructor requires equal branch sorts. The shared sort
        // boundary must reject this before AY translation, avoiding both an
        // unwind and the process-global panic hook's stderr output.
        let malformed = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
            Box::new(Formula::Int(0)),
        );
        let result = InProcessAyBackend::new().run_strict(&malformed);
        assert!(matches!(
            result,
            VerificationResult::Unknown { ref reason, .. }
                if reason.contains("sort-invalid") && reason.contains("if-then-else")
        ));
        assert!(revalidate_vc_unsat_strict(&malformed, 1_000, EffortScale::BUILTIN).is_none());
    }

    #[test]
    fn revalidate_rejects_conflicting_free_variable_sorts() {
        let malformed = Formula::And(vec![
            Formula::Var("same".into(), Sort::Bool),
            Formula::Eq(
                Box::new(Formula::Var("same".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);
        let result = InProcessAyBackend::new().run_strict(&malformed);
        assert!(matches!(
            result,
            VerificationResult::Unknown { ref reason, .. }
                if reason.contains("conflicting sorts") && reason.contains("`same`")
        ));
        assert!(revalidate_vc_unsat_strict(&malformed, 1_000, EffortScale::BUILTIN).is_none());
    }

    #[test]
    fn revalidation_policy_never_mints_from_bounded_finite_only() {
        // A ground false violation has a complete one-case finite-domain proof,
        // which is sufficient to exercise the policy without relying on AY's
        // current proof-production coverage for a particular theory fragment.
        let formula = Formula::Bool(false);
        let base = VerificationResult::Unknown {
            solver: SOLVER_NAME.into(),
            time_ms: 0,
            reason: "UNSAT without a strict AY artifact".into(),
        };
        assert!(matches!(
            InProcessAyBackend::finish_verified_result(base.clone(), &formula, 0, true),
            VerificationResult::Proved { .. }
        ));
        assert!(matches!(
            InProcessAyBackend::finish_verified_result(base, &formula, 0, false),
            VerificationResult::Unknown { .. }
        ));
    }

    #[test]
    fn revalidation_problem_declares_symbol_variables_exactly() {
        let formula = Formula::Eq(
            Box::new(Formula::SymVar(Symbol::intern("s1_bits"), Sort::BitVec(8))),
            Box::new(Formula::BitVec { value: 7, width: 8 }),
        );
        let problem = problem_smt2(&formula);
        // Trust: the transcript declares the symbol in Trust's ay namespace —
        // the same spelling `build_program` declares natively — so a `SymVar`
        // named like an ay builtin can never collide. Exactly one declaration.
        let declared = format!("{}s1_bits", ay_symbol_namespace::AY_USER_SYMBOL_PREFIX);
        assert!(problem.starts_with("(set-logic QF_BV)\n"), "{problem}");
        assert!(
            problem.contains(&format!("(declare-fun {declared} () (_ BitVec 8))\n")),
            "{problem}"
        );
        assert_eq!(problem.matches(&format!("declare-fun {declared}")).count(), 1);
    }

    /// An unsatisfiable violation formula (`x > 10 ∧ x < 5`): the fresh solve
    /// re-proves UNSAT, so revalidation mints an outcome carrying the exact
    /// canonical problem bytes it checked and their domain-separated digest.
    #[test]
    fn revalidate_mints_on_unsatisfiable_violation() {
        let out = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000, EffortScale::BUILTIN)
            .expect("an unsatisfiable violation must re-prove and mint");
        assert_eq!(out.canonical_problem(), problem_smt2(&x_gt10_lt5()));
        assert_eq!(out.canonical_problem_sha256().len(), 64, "sha-256 hex");
        assert!(out.canonical_problem_sha256().bytes().all(|b| b.is_ascii_hexdigit()));
    }

    /// Determinism: the same formula re-solves to the same canonical bytes and
    /// digest, so the mint site's row binding is stable across runs.
    #[test]
    fn revalidate_digest_is_deterministic() {
        let a = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000, EffortScale::BUILTIN)
            .expect("mint a");
        let b = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000, EffortScale::BUILTIN)
            .expect("mint b");
        assert_eq!(a.canonical_problem_sha256(), b.canonical_problem_sha256());
        assert_eq!(a.canonical_problem(), b.canonical_problem());
    }

    /// The digest is domain-separated: it is NOT the bare SHA-256 of the problem
    /// bytes, so a digest computed elsewhere over `problem_smt2` cannot be passed
    /// off as a revalidation receipt digest.
    #[test]
    fn revalidate_digest_is_domain_separated() {
        let out =
            revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000, EffortScale::BUILTIN).expect("mint");
        let mut bare = Sha256::new();
        bare.update(out.canonical_problem().as_bytes());
        let bare_hex = format!("{:x}", bare.finalize());
        assert_ne!(out.canonical_problem_sha256(), bare_hex);
    }
}

/// Track D increment 2: unit tests for the MONOTONE Carcara cross-check gate.
///
/// These exercise the pure decision logic [`InProcessAyBackend::apply_carcara_gate`]
/// directly — they construct a `Proved` result and feed each [`CrossCheck`]
/// verdict, so NO live solver and NO live Carcara binary are required. The
/// cardinal rule under test: a `Reject` downgrades to `Unknown` (fail-closed),
/// while `Accept` and `Unavailable` both keep the strict-checked `Proved` (an
/// absent Carcara must never introduce a false-FAIL).
#[cfg(all(test, feature = "ay-backend", feature = "carcara-crosscheck"))]
mod carcara_gate_tests {
    use super::*;
    use crate::carcara_cross_check::CrossCheck;

    /// Build the strict-checked `Proved` result the gate receives (the same shape
    /// `unsat_to_result` constructs once ay's strict checker has accepted).
    fn strict_proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: SOLVER_NAME.into(),
            time_ms: 7,
            strength: ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(vec![1, 2, 3]),
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    /// (a) Proved + Reject -> the result is NOT proved (downgraded to Unknown,
    /// fail-closed). This is the load-bearing soundness case: ay and Carcara
    /// disagree, so we refuse to surface the PROVE.
    #[test]
    fn apply_carcara_gate_reject_downgrades_to_unknown() {
        let result = InProcessAyBackend::apply_carcara_gate(strict_proved(), CrossCheck::Reject, 7);
        assert!(
            !result.is_proved(),
            "Carcara Reject must downgrade Proved to non-proved (fail-closed), got: {result:?}"
        );
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(
                    reason.contains("carcara") && reason.contains("fail-closed"),
                    "downgrade reason must name the carcara cross-check fail-closed downgrade: \
                     {reason}"
                );
            }
            other => panic!("Reject must yield Unknown, got: {other:?}"),
        }
    }

    /// (b) Proved + Accept -> still Proved (both checkers agree). The gate is
    /// monotone: Accept never strengthens, it only preserves the input verdict.
    #[test]
    fn apply_carcara_gate_accept_keeps_proved() {
        let result = InProcessAyBackend::apply_carcara_gate(strict_proved(), CrossCheck::Accept, 7);
        assert!(
            result.is_proved(),
            "Carcara Accept must keep the strict-checked Proved, got: {result:?}"
        );
        match result {
            VerificationResult::Proved { strength, .. } => {
                assert_eq!(
                    strength,
                    ProofStrength::smt_unsat_strict_checked(),
                    "Accept must NOT strengthen the assurance level beyond ay's strict check"
                );
            }
            other => panic!("Accept must keep Proved, got: {other:?}"),
        }
    }

    /// (c) Proved + Unavailable -> still Proved. Carcara being absent is NOT
    /// disagreement; ay's own strict check already gated the Proved, so an
    /// unavailable second checker must NEVER introduce a false-FAIL.
    #[test]
    fn apply_carcara_gate_unavailable_keeps_proved_no_false_fail() {
        let result =
            InProcessAyBackend::apply_carcara_gate(strict_proved(), CrossCheck::Unavailable, 7);
        assert!(
            result.is_proved(),
            "Carcara Unavailable must keep ay's strict-checked Proved (no false-FAIL when \
             carcara is absent), got: {result:?}"
        );
    }
}

/// Direct native FP-to-BV measurements at the parent-pinned AY revision.
/// These probes bypass the router's qualification gate. AY 41a20c2abd06
/// replaced host-u64 bounds with BigInt bounds: an encode sweep and exact
/// pinned-operand models now guard that improvement. Encoding a NaN probe
/// alone does not establish conversion correctness or expand proof authority.
#[cfg(test)]
mod fp_to_bv_native_boundary_measurement {
    use trust_types::{Formula, RoundingMode};

    /// Whether ay encodes the saturating conversion at `width` without
    /// panicking. `false` means "outside the native domain", by either route:
    /// a panic in the blaster, or a lowering this bridge refuses.
    ///
    /// The probe is `Eq(FpToSbv/FpToUbv(NaN, w), (_ bv0 w))`: well-sorted at
    /// every width, ground, and small, so what it measures is whether ay can
    /// ENCODE the node at all, not whether it decides anything about it.
    fn native_encodes(width: u32, signed: bool) -> bool {
        use ay_bindings::AYProgram;
        use ay_bindings::execute_direct::execute_incremental;

        let rm = Box::new(Formula::FpRoundingMode(RoundingMode::RNE));
        let value = Box::new(Formula::FpNaN { eb: 11, sb: 53 });
        let conv = if signed {
            Formula::FpToSbv { rm, value, width, eb: 11, sb: 53 }
        } else {
            Formula::FpToUbv { rm, value, width, eb: 11, sb: 53 }
        };
        let formula = Formula::Eq(Box::new(conv), Box::new(Formula::BitVec { value: 0, width }));

        // ay's executor carries shared, non-reentrant state; take the same lock
        // the in-process backend does.
        let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());

        let outcome = crate::test_panic_hook::catch_unwind_silently(|| {
            let mut program = AYProgram::new();
            // The NATIVE lane's own name, not the transcript's: this probe
            // drives `execute_incremental`, so a name `parse_logic` refuses
            // would report "did not encode" for a header defect rather than
            // for the encoding boundary this measures.
            program.set_logic(crate::in_process_ay_backend::native_lane_logic(
                crate::smt2_export::formula_features(&formula),
            ));
            let Ok(expr) = trust_types::ay_bridge::formula_to_expr(&formula) else {
                return false;
            };
            program.assert(expr);
            program.check_sat();
            execute_incremental(&program).is_ok()
        });

        outcome.unwrap_or(false)
    }

    /// The widths in `1..=limit` that encode, and the widths that do not.
    fn sweep(signed: bool, limit: u32) -> (Vec<u32>, Vec<u32>) {
        let mut ok = Vec::new();
        let mut bad = Vec::new();
        for w in 1..=limit {
            if native_encodes(w, signed) { ok.push(w) } else { bad.push(w) }
        }
        (ok, bad)
    }

    /// Re-measured after AY's BigInt-bound fix: both arms encode the entire
    /// sampled range and selected widths beyond the old host-word boundary.
    #[test]
    fn native_conversion_encodes_the_measured_range_after_bigint_bounds() {
        for signed in [true, false] {
            let (ok, bad) = sweep(signed, 127);
            assert_eq!(ok, (1..=127).collect::<Vec<_>>(), "signed={signed}");
            assert!(bad.is_empty(), "signed={signed}: {bad:?}");
            for width in [128, 200] {
                assert!(native_encodes(width, signed), "width={width}, signed={signed}");
            }
        }
    }

    /// f64 bit patterns for the exactly-representable powers of two the
    /// unsigned probes need. `2^64` is THE distinguishing value: it crosses
    /// the old host-u64 boundary.
    const F64_TWO_POW_63: u128 = 0x43E0_0000_0000_0000;
    const F64_TWO_POW_64: u128 = 0x43F0_0000_0000_0000;
    const F64_TWO_POW_100: u128 = 0x4630_0000_0000_0000;

    /// How the probe hands ay the f64 it converts.
    #[derive(Clone, Copy, Debug)]
    enum Operand {
        /// The `FpConst` itself, which ay's word-level FP rewriter folds.
        Constant,
        /// A variable `x` pinned to the constant by `fp.eq`, which the
        /// rewriter cannot fold, so the node reaches ay's bit-blaster.
        Pinned,
    }

    /// Ask ay for a MODEL of `FpToUbv(<f64 bit pattern>, width) == r` and
    /// return the value it assigns `r`, or `None` when it returns no model.
    ///
    /// (The value is read out of the rendered counterexample rather than
    /// through a typed accessor — this is a measurement harness, and the
    /// rendering is the same one the backend hands a user.)
    fn unsigned_conversion_model(bits: u128, width: u32, operand: Operand) -> Option<String> {
        use ay_bindings::execute_direct::{self, ExecuteTypedResult};

        let constant = || Box::new(Formula::FpConst { bits, eb: 11, sb: 53 });
        let x = || Box::new(Formula::Var("x".into(), trust_types::Sort::Float { eb: 11, sb: 53 }));
        let conversion = |value| {
            Formula::Eq(
                Box::new(Formula::FpToUbv {
                    rm: Box::new(Formula::FpRoundingMode(RoundingMode::RNE)),
                    value,
                    width,
                    eb: 11,
                    sb: 53,
                }),
                Box::new(Formula::Var("r".into(), trust_types::Sort::BitVec(width))),
            )
        };
        let probe = match operand {
            Operand::Constant => conversion(constant()),
            Operand::Pinned => Formula::And(vec![Formula::FpEq(x(), constant()), conversion(x())]),
        };

        let backend = super::InProcessAyBackend::new().with_timeout(60_000);
        let program = backend.build_program(&probe).ok()?;

        let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        let outcome = crate::test_panic_hook::catch_unwind_silently(|| {
            let outcomes = execute_direct::execute_incremental(&program).ok()?;
            let last = outcomes.last()?;
            let ExecuteTypedResult::Counterexample(cex) = &last.result else {
                return None;
            };
            let rendered = format!("{:?}", super::counterexample_from_ay_model(cex));
            // `r`'s value by name: a `Pinned` model also assigns `x`.
            let digits = rendered.split("(\"r\", Uint(").nth(1)?;
            Some(digits.split(')').next()?.to_string())
        });

        outcome.ok().flatten()
    }

    /// The old u64-bound circuit stopped producing a pinned-operand model
    /// above width 65. The BigInt bounds now preserve the exact value across
    /// that boundary, while the guarded expansion still saturates at width 64.
    #[test]
    fn pinned_unsigned_operands_keep_exact_values_above_the_old_u64_bound() {
        let model = |bits, w| unsigned_conversion_model(bits, w, Operand::Pinned);
        for w in [64u32, 65, 66, 70, 80, 128] {
            assert_eq!(
                model(F64_TWO_POW_63, w).as_deref(),
                Some((1u128 << 63).to_string()).as_deref(),
                "2^63 must convert exactly at width {w}"
            );
        }
        assert_eq!(
            model(F64_TWO_POW_64, 64).as_deref(),
            Some(((1u128 << 64) - 1).to_string()).as_deref(),
            "the guarded expansion must still saturate at width 64"
        );
        for w in [65u32, 66, 70, 80, 128] {
            assert_eq!(
                model(F64_TWO_POW_64, w).as_deref(),
                Some((1u128 << 64).to_string()).as_deref(),
                "the pinned operand must retain 2^64 at width {w}"
            );
        }
        for w in [101u32, 128] {
            assert_eq!(
                model(F64_TWO_POW_100, w).as_deref(),
                Some((1u128 << 100).to_string()).as_deref(),
                "the pinned operand must retain 2^100 at width {w}"
            );
        }
        assert_eq!(
            model(F64_TWO_POW_100, 80).as_deref(),
            Some(((1u128 << 80) - 1).to_string()).as_deref(),
            "an out-of-range pinned operand must saturate, not truncate"
        );
    }

    /// Constant operands are folded exactly before bit-blasting. Keep this
    /// separate from the pinned-variable probes above so a successful fold
    /// cannot conceal a regression in the native circuit's wide bounds.
    #[test]
    fn a_constant_operand_is_folded_exactly_before_the_blaster() {
        let model = |bits, w| unsigned_conversion_model(bits, w, Operand::Constant);

        assert_eq!(
            model(F64_TWO_POW_64, 64).as_deref(),
            Some(((1u128 << 64) - 1).to_string()).as_deref(),
            "at width 64 the guarded expansion clamps 2^64 to the maximum"
        );
        for w in [65u32, 66, 70, 80, 128, 200] {
            assert_eq!(
                model(F64_TWO_POW_64, w).as_deref(),
                Some((1u128 << 64).to_string()).as_deref(),
                "at width {w} ay folds the constant conversion of 2^64 exactly"
            );
        }
        // Far above the old host-u64 bound: the clamp at the width that cannot hold
        // `2^100`, and the exact value one width up.
        assert_eq!(
            model(F64_TWO_POW_100, 100).as_deref(),
            Some(((1u128 << 100) - 1).to_string()).as_deref(),
            "at width 100 the guarded expansion clamps 2^100 to the maximum"
        );
        assert_eq!(
            model(F64_TWO_POW_100, 101).as_deref(),
            Some((1u128 << 100).to_string()).as_deref(),
            "at width 101 ay folds the constant conversion of 2^100 exactly"
        );
    }
}

/// THE NATIVE LANE'S LOGIC-NAME GUARD, measured against the parser it guards.
///
/// Every test here drives the LINKED `ay_bindings::execute_direct` path — the
/// lane `build_program` feeds — rather than the `ay` binary, because the two
/// disagree about logic names and only the linked one governs here. See
/// [`NATIVE_LANE_LOGIC_VOCABULARY`].
#[cfg(test)]
mod native_lane_logic_tests {
    use ay_bindings::AYProgram;
    use ay_bindings::execute_direct::{CheckSatOutcome, execute_incremental};
    use sha2::{Digest, Sha256};
    use trust_types::logic_lattice::{LOGIC_LATTICE, Theories, logic_admits, select_logic_name};
    use trust_types::{Formula, Sort};

    use super::{
        InProcessAyBackend, NATIVE_LANE_LOGIC_VOCABULARY, native_lane_logic,
        native_lane_parses_logic, problem_smt2, select_accepted_logic,
    };
    use crate::smt2_export;

    /// A FABRICATED name, so every agreement below has a negative case. If this
    /// were ever accepted, "the parser accepts everything we ask it" would read
    /// green while meaning nothing.
    const NOT_A_LOGIC: &str = "QF_NOT_A_LOGIC";

    /// Every feature set, as the lattice's own tests enumerate them.
    fn powerset() -> Vec<Theories> {
        (0..(1u16 << Theories::BIT_COUNT)).map(Theories::from_bits).collect()
    }

    /// Whether the LINKED lane accepts `name`: a native program, that logic, a
    /// ground `1 != 1`, executed. `false` is `ExecuteError` (the
    /// `UnsupportedLogic` shape) or a panic, both of which mean "this lane
    /// cannot run under that header".
    fn lane_accepts(name: &str) -> bool {
        let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        let outcome = crate::test_panic_hook::catch_unwind_silently(|| {
            let mut program = AYProgram::new();
            program.set_logic(name);
            let one = ay_bindings::Expr::int(1);
            let other = ay_bindings::Expr::int(1);
            program.assert(one.eq(other).not());
            program.check_sat();
            execute_incremental(&program).is_ok()
        });
        outcome.unwrap_or(false)
    }

    /// A REAL name this lane still refuses, so the agreement below has a
    /// negative case that is not merely fabricated. `parse_logic` refuses
    /// `HORN` in an arm of its own — it needs CHC infrastructure, not a theory
    /// configuration — and `AYProgram::horn()` writes it, so it is a name that
    /// really reaches this parser.
    const REFUSED_REAL_NAME: &str = "HORN";

    /// REQUIREMENT 1: the vocabulary is `parse_logic`'s RULES, not a sample of
    /// its answers, and it is checked against the parser itself.
    ///
    /// RE-MEASURED 2026-09-19 at `first-party/ay` `9d2cda9c8727`. Four
    /// populations are probed — the vocabulary list, every row of
    /// `LOGIC_LATTICE` (so a row added later cannot slip past unexamined),
    /// [`REFUSED_REAL_NAME`], and the fabricated control — and
    /// [`native_lane_parses_logic`] must agree with the lane on all of them.
    /// A disagreement in EITHER direction fails: a name the list claims and the
    /// parser refuses would cost verdicts, and one the list omits and the parser
    /// accepts would push the lane onto a needlessly wide header.
    ///
    /// # WHAT THIS MEASUREMENT SAYS NOW, AND WHAT IT SAID BEFORE
    ///
    /// It used to pin SIXTEEN `LOGIC_LATTICE` rows as REFUSED — `QF_UFFP`,
    /// `FP`, `BVFP`, `QF_ANIA`, `FPLRA`, `ABVFP`, `UFBVFP`, `QF_AUFBVFP`,
    /// `QF_BVFPLRA`, `ANIA`, `AUFBVFP`, `UFBVLIA`, `BVFPLRA`, `QF_ABVFPLRA`,
    /// `QF_AUFBVNIA`, `ABVFPLRA` — each one a query ay could otherwise decide,
    /// aborted into `Unknown: unsupported logic` before it ever saw an
    /// assertion. ay `9d2cda9c8727` added `SMT_LIB_LOGICS` and all sixteen are
    /// now ACCEPTED. The refused-row list is therefore EMPTY, and that emptiness
    /// is what is pinned: if ay narrows again, a row reappears here and this
    /// test fails rather than a verdict quietly disappearing.
    ///
    /// The test does NOT rest on the fabricated control alone for its negative
    /// case — an empty refused list beside a single made-up name would be thin
    /// evidence. `HORN` is a real SMT-LIB division that this lane really
    /// refuses, and it is probed as such.
    #[test]
    fn the_native_lane_vocabulary_is_what_ay_actually_parses() {
        let mut probed = 0usize;
        let mut refused_rows = Vec::new();
        for name in NATIVE_LANE_LOGIC_VOCABULARY
            .iter()
            .copied()
            .chain(LOGIC_LATTICE.iter().map(|row| row.name))
            .chain([REFUSED_REAL_NAME, NOT_A_LOGIC])
        {
            let measured = lane_accepts(name);
            assert_eq!(
                native_lane_parses_logic(name),
                measured,
                "`{name}`: `native_lane_parses_logic` says {}, the linked ay lane says {measured} \
                 — re-derive NATIVE_LANE_LOGIC_VOCABULARY from `parse_logic`, do not patch the \
                 symptom",
                native_lane_parses_logic(name)
            );
            probed += 1;
        }
        for row in LOGIC_LATTICE {
            if !native_lane_parses_logic(row.name) {
                refused_rows.push(row.name);
            }
        }
        assert!(probed >= LOGIC_LATTICE.len(), "every row must have been probed");

        // THE TWO NEGATIVES, so nothing below is vacuous: one fabricated, one
        // real.
        assert!(!lane_accepts(NOT_A_LOGIC), "the control must be REFUSED or this test is vacuous");
        assert!(
            !lane_accepts(REFUSED_REAL_NAME),
            "`{REFUSED_REAL_NAME}` is `parse_logic`'s own refusal arm; if ay learned it, this \
             test needs a new real negative, not a deleted one"
        );

        // MEASURED 2026-09-19 at ay `9d2cda9c8727`: NO `LOGIC_LATTICE` row is
        // refused by this lane. The sixteen that were are named in this test's
        // doc; they are accepted now. Pinned as an EMPTY list rather than
        // deleted, because the emptiness is the measurement — a narrowing in ay
        // puts a name back here and fails this assertion.
        assert_eq!(
            refused_rows,
            [] as [&str; 0],
            "the native lane's parser now accepts every row; a newly refused row is a LOST \
             VERDICT and needs a measurement, not an edit here"
        );

        // …and the vocabulary is the size that measurement produced: 89 listed
        // names, with the `*DT*` spellings left to the RULE.
        assert_eq!(NATIVE_LANE_LOGIC_VOCABULARY.len(), 89);
        assert!(
            !NATIVE_LANE_LOGIC_VOCABULARY.iter().any(|name| name.contains("DT")),
            "`contains(\"DT\")` is a RULE, not a list — no `*DT*` spelling belongs in the table"
        );
        for dt in ["QF_DT", "UFDTNIRA", "QF_UFBVDT", "QF_NEVER_SEEN_DT_NAME"] {
            assert!(native_lane_parses_logic(dt), "`{dt}` must be accepted by the RULE");
        }
        for dt in ["QF_DT", "UFDTNIRA", "QF_UFBVDT", "QF_NEVER_SEEN_DT_NAME"] {
            assert!(
                lane_accepts(dt),
                "`{dt}`: the RULE must still match the parser — the last of these is FABRICATED \
                 and accepted only because `parse_logic` matches on the spelling"
            );
        }
    }

    /// THE ARRAY-AND-REAL CANDIDATES: ACCEPTED BY THIS LANE, ATTESTED BY NO
    /// SOURCE — the retired criterion pointing the OTHER way.
    ///
    /// `ALRA`, `AUFLRA`, `QF_AUFLRA` and `QF_AUFLIRA` would close the
    /// array-and-real precision gap (28 of the 256 array-and-real feature sets
    /// head `AUFNIRA`, a cardinality-7 name, and 20 of those 28 are promised
    /// nonlinearity or integers the query does not use). Driven against all
    /// three sources 2026-09-19,
    /// NONE of the four is attested: not by the standard's logic declarations
    /// [S1], not by the 2025 library release's 89 per-logic archives [S2], and
    /// not by the SMT-COMP division lists [S3]. The lattice therefore refuses
    /// all four, and `trust_types::logic_lattice`'s
    /// `the_array_and_real_gap_is_pinned_with_its_rejection` pins the cost.
    ///
    /// WHAT THIS TEST ADDS is the half that belongs HERE rather than there, and
    /// it is the half that is easy to mistake for evidence: **this lane's
    /// parser ACCEPTS all four**, measured, not assumed — they are
    /// [`NATIVE_LANE_LOGIC_VOCABULARY`] entries and `lane_accepts` agrees. A
    /// round looking for a way to close the gap will find that acceptance
    /// first and may read it as attestation. It is not. It is the same
    /// criterion the lattice retired in 2026-09-18 (a consumer's parser
    /// deciding table membership), inverted: acceptance no more makes a name an
    /// SMT-LIB logic than refusal unmakes one. Measured beside the fabricated
    /// control, so the measurement cannot go vacuously green.
    ///
    /// THE PRACTICAL CONSEQUENCE, pinned so a future row-adder can read it off:
    /// were any of the four ever ATTESTED and added as a row, this lane would
    /// pick it up immediately — `native_lane_logic` selects from the accepted
    /// sublattice and all four are already in it — so such a row would move the
    /// NATIVE header too, unlike Lever C's six, which moved only the text lane.
    #[test]
    fn the_unattested_array_and_real_names_are_parseable_here_and_still_not_rows() {
        const CANDIDATES: [&str; 4] = ["ALRA", "AUFLRA", "QF_AUFLRA", "QF_AUFLIRA"];

        for name in CANDIDATES {
            // MEASURED acceptance by the linked lane …
            assert!(
                lane_accepts(name),
                "`{name}` is expected to be parseable by this lane; if ay's `parse_logic` has \
                 changed, re-measure NATIVE_LANE_LOGIC_VOCABULARY rather than deleting this"
            );
            assert!(native_lane_parses_logic(name));
            assert!(NATIVE_LANE_LOGIC_VOCABULARY.contains(&name));
            // … and NO row, because acceptance is not attestation.
            assert_eq!(
                logic_admits(name),
                None,
                "`{name}` is accepted by this lane's parser and attested by no SMT-LIB source — \
                 the parser is not a table criterion, in either direction"
            );
        }
        // The negative case, so the acceptances above mean something.
        assert!(!lane_accepts(NOT_A_LOGIC), "the control must be REFUSED or this test is vacuous");

        // THE GAP IS STILL THERE, on this lane too: an array-over-reals query
        // with an uninterpreted function heads the same widened name here as in
        // the text lane, because `AUFNIRA` is parseable and no narrower
        // parseable row admits the set.
        let array_real_uf =
            Theories::ARRAYS.union(Theories::REALS).union(Theories::UF).union(Theories::WIDE_ARITH);
        assert_eq!(select_logic_name(array_real_uf), "AUFNIRA");
        assert_eq!(native_lane_logic(array_real_uf), "AUFNIRA");
    }

    /// The guard's ACCEPTED property, over the whole powerset: whatever the
    /// lattice names, this lane never installs a header its own parser refuses.
    #[test]
    fn the_native_lane_never_installs_a_name_its_parser_refuses() {
        for required in powerset() {
            let chosen = native_lane_logic(required);
            assert!(
                native_lane_parses_logic(chosen),
                "{required:?} -> `{chosen}`, which `parse_logic` refuses"
            );
        }
    }

    /// The guard's ADMISSIBLE property, over the whole powerset: narrowing to
    /// the parseable rows never produces a header narrower than the query.
    #[test]
    fn the_native_lane_name_admits_everything_the_query_uses() {
        for required in powerset() {
            let chosen = native_lane_logic(required);
            let admits = logic_admits(chosen).expect("the guard only ever returns a table row");
            assert!(
                required.is_subset_of(admits),
                "{required:?} -> `{chosen}`, which admits {admits:?} and not the whole record"
            );
        }
    }

    /// THE SAFETY PROPERTY, and the reason this guard cannot move a verdict that
    /// exists today: wherever the unrestricted selector already names something
    /// this parser accepts, the guard returns that same name.
    ///
    /// # AT THIS PIN THE GUARD IS A TOTAL NO-OP, AND THAT IS THE MEASUREMENT
    ///
    /// RE-MEASURED 2026-09-19 at ay `9d2cda9c8727` over all 1024 feature sets
    /// (re-run unchanged over the 2048 of the array-shape bit, 2026-09-21):
    /// the guard differs from `select_logic_name` for ZERO of them, because
    /// every `LOGIC_LATTICE` row is now parseable (see
    /// [`the_native_lane_vocabulary_is_what_ay_actually_parses`]). Before the
    /// bump it rescued 76 of the 1024 and replaced 18 distinct
    /// `(refused -> accepted)` pairs; both counts are now zero and empty.
    ///
    /// THE GUARD IS NOT DELETED, AND THIS TEST IS WHY. A no-op guard costs one
    /// table scan and buys the alarm: if ay ever narrows `parse_logic` again,
    /// `differed` goes non-zero and this test fails HERE — loudly, in a unit
    /// test — instead of the lane silently opening on a wider header, or, for a
    /// future row `parse_logic` does not know, aborting the solve outright.
    /// `HORN` is still refused, so the narrowing direction is not hypothetical.
    ///
    /// # WHAT THAT DID TO LEVER C, re-measured rather than inherited
    ///
    /// This test used to prove that the six `*BVLIA`/`*BVFPLRA`/`*BVNIA` rows
    /// Lever C added "move the text lane and nothing else": they moved 53
    /// feature sets in the text lane and ZERO here, because this lane could not
    /// parse any of the six. It can parse all six now, so the SAME 53 sets move
    /// here too — measured below, with the count and the name pairs pinned. The
    /// property that replaced it is stronger and simpler: the two lanes now
    /// agree on the header for every feature set.
    #[test]
    fn the_guard_is_a_no_op_wherever_the_table_already_names_something_parseable() {
        let mut differed = 0usize;
        let mut replaced: Vec<(&str, &str)> = Vec::new();
        for required in powerset() {
            let table = select_logic_name(required);
            let native = native_lane_logic(required);
            if native_lane_parses_logic(table) {
                assert_eq!(
                    native, table,
                    "{required:?}: the table's `{table}` is parseable, so the guard must not \
                     have moved it to `{native}`"
                );
                continue;
            }
            differed += 1;
            assert!(
                native_lane_parses_logic(native),
                "{required:?}: `{table}` is refused and its replacement `{native}` is too"
            );
            if !replaced.contains(&(table, native)) {
                replaced.push((table, native));
            }
        }
        replaced.sort_unstable();

        // MEASURED 2026-09-19: the guard rescues NOTHING, because there is
        // nothing left to rescue. Was 76 of 1024 at the previous ay pin.
        assert_eq!(differed, 0, "feature sets the guard rescues, of 2048");
        assert_eq!(
            replaced,
            [] as [(&str, &str); 0],
            "the guard's replacement map is empty: every table name is parseable"
        );

        // LEVER C NOW MOVES THIS LANE TOO, and by exactly the amount it moves
        // the text lane. Checked directly, by re-running the guard's scan over
        // the table MINUS those six and counting where the answer differs.
        let lever_c =
            ["QF_BVFPLRA", "UFBVLIA", "BVFPLRA", "QF_ABVFPLRA", "QF_AUFBVNIA", "ABVFPLRA"];
        for name in lever_c {
            assert!(
                native_lane_parses_logic(name),
                "`{name}`: Lever C's rows are parseable here now; that is the whole change"
            );
        }
        let mut moved = 0usize;
        let mut moves: Vec<(&str, &str)> = Vec::new();
        for required in powerset() {
            let without_lever_c = LOGIC_LATTICE
                .iter()
                .filter(|row| !lever_c.contains(&row.name))
                .filter(|row| native_lane_parses_logic(row.name))
                .filter(|row| required.is_subset_of(row.admits))
                .min_by_key(|row| row.admits.len())
                .map_or("ALL", |row| row.name);
            let native = native_lane_logic(required);
            if native != without_lever_c {
                moved += 1;
                if !moves.contains(&(without_lever_c, native)) {
                    moves.push((without_lever_c, native));
                }
            }
        }
        moves.sort_unstable();
        // Still 53 of the 2048 after the array-shape bit: every set the six
        // rows capture carries `BITVECTORS`, and no `WIDE_ARRAY`-bearing set
        // can reach a `*BV*` row, so the doubled powerset adds no movers.
        assert_eq!(moved, 53, "Lever C's rows move the NATIVE header for this many of the 2048");
        assert_eq!(
            moves,
            [
                ("ALL", "ABVFPLRA"),
                ("ALL", "BVFPLRA"),
                ("ALL", "QF_ABVFPLRA"),
                ("ALL", "QF_AUFBVNIA"),
                ("ALL", "QF_BVFPLRA"),
                ("ALL", "UFBVLIA"),
                ("AUFNIRA", "ABVFPLRA"),
                ("AUFNIRA", "QF_ABVFPLRA"),
            ],
            "what Lever C's rows move the native header FROM and TO, pinned"
        );
    }

    /// THE NARROWING IS REAL — pinned against a vocabulary chosen to exercise it.
    ///
    /// The test above measures that the guard rescues NOTHING at this pin, which
    /// is the good news and also the problem: with the accepted sublattice equal
    /// to the lattice, every assertion about the guard is satisfied by a function
    /// that does no narrowing at all. Deleting the `accepts` filter from
    /// [`select_accepted_logic`] passed the entire suite.
    ///
    /// So the narrowing is measured here directly, by handing the SAME selector a
    /// vocabulary that refuses a row and requiring the answer to move off it.
    /// Four things are checked:
    ///
    /// * a feature set whose minimal row is refused is answered with a DIFFERENT,
    ///   accepted name — this one FAILS if the filter is deleted, and it is the
    ///   assertion that closes the gap;
    /// * that replacement still ADMITS everything the feature set requires, so
    ///   narrowing the vocabulary never produces a header narrower than its
    ///   content — the property the whole guard exists to preserve;
    /// * with only `ALL` accepted, every one of the 2048 sets is answered `ALL`;
    /// * with NOTHING refused, the selector reproduces `select_logic_name` over
    ///   all 2048 — so the accepting predicate is the only thing that can ever
    ///   make the native lane and the text lane disagree on a header.
    ///
    /// This is a property of the selector, not a claim about ay: it stays true
    /// and stays meaningful whatever `parse_logic` learns or forgets next.
    #[test]
    fn the_narrowing_is_real_under_a_restricted_vocabulary() {
        // `QF_UF` is the minimal row for the bare-UF record, and it is what the
        // unrestricted selector answers.
        let uf_only = Theories::UF;
        assert_eq!(select_logic_name(uf_only), "QF_UF", "the unrestricted minimum for {uf_only:?}");
        assert_eq!(
            native_lane_logic(uf_only),
            "QF_UF",
            "against the live parser the guard is a no-op, as the test above measures"
        );

        // Refuse exactly that row and the selector must move to another accepted
        // row that still admits UF — never stay, and never narrow.
        let without_qf_uf = select_accepted_logic(uf_only, |name| name != "QF_UF");
        assert_ne!(
            without_qf_uf, "QF_UF",
            "the accepting predicate REFUSES `QF_UF`; a selector that still answers it is not \
             narrowing at all — the `accepts` filter has been lost"
        );
        let row = LOGIC_LATTICE
            .iter()
            .find(|row| row.name == without_qf_uf)
            .expect("the replacement is a row of the lattice");
        assert!(
            uf_only.is_subset_of(row.admits),
            "`{without_qf_uf}` replaced `QF_UF` but does not admit UF — a header narrower than \
             its own content is the one outcome the guard must never produce"
        );

        // The same, over the whole powerset, against the harshest vocabulary
        // that is still total: `ALL` alone.
        for required in powerset() {
            assert_eq!(
                select_accepted_logic(required, |name| name == "ALL"),
                "ALL",
                "{required:?}: with only `ALL` accepted there is no other answer"
            );
        }

        // And the converse direction: accepting everything reproduces the
        // unrestricted table exactly, over all 2048 — so the guard's narrowing
        // is the ONLY thing that can ever make the two lanes disagree.
        for required in powerset() {
            assert_eq!(
                select_accepted_logic(required, |_| true),
                select_logic_name(required),
                "{required:?}: with nothing refused this must BE `select_logic_name`"
            );
        }
    }

    // ── The ten defect shapes ────────────────────────────────────────────────
    //
    // One formula per row the native lane refused BEFORE this guard, each built
    // so its theory record selects exactly that row. The construction is checked
    // rather than asserted: `the_text_lane_still_writes_the_precise_name` fails
    // if a formula drifts off its target, so the sweep below can never go
    // vacuously green by testing the wrong shape.

    fn f64_var(name: &str) -> Formula {
        Formula::Var(name.to_string(), Sort::Float { eb: 11, sb: 53 })
    }

    fn bv(name: &str, width: u32) -> Formula {
        Formula::Var(name.to_string(), Sort::BitVec(width))
    }

    fn uf_bool(arg: Formula) -> Formula {
        Formula::FnApp { func: "g".to_string(), args: vec![arg], sort: Sort::Bool }
    }

    fn from_bits(inner: Formula) -> Formula {
        Formula::FpFromBits { bits: Box::new(inner), eb: 11, sb: 53 }
    }

    /// `(Array (_ BitVec 8) (_ BitVec 64))` — a bitvector-indexed array, so the
    /// ARRAYS bit arrives without dragging INTS in with it.
    fn bv_array() -> Formula {
        Formula::Var(
            "mem".to_string(),
            Sort::Array(Box::new(Sort::BitVec(8)), Box::new(Sort::BitVec(64))),
        )
    }

    fn int_array() -> Formula {
        Formula::Var("heap".to_string(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)))
    }

    fn select(array: Formula, index: Formula) -> Formula {
        Formula::Select(Box::new(array), Box::new(index))
    }

    /// The ten `(name, formula)` pairs, one per row the native lane REFUSED at
    /// ay c4ade436 that some feature set actually selects.
    ///
    /// Past tense deliberately: ay 9d2cda9c8 (2026-09-19) taught `parse_logic`
    /// all sixteen names, so none of these is refused today. The shapes are
    /// kept because they are the corpus that proves it — the tests below drive
    /// each one under its PRECISE name and require the header abort to be gone,
    /// so if ay narrows again this list is what catches it.
    fn defect_shapes() -> Vec<(&'static str, Formula)> {
        let sym = trust_types::Symbol::intern;
        vec![
            // {UF, Floats}
            (
                "QF_UFFP",
                Formula::And(vec![
                    uf_bool(f64_var("x")),
                    Formula::Not(Box::new(uf_bool(f64_var("x")))),
                ]),
            ),
            // {Quantifiers, Floats}
            (
                "FP",
                Formula::Forall(
                    vec![(sym("q"), Sort::Float { eb: 11, sb: 53 })],
                    Box::new(Formula::FpIsNaN(Box::new(Formula::Var(
                        "q".to_string(),
                        Sort::Float { eb: 11, sb: 53 },
                    )))),
                ),
            ),
            // {Quantifiers, BitVectors, Floats}
            (
                "BVFP",
                Formula::Forall(
                    vec![(sym("q"), Sort::BitVec(64))],
                    Box::new(Formula::FpIsNaN(Box::new(from_bits(bv("q", 64))))),
                ),
            ),
            // {Nonlinear, Arrays, Ints, WideArith}
            (
                "QF_ANIA",
                Formula::Gt(
                    Box::new(Formula::Mul(
                        Box::new(select(int_array(), Formula::Int(0))),
                        Box::new(select(int_array(), Formula::Int(1))),
                    )),
                    Box::new(Formula::Int(0)),
                ),
            ),
            // {Quantifiers, Reals, Floats, WideArith}
            (
                "FPLRA",
                Formula::Forall(
                    vec![(sym("q"), Sort::Real)],
                    Box::new(Formula::And(vec![
                        Formula::Gt(
                            Box::new(Formula::Add(
                                Box::new(Formula::Var("q".to_string(), Sort::Real)),
                                Box::new(Formula::Var("q".to_string(), Sort::Real)),
                            )),
                            Box::new(Formula::Var("q".to_string(), Sort::Real)),
                        ),
                        Formula::FpIsNaN(Box::new(Formula::FpNaN { eb: 11, sb: 53 })),
                    ])),
                ),
            ),
            // {Quantifiers, Arrays, BitVectors, Floats}
            (
                "ABVFP",
                Formula::Forall(
                    vec![(sym("q"), Sort::BitVec(8))],
                    Box::new(Formula::FpIsNaN(Box::new(from_bits(select(bv_array(), bv("q", 8)))))),
                ),
            ),
            // {Quantifiers, UF, BitVectors, Floats}
            (
                "UFBVFP",
                Formula::Forall(
                    vec![(sym("q"), Sort::BitVec(64))],
                    Box::new(uf_bool(from_bits(bv("q", 64)))),
                ),
            ),
            // {Arrays, UF, BitVectors, Floats}
            (
                "QF_AUFBVFP",
                uf_bool(from_bits(select(bv_array(), Formula::BitVec { value: 0, width: 8 }))),
            ),
            // {Nonlinear, Quantifiers, Arrays, Ints, WideArith}
            (
                "ANIA",
                Formula::Forall(
                    vec![(sym("q"), Sort::Int)],
                    Box::new(Formula::Gt(
                        Box::new(Formula::Mul(
                            Box::new(select(int_array(), Formula::Var("q".to_string(), Sort::Int))),
                            Box::new(select(int_array(), Formula::Var("q".to_string(), Sort::Int))),
                        )),
                        Box::new(Formula::Int(0)),
                    )),
                ),
            ),
            // {Quantifiers, Arrays, UF, BitVectors, Floats}
            (
                "AUFBVFP",
                Formula::Forall(
                    vec![(sym("q"), Sort::BitVec(8))],
                    Box::new(uf_bool(from_bits(select(bv_array(), bv("q", 8))))),
                ),
            ),
        ]
    }

    /// REQUIREMENT 2: THE TEXT LANE IS UNCHANGED — AND THE NATIVE LANE HAS
    /// CAUGHT UP WITH IT.
    ///
    /// For every one of the ten, the canonical transcript still opens with the
    /// PRECISE SMT-LIB name — the whole evidentiary content of a `(set-logic …)`
    /// line. This is also what pins the ten formulas to their targets, so the
    /// verdict sweep below cannot test the wrong shapes.
    ///
    /// WHAT INVERTED HERE, measured 2026-09-19. This test used to assert that
    /// the native lane does NOT write these ten names, "precisely because it
    /// cannot": each was a `parse_logic` refusal and the guard replaced it. ay
    /// `9d2cda9c8727` taught the parser all ten, so the native program now opens
    /// with the SAME precise name the transcript carries — measured below, name
    /// by name, rather than argued from the guard being a no-op.
    #[test]
    fn the_text_lane_still_writes_the_precise_name() {
        for (name, formula) in defect_shapes() {
            assert_eq!(
                smt2_export::detect_logic(&formula),
                name,
                "the probe formula for `{name}` no longer selects it — fix the formula, not the \
                 expectation"
            );
            let text = problem_smt2(&formula);
            assert!(
                text.starts_with(&format!("(set-logic {name})\n")),
                "the transcript for `{name}` must still carry the precise header:\n{text}"
            );
            // …and so does the native program, which is the half that changed.
            assert!(
                native_lane_parses_logic(name),
                "`{name}` is one of the sixteen ay `9d2cda9c8727` learned; if it is refused \
                 again, re-measure NATIVE_LANE_LOGIC_VOCABULARY"
            );
            assert!(lane_accepts(name), "`{name}`: measured against the linked lane, not assumed");
            assert_eq!(
                native_lane_logic(smt2_export::formula_features(&formula)),
                name,
                "the guard has nothing left to replace for `{name}`: both lanes write it"
            );
        }
        // The negative case, so the acceptances above are not vacuous.
        assert!(!lane_accepts(NOT_A_LOGIC));
        assert!(!lane_accepts(REFUSED_REAL_NAME));
    }

    /// Everything about one native run that a change of header could disturb.
    ///
    /// `alethe_problem_smt2` is deliberately EXCLUDED from the fingerprint and
    /// compared separately in [`no_feature_set_loses_a_verdict_to_the_parser`]:
    /// it is the problem text ay authored FOR the proof, so it embeds the
    /// `(set-logic …)` line by construction and would differ for the one reason
    /// this comparison is not about.
    fn fingerprint(outcome: &CheckSatOutcome) -> String {
        let digest = |s: &str| {
            let mut hasher = Sha256::new();
            hasher.update(s.as_bytes());
            format!("{:x}", hasher.finalize())
        };
        let proof = outcome.unsat_proof.as_ref().map_or_else(
            || "proof=none".to_string(),
            |p| {
                format!(
                    "strict={:?};clean={};quality={:?};alethe={}",
                    p.strict_verdict,
                    p.clean_supported,
                    p.quality,
                    digest(&p.alethe)
                )
            },
        );
        format!(
            "result={:?}|degradation={:?}|core={:?}|{proof}",
            outcome.result, outcome.degradation, outcome.unsat_core
        )
    }

    /// Run `formula`'s native program with `logic` forced as its header, and
    /// return everything the header could have changed.
    ///
    /// The program is the one `build_program` builds — same options, same
    /// datatype registration, same declarations, same assertion — with only the
    /// `(set-logic …)` replaced, so the comparison isolates the header. An
    /// execution ERROR is a legitimate observation and is returned as one,
    /// because "this lane behaves the same under both names" has to include the
    /// case where it refuses under both.
    fn run_under(formula: &Formula, logic: &str) -> (String, Option<String>) {
        let backend = InProcessAyBackend::new().with_timeout(30_000);
        let mut program = backend.build_program(formula).expect("the probe shapes all build");
        program.set_logic(logic);
        let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        let outcomes = match execute_incremental(&program) {
            Ok(outcomes) => outcomes,
            Err(err) => return (format!("execute-error: {err}"), None),
        };
        let outcome = outcomes.last().expect("one check-sat, one outcome");
        let problem = outcome.unsat_proof.as_ref().and_then(|p| p.alethe_problem_smt2.clone());
        (fingerprint(outcome), problem)
    }

    /// The error ay's proof-source reconstruction USED to raise for ANY
    /// assertion carrying a binder, kept as a REGRESSION ALARM rather than as a
    /// description of today.
    ///
    /// `Solver::try_assert_term_with_source` demands that the retained
    /// assertion text re-elaborate to the same `TermId`. Every quantifier
    /// failed that check, because `mk_fresh_var` mints a unique binder name per
    /// occurrence and the alpha-sharing index was populated only from the
    /// surface elaborator, so a natively built quantifier was invisible to it
    /// and re-elaboration produced an alpha-VARIANT. ay `9d2cda9c8727` indexes
    /// native quantifiers into that same index — INDEXING ONLY: the soundness
    /// guard in ay's `native_assertion_source.rs` has a zero-line diff and
    /// still demands one `TermId`, so a source that really does not reconstruct
    /// the assertion is still refused.
    ///
    /// MEASURED 2026-09-19: this string appears for NONE of the shapes in this
    /// module. Both tests below assert its absence, so a regression in ay is a
    /// test failure here rather than a silent return to no-verdict.
    const BINDER_SOURCE_ABORT: &str = "execute-error: constraint execution failed: invalid \
                                       argument to assert_term_with_source: source does not \
                                       reconstruct the native assertion";

    /// REQUIREMENT 3: NO FEATURE SET IS HANDED A NAME THIS LANE REFUSES.
    ///
    /// # The teeth, re-derived 2026-09-19 from the measurement and not from the pin
    ///
    /// The claim in this test's name is a statement about ALL 2048 feature sets,
    /// so it is checked over all 2048: every distinct `(set-logic …)` name the
    /// table can emit is driven through the LINKED lane — a native `AYProgram`,
    /// that header, a ground `1 != 1`, `execute_incremental` — and every one
    /// must be ACCEPTED. That is 75 distinct names at this pin. Both negatives
    /// (`HORN` and the fabricated control) are driven in the same run, so an
    /// accepting-everything parser cannot make this green by accident, and a
    /// narrowing in ay fails it immediately.
    ///
    /// The ten shapes then carry the rest: for each, the lane no longer refuses
    /// the PRECISE name (`execute_incremental` returns no error at all, where
    /// it used to return `unsupported logic: …`), the run under that name
    /// behaves EXACTLY as the run under `ALL`, and the live backend's verdict
    /// class is pinned.
    ///
    /// # WHAT CHANGED UNDER THIS TEST, MEASURED AT ay `8946803021a3` (2026-09-21)
    ///
    /// It once recorded "three of the ten reach a verdict; the other seven hit a
    /// second, unrelated native-lane abort" — the binder source abort, which
    /// stopped every non-`QF_` name because those names are selected only by
    /// quantified feature sets. Both halves of that were fixed at ay
    /// `9d2cda9c8727` (header) and the quantifier-indexing work (binder), and
    /// [`BINDER_SOURCE_ABORT`] appears nowhere, asserted below.
    ///
    /// SEVEN of the ten now reach a solver verdict, up from four. `ABVFP`,
    /// `ANIA` and `FP` joined with ay's quantifier work: `ABVFP` previously got
    /// far enough to want a model and could not extract one for the bound
    /// variable's `(_ BitVec 8)` sort, and `ANIA` and `FP` previously answered
    /// `(incomplete quantifier-unhandled)`.
    ///
    /// # THE ROUND TRIP THIS TEST CAUGHT, AND WHY IT IS THE POINT
    ///
    /// `QF_UFFP` left the decided set at ay `7790765358` and came back at ay
    /// `6d164c617`. It is worth reading rather than treating as a wash, because
    /// the first reading of it here WAS WRONG and this test is the reason that
    /// got found out.
    ///
    /// The symptom was `unsat` becoming `(incomplete self-check-rejected)`, with
    /// ay's strict certification refusing the proof: `step t0 uses unsupported
    /// hole rule`. That reads like a gate tightening — ay declining to publish
    /// an UNSAT it cannot certify — and it was recorded here as exactly that.
    /// It was not. Diffed across the window, ay's `executor/unsat_cert.rs`,
    /// `check_strict_unsat_presentation`, the sidecar-blocking policy and
    /// ay-proof's hole rule were all BYTE-IDENTICAL. The checker never moved.
    /// What moved was the document handed to it: `7790765358` discarded an
    /// assembled proof that tripped a deny-only wire-gap screen — a screen about
    /// Alethe EXPORTABILITY, not validity — and substituted a materialized
    /// checked-SAT reconstruction whose first step prints as a non-deferred
    /// `hole`, running BEFORE `finalize_bv_source_proof`, the step that was
    /// about to make the original clean. A correct `unsat` was thrown away.
    /// ay `6d164c617` makes that substitution monotone: the reconstruction is
    /// adopted only when the strict checker accepts it, or when the assembled
    /// proof was already being rejected too. It also turned nine of ay's own
    /// red tests green.
    ///
    /// THE LESSON FOR WHOEVER READS THIS NEXT: a withheld verdict whose stderr
    /// names the certification gate is NOT evidence that the gate tightened. It
    /// is evidence about the gate's INPUT. Diff the certification path before
    /// believing the comfortable reading — and note that `QF_UFFP`'s LIVE class
    /// never moved through any of this, so only the native-outcome arm below
    /// would ever have caught it.
    ///
    /// So the ten moved THREE GAINS AND ZERO LOSSES, and both layers are pinned
    /// below, separately, because they move independently.
    ///
    /// The three that still do not decide stop for a reason MEASURED here rather
    /// than inherited, and none is a header refusal or a source-reconstruction
    /// abort: `BVFP` on `(incomplete quantifier-unhandled)`, `FPLRA` and
    /// `AUFBVFP` on a plain `incomplete`. All three are honest `unknown`s from
    /// inside the solver — a capability limit in ay, not a lost solve.
    /// [`a_binder_survives_its_own_retained_source`] is the companion
    /// measurement that establishes each binder shape's truth independently.
    ///
    /// # RE-MEASURED 2026-09-23 (D7, ay `badf3691`)
    ///
    /// ALL TEN now decide natively: `BVFP` and `FPLRA` answer `unsat` and
    /// `AUFBVFP` `sat`, each matching its hand-derived truth. And the four
    /// FP-sorted UNSAT rows (`QF_UFFP`, `FP`, `BVFP`, `FPLRA`) are now `Proved`
    /// live, at the strict-checker class and never `Certified`: decision
    /// D7 has ay export the strict-accepted Alethe document and disclose
    /// `carcara_surface = unsupported(...)` rather than refuse the export,
    /// which left these rows `Unknown` "no strict-checked proof artifact". The
    /// guarded-vs-`ALL` problem-text comparison is one-directional for the same
    /// reason the verdict comparison is: under D7 the side that GAINS a verdict
    /// is also the only side that authors a text.
    #[test]
    fn no_feature_set_loses_a_verdict_to_the_parser() {
        // (A) THE PROPERTY, over the whole powerset: every name the table can
        // emit is one this lane's parser accepts, measured against the parser.
        let mut emitted: Vec<&str> = Vec::new();
        for required in powerset() {
            let name = select_logic_name(required);
            if !emitted.contains(&name) {
                emitted.push(name);
            }
            assert_eq!(
                native_lane_logic(required),
                name,
                "{required:?}: at this pin the guard is a no-op; if it is not, re-measure"
            );
        }
        emitted.sort_unstable();
        assert_eq!(emitted.len(), 75, "distinct names the table emits over the 2048 feature sets");
        for name in &emitted {
            assert!(
                lane_accepts(name),
                "`{name}` is handed to the native lane by some feature set and the LINKED lane \\
                 REFUSES it — that feature set loses its verdict AND its artifact. Re-measure \\
                 NATIVE_LANE_LOGIC_VOCABULARY; the guard exists for exactly this."
            );
        }
        // The two negatives, so (A) cannot pass by the parser accepting anything.
        assert!(!lane_accepts(NOT_A_LOGIC), "the control must be REFUSED or this test is vacuous");
        assert!(!lane_accepts(REFUSED_REAL_NAME), "`HORN` is still refused in its own arm");

        // (B) THE TEN SHAPES, end to end.
        let mut decided = Vec::new();
        let mut undecided: Vec<(&str, String)> = Vec::new();
        let mut live: Vec<(&str, String)> = Vec::new();
        for (name, formula) in defect_shapes() {
            let guarded_name = native_lane_logic(smt2_export::formula_features(&formula));
            let (guarded, guarded_problem) = run_under(&formula, guarded_name);
            let (under_all, all_problem) = run_under(&formula, "ALL");
            // THE INVARIANT IS ONE-DIRECTIONAL: the installed name may never
            // LOSE a verdict relative to `ALL`. It MAY gain one, and since ay
            // c4cad0aa1 it does: a precise name routes to the theory it names,
            // while `ALL` makes `detect_logic_category` infer the category from
            // the ground window — which for a lone unhandled `forall` is EMPTY,
            // so it answers `QF_UF` and the FP theory never runs. Demanding
            // equality here would have demanded that trust throw that away.
            // Measured 2026-09-21: `FP` is the one row of the ten where they
            // differ, and it differs in the gaining direction.
            // An `execute-error:` is NOT a decision. Spelling this as
            // "reaches the solver AND is not unknown" rather than as
            // "not unknown" matters: `run_under` returns execution errors in
            // the same `String`, and the loose reading would let an error on
            // the guarded side satisfy the gaining direction.
            let decided_under =
                |o: &str| o.starts_with("result=") && !o.starts_with("result=Unknown");
            if guarded != under_all {
                assert!(
                    decided_under(&guarded) && !decided_under(&under_all),
                    "`{name}`: the lane installs `{guarded_name}` and it differs from `ALL` \\
                     in the LOSING direction — guarded={guarded}, all={under_all}. The guard \\
                     exists to stop exactly this."
                );
            }
            assert_ne!(
                guarded, BINDER_SOURCE_ABORT,
                "`{name}`: ay `9d2cda9c8727` fixed the binder source abort; its return is a \\
                 REGRESSION, not a new pin"
            );

            // The authored problem text is the one thing that MAY differ, and
            // only by its own header: it is the text ay wrote for the proof.
            let strip = |text: Option<String>| {
                text.map(|t| {
                    t.lines()
                        .filter(|line| !line.trim_start().starts_with("(set-logic"))
                        .collect::<Vec<_>>()
                        .join("\n")
                })
            };
            // D7 (2026-09-22): ay now authors a problem text for every UNSAT
            // its strict checker accepted, so when the guarded name DECIDES a
            // row that `ALL` leaves `unknown` (the gaining direction above —
            // `FP`, measured), only the guarded side has a text. That is the
            // same one-directional gain one layer down, and it is allowed ONLY
            // there: a text on the `ALL` side alone, or a text on the guarded
            // side for a row that did not gain, is a failure.
            match (strip(guarded_problem), strip(all_problem)) {
                (Some(guarded_text), Some(all_text)) => assert_eq!(
                    guarded_text, all_text,
                    "`{name}`: the authored problem text must differ only in its `(set-logic …)` \
                     line"
                ),
                (None, None) => {}
                (Some(_), None) => assert!(
                    guarded != under_all && decided_under(&guarded) && !decided_under(&under_all),
                    "`{name}`: only the guarded side authored a problem text, but the guarded \
                     side did not GAIN a verdict over `ALL` — guarded={guarded}, all={under_all}"
                ),
                (None, Some(_)) => panic!(
                    "`{name}`: `ALL` authored a problem text and the installed name did not — \
                     the guard LOST an artifact (guarded={guarded}, all={under_all})"
                ),
            }

            assert!(
                guarded.starts_with("result="),
                "`{name}`: the lane must reach the solver, got: {guarded}"
            );
            if guarded.starts_with("result=Unknown") {
                undecided.push((name, guarded));
            } else {
                decided.push((name, guarded));
            }

            // THE DEFECT, GONE AT ITS OWN LAYER: hand the same program the name
            // the TABLE chose and the lane runs it. This used to be
            // `Some("unsupported logic: {name}")` for every one of the ten.
            let backend = InProcessAyBackend::new().with_timeout(30_000);
            let mut program = backend.build_program(&formula).expect("builds");
            program.set_logic(name);
            let error = {
                let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
                execute_incremental(&program).err().map(|e| e.to_string())
            };
            assert_eq!(
                error, None,
                "`{name}`: ay learned this name; the lane must run it rather than refuse it"
            );

            let verdict = format!("{:?}", backend.run(&formula));
            assert!(
                !verdict.contains("unsupported logic"),
                "`{name}`: the live backend must not decline on the header: {verdict}"
            );
            assert!(
                !verdict.contains("assert_term_with_source"),
                "`{name}`: no shape may stop at the source-reconstruction abort any more: \\
                 {verdict}"
            );
            live.push((name, verdict));
        }

        // ALL TEN REACH A SOLVER VERDICT, pinned with it. Was FOUR at ay
        // `9d2cda9c8727`, the pin this corpus was first measured against.
        // `ABVFP`, `ANIA` and `FP` joined with ay's quantifier work. `QF_UFFP`
        // LEFT at ay `7790765358` and came back at ay `6d164c617`, which is a
        // round trip worth reading rather than a wash — the arm below says why.
        // `BVFP`, `FPLRA` and `AUFBVFP` joined by ay `badf3691` (superproject
        // `fa6661d85e`; first observed 2026-09-23, not bisected), each on the
        // verdict its hand-derived truth below demands.
        let names: Vec<&str> = decided.iter().map(|(name, _)| *name).collect();
        assert_eq!(
            names,
            [
                "QF_UFFP",
                "FP",
                "BVFP",
                "QF_ANIA",
                "FPLRA",
                "ABVFP",
                "UFBVFP",
                "QF_AUFBVFP",
                "ANIA",
                "AUFBVFP"
            ],
            "the shapes of the ten this lane can decide today"
        );
        for (name, outcome) in &decided {
            let expected = match *name {
                // UNSAT: `g(x) ∧ ¬g(x)` is unsatisfiable on any reading of `g`.
                "QF_UFFP" => "result=Verified",
                // UNSAT: `∀q:Float64. isNaN(q)` is false in every model (take
                // q = 0.0), so the VIOLATION formula is unsatisfiable. This is
                // the row the precise header buys — under `ALL` it is an
                // `unknown`, measured by the one-directional invariant above.
                "FP" => "result=Verified",
                // UNSAT: `∀q:bv64. isNaN(to_fp q)` is false at q = 0 (+0.0).
                "BVFP" => "result=Verified",
                // UNSAT: `∀q:Real. q+q > q ∧ isNaN(NaN)` is false at q = 0.
                "FPLRA" => "result=Verified",
                // SAT, each with a model: `heap` / `mem` / `g` are free, so the
                // violation formula has a witness.
                _ => "result=Counterexample",
            };
            assert!(
                outcome.starts_with(expected),
                "`{name}`: expected `{expected}`, got: {outcome}"
            );
        }

        // NONE DO NOT, measured at ay `badf3691`. The classifier stays so that a
        // future pin that loses one says WHY: a header refusal or a
        // source-reconstruction abort would be a regression of THIS lane, where
        // an `unknown` from inside the solver is ay's own incompleteness.
        let undecided_reasons: Vec<(&str, &str)> = undecided
            .iter()
            .map(|(name, outcome)| {
                let reason = if outcome.contains("self-check-rejected") {
                    "self-check-rejected"
                } else if outcome.contains("quantifier-unhandled") {
                    "quantifier-unhandled"
                } else if outcome.contains("model extraction failed") {
                    "model-extraction-failed"
                } else if outcome.contains("Unknown(\"incomplete\")") {
                    "incomplete"
                } else {
                    "OTHER"
                };
                (*name, reason)
            })
            .collect();
        assert_eq!(
            undecided_reasons,
            [],
            "every shape decided at ay `badf3691` (was BVFP quantifier-unhandled, FPLRA and \
             AUFBVFP incomplete, measured 2026-09-21); a shape that stops again is named here \
             with its reason"
        );

        let live_kinds: Vec<(&str, &str)> = live
            .iter()
            .map(|(name, verdict)| (*name, verdict.split_whitespace().next().unwrap_or("?")))
            .collect();
        // The four FP-sorted UNSAT rows are `Proved` on every build that claims
        // no external Carcara check (`trustc`'s among them). A
        // `carcara-crosscheck` build CLAIMS one, and pinned Carcara cannot parse
        // an FP document, so there they are refused fail-closed (`Unknown`).
        let fp_unsat_live = if cfg!(feature = "carcara-crosscheck") { "Unknown" } else { "Proved" };
        assert_eq!(
            live_kinds,
            [
                // UNSAT, strict-checked, `Proved` since D7 (2026-09-22): ay
                // now exports the Alethe artifact its strict checker accepted
                // for an FP-sorted refutation (disclosed
                // `carcara_surface=unsupported`). Was `Unknown` — "no
                // strict-checked proof artifact" — under the refuse-the-export
                // disposition. See the class assertion below.
                ("QF_UFFP", fp_unsat_live),
                ("FP", fp_unsat_live),
                // UNSAT, FP-sorted, `Proved` at the strict-checker class —
                // decided natively since ay `badf3691`, minted since D7.
                ("BVFP", fp_unsat_live),
                // A real refutation with a model.
                ("QF_ANIA", "Failed"),
                // As `BVFP`.
                ("FPLRA", fp_unsat_live),
                // GAINED at ay `8946803021a3`: previously `Unknown`, the model
                // extraction having failed for the bound `(_ BitVec 8)`.
                ("ABVFP", "Failed"),
                // Quantified, and decided. This read
                // `Unknown … assert_term_with_source` before ay `9d2cda9c8727`.
                ("UFBVFP", "Failed"),
                ("QF_AUFBVFP", "Failed"),
                // GAINED at ay `8946803021a3`: previously
                // `(incomplete quantifier-unhandled)`.
                ("ANIA", "Failed"),
                // SAT (`g` is free), with a model, since ay `badf3691`.
                ("AUFBVFP", "Failed"),
            ],
            "the live backend's verdict class for each of the ten is pinned"
        );

        // NO ROW MAY REGRESS. The live verdict class at ay `c4cad0aa11a7`,
        // written down so a future bump is checked against it in the direction
        // that matters rather than merely re-pinned. `Failed` and `Proved` are
        // decided; `Unknown` is not. A row that was decided and is not any more
        // fails HERE, with its own name, whatever else moved.
        // `QF_UFFP` and `FP` joined at D7 (2026-09-22), `BVFP`, `FPLRA` and
        // `AUFBVFP` at ay `badf3691`: a future pin that quietly returns any of
        // them to `Unknown` is a capability loss, named here.
        let previously_decided =
            ["QF_ANIA", "UFBVFP", "QF_AUFBVFP", "QF_UFFP", "FP", "BVFP", "FPLRA", "AUFBVFP"];
        for name in previously_decided {
            if cfg!(feature = "carcara-crosscheck")
                && ["QF_UFFP", "FP", "BVFP", "FPLRA"].contains(&name)
            {
                // Refused by the Carcara-claiming consumer, asserted below.
                continue;
            }
            let (_, verdict) = live
                .iter()
                .find(|(shape, _)| *shape == name)
                .expect("every pinned name is one of the ten");
            assert!(
                !verdict.starts_with("Unknown"),
                "`{name}` reached a live verdict at the previous ay pin and does not now: \
                 {verdict}. This is a capability LOSS — find what took it before re-pinning."
            );
        }

        // AND THE SAME GUARD ONE LAYER DOWN, where the round trip actually
        // happened. `QF_UFFP`'s LIVE class never moved — `Unknown` before ay
        // `7790765358` took its native verdict, `Unknown` after ay `6d164c617`
        // gave it back — so the live table above would have caught NEITHER
        // event. The native outcome is what moved, and this is what watches it.
        // A pin that only reads the top layer is a pin with a blind spot; this
        // is the patch over that blind spot, and it is the arm that fails if ay
        // ever re-breaks the checked-SAT retention.
        for name in ["QF_UFFP", "FP"] {
            let (_, outcome) = decided
                .iter()
                .find(|(shape, _)| *shape == name)
                .unwrap_or_else(|| panic!("`{name}` decides natively at this pin and must"));
            assert!(
                outcome.starts_with("result=Verified"),
                "`{name}`: the native lane answered `unsat` here; got {outcome}"
            );
        }

        // WHAT THE TWO UNSAT ROWS ARE, AND WHAT THEY ARE NOT (D7, 2026-09-22).
        // Until ay `31c874c438` these were the rows where ay decided and trust
        // declined: ay REFUSED to export an Alethe document for an FP-sorted
        // refutation (pinned Carcara cannot parse `FloatingPoint`), so no
        // `UnsatProofArtifact` existed and both fail-closed to `Unknown` "UNSAT
        // but no strict-checked proof artifact was produced". Decision
        // D7 keeps the export and DISCLOSES the surface instead
        // (`carcara_surface = unsupported(...)`); minting reads only the strict
        // verdict, never the Alethe text or its surface.
        //
        // So the class these rows may reach is EXACTLY ay's strict-checker
        // class — `Proved` at `smt_unsat_strict_checked()` — and never
        // `Certified`: nothing on this lane re-checks the Alethe, and for FP
        // the steps ay prints as `:rule hole` are re-derived by ay's OWN FP
        // reasoning, so the checker is not independent of the solver there.
        // A `Certified` strength on either row would mean something started
        // reading the unsupported document as independent evidence — ABORT
        // (D7 abort criterion), do not re-pin. The old refusal string must be
        // gone too: its return means the export was refused again. `BVFP` and
        // `FPLRA` are FP-sorted UNSATs of the same kind (decided since ay
        // `badf3691`) and are held to the same ceiling.
        for name in ["QF_UFFP", "FP", "BVFP", "FPLRA"] {
            let (_, verdict) =
                live.iter().find(|(shape, _)| *shape == name).expect("both are among the ten");
            assert!(
                !verdict.contains("UNSAT but no strict-checked proof artifact was produced"),
                "`{name}`: ay exports a strict-checked artifact for this FP refutation since \
                 D7; the old refusal is back — got: {verdict}"
            );
            let formula = defect_shapes()
                .into_iter()
                .find(|(shape, _)| *shape == name)
                .map(|(_, formula)| formula)
                .expect("both are among the ten");
            let verdict = InProcessAyBackend::new().with_timeout(30_000).run(&formula);
            // Under `carcara-crosscheck` (not compiled into `trustc`) the
            // consumer CLAIMS an external Carcara check, and there is none for
            // an FP document: the row must be refused fail-closed, never kept.
            #[cfg(feature = "carcara-crosscheck")]
            {
                match verdict {
                    super::VerificationResult::Unknown { reason, .. } => assert!(
                        reason.contains("carcara"),
                        "`{name}`: the refusal must name the Carcara cross-check: {reason}"
                    ),
                    other => panic!(
                        "`{name}`: a Carcara-claiming build must refuse an FP-sorted \
                         (carcara_surface=unsupported) refutation, got {other:?}"
                    ),
                }
                continue;
            }
            #[allow(unreachable_code)]
            match verdict {
                super::VerificationResult::Proved { strength, native_proof_envelope, .. } => {
                    assert_eq!(
                        strength,
                        super::ProofStrength::smt_unsat_strict_checked(),
                        "`{name}`: an FP-sorted refutation is `Proved` at ay's strict-checker \
                         class and NO higher — a `Certified` here is the D7 abort criterion"
                    );
                    assert!(
                        native_proof_envelope.is_none(),
                        "`{name}`: no kernel envelope may ride on an FP-sorted row"
                    );
                }
                other => panic!(
                    "`{name}`: expected `Proved` at the strict-checker class (D7), got {other:?}"
                ),
            }
        }
    }

    /// THE BINDER SHAPES, RE-MEASURED 2026-09-19 — and each one's truth
    /// established INDEPENDENTLY before its verdict is read.
    ///
    /// This replaces a pin that said the in-process lane could not execute ANY
    /// assertion carrying a binder under `:produce-proofs`: ay retained the
    /// assertion SOURCE, re-parsed it, and a binder had no parser identity to
    /// reconstruct, so `assert_term_with_source` refused and the solve aborted
    /// with no verdict — "for a bare `(forall ((q Int)) (> q 0))` as much as for
    /// any shape here". ay `9d2cda9c8727` fixed it. THAT EXACT FORMULA is the
    /// first row below, and it now comes back `Proved`.
    ///
    /// # Reading a verdict requires knowing the truth first
    ///
    /// `VerificationCondition::formula` is the VIOLATION formula, so the solver
    /// is asked for SATISFIABILITY of the violation:
    ///
    /// * UNSAT — no violation exists — is `Proved`;
    /// * SAT — a violation exists — is `Failed`, WITH a witness.
    ///
    /// A TAUTOLOGY is therefore the trap: it is satisfiable, so it must come
    /// back `Failed` with a witness, and a `Proved` for one of the four
    /// tautologies below would be an unsoundness, not a strength. Each row
    /// carries the truth worked out by hand, from the formula alone, and the
    /// measured verdict is checked AGAINST it — so this test cannot be made
    /// green by writing down whatever ay happened to answer.
    ///
    /// # What was measured
    ///
    /// Nine binder shapes across `Int`, `Real`, `Bool` and `(_ BitVec 8)`, with
    /// `forall`, `exists`, a nested `forall`/`exists` and a two-variable binder.
    /// At ay `01b580120` (2026-10-07) ALL NINE reach a verdict and every one
    /// agrees with the hand-derived truth. NONE of the nine hits
    /// [`BINDER_SOURCE_ABORT`]. Until that pin `∀q:Bool. q` was an honest
    /// `unknown` (`(incomplete self-check-rejected)`); ay now proves it with
    /// `forall_inst :args (false)` and no hole.
    ///
    /// A `carcara-crosscheck` build (not `trustc`'s) refuses ONE of the nine,
    /// `forall-bool`, fail-closed, and the refusal is the problem the gate
    /// checks against, not a rule. ay's document assumes the binder under a
    /// spelling it renamed, `(forall ((__trust_u_q_0 Bool)) __trust_u_q_0)`,
    /// while the gate rebuilds the problem from the formula
    /// (`build_problem_smt2`), which asserts `(forall ((__trust_u_q Bool))
    /// __trust_u_q)`. Carcara fails the `assume` step ("assumption not present
    /// in the problem"). Measured: the same document is Carcara-valid against
    /// ay's own `alethe_problem_smt2`, which spells the binder `__trust_u_q_0`
    /// too. `forall-int-unsat` used to be refused for a `:rule hole` step; ay
    /// `6fb4b5310` replaced that hole with a checked bridge (`sko_forall` over
    /// `eq_simplify`, `cong`, `not_simplify`, `trans`), so it is `Proved` on
    /// every build.
    #[test]
    fn a_binder_survives_its_own_retained_source() {
        /// What the VIOLATION formula actually is, worked out by hand from the
        /// formula and nothing else.
        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        enum Truth {
            /// No model satisfies it, so `Proved` is the only correct verdict.
            Unsat,
            /// Some model satisfies it, so `Failed`-with-witness is the only
            /// correct verdict. Every tautology lands here.
            Sat,
        }

        let sym = trust_types::Symbol::intern;
        let int = |name: &str| Formula::Var(name.to_string(), Sort::Int);
        let real = |name: &str| Formula::Var(name.to_string(), Sort::Real);
        let eq = |a: Formula, b: Formula| Formula::Eq(Box::new(a), Box::new(b));
        let gt = |a: Formula, b: Formula| Formula::Gt(Box::new(a), Box::new(b));

        let shapes: Vec<(&str, Truth, Formula)> = vec![
            // `∀q:Int. q > 0` is FALSE in every model (take q = 0), so the
            // violation is unsatisfiable. THIS IS THE EXACT FORMULA the old pin
            // named as the minimal reproducer of the source abort.
            (
                "forall-int-gt0",
                Truth::Unsat,
                Formula::Forall(
                    vec![(sym("q"), Sort::Int)],
                    Box::new(gt(int("q"), Formula::Int(0))),
                ),
            ),
            // `∃q:Int. q > 0` is TRUE (take q = 1): satisfiable.
            (
                "exists-int-gt0",
                Truth::Sat,
                Formula::Exists(
                    vec![(sym("q"), Sort::Int)],
                    Box::new(gt(int("q"), Formula::Int(0))),
                ),
            ),
            // TAUTOLOGY: `∀q:Int. q = q` holds in every model, so it is
            // satisfiable and MUST be refuted with a witness.
            (
                "forall-int-tautology",
                Truth::Sat,
                Formula::Forall(vec![(sym("q"), Sort::Int)], Box::new(eq(int("q"), int("q")))),
            ),
            // `∀q:Int. q ≠ q` is false in every model: unsatisfiable.
            (
                "forall-int-unsat",
                Truth::Unsat,
                Formula::Forall(
                    vec![(sym("q"), Sort::Int)],
                    Box::new(Formula::Not(Box::new(eq(int("q"), int("q"))))),
                ),
            ),
            // `∀q:Bool. q` is false in every model (take q = false):
            // unsatisfiable. ay decides it since `01b580120`; a
            // `carcara-crosscheck` build refuses it (see the doc above).
            (
                "forall-bool",
                Truth::Unsat,
                Formula::Forall(
                    vec![(sym("q"), Sort::Bool)],
                    Box::new(Formula::Var("q".to_string(), Sort::Bool)),
                ),
            ),
            // TAUTOLOGY over a bitvector sort.
            (
                "forall-bv8",
                Truth::Sat,
                Formula::Forall(
                    vec![(sym("q"), Sort::BitVec(8))],
                    Box::new(eq(bv("q", 8), bv("q", 8))),
                ),
            ),
            // TAUTOLOGY over the reals.
            (
                "forall-real",
                Truth::Sat,
                Formula::Forall(vec![(sym("q"), Sort::Real)], Box::new(eq(real("q"), real("q")))),
            ),
            // `∀q ∃r. r > q` is TRUE over the integers (take r = q + 1):
            // satisfiable. A nested binder, so the index has to survive one.
            (
                "nested-forall-exists",
                Truth::Sat,
                Formula::Forall(
                    vec![(sym("q"), Sort::Int)],
                    Box::new(Formula::Exists(
                        vec![(sym("r"), Sort::Int)],
                        Box::new(gt(int("r"), int("q"))),
                    )),
                ),
            ),
            // TAUTOLOGY with TWO variables under one binder: commutativity.
            (
                "forall-two-binders",
                Truth::Sat,
                Formula::Forall(
                    vec![(sym("q"), Sort::Int), (sym("r"), Sort::Int)],
                    Box::new(eq(
                        Formula::Add(Box::new(int("q")), Box::new(int("r"))),
                        Formula::Add(Box::new(int("r")), Box::new(int("q"))),
                    )),
                ),
            ),
        ];

        let mut decided: Vec<(&str, &str)> = Vec::new();
        let mut undecided: Vec<&str> = Vec::new();
        for (label, truth, formula) in shapes {
            let name = native_lane_logic(smt2_export::formula_features(&formula));
            assert!(lane_accepts(name), "`{label}`: the header `{name}` must be parseable");
            let (fingerprint, _) = run_under(&formula, name);
            assert_ne!(
                fingerprint, BINDER_SOURCE_ABORT,
                "`{label}`: the binder source abort is FIXED upstream; its return is a regression"
            );
            assert!(
                fingerprint.starts_with("result="),
                "`{label}`: a binder must reach the solver, got: {fingerprint}"
            );

            let backend = InProcessAyBackend::new().with_timeout(30_000);
            let verdict = format!("{:?}", backend.run(&formula));
            assert!(
                !verdict.contains("assert_term_with_source"),
                "`{label}`: no binder may stop at the source reconstruction: {verdict}"
            );
            let kind = verdict.split_whitespace().next().unwrap_or("?");

            // THE CORRECTNESS CHECK: the verdict is read against the truth
            // derived by hand above, in both directions.
            match kind {
                "Proved" => {
                    assert_eq!(
                        truth,
                        Truth::Unsat,
                        "`{label}`: ay answered `Proved`, i.e. the violation formula is \
                         UNSATISFIABLE — but it is satisfiable. That is an UNSOUND verdict, \
                         not a stale pin."
                    );
                    decided.push((label, "Proved"));
                }
                "Failed" => {
                    assert_eq!(
                        truth,
                        Truth::Sat,
                        "`{label}`: ay answered `Failed`, i.e. the violation formula is \
                         SATISFIABLE — but it is unsatisfiable. That is an INCOMPLETE \
                         refutation, and it is wrong."
                    );
                    assert!(
                        verdict.contains("counterexample: Some"),
                        "`{label}`: a refutation must carry its witness: {verdict}"
                    );
                    decided.push((label, "Failed"));
                }
                _ => {
                    assert_eq!(
                        kind, "Unknown",
                        "`{label}`: expected a verdict or an honest unknown, got: {verdict}"
                    );
                    // The carcara arm below: the refusal must be the
                    // cross-check's, not some other unknown, and for an
                    // assumption the gate's problem does not contain, not for
                    // a hole or a rule Carcara rejected.
                    #[cfg(feature = "carcara-crosscheck")]
                    if label == "forall-bool" {
                        assert!(
                            verdict.contains("carcara N-version cross-check rejected")
                                && verdict.contains("fail-closed"),
                            "`{label}`: the refusal must be the Carcara cross-check's \
                             fail-closed downgrade: {verdict}"
                        );
                        assert!(
                            super::native_unsat_hole_steps(&backend, &formula).is_empty(),
                            "`{label}`: the refused document now carries a `:rule hole` step, \
                             which is not the refusal this arm pins. Re-measure."
                        );
                        assert!(
                            !super::native_unsat_foreign_assumptions(&backend, &formula).is_empty(),
                            "`{label}`: every assumption of ay's document is now in the problem \
                             the gate rebuilds, so the refusal is something else (a named rule \
                             Carcara rejects would be a real N-version disagreement). \
                             Re-measure before deleting or re-pinning this arm."
                        );
                    }
                    undecided.push(label);
                }
            }
        }

        // MEASURED 2026-10-07 at ay `01b580120`: all nine decide, each
        // correctly. The four tautologies are all `Failed`-with-witness, which
        // is the direction that would be an unsoundness if it flipped.
        let want_decided = vec![
            ("forall-int-gt0", "Proved"),
            ("exists-int-gt0", "Failed"),
            ("forall-int-tautology", "Failed"),
            ("forall-int-unsat", "Proved"),
            ("forall-bool", "Proved"),
            ("forall-bv8", "Failed"),
            ("forall-real", "Failed"),
            ("nested-forall-exists", "Failed"),
            ("forall-two-binders", "Failed"),
        ];
        // MEASURED 2026-10-10 at ay `ffaba97f6` (pin train P4a.1): `forall-bool` is now
        // `Proved` on the `carcara-crosscheck` build too — ay's document assumes the
        // authored binder spelling, so the Carcara re-check accepts it. The arm that
        // filtered it out of a Carcara build (docs/issues/
        // 2026-10-01-ay-alethe-hole-rule-blocks-carcara-for-datatype-and-skolem-refl.md)
        // is deleted, as it said to do.
        assert_eq!(decided, want_decided, "which binder shapes reach a verdict, and which verdict");
        let want_undecided: &[&str] = &[];
        assert_eq!(
            undecided, want_undecided,
            "every binder shape reaches a verdict, on every build"
        );
    }
}

/// Regression: `trustc-ice-2026-09-08T05_49_46-43547` (clean-kernel, trustc
/// 10f221fbe) — `invalid argument to declare_const: symbol 'kind' is already
/// bound to a different declaration`, a panic at
/// `ay_dpll::api::terms::declare_const` reached from
/// `try_harvest_flip` -> `Router::verify_all` -> `run_with_policy`.
///
/// The collision was between two DISTINCT Rust entities that the ay lane
/// spelled identically: the kernel `Expr` struct's field `kind` (lowered to a
/// datatype SELECTOR, i.e. an ay function symbol `kind`) and a local or
/// parameter `kind` (a VC free variable, declared as an ay constant `kind`).
/// Before `ay_symbol_namespace` the variable was declared bare, so ay saw a
/// constant rebinding a function symbol; ay's refusal was a panic that
/// unwound into the compiler. The namespace maps every variable to
/// `__trust_u_<name>` and every selector to a `__trust_s_` image of its
/// datatype and name, so the two stay disjoint and the same formula reaches the
/// solver and gets its honest verdict.
#[cfg(test)]
mod tests_variable_named_like_a_datatype_selector {
    use ay_bindings::Sort as AYSort;

    use super::*;

    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    /// A one-constructor struct datatype `Expr { kind: Int }` — the shape the
    /// Lever A lowering gives the kernel `Expr` (field `kind`).
    fn expr_sort() -> Sort {
        Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![("Expr".into(), vec![("kind".into(), Sort::Int)])],
        }
    }

    fn e() -> Formula {
        Formula::Var("e".into(), expr_sort())
    }

    /// `e.kind`
    fn e_kind() -> Formula {
        Formula::Sel {
            datatype: "Expr".into(),
            field: "kind".into(),
            field_sort: Sort::Int,
            arg: b(e()),
        }
    }

    /// The local `kind`, same spelling as the selector.
    fn kind() -> Formula {
        Formula::Var("kind".into(), Sort::Int)
    }

    #[test]
    fn test_variable_named_like_a_selector_is_solved_not_declined() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();

        // UNSAT: `e.kind == kind && !(e.kind == kind)` — must be Proved.
        let unsat = Formula::And(vec![
            Formula::Eq(b(e_kind()), b(kind())),
            Formula::Not(b(Formula::Eq(b(e_kind()), b(kind())))),
        ]);
        let result = backend.run(&unsat);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "a variable spelled like a datatype selector must reach the solver and be \
             refuted like any other name (the 09-08 clean-kernel ICE shape), got {result:?}"
        );

        // SAT: `e.kind == kind && kind > 3` — refuted with a witness that
        // names the SOURCE variable `kind`, not its namespaced spelling.
        let sat = Formula::And(vec![
            Formula::Eq(b(e_kind()), b(kind())),
            Formula::Gt(b(kind()), b(Formula::Int(3))),
        ]);
        match backend.run(&sat) {
            VerificationResult::Failed { counterexample: Some(cex), .. } => {
                let names: Vec<&str> =
                    cex.assignments.iter().map(|(name, _)| name.as_str()).collect();
                assert!(names.contains(&"kind"), "witness must name `kind`: {names:?}");
                assert!(
                    !names
                        .iter()
                        .any(|name| name.starts_with(ay_symbol_namespace::AY_USER_SYMBOL_PREFIX)),
                    "no namespaced spelling may leak into the witness: {names:?}"
                );
            }
            other => {
                panic!("a satisfiable violation must be refuted with a witness, got {other:?}")
            }
        }
    }

    /// Both ay-facing renderers keep the variable and the selector apart: the
    /// constant is `__trust_u_kind`, the selector is `Expr`'s `__trust_s_` image
    /// of `kind`.
    #[test]
    fn test_program_and_transcript_declare_the_variable_apart_from_the_selector() {
        let formula = Formula::Eq(b(e_kind()), b(kind()));
        let namespaced = format!("{}kind", ay_symbol_namespace::AY_USER_SYMBOL_PREFIX);
        let text = problem_smt2(&formula);
        assert!(
            text.contains(&format!("(declare-fun {namespaced} () Int)")),
            "transcript must declare the variable as `{namespaced}`: {text}"
        );
        assert!(
            !text.contains("(declare-fun kind ") && !text.contains("(declare-const kind "),
            "transcript must not declare a constant spelled like the selector: {text}"
        );
        let program = InProcessAyBackend::new()
            .build_program(&formula)
            .expect("a well-formed datatype VC builds a program")
            .to_string();
        assert!(program.contains(&namespaced), "program must declare `{namespaced}`: {program}");
    }

    /// The ay boundary itself: the PRE-namespace program — selector `kind`
    /// declared by the datatype, then a bare constant `kind` — must come back
    /// as an `ExecuteError` naming the rebinding, never as a panic that
    /// unwinds into the embedding compiler (which is what the 09-08 dump
    /// recorded, four times, from one `analysis` query).
    #[test]
    fn test_bare_constant_rebinding_a_selector_is_an_error_not_a_panic() {
        if !execute_direct::is_available() {
            return;
        }
        let formula = Formula::Eq(b(e_kind()), b(kind()));
        let defs = DatatypeDefs::collect(&formula).expect("one definition of Expr");
        let mut program = AYProgram::new();
        program.set_logic("ALL");
        for dt in defs.to_ay_declarations() {
            program.try_declare_datatype(dt).expect("Expr declares");
        }
        let _ = program.try_declare_const("kind", AYSort::int()).expect("recorded");
        let _ = program
            .try_declare_const("e", sort_to_ay_in(&expr_sort(), &defs, &mut Vec::new()))
            .expect("recorded");
        program
            .assert(formula_to_expr_with_datatype_defs(&formula, &defs).expect("well-formed term"));
        program.check_sat();
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            execute_direct::execute_incremental(&program)
        }));
        match outcome {
            Ok(Err(error)) => assert!(
                error.to_string().contains("already bound to a different declaration"),
                "the refusal must name the rebinding: {error}"
            ),
            Ok(Ok(outcomes)) => {
                panic!("ay must refuse a constant that rebinds selector `kind`, got {outcomes:?}")
            }
            Err(_) => panic!(
                "a declaration collision must surface as an ExecuteError, never a panic that \
                 unwinds into the embedding compiler"
            ),
        }
    }
}

/// DECISION_QUEUE D7 (2026-09-22): what an FP-sorted UNSAT may claim now that
/// ay EXPORTS the Alethe document its strict checker accepted and DISCLOSES
/// `carcara_surface = unsupported(...)` beside it, instead of refusing the
/// export.
///
/// The class such a row reaches is exactly ay's strict-checker class
/// (`Proved` at [`ProofStrength::smt_unsat_strict_checked`], i.e. TCB
/// `SolverRevalidated`), never `Certified`: minting reads the strict verdict,
/// never the Alethe text or its surface, and for FP the steps ay prints as
/// `:rule hole` (e.g. `FpForwardError`) are re-derived by ay's OWN FP reasoning
/// — the checker is not independent of the solver there. That makes ay's FP
/// strict-check rules load-bearing on this lane, so this module also carries
/// the STANDING ABORT INSTRUMENT the critique required:
/// [`satisfiable_fp_differential_fuzz_is_never_proved`]. If it ever fails, a
/// satisfiable FP violation formula was `Proved` — a false proof. Fix ay's
/// checker; do not re-pin, and do not bring back the refused export (that kept
/// no row out of any class — see the D7 memo).
#[cfg(test)]
mod d7_fp_alethe_surface_tests {
    use super::*;

    const F32: Sort = Sort::Float { eb: 8, sb: 24 };

    fn boxed(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    fn fvar(name: &str) -> Formula {
        Formula::Var(name.into(), F32)
    }

    fn vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "d7_fp_probe".into(),
            location: trust_types::SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// `isNaN(x) ∧ isNormal(x)` over f32: UNSAT (the classes are disjoint), and
    /// the body ay's own D7 control uses.
    fn nan_and_normal() -> Formula {
        Formula::And(vec![
            Formula::FpIsNaN(boxed(fvar("x"))),
            Formula::FpIsNormal(boxed(fvar("x"))),
        ])
    }

    /// Solve `formula` on the linked native lane and return the last outcome.
    fn native_outcome(formula: &Formula) -> ay_bindings::execute_direct::CheckSatOutcome {
        let program =
            InProcessAyBackend::new().with_timeout(20_000).build_program(formula).expect("builds");
        let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
        let mut outcomes =
            execute_direct::execute_incremental(&program).expect("the native lane executes");
        outcomes.pop().expect("one check-sat")
    }

    /// THE ROW D7 ADDS, end to end: an FP-sorted UNSAT carries a strict-Verified
    /// artifact disclosed `carcara_surface = unsupported(... FloatingPoint ...)`,
    /// and the backend mints it `Proved` at the strict-checker class — no higher.
    /// Under B (refuse the export) this was `Unknown` "UNSAT but no
    /// strict-checked proof artifact was produced".
    #[test]
    fn fp_unsat_with_unsupported_surface_is_strict_checked_proved() {
        let formula = nan_and_normal();

        let outcome = native_outcome(&formula);
        assert!(matches!(outcome.result, ExecuteTypedResult::Verified), "{outcome:?}");
        let artifact = outcome
            .unsat_proof
            .as_ref()
            .expect("D7: ay exports the strict-accepted artifact for an FP-sorted UNSAT");
        assert!(
            matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "{artifact:?}"
        );
        assert!(
            !artifact.carcara_surface.is_supported(),
            "an FP-sorted document is outside pinned Carcara's grammar and must SAY so"
        );
        let reason = artifact.carcara_surface.unsupported_reason().unwrap_or_default();
        assert!(reason.contains("FloatingPoint"), "the disclosure names the sort: {reason}");
        // Whether the document carries a step the cross-check refuses as
        // UNRECONSTRUCTED before it ever reads the surface (ay prints FP steps
        // it re-derives internally, e.g. `FpForwardError`, as `:rule hole`).
        let holey = artifact.quality.trust_count > 0
            || artifact.alethe.lines().any(|line| {
                line.contains(":rule hole")
                    || line.contains(":rule trust")
                    || (line.contains(":rule la_generic") && !line.contains(":args"))
            });
        let unreconstructed: Vec<&str> = artifact
            .alethe
            .lines()
            .filter(|line| {
                line.contains(":rule hole")
                    || line.contains(":rule trust")
                    || (line.contains(":rule la_generic") && !line.contains(":args"))
            })
            .collect();
        eprintln!(
            "d7 fp artifact: holey={holey} hole_count={} trust_count={} surface={} \
             unreconstructed={unreconstructed:?}",
            artifact.quality.hole_count, artifact.quality.trust_count, artifact.carcara_surface
        );

        let verdict = InProcessAyBackend::new().with_timeout(20_000).verify(&vc(formula.clone()));
        #[cfg(not(feature = "carcara-crosscheck"))]
        match &verdict {
            VerificationResult::Proved { strength, native_proof_envelope, .. } => {
                assert_eq!(*strength, ProofStrength::smt_unsat_strict_checked());
                assert!(native_proof_envelope.is_none(), "no kernel envelope on an FP row");
            }
            other => panic!("D7: expected strict-checked Proved, got {other:?}"),
        }
        // A Carcara-claiming build refuses it, fail-closed. The hole/trust
        // refusal stays AHEAD of the surface refusal (a holey document is
        // refused as holey whatever its surface), so which name the refusal
        // carries is decided by the document, and asserted from it.
        #[cfg(feature = "carcara-crosscheck")]
        match &verdict {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("carcara") && reason.contains("fail-closed"), "{reason}");
                if holey {
                    assert!(reason.contains("unreconstructed"), "{reason}");
                } else {
                    assert!(
                        reason.contains("carcara_surface=unsupported")
                            && reason.contains("FloatingPoint"),
                        "a hole-free FP document is refused BY ITS SURFACE: {reason}"
                    );
                }
            }
            other => panic!("a Carcara-claiming build must refuse the FP row, got {other:?}"),
        }
        // MEASURED 2026-09-23 (ay `badf3691`): the whole FP refutation is ONE
        // step, `(cl (not (and (fp.isNaN x) (fp.isNormal x)))) :rule hole`,
        // strict-`Verified` by ay's own FP reasoning — while the artifact's
        // self-reported `hole_count` is 0. That is what the TCB
        // `SolverRevalidated` row states: on FP the printed document is not
        // independent evidence. If this starts failing because ay reconstructs
        // the step, the row's FP sentence is stale — re-measure and amend it.
        assert!(
            holey,
            "the FP document no longer carries an unreconstructed step; update the TCB \
             `SolverRevalidated` FP sentence (D7) before re-pinning"
        );

        // The S1 revalidation gate re-solves it itself and mints (default build).
        #[cfg(not(feature = "carcara-crosscheck"))]
        assert!(revalidate_vc_unsat_strict(&formula, 20_000, EffortScale::BUILTIN).is_some());
    }

    /// Control: a BV-only UNSAT is `supported` — the disclosure is not a blanket
    /// `unsupported` that would make the FP assertion above vacuous — and it is
    /// `Proved` on every build.
    #[test]
    fn bv_unsat_control_has_a_supported_surface_and_is_proved() {
        let bx = Formula::Var("bx".into(), Sort::BitVec(32));
        let formula = Formula::Not(boxed(Formula::Eq(boxed(bx.clone()), boxed(bx))));
        let outcome = native_outcome(&formula);
        let artifact = outcome.unsat_proof.as_ref().expect("a BV UNSAT carries its artifact");
        assert!(
            artifact.carcara_surface.is_supported(),
            "a BV-only document is inside pinned Carcara's grammar: {:?}",
            artifact.carcara_surface
        );
        let verdict = InProcessAyBackend::new().with_timeout(20_000).verify(&vc(formula));
        assert!(verdict.is_proved(), "{verdict:?}");
    }

    /// Negative control: a SATISFIABLE FP violation is `Failed` WITH a model,
    /// never `Proved`.
    #[test]
    fn fp_lt_sat_control_is_failed_with_a_model_never_proved() {
        let formula = Formula::FpLt(boxed(fvar("x")), boxed(fvar("y")));
        match InProcessAyBackend::new().with_timeout(20_000).verify(&vc(formula.clone())) {
            VerificationResult::Failed { counterexample, .. } => {
                assert!(counterexample.is_some(), "a SAT verdict carries its witness");
            }
            VerificationResult::Proved { .. } => {
                panic!("FALSE PROOF: `x < y` is satisfiable (x=0, y=1) — D7 ABORT")
            }
            other => panic!("expected `Failed` with a model, got {other:?}"),
        }
        assert!(revalidate_vc_unsat_strict(&formula, 20_000, EffortScale::BUILTIN).is_none());
    }

    /// The strict checker is NOT a rubber stamp for FP, pinned as measured
    /// 2026-09-23: two UNSAT FP shapes are refused by ay's own self-check and
    /// fail closed. If one of these starts answering `Proved`, it is a GAIN to
    /// re-pin — but only after the fuzz below is green on the same pin.
    #[test]
    fn strict_checker_refusals_on_fp_stay_visible() {
        let x = || boxed(fvar("x"));
        let y = || boxed(fvar("y"));
        let shapes = [
            ("fp_lt_antisym", Formula::And(vec![Formula::FpLt(x(), y()), Formula::FpLt(y(), x())])),
            (
                "fp_neg_involution",
                Formula::Not(boxed(Formula::Eq(
                    boxed(Formula::FpNeg(boxed(Formula::FpNeg(x())))),
                    x(),
                ))),
            ),
        ];
        for (name, formula) in shapes {
            let verdict = InProcessAyBackend::new().with_timeout(20_000).verify(&vc(formula));
            match &verdict {
                VerificationResult::Unknown { reason, .. } => assert!(
                    reason.contains("self-check-rejected"),
                    "`{name}`: measured as ay's self-check refusal; got {reason}"
                ),
                other => panic!("`{name}`: expected the fail-closed refusal, got {other:?}"),
            }
            // Determinism plan §3.1 (review 2026-09-29): the refusal comes out of
            // ay's certification funnel, whose deferred-clause discharge is
            // counted since P4a.1 (ay ffaba97f6) and publishes a stop as that
            // stop: the refusal is the proof's, the same on every host.
            assert_eq!(
                StopCause::of_result(&verdict),
                StopCause::SolverIncomplete,
                "`{name}`: a certification refusal is the proof's: {verdict:?}"
            );
        }
    }

    // ── THE STANDING ABORT INSTRUMENT ────────────────────────────────────────

    /// Deterministic xorshift64*, so a failure reproduces from its seed.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// A term over `x`, `y` and a small constant pool, with the concrete
    /// evaluator alongside. Arithmetic uses RNE only, because that is the mode
    /// the host's `f32` implements — the evaluator IS the ground truth, so it
    /// may only contain operations it computes exactly as SMT-LIB defines them.
    #[derive(Clone, Debug)]
    enum T {
        X,
        Y,
        C(u32),
        Neg(Box<T>),
        Abs(Box<T>),
        Add(Box<T>, Box<T>),
        Sub(Box<T>, Box<T>),
        Mul(Box<T>, Box<T>),
    }

    #[derive(Clone, Debug)]
    enum A {
        Class(u8, T),
        Cmp(u8, T, T),
        /// SMT-LIB `=` on FloatingPoint: ONE NaN, and `+0 ≠ -0`.
        Same(T, T),
        Not(Box<A>),
    }

    const CONSTS: [u32; 8] = [
        0x0000_0000, // +0
        0x8000_0000, // -0
        0x3F80_0000, // 1.0
        0xBF80_0000, // -1.0
        0x7F80_0000, // +inf
        0x0000_0001, // min subnormal
        0x0080_0000, // min normal
        0x7F7F_FFFF, // max finite
    ];

    fn gen_t(rng: &mut Rng, depth: u32) -> T {
        let leaf = depth == 0 || rng.below(3) == 0;
        if leaf {
            return match rng.below(5) {
                0 | 1 => T::X,
                2 | 3 => T::Y,
                _ => T::C(CONSTS[rng.below(CONSTS.len() as u64) as usize]),
            };
        }
        let a = Box::new(gen_t(rng, depth - 1));
        match rng.below(5) {
            0 => T::Neg(a),
            1 => T::Abs(a),
            2 => T::Add(a, Box::new(gen_t(rng, depth - 1))),
            3 => T::Sub(a, Box::new(gen_t(rng, depth - 1))),
            _ => T::Mul(a, Box::new(gen_t(rng, depth - 1))),
        }
    }

    fn gen_a(rng: &mut Rng) -> A {
        let atom = match rng.below(3) {
            0 => A::Class(rng.below(7) as u8, gen_t(rng, 2)),
            1 => A::Cmp(rng.below(5) as u8, gen_t(rng, 1), gen_t(rng, 1)),
            _ => A::Same(gen_t(rng, 1), gen_t(rng, 1)),
        };
        if rng.below(3) == 0 { A::Not(Box::new(atom)) } else { atom }
    }

    fn eval_t(t: &T, x: f32, y: f32) -> f32 {
        match t {
            T::X => x,
            T::Y => y,
            T::C(bits) => f32::from_bits(*bits),
            T::Neg(a) => -eval_t(a, x, y),
            T::Abs(a) => eval_t(a, x, y).abs(),
            T::Add(a, b) => eval_t(a, x, y) + eval_t(b, x, y),
            T::Sub(a, b) => eval_t(a, x, y) - eval_t(b, x, y),
            T::Mul(a, b) => eval_t(a, x, y) * eval_t(b, x, y),
        }
    }

    fn eval_a(a: &A, x: f32, y: f32) -> bool {
        match a {
            A::Class(k, t) => {
                let v = eval_t(t, x, y);
                match k {
                    0 => v.is_nan(),
                    1 => v.is_infinite(),
                    2 => v == 0.0,
                    3 => v.is_normal(),
                    4 => v.is_subnormal(),
                    // SMT-LIB: isNegative / isPositive are FALSE on NaN.
                    5 => !v.is_nan() && v.is_sign_negative(),
                    _ => !v.is_nan() && v.is_sign_positive(),
                }
            }
            A::Cmp(k, l, r) => {
                let (l, r) = (eval_t(l, x, y), eval_t(r, x, y));
                match k {
                    0 => l == r,
                    1 => l < r,
                    2 => l <= r,
                    3 => l > r,
                    _ => l >= r,
                }
            }
            A::Same(l, r) => {
                let (l, r) = (eval_t(l, x, y), eval_t(r, x, y));
                (l.is_nan() && r.is_nan()) || l.to_bits() == r.to_bits()
            }
            A::Not(inner) => !eval_a(inner, x, y),
        }
    }

    fn lower_t(t: &T) -> Formula {
        let rne = || boxed(Formula::FpRoundingMode(trust_types::RoundingMode::RNE));
        match t {
            T::X => fvar("x"),
            T::Y => fvar("y"),
            T::C(bits) => Formula::FpConst { bits: u128::from(*bits), eb: 8, sb: 24 },
            T::Neg(a) => Formula::FpNeg(boxed(lower_t(a))),
            T::Abs(a) => Formula::FpAbs(boxed(lower_t(a))),
            T::Add(a, b) => Formula::FpAdd(rne(), boxed(lower_t(a)), boxed(lower_t(b))),
            T::Sub(a, b) => Formula::FpSub(rne(), boxed(lower_t(a)), boxed(lower_t(b))),
            T::Mul(a, b) => Formula::FpMul(rne(), boxed(lower_t(a)), boxed(lower_t(b))),
        }
    }

    fn lower_a(a: &A) -> Formula {
        match a {
            A::Class(k, t) => {
                let t = boxed(lower_t(t));
                match k {
                    0 => Formula::FpIsNaN(t),
                    1 => Formula::FpIsInfinite(t),
                    2 => Formula::FpIsZero(t),
                    3 => Formula::FpIsNormal(t),
                    4 => Formula::FpIsSubnormal(t),
                    5 => Formula::FpIsNegative(t),
                    _ => Formula::FpIsPositive(t),
                }
            }
            A::Cmp(k, l, r) => {
                let (l, r) = (boxed(lower_t(l)), boxed(lower_t(r)));
                match k {
                    0 => Formula::FpEq(l, r),
                    1 => Formula::FpLt(l, r),
                    2 => Formula::FpLe(l, r),
                    3 => Formula::FpGt(l, r),
                    _ => Formula::FpGe(l, r),
                }
            }
            A::Same(l, r) => Formula::Eq(boxed(lower_t(l)), boxed(lower_t(r))),
            A::Not(inner) => Formula::Not(boxed(lower_a(inner))),
        }
    }

    /// Candidate witnesses: every IEEE class, both signs, and some random bits.
    fn witness_pool(rng: &mut Rng) -> Vec<f32> {
        let mut pool: Vec<f32> = [
            0x0000_0000u32,
            0x8000_0000,
            0x3F80_0000,
            0xBF80_0000,
            0x4000_0000,
            0x3F00_0000,
            0x4040_0000,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_0000,
            0x0000_0001,
            0x8000_0001,
            0x007F_FFFF,
            0x0080_0000,
            0x8080_0000,
            0x7F7F_FFFF,
            0xFF7F_FFFF,
            0x3400_0000,
            0x4B80_0000,
        ]
        .into_iter()
        .map(f32::from_bits)
        .collect();
        for _ in 0..13 {
            pool.push(f32::from_bits(rng.next() as u32));
        }
        pool
    }

    /// THE D7 STANDING ABORT INSTRUMENT: a SATISFIABLE FP violation formula must
    /// never come back `Proved`, by `verify` or by the S1 revalidation gate.
    ///
    /// DIFFERENTIAL: each generated formula is first evaluated on the host's
    /// IEEE `f32` over a witness pool; a formula with a concrete witness is SAT
    /// by construction, whatever ay says. Formulas without a found witness make
    /// no claim and are only counted. Teeth, both asserted:
    /// * enough SAT cases are generated that the zero means something;
    /// * the same harness DOES produce `Proved` for a known FP UNSAT (default
    ///   build), so "never Proved" is not "the lane never proves anything".
    ///
    /// `TRUST_D7_FP_FUZZ_SEED` / `TRUST_D7_FP_FUZZ_CASES` widen a standing run.
    /// Widen with `--release`: measured 2026-09-23 (seed 7, 200 cases), a
    /// debug build spent 20+ minutes inside ay's `Sweeper::
    /// debug_verify_equivalence_claim` during one `revalidate_vc_unsat_strict`
    /// call, past the 5 s budget — a debug-only cost in ay, not a verdict.
    #[test]
    fn satisfiable_fp_differential_fuzz_is_never_proved() {
        let seed = std::env::var("TRUST_D7_FP_FUZZ_SEED")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0xD7F0_0D5E_ED00_0001)
            | 1;
        let cases = std::env::var("TRUST_D7_FP_FUZZ_CASES")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(96);
        let mut rng = Rng(seed);
        let pool = witness_pool(&mut rng);
        let backend = InProcessAyBackend::new().with_timeout(5_000);

        let (mut sat, mut failed, mut unknown, mut no_witness) = (0usize, 0usize, 0usize, 0usize);
        for case in 0..cases {
            let atoms: Vec<A> = (0..1 + rng.below(3)).map(|_| gen_a(&mut rng)).collect();
            let witness = pool.iter().find_map(|&x| {
                pool.iter().find(|&&y| atoms.iter().all(|a| eval_a(a, x, y))).map(|&y| (x, y))
            });
            let Some((wx, wy)) = witness else {
                no_witness += 1;
                continue;
            };
            sat += 1;
            let formula = if atoms.len() == 1 {
                lower_a(&atoms[0])
            } else {
                Formula::And(atoms.iter().map(lower_a).collect())
            };
            let verdict = backend.verify(&vc(formula.clone()));
            if verdict.is_proved() {
                panic!(
                    "D7 ABORT — FALSE PROOF on a satisfiable FP formula (seed={seed:#x}, \
                     case={case}): witness x={wx:?} ({:#010x}), y={wy:?} ({:#010x}); atoms={atoms:?}; \
                     verdict={verdict:?}",
                    wx.to_bits(),
                    wy.to_bits()
                );
            }
            assert!(
                revalidate_vc_unsat_strict(&formula, 5_000, EffortScale::BUILTIN).is_none(),
                "D7 ABORT — the S1 revalidation gate minted a satisfiable FP formula \
                 (seed={seed:#x}, case={case}, witness x={wx:?} y={wy:?}): {atoms:?}"
            );
            match verdict {
                VerificationResult::Failed { .. } => failed += 1,
                _ => unknown += 1,
            }
        }
        eprintln!(
            "d7 fp fuzz: seed={seed:#x} cases={cases} sat={sat} failed={failed} \
             unknown_or_other={unknown} no_witness={no_witness}"
        );
        assert!(
            sat * 2 >= cases,
            "the instrument must be dominated by SAT cases or its zero is vacuous: sat={sat} of \
             {cases}"
        );
        assert!(failed > 0, "the lane decided none of the SAT cases — the instrument is blind");

        // Positive control: this harness CAN observe a `Proved` on an FP row.
        #[cfg(not(feature = "carcara-crosscheck"))]
        assert!(
            backend.verify(&vc(nan_and_normal())).is_proved(),
            "positive control: the FP UNSAT `isNaN ∧ isNormal` must be Proved here"
        );
    }
}

/// D7 under the Carcara-claiming consumer: an `unsupported` surface is refused
/// by NAME. Pure gate logic, no live solver.
#[cfg(all(test, feature = "ay-backend", feature = "carcara-crosscheck"))]
mod d7_carcara_surface_gate_tests {
    use super::*;
    use crate::carcara_cross_check::CrossCheck;

    #[test]
    fn apply_carcara_gate_surface_unsupported_downgrades_with_reason() {
        let proved = VerificationResult::Proved {
            solver: SOLVER_NAME.into(),
            time_ms: 7,
            strength: ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };
        let offender = "sort `(_ FloatingPoint 8 24)`";
        let result = InProcessAyBackend::apply_carcara_gate(
            proved,
            CrossCheck::SurfaceUnsupported { reason: offender.to_string() },
            7,
        );
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(reason.contains("carcara_surface=unsupported"), "{reason}");
                assert!(reason.contains(offender), "the refusal names ay's offender: {reason}");
                assert!(reason.contains("fail-closed"), "{reason}");
            }
            other => panic!("an unsupported surface must never keep `Proved`: {other:?}"),
        }
    }
}

/// The `:rule hole` lines of the Alethe document ay's native lane exports for
/// the UNSAT `formula`, solved with `backend`'s program. The
/// `carcara-crosscheck` expectation arms read it to pin WHY the cross-check
/// refused: `CrossCheck::Reject` gives one reason string to a hole, a `trust`
/// step, a bare `la_generic`, Carcara's `Ok(false)` and a Carcara error, so a
/// future ay that printed a named rule Carcara rejects (a real N-version
/// disagreement) would keep the reason and pass an arm that checks the reason
/// alone (docs/issues/2026-10-01-ay-alethe-hole-rule-blocks-carcara-for-datatype-and-skolem-refl.md).
#[cfg(all(test, feature = "carcara-crosscheck"))]
fn native_unsat_hole_steps(backend: &InProcessAyBackend, formula: &Formula) -> Vec<String> {
    let program = backend.build_program(formula).expect("the UNSAT formula builds");
    let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
    let mut outcomes =
        execute_direct::execute_incremental(&program).expect("the native lane executes");
    let outcome = outcomes.pop().expect("one check-sat");
    let artifact = outcome.unsat_proof.as_ref().unwrap_or_else(|| {
        panic!("an UNSAT exports its strict-accepted artifact: {:?}", outcome.result)
    });
    eprintln!(
        "carcara arm artifact: hole_count={} trust_count={} surface={} clean_supported={} \
         alethe_problem_smt2={}",
        artifact.quality.hole_count,
        artifact.quality.trust_count,
        artifact.carcara_surface,
        artifact.clean_supported,
        if artifact.alethe_problem_smt2.is_some() { "Some" } else { "None" }
    );
    artifact.alethe.lines().filter(|line| line.contains(":rule hole")).map(str::to_owned).collect()
}

/// The `assume` terms of the Alethe document ay's native lane exports for the
/// UNSAT `formula` that do NOT occur in the problem the Carcara gate rebuilds
/// for it (`build_problem_smt2`). Carcara checks each `assume` against that
/// problem, so a term listed here is one it refuses as "assumption not present
/// in the problem". The `forall-bool` arm of
/// `a_binder_survives_its_own_retained_source` reads it to pin WHY the
/// cross-check refused, as `native_unsat_hole_steps` does for a hole.
#[cfg(all(test, feature = "carcara-crosscheck"))]
fn native_unsat_foreign_assumptions(
    backend: &InProcessAyBackend,
    formula: &Formula,
) -> Vec<String> {
    let program = backend.build_program(formula).expect("the UNSAT formula builds");
    let _guard = trust_types::ay_exec_lock().lock().unwrap_or_else(|e| e.into_inner());
    let mut outcomes =
        execute_direct::execute_incremental(&program).expect("the native lane executes");
    let outcome = outcomes.pop().expect("one check-sat");
    let artifact = outcome.unsat_proof.as_ref().unwrap_or_else(|| {
        panic!("an UNSAT exports its strict-accepted artifact: {:?}", outcome.result)
    });
    let problem = InProcessAyBackend::build_problem_smt2(formula);
    artifact
        .alethe
        .lines()
        .filter_map(|line| {
            // `(assume <id> <term>)`: the term is everything after the id,
            // less the closing parenthesis.
            let rest = line.trim().strip_prefix("(assume ")?.strip_suffix(')')?;
            Some(rest.split_once(' ')?.1.to_owned())
        })
        .filter(|term| !problem.contains(term.as_str()))
        .collect()
}

// Datatype member naming at the ay boundary (TRUST-04, TRUST-05): solver-level
// regressions over the member spellings the pipeline actually produces. A
// child module so it can drive the private `run`, like the modules above.
#[cfg(test)]
#[path = "datatype_symbol_naming_tests.rs"]
mod datatype_symbol_naming_tests;

// A `true` conjunct, `false` disjunct or unary `or` that ay's elaborator folds
// away must still be Proved (ay ba4e7b5d1, the true-under-or self-check fix).
#[cfg(test)]
#[path = "in_process_ay_backend/true_conjunct_fold_tests.rs"]
mod true_conjunct_fold_tests;

// A query's clock is charged for its work, never for its wait on AY's
// execution lock; the enclosing deadline still ends a wait (ROUTER-LOCK-CLOCK-1).
#[cfg(test)]
#[path = "in_process_ay_backend/lock_clock_tests.rs"]
mod lock_clock_tests;
