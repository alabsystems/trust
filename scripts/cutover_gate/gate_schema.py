"""trust-ir-cutover gate — executable schema, version 1.

This module IS the documented, versioned gate schema demanded by
docs/plans/2026-07-27-trust-ir-first-cutover.md (rev 4, RATIFIED-PLANNING),
whose OPEN DEFECT REGISTER states the intended resolution: prose iteration on
the gate was not converging (rev 3: 105 applied / 8 introduced, 1 fatal;
rev 4: 62 closed / 29 introduced, 4 fatal), so the gate becomes an EXECUTABLE
artifact — this schema + validate.py + the adversarial suite in
test_validate.py — and the plan's own section 3 shrinks to narrative.

Defect-register coverage (the 9 classes, quoted ids D1-D9 below, in the
register's order) and the plan-conjunct ids each validator conjunct maps to
are pinned in CONJUNCTS at the bottom.  Every conjunct in validate.py carries
its id in comments and in the verdict output, so "which defect does this
close" is machine-readable, not prose.

--------------------------------------------------------------------------
THE ARTIFACT (JSON, one file, committed in the repository it describes)
--------------------------------------------------------------------------

Top-level keys (closed set — an unknown key FAILS, section 5.4 check 1):

  schema              "trust-ir-cutover-gate/v1" (exact match required)
  phase_reached       int >= 0.  Monotone against the previous accepted
                      artifact (section 3.-0.5 rule 4).  Semantics: N means
                      "phase N's gate held and phase N is licensed/executed"
                      (P7.3: it advances in a commit at which the phase's
                      gate holds).
  ratchet_base_commit sha or null.  MUST equal the commit of the last GREEN
                      run in the runner's log, and MUST be a descendant of
                      the previously recorded base (register defect D5;
                      section 3.5 item 1 — never a remote-tracking ref).
  runs_log_head       {"seq": int, "sha256": hex} or null.  The head of the
                      runner's log as of the previous accepted run; the
                      current log must still contain that exact line at that
                      seq (truncation detection, D6 / section 3.5 item 8).
  shadow_lane_state   "required" | "severed".  Structurally tied to
                      phase_reached and to the tree probes (D8, A14a/A14c):
                      "required" iff phase_reached < 8, "severed" iff >= 8.
  lane_minimums       {"A": {"count": int, "required_from": int}, ...}
                      Lane "A" MUST be present with count >= 1 — the floor
                      is configurable but never zero (D7, section 3.1.2).
                      count may not decrease and required_from may not
                      increase against the previous artifact (check 14).
  keys                The ratchet key census (D4, section 3.5 item 2):
                      name -> {"value": number,
                               "first_seen_commit": sha or null,
                               "origin": "measured" | "declared"}
                      * name MUST match one of the four pinned polarity
                        prefixes max_/baseline_/min_/fixed_ (check 7 — a
                        key matching none is audited by nothing and FAILS;
                        this is rev 3's vacuity_floor defect).
                      * first_seen_commit: null ONLY while the key is new
                        (absent from the previous accepted artifact); the
                        next accepted artifact must pin it to the commit at
                        which the key first appeared, and the validator
                        verifies presence at that commit AND ABSENCE AT ITS
                        PARENT via git (D4).  Once pinned, immutable.
                      * creation is not relaxation (section 3.1): a new key
                        is exempt from polarity comparison; every later
                        change obeys prefix polarity.
                      * MEASURED_CREATION_KEYS (max_join_residue) must carry
                        origin == "measured": the bound is created at item
                        0.12 from the MEASURED residue and then only
                        ratchets down — a hardcoded 0 typed in before any
                        measurement is RED (D2, section 3.0.1).
  corpora             [{"id", "lane", "kind", "artifact_fields", "floors"}]
                      * lane/kind are IMMUTABLE once a corpus appears in an
                        accepted artifact (X4a; the one-word relabel attack,
                        D7).
                      * artifact_fields: field -> {"path" (repo-relative),
                        "sha256", "line_count"}.  A15 discipline as repaired
                        for D1: every field must EXIST and HASH-MATCH;
                        "non-empty" is demanded only where the field's floor
                        in "floors" is > 0; an empty artifact hashes to the
                        empty-file digest (EMPTY_SHA256) and is green when
                        its floor is 0.  This is the satisfiability repair:
                        rev 4's A15 ("every field non-empty") conjoined with
                        the plan's own zero-targets was UNSATISFIABLE.
                      * floors: field -> int ("baseline_<field>_rows"; may
                        only rise — polarity is audited with the keys).
  oracles             name -> {"path", "sha256", "line_count"} for each
                      oracle whose window (pinned in ORACLES below, NOT in
                      the artifact — the schedule is schema-owned so an
                      author cannot edit an oracle out of existence) covers
                      phase_reached.  Liveness: file exists, hash matches,
                      line_count >= 1 (baseline_preauthored_expectations
                      floor, A18).  D9: the differential/conformance suite
                      is a REQUIRED artifact with its own liveness conjunct
                      until the phase that formally retires it.

Forbidden top-level keys: any member of FORBIDDEN_SOAK_KEYS.  The soak is
computed ONLY from the runner's append-only log; an author-provided soak
list is rejected outright (D6).

--------------------------------------------------------------------------
THE RUNNER'S LOG (runs.log, append-only, hash-chained)
--------------------------------------------------------------------------

One JSON object per line:
  {"seq": i, "prev": sha256-of-previous-raw-line or "genesis",
   "commit": HEAD-at-run-time, "utc": iso8601, "verdict": "green"|"red",
   "failed": [conjunct ids]}

The VALIDATOR ITSELF appends a record on every run — red or green — before
emitting its decision (D6: "only green runs get recorded" is the defect;
every run is recorded by the runner, and the soak reads this log, never an
author list).  The chain makes edits detectable; runs_log_head makes
truncation below the previously recorded head detectable; soak_run rows at
the base are thereby a prefix of HEAD's (section 3.5 item 8).

--------------------------------------------------------------------------
TREE PROBES (probes.json — pluggable, fail-closed)
--------------------------------------------------------------------------

  {"authority_capability_present": "yes"|"no"|"unavailable",
   "shadow_severed":               "yes"|"no"|"unavailable",
   "shadow_present":               "yes"|"no"|"unavailable"}

D3's fix shape verbatim: phase_reached is checked as a STRUCTURAL
BICONDITIONAL against tree state — authority capability present <=> phase
>= 7 (AUTHORITY_PHASE); shadow severed <=> phase >= 8 (SHADOW_SEVERED_
PHASE).  The probes are pluggable checks (in-tree they become structural
greps over crate_module.rs's DirectObligationCapability and the presence of
differential.rs / the shadow publish path); a missing or "unavailable"
answer is RED, never skipped — section 3.-0.5 rule 1, "an unevaluable
conjunct is RED".

--------------------------------------------------------------------------
EXIT DISCIPLINE
--------------------------------------------------------------------------

validate.py exits 0 iff every conjunct is green; 1 otherwise, printing one
row per conjunct: id, green|red|unevaluable, detail, and the defect /
plan-conjunct ids it maps to.  "unevaluable" is a reported status but a RED
outcome (rule 1).
"""

# Schema version.  Bump only with a documented migration.
SCHEMA_VERSION = "trust-ir-cutover-gate/v1"

# sha256 of zero bytes — the empty-file digest the D1 fix shape names:
# "an empty artifact hashes to the empty-file digest" rather than failing.
EMPTY_SHA256 = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

# Closed top-level key set (section 5.4 check 1: unknown keys are an error).
TOP_LEVEL_KEYS = frozenset(
    [
        "schema",
        "phase_reached",
        "ratchet_base_commit",
        "runs_log_head",
        "shadow_lane_state",
        "lane_minimums",
        "keys",
        "corpora",
        "oracles",
    ]
)

# D6: an author-provided soak list is rejected; the soak reads the runner's
# log.  Any of these appearing in the artifact is RED.
FORBIDDEN_SOAK_KEYS = frozenset(
    ["soak", "soak_runs", "soak_log", "soak_status", "soak_complete"]
)

# The four pinned polarity prefixes (section 3.1).  A ratchet-tracked numeric
# key matching none of these fails validator check 7 — rev 3's vacuity_floor
# matched none and was therefore audited by nothing.
POLARITY_PREFIXES = ("max_", "baseline_", "min_", "fixed_")

# D2: keys whose CREATION value must come from a measurement (item 0.12
# creates max_join_residue from the MEASURED residue; a hardcoded 0 typed in
# before measurement is RED).
MEASURED_CREATION_KEYS = frozenset(["max_join_residue"])

# D3 fix shape, verbatim from the register:
#   authority capability present  <=>  phase_reached >= 7
#   shadow severed                <=>  phase_reached >= 8
AUTHORITY_PHASE = 7
SHADOW_SEVERED_PHASE = 8

# D9: oracle liveness windows are SCHEMA-pinned, not artifact fields, so the
# schedule cannot be edited out from under the gate.  (from, until): required
# while from <= phase_reached < until; until=None means never retired.
#   differential — the R-prod adjudication oracle; formally retired by item
#     8.5 (the same event as shadow severance), i.e. at SHADOW_SEVERED_PHASE.
#   conformance  — A18's authored-expectation suite; created by item 2.1
#     (binds from phase 2) and PERMANENT (it is the only oracle after 8.5).
ORACLES = {
    "differential": {"required_from_phase": 0, "required_until_phase": SHADOW_SEVERED_PHASE},
    "conformance": {"required_from_phase": 2, "required_until_phase": None},
}

# Valid probe answers.
PROBE_ANSWERS = frozenset(["yes", "no", "unavailable"])
PROBE_NAMES = ("authority_capability_present", "shadow_severed", "shadow_present")

# Soak parameters (section 3.8.1) — reported informationally by the
# validator; consumed by phase gates, never by a conjunct (acyclicity rule).
SOAK_RUNS = 8
SOAK_DAYS = 28

# ---------------------------------------------------------------------------
# The conjunct census: every validator conjunct, the register defect(s) it
# closes, and the plan-conjunct / section ids it implements.  Requirement 3:
# "every conjunct maps to a register defect or a section-3 conjunct by ID".
# ---------------------------------------------------------------------------
CONJUNCTS = {
    "V-SCHEMA": {
        "defects": [],
        "plan": ["§5.4 check 1"],
        "desc": "schema version exact; top-level key set closed; shapes well-formed",
    },
    "V-A15": {
        "defects": ["D1"],
        "plan": ["A15", "B1.13", "§3.1.1", "§5.4 check 9"],
        "desc": "every artifact field exists and hash/line-count-matches; "
        "non-empty only where its floor > 0; empty file = empty-file digest",
    },
    "V-JOIN-RESIDUE": {
        "defects": ["D2"],
        "plan": ["§3.0.1", "item 0.12", "A1"],
        "desc": "max_join_residue is created from a MEASURED residue "
        "(origin=measured), never a hardcoded pre-measurement 0",
    },
    "V-PHASE-TREE": {
        "defects": ["D3"],
        "plan": ["§3.-0.5 rule 4", "P7.3"],
        "desc": "phase_reached monotone AND biconditional against tree probes: "
        "authority present <=> phase>=7; shadow severed <=> phase>=8; "
        "probe unavailable => RED",
    },
    "V-KEY-CENSUS": {
        "defects": ["D4"],
        "plan": ["§3.5 item 2", "§5.4 check 12", "§3.1 creation-vs-relaxation"],
        "desc": "first_seen_commit immutable against the prior census; a new "
        "pin requires key presence at that commit and ABSENCE at its parent "
        "(git); key set superset of previous",
    },
    "V-RATCHET-BASE": {
        "defects": ["D5"],
        "plan": ["§3.5 item 1", "§5.4 check 3"],
        "desc": "ratchet_base_commit == last green run's commit (from the "
        "runner's log) and a descendant of the previously recorded base",
    },
    "V-SOAK-LOG": {
        "defects": ["D6"],
        "plan": ["§3.8.1", "§3.5 item 8", "§5.4 check 13"],
        "desc": "runner-owned append-only hash-chained log; previous head "
        "still present (prefix rule); author-provided soak list REJECTED",
    },
    "V-LANE-FLOOR": {
        "defects": ["D7"],
        "plan": ["§3.1.2", "X4", "X4a"],
        "desc": "lane_minimums['A'].count >= 1 (configurable, never zero); "
        "bound minimums met; lane/kind immutable once accepted",
    },
    "V-SHADOW": {
        "defects": ["D8"],
        "plan": ["A14a", "A14c"],
        "desc": "phase-conditioned shadow obligation: state 'required' and "
        "shadow present while phase < 8; 'severed' only at phase >= 8 — "
        "deletion before the licensing phase is RED, never vacuous",
    },
    "V-ORACLE": {
        "defects": ["D9"],
        "plan": ["A18", "A11c", "§6 row 16"],
        "desc": "each oracle is a REQUIRED live artifact (exists, hash "
        "matches, >= 1 case) throughout its schema-pinned window until the "
        "phase that formally retires it",
    },
    "V-POLARITY": {
        "defects": ["D2"],
        "plan": ["§5.4 check 7", "§3.1"],
        "desc": "prefix polarity: max_ down-only, baseline_/min_ up-only, "
        "fixed_ frozen, floors up-only; a numeric key matching no prefix "
        "FAILS (the vacuity_floor class); creation exempt, changes never",
    },
}
