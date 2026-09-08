//@ probe-shape: BoolBinary
//@ probe-expect: other
//@ probe-flags: -O
//@ probe-note: FORMER DEFECT PIN, now pinned GREEN (rebuild-gated). The clause
//@ probe-note: spells the conjunction INLINE -- `result == (A && B)` -- and the
//@ probe-note: native trust-mc lane used to FALSELY REFUTE it: `0 proved,
//@ probe-note: 3 failed, counterexample: verified_counterexample = true`
//@ probe-note: against a tautologically true postcondition (the body IS the
//@ probe-note: clause's RHS). Measured 2026-08-25 at i64 and i128.
//@ probe-note:
//@ probe-note: ROOT CAUSE (fixed 2026-08-25, trust-vcgen contract_vcs): the
//@ probe-note: `&&` lowering diamond writes `_0` in TWO return predecessors, so
//@ probe-note: the per-predecessor postcondition VC negates the clause at the
//@ probe-note: Return block's MERGED reaching-def token (`_0#s1_0_s2_0`) while
//@ probe-note: the return-value pin carries THIS predecessor's single token
//@ probe-note: (`_0#s1_0`/`_0#s2_0`). `unify_return_slot_versions` exists to
//@ probe-note: bridge exactly that gap, but its pin finder
//@ probe-note: (`return_slot_pin_version`) walked EVERYWHERE and counted the
//@ probe-note: Eq-shaped clause's own negated equality as a second "pin", saw
//@ probe-note: phantom ambiguity, and bailed -- leaving the merged join name
//@ probe-note: FREE, so `Not(post)` was satisfiable by havoc and the
//@ probe-note: "counterexample" was a model of a formula about nothing. A
//@ probe-note: single-comparison clause (`result == (x >= 0)`) never branched,
//@ probe-note: so no join token existed and it proved fine; that is why the
//@ probe-note: defect looked specific to the BoolBinary conjunction shape. The
//@ probe-note: fix makes the pin finder SPINE-ONLY, mirroring its sibling
//@ probe-note: `formula_has_return_slot_pin` ("an equality inside the negated
//@ probe-note: clause is the obligation, not a pin"); regression tests:
//@ probe-note: trust-vcgen generate/return_slot_join_version_tests.rs.
//@ probe-note:
//@ probe-note: EXPECTED VERDICT is `other`, not `discharged`: with no island
//@ probe-note: call in the clause the uncited defeq route declines the whole
//@ probe-note: function (E9 prints NO-ISLAND-CALL, never DISCHARGED), and the
//@ probe-note: function closes instead by the native trust-mc typed CHC/PDR
//@ probe-note: lane proving every row (`3 proved, 0 failed`, exit 0) -- the
//@ probe-note: same clean-compile shape the single-comparison control measures
//@ probe-note: today, which the runner names `other`. The kernel island-call
//@ probe-note: route for these bodies stays pinned by f45/f46/f48.
//@ probe-note:
//@ probe-note: REBUILD GATE: this expectation describes trustc built from
//@ probe-note: source AFTER the trust-vcgen fix. Until stage2 is rebuilt the
//@ probe-note: shipped binary still measures `unproved` (the false refutation)
//@ probe-note: and this row is deliberately RED, exactly like a fragment
//@ probe-note: widening awaiting its expectation bump -- the runner failing
//@ probe-note: here is the signal to rebuild, not to revert this header.
//@ probe-note:
//@ probe-note: TRIAGE if still `unproved` post-rebuild: the pin here is the
//@ probe-note: FALSE REFUTATION -- the two `runner refuted obligation ...`
//@ probe-note: rows and `verified_counterexample = true` must be GONE (both
//@ probe-note: postcondition rows prove from a now-UNSAT constraint). The
//@ probe-note: default-admission row's transport authority is a separate lane
//@ probe-note: (the single-comparison control body proves 2/2 through it
//@ probe-note: today); if only that row still refuses, that is a new, honest
//@ probe-note: coverage gap -- repin it as such, never as this defect.
pub fn in_range(x: i64) -> bool
    ensures result == (x >= -128 && x <= 127)
{ x >= -128 && x <= 127 }
