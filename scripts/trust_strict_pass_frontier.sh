#!/usr/bin/env bash
# trust_strict_pass_frontier.sh — pin the exact boundary of what can pass the
# AUTHENTICATED strict lane (`targo trust check`), with a live mutation control.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHY THIS EXISTS
# ---------------
# Three separate measurements had concluded "no crate passes strict". Measured
# 2026-08-27, one CAN: `tests/self-proof/strict-pass-frontier/pass.rs` reaches
# `Gate: PASS [strict lane, exit 0]` with two non-vacuous PROVED rows. What the
# earlier sweeps had actually found is narrower and more useful:
#
#   the default `unix_hardened` profile emits a SECOND `hardened_panic_boundary`
#   row beside every MIR arithmetic assert, adjudicated separately, and the
#   `Overflow(*)` family of those twins is NOT discharged by the guards that
#   prove the primary row.
#
# So `divzero` passes (its twin discharges) and `Overflow(Add)` does not. This
# script pins both sides so the boundary cannot move unobserved.
#
# THE TRAP THIS GUARDS
# --------------------
# `blocked.rs` fails with exit 101 while publishing
#   Summary: 1 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 unknown (1 total)
#   Coverage: 1/1 eligible function bodies verified (complete)
# The compiler reports TWO obligations not fully verified; the transport
# publishes one. Reading the Summary line alone says it passed. Every assertion
# below is therefore on the EXIT CODE and the `Gate:` line, never the Summary.
#
# Usage:  scripts/trust_strict_pass_frontier.sh
set -uo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
FIX="$REPO_ROOT/tests/self-proof/strict-pass-frontier"
TARGO="${TARGO:-$REPO_ROOT/build/aarch64-apple-darwin/stage1/bin/targo}"

if [ ! -x "$TARGO" ]; then
  echo "REFUSE: no targo at $TARGO (set TARGO=...)"; exit 2
fi
# The authenticated lane refuses a group- or world-writable path component, so
# the fixture must be driven in-tree, never from /tmp.
case "$FIX" in /tmp/*|/private/tmp/*) echo "REFUSE: fixture under a world-writable prefix"; exit 2;; esac

fails=0
# `run` keeps the last log at $LAST_LOG so a caller can make a further, more
# specific assertion about the SAME run (see the postcondition check below).
LAST_LOG=""
run() { # run <variant> <expect-pass|expect-fail>
  local v="$1" expect="$2" log rc gate
  log="$(mktemp)"
  cp "$FIX/$v.rs" "$FIX/src/lib.rs"
  ( cd "$FIX" && "$TARGO" trust check -p strict-pass-frontier ) > "$log" 2>&1
  rc=$?
  gate="$(grep -oE 'Gate: [A-Z]+ \[strict lane, exit [0-9]+\]' "$log" | tail -1)"
  # A run that produced no Gate line did not verify anything; never let that
  # read as a pass.
  if [ -z "$gate" ]; then
    echo "  FAIL $v: no Gate: line — the lane did not run (vacuous)"; fails=$((fails+1))
    cat "$log" | tail -5; LAST_LOG="$log"; return
  fi
  if [ "$expect" = expect-pass ] && [ "$rc" -eq 0 ]; then echo "  ok   $v  $gate"
  elif [ "$expect" = expect-fail ] && [ "$rc" -ne 0 ]; then echo "  ok   $v  $gate"
  else echo "  FAIL $v: rc=$rc expected=$expect  $gate"; fails=$((fails+1)); fi
  LAST_LOG="$log"
}

# Count `[postcondition] ... PROVED` rows in the last run.
proved_postconditions() {
  grep -cE '^\s*\[postcondition\] postcondition PROVED' "$LAST_LOG" 2>/dev/null || true
}
expect_proved_postconditions() { # expect_proved_postconditions <variant> <n>
  local v="$1" want="$2" got
  got="$(proved_postconditions)"
  if [ "$got" = "$want" ]; then echo "       $v: [postcondition] PROVED rows = $got (expected $want)"
  else echo "  FAIL $v: [postcondition] PROVED rows = $got, expected $want"; fails=$((fails+1)); fi
}

echo "strict-pass frontier:"
# The pass, and the mutation control that proves the gate is live. A strict pass
# that has never been seen to fail is not evidence.
run pass    expect-pass
rm -f "$LAST_LOG"
run refute  expect-fail
rm -f "$LAST_LOG"
# WAS the frontier marker. The producer fix (#222) has landed, but THIS
# ASSERTION IS STILL `expect-fail` ON PURPOSE — see the two corrections below.
#
# CORRECTION 1 — the gate was NOT measured. An earlier revision flipped this to
# `expect-pass`. The build that would have confirmed it never completed, so the
# flip asserted a PREDICTION. A gate that asserts an unmeasured outcome is how a
# false green enters the tree; it stays `expect-fail` until someone RUNS it and
# sees `blocked` pass. Flip it in the same commit that shows the passing output.
#
# CORRECTION 2 — the scope claim below was REFUTED by adversarial re-measurement.
# An earlier revision called this "the shape the whole `Overflow(Add|Sub|Mul)`
# family failed on, and therefore the shape that blocked every crate doing
# guarded integer arithmetic". Measured across 10 op/type/guard cells, pre-fix
# vs post-fix: **3 GAINED (all `Add`), 7 unchanged, 0 LOST**. `Sub` and `Mul`
# did not move, and `widen_add.rs` — which also adds two integers — ALREADY
# passed before the fix, via the separate summand-bounded recognizer. The honest
# scope is: guarded `Add` on direct integer parameters. Not a family, not
# "every crate that adds two integers".
#
# WHAT WAS WRONG, and it was never a refutation. Every `blocked` run reported
# `0 failed`; the interval solver returned Proved for BOTH rows and `trustc`
# printed the downgrade `targo` hides — `[hardened_panic_boundary] UNKNOWN
# (interval): Proved label lacked exact kernel/native proof authority`. The two
# rows were the same proposition in two SYNTAXES: the per-statement lane emits
# `Or([Lt(sum, lo), Gt(sum, hi)])` and the hardened twin hand-rolled its De
# Morgan dual `Not(And([Le(lo, sum), Le(sum, hi)]))`.
# `certify_disjunctive_contradiction` builds its kernel proof by case-splitting a
# `Formula::Or`, so the dual never reached the recognizer and the kernel
# certified nothing it was never handed.
#
# THE FIX IS IN THE PRODUCER, not the certifier: `guards::
# checked_binop_out_of_range_violation` now emits the canonical disjunction, so
# the twin carries its primary's spelling — the same term
# `trust_semantics::noOverflow_violation_formula` names. The recognizer was not
# touched or widened.
run blocked expect-fail   # NOT expect-pass: see CORRECTION 1 above — unmeasured
rm -f "$LAST_LOG"
# THE MUTATION CONTROL FOR THAT PASS, and the reason the fix is not a false
# PROVE. Same body, guards widened to 2_000_000_000 so `a + b` GENUINELY
# overflows `i32` (z3 4.x: SAT, witness `a = 147483648, b = 2000000000`, a model
# satisfying every guard). A re-spelling that made this certify would ship
# exactly the false verify the change exists to avoid, and `blocked` passing
# cannot detect that. Never adjust this expectation; if it ever passes, revert.
run blocked_overflows expect-fail
rm -f "$LAST_LOG"
# The BOUND on that marker. `widen_add.rs` adds two integers, keeps the default
# `unix_hardened` profile, and PASSES at exit 0 with the hardened Overflow(Add)
# twin among the proved rows — so "the twin blocks any crate that adds two
# integers" is false, and the boundary is the violation's SHAPE. Without this
# line `blocked` alone reads as a categorical claim about arithmetic.
run widen_add expect-pass
rm -f "$LAST_LOG"

# ---------------------------------------------------------------------------
# THE CONTRACT COST. Measured 2026-08-27; this is the reason "write more
# contracts" cannot by itself carry a crate to a strict pass.
#
# `ens.rs` and `req.rs` have a body BYTE-IDENTICAL to `pass.rs` — which passes
# at exit 0 with `2 proved, 0 unknown (2 total)`. The only change is one added
# contract clause. Both then FAIL the strict lane:
#
#   pass       exit 0  Gate: PASS          2 proved, 0 unknown          (2 total)
#   + ensures  exit 1  Gate: FAIL          3 proved, 2 inconclusive     (5 total)
#   + requires exit 1  Gate: INCONCLUSIVE  2 proved, 1 assumed          (3 total)
#
# The added clause IS proved — `ens` reports one `[postcondition] PROVED
# (trust-full-verifier, CONSTRUCTIVE, kernel-rechecked)`. It is the COMPANION
# rows that are undischargeable:
#
#   ensures  -> 3 rows: 1 PROVED, plus `trust-exact-source-clause-discharge`
#               ("source-clause catalog marker awaits sealed private body
#               authorities") and a trust-mc native-lane row, both UNKNOWN.
#   requires -> the def-site marker `unsupported MIR
#               FullVerification::Precondition`, routed to the UnsupportedMir
#               fallthrough on purpose (trust_verify.rs, `native_contract_vc_kind`,
#               where the comment calls it "a non-fatal coverage gap"). It is
#               non-fatal to rustc's per-function gate but it is counted by the
#               targo strict gate, so it is fatal to a PASS.
#
# Rows RISE in both cases (2 -> 5, 2 -> 3): nothing vanished, the additions are
# real and simply cannot be discharged today. When either companion class learns
# to discharge, the matching line below flips to expect-pass — deliberately,
# with the measurement that justified it.
run ens     expect-fail
expect_proved_postconditions ens 1
rm -f "$LAST_LOG"
run req     expect-fail
rm -f "$LAST_LOG"
# Mutation control for `ens`: the SAME clause negated so it is FALSE. Without
# this, the "1 PROVED postcondition" above is not evidence that the postcondition
# machinery decides anything.
run ens_false expect-fail
expect_proved_postconditions ens_false 0
rm -f "$LAST_LOG"

echo "// placeholder; the runner copies a variant over this file" > "$FIX/src/lib.rs"
[ "$fails" -eq 0 ] && { echo "OK"; exit 0; } || { echo "$fails assertion(s) failed"; exit 1; }
