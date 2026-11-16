#!/usr/bin/env bash
# Trust: unit test for `trust_falsification_gate.sh`'s verdict classifier.
#
# WHY THIS EXISTS. Until 2026-07-30 the gate had ONE label for two different
# answers. `contains_trust_rejection_verdict` matched
# `Trust (strict|full|memory-safe) verification failed` — the INCOMPLETENESS
# header, printed whenever an obligation is merely undischarged — so a run in
# which the verifier caught nothing classified as `refuted`.
#
# On the `mutant/` lane, `refuted` is the PASS condition. An uncaught mutant
# therefore scored PASS and was counted in the closing line "N mutants explicitly
# refuted". The gate could report a green mutation score while catching nothing.
#
# The whole gate needs a stage2 `trustc` and minutes of wall clock; this
# classifier is pure text and needs neither, so the distinction that carries the
# gate's central claim gets a test that actually runs.
set -uo pipefail

script=${1:-"$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/scripts/trust_falsification_gate.sh"}
[[ -r $script ]] || {
  printf 'classify_verdict_test: cannot read %s\n' "$script" >&2
  exit 2
}

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

# Source ONLY the predicates and the classifier: the script runs its main() on
# source, so pulling in the whole file would launch a gate run.
sed -n \
  -e '/^contains_tool_error()/,/^}/p' \
  -e '/^contains_trust_counterexample_verdict()/,/^}/p' \
  -e '/^contains_trust_incompleteness_verdict()/,/^}/p' \
  -e '/^contains_incomplete_static_accept()/,/^}/p' \
  -e '/^classify_verdict()/,/^}/p' \
  "$script" >"$work/fns.sh"

for required in contains_tool_error contains_trust_counterexample_verdict \
  contains_trust_incompleteness_verdict contains_incomplete_static_accept \
  classify_verdict; do
  grep -q "^$required()" "$work/fns.sh" || {
    printf 'classify_verdict_test: %s not found — did the gate rename it?\n' "$required" >&2
    exit 2
  }
done
# shellcheck source=/dev/null
. "$work/fns.sh"

failed=0
check() {
  local name=$1 rc=$2 text=$3 expect=$4 got
  printf '%s' "$text" >"$work/stderr.txt"
  got=$(classify_verdict "$rc" "$work/stderr.txt")
  if [[ $got == "$expect" ]]; then
    printf '  ok    %-46s -> %s\n' "$name" "$got"
  else
    printf '  FAIL  %-46s -> %s (expected %s)\n' "$name" "$got" "$expect"
    failed=1
  fi
}

check 'clean compile' 0 '' proved

# EXIT 0 IS NOT PROOF (2026-08-04, task #37). Policy B's default exits 0 while
# RETAINING runtime checks for undischarged obligations; the two shift-reduction
# mutants rode that to a `proved` row and a false "SURVIVING MUTANT" headline.
# rc=0 is `proved` only when every report summary is all-zero except proved.
check 'exit 0, all obligations static' 0 \
  'note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)' proved
check 'exit 0, runtime-checked row' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 2 obligation(s)' runtime-checked
check 'exit 0, unknown row' 0 \
  'note: Trust verification: 1 proved, 0 failed, 1 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)' runtime-checked
check 'exit 0, timed-out row' 0 \
  'note: Trust verification: 3 proved, 0 failed, 0 unknown, 1 timed out, 0 runtime-checked out of 4 obligation(s)' runtime-checked
# Zero-obligation acceptance fixtures emit no headline at all — still proved.
check 'exit 0, no report (acceptance fixture)' 0 \
  'warning: unused variable' proved
# Two functions, second one degrades — any non-all-zero summary demotes.
check 'exit 0, second fn runtime-checked' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
note: Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked out of 1 obligation(s)' runtime-checked

# A REFUTATION: the verifier exhibited a violated obligation. Only these count as
# "caught" on the mutant lane.
check 'counterexample: L0 violation' 1 \
  'error: Trust verification found 2 guaranteed Level 0 safety violations' refuted
check 'counterexample: N failed' 1 \
  'Level 0 summary: 1 failed, 0 unknown' refuted
# A real refutation prints the header too — the counterexample test must win.
check 'refutation printing both' 1 \
  'Trust full verification failed
Level 0 summary: 2 failed' refuted

# INCOMPLETENESS: nothing was caught. THIS is the case that used to read
# `refuted`; if either of these two regresses, the mutant lane starts passing
# mutants it never detected.
check 'incompleteness header alone' 1 \
  'error: Trust strict verification failed: 3 obligation(s) were not fully verified' incomplete
check 'strict-scope refusal' 1 \
  'strict Trust verification requires every Level 0 obligation to be discharged' incomplete

# OD-1's CERTIFY refusals (FALSIF-OD1-VOCAB, 2026-10-06). Since c77d7678cf the
# certify policy refuses an instance-hypothesis row with its own header,
# `Trust certify verification failed`, and three more certify refusals share it
# (termination unmeasured, a runtime-checked std member, `main`'s return type).
# Each is an INCOMPLETENESS refusal: nothing was caught. Before this row the
# header matched neither predicate and the gate scored it `tool-error`; the
# tempting fix — adding it to the counterexample predicate — would score an
# assumption refusal as a refutation, the laundering the 2026-07-30 split exists
# to prevent. These rows pin both halves.
check 'certify: instance hypothesis refusal' 1 \
  'error: Trust certify verification failed for `absent_callee_call_only_generic::r3_t_default`: 1 instance hypothesis row(s) — panic-freedom of open generic dispatch is assumed, not proved
  = note: under -Ztrust-policy=certify an assumption:instance-hypothesis row is fatal; the default lane records it and passes CONDITIONALLY' incomplete
check 'certify: refusal plus a real refutation' 1 \
  'error: Trust certify verification failed for `c::f`: 1 instance hypothesis row(s) — panic-freedom of open generic dispatch is assumed, not proved
note: Level 0 summary: 1 failed, 0 unknown' refuted
check 'certify: termination unmeasured' 1 \
  'error: Trust certify verification failed for `t::spin`: termination is not measured' incomplete
check 'certify: runtime-checked std member' 1 \
  'error: Trust certify verification failed for `s::f`: a bundled std/core/alloc member is runtime-checked' incomplete
check 'certify: main return type' 1 \
  'error: Trust certify verification failed for `m::main`: `main`'"'"'s return type is not verified' incomplete
check 'certify header after a rustc error' 1 \
  'error[E0308]: mismatched types
error: Trust certify verification failed for `f`: 1 instance hypothesis row(s)' tool-error

# THE ARMOR READS WHOLE LINES (FALSIF-ARMOR-ASSUMED, 2026-10-06). The summary
# line grew columns after `runtime-checked` (`, N assumed (requires)`, `, N assumed
# (instance discharge)`, `, N skipped`; 688d2058fd, bef42cea64) and a second
# counter label (`conditionally discharged (NOT proved)`). The old armor matched a
# fixed TAIL substring and selected lines by `N proved,`, so it (a) read the
# certify-accepted `assumed (requires)` column as non-static — a false red on
# proved/contract_caller_precondition_met — and (b) never selected a conditional
# line at all, reading it as a clean exit (fail-open). A line is static only when
# it matches the whole static grammar; anything else, including any column added
# in future, is not.
# (a) the exact two w17 lines of contract_caller_precondition_met (certify, rc=0).
check 'exit 0, assumed (requires) is static' 0 \
  'note: Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 1 obligation(s)
note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires) out of 2 obligation(s)' proved
# (b) the coroutine label: rc=0 under advisory, NOT proved by its own words.
check 'exit 0, conditionally discharged' 0 \
  'note: Trust verification: 1 conditionally discharged (NOT proved), 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 4 skipped out of 5 obligation(s)' runtime-checked
check 'exit 0, conditional line beside a clean one' 0 \
  'note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)
note: Trust verification: 1 conditionally discharged (NOT proved), 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)' runtime-checked
# (c) skipped rows are not static.
check 'exit 0, skipped row' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 skipped out of 2 obligation(s)' runtime-checked
check 'exit 0, assumed (requires) then skipped' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (requires), 1 skipped out of 3 obligation(s)' runtime-checked
# (d) an instance-discharge row reports another body's verdict; it is not static here.
check 'exit 0, assumed (instance discharge)' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 assumed (instance discharge) out of 2 obligation(s)' runtime-checked
# (e) a column nobody has taught the armor yet fails closed.
check 'exit 0, unknown future column' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 1 frobnicated out of 2 obligation(s)' runtime-checked
# (f) a nonzero column next to `assumed (requires)` is still caught.
check 'exit 0, assumed (requires) with runtime-checked' 0 \
  'note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 assumed (requires) out of 3 obligation(s)' runtime-checked
# (g) the counts must account for the whole denominator: a row the line does
# not name is not static.
check 'exit 0, counts short of the total' 0 \
  'note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)' runtime-checked
# (h) a summary that is not a top-level note (another severity, or text around
# it) is not the line the armor knows.
check 'exit 0, summary at warning severity' 0 \
  'warning: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)' runtime-checked
check 'exit 0, trailing text after the summary' 0 \
  'note: Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s) (cached)' runtime-checked
# (i) policy drift with NO summary line: an OD-1 instance hypothesis under the
# default policy exits 0 with only an advisory warning (measured on w17 for
# mutant/absent_callee_call_only_generic.rs without `-Ztrust-policy=certify`).
# The zero-headline rule must not read that as a zero-obligation acceptance.
check 'exit 0, OD-1 advisory warning, no summary' 0 \
  'warning: Trust verification advisory for `absent_callee_call_only_generic::r3_t_default`: 1 instance hypothesis row(s) — panic-freedom of open generic dispatch is ASSUMED per instance, not proved
  = note: recorded as `assumption:instance-hypothesis` (skipped, NOT proved): the crate'"'"'s result is CONDITIONAL
warning: 1 warning emitted' runtime-checked
check 'exit 0, advisory not-fully-verified warning' 0 \
  'warning: Trust verification advisory for `m::f`: 1 obligation(s) were not fully verified
note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)' runtime-checked
check 'exit 0, survey-mode incomplete warning' 0 \
  'warning: Trust Level 0 safety verification incomplete for `m::f`: 3 obligation(s) were not proved' runtime-checked
# An ordinary rustc warning beside a clean summary stays proved.
check 'exit 0, unrelated rustc warning' 0 \
  'warning: value passed to `x` is never read
note: Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
warning: 1 warning emitted' proved

# Tool failures are never a verdict.
check 'ICE is not a verdict' 1 'internal compiler error: oh no' tool-error
check 'unrelated exit 1' 1 'error: could not find crate' tool-error

if ((failed)); then
  printf 'classify_verdict_test: FAILED\n'
  exit 1
fi
printf 'classify_verdict_test: all cases pass\n'
