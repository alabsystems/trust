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
  -e '/^classify_verdict()/,/^}/p' \
  "$script" >"$work/fns.sh"

for required in contains_tool_error contains_trust_counterexample_verdict \
  contains_trust_incompleteness_verdict classify_verdict; do
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

# Tool failures are never a verdict.
check 'ICE is not a verdict' 1 'internal compiler error: oh no' tool-error
check 'unrelated exit 1' 1 'error: could not find crate' tool-error

if ((failed)); then
  printf 'classify_verdict_test: FAILED\n'
  exit 1
fi
printf 'classify_verdict_test: all cases pass\n'
