#!/usr/bin/env bash
# Control for the ONE channel a PASSING harness lane has to say something.
#
# WHY THIS EXISTS. `tests/run_trust_comprehensive_harness.sh` writes each lane's
# output to a log and, on PASS, prints the single word PASS. Nobody opens the log
# of a lane that passed. So a lane that knows a dated failure is coming --
# `fast.two-language-claim-ledger` knows the exact instant a claim lease lapses
# and refuses every push in every repo that runs it -- had no way to say so
# before it happened, and the first news of a fleet-wide stop was the stop.
#
# `surface_gate_warnings` is that channel: a lane announces by printing a line
# beginning `WARN:`, and the harness echoes those lines on its own stdout even
# though the lane passed.
#
# A WARNING THAT IS NOT PROVED TO REACH ANYONE IS THE THING IT WAS ADDED TO
# REPLACE, so this drives the REAL `run_gate` out of the real harness file --
# not a copy of its logic -- and checks all three directions:
#
#   1. a passing lane that prints `WARN:` has that line on the harness's stdout;
#   2. a passing lane that prints nothing produces no surfacing output at all
#      (a channel that always fires carries no information);
#   3. MUTATION: with `surface_gate_warnings` replaced by a no-op, the line is
#      still in the lane's log and is NO LONGER on the harness's stdout -- so the
#      surfacing, and not something else, is what delivers it.
#
# It also fails loudly if the harness is restructured such that the prefix can no
# longer be loaded, rather than silently testing nothing.
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
HARNESS="$REPO_ROOT/tests/run_trust_comprehensive_harness.sh"
FAILURES=0

fail() {
    echo "FAIL: $*" >&2
    FAILURES=$((FAILURES + 1))
}

if [ ! -f "$HARNESS" ]; then
    echo "FAIL: harness not found at $HARNESS" >&2
    exit 2
fi

# The driver loop begins at `selected_count=0`; everything above it is
# definitions and setup. Loading exactly that prefix gives us the real run_gate
# without executing a single real lane. If the marker moves or doubles, this
# test refuses instead of quietly measuring the wrong thing.
MARKER='^selected_count=0$'
marker_count="$(grep -c "$MARKER" "$HARNESS")"
if [ "$marker_count" != "1" ]; then
    echo "FAIL: expected exactly one '$MARKER' line in the harness, found $marker_count." >&2
    echo "      The harness driver was restructured; re-anchor this control." >&2
    exit 2
fi
if ! grep -q '^surface_gate_warnings() {$' "$HARNESS"; then
    echo "FAIL: the harness defines no surface_gate_warnings function." >&2
    exit 2
fi
if ! grep -q 'surface_gate_warnings "\$gate_id" "\$log_path"' "$HARNESS"; then
    echo "FAIL: run_gate does not call surface_gate_warnings on the PASS path." >&2
    exit 2
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

PREFIX="$WORK/harness_prefix.sh"
awk -v marker="selected_count=0" '$0 == marker { exit } { print }' "$HARNESS" >"$PREFIX"

# Run one fixture lane through the real run_gate and echo the harness's own
# stdout. Everything runs in a subshell so the sourced prefix's `set -uo
# pipefail`, globals and traps cannot leak into this script.
drive_gate() {
    local out_dir="$1" gate_id="$2" command="$3" neuter="$4"
    (
        export TRUST_COMPREHENSIVE_OUT_DIR="$out_dir"
        export TRUST_COMPREHENSIVE_RUN_ID="fixture"
        # shellcheck disable=SC1090
        . "$PREFIX" manifest
        # $0 is this test, so the prefix derived TRUST_ROOT from scripts/tests/.
        # run_gate cd's there; point it at the repo so the fixture runs where a
        # real lane would.
        TRUST_ROOT="$REPO_ROOT"
        if [ "$neuter" = "neuter" ]; then
            surface_gate_warnings() { :; }
        fi
        run_gate "$gate_id" "fixture" "true" "never" "$command"
    ) 2>&1
}

WARN_LINE='WARN: lease-expiry: fixture claim expires in 3h00m'

# The lane must emit the warning from a SCRIPT, never from the command string:
# run_gate echoes `command:  <command>` before running it, so a command
# containing the literal text would put the line on stdout with the surfacing
# doing nothing -- the positive check would pass for the wrong reason and the
# mutation could never fail.
WARN_LANE="$WORK/warn_lane.sh"
{
    echo '#!/usr/bin/env bash'
    echo "echo '$WARN_LINE'"
    echo 'exit 0'
} >"$WARN_LANE"
SILENT_LANE="$WORK/silent_lane.sh"
{
    echo '#!/usr/bin/env bash'
    echo "echo 'ordinary output'"
    echo 'exit 0'
} >"$SILENT_LANE"
case "bash $WARN_LANE" in
    *WARN*)
        echo "FAIL: the fixture command string itself contains WARN; the control is vacuous" >&2
        exit 2
        ;;
esac
if ! bash "$WARN_LANE" | grep -qF "$WARN_LINE"; then
    echo "FAIL: the fixture lane does not print the warning it exists to print" >&2
    exit 2
fi

# 1. POSITIVE -- a passing lane's WARN line reaches the harness's stdout.
out_dir="$WORK/positive"
stdout="$(drive_gate "$out_dir" "fixture.warns" "bash $WARN_LANE" "keep")"
case "$stdout" in
    *"status:   PASS"*) ;;
    *) fail "fixture.warns did not PASS; harness said: $stdout" ;;
esac
case "$stdout" in
    *"$WARN_LINE"*) ;;
    *) fail "a passing lane's WARN line did not reach the harness stdout: $stdout" ;;
esac
case "$stdout" in
    *"warnings: fixture.warns passed and reported the above"*) ;;
    *) fail "the surfacing trailer naming the gate is missing: $stdout" ;;
esac

# 2. NEGATIVE -- a silent passing lane produces no surfacing output. A channel
#    that fires for every lane says nothing about any of them.
out_dir="$WORK/silent"
stdout="$(drive_gate "$out_dir" "fixture.silent" "bash $SILENT_LANE" "keep")"
case "$stdout" in
    *"status:   PASS"*) ;;
    *) fail "fixture.silent did not PASS; harness said: $stdout" ;;
esac
case "$stdout" in
    *"WARN:"*) fail "a lane that emitted no WARN line still produced one: $stdout" ;;
esac
case "$stdout" in
    *"warnings:"*) fail "a lane that emitted no WARN line produced a warnings trailer: $stdout" ;;
esac

# 3. MUTATION -- neuter the surfacing and the SAME lane's warning disappears
#    from stdout while remaining in the lane's log. This is what proves the
#    delivery is the surfacing rather than an accident of some other echo.
out_dir="$WORK/mutated"
stdout="$(drive_gate "$out_dir" "fixture.warns" "bash $WARN_LANE" "neuter")"
case "$stdout" in
    *"status:   PASS"*) ;;
    *) fail "mutated fixture.warns did not PASS; harness said: $stdout" ;;
esac
case "$stdout" in
    *"$WARN_LINE"*) fail "neutering surface_gate_warnings did not remove the warning from stdout" ;;
esac
mutated_log="$out_dir/logs/fixture.warns.log"
if [ ! -f "$mutated_log" ]; then
    fail "expected the mutated run's lane log at $mutated_log"
elif ! grep -qF "$WARN_LINE" "$mutated_log"; then
    fail "the mutated run's lane log lost the WARN line; the mutation moved the wrong thing"
fi

if [ "$FAILURES" -ne 0 ]; then
    echo "gate warning surface: $FAILURES check(s) failed" >&2
    exit 1
fi
echo "gate warning surface: PASS (positive, silent-negative, and neutering mutation)"
