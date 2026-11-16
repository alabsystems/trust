#!/usr/bin/env bash
# Control for the ONE channel a PASSING harness lane has to say something.
#
# WHY THIS EXISTS. `tests/run_trust_comprehensive_harness.sh` writes each lane's
# output to a log and, on PASS, prints the single word PASS. Nobody opens the log
# of a lane that passed. So a lane that knows a dated failure is coming --
# the since-retired `fast.two-language-claim-ledger` knew the exact instant a
# claim lease lapsed -- had no way to say so before it happened. (That row was
# removed on 2026-09-30 with the ledger ref it read.)
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
# The same log-token channel carries `SKIPPED:`, and a SKIP that is graded PASS
# lets a lane that ran nothing advance its own `last_green` (measured
# 2026-09-27: all three scoped lanes PASS in 0s at a clean origin/main, each
# with a LAST-GREEN offer). So it is checked in the same way:
#
#   4. a lane that exits 0 after printing `SKIPPED:` is graded SKIP, prints NO
#      LAST-GREEN line, and is recorded skipped=true in results.tsv;
#   5. a lane that exits 0 WITHOUT the token is still PASS with the LAST-GREEN
#      line and skipped=false (the grading must not suppress a real green);
#   6. a lane that prints the token and exits non-zero is FAIL, not SKIP;
#   7. MUTATION: with `gate_skipped` replaced by one that never matches, the
#      same skipping lane is graded PASS with a LAST-GREEN line again while its
#      log still holds the token -- so `gate_skipped` is what grades it.
#
# `--record-last-green` turns those LAST-GREEN offers into manifest edits, so:
#
#   8. against a fixture manifest, exactly the offered rows move to the run's
#      UTC start date; SKIP, FAIL, a later date and a row edited mid-run keep
#      their bytes, as does the rest of the file and its mode;
#   9. MUTATION: with `gate_skipped` neutered the SKIP row IS recorded;
#  10. MUTATION: with the offer rule neutered, the writer's own check still
#      refuses to move a date backward;
#  11. the flag is opt-in and does not change the selected profile.
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
if ! grep -q '^gate_skipped() {$' "$HARNESS"; then
    echo "FAIL: the harness defines no gate_skipped function." >&2
    exit 2
fi
if ! grep -q 'gate_skipped "\$log_path"' "$HARNESS"; then
    echo "FAIL: run_gate does not call gate_skipped to grade a zero exit." >&2
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
        if [ "$neuter" = "neuter-skip" ]; then
            gate_skipped() { return 1; }
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
# The skip token comes from a script too, and in the shape the real scoped lanes
# print it (scripts/check_compiler_targets_build.sh on an empty diff).
SKIP_LINE='SKIPPED: no changes against origin/main — nothing to check'
SKIP_LANE="$WORK/skip_lane.sh"
{
    echo '#!/usr/bin/env bash'
    echo "echo '$SKIP_LINE'"
    echo 'exit 0'
} >"$SKIP_LANE"
SKIP_RED_LANE="$WORK/skip_red_lane.sh"
{
    echo '#!/usr/bin/env bash'
    echo "echo '$SKIP_LINE'"
    echo 'exit 3'
} >"$SKIP_RED_LANE"
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

# The `skipped` column of the one row run_gate wrote, looked up by header name.
skipped_column() {
    awk -F'\t' 'NR == 1 { for (i = 1; i <= NF; i++) if ($i == "skipped") c = i }
                NR == 2 { print (c ? $c : "<no skipped column>") }' "$1/results.tsv"
}

# 4. SKIP -- a lane that ran nothing is SKIP, never PASS, and offers no
#    LAST-GREEN ratchet. drive_gate records last_green `never`, so any PASS
#    would print the ratchet line; its absence is the grading, not the date.
out_dir="$WORK/skip"
stdout="$(drive_gate "$out_dir" "fixture.skips" "bash $SKIP_LANE" "keep")"
case "$stdout" in
    *"status:   SKIP"*) ;;
    *) fail "a lane that printed SKIPPED: was not graded SKIP: $stdout" ;;
esac
case "$stdout" in
    *"status:   PASS"*) fail "a lane that printed SKIPPED: was graded PASS: $stdout" ;;
esac
case "$stdout" in
    *"LAST-GREEN"*) fail "a lane that ran nothing offered to advance last_green: $stdout" ;;
esac
[ "$(skipped_column "$out_dir")" = "true" ] \
    || fail "results.tsv does not record the skipped lane as skipped=true: $(cat "$out_dir/results.tsv")"

# 5. SKIP NEGATIVE -- a lane that ran and printed no token is still PASS with
#    the ratchet line. Grading every zero exit SKIP would pass step 4 and hide
#    every real green.
out_dir="$WORK/skip-negative"
stdout="$(drive_gate "$out_dir" "fixture.silent" "bash $SILENT_LANE" "keep")"
case "$stdout" in
    *"status:   PASS"*) ;;
    *) fail "a lane that ran and printed no SKIPPED: was not PASS: $stdout" ;;
esac
case "$stdout" in
    *"LAST-GREEN: update the manifest row for fixture.silent to "*) ;;
    *) fail "a real PASS no longer offers the LAST-GREEN ratchet: $stdout" ;;
esac
case "$stdout" in
    *"status:   SKIP"*) fail "a lane that printed no SKIPPED: was graded SKIP: $stdout" ;;
esac
[ "$(skipped_column "$out_dir")" = "false" ] \
    || fail "results.tsv does not record the real PASS as skipped=false: $(cat "$out_dir/results.tsv")"

# 6. A non-zero exit is FAIL whatever the log says: the token must not launder
#    a red into a SKIP.
out_dir="$WORK/skip-red"
stdout="$(drive_gate "$out_dir" "fixture.skip-red" "bash $SKIP_RED_LANE" "keep")"
case "$stdout" in
    *"status:   FAIL exit=3"*) ;;
    *) fail "a red lane that printed SKIPPED: was not graded FAIL: $stdout" ;;
esac
[ "$(skipped_column "$out_dir")" = "false" ] \
    || fail "results.tsv records a red lane as skipped: $(cat "$out_dir/results.tsv")"

# 7. MUTATION -- with gate_skipped never matching, the SAME skipping lane is
#    PASS with a LAST-GREEN offer again while its log still holds the token:
#    gate_skipped, and nothing else, is what grades it.
out_dir="$WORK/skip-mutated"
stdout="$(drive_gate "$out_dir" "fixture.skips" "bash $SKIP_LANE" "neuter-skip")"
case "$stdout" in
    *"status:   PASS"*"LAST-GREEN: update the manifest row for fixture.skips to "*) ;;
    *) fail "neutering gate_skipped did not restore the PASS + LAST-GREEN grading: $stdout" ;;
esac
mutated_log="$out_dir/logs/fixture.skips.log"
if [ ! -f "$mutated_log" ]; then
    fail "expected the mutated skip run's lane log at $mutated_log"
elif ! grep -qF "$SKIP_LINE" "$mutated_log"; then
    fail "the mutated skip run's lane log lost the SKIPPED line; the mutation moved the wrong thing"
fi

# 8. RECORD -- `--record-last-green` writes exactly the LAST-GREEN offers into
#    the manifest rows. A fixture manifest drives the real run_gate and the real
#    record_last_green: a PASS moves an older date or `never` to the run's UTC
#    start date; a SKIP, a FAIL, a later date, and a row whose command was
#    edited mid-run keep their bytes, as does every other line of the file.
fixture_manifest() { # <old> <never> <skips> <edited-suffix>
    printf '#!/bin/bash\n# fixture\nemit_gate_manifest() {\n    cat <<'\''EOF'\''\n'
    printf 'fixture.pass-old|fast|fixture|true|%s|bash %s\n' "$1" "$SILENT_LANE"
    printf 'fixture.pass-never|fast|fixture|true|%s|bash %s\n' "$2" "$SILENT_LANE"
    printf 'fixture.pass-future|fast|fixture|true|2999-01-01|bash %s\n' "$SILENT_LANE"
    printf 'fixture.skips|fast|fixture|true|%s|bash %s\n' "$3" "$SKIP_LANE"
    printf 'fixture.fails|fast|fixture|true|2020-01-01|bash %s\n' "$SKIP_RED_LANE"
    printf 'fixture.edited|fast|fixture|true|2020-01-01|bash %s%s\n' "$SILENT_LANE" "$4"
    printf 'EOF\n}\n# trailing line\n'
}
drive_record() { # <out_dir> <manifest> <neuter>
    local out_dir="$1" manifest="$2" neuter="$3" edited
    (
        export TRUST_COMPREHENSIVE_OUT_DIR="$out_dir"
        export TRUST_COMPREHENSIVE_RUN_ID="fixture"
        # shellcheck disable=SC1090
        . "$PREFIX" --record-last-green manifest
        TRUST_ROOT="$REPO_ROOT"
        MANIFEST_FILE="$manifest"
        case "$neuter" in
            neuter-skip) gate_skipped() { return 1; } ;;
            neuter-advance) last_green_advances() { return 0; } ;;
        esac
        echo "record-flag: $RECORD_LAST_GREEN; run-date: ${RUN_STARTED_AT%%T*}"
        while IFS='|' read -r gate_id _profiles category required last_green command; do
            run_gate "$gate_id" "$category" "$required" "$last_green" "$command"
        done < <(awk '/<<.EOF.$/ { on = 1; next } /^EOF$/ { on = 0 } on' "$manifest")
        # A person edits one row while the run is still going (same inode).
        edited="$(sed 's/^\(fixture\.edited|.*\)$/\1 --edited/' "$manifest")"
        printf '%s\n' "$edited" >"$manifest"
        record_last_green
    ) 2>&1
}
record_case() { # <name> <neuter> -> RECORD_OUT, RECORD_FILE, RUN_DATE
    RECORD_FILE="$WORK/$1.manifest.sh"
    fixture_manifest 2020-01-01 never 2020-01-01 "" >"$RECORD_FILE"
    chmod 755 "$RECORD_FILE"
    RECORD_OUT="$(drive_record "$WORK/$1" "$RECORD_FILE" "$2")"
    RUN_DATE="$(printf '%s\n' "$RECORD_OUT" | sed -n 's/^record-flag: 1; run-date: //p')"
}

record_case record keep
case "$RUN_DATE" in
    [0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]) ;;
    *) fail "the prefix did not take --record-last-green, or no run date: $RECORD_OUT" ;;
esac
fixture_manifest "$RUN_DATE" "$RUN_DATE" 2020-01-01 " --edited" >"$WORK/record.expected"
if ! cmp -s "$WORK/record.expected" "$RECORD_FILE"; then
    fail "--record-last-green did not write exactly the offered rows: $(diff "$WORK/record.expected" "$RECORD_FILE")"
fi
[ "$(ls -l "$RECORD_FILE" | cut -c1-10)" = "-rwxr-xr-x" ] \
    || fail "--record-last-green lost the manifest file's mode: $(ls -l "$RECORD_FILE")"
case "$RECORD_OUT" in
    *"last-green: recorded 2 row(s)"*"fixture.pass-old: 2020-01-01 -> $RUN_DATE"*) ;;
    *) fail "--record-last-green did not report the two rows it moved: $RECORD_OUT" ;;
esac
case "$RECORD_OUT" in
    *"last-green: fixture.edited NOT recorded: its command changed during the run"*) ;;
    *) fail "a row edited mid-run was not reported as unrecorded: $RECORD_OUT" ;;
esac
case "$RECORD_OUT" in
    *"LAST-GREEN: update the manifest row for fixture.pass-future"*)
        fail "a PASS offered to move a later date backward: $RECORD_OUT" ;;
esac

# 9. MUTATION -- with gate_skipped never matching, the SKIP row IS recorded:
#    the grading, and nothing else, is what keeps a SKIP out of the manifest.
record_case record-skip neuter-skip
fixture_manifest "$RUN_DATE" "$RUN_DATE" "$RUN_DATE" " --edited" >"$WORK/record-skip.expected"
cmp -s "$WORK/record-skip.expected" "$RECORD_FILE" \
    || fail "neutering gate_skipped did not let the SKIP row be recorded: $(diff "$WORK/record-skip.expected" "$RECORD_FILE")"

# 10. MUTATION -- with the offer rule neutered, run_gate offers the later date
#     too, and the writer still refuses to move it backward on its own check.
record_case record-backward neuter-advance
case "$RECORD_OUT" in
    *"LAST-GREEN: update the manifest row for fixture.pass-future"*) ;;
    *) fail "neutering last_green_advances did not produce the backward offer: $RECORD_OUT" ;;
esac
fixture_manifest "$RUN_DATE" "$RUN_DATE" 2020-01-01 " --edited" >"$WORK/record-backward.expected"
cmp -s "$WORK/record-backward.expected" "$RECORD_FILE" \
    || fail "the writer moved a date backward: $(diff "$WORK/record-backward.expected" "$RECORD_FILE")"

# 11. The flag is opt-in and stripped before the profile is read.
[ "$(bash "$HARNESS" --record-last-green --list manifest)" = "$(bash "$HARNESS" --list manifest)" ] \
    || fail "--record-last-green changed the selected profile"
grep -q '^if \[ "\$RECORD_LAST_GREEN" = "1" \] && ! record_last_green; then$' "$HARNESS" \
    || fail "the harness does not call record_last_green only under --record-last-green"

if [ "$FAILURES" -ne 0 ]; then
    echo "gate warning surface: $FAILURES check(s) failed" >&2
    exit 1
fi
echo "gate warning surface: PASS (positive, silent-negative, neutering mutation," \
    "skip, skip-negative, skip-red, skip neutering mutation, record-last-green and its two mutations)"
