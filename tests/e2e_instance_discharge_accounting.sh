#!/bin/bash
# Instance-discharge transport accounting, end to end: targo-trust over the
# compiler's REAL envelope for a `proved` instance-discharge row.
#
# A `proved` instance-discharge row (kind `instance-hypothesis:discharge`,
# solver `trust-classifier`; OD-1 phase 1) reports the resolved callee's
# verdict and carries no proof of its own. The compiler therefore counts it
# `skipped` in the function's summary counters and in the crate summary
# (`PublishedRowTally::json_counts`), while the row itself travels with outcome
# `proved`. targo-trust cross-checks every function's rows against those
# counters and the crate's rows against the crate summary. A reconciler that
# counts the row by its outcome disagrees with the compiler by exactly one row
# per proved discharge row; it then publishes two accounting rows of its own
# (`transport:summary-accounting`, `transport:crate-summary-accounting`), they
# carry no stable key, and a keyless row makes the whole unit COULD NOT RUN
# (T9). That was trust main until this test: every crate with a proved
# discharge row was refused, and nothing ran targo-trust over a compiler-made
# discharge row (the compiler's half is pinned by
# tests/ui/trust/instance_hypothesis/discharge_row_per_instance.rs, targo's by
# unit tests).
#
# This runs `targo trust check --lib --allow-l0-gaps` on a copy of
# tests/fixtures/instance-discharge (one generic with one trait-method site,
# named at one instance whose callee is panic-free) and requires:
#   * a `[PROVED] [instance-hypothesis:discharge]` row in the run's report. If
#     the compiler stops publishing one for this source the test pins nothing,
#     and it FAILS so the fixture is re-pinned instead of passing empty;
#   * a `Summary:` line, no `COULD NOT RUN:` refusal ("verification did not
#     run"), no `[transport:` row;
#   * in report.json: neither the gate decision nor the determinism outcome is
#     could-not-run, no function is unkeyed, no row is one targo synthesized
#     for a transport defect, and the gate counts at least as many `assumed`
#     rows as there are proved discharge rows (such a row is conditional
#     evidence, never proof).
#
# It does not pin the counts, the exit status or `measured`: those belong to
# the rows of the fixture, not to the accounting.
#
# This needs a BUILT toolchain. It runs on --targo PATH; else on the TARGO of
# its environment, which is how scripts/run_e2e_shell_corpus.sh hands every
# script of the corpus the toolchain it was pointed at (TRUST_E2E_STAGE2_BIN),
# so the corpus cannot judge one toolchain while this script runs another;
# else on the repo-local stage2 targo (build/*/stage2/bin/targo). It prints
# which one it ran. It is not a unit test and has no silent skip: a missing
# toolchain is exit 3 (could not run).
#
# Usage:
#   tests/e2e_instance_discharge_accounting.sh [--targo PATH] [--crate DIR] [--keep]
#
# Exit: 0 the run is accounted and summarized; 1 an accounting row, a refusal,
# a missing Summary line, or a fixture with no proved discharge row; 2
# usage/setup error; 3 could not run (no toolchain, or the run wrote no report).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# The corpus runner's TARGO, when there is one; --targo overrides it.
TARGO="${TARGO:-}"
TARGO_FROM="the environment's TARGO"
CRATE="$TRUST_ROOT/tests/fixtures/instance-discharge"
KEEP=0
while [ "$#" -gt 0 ]; do
    case "$1" in
        --targo) [ "$#" -ge 2 ] || { echo "--targo needs a path" >&2; exit 2; }
                 TARGO="$2"; TARGO_FROM="--targo"; shift 2 ;;
        --crate) [ "$#" -ge 2 ] || { echo "--crate needs a directory" >&2; exit 2; }
                 CRATE="$(cd "$2" && pwd)" || exit 2; shift 2 ;;
        --keep) KEEP=1; shift ;;
        -h|--help) sed -n '2,52p' "$0"; exit 0 ;;
        *) echo "unknown argument: $1" >&2; exit 2 ;;
    esac
done
[ -f "$CRATE/Cargo.toml" ] || { echo "no Cargo.toml in $CRATE" >&2; exit 2; }

find_stage2_targo() {
    local candidate
    while IFS= read -r candidate; do
        if [ -x "$candidate" ] && [ -x "$(dirname "$candidate")/trustc" ]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done < <(find -H "$TRUST_ROOT/build" -path "*/stage2/bin/targo" -type f -perm -111 -print 2>/dev/null | sort -r)
    return 1
}

if [ -z "$TARGO" ]; then
    if ! TARGO="$(find_stage2_targo)"; then
        echo "COULD NOT RUN: no stage2 targo under $TRUST_ROOT/build/*/stage2/bin; build one (./x.py build --stage 2), pass --targo, or set TARGO" >&2
        exit 3
    fi
    TARGO_FROM="the repo-local stage2"
fi
if ! "$TARGO" --unverified --version >/dev/null 2>&1; then
    echo "COULD NOT RUN: $TARGO is not a Trust targo (it rejects --unverified)" >&2
    exit 3
fi
command -v python3 >/dev/null 2>&1 || { echo "COULD NOT RUN: python3 is required" >&2; exit 3; }

# Private scratch (never /tmp: targo refuses a world-writable path component).
WORK="$(mktemp -d "${TMPDIR:-$HOME}/trust-instance-discharge.XXXXXX")"
cleanup() {
    if [ "$KEEP" = 1 ]; then echo "kept $WORK"; else rm -rf "$WORK"; fi
}
trap cleanup EXIT

echo "=== Trust instance-discharge transport accounting ==="
echo "targo: $TARGO ($("$TARGO" --unverified --version 2>/dev/null | head -1)), from $TARGO_FROM"
echo "crate: $CRATE"
echo

# A copy of the crate, so its target directory stays out of the tree.
COPY="$WORK/$(basename "$CRATE")"
cp -R "$CRATE" "$COPY"
rm -rf "$COPY/target"
OUT="$WORK/run"
mkdir -p "$OUT/report"
LOG="$OUT/check.log"
REPORT="$OUT/report/report.json"

rc=0
(
    cd "$COPY"
    env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u TRUSTFLAGS -u CARGO_ENCODED_TRUSTFLAGS \
        CARGO_TARGET_DIR="$OUT/target" \
        "$TARGO" trust check --all-rows --lib --allow-l0-gaps --report-dir "$OUT/report" >"$LOG" 2>&1
) || rc=$?
echo "targo trust check --all-rows --lib --allow-l0-gaps: exit $rc"
if [ ! -s "$REPORT" ]; then
    echo "COULD NOT RUN: the run wrote no report ($LOG):" >&2
    tail -20 "$LOG" >&2 || true
    exit 3
fi

status=0
fail() {
    echo "  FAIL: $1"
    status=1
}

# The lines the judgment is about, as the run printed them.
grep -E '^[[:space:]]*\[[A-Z-]+\] \[(instance-hypothesis:discharge|transport:[a-z-]+)\]|^(Summary|COULD NOT RUN|Result):|^[[:space:]]*Gate:' "$LOG" \
    | cut -c1-240 | sed 's/^/  | /' || true

proved_discharge="$(grep -cE '^[[:space:]]*\[PROVED\] \[instance-hypothesis:discharge\]' "$LOG" || true)"
if [ "$proved_discharge" -lt 1 ]; then
    fail "the run published no [PROVED] [instance-hypothesis:discharge] row: the fixture no longer exercises the case this test exists for (re-pin it on a source whose instance discharge is proved)"
fi
# The refusal printed in place of a Summary line ("COULD NOT RUN: verification
# did not run to a measurement: ..."), by the phrase its consumers key on.
if grep -qE '^COULD NOT RUN:|verification did not run' "$LOG"; then
    fail "the run was refused: COULD NOT RUN, verification did not run to a measurement"
fi
if ! grep -q '^Summary: ' "$LOG"; then
    fail "the run printed no Summary line"
fi
if grep -qE '\[transport:[a-z-]+\]' "$LOG"; then
    fail "the run carries a transport: row: targo's row counts disagree with the compiler's summary counters"
fi

judge_rc=0
python3 - "$REPORT" "$proved_discharge" <<'PY' || judge_rc=$?
import json, sys

with open(sys.argv[1], encoding="utf-8") as fh:
    report = json.load(fh)
proved_discharge = int(sys.argv[2])
ok = True

def fail(message):
    global ok
    ok = False
    print(f"  FAIL: {message}")

gate = report.get("verification_gate") or {}
counts = gate.get("counts") or {}
block = gate.get("determinism")
if block is None:
    print("COULD NOT RUN: report.json carries no verification_gate.determinism "
          "(a toolchain without the determinism block)")
    sys.exit(3)

print("  gate: decision={} exit_code={} counts={}".format(
    gate.get("decision"), gate.get("exit_code"),
    " ".join(f"{key}={counts.get(key)}" for key in
             ("proved", "failed", "runtime_checked", "assumed", "unknown", "total"))))
print("  determinism: outcome={} unkeyed_functions={}".format(
    block.get("outcome"), len(block.get("unkeyed_functions") or [])))

if gate.get("decision") == "could-not-run":
    fail("the gate decision is could-not-run")
if block.get("outcome") == "could-not-run":
    fail("the determinism outcome is could-not-run")
for function in block.get("unkeyed_functions") or []:
    fail(f"a row of `{function.rsplit(')::', 1)[-1]}` has no stable key")

# A row targo synthesized for a transport defect: backend `targo-trust`, and
# the canonical report keeps its wire kind in the description.
for function in report.get("functions") or []:
    for row in function.get("obligations") or []:
        description = str(row.get("description", ""))
        if row.get("solver") == "targo-trust" and "transport:" in description:
            reason = str((row.get("outcome") or {}).get("reason", ""))
            fail("targo-trust reported `{}` for `{}`: {}".format(
                description, str(function.get("function", "")).rsplit(")::", 1)[-1],
                reason.split("returned unknown: ", 1)[-1][:260]))

assumed = counts.get("assumed")
if not isinstance(assumed, int) or assumed < proved_discharge:
    fail(f"the gate counts {assumed} assumed row(s) for {proved_discharge} proved "
         "instance-discharge row(s): such a row is conditional evidence, never proof")

sys.exit(0 if ok else 1)
PY
case "$judge_rc" in
    0) ;;
    3) exit 3 ;;
    *) status=1 ;;
esac

echo
if [ "$status" = 0 ]; then
    echo "PASS: targo-trust accounted for the compiler's proved instance-discharge row and summarized the run"
else
    echo "FAIL: see above (log: $LOG)"
    sed -n '/^=== Trust Verification Report ===/,/^=================================/p' "$LOG" | cut -c1-300 | head -40 || true
fi
exit "$status"
