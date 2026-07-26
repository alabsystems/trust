#!/usr/bin/env bash
# check_frontier_ratchet.sh — the proof frontier may not go backwards.
#
# `targo trust self-improve` verifies Trust's own crates and reduces the run to
# a frontier: obligations, proved, runtime-checked, failed, unknown. Nothing
# consumed that number, so the one measurement that would notice the rewrite
# loop (or the verifier, or a refactor) making Trust prove LESS than it did
# yesterday was being thrown away after every run.
#
# This is the consumer. It compares a fresh measurement against the committed
# baseline and fails when `total_proved` has dropped. `unproved` is reported but
# does not fail on its own: new code legitimately adds obligations, and a gate
# that punishes writing code is a gate people delete.
#
#   default (--check): measure, compare, fail on proved_delta < 0.
#   --update:          mint/refresh the baseline from a fresh measurement.
#                      Review the diff before committing it — this is the file
#                      that decides what "worse" means.
#
# A missing baseline fails closed with instructions rather than passing: an
# absent number is not evidence of no regression.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${TRUST_FRONTIER_BASELINE:-$ROOT/reports/trust-frontier-baseline.json}"
TARGO_TRUST="${TRUST_FRONTIER_TARGO:-$ROOT/build/host/stage2/bin/targo-trust}"

case "${1:---check}" in
  --check) MODE="check" ;;
  --update) MODE="update" ;;
  -h|--help)
    sed -n '2,21p' "${BASH_SOURCE[0]}"
    exit 0
    ;;
  *) echo "usage: scripts/check_frontier_ratchet.sh [--check|--update]" >&2; exit 2 ;;
esac
if [[ "$#" -gt 1 ]]; then
  echo "usage: scripts/check_frontier_ratchet.sh [--check|--update]" >&2
  exit 2
fi

if [[ ! -x "$TARGO_TRUST" ]]; then
  echo "FRONTIER RATCHET CANNOT RUN: no targo-trust at $TARGO_TRUST" >&2
  echo "  Build the toolchain, or set TRUST_FRONTIER_TARGO=/path/to/targo-trust." >&2
  exit 2
fi

MEASURED="$(mktemp "${TMPDIR:-/tmp}/trust-frontier-XXXXXX.json")"
trap 'rm -f "$MEASURED"' EXIT

# The measurement itself: a real verification run over the Trust-owned crates.
"$TARGO_TRUST" self-improve --out "$MEASURED" >/dev/null

if [[ "$MODE" == "update" ]]; then
  mkdir -p "$(dirname "$BASELINE")"
  cp "$MEASURED" "$BASELINE"
  echo "FRONTIER BASELINE WRITTEN: $BASELINE"
  python3 - "$BASELINE" <<'PY'
import json, sys
with open(sys.argv[1]) as handle:
    frontier = json.load(handle)
print(
    "  total_obligations={} total_proved={} total_unproved={} convergence_score={:.4f}".format(
        frontier.get("total_obligations", 0),
        frontier.get("total_proved", 0),
        frontier.get("total_unproved", 0),
        float(frontier.get("convergence_score", 0.0)),
    )
)
PY
  exit 0
fi

if [[ ! -f "$BASELINE" ]]; then
  echo "FRONTIER RATCHET HAS NO BASELINE: $BASELINE is missing" >&2
  echo "  Mint it from a full toolchain run: scripts/check_frontier_ratchet.sh --update" >&2
  echo "  An absent baseline cannot witness that nothing regressed." >&2
  exit 2
fi

python3 - "$BASELINE" "$MEASURED" <<'PY'
import json, sys

def load(path):
    with open(path) as handle:
        return json.load(handle)

baseline, current = load(sys.argv[1]), load(sys.argv[2])
proved_delta = current.get("total_proved", 0) - baseline.get("total_proved", 0)
unproved_delta = current.get("total_unproved", 0) - baseline.get("total_unproved", 0)
print(
    "frontier: proved {} -> {} ({:+d}), unproved {} -> {} ({:+d})".format(
        baseline.get("total_proved", 0),
        current.get("total_proved", 0),
        proved_delta,
        baseline.get("total_unproved", 0),
        current.get("total_unproved", 0),
        unproved_delta,
    )
)

# Per-crate detail, so a red ratchet names the crate that lost ground rather
# than leaving the reader to diff two JSON blobs by eye.
before = {entry.get("crate"): entry for entry in baseline.get("crates", [])}
for entry in current.get("crates", []):
    name = entry.get("crate")
    was = before.get(name)
    if was is None:
        continue
    delta = entry.get("proved", 0) - was.get("proved", 0)
    if delta < 0:
        print("  REGRESSED {}: proved {} -> {}".format(name, was.get("proved", 0), entry.get("proved", 0)))

if proved_delta < 0:
    print("FRONTIER RATCHET RED: Trust proves {} fewer obligations than the baseline".format(-proved_delta))
    sys.exit(1)
print("FRONTIER RATCHET GREEN")
PY
