#!/usr/bin/env bash
# Parse every gate script and orchestrator without running one.
#
# Shell files are parsed with `bash -n`, the Perl helpers under `scripts/hooks/`
# with `perl -c`. Tests: scripts/tests/check_gate_script_syntax_test.py.
#
# A syntax error in a gate script surfaces as exit 2 at the moment the gate is
# invoked — which, for the release-profile lanes, is hours into a run. `bash -n`
# costs milliseconds and catches it at push time. The manifest names each
# orchestrator individually; this covers the gate scripts and every other shell
# entrypoint under `scripts/`, so a new one is parsed by existing.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

ERR_LOG="$(mktemp)"
trap 'rm -f "$ERR_LOG"' EXIT

TOTAL=0
BAD=()

# `scripts/hooks-pin/*` was missing from this list while the header already claimed
# "every other shell entrypoint under `scripts/`" — and that directory is the one
# `core.hooksPath` actually points at on this machine, so a syntax error there breaks
# every push rather than one gate. Added 2026-08-20 alongside the oracle-freeze lane.
# `scripts/lib/*.sh` added 2026-08-20 with the measurement-provenance lane: the
# header has always claimed "every other shell entrypoint under `scripts/`", and
# `scripts/lib/` held three sourceable helpers that no `bash -n` ever reached.
# Measured before widening: all three parse, so this adds coverage and no red.
for script in scripts/*.sh scripts/lib/*.sh scripts/tests/*.sh scripts/hooks/* scripts/hooks-pin/*; do
  [ -f "$script" ] || continue
  # `scripts/hooks-pin/` holds a `.txt` waiver table beside its hooks. `bash -n` on a
  # pipe-separated data file happens to parse today (`a|b|c` is a pipeline) and would
  # start failing the moment a reason column contains an unmatched quote. Skip data.
  case "$script" in *.md|*.txt) continue ;; esac
  # Each file is parsed by its own language's parser. `scripts/hooks/_ssh_probe.pl`
  # (b2c6fa0712, 2026-10-25) is Perl that `_ssh_keepalive.sh` runs with `perl`;
  # `bash -n` read it as shell and this check was red from that day on a file that
  # was never broken. `perl -c` compiles the file without running its main program
  # (it does run `use` imports and BEGIN blocks, which the hook runs anyway). A host
  # without `perl` fails here, as the hook's helper would fail there.
  case "$script" in
    *.pl) parse=(perl -c) ;;
    *) parse=(bash -n) ;;
  esac
  TOTAL=$((TOTAL + 1))
  if ! "${parse[@]}" "$script" >"$ERR_LOG" 2>&1; then
    BAD+=("$script")
    sed 's/^/    /' "$ERR_LOG" >&2
  fi
done

if [ "$TOTAL" -eq 0 ]; then
  echo "gate script syntax: no scripts found — an empty scan is not a pass" >&2
  exit 2
fi

if [ "${#BAD[@]}" -ne 0 ]; then
  printf 'gate script syntax FAIL (%d/%d): %s\n' "${#BAD[@]}" "$TOTAL" "${BAD[*]}" >&2
  exit 1
fi

echo "gate script syntax: $TOTAL scripts parse"
