#!/usr/bin/env bash
# The `tests/e2e_*.sh` corpus as one schedulable gate.
#
# The corpus is a lane in its own right: it is the only coverage several of the
# toolchain's public surfaces have, and it should be runnable without first
# committing to the tier sequence of `scripts/run_tests_after_build.sh`.
#
# Every script gets the stage2 sysroot on PATH and the four tool env vars its
# peers already read. A script that cannot find `trustc` fails before its own
# assertions start, which reads as a test failure and is not one — so a missing
# stage2 is exit 2 up front, not a corpus of red scripts.
#
# A zero-script run is a failure, not a pass: an empty glob must never be
# mistaken for a clean corpus.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

STAGE2_BIN="${TRUST_E2E_STAGE2_BIN:-$REPO_ROOT/build/host/stage2/bin}"
if [ ! -x "$STAGE2_BIN/trustc" ]; then
  echo "e2e corpus: no stage2 trustc at $STAGE2_BIN/trustc" >&2
  echo "  build it (python3 x.py build --stage 2) or set TRUST_E2E_STAGE2_BIN" >&2
  exit 2
fi

TOTAL=0
PASSED=0
FAILED_SCRIPTS=()

# tests/e2e_two_language_programs.sh has a manifest row of its own
# (`release.two-language-programs`, roadmap WS8.8) because it writes evidence
# artifacts the corpus tally cannot carry; running it here as well would be the
# same battery twice per release. It is skipped by NAME, and only that one.
CORPUS_SKIP="tests/e2e_two_language_programs.sh"

for script in tests/e2e_*.sh; do
  [ -f "$script" ] || continue
  if [ "$script" = "$CORPUS_SKIP" ]; then
    echo "=== $script === skipped: runs as its own manifest row (release.two-language-programs)"
    continue
  fi
  TOTAL=$((TOTAL + 1))
  echo "=== $script ==="
  if PATH="$STAGE2_BIN:$PATH" \
     TRUSTC="$STAGE2_BIN/trustc" \
     TARGO="$STAGE2_BIN/targo" \
     TARGO_TRUST="$STAGE2_BIN/targo-trust" \
     TRUSTD="$STAGE2_BIN/trustd" \
     bash "$script" </dev/null; then
    PASSED=$((PASSED + 1))
    echo "--- $script PASS"
  else
    status=$?
    FAILED_SCRIPTS+=("$script(exit=$status)")
    echo "--- $script FAIL exit=$status"
  fi
done

if [ "$TOTAL" -eq 0 ]; then
  echo "e2e corpus: no tests/e2e_*.sh found — an empty corpus is not a pass" >&2
  exit 2
fi

echo
echo "e2e corpus: $PASSED/$TOTAL passed"
if [ "${#FAILED_SCRIPTS[@]}" -ne 0 ]; then
  printf 'e2e corpus FAIL: %s\n' "${FAILED_SCRIPTS[*]}" >&2
  exit 1
fi
echo "e2e corpus: PASS"
