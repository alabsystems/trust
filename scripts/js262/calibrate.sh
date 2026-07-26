#!/usr/bin/env bash
# calibrate.sh — thin runner for the js262 calibration gate.
#
# Fetch + verify the pinned Test262 corpus (fail-closed on drift), then run
# the trust-js-differential `calibrate` subcommand over the frozen S0 slice
# with bounded parallelism and pinned engines. Extra arguments are forwarded
# to the calibrate subcommand verbatim.
#
# The ledger and artifact paths are passed absolutely because the run happens
# from `crates/` (cargo needs that workspace); the subcommand's relative
# defaults would resolve under `crates/` and silently miss every ledger.
#
# Engines resolve from PATH; the harness asserts the version pin (node 24.5.0,
# bun 1.3.14) and fails closed on a mismatch, so an override only relocates the
# install, it never admits an unpinned engine.
#
# Env knobs:
#   TRUST_JOBS     cargo -j bound (default 4 — NEVER run unbounded builds)
#   TRUST_JS_NODE  node binary for an install outside PATH
#   TRUST_JS_BUN   bun binary  for an install outside PATH
#
# Author: Andrew Yates
# Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

"$REPO_ROOT/scripts/js262/fetch_corpus.sh"

PIN="$REPO_ROOT/tests/js262/corpus-pin.json"
SHA="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["git_commit_hash"])' "$PIN")"
CORPUS="$REPO_ROOT/build/js262/test262-$SHA"

JOBS="${TRUST_JOBS:-4}"

cd "$REPO_ROOT/crates"
exec env \
    TZ=UTC LANG=C LC_ALL=C \
    RUSTC_BOOTSTRAP=1 \
    cargo run -j "$JOBS" -p trust-js-differential -- \
    calibrate \
    --corpus "$CORPUS" \
    --slice "$REPO_ROOT/tests/js262/S0.toml" \
    --ledgers "$REPO_ROOT/tests/js262" \
    --out-dir "$REPO_ROOT/build/js262/calibration" \
    --sem \
    "$@"
