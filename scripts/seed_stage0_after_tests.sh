#!/bin/bash
# re-seed bootstrap/trust-stage0 from a verified build.
#
# Closes the loop on bootstrap recreation: after a successful build +
# test orchestrator run, this script:
#
#   1. Verifies the test orchestrator's summary log shows all tiers
#      passed (or all expected-failures matched the ledger).
#   2. Invokes `./x.py dist --stage 2` to produce build/dist artifacts.
#   3. Runs `src/tools/trust-stage0-dist/prepare.py` to materialize
#      `bootstrap/trust-stage0/` from the dist output.
#   4. Stages the new stage0 payloads + updated `src/stage0` manifest
#      for review (does NOT commit — humans review the seed before it
#      lands).
#
# This is the missing piece from `scripts/recreate_bootstrap.py`: once
# you've built a working stage2 toolchain, the next checkout shouldn't
# have to repeat the genesis-adapter dance. Running this and committing
# the result means fresh-clone bootstrap reads stage0 directly.
#
# Usage:
#   scripts/seed_stage0_after_tests.sh             # gated on test pass
#   scripts/seed_stage0_after_tests.sh --force     # skip the gate
#                                                  # (don't unless you
#                                                  # really mean it)
#
# Exit codes:
#   0   stage0 seed materialized; review and commit
#   1   precondition failed (no successful build, tests not passed, etc.)
#   2   dist or prepare.py failed
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

set -u
cd "$(dirname "$0")/.."

REPO="$(pwd -P)"
LOGS="${REPO}/build-logs"
PY=/opt/homebrew/opt/python@3.14/bin/python3.14
HOST="aarch64-apple-darwin"
STAGE2_BIN="${REPO}/build/${HOST}/stage2/bin"
DIST_DIR="${REPO}/build/dist"

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
    FORCE=1
fi

echo "Trust stage0 seeder"
echo "  repo:  ${REPO}"
echo "  host:  ${HOST}"

# Precondition 1: a working stage2 toolchain.
if [[ ! -x "${STAGE2_BIN}/trustc" ]] || [[ ! -x "${STAGE2_BIN}/targo" ]]; then
    echo "ERROR: stage2 toolchain not built (need ${STAGE2_BIN}/trustc and targo)"
    echo "       run scripts/recreate_bootstrap.py first"
    exit 1
fi

# Precondition 2: test orchestrator reports a clean run (unless --force).
if [[ ${FORCE} -eq 0 ]]; then
    SUMMARY="${LOGS}/tests-summary.log"
    if [[ ! -f "${SUMMARY}" ]]; then
        echo "ERROR: ${SUMMARY} not found"
        echo "       run scripts/run_tests_after_build.sh first, or pass --force"
        exit 1
    fi
    # Require at least one PASS and zero FAIL lines.
    PASS_COUNT=$(grep -c ': PASS' "${SUMMARY}" || echo 0)
    FAIL_COUNT=$(grep -c ': FAIL ' "${SUMMARY}" || echo 0)
    echo "  test orchestrator: ${PASS_COUNT} PASS, ${FAIL_COUNT} FAIL"
    if [[ "${PASS_COUNT}" -eq 0 ]] || [[ "${FAIL_COUNT}" -ne 0 ]]; then
        echo "ERROR: orchestrator hasn't run cleanly. Tail of ${SUMMARY##*/}:"
        tail -10 "${SUMMARY}" | sed 's/^/  /'
        echo "       fix the failing tier or pass --force (not recommended)"
        exit 1
    fi
fi

# Step 1: produce dist artifacts via x.py dist.
echo
echo "Step 1/4: ./x.py dist --stage 2"
DIST_LOG="${LOGS}/seed-stage0-xpy-dist.log"
mkdir -p "${LOGS}"
echo "  log: ${DIST_LOG}"
if ! "${PY}" "${REPO}/x.py" dist --stage 2 -j "${TRUST_JOBS:-4}" > "${DIST_LOG}" 2>&1; then
    echo "ERROR: x.py dist failed; see ${DIST_LOG##*/}"
    tail -20 "${DIST_LOG}" | sed 's/^/  /'
    exit 2
fi
echo "  dist artifacts: ${DIST_DIR}"

# Step 2: generate the release channel manifest (channel-rust-trust.toml).
# Plain `x.py dist` produces the tarballs but never runs build-manifest, so
# prepare.py's required source manifest is missing. Build the tool and invoke
# it directly (the `x.py run src/tools/build-manifest` path panics unless
# dist.sign-folder/upload-addr are set in bootstrap.toml). build-manifest args
# are: <input-dist> <output-dist> <date> <upload-addr> <channel>. prepare.py
# reads the date back out of the manifest and recomputes every dist URL from
# the stage0 dist_server, so the upload-addr is an inert placeholder here.
echo
echo "Step 2/4: build-manifest -> channel-rust-trust.toml"
BM_LOG="${LOGS}/seed-stage0-build-manifest.log"
echo "  log: ${BM_LOG}"
if ! "${PY}" "${REPO}/x.py" build src/tools/build-manifest --stage 2 -j "${TRUST_JOBS:-4}" > "${BM_LOG}" 2>&1; then
    echo "ERROR: building build-manifest failed; see ${BM_LOG##*/}"
    tail -20 "${BM_LOG}" | sed 's/^/  /'
    exit 2
fi
BUILD_MANIFEST=$(find "${REPO}/build" -type f -name build-manifest -path '*stage2-tools*' 2>/dev/null | head -1)
if [[ -z "${BUILD_MANIFEST}" ]] || [[ ! -x "${BUILD_MANIFEST}" ]]; then
    echo "ERROR: build-manifest binary not found under ${REPO}/build after build"
    exit 2
fi
MANIFEST_DATE=$(date +%Y-%m-%d)
# Placeholder base URL: prepare.py rewrites all dist URLs, so this is inert.
MANIFEST_UPLOAD_ADDR="https://static.trust-lang.org"
echo "  build-manifest: ${BUILD_MANIFEST}"
echo "  date: ${MANIFEST_DATE}"
if ! "${BUILD_MANIFEST}" "${DIST_DIR}" "${DIST_DIR}" "${MANIFEST_DATE}" "${MANIFEST_UPLOAD_ADDR}" trust >> "${BM_LOG}" 2>&1; then
    echo "ERROR: build-manifest run failed; see ${BM_LOG##*/}"
    tail -20 "${BM_LOG}" | sed 's/^/  /'
    exit 2
fi
if [[ ! -f "${DIST_DIR}/channel-rust-trust.toml" ]]; then
    echo "ERROR: build-manifest did not produce ${DIST_DIR}/channel-rust-trust.toml"
    tail -20 "${BM_LOG}" | sed 's/^/  /'
    exit 2
fi
echo "  manifest: ${DIST_DIR}/channel-rust-trust.toml"

# Step 3: run prepare.py with the canonical Trust seed args.
echo
echo "Step 3/4: src/tools/trust-stage0-dist/prepare.py"
# Derive the git commit hash for the seed.
GIT_SHA=$(git -C "${REPO}" rev-parse HEAD)
echo "  git-commit-hash: ${GIT_SHA}"
PREP_LOG="${LOGS}/seed-stage0-prepare.log"
echo "  log: ${PREP_LOG}"
if ! "${PY}" "${REPO}/src/tools/trust-stage0-dist/prepare.py" \
    --input-dist "${DIST_DIR}" \
    --source-channel trust \
    --owned-channel trust \
    --archive-format xz \
    --stage0-seed-only \
    --git-commit-hash "${GIT_SHA}" \
    --output-root "${REPO}/bootstrap/trust-stage0" \
    --stage0-output "${REPO}/src/stage0" \
    > "${PREP_LOG}" 2>&1; then
    echo "ERROR: prepare.py failed; see ${PREP_LOG##*/}"
    tail -30 "${PREP_LOG}" | sed 's/^/  /'
    exit 2
fi

# Step 4: stage the result for human review.
echo
echo "Step 4/4: staging stage0 payloads for review"
git -C "${REPO}" add bootstrap/trust-stage0 src/stage0 2>&1 | sed 's/^/  /'

echo
echo "Seed materialized. Review:"
echo "  git status"
echo "  ls bootstrap/trust-stage0/dist/"
echo
echo "When satisfied, commit:"
echo "  git commit -m 'Refresh bootstrap/trust-stage0 from $(git rev-parse --short HEAD)'"
echo
echo "After commit, a fresh clone will not need scripts/recreate_bootstrap.py — "
echo "./x.py build will use this in-tree stage0 directly."
