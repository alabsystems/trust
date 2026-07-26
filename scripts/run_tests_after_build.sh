#!/bin/bash
# Run developer test tiers after the current x.py build exits.
#
# This shell/Python orchestrator is a fail-closed diagnostic, not independently
# authenticated release proof. It requires and verifies the Stage2 producer
# receipt; it never treats an ignored log line as build-success authority.
#
# Tiers (in order — run all, then fail if any required tier failed):
#   T0  tidy / format / lint sanity              ~ 5 min
#   T1  targo test on Trust verifier crates      ~10 min
#   T2  ./x.py test library/std (stdlib)         ~30 min
#   T3  Trust e2e shell scripts                  ~variable
#   T3b certified-monitor release E2Es (Linux)   ~variable
#   T4  ./x.py test tests/ui (canonical suite)   ~2-6 hours
#
# Outputs each tier's log under build-logs/tests-T*.log and a one-line
# summary per tier on this script's own stdout.
#
# Polls every 60s for the in-flight x.py build to exit; if exit code !=
# 0, refuses to run tests.

set -uo pipefail
cd "$(dirname "$0")/.."

REPO="$(pwd -P)"
LOGS="${REPO}/build-logs"
SUMMARY="${LOGS}/tests-summary.log"
mkdir -p "${LOGS}"

require_absolute_executable() {
    local name="$1"
    local path="$2"

    if [[ -z "${path}" ]]; then
        echo "missing ${name}; set ${name}=/absolute/path/to/tool" | tee -a "${SUMMARY}"
        exit 1
    fi
    if [[ "${path}" != /* ]]; then
        echo "${name} must be an absolute executable path: ${path}" | tee -a "${SUMMARY}"
        exit 1
    fi
    if [[ ! -x "${path}" ]]; then
        echo "${name} must be executable: ${path}" | tee -a "${SUMMARY}"
        exit 1
    fi
}

resolve_from_path() {
    local tool="$1"
    local resolved

    resolved="$(command -v "${tool}" 2>/dev/null)" || return 1
    [[ -n "${resolved}" ]] || return 1
    printf '%s\n' "${resolved}"
}

PY="${PYTHON:-$(resolve_from_path python3.11 || resolve_from_path python3 || true)}"
if [[ -z "${PY}" ]]; then
    echo "missing Python 3.11+ interpreter; set PYTHON=/absolute/path/to/python3.11" | tee -a "${SUMMARY}"
    exit 1
fi
require_absolute_executable PYTHON "${PY}"
if ! PY_IDENTITY="$("${PY}" - 2>/dev/null <<'PY'
import sys

if sys.version_info < (3, 11):
    raise SystemExit(1)
print(f"{sys.executable} {sys.version.split()[0]}")
PY
)";
then
    echo "Python 3.11+ required for Trust repository helper scripts: ${PY}" | tee -a "${SUMMARY}"
    exit 1
fi
if [[ -z "${PY_IDENTITY}" ]]; then
    echo "Python identity check produced no output: ${PY}" | tee -a "${SUMMARY}"
    exit 1
fi
echo "$(date '+%H:%M:%S') using PYTHON: ${PY} (${PY_IDENTITY})" | tee -a "${SUMMARY}"

GIT_BIN="/usr/bin/git"
require_absolute_executable GIT "${GIT_BIN}"

git_candidate_command() {
    env -i \
        PATH=/usr/bin:/bin \
        LC_ALL=C \
        LANG=C \
        GIT_CONFIG_GLOBAL=/dev/null \
        GIT_CONFIG_NOSYSTEM=1 \
        GIT_OPTIONAL_LOCKS=0 \
        GIT_NO_REPLACE_OBJECTS=1 \
        GIT_PAGER=cat \
        "${GIT_BIN}" \
        -c core.fsmonitor=false \
        -c core.untrackedCache=false \
        -c core.hooksPath=/dev/null \
        -c core.worktree="${REPO}" \
        -c core.filemode=true \
        -c core.symlinks=true \
        -c core.sparseCheckout=false \
        -c core.excludesFile=/dev/null \
        -C "${REPO}" "$@"
}

CANDIDATE_HEAD=""

assert_exact_clean_head() {
    local expected_head="${1:-}"
    local observed_head=""
    local status=""

    observed_head="$(git_candidate_command rev-parse HEAD 2>/dev/null)" || {
        echo "could not resolve candidate Git HEAD" | tee -a "${SUMMARY}"
        return 1
    }
    if [[ ${#observed_head} -ne 40 || "${observed_head}" == *[!0-9a-f]* ]]; then
        echo "candidate Git HEAD is not canonical lowercase 40-hex: ${observed_head:-<empty>}" \
            | tee -a "${SUMMARY}"
        return 1
    fi
    if [[ -n "${expected_head}" && "${observed_head}" != "${expected_head}" ]]; then
        echo "candidate Git HEAD changed: expected ${expected_head}, got ${observed_head}" \
            | tee -a "${SUMMARY}"
        return 1
    fi
    status="$(git_candidate_command status --porcelain=v1 --untracked-files=all --ignore-submodules=none 2>/dev/null)" || {
        echo "could not prove complete candidate Git cleanliness" | tee -a "${SUMMARY}"
        return 1
    }
    if [[ -n "${status}" ]]; then
        echo "candidate Git tree or recursive submodule closure is dirty:" | tee -a "${SUMMARY}"
        printf '%s\n' "${status}" | sed 's/^/    /' | tee -a "${SUMMARY}"
        return 1
    fi
    CANDIDATE_HEAD="${observed_head}"
}

FAILED_TIERS=()
OVERALL_RC=0

find_stage2_tool() {
    local tool="$1"
    local candidate

    while IFS= read -r candidate; do
        if [[ -x "$candidate" ]]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done < <(find "${REPO}/build" -path "*/stage2/bin/${tool}" -type f -print 2>/dev/null | sort)

    return 1
}

sha256_file() {
    local path="$1"
    local digest=""
    local output=""

    if [[ -x /usr/bin/sha256sum ]]; then
        output="$(/usr/bin/sha256sum -- "$path")" || return 1
        digest="${output%% *}"
    elif [[ -x /usr/bin/shasum ]]; then
        output="$(/usr/bin/shasum -a 256 -- "$path")" || return 1
        digest="${output%% *}"
    elif [[ -x /usr/bin/openssl ]]; then
        output="$(/usr/bin/openssl dgst -sha256 "$path")" || return 1
        digest="${output##* }"
    else
        echo "no SHA-256 implementation found for stage2 tool identity" | tee -a "${SUMMARY}"
        return 1
    fi

    if [[ ${#digest} -ne 64 || "$digest" == *[!0-9a-f]* ]]; then
        echo "invalid SHA-256 result for ${path}: ${digest:-<empty>}" | tee -a "${SUMMARY}"
        return 1
    fi
    printf '%s\n' "$digest"
}

STAGE2_TRUSTC_COMMIT=""
STAGE2_TRUSTC_RELEASE=""
STAGE2_TRUSTC_SHA256=""
STAGE2_TARGO_SHA256=""
STAGE2_TARGO_TRUST_SHA256=""
STAGE2_TRUSTD_SHA256=""
STAGE2_PROVENANCE_SHA256=""

record_stage2_tool_identity() {
    local name="$1"
    local path="$2"
    local identity=""
    local identity_one_line
    local expected_sysroot=""
    local reported_sysroot=""
    local reported_sysroot_raw=""
    local commit=""
    local commit_count=0
    local release=""
    local release_count=0
    local sha256_before=""
    local sha256_after=""
    local first_line=""
    local legacy_commit=""
    local legacy_commit_count=0

    case "${name}" in
        TRUSTC)
            identity="$(env -i "${path}" -Vv 2>/dev/null)" || {
                echo "${name} identity check failed: ${path}" | tee -a "${SUMMARY}"
                exit 1
            }
            case "${identity}" in
                *"binary: trustc"*) ;;
                *)
                    echo "${name} identity check did not report canonical trustc: ${path}" \
                        | tee -a "${SUMMARY}"
                    exit 1
                    ;;
            esac
            commit_count="$(printf '%s\n' "${identity}" | grep -c '^commit-hash: [0-9a-f][0-9a-f]*$' || true)"
            commit="$(printf '%s\n' "${identity}" | sed -n 's/^commit-hash: //p')"
            if [[ "$commit_count" -ne 1 || ${#commit} -ne 40 || "$commit" == *[!0-9a-f]* ]]; then
                echo "${name} identity must report exactly one canonical 40-lowerhex commit-hash: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            release_count="$(printf '%s\n' "${identity}" | grep -c '^release: .\+$' || true)"
            release="$(printf '%s\n' "${identity}" | sed -n 's/^release: //p')"
            if [[ "$release_count" -ne 1 || -z "$release" ]]; then
                echo "${name} identity must report exactly one non-empty release: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            STAGE2_TRUSTC_COMMIT="$commit"
            STAGE2_TRUSTC_RELEASE="$release"
            expected_sysroot="$(cd "$(dirname "${path}")/.." && pwd -P)" || {
                echo "${name} expected sysroot cannot be resolved: ${path}" | tee -a "${SUMMARY}"
                exit 1
            }
            reported_sysroot_raw="$(env -i "${path}" --print sysroot 2>/dev/null)" || {
                echo "${name} sysroot check failed: ${path}" | tee -a "${SUMMARY}"
                exit 1
            }
            reported_sysroot_raw="${reported_sysroot_raw%%$'\n'*}"
            if [[ -z "${reported_sysroot_raw}" ]]; then
                echo "${name} sysroot check produced no output: ${path}" | tee -a "${SUMMARY}"
                exit 1
            fi
            reported_sysroot="$(cd "${reported_sysroot_raw}" 2>/dev/null && pwd -P)" || {
                echo "${name} sysroot path does not exist: ${reported_sysroot_raw}" \
                    | tee -a "${SUMMARY}"
                exit 1
            }
            if [[ "${reported_sysroot}" != "${expected_sysroot}" ]]; then
                echo "${name} sysroot mismatch: expected ${expected_sysroot}, got ${reported_sysroot}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            identity="${identity}"$'\n'"sysroot: ${reported_sysroot}"
            ;;
        TARGO)
            if ! identity="$(env -i "${path}" -vV 2>/dev/null)" || [[ -z "${identity}" ]]; then
                identity="$(env -i "${path}" --version 2>/dev/null)" || {
                    echo "${name} identity check failed: ${path}" | tee -a "${SUMMARY}"
                    exit 1
                }
            fi
            case "${identity}" in
                targo\ *|*"binary: targo"*) ;;
                *)
                    echo "${name} identity check did not report targo identity: ${path}" \
                        | tee -a "${SUMMARY}"
                    exit 1
                    ;;
            esac
            if [[ "$(printf '%s\n' "${identity}" | grep -Fxc "commit-hash: ${STAGE2_TRUSTC_COMMIT}" || true)" -ne 1 \
                || "$(printf '%s\n' "${identity}" | grep -Fxc "release: ${STAGE2_TRUSTC_RELEASE}" || true)" -ne 1 ]]; then
                echo "${name} identity does not match stage2 trustc commit/release: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            ;;
        TARGO_TRUST)
            identity="$(env -i "${path}" --version 2>/dev/null)" || {
                echo "${name} identity check failed: ${path}" | tee -a "${SUMMARY}"
                exit 1
            }
            case "${identity}" in
                targo-trust\ *|*"trust.identity=targo trust"*) ;;
                *)
                    echo "${name} identity check did not report targo-trust identity: ${path}" \
                        | tee -a "${SUMMARY}"
                    exit 1
                    ;;
            esac
            if [[ "$(printf '%s\n' "${identity}" | grep -Fxc "trust-repo-commit-hash: ${STAGE2_TRUSTC_COMMIT}" || true)" -ne 1 ]]; then
                echo "${name} identity does not match stage2 trustc commit: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            ;;
        TRUSTD)
            if [[ -L "${path}" || ! -f "${path}" || ! -x "${path}" ]]; then
                echo "${name} must be an exact regular executable sibling: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            sha256_before="$(sha256_file "${path}")" || {
                echo "${name} could not be hashed before identity probe: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            }
            identity="$(
                env -i "${path}" --version 2>/dev/null
            )" || {
                echo "${name} identity check failed: ${path}" | tee -a "${SUMMARY}"
                exit 1
            }
            sha256_after="$(sha256_file "${path}")" || {
                echo "${name} could not be hashed after identity probe: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            }
            if [[ "$sha256_before" != "$sha256_after" ]]; then
                echo "${name} executable changed during identity probe: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            first_line="${identity%%$'\n'*}"
            if [[ -z "${STAGE2_TRUSTC_RELEASE}" \
                || "$first_line" != "trustd ${STAGE2_TRUSTC_RELEASE}" ]]; then
                echo "${name} release identity mismatch: expected trustd ${STAGE2_TRUSTC_RELEASE:-<missing-trustc-release>}, got ${first_line:-<empty>}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            if [[ "$(printf '%s\n' "${identity}" | grep -Fxc 'trust.identity=trustd' || true)" -ne 1 ]]; then
                echo "${name} identity must report exactly one trust.identity=trustd: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            if [[ "$(printf '%s\n' "${identity}" | grep -Fxc 'trust.protocol=trustd.status.v1' || true)" -ne 1 ]]; then
                echo "${name} identity must report exactly one trust.protocol=trustd.status.v1: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            commit_count="$(printf '%s\n' "${identity}" | grep -c '^commit-hash: [0-9a-f][0-9a-f]*$' || true)"
            commit="$(printf '%s\n' "${identity}" | sed -n 's/^commit-hash: //p')"
            if [[ "$commit_count" -ne 1 || ${#commit} -ne 40 || "$commit" == *[!0-9a-f]* ]]; then
                echo "${name} identity must report exactly one canonical 40-lowerhex commit-hash: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            legacy_commit_count="$(printf '%s\n' "${identity}" | grep -c '^trust-repo-commit-hash: [0-9a-f][0-9a-f]*$' || true)"
            legacy_commit="$(printf '%s\n' "${identity}" | sed -n 's/^trust-repo-commit-hash: //p')"
            if [[ "$legacy_commit_count" -ne 1 || "$legacy_commit" != "$commit" ]]; then
                echo "${name} identity must report one matching trust-repo-commit-hash: ${path}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            if [[ -z "${STAGE2_TRUSTC_COMMIT}" || "$commit" != "${STAGE2_TRUSTC_COMMIT}" ]]; then
                echo "${name} commit mismatch: expected ${STAGE2_TRUSTC_COMMIT:-<missing-trustc-commit>}, got ${commit}" \
                    | tee -a "${SUMMARY}"
                exit 1
            fi
            STAGE2_TRUSTD_SHA256="$sha256_after"
            identity="${identity}"$'\n'"sha256: ${STAGE2_TRUSTD_SHA256}"
            ;;
        *)
            echo "internal error: unknown stage2 tool identity ${name}" | tee -a "${SUMMARY}"
            exit 1
            ;;
    esac

    if [[ -z "${identity}" ]]; then
        echo "${name} identity check produced no output: ${path}" | tee -a "${SUMMARY}"
        exit 1
    fi
    identity_one_line="$(printf '%s' "${identity}" | tr '\n' ';' | sed 's/;*$//')"
    echo "$(date '+%H:%M:%S') using ${name}: ${path} (${identity_one_line})" \
        | tee -a "${SUMMARY}"
}

record_tier_status() {
    local name="$1"
    local rc="$2"

    if [[ $rc -ne 0 ]]; then
        FAILED_TIERS+=("${name}(exit=${rc})")
        OVERALL_RC=1
    fi
}

echo "$(date '+%H:%M:%S') waiting for in-flight x.py build to exit" | tee -a "${SUMMARY}"

# Wait for x.py build (any attempt) to no longer be running.
while pgrep -f "x\.py build --stage" >/dev/null 2>&1; do
    sleep 60
done

echo "$(date '+%H:%M:%S') x.py exited; requiring candidate-bound Stage2 provenance" \
    | tee -a "${SUMMARY}"

assert_exact_clean_head || exit 1
echo "$(date '+%H:%M:%S') diagnostic Git-clean candidate: ${CANDIDATE_HEAD} (local Git authority; not release proof)" | tee -a "${SUMMARY}"

# Stage2 selectors and daemon controls are derived from the completed sysroot.
# Never let an outer T3 invocation or developer shell export relocate/disable
# the post-build identity boundary, and keep these variables unexported so T4+
# receive them only when explicitly scoped below.
unset TRUSTC TARGO TARGO_TRUST TRUSTD TRUST_MEMORY_JOBSERVER_SOCK TRUSTD_DISABLE
TRUSTC=""
if ! TRUSTC="$(find_stage2_tool trustc)"; then
    TRUSTC=""
fi
[[ -n "${TRUSTC}" && -x "${TRUSTC}" ]] || {
    echo "missing stage2 trustc under ${REPO}/build/*/stage2/bin/trustc" | tee -a "${SUMMARY}"
    exit 1
}
STAGE2_BIN="$(dirname "${TRUSTC}")"
STAGE2_ROOT="$(cd "${STAGE2_BIN}/.." && pwd -P)" || exit 1
STAGE2_HOST="$(basename "$(dirname "${STAGE2_ROOT}")")"
STAGE2_PROVENANCE="${STAGE2_ROOT}/tool-provenance.json"
TARGO="${STAGE2_BIN}/targo"
TARGO_TRUST="${STAGE2_BIN}/targo-trust"
TRUSTD="${STAGE2_BIN}/trustd"
for exact_tool in "${TRUSTC}" "${TARGO}" "${TARGO_TRUST}" "${TRUSTD}"; do
    [[ -f "${exact_tool}" && ! -L "${exact_tool}" && -x "${exact_tool}" ]] || {
        echo "stage2 tool must be an exact regular executable: ${exact_tool}" | tee -a "${SUMMARY}"
        exit 1
    }
done
if [[ -L "${STAGE2_PROVENANCE}" || ! -f "${STAGE2_PROVENANCE}" ]]; then
    echo "missing exact Stage2 producer receipt: ${STAGE2_PROVENANCE}" | tee -a "${SUMMARY}"
    exit 1
fi
STAGE2_PROVENANCE_SHA256="$(sha256_file "${STAGE2_PROVENANCE}")" || exit 1
PROVENANCE_LOG="${LOGS}/tests-Tpre_stage2_provenance.log"
if ! env -i \
    PATH=/usr/bin:/bin \
    LC_ALL=C \
    LANG=C \
    TZ=UTC \
    PYTHONNOUSERSITE=1 \
    PYTHONSAFEPATH=1 \
    "${PY}" scripts/recreate_bootstrap.py \
        --verify-stage-provenance \
        --require-immutable-lineage \
        --stage 2 \
        --host "${STAGE2_HOST}" \
        >"${PROVENANCE_LOG}" 2>&1; then
    echo "Stage2 producer receipt verification failed; see ${PROVENANCE_LOG##*/}" \
        | tee -a "${SUMMARY}"
    exit 1
fi
if [[ "$(sha256_file "${STAGE2_PROVENANCE}")" != "${STAGE2_PROVENANCE_SHA256}" ]]; then
    echo "Stage2 producer receipt changed during verification: ${STAGE2_PROVENANCE}" \
        | tee -a "${SUMMARY}"
    exit 1
fi
echo "$(date '+%H:%M:%S') Stage2 producer receipt: diagnostic verifier accepted (${STAGE2_PROVENANCE_SHA256})" \
    | tee -a "${SUMMARY}"
[[ -x "${TARGO}" ]] || {
    echo "missing stage2 targo under ${STAGE2_BIN}/targo" | tee -a "${SUMMARY}"
    exit 1
}
[[ -n "${TARGO_TRUST}" && -x "${TARGO_TRUST}" ]] || {
    echo "missing stage2 targo-trust under ${STAGE2_BIN}/targo-trust" | tee -a "${SUMMARY}"
    exit 1
}
[[ -f "${TRUSTD}" && ! -L "${TRUSTD}" && -x "${TRUSTD}" ]] || {
    echo "missing exact regular stage2 trustd under ${STAGE2_BIN}/trustd" | tee -a "${SUMMARY}"
    exit 1
}
record_stage2_tool_identity TRUSTC "${TRUSTC}"
record_stage2_tool_identity TARGO "${TARGO}"
record_stage2_tool_identity TARGO_TRUST "${TARGO_TRUST}"
record_stage2_tool_identity TRUSTD "${TRUSTD}"
if [[ "${STAGE2_TRUSTC_COMMIT}" != "${CANDIDATE_HEAD}" ]]; then
    echo "stage2 trustc commit ${STAGE2_TRUSTC_COMMIT:-<missing>} does not match exact candidate HEAD ${CANDIDATE_HEAD}" \
        | tee -a "${SUMMARY}"
    exit 1
fi
STAGE2_TRUSTC_SHA256="$(sha256_file "${TRUSTC}")" || exit 1
STAGE2_TARGO_SHA256="$(sha256_file "${TARGO}")" || exit 1
STAGE2_TARGO_TRUST_SHA256="$(sha256_file "${TARGO_TRUST}")" || exit 1
CARGO_BIN="${TARGO}"

run_tier() {
    local name="$1"; shift
    local log="${LOGS}/tests-${name}.log"
    echo "$(date '+%H:%M:%S') ${name}: START — ${*}" | tee -a "${SUMMARY}"
    local t0=$SECONDS
    "$@" > "${log}" 2>&1
    local rc=$?
    local dt=$(( SECONDS - t0 ))
    if [[ $rc -eq 0 ]]; then
        echo "$(date '+%H:%M:%S') ${name}: PASS (${dt}s)" | tee -a "${SUMMARY}"
    else
        echo "$(date '+%H:%M:%S') ${name}: FAIL exit=${rc} (${dt}s); see ${log##*/}" \
            | tee -a "${SUMMARY}"
        # Surface the first 5 errorish lines to summary
        grep -nE "^error|^FAIL|^thread.*panic|^failures:" "${log}" | head -5 \
            | sed 's/^/    /' | tee -a "${SUMMARY}"
    fi
    return $rc
}

run_tier_and_record() {
    local name="$1"; shift
    local rc

    run_tier "$name" "$@"
    rc=$?
    record_tier_status "$name" "$rc"
}

# T-1: ledger expiration gate — runs first because it's the cheapest
# check and catches the class of regressions where Trust silently
# accepts upstream test failures past their reviewed expiration date.
# See CLAUDE.md → "Upstream test parity".
run_tier_and_record Tneg1_ledger \
    "${PY}" scripts/check_ledger_expirations.py --warn-days 14
run_tier_and_record Tneg1_e2e_receipts \
    "${PY}" scripts/tests/trust_e2e_receipt_test.py
run_tier_and_record Tneg1_upstream_revision \
    "${PY}" scripts/tests/upstream_revision_consistency_test.py

# T0: tidy — fastest sanity check
run_tier_and_record T0_tidy \
    "${PY}" x.py test tidy --stage 2

# T1: Trust verifier crate tests (compile with targo/trustc, fast)
run_tier_and_record T1_trust_crates \
    "${CARGO_BIN}" --unverified test --manifest-path crates/Cargo.toml \
    --locked \
    -p trust-loop -p trust-vcgen -p trust-router \
    --no-fail-fast

# T1b: Trust's own machine-checked proof corpora (trust-soundness apex proofs,
# codegen-equivalence). Kernel-checked in process at the pinned first-party/clean
# revision, so this tier's verdict does not depend on any installed `clean`
# executable — and unlike the sibling binary cross-checks, it cannot skip.
run_tier_and_record T1b_proof_corpora \
    "${CARGO_BIN}" --unverified test --manifest-path crates/Cargo.toml \
    --locked \
    -p trust-integration-tests --test lean_front_door_gate \
    --no-fail-fast

# T1c: the ny certificate bridge, which no other tier reaches. Its `ny` feature
# is off by default — nothing in the verifier calls it yet — so without an
# explicit tier its rational-clearing arithmetic (checked u128/i128, where an
# unnoticed overflow would turn a fail-closed `None` into a wrong integer
# system and a certificate about the wrong constraints) would compile in no
# build and be exercised by no gate.
run_tier_and_record T1c_ny_bridge \
    "${CARGO_BIN}" --unverified test --manifest-path crates/Cargo.toml \
    --locked \
    -p trust-ny-bridge --features ny \
    --no-fail-fast

# T2: stdlib regression
run_tier_and_record T2_libstd \
    "${PY}" x.py test --stage 2 library/std

# T3: Trust end-to-end shell scripts.
# Many e2e scripts look for `trustc` / `targo` / `targo-trust` / `trustd` on
# PATH — without prepending the stage2 sysroot they fail before
# their actual test starts. Set TRUSTC explicitly too because some
# tests check the env var instead of PATH lookup.
T3_LOG="${LOGS}/tests-T3_e2e.log"
echo "$(date '+%H:%M:%S') T3_e2e: START — Trust e2e shell scripts" | tee -a "${SUMMARY}"
T3_TOTAL=0; T3_PASS=0
T3_RC=0
{
    for sh in tests/e2e_*.sh; do
        [[ -f "$sh" ]] || continue
        T3_TOTAL=$((T3_TOTAL + 1))
        echo "::: $sh"
        if PATH="${STAGE2_BIN}:${PATH}" \
            TRUSTC="${STAGE2_BIN}/trustc" \
            TARGO="${STAGE2_BIN}/targo" \
            TARGO_TRUST="${STAGE2_BIN}/targo-trust" \
            TRUSTD="${STAGE2_BIN}/trustd" \
            bash "$sh" </dev/null; then
            echo "::: $sh PASS"
            T3_PASS=$((T3_PASS + 1))
        else
            sh_rc=$?
            echo "::: $sh FAIL (exit ${sh_rc})"
            T3_RC=1
        fi
    done
} > "${T3_LOG}" 2>&1
if [[ $T3_TOTAL -eq 0 ]]; then
    T3_RC=2
    echo "$(date '+%H:%M:%S') T3_e2e: FAIL (no tests/e2e_*.sh scripts found); see tests-T3_e2e.log" \
        | tee -a "${SUMMARY}"
elif [[ $T3_RC -eq 0 ]]; then
    echo "$(date '+%H:%M:%S') T3_e2e: PASS ${T3_PASS}/${T3_TOTAL}; see tests-T3_e2e.log" \
        | tee -a "${SUMMARY}"
else
    echo "$(date '+%H:%M:%S') T3_e2e: FAIL ${T3_PASS}/${T3_TOTAL} passed; see tests-T3_e2e.log" \
        | tee -a "${SUMMARY}"
fi
record_tier_status T3_e2e "$T3_RC"

# T3b: the three ignored real-Targo certified-monitor tests are a distinct
# release boundary. Ordinary `targo test` and the T3 shell glob do not execute
# them. The dedicated gate proves each exact ignored test actually ran once;
# it deliberately fails on non-Linux and non-x86_64/aarch64 hosts instead of
# converting the platform cfg into a successful zero-test run.
STAGE2_SYSROOT="$(cd "${STAGE2_BIN}/.." && pwd -P)"
T3B_ENV=(
    /usr/bin/env -i
    PATH=/usr/bin:/bin
    LC_ALL=C
    LANG=C
    TZ=UTC
    GIT_CONFIG_GLOBAL=/dev/null
    GIT_CONFIG_NOSYSTEM=1
    "TRUST_STAGE2_SYSROOT=${STAGE2_SYSROOT}"
)
if [[ -n "${CARGO_HOME:-}" ]]; then
    T3B_ENV+=("TRUST_CERTIFIED_MONITOR_E2E_CACHE_HOME=$CARGO_HOME")
elif [[ -n "${HOME:-}" ]]; then
    T3B_ENV+=("TRUST_CERTIFIED_MONITOR_E2E_CACHE_HOME=$HOME/.cargo")
fi
run_tier_and_record T3b_certified_monitors \
    "${T3B_ENV[@]}" \
    "${STAGE2_BIN}/targo-trust" trust release validate certified-monitors

# T4: UI regression — the big one. Hours.
run_tier_and_record T4_ui \
    "${PY}" x.py test --stage 2 tests/ui

# T5: upstream-test parity scorecard.
# The scorecard runners (`targo trust domination upstream-tests` /
# `run_upstream_rust_adopted_evidence.py`) walk every upstream Rust
# test file at the baseline SHA pinned in `tests/upstream-rust/baseline.toml`.
# That SHA only exists as a git object on a checkout that has rust-lang/rust
# fetched as the `upstream` remote. If we don't have that remote (most
# fresh checkouts), the runner crashes with `git ls-tree ... exit 128`.
# Preflight: check whether the baseline SHA is reachable. If it is not,
# fail closed: the orchestrator has not validated upstream parity.
T5_LOG="${LOGS}/tests-T5_parity.log"
echo "$(date '+%H:%M:%S') T5_parity: START — upstream-rust adopted evidence" \
    | tee -a "${SUMMARY}"
BASELINE_SHA=$(grep -m1 'revision = "rust-lang/rust:' \
    "${REPO}/tests/upstream-rust/baseline.toml" 2>/dev/null \
    | sed -E 's/.*"rust-lang\/rust:([0-9a-f]+)".*/\1/')
T5_RC=0
if [[ -z "${BASELINE_SHA}" ]] \
    || ! git_candidate_command cat-file -e "${BASELINE_SHA}^{commit}" 2>/dev/null; then
    T5_RC=2
    echo "$(date '+%H:%M:%S') T5_parity: FAIL (baseline rust-lang/rust SHA ${BASELINE_SHA:-?} not present locally)" \
        | tee -a "${SUMMARY}"
    echo "  to enable: git remote add upstream https://github.com/rust-lang/rust && git fetch upstream" \
        | tee -a "${SUMMARY}"
else
    {
        echo "::: ${TARGO} trust domination upstream-tests --release"
        TRUST_UPSTREAM_COMPAT_CARGO="${TARGO}" \
            TRUST_TARGO_BIN="${TARGO}" \
            PATH="${STAGE2_BIN}:${PATH}" \
            "${TARGO}" trust domination upstream-tests --release || T5_RC=$?
    } > "${T5_LOG}" 2>&1
    if [[ $T5_RC -eq 0 ]]; then
        echo "$(date '+%H:%M:%S') T5_parity: PASS (scorecard clean against ledger)" \
            | tee -a "${SUMMARY}"
    else
        echo "$(date '+%H:%M:%S') T5_parity: FAIL exit=${T5_RC}; unaccounted upstream failures — see tests-T5_parity.log" \
            | tee -a "${SUMMARY}"
        grep -nE "totals\.failed|validation_failures|unaccounted|regression" "${T5_LOG}" \
            | head -10 | sed 's/^/    /' | tee -a "${SUMMARY}"
    fi
fi
record_tier_status T5_parity "$T5_RC"

verify_final_candidate_closure() {
    local expected_head="$1"
    local current_hash=""
    local name=""
    local path=""
    local expected_hash=""

    assert_exact_clean_head "${expected_head}" || return 1

    while IFS='|' read -r name path expected_hash; do
        current_hash="$(sha256_file "${path}")" || {
            echo "could not re-hash final ${name}: ${path}" | tee -a "${SUMMARY}"
            return 1
        }
        if [[ "${current_hash}" != "${expected_hash}" ]]; then
            echo "final ${name} changed during the test run: ${path}" | tee -a "${SUMMARY}"
            echo "  expected sha256 ${expected_hash}" | tee -a "${SUMMARY}"
            echo "  observed sha256 ${current_hash}" | tee -a "${SUMMARY}"
            return 1
        fi
    done <<EOF
trustc|${TRUSTC}|${STAGE2_TRUSTC_SHA256}
targo|${TARGO}|${STAGE2_TARGO_SHA256}
targo-trust|${TARGO_TRUST}|${STAGE2_TARGO_TRUST_SHA256}
trustd|${TRUSTD}|${STAGE2_TRUSTD_SHA256}
tool-provenance.json|${STAGE2_PROVENANCE}|${STAGE2_PROVENANCE_SHA256}
EOF

    echo "diagnostic final consistency matches candidate ${expected_head}, the producer receipt, and all four captured Stage 2 tool hashes; local Git authority is not release proof"
}

FINAL_CANDIDATE_HEAD="${CANDIDATE_HEAD}"
run_tier_and_record Tfinal_candidate_closure \
    verify_final_candidate_closure "${FINAL_CANDIDATE_HEAD}"

if [[ $OVERALL_RC -eq 0 ]]; then
    echo "$(date '+%H:%M:%S') ALL TIERS COMPLETE: PASS (DIAGNOSTIC ONLY; NOT RELEASE EVIDENCE) — see ${SUMMARY##*/}" | tee -a "${SUMMARY}"
else
    printf -v FAILED_TIER_LIST '%s, ' "${FAILED_TIERS[@]}"
    FAILED_TIER_LIST="${FAILED_TIER_LIST%, }"
    echo "$(date '+%H:%M:%S') ALL TIERS COMPLETE: FAIL (${FAILED_TIER_LIST}) — see ${SUMMARY##*/}" \
        | tee -a "${SUMMARY}"
fi
exit "$OVERALL_RC"
