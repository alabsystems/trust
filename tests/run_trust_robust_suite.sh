#!/bin/bash
# Robust test runner for tRust.
#
# Separates:
#   - baseline Rust parity
#   - the supported linked-toolchain + `targo trust check` public contract
#   - explicitly named installed/pre-publish/distribution/lineage diagnostics
#   - fail-closed canonical release inventory entrypoints
#   - the deeper native compiler transport gate
#
# A green smoke/full run should make it obvious whether a failure is in the
# linked toolchain, the public CLI, or the raw compiler integration.
# The `launch` mode is the current linked/local approximation of the eventual
# fresh-machine switch gate; it is not a packaged install/dist claim.

set -euo pipefail
umask 077

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MODE="${1:-smoke}"
ALLOW_REVIEW_GATE_SKIPS="${TRUST_ALLOW_REVIEW_GATE_SKIPS:-0}"

release_like_mode() {
    case "$MODE" in
        launch|installed|installed-default|public-distribution|prepublish|stage0-lineage)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

require_release_like_fail_closed_env() {
    if release_like_mode && [ "$ALLOW_REVIEW_GATE_SKIPS" = "1" ]; then
        echo "ERROR: canonical mode $MODE is fail-closed; review-skip overrides are not accepted." >&2
        exit 2
    fi
}

block_canonical_release_mode() {
    local mode="$1"
    local diagnostic="${2:-}"

    echo "SETUP/BLOCKED: canonical trust-added mode '$mode' cannot run through the legacy shell harness." >&2
    echo "Canonical command: targo trust domination trust-added --release $mode" >&2
    echo "That command currently fails closed until independently authenticated native execution exists." >&2
    if [ -n "$diagnostic" ]; then
        echo "For non-authoritative local troubleshooting only: $0 $diagnostic" >&2
    fi
}

local_diagnostic_mode() {
    case "$MODE" in
        launch-diagnostic|installed-diagnostic|installed-default-diagnostic|public-distribution-diagnostic|prepublish-diagnostic|stage0-lineage-diagnostic)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

strict_skip_handling_enabled() {
    release_like_mode
}

log_has_unexpected_skip() {
    local log="$1"
    python3 - "$log" <<'PY'
import re
import sys

text = open(sys.argv[1], encoding="utf-8", errors="replace").read()
text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", text)
raise SystemExit(0 if re.search(r"(^|[\s(])SKIP(?:PING|PED)?\s*:", text, re.MULTILINE) else 1)
PY
}

run() {
    local log status

    echo
    echo ">>> $*"
    if ! strict_skip_handling_enabled; then
        "$@"
        return
    fi

    log="$(/usr/bin/mktemp /tmp/trust-robust.XXXXXX)" || {
        echo "ERROR: could not create a private fixed-root robust-suite log" >&2
        return 2
    }
    set +e
    "$@" 2>&1 | tee "$log"
    status=${PIPESTATUS[0]}
    set -e

    if [ "$status" -ne 0 ]; then
        /bin/rm -f "$log"
        return "$status"
    fi

    if log_has_unexpected_skip "$log"; then
        echo "ERROR: robust replacement gate saw an unexpected SKIP in: $*" >&2
        echo "Release-like robust modes fail closed on skipped subchecks; use smoke for local development." >&2
        /bin/rm -f "$log"
        return 2
    fi

    /bin/rm -f "$log"
}

section() {
    echo
    echo "--- $1"
}

require_script() {
    local script="$1"
    if [ ! -f "$script" ]; then
        echo "ERROR: required evidence script is missing: $script" >&2
        echo "Restore or replace this gate before using $MODE as Trust replacement evidence." >&2
        exit 2
    fi
}

require_release_like_fail_closed_env

run_launch_gate() {
    section "Supported launch gate: linked trust toolchain"
    run bash "$TRUST_ROOT/tests/e2e_trust_toolchain.sh"
    section "Supported launch gate: targo trust public CLI"
    run bash "$TRUST_ROOT/tests/e2e_targo_trust_cli.sh"
    section "Supported launch gate: targo trust root resolution"
    run bash "$TRUST_ROOT/tests/e2e_targo_trust_root_resolution.sh"
    section "Explicit native compiler transport gate"
    run bash "$TRUST_ROOT/tests/e2e_compiler_verify.sh"
}

echo "=== tRust Robust Test Suite ($MODE) ==="

case "$MODE" in
    smoke)
        section "Baseline parity"
        run bash "$TRUST_ROOT/tests/e2e_semantic_parity.sh"
        run_launch_gate
        ;;
    quick|trust-added-compiletest|trustc-native|native-contracts-pipeline-v2|binary-decompilation-golden|trust-extra)
        block_canonical_release_mode "$MODE"
        exit 2
        ;;
    launch|installed|installed-default|public-distribution|prepublish|stage0-lineage)
        case "$MODE" in
            launch) diagnostic="launch-diagnostic" ;;
            installed) diagnostic="installed-diagnostic" ;;
            installed-default) diagnostic="installed-default-diagnostic" ;;
            public-distribution) diagnostic="public-distribution-diagnostic" ;;
            prepublish) diagnostic="prepublish-diagnostic" ;;
            stage0-lineage) diagnostic="stage0-lineage-diagnostic" ;;
        esac
        block_canonical_release_mode "$MODE" "$diagnostic"
        exit 2
        ;;
    launch-diagnostic)
        section "Current linked/local launch approximation"
        run_launch_gate
        ;;
    installed-diagnostic)
        section "Installed-toolchain local diagnostic"
        run bash "$TRUST_ROOT/tests/e2e_trust_installed_toolchain.sh"
        ;;
    installed-default-diagnostic)
        section "Installed default/no-flags local diagnostic"
        run bash "$TRUST_ROOT/tests/e2e_trust_installed_toolchain.sh" --set-default
        ;;
    public-distribution-diagnostic)
        section "Public distribution root local diagnostic"
        run bash "$TRUST_ROOT/tests/e2e_public_distribution_roots.sh"
        section "Owned internal repo public-version gate"
        run env TRUST_REQUIRE_RELEASED_INTERNAL_REPOS=1 bash "$TRUST_ROOT/tests/e2e_internal_repo_public_versions.sh"
        section "Owned public dependency source gate"
        run python3 "$TRUST_ROOT/tests/test_owned_dependency_sources.py"
        ;;
    prepublish-diagnostic)
        section "Pre-publish local rehearsal"
        section "Public distribution root diagnostic"
        run bash "$TRUST_ROOT/tests/e2e_public_distribution_roots.sh"
        section "Pre-publish dist artifact rehearsal"
        require_script "$TRUST_ROOT/tests/e2e_trust_dist_artifacts.sh"
        run bash "$TRUST_ROOT/tests/e2e_trust_dist_artifacts.sh"
        section "Pre-publish local rustup install rehearsal"
        run bash "$TRUST_ROOT/tests/e2e_trust_local_rustup_install.sh"
        ;;
    stage0-lineage-diagnostic)
        section "Bootstrap stage0 lineage local diagnostic"
        run bash "$TRUST_ROOT/tests/e2e_trust_stage0_lineage.sh"
        ;;
    parity)
        section "Baseline parity"
        run bash "$TRUST_ROOT/tests/e2e_semantic_parity.sh"
        run ./x.py test --stage 2 tests/ui tests/run-make tests/mir-opt tests/codegen tests/codegen-units tests/incremental tests/ui-fulldeps tests/rustdoc-ui
        ;;
    full)
        section "Baseline parity"
        run bash "$TRUST_ROOT/tests/e2e_semantic_parity.sh"
        run ./x.py test --stage 2 tests/ui tests/run-make tests/mir-opt tests/codegen tests/codegen-units tests/incremental tests/ui-fulldeps tests/rustdoc-ui
        run_launch_gate
        section "Verifier-example regression diagnostic (not proof or release evidence)"
        run bash "$TRUST_ROOT/tests/e2e_verify_suite.sh"
        ;;
    *)
        echo "Usage: $0 [smoke|launch|installed|installed-default|public-distribution|prepublish|stage0-lineage|launch-diagnostic|installed-diagnostic|installed-default-diagnostic|public-distribution-diagnostic|prepublish-diagnostic|stage0-lineage-diagnostic|parity|full]"
        exit 2
        ;;
esac

echo
if local_diagnostic_mode; then
    echo "=== tRust Robust Test Suite ($MODE): LOCAL DIAGNOSTIC PASS (non-authoritative) ==="
else
    echo "=== tRust Robust Test Suite ($MODE): PASS ==="
fi
