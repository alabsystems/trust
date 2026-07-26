#!/bin/bash
# Print a concise release-gate readiness matrix for the trust gates.
#
# This helper reports the release inventory fail-closed. It runs unrelated
# runnable gates, but records every canonical trust-added ID as blocked without
# executing a weaker shell diagnostic.
#
# Environment:
#   TRUST_GATE_STATUS_LOG_DIR=PATH  Preserve per-gate logs in this directory.

set -euo pipefail
umask 077

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ROBUST_SUITE="$SCRIPT_DIR/run_trust_robust_suite.sh"
SUPERSET_SUITE="$SCRIPT_DIR/run_trust_superset_suite.sh"
LOG_DIR="${TRUST_GATE_STATUS_LOG_DIR:-}"
if [ -n "$LOG_DIR" ]; then
    mkdir -p "$LOG_DIR"
else
    LOG_DIR="$(/usr/bin/mktemp -d /tmp/trust-gate-status.XXXXXX)" || {
        echo "ERROR: could not create a private fixed-root gate-status log directory" >&2
        exit 2
    }
fi
TAIL_LINES="${TRUST_GATE_STATUS_TAIL_LINES:-20}"
ALLOW_REVIEW_GATE_SKIPS="${TRUST_ALLOW_REVIEW_GATE_SKIPS:-0}"

CORE_GATES=(
    trust-compat
    upstream-rust-porting
    quick
    trust-added-compiletest
    trustc-native
    native-contracts-pipeline-v2
    trust-extra
    public-distribution
    launch
    prepublish
    installed
    installed-default
    stage0-lineage
    binary-decompilation-golden
)
LEGACY_COMPAT_GATES=(
    upstream-rust-compat
)
EVIDENCE_CLASSES=(
    "no-verification compatibility|trust-compat,launch|Stage2 no-verification compatibility and linked/local launch smoke; no proof claim."
    "strict Tier-0 proof|trust-extra|Strict verifier corpus evidence with proof-grade rows; runtime_checked, unknown, and no-verification rows do not satisfy this claim."
    "native proof engines|native-contracts-pipeline-v2|Native TrustIr/trust-mc/trust-wp/trust-vc evidence must be same-row proof evidence, not text-only transport markers."
    "hardened proof|-|Hardened model-backed proof is unclaimed until model assumptions and proof-backed hardened rows are present; inventory-only findings do not satisfy this claim."
    "trust-codegen|trust-extra|trust-codegen requires enforce-mode parity and translation-validation evidence, not report-mode exceptions."
    "dependency integrity|public-distribution|Owned dependency release readiness, public source, checksums, and distribution-root integrity evidence."
    "upstream compatibility|upstream-rust-porting|Rust-vs-Trust upstream adoption scorecard and porting evidence; legacy compatibility accounting is not release evidence."
    "distribution install|public-distribution,prepublish,installed,installed-default,stage0-lineage|Public distribution roots, prepublish artifacts, installed/default toolchain, and stage0 lineage evidence."
    "self-build|-|Verification-enabled self-build is unclaimed until L29 supplies bounded scope, budgets, retained proof rows, and same-commit reproduction evidence."
)
GATES=("${CORE_GATES[@]}")
if [ "${TRUST_GATE_STATUS_INCLUDE_LEGACY_COMPAT:-0}" = "1" ]; then
    GATES+=("${LEGACY_COMPAT_GATES[@]}")
fi

gate_names=()
gate_statuses=()
gate_codes=()
gate_logs=()

status_for_code() {
    local code="$1"
    case "$code" in
        0) printf 'PASS' ;;
        2) printf 'SETUP/BLOCKED' ;;
        *) printf 'FAIL' ;;
    esac
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

mode_supported() {
    local suite="$1"
    local mode="$2"
    [ -f "$suite" ] || return 1
    awk -v mode="$mode" '$1 == mode ")" { found = 1 } END { exit found ? 0 : 1 }' "$suite"
}

suite_for_gate() {
    local mode="$1"
    case "$mode" in
        trust-compat|upstream-rust-porting|upstream-rust-compat|trustc-native|native-contracts-pipeline-v2|trust-extra|binary-decompilation-golden) printf '%s\n' "$SUPERSET_SUITE" ;;
        *) printf '%s\n' "$ROBUST_SUITE" ;;
    esac
}

canonical_trust_added_release_mode() {
    case "$1" in
        quick|trust-added-compiletest|trustc-native|native-contracts-pipeline-v2|trust-extra|binary-decompilation-golden|launch|public-distribution|prepublish|installed|installed-default|stage0-lineage)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

gate_code_for_name() {
    local name="$1"
    local idx

    for idx in "${!gate_names[@]}"; do
        if [ "${gate_names[$idx]}" = "$name" ]; then
            printf '%s\n' "${gate_codes[$idx]}"
            return 0
        fi
    done

    return 1
}

class_status_for_gates() {
    local gates_csv="$1"
    local gate code
    local saw_missing=0
    local saw_blocked=0

    if [ "$gates_csv" = "-" ]; then
        printf 'NOT CLAIMED'
        return
    fi

    IFS=',' read -r -a class_gates <<<"$gates_csv"
    for gate in "${class_gates[@]}"; do
        if ! code="$(gate_code_for_name "$gate")"; then
            saw_missing=1
            continue
        fi

        case "$code" in
            0) ;;
            2) saw_blocked=1 ;;
            *)
                printf 'FAIL'
                return
                ;;
        esac
    done

    if [ "$saw_blocked" -eq 1 ]; then
        printf 'SETUP/BLOCKED'
    elif [ "$saw_missing" -eq 1 ]; then
        printf 'NOT RUN'
    else
        printf 'PASS'
    fi
}

format_gate_list() {
    local gates_csv="$1"

    if [ "$gates_csv" = "-" ]; then
        printf 'no dedicated gate'
        return
    fi

    printf '%s' "${gates_csv//,/ }"
}

record_gate() {
    local name="$1"
    local code="$2"
    local log="$3"

    gate_names+=("$name")
    gate_codes+=("$code")
    gate_statuses+=("$(status_for_code "$code")")
    gate_logs+=("$log")
}

run_gate() {
    local gate="$1"
    local suite
    local log="$LOG_DIR/$gate.log"
    local code
    local -a gate_env=()
    suite="$(suite_for_gate "$gate")"

    # These names are canonical trust-added release inventory IDs. The legacy
    # shell suites expose only weaker local diagnostics, so never execute them
    # here or promote a zero exit to release readiness.
    if canonical_trust_added_release_mode "$gate"; then
        {
            echo "SETUP/BLOCKED: canonical trust-added release mode '$gate' has no authenticated native execution authority."
            echo "Canonical command: targo trust domination trust-added --release $gate"
            echo "Direct shell diagnostics are intentionally not run by this release-status report."
        } >"$log"
        record_gate "$gate" 2 "$log"
        return
    fi

    if [ ! -f "$suite" ]; then
        {
            echo "ERROR: gate suite not found: $suite"
            echo "Expected gate suite to provide mode '$gate'."
        } >"$log"
        record_gate "$gate" 2 "$log"
        return
    fi

    if ! mode_supported "$suite" "$gate"; then
        {
            echo "ERROR: robust suite mode is missing: $gate"
            echo "Expected $suite to support '$gate'."
        } >"$log"
        record_gate "$gate" 2 "$log"
        return
    fi

    set +e
    case "$gate" in
        binary-decompilation-golden)
            gate_env=(TRUST_STRICT=1 TRUST_RELEASE_GATE=1 TRUST_PUBLIC_PROOF_GRADE_CLAIM=1)
            ;;
        trust-compat|upstream-rust-porting|upstream-rust-compat|trustc-native|trust-extra)
            gate_env=(TRUST_STRICT=1 TRUST_RELEASE_GATE=1)
            ;;
        native-contracts-pipeline-v2)
            gate_env=(TRUST_STRICT=1 TRUST_RELEASE_GATE=1)
            ;;
    esac
    (
        cd "$TRUST_ROOT"
        if [ "${#gate_env[@]}" -gt 0 ]; then
            env RUSTUP_SELF_UPDATE=disable "${gate_env[@]}" bash "$suite" "$gate"
        else
            env RUSTUP_SELF_UPDATE=disable bash "$suite" "$gate"
        fi
    ) >"$log" 2>&1
    code=$?
    set -e

    if [ "$code" -eq 0 ] && [ "$ALLOW_REVIEW_GATE_SKIPS" != "1" ] && log_has_unexpected_skip "$log"; then
        {
            echo
            echo "ERROR: release evidence gate emitted an unexpected SKIP line."
            echo "Set TRUST_ALLOW_REVIEW_GATE_SKIPS=1 only for local development, not review/release evidence."
        } >>"$log"
        code=2
    fi

    record_gate "$gate" "$code" "$log"
}

print_summary() {
    local idx
    local class name gates evidence status

    echo "=== tRust release inventory status (fail-closed) ==="
    echo "Logs: $LOG_DIR"
    echo
    printf '%-16s %-14s %-6s %s\n' "Gate" "Status" "Exit" "Log"
    printf '%-16s %-14s %-6s %s\n' "----" "------" "----" "---"

    for idx in "${!gate_names[@]}"; do
        printf '%-16s %-14s %-6s %s\n' \
            "${gate_names[$idx]}" \
            "${gate_statuses[$idx]}" \
            "${gate_codes[$idx]}" \
            "${gate_logs[$idx]}"
    done

    echo
    echo "Evidence claim classes:"
    printf '%-33s %-14s %-58s %s\n' "Class" "Status" "Gate(s)" "Required evidence"
    printf '%-33s %-14s %-58s %s\n' "-----" "------" "-------" "-----------------"
    for class in "${EVIDENCE_CLASSES[@]}"; do
        IFS='|' read -r name gates evidence <<<"$class"
        status="$(class_status_for_gates "$gates")"
        printf '%-33s %-14s %-58s %s\n' \
            "$name" \
            "$status" \
            "$(format_gate_list "$gates")" \
            "$evidence"
    done

    echo
    echo "Upstream Rust porting:"
    echo "  canonical release evidence: targo trust domination upstream-tests"
    echo "  upstream-rust-porting is a local wrapper that delegates to that command"
    echo "  legacy upstream-rust-compat is internal compatibility/accounting status only"
    echo "  set TRUST_GATE_STATUS_INCLUDE_LEGACY_COMPAT=1 to include that legacy status"
    echo
    echo "Native contracts Pipeline v2 status:"
    echo "  native-contracts-pipeline-v2 remains blocked as canonical release evidence"
    echo "  its direct shell/Rust-native runners are local diagnostics only"
    echo "  Formula compatibility is compatibility evidence only, not native proof evidence"
    echo "  missing native contract transport/corpus/owner-matrix evidence is reported fail-closed"
    echo
    echo "Binary decompilation golden coverage:"
    echo "  exact-byte replay targo-trust unit gates"
    echo "  checked binary certificate gates, including manifest import visibility or manifest rejection without proof-grade acceptance"
    echo "  public proof-grade positive rows require real targo_trust_release_export origin, exact schema/type/status, explicit accepted/null semantics, current candidate commit, binary digest, selected-image identity, complete VC and checked-certificate readback digest inventories, replay transcript digests, provenance artifact digests, empty unsupported ledgers, target proof-consumer artifact digests, exact source/type ownership evidence, empty blockers, and release transcript binding digest matching the trust.proof-grade-row-binding.v1 producer row profile"
    echo "  decompile JSON for Rust/TrustIr and convert JSON for trust-codegen/Wasm target, provenance, and backprop blockers"
    echo "  missing-target-semantic-validation blockers for trust-codegen/Wasm target consumers"
    echo "  symbolic formula preservation and proof-semantics blockers through TrustIr/trust-codegen/Wasm"
    echo "  fail-closed unsupported binary targets for PE/COFF and ELF i386"
    echo "  repo-owned AArch64 fixture and unsupported-ledger smoke without local cross assembly"
}

print_failure_tails() {
    local idx

    for idx in "${!gate_names[@]}"; do
        if [ "${gate_codes[$idx]}" -eq 0 ]; then
            continue
        fi

        echo
        echo "--- ${gate_names[$idx]} ${gate_statuses[$idx]} tail (${gate_logs[$idx]}) ---"
        tail -n "$TAIL_LINES" "${gate_logs[$idx]}" || true
    done
}

summary_exit_code() {
    local idx
    local saw_blocked=0

    for idx in "${!gate_codes[@]}"; do
        case "${gate_codes[$idx]}" in
            0) ;;
            2) saw_blocked=1 ;;
            *) return 1 ;;
        esac
    done

    if [ "$saw_blocked" -eq 1 ]; then
        return 2
    fi

    return 0
}

for gate in "${GATES[@]}"; do
    run_gate "$gate"
done

print_summary
print_failure_tails
summary_exit_code
