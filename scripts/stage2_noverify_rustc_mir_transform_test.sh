#!/usr/bin/env bash
# Run the focused Trust MIR-transform native trust_ir unit test as a
# no-verification control. This only proves the compiler-side unit test can run
# without stale bootstrap wrappers turning dependency rebuilds into broad Trust
# verification. Pair this with separate verification-on evidence; do not treat a
# pass here as proof that the verifier stack discharged obligations.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
TRUST_TOOLCHAIN_PYTHON3="${PYTHON3:-python3}"
. "$SCRIPT_DIR/lib/trust_toolchain_surface.sh"
cd "$TRUST_ROOT"

DEFAULT_TEST_ARGS="trust_verify::tests::full_verification_compiler_input_defers_direct_trust_vc_proof_unit --exact --nocapture"
TEST_ARGS="${TRUST_STAGE2_MIR_TRANSFORM_TEST_ARGS:-$DEFAULT_TEST_ARGS}"
JOBS="${TRUST_STAGE2_MIR_TRANSFORM_TEST_JOBS:-${TRUST_JOBS:-}}"
DRY_RUN="${TRUST_STAGE2_MIR_TRANSFORM_TEST_DRY_RUN:-0}"
ALLOW_STALE_STAGE2="${TRUST_STAGE2_MIR_TRANSFORM_TEST_ALLOW_STALE_STAGE2:-0}"
ALLOW_BOOTSTRAP_PLAN="${TRUST_STAGE2_MIR_TRANSFORM_TEST_ALLOW_BOOTSTRAP_PLAN:-0}"
PLAN_LOG="${TRUST_STAGE2_MIR_TRANSFORM_TEST_PLAN_LOG:-}"

# Keep this focused test independent of caller-local cargo/trustc wrappers.
# This mirrors scripts/stage2_noverify_self_build.sh, where stale wrapper state
# can route bootstrap through an upstream or verification-on compiler shim.
BOOTSTRAP_WRAPPER_ENV_UNSET=(
    "RUSTC_WRAPPER"
    "RUSTC_WORKSPACE_WRAPPER"
    "RUSTC_WRAPPER_REAL"
    "CARGO_BUILD_RUSTC_WRAPPER"
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
)
STAGE2_REQUIRED_TOOLS=(
    "trustc"
    "targo"
    "targo-trust"
    "trustd"
    "trustdoc"
    "trustfmt"
    "targo-fmt"
    "tippy"
    "targo-tippy"
    "tippy-driver"
    "trust-analyzer"
)

append_shell_word() {
    local current="$1"
    local word="$2"

    if [[ -z "$current" ]]; then
        printf '%s\n' "$word"
    elif [[ " $current " == *" $word "* ]]; then
        printf '%s\n' "$current"
    else
        printf '%s %s\n' "$current" "$word"
    fi
}

format_command() {
    local out=""
    local arg

    for arg in "$@"; do
        if [[ -n "$out" ]]; then
            out+=" "
        fi
        printf -v out "%s%q" "$out" "$arg"
    done
    printf '%s\n' "$out"
}

fail() {
    echo "error: $*" >&2
    exit 1
}

stage2_sysroot_candidates() {
    shopt -s nullglob
    local candidates=("$TRUST_ROOT/build/host/stage2")
    local candidate
    local seen=" "

    for candidate in "$TRUST_ROOT"/build/*/stage2; do
        candidates+=("$candidate")
    done
    shopt -u nullglob

    for candidate in "${candidates[@]}"; do
        [[ -n "$candidate" ]] || continue
        if [[ " $seen " == *" $candidate "* ]]; then
            continue
        fi
        seen+="$candidate "
        printf '%s\n' "$candidate"
    done
}

find_stage2_sysroot() {
    local candidate
    local resolved
    local tool
    local missing

    while IFS= read -r candidate; do
        missing=0
        if ! resolved="$(
            trust_toolchain_resolve_repo_stage2 "$TRUST_ROOT" "$candidate"
        )"; then
            continue
        fi
        trust_toolchain_exact_executables_valid \
            "$resolved/bin" "${STAGE2_REQUIRED_TOOLS[@]}" || missing=1
        if [[ "$missing" -eq 0 ]]; then
            printf '%s\n' "$resolved"
            return 0
        fi
    done < <(stage2_sysroot_candidates)

    return 1
}

version_commit_hash() {
    awk -F': ' '/^commit-hash:/{print $2; exit}'
}

preflight_current_head_stage2() {
    local repo_head
    local stage2_sysroot
    local tool
    local path
    local version_output
    local commit_hash
    local status=0

    repo_head="$(git rev-parse HEAD)"
    stage2_sysroot="$(find_stage2_sysroot)" \
        || fail "repo-local stage2 sysroot with the complete canonical Trust tool surface not found under build/*/stage2; rebuild stage2 before this focused test"

    echo "stage2 sysroot: $stage2_sysroot" >&2
    echo "repo HEAD: $repo_head" >&2

    for tool in "${STAGE2_REQUIRED_TOOLS[@]}"; do
        path="$stage2_sysroot/bin/$tool"
        if ! trust_toolchain_exact_executables_valid "$stage2_sysroot/bin" "$tool"; then
            echo "missing or non-exact required stage2 $tool: $path" >&2
            status=1
            continue
        fi

        if [[ "$tool" == "trustc" || "$tool" == "targo" ]]; then
            version_output="$("$path" -Vv 2>&1)" || {
                printf '%s\n' "$version_output" >&2
                echo "stage2 $tool -Vv failed: $path" >&2
                status=1
                continue
            }
        else
            version_output="$("$path" --version 2>&1)" || {
                printf '%s\n' "$version_output" >&2
                echo "stage2 $tool --version failed: $path" >&2
                status=1
                continue
            }
        fi

        if [[ "$tool" != "trustc" ]]; then
            echo "stage2 $tool version: ${version_output%%$'\n'*}" >&2
            continue
        fi

        commit_hash="$(printf '%s\n' "$version_output" | version_commit_hash)"
        echo "stage2 $tool commit-hash: ${commit_hash:-<missing>}" >&2
        if [[ -z "$commit_hash" ]]; then
            echo "stage2 $tool version output lacks commit-hash: $path" >&2
            status=1
        elif [[ "$commit_hash" != "$repo_head" ]]; then
            echo "stage2 $tool commit-hash does not match repo HEAD: $commit_hash != $repo_head" >&2
            status=1
        fi
    done

    if [[ "$status" -ne 0 && "$ALLOW_STALE_STAGE2" != "1" ]]; then
        fail "stale or incomplete stage2 toolchain; set TRUST_STAGE2_MIR_TRANSFORM_TEST_ALLOW_STALE_STAGE2=1 only for an explicit mismatch investigation"
    fi
    if [[ "$status" -ne 0 ]]; then
        echo "warning: continuing with stale/incomplete stage2 because TRUST_STAGE2_MIR_TRANSFORM_TEST_ALLOW_STALE_STAGE2=1" >&2
    fi
}

preflight_focused_reachability() {
    local plan_output
    local plan_status
    local broad_steps

    echo "checking focused x.py dry-run plan before live execution" >&2
    echo "dry-run: $(format_command "${plan_command[@]}")" >&2

    set +e
    plan_output="$("${plan_command[@]}" 2>&1)"
    plan_status=$?
    set -e

    if [[ -n "$PLAN_LOG" ]]; then
        mkdir -p "$(dirname "$PLAN_LOG")"
        {
            echo "command=$(format_command "${plan_command[@]}")"
            echo "exit_code=$plan_status"
            echo
            printf '%s\n' "$plan_output"
        } >"$PLAN_LOG"
        echo "dry-run plan log: $PLAN_LOG" >&2
    fi

    if [[ "$plan_status" -ne 0 ]]; then
        printf '%s\n' "$plan_output" >&2
        fail "x.py focused dry-run failed; refusing live test"
    fi

    if ! printf '%s\n' "$plan_output" | grep -q 'Testing stage2 {rustc_mir_transform}'; then
        printf '%s\n' "$plan_output" >&2
        fail "x.py dry-run did not reach Testing stage2 {rustc_mir_transform}; refusing live test"
    fi

    broad_steps="$(
        printf '%s\n' "$plan_output" |
            awk '
                /Testing stage2 \{rustc_mir_transform\}/ { exit }
                /^(Building stage1 |Building LLVM|Creating a sysroot for stage1|Building stage2 (cargo|targo-trust|compiler|library|rustdoc))/ { print }
            '
    )"
    if [[ -n "$broad_steps" && "$ALLOW_BOOTSTRAP_PLAN" != "1" ]]; then
        printf '%s\n' "$broad_steps" >&2
        fail "focused test is not currently reachable without broad bootstrap work; set TRUST_STAGE2_MIR_TRANSFORM_TEST_ALLOW_BOOTSTRAP_PLAN=1 only for an explicit rebuilding run"
    fi
    if [[ -n "$broad_steps" ]]; then
        echo "warning: continuing despite broad dry-run plan because TRUST_STAGE2_MIR_TRANSFORM_TEST_ALLOW_BOOTSTRAP_PLAN=1" >&2
    fi
}

wrapper_env_unsets=()
for wrapper_env in "${BOOTSTRAP_WRAPPER_ENV_UNSET[@]}"; do
    wrapper_env_unsets+=("-u" "$wrapper_env")
done

noverify_rustflags_bootstrap="$(append_shell_word "${RUSTFLAGS_BOOTSTRAP:-}" "-Ztrust-verify=off")"
noverify_rustflags_not_bootstrap="$(append_shell_word "${RUSTFLAGS_NOT_BOOTSTRAP:-}" "-Ztrust-verify=off")"
noverify_magic_rustflags="$(append_shell_word "${MAGIC_EXTRA_RUSTFLAGS:-}" "-Ztrust-verify=off")"

command=(
    env
    "${wrapper_env_unsets[@]}"
    "RUSTFLAGS_BOOTSTRAP=$noverify_rustflags_bootstrap"
    "RUSTFLAGS_NOT_BOOTSTRAP=$noverify_rustflags_not_bootstrap"
    "MAGIC_EXTRA_RUSTFLAGS=$noverify_magic_rustflags"
    ./x.py test
    --stage 2
)

if [[ -n "$JOBS" ]]; then
    command+=(-j "$JOBS")
fi

command+=(
    compiler/rustc_mir_transform
    --test-args "$TEST_ARGS"
)

command_target_offset=$((${#command[@]} - 3))
plan_command=("${command[@]:0:$command_target_offset}" --dry-run "${command[@]:$command_target_offset}")

if [[ "$DRY_RUN" == "1" ]]; then
    format_command "${command[@]}"
    exit 0
fi

preflight_current_head_stage2
preflight_focused_reachability

echo "note: no-verification control only; pair with verification-on stage2 evidence" >&2
echo "running: $(format_command "${command[@]}")" >&2
run_log="$(mktemp "${TMPDIR:-/tmp}/trust-stage2-mir-transform.XXXXXX")"
trap 'rm -f "$run_log"' EXIT

set +e
"${command[@]}" 2>&1 | tee "$run_log"
command_status=${PIPESTATUS[0]}
set -e

if [[ "$command_status" -ne 0 ]]; then
    exit "$command_status"
fi
if ! grep -Eq 'running [1-9][0-9]* tests?' "$run_log"; then
    fail "focused stage2 invocation completed without running a test"
fi
