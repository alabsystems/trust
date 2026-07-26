#!/bin/bash
# End-to-end regression test for the post-build test orchestrator's
# fail-closed preflights. These fixtures use a tiny temporary repo so the
# checks do not require a real stage2 build.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
SOURCE_SCRIPT="${TRUST_ROOT}/scripts/run_tests_after_build.sh"

fail_test() {
    echo "FAIL: $1"
    exit 1
}

write_exe() {
    local path="$1"
    local body="$2"

    mkdir -p "$(dirname "$path")"
    printf '%s\n' "$body" >"$path"
    chmod +x "$path"
}

write_common_repo() {
    local repo="$1"

    mkdir -p \
        "$repo/scripts" \
        "$repo/build-logs" \
        "$repo/build/host/stage2/bin" \
        "$repo/tests/upstream-rust"
    cp "$SOURCE_SCRIPT" "$repo/scripts/run_tests_after_build.sh"
    chmod +x "$repo/scripts/run_tests_after_build.sh"
    printf '/build-logs/\n/output.log\n' >"$repo/.gitignore"
    printf '{"schema":"fixture-stage2-producer-receipt"}\n' \
        >"$repo/build/host/stage2/tool-provenance.json"
}

write_fake_pgrep() {
    local bin_dir="$1"

    write_exe "$bin_dir/pgrep" '#!/bin/sh
exit 1'
}

write_fake_python() {
    local bin_dir="$1"

    write_exe "$bin_dir/python3.11" '#!/bin/sh
if [ "${1:-}" = "-" ]; then
    cat >/dev/null
    echo "$0 3.11.0"
    exit 0
fi
exit 0'
}

write_fake_python_provenance_failure() {
    local bin_dir="$1"

    write_exe "$bin_dir/python3.11" '#!/bin/sh
if [ "${1:-}" = "-" ]; then
    cat >/dev/null
    echo "$0 3.11.0"
    exit 0
fi
case "${1:-}" in
    scripts/recreate_bootstrap.py|*/scripts/recreate_bootstrap.py) exit 43 ;;
esac
exit 0'
}

write_fake_python_t4_env_guard() {
    local bin_dir="$1"
    local stage2_bin="$2"
    local marker="$3"

    write_exe "$bin_dir/python3.11" "#!/bin/sh
if [ \"\${1:-}\" = \"-\" ]; then
    cat >/dev/null
    echo \"\$0 3.11.0\"
    exit 0
fi
if [ \"\${1:-}\" = \"x.py\" ] \
    && [ \"\${2:-}\" = \"test\" ] \
    && [ \"\${3:-}\" = \"--stage\" ] \
    && [ \"\${4:-}\" = \"2\" ] \
    && [ \"\${5:-}\" = \"tests/ui\" ]; then
    if [ -n \"\${TRUSTC:-}\" ] \
        || [ -n \"\${TARGO:-}\" ] \
        || [ -n \"\${TARGO_TRUST:-}\" ] \
        || [ -n \"\${TRUSTD:-}\" ] \
        || [ -n \"\${TRUST_MEMORY_JOBSERVER_SOCK:-}\" ] \
        || [ -n \"\${TRUSTD_DISABLE:-}\" ]; then
        touch '$marker'
    fi
    case \":\${PATH:-}:\" in
        *\":$stage2_bin:\"*) touch '$marker' ;;
    esac
fi
exit 0"
}

write_fake_cargo() {
    local bin_dir="$1"

    # The orchestrator's CARGO identity gate accepts only a targo-versioned
    # executable; a stock `cargo ...` identity is rejected before any tier runs.
    write_exe "$bin_dir/cargo" '#!/bin/sh
if [ "${1:-}" = "--version" ]; then
    echo "targo 0.1.0 (trust-test)"
    exit 0
fi
exit 0'
}

write_fake_stage2_tool() {
    local path="$1"
    local name="$2"
    local sysroot
    local repo

    mkdir -p "$(dirname "$path")"
    sysroot="$(cd "$(dirname "$path")/.." && pwd -P)"
    repo="$(cd "$(dirname "$path")/../../../.." && pwd -P)"

    write_exe "$path" "#!/bin/sh
if [ -f '$repo/.fixture-stage2-commit' ]; then
    IFS= read -r commit <'$repo/.fixture-stage2-commit' || exit 99
else
    commit=\"\$(/usr/bin/git -C '$repo' rev-parse HEAD)\" || exit 99
fi
if [ \"$name\" = \"trustc\" ] && [ \"\${1:-}\" = \"--print\" ] && [ \"\${2:-}\" = \"sysroot\" ]; then
    echo \"$sysroot\"
    exit 0
fi
case \"\${1:-}\" in
    -Vv|-vV|--version)
        case \"$name\" in
            trustc)
                echo \"trustc 0.1.0 (trust-test)\"
                echo \"binary: trustc\"
                echo \"commit-hash: \$commit\"
                echo \"release: 0.1.0-test\"
                ;;
            targo)
                echo \"cargo 0.1.0 (trust-test)\"
                echo \"binary: targo\"
                echo \"commit-hash: \$commit\"
                echo \"release: 0.1.0-test\"
                ;;
            targo-trust)
                echo \"targo-trust 0.1.0 (trust-test)\"
                echo \"trust-repo-commit-hash: \$commit\"
                ;;
            trustd)
                [ -z \"\${TRUST_MEMORY_JOBSERVER_SOCK:-}\" ] || exit 97
                [ -z \"\${TRUSTD_DISABLE:-}\" ] || exit 98
                echo \"trustd 0.1.0-test\"
                echo \"trust.identity=trustd\"
                echo \"trust.protocol=trustd.status.v1\"
                echo \"commit-hash: \$commit\"
                echo \"trust-repo-commit-hash: \$commit\"
                ;;
        esac
        exit 0
        ;;
esac
exit 0"
}

run_orchestrator() {
    local repo="$1"
    local fake_bin="$2"
    local output="$3"
    local rc=0
    local python_path="${RUN_TESTS_PYTHON:-$fake_bin/python3.11}"

    /usr/bin/git -C "$repo" init -q
    /usr/bin/git -C "$repo" config user.name "Trust Test"
    /usr/bin/git -C "$repo" config user.email "trust-test@example.invalid"
    /usr/bin/git -C "$repo" add -A
    /usr/bin/git -C "$repo" commit --allow-empty -qm "candidate fixture"
    if [[ -n "${RUN_TESTS_DIRTY_AFTER_COMMIT:-}" ]]; then
        printf 'dirty after candidate commit\n' >>"$repo/$RUN_TESTS_DIRTY_AFTER_COMMIT"
    fi

    # Deliberately inject hostile selectors and daemon controls. The
    # orchestrator must derive its own Stage2 siblings, clear controls before
    # probing trustd, scope the selectors to T3, and keep all of them out of T4.
    env \
        TRUSTC="$fake_bin/ambient-trustc" \
        TARGO="$fake_bin/ambient-targo" \
        TARGO_TRUST="$fake_bin/ambient-targo-trust" \
        TRUSTD="$fake_bin/ambient-trustd" \
        TRUST_MEMORY_JOBSERVER_SOCK="$repo/ambient-trustd.sock" \
        TRUSTD_DISABLE=1 \
        PYTHON="$python_path" \
        CARGO="$fake_bin/cargo" \
        PATH="$fake_bin:$PATH" \
        /bin/bash "$repo/scripts/run_tests_after_build.sh" >"$output" 2>&1 || rc=$?
    printf '%s\n' "$rc"
}

assert_contains() {
    local file="$1"
    local needle="$2"

    if ! grep -qF "$needle" "$file"; then
        echo "--- output ---"
        cat "$file"
        echo "--------------"
        fail_test "expected output to contain: $needle"
    fi
}

assert_not_contains() {
    local file="$1"
    local needle="$2"

    if grep -qF "$needle" "$file"; then
        echo "--- output ---"
        cat "$file"
        echo "--------------"
        fail_test "did not expect output to contain: $needle"
    fi
}

TMP_DIR="$(mktemp -d /tmp/trust_run_tests_after_build_fail_closed_XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

echo "=== run_tests_after_build fail-closed regression ==="

echo "--- relative PYTHON rejected"
RELATIVE_PYTHON_REPO="$TMP_DIR/relative-python"
RELATIVE_PYTHON_BIN="$RELATIVE_PYTHON_REPO/fake-bin"
RELATIVE_PYTHON_OUT="$RELATIVE_PYTHON_REPO/output.log"

write_common_repo "$RELATIVE_PYTHON_REPO"
mkdir -p "$RELATIVE_PYTHON_BIN"
write_fake_python "$RELATIVE_PYTHON_BIN"
write_fake_cargo "$RELATIVE_PYTHON_BIN"

RUN_TESTS_PYTHON="python3.11"
relative_python_rc="$(run_orchestrator \
    "$RELATIVE_PYTHON_REPO" \
    "$RELATIVE_PYTHON_BIN" \
    "$RELATIVE_PYTHON_OUT")"
unset RUN_TESTS_PYTHON
if [[ "$relative_python_rc" -eq 0 ]]; then
    fail_test "relative PYTHON should fail"
fi
assert_contains "$RELATIVE_PYTHON_OUT" \
    "PYTHON must be an absolute executable path: python3.11"
assert_not_contains "$RELATIVE_PYTHON_OUT" "using PYTHON:"

echo "--- dirty tracked candidate rejected"
DIRTY_TRACKED_REPO="$TMP_DIR/dirty-tracked"
DIRTY_TRACKED_BIN="$DIRTY_TRACKED_REPO/fake-bin"
DIRTY_TRACKED_OUT="$DIRTY_TRACKED_REPO/output.log"

write_common_repo "$DIRTY_TRACKED_REPO"
mkdir -p "$DIRTY_TRACKED_BIN"
write_fake_pgrep "$DIRTY_TRACKED_BIN"
write_fake_python "$DIRTY_TRACKED_BIN"
write_fake_cargo "$DIRTY_TRACKED_BIN"
RUN_TESTS_DIRTY_AFTER_COMMIT=".gitignore"
dirty_tracked_rc="$(run_orchestrator \
    "$DIRTY_TRACKED_REPO" \
    "$DIRTY_TRACKED_BIN" \
    "$DIRTY_TRACKED_OUT")"
unset RUN_TESTS_DIRTY_AFTER_COMMIT
if [[ "$dirty_tracked_rc" -eq 0 ]]; then
    fail_test "dirty tracked candidate should fail"
fi
assert_contains "$DIRTY_TRACKED_OUT" "candidate Git tree or recursive submodule closure is dirty:"
assert_contains "$DIRTY_TRACKED_OUT" ".gitignore"
assert_not_contains "$DIRTY_TRACKED_OUT" "using TRUSTC:"

echo "--- dirty untracked candidate rejected"
DIRTY_UNTRACKED_REPO="$TMP_DIR/dirty-untracked"
DIRTY_UNTRACKED_BIN="$DIRTY_UNTRACKED_REPO/fake-bin"
DIRTY_UNTRACKED_OUT="$DIRTY_UNTRACKED_REPO/output.log"

write_common_repo "$DIRTY_UNTRACKED_REPO"
mkdir -p "$DIRTY_UNTRACKED_BIN"
write_fake_pgrep "$DIRTY_UNTRACKED_BIN"
write_fake_python "$DIRTY_UNTRACKED_BIN"
write_fake_cargo "$DIRTY_UNTRACKED_BIN"
RUN_TESTS_DIRTY_AFTER_COMMIT="dirty-untracked.txt"
dirty_untracked_rc="$(run_orchestrator \
    "$DIRTY_UNTRACKED_REPO" \
    "$DIRTY_UNTRACKED_BIN" \
    "$DIRTY_UNTRACKED_OUT")"
unset RUN_TESTS_DIRTY_AFTER_COMMIT
if [[ "$dirty_untracked_rc" -eq 0 ]]; then
    fail_test "dirty untracked candidate should fail"
fi
assert_contains "$DIRTY_UNTRACKED_OUT" "candidate Git tree or recursive submodule closure is dirty:"
assert_contains "$DIRTY_UNTRACKED_OUT" "dirty-untracked.txt"
assert_not_contains "$DIRTY_UNTRACKED_OUT" "using TRUSTC:"

echo "--- stage2 commit must match exact candidate HEAD"
HEAD_MISMATCH_REPO="$TMP_DIR/head-mismatch"
HEAD_MISMATCH_BIN="$HEAD_MISMATCH_REPO/fake-bin"
HEAD_MISMATCH_OUT="$HEAD_MISMATCH_REPO/output.log"
HEAD_MISMATCH_COMMIT="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

write_common_repo "$HEAD_MISMATCH_REPO"
mkdir -p "$HEAD_MISMATCH_BIN"
write_fake_pgrep "$HEAD_MISMATCH_BIN"
write_fake_python "$HEAD_MISMATCH_BIN"
write_fake_cargo "$HEAD_MISMATCH_BIN"
printf '%s\n' "$HEAD_MISMATCH_COMMIT" >"$HEAD_MISMATCH_REPO/.fixture-stage2-commit"
write_fake_stage2_tool "$HEAD_MISMATCH_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$HEAD_MISMATCH_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$HEAD_MISMATCH_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$HEAD_MISMATCH_REPO/build/host/stage2/bin/trustd" trustd
head_mismatch_rc="$(run_orchestrator \
    "$HEAD_MISMATCH_REPO" \
    "$HEAD_MISMATCH_BIN" \
    "$HEAD_MISMATCH_OUT")"
HEAD_MISMATCH_ACTUAL="$(/usr/bin/git -C "$HEAD_MISMATCH_REPO" rev-parse HEAD)"
if [[ "$head_mismatch_rc" -eq 0 ]]; then
    fail_test "stage2 commit mismatch with candidate HEAD should fail"
fi
assert_contains "$HEAD_MISMATCH_OUT" \
    "stage2 trustc commit $HEAD_MISMATCH_COMMIT does not match exact candidate HEAD $HEAD_MISMATCH_ACTUAL"
assert_not_contains "$HEAD_MISMATCH_OUT" "Tneg1_ledger: START"

echo "--- missing Stage2 producer receipt rejected"
MISSING_RECEIPT_REPO="$TMP_DIR/missing-producer-receipt"
MISSING_RECEIPT_BIN="$MISSING_RECEIPT_REPO/fake-bin"
MISSING_RECEIPT_OUT="$MISSING_RECEIPT_REPO/output.log"

write_common_repo "$MISSING_RECEIPT_REPO"
mkdir -p "$MISSING_RECEIPT_BIN"
write_fake_pgrep "$MISSING_RECEIPT_BIN"
write_fake_python "$MISSING_RECEIPT_BIN"
write_fake_cargo "$MISSING_RECEIPT_BIN"
write_fake_stage2_tool "$MISSING_RECEIPT_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$MISSING_RECEIPT_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$MISSING_RECEIPT_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$MISSING_RECEIPT_REPO/build/host/stage2/bin/trustd" trustd
rm "$MISSING_RECEIPT_REPO/build/host/stage2/tool-provenance.json"
missing_receipt_rc="$(run_orchestrator \
    "$MISSING_RECEIPT_REPO" \
    "$MISSING_RECEIPT_BIN" \
    "$MISSING_RECEIPT_OUT")"
MISSING_RECEIPT_REPO_REAL="$(cd "$MISSING_RECEIPT_REPO" && pwd -P)"
if [[ "$missing_receipt_rc" -eq 0 ]]; then
    fail_test "missing Stage2 producer receipt should fail"
fi
assert_contains "$MISSING_RECEIPT_OUT" \
    "missing exact Stage2 producer receipt: $MISSING_RECEIPT_REPO_REAL/build/host/stage2/tool-provenance.json"
assert_not_contains "$MISSING_RECEIPT_OUT" "using TRUSTC:"

echo "--- rejected Stage2 producer receipt rejected"
REJECTED_RECEIPT_REPO="$TMP_DIR/rejected-producer-receipt"
REJECTED_RECEIPT_BIN="$REJECTED_RECEIPT_REPO/fake-bin"
REJECTED_RECEIPT_OUT="$REJECTED_RECEIPT_REPO/output.log"

write_common_repo "$REJECTED_RECEIPT_REPO"
mkdir -p "$REJECTED_RECEIPT_BIN"
write_fake_pgrep "$REJECTED_RECEIPT_BIN"
write_fake_python_provenance_failure "$REJECTED_RECEIPT_BIN"
write_fake_cargo "$REJECTED_RECEIPT_BIN"
write_fake_stage2_tool "$REJECTED_RECEIPT_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$REJECTED_RECEIPT_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$REJECTED_RECEIPT_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$REJECTED_RECEIPT_REPO/build/host/stage2/bin/trustd" trustd
rejected_receipt_rc="$(run_orchestrator \
    "$REJECTED_RECEIPT_REPO" \
    "$REJECTED_RECEIPT_BIN" \
    "$REJECTED_RECEIPT_OUT")"
if [[ "$rejected_receipt_rc" -eq 0 ]]; then
    fail_test "rejected Stage2 producer receipt should fail"
fi
assert_contains "$REJECTED_RECEIPT_OUT" \
    "Stage2 producer receipt verification failed; see tests-Tpre_stage2_provenance.log"
assert_not_contains "$REJECTED_RECEIPT_OUT" "using TRUSTC:"

echo "--- missing stage2 targo"
MISSING_TARGO_REPO="$TMP_DIR/missing-stage2-targo"
MISSING_TARGO_BIN="$MISSING_TARGO_REPO/fake-bin"
MISSING_TARGO_OUT="$MISSING_TARGO_REPO/output.log"
AMBIENT_TARGO_MARKER="$MISSING_TARGO_REPO/ambient-targo-used"
AMBIENT_CARGO_MARKER="$MISSING_TARGO_REPO/ambient-cargo-used"

write_common_repo "$MISSING_TARGO_REPO"
mkdir -p "$MISSING_TARGO_BIN"
write_fake_pgrep "$MISSING_TARGO_BIN"
write_fake_python "$MISSING_TARGO_BIN"
write_exe "$MISSING_TARGO_BIN/cargo" "#!/bin/sh
touch '$AMBIENT_CARGO_MARKER'
exit 88"
write_fake_stage2_tool "$MISSING_TARGO_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$MISSING_TARGO_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$MISSING_TARGO_REPO/build/host/stage2/bin/trustd" trustd
write_exe "$MISSING_TARGO_BIN/targo" "#!/bin/sh
touch '$AMBIENT_TARGO_MARKER'
exit 0"

missing_targo_rc="$(run_orchestrator \
    "$MISSING_TARGO_REPO" \
    "$MISSING_TARGO_BIN" \
    "$MISSING_TARGO_OUT")"
if [[ "$missing_targo_rc" -eq 0 ]]; then
    fail_test "missing stage2 targo should fail"
fi
MISSING_TARGO_REPO_REAL="$(cd "$MISSING_TARGO_REPO" && pwd -P)"
assert_contains "$MISSING_TARGO_OUT" "using PYTHON: $MISSING_TARGO_BIN/python3.11"
assert_not_contains "$MISSING_TARGO_OUT" "using CARGO:"
assert_contains "$MISSING_TARGO_OUT" \
    "stage2 tool must be an exact regular executable: $MISSING_TARGO_REPO_REAL/build/host/stage2/bin/targo"
if [[ -e "$AMBIENT_TARGO_MARKER" ]]; then
    fail_test "ambient targo was invoked despite missing stage2 targo"
fi
if [[ -e "$AMBIENT_CARGO_MARKER" ]]; then
    fail_test "ambient CARGO was invoked instead of the exact stage2 targo"
fi

echo "--- missing stage2 trustd"
MISSING_TRUSTD_REPO="$TMP_DIR/missing-stage2-trustd"
MISSING_TRUSTD_BIN="$MISSING_TRUSTD_REPO/fake-bin"
MISSING_TRUSTD_OUT="$MISSING_TRUSTD_REPO/output.log"
AMBIENT_TRUSTD_MARKER="$MISSING_TRUSTD_REPO/ambient-trustd-used"

write_common_repo "$MISSING_TRUSTD_REPO"
mkdir -p "$MISSING_TRUSTD_BIN"
write_fake_pgrep "$MISSING_TRUSTD_BIN"
write_fake_python "$MISSING_TRUSTD_BIN"
write_fake_cargo "$MISSING_TRUSTD_BIN"
write_fake_stage2_tool "$MISSING_TRUSTD_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$MISSING_TRUSTD_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$MISSING_TRUSTD_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_exe "$MISSING_TRUSTD_BIN/ambient-trustd" "#!/bin/sh
touch '$AMBIENT_TRUSTD_MARKER'
exit 0"

missing_trustd_rc="$(run_orchestrator \
    "$MISSING_TRUSTD_REPO" \
    "$MISSING_TRUSTD_BIN" \
    "$MISSING_TRUSTD_OUT")"
if [[ "$missing_trustd_rc" -eq 0 ]]; then
    fail_test "missing stage2 trustd should fail"
fi
MISSING_TRUSTD_REPO_REAL="$(cd "$MISSING_TRUSTD_REPO" && pwd -P)"
assert_contains "$MISSING_TRUSTD_OUT" \
    "stage2 tool must be an exact regular executable: $MISSING_TRUSTD_REPO_REAL/build/host/stage2/bin/trustd"
assert_not_contains "$MISSING_TRUSTD_OUT" "T3_e2e: START"
if [[ -e "$AMBIENT_TRUSTD_MARKER" ]]; then
    fail_test "ambient trustd was invoked despite missing stage2 trustd"
fi

echo "--- stage2 trustd commit mismatch"
BAD_TRUSTD_REPO="$TMP_DIR/stage2-trustd-commit"
BAD_TRUSTD_BIN="$BAD_TRUSTD_REPO/fake-bin"
BAD_TRUSTD_OUT="$BAD_TRUSTD_REPO/output.log"
WRONG_TRUSTD_COMMIT="fedcba9876543210fedcba9876543210fedcba98"

write_common_repo "$BAD_TRUSTD_REPO"
mkdir -p "$BAD_TRUSTD_BIN"
write_fake_pgrep "$BAD_TRUSTD_BIN"
write_fake_python "$BAD_TRUSTD_BIN"
write_fake_cargo "$BAD_TRUSTD_BIN"
write_fake_stage2_tool "$BAD_TRUSTD_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$BAD_TRUSTD_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$BAD_TRUSTD_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_exe "$BAD_TRUSTD_REPO/build/host/stage2/bin/trustd" "#!/bin/sh
[ \"\${1:-}\" = \"--version\" ] || exit 9
echo \"trustd 0.1.0-test\"
echo \"trust.identity=trustd\"
echo \"trust.protocol=trustd.status.v1\"
echo \"commit-hash: $WRONG_TRUSTD_COMMIT\"
echo \"trust-repo-commit-hash: $WRONG_TRUSTD_COMMIT\"
exit 0"

bad_trustd_rc="$(run_orchestrator \
    "$BAD_TRUSTD_REPO" \
    "$BAD_TRUSTD_BIN" \
    "$BAD_TRUSTD_OUT")"
TRUSTC_COMMIT="$(/usr/bin/git -C "$BAD_TRUSTD_REPO" rev-parse HEAD)"
if [[ "$bad_trustd_rc" -eq 0 ]]; then
    fail_test "mismatched stage2 trustd commit should fail"
fi
assert_contains "$BAD_TRUSTD_OUT" \
    "TRUSTD commit mismatch: expected $TRUSTC_COMMIT, got $WRONG_TRUSTD_COMMIT"
assert_not_contains "$BAD_TRUSTD_OUT" "T3_e2e: START"

echo "--- stage2 targo identity failure"
BAD_TARGO_REPO="$TMP_DIR/stage2-targo-identity"
BAD_TARGO_BIN="$BAD_TARGO_REPO/fake-bin"
BAD_TARGO_OUT="$BAD_TARGO_REPO/output.log"
BAD_AMBIENT_TARGO_MARKER="$BAD_TARGO_REPO/ambient-targo-used"

write_common_repo "$BAD_TARGO_REPO"
mkdir -p "$BAD_TARGO_BIN"
write_fake_pgrep "$BAD_TARGO_BIN"
write_fake_python "$BAD_TARGO_BIN"
write_fake_cargo "$BAD_TARGO_BIN"
write_fake_stage2_tool "$BAD_TARGO_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$BAD_TARGO_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$BAD_TARGO_REPO/build/host/stage2/bin/trustd" trustd
write_exe "$BAD_TARGO_REPO/build/host/stage2/bin/targo" '#!/bin/sh
case "${1:-}" in
    -vV|--version)
        echo "notcargo 0.1.0"
        exit 0
        ;;
esac
exit 0'
write_exe "$BAD_TARGO_BIN/targo" "#!/bin/sh
touch '$BAD_AMBIENT_TARGO_MARKER'
exit 0"

bad_targo_rc="$(run_orchestrator \
    "$BAD_TARGO_REPO" \
    "$BAD_TARGO_BIN" \
    "$BAD_TARGO_OUT")"
if [[ "$bad_targo_rc" -eq 0 ]]; then
    fail_test "bad stage2 targo identity should fail"
fi
BAD_TARGO_REPO_REAL="$(cd "$BAD_TARGO_REPO" && pwd -P)"
assert_contains "$BAD_TARGO_OUT" \
    "using TRUSTC: $BAD_TARGO_REPO_REAL/build/host/stage2/bin/trustc"
assert_contains "$BAD_TARGO_OUT" \
    "TARGO identity check did not report targo identity: $BAD_TARGO_REPO_REAL/build/host/stage2/bin/targo"
assert_not_contains "$BAD_TARGO_OUT" "T3_e2e: START"
if [[ -e "$BAD_AMBIENT_TARGO_MARKER" ]]; then
    fail_test "ambient targo was invoked despite bad stage2 targo identity"
fi

echo "--- stage2 trustc sysroot mismatch"
BAD_SYSROOT_REPO="$TMP_DIR/stage2-trustc-sysroot"
BAD_SYSROOT_BIN="$BAD_SYSROOT_REPO/fake-bin"
BAD_SYSROOT_OUT="$BAD_SYSROOT_REPO/output.log"

write_common_repo "$BAD_SYSROOT_REPO"
mkdir -p "$BAD_SYSROOT_BIN"
write_fake_pgrep "$BAD_SYSROOT_BIN"
write_fake_python "$BAD_SYSROOT_BIN"
write_fake_cargo "$BAD_SYSROOT_BIN"
write_exe "$BAD_SYSROOT_REPO/build/host/stage2/bin/trustc" '#!/bin/sh
if [ "${1:-}" = "-Vv" ]; then
    echo "trustc 0.1.0 (trust-test)"
    echo "binary: trustc"
    echo "commit-hash: 0123456789abcdef0123456789abcdef01234567"
    echo "release: 0.1.0-test"
    exit 0
fi
if [ "${1:-}" = "--print" ] && [ "${2:-}" = "sysroot" ]; then
    echo "/tmp"
    exit 0
fi
exit 0'
write_fake_stage2_tool "$BAD_SYSROOT_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$BAD_SYSROOT_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$BAD_SYSROOT_REPO/build/host/stage2/bin/trustd" trustd

bad_sysroot_rc="$(run_orchestrator \
    "$BAD_SYSROOT_REPO" \
    "$BAD_SYSROOT_BIN" \
    "$BAD_SYSROOT_OUT")"
if [[ "$bad_sysroot_rc" -eq 0 ]]; then
    fail_test "bad stage2 trustc sysroot should fail"
fi
BAD_SYSROOT_REPO_REAL="$(cd "$BAD_SYSROOT_REPO" && pwd -P)"
BAD_REPORTED_SYSROOT_REAL="$(cd /tmp && pwd -P)"
assert_contains "$BAD_SYSROOT_OUT" \
    "TRUSTC sysroot mismatch: expected $BAD_SYSROOT_REPO_REAL/build/host/stage2, got $BAD_REPORTED_SYSROOT_REAL"
assert_not_contains "$BAD_SYSROOT_OUT" "T3_e2e: START"

echo "--- missing e2e coverage"
MISSING_E2E_REPO="$TMP_DIR/missing-e2e-coverage"
MISSING_E2E_BIN="$MISSING_E2E_REPO/fake-bin"
MISSING_E2E_OUT="$MISSING_E2E_REPO/output.log"

write_common_repo "$MISSING_E2E_REPO"
mkdir -p "$MISSING_E2E_BIN"
write_fake_pgrep "$MISSING_E2E_BIN"
write_fake_python "$MISSING_E2E_BIN"
write_fake_cargo "$MISSING_E2E_BIN"
write_fake_stage2_tool "$MISSING_E2E_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$MISSING_E2E_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$MISSING_E2E_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$MISSING_E2E_REPO/build/host/stage2/bin/trustd" trustd
cat >"$MISSING_E2E_REPO/scripts/check_ledger_expirations.py" <<'PY'
import sys
sys.exit(0)
PY
cat >"$MISSING_E2E_REPO/x.py" <<'PY'
import sys
sys.exit(0)
PY

missing_e2e_rc="$(run_orchestrator \
    "$MISSING_E2E_REPO" \
    "$MISSING_E2E_BIN" \
    "$MISSING_E2E_OUT")"
if [[ "$missing_e2e_rc" -eq 0 ]]; then
    fail_test "missing e2e coverage should fail"
fi
MISSING_E2E_REPO_REAL="$(cd "$MISSING_E2E_REPO" && pwd -P)"
assert_contains "$MISSING_E2E_OUT" \
    "using TRUSTC: $MISSING_E2E_REPO_REAL/build/host/stage2/bin/trustc"
assert_contains "$MISSING_E2E_OUT" \
    "using TARGO: $MISSING_E2E_REPO_REAL/build/host/stage2/bin/targo"
assert_contains "$MISSING_E2E_OUT" \
    "using TARGO_TRUST: $MISSING_E2E_REPO_REAL/build/host/stage2/bin/targo-trust"
assert_contains "$MISSING_E2E_OUT" \
    "using TRUSTD: $MISSING_E2E_REPO_REAL/build/host/stage2/bin/trustd"
assert_contains "$MISSING_E2E_OUT" "trust.protocol=trustd.status.v1"
assert_contains "$MISSING_E2E_OUT" "sha256:"
assert_contains "$MISSING_E2E_OUT" \
    "T3_e2e: FAIL (no tests/e2e_*.sh scripts found)"
assert_contains "$MISSING_E2E_OUT" "T3_e2e(exit=2)"
assert_not_contains "$MISSING_E2E_OUT" "T3_e2e: SKIPPED"
assert_not_contains "$MISSING_E2E_OUT" "ALL TIERS COMPLETE: PASS"

echo "--- T3 environment scoped before T4"
ENV_SCOPE_REPO="$TMP_DIR/t3-env-scope"
ENV_SCOPE_BIN="$ENV_SCOPE_REPO/fake-bin"
ENV_SCOPE_OUT="$ENV_SCOPE_REPO/output.log"
ENV_SCOPE_STAGE2_BIN="$ENV_SCOPE_REPO/build/host/stage2/bin"
T4_ENV_MARKER="$ENV_SCOPE_REPO/t4-stage2-env-leaked"
ENV_SCOPE_BASELINE="fedcba9876543210fedcba9876543210fedcba98"

write_common_repo "$ENV_SCOPE_REPO"
ENV_SCOPE_STAGE2_BIN="$(cd "$ENV_SCOPE_STAGE2_BIN" && pwd -P)"
mkdir -p "$ENV_SCOPE_BIN"
write_fake_pgrep "$ENV_SCOPE_BIN"
write_fake_python_t4_env_guard "$ENV_SCOPE_BIN" "$ENV_SCOPE_STAGE2_BIN" "$T4_ENV_MARKER"
write_fake_cargo "$ENV_SCOPE_BIN"
write_fake_stage2_tool "$ENV_SCOPE_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$ENV_SCOPE_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$ENV_SCOPE_REPO/build/host/stage2/bin/targo" targo
write_fake_stage2_tool "$ENV_SCOPE_REPO/build/host/stage2/bin/trustd" trustd
write_exe "$ENV_SCOPE_REPO/tests/e2e_smoke.sh" "#!/bin/sh
[ \"\${TRUSTD:-}\" = '$ENV_SCOPE_STAGE2_BIN/trustd' ] || exit 91
case :\${PATH:-}: in
    *:$ENV_SCOPE_STAGE2_BIN:*) ;;
    *) exit 92 ;;
esac
\"\$TRUSTD\" --version >/dev/null 2>&1 || exit 93
exit 0"
write_exe "$ENV_SCOPE_REPO/scripts/stage2_certified_monitor_e2e.sh" '#!/bin/sh
exit 0'
cat >"$ENV_SCOPE_REPO/scripts/check_ledger_expirations.py" <<'PY'
import sys
sys.exit(0)
PY
cat >"$ENV_SCOPE_REPO/x.py" <<'PY'
import sys
sys.exit(0)
PY
cat >"$ENV_SCOPE_REPO/tests/upstream-rust/baseline.toml" <<TOML
revision = "rust-lang/rust:$ENV_SCOPE_BASELINE"
TOML
git -C "$ENV_SCOPE_REPO" init -q

env_scope_rc="$(run_orchestrator \
    "$ENV_SCOPE_REPO" \
    "$ENV_SCOPE_BIN" \
    "$ENV_SCOPE_OUT")"
if [[ "$env_scope_rc" -eq 0 ]]; then
    fail_test "T3 environment scope fixture should fail only at unreachable T5 baseline"
fi
assert_contains "$ENV_SCOPE_OUT" "T3_e2e: PASS 1/1"
assert_contains "$ENV_SCOPE_OUT" \
    "T5_parity: FAIL (baseline rust-lang/rust SHA $ENV_SCOPE_BASELINE not present locally)"
if [[ -e "$T4_ENV_MARKER" ]]; then
    fail_test "T3 stage2 environment leaked into T4"
fi

echo "--- missing upstream baseline"
MISSING_BASELINE_REPO="$TMP_DIR/missing-upstream-baseline"
MISSING_BASELINE_BIN="$MISSING_BASELINE_REPO/fake-bin"
MISSING_BASELINE_OUT="$MISSING_BASELINE_REPO/output.log"
UNREACHABLE_BASELINE="0123456789abcdef0123456789abcdef01234567"
T5_TARGO_MARKER="$MISSING_BASELINE_REPO/t5-targo-used"

write_common_repo "$MISSING_BASELINE_REPO"
mkdir -p "$MISSING_BASELINE_BIN"
write_fake_pgrep "$MISSING_BASELINE_BIN"
write_fake_python "$MISSING_BASELINE_BIN"
write_fake_cargo "$MISSING_BASELINE_BIN"
write_fake_stage2_tool "$MISSING_BASELINE_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$MISSING_BASELINE_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$MISSING_BASELINE_REPO/build/host/stage2/bin/trustd" trustd
write_exe "$MISSING_BASELINE_REPO/build/host/stage2/bin/targo" "#!/bin/sh
commit=\"\$(/usr/bin/git -C '$MISSING_BASELINE_REPO' rev-parse HEAD)\" || exit 99
case \"\${1:-}\" in
    -vV|--version)
        echo \"cargo 0.1.0 (trust-test)\"
        echo \"binary: targo\"
        echo \"commit-hash: \$commit\"
        echo \"release: 0.1.0-test\"
        exit 0
        ;;
esac
if [ \"\${1:-}\" = \"trust\" ] \
    && [ \"\${2:-}\" = \"domination\" ] \
    && [ \"\${3:-}\" = \"upstream-tests\" ]; then
    touch '$T5_TARGO_MARKER'
fi
exit 0"
write_exe "$MISSING_BASELINE_REPO/tests/e2e_smoke.sh" '#!/bin/sh
exit 0'
write_exe "$MISSING_BASELINE_REPO/scripts/stage2_certified_monitor_e2e.sh" '#!/bin/sh
exit 0'
cat >"$MISSING_BASELINE_REPO/scripts/check_ledger_expirations.py" <<'PY'
import sys
sys.exit(0)
PY
cat >"$MISSING_BASELINE_REPO/x.py" <<'PY'
import sys
sys.exit(0)
PY
cat >"$MISSING_BASELINE_REPO/tests/upstream-rust/baseline.toml" <<TOML
revision = "rust-lang/rust:$UNREACHABLE_BASELINE"
TOML
git -C "$MISSING_BASELINE_REPO" init -q

missing_baseline_rc="$(run_orchestrator \
    "$MISSING_BASELINE_REPO" \
    "$MISSING_BASELINE_BIN" \
    "$MISSING_BASELINE_OUT")"
if [[ "$missing_baseline_rc" -eq 0 ]]; then
    fail_test "missing upstream baseline should fail"
fi
assert_contains "$MISSING_BASELINE_OUT" \
    "T5_parity: FAIL (baseline rust-lang/rust SHA $UNREACHABLE_BASELINE not present locally)"
assert_contains "$MISSING_BASELINE_OUT" "ALL TIERS COMPLETE: FAIL (T5_parity(exit=2))"
assert_not_contains "$MISSING_BASELINE_OUT" "T5_parity: SKIPPED"
if [[ -e "$T5_TARGO_MARKER" ]]; then
    fail_test "targo should not run when the upstream baseline is unreachable"
fi

echo "--- final candidate mutation rejected"
FINAL_MUTATION_REPO="$TMP_DIR/final-mutation"
FINAL_MUTATION_BIN="$FINAL_MUTATION_REPO/fake-bin"
FINAL_MUTATION_OUT="$FINAL_MUTATION_REPO/output.log"

write_common_repo "$FINAL_MUTATION_REPO"
mkdir -p "$FINAL_MUTATION_BIN"
write_fake_pgrep "$FINAL_MUTATION_BIN"
write_fake_python "$FINAL_MUTATION_BIN"
write_fake_cargo "$FINAL_MUTATION_BIN"
write_fake_stage2_tool "$FINAL_MUTATION_REPO/build/host/stage2/bin/trustc" trustc
write_fake_stage2_tool "$FINAL_MUTATION_REPO/build/host/stage2/bin/targo-trust" targo-trust
write_fake_stage2_tool "$FINAL_MUTATION_REPO/build/host/stage2/bin/trustd" trustd
write_exe "$FINAL_MUTATION_REPO/build/host/stage2/bin/targo" "#!/bin/sh
commit=\"\$(/usr/bin/git -C '$FINAL_MUTATION_REPO' rev-parse HEAD)\" || exit 99
case \"\${1:-}\" in
    -vV|--version)
        echo \"cargo 0.1.0 (trust-test)\"
        echo \"binary: targo\"
        echo \"commit-hash: \$commit\"
        echo \"release: 0.1.0-test\"
        exit 0
        ;;
esac
printf '# mutated by tier command\\n' >>'$FINAL_MUTATION_REPO/.gitignore'
exit 0"
write_exe "$FINAL_MUTATION_REPO/tests/e2e_smoke.sh" '#!/bin/sh
exit 0'
write_exe "$FINAL_MUTATION_REPO/scripts/stage2_certified_monitor_e2e.sh" '#!/bin/sh
exit 0'
cat >"$FINAL_MUTATION_REPO/scripts/check_ledger_expirations.py" <<'PY'
import sys
sys.exit(0)
PY
cat >"$FINAL_MUTATION_REPO/x.py" <<'PY'
import sys
sys.exit(0)
PY
/usr/bin/git -C "$FINAL_MUTATION_REPO" init -q
/usr/bin/git -C "$FINAL_MUTATION_REPO" config user.name "Trust Test"
/usr/bin/git -C "$FINAL_MUTATION_REPO" config user.email "trust-test@example.invalid"
/usr/bin/git -C "$FINAL_MUTATION_REPO" commit --allow-empty -qm "reachable upstream baseline"
FINAL_MUTATION_BASELINE="$(/usr/bin/git -C "$FINAL_MUTATION_REPO" rev-parse HEAD)"
cat >"$FINAL_MUTATION_REPO/tests/upstream-rust/baseline.toml" <<TOML
revision = "rust-lang/rust:$FINAL_MUTATION_BASELINE"
TOML

final_mutation_rc="$(run_orchestrator \
    "$FINAL_MUTATION_REPO" \
    "$FINAL_MUTATION_BIN" \
    "$FINAL_MUTATION_OUT")"
if [[ "$final_mutation_rc" -eq 0 ]]; then
    fail_test "a candidate mutated during tiers should fail final closure"
fi
assert_contains "$FINAL_MUTATION_OUT" "T5_parity: PASS"
assert_contains "$FINAL_MUTATION_OUT" "Tfinal_candidate_closure: FAIL"
assert_contains "$FINAL_MUTATION_OUT" \
    "ALL TIERS COMPLETE: FAIL (Tfinal_candidate_closure(exit=1))"
assert_not_contains "$FINAL_MUTATION_OUT" "ALL TIERS COMPLETE: PASS"

echo "PASS"
