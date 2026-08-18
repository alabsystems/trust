#!/usr/bin/env bash
# Focused, no-build regression tests for Cargo/resource guard accounting.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PROCESS_TREE="$REPO_ROOT/scripts/lib/process_tree.sh"
CARGO_CAP="$REPO_ROOT/scripts/cargo-concurrency-cap.sh"

fail() {
    echo "resource_guards_test: FAIL: $*" >&2
    exit 1
}

assert_eq() {
    local expected="$1"
    local actual="$2"
    local label="$3"
    if [[ "$actual" != "$expected" ]]; then
        fail "$label: expected '$expected', got '$actual'"
    fi
}

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/trust-resource-guards.XXXXXX")"
cleanup() {
    rm -rf "$TMP_ROOT"
}
trap cleanup EXIT

# shellcheck source=../lib/process_tree.sh
. "$PROCESS_TREE"

# Override only the read-only snapshot seam. The unrelated rustc is much
# larger than every member of root 100's tree and must never be measured or
# selected by the governor helper.
trust_process_snapshot() {
    cat <<'EOF'
100 1 10 cargo
101 100 20 rustc
102 101 30 lld
103 100 5 sh
200 1 999999 rustc
201 200 888888 lld
EOF
}

read -r tree_rss tree_count <<<"$(trust_process_tree_rss_kb 100)"
assert_eq 65 "$tree_rss" "recursive process-tree RSS"
assert_eq 4 "$tree_count" "recursive process-tree count"

read -r hog_pid hog_mib <<<"$(trust_heaviest_matching_descendant 100 'rustc|lld')"
assert_eq 102 "$hog_pid" "heaviest in-tree compiler PID"
assert_eq 0 "$hog_mib" "fixture compiler RSS MiB"
trust_process_is_descendant 100 102 || fail "grandchild should be in root tree"
if trust_process_is_descendant 100 200; then
    fail "unrelated compiler was classified as a descendant"
fi

FAKE_CARGO="$TMP_ROOT/fake-cargo"
CAPTURE="$TMP_ROOT/cargo-capture.txt"
cat >"$FAKE_CARGO" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
: "${CARGO_CAP_TEST_CAPTURE:?}"
{
    printf 'jobs=%s\n' "${CARGO_BUILD_JOBS:-unset}"
    for arg in "$@"; do
        printf 'arg=%s\n' "$arg"
    done
} >"$CARGO_CAP_TEST_CAPTURE"
if [[ -n "${CARGO_CAP_TEST_SLEEP:-}" ]]; then
    sleep "$CARGO_CAP_TEST_SLEEP"
fi
exit "${CARGO_CAP_TEST_EXIT:-0}"
EOF
chmod +x "$FAKE_CARGO"

LOCK_DIR="$TMP_ROOT/locks"
CARGO_CAP_TEST_CAPTURE="$CAPTURE" \
TRUST_REAL_CARGO="$FAKE_CARGO" \
TRUST_LOCK_DIR="$LOCK_DIR" \
TRUST_MAX_CONCURRENT=1 \
TRUST_CARGO_JOBS=2 \
TRUST_RSS_MONITOR=0 \
bash "$CARGO_CAP" test -p demo --jobs=1 -- --jobs 99 >/dev/null 2>&1

expected_capture="$(cat <<'EOF'
jobs=1
arg=test
arg=--jobs
arg=1
arg=-p
arg=demo
arg=--
arg=--jobs
arg=99
EOF
)"
assert_eq "$expected_capture" "$(<"$CAPTURE")" "canonical Cargo job arguments"

# A failing Cargo must keep its status and release the semaphore slot.
set +e
CARGO_CAP_TEST_CAPTURE="$CAPTURE" \
CARGO_CAP_TEST_EXIT=37 \
TRUST_REAL_CARGO="$FAKE_CARGO" \
TRUST_LOCK_DIR="$LOCK_DIR" \
TRUST_MAX_CONCURRENT=1 \
TRUST_CARGO_JOBS=1 \
TRUST_RSS_MONITOR=0 \
bash "$CARGO_CAP" check >/dev/null 2>&1
failure_status=$?
set -e
assert_eq 37 "$failure_status" "Cargo failure status propagation"
if find "$LOCK_DIR" -maxdepth 1 -type d -name 'slot_*' -print -quit | grep -q .; then
    fail "Cargo failure leaked a semaphore slot"
fi

# Invalid caps fail before invoking Cargo.
set +e
CARGO_CAP_TEST_CAPTURE="$CAPTURE" \
TRUST_REAL_CARGO="$FAKE_CARGO" \
TRUST_LOCK_DIR="$LOCK_DIR" \
TRUST_MAX_CONCURRENT=1 \
TRUST_CARGO_JOBS=0 \
TRUST_RSS_MONITOR=0 \
bash "$CARGO_CAP" check >/dev/null 2>&1
invalid_status=$?
set -e
assert_eq 2 "$invalid_status" "invalid Cargo job cap status"

# The integrated monitor must sample descendants and finalize immediately when
# the wrapper terminates it, rather than dying during its polling sleep without
# writing a record.
RSS_LOG="$TMP_ROOT/build-rss.log"
CARGO_CAP_TEST_CAPTURE="$CAPTURE" \
CARGO_CAP_TEST_SLEEP=1 \
TRUST_REAL_CARGO="$FAKE_CARGO" \
TRUST_LOCK_DIR="$LOCK_DIR" \
TRUST_MAX_CONCURRENT=1 \
TRUST_CARGO_JOBS=1 \
TRUST_RSS_INTERVAL=30 \
TRUST_RSS_LOG="$RSS_LOG" \
bash "$CARGO_CAP" check >/dev/null 2>&1

grep -qx 'scope: process_tree' "$RSS_LOG" || fail "RSS log omitted process-tree scope"
samples="$(awk '/^samples:/ { value=$2 } END { print value+0 }' "$RSS_LOG")"
peak_processes="$(awk '/^peak_process_count:/ { value=$2 } END { print value+0 }' "$RSS_LOG")"
[[ "$samples" -ge 1 ]] || fail "RSS monitor recorded no samples"
[[ "$peak_processes" -ge 2 ]] || fail "RSS monitor did not observe the fake Cargo child"

echo "resource guards: PASS"
