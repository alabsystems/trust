#!/usr/bin/env bash
# Conformance test for scripts/dev-test.sh's split Cargo/bootstrap inventory.

set -euo pipefail

TRUST_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/trust-dev-test-dispatch.XXXXXX")"
trap 'rm -rf "$TMP_ROOT"' EXIT

FIXTURE="$TMP_ROOT/repo"
LOG="$TMP_ROOT/invocations.log"
mkdir -p "$FIXTURE/scripts" "$FIXTURE/crates/trust-types" "$FIXTURE/crates/trust-integration-tests" "$FIXTURE/toolchain"
cp "$TRUST_ROOT/scripts/dev-test.sh" "$FIXTURE/scripts/dev-test.sh"
# dev-test.sh reads the targo-trust path with this script's parser.
cp "$TRUST_ROOT/scripts/check_crates_tests_scoped.py" "$FIXTURE/scripts/check_crates_tests_scoped.py"
TARGET_BIN="$TMP_ROOT/target/debug/targo-trust"

cat >"$FIXTURE/x.py" <<'PY'
#!/usr/bin/env python3
import os
import sys

with open(os.environ["DEV_TEST_DISPATCH_LOG"], "a", encoding="utf-8") as log:
    log.write("x.py " + " ".join(sys.argv[1:]) + "\n")
PY

cat >"$FIXTURE/toolchain/targo" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
case "${1:-}" in
    -vV|--version)
        echo 'targo dev-test-dispatch fixture'
        exit 0
        ;;
esac
printf 'targo' >>"$DEV_TEST_DISPATCH_LOG"
printf ' %s' "$@" >>"$DEV_TEST_DISPATCH_LOG"
printf '\n' >>"$DEV_TEST_DISPATCH_LOG"
if [[ "${2:-}" == "build" ]]; then  # the targo-trust prebuild: JSON on stdout
    if [[ "${DEV_TEST_DISPATCH_BUILD:-ok}" == "fail" ]]; then
        echo 'error: could not compile `targo-trust`' >&2
        exit 101
    fi
    mkdir -p "$(dirname "$DEV_TEST_DISPATCH_TARGET_BIN")"
    printf 'built from this tree\n' >"$DEV_TEST_DISPATCH_TARGET_BIN"
    if [[ "${DEV_TEST_DISPATCH_BUILD:-ok}" != "no-artifact" ]]; then
        printf '{"reason":"compiler-artifact","target":{"name":"targo-trust","kind":["bin"]},"executable":"%s"}\n' \
            "$DEV_TEST_DISPATCH_TARGET_BIN"
    fi
    exit 0
fi
if [[ -n "${TRUST_TARGO_TRUST_BIN:-}" ]]; then
    # A sibling build relinks the target dir's file; the tests hold a copy.
    printf 'relinked by a sibling build\n' >"$DEV_TEST_DISPATCH_TARGET_BIN"
    printf 'test sees %s: %s\n' "$TRUST_TARGO_TRUST_BIN" "$(cat "$TRUST_TARGO_TRUST_BIN")" \
        >>"$DEV_TEST_DISPATCH_LOG"
fi
SH
chmod +x "$FIXTURE/x.py" "$FIXTURE/toolchain/targo"

run_fixture() {
    : >"$LOG"
    env -u TRUST_TARGO_TRUST_BIN \
        DEV_TEST_DISPATCH_LOG="$LOG" \
        DEV_TEST_DISPATCH_TARGET_BIN="$TARGET_BIN" \
        TRUST_JOBS=1 \
        TRUST_TARGO_BIN="$FIXTURE/toolchain/targo" \
        "$FIXTURE/scripts/dev-test.sh" "$@" >/dev/null
}

# `if`, not a bare `[[ ... ]]`: macOS /bin/bash 3.2 does not trip errexit on
# a failing `[[`, so a bare count check there checks nothing.
require_line_count() {
    local expected="$1"
    local count
    count="$(wc -l <"$LOG" | tr -d ' ')"
    if [ "$count" -ne "$expected" ]; then
        echo "expected $expected invocation(s), observed $count" >&2
        sed 's/^/  observed: /' "$LOG" >&2
        exit 1
    fi
}

require_exact_line() {
    local expected="$1"
    local count
    count="$(grep -Fxc "$expected" "$LOG" || true)"
    if [[ "$count" -ne 1 ]]; then
        echo "expected exactly one invocation: $expected" >&2
        sed 's/^/  observed: /' "$LOG" >&2
        exit 1
    fi
}

# No crate arguments means the ordinary workspace *and* every excluded
# rustc_private crate. This is the path used by the quick/trust-extra suites.
run_fixture --lib
require_exact_line "x.py test --stage 1 crates/trust-mir-extract"
require_exact_line "x.py test --stage 1 crates/trust-thir-lower"
require_exact_line "x.py test --stage 1 crates/trust-witness"
require_exact_line "targo --unverified test -j 1 --workspace --lib"
require_line_count 4

# Explicit selection remains narrow: one excluded crate is bootstrap-dispatched
# and one ordinary crate is retained for Cargo.
run_fixture --lib trust-thir-lower trust-types
require_exact_line "x.py test --stage 1 crates/trust-thir-lower"
require_exact_line "targo --unverified test -j 1 -p trust-types --lib"
require_line_count 2

# An excluded-only explicit selection finishes after bootstrap and must not
# accidentally widen back to the ordinary workspace.
run_fixture trust-witness
require_exact_line "x.py test --stage 1 crates/trust-witness"
if grep -q '^targo ' "$LOG"; then
    echo "excluded-only selection unexpectedly invoked Targo" >&2
    sed 's/^/  observed: /' "$LOG" >&2
    exit 1
fi

# trust-integration-tests' tests/*.rs run targo-trust and fail without it: a
# run that includes them builds it first and hands the tests a private copy
# of the file cargo's compiler-artifact message names.
BUILD_LINE="targo --unverified build --manifest-path targo-trust/Cargo.toml --bin targo-trust --locked --message-format json-render-diagnostics"
TMPDIR="$TMP_ROOT" run_fixture trust-integration-tests --filter x
require_exact_line "$BUILD_LINE"
require_exact_line "targo --unverified test -j 1 -p trust-integration-tests -- x"
handed="$(sed -n 's/^test sees \(.*\): built from this tree$/\1/p' "$LOG")"
if [[ -z "$handed" || "$handed" == "$TARGET_BIN" || "$(dirname "$handed")" == "$(dirname "$TARGET_BIN")" ]]; then
    echo "the tests did not get a private copy of the built targo-trust" >&2
    sed 's/^/  observed: /' "$LOG" >&2
    exit 1
fi
if [[ -e "$handed" ]]; then
    echo "the private targo-trust copy outlived dev-test.sh: $handed" >&2
    exit 1
fi
require_line_count 3

# A failed build fails the run, and nothing is tested; so does a build whose
# messages name no targo-trust bin. Neither is a skip.
for case in "fail:targo-trust failed to build" "no-artifact:no compiler-artifact message named the targo-trust bin"; do
    mode="${case%%:*}"
    if DEV_TEST_DISPATCH_BUILD="$mode" run_fixture trust-integration-tests 2>"$TMP_ROOT/stderr"; then
        echo "a targo-trust build ending in '$mode' did not fail dev-test.sh" >&2
        exit 1
    fi
    if ! grep -qF "${case#*:}" "$TMP_ROOT/stderr"; then
        echo "a targo-trust build ending in '$mode' failed without saying: ${case#*:}" >&2
        sed 's/^/  stderr: /' "$TMP_ROOT/stderr" >&2
        exit 1
    fi
    require_exact_line "$BUILD_LINE"
    require_line_count 1
done

# Neither a --lib run nor a crate list without trust-integration-tests runs
# those tests, so neither builds targo-trust (the --lib cases above count it).
run_fixture trust-types
require_exact_line "targo --unverified test -j 1 -p trust-types"
require_line_count 1

# The default run (no crate list, no --lib) is every crate's tests/*.rs,
# trust-integration-tests' included: it builds targo-trust first and the
# workspace run gets the copy.
TMPDIR="$TMP_ROOT" run_fixture
require_exact_line "$BUILD_LINE"
require_exact_line "x.py test --stage 1 crates/trust-mir-extract"
require_exact_line "x.py test --stage 1 crates/trust-thir-lower"
require_exact_line "x.py test --stage 1 crates/trust-witness"
require_exact_line "targo --unverified test -j 1 --workspace"
build_at="$(grep -nFx "$BUILD_LINE" "$LOG" | cut -d: -f1)"
test_at="$(grep -nFx "targo --unverified test -j 1 --workspace" "$LOG" | cut -d: -f1)"
if [ "$build_at" -ge "$test_at" ]; then
    echo "targo-trust was not built before the workspace tests" >&2
    sed 's/^/  observed: /' "$LOG" >&2
    exit 1
fi
if ! grep -q '^test sees .*: built from this tree$' "$LOG"; then
    echo "the default run's tests did not get the built targo-trust" >&2
    sed 's/^/  observed: /' "$LOG" >&2
    exit 1
fi
require_line_count 6

echo "dev-test dispatch conformance: PASS"
