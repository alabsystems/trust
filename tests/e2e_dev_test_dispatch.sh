#!/usr/bin/env bash
# Conformance test for scripts/dev-test.sh's split Cargo/bootstrap inventory.

set -euo pipefail

TRUST_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/trust-dev-test-dispatch.XXXXXX")"
trap 'rm -rf "$TMP_ROOT"' EXIT

FIXTURE="$TMP_ROOT/repo"
LOG="$TMP_ROOT/invocations.log"
mkdir -p "$FIXTURE/scripts" "$FIXTURE/crates/trust-types" "$FIXTURE/toolchain"
cp "$TRUST_ROOT/scripts/dev-test.sh" "$FIXTURE/scripts/dev-test.sh"

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
SH
chmod +x "$FIXTURE/x.py" "$FIXTURE/toolchain/targo"

run_fixture() {
    : >"$LOG"
    DEV_TEST_DISPATCH_LOG="$LOG" \
        TRUST_JOBS=1 \
        TRUST_TARGO_BIN="$FIXTURE/toolchain/targo" \
        "$FIXTURE/scripts/dev-test.sh" "$@" >/dev/null
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
[[ "$(wc -l <"$LOG" | tr -d ' ')" -eq 4 ]]

# Explicit selection remains narrow: one excluded crate is bootstrap-dispatched
# and one ordinary crate is retained for Cargo.
run_fixture --lib trust-thir-lower trust-types
require_exact_line "x.py test --stage 1 crates/trust-thir-lower"
require_exact_line "targo --unverified test -j 1 -p trust-types --lib"
[[ "$(wc -l <"$LOG" | tr -d ' ')" -eq 2 ]]

# An excluded-only explicit selection finishes after bootstrap and must not
# accidentally widen back to the ordinary workspace.
run_fixture trust-witness
require_exact_line "x.py test --stage 1 crates/trust-witness"
if grep -q '^targo ' "$LOG"; then
    echo "excluded-only selection unexpectedly invoked Targo" >&2
    sed 's/^/  observed: /' "$LOG" >&2
    exit 1
fi

echo "dev-test dispatch conformance: PASS"
