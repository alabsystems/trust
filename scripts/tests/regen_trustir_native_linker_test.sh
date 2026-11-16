#!/usr/bin/env bash
# Exercise the real producer's early linker validation without starting a build.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="${SCRIPT_UNDER_TEST:-$ROOT/scripts/regen-trustir-oleans.sh}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/scripts"
cp "$SCRIPT" "$TMP/scripts/regen-trustir-oleans.sh"
git -C "$TMP" init --quiet
printf '#!/bin/sh\nexit 99\n' > "$TMP/linker with spaces"
chmod +x "$TMP/linker with spaces"
touch "$TMP/not-executable"
failed=0
check() {
    local name=$1 path=$2 expected=$3 diagnostic=$4 status=0
    (cd "$TMP" && TRUST_REGEN_NATIVE_LINKER="$path" bash scripts/regen-trustir-oleans.sh --check) \
        >"$TMP/out" 2>&1 || status=$?
    if [[ "$status" != "$expected" ]] || ! grep -Fq "$diagnostic" "$TMP/out"; then
        echo "FAIL $name: exit $status, expected $expected" >&2
        cat "$TMP/out" >&2
        failed=1
    else
        echo "ok $name"
    fi
}
refusal='TRUST_REGEN_NATIVE_LINKER must name an absolute executable file'
check relative clang 2 "$refusal"
check missing "$TMP/missing" 2 "$refusal"
check directory "$TMP" 2 "$refusal"
check not-executable "$TMP/not-executable" 2 "$refusal"
# A valid absolute pathname with spaces passes validation, then reaches the
# fixture's missing-source precondition. No compiler or linker is executed.
check executable-with-spaces "$TMP/linker with spaces" 1 'first-party/trust-ir is not initialized'
exit "$failed"
