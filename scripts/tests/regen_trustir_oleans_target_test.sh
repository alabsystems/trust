#!/usr/bin/env bash
# Self-test: scripts/regen-trustir-oleans.sh names its build target in the environment.
#
# atpkg's targo refuses the workspace's `.cargo/config.toml` `target-dir` ("build cache
# ownership refused: explicit build target is unmanaged or unsupported", exit 75, no build
# started) and accepts the same directory named as CARGO_TARGET_DIR. The land gate's
# olean-audit leg names neither, so the audit refused in under a second on every
# atpkg-managed host (land gate 20261108T022428; identical on main e36421c2ed, and AUDIT OK
# there with CARGO_TARGET_DIR named). A fake targo records the target the script's first
# build hands it, then stops the script.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
set -uo pipefail
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SCRIPT="$REPO_ROOT/scripts/regen-trustir-oleans.sh"
[ -f "$SCRIPT" ] || { echo "regen_trustir_oleans_target tests: no $SCRIPT" >&2; exit 2; }
# The script refuses before any build without an initialized trust-ir checkout; that is a
# precondition of this test, not a pass.
[ -e "$REPO_ROOT/first-party/trust-ir/.git" ] || {
  echo "regen_trustir_oleans_target tests: first-party/trust-ir is not initialized" >&2; exit 2; }

TMP="$(mktemp -d)" || exit 2
trap 'rm -rf "$TMP"' EXIT
cat > "$TMP/targo" <<'EOF'
#!/usr/bin/env bash
# `--unverified --version` is the script's identity probe: it must accept the flag and
# name itself `targo ` as a real Targo does. Every other call is a build.
if [ "${1:-}" = --unverified ] && [ "${2:-}" = --version ]; then echo "targo 0.0.0 (fake)"; exit 0; fi
printf '%s|%s|%s\n' "${CARGO_TARGET_DIR-<unset>}" "${CARGO_BUILD_TARGET_DIR-<unset>}" \
  "${TARGO_TARGET_DIR-<unset>}" > "$SEEN"
exit 3
EOF
chmod +x "$TMP/targo"

FAILED=0
# check <name> <expected CARGO_TARGET_DIR|CARGO_BUILD_TARGET_DIR|TARGO_TARGET_DIR> [VAR=value ...]
check() {
  local name=$1 want=$2; shift 2
  rm -f "$TMP/seen"
  env -u CARGO_TARGET_DIR -u TARGO_TARGET_DIR -u CARGO_BUILD_TARGET_DIR \
    SEEN="$TMP/seen" TRUST_REGEN_TARGO="$TMP/targo" TMPDIR="$TMP" "$@" \
    bash "$SCRIPT" --check >"$TMP/out" 2>&1
  local status=$? got
  got="$(cat "$TMP/seen" 2>/dev/null || echo '<no build>')"
  if [ "$status" -ne 3 ] || [ "$got" != "$want" ]; then
    echo "FAIL $name: exit $status (want 3, the fake build's), target '$got' (want '$want')"
    sed 's/^/    /' "$TMP/out" | tail -5
    FAILED=1
  else
    echo "ok   $name"
  fi
}

check "no caller target: the workspace's own, named in the environment" \
  "$REPO_ROOT/crates/target|<unset>|<unset>"
check "a caller's CARGO_TARGET_DIR wins" "$TMP/mine|<unset>|<unset>" CARGO_TARGET_DIR="$TMP/mine"
check "a caller's CARGO_BUILD_TARGET_DIR wins" "<unset>|$TMP/cfg|<unset>" \
  CARGO_BUILD_TARGET_DIR="$TMP/cfg"
check "a caller's TARGO_TARGET_DIR wins (native Targo reads it only without CARGO_TARGET_DIR)" \
  "<unset>|<unset>|$TMP/native" TARGO_TARGET_DIR="$TMP/native"

[ "$FAILED" -eq 0 ] && echo "regen_trustir_oleans_target tests: PASS"
exit "$FAILED"
