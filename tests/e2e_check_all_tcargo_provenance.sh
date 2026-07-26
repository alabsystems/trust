#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust-check-all-targo.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

fail() {
    echo "FAIL: $*" >&2
    exit 1
}

write_exe() {
    local path="$1"
    local body="$2"
    mkdir -p "$(dirname "$path")"
    printf '%s\n' "$body" >"$path"
    chmod +x "$path"
}

write_python_script() {
    local path="$1"
    mkdir -p "$(dirname "$path")"
    cat >"$path" <<'PY'
#!/usr/bin/env python3
raise SystemExit(0)
PY
}

write_fixture_repo() {
    local repo="$1"
    mkdir -p "$repo/scripts" "$repo/crates" "$repo/targo-trust"
    cp "$ROOT/scripts/check_all.sh" "$repo/scripts/check_all.sh"
    chmod +x "$repo/scripts/check_all.sh"
    write_python_script "$repo/scripts/check_cargo_manifest_alignment.py"
    write_python_script "$repo/scripts/check_ledger_expirations.py"
    printf '[workspace]\n' >"$repo/crates/Cargo.toml"
    printf '# lock\n' >"$repo/crates/Cargo.lock"
    printf '[package]\nname = "fixture"\nversion = "0.0.0"\nedition = "2021"\n' \
        >"$repo/targo-trust/Cargo.toml"
    printf '# lock\n' >"$repo/targo-trust/Cargo.lock"
    write_exe "$repo/build/host/stage2/bin/trustc" '#!/usr/bin/env sh
exit 0'
}

write_fake_targo() {
    local path="$1"
    local log="$2"
    write_exe "$path" "#!/usr/bin/env sh
printf '%s\n' \"\$*\" >> '$log'
exit 0"
}

write_fake_cargo() {
    local path="$1"
    local marker="$2"
    local exit_code="$3"
    write_exe "$path" "#!/usr/bin/env sh
touch '$marker'
exit $exit_code"
}

find_python_with_toml() {
    local candidate
    for candidate in "${PYTHON:-}" python3.14 python3.13 python3.12 python3.11 python3 python; do
        [ -n "$candidate" ] || continue
        if command -v "$candidate" >/dev/null 2>&1 \
            && "$candidate" - <<'PY' >/dev/null 2>&1
import importlib.util
raise SystemExit(
    0
    if importlib.util.find_spec("tomllib") or importlib.util.find_spec("tomli")
    else 1
)
PY
        then
            command -v "$candidate"
            return 0
        fi
    done
    return 1
}

PYTHON_BIN="$(find_python_with_toml)" || fail "Python with tomllib/tomli is required"

echo "--- missing stage2 targo rejects ambient cargo"
REPO="$TMP_DIR/missing-targo"
OUT="$REPO/output.log"
AMBIENT_MARKER="$REPO/ambient-cargo-used"
write_fixture_repo "$REPO"
mkdir -p "$REPO/fake-bin"
write_fake_cargo "$REPO/fake-bin/cargo" "$AMBIENT_MARKER" 0
if CARGO="$REPO/fake-bin/cargo" PYTHON="$PYTHON_BIN" bash "$REPO/scripts/check_all.sh" \
    >"$OUT" 2>&1; then
    fail "check_all should fail when stage2 targo is missing"
fi
grep -q "Missing repo-local stage2 Trust targo required for golden checks" "$OUT" \
    || fail "missing targo failure should name the required stage2 targo"
grep -q "ambient Cargo/Targo is never accepted as release-gate evidence" "$OUT" \
    || fail "missing targo failure should explain ambient CARGO is ignored"
[ ! -e "$AMBIENT_MARKER" ] || fail "ambient cargo must not run without stage2 targo"

echo "--- golden checks use stage2 targo despite poisoned cargo"
REPO="$TMP_DIR/stage2-targo"
OUT="$REPO/output.log"
TARGO_LOG="$REPO/targo.log"
AMBIENT_MARKER="$REPO/ambient-cargo-used"
write_fixture_repo "$REPO"
write_fake_targo "$REPO/build/host/stage2/bin/targo" "$TARGO_LOG"
mkdir -p "$REPO/fake-bin"
write_fake_cargo "$REPO/fake-bin/cargo" "$AMBIENT_MARKER" 99
CARGO="$REPO/fake-bin/cargo" PYTHON="$PYTHON_BIN" bash "$REPO/scripts/check_all.sh" \
    >"$OUT" 2>&1 || {
        cat "$OUT" >&2
        fail "check_all should pass with stage2 targo"
    }
grep -q "trust gate check-all" "$TARGO_LOG" \
    || fail "stage2 targo should run the Rust-native check-all gate"
grep -Eq -- "--targo [^ ]*/build/host/stage2/bin/targo" "$TARGO_LOG" \
    || fail "stage2 targo gate should pin the repo-local stage2 targo"
if grep -q -- "--host-diagnostics" "$TARGO_LOG"; then
    fail "host diagnostics must not be requested unless explicitly enabled"
fi
[ ! -e "$AMBIENT_MARKER" ] || fail "poisoned ambient cargo must not run"

echo "--- host diagnostics are optional and explicitly requested"
REPO="$TMP_DIR/host-diagnostic"
OUT="$REPO/output.log"
TARGO_LOG="$REPO/targo.log"
AMBIENT_MARKER="$REPO/host-cargo-used"
write_fixture_repo "$REPO"
write_fake_targo "$REPO/build/host/stage2/bin/targo" "$TARGO_LOG"
mkdir -p "$REPO/fake-bin"
write_fake_cargo "$REPO/fake-bin/cargo" "$AMBIENT_MARKER" 99
CARGO="$REPO/fake-bin/cargo" PYTHON="$PYTHON_BIN" TRUST_CHECK_ALL_RUN_HOST_DIAGNOSTICS=1 \
    bash "$REPO/scripts/check_all.sh" >"$OUT" 2>&1 \
    || fail "host diagnostic request should not fail golden checks"
grep -q "trust gate check-all" "$TARGO_LOG" \
    || fail "stage2 targo should run the Rust-native check-all gate"
grep -q -- "--host-diagnostics" "$TARGO_LOG" \
    || fail "explicitly enabled host diagnostics should be forwarded to the gate"
[ ! -e "$AMBIENT_MARKER" ] || fail "the wrapper itself must never invoke ambient cargo"

echo "--- host diagnostics cannot satisfy missing golden targo"
REPO="$TMP_DIR/host-diagnostic-missing-targo"
OUT="$REPO/output.log"
AMBIENT_MARKER="$REPO/host-cargo-used"
write_fixture_repo "$REPO"
mkdir -p "$REPO/fake-bin"
write_fake_cargo "$REPO/fake-bin/cargo" "$AMBIENT_MARKER" 0
if CARGO="$REPO/fake-bin/cargo" PYTHON="$PYTHON_BIN" TRUST_CHECK_ALL_RUN_HOST_DIAGNOSTICS=1 \
    bash "$REPO/scripts/check_all.sh" >"$OUT" 2>&1; then
    fail "host diagnostics must not satisfy missing stage2 targo"
fi
[ ! -e "$AMBIENT_MARKER" ] || fail "host diagnostic cargo must not run before golden targo check"

echo "check_all stage2 targo provenance regressions passed"
