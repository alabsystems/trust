#!/usr/bin/env bash
# Self-test for scripts/check_frontier_ratchet.sh.
#
# The ratchet's whole value is the RED case, so a stub measurement stands in for
# the toolchain here: what is under test is the comparison and its exit codes,
# not the verifier. A ratchet that cannot be shown to go red is decoration.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RATCHET="$ROOT/scripts/check_frontier_ratchet.sh"
TMP_ROOT="$(mktemp -d)"
trap 'rm -rf "$TMP_ROOT"' EXIT

FAILURES=0

fail() {
  echo "FAIL: $*" >&2
  FAILURES=$((FAILURES + 1))
}

# A stub `targo-trust` whose `self-improve --out PATH` writes the frontier named
# by FAKE_PROVED / FAKE_UNPROVED.
write_stub_targo() {
  local stub="$1"
  cat >"$stub" <<'SH'
#!/usr/bin/env bash
set -euo pipefail

out=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --out) out="$2"; shift 2 ;;
    *) shift ;;
  esac
done
[ -n "$out" ] || { echo "stub: no --out" >&2; exit 2; }
proved="${FAKE_PROVED:?}"
unproved="${FAKE_UNPROVED:?}"
obligations=$((proved + unproved))
cat >"$out" <<JSON
{"schema":"trust.self-improve.frontier.v1",
 "convergence_score":0.5,
 "total_obligations":$obligations,
 "total_proved":$proved,
 "total_runtime_checked":0,
 "total_unproved":$unproved,
 "crates":[{"crate":"trust-demo","obligations":$obligations,"proved":$proved,
            "runtime_checked":0,"failed":$unproved,"unknown":0}]}
JSON
SH
  chmod +x "$stub"
}

STUB="$TMP_ROOT/targo-trust"
write_stub_targo "$STUB"
BASELINE="$TMP_ROOT/baseline.json"

# 1. No baseline is not a pass.
FAKE_PROVED=10 FAKE_UNPROVED=2 TRUST_FRONTIER_TARGO="$STUB" TRUST_FRONTIER_BASELINE="$BASELINE" \
  bash "$RATCHET" --check >/dev/null 2>&1
status=$?
[ "$status" -eq 2 ] || fail "a missing baseline must exit 2, got $status"

# 2. Mint the baseline.
FAKE_PROVED=10 FAKE_UNPROVED=2 TRUST_FRONTIER_TARGO="$STUB" TRUST_FRONTIER_BASELINE="$BASELINE" \
  bash "$RATCHET" --update >/dev/null 2>&1
status=$?
[ "$status" -eq 0 ] || fail "--update must succeed, got $status"
[ -f "$BASELINE" ] || fail "--update must write the baseline"

# 3. Holding the line is green.
FAKE_PROVED=10 FAKE_UNPROVED=2 TRUST_FRONTIER_TARGO="$STUB" TRUST_FRONTIER_BASELINE="$BASELINE" \
  bash "$RATCHET" --check >/dev/null 2>&1
status=$?
[ "$status" -eq 0 ] || fail "an unchanged frontier must pass, got $status"

# 4. New obligations alone must not red the gate: writing code is not a
#    regression, and a gate that says otherwise gets deleted.
FAKE_PROVED=10 FAKE_UNPROVED=40 TRUST_FRONTIER_TARGO="$STUB" TRUST_FRONTIER_BASELINE="$BASELINE" \
  bash "$RATCHET" --check >/dev/null 2>&1
status=$?
[ "$status" -eq 0 ] || fail "more unproved obligations alone must not fail, got $status"

# 5. Proving less is red, and the message names the crate.
output="$(FAKE_PROVED=7 FAKE_UNPROVED=2 TRUST_FRONTIER_TARGO="$STUB" \
  TRUST_FRONTIER_BASELINE="$BASELINE" bash "$RATCHET" --check 2>&1)"
status=$?
[ "$status" -eq 1 ] || fail "a dropped proved count must exit 1, got $status"
case "$output" in
  *"FRONTIER RATCHET RED"*) ;;
  *) fail "red run must say so: $output" ;;
esac
case "$output" in
  *"REGRESSED trust-demo"*) ;;
  *) fail "red run must name the crate that lost ground: $output" ;;
esac

# 6. A missing toolchain is "cannot evaluate", not "green".
TRUST_FRONTIER_TARGO="$TMP_ROOT/absent" TRUST_FRONTIER_BASELINE="$BASELINE" \
  bash "$RATCHET" --check >/dev/null 2>&1
status=$?
[ "$status" -eq 2 ] || fail "an unavailable toolchain must exit 2, got $status"

if [ "$FAILURES" -ne 0 ]; then
  echo "check_frontier_ratchet_test: $FAILURES failure(s)" >&2
  exit 1
fi
echo "check_frontier_ratchet_test: OK"
