#!/bin/bash
# check_verifier_executes.sh — a push-profile lane that RUNS THE VERIFIER.
#
# WHY THIS EXISTS. Until 2026-09-14 no lane on the `push` profile executed a
# verifier at all: every push-tier row was a checker, a parser, a syntax pass,
# or a type-check. That is how `tcb_document_exhaustiveness` sat red for weeks
# with nobody noticing (docs/audits/2026-09-14-four-claims-audit.md §5.1, roadmap
# R4). A crate-level `targo trust check -p <crate>` cannot fill the slot: measured
# 2026-09-14, all five crates docs/STRICT_VERIFICATION_FRAGMENT.md names as
# strict-lane passes report `Gate: FAIL` on the shipped pack (26 rows share one
# reason, "solver reported Proved without exact kernel/native proof authority"),
# and the pack's rev is not on main's history — so such a lane would be red on
# every machine that installs the pack, for reasons unrelated to the push.
#
# WHAT IT DOES INSTEAD. Two four-line fixtures, compiled with the toolchain on
# PATH and NO flags, so the default lane is what is exercised:
#
#   * `honest.rs`  — bounded-integer contracts that hold. MUST exit 0 with N>0
#                    obligations proved and 0 failed, and MUST NOT print the
#                    "compiled WITHOUT Trust verification" note (verification
#                    was on).
#   * `violated.rs` — the same shape with a postcondition the body breaks. MUST
#                    exit non-zero with at least one failed/refuted obligation.
#
# The violated twin is the mutation proof: a verifier that rubber-stamps would
# pass `honest.rs` and ALSO pass `violated.rs`, and this lane fails on the
# second. A verifier that is silently off prints the vanilla note on the first,
# and this lane fails on that. Both fixtures were measured on the shipped pack
# on 2026-09-14 (honest: `4 proved, 0 failed`, exit 0; violated: refuted by
# trust-mc PDR, exit 1) and take ~2-4 s each, dominated by kernel startup.
#
# WHAT IT DOES NOT CLAIM. Two fixtures are not coverage. This lane says the
# verifier on this machine executes, decides, and refuses — nothing about what
# fraction of real code it proves. The strict-fragment crates remain the
# coverage instrument; this is the pulse check that would have caught a
# toolchain whose verifier stopped answering.
set -euo pipefail

TRUSTC="${TRUSTC:-trustc}"
if ! command -v "$TRUSTC" >/dev/null 2>&1; then
  echo "FAIL: no trustc on PATH (TRUSTC=$TRUSTC). This lane runs the verifier; it cannot pass without one." >&2
  echo "      Fix: put the Trust toolchain on PATH (atpkg's shell.d hook, or build/host/stage1/bin), or set TRUSTC." >&2
  exit 2
fi
if ! "$TRUSTC" --version 2>/dev/null | grep -q "trustc"; then
  echo "FAIL: $TRUSTC --version does not name trustc: $("$TRUSTC" --version 2>&1 | head -1)" >&2
  echo "      A stock rustc under this name would accept the fixtures and prove nothing." >&2
  exit 2
fi

WORK="$(mktemp -d "${TMPDIR:-/tmp}/trust-verifier-executes.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

# Protocol 1 admits this synchronous lane but carries no GNU scheduler. A
# source-built owner lends the compiler one execution through the existing
# zero-token jobserver API. Every existing advertisement (even empty/broken)
# and every other custody locator follows the original direct launch unchanged.
LENDER=""
loan_owed=0
if [ "${BUILD_SLOT_CPU_PROTOCOL:-}" = 1 ] && [ "${BUILD_SLOT_HELD:-}" = 1 ]; then
  loan_owed=1
  for name in CARGO_JOBSERVER_HANDOFF TRUST_CPU_HANDOFF TRUST_FIXED_CLAIM_HANDOFF_V1 \
      CARGO_MAKEFLAGS MAKEFLAGS MFLAGS TRUST_CPU_IMPLICIT_FD BUILD_SLOT_FENCE_FDS \
      ATERM_SDK_LEASE_V3 ATERM_WORKLOAD_CPU_FDS_V1 ATERM_WORKLOAD_HOST_STORE_FD_V1 \
      ATERM_WORKLOAD_HOST_CONTROL_FDS_V1; do
    if printenv "$name" >/dev/null 2>&1; then loan_owed=0; fi
  done
fi
if [ "$loan_owed" -eq 1 ]; then
  ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
  TARGO="${TARGO:-targo}"
  PYTHON_BIN=""
  for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1; then PYTHON_BIN="$candidate"; break; fi
  done
  if [ -z "$PYTHON_BIN" ]; then
    echo "FAIL: Python is required to bind the source-built execution owner." >&2
    exit 2
  fi
  # Only this scheduling helper is built unverified. The two compiler commands
  # below retain their exact default verification policy and fixture arguments.
  "$TARGO" --unverified build --locked --manifest-path "$ROOT/src/jobserver_utils/Cargo.toml" \
    --example lend_execution --message-format=json >"$WORK/lender-build.jsonl"
  LENDER="$("$PYTHON_BIN" - "$WORK/lender-build.jsonl" "$ROOT/src/jobserver_utils/examples/lend_execution.rs" <<'PY'
import json
from pathlib import Path
import sys
source = Path(sys.argv[2]).resolve(strict=True)
found = set()
for line in Path(sys.argv[1]).read_text().splitlines():
    row = json.loads(line)
    target = row.get("target", {})
    if (row.get("reason") == "compiler-artifact"
            and target.get("name") == "lend_execution"
            and "example" in target.get("kind", [])
            and Path(target.get("src_path", "")).resolve() == source
            and isinstance(row.get("executable"), str)):
        binary = Path(row["executable"])
        if binary.is_symlink() or not binary.is_file():
            raise SystemExit("execution owner is not a regular source-built artifact")
        found.add(str(binary.resolve(strict=True)))
if len(found) != 1:
    raise SystemExit("build did not identify one exact execution owner")
print(found.pop())
PY
)"
fi
run_trustc() {
  if [ -n "$LENDER" ]; then "$LENDER" "$TRUSTC" "$@"; else "$TRUSTC" "$@"; fi
}

cat >"$WORK/honest.rs" <<'EOF'
#![crate_type = "lib"]
pub fn f(x: i32) -> i32 requires x > 0 && x < 1000 ensures result > 0 { x + 1 }
pub fn g(a: u8) -> u8 requires a < 100 ensures result < 200 { a * 2 }
EOF
cat >"$WORK/violated.rs" <<'EOF'
#![crate_type = "lib"]
pub fn f(x: i32) -> i32 requires x > 0 && x < 1000 ensures result > 0 { x - 1000 }
EOF

fail=0

# --- honest: must prove, must not be vanilla ---------------------------------
set +e
honest_out="$(run_trustc --edition 2021 --emit=metadata -o "$WORK/honest.rmeta" "$WORK/honest.rs" 2>&1)"
honest_rc=$?
set -e
honest_summary="$(printf '%s\n' "$honest_out" | grep -E 'Trust verification: [0-9]+ proved' | tail -1 || true)"
honest_proved="$(printf '%s\n' "$honest_summary" | sed -nE 's/.*Trust verification: ([0-9]+) proved, ([0-9]+) failed.*/\1/p' || true)"
honest_failed="$(printf '%s\n' "$honest_summary" | sed -nE 's/.*Trust verification: ([0-9]+) proved, ([0-9]+) failed.*/\2/p' || true)"
if [ "$honest_rc" -ne 0 ]; then
  echo "FAIL: honest.rs exited $honest_rc (expected 0). The verifier refused a contract that holds." >&2
  printf '%s\n' "$honest_out" | tail -12 >&2; fail=1
elif [ -z "$honest_proved" ] || [ "$honest_proved" -lt 1 ] || [ "${honest_failed:-1}" -ne 0 ]; then
  echo "FAIL: honest.rs exited 0 but reported '${honest_summary:-<no summary line>}' (expected N>0 proved, 0 failed)." >&2
  echo "      An exit 0 with nothing proved is a verifier that did not run." >&2; fail=1
elif printf '%s\n' "$honest_out" | grep -q 'compiled WITHOUT Trust verification'; then
  echo "FAIL: honest.rs printed the vanilla note — verification was OFF for this compile." >&2
  echo "      Something in this environment (TRUST_NO_VERIFY, a config, an RUSTFLAGS) disabled it." >&2; fail=1
else
  echo "ok   honest.rs: exit 0, $honest_summary"
fi

# --- violated: must be refused, with a failed/refuted row ----------------------
set +e
violated_out="$(run_trustc --edition 2021 --emit=metadata -o "$WORK/violated.rmeta" "$WORK/violated.rs" 2>&1)"
violated_rc=$?
set -e
violated_summary="$(printf '%s\n' "$violated_out" | grep -E 'Trust verification: [0-9]+ proved' | tail -1 || true)"
violated_failed="$(printf '%s\n' "$violated_summary" | sed -nE 's/.*Trust verification: ([0-9]+) proved, ([0-9]+) failed.*/\2/p' || true)"
violated_unknown="$(printf '%s\n' "$violated_summary" | sed -nE 's/.*([0-9]+) unknown.*/\1/p' || true)"
if [ "$violated_rc" -eq 0 ]; then
  echo "FAIL: violated.rs exited 0 — the verifier ACCEPTED a postcondition the body breaks." >&2
  echo "      This is the rubber-stamp failure this lane exists to catch." >&2
  printf '%s\n' "$violated_out" | tail -8 >&2; fail=1
elif [ "${violated_failed:-0}" -lt 1 ] && [ "${violated_unknown:-0}" -lt 1 ]; then
  echo "FAIL: violated.rs exited $violated_rc but reported '${violated_summary:-<no summary line>}' (expected >=1 failed or unknown)." >&2
  echo "      A non-zero exit with no refuted row is a compile error, not a verdict." >&2
  printf '%s\n' "$violated_out" | grep -E '^error' | head -3 >&2; fail=1
else
  echo "ok   violated.rs: exit $violated_rc, $violated_summary"
fi

if [ "$fail" -ne 0 ]; then
  echo "VERIFIER-EXECUTES: RED" >&2
  exit 1
fi
echo "VERIFIER-EXECUTES: GREEN — the default lane proved an honest contract and refused a violated one ($("$TRUSTC" --version 2>&1 | head -1))"
