#!/bin/bash
# Smoke test: the basic contracts example crate type-checks with targo and
# produces a JSON verification report through the public verifier CLI.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CRATE_DIR="$TRUST_ROOT/examples/contracts/basic-contracts"

echo "=== tRust E2E Test: basic contracts proof corpus smoke ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
}

# This e2e exercises the REPO-LOCAL stage2 toolchain by construction (see
# find_standalone_targo below), which is developer-owned: opt in to the
# dev-toolchain launcher exemption (TRUST_ALLOW_UNSEALED_DEV_LAUNCHER widens
# only toolchain-binary provenance authority — never a proof verdict; unset,
# release behavior is byte-identical and a user-owned tree fails closed at
# the verified-launcher pathname check).
run_trust_targo() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        TRUST_ALLOW_UNSEALED_DEV_LAUNCHER=1 \
        "$TRUST_TARGO" "$@"
}

run_public_cli() {
    env -u TRUSTC -u RUSTUP_TOOLCHAIN -u RUSTC -u RUSTDOC \
        -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER \
        -u CARGO_BUILD_RUSTC -u CARGO_BUILD_RUSTDOC \
        -u CARGO_BUILD_RUSTC_WRAPPER -u CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER \
        TRUST_ALLOW_UNSEALED_DEV_LAUNCHER=1 \
        "$TRUST_TARGO" trust "$@"
}

if [ ! -f "$CRATE_DIR/Cargo.toml" ]; then
    fail_setup "example crate manifest not found: $CRATE_DIR/Cargo.toml"
fi

# The Cargo target dir joins the verified runtime-library closure, whose
# per-component authority check rejects sticky world-writable roots like
# /tmp (mode 1777) even under the dev-launcher exemption. Keep the scratch
# tree inside the repo's own build directory (self-owned, non-world-writable).
mkdir -p "$TRUST_ROOT/build/tmp"
TMP_DIR="$(mktemp -d "$TRUST_ROOT/build/tmp/basic_contracts_smoke_XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

find_standalone_targo() {
    local candidate
    while IFS= read -r candidate; do
        if [ -x "$candidate" ] && [ -x "$(dirname "$candidate")/trustc" ]; then
            printf '%s\n' "$candidate"
            return 0
        fi
    done < <(find "$TRUST_ROOT/build" -path "*/stage2/bin/targo" -type f -perm -111 -print 2>/dev/null | sort -r)

    return 1
}

if ! TRUST_TARGO="$(find_standalone_targo)"; then
    fail_setup "repo-local stage2 Trust targo/trustc not found under build/*/stage2/bin. Run ./x.py build --stage 2."
fi
TRUSTC_BIN="$(dirname "$TRUST_TARGO")/trustc"
if ! run_trust_targo --version >/dev/null 2>&1; then
    fail_setup "repo-local stage2 Trust targo is not runnable: $TRUST_TARGO"
fi

echo "Using targo:       $TRUST_TARGO"
echo "Using trustc:       $TRUSTC_BIN"
echo "Crate:             $CRATE_DIR"
echo

echo "--- standalone targo check"
CHECK_STDOUT="$TMP_DIR/cargo_check.stdout"
CHECK_STDERR="$TMP_DIR/cargo_check.stderr"
check_exit=0
(
    cd "$CRATE_DIR"
    CARGO_TARGET_DIR="$TMP_DIR/target" run_trust_targo --unverified check --locked >"$CHECK_STDOUT" 2>"$CHECK_STDERR"
) || check_exit=$?

if [ "$check_exit" -ne 0 ]; then
    echo "FAIL: basic-contracts targo check exited with status $check_exit"
    echo "--- targo check stdout"
    cat "$CHECK_STDOUT"
    echo "--- targo check stderr"
    cat "$CHECK_STDERR"
    exit 1
fi
echo "  PASS: basic-contracts targo check succeeded"
echo

echo "--- targo trust check --format json"
if ! run_public_cli --help >/dev/null 2>&1; then
    fail_setup "repo-local stage2 targo does not expose the canonical \`targo trust\` subcommand"
fi

TRUST_JSON="$TMP_DIR/trust_check.json"
TRUST_STDERR="$TMP_DIR/trust_check.stderr"
trust_exit=0
(
    cd "$CRATE_DIR"
    CARGO_TARGET_DIR="$TMP_DIR/target" run_public_cli check --format json >"$TRUST_JSON" 2>"$TRUST_STDERR"
) || trust_exit=$?

if [ "$trust_exit" -gt 1 ]; then
    echo "FAIL: targo trust check --format json exited with unexpected status $trust_exit"
    echo "--- targo trust stderr"
    cat "$TRUST_STDERR"
    echo "--- targo trust stdout"
    cat "$TRUST_JSON"
    exit 1
fi

if grep -q "TRUST_JSON:" "$TRUST_JSON" "$TRUST_STDERR"; then
    fail_test "targo trust check leaked raw TRUST_JSON transport"
fi
if grep -q "falling back to standalone source analysis" "$TRUST_STDERR"; then
    echo "--- targo trust stderr"
    cat "$TRUST_STDERR"
    fail_setup "standalone Trust toolchain is visible, but targo trust fell back to source inventory"
fi
if ! grep -q "using native compiler" "$TRUST_STDERR"; then
    echo "--- targo trust stderr"
    cat "$TRUST_STDERR"
    fail_setup "standalone Trust toolchain is visible, but targo trust did not report native compiler verification"
fi

if ! command -v python3 >/dev/null 2>&1; then
    fail_setup "python3 not found on PATH; needed to validate targo trust JSON output"
fi

if ! python3 - "$TRUST_JSON" "$trust_exit" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)
trust_exit = int(sys.argv[2])

functions = report.get("functions")
if not isinstance(functions, list) or not functions:
    raise AssertionError("expected at least one reported function")

names = {
    str(entry.get("function", "")).split("::")[-1]
    for entry in functions
    if isinstance(entry, dict)
}
expected = {"divide_exact", "abs_total", "get_at"}
missing = sorted(expected - names)
if missing:
    raise AssertionError("missing expected contract functions: " + ", ".join(missing))

summary = report.get("summary")
if not isinstance(summary, dict):
    raise AssertionError("missing summary object")
if summary.get("total_obligations", 0) < 1:
    raise AssertionError("expected at least one verification obligation")

# Corpus-declared refutation ledger. These (function, obligation) pairs are
# GENUINELY TRUE counterexamples against the corpus AS AUTHORED (see
# examples/contracts/basic-contracts/README.md). Keying on the exact
# obligation, not just the function, is deliberate: the fixture's ORIGINAL
# refutation (divide_exact's false `ensures`) silently demoted to `unknown`
# during the 2026-07-20 solver work, so a function-granular pin would have
# stayed green while the refutation oracle quietly became a coverage-gap
# oracle. A `proved` verdict on any ledger row is a SOUNDNESS bug; a row that
# vanishes or demotes below `failed` is a regression of the oracle itself. A
# row leaves this ledger only in the same commit as the source change that
# legitimizes it.
MUST_NEVER_BE_PROVED = {
    # i32::MIN / -1 overflows and panics; `requires denominator != 0` admits it.
    ("divide_exact", "arithmetic overflow (Div)"),
}

failures = set()
fail_closed = {}
proved = set()
for entry in functions:
    if not isinstance(entry, dict):
        continue
    short_name = str(entry.get("function", "")).split("::")[-1]
    for obligation in entry.get("obligations") or []:
        if not isinstance(obligation, dict):
            continue
        outcome = obligation.get("outcome")
        status = outcome.get("status") if isinstance(outcome, dict) else outcome
        key = (short_name, obligation.get("description"))
        if status == "failed":
            failures.add(key)
        if status == "proved":
            proved.add(key)
        if status in {"failed", "unknown", "runtime_checked"}:
            fail_closed[key] = status

# (1) No ledger row may EVER be proved — independent of the exit code.
false_proofs = sorted(MUST_NEVER_BE_PROVED & proved)
if false_proofs:
    raise AssertionError(f"verifier claims a PROOF of a true counterexample: {false_proofs!r}")

# (2) Every ledger row must still be OBSERVED and HARD-refuted. A vanished row
# is as bad as a false proof, and a `failed` demoted to `unknown` means the
# corpus stopped being a refutation oracle — which stays green while the
# verifier regresses.
for key in sorted(MUST_NEVER_BE_PROVED):
    status = fail_closed.get(key)
    if status is None:
        raise AssertionError(f"refutation ledger row vanished from the report: {key!r}")
    if status != "failed":
        raise AssertionError(
            f"refutation ledger row is no longer hard-refuted: {key!r} -> {status!r}"
        )

if trust_exit == 0:
    if failures:
        raise AssertionError(f"native report succeeded but still contains failures: {sorted(failures)!r}")
    # A ledger row is a hard failure, so exit 0 is unreachable while the ledger
    # is non-empty; guard it explicitly rather than relying on that coupling.
    if MUST_NEVER_BE_PROVED:
        raise AssertionError("exit 0 with a non-empty refutation ledger is impossible")
elif trust_exit == 1:
    # Per-function attribution: a count-only oracle would stay green even if
    # the verifier silently stopped emitting a hard function's rows entirely.
    required_fail_closed_functions = {"divide_exact", "get_at"}
    observed_fail_closed_functions = {name for name, _ in fail_closed}
    missing_functions = sorted(required_fail_closed_functions - observed_fail_closed_functions)
    if missing_functions or not failures:
        raise AssertionError(
            "native compat contract fail-closed set changed: "
            f"missing_functions={missing_functions!r}, failures={sorted(failures)!r}, "
            f"statuses={fail_closed!r}"
        )
else:
    raise AssertionError(f"unexpected trust exit status {trust_exit}")
PY
then
    echo "FAIL: targo trust JSON report did not match the expected proof-corpus schema"
    echo "--- targo trust stdout"
    cat "$TRUST_JSON"
    echo "--- targo trust stderr"
    cat "$TRUST_STDERR"
    exit 1
fi

if [ "$trust_exit" -eq 1 ]; then
    echo "  PASS: native compiler verification keeps trust-spec compat preconditions fail-closed/runtime-checked"
else
    echo "  PASS: native compiler verification discharged the basic contracts corpus"
fi

echo "  PASS: targo trust JSON report includes expected basic contract functions"
echo

echo "--- targo trust check --standalone --format json"
STANDALONE_JSON="$TMP_DIR/standalone.json"
STANDALONE_STDERR="$TMP_DIR/standalone.stderr"
standalone_exit=0
(
    cd "$CRATE_DIR"
    CARGO_TARGET_DIR="$TMP_DIR/target" run_public_cli check --standalone --format json >"$STANDALONE_JSON" 2>"$STANDALONE_STDERR"
) || standalone_exit=$?

if [ "$standalone_exit" -ne 0 ]; then
    echo "FAIL: targo trust check --standalone --format json exited with status $standalone_exit"
    echo "--- targo trust standalone stderr"
    cat "$STANDALONE_STDERR"
    echo "--- targo trust standalone stdout"
    cat "$STANDALONE_JSON"
    exit 1
fi

if ! python3 - "$STANDALONE_JSON" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

if report.get("mode") != "source-audit":
    raise AssertionError(f"expected source-audit mode, got {report.get('mode')!r}")
if report.get("proof_authority") != "none" or report.get("compiler_verification_performed") is not False:
    raise AssertionError("standalone source audit must declare no proof authority")
if report.get("files_analyzed", 0) < 1:
    raise AssertionError("standalone report should analyze at least one file")
if report.get("public_functions", 0) < 5:
    raise AssertionError("standalone report should inventory public crate APIs")
if report.get("specified_functions", 0) < 3:
    raise AssertionError("standalone report should see trust-spec compatibility attrs")
if report.get("failed", 0) != 0:
    raise AssertionError("standalone compatibility inventory should not report failed proofs")

functions = report.get("functions")
if not isinstance(functions, list) or not functions:
    raise AssertionError("standalone report should include functions")

by_name = {entry.get("name"): entry for entry in functions if isinstance(entry, dict)}
for name in ["divide_exact", "abs_total", "get_at"]:
    if name not in by_name:
        raise AssertionError(f"standalone report missing expected function {name}")
if not by_name["divide_exact"].get("has_requires") or not by_name["divide_exact"].get("has_ensures"):
    raise AssertionError("standalone report should preserve divide_exact trust-spec attrs")
if not by_name["get_at"].get("has_requires") or not by_name["get_at"].get("has_ensures"):
    raise AssertionError("standalone report should preserve get_at trust-spec attrs")
if by_name["abs_total"].get("has_requires") or not by_name["abs_total"].get("has_ensures"):
    raise AssertionError("standalone report should preserve abs_total ensures-only contract")
PY
then
    echo "FAIL: targo trust standalone JSON did not preserve trust-spec compatibility attrs"
    echo "--- targo trust standalone stdout"
    cat "$STANDALONE_JSON"
    echo "--- targo trust standalone stderr"
    cat "$STANDALONE_STDERR"
    exit 1
fi

echo "  PASS: standalone compatibility inventory preserves trust-spec attrs"
echo
echo "=== basic contracts proof corpus smoke: PASS ==="
