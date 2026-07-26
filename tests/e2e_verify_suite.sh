#!/bin/bash
# E2E Verifier-Example Regression Diagnostic
#
# Runs all examples/verify_*.rs programs through the Trust verification
# pipeline and checks that each produces its expected result.
#
# Every declared status is exact. `PROVED` requires a matching proved row,
# `FAILED` requires a matching failed row, and `ABSENT` is a distinct generation
# assertion requiring the structured report to contain no row of that VcKind.
#
# This script is a fail-closed regression diagnostic, not proof or release
# evidence. Its shell/Python/Git startup authority and source/tool provenance
# are not independently authenticated. A successful exit means only that the
# observed example outputs satisfied the declared kind/status assertions during
# this run; unmentioned properties and output rows are outside its claim.
#
# Usage:
#   ./tests/e2e_verify_suite.sh              # run all
#   ./tests/e2e_verify_suite.sh verify_div_zero  # run one (substring match)
#   ./tests/e2e_verify_suite.sh --self-test-complete-corpus-diagnostic
#
# Prerequisites:
#   Stage2 trustc build (./x.py build --stage 2 compiler/rustc library/std) plus
#   default-on Trust verification. Missing native verification is a setup
#   failure, not a syntax-only pass.
#   Python 3 (for strict parsing of structured verifier envelopes) and
#   timeout/gtimeout (macOS: coreutils).
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -uo pipefail

complete_corpus_diagnostic_self_test() {
    local scratch
    scratch=$(mktemp -d /tmp/trust_verify_complete_diagnostic_XXXXXX) || return 1
    trap "rm -rf '$scratch'" EXIT HUP INT TERM

    mkdir -p "$scratch/tests" "$scratch/examples" "$scratch/build/host/stage2/bin"
    cp "$0" "$scratch/tests/e2e_verify_suite.sh"
    chmod +x "$scratch/tests/e2e_verify_suite.sh"

    cat >"$scratch/examples/verify_ok.rs" <<'RUST'
// Expected: DivisionByZero FAILED
fn main() {}
RUST
    cat >"$scratch/examples/verify_absent.rs" <<'RUST'
// Expected: FloatDivisionByZero ABSENT
fn main() {}
RUST
    cat >"$scratch/examples/verify_skipped.rs" <<'RUST'
fn main() {}
RUST
    cat >"$scratch/build/host/stage2/bin/trustc" <<'SH'
#!/bin/bash
set -u
root="$(cd "$(dirname "$0")/../../../.." && pwd)"
if [ "${1:-}" = "-vV" ]; then
    echo "trustc 0.1.0-trust"
    echo "binary: trustc"
    echo "commit-hash: $(git -C "$root" rev-parse HEAD)"
    echo "host: test-complete-corpus-diagnostic"
    exit 0
fi
output=""
source=""
session=""
while [ "$#" -gt 0 ]; do
    if [ "$1" = "-o" ] && [ "$#" -ge 2 ]; then
        output="$2"
        shift 2
    else
        case "$1" in
            *.rs) source="$1" ;;
            trust-verify-session=*) session="${1#trust-verify-session=}" ;;
        esac
        shift
    fi
done
[ -z "$output" ] || : >"$output"
crate="$(basename "${source:-verify_ok.rs}" .rs)"
if [ "$crate" != "verify_absent" ]; then
    echo "=== Trust Verification Report ($crate) ===" >&2
fi
case "$crate" in
    verify_absent_violation)
        printf 'TRUST_JSON:{"type":"function_result","function":"%s::main","crate_name":"%s","verification_session":"%s","results":[{"obligation_id":"obl-1","kind":"float_division_by_zero","description":"float division by zero","location":{"file":"fixture.rs","line_start":1,"column_start":1,"line_end":1,"column_end":2},"outcome":"unknown"}],"total":1}\n' "$crate" "$crate" "$session" >&2
        echo "note: Trust [float_division_by_zero]: UNKNOWN" >&2
        ;;
    verify_absent)
        printf 'TRUST_JSON:{"type":"function_result","function":"%s::main","crate_name":"%s","verification_session":"%s","results":[{"kind":"no_obligations","description":"no obligations","outcome":"proved"}],"total":1}\n' "$crate" "$crate" "$session" >&2
        ;;
    verify_absent_no_envelope)
        echo "note: no structured verifier envelope was emitted" >&2
        ;;
    verify_wrong_status)
        printf 'TRUST_JSON:{"type":"function_result","function":"%s::main","crate_name":"%s","verification_session":"%s","results":[{"obligation_id":"obl-1","kind":"divzero","description":"division by zero","location":{"file":"fixture.rs","line_start":1,"column_start":1,"line_end":1,"column_end":2},"outcome":"runtime_checked"}],"total":1}\n' "$crate" "$crate" "$session" >&2
        echo "note: Trust [divzero]: division by zero -- RUNTIME-CHECKED" >&2
        ;;
    *)
        printf 'TRUST_JSON:{"type":"function_result","function":"%s::main","crate_name":"%s","verification_session":"%s","results":[{"obligation_id":"obl-1","kind":"divzero","description":"division by zero","location":{"file":"fixture.rs","line_start":1,"column_start":1,"line_end":1,"column_end":2},"outcome":"failed"}],"total":1}\n' "$crate" "$crate" "$session" >&2
        echo "note: Trust [divzero]: division by zero -- FAILED" >&2
        ;;
esac
exit 1
SH
    chmod +x "$scratch/build/host/stage2/bin/trustc"

    git -C "$scratch" init -q
    git -C "$scratch" config user.name "Trust complete-corpus diagnostic self-test"
    git -C "$scratch" config user.email "complete-corpus-diagnostic-self-test@invalid"
    git -C "$scratch" add .
    git -C "$scratch" commit -qm "complete-corpus diagnostic fixture"

    local output
    if ! output=$(bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: selected-example diagnostic should permit a mixed pass/skip run" >&2
        echo "$output" >&2
        return 1
    fi
    if output=$(TRUST_RELEASE_GATE=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: retired TRUST_RELEASE_GATE was accepted" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "TRUST_RELEASE_GATE is retired" <<<"$output"; then
        echo "FAIL: retired release-evidence environment did not explain the diagnostic replacement" >&2
        echo "$output" >&2
        return 1
    fi
    if output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: complete-corpus diagnostic accepted a skipped example" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "complete-corpus diagnostic forbids skipped examples" <<<"$output"; then
        echo "FAIL: complete-corpus diagnostic did not report the skip blocker" >&2
        echo "$output" >&2
        return 1
    fi
    if output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" verify_ok 2>&1); then
        echo "FAIL: complete-corpus diagnostic accepted a filtered corpus" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "complete-corpus diagnostic must run the complete corpus" <<<"$output"; then
        echo "FAIL: complete-corpus diagnostic did not report the filter blocker" >&2
        echo "$output" >&2
        return 1
    fi

    rm "$scratch/examples/verify_skipped.rs"
    git -C "$scratch" add -u
    git -C "$scratch" commit -qm "remove skipped fixture"
    if ! output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: complete-corpus diagnostic rejected a clean complete corpus" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "not proof or release evidence" <<<"$output"; then
        echo "FAIL: successful complete-corpus diagnostic omitted its non-evidence boundary" >&2
        echo "$output" >&2
        return 1
    fi

    cat >"$scratch/examples/verify_absent_violation.rs" <<'RUST'
// Expected: FloatDivisionByZero ABSENT
fn main() {}
RUST
    git -C "$scratch" add examples/verify_absent_violation.rs
    git -C "$scratch" commit -qm "add prohibited absent-kind fixture"
    if output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: complete-corpus diagnostic accepted a prohibited ABSENT kind" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "Expected FloatDivisionByZero ABSENT" <<<"$output"; then
        echo "FAIL: complete-corpus diagnostic did not report the violated ABSENT assertion" >&2
        echo "$output" >&2
        return 1
    fi

    rm "$scratch/examples/verify_absent_violation.rs"
    cat >"$scratch/examples/verify_absent_no_envelope.rs" <<'RUST'
// Expected: FloatDivisionByZero ABSENT
fn main() {}
RUST
    git -C "$scratch" add -A examples
    git -C "$scratch" commit -qm "replace prohibited kind with missing envelope"
    if output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: complete-corpus diagnostic accepted ABSENT without structured results" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "structured expectation matching requires a valid verifier results envelope" <<<"$output"; then
        echo "FAIL: complete-corpus diagnostic did not report the missing ABSENT envelope" >&2
        echo "$output" >&2
        return 1
    fi

    rm "$scratch/examples/verify_absent_no_envelope.rs"
    cat >"$scratch/examples/verify_wrong_status.rs" <<'RUST'
// Expected: DivisionByZero FAILED
fn main() {}
RUST
    git -C "$scratch" add -A examples
    git -C "$scratch" commit -qm "replace missing envelope with wrong exact status"
    if output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: complete-corpus diagnostic treated RUNTIME-CHECKED as FAILED" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "Expected DivisionByZero FAILED but not found" <<<"$output"; then
        echo "FAIL: complete-corpus diagnostic did not report the exact-status mismatch" >&2
        echo "$output" >&2
        return 1
    fi

    rm "$scratch/examples/verify_wrong_status.rs"
    cat >"$scratch/examples/verify_malformed.rs" <<'RUST'
// Expected: deref NOT proved (prose is not an accepted structured status)
fn main() {}
RUST
    git -C "$scratch" add -A examples
    git -C "$scratch" commit -qm "replace prohibited kind with malformed expectation"
    if output=$(TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 bash "$scratch/tests/e2e_verify_suite.sh" 2>&1); then
        echo "FAIL: complete-corpus diagnostic accepted a malformed Expected header" >&2
        echo "$output" >&2
        return 1
    fi
    if ! grep -q "malformed '// Expected:' assertion" <<<"$output"; then
        echo "FAIL: complete-corpus diagnostic did not report the malformed assertion" >&2
        echo "$output" >&2
        return 1
    fi

    echo "PASS: complete-corpus regression diagnostic enforces coverage, structured syntax, declared statuses, and ABSENT assertions (diagnostic only; not proof or release evidence)"
}

if [ "${1:-}" = "--self-test-complete-corpus-diagnostic" ]; then
    if [ "$#" -ne 1 ]; then
        echo "FAIL: --self-test-complete-corpus-diagnostic takes no additional arguments" >&2
        exit 2
    fi
    complete_corpus_diagnostic_self_test
    exit $?
fi

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXAMPLES_DIR="$TRUST_ROOT/examples"
FILTER="${1:-}"
COMPLETE_CORPUS_DIAGNOSTIC="${TRUST_COMPLETE_CORPUS_DIAGNOSTIC:-0}"
VERIFY_TIMEOUT_SECONDS=45

if [ "${TRUST_RELEASE_GATE+x}" = "x" ]; then
    echo "FAIL: TRUST_RELEASE_GATE is retired for e2e_verify_suite.sh; this lane is not release evidence. Use TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 for the complete-corpus regression diagnostic." >&2
    exit 2
fi

case "$COMPLETE_CORPUS_DIAGNOSTIC" in
    0|1)
        ;;
    *)
        echo "FAIL: TRUST_COMPLETE_CORPUS_DIAGNOSTIC must be 0 or 1 (got: $COMPLETE_CORPUS_DIAGNOSTIC)" >&2
        exit 2
        ;;
esac

if [ "$COMPLETE_CORPUS_DIAGNOSTIC" = "1" ] && [ -n "$FILTER" ]; then
    echo "FAIL: TRUST_COMPLETE_CORPUS_DIAGNOSTIC=1 complete-corpus diagnostic must run the complete corpus; filters are not allowed" >&2
    exit 2
fi

TIMEOUT_BIN="$(command -v timeout 2>/dev/null || command -v gtimeout 2>/dev/null || true)"
if [ -z "$TIMEOUT_BIN" ]; then
    echo "FAIL: this suite requires timeout or gtimeout (macOS: brew install coreutils)" >&2
    exit 2
fi

PYTHON_BIN="$(command -v python3 2>/dev/null || true)"
if [ -z "$PYTHON_BIN" ]; then
    echo "FAIL: this suite requires Python 3 to validate structured verifier output" >&2
    exit 2
fi

# Counters
TOTAL=0
PASSED=0
FAILED=0
SKIPPED=0
ERRORS=""

# --- Colors (if terminal supports them) ---
if [ -t 1 ]; then
    GREEN='\033[0;32m'
    RED='\033[0;31m'
    YELLOW='\033[0;33m'
    BOLD='\033[1m'
    RESET='\033[0m'
else
    GREEN=''
    RED=''
    YELLOW=''
    BOLD=''
    RESET=''
fi

# --- Locate canonical stage2 trustc ---
find_trustc() {
    local candidates=(
        "$TRUST_ROOT/build/host/stage2/bin/trustc"
        "$TRUST_ROOT/build/aarch64-unknown-linux-gnu/stage2/bin/trustc"
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage2/bin/trustc"
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2/bin/trustc"
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage2/bin/trustc"
    )
    for candidate in "${candidates[@]}"; do
        if [ -x "$candidate" ]; then
            echo "$candidate"
            return 0
        fi
    done
    return 1
}

validate_complete_corpus_diagnostic_context() {
    local trustc="$1"
    local head
    local status
    local identity
    local canonical
    local sha256

    if ! head=$(git -C "$TRUST_ROOT" rev-parse --verify 'HEAD^{commit}' 2>/dev/null) \
        || ! [[ "$head" =~ ^[0-9a-f]{40}$ ]]; then
        echo "FAIL: complete-corpus diagnostic could not resolve the observed Git commit" >&2
        return 1
    fi
    if ! status=$(git -C "$TRUST_ROOT" -c core.fsmonitor=false status \
        --porcelain=v1 --untracked-files=all --ignore-submodules=none 2>/dev/null); then
        echo "FAIL: complete-corpus diagnostic could not inspect the observed Git checkout" >&2
        return 1
    fi
    if [ -n "$status" ]; then
        echo "FAIL: complete-corpus diagnostic requires a clean checkout for its best-effort mutation guard" >&2
        return 1
    fi
    if ! canonical=$("$PYTHON_BIN" -c '
import os
import pathlib
import stat
import sys

root = pathlib.Path(sys.argv[1]).resolve(strict=True)
candidate = pathlib.Path(sys.argv[2])
leaf = candidate.lstat()
if stat.S_ISLNK(leaf.st_mode) or not stat.S_ISREG(leaf.st_mode):
    raise SystemExit(1)
path = candidate.resolve(strict=True)
relative = path.relative_to(root)
parts = relative.parts
if len(parts) != 5 or parts[0] != "build" or parts[2:] != ("stage2", "bin", "trustc"):
    raise SystemExit(1)
resolved = path.lstat()
if not stat.S_ISREG(resolved.st_mode) or resolved.st_uid != os.geteuid() or not os.access(path, os.X_OK):
    raise SystemExit(1)
print(path)
' "$TRUST_ROOT" "$trustc" 2>/dev/null); then
        echo "FAIL: complete-corpus diagnostic requires an owned, regular, executable build/<host>/stage2/bin/trustc leaf" >&2
        return 1
    fi
    if ! identity=$("$TIMEOUT_BIN" 10 "$canonical" -vV 2>&1); then
        echo "FAIL: complete-corpus diagnostic could not read stage2 trustc identity" >&2
        echo "$identity" >&2
        return 1
    fi
    if ! "$PYTHON_BIN" -c '
import sys
head = sys.argv[1]
lines = [line.strip() for line in sys.stdin.read().splitlines()]
binary = [line for line in lines if line.startswith("binary:")]
commits = [line for line in lines if line.startswith("commit-hash:")]
if binary != ["binary: trustc"] or commits != [f"commit-hash: {head}"]:
    raise SystemExit(1)
' "$head" <<<"$identity"; then
        echo "FAIL: complete-corpus diagnostic compiler identity must contain exactly one canonical binary and observed commit binding ($head)" >&2
        echo "$identity" >&2
        return 1
    fi
    if ! sha256=$("$PYTHON_BIN" -c '
import hashlib
import pathlib
import sys
path = pathlib.Path(sys.argv[1])
digest = hashlib.sha256()
with path.open("rb") as stream:
    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(chunk)
print(digest.hexdigest())
' "$canonical"); then
        echo "FAIL: complete-corpus diagnostic could not hash the exact stage2 trustc" >&2
        return 1
    fi

    DIAGNOSTIC_HEAD="$head"
    DIAGNOSTIC_TRUSTC_PATH="$canonical"
    DIAGNOSTIC_TRUSTC_SHA256="$sha256"
    DIAGNOSTIC_TRUSTC_IDENTITY="$identity"
}

validate_complete_corpus_diagnostic_unchanged() {
    local status
    local head
    local identity
    local sha256

    if ! head=$(git -C "$TRUST_ROOT" rev-parse --verify 'HEAD^{commit}' 2>/dev/null) \
        || [ "$head" != "$DIAGNOSTIC_HEAD" ]; then
        echo "FAIL: observed Git commit changed while the complete-corpus diagnostic was running" >&2
        return 1
    fi
    if ! status=$(git -C "$TRUST_ROOT" -c core.fsmonitor=false status \
        --porcelain=v1 --untracked-files=all --ignore-submodules=none 2>/dev/null) \
        || [ -n "$status" ]; then
        echo "FAIL: observed checkout changed while the complete-corpus diagnostic was running" >&2
        return 1
    fi
    if ! sha256=$("$PYTHON_BIN" -c '
import hashlib
import pathlib
import sys
digest = hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest()
print(digest)
' "$DIAGNOSTIC_TRUSTC_PATH") || [ "$sha256" != "$DIAGNOSTIC_TRUSTC_SHA256" ]; then
        echo "FAIL: exact stage2 trustc changed while the complete-corpus diagnostic was running" >&2
        return 1
    fi
    if ! identity=$("$TIMEOUT_BIN" 10 "$DIAGNOSTIC_TRUSTC_PATH" -vV 2>&1) \
        || [ "$identity" != "$DIAGNOSTIC_TRUSTC_IDENTITY" ]; then
        echo "FAIL: stage2 trustc identity changed while the complete-corpus diagnostic was running" >&2
        return 1
    fi
}

# --- Parse expected patterns from file header ---
# Reads the first "// Expected: ..." line plus any immediately following
# comment continuations that still contain expectation statuses.
# Returns a newline-separated list of tab-separated VcKind name and expected
# status pairs.
parse_expected_patterns() {
    local file="$1"
    local expected_block
    expected_block=$(
        awk '
            /^\/\/ Expected:/ {
                capture = 1
                sub(/^\/\/ Expected:[[:space:]]*/, "", $0)
                print
                next
            }
            capture && /^\/\/[[:space:]]+/ {
                if ($0 ~ /(FAILED|PROVED|RUNTIME-CHECKED|UNKNOWN|TIMEOUT|ABSENT)/) {
                    sub(/^\/\/[[:space:]]*/, "", $0)
                    print
                    next
                }
                exit
            }
            capture {
                exit
            }
        ' "$file"
    )
    if [ -z "$expected_block" ]; then
        echo ""
        return
    fi

    # Split on comma/AND separators, extract VcKind names and statuses.
    # Each token looks like "VcKindName FAILED" or "VcKindName(Op) PROVED"
    echo "$expected_block" | tr ',' '\n' | sed 's/ AND /\n/g' | while IFS= read -r token; do
        # Trim whitespace
        token=$(echo "$token" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        # Skip empty
        [ -z "$token" ] && continue
        # Extract the VcKind name (everything before status, trimmed) and the
        # first declared status. Never invent a default for prose-only text:
        # malformed Expected headers fail this diagnostic; they never acquire
        # a default FAILED claim.
        local vc_name
        vc_name=$(echo "$token" | sed -E 's/[[:space:]]*(FAILED|PROVED|RUNTIME-CHECKED|UNKNOWN|TIMEOUT|ABSENT).*//;s/[[:space:]]*$//')
        local expected_status
        expected_status=$(echo "$token" | sed -nE 's/.*[[:space:]](FAILED|PROVED|RUNTIME-CHECKED|UNKNOWN|TIMEOUT|ABSENT).*/\1/p' | head -n 1)
        if [ -z "$vc_name" ] || [ -z "$expected_status" ]; then
            printf '__INVALID__\t%s\n' "$token"
            continue
        fi
        printf '%s\t%s\n' "$vc_name" "$expected_status"
    done
}

tag_for_expected_kind() {
    case "$1" in
        DivisionByZero) echo "divzero" ;;
        RemainderByZero) echo "remzero" ;;
        IndexOutOfBounds) echo "bounds" ;;
        SliceBoundsCheck) echo "slice" ;;
        Assertion) echo "assert" ;;
        Precondition) echo "precond" ;;
        Postcondition) echo "postcond" ;;
        Unreachable) echo "unreach" ;;
        CastOverflow) echo "cast" ;;
        NegationOverflow) echo "negation" ;;
        FloatDivisionByZero) echo "float_division_by_zero" ;;
        FloatOverflowToInfinity|FloatOverflowToInfinity\(*\)) echo "float_overflow_to_infinity" ;;
        ArithmeticOverflow\(Add\)) echo "overflow:add" ;;
        ArithmeticOverflow\(Sub\)) echo "overflow:sub" ;;
        ArithmeticOverflow\(Mul\)) echo "overflow:mul" ;;
        ArithmeticOverflow\(Div\)) echo "overflow" ;;
        ShiftOverflow\(Shl\)) echo "shift:left" ;;
        ShiftOverflow\(Shr\)) echo "shift:right" ;;
        *) echo "" ;;
    esac
}

op_for_expected_kind() {
    case "$1" in
        FloatOverflowToInfinity\(Add\)|ArithmeticOverflow\(Add\)) echo "Add" ;;
        ArithmeticOverflow\(Sub\)) echo "Sub" ;;
        ArithmeticOverflow\(Mul\)) echo "Mul" ;;
        ArithmeticOverflow\(Div\)) echo "Div" ;;
        ShiftOverflow\(Shl\)) echo "Shl" ;;
        ShiftOverflow\(Shr\)) echo "Shr" ;;
        *) echo "" ;;
    esac
}

structured_results_envelope_present() {
    local output="$1"
    local session="$2"
    "$PYTHON_BIN" -c '
import json
import sys

session = sys.argv[1]
found = False
for line in sys.stdin:
    stripped = line.lstrip()
    if not stripped.startswith("TRUST_JSON:"):
        continue
    try:
        value = json.loads(stripped.removeprefix("TRUST_JSON:"))
    except (json.JSONDecodeError, TypeError):
        raise SystemExit(1)
    if not isinstance(value, dict):
        raise SystemExit(1)
    observed_session = value.get("verification_session")
    if observed_session is not None and observed_session != session:
        raise SystemExit(1)
    results = value.get("results")
    if results is None:
        continue
    if not isinstance(results, list) or value.get("verification_session") != session:
        raise SystemExit(1)
    if value.get("total") != len(results):
        raise SystemExit(1)
    for row in results:
        if not isinstance(row, dict):
            raise SystemExit(1)
        kind = row.get("kind")
        outcome = row.get("outcome")
        if not isinstance(kind, str) or not kind or outcome not in {
            "proved", "failed", "unknown", "timeout", "runtime_checked", "skipped"
        }:
            raise SystemExit(1)
        if kind != "no_obligations":
            if not isinstance(row.get("obligation_id"), str) or not row["obligation_id"]:
                raise SystemExit(1)
            if not isinstance(row.get("location"), dict):
                raise SystemExit(1)
    found = True
raise SystemExit(0 if found else 1)
' "$session" <<<"$output"
}

structured_result_satisfies() {
    local output="$1"
    local vc_name="$2"
    local expected_status="$3"
    local match_mode="${4:-any}"
    local session="$5"
    local tag
    local op
    tag=$(tag_for_expected_kind "$vc_name")
    op=$(op_for_expected_kind "$vc_name")
    [ -n "$tag" ] || return 1
    "$PYTHON_BIN" -c '
import json
import sys

tag = sys.argv[1]
status = sys.argv[2]
op = sys.argv[3]
match_mode = sys.argv[4]
session = sys.argv[5]
rows = []
for line in sys.stdin:
    stripped = line.lstrip()
    if not stripped.startswith("TRUST_JSON:"):
        continue
    try:
        value = json.loads(stripped.removeprefix("TRUST_JSON:"))
    except (json.JSONDecodeError, TypeError):
        continue
    results = value.get("results") if isinstance(value, dict) else None
    if isinstance(results, list) and value.get("verification_session") == session:
        rows.extend(row for row in results if isinstance(row, dict))

matching = []
for row in rows:
    if str(row.get("kind", "")).lower() != tag.lower():
        continue
    if op:
        description = str(row.get("description", "")).lower()
        typed_kind = json.dumps(row.get("typed_kind"), sort_keys=True).lower()
        typed_op = f"\"op\": \"{op.lower()}\""
        if f"({op.lower()})" not in description and typed_op not in typed_kind:
            continue
    matching.append(row)
if status == "ABSENT":
    raise SystemExit(0 if not matching else 1)
wanted = status.lower().replace("-", "_")
outcomes = [str(row.get("outcome", "")).lower().replace("-", "_") for row in matching]
if match_mode == "all":
    raise SystemExit(0 if outcomes and all(outcome == wanted for outcome in outcomes) else 1)
raise SystemExit(
    0
    if any(outcome == wanted for outcome in outcomes)
    else 1
)
' "$tag" "$expected_status" "$op" "$match_mode" "$session" <<<"$output"
}

# --- Determine if file is a safe variant ---
is_safe_variant() {
    local basename
    basename=$(basename "$1" .rs)
    case "$basename" in
        *_safe) return 0 ;;
        *) return 1 ;;
    esac
}

# --- Clear TRUST_DISABLE_* environment variables ---
unset_trust_disables() {
    local var
    for var in $(env | grep '^TRUST_DISABLE_' | cut -d= -f1); do
        unset "$var"
    done
}

# --- Run a single test ---
run_test() {
    local file="$1"
    local trustc="$2"
    local basename
    basename=$(basename "$file" .rs)

    TOTAL=$((TOTAL + 1))
    echo -e "${BOLD}[$TOTAL] $basename${RESET}"

    # Parse expected patterns
    local patterns
    patterns=$(parse_expected_patterns "$file")

    if [ -z "$patterns" ]; then
        echo -e "  ${YELLOW}SKIP${RESET}: No '// Expected:' header found"
        SKIPPED=$((SKIPPED + 1))
        return
    fi
    if grep -q $'^__INVALID__\t' <<<"$patterns"; then
        local invalid
        invalid=$(sed -n $'s/^__INVALID__\t//p' <<<"$patterns" | paste -sd '; ' -)
        echo -e "  ${RED}FAIL${RESET}: malformed '// Expected:' assertion: $invalid"
        FAILED=$((FAILED + 1))
        ERRORS="${ERRORS}\n  $basename: malformed Expected assertion"
        return
    fi

    # Clear any TRUST_DISABLE_* variables
    unset_trust_disables

    local output=""
    local exit_code=0
    local infrastructure_timeout=false
    local session="trust-e2e-$basename"
    local stderr_file
    stderr_file=$(mktemp /tmp/trust_e2e_XXXXXX)

    # Full verification via the checked stage2 Trust compiler.
    local output_file
    output_file=$(mktemp /tmp/trust_e2e_out_XXXXXX)
    "$TIMEOUT_BIN" "$VERIFY_TIMEOUT_SECONDS" "$trustc" --edition 2021 \
        -Z trust-verify-output=both -Z "trust-verify-session=$session" "$file" \
        -o "$output_file" 2>"$stderr_file" || exit_code=$?
    output=$(cat "$stderr_file")
    if [ $exit_code -eq 124 ] || [ $exit_code -eq 137 ]; then
        infrastructure_timeout=true
        output="${output}
TIMEOUT: trustc exceeded ${VERIFY_TIMEOUT_SECONDS}s verification timeout"
    fi
    rm -f "$output_file"
    rm -f "$stderr_file"

    # --- Check verification results ---
    local test_passed=true

    if [ "$COMPLETE_CORPUS_DIAGNOSTIC" = "1" ] && $infrastructure_timeout; then
        echo -e "  ${RED}FAIL${RESET}: complete-corpus diagnostic forbids infrastructure timeouts"
        test_passed=false
    fi
    if ! structured_results_envelope_present "$output" "$session"; then
        echo -e "  ${RED}FAIL${RESET}: structured expectation matching requires a valid verifier results envelope"
        FAILED=$((FAILED + 1))
        ERRORS="${ERRORS}\n  $basename: missing structured verifier results envelope"
        return
    fi
    if is_safe_variant "$file" && [ "$exit_code" -ne 0 ]; then
        echo -e "  ${RED}FAIL${RESET}: safe variant exited $exit_code instead of 0"
        test_passed=false
    fi

    if is_safe_variant "$file"; then
        # Safe variant: each structured status is exact; ABSENT was handled above.
        while IFS=$'\t' read -r vc_name expected_status; do
            [ -z "$vc_name" ] && continue
            expected_status="${expected_status:-PROVED}"
            if [ "$expected_status" = "ABSENT" ]; then
                if structured_result_satisfies "$output" "$vc_name" "$expected_status" any "$session"; then
                    echo -e "  ${GREEN}OK${RESET}: $vc_name ABSENT"
                else
                    echo -e "  ${RED}FAIL${RESET}: Expected $vc_name ABSENT but a structured row was emitted"
                    test_passed=false
                fi
                continue
            fi
            if [ "$expected_status" != "PROVED" ]; then
                if structured_result_satisfies "$output" "$vc_name" "$expected_status" any "$session"; then
                    echo -e "  ${GREEN}OK${RESET}: $vc_name $expected_status"
                else
                    echo -e "  ${RED}FAIL${RESET}: Expected $vc_name $expected_status but not found"
                    test_passed=false
                fi
            elif structured_result_satisfies "$output" "$vc_name" "$expected_status" all "$session"; then
                echo -e "  ${GREEN}OK${RESET}: $vc_name PROVED"
            else
                echo -e "  ${RED}FAIL${RESET}: Expected $vc_name PROVED but no matching proved row was emitted"
                test_passed=false
            fi
        done <<< "$patterns"
    else
        # Buggy variant: each VcKind should appear with the declared status.
        while IFS=$'\t' read -r vc_name expected_status; do
            [ -z "$vc_name" ] && continue
            expected_status="${expected_status:-FAILED}"
            if [ "$expected_status" = "ABSENT" ]; then
                if structured_result_satisfies "$output" "$vc_name" "$expected_status" any "$session"; then
                    echo -e "  ${GREEN}OK${RESET}: $vc_name ABSENT"
                else
                    echo -e "  ${RED}FAIL${RESET}: Expected $vc_name ABSENT but a structured row was emitted"
                    test_passed=false
                fi
                continue
            fi
            if structured_result_satisfies "$output" "$vc_name" "$expected_status" any "$session"; then
                if [ "$expected_status" = "UNKNOWN" ]; then
                    echo -e "  ${GREEN}OK${RESET}: $vc_name UNKNOWN (fail-closed)"
                elif [ "$expected_status" = "FAILED" ]; then
                    echo -e "  ${GREEN}OK${RESET}: $vc_name FAILED (bug detected)"
                else
                    echo -e "  ${GREEN}OK${RESET}: $vc_name $expected_status"
                fi
            else
                echo -e "  ${RED}FAIL${RESET}: Expected $vc_name $expected_status but not found"
                test_passed=false
            fi
        done <<< "$patterns"
    fi

    if $test_passed; then
        PASSED=$((PASSED + 1))
    else
        FAILED=$((FAILED + 1))
        ERRORS="${ERRORS}\n  $basename: verification output mismatch"
    fi
}

# ============================================================
# Main
# ============================================================

echo "=============================================="
echo "  Trust Verifier-Example Regression Diagnostic"
echo "=============================================="
echo

# Detect verification mode
TRUSTC_BIN=""
if ! TRUSTC_BIN=$(find_trustc); then
    echo "FAIL: stage2 Trust compiler not found."
    echo "Build stage2 Trust first: cd $TRUST_ROOT && ./x.py build --stage 2 compiler/rustc library/std"
    exit 2
fi

echo "Mode:    stage2 Trust compiler (default verification)"
echo "Trustc:  $TRUSTC_BIN"
echo "Root:    $TRUST_ROOT"
echo "Filter:  ${FILTER:-<all>}"
echo "Complete-corpus diagnostic: $COMPLETE_CORPUS_DIAGNOSTIC"
echo "Authority: diagnostic only; not proof or release evidence"
echo "Provenance: source/tool provenance is not independently authenticated"
echo

if [ "$COMPLETE_CORPUS_DIAGNOSTIC" = "1" ] \
    && ! validate_complete_corpus_diagnostic_context "$TRUSTC_BIN"; then
    exit 2
fi
if [ "$COMPLETE_CORPUS_DIAGNOSTIC" = "1" ]; then
    TRUSTC_BIN="$DIAGNOSTIC_TRUSTC_PATH"
fi

# Collect test files
FILES=()
for f in "$EXAMPLES_DIR"/verify_*.rs; do
    [ -f "$f" ] || continue
    if [ -n "$FILTER" ]; then
        basename=$(basename "$f" .rs)
        case "$basename" in
            *"$FILTER"*) ;;
            *) continue ;;
        esac
    fi
    FILES+=("$f")
done

if [ ${#FILES[@]} -eq 0 ]; then
    echo "No matching examples/verify_*.rs files found."
    if [ -n "$FILTER" ]; then
        echo "Filter '$FILTER' matched nothing."
    fi
    exit 2
fi

echo "Found ${#FILES[@]} test file(s)"
echo "----------------------------------------------"
echo

# Run tests
START_TIME=$(date +%s)

for file in "${FILES[@]}"; do
    run_test "$file" "$TRUSTC_BIN"
    echo
done

END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))

if [ "$COMPLETE_CORPUS_DIAGNOSTIC" = "1" ] \
    && ! validate_complete_corpus_diagnostic_unchanged; then
    exit 2
fi

if [ "$COMPLETE_CORPUS_DIAGNOSTIC" = "1" ] && [ $SKIPPED -gt 0 ]; then
    FAILED=$((FAILED + 1))
    ERRORS="${ERRORS}\n  complete-corpus diagnostic forbids skipped examples ($SKIPPED skipped)"
fi

# --- Summary ---
echo "=============================================="
echo "  Summary"
echo "=============================================="
echo
echo "  Total:   $TOTAL"
echo -e "  Matched: ${GREEN}$PASSED${RESET}"
echo -e "  Failed:  ${RED}$FAILED${RESET}"
echo -e "  Skipped: ${YELLOW}$SKIPPED${RESET}"
echo "  Time:    ${ELAPSED}s"

if [ $FAILED -gt 0 ]; then
    echo
    echo -e "${RED}FAILURES:${RESET}"
    echo -e "$ERRORS"
    echo
    exit 1
fi

if [ $PASSED -eq 0 ] && [ $SKIPPED -gt 0 ]; then
    echo
    echo -e "${RED}FAIL: All verifier-example regression checks skipped.${RESET}"
    echo "Build stage2 for default Trust verification: cd $TRUST_ROOT && ./x.py build --stage 2 compiler/rustc library/std"
    echo
    echo "Declared regression-assertion coverage cannot be skipped in this diagnostic."
    echo
    exit 2
fi

echo
echo -e "${GREEN}DIAGNOSTIC PASS: all observed example outputs satisfied their declared structured assertions.${RESET}"
echo "This is diagnostic only; it is not proof or release evidence, and source/tool provenance is unauthenticated."
exit 0
