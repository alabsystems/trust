#!/usr/bin/env bash
# End-to-end regression test for hardened standalone source checks.
#
# Primary command under test:
#   targo trust check --standalone --format json --manifest-path examples/hardened/Cargo.toml
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
FIXTURE_MANIFEST="$TRUST_ROOT/examples/hardened/Cargo.toml"

echo "=== tRust E2E Test: hardened standalone CLI corpus ==="
echo

fail_setup() {
    echo "ERROR: $1"
    exit 2
}

fail_test() {
    echo "FAIL: $1"
    exit 1
}

if [ ! -f "$FIXTURE_MANIFEST" ]; then
    fail_setup "hardened fixture manifest not found: $FIXTURE_MANIFEST"
fi

if ! command -v python3 >/dev/null 2>&1; then
    fail_setup "python3 not found on PATH; needed to validate hardened JSON output"
fi

TMP_ROOT="${TMPDIR:-/tmp}"
TMP_DIR="$(mktemp -d "${TMP_ROOT%/}/hardened_cli_XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

JSON_STDOUT="$TMP_DIR/hardened.json"
JSON_STDERR="$TMP_DIR/hardened.stderr"

trust_stage2_bin_dir() {
    local candidate
    for candidate in "$TRUST_ROOT/build/host/stage2/bin" "$TRUST_ROOT"/build/*/stage2/bin; do
        if [ -x "$candidate/targo" ] && [ -x "$candidate/trustc" ]; then
            # Protected Trust subcommands authenticate their toolchain
            # directory and fail closed on symlinked/non-canonical paths
            # (e.g. build/host -> build/<triple>), so hand them the
            # physical path.
            (cd "$candidate" && pwd -P)
            return 0
        fi
    done
    return 1
}

run_hardened_cli() {
    local trust_bin

    if trust_bin="$(trust_stage2_bin_dir)"; then
        "$trust_bin/targo" trust check --standalone --format json \
            --manifest-path "$FIXTURE_MANIFEST"
        return
    fi

    fail_setup "stage2 Trust targo/trustc not found. Build the standalone Trust toolchain first."
}

echo "Fixture: $FIXTURE_MANIFEST"
echo

cli_exit=0
run_hardened_cli >"$JSON_STDOUT" 2>"$JSON_STDERR" || cli_exit=$?

if [ "$cli_exit" -eq 0 ]; then
    fail_test "hardened fixture unexpectedly passed; hardened regressions should fail closed"
fi
if [ "$cli_exit" -gt 1 ]; then
    echo "--- stdout"
    cat "$JSON_STDOUT"
    echo "--- stderr"
    cat "$JSON_STDERR"
    fail_test "hardened CLI exited with unexpected status $cli_exit"
fi

if grep -q "TRUST_JSON:" "$JSON_STDOUT" "$JSON_STDERR"; then
    fail_test "hardened standalone output leaked raw TRUST_JSON transport"
fi

python3 - "$JSON_STDOUT" <<'PY'
import json
import sys
from collections import Counter

with open(sys.argv[1], "r", encoding="utf-8") as fh:
    report = json.load(fh)

if report.get("mode") != "source-audit":
    raise AssertionError(f"expected source-audit mode, got {report.get('mode')!r}")

files_analyzed = report.get("files_analyzed")
if not isinstance(files_analyzed, int) or files_analyzed < 2:
    raise AssertionError(f"expected claim modules to be analyzed, got {files_analyzed!r}")

required = {
    "HardenedRawPathApi",
    "HardenedPathIdentity",
    "HardenedPermissionChange",
    "HardenedPermissionCreate",
    "HardenedPermissionWindow",
    "HardenedUtf8Boundary",
    "HardenedByteLoss",
    "HardenedErrorDiscard",
    "HardenedPanic",
    "HardenedTrustBoundary",
    "HardenedTrustDomainOrder",
    "HardenedCompatibility",
    "HardenedProcessSemantics",
    "HardenedUnsafeOperation",
    "HardenedFfiBoundary",
}

vcs = report.get("audit_rows")
if not isinstance(vcs, list):
    raise AssertionError("missing audit_rows array")

kinds = Counter(vc.get("kind") for vc in vcs if isinstance(vc, dict))
missing = sorted(kind for kind in required if kinds[kind] < 1)
if missing:
    raise AssertionError("missing hardened VC kinds: " + ", ".join(missing))

allowed_source_root = "examples/hardened/"
files = {str(vc.get("file", "")) for vc in vcs if isinstance(vc, dict)}
if not files or not all(allowed_source_root in path for path in files):
    raise AssertionError(f"expected all VCs from hardened source tree, got {sorted(files)!r}")

failed = report.get("failed")
if not isinstance(failed, int) or failed < len(required):
    raise AssertionError(f"expected at least {len(required)} failed hardened VCs, got {failed!r}")

descriptions = "\n".join(str(vc.get("description", "")) for vc in vcs if isinstance(vc, dict))
expected_fragments = [
    "raw path",
    "identity",
    "path-based permission",
    "directory creation by path",
    "UTF-8",
    "lossy",
    "discard",
    "panic",
    "creation at line",
    "parent dirfd contracts",
    "chroot",
    "CLI boundary",
    "SIGPIPE",
    "trusted-wrapper",
]
missing_fragments = [fragment for fragment in expected_fragments if fragment not in descriptions]
if missing_fragments:
    raise AssertionError("missing hardened diagnostics: " + ", ".join(missing_fragments))
PY

echo "  PASS: hardened standalone CLI reports all expected fail-closed categories"
echo
echo "=== hardened standalone CLI corpus: PASS ==="
