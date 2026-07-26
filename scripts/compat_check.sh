#!/usr/bin/env bash
# Backward-compatible entry point for the diagnostic compatibility corpus.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

TARGO_BIN="${1:-}"
CRATE_LIST="${2:-$REPO_ROOT/tests/compat/top_crates.txt}"
RECEIPT="${3:-$REPO_ROOT/build/evidence/crates-io-native-compatibility.json}"

ARGS=(
    --crate-list "$CRATE_LIST"
    --receipt "$RECEIPT"
)
if [[ -n "$TARGO_BIN" ]]; then
    ARGS+=(--targo "$TARGO_BIN")
fi

PYTHON_BIN=""
for candidate in /opt/homebrew/bin/python3.14 /usr/bin/python3; do
    if [[ -f "$candidate" && -x "$candidate" ]]; then
        PYTHON_BIN="$candidate"
        break
    fi
done
if [[ -z "$PYTHON_BIN" ]]; then
    echo "compat_check.sh: no fixed Python exists at /opt/homebrew/bin/python3.14 or /usr/bin/python3" >&2
    exit 2
fi

# Suppress user-site, sitecustomize, PYTHONPATH, and PYTHON* startup hooks for
# the nested run. The receipt remains explicitly unauthenticated because this
# shell is not a native authority boundary.
exec "$PYTHON_BIN" -I -S -E "$SCRIPT_DIR/compat_check.py" "${ARGS[@]}"
