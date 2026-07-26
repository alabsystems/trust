#!/usr/bin/env bash
# generate_mir_fixtures.sh: Generate real MIR JSON fixtures from Rust source files.
#
# Uses the stage1 compiler (or trustc) with `-Ztrust-dump=mir:<dir>` and
# `-Ztrust-dump=mir-only:<dir>` to extract VerifiableFunction JSON without dispatching
# verification work for each function in the test source files.
#
# Usage:
#   ./scripts/generate_mir_fixtures.sh
#
# Prerequisites:
#   - Stage1 compiler built: ./x.py build --stage 1
#   - OR: a `trustc` on PATH
#
# Output:
#   crates/trust-integration-tests/fixtures/real_mir/*.json
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FIXTURE_DIR="$REPO_ROOT/crates/trust-integration-tests/fixtures/real_mir"
SRC_DIR="$FIXTURE_DIR/src"
OUTPUT_DIR="$FIXTURE_DIR"

# Find the compiler to use.
TRUSTC=""
if [ -f "$REPO_ROOT/build/host/stage1/bin/trustc" ]; then
    TRUSTC="$REPO_ROOT/build/host/stage1/bin/trustc"
    echo "Using stage1 compiler: $TRUSTC"
elif command -v trustc &>/dev/null; then
    TRUSTC="trustc"
    echo "Using trustc from PATH"
else
    echo "ERROR: No stage1 compiler or trustc found."
    echo "Build with: ./x.py build --stage 1"
    echo "Or put a trustc on PATH."
    exit 1
fi

# Remove old fixtures (keep src/ directory).
find "$OUTPUT_DIR" -maxdepth 1 -name '*.json' -delete 2>/dev/null || true

echo "Generating MIR fixtures from source files in $SRC_DIR..."

for src_file in "$SRC_DIR"/*.rs; do
    filename="$(basename "$src_file" .rs)"
    echo "  Compiling: $filename.rs"

    "$TRUSTC" \
        -Ztrust-policy=advisory \
        -Z"trust-dump=mir:$OUTPUT_DIR" \
        \
        --edition 2021 \
        --crate-type lib \
        -o /dev/null \
        "$src_file" 2>/dev/null || {
            echo "    WARNING: Compilation failed for $filename.rs (non-fatal)"
            continue
        }
done

# Count generated fixtures.
fixture_count=$(find "$OUTPUT_DIR" -maxdepth 1 -name '*.json' | wc -l | tr -d ' ')
echo ""
echo "Generated $fixture_count MIR fixtures in $OUTPUT_DIR"
echo ""

if [ "$fixture_count" -eq 0 ]; then
    echo "WARNING: No fixtures generated. The compiler may not support -Ztrust-dump=mir:<dir> yet."
    echo "Rebuild the compiler with the latest trust_verify.rs changes:"
    echo "  ./x.py build --stage 1"
    exit 1
fi

# List generated files.
ls -la "$OUTPUT_DIR"/*.json 2>/dev/null || true
