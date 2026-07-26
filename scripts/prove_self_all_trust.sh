#!/usr/bin/env bash
# prove_self_all_trust.sh — the §6 definition-of-done over the ENTIRE Trust tree.
#
# Dumps every function's VerifiableFunction during a full stage-2 build (the MIR
# verify pass writes one content-addressed JSON file per function when the tracked
# `-Ztrust-dump=mir-only:<dir>` option is set). The extraction build also selects
# `-Ztrust-dump=mir-only:<dir>`, so it never spends time dispatching those obligations to
# solvers or certifiers before the dedicated proof phase,
# then runs `targo trust prove` over the whole dump, reconstructing each
# obligation as a kernel proof modulo exactly the 3 foundational axioms.
#
# This is the build-bound finish: the build is multi-hour; the prove step is the
# same pipeline already verified over hand-fixtures, the 20-fixture corpus, and
# real trustc-compiled functions. On full success it prints:
#
#     ALL OF TRUST PROVEN IN CLEAN. axioms: 3.
#
# Usage:  scripts/prove_self_all_trust.sh [DUMP_DIR]
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

DUMP_DIR="${1:-target/trust-mir-dump}"
mkdir -p "$DUMP_DIR"
DUMP_PATH="$(cd "$DUMP_DIR" && pwd)"

case "$DUMP_PATH" in
  *[[:space:]]*)
    echo "error: MIR dump path contains whitespace, which RUSTFLAGS_NOT_BOOTSTRAP cannot encode: $DUMP_PATH" >&2
    exit 2
    ;;
esac

echo "== [1/2] dumping every function's VerifiableFunction over the whole tree =="
echo "   RUSTFLAGS_NOT_BOOTSTRAP='-Ztrust-policy=advisory -Ztrust-dump=mir-only:$DUMP_PATH' ./x.py build --stage 2"
RUSTFLAGS_NOT_BOOTSTRAP="${RUSTFLAGS_NOT_BOOTSTRAP:+$RUSTFLAGS_NOT_BOOTSTRAP }-Ztrust-policy=advisory -Ztrust-dump=mir-only:$DUMP_PATH" \
  ./x.py build --stage 2

DUMPED="$(find "$DUMP_PATH" -name '*.json' | wc -l | tr -d ' ')"
echo "   dumped $DUMPED functions"

echo "== [2/2] proving every obligation in Clean modulo 3 axioms =="
echo "   targo trust prove --self --kernel --require-axioms=3 --dump-dir $DUMP_PATH"
exec targo trust prove --self --kernel --require-axioms=3 --dump-dir "$DUMP_PATH"
