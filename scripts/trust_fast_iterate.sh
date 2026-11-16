#!/usr/bin/env bash
# Trust: the FAST compiler-iteration lane — build the compiler, not the toolbox.
#
# WHY IT IS 4x. `x.py build --stage 1` also rebuilds everything `bootstrap.toml`'s
# `[build] tools` list names: targo, trustd, ay, ty, clean, rust-analyzer, tippy,
# trustfmt, trust-miri, trustdoc. MEASURED 2026-09-15 on a one-file compiler
# change, same machine, back to back:
#
#     x.py build --stage 1                  20m24s   528 crate compiles
#     x.py build --stage 1 compiler/rustc library
#                                            4m49s    72 crate compiles
#
# 464 of those 528 compiles (88%) happen AFTER the compiler and std are built and
# linked. Nothing under `compiler/**` or `crates/**` can change their output, and
# the binaries they produce are already in the sysroot from the previous full
# build. `tests/ui/trust` returns BYTE-IDENTICAL results either way (655 passed /
# 139 failed on both, measured the same day).
#
# WHEN NOT TO USE IT — and the script refuses rather than trusting you:
#   * a `first-party/*` pin is modified, so a sibling's own binary (ay / clean /
#     ty) may be stale in the sysroot. Take the full build.
#   * the sysroot has no stage1 compiler yet, or is missing a backend binary.
#     There is nothing to iterate ON. Take the full build.
#
# USAGE
#   scripts/trust_fast_iterate.sh                        # build only
#   scripts/trust_fast_iterate.sh tests/ui/trust         # build, then one suite
#   scripts/trust_fast_iterate.sh tests/ui/trust/foo.rs tests/run-make
#
# A test path is passed straight to `x.py test --stage 1 … --force-rerun`, so a
# single fixture works and is the point: the suite is 4 minutes, one fixture is
# seconds, and iteration rarely needs the suite until the end.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

SYSROOT="build/host/stage1"
LOG="${TRUST_FAST_LOG:-/tmp/trust-fast-iterate.log}"

fail() { echo "trust_fast_iterate: $1"; echo; echo "  Use the full build instead:"; echo "      ./x.py build --stage 1"; exit 3; }

if ! git diff --quiet HEAD -- first-party/ 2>/dev/null; then
    fail "a first-party/* pin is modified, so ay / clean / ty may be stale in the sysroot."
fi
[ -x "$SYSROOT/bin/trustc" ] || fail "no stage1 compiler at $SYSROOT/bin/trustc."
for backend in ay clean ty; do
    [ -x "$SYSROOT/bin/$backend" ] || fail "the stage1 sysroot has no \`$backend\` binary."
done

echo "=== build: compiler + library only $(date +%H:%M:%S)"
if ! ./x.py build --stage 1 compiler/rustc library > "$LOG" 2>&1; then
    echo "BUILD FAILED — full log at $LOG"
    grep -E "^error" "$LOG" | grep -v missing_docs | head -8
    exit 1
fi
grep -E "Build completed" "$LOG"

status=0
for t in "$@"; do
    out="${LOG%.log}-$(basename "$t" | tr / _).log"
    echo "=== $t $(date +%H:%M:%S)"
    ./x.py test --stage 1 "$t" --force-rerun > "$out" 2>&1 || status=1
    grep -E "^test result" "$out" || echo "  (no test result line — see $out)"
    grep -oE "^    \[(ui|run-make)\] \S+" "$out" | sort -u | head -20
done
echo "=== done $(date +%H:%M:%S)"
exit $status
