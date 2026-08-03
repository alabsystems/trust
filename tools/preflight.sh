#!/bin/sh
# Trust build preflight - fail fast, in seconds, before paying for x.py.
#
# This is a thin POSIX-sh launcher whose only job is to find a python that has
# `tomllib` (>= 3.11) and hand off to tools/preflight.py.
#
# Why the real checker is python and not sh:
#   * bootstrap.toml, every Cargo.toml AND every Cargo.lock are TOML. tomllib is
#     in the stdlib from 3.11, so parsing them costs zero new dependencies.
#     Doing the same in sh means regexing TOML, and a regex that mis-parses a
#     `tools = [...]` list fails OPEN - it reports "backends present" on a
#     config that omits them, which is exactly the silent failure we are here
#     to prevent. A checker that can lie is worse than no checker.
#   * per-probe timeouts and bounded parallelism: `timeout(1)` is not on stock
#     macOS, so the "run 20 resolves in seconds" requirement is not portably
#     expressible in sh.
#   * sh is still the entry point, so `sh tools/preflight.sh` works on a tree
#     with no toolchain built yet.
#
# Usage:
#   tools/preflight.sh                 # fast audit (seconds)
#   tools/preflight.sh --for-build     # what the x.py hook runs
#   tools/preflight.sh --deep          # + authoritative `metadata --locked`
#   tools/preflight.sh --only tools --bootstrap-toml /path/to/candidate.toml
#
# Exit: 0 = cleared, 1 = blocking problem found, 2 = preflight itself broke.

set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
checker="$here/preflight.py"

if [ ! -f "$checker" ]; then
    echo "preflight: missing $checker" >&2
    exit 2
fi

# Prefer the interpreter bootstrap itself is configured to use, then anything
# modern on PATH. First one with tomllib wins.
candidates=""
if [ -f "$here/../bootstrap.toml" ]; then
    cfg_py=$(sed -n 's/^[[:space:]]*python[[:space:]]*=[[:space:]]*"\(.*\)".*/\1/p' \
             "$here/../bootstrap.toml" 2>/dev/null | head -n1 || true)
    [ -n "${cfg_py:-}" ] && candidates="$cfg_py"
fi
candidates="$candidates python3 python3.14 python3.13 python3.12 python3.11 python"

for c in $candidates; do
    if [ -x "$c" ]; then
        py="$c"
    elif py=$(command -v "$c" 2>/dev/null); then
        :
    else
        continue
    fi
    if "$py" -c 'import tomllib' >/dev/null 2>&1; then
        exec "$py" "$checker" "$@"
    fi
done

echo "preflight: no python >= 3.11 (needs tomllib) found." >&2
echo "preflight: tried: $candidates" >&2
exit 2
