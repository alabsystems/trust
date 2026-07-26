#!/usr/bin/env bash
# Compatibility entrypoint for the former destructive first-party sync helper.
#
# This command is intentionally read-only. It no longer discards tracked
# Cargo.lock changes or runs an ambient recursive submodule update. The
# recreator is the sole canonical owner of bounded missing-gitlink acquisition;
# it never moves an already materialized sibling back to a committed pin.
set -euo pipefail

SCRIPT_ROOT="$(cd "$(dirname "$0")/.." && pwd -P)"
if [[ "$#" -ne 0 && ! ( "$#" -eq 1 && "$1" == "--check" ) ]]; then
    printf 'usage: %s [--check]\n' "$0" >&2
    exit 64
fi

printf '%s\n' \
    'sync-first-party.sh is now a read-only compatibility check.' \
    'It preserves Cargo.lock edits and never resets materialized submodules.' \
    'For a fresh superproject-only clone, the canonical recreator initializes' \
    'only missing indexed gitlinks through its bounded credential scope.'
exec python3 "$SCRIPT_ROOT/scripts/recreate_bootstrap.py" --check
