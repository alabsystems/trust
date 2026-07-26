#!/usr/bin/env bash
# Trust developer bootstrap: one authority-owning path from a fresh
# superproject checkout to a seed-required fresh Stage2 toolchain.
#
# This wrapper deliberately performs no separate package installation,
# submodule update, stock-Rust probe, raw x.py build, or smoke-test downgrade.
# The Python recreator owns acquisition, credentials, timeouts, configuration,
# build provenance, inventory, acceptance, and optional rustup registration.
#
#   bash scripts/dev-bootstrap.sh
#   bash scripts/dev-bootstrap.sh --check
#
# The private source-build path is internal evidence, not public release or
# self-proof. See INSTALL.md and docs/BOOTSTRAP_FROM_SCRATCH.md.
set -euo pipefail

SCRIPT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RECREATOR="$SCRIPT_ROOT/scripts/recreate_bootstrap.py"

usage() {
    printf '%s\n' \
        'usage: scripts/dev-bootstrap.sh [--check]' \
        '' \
        '  no args   require the admitted seed and build/audit a fresh Stage2' \
        '  --check   read-only prerequisite and seed-state report'
}

case "$#:${1:-}" in
    0:)
        exec python3 "$RECREATOR" --require-seed --fresh-seed --stage 2
        ;;
    1:--check)
        exec python3 "$RECREATOR" --check --require-seed --stage 2
        ;;
    1:-h|1:--help)
        usage
        ;;
    *)
        usage >&2
        printf '%s\n' \
            'noncanonical options must be passed directly to scripts/recreate_bootstrap.py' >&2
        exit 2
        ;;
esac
