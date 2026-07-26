#!/bin/bash
# Local diagnostic entrypoint for the copied/read-only installed-toolchain
# rehearsal. It is not canonical release authority; both historical script
# names exercise the same isolated rustup and Cargo homes.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

case "${1:-}" in
    -h|--help)
        cat <<'EOF'
Usage: tests/e2e_trust_installed_toolchain.sh [options]

Delegates to e2e_trust_local_rustup_install.sh. Supported options include
--source-sysroot PATH, --stage-provenance PATH, --receipt PATH, --set-default,
and --keep-temp. Unlike the retired placeholder, --set-default exercises a
real default inside a fresh isolated RUSTUP_HOME and cannot modify the caller's
rustup configuration. Record publication is fail-closed, forbids diagnostic
skips, and remains non-authoritative local rehearsal output.
EOF
        exit 0
        ;;
esac

exec bash "$SCRIPT_DIR/e2e_trust_local_rustup_install.sh" "$@"
