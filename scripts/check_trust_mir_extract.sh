#!/usr/bin/env bash
# Check the rustc_private Trust MIR extraction path through bootstrap.
#
# `crates/trust-mir-extract` intentionally cannot be checked by the standalone
# `crates/Cargo.toml` workspace: it depends on in-tree rustc_private crates and
# must be built with the same compiler/bootstrap configuration as rustc itself.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

cd "$REPO_ROOT"

python3 x.py check compiler/rustc_mir_transform
