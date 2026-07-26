#!/usr/bin/env bash
# Windows (x86_64-pc-windows-msvc) cross-CHECK of the pure-Rust verifier stack.
#
# `cargo check` type/borrow-checks without linking, so it verifies the Windows
# *port* of the Trust-owned verifier crates from a Unix host with no MSVC linker —
# it is the oracle used to Windows-port them (docs/GENESIS_TRUST_ROOT.md root #3,
# scripts/win-genesis/README.md).
#
# SCOPE — pure Rust only. The native-backend features (ay-backend, trust-mc-backend,
# trust-wp-backend, trust-build, carcara-crosscheck) pull C deps (stacker/cc, GMP
# via rug) that need a Windows C cross-toolchain, and the trust-mc/ay-chc issue is a
# *link* failure `check` cannot see — those must be verified on a real Windows box.
# This gate covers everything that does NOT require that.
set -uo pipefail

TARGET=x86_64-pc-windows-msvc
TOOLCHAIN=${TRUST_WIN_CHECK_TOOLCHAIN:-nightly}

ROOT=$(cd -P "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P) || { echo "cannot resolve repo root" >&2; exit 1; }
cd -P "$ROOT" || exit 1

command -v cargo >/dev/null 2>&1 || { echo "FAIL: cargo not found" >&2; exit 1; }

# Ensure the Windows target's std is available (check needs it; no linker needed).
if ! rustup target list --installed --toolchain "$TOOLCHAIN" 2>/dev/null | grep -qx "$TARGET"; then
    echo "adding $TARGET std to $TOOLCHAIN ..."
    rustup target add "$TARGET" --toolchain "$TOOLCHAIN" || {
        echo "FAIL: could not add $TARGET std" >&2; exit 1; }
fi

# The pure-Rust verifier crates (Trust-owned, no native-backend C deps).
CRATES=(
    trust-router trust-types trust-cache trust-deps trust-wp
    trust-backprop trust-buildcache trust-os
    trust-loop trust-vcgen trust-report trust-proof-cert
    trust-strengthen trust-convergence
)
declare -a PKG_ARGS
for c in "${CRATES[@]}"; do PKG_ARGS+=(-p "$c"); done

echo "== Windows cross-check ($TARGET, $TOOLCHAIN): ${#CRATES[@]} pure-Rust verifier crates =="
if cargo "+$TOOLCHAIN" check --target "$TARGET" --manifest-path crates/Cargo.toml "${PKG_ARGS[@]}"; then
    echo
    echo "PASS: the pure-Rust verifier stack cross-checks clean for $TARGET."
    echo "NOTE: native ay/trust-mc/clean backends + the trust-mc link path are NOT"
    echo "      covered here — verify those on a real Windows box (see win-genesis)."
    exit 0
fi
echo
echo "FAIL: Windows cross-check found un-ported (un-cfg-gated) code above." >&2
exit 1
