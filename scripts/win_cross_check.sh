#!/usr/bin/env bash
# Windows (x86_64-pc-windows-msvc) cross-CHECK of the pure-Rust verifier stack.
#
# `targo --unverified check` type/borrow-checks without linking, so it verifies the Windows
# *port* of the Trust-owned verifier crates from a Unix host with no MSVC linker —
# it is the oracle used to Windows-port them (docs/GENESIS_TRUST_ROOT.md root #3,
# scripts/win-genesis/README.md).
#
# SCOPE — pure Rust only. The native-backend features (ay-backend, trust-build,
# carcara-crosscheck) pull C deps (stacker/cc, GMP
# via rug) that need a Windows C cross-toolchain, and the trust-mc/ay-chc issue is a
# *link* failure `check` cannot see — those must be verified on a real Windows box.
# This gate covers everything that does NOT require that.
set -uo pipefail

TARGET=x86_64-pc-windows-msvc
TOOLCHAIN=${TRUST_WIN_CHECK_TOOLCHAIN:-nightly}

ROOT=$(cd -P "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P) || { echo "cannot resolve repo root" >&2; exit 1; }
cd -P "$ROOT" || exit 1

# DRIVER. On this machine Rust is the Trust toolchain (CLAUDE.md "Build"), so
# the Trust spelling is tried FIRST: `targo --unverified check` whenever the
# Trust sysroot carries the target's std. The stock-nightly leg below is a
# measured exception, not a default: on 2026-09-23 the Trust sysroot shipped
# only `lib/rustlib/aarch64-apple-darwin`, and `targo --unverified check
# --target x86_64-pc-windows-msvc` failed E0463 ("can't find crate for `core`").
# That leg prints a STOCK: line so no report can read it as a Trust run.
TRUST_SYSROOT=""
if command -v targo >/dev/null 2>&1 && targo --unverified --version >/dev/null 2>&1 \
   && command -v trustc >/dev/null 2>&1; then
    TRUST_SYSROOT=$(trustc --print sysroot 2>/dev/null || true)
fi
if [ -n "$TRUST_SYSROOT" ] && [ -d "$TRUST_SYSROOT/lib/rustlib/$TARGET" ]; then
    DRIVER=(targo --unverified)
    DRIVER_LABEL="Trust toolchain: $TRUST_SYSROOT"
else
    # STOCK EXCEPTION (Trust lacks a $TARGET std; measured 2026-09-28 on 321aaeda7:
    # `targo --unverified check --target x86_64-pc-windows-msvc` -> E0463 can't find crate for `core`).
    # A cross-target check only, never the host build; named explicitly through rustup so no
    # PATH `cargo` (the aterm reroute stub, or a rustup proxy) is ever what runs.
    echo "STOCK: the Trust sysroot (${TRUST_SYSROOT:-no targo/trustc on PATH}) has no $TARGET std;" >&2
    echo "       using stock \`rustup run $TOOLCHAIN cargo\` for this cross-check only." >&2
    command -v rustup >/dev/null 2>&1 || { echo "FAIL: no Trust $TARGET std and no rustup for the stock cross-check" >&2; exit 1; }
    DRIVER=(rustup run "$TOOLCHAIN" cargo)
    DRIVER_LABEL="STOCK $TOOLCHAIN"
fi

# Ensure the Windows target's std is available (check needs it; no linker needed).
if [ "${DRIVER[0]}" = rustup ] && ! rustup target list --installed --toolchain "$TOOLCHAIN" 2>/dev/null | grep -qx "$TARGET"; then
    echo "adding $TARGET std to $TOOLCHAIN ..."
    rustup target add "$TARGET" --toolchain "$TOOLCHAIN" || {
        echo "FAIL: could not add $TARGET std" >&2; exit 1; }
fi

# The pure-Rust verifier crates (Trust-owned, no native-backend C deps).
CRATES=(
    trust-router trust-types trust-cache trust-wp
    trust-backprop trust-os
    trust-loop trust-vcgen trust-report trust-proof-cert
    trust-strengthen trust-convergence
)
declare -a PKG_ARGS
for c in "${CRATES[@]}"; do PKG_ARGS+=(-p "$c"); done

echo "== Windows cross-check ($TARGET, $DRIVER_LABEL): ${#CRATES[@]} pure-Rust verifier crates =="
if "${DRIVER[@]}" check --target "$TARGET" --manifest-path Cargo.toml "${PKG_ARGS[@]}"; then
    echo
    echo "PASS: the pure-Rust verifier stack cross-checks clean for $TARGET."
    echo "NOTE: native ay/trust-mc/clean backends + the trust-mc link path are NOT"
    echo "      covered here — verify those on a real Windows box (see win-genesis)."
    exit 0
fi
echo
echo "FAIL: Windows cross-check found un-ported (un-cfg-gated) code above." >&2
exit 1
