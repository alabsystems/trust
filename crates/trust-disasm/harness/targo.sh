# Sourced by every harness run.sh: resolve the Trust toolchain's `targo`.
#
# The drivers are Trust code, so the Trust toolchain builds them — never a host
# Rust (`cargo +beta` was used here until 2026-09-16, and it stopped
# working wherever rustup's proxies were off PATH). `targo` comes from PATH (the
# atpkg `trust` pack) or, failing that, this checkout's stage2 sysroot.
#
# The identity check is the one CLAUDE.md records as the only discriminator that
# has held: a real targo accepts `--unverified --version`; upstream cargo shipped
# under the name `targo` answers "unexpected argument '--unverified'".
#
# Sets TARGO, or exits 2 with the reason.
TARGO=${TARGO:-}
if [ -z "$TARGO" ]; then
    if command -v targo >/dev/null 2>&1; then
        TARGO=$(command -v targo)
    else
        _stage2="$(git rev-parse --show-toplevel 2>/dev/null)/build/host/stage2/bin/targo"
        [ -x "$_stage2" ] && TARGO=$_stage2
    fi
fi
if [ -z "$TARGO" ]; then
    echo "no targo on PATH and no stage2 targo: install the Trust toolchain (atpkg trust pack)" >&2
    exit 2
fi
if ! "$TARGO" --unverified --version >/dev/null 2>&1; then
    echo "$TARGO is not targo: it rejects --unverified (upstream cargo under the targo name)" >&2
    exit 2
fi
