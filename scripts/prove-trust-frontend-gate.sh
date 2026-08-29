#!/bin/sh
# prove-trust-frontend-gate.sh — prove that a linked Trust toolchain actually
# SERVES the gates that pin it, and that those gates can still fail.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# WHY THIS EXISTS, AND WHY IT IS NOT tools/verify-toolchain.sh
# ------------------------------------------------------------
# verify-toolchain.sh answers "did the build produce binaries that run". This
# answers the question a consumer repo actually asks: "does `channel = "trust"`
# in MY rust-toolchain.toml reach those binaries, and does a gate run through
# them". Those are different failures. A perfect sysroot that rustup never
# selects is exactly as useless to clean/trust-vc/aterm as a missing one, and
# the way it fails is silent — clean/scripts/rust_frontend.sh measured it on
# 2026-08-22: with no `trust` toolchain linked, the workspace gate ran stock
# cargo-clippy and reported CLEAN while `targo tippy` had six `-D warnings`
# violations on the same tree.
#
# So this reproduces that resolution path end to end, on a throwaway crate:
#
#   1. RESOLUTION. From a crate pinned to the channel, `rustc --print sysroot`
#      (through the rustup shim — the only thing that reads rust-toolchain.toml)
#      must name the same sysroot as `rustup run <name>`.
#   2. THE REFUSAL PREDICATE. rust_frontend.sh refuses when
#      `$sysroot/bin/<channel>c` is absent. Assert it is present, in that exact
#      form, so this proof and that refusal cannot drift apart.
#   3. FORMAT GATE. `$bindir/targo fmt --check` — the Trust frontend, invoked
#      from the canonical sysroot path, which is what rust_frontend.sh execs
#      (`targo fmt` through the rustup shim or the rustup toolchain dir is
#      REFUSED by design: protected frontends reject symlinked/non-canonical
#      paths).
#   4. LINT GATE. `$bindir/targo tippy --offline -- -D warnings`.
#
# Steps 3 and 4 are each run TWICE: once on clean source, which must pass, and
# once on deliberately broken source, which must fail. A gate that cannot fail
# is not evidence — an "installed" toolchain whose fmt frontend silently no-ops
# would sail through a pass-only check.
#
# Costs about 3 seconds against a warm toolchain. Nothing it writes leaves the
# temporary directory, and it never touches the sysroot.
#
# Usage:
#   scripts/prove-trust-frontend-gate.sh [--name NAME] [--keep]
#
#   --name NAME   toolchain / pinned channel to prove (default: trust)
#   --keep        leave the throwaway crate behind for inspection
#
# Exit: 0 proved   1 a step failed (the toolchain is not usable by the pinned
#                    repos AS THIS MACHINE IS CONFIGURED, and the message says
#                    which step — including step 0, the PATH, which this script
#                    deliberately never repairs for itself)
#       2 usage / environment

set -eu

TOOLCHAIN_NAME=trust
KEEP=0

while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help) sed -n '/^# Usage:/,/^# Exit:/p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        --name) shift; [ $# -gt 0 ] || { echo "prove: --name requires a value" >&2; exit 2; }; TOOLCHAIN_NAME=$1 ;;
        --name=*) TOOLCHAIN_NAME=${1#--name=} ;;
        --keep) KEEP=1 ;;
        *) printf 'prove: unknown argument: %s\n' "$1" >&2; exit 2 ;;
    esac
    shift
done
[ -n "$TOOLCHAIN_NAME" ] || { echo "prove: --name must not be empty" >&2; exit 2; }

fail() { printf 'PROOF FAILED: %s\n' "$*" >&2; exit 1; }
ok()   { printf '  PROVED   %s\n' "$*"; }

# RUSTUP_TOOLCHAIN overrides rust-toolchain.toml. Leaving it set would prove the
# override works, not that the PIN resolves — the whole point of step 1.
unset RUSTUP_TOOLCHAIN || true

# NO SELF-HEALING OF PATH. The gates in clean, trust-vc and aterm run with the
# PATH the machine actually has. If the rustup shim is not on it, nothing reads
# rust-toolchain.toml, `rustc` is whatever binary is ahead, and those gates
# refuse (or worse, run a different lint set under the same name) — which is the
# precise machine state this install path exists to cure.
#
# This script used to repair PATH from $HOME/.cargo/bin, print one stderr NOTE,
# and then go on to print PROOF COMPLETE: a proof about a shell it had just
# constructed, on a machine where every pinned repository would still refuse.
# The NOTE was the only marker, and a NOTE under a green PROOF COMPLETE is read
# by nobody. So the repair is gone and this is a failure. Repairing PATH here
# could only ever prove that a shell WITH the shim works, which was never in
# doubt; the proposition under test is that THIS environment resolves the pin.
if ! command -v rustup >/dev/null 2>&1; then
    if [ -x "$HOME/.cargo/bin/rustup" ]; then
        fail "rustup is installed at $HOME/.cargo/bin/rustup, but $HOME/.cargo/bin is not
  on the PATH this proof inherited. That is not a detail this script may paper
  over: it is exactly the machine state in which channel = \"$TOOLCHAIN_NAME\"
  fails to resolve, so the gates in clean, trust-vc and aterm would still refuse
  no matter how good the linked toolchain is.

  Fix the environment, not the proof:

      export PATH=\"\$HOME/.cargo/bin:\$PATH\"                        # this shell
      echo 'export PATH=\"\$HOME/.cargo/bin:\$PATH\"' >> ~/.zshrc     # every future shell

  then re-run this script. It will then be proving something about the PATH the
  pinned repositories will actually get."
    fi
    echo "prove: rustup not found — a pinned channel cannot resolve without it" >&2
    exit 2
fi

if ! rustup toolchain list 2>/dev/null | cut -d' ' -f1 | grep -qx "$TOOLCHAIN_NAME"; then
    fail "no rustup toolchain named '$TOOLCHAIN_NAME'.
  Run scripts/install-trust-toolchain.sh first."
fi

CRATE=$(mktemp -d "${TMPDIR:-/tmp}/trust-frontend-proof.XXXXXX")
cleanup() {
    if [ "$KEEP" = 1 ]; then
        printf 'prove: kept %s\n' "$CRATE" >&2
    else
        chmod -R u+w "$CRATE" 2>/dev/null || true
        rm -rf "$CRATE"
    fi
}
trap cleanup EXIT HUP INT TERM

mkdir -p "$CRATE/src"
cat >"$CRATE/Cargo.toml" <<TOML
[package]
name = "trust-frontend-proof"
version = "0.0.0"
edition = "2021"

[lib]
path = "src/lib.rs"

# Not a member of anything: an accidental parent workspace would change which
# lints and which fmt config this proof runs under.
[workspace]
TOML
cat >"$CRATE/rust-toolchain.toml" <<TOML
[toolchain]
channel = "$TOOLCHAIN_NAME"
TOML
write_clean_source() {
    cat >"$CRATE/src/lib.rs" <<'RS'
pub fn proof() -> u32 {
    7
}
RS
}
write_clean_source

printf 'prove: channel "%s", throwaway crate %s\n' "$TOOLCHAIN_NAME" "$CRATE"

# --- 1. the pin resolves -----------------------------------------------------
PINNED_SYSROOT=$( (cd "$CRATE" && rustc --print sysroot) 2>/dev/null || true)
[ -n "$PINNED_SYSROOT" ] || fail "\`rustc --print sysroot\` from a crate pinned to
  channel = \"$TOOLCHAIN_NAME\" produced nothing. The rustup shim is not resolving
  the pin — check that $HOME/.cargo/bin precedes any other rustc on PATH."
NAMED_SYSROOT=$(rustup run "$TOOLCHAIN_NAME" rustc --print sysroot 2>/dev/null || true)
[ -n "$NAMED_SYSROOT" ] || fail "\`rustup run $TOOLCHAIN_NAME rustc --print sysroot\` failed"

canonical() { python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$1" 2>/dev/null || printf '%s\n' "$1"; }
PINNED_REAL=$(canonical "$PINNED_SYSROOT")
NAMED_REAL=$(canonical "$NAMED_SYSROOT")
if [ "$PINNED_REAL" != "$NAMED_REAL" ]; then
    fail "the pin resolves to a DIFFERENT toolchain than '$TOOLCHAIN_NAME':
    rust-toolchain.toml -> $PINNED_REAL
    rustup run $TOOLCHAIN_NAME -> $NAMED_REAL
  Some other rustc is ahead of the rustup shim on PATH. This is the exact state
  in which a gate runs a different lint set under the same name."
fi
ok "channel = \"$TOOLCHAIN_NAME\" resolves to $PINNED_REAL"

BIN="$PINNED_REAL/bin"

# --- 2. the consumer's refusal predicate, in its own form --------------------
if [ ! -x "$BIN/${TOOLCHAIN_NAME}c" ] && [ ! -x "$BIN/$TOOLCHAIN_NAME" ]; then
    fail "neither $BIN/${TOOLCHAIN_NAME}c nor $BIN/$TOOLCHAIN_NAME is executable.
  This is the literal condition on which clean/scripts/rust_frontend.sh refuses
  to run a gate, so every pinned repo would refuse against this sysroot."
fi
ok "rust_frontend.sh's pinned-channel predicate holds ($BIN/${TOOLCHAIN_NAME}c)"

[ -x "$BIN/targo" ] || fail "$BIN/targo is missing: the package frontend that both
  gates below are invoked through. A sysroot built without \`extended = true\`
  looks like this."

# --- 3. format gate ----------------------------------------------------------
fmt_out="$CRATE/fmt.out"
if ! (cd "$CRATE" && "$BIN/targo" fmt --check) >"$fmt_out" 2>&1; then
    sed 's/^/    /' "$fmt_out" >&2
    fail "\`targo fmt --check\` failed on correctly formatted source. The format
  gate every pinned repo runs cannot pass against this toolchain."
fi
ok "format gate passes on clean source (targo fmt --check)"

cat >"$CRATE/src/misformatted.rs" <<'RS'
pub fn bad()->u32{   1 }
RS
cat >"$CRATE/src/lib.rs" <<'RS'
pub mod misformatted;

pub fn proof() -> u32 {
    7
}
RS
if (cd "$CRATE" && "$BIN/targo" fmt --check) >"$fmt_out" 2>&1; then
    fail "\`targo fmt --check\` PASSED on deliberately misformatted source. The gate
  is not checking anything, so its green means nothing."
fi
grep -q 'Diff in' "$fmt_out" || {
    sed 's/^/    /' "$fmt_out" >&2
    fail "\`targo fmt --check\` failed on misformatted source without reporting a diff —
  it errored for some other reason, so this is not a working format gate."
}
ok "format gate REJECTS misformatted source (it is a real gate, not a no-op)"
rm -f "$CRATE/src/misformatted.rs"
write_clean_source

# --- 4. lint gate ------------------------------------------------------------
# --offline: a proof must not depend on the network. The crate has no
# dependencies, so nothing legitimate needs to be fetched.
lint_out="$CRATE/lint.out"
if ! (cd "$CRATE" && "$BIN/targo" tippy --offline -- -D warnings) >"$lint_out" 2>&1; then
    sed 's/^/    /' "$lint_out" >&2
    fail "\`targo tippy -- -D warnings\` failed on clean source. This is the gate
  clean/trust-vc/aterm run as \`clippy --workspace -- -D warnings\`."
fi
ok "lint gate passes on clean source (targo tippy -- -D warnings)"

cat >"$CRATE/src/lib.rs" <<'RS'
pub fn proof() -> u32 {
    let unused_local = 1;
    7
}
RS
if (cd "$CRATE" && "$BIN/targo" tippy --offline -- -D warnings) >"$lint_out" 2>&1; then
    fail "\`targo tippy -- -D warnings\` PASSED on source with an unused local. The
  lint gate is not denying warnings, which is the whole contract."
fi
grep -q 'unused' "$lint_out" || {
    sed 's/^/    /' "$lint_out" >&2
    fail "\`targo tippy\` failed on the lint fixture without reporting the unused
  local — it errored for some other reason, so this is not a working lint gate."
}
ok "lint gate REJECTS a warning under -D warnings"
write_clean_source

printf '\nPROOF COMPLETE — channel "%s" resolves, and both gates the pinned repos\n' "$TOOLCHAIN_NAME"
printf 'run (format, lint under -D warnings) pass on clean source and fail on broken\n'
printf 'source through %s.\n' "$BIN"
exit 0
