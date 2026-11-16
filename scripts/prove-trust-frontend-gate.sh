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
#   1. RESOLUTION. The Trust frontend on PATH (`trustc`, which is what aterm
#      and the migrated gates run) and `rustup run <name>` (what a channel pin
#      and the publish gate's `rustup run trust targo` resolve) must be ONE
#      Trust build: the same sysroot, or byte-identical `trustc` and
#      `librustc_driver`. Every `rustc` on PATH that is not aterm's reroute
#      stub (identified positively, never by "printed nothing") must resolve
#      the pin to that build too; a shim that cannot resolve it FAILS. With
#      only the stub, nothing reads the pin, and the closing line says the pin
#      was not checked. (Until 2026-09-28 this step asked only the shim,
#      `rustc --print sysroot`, which the reroute stub fails on every aterm
#      machine although every gate resolved Trust.)
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

# NO SELF-HEALING OF PATH. The gates run with the PATH the machine actually
# has, so this proof does too: it never adds a directory to find a tool. It
# used to repair PATH from $HOME/.cargo/bin, print one stderr NOTE and go on to
# PROOF COMPLETE — a proof about a shell it had just constructed. A rustup that
# is installed but unreachable is a failure, and the fix is the user's to make.
#
# The durable line goes in ~/.zprofile (main's 0a345d9cc8): macOS's
# /etc/zprofile runs path_helper after ~/.zshenv and re-sorts /etc/paths.d
# ahead of what was added there, and ~/.zshrc is where aterm's reroute block
# lives. The line APPENDS, so wherever it runs it cannot get ahead of
# targo/trustc or the reroute stubs.
if ! command -v rustup >/dev/null 2>&1; then
    if [ -x "$HOME/.cargo/bin/rustup" ]; then
        fail "rustup is installed at $HOME/.cargo/bin/rustup, but $HOME/.cargo/bin is not
  on the PATH this proof inherited, so \`rustup run $TOOLCHAIN_NAME\` and every
  channel = \"$TOOLCHAIN_NAME\" pin read through a rustup shim fail to resolve here.

  Fix the environment, not the proof — APPEND it, so the Trust frontend
  (targo/trustc) and aterm's reroute stubs stay ahead of rustup's cargo/rustc:

      export PATH=\"\$PATH:\$HOME/.cargo/bin\"                          # this shell
      echo 'export PATH=\"\$PATH:\$HOME/.cargo/bin\"' >> ~/.zprofile    # every future login shell

  then re-run this script."
    fi
    echo "prove: rustup not found — \`rustup run $TOOLCHAIN_NAME\` and every channel pin need it" >&2
    exit 2
fi
if ! command -v trustc >/dev/null 2>&1; then
    fail "no \`trustc\` on PATH. The migrated gates run the Trust frontend by name
  (targo/trustc on PATH, as aterm provides them); install or repair the Trust
  toolchain (aterm pkg doctor)."
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

# --- 1. the frontend, the named toolchain and the pin are one Trust build ----
canonical() { python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$1" 2>/dev/null || printf '%s\n' "$1"; }
digest() { shasum -a 256 "$1" 2>/dev/null | cut -d' ' -f1; }
# The build identity of a sysroot: its trustc bytes and its compiler-driver bytes.
# Two directories with the same identity serve the same compiler (aterm keeps the
# PATH store and the rustup link as separate byte-identical copies).
build_identity() {
    printf 'trustc=%s' "$(digest "$1/bin/trustc")"
    for driver in "$1"/lib/librustc_driver-*; do
        [ -f "$driver" ] && printf ' driver=%s' "$(digest "$driver")"
    done
    printf '\n'
}
same_build() {
    [ "$(canonical "$1")" = "$(canonical "$2")" ] && return 0
    [ -x "$1/bin/trustc" ] && [ -x "$2/bin/trustc" ] || return 1
    [ "$(build_identity "$1")" = "$(build_identity "$2")" ]
}

FRONTEND_SYSROOT=$( (cd "$CRATE" && trustc --print sysroot) 2>/dev/null || true)
[ -n "$FRONTEND_SYSROOT" ] || fail "\`trustc --print sysroot\` (PATH frontend) produced nothing."
NAMED_SYSROOT=$(rustup run "$TOOLCHAIN_NAME" trustc --print sysroot 2>/dev/null || true)
[ -n "$NAMED_SYSROOT" ] || fail "\`rustup run $TOOLCHAIN_NAME trustc --print sysroot\` failed"
FRONTEND_REAL=$(canonical "$FRONTEND_SYSROOT")
NAMED_REAL=$(canonical "$NAMED_SYSROOT")
if ! same_build "$FRONTEND_REAL" "$NAMED_REAL"; then
    fail "the PATH Trust frontend and rustup's '$TOOLCHAIN_NAME' are DIFFERENT builds:
    trustc on PATH             -> $FRONTEND_REAL ($(build_identity "$FRONTEND_REAL"))
    rustup run $TOOLCHAIN_NAME -> $NAMED_REAL ($(build_identity "$NAMED_REAL"))
  A gate run by name and a gate run through the pin would then use different
  compilers under the same name. Re-link one to the other (aterm pkg doctor)."
fi
ok "trustc on PATH and \`rustup run $TOOLCHAIN_NAME\` are one build ($FRONTEND_REAL)"

# The pin, read through `rustc` — the name a rustup shim answers to. Exactly one
# `rustc` may be skipped: aterm's reroute stub, identified POSITIVELY (its
# directory carries `.atpkg-reroute-dir`, and its second line is the stub
# banner). It never reads a pin; in passthrough mode (`aterm --no-reroute`) it
# execs the first non-stub `rustc` behind it, so that one is the reader proved
# here. Any other `rustc` must resolve the pin to the build proved above: a shim
# that prints no sysroot — e.g. a stale link, "'rustc' is not installed for the
# custom toolchain 'trust'" — is a FAILURE, never "no shim on PATH".
is_reroute_stub() {
    [ -f "$(dirname "$1")/.atpkg-reroute-dir" ] && return 0
    [ -f "$1" ] && [ -r "$1" ] && [ "$(sed -n 2p "$1" 2>/dev/null)" = '# atpkg reroute stub v1' ]
}
# The first `rustc` on PATH that is not a reroute stub, skipping every reroute
# directory the way the stub's own passthrough loop does.
first_non_stub_rustc() {
    _ifs=$IFS
    IFS=:
    set -f
    for _d in $PATH; do
        case $_d in /*) ;; *) continue ;; esac
        [ -f "$_d/.atpkg-reroute-dir" ] && continue
        if [ -x "$_d/rustc" ] && [ ! -d "$_d/rustc" ] && ! is_reroute_stub "$_d/rustc"; then
            IFS=$_ifs
            set +f
            printf '%s\n' "$_d/rustc"
            return 0
        fi
    done
    IFS=$_ifs
    set +f
    return 1
}

PIN_READER=$(first_non_stub_rustc || true)
PATH_RUSTC=$(command -v rustc 2>/dev/null || true)
PIN_NOTE=
if [ -n "$PIN_READER" ]; then
    PINNED_SYSROOT=$( (cd "$CRATE" && "$PIN_READER" --print sysroot) 2>/dev/null || true)
    if [ -z "$PINNED_SYSROOT" ]; then
        fail "\`$PIN_READER --print sysroot\`, run in a crate pinned to channel = \"$TOOLCHAIN_NAME\",
  produced no sysroot. That \`rustc\` is not aterm's reroute stub, so it is the
  thing that reads the pin on this PATH, and it cannot resolve it. A rustup shim
  with a stale link fails exactly this way (\"'rustc' is not installed for the
  custom toolchain '$TOOLCHAIN_NAME'\"): run \`aterm pkg doctor\`, then \`aterm pkg repair\`."
    fi
    PINNED_REAL=$(canonical "$PINNED_SYSROOT")
    if ! same_build "$PINNED_REAL" "$FRONTEND_REAL"; then
        fail "the pin resolves to a DIFFERENT toolchain than the Trust frontend:
    rust-toolchain.toml (via $PIN_READER) -> $PINNED_REAL
    trustc on PATH -> $FRONTEND_REAL
  Some other rustc is ahead of the rustup shim on PATH. This is the exact state
  in which a gate runs a different lint set under the same name.

  Fix the environment, not the proof: uninstall that rustc if nothing needs it,
  or put $HOME/.cargo/bin ahead of its directory in your login profile, but
  behind targo/trustc and aterm's reroute stubs."
    fi
    ok "channel = \"$TOOLCHAIN_NAME\" read by $PIN_READER resolves to the same build"
elif [ -z "$PATH_RUSTC" ]; then
    PIN_NOTE="no \`rustc\` is on PATH at all"
    ok "no pin reader on PATH: $PIN_NOTE; gates run the PATH frontend"
elif is_reroute_stub "$PATH_RUSTC"; then
    PIN_NOTE="the only \`rustc\` on PATH is aterm's reroute stub ($PATH_RUSTC), which reads no pin"
    ok "no pin reader on PATH: $PIN_NOTE; gates run the PATH frontend"
else
    fail "\`rustc\` on PATH is $PATH_RUSTC, reached through a relative PATH entry:
  it is not aterm's reroute stub, and this proof does not judge a relative PATH."
fi

BIN="$FRONTEND_REAL/bin"

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

if [ -z "$PIN_NOTE" ]; then
    printf '\nPROOF COMPLETE — channel "%s" resolves, and both gates the pinned repos\n' "$TOOLCHAIN_NAME"
else
    printf '\nPROOF COMPLETE — the PATH Trust frontend and `rustup run %s` are one build.\n' "$TOOLCHAIN_NAME"
    printf 'The channel pin itself was NOT read: %s. Both gates the pinned repos\n' "$PIN_NOTE"
fi
printf 'run (format, lint under -D warnings) pass on clean source and fail on broken\n'
printf 'source through %s.\n' "$BIN"
exit 0
