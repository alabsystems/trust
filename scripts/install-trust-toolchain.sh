#!/bin/sh
# install-trust-toolchain.sh — ONE command from "this machine has no Trust
# toolchain" to "the pinned `trust` channel resolves and its gates run".
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#
# WHY THIS EXISTS
# ---------------
# Three repositories pin `channel = "trust"` in `rust-toolchain.toml` — clean,
# trust-vc, aterm — and their format/lint gates need `trustfmt` and `tippy` out
# of a Trust sysroot. `clean/scripts/rust_frontend.sh` now REFUSES to run when
# that pin did not resolve, because the alternative is worse: measured
# 2026-08-22, with no `trust` toolchain linked the workspace gate ran stock
# `cargo-clippy`, reported clean, and `targo tippy` had six `-D warnings`
# violations on the same tree. The refusal is right. What was missing was a
# scripted way to CURE it: the recipe existed only as a sequence carried in
# somebody's head —
#
#   worktree of trust at origin/main
#   copy the gitignored bootstrap.toml from a machine that already had one
#   git submodule update --init --recursive
#   LIBRARY_PATH=/opt/homebrew/lib python3 x.py build --stage 1   (15-36 min)
#   rustup toolchain link trust BUILDDIR/build/<host-triple>/stage1
#
# — every step of which has a silent failure mode. This script is that recipe
# with each step checked, and it OWNS none of the checking:
#
#   output contract   tools/verify-toolchain.sh        (the binaries exist AND run)
#   link rules        scripts/rustup-link-trust.sh     (same-surface aliases, no
#                                                       genesis shim, no stock names)
#   proof             scripts/prove-trust-frontend-gate.sh
#                                                      (a gate that needs the Trust
#                                                       frontend actually passes,
#                                                       and can still fail)
#
# IDEMPOTENT AND RESUMABLE, because a 15-36 minute build that restarts from zero
# after an interruption is not a recovery path. Every step is a no-op when its
# postcondition already holds: an existing build tree is reused, an existing
# `bootstrap.toml` is VALIDATED rather than rewritten, `x.py` resumes
# incrementally, and `rustup toolchain link` onto the same sysroot is a rewrite
# of one symlink. Re-running this script after a successful run exits 0 having
# changed nothing.
#
# WHAT IT DELIBERATELY DOES NOT DO
# --------------------------------
#   * It does not fetch the private stage0 seed. `scripts/recreate_bootstrap.py
#     --require-seed` owns that path and it needs authenticated access to a
#     private release. This script bootstraps from a host Rust instead
#     (`[build] rustc/cargo` below), which is the GENESIS lineage: usable as a
#     working toolchain, never citable as Trust-from-Trust or as release
#     evidence. See INSTALL.md.
#   * It does not produce release evidence of any kind. `--stage 1` is a
#     developer artifact; docs/rustup-toolchain-link.md says so and still does.
#   * It never deletes a build tree, a sysroot, or a rustup toolchain.
#
# Usage:
#   scripts/install-trust-toolchain.sh [options]
#
#   --build-dir DIR   where to build (default: this repo). If DIR does not
#                     exist and this repo is a git checkout, it is created as a
#                     detached worktree at HEAD — which is how the toolchain
#                     tree on the first machine was made, and it keeps a
#                     20-minute build out of the tree you are editing.
#   --stage N         1 (default) or 2. Stage 1 already carries the whole tier-2
#                     surface this exists to deliver (trustfmt, targo-fmt, tippy,
#                     targo-tippy, tippy-driver, trust-analyzer, and the three
#                     verification backends) — measured on the first machine's
#                     stage1 sysroot, which passes tools/verify-toolchain.sh in
#                     full. Stage 2 costs hours more and adds no gate this
#                     script promises.
#   --name NAME       rustup toolchain name (default: trust — the pinned channel)
#   --link-only       skip submodules and x.py; verify + link + prove a tree that
#                     is already built
#   --skip-proof      do everything except the final gate proof (CI split lanes)
#   --jobs N          x.py -j (default: memory-aware, see below)
#   --dry-run         print the plan and touch nothing
#
# Environment: TRUST_INSTALL_BUILD_DIR, TRUST_INSTALL_NAME, TRUST_JOBS,
# TRUST_STAGE0_RUSTC (host Rust to bootstrap from), TRUST_HOST_TRIPLE.

set -eu

SCRIPT_DIR=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH='' cd -- "$SCRIPT_DIR/.." && pwd)

BUILD_DIR=${TRUST_INSTALL_BUILD_DIR:-$REPO_ROOT}
STAGE=1
TOOLCHAIN_NAME=${TRUST_INSTALL_NAME:-trust}
JOBS=${TRUST_JOBS:-}
DRY_RUN=0
LINK_ONLY=0
RUN_PROOF=1
STEP_NO=0
# Set when preflight has to put the rustup shim on PATH for this process. The
# repair dies with the process, so the closing summary has to say so out loud:
# everything after it — including the proof — ran in an environment this script
# manufactured, not the one the pinned repositories will get.
PATH_REPAIRED=0

usage() {
    sed -n '/^# Usage:/,/^# Environment:/p' "$0" | sed 's/^# \{0,1\}//'
}

say()  { printf '%s\n' "$*"; }
warn() { printf 'install-trust-toolchain: WARNING: %s\n' "$*" >&2; }
die()  { printf 'install-trust-toolchain: error: %s\n' "$*" >&2; exit 1; }

step() {
    STEP_NO=$((STEP_NO + 1))
    printf '\n=== step %s/8  %s\n' "$STEP_NO" "$*"
}

# Every mutating command goes through run(): it is the single place --dry-run is
# honoured, so a new step cannot forget to respect it.
run() {
    if [ "$DRY_RUN" = 1 ]; then
        printf '  would run: %s\n' "$*"
        return 0
    fi
    printf '  + %s\n' "$*"
    "$@"
}

while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help) usage; exit 0 ;;
        --build-dir) shift; [ $# -gt 0 ] || die "--build-dir requires a path"; BUILD_DIR=$1 ;;
        --build-dir=*) BUILD_DIR=${1#--build-dir=} ;;
        --stage) shift; [ $# -gt 0 ] || die "--stage requires 1 or 2"; STAGE=$1 ;;
        --stage=*) STAGE=${1#--stage=} ;;
        --name) shift; [ $# -gt 0 ] || die "--name requires a toolchain name"; TOOLCHAIN_NAME=$1 ;;
        --name=*) TOOLCHAIN_NAME=${1#--name=} ;;
        --jobs) shift; [ $# -gt 0 ] || die "--jobs requires a number"; JOBS=$1 ;;
        --jobs=*) JOBS=${1#--jobs=} ;;
        --link-only) LINK_ONLY=1 ;;
        --skip-proof) RUN_PROOF=0 ;;
        --dry-run) DRY_RUN=1 ;;
        *) printf 'install-trust-toolchain: unknown argument: %s\n' "$1" >&2; usage >&2; exit 2 ;;
    esac
    shift
done

case "$STAGE" in
    1|2) ;;
    *) die "--stage must be 1 or 2 (got $STAGE)" ;;
esac
[ -n "$TOOLCHAIN_NAME" ] || die "--name must not be empty"
case "$JOBS" in
    ''|*[!0-9]*) [ -z "$JOBS" ] || die "--jobs must be a whole number (got $JOBS)" ;;
esac

# ---------------------------------------------------------------------------
# 1. PREFLIGHT
#
# The two failures this catches are the two that make a linked toolchain look
# installed and behave as if it were not:
#   * rustup absent          — nothing can link, and `+trust` means nothing
#   * ~/.cargo/bin off PATH  — the rustup SHIM is what reads rust-toolchain.toml.
#                              With a real rustc ahead of it (Homebrew's, on this
#                              machine) `rustc` is some other compiler, the pin is
#                              never consulted, and gates silently run the wrong
#                              lint set. Measured on this host: the default PATH
#                              has no ~/.cargo/bin and `command -v rustc` is
#                              /opt/homebrew/bin/rustc.
# ---------------------------------------------------------------------------
step "preflight: rustup, PATH, python3, git"

RUSTUP=$(command -v rustup 2>/dev/null || true)
if [ -z "$RUSTUP" ]; then
    if [ -x "$HOME/.cargo/bin/rustup" ]; then
        warn "rustup is installed at $HOME/.cargo/bin/rustup but $HOME/.cargo/bin is NOT on PATH."
        warn "Using it for this run. Add it permanently or every future +$TOOLCHAIN_NAME lookup fails:"
        warn "    export PATH=\"\$HOME/.cargo/bin:\$PATH\"    # in ~/.zshrc or ~/.bashrc"
        PATH="$HOME/.cargo/bin:$PATH"
        export PATH
        PATH_REPAIRED=1
        RUSTUP="$HOME/.cargo/bin/rustup"
    else
        die "rustup not found. Install it first (brew install rustup, or https://rustup.rs),
  then re-run this script. rustup is the toolchain SELECTOR: without it a
  rust-toolchain.toml pin of channel = \"$TOOLCHAIN_NAME\" cannot resolve to anything."
    fi
fi
say "  rustup:  $RUSTUP"

RUSTUP_BIN_DIR=$(CDPATH='' cd -- "$(dirname -- "$RUSTUP")" && pwd)
RUSTC_ON_PATH=$(command -v rustc 2>/dev/null || true)
if [ -n "$RUSTC_ON_PATH" ]; then
    RUSTC_DIR=$(CDPATH='' cd -- "$(dirname -- "$RUSTC_ON_PATH")" && pwd)
    if [ "$RUSTC_DIR" != "$RUSTUP_BIN_DIR" ]; then
        warn "\`rustc\` on PATH is $RUSTC_ON_PATH, not the rustup shim in $RUSTUP_BIN_DIR."
        warn "A non-shim rustc SHADOWS the pin: rust-toolchain.toml is read by the shim and"
        warn "by nothing else, so gates in clean/trust-vc/aterm would resolve a different"
        warn "compiler than the one this script is about to link. Put the shim first:"
        warn "    export PATH=\"$RUSTUP_BIN_DIR:\$PATH\""
    fi
fi

command -v python3 >/dev/null 2>&1 || die "python3 not found — x.py is a Python program"
command -v git >/dev/null 2>&1 || die "git not found — the first-party/ submodules cannot be initialised"

# The host Rust that plays stage0. Probed with cwd=/ so a rust-toolchain.toml in
# any repo cannot make the probe resolve through the very toolchain we are here
# to build (which would fail, misleadingly, before it exists).
find_stage0_rustc() {
    if [ -n "${TRUST_STAGE0_RUSTC:-}" ]; then
        [ -x "$TRUST_STAGE0_RUSTC" ] || die "TRUST_STAGE0_RUSTC is not executable: $TRUST_STAGE0_RUSTC"
        printf '%s\n' "$TRUST_STAGE0_RUSTC"
        return 0
    fi
    for _prefix in "$(brew --prefix 2>/dev/null || true)" /opt/homebrew /usr/local; do
        [ -n "$_prefix" ] || continue
        _cand="$_prefix/bin/rustc"
        # Never accept the rustup shim as stage0: it dispatches back through
        # rustup and, once `trust` is linked, back into the compiler being built.
        [ -x "$_cand" ] || continue
        [ "$(CDPATH='' cd -- "$(dirname -- "$_cand")" && pwd)" = "$RUSTUP_BIN_DIR" ] && continue
        if (cd / && "$_cand" -vV >/dev/null 2>&1); then
            printf '%s\n' "$_cand"
            return 0
        fi
    done
    # Fall back to a rustup-managed upstream toolchain if one is installed.
    for _chan in stable beta nightly; do
        _sysroot=$(cd / && "$RUSTUP" run "$_chan" rustc --print sysroot 2>/dev/null || true)
        if [ -n "$_sysroot" ] && [ -x "$_sysroot/bin/rustc" ]; then
            printf '%s\n' "$_sysroot/bin/rustc"
            return 0
        fi
    done
    return 1
}

STAGE0_RUSTC=$(find_stage0_rustc || true)
STAGE0_BIN=""
if [ -n "$STAGE0_RUSTC" ]; then
    STAGE0_BIN=$(CDPATH='' cd -- "$(dirname -- "$STAGE0_RUSTC")" && pwd)
    say "  host Rust (stage0): $STAGE0_RUSTC  [$( (cd / && "$STAGE0_RUSTC" --version) 2>/dev/null || echo '?')]"
fi

HOST_TRIPLE=${TRUST_HOST_TRIPLE:-}
if [ -z "$HOST_TRIPLE" ] && [ -n "$STAGE0_RUSTC" ]; then
    HOST_TRIPLE=$( (cd / && "$STAGE0_RUSTC" -vV) 2>/dev/null | sed -n 's/^host: //p' | head -n 1)
fi
if [ -z "$HOST_TRIPLE" ]; then
    case "$(uname -s)-$(uname -m)" in
        Darwin-arm64)          HOST_TRIPLE=aarch64-apple-darwin ;;
        Darwin-x86_64)         HOST_TRIPLE=x86_64-apple-darwin ;;
        Linux-x86_64)          HOST_TRIPLE=x86_64-unknown-linux-gnu ;;
        Linux-aarch64|Linux-arm64) HOST_TRIPLE=aarch64-unknown-linux-gnu ;;
        *) die "cannot determine the host triple; set TRUST_HOST_TRIPLE" ;;
    esac
fi
say "  host triple: $HOST_TRIPLE"

# Homebrew LLVM, when present, is what makes this a 15-36 minute build instead of
# a multi-hour one: `[target.<triple>] llvm-config` links an existing LLVM rather
# than building src/llvm-project. Same LLVM the first machine's stage1 was built
# against.
LLVM_CONFIG=${TRUST_LLVM_CONFIG:-}
if [ -z "$LLVM_CONFIG" ]; then
    for _cand in \
        "$(brew --prefix llvm 2>/dev/null || true)/bin/llvm-config" \
        /opt/homebrew/opt/llvm/bin/llvm-config \
        /usr/local/opt/llvm/bin/llvm-config
    do
        case "$_cand" in /bin/llvm-config) continue ;; esac
        if [ -x "$_cand" ]; then LLVM_CONFIG=$_cand; break; fi
    done
fi
if [ -n "$LLVM_CONFIG" ]; then
    say "  llvm-config: $LLVM_CONFIG  [$("$LLVM_CONFIG" --version 2>/dev/null || echo '?')]"
else
    warn "no external llvm-config found. The build will compile src/llvm-project in-tree:"
    warn "hours, ~1.9 GB of sources, and it needs cmake + ninja. On macOS,"
    warn "\`brew install llvm\` first and re-run — that is the difference between a"
    warn "15-36 minute build and an afternoon."
fi

# ---------------------------------------------------------------------------
# 2. BUILD TREE
# ---------------------------------------------------------------------------
step "build tree: $BUILD_DIR"

if [ -e "$BUILD_DIR" ]; then
    [ -d "$BUILD_DIR" ] || die "--build-dir exists and is not a directory: $BUILD_DIR"
    [ -f "$BUILD_DIR/x.py" ] || die "no x.py in $BUILD_DIR — that is not a Trust checkout"
    say "  reusing existing checkout"
else
    if git -C "$REPO_ROOT" rev-parse --git-dir >/dev/null 2>&1; then
        say "  creating a detached worktree at HEAD (keeps the build out of the tree you edit)"
        run git -C "$REPO_ROOT" worktree add --detach "$BUILD_DIR" HEAD
    else
        die "$BUILD_DIR does not exist and $REPO_ROOT is not a git checkout, so it cannot
  be created as a worktree. Clone Trust there yourself, or pass an existing tree."
    fi
fi
if [ -d "$BUILD_DIR" ]; then
    BUILD_DIR=$(CDPATH='' cd -- "$BUILD_DIR" && pwd -P)
fi

SYSROOT="$BUILD_DIR/build/$HOST_TRIPLE/stage$STAGE"
BOOTSTRAP_TOML="$BUILD_DIR/bootstrap.toml"
# The contract scripts come from THIS repo, not from the build tree, even when
# the build tree has its own copies. They are versioned as one unit with this
# script and the policy they encode moves: measured 2026-08-22, pointing
# --build-dir at a tree 14 commits behind main made that tree's own
# verify-toolchain.sh reject a sysroot ITS OWN bootstrap had produced —
#
#   FORBIDDEN: forbidden stock or retired public entrypoint is present:
#              .../stage1/bin/rustdoc
#
# — because 76d408e1cd (bootstrap emits `rustdoc` into every stage >= 1, since
# cargo spawns it by name for doctests) was in that tree while f12893ca49 (the
# gate admitting `rustdoc` as an alias rather than a stock name) was not. Taking
# the check from whichever tree you happened to point at means the decision to
# link is made by an arbitrary commit. Taking it from here means it is made by
# the version this script was tested against; a build tree older than the
# contract then fails with a message naming the artifact, which is the honest
# outcome.
VERIFY_SCRIPT="$REPO_ROOT/tools/verify-toolchain.sh"
LINK_SCRIPT="$REPO_ROOT/scripts/rustup-link-trust.sh"
PROVE_SCRIPT="$SCRIPT_DIR/prove-trust-frontend-gate.sh"
# Same rule for the submodule classifier, and for the same reason: it decides
# whether a destructive checkout is allowed to happen, so which commit's copy of
# that decision runs must not depend on where --build-dir happens to point. It
# is driven with `--root "$BUILD_DIR"`, an interface it already has.
SYNC_SCRIPT="$SCRIPT_DIR/submodule_sync.sh"
[ -f "$VERIFY_SCRIPT" ] || die "missing $VERIFY_SCRIPT — this is not a Trust checkout"
[ -f "$LINK_SCRIPT" ] || die "missing $LINK_SCRIPT — this is not a Trust checkout"
[ -f "$PROVE_SCRIPT" ] || die "missing $PROVE_SCRIPT"
[ -f "$SYNC_SCRIPT" ] || die "missing $SYNC_SCRIPT — this is not a Trust checkout"

# ---------------------------------------------------------------------------
# 3. bootstrap.toml
#
# `bootstrap.toml` is gitignored — it holds machine-absolute paths — so every
# machine writes its own, and every machine has therefore been one typo away
# from failure 6: `[build] tools = [...]` is an ALLOWLIST
# (src/bootstrap/src/core/build_steps/tool.rs:900 l2_backend_enabled, absent =
# ALL, PRESENT = ONLY THESE). A build that names any tool silently drops the
# verification backends and still exits 0. So this step generates a file with
# `extended = true` and NO tools list, and refuses to build against one that has
# a list rather than quietly producing a toolchain that cannot verify.
#
# WHY NOT DERIVE IT FROM bootstrap.example.toml. That file is 1116 lines of
# commented-out reference documentation for every setting bootstrap has; the
# config that actually builds this toolchain is the twenty lines below, and
# "uncomment these six keys, edit four paths, leave the other 1100 lines alone"
# is a transformation that breaks the first time upstream renumbers the example.
# The example stays the reference; this stays the generator, and the [build]
# section it emits is pinned to the working tree's by
# scripts/tests/install_trust_toolchain_test.sh.
# ---------------------------------------------------------------------------
step "bootstrap.toml"

emit_bootstrap_toml() {
    cat <<TOML
# Written by scripts/install-trust-toolchain.sh ($(date -u '+%Y-%m-%d'))
# on host $HOST_TRIPLE. This file is gitignored: it holds machine-absolute
# paths. Regenerate by deleting it and re-running that script.
[build]
# Stage0 is a HOST Rust, not the pinned private trust-stage0 seed. That makes
# everything built here GENESIS lineage: a working toolchain, never citable as
# Trust-from-Trust or as release evidence (INSTALL.md). Use
# scripts/recreate_bootstrap.py --require-seed for the seed-first path.
rustc   = "$STAGE0_BIN/rustc"
cargo   = "$STAGE0_BIN/cargo"
rustfmt = "$STAGE0_BIN/rustfmt"
rustdoc = "$STAGE0_BIN/rustdoc"
docs = false
submodules = false
# Build the full Trust toolchain surface (trustfmt, tippy, trust-analyzer, ...).
# Deliberately NO \`tools = [...]\` list: tool.rs:900 l2_backend_enabled treats that
# list as an ALLOWLIST (absent = ALL, present = ONLY THESE), which is how the
# verification backends got silently dropped before. Absent means all.
extended = true

[llvm]
download-ci-llvm = false
TOML
    if [ -n "$LLVM_CONFIG" ]; then
        cat <<TOML

[target.$HOST_TRIPLE]
llvm-config = "$LLVM_CONFIG"
TOML
    fi
    cat <<TOML

[rust]
channel = "trust"
deny-warnings = false
TOML
}

if [ -f "$BOOTSTRAP_TOML" ]; then
    say "  reusing existing $BOOTSTRAP_TOML"
    if grep -Eq '^[[:space:]]*(build\.)?tools[[:space:]]*=' "$BOOTSTRAP_TOML"; then
        die "$BOOTSTRAP_TOML declares a [build] tools list.

  tool.rs:900 l2_backend_enabled reads that list as an ALLOWLIST: absent means
  ALL, present means ONLY THESE. A list is how a green \`x.py build\` shipped a
  sysroot with no ay/ty/clean and no formatter — see tools/verify-toolchain.sh.
  Delete the \`tools = [...]\` line (that is the fix; it is not a narrowing knob)
  or, if the narrow surface is deliberate, build it by hand and link it with
  scripts/rustup-link-trust.sh --sysroot."
    fi
    if ! grep -Eq '^[[:space:]]*(build\.)?extended[[:space:]]*=[[:space:]]*true' "$BOOTSTRAP_TOML"; then
        die "$BOOTSTRAP_TOML does not set [build] extended = true.

  Without it the tier-2 surface this script exists to deliver — trustfmt,
  targo-fmt, tippy, targo-tippy, tippy-driver, trust-analyzer,
  trust-analyzer-proc-macro-srv — is never built, and the gates in clean,
  trust-vc and aterm have nothing to run. Add \`extended = true\` under [build]."
    fi
    say "  checked: extended = true, no [build] tools allowlist"
elif [ "$LINK_ONLY" = 1 ]; then
    say "  --link-only: not generating a config for a tree that is already built"
else
    [ -n "$STAGE0_BIN" ] || die "no host Rust found to bootstrap from.

  Install one (macOS: brew install rust; or rustup toolchain install stable) or
  point TRUST_STAGE0_RUSTC at a rustc. x.py cannot start without a stage0
  compiler, and the seed-first alternative needs authenticated access to the
  private trust-stage0 release (INSTALL.md)."
    if [ "$DRY_RUN" = 1 ]; then
        say "  would write $BOOTSTRAP_TOML:"
        emit_bootstrap_toml | sed 's/^/  | /'
    else
        say "  + writing $BOOTSTRAP_TOML"
        emit_bootstrap_toml >"$BOOTSTRAP_TOML"
    fi
fi

# ---------------------------------------------------------------------------
# 4. SUBMODULES
#
# `submodules = false` above means x.py will NOT fix these for you, by design:
# the repo's own scripts/submodule_sync.sh is the tool that can tell BEHIND
# (lossless to restore) from AHEAD/DIVERGENT (restoring destroys commits), and a
# blanket `git submodule update` cannot. Initialising is safe on a fresh tree;
# the sync report is what catches the drifted case, whose signature is a compile
# error deep in unrelated code (CLAUDE.md, "Build").
#
# CLASSIFY BEFORE MUTATING — the ordering IS the guard.
# This step used to run `git submodule update --init --recursive` first and the
# classifier second, which made the guard unfireable: the blanket recursive
# update checks every drifted worktree back onto its pin, so by the time
# submodule_sync.sh looked, the tree was in sync and it returned 0. Measured
# 2026-08-23 on a purpose-built fixture (superproject, first-party/sub pinned at
# C, worktree detached one commit past C on a commit no ref holds):
#
#   before the update:  AHEAD, 1 ahead, NOT ANCHORED   -> exit 2   (would die)
#   after  the update:  "all 1 submodule worktrees are at the pins" -> exit 0
#
# and the unlanded commit was held by no ref afterwards. The message this step
# prints on failure — "restoring it would destroy commits" — described a
# destruction the step had already performed itself. So the classification now
# runs FIRST, on the untouched tree, and the update runs only after it has
# cleared. Nothing is initialised or checked out on the refusal path.
#
# The fallback matters as much as the classifier. submodule_sync.sh is a bash
# program; if bash is missing, the ambiguity it resolves does not go away, so
# fall back to `git submodule status --recursive`, which cannot tell BEHIND from
# AHEAD but CAN tell "differs from the pin" (a leading `+`) from "does not"
# (a leading `-` for never-checked-out, or a space for in-sync). No `+` means
# there is provably nothing to lose and the update is authorised; any `+` that
# nothing could classify is refused, because that is the state the guard is for.
# ---------------------------------------------------------------------------

# Leading-`+` modules per `git submodule status`, i.e. worktrees that disagree
# with the recorded pin in the direction git will not name.
count_status_plus_modules() {
    git -C "$BUILD_DIR" submodule status --recursive 2>/dev/null \
        | awk '/^\+/ { n++ } END { print n + 0 }'
}

if [ "$LINK_ONLY" = 1 ]; then
    step "submodules — skipped (--link-only)"
else
    step "submodules: classify drift FIRST, then init first-party/ and the rest"
    if [ "$DRY_RUN" = 1 ]; then
        say "  would run: bash $SYNC_SCRIPT --root $BUILD_DIR   (classification, BEFORE any mutation)"
        say "  would run: git -C $BUILD_DIR submodule update --init --recursive"
    else
        sync_rc=0
        if command -v bash >/dev/null 2>&1; then
            printf '  + bash %s --root %s\n' "$SYNC_SCRIPT" "$BUILD_DIR"
            bash "$SYNC_SCRIPT" --root "$BUILD_DIR" || sync_rc=$?
        else
            sync_rc=126
        fi
        case "$sync_rc" in
            0) say "  every submodule worktree is already at its recorded pin" ;;
            1) say "  drift found, and every drifted module is provably lossless to restore" ;;
            2) die "scripts/submodule_sync.sh exited 2 — and it ran BEFORE anything was
  touched, so nothing here has been initialised, checked out or moved.

  At least one submodule worktree is AHEAD of or DIVERGENT from the pin recorded
  at superproject HEAD, holding commits that no durable ref holds. The
  'git submodule update --init --recursive' this step was about to run would move
  HEAD off exactly those commits. The report above names each module and the
  commits at stake.

  Resolve it, then re-run this script:
      bash $SYNC_SCRIPT --root $BUILD_DIR            # the same report
      bash $SYNC_SCRIPT --root $BUILD_DIR --restore  # moves ONLY the provably lossless subset" ;;
            *)
                # The classifier could not run (3 = usage/environment, 126 = no
                # bash, anything else = it broke). Do not treat that as a clean
                # bill of health, and do not refuse a tree that has nothing to
                # lose either: ask git the one question it can answer.
                _plus=$(count_status_plus_modules)
                if [ "$_plus" -gt 0 ]; then
                    die "the submodule classifier could not run (exit $sync_rc), and
  \`git submodule status --recursive\` reports $_plus submodule worktree(s) that
  DIFFER from the pin recorded at HEAD. git prints one '+' for BEHIND, AHEAD and
  DIVERGENT alike, so nothing here can tell a lossless restore from one that
  discards unlanded commits — and the update this step runs next is that restore.
  Refusing while it is ambiguous. Nothing has been touched.

  Run the classifier yourself (it needs bash):
      bash $SYNC_SCRIPT --root $BUILD_DIR"
                fi
                warn "the submodule classifier could not run (exit $sync_rc); \`git submodule status\`"
                warn "reports no worktree differing from its pin, so the init below can lose nothing."
                ;;
        esac
        run git -C "$BUILD_DIR" submodule update --init --recursive
    fi
fi

# ---------------------------------------------------------------------------
# 5. BUILD
#
# Job count is capped by BOTH cores and RAM at ~5 GB/job, the same formula
# scripts/dev-build.sh uses and for the same measured reason: defaulting to
# hw.ncpu on a 24 GB host exhausted the VM compressor and panicked the machine.
#
# LIBRARY_PATH carries the Homebrew lib dir because an external LLVM links
# against Homebrew's libzstd/libxml2; without it the build fails at link time
# with a missing -lzstd rather than anything that mentions LLVM.
#
# The build takes the repo's build-tree lock itself — the lock lives inside x.py
# (scripts/trust_build_lock.sh, CLAUDE.md "Build"), so a concurrent measurement
# sweep refuses this build rather than racing it. Set TRUST_BUILD_LOCK_WAIT to
# block instead of refusing.
# ---------------------------------------------------------------------------
if [ "$LINK_ONLY" = 1 ]; then
    step "x.py build — skipped (--link-only)"
else
    step "x.py build --stage $STAGE  (15-36 min cold; a re-run resumes)"
    if [ -z "$JOBS" ]; then
        _ncpu=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 8)
        _mem=$(sysctl -n hw.memsize 2>/dev/null \
            || awk '/MemTotal/ {print $2*1024; exit}' /proc/meminfo 2>/dev/null \
            || echo $((16 * 1024 * 1024 * 1024)))
        _memjobs=$(( _mem / (5 * 1024 * 1024 * 1024) ))
        [ "$_memjobs" -lt 1 ] && _memjobs=1
        if [ "$_ncpu" -lt "$_memjobs" ]; then JOBS=$_ncpu; else JOBS=$_memjobs; fi
    fi
    say "  jobs: $JOBS"
    BREW_LIB=""
    for _p in "$(brew --prefix 2>/dev/null || true)" /opt/homebrew /usr/local; do
        [ -n "$_p" ] || continue
        if [ -d "$_p/lib" ]; then BREW_LIB="$_p/lib"; break; fi
    done
    if [ -n "$BREW_LIB" ]; then
        LIBRARY_PATH="$BREW_LIB${LIBRARY_PATH:+:$LIBRARY_PATH}"
        export LIBRARY_PATH
        say "  LIBRARY_PATH=$LIBRARY_PATH"
    fi
    _build_start=$(date +%s)
    if [ "$DRY_RUN" = 1 ]; then
        say "  would run: (cd $BUILD_DIR && python3 x.py build --stage $STAGE -j $JOBS)"
    else
        printf '  + (cd %s && python3 x.py build --stage %s -j %s)\n' "$BUILD_DIR" "$STAGE" "$JOBS"
        if ! (cd "$BUILD_DIR" && python3 x.py build --stage "$STAGE" -j "$JOBS"); then
            die "x.py build failed. Nothing here is lost: fix the cause and re-run this
  script — x.py is incremental and picks up where it stopped."
        fi
        _elapsed=$(( $(date +%s) - _build_start ))
        say "  build finished in $(( _elapsed / 60 ))m $(( _elapsed % 60 ))s"
    fi
fi

# ---------------------------------------------------------------------------
# 6. VERIFY THE OUTPUT CONTRACT
#
# A build is not successful because it exited 0. tools/verify-toolchain.sh runs
# every required binary and fails on a present-but-broken one, which is the
# failure `[ -f ]` cannot see.
# ---------------------------------------------------------------------------
step "verify the output contract (tools/verify-toolchain.sh)"

if [ ! -d "$SYSROOT" ] && [ -d "$BUILD_DIR/build/host/stage$STAGE" ]; then
    say "  $SYSROOT absent; falling back to the build/host symlink"
    SYSROOT="$BUILD_DIR/build/host/stage$STAGE"
fi
say "  sysroot: $SYSROOT"
if [ "$DRY_RUN" = 1 ]; then
    say "  would run: sh $VERIFY_SCRIPT $SYSROOT"
else
    [ -d "$SYSROOT" ] || die "no sysroot at $SYSROOT — the build did not produce stage$STAGE"
    sh "$VERIFY_SCRIPT" "$SYSROOT" || die "the output contract is VIOLATED; refusing to link this sysroot"
fi

# ---------------------------------------------------------------------------
# 7. LINK
#
# --sysroot, not a stage selector: the stage selector resolves through the build
# tree's own build/host symlink, and this script may be linking a tree that is
# not the repo it was run from. --sysroot also holds an EXTERNAL root to the full
# same-surface alias contract with repair forbidden — exactly right here, because
# a root that needs repairing to be linkable is a root that was not built
# completely.
# ---------------------------------------------------------------------------
step "link as rustup toolchain '$TOOLCHAIN_NAME'"

if [ "$DRY_RUN" = 1 ]; then
    say "  would run: sh $LINK_SCRIPT --name $TOOLCHAIN_NAME --sysroot $SYSROOT"
else
    sh "$LINK_SCRIPT" --name "$TOOLCHAIN_NAME" --sysroot "$SYSROOT"
fi

# ---------------------------------------------------------------------------
# 8. PROVE IT
# ---------------------------------------------------------------------------
if [ "$RUN_PROOF" = 0 ]; then
    step "proof — skipped (--skip-proof)"
elif [ "$DRY_RUN" = 1 ]; then
    step "proof"
    say "  would run: sh $PROVE_SCRIPT --name $TOOLCHAIN_NAME"
else
    step "prove a gate that needs the Trust frontend"
    sh "$PROVE_SCRIPT" --name "$TOOLCHAIN_NAME"
fi

cat <<SUMMARY

=== done
toolchain '$TOOLCHAIN_NAME' -> $SYSROOT

DO NOT DELETE OR MOVE THAT DIRECTORY. The rustup toolchain is a SYMLINK into the
build tree, not a copy. Deleting the tree (or running \`git worktree remove\` on
it) breaks every repository that pins channel = "$TOOLCHAIN_NAME" — clean,
trust-vc, aterm — with a rustup lookup failure that names none of this.

Make sure the rustup shim stays first on PATH, or the pin resolves to whatever
rustc happens to be ahead of it:

    export PATH="\$HOME/.cargo/bin:\$PATH"

Re-running this script is safe and cheap: it re-verifies, re-links and re-proves,
and rebuilds nothing that is already built.
SUMMARY

if [ "$STAGE" = 1 ]; then
    cat <<'STAGE1'

stage1 is a DEVELOPER artifact. It carries the whole tool surface the pinned
repositories need — that is why it is linked here — but it is not release
evidence, and `rustup default` should not point at it
(docs/rustup-toolchain-link.md).
STAGE1
fi

# The honest half of a green run on a machine like this one. Preflight puts the
# rustup shim on PATH when it is missing so that the link and the proof can
# happen at all — but that repair lives and dies with this process, and
# scripts/prove-trust-frontend-gate.sh refuses to repair its own PATH precisely
# because a proof that fixes its premise proves nothing. So say plainly which
# half is done: the toolchain is built, linked and proved; the ENVIRONMENT is
# not, and until the shell rc carries the line below every new shell resolves
# `channel = "$TOOLCHAIN_NAME"` through whatever rustc is ahead of the shim.
if [ "$PATH_REPAIRED" = 1 ] && [ "$DRY_RUN" = 0 ]; then
    cat >&2 <<PATHFIX

################################################################################
## ACTION REQUIRED — the toolchain is installed; this MACHINE is not yet fixed.
##
## $RUSTUP_BIN_DIR was not on the PATH this script
## inherited. It was added for this process only, which is how the steps above
## were able to run at all. That repair is gone the moment this script exits.
##
## Until this line is in your shell rc, every gate in clean, trust-vc and aterm
## still starts in the state this whole script exists to cure:
##
##     echo 'export PATH="\$HOME/.cargo/bin:\$PATH"' >> ~/.zshrc
##
## Then, in a NEW shell, confirm it with the proof on its own — it will refuse
## to repair PATH for you, so a pass there is a statement about your machine:
##
##     sh $SCRIPT_DIR/prove-trust-frontend-gate.sh --name $TOOLCHAIN_NAME
################################################################################
PATHFIX
fi
