#!/bin/sh
# Register a Trust stage toolchain with rustup for local compatibility
# rehearsals.
#
# Usage:
#   scripts/rustup-link-trust.sh [--repair-aliases] [--name NAME] [stage]
#   scripts/rustup-link-trust.sh [--name NAME] --sysroot PATH
#
# Stage defaults to `stage2` (the fully self-hosted toolchain with linked
# targo, trustdoc, trust-analyzer, etc.). Pass `stage1` for a faster
# rebuild path when you only need trustc. Stage1 links as `trust-stage1` by
# default; use `--name trust` only when you explicitly want plain `trust`.
#
# After linking:
#   rustup run trust targo --unverified build # explicit native smoke
#   rustup run trust targo --unverified check
#   rustup default trust         # daily-driver only after a complete stage2 link
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0

set -eu

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRUST_TOOLCHAIN_PYTHON3="${PYTHON3:-python3}"
. "$SCRIPT_DIR/lib/trust_toolchain_surface.sh"

usage() {
    cat <<EOF
Usage: scripts/rustup-link-trust.sh [--repair-aliases] [--name NAME] [stage1|stage2]
       scripts/rustup-link-trust.sh [--name NAME] --sysroot PATH

Registers a local Trust stage toolchain with rustup for compatibility
rehearsals. Stage defaults to stage2 and toolchain name defaults to:

    stage2 -> trust
    stage1 -> trust-stage1

Alias repair is disabled by default. Pass --repair-aliases or set
TRUST_RUSTUP_LINK_REPAIR_ALIASES=1 to create only the admitted missing
same-sysroot compatibility entrypoints: rustc -> trustc, plus cargo -> targo
for stage2. Canonical Trust tools and secondary Rust spellings are never
created by repair.

--sysroot links an already assembled, external stage2 sysroot. It is mutually
exclusive with stage1/stage2 and never permits alias repair: an installed or
read-only toolchain must be complete before this script is allowed to link it.

Environment:
    TRUST_RUSTUP_LINK_NAME=NAME
    TRUST_RUSTUP_LINK_REPAIR_ALIASES=1
EOF
}

REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
STAGE=""
EXTERNAL_SYSROOT=""
TOOLCHAIN_NAME="${TRUST_RUSTUP_LINK_NAME:-}"
REPAIR_ALIASES="${TRUST_RUSTUP_LINK_REPAIR_ALIASES:-0}"

while [ "$#" -gt 0 ]; do
    case "$1" in
        stage1|stage2)
            if [ -n "$STAGE" ]; then
                echo "error: stage specified more than once" >&2
                exit 2
            fi
            STAGE="$1"
            ;;
        --repair-aliases)
            REPAIR_ALIASES=1
            ;;
        --no-repair-aliases)
            REPAIR_ALIASES=0
            ;;
        --sysroot)
            shift
            if [ "$#" -eq 0 ] || [ -z "$1" ]; then
                echo "error: --sysroot requires a non-empty path" >&2
                exit 2
            fi
            if [ -n "$EXTERNAL_SYSROOT" ]; then
                echo "error: --sysroot specified more than once" >&2
                exit 2
            fi
            EXTERNAL_SYSROOT="$1"
            ;;
        --sysroot=*)
            if [ -n "$EXTERNAL_SYSROOT" ]; then
                echo "error: --sysroot specified more than once" >&2
                exit 2
            fi
            EXTERNAL_SYSROOT="${1#*=}"
            if [ -z "$EXTERNAL_SYSROOT" ]; then
                echo "error: --sysroot requires a non-empty path" >&2
                exit 2
            fi
            ;;
        --name|--toolchain-name)
            shift
            if [ "$#" -eq 0 ] || [ -z "$1" ]; then
                echo "error: --name requires a non-empty toolchain name" >&2
                exit 2
            fi
            TOOLCHAIN_NAME="$1"
            ;;
        --name=*|--toolchain-name=*)
            TOOLCHAIN_NAME="${1#*=}"
            if [ -z "$TOOLCHAIN_NAME" ]; then
                echo "error: --name requires a non-empty toolchain name" >&2
                exit 2
            fi
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            echo "error: unrecognized argument: $1" >&2
            usage >&2
            exit 2
            ;;
    esac
    shift
done

if [ -n "$EXTERNAL_SYSROOT" ] && [ -n "$STAGE" ]; then
    echo "error: --sysroot is mutually exclusive with stage1/stage2" >&2
    exit 2
fi

if [ -n "$EXTERNAL_SYSROOT" ]; then
    STAGE="stage2"
else
    STAGE="${STAGE:-stage2}"
fi
case "$REPAIR_ALIASES" in
    1|true|TRUE|yes|YES|on|ON)
        REPAIR_ALIASES=1
        ;;
    0|false|FALSE|no|NO|off|OFF|"")
        REPAIR_ALIASES=0
        ;;
    *)
        echo "error: TRUST_RUSTUP_LINK_REPAIR_ALIASES must be 0/1 or true/false" >&2
        exit 2
        ;;
esac

if [ -n "$EXTERNAL_SYSROOT" ] && [ "$REPAIR_ALIASES" = "1" ]; then
    echo "error: alias repair is forbidden with --sysroot; external sysroots must already be complete and immutable" >&2
    exit 2
fi

if [ -z "$TOOLCHAIN_NAME" ]; then
    case "$STAGE" in
        stage1)
            TOOLCHAIN_NAME="trust-stage1"
            ;;
        stage2)
            TOOLCHAIN_NAME="trust"
            ;;
    esac
fi

if [ -n "$EXTERNAL_SYSROOT" ]; then
    if [ ! -d "$EXTERNAL_SYSROOT" ]; then
        echo "error: external sysroot does not exist: $EXTERNAL_SYSROOT" >&2
        exit 1
    fi
    TOOLCHAIN_DIR="$(cd "$EXTERNAL_SYSROOT" && pwd -P)"
else
    case "$STAGE" in
        stage1)
            TOOLCHAIN_DIR="$REPO_ROOT/build/host/stage1"
            ;;
        stage2)
            TOOLCHAIN_DIR="$REPO_ROOT/build/host/stage2"
            ;;
        *)
            echo "error: stage must be stage1 or stage2 (got $STAGE)" >&2
            exit 2
            ;;
    esac
fi

if [ ! -d "$TOOLCHAIN_DIR/bin" ]; then
    cat >&2 <<EOF
error: $TOOLCHAIN_DIR/bin does not exist.

The Trust $STAGE toolchain has not been built yet. Run one of:

    ./x.py build --stage 2          # full self-hosted toolchain (recommended)
    ./x.py build --stage 1          # trustc only (faster, no linked targo)

then rerun this script.
EOF
    exit 1
fi

if [ ! -x "$TOOLCHAIN_DIR/bin/rustc" ] && [ ! -x "$TOOLCHAIN_DIR/bin/trustc" ]; then
    echo "error: neither $TOOLCHAIN_DIR/bin/rustc nor bin/trustc is executable" >&2
    exit 1
fi

require_tool() {
    tool="$1"
    if [ ! -x "$TOOLCHAIN_DIR/bin/$tool" ]; then
        echo "error: missing required $STAGE tool: $TOOLCHAIN_DIR/bin/$tool" >&2
        if [ -n "$EXTERNAL_SYSROOT" ]; then
            echo "hint: rebuild or reinstall a complete external sysroot; --sysroot validation never repairs it" >&2
        else
            echo "hint: alias repair is opt-in; rerun with --repair-aliases only if the sibling Trust/Rust name is intentionally the same artifact" >&2
        fi
        exit 1
    fi
}

require_dir() {
    dir="$1"
    if [ ! -d "$dir" ]; then
        echo "error: missing required $STAGE directory: $dir" >&2
        exit 1
    fi
}

canonical_dir() {
    (
        cd "$1"
        pwd -P
    )
}

require_version_prefix() {
    tool="$1"
    prefix="$2"
    version="$("$TOOLCHAIN_DIR/bin/$tool" --version 2>&1 || true)"
    case "$version" in
        "$prefix"*) ;;
        *)
            echo "error: $tool --version must start with '$prefix' for a Trust link, got: $version" >&2
            exit 1
            ;;
    esac
}

# The rustc-derived binaries keep the upstream version banner — the leading
# `rustc` token is untouchable, because the ecosystem's version-sniffing build
# scripts assert it — and carry their Trust identity in a trailing parenthetical
# instead. So match the parenthetical rather than a leading token.
#
# THE PARENTHETICAL HAS TWO LEGITIMATE SHAPES, and this check used to accept
# only one. rustc_driver_impl builds it as
#
#     format!(" ({display_binary} {trust_version})")   // CFG_TRUST_VERSION set
#     format!(" ({display_binary})")                   // otherwise
#
# (compiler/rustc_driver_impl/src/lib.rs:2382-2389), so an ordinary build says
# `(trustc 0.1.0)` and only a build without CFG_TRUST_VERSION says `(trustc)`.
# Matching the literal string "(trustc)" therefore REJECTED every real toolchain
# built since the version was threaded through: measured 2026-08-22 against
# build/aarch64-apple-darwin/stage1 of a tree that passes
# tools/verify-toolchain.sh in full —
#
#   error: trustc --version must contain '(trustc)' for a Trust link,
#   got: rustc 1.99.0-dev (52e0a7031 2026-08-22) (trustc 0.1.0)
#
# — while the bare form is not a relic of one artifact. Re-derived 2026-08-23:
#
#   git grep -lF '(trustc)' | wc -l              -> 353 tracked files
#   git grep -lE 'rustc [0-9][^ ]* \([0-9a-f]{7,} [0-9-]{10}\) \(trustc\)' | wc -l
#                                                -> 303 of them are a RECORDED
#                                                   version banner in the bare
#                                                   shape, dated 2026-06-22
#                                                   through 2026-07-28
#
# i.e. essentially every banner captured before `CFG_TRUST_VERSION` was threaded
# through bootstrap (a81c07e1d6, 2026-07-24); the versioned banner appears in 5
# files, dated 2026-07-30 onward. Both shapes are real history, a toolchain built
# without CFG_TRUST_VERSION still emits the bare one today, and this check must
# link either. So accept exactly the two shapes the emitter can produce and
# nothing looser: `(name)` or `(name <version>)`. A stock rustc, which prints no
# parenthetical at all, still fails, which is the property this check exists for.
require_trust_brand() {
    tool="$1"
    brand="$2"
    version="$("$TOOLCHAIN_DIR/bin/$tool" --version 2>&1 || true)"
    case "$version" in
        *"($brand)"*|*"($brand "*) ;;
        *)
            echo "error: $tool --version must carry the Trust brand '($brand)' or '($brand <version>)' for a Trust link, got: $version" >&2
            exit 1
            ;;
    esac
}

require_same_artifact() {
    left="$1"
    right="$2"
    require_tool "$left"
    require_tool "$right"
    if alias_error="$(
        trust_toolchain_alias_pair_error "$TOOLCHAIN_DIR/bin" "$left" "$right"
    )"; then
        echo "error: invalid same-sysroot alias pair $left:$right: $alias_error" >&2
        exit 1
    fi
}

link_missing_alias() {
    target="$1"
    source="$2"
    if [ ! -e "$TOOLCHAIN_DIR/bin/$target" ] \
        && [ ! -L "$TOOLCHAIN_DIR/bin/$target" ] \
        && [ -x "$TOOLCHAIN_DIR/bin/$source" ]; then
        ln -s "$source" "$TOOLCHAIN_DIR/bin/$target"
        echo "linked $TOOLCHAIN_DIR/bin/$target -> $source"
    fi
}

if forbidden_error="$(trust_toolchain_forbidden_entry_error "$TOOLCHAIN_DIR/bin")"; then
    echo "error: $forbidden_error" >&2
    exit 1
fi

if [ "$STAGE" = "stage2" ]; then
    for tool in \
        trustc \
        targo \
        targo-trust \
        trustd \
        trustdoc \
        trustfmt \
        targo-fmt \
        tippy \
        targo-tippy \
        tippy-driver \
        trust-analyzer
    do
        require_tool "$tool"
    done
    if [ -e "$TOOLCHAIN_DIR/bin/trust-miri" ] \
        || [ -e "$TOOLCHAIN_DIR/bin/targo-miri" ]; then
        for tool in trust-miri targo-miri; do
            require_tool "$tool"
        done
    fi
else
    require_tool trustc
fi

# Refuse mismatched or dangling existing aliases before making any repair, so a
# failed preflight does not leave a partly mutated toolchain behind.
if [ -e "$TOOLCHAIN_DIR/bin/rustc" ] || [ -L "$TOOLCHAIN_DIR/bin/rustc" ]; then
    require_same_artifact trustc rustc
fi
if [ "$STAGE" = "stage2" ] \
    && { [ -e "$TOOLCHAIN_DIR/bin/cargo" ] || [ -L "$TOOLCHAIN_DIR/bin/cargo" ]; }; then
    require_same_artifact targo cargo
fi
# `rustdoc` joined the admitted names in 76d408e1cd: cargo spawns a binary of
# that name for its doctest phase, so bootstrap emits it into every stage >= 1
# sysroot. Hold it to the same binding rule as the other two when it is there.
if [ -e "$TOOLCHAIN_DIR/bin/rustdoc" ] || [ -L "$TOOLCHAIN_DIR/bin/rustdoc" ]; then
    require_same_artifact trustdoc rustdoc
fi

# Rust tooling needs exactly the three admitted compatibility names. Repair those
# names only when the caller explicitly requests it, and leave every secondary
# tool Trust-only.
if [ "$REPAIR_ALIASES" = "1" ]; then
    link_missing_alias rustc trustc
    if [ "$STAGE" = "stage2" ]; then
        link_missing_alias cargo targo
        link_missing_alias rustdoc trustdoc
    fi
elif [ -n "$EXTERNAL_SYSROOT" ]; then
    echo "alias repair: forbidden for external --sysroot (validation only)" >&2
else
    echo "alias repair: disabled (pass --repair-aliases or set TRUST_RUSTUP_LINK_REPAIR_ALIASES=1 to repair missing aliases)" >&2
fi

require_same_artifact trustc rustc
if [ "$STAGE" = "stage2" ]; then
    require_same_artifact targo cargo
fi

# Verify trustc actually runs. If it points at the genesis-stage0 shim that
# calls back through rustup, we get an infinite-recursion error here —
# refuse to link in that case so we do not poison the user's rustup config.
if "$TOOLCHAIN_DIR/bin/trustc" --version 2>&1 | grep -q "infinite recursion"; then
    cat >&2 <<EOF
error: $TOOLCHAIN_DIR/bin/trustc is the genesis-stage0 shim that calls back
through rustup. This is not a real Trust compiler — it is only used to
bootstrap the first real stage. Build a real stage1 first:

    ./x.py build --stage 1

Refusing to link the genesis shim.
EOF
    exit 1
fi

if [ "$STAGE" = "stage2" ]; then
    selected_sysroot="$("$TOOLCHAIN_DIR/bin/trustc" --print sysroot 2>/dev/null || true)"
    if [ -z "$selected_sysroot" ]; then
        echo "error: trustc --print sysroot failed for $TOOLCHAIN_DIR" >&2
        exit 1
    fi
    if [ "$(canonical_dir "$selected_sysroot")" != "$(canonical_dir "$TOOLCHAIN_DIR")" ]; then
        echo "error: trustc --print sysroot does not match selected toolchain dir" >&2
        echo "  selected: $(canonical_dir "$TOOLCHAIN_DIR")" >&2
        echo "  reported: $(canonical_dir "$selected_sysroot")" >&2
        exit 1
    fi

    target_libdir="$("$TOOLCHAIN_DIR/bin/trustc" --print target-libdir 2>/dev/null || true)"
    if [ -z "$target_libdir" ] || [ ! -d "$target_libdir" ]; then
        echo "error: trustc --print target-libdir did not return an existing directory" >&2
        exit 1
    fi
    set -- "$target_libdir"/libstd-*.rlib
    if [ ! -e "$1" ]; then
        echo "error: target std library not found in $target_libdir" >&2
        exit 1
    fi

    require_dir "$TOOLCHAIN_DIR/lib/rustlib/src/rust/library"
    require_trust_brand trustc trustc
    require_version_prefix targo "targo "
    require_version_prefix trustd "trustd "
    require_trust_brand trustdoc trustdoc
fi

rustup toolchain link "$TOOLCHAIN_NAME" "$TOOLCHAIN_DIR"
echo
echo "linked: rustup toolchain '$TOOLCHAIN_NAME' -> $TOOLCHAIN_DIR"
echo
echo "verify with:"
echo "    rustup run $TOOLCHAIN_NAME trustc --version"
if [ "$STAGE" = "stage2" ]; then
    echo "    rustup run $TOOLCHAIN_NAME targo --version"
fi
echo
echo "local compatibility smoke commands:"
if [ "$STAGE" = "stage2" ]; then
    echo "    rustup run $TOOLCHAIN_NAME targo --unverified build"
    echo "    rustup run $TOOLCHAIN_NAME targo --unverified check"
else
    echo "    rustup run $TOOLCHAIN_NAME trustc --version"
fi
echo
# Closing guidance follows the sysroot, not $STAGE. With --sysroot, STAGE is
# forced to "stage2" above as a VALIDATION LEVEL — the full same-surface contract
# an external root must already satisfy — and that is not a claim about how the
# root was produced. Reading it as one printed daily-driver advice for a stage1
# tree: `install-trust-toolchain.sh --stage 1` links
# build/<triple>/stage1 through --sysroot, so a single run said "make default in
# this shell: rustup default trust" here and "stage1 is a DEVELOPER artifact and
# `rustup default` should not point at it" in the installer's own summary. When
# the sysroot names its stage, believe the name; when it does not, say what is
# unknown rather than recommending a default (docs/rustup-toolchain-link.md).
GUIDANCE_STAGE="$STAGE"
if [ -n "$EXTERNAL_SYSROOT" ]; then
    case "${TOOLCHAIN_DIR##*/}" in
        stage1) GUIDANCE_STAGE="stage1" ;;
        stage2) GUIDANCE_STAGE="stage2" ;;
        *)      GUIDANCE_STAGE="unknown" ;;
    esac
fi
case "$GUIDANCE_STAGE" in
    stage1)
        echo "stage1 is developer-only; do not make it the daily-driver/default toolchain"
        echo "or use it as release evidence."
        ;;
    stage2)
        echo "make default in this shell:"
        echo "    rustup default $TOOLCHAIN_NAME"
        ;;
    *)
        echo "this sysroot was supplied with --sysroot and its path does not name a stage,"
        echo "so this script validated its SURFACE but cannot tell a complete stage2 from a"
        echo "stage1 developer tree. Do not make it the default, and do not cite it as"
        echo "release evidence, until you know which it is (docs/rustup-toolchain-link.md)."
        ;;
esac
