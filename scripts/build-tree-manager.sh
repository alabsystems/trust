#!/usr/bin/env bash
# build-tree-manager.sh — give a tree with no Bootstrap yet its own native
# build-tree manager, so that x.py can take the build-tree lease.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# x.py takes the build-tree lease before it builds anything, and only the native
# manager (protocol trust-build-tree-manager-v2) may grant it: this tree's
# Bootstrap through `--trust-build-tree-lock`, or a current Targo through
# `targo trust repo lock`. A fresh checkout or worktree has no Bootstrap, and
# a published Targo older than that protocol has no `trust repo lock`, so x.py
# refuses before writing anything. It never builds a manager itself
# (docs/DECISION_QUEUE.md, 2026-11-09 "Retire the Python cold-manager
# constructor in favor of native Targo").
#
# This script is the explicit step for that tree: it builds THIS tree's
# Bootstrap, the same program and source bootstrap.py builds, with an installed
# Trust Targo, into build-tree-manager.noindex/ at the tree's root, which x.py's
# frontend list names after build/bootstrap. It adds no lock, ownership, waiting
# or recovery logic of its own; the binary's `--trust-build-tree-lock` entry is
# the native manager. It writes nothing under build/ and takes no lease: the
# first x.py run takes the lease through this binary and builds the normal
# Bootstrap under build/ with the Stage0 seed. FRESH-TREE-LOCK-FRONTEND-1.
#
# Two runs at once on one tree are serialized by Cargo's own exclusive lock on
# the build directory; the later run finds the binary fresh. While it runs, the
# native manager counts its Cargo and compiler processes as writers of this
# tree, so a concurrent x.py acquisition is refused or waits.
#
# Usage: scripts/build-tree-manager.sh [--targo PATH] [--seed-dylib-path DIR]...
#   --targo PATH           the Targo to build with (default: $TARGO, else `targo` on PATH);
#                          it compiles with the trustc beside it
#   --seed-dylib-path DIR  a directory first on DYLD_LIBRARY_PATH for that Targo and its
#                          compiler, as the mint's option of this name is for a seed whose
#                          binaries load a library the system does not provide (repeatable)
# On a shared machine run it under admission: scripts/build-slot -- scripts/build-tree-manager.sh
#
# The build is --frozen, like bootstrap.py's: it neither updates the lock file
# nor fetches, so its Cargo home must hold the registry index entry and the
# archive of every crate src/bootstrap/Cargo.lock names, optional ones included.
# Cargo names the first one it lacks ("no matching package named ..."); fetch
# Bootstrap's locked sources first:
#   targo fetch --locked --manifest-path src/bootstrap/Cargo.toml
# The daily runner gives this step the Cargo home and the seed Targo its dependency
# preparation proved offline (scripts/daily_toolchain_stage.py, build_tree_manager).
set -euo pipefail

PROTOCOL="trust-build-tree-manager-v2"
targo="${TARGO:-targo}"
dylibs=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --targo)
      [ "$#" -ge 2 ] || { echo "build-tree-manager: --targo needs a path" >&2; exit 2; }
      targo="$2"; shift 2 ;;
    --seed-dylib-path)
      [ "$#" -ge 2 ] || { echo "build-tree-manager: --seed-dylib-path needs a directory" >&2; exit 2; }
      case "$2" in
        /*) [ -d "$2" ] || { echo "build-tree-manager: --seed-dylib-path is not a directory: $2" >&2; exit 2; } ;;
        *) echo "build-tree-manager: --seed-dylib-path takes an absolute directory: $2" >&2; exit 2 ;;
      esac
      case "$2" in
        *:*) echo "build-tree-manager: --seed-dylib-path cannot hold a colon: $2" >&2; exit 2 ;;
      esac
      dylibs="${dylibs:+$dylibs:}$2"; shift 2 ;;
    -h|--help)
      sed -n '2,/^set -euo/p' "${BASH_SOURCE[0]}" | sed '$d; s/^# \{0,1\}//'
      exit 0 ;;
    *)
      echo "build-tree-manager: unknown argument: $1" >&2; exit 2 ;;
  esac
done

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
manifest="$root/src/bootstrap/Cargo.toml"
target="$root/build-tree-manager.noindex"
binary="$target/debug/bootstrap"
if [ ! -f "$manifest" ] || [ ! -f "$root/x.py" ]; then
  echo "build-tree-manager: $root is not a Trust source tree (no x.py or src/bootstrap/Cargo.toml)" >&2
  exit 2
fi

# The one discriminator that has held: a real Targo accepts --unverified, and a
# stock Cargo under that name rejects it (CLAUDE.md "Before you debug anything").
if ! version="$("$targo" --unverified --version 2>/dev/null)" || [ "${version#targo }" = "$version" ]; then
  echo "build-tree-manager: $targo is not a Trust Targo (\`$targo --unverified --version\` did not answer \`targo ...\`); name one with --targo" >&2
  exit 2
fi
echo "build-tree-manager: building this tree's Bootstrap with $version into $target" >&2

# Only Cargo's own target is chosen here. Inherited compiler and target
# selection would build something else: RUSTC inside a Bootstrap shell is
# Bootstrap's shim, and a CARGO_BUILD_TARGET puts the binary under a triple.
# RUSTC_BOOTSTRAP=1 is what bootstrap.py also sets for this build: Bootstrap's
# dependency graph enables a Trust std feature on a Trust compiler.
# dyld searches DYLD_LIBRARY_PATH by leaf name before a load command's own path, and
# a system shell drops the variable, so it is set here, on the Targo's own launch.
cd "$root"
env -u RUSTC -u RUSTC_WRAPPER -u RUSTC_WORKSPACE_WRAPPER -u RUSTFLAGS \
    -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS -u CARGO_BUILD_TARGET \
    -u CARGO_BUILD_TARGET_DIR -u CARGO_BUILD_BUILD_DIR \
    ${dylibs:+DYLD_LIBRARY_PATH="$dylibs"} \
    CARGO_TARGET_DIR="$target" CARGO_INCREMENTAL=0 RUSTC_BOOTSTRAP=1 \
    "$targo" --unverified build --frozen --manifest-path "$manifest" --bin bootstrap

# The binary is accepted only as x.py would accept it.
if ! answer="$("$binary" --trust-build-tree-lock --protocol)" || [ "$answer" != "$PROTOCOL" ]; then
  echo "build-tree-manager: $binary does not answer $PROTOCOL" >&2
  exit 1
fi
echo "$binary"
