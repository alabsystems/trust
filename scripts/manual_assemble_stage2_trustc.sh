#!/bin/sh
# Manually assemble a standalone stage2 Trust sysroot when bootstrap's own
# materialize_local_compiler_aliases step is skipped (uplift path) and leaves
# build/host/stage2/{bin,lib} empty. Replicates that step + the sysroot std/lib
# population using the stage2-rustc .librustc-stamp + the uplifted stage1 std.
#
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
HOST=aarch64-apple-darwin
RUSTC_REL="$ROOT/build/$HOST/stage2-rustc/$HOST/release"
STD_DIST="$ROOT/build/$HOST/stage1-std/$HOST/dist"
SYS="$ROOT/build/host/stage2"
BIN="$SYS/bin"
LIB="$SYS/lib"
RUSTLIB="$LIB/rustlib/$HOST/lib"

[ -f "$RUSTC_REL/rustc-main" ] || { echo "no rustc-main at $RUSTC_REL" >&2; exit 1; }
mkdir -p "$BIN" "$LIB" "$RUSTLIB"

echo "== 1. compiler binary -> bin/{trustc,rustc}"
cp -f "$RUSTC_REL/rustc-main" "$BIN/trustc"
cp -f "$RUSTC_REL/rustc-main" "$BIN/rustc"

echo "== 2. rustc dylibs from .librustc-stamp -> lib/ (rpath @loader_path/../lib) and rustlib"
python3 - "$RUSTC_REL/.librustc-stamp" "$LIB" "$RUSTLIB" <<'PY'
import os, sys, shutil
stamp, libdir, rustlib = sys.argv[1], sys.argv[2], sys.argv[3]
data = open(stamp, 'rb').read()
n = 0
for rec in data.split(b'\0'):
    if not rec: continue
    # records are <type-char><path>
    path = rec[1:].decode('utf-8', 'replace')
    if not os.path.isfile(path): continue
    base = os.path.basename(path)
    if base.endswith('.dylib'):
        shutil.copy2(path, os.path.join(libdir, base))     # for the rustc-main rpath loader
        shutil.copy2(path, os.path.join(rustlib, base))    # for the sysroot
        n += 1
    elif base.endswith(('.rlib', '.rmeta', '.so')):
        shutil.copy2(path, os.path.join(rustlib, base)); n += 1
print(f"  copied {n} rustc artifacts")
PY

echo "== 3. also copy the release/ top-level rustc dylib aliases -> lib/"
# Do not sweep release/deps here. That directory is shared across incremental
# compiler builds and can contain stale, mutually incompatible driver hashes.
# Step 2 already copied the exact hashed driver selected by .librustc-stamp;
# only the current top-level aliases belong beside it in the assembled sysroot.
for d in "$RUSTC_REL"/*.dylib; do
  [ -f "$d" ] && cp -f "$d" "$LIB/$(basename "$d")" 2>/dev/null || true
done

set -- "$LIB"/librustc_driver-*.dylib
[ "$#" -eq 1 ] && [ -f "$1" ] || {
  echo "expected exactly one stamped librustc_driver under $LIB" >&2
  exit 1
}

echo "== 4. std (uplifted) -> rustlib/<host>/lib"
if [ -f "$STD_DIST/.libstd-stamp" ]; then
  python3 - "$STD_DIST/.libstd-stamp" "$LIB" "$RUSTLIB" <<'PY'
import os, sys, shutil
stamp, libdir, rustlib = sys.argv[1], sys.argv[2], sys.argv[3]
n = 0
for rec in open(stamp, 'rb').read().split(b'\0'):
    if not rec:
        continue
    path = rec[1:].decode('utf-8', 'replace')
    if not os.path.isfile(path):
        continue
    base = os.path.basename(path)
    if base.endswith(('.rlib', '.rmeta', '.dylib', '.so')):
        shutil.copy2(path, os.path.join(rustlib, base))
        if base.startswith('libstd-') and base.endswith(('.dylib', '.so')):
            shutil.copy2(path, os.path.join(libdir, base))
        n += 1
print(f"  copied {n} stamped std artifacts")
PY
fi
# also try the standard std libdir locations
for cand in "$ROOT/build/$HOST/stage2-std/$HOST/release/deps" "$ROOT/build/$HOST/stage1/lib/rustlib/$HOST/lib"; do
  [ -d "$cand" ] && { cp -f "$cand"/*.rlib "$RUSTLIB/" 2>/dev/null || true; cp -f "$cand"/*.dylib "$RUSTLIB/" 2>/dev/null || true; cp -f "$cand"/*.rmeta "$RUSTLIB/" 2>/dev/null || true; }
done
set -- "$RUSTLIB"/libstd-*.rlib
[ "$#" -eq 1 ] && [ -f "$1" ] || {
  echo "expected exactly one stamped libstd under $RUSTLIB" >&2
  exit 1
}

echo "== 5. preserve valid signatures; ad-hoc sign only unsigned Mach-O files"
# `cp` preserves an embedded signature. Re-signing an already linker-signed
# compiler dylib changes its bytes and breaks the exact driver identity shared
# with the prepared rustc-private sysroot. Only repair files whose copied
# signature does not verify.
for f in "$BIN/trustc" "$BIN/rustc" "$LIB"/*.dylib "$RUSTLIB"/*.dylib; do
  [ -f "$f" ] || continue
  codesign --verify --strict "$f" 2>/dev/null \
    || codesign --force --sign - "$f" 2>/dev/null \
    || true
done

echo "== 6. rustc-dev (rustc_private) rlibs/rmetas from .librustc-stamp -> rustlib"
# Inlined (formerly scripts/restore-rustc-dev.sh, retired). For a normal
# `x.py build`, the Assemble step now folds rustc-dev into the sysroot natively;
# this manual/uplift path bypasses Assemble, so copy every stamp-recorded lib
# into the sysroot target libdir here.
python3 - "$RUSTC_REL/.librustc-stamp" "$RUSTLIB" <<'PY'
import os, sys, shutil
stamp, rustlib = sys.argv[1], sys.argv[2]
n = 0
for rec in open(stamp, 'rb').read().split(b'\0'):
    if not rec:
        continue
    path = rec[1:].decode('utf-8', 'replace')   # drop 1-char dependency-type prefix
    if not os.path.isfile(path):
        continue
    dst = os.path.join(rustlib, os.path.basename(path))
    if os.path.abspath(path) != os.path.abspath(dst):
        shutil.copy2(path, dst)
        n += 1
print(f"  restored {n} rustc-dev libs into {rustlib}")
PY

echo "== done. bin: $(ls "$BIN")"
