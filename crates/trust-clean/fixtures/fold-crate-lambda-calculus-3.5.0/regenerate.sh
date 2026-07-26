#!/usr/bin/env bash
# Generate fresh Trust MIR dumps for the checksum-pinned lambda_calculus 3.5.0
# source intake.  Scratch output is the default evidence path; replacing the
# checked-in core dumps requires an explicit --replace-committed opt-in.
# Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0 OR MIT
set -euo pipefail

PATH=/usr/bin:/bin:/usr/sbin:/sbin
export PATH
GIT_CONFIG_GLOBAL=/dev/null
GIT_CONFIG_SYSTEM=/dev/null
export GIT_CONFIG_GLOBAL GIT_CONFIG_SYSTEM
unset CDPATH ENV BASH_ENV

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO="$(/usr/bin/git -C "$HERE" rev-parse --show-toplevel)"
CRATE=lambda_calculus
VERS=3.5.0
SHA256_PIN=168030aef659e9a35ba517952982bb0212fda53d531837e3f18c399f9d28dba8
OUTPUT_ROOT=
TRUSTC_ARG=
VERIFY_SOURCE=0
REPLACE_COMMITTED=0

usage() {
  cat <<'EOF'
usage: regenerate.sh [--verify-source] [--trustc PATH]
                     (--output-root PATH | --replace-committed)

  --output-root PATH     create PATH/{full,core} plus compiler transcripts
  --replace-committed    explicitly replace the fixture's tracked core *.json
  --trustc PATH          exact repository-local build/*/stage2/bin/trustc
  --verify-source        download, checksum, and byte-compare the .crate source
  --verify               compatibility alias for --verify-source

Ambient TRUSTC is rejected.  With no --trustc, exactly one repository-local
Stage2 trustc must exist.  --output-root never edits the fixture directory.
EOF
}

while (( $# )); do
  case "$1" in
    --output-root)
      [[ $# -ge 2 && -n "$2" ]] || { echo "regenerate.sh: --output-root requires a path" >&2; exit 2; }
      [[ -z "$OUTPUT_ROOT" ]] || { echo "regenerate.sh: --output-root may appear only once" >&2; exit 2; }
      OUTPUT_ROOT=$2
      shift 2
      ;;
    --trustc)
      [[ $# -ge 2 && -n "$2" ]] || { echo "regenerate.sh: --trustc requires a path" >&2; exit 2; }
      [[ -z "$TRUSTC_ARG" ]] || { echo "regenerate.sh: --trustc may appear only once" >&2; exit 2; }
      TRUSTC_ARG=$2
      shift 2
      ;;
    --verify|--verify-source)
      VERIFY_SOURCE=1
      shift
      ;;
    --replace-committed)
      REPLACE_COMMITTED=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "regenerate.sh: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

if [[ $REPLACE_COMMITTED -eq 1 && -n "$OUTPUT_ROOT" ]]; then
  echo "regenerate.sh: choose either --output-root or --replace-committed" >&2
  exit 2
fi
if [[ $REPLACE_COMMITTED -eq 0 && -z "$OUTPUT_ROOT" ]]; then
  echo "regenerate.sh: pass --output-root for non-destructive output or --replace-committed" >&2
  exit 2
fi

select_trustc() {
  local candidate
  local -a candidates=()
  if [[ -n "$TRUSTC_ARG" ]]; then
    candidate=$TRUSTC_ARG
  else
    if [[ -n "${TRUSTC:-}" ]]; then
      echo "regenerate.sh: ambient TRUSTC is not an authority; pass --trustc explicitly" >&2
      return 2
    fi
    for candidate in "$REPO"/build/*/stage2/bin/trustc; do
      [[ -f "$candidate" && -x "$candidate" && ! -L "$candidate" ]] && candidates+=("$candidate")
    done
    if [[ ${#candidates[@]} -ne 1 ]]; then
      echo "regenerate.sh: expected exactly one repository-local Stage2 trustc; found ${#candidates[@]} (pass --trustc)" >&2
      return 2
    fi
    candidate=${candidates[0]}
  fi

  [[ ! -L "$candidate" && -f "$candidate" && -x "$candidate" ]] || {
    echo "regenerate.sh: trustc must be an executable regular non-symlink file: $candidate" >&2
    return 2
  }
  local directory canonical
  directory="$(cd "$(dirname "$candidate")" && pwd -P)"
  canonical="$directory/$(basename "$candidate")"
  case "$canonical" in
    "$REPO"/build/*/stage2/bin/trustc) ;;
    *)
      echo "regenerate.sh: trustc is not repository-local build/*/stage2/bin/trustc: $canonical" >&2
      return 2
      ;;
  esac
  printf '%s\n' "$canonical"
}

TRUSTC_PATH="$(select_trustc)"

VERIFY_SCRATCH=
OUTPUT_SCRATCH=
cleanup() {
  if [[ -n "$VERIFY_SCRATCH" && -d "$VERIFY_SCRATCH" ]]; then
    rm -rf -- "$VERIFY_SCRATCH"
  fi
  if [[ -n "$OUTPUT_SCRATCH" && -d "$OUTPUT_SCRATCH" ]]; then
    rm -rf -- "$OUTPUT_SCRATCH"
  fi
}
trap cleanup EXIT

if [[ $VERIFY_SOURCE -eq 1 ]]; then
  VERIFY_SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/trust-lambda-source.XXXXXX")"
  /usr/bin/curl -sSf -A 'trust-verifier-research' \
    -o "$VERIFY_SCRATCH/$CRATE-$VERS.crate" \
    "https://static.crates.io/crates/$CRATE/$CRATE-$VERS.crate"
  echo "$SHA256_PIN  $VERIFY_SCRATCH/$CRATE-$VERS.crate" | /usr/bin/shasum -a 256 -c -
  /usr/bin/tar xzf "$VERIFY_SCRATCH/$CRATE-$VERS.crate" -C "$VERIFY_SCRATCH"
  /usr/bin/diff -r "$VERIFY_SCRATCH/$CRATE-$VERS" "$HERE/SOURCE"
  echo "provenance verified: vendored SOURCE is byte-identical to the published tarball ($SHA256_PIN)"
fi

if [[ $REPLACE_COMMITTED -eq 1 ]]; then
  OUTPUT_SCRATCH="$(mktemp -d "${TMPDIR:-/tmp}/trust-lambda-dumps.XXXXXX")"
  GENERATED=$OUTPUT_SCRATCH/generated
else
  OUTPUT_PARENT=$(dirname "$OUTPUT_ROOT")
  OUTPUT_NAME=$(basename "$OUTPUT_ROOT")
  [[ "$OUTPUT_NAME" != . && "$OUTPUT_NAME" != .. ]] || {
    echo "regenerate.sh: --output-root must name a new directory" >&2
    exit 2
  }
  [[ -d "$OUTPUT_PARENT" && ! -L "$OUTPUT_PARENT" ]] || {
    echo "regenerate.sh: --output-root parent must be an existing real directory: $OUTPUT_PARENT" >&2
    exit 2
  }
  OUTPUT_ROOT="$(cd "$OUTPUT_PARENT" && pwd -P)/$OUTPUT_NAME"
  case "$OUTPUT_ROOT" in
    "$HERE"|"$HERE"/*)
      echo "regenerate.sh: --output-root must be outside the fixture tree" >&2
      exit 2
      ;;
  esac
  [[ ! -e "$OUTPUT_ROOT" && ! -L "$OUTPUT_ROOT" ]] || {
    echo "regenerate.sh: --output-root must not already exist: $OUTPUT_ROOT" >&2
    exit 2
  }
  GENERATED=$OUTPUT_ROOT
fi

mkdir -m 700 "$GENERATED"
mkdir -m 700 "$GENERATED/full" "$GENERATED/core"

COMPILER_ARGS=(
  "$TRUSTC_PATH"
 
  "-Ztrust-dump=mir-only:$GENERATED/full"
  -Ztrust-policy=advisory
  --edition 2024
  --cfg 'feature="encoding"'
  --crate-type lib
  -o "$GENERATED/out.rlib"
  "$HERE/SOURCE/src/lib.rs"
)
printf '%s\n' "${COMPILER_ARGS[@]}" > "$GENERATED/compiler.argv"

STAGE_ROOT=$(cd "$(dirname "$TRUSTC_PATH")/.." && pwd -P)
COMPILER_HOME="$GENERATED/compiler-home"
COMPILER_TMP="$GENERATED/compiler-tmp"
mkdir -m 700 "$COMPILER_HOME" "$COMPILER_TMP"
COMPILER_ENV=(
  "PATH=$PATH"
  "HOME=$COMPILER_HOME"
  "TMPDIR=$COMPILER_TMP"
  "TMP=$COMPILER_TMP"
  "TEMP=$COMPILER_TMP"
  "LC_ALL=C"
  "LANG=C"
  "TZ=UTC"
  "CARGO_NET_OFFLINE=true"
)
RUNTIME_LIBS=
for library in "$STAGE_ROOT/lib" "$STAGE_ROOT"/lib/rustlib/*/lib; do
  if [[ -d "$library" ]]; then
    if [[ -n "$RUNTIME_LIBS" ]]; then
      RUNTIME_LIBS="$RUNTIME_LIBS:$library"
    else
      RUNTIME_LIBS=$library
    fi
  fi
done
if [[ -n "$RUNTIME_LIBS" ]]; then
  if [[ "$(/usr/bin/uname -s)" == Darwin ]]; then
    COMPILER_ENV+=("DYLD_LIBRARY_PATH=$RUNTIME_LIBS")
  else
    COMPILER_ENV+=("LD_LIBRARY_PATH=$RUNTIME_LIBS")
  fi
fi
printf '%s\n' "${COMPILER_ENV[@]}" > "$GENERATED/compiler.env"

set +e
/usr/bin/env -i "${COMPILER_ENV[@]}" "${COMPILER_ARGS[@]}" \
  > "$GENERATED/compiler.stdout" 2> "$GENERATED/compiler.stderr"
COMPILER_EXIT=$?
set -e
printf '%s\n' "$COMPILER_EXIT" > "$GENERATED/compiler.exit-code"
if [[ $COMPILER_EXIT -ne 0 ]]; then
  echo "regenerate.sh: trustc failed with exit $COMPILER_EXIT; transcripts remain in $GENERATED" >&2
  exit "$COMPILER_EXIT"
fi
rm -rf -- "$COMPILER_HOME" "$COMPILER_TMP"

FULL_COUNT=0
CORE_COUNT=0
while IFS= read -r -d '' dump; do
  ((FULL_COUNT += 1))
  name=${dump##*/}
  if [[ "$name" != *data__* ]]; then
    /bin/cp "$dump" "$GENERATED/core/$name"
    ((CORE_COUNT += 1))
  fi
done < <(/usr/bin/find "$GENERATED/full" -maxdepth 1 -type f -name '*.json' -print0)

if [[ $FULL_COUNT -eq 0 || $CORE_COUNT -eq 0 ]]; then
  echo "regenerate.sh: compiler produced a vacuous dump population (full=$FULL_COUNT core=$CORE_COUNT)" >&2
  exit 1
fi

printf '%s\n' "$FULL_COUNT" > "$GENERATED/full.count"
printf '%s\n' "$CORE_COUNT" > "$GENERATED/core.count"
echo "generated $CORE_COUNT core-module dumps from $FULL_COUNT full-crate dumps in $GENERATED"

if [[ $REPLACE_COMMITTED -eq 1 ]]; then
  rm -f -- "$HERE"/*.json
  /bin/cp "$GENERATED"/core/*.json "$HERE/"
  echo "explicitly replaced $CORE_COUNT committed core-module dumps in $HERE"
fi
