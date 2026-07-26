#!/bin/sh
# Regenerate or validate the cmp leaf harvest using this checkout only. All
# candidate artifacts are authenticated and analyzed before transactional
# publication; a failed command leaves the committed corpus untouched.
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO=$(cd "${REPO:-$HERE/../../../..}" && pwd)
TRUSTC=${TRUSTC:-$REPO/build/host/stage1/bin/trustc}
VALIDATE_ONLY=0
case "${1:-}" in
  --validate-only)
    VALIDATE_ONLY=1
    shift
    ;;
  "") ;;
  *)
    echo "usage: $0 [--validate-only]" >&2
    exit 2
    ;;
esac
test "$#" -eq 0 || {
  echo "usage: $0 [--validate-only]" >&2
  exit 2
}
test -f "$REPO/crates/Cargo.toml" && test -f "$REPO/library/core/src/lib.rs" || {
  echo "error: REPO is not a Trust checkout: $REPO" >&2
  exit 1
}

TMP=$(mktemp -d)
CANDIDATE_ROOT="$HERE/.regenerate-cmp.$$"
BACKUP_ROOT="$HERE/.corpus.previous.$$"
LOCK_DIR="$HERE/.regenerate-cmp.lock"
VALIDATION_TARGET_DIR=${TRUST_CMP_VALIDATION_TARGET_DIR:-$TMP/cargo-target}
PUBLISHING=0

rollback_publication() {
  test "$PUBLISHING" -eq 1 || return 0
  for directory in dumps controls wrappers forgeries; do
    if test -d "$BACKUP_ROOT/$directory"; then
      if test -d "$HERE/$directory"; then
        mv "$HERE/$directory" "$TMP/failed-$directory"
      fi
      mv "$BACKUP_ROOT/$directory" "$HERE/$directory"
    fi
  done
}

cleanup() {
  rollback_publication
  rm -rf "$TMP" "$CANDIDATE_ROOT" "$BACKUP_ROOT" "$LOCK_DIR"
}

test ! -e "$CANDIDATE_ROOT" && test ! -e "$BACKUP_ROOT" || {
  echo "error: stale process-specific cmp regeneration path" >&2
  rm -rf "$TMP"
  exit 1
}
if ! mkdir "$LOCK_DIR"; then
  echo "error: another cmp corpus validation/regeneration is already running" >&2
  rm -rf "$TMP"
  exit 1
fi
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

check_manifest() {
  base=$1
  manifest=$2
  if command -v sha256sum >/dev/null 2>&1; then
    (cd "$base" && sha256sum -c "$manifest")
  else
    (cd "$base" && shasum -a 256 -c "$manifest")
  fi
}

check_manifest "$REPO" "$HERE/SOURCE.sha256"

if test "$VALIDATE_ONLY" -eq 0; then
  test -x "$TRUSTC" || {
    echo "error: dump-capable stage1 trustc not found at $TRUSTC (set TRUSTC explicitly)" >&2
    exit 1
  }
  test ! -L "$TRUSTC" || {
    echo "error: TRUSTC must be a regular executable or hardlink, not a symlink" >&2
    exit 1
  }
  TRUSTC=$(cd "$(dirname "$TRUSTC")" && pwd -P)/$(basename "$TRUSTC")
  expected_version=$(sed -n 's/^trustc version: //p' "$HERE/TOOLCHAIN.sha256")
  expected_trustc_hash=$(sed -n 's/^trustc binary sha256: //p' "$HERE/TOOLCHAIN.sha256")
  expected_driver_name=$(sed -n 's/^rustc_driver dylib: //p' "$HERE/TOOLCHAIN.sha256")
  expected_driver_hash=$(sed -n 's/^rustc_driver sha256: //p' "$HERE/TOOLCHAIN.sha256")
  expected_host=$(sed -n 's/^host: //p' "$HERE/TOOLCHAIN.sha256")
  expected_core_count=$(sed -n 's/^expected recursive core dump count: //p' "$HERE/TOOLCHAIN.sha256")
  expected_source_count=$(sed -n 's/^expected recursive SOURCE dump count: //p' "$HERE/TOOLCHAIN.sha256")
  expected_core_warnings=$(sed -n 's/^expected core survey warning count: //p' "$HERE/TOOLCHAIN.sha256")
  expected_source_warnings=$(sed -n 's/^expected SOURCE survey warning count: //p' "$HERE/TOOLCHAIN.sha256")
  test -n "$expected_version" && test -n "$expected_trustc_hash" && \
    test -n "$expected_driver_name" && test -n "$expected_driver_hash" && \
    test -n "$expected_host" && test -n "$expected_core_count" && \
    test -n "$expected_source_count" && test -n "$expected_core_warnings" && \
    test -n "$expected_source_warnings" || {
    echo "error: incomplete compiler/extraction identity in TOOLCHAIN.sha256" >&2
    exit 1
  }

  run_trustc() {
    env -u DYLD_LIBRARY_PATH -u DYLD_FALLBACK_LIBRARY_PATH \
      -u DYLD_VERSIONED_LIBRARY_PATH -u DYLD_INSERT_LIBRARIES \
      -u DYLD_IMAGE_SUFFIX -u DYLD_ROOT_PATH "$TRUSTC" "$@"
  }
  actual_version=$(run_trustc --version)
  actual_trustc_hash=$(hash_file "$TRUSTC")
  actual_host=$(run_trustc -vV | sed -n 's/^host: //p')
  test "$actual_version" = "$expected_version" || {
    echo "error: trustc version drift: $actual_version" >&2
    exit 1
  }
  test "$actual_trustc_hash" = "$expected_trustc_hash" || {
    echo "error: trustc binary hash drift: $actual_trustc_hash" >&2
    exit 1
  }
  test "$actual_host" = "$expected_host" || {
    echo "error: trustc host drift: $actual_host" >&2
    exit 1
  }

  command -v otool >/dev/null 2>&1 || {
    echo "error: otool is required to authenticate the recorded Apple trustc" >&2
    exit 1
  }
  linked_driver_names=$(otool -L "$TRUSTC" | \
    sed -n 's|.*[/]\(librustc_driver-[^[:space:]]*\.dylib\).*|\1|p')
  linked_driver_count=$(printf '%s\n' "$linked_driver_names" | sed '/^$/d' | wc -l | tr -d ' ')
  test "$linked_driver_count" -eq 1 || {
    echo "error: trustc does not link exactly one rustc_driver dylib" >&2
    exit 1
  }
  test "$linked_driver_names" = "$expected_driver_name" || {
    echo "error: trustc links unexpected rustc_driver: $linked_driver_names" >&2
    exit 1
  }
  linked_rpaths=$(otool -l "$TRUSTC" | awk '
    $1 == "cmd" && $2 == "LC_RPATH" { in_rpath = 1; next }
    in_rpath && $1 == "path" { print $2; in_rpath = 0 }
  ')
  test "$linked_rpaths" = '@loader_path/../lib' || {
    echo "error: trustc LC_RPATH is not exactly @loader_path/../lib: $linked_rpaths" >&2
    exit 1
  }
  TRUSTC_DRIVER=$(cd "$(dirname "$TRUSTC")/../lib" && pwd -P)/$expected_driver_name
  test -f "$TRUSTC_DRIVER" || {
    echo "error: pinned adjacent rustc_driver not found at $TRUSTC_DRIVER" >&2
    exit 1
  }
  actual_driver_hash=$(hash_file "$TRUSTC_DRIVER")
  test "$actual_driver_hash" = "$expected_driver_hash" || {
    echo "error: rustc_driver hash drift: $actual_driver_hash" >&2
    exit 1
  }

  cp -R "$REPO/library/core" "$TMP/L-core"
  mkdir -p "$TMP/L"
  mv "$TMP/L-core" "$TMP/L/core"
  ln -s "$REPO/library/stdarch" "$TMP/L/stdarch"
  ln -s "$REPO/library/portable-simd" "$TMP/L/portable-simd"
  patch --batch --forward -p0 -d "$TMP/L/core" < "$HERE/int_log10-workaround.diff"

  TRUST_LIBRARY_PATH=${TRUST_LIBRARY_PATH:-}
  if test -z "$TRUST_LIBRARY_PATH"; then
    command -v brew >/dev/null 2>&1 || {
      echo "error: set TRUST_LIBRARY_PATH (or install Homebrew for automatic discovery)" >&2
      exit 1
    }
    if ! brew_prefix=$(brew --prefix); then
      echo "error: Homebrew prefix discovery failed; set TRUST_LIBRARY_PATH explicitly" >&2
      exit 1
    fi
    test -n "$brew_prefix" || {
      echo "error: Homebrew returned an empty prefix; set TRUST_LIBRARY_PATH explicitly" >&2
      exit 1
    }
    TRUST_LIBRARY_PATH=$brew_prefix/lib
  fi
  test -d "$TRUST_LIBRARY_PATH" || {
    echo "error: extraction LIBRARY_PATH is unavailable: $TRUST_LIBRARY_PATH" >&2
    exit 1
  }
  mkdir -p "$TMP/core-dump"
  set +e
  (
    cd "$TMP"
    LIBRARY_PATH="$TRUST_LIBRARY_PATH" \
      run_trustc --edition 2024 --crate-type lib --crate-name core \
      -Z"trust-dump=mir:$TMP/core-dump" -Ztrust-policy=advisory \
      -o "$TMP/core.rlib" "$TMP/L/core/src/lib.rs"
  ) > "$TMP/core.stdout" 2> "$TMP/core.stderr"
  core_status=$?
  set -e
  test "$core_status" -eq 101 || {
    echo "error: pinned core extraction exit drift: expected 101, got $core_status" >&2
    exit 1
  }
  test ! -s "$TMP/core.stdout" && \
    test "$(grep -c '^error:' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c '^error: internal compiler error: unexpected ambiguity:' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c -F '::ptr::metadata::Pointee::Metadata' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c -F 'num::nonzero::NonZero<T/#0>' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c -F 'NormalizationResult' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c -F 'note: no errors encountered even though delayed bugs were created' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c -F 'note: those delayed bugs will now be shown as internal compiler errors' "$TMP/core.stderr")" -eq 1 && \
    test "$(grep -c -F "warning: $expected_core_warnings warnings emitted" "$TMP/core.stderr")" -eq 1 || {
    echo "error: core extraction did not fail with the one exact recorded delayed bug" >&2
    tail -n 100 "$TMP/core.stderr" >&2
    exit 1
  }
  core_count=$(find "$TMP/core-dump" -type f -name '*.json' | wc -l | tr -d ' ')
  test "$core_count" -eq "$expected_core_count" || {
    echo "error: exact core dump inventory drift: expected $expected_core_count, found $core_count" >&2
    exit 1
  }

  mkdir -p "$TMP/source-dump"
  (
    cd "$TMP"
    LIBRARY_PATH="$TRUST_LIBRARY_PATH" \
      run_trustc --edition 2024 --crate-type lib --crate-name stdlib_leaf_cmp_source \
      -Z"trust-dump=mir:$TMP/source-dump" -Ztrust-policy=advisory \
      -o "$TMP/source.rlib" "$HERE/SOURCE/src/lib.rs"
  ) > "$TMP/source.stdout" 2> "$TMP/source.stderr"
  test ! -s "$TMP/source.stdout" || {
    echo "error: SOURCE extraction unexpectedly wrote stdout" >&2
    exit 1
  }
  test "$(awk '/^error:/ { count++ } END { print count + 0 }' "$TMP/source.stderr")" -eq 0 && \
    test "$(grep -c -F "warning: $expected_source_warnings warnings emitted" "$TMP/source.stderr")" -eq 1 || {
    echo "error: SOURCE extraction diagnostics drifted" >&2
    tail -n 100 "$TMP/source.stderr" >&2
    exit 1
  }
  source_count=$(find "$TMP/source-dump" -type f -name '*.json' | wc -l | tr -d ' ')
  test "$source_count" -eq "$expected_source_count" || {
    echo "error: exact SOURCE dump inventory drift: expected $expected_source_count, found $source_count" >&2
    exit 1
  }
  test "$(hash_file "$TRUSTC")" = "$expected_trustc_hash" && \
    test "$(hash_file "$TRUSTC_DRIVER")" = "$expected_driver_hash" || {
    echo "error: trustc or rustc_driver changed during extraction" >&2
    exit 1
  }

  python3 "$HERE/prepare_corpus.py" \
    "$TMP/core-dump" "$core_count" "$TMP/source-dump" "$CANDIDATE_ROOT"
else
  mkdir "$CANDIDATE_ROOT"
  for directory in dumps controls wrappers forgeries; do
    cp -R "$HERE/$directory" "$CANDIDATE_ROOT/$directory"
  done
fi

for table in results.tsv controls.tsv wrappers.tsv forgeries.tsv; do
  cp "$HERE/$table" "$CANDIDATE_ROOT/$table"
done
python3 "$HERE/canonicalize_dump_paths.py" \
  "$CANDIDATE_ROOT/dumps" "$CANDIDATE_ROOT/controls" \
  "$CANDIDATE_ROOT/wrappers" "$CANDIDATE_ROOT/forgeries"

# A manifest is an inventory guarantee only when it names every published JSON
# and result table exactly once. Check coverage before checking the hashes.
(
  cd "$CANDIDATE_ROOT"
  find dumps controls wrappers forgeries -type f -print
  printf '%s\n' results.tsv controls.tsv wrappers.tsv forgeries.tsv
) | LC_ALL=C sort > "$TMP/expected-artifacts"
awk '
  NF != 2 || length($1) != 64 { bad = 1 }
  { print $2 }
  END { exit bad }
' "$HERE/ARTIFACTS.sha256" | LC_ALL=C sort > "$TMP/manifest-artifacts" || {
  echo "error: malformed ARTIFACTS.sha256" >&2
  exit 1
}
cmp "$TMP/expected-artifacts" "$TMP/manifest-artifacts" || {
  echo "error: ARTIFACTS.sha256 does not exactly cover the published cmp corpus" >&2
  exit 1
}
check_manifest "$CANDIDATE_ROOT" "$HERE/ARTIFACTS.sha256"

CARGO_TARGET_DIR="$VALIDATION_TARGET_DIR" CARGO_NET_OFFLINE=${CARGO_NET_OFFLINE:-true} \
  RUSTC_BOOTSTRAP=1 \
  cargo build --release --locked -p trust-clean --manifest-path "$REPO/crates/Cargo.toml" \
  --bin ff-gate-diagnose-2026-07-10 --bin census-2026-07-06
TOOLS="$VALIDATION_TARGET_DIR/release"
ff_hash=$(hash_file "$TOOLS/ff-gate-diagnose-2026-07-10")
census_hash=$(hash_file "$TOOLS/census-2026-07-06")

for lane in dumps controls wrappers forgeries; do
  "$TOOLS/ff-gate-diagnose-2026-07-10" "$CANDIDATE_ROOT/$lane" \
    > "$TMP/$lane.ff.tsv" 2> "$TMP/$lane.ff.stderr"
  TRUST_CENSUS_BUDGET_SECS=${TRUST_CENSUS_BUDGET_SECS:-180} \
    "$TOOLS/census-2026-07-06" "$CANDIDATE_ROOT/$lane" \
    > "$TMP/$lane.census.tsv" 2> "$TMP/$lane.census.stderr"
  if grep -i 'warning' "$TMP/$lane.ff.stderr" "$TMP/$lane.census.stderr" >/dev/null; then
    echo "error: analyzer warning makes $lane results non-authoritative" >&2
    grep -i 'warning' "$TMP/$lane.ff.stderr" "$TMP/$lane.census.stderr" >&2
    exit 1
  fi
  case "$lane" in
    dumps) expected_table=results.tsv ;;
    *) expected_table=$lane.tsv ;;
  esac
  python3 "$HERE/validate_results.py" \
    "$CANDIDATE_ROOT/$expected_table" "$CANDIDATE_ROOT/$lane" \
    "$TMP/$lane.ff.tsv" "$TMP/$lane.census.tsv"
done

test "$(hash_file "$TOOLS/ff-gate-diagnose-2026-07-10")" = "$ff_hash" && \
  test "$(hash_file "$TOOLS/census-2026-07-06")" = "$census_hash" || {
  echo "error: a validation tool changed while the corpus was being checked" >&2
  exit 1
}

if test "$VALIDATE_ONLY" -eq 0; then
  mkdir "$BACKUP_ROOT"
  PUBLISHING=1
  for directory in dumps controls wrappers forgeries; do
    mv "$HERE/$directory" "$BACKUP_ROOT/$directory"
  done
  for directory in dumps controls wrappers forgeries; do
    mv "$CANDIDATE_ROOT/$directory" "$HERE/$directory"
  done
  PUBLISHING=0
  rm -rf "$BACKUP_ROOT"
fi

echo "validated exact cmp corpus: real 0/12, controls 5/5, wrappers 0/7, forgeries 1/6; kernel_rejected=0"
