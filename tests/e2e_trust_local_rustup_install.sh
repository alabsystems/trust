#!/bin/bash
# Exercise a copied Trust stage2 sysroot as a read-only, relocatable local
# installation. This is a non-authoritative local diagnostic; it does not prove
# that a public rustup channel or downloadable package exists.

set -euo pipefail
umask 077

CALLER_DIR="$(pwd -P)"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
PYTHON3_BIN="${TRUST_E2E_PYTHON3:-}"
if [ -z "$PYTHON3_BIN" ]; then
    PYTHON3_BIN="$(command -v python3 2>/dev/null || true)"
fi
HOST_RUSTUP_BIN="$(command -v rustup 2>/dev/null || true)"
SOURCE_SYSROOT="${TRUST_E2E_STAGE2_SYSROOT:-}"
STAGE_PROVENANCE="${TRUST_E2E_STAGE_PROVENANCE:-}"
RECEIPT_OUT="${TRUST_E2E_RECEIPT:-}"
RECEIPT_HELPER="$TRUST_ROOT/scripts/lib/trust_e2e_receipt.py"
SET_DEFAULT=0
KEEP_TEMP=0

usage() {
    cat <<'EOF'
Usage: tests/e2e_trust_local_rustup_install.sh [options]

Options:
  --source-sysroot PATH  Copy this complete stage2/installed sysroot
  --stage-provenance PATH
                         Stage2 tool-provenance.json to bind into the receipt
  --receipt PATH         Publish a new local diagnostic record after a pass; PATH
                         is anchored to the invocation directory and must not
                         already exist
  --set-default          Exercise isolated rustup default/proxy dispatch too
  --keep-temp            Preserve the isolated test directory for diagnosis
  -h, --help             Show this help

The script never changes the caller's rustup or Cargo homes. The copied
toolchain, registries, build outputs, and optional default all live below one
new temporary directory.
EOF
}

fail() {
    printf 'FAIL: %s\n' "$*" >&2
    exit 1
}

canonical_temp_directory() {
    (
        cd "$1" 2>/dev/null
        pwd -P
    )
}

temp_directory_mode() {
    local path="$1"
    local value

    value="$(/usr/bin/stat -f '%Lp' "$path" 2>/dev/null || true)"
    case "$value" in
        700|0700) printf '%s\n' "$value"; return 0 ;;
    esac
    value="$(/usr/bin/stat -c '%a' "$path" 2>/dev/null || true)"
    case "$value" in
        700|0700) printf '%s\n' "$value"; return 0 ;;
    esac
    return 1
}

temp_directory_identity() {
    local path="$1"
    local value

    value="$(/usr/bin/stat -f '%d:%i' "$path" 2>/dev/null || true)"
    case "$value" in
        *[!0-9:]*|*:*:*) ;;
        [0-9]*:[0-9]*) printf '%s\n' "$value"; return 0 ;;
    esac
    value="$(/usr/bin/stat -c '%d:%i' "$path" 2>/dev/null || true)"
    case "$value" in
        *[!0-9:]*|*:*:*) ;;
        [0-9]*:[0-9]*) printf '%s\n' "$value"; return 0 ;;
    esac
    return 1
}

validate_private_temp_root() {
    local path="$1"
    local expected_identity="${2:-}"
    local canonical parent name suffix identity

    case "$path" in
        /*) ;;
        *) printf 'FAIL: refusing non-absolute temporary root: %s\n' "$path" >&2; return 1 ;;
    esac
    if [ ! -d "$path" ] || [ -L "$path" ]; then
        printf 'FAIL: refusing temporary root that is not a real directory: %s\n' "$path" >&2
        return 1
    fi
    if [ ! -O "$path" ]; then
        printf 'FAIL: refusing temporary root not owned by the current user: %s\n' "$path" >&2
        return 1
    fi
    temp_directory_mode "$path" >/dev/null || {
        printf 'FAIL: refusing temporary root without private mode 700: %s\n' "$path" >&2
        return 1
    }
    canonical="$(canonical_temp_directory "$path")" || return 1
    parent="${canonical%/*}"
    name="${canonical##*/}"
    [ "$parent" = "$SYSTEM_TEMP_PARENT" ] || {
        printf 'FAIL: refusing temporary root outside fixed system temp parent: %s\n' "$canonical" >&2
        return 1
    }
    case "$name" in
        trust-installed-e2e.*) ;;
        *) printf 'FAIL: refusing temporary root with unexpected name: %s\n' "$canonical" >&2; return 1 ;;
    esac
    suffix="${name#trust-installed-e2e.}"
    case "$suffix" in
        ??????*) ;;
        *) printf 'FAIL: refusing temporary root with short random suffix: %s\n' "$canonical" >&2; return 1 ;;
    esac
    identity="$(temp_directory_identity "$path")" || {
        printf 'FAIL: could not bind temporary root identity: %s\n' "$canonical" >&2
        return 1
    }
    if [ -n "$expected_identity" ] && [ "$identity" != "$expected_identity" ]; then
        printf 'FAIL: refusing replaced temporary root: %s\n' "$canonical" >&2
        return 1
    fi
}

skip_or_fail() {
    if [ -z "$RECEIPT_OUT" ] && [ "${TRUST_E2E_ALLOW_SKIP:-0}" = "1" ]; then
        printf 'SKIP: %s\n' "$*" >&2
        exit 0
    fi
    if [ -n "$RECEIPT_OUT" ]; then
        fail "$* (receipt mode forbids diagnostic skips)"
    fi
    fail "$* (TRUST_E2E_ALLOW_SKIP=1 is diagnostic-only)"
}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --source-sysroot)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--source-sysroot requires a path"
            SOURCE_SYSROOT="$1"
            ;;
        --source-sysroot=*)
            SOURCE_SYSROOT="${1#*=}"
            [ -n "$SOURCE_SYSROOT" ] || fail "--source-sysroot requires a path"
            ;;
        --stage-provenance)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--stage-provenance requires a path"
            STAGE_PROVENANCE="$1"
            ;;
        --stage-provenance=*)
            STAGE_PROVENANCE="${1#*=}"
            [ -n "$STAGE_PROVENANCE" ] || fail "--stage-provenance requires a path"
            ;;
        --receipt)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--receipt requires a path"
            RECEIPT_OUT="$1"
            ;;
        --receipt=*)
            RECEIPT_OUT="${1#*=}"
            [ -n "$RECEIPT_OUT" ] || fail "--receipt requires a path"
            ;;
        --set-default)
            SET_DEFAULT=1
            ;;
        --keep-temp)
            KEEP_TEMP=1
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            fail "unknown argument: $1"
            ;;
    esac
    shift
done

canonical_dir() {
    (
        cd "$1"
        pwd -P
    )
}

sha256_file() {
    "$PYTHON3_BIN" - "$1" <<'PY'
import hashlib
import pathlib
import sys

digest = hashlib.sha256()
with pathlib.Path(sys.argv[1]).open("rb") as handle:
    for chunk in iter(lambda: handle.read(1024 * 1024), b""):
        digest.update(chunk)
print(digest.hexdigest())
PY
}

prepare_receipt_output() {
    [ -n "$RECEIPT_OUT" ] || return 0
    command -v git >/dev/null 2>&1 || fail "git is required in receipt mode"
    [ -f "$RECEIPT_HELPER" ] \
        || fail "receipt helper is missing: $RECEIPT_HELPER"

    normalized_receipt="$(
        "$PYTHON3_BIN" "$RECEIPT_HELPER" prepare-output \
            --output "$RECEIPT_OUT" \
            --caller-directory "$CALLER_DIR"
    )" || fail "receipt destination is not safe for a new diagnostic record"
    [ -n "$normalized_receipt" ] \
        || fail "receipt helper returned an empty destination"
    RECEIPT_OUT="$normalized_receipt"

    # A new path inside the checkout is permitted only where Git explicitly
    # ignores it (for example build/evidence). Otherwise publication itself
    # would invalidate the receipt's clean-source claim.
    case "$RECEIPT_OUT" in
        "$TRUST_ROOT"/*)
            receipt_relative="${RECEIPT_OUT#"$TRUST_ROOT"/}"
            if git -C "$TRUST_ROOT" ls-files --error-unmatch -- "$receipt_relative" >/dev/null 2>&1; then
                fail "receipt destination must not be a tracked repository path: $RECEIPT_OUT"
            fi
            git -C "$TRUST_ROOT" check-ignore --quiet --no-index -- "$receipt_relative" \
                || fail "receipt destination inside the repository must be ignored: $RECEIPT_OUT"
            ;;
    esac
}

require_clean_repository_state() {
    local dirty_message="$1"
    local repository_status
    if ! repository_status="$(git -C "$TRUST_ROOT" status --porcelain=v1 --untracked-files=all --ignore-submodules=none)"; then
        fail "could not inspect repository and submodule state"
    fi
    [ -z "$repository_status" ] || fail "$dirty_message"
}

require_materialized_inputs_tracked() {
    local input_status
    if ! input_status="$(
        git -C "$TRUST_ROOT" status \
            --porcelain=v1 \
            --untracked-files=all \
            --ignored=matching \
            --ignore-submodules=none \
            -- Cargo.lock compiler library src/llvm-project/libunwind
    )"; then
        fail "could not inspect the Git status of materialized source inputs"
    fi
    if [ -n "$input_status" ]; then
        printf '%s\n' "$input_status" >&2
        fail "materialized source inputs include modified, untracked, or ignored paths; only clean HEAD-tracked files may be copied"
    fi
}

verify_repository_before_publication() {
    [ "$(git -C "$TRUST_ROOT" rev-parse --verify HEAD)" = "$REPO_HEAD_START" ] \
        || fail "repository HEAD changed before publishing the installed-toolchain record"
    require_clean_repository_state \
        "repository or submodule state changed before publishing the installed-toolchain record"
    require_materialized_inputs_tracked
    [ "$(sha256_file "$SCRIPT_DIR/e2e_trust_local_rustup_install.sh")" = "$SCRIPT_SHA256_START" ] \
        || fail "installed-toolchain gate script changed before publishing its record"
    [ "$(sha256_file "$RECEIPT_HELPER")" = "$RECEIPT_HELPER_SHA256_START" ] \
        || fail "receipt helper changed before publishing the installed-toolchain record"
    [ "$(sha256_file "$STAGE_PROVENANCE")" = "$PROVENANCE_SHA256_START" ] \
        || fail "Stage2 provenance changed before publishing the installed-toolchain record"
    "$PYTHON3_BIN" "$RECEIPT_HELPER" validate-stage \
        --provenance "$STAGE_PROVENANCE" \
        --repository-head "$REPO_HEAD_START" \
        --trustc "$SOURCE_SYSROOT/bin/trustc" >/dev/null
}

[ -n "$PYTHON3_BIN" ] || skip_or_fail "python3 is required"
[ -f "$RECEIPT_HELPER" ] || fail "receipt helper is missing: $RECEIPT_HELPER"
[ -z "$RECEIPT_OUT" ] || prepare_receipt_output
[ -n "$HOST_RUSTUP_BIN" ] || skip_or_fail "rustup is required for the isolated link rehearsal"

if [ -z "$SOURCE_SYSROOT" ]; then
    for candidate in \
        "$TRUST_ROOT/build/host/stage2" \
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage2" \
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage2" \
        "$TRUST_ROOT/build/aarch64-unknown-linux-gnu/stage2" \
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2"
    do
        if [ -x "$candidate/bin/trustc" ]; then
            SOURCE_SYSROOT="$candidate"
            break
        fi
    done
fi

[ -n "$SOURCE_SYSROOT" ] || skip_or_fail "no local stage2 sysroot was found"
[ -d "$SOURCE_SYSROOT" ] || fail "source sysroot is not a directory: $SOURCE_SYSROOT"
SOURCE_SYSROOT="$(canonical_dir "$SOURCE_SYSROOT")"

if [ -z "$STAGE_PROVENANCE" ]; then
    STAGE_PROVENANCE="$SOURCE_SYSROOT/tool-provenance.json"
fi

REPO_HEAD_START=""
SCRIPT_SHA256_START=""
RECEIPT_HELPER_SHA256_START=""
PROVENANCE_SHA256_START=""
if [ -n "$RECEIPT_OUT" ]; then
    command -v git >/dev/null 2>&1 || fail "git is required in receipt mode"
    [ -f "$STAGE_PROVENANCE" ] \
        || fail "Stage2 provenance is missing: $STAGE_PROVENANCE"
    STAGE_PROVENANCE="$($PYTHON3_BIN - "$STAGE_PROVENANCE" <<'PY'
import pathlib
import sys
print(pathlib.Path(sys.argv[1]).resolve(strict=True))
PY
)"
    REPO_HEAD_START="$(git -C "$TRUST_ROOT" rev-parse --verify HEAD)"
    [ -n "$REPO_HEAD_START" ] || fail "could not resolve repository HEAD"
    require_clean_repository_state \
        "receipt mode requires a clean repository and clean submodules"
    require_materialized_inputs_tracked
    SCRIPT_SHA256_START="$(sha256_file "$SCRIPT_DIR/e2e_trust_local_rustup_install.sh")"
    RECEIPT_HELPER_SHA256_START="$(sha256_file "$RECEIPT_HELPER")"
    PROVENANCE_SHA256_START="$(sha256_file "$STAGE_PROVENANCE")"
    "$PYTHON3_BIN" "$RECEIPT_HELPER" validate-stage \
        --provenance "$STAGE_PROVENANCE" \
        --repository-head "$REPO_HEAD_START" \
        --trustc "$SOURCE_SYSROOT/bin/trustc" >/dev/null
fi

write_content_manifest() {
    local root output normalize_writes record_modes
    root="$1"
    output="$2"
    normalize_writes="$3"
    record_modes="${4:-1}"
    "$PYTHON3_BIN" - "$root" "$normalize_writes" "$record_modes" >"$output" <<'PY'
import hashlib
import json
import pathlib
import stat
import sys

root = pathlib.Path(sys.argv[1])
normalize_writes = sys.argv[2] == "1"
record_modes = sys.argv[3] == "1"
paths = [root, *root.rglob("*")]
for path in sorted(paths, key=lambda item: item.relative_to(root).as_posix()):
    rel = path.relative_to(root).as_posix()
    info = path.lstat()
    mode = stat.S_IMODE(info.st_mode)
    if normalize_writes and not stat.S_ISLNK(info.st_mode):
        mode &= ~(stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH)
    if stat.S_ISDIR(info.st_mode):
        row = {"path": rel, "type": "directory"}
    elif stat.S_ISLNK(info.st_mode):
        row = {"path": rel, "type": "symlink", "target": path.readlink().as_posix()}
    elif stat.S_ISREG(info.st_mode):
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        row = {
            "path": rel,
            "type": "file",
            "size": info.st_size,
            "sha256": digest.hexdigest(),
        }
    else:
        raise SystemExit(f"unsupported filesystem entry in sysroot: {rel}")
    if record_modes and not stat.S_ISLNK(info.st_mode):
        row["mode"] = mode
    print(json.dumps(row, sort_keys=True, separators=(",", ":")))
PY
}

resolve_admitted_source_target() {
    relative_link="$1"
    source_link="$SOURCE_SYSROOT/$relative_link"
    [ -L "$source_link" ] || return 0
    "$PYTHON3_BIN" - "$source_link" "$TRUST_ROOT" <<'PY'
import pathlib
import sys

link = pathlib.Path(sys.argv[1])
repository = pathlib.Path(sys.argv[2]).resolve(strict=True)
target = link.resolve(strict=True)
if target != repository:
    raise SystemExit(
        f"admitted source-sysroot link must resolve to the exact bound checkout root: {link} -> {target}"
    )
print(target)
PY
}

write_materialized_source_inputs_manifest() {
    output="$1"
    library_target="$2"
    compiler_target="$3"
    library_binding="$4"
    compiler_binding="$5"
    "$PYTHON3_BIN" - \
        "$library_target" \
        "$compiler_target" \
        "$library_binding" \
        "$compiler_binding" >"$output" <<'PY'
import hashlib
import json
import pathlib
import stat
import sys

library_value, compiler_value, library_binding, compiler_binding = sys.argv[1:]


def emit(row):
    print(json.dumps(row, sort_keys=True, separators=(",", ":")))


def manifest_subset(label, path, *, required, expected_kind):
    if not path.exists() and not path.is_symlink():
        if required:
            raise SystemExit(f"materialized source input is missing: {label}: {path}")
        emit({"input": label, "type": "absent"})
        return
    root_info = path.lstat()
    if expected_kind == "directory" and (
        not stat.S_ISDIR(root_info.st_mode) or stat.S_ISLNK(root_info.st_mode)
    ):
        raise SystemExit(f"materialized source input is not a real directory: {label}: {path}")
    if expected_kind == "file" and (
        not stat.S_ISREG(root_info.st_mode) or stat.S_ISLNK(root_info.st_mode)
    ):
        raise SystemExit(f"materialized source input is not a real file: {label}: {path}")

    paths = [path, *path.rglob("*")] if expected_kind == "directory" else [path]
    for entry in sorted(paths, key=lambda item: item.relative_to(path).as_posix()):
        relative = entry.relative_to(path).as_posix()
        info = entry.lstat()
        row = {"input": label, "path": relative}
        if stat.S_ISDIR(info.st_mode):
            row["type"] = "directory"
        elif stat.S_ISLNK(info.st_mode):
            row.update(type="symlink", target=entry.readlink().as_posix())
        elif stat.S_ISREG(info.st_mode):
            digest = hashlib.sha256()
            with entry.open("rb") as handle:
                for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                    digest.update(chunk)
            row.update(type="file", size=info.st_size, sha256=digest.hexdigest())
        else:
            raise SystemExit(f"unsupported materialized source input: {label}: {entry}")
        emit(row)


def bind_target(kind, value, binding):
    if not value:
        if binding:
            raise SystemExit(f"materialized {kind} source binding has no content root")
        emit({"input": f"{kind}-link-target", "type": "absent"})
        return None
    if not binding:
        raise SystemExit(f"materialized {kind} source content has no bound source target")
    target = pathlib.Path(value).resolve(strict=True)
    bound_target = pathlib.Path(binding).resolve(strict=True)
    emit({"input": f"{kind}-link-target", "path": str(bound_target), "type": "target"})
    return target


library_target = bind_target("library", library_value, library_binding)
compiler_target = bind_target("compiler", compiler_value, compiler_binding)
if library_target is not None:
    manifest_subset(
        "library/library", library_target / "library", required=True, expected_kind="directory"
    )
    manifest_subset(
        "library/libunwind",
        library_target / "src" / "llvm-project" / "libunwind",
        required=False,
        expected_kind="directory",
    )
if compiler_target is not None:
    manifest_subset(
        "compiler/compiler", compiler_target / "compiler", required=True, expected_kind="directory"
    )
    manifest_subset(
        "compiler/proc_macro",
        compiler_target / "library" / "proc_macro",
        required=True,
        expected_kind="directory",
    )
    manifest_subset(
        "compiler/Cargo.lock",
        compiler_target / "Cargo.lock",
        required=False,
        expected_kind="file",
    )
PY
}

require_source_target_unchanged() {
    relative_link="$1"
    expected_target="$2"
    current_target="$(resolve_admitted_source_target "$relative_link")" \
        || fail "could not re-resolve admitted source input: $relative_link"
    [ "$current_target" = "$expected_target" ] \
        || fail "admitted source input changed during the gate: $relative_link"
}

SYSTEM_TEMP_PARENT="$(canonical_temp_directory /tmp)" \
    || fail "fixed system temporary parent is unavailable: /tmp"
RAW_TMP_ROOT="$(/usr/bin/mktemp -d /tmp/trust-installed-e2e.XXXXXX)" \
    || fail "could not create a private fixed-root temporary directory"
case "$RAW_TMP_ROOT" in
    /*) ;;
    *) fail "system mktemp returned a non-absolute path: $RAW_TMP_ROOT" ;;
esac
TMP_ROOT="$(canonical_temp_directory "$RAW_TMP_ROOT")" \
    || fail "could not canonicalize the new temporary directory"
validate_private_temp_root "$TMP_ROOT" \
    || fail "new temporary directory failed private-root validation"
TMP_ROOT_ID="$(temp_directory_identity "$TMP_ROOT")" \
    || fail "could not record the new temporary directory identity"
validate_private_temp_root "$TMP_ROOT" "$TMP_ROOT_ID" \
    || fail "new temporary directory identity changed before use"
cleanup() {
    local original_status=$?
    trap - EXIT HUP INT TERM

    if [ "$KEEP_TEMP" = "1" ]; then
        validate_private_temp_root "$TMP_ROOT" "$TMP_ROOT_ID" || exit 2
        printf 'kept isolated install gate directory: %s\n' "$TMP_ROOT" >&2
        exit "$original_status"
    fi
    "$PYTHON3_BIN" "$RECEIPT_HELPER" remove-private-temp \
        --path "$TMP_ROOT" \
        --system-parent "$SYSTEM_TEMP_PARENT" \
        --expected-prefix "trust-installed-e2e." \
        --expected-identity "$TMP_ROOT_ID" || {
        printf 'FAIL: descriptor-bound cleanup refused the temporary tree: %s\n' "$TMP_ROOT" >&2
        exit 2
    }
    if [ -e "$TMP_ROOT" ] || [ -L "$TMP_ROOT" ]; then
        printf 'FAIL: bound temporary tree still exists after cleanup: %s\n' "$TMP_ROOT" >&2
        exit 2
    fi
    exit "$original_status"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

INSTALL_ROOT="$TMP_ROOT/install"
INSTALLED_SYSROOT="$INSTALL_ROOT/trust"
ISOLATED_HOME="$TMP_ROOT/home"
ISOLATED_RUSTUP_HOME="$TMP_ROOT/rustup"
ISOLATED_CARGO_HOME="$TMP_ROOT/cargo"
ISOLATED_TMP="$TMP_ROOT/tmp"
ISOLATED_TARGET="$TMP_ROOT/target"
PROXY_BIN="$ISOLATED_CARGO_HOME/bin"
WORKSPACE="$TMP_ROOT/workspace/installed-serde-derive"
TOOLCHAIN_NAME="trust"
SYSTEM_PATH="/usr/bin:/bin:/usr/sbin:/sbin"

mkdir -p \
    "$INSTALLED_SYSROOT" \
    "$ISOLATED_HOME" \
    "$ISOLATED_RUSTUP_HOME" \
    "$PROXY_BIN" \
    "$ISOLATED_TMP" \
    "$ISOLATED_TARGET" \
    "$(dirname "$WORKSPACE")"

# Bind the complete source sysroot before any scan, copy, or source-link
# materialization so the final equality check covers every consumed input.
SOURCE_MANIFEST="$TMP_ROOT/source-sysroot.ndjson"
SOURCE_COPY_CONTENT_MANIFEST="$TMP_ROOT/source-sysroot-copy-content.ndjson"
SOURCE_LINK_INPUT_MANIFEST="$TMP_ROOT/materialized-source-inputs.ndjson"
SERDE_FIXTURE_MANIFEST="$TMP_ROOT/serde-fixture.ndjson"
LIBRARY_SOURCE_TARGET="$(resolve_admitted_source_target "lib/rustlib/src/rust")" \
    || fail "could not bind the admitted library source input"
COMPILER_SOURCE_TARGET="$(resolve_admitted_source_target "lib/rustlib/rustc-src/rust")" \
    || fail "could not bind the admitted compiler source input"
if [ -n "$RECEIPT_OUT" ]; then
    write_content_manifest "$SOURCE_SYSROOT" "$SOURCE_MANIFEST" 0
    write_content_manifest "$SOURCE_SYSROOT" "$SOURCE_COPY_CONTENT_MANIFEST" 0 0
    write_materialized_source_inputs_manifest \
        "$SOURCE_LINK_INPUT_MANIFEST" \
        "$LIBRARY_SOURCE_TARGET" \
        "$COMPILER_SOURCE_TARGET" \
        "$LIBRARY_SOURCE_TARGET" \
        "$COMPILER_SOURCE_TARGET"
    write_content_manifest \
        "$TRUST_ROOT/tests/fixtures/installed-serde-derive" \
        "$SERDE_FIXTURE_MANIFEST" \
        0
fi

# A raw build sysroot uses exactly two repo-local source symlinks. Admit only
# those inputs and materialize their installer-equivalent source subsets below.
# Every other escaping or broken link is a hard failure.
"$PYTHON3_BIN" - "$SOURCE_SYSROOT" "$TRUST_ROOT" <<'PY'
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve(strict=True)
repository = pathlib.Path(sys.argv[2]).resolve(strict=True)
admitted = {
    pathlib.PurePosixPath("lib/rustlib/src/rust"),
    pathlib.PurePosixPath("lib/rustlib/rustc-src/rust"),
}
for path in root.rglob("*"):
    if not path.is_symlink():
        continue
    rel = pathlib.PurePosixPath(path.relative_to(root).as_posix())
    try:
        resolved = path.resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise SystemExit(f"broken source-sysroot symlink {rel}: {error}")
    try:
        resolved.relative_to(root)
    except ValueError:
        if rel not in admitted:
            raise SystemExit(f"source-sysroot symlink escapes selected root: {rel} -> {resolved}")
        if resolved != repository:
            raise SystemExit(
                f"admitted source-sysroot symlink must resolve to the exact bound checkout root: {rel} -> {resolved}"
            )
PY

printf 'copying standalone sysroot: %s -> %s\n' "$SOURCE_SYSROOT" "$INSTALLED_SYSROOT"
cp -R "$SOURCE_SYSROOT/." "$INSTALLED_SYSROOT/"

if [ -n "$RECEIPT_OUT" ]; then
    COPIED_SYSROOT_CONTENT_MANIFEST="$TMP_ROOT/copied-sysroot-before-materialization.ndjson"
    write_content_manifest "$INSTALLED_SYSROOT" "$COPIED_SYSROOT_CONTENT_MANIFEST" 0 0
    cmp -s "$SOURCE_COPY_CONTENT_MANIFEST" "$COPIED_SYSROOT_CONTENT_MANIFEST" \
        || fail "copied sysroot differs from the bound source before source-link materialization"
fi

materialize_source_link() {
    relative_link="$1"
    source_kind="$2"
    source_tree="$3"
    source_link="$SOURCE_SYSROOT/$relative_link"
    installed_link="$INSTALLED_SYSROOT/$relative_link"

    if [ ! -L "$source_link" ]; then
        [ -z "$source_tree" ] \
            || fail "admitted source link disappeared after its target was bound: $relative_link"
        return 0
    fi
    [ -n "$source_tree" ] \
        || fail "admitted source link appeared after the source baseline: $relative_link"
    [ -L "$installed_link" ] || fail "copied source link changed type: $relative_link"
    rm "$installed_link"
    mkdir -p "$installed_link"
    case "$source_kind" in
        library)
            [ -d "$source_tree/library" ] || fail "source link lacks library/: $source_link"
            cp -R "$source_tree/library" "$installed_link/library"
            if [ -d "$source_tree/src/llvm-project/libunwind" ]; then
                mkdir -p "$installed_link/src/llvm-project"
                cp -R "$source_tree/src/llvm-project/libunwind" \
                    "$installed_link/src/llvm-project/libunwind"
            fi
            ;;
        compiler)
            [ -d "$source_tree/compiler" ] || fail "source link lacks compiler/: $source_link"
            [ -d "$source_tree/library/proc_macro" ] \
                || fail "source link lacks library/proc_macro: $source_link"
            cp -R "$source_tree/compiler" "$installed_link/compiler"
            mkdir -p "$installed_link/library"
            cp -R "$source_tree/library/proc_macro" "$installed_link/library/proc_macro"
            if [ -f "$source_tree/Cargo.lock" ]; then
                cp "$source_tree/Cargo.lock" "$installed_link/Cargo.lock"
            fi
            ;;
        *)
            fail "unknown source materialization kind: $source_kind"
            ;;
    esac
}

materialize_source_link \
    "lib/rustlib/src/rust" library "$LIBRARY_SOURCE_TARGET"
materialize_source_link \
    "lib/rustlib/rustc-src/rust" compiler "$COMPILER_SOURCE_TARGET"

if [ -n "$RECEIPT_OUT" ]; then
    INSTALLED_LINK_INPUT_MANIFEST="$TMP_ROOT/materialized-installed-inputs.ndjson"
    INSTALLED_LIBRARY_TARGET=""
    INSTALLED_COMPILER_TARGET=""
    if [ -n "$LIBRARY_SOURCE_TARGET" ]; then
        INSTALLED_LIBRARY_TARGET="$INSTALLED_SYSROOT/lib/rustlib/src/rust"
    fi
    if [ -n "$COMPILER_SOURCE_TARGET" ]; then
        INSTALLED_COMPILER_TARGET="$INSTALLED_SYSROOT/lib/rustlib/rustc-src/rust"
    fi
    write_materialized_source_inputs_manifest \
        "$INSTALLED_LINK_INPUT_MANIFEST" \
        "$INSTALLED_LIBRARY_TARGET" \
        "$INSTALLED_COMPILER_TARGET" \
        "$LIBRARY_SOURCE_TARGET" \
        "$COMPILER_SOURCE_TARGET"
    cmp -s "$SOURCE_LINK_INPUT_MANIFEST" "$INSTALLED_LINK_INPUT_MANIFEST" \
        || fail "materialized installed source bytes differ from the bound source inputs"
fi

# The installed tree must contain no link that can resolve outside it.
"$PYTHON3_BIN" - "$INSTALLED_SYSROOT" <<'PY'
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve(strict=True)
for path in root.rglob("*"):
    if not path.is_symlink():
        continue
    rel = path.relative_to(root)
    try:
        resolved = path.resolve(strict=True)
    except (OSError, RuntimeError) as error:
        raise SystemExit(f"broken installed-sysroot symlink {rel}: {error}")
    try:
        resolved.relative_to(root)
    except ValueError:
        raise SystemExit(f"installed-sysroot symlink escapes immutable root: {rel} -> {resolved}")
PY

# Prove that no regular destination file is a hardlink to its source peer.
"$PYTHON3_BIN" - "$SOURCE_SYSROOT" "$INSTALLED_SYSROOT" <<'PY'
import os
import pathlib
import stat
import sys

source = pathlib.Path(sys.argv[1])
installed = pathlib.Path(sys.argv[2])
for destination in installed.rglob("*"):
    try:
        rel = destination.relative_to(installed)
        source_peer = source / rel
        dst_stat = destination.lstat()
        src_stat = source_peer.lstat()
    except FileNotFoundError:
        continue
    if stat.S_ISREG(dst_stat.st_mode) and stat.S_ISREG(src_stat.st_mode):
        if (dst_stat.st_dev, dst_stat.st_ino) == (src_stat.st_dev, src_stat.st_ino):
            raise SystemExit(f"destination is hardlinked to build sysroot: {rel}")
PY

MANIFEST_BEFORE="$TMP_ROOT/sysroot-before-read-only.ndjson"
MANIFEST_AFTER="$TMP_ROOT/sysroot-after-read-only.ndjson"
write_content_manifest "$INSTALLED_SYSROOT" "$MANIFEST_BEFORE" 1
chmod -R a-w "$INSTALLED_SYSROOT"
write_content_manifest "$INSTALLED_SYSROOT" "$MANIFEST_AFTER" 0
cmp -s "$MANIFEST_BEFORE" "$MANIFEST_AFTER" \
    || fail "sysroot content changed while it was made read-only"
"$PYTHON3_BIN" - "$INSTALLED_SYSROOT" <<'PY'
import pathlib
import stat
import sys

root = pathlib.Path(sys.argv[1])
for path in [root, *root.rglob("*")]:
    if path.is_symlink():
        continue
    if path.lstat().st_mode & (stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH):
        raise SystemExit(f"installed sysroot entry remains writable: {path.relative_to(root)}")
PY

BIN_DIR="$INSTALLED_SYSROOT/bin"
TRUST_TOOLCHAIN_PYTHON3="$PYTHON3_BIN"
. "$TRUST_ROOT/scripts/lib/trust_toolchain_surface.sh"

require_executable() {
    [ -x "$1" ] || fail "missing executable: $1"
}

require_directory() {
    [ -d "$1" ] || fail "missing directory: $1"
}

for tool in \
    trustc targo targo-trust trustd trustdoc trustfmt targo-fmt \
    tippy targo-tippy tippy-driver trust-analyzer
do
    require_executable "$BIN_DIR/$tool"
done
if forbidden_error="$(trust_toolchain_forbidden_entry_error "$BIN_DIR")"; then
    fail "$forbidden_error"
fi
if alias_error="$(trust_toolchain_alias_pair_error "$BIN_DIR" trustc rustc)"; then
    fail "invalid trustc/rustc same-sysroot alias: $alias_error"
fi
if alias_error="$(trust_toolchain_alias_pair_error "$BIN_DIR" targo cargo)"; then
    fail "invalid targo/cargo same-sysroot alias: $alias_error"
fi

TRUSTC_SYSROOT="$($BIN_DIR/trustc --print sysroot)"
[ "$(canonical_dir "$TRUSTC_SYSROOT")" = "$INSTALLED_SYSROOT" ] \
    || fail "relocated trustc reported a different sysroot: $TRUSTC_SYSROOT"
HOST_TRIPLE="$($BIN_DIR/trustc -vV | awk '/^host: / { print $2; exit }')"
[ -n "$HOST_TRIPLE" ] || fail "could not determine installed trustc host triple"
TARGET_LIBDIR="$($BIN_DIR/trustc --print target-libdir)"
require_directory "$TARGET_LIBDIR"
case "$(canonical_dir "$TARGET_LIBDIR")" in
    "$INSTALLED_SYSROOT"/*) ;;
    *) fail "target libdir escapes installed sysroot: $TARGET_LIBDIR" ;;
esac
set -- "$TARGET_LIBDIR"/libstd-*.rlib
[ -e "$1" ] || fail "installed target std is missing from $TARGET_LIBDIR"
require_directory "$INSTALLED_SYSROOT/lib/rustlib/src/rust/library"
[ -f "$INSTALLED_SYSROOT/lib/rustlib/src/rust/library/Cargo.toml" ] \
    || fail "installed trust-src payload is missing library/Cargo.toml"
require_directory "$INSTALLED_SYSROOT/lib/rustlib/rustc-src/rust/compiler/rustc_driver_impl"
ANALYZER_HELPER="$INSTALLED_SYSROOT/libexec/trust-analyzer-proc-macro-srv"
require_executable "$ANALYZER_HELPER"
for llvm_tool in llvm-ar llvm-nm llvm-objdump llvm-profdata; do
    require_executable "$INSTALLED_SYSROOT/lib/rustlib/$HOST_TRIPLE/bin/$llvm_tool"
done

# Copy the rustup executable and create only isolated, known rustup proxies.
HOST_RUSTUP_BIN="$($PYTHON3_BIN - "$HOST_RUSTUP_BIN" <<'PY'
import pathlib
import sys
print(pathlib.Path(sys.argv[1]).resolve(strict=True))
PY
)"
cp "$HOST_RUSTUP_BIN" "$PROXY_BIN/rustup"
chmod +x "$PROXY_BIN/rustup"
ln -s rustup "$PROXY_BIN/rustc"
ln -s rustup "$PROXY_BIN/cargo"

isolated_env() {
    env -i \
        HOME="$ISOLATED_HOME" \
        USER="trust-e2e" \
        LOGNAME="trust-e2e" \
        SHELL="/bin/sh" \
        PATH="$PROXY_BIN:$SYSTEM_PATH" \
        RUSTUP_HOME="$ISOLATED_RUSTUP_HOME" \
        CARGO_HOME="$ISOLATED_CARGO_HOME" \
        TMPDIR="$ISOLATED_TMP" \
        CARGO_TARGET_DIR="$ISOLATED_TARGET" \
        CARGO_TERM_COLOR=never \
        PYTHON3="$PYTHON3_BIN" \
        RUST_BACKTRACE=1 \
        RUST_ANALYZER_INTERNALS_DO_NOT_USE=1 \
        CI=1 \
        "$@"
}

isolated_rustup() {
    isolated_env "$PROXY_BIN/rustup" "$@"
}

run_tool() {
    tool="$1"
    shift
    isolated_rustup run "$TOOLCHAIN_NAME" "$tool" "$@"
}

for proxy in rustup rustc cargo; do
    proxy_path="$(isolated_env sh -c 'command -v "$1"' sh "$proxy")"
    [ "$proxy_path" = "$PROXY_BIN/$proxy" ] \
        || fail "isolated PATH selected an ambient $proxy proxy: $proxy_path"
done
if isolated_env sh -c 'command -v trustc >/dev/null 2>&1 || command -v targo >/dev/null 2>&1'; then
    fail "isolated PATH exposes an ambient Trust tool before rustup dispatch"
fi

isolated_env bash "$TRUST_ROOT/scripts/rustup-link-trust.sh" \
    --name "$TOOLCHAIN_NAME" --sysroot "$INSTALLED_SYSROOT"

LINKED_TRUSTC="$(isolated_rustup which --toolchain "$TOOLCHAIN_NAME" trustc)"
[ "$(canonical_dir "$(dirname "$LINKED_TRUSTC")/..")" = "$INSTALLED_SYSROOT" ] \
    || fail "isolated rustup resolved trustc outside the installed sysroot: $LINKED_TRUSTC"

if [ "$SET_DEFAULT" = "1" ]; then
    isolated_rustup default "$TOOLCHAIN_NAME"
    DEFAULT_SYSROOT="$(isolated_env "$PROXY_BIN/rustc" --print sysroot)"
    [ "$(canonical_dir "$DEFAULT_SYSROOT")" = "$INSTALLED_SYSROOT" ] \
        || fail "isolated default rustc proxy escaped installed sysroot: $DEFAULT_SYSROOT"
fi

run_tool trustc --version
run_tool targo --version
run_tool targo-trust --version
run_tool trustd --version
run_tool trustdoc --version
run_tool trustfmt --version
run_tool tippy --version
run_tool trust-analyzer --version
isolated_env "$ANALYZER_HELPER" --version

DOCTOR_JSON="$TMP_ROOT/doctor.json"
DOCTOR_STDERR="$TMP_ROOT/doctor.stderr"
doctor_status=0
run_tool targo trust doctor --format json >"$DOCTOR_JSON" 2>"$DOCTOR_STDERR" \
    || doctor_status=$?
[ "$doctor_status" -le 1 ] || fail "targo trust doctor failed: $(cat "$DOCTOR_STDERR")"
"$PYTHON3_BIN" - "$DOCTOR_JSON" "$INSTALLED_SYSROOT" <<'PY'
import json
import pathlib
import sys

report = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
root = pathlib.Path(sys.argv[2]).resolve()
compiler = report.get("compiler") or {}
if report.get("ready") is not True or report.get("status") != "ready":
    raise SystemExit(f"doctor did not report a release-ready setup: {report!r}")
if compiler.get("check_report_mode") != "native_compiler":
    raise SystemExit(f"doctor did not report native compiler mode: {compiler!r}")
if compiler.get("trust_verify") is not True or compiler.get("json_transport") is not True:
    raise SystemExit(f"doctor did not report native verification transport: {compiler!r}")
compiler_path = pathlib.Path(compiler.get("path", "")).resolve()
if compiler_path != root / "bin" / "trustc":
    raise SystemExit(f"doctor compiler escaped installed sysroot: {compiler_path}")
daily_driver = compiler.get("daily_driver") or {}
if daily_driver.get("ready") is not True:
    raise SystemExit(f"doctor did not report a complete daily-driver surface: {daily_driver!r}")
suites = {
    suite.get("name"): suite
    for suite in report.get("verifier_suites", [])
    if isinstance(suite, dict)
}
for name in ("trust-mc", "trust-wp", "trust-vc"):
    suite = suites.get(name)
    if not suite:
        raise SystemExit(f"doctor omitted verifier suite {name}")
    if suite.get("adapter_compiled") is not True:
        raise SystemExit(f"doctor reports {name} adapter is not compiled: {suite!r}")
    if suite.get("capability_available") is not True:
        raise SystemExit(f"doctor reports {name} capability is unavailable: {suite!r}")
PY

cp -R "$TRUST_ROOT/tests/fixtures/installed-serde-derive" "$WORKSPACE"
cd "$WORKSPACE"

run_tool targo fetch --locked

IMPLICIT_STDOUT="$TMP_ROOT/implicit-targo.stdout"
IMPLICIT_STDERR="$TMP_ROOT/implicit-targo.stderr"
if run_tool targo build --locked >"$IMPLICIT_STDOUT" 2>"$IMPLICIT_STDERR"; then
    fail "implicit branded 'targo build' compiled without an explicit verification lane"
fi
if ! grep -Eiq -- '--unverified|verification|verified' "$IMPLICIT_STDOUT" "$IMPLICIT_STDERR"; then
    fail "implicit targo rejection did not explain verification or --unverified"
fi

UNVERIFIED_STDOUT="$TMP_ROOT/unverified-targo.stdout"
UNVERIFIED_STDERR="$TMP_ROOT/unverified-targo.stderr"
run_tool targo --unverified build --locked >"$UNVERIFIED_STDOUT" 2>"$UNVERIFIED_STDERR"
if ! grep -q 'UNVERIFIED' "$UNVERIFIED_STDOUT" "$UNVERIFIED_STDERR"; then
    fail "explicit native build did not emit the mandatory UNVERIFIED banner"
fi
run_tool targo --unverified test --locked
RUN_STDOUT="$TMP_ROOT/native-run.stdout"
RUN_STDERR="$TMP_ROOT/native-run.stderr"
run_tool targo --unverified run --locked --quiet >"$RUN_STDOUT" 2>"$RUN_STDERR"
"$PYTHON3_BIN" - "$RUN_STDOUT" <<'PY'
import json
import pathlib
import sys

message = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
expected = {
    "sender": "Sanny",
    "body": "Trust installed-toolchain fixture",
    "priority": 2,
}
if message != expected:
    raise SystemExit(f"serde runtime round-trip mismatch: {message!r}")
PY
run_tool targo --unverified doc --locked --no-deps
run_tool targo fmt --check
run_tool tippy --no-deps -- -D warnings

VERIFIED_STDOUT="$TMP_ROOT/verified-proc-macro.stdout"
VERIFIED_STDERR="$TMP_ROOT/verified-proc-macro.stderr"
verified_status=0
run_tool targo trust check --format json >"$VERIFIED_STDOUT" 2>"$VERIFIED_STDERR" \
    || verified_status=$?
[ "$verified_status" -ne 0 ] \
    || fail "verified serde derive unexpectedly crossed the unaudited proc-macro boundary"
if ! grep -q 'no-proc-macro TCB boundary' "$VERIFIED_STDOUT" "$VERIFIED_STDERR"; then
    fail "verified serde rejection did not identify the no-proc-macro TCB boundary"
fi

run_tool trust-analyzer diagnostics "$WORKSPACE" \
    --proc-macro-srv "$ANALYZER_HELPER"
run_tool trust-analyzer analysis-stats "$WORKSPACE" \
    --with-deps \
    --proc-macro-srv "$ANALYZER_HELPER"

write_content_manifest "$INSTALLED_SYSROOT" "$TMP_ROOT/sysroot-final.ndjson" 0
cmp -s "$MANIFEST_AFTER" "$TMP_ROOT/sysroot-final.ndjson" \
    || fail "installed-toolchain behavior mutated the read-only sysroot"

if [ -n "$RECEIPT_OUT" ]; then
    SOURCE_MANIFEST_FINAL="$TMP_ROOT/source-sysroot-final.ndjson"
    SOURCE_LINK_INPUT_MANIFEST_FINAL="$TMP_ROOT/materialized-source-inputs-final.ndjson"
    SERDE_FIXTURE_MANIFEST_FINAL="$TMP_ROOT/serde-fixture-final.ndjson"
    require_source_target_unchanged \
        "lib/rustlib/src/rust" "$LIBRARY_SOURCE_TARGET"
    require_source_target_unchanged \
        "lib/rustlib/rustc-src/rust" "$COMPILER_SOURCE_TARGET"
    write_materialized_source_inputs_manifest \
        "$SOURCE_LINK_INPUT_MANIFEST_FINAL" \
        "$LIBRARY_SOURCE_TARGET" \
        "$COMPILER_SOURCE_TARGET" \
        "$LIBRARY_SOURCE_TARGET" \
        "$COMPILER_SOURCE_TARGET"
    cmp -s "$SOURCE_LINK_INPUT_MANIFEST" "$SOURCE_LINK_INPUT_MANIFEST_FINAL" \
        || fail "materialized source inputs changed during the installed-toolchain gate"
    write_content_manifest "$SOURCE_SYSROOT" "$SOURCE_MANIFEST_FINAL" 0
    cmp -s "$SOURCE_MANIFEST" "$SOURCE_MANIFEST_FINAL" \
        || fail "source sysroot changed during the installed-toolchain gate"
    write_content_manifest \
        "$TRUST_ROOT/tests/fixtures/installed-serde-derive" \
        "$SERDE_FIXTURE_MANIFEST_FINAL" \
        0
    cmp -s "$SERDE_FIXTURE_MANIFEST" "$SERDE_FIXTURE_MANIFEST_FINAL" \
        || fail "locked serde fixture changed during the installed-toolchain gate"
    [ "$(git -C "$TRUST_ROOT" rev-parse --verify HEAD)" = "$REPO_HEAD_START" ] \
        || fail "repository HEAD changed during the installed-toolchain gate"
    require_clean_repository_state \
        "repository or submodule state changed during the installed-toolchain gate"
    require_materialized_inputs_tracked
    [ "$(sha256_file "$SCRIPT_DIR/e2e_trust_local_rustup_install.sh")" = "$SCRIPT_SHA256_START" ] \
        || fail "installed-toolchain gate script changed during execution"
    [ "$(sha256_file "$RECEIPT_HELPER")" = "$RECEIPT_HELPER_SHA256_START" ] \
        || fail "receipt helper changed during execution"
    [ "$(sha256_file "$STAGE_PROVENANCE")" = "$PROVENANCE_SHA256_START" ] \
        || fail "Stage2 provenance changed during the installed-toolchain gate"
    "$PYTHON3_BIN" "$RECEIPT_HELPER" validate-stage \
        --provenance "$STAGE_PROVENANCE" \
        --repository-head "$REPO_HEAD_START" \
        --trustc "$SOURCE_SYSROOT/bin/trustc" >/dev/null

    INSTALLED_VERBOSE_FILE="$TMP_ROOT/installed-trustc-vv.txt"
    "$BIN_DIR/trustc" -vV >"$INSTALLED_VERBOSE_FILE"
    RECEIPT_CANDIDATE="$TMP_ROOT/installed-toolchain-receipt.json"
    "$PYTHON3_BIN" - \
        "$RECEIPT_CANDIDATE" \
        "$TRUST_ROOT" \
        "$REPO_HEAD_START" \
        "$SCRIPT_SHA256_START" \
        "$RECEIPT_HELPER_SHA256_START" \
        "$STAGE_PROVENANCE" \
        "$PROVENANCE_SHA256_START" \
        "$SOURCE_SYSROOT" \
        "$SOURCE_MANIFEST" \
        "$SOURCE_COPY_CONTENT_MANIFEST" \
        "$COPIED_SYSROOT_CONTENT_MANIFEST" \
        "$SOURCE_LINK_INPUT_MANIFEST" \
        "$INSTALLED_SYSROOT" \
        "$MANIFEST_AFTER" \
        "$BIN_DIR/trustc" \
        "$INSTALLED_VERBOSE_FILE" \
        "$DOCTOR_JSON" \
        "$TRUST_ROOT/tests/fixtures/installed-serde-derive" \
        "$SERDE_FIXTURE_MANIFEST" \
        "$RUN_STDOUT" \
        "$SET_DEFAULT" <<'PY'
import datetime
import hashlib
import importlib.util
import json
import pathlib
import sys

(
    candidate_path,
    root_value,
    repository_head,
    script_sha256,
    helper_sha256,
    provenance_value,
    provenance_sha256,
    source_root_value,
    source_manifest_value,
    source_copy_content_manifest_value,
    copied_sysroot_content_manifest_value,
    source_link_input_manifest_value,
    installed_root_value,
    installed_manifest_value,
    trustc_value,
    trustc_verbose_value,
    doctor_value,
    fixture_root_value,
    fixture_manifest_value,
    runtime_value,
    set_default_value,
) = sys.argv[1:]

def sha256(path):
    digest = hashlib.sha256()
    with pathlib.Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

root = pathlib.Path(root_value).resolve()
receipt_helper_path = root / "scripts" / "lib" / "trust_e2e_receipt.py"
receipt_helper_spec = importlib.util.spec_from_file_location(
    "trust_e2e_receipt_candidate_builder", receipt_helper_path
)
if receipt_helper_spec is None or receipt_helper_spec.loader is None:
    raise SystemExit(f"could not load receipt helper: {receipt_helper_path}")
receipt_helper = importlib.util.module_from_spec(receipt_helper_spec)
receipt_helper_spec.loader.exec_module(receipt_helper)
provenance_path = pathlib.Path(provenance_value).resolve()
source_root = pathlib.Path(source_root_value).resolve()
installed_root = pathlib.Path(installed_root_value).resolve()
trustc_path = pathlib.Path(trustc_value).resolve()
fixture_root = pathlib.Path(fixture_root_value).resolve()
lock_path = fixture_root / "Cargo.lock"
provenance = json.loads(provenance_path.read_text(encoding="utf-8"))
doctor = json.loads(pathlib.Path(doctor_value).read_text(encoding="utf-8"))
runtime = json.loads(pathlib.Path(runtime_value).read_text(encoding="utf-8"))
trustc_sha256 = sha256(trustc_path)
source_trustc_sha256 = sha256(source_root / "bin" / "trustc")
recorded_trustc_sha256 = (provenance.get("compiler") or {}).get("compiler_sha256")
if recorded_trustc_sha256 != source_trustc_sha256:
    raise SystemExit("Stage2 provenance compiler digest does not match source trustc")
if trustc_sha256 != source_trustc_sha256:
    raise SystemExit("installed trustc digest does not match the selected source compiler")
if (provenance.get("compiler") or {}).get("source_commit") != repository_head:
    raise SystemExit("Stage2 provenance source commit changed during the gate")

document = {
    "schema": "trust.e2e.installed-toolchain-receipt.v1",
    "status": "passed",
    "finished_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source": {
        "repository_root": str(root),
        "repository_head": repository_head,
        "repository_clean_before_and_after": True,
        "gate_script": "tests/e2e_trust_local_rustup_install.sh",
        "gate_script_sha256": script_sha256,
        "receipt_helper": "scripts/lib/trust_e2e_receipt.py",
        "receipt_helper_sha256": helper_sha256,
        "inputs_stable_before_and_after": True,
    },
    "stage_provenance": {
        "path": str(provenance_path),
        "sha256": provenance_sha256,
        "schema": provenance.get("schema"),
        "status": provenance.get("status"),
        "stage": provenance.get("stage"),
        "host": provenance.get("host"),
        "source_commit": (provenance.get("compiler") or {}).get("source_commit"),
        "verified_before_and_after": True,
    },
    "sysroots": {
        "source": {
            "path": str(source_root),
            "manifest_schema": "trust.filesystem-content-manifest.ndjson.v1",
            "manifest_scope": "entry-kind-mode-symlink-target-file-bytes;excludes-owner-xattrs-flags-hardlink-topology",
            "manifest_sha256": sha256(source_manifest_value),
            "stable_before_and_after": True,
            "copy_content_manifest_schema": "trust.filesystem-content-manifest.ndjson.v1",
            "copy_content_manifest_scope": "entry-kind-symlink-target-file-bytes;excludes-mode-owner-xattrs-flags-hardlink-topology",
            "copy_content_manifest_sha256": sha256(source_copy_content_manifest_value),
            "copied_sysroot_content_manifest_sha256": sha256(copied_sysroot_content_manifest_value),
            "copied_sysroot_matches_source_content_manifest": True,
            "materialized_link_inputs_manifest_schema": "trust.materialized-source-input-manifest.ndjson.v1",
            "materialized_link_inputs_manifest_scope": "entry-kind-symlink-target-file-bytes;excludes-mode-owner-xattrs-flags-hardlink-topology",
            "materialized_link_inputs_manifest_sha256": sha256(source_link_input_manifest_value),
            "materialized_link_inputs_stable_before_and_after": True,
            "materialized_link_input_content_copied_exactly": True,
            "materialized_link_input_files_git_tracked_only": True,
        },
        "installed": {
            "path_scope": "ephemeral-local-install",
            "path": str(installed_root),
            "read_only": True,
            "no_escaping_symlinks": True,
            "no_source_hardlinks": True,
            "manifest_schema": "trust.filesystem-content-manifest.ndjson.v1",
            "manifest_scope": "entry-kind-mode-symlink-target-file-bytes;excludes-owner-xattrs-flags-hardlink-topology",
            "manifest_sha256": sha256(installed_manifest_value),
            "unchanged_after_behavior_checks": True,
        },
    },
    "compiler": {
        "path": str(trustc_path),
        "sha256": trustc_sha256,
        "source_sha256": source_trustc_sha256,
        "verbose": pathlib.Path(trustc_verbose_value).read_text(encoding="utf-8").strip(),
        "provenance_digest_match": True,
    },
    "doctor": {
        "report_sha256": receipt_helper.canonical_embedded_json_sha256(doctor),
        "report": doctor,
        "ready": True,
        "daily_driver_ready": True,
        "required_verifier_suites": ["trust-mc", "trust-wp", "trust-vc"],
    },
    "serde_fixture": {
        "path": str(fixture_root),
        "tree_manifest_sha256": sha256(fixture_manifest_value),
        "cargo_lock_sha256": sha256(lock_path),
        "runtime_output_sha256": receipt_helper.canonical_embedded_json_sha256(runtime),
        "runtime_output": runtime,
        "native_proc_macro_lane": "explicitly-unverified",
        "verified_proc_macro_boundary": "rejected-fail-closed",
    },
    "isolation": {
        "caller_rustup_unchanged": True,
        "caller_cargo_home_unchanged": True,
        "isolated_default_exercised": set_default_value == "1",
        "ambient_trust_tools_excluded": True,
    },
    "checks": {
        "canonical_tool_inventory": "passed",
        "compatibility_alias_inventory": "passed",
        "relocation": "passed",
        "immutable_sysroot": "passed",
        "isolated_rustup_link": "passed",
        "implicit_targo_rejected": "passed",
        "explicit_unverified_build_test_run_doc": "passed",
        "formatter_and_linter": "passed",
        "doctor_and_native_verifier_suites": "passed",
        "analyzer_and_proc_macro_helper": "passed",
        "serde_locked_runtime_round_trip": "passed",
        "verified_proc_macro_boundary": "passed",
    },
    "claim_scope": {
        "kind": "local-installed-toolchain-rehearsal",
        "public_rustup_channel": False,
        "notarized_macos_application": False,
        "ecosystem_superiority": False,
    },
}
pathlib.Path(candidate_path).write_text(
    json.dumps(
        document,
        allow_nan=False,
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
    ) + "\n",
    encoding="utf-8",
)
PY
    verify_repository_before_publication
fi

if [ -n "$RECEIPT_OUT" ]; then
    printf '\ninstalled Trust toolchain: VALIDATION COMPLETE (non-authoritative)\n'
    printf '  copied sysroot: %s\n' "$INSTALLED_SYSROOT"
    printf '  isolated rustup: %s\n' "$ISOLATED_RUSTUP_HOME"
    printf '  serde fixture: native build/test/run passed; verified proc macro rejected fail-closed\n'
    printf '  committing local diagnostic record as the final action: %s\n' "$RECEIPT_OUT"
    if [ "$KEEP_TEMP" = "1" ]; then
        validate_private_temp_root "$TMP_ROOT" "$TMP_ROOT_ID" \
            || fail "temporary root changed before retained-record publication"
        printf '  keeping isolated install gate directory: %s\n' "$TMP_ROOT"
        trap - EXIT HUP INT TERM
        exec "$PYTHON3_BIN" "$RECEIPT_HELPER" publish \
            --input "$RECEIPT_CANDIDATE" \
            --output "$RECEIPT_OUT" \
            --no-replace
    fi
    trap - EXIT HUP INT TERM
    exec "$PYTHON3_BIN" "$RECEIPT_HELPER" publish-after-cleanup \
        --input "$RECEIPT_CANDIDATE" \
        --output "$RECEIPT_OUT" \
        --cleanup-path "$TMP_ROOT" \
        --system-parent "$SYSTEM_TEMP_PARENT" \
        --expected-prefix "trust-installed-e2e." \
        --expected-identity "$TMP_ROOT_ID"
fi

printf '\ninstalled Trust toolchain: LOCAL DIAGNOSTIC PASS (non-authoritative)\n'
printf '  copied sysroot: %s\n' "$INSTALLED_SYSROOT"
printf '  isolated rustup: %s\n' "$ISOLATED_RUSTUP_HOME"
printf '  serde fixture: native build/test/run passed; verified proc macro rejected fail-closed\n'
