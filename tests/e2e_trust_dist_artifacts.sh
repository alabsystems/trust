#!/bin/bash
# Validate and install local Trust component archives, then exercise the
# read-only installed-toolchain behavior diagnostic against the assembled
# prefix. A pass is a local rehearsal result, not public-release evidence.

set -euo pipefail
umask 077

CALLER_DIR="$(pwd -P)"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
TRUST_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
DIST_DIR="${TRUST_E2E_DIST_DIR:-$TRUST_ROOT/build/dist}"
STAGE2_SYSROOT="${TRUST_E2E_STAGE2_SYSROOT:-}"
CHANNEL_MANIFEST="${TRUST_E2E_CHANNEL_MANIFEST:-}"
RECEIPT_OUT="${TRUST_E2E_RECEIPT:-}"
RECEIPT_HELPER="$TRUST_ROOT/scripts/lib/trust_e2e_receipt.py"
DIST_HOST="${TRUST_DIST_HOST:-}"
DIST_VERSION="${TRUST_DIST_VERSION:-}"
EXPECTED_COMPILER_HOST=""
EXPECTED_COMPILER_RELEASE=""
EXPECTED_COMPILER_COMMIT=""
PYTHON3_BIN="${TRUST_E2E_PYTHON3:-${PYTHON:-}}"
if [ -z "$PYTHON3_BIN" ]; then
    for python_name in python3.15 python3.14 python3.13 python3.12 python3.11 python3; do
        python_candidate="$(command -v "$python_name" 2>/dev/null || true)"
        [ -n "$python_candidate" ] || continue
        if "$python_candidate" -c 'import tomllib' >/dev/null 2>&1; then
            PYTHON3_BIN="$python_candidate"
            break
        fi
    done
fi
KEEP_TEMP=0

usage() {
    cat <<'EOF'
Usage: tests/e2e_trust_dist_artifacts.sh [options]

Options:
  --dist-dir PATH        Directory containing x.py dist component archives
  --stage2-sysroot PATH  Compiler used to bind archive host/version to the record
  --channel-manifest PATH
                         Generated Trust channel TOML (default: DIST_DIR/channel-rust-trust.toml)
  --receipt PATH         Publish a new local rehearsal record after a pass; PATH
                         is anchored to the invocation directory and must not
                         already exist
  --host TRIPLE          Explicit archive host (otherwise read from trustc -vV)
  --version VERSION      Explicit archive package version (for example 0.1.0-trust)
  --keep-temp            Preserve extracted and installed artifacts
  -h, --help             Show this help

This gate installs local archives into a temporary prefix. It never publishes
artifacts and never modifies the caller's rustup or Cargo homes.
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
        trust-dist-e2e.*) ;;
        *) printf 'FAIL: refusing temporary root with unexpected name: %s\n' "$canonical" >&2; return 1 ;;
    esac
    suffix="${name#trust-dist-e2e.}"
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

    normalized_receipt="$(
        "$PYTHON3_BIN" "$RECEIPT_HELPER" prepare-output \
            --output "$RECEIPT_OUT" \
            --caller-directory "$CALLER_DIR"
    )" || fail "receipt destination is not safe for a new rehearsal record"
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

verify_repository_before_publication() {
    [ "$(git -C "$TRUST_ROOT" rev-parse --verify HEAD)" = "$REPO_HEAD_START" ] \
        || fail "repository HEAD changed before publishing the dist-artifact record"
    require_clean_repository_state \
        "repository or submodule state changed before publishing the dist-artifact record"
    [ "$(sha256_file "$SCRIPT_DIR/e2e_trust_dist_artifacts.sh")" = "$SCRIPT_SHA256_START" ] \
        || fail "dist artifact gate script changed before publishing its record"
    [ "$(sha256_file "$RECEIPT_HELPER")" = "$RECEIPT_HELPER_SHA256_START" ] \
        || fail "receipt helper changed before publishing the dist-artifact record"
    [ "$(sha256_file "$CHANNEL_MANIFEST")" = "$CHANNEL_MANIFEST_SHA256_START" ] \
        || fail "channel manifest changed before publishing the dist-artifact record"
    [ "$(sha256_file "$STAGE_PROVENANCE")" = "$STAGE_PROVENANCE_SHA256_START" ] \
        || fail "Stage2 provenance changed before publishing the dist-artifact record"
    [ "$(sha256_file "$STAGE2_SYSROOT/bin/trustc")" = "$STAGE2_TRUSTC_SHA256_START" ] \
        || fail "selected Stage2 compiler changed before publishing the dist-artifact record"
    "$PYTHON3_BIN" "$RECEIPT_HELPER" validate-stage \
        --provenance "$STAGE_PROVENANCE" \
        --repository-head "$REPO_HEAD_START" \
        --trustc "$STAGE2_SYSROOT/bin/trustc" >/dev/null
}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --dist-dir)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--dist-dir requires a path"
            DIST_DIR="$1"
            ;;
        --dist-dir=*) DIST_DIR="${1#*=}" ;;
        --stage2-sysroot)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--stage2-sysroot requires a path"
            STAGE2_SYSROOT="$1"
            ;;
        --stage2-sysroot=*) STAGE2_SYSROOT="${1#*=}" ;;
        --channel-manifest)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--channel-manifest requires a path"
            CHANNEL_MANIFEST="$1"
            ;;
        --channel-manifest=*)
            CHANNEL_MANIFEST="${1#*=}"
            [ -n "$CHANNEL_MANIFEST" ] || fail "--channel-manifest requires a path"
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
        --host)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--host requires a triple"
            DIST_HOST="$1"
            ;;
        --host=*) DIST_HOST="${1#*=}" ;;
        --version)
            shift
            [ "$#" -gt 0 ] && [ -n "$1" ] || fail "--version requires a value"
            DIST_VERSION="$1"
            ;;
        --version=*) DIST_VERSION="${1#*=}" ;;
        --keep-temp) KEEP_TEMP=1 ;;
        -h|--help)
            usage
            exit 0
            ;;
        *) fail "unknown argument: $1" ;;
    esac
    shift
done

[ -n "$PYTHON3_BIN" ] || skip_or_fail "Python 3.11+ with tomllib is required"
[ -f "$RECEIPT_HELPER" ] || fail "receipt helper is missing: $RECEIPT_HELPER"
[ -z "$RECEIPT_OUT" ] || prepare_receipt_output
"$PYTHON3_BIN" -c 'import tomllib' >/dev/null 2>&1 \
    || skip_or_fail "configured TRUST_E2E_PYTHON3 lacks tomllib (Python 3.11+ required)"
[ -d "$DIST_DIR" ] || skip_or_fail "dist directory is missing: $DIST_DIR"
DIST_DIR="$(cd "$DIST_DIR" && pwd -P)"
if [ -z "$CHANNEL_MANIFEST" ]; then
    CHANNEL_MANIFEST="$DIST_DIR/channel-rust-trust.toml"
fi
[ -f "$CHANNEL_MANIFEST" ] || skip_or_fail "channel manifest is missing: $CHANNEL_MANIFEST"
CHANNEL_MANIFEST="$($PYTHON3_BIN - "$CHANNEL_MANIFEST" <<'PY'
import pathlib
import sys
print(pathlib.Path(sys.argv[1]).resolve(strict=True))
PY
)"

if [ -z "$STAGE2_SYSROOT" ]; then
    for candidate in \
        "$TRUST_ROOT/build/host/stage2" \
        "$TRUST_ROOT/build/aarch64-apple-darwin/stage2" \
        "$TRUST_ROOT/build/x86_64-apple-darwin/stage2" \
        "$TRUST_ROOT/build/aarch64-unknown-linux-gnu/stage2" \
        "$TRUST_ROOT/build/x86_64-unknown-linux-gnu/stage2"
    do
        if [ -x "$candidate/bin/trustc" ]; then
            STAGE2_SYSROOT="$candidate"
            break
        fi
    done
fi

if [ -n "$STAGE2_SYSROOT" ] && [ -x "$STAGE2_SYSROOT/bin/trustc" ]; then
    STAGE2_SYSROOT="$(cd "$STAGE2_SYSROOT" && pwd -P)"
    TRUSTC_VERBOSE="$($STAGE2_SYSROOT/bin/trustc -vV)"
    EXPECTED_COMPILER_HOST="$(printf '%s\n' "$TRUSTC_VERBOSE" | awk '/^host: / { print $2; exit }')"
    EXPECTED_COMPILER_RELEASE="$(printf '%s\n' "$TRUSTC_VERBOSE" | awk '/^release: / { print $2; exit }')"
    EXPECTED_COMPILER_COMMIT="$(printf '%s\n' "$TRUSTC_VERBOSE" | awk '/^commit-hash: / { print $2; exit }')"
    if [ -z "$DIST_HOST" ]; then
        DIST_HOST="$EXPECTED_COMPILER_HOST"
    fi
fi
if [ -n "$RECEIPT_OUT" ] && { [ -z "$STAGE2_SYSROOT" ] || [ ! -x "$STAGE2_SYSROOT/bin/trustc" ]; }; then
    fail "receipt mode requires a complete --stage2-sysroot"
fi

if [ -z "$DIST_VERSION" ]; then
    [ -f "$TRUST_ROOT/src/version" ] \
        || fail "cannot derive archive package version; pass --version"
    BASE_VERSION="$(sed -n '1p' "$TRUST_ROOT/src/version")"
    [ -n "$BASE_VERSION" ] || fail "src/version is empty; pass --version"
    CHANNEL="$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' "$TRUST_ROOT/bootstrap.toml" | head -1)"
    case "$CHANNEL" in
        trust) DIST_VERSION="$BASE_VERSION-trust" ;;
        stable) DIST_VERSION="$BASE_VERSION" ;;
        beta|nightly) DIST_VERSION="$CHANNEL" ;;
        *) DIST_VERSION="$BASE_VERSION-dev" ;;
    esac
fi
[ -n "$DIST_HOST" ] || fail "could not determine dist host"
[ -n "$DIST_VERSION" ] || fail "could not determine dist package version"

REPO_HEAD_START=""
SCRIPT_SHA256_START=""
RECEIPT_HELPER_SHA256_START=""
CHANNEL_MANIFEST_SHA256_START=""
STAGE_PROVENANCE=""
STAGE_PROVENANCE_SHA256_START=""
STAGE2_TRUSTC_SHA256_START=""
if [ -n "$RECEIPT_OUT" ]; then
    command -v git >/dev/null 2>&1 || fail "git is required in receipt mode"
    REPO_HEAD_START="$(git -C "$TRUST_ROOT" rev-parse --verify HEAD)"
    [ -n "$REPO_HEAD_START" ] || fail "could not resolve repository HEAD"
    require_clean_repository_state \
        "receipt mode requires a clean repository and clean submodules"
    STAGE_PROVENANCE="$STAGE2_SYSROOT/tool-provenance.json"
    [ -f "$STAGE_PROVENANCE" ] \
        || fail "Stage2 provenance is missing: $STAGE_PROVENANCE"
    SCRIPT_SHA256_START="$(sha256_file "$SCRIPT_DIR/e2e_trust_dist_artifacts.sh")"
    RECEIPT_HELPER_SHA256_START="$(sha256_file "$RECEIPT_HELPER")"
    CHANNEL_MANIFEST_SHA256_START="$(sha256_file "$CHANNEL_MANIFEST")"
    STAGE_PROVENANCE_SHA256_START="$(sha256_file "$STAGE_PROVENANCE")"
    STAGE2_TRUSTC_SHA256_START="$(sha256_file "$STAGE2_SYSROOT/bin/trustc")"
    "$PYTHON3_BIN" "$RECEIPT_HELPER" validate-stage \
        --provenance "$STAGE_PROVENANCE" \
        --repository-head "$REPO_HEAD_START" \
        --trustc "$STAGE2_SYSROOT/bin/trustc" >/dev/null
fi

SYSTEM_TEMP_PARENT="$(canonical_temp_directory /tmp)" \
    || fail "fixed system temporary parent is unavailable: /tmp"
RAW_TMP_ROOT="$(/usr/bin/mktemp -d /tmp/trust-dist-e2e.XXXXXX)" \
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
        printf 'kept dist gate directory: %s\n' "$TMP_ROOT" >&2
        exit "$original_status"
    fi
    "$PYTHON3_BIN" "$RECEIPT_HELPER" remove-private-temp \
        --path "$TMP_ROOT" \
        --system-parent "$SYSTEM_TEMP_PARENT" \
        --expected-prefix "trust-dist-e2e." \
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

PREFIX="$TMP_ROOT/prefix"
EXTRACT_BASE="$TMP_ROOT/extracted"
ARCHIVE_MANIFEST="$TMP_ROOT/archive-manifest.ndjson"
mkdir -p "$PREFIX" "$EXTRACT_BASE"
: >"$ARCHIVE_MANIFEST"

archive_basename() {
    component="$1"
    case "$component" in
        trust-src)
            printf '%s-%s\n' "$component" "$DIST_VERSION"
            ;;
        *)
            printf '%s-%s-%s\n' "$component" "$DIST_VERSION" "$DIST_HOST"
            ;;
    esac
}

select_and_validate_archive() {
    component="$1"
    package="$(archive_basename "$component")"
    selected=""
    found=0
    for extension in tar.xz tar.gz; do
        archive="$DIST_DIR/$package.$extension"
        [ -f "$archive" ] || continue
        found=$((found + 1))
        [ -n "$selected" ] || selected="$archive"
        root_file="$TMP_ROOT/$component-$extension.root"
        "$PYTHON3_BIN" - "$archive" "$component" >"$root_file" <<'PY'
import pathlib
import stat
import sys
import tarfile

archive = pathlib.Path(sys.argv[1])
component = sys.argv[2]
roots = set()
install_member = None
seen_paths = set()
seen_casefolded_paths = set()
targo_trust_binary = False
targo_trust_daemon = False
targo_trust_docs = False

with tarfile.open(archive, "r:*") as package:
    members = package.getmembers()
    if not members:
        raise SystemExit(f"empty dist archive: {archive}")
    for member in members:
        raw = member.name.replace("\\", "/")
        path = pathlib.PurePosixPath(raw)
        if path.is_absolute() or ".." in path.parts or not path.parts:
            raise SystemExit(f"unsafe archive member in {archive.name}: {member.name}")
        normalized = path.as_posix()
        if normalized in seen_paths or normalized.casefold() in seen_casefolded_paths:
            raise SystemExit(f"duplicate/case-colliding archive member in {archive.name}: {member.name}")
        seen_paths.add(normalized)
        seen_casefolded_paths.add(normalized.casefold())
        roots.add(path.parts[0])
        if member.issym() or member.islnk():
            raise SystemExit(f"link entry is forbidden in dist archive {archive.name}: {member.name}")
        if not (member.isdir() or member.isfile()):
            raise SystemExit(f"special entry is forbidden in dist archive {archive.name}: {member.name}")
        if len(path.parts) == 2 and path.parts[1] == "install.sh":
            install_member = member

        if component == "targo-trust" and member.isfile():
            if len(path.parts) >= 2 and path.parts[-2:] == ("bin", "targo-trust"):
                targo_trust_binary = True
            if len(path.parts) >= 2 and path.parts[-2:] == ("bin", "trustd"):
                targo_trust_daemon = True
            if "share" in path.parts and "doc" in path.parts and "targo-trust" in path.parts:
                targo_trust_docs = True

        if component == "trust-src":
            lowered = tuple(part.lower() for part in path.parts)
            if ".git" in lowered or ".gitmodules" in lowered:
                raise SystemExit(f"source archive contains VCS metadata: {member.name}")
            if "first-party" in path.parts and path.name == "Cargo.lock":
                raise SystemExit(f"source archive contains a first-party lockfile: {member.name}")
            for index, part in enumerate(path.parts[:-1]):
                if part == "targo-trust" and path.parts[index + 1] == "target":
                    raise SystemExit(f"source archive contains targo-trust build output: {member.name}")

if len(roots) != 1:
    raise SystemExit(f"dist archive must have one top-level directory: {archive.name}: {sorted(roots)}")
root = next(iter(roots))
if install_member is None or pathlib.PurePosixPath(install_member.name).parts[0] != root:
    raise SystemExit(f"dist archive has no top-level install.sh: {archive.name}")
if install_member.mode & 0o111 == 0:
    raise SystemExit(f"dist archive install.sh is not executable: {archive.name}")
if component == "targo-trust" and not targo_trust_binary:
    raise SystemExit(f"targo-trust archive omits bin/targo-trust: {archive.name}")
if component == "targo-trust" and not targo_trust_daemon:
    raise SystemExit(f"targo-trust archive omits bin/trustd: {archive.name}")
if component == "targo-trust" and not targo_trust_docs:
    raise SystemExit(f"targo-trust archive omits share/doc/targo-trust: {archive.name}")
print(root)
PY
        digest="$($PYTHON3_BIN - "$archive" <<'PY'
import hashlib
import pathlib
import sys

digest = hashlib.sha256()
with pathlib.Path(sys.argv[1]).open("rb") as handle:
    for chunk in iter(lambda: handle.read(1024 * 1024), b""):
        digest.update(chunk)
print(digest.hexdigest())
PY
)"
        printf '%s\n' "$digest" >"$TMP_ROOT/$component-$extension.sha256"
        archive_root="$(cat "$root_file")"
        selected_flag=0
        [ "$archive" = "$selected" ] && selected_flag=1
        "$PYTHON3_BIN" - \
            "$ARCHIVE_MANIFEST" \
            "$component" \
            "$archive" \
            "$extension" \
            "$archive_root" \
            "$digest" \
            "$selected_flag" <<'PY'
import json
import pathlib
import sys

manifest = pathlib.Path(sys.argv[1])
archive = pathlib.Path(sys.argv[3]).resolve()
row = {
    "component": sys.argv[2],
    "archive_path": str(archive),
    "archive_filename": archive.name,
    "size_bytes": archive.stat().st_size,
    "extension": sys.argv[4],
    "archive_root": sys.argv[5],
    "sha256": sys.argv[6],
    "selected": sys.argv[7] == "1",
}
with manifest.open("a", encoding="utf-8") as handle:
    handle.write(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n")
PY
    done
    [ "$found" -gt 0 ] || fail "missing dist archive: $DIST_DIR/$package.tar.{xz,gz}"
    printf '%s\n' "$selected"
}

install_archive() {
    component="$1"
    archive="$2"
    extension="${archive##*.tar.}"
    root_file="$TMP_ROOT/$component-tar.$extension.root"
    [ -f "$root_file" ] || fail "validated archive root is missing for $archive"
    package_root="$(cat "$root_file")"
    expected_digest="$(cat "$TMP_ROOT/$component-tar.$extension.sha256")"
    actual_digest="$($PYTHON3_BIN - "$archive" <<'PY'
import hashlib
import pathlib
import sys

digest = hashlib.sha256()
with pathlib.Path(sys.argv[1]).open("rb") as handle:
    for chunk in iter(lambda: handle.read(1024 * 1024), b""):
        digest.update(chunk)
print(digest.hexdigest())
PY
)"
    [ "$actual_digest" = "$expected_digest" ] \
        || fail "dist archive changed between validation and extraction: $archive"
    extract_dir="$EXTRACT_BASE/$component"
    mkdir -p "$extract_dir"
    tar -xf "$archive" -C "$extract_dir"
    installer="$extract_dir/$package_root/install.sh"
    [ -x "$installer" ] || fail "extracted installer is missing: $installer"
    "$installer" --prefix="$PREFIX" --disable-ldconfig
}

UMBRELLA_ARCHIVE="$(select_and_validate_archive trust)"
printf 'validated umbrella trust archive: %s\n' "${UMBRELLA_ARCHIVE##*/}"

INSTALL_COMPONENTS='trustc trustc-dev trust-std targo targo-trust trust-docs trustfmt tippy trust-analyzer trust-src trust-llvm-tools'
for component in $INSTALL_COMPONENTS; do
    archive="$(select_and_validate_archive "$component")"
    printf 'installing %s from %s\n' "$component" "${archive##*/}"
    install_archive "$component" "$archive"
done

CHANNEL_BINDING="$TMP_ROOT/channel-manifest-binding.json"
"$PYTHON3_BIN" "$RECEIPT_HELPER" validate-channel \
    --manifest "$CHANNEL_MANIFEST" \
    --archive-manifest "$ARCHIVE_MANIFEST" \
    --dist-dir "$DIST_DIR" \
    --host "$DIST_HOST" >"$CHANNEL_BINDING"

[ -f "$PREFIX/share/doc/rust/html/robots.txt" ] \
    || fail "installed trust-docs component is missing share/doc/rust/html/robots.txt"

# Bind the assembled compiler identity back to the reviewed stage2 used to
# select the artifacts. This prevents a same-directory archive mix-up.
INSTALLED_VERBOSE="$($PREFIX/bin/trustc -vV)"
INSTALLED_HOST="$(printf '%s\n' "$INSTALLED_VERBOSE" | awk '/^host: / { print $2; exit }')"
INSTALLED_RELEASE="$(printf '%s\n' "$INSTALLED_VERBOSE" | awk '/^release: / { print $2; exit }')"
INSTALLED_COMMIT="$(printf '%s\n' "$INSTALLED_VERBOSE" | awk '/^commit-hash: / { print $2; exit }')"
[ "$INSTALLED_HOST" = "$DIST_HOST" ] \
    || fail "installed dist host mismatch: expected $DIST_HOST, got $INSTALLED_HOST"
if [ -n "$EXPECTED_COMPILER_HOST" ]; then
    [ "$INSTALLED_HOST" = "$EXPECTED_COMPILER_HOST" ] \
        || fail "installed compiler host differs from stage2: expected $EXPECTED_COMPILER_HOST, got $INSTALLED_HOST"
    [ "$INSTALLED_RELEASE" = "$EXPECTED_COMPILER_RELEASE" ] \
        || fail "installed compiler release differs from stage2: expected $EXPECTED_COMPILER_RELEASE, got $INSTALLED_RELEASE"
    [ "$INSTALLED_COMMIT" = "$EXPECTED_COMPILER_COMMIT" ] \
        || fail "installed compiler commit differs from stage2: expected $EXPECTED_COMPILER_COMMIT, got $INSTALLED_COMMIT"
fi

CHILD_RECEIPT=""
if [ -n "$RECEIPT_OUT" ]; then
    CHILD_RECEIPT="$TMP_ROOT/installed-toolchain-receipt.json"
    bash "$SCRIPT_DIR/e2e_trust_installed_toolchain.sh" \
        --source-sysroot "$PREFIX" \
        --stage-provenance "$STAGE_PROVENANCE" \
        --receipt "$CHILD_RECEIPT" \
        --set-default
else
    bash "$SCRIPT_DIR/e2e_trust_installed_toolchain.sh" \
        --source-sysroot "$PREFIX" \
        --set-default
fi

# Re-read the manifest and every archive after installation and the child
# behavior gate. A validated-before-extraction-only list would not bind the
# actual inputs used by a long-running rehearsal.
CHANNEL_BINDING_FINAL="$TMP_ROOT/channel-manifest-binding-final.json"
"$PYTHON3_BIN" "$RECEIPT_HELPER" validate-channel \
    --manifest "$CHANNEL_MANIFEST" \
    --archive-manifest "$ARCHIVE_MANIFEST" \
    --dist-dir "$DIST_DIR" \
    --host "$DIST_HOST" >"$CHANNEL_BINDING_FINAL"
cmp -s "$CHANNEL_BINDING" "$CHANNEL_BINDING_FINAL" \
    || fail "channel manifest or dist archives changed during installation"

if [ -n "$RECEIPT_OUT" ]; then
    [ "$(git -C "$TRUST_ROOT" rev-parse --verify HEAD)" = "$REPO_HEAD_START" ] \
        || fail "repository HEAD changed during the dist artifact gate"
    require_clean_repository_state \
        "repository or submodule state changed during the dist artifact gate"
    [ "$(sha256_file "$SCRIPT_DIR/e2e_trust_dist_artifacts.sh")" = "$SCRIPT_SHA256_START" ] \
        || fail "dist artifact gate script changed during execution"
    [ "$(sha256_file "$RECEIPT_HELPER")" = "$RECEIPT_HELPER_SHA256_START" ] \
        || fail "receipt helper changed during execution"
    [ "$(sha256_file "$CHANNEL_MANIFEST")" = "$CHANNEL_MANIFEST_SHA256_START" ] \
        || fail "channel manifest changed during the dist artifact gate"
    [ "$(sha256_file "$STAGE_PROVENANCE")" = "$STAGE_PROVENANCE_SHA256_START" ] \
        || fail "Stage2 provenance changed during the dist artifact gate"
    [ "$(sha256_file "$STAGE2_SYSROOT/bin/trustc")" = "$STAGE2_TRUSTC_SHA256_START" ] \
        || fail "selected Stage2 compiler changed during the dist artifact gate"
    "$PYTHON3_BIN" "$RECEIPT_HELPER" validate-stage \
        --provenance "$STAGE_PROVENANCE" \
        --repository-head "$REPO_HEAD_START" \
        --trustc "$STAGE2_SYSROOT/bin/trustc" >/dev/null
    [ -f "$CHILD_RECEIPT" ] || fail "installed-toolchain child receipt is missing"

    STAGE2_VERBOSE_FILE="$TMP_ROOT/stage2-trustc-vv.txt"
    INSTALLED_VERBOSE_FILE="$TMP_ROOT/dist-installed-trustc-vv.txt"
    printf '%s\n' "$TRUSTC_VERBOSE" >"$STAGE2_VERBOSE_FILE"
    printf '%s\n' "$INSTALLED_VERBOSE" >"$INSTALLED_VERBOSE_FILE"
    RECEIPT_CANDIDATE="$TMP_ROOT/dist-artifact-receipt.json"
    "$PYTHON3_BIN" - \
        "$RECEIPT_CANDIDATE" \
        "$TRUST_ROOT" \
        "$REPO_HEAD_START" \
        "$SCRIPT_SHA256_START" \
        "$RECEIPT_HELPER_SHA256_START" \
        "$DIST_DIR" \
        "$DIST_HOST" \
        "$DIST_VERSION" \
        "$ARCHIVE_MANIFEST" \
        "$CHANNEL_BINDING_FINAL" \
        "$STAGE2_SYSROOT" \
        "$STAGE2_VERBOSE_FILE" \
        "$STAGE2_TRUSTC_SHA256_START" \
        "$STAGE_PROVENANCE" \
        "$STAGE_PROVENANCE_SHA256_START" \
        "$PREFIX" \
        "$INSTALLED_VERBOSE_FILE" \
        "$CHILD_RECEIPT" <<'PY'
import datetime
import hashlib
import json
import pathlib
import sys

(
    candidate_value,
    root_value,
    repository_head,
    script_sha256,
    helper_sha256,
    dist_dir_value,
    host,
    version,
    archive_manifest_value,
    channel_binding_value,
    stage2_root_value,
    stage2_verbose_value,
    stage2_trustc_sha256,
    provenance_value,
    provenance_sha256,
    prefix_value,
    installed_verbose_value,
    child_receipt_value,
) = sys.argv[1:]

def sha256(path):
    digest = hashlib.sha256()
    with pathlib.Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

archive_manifest_path = pathlib.Path(archive_manifest_value)
archive_rows = [
    json.loads(line)
    for line in archive_manifest_path.read_text(encoding="utf-8").splitlines()
    if line.strip()
]
channel_binding = json.loads(pathlib.Path(channel_binding_value).read_text(encoding="utf-8"))
provenance_path = pathlib.Path(provenance_value).resolve()
provenance = json.loads(provenance_path.read_text(encoding="utf-8"))
child_path = pathlib.Path(child_receipt_value)
child_receipt = json.loads(child_path.read_text(encoding="utf-8"))
if child_receipt.get("schema") != "trust.e2e.installed-toolchain-receipt.v1":
    raise SystemExit("installed-toolchain child receipt has the wrong schema")
if child_receipt.get("status") != "passed":
    raise SystemExit("installed-toolchain child receipt did not pass")
if (child_receipt.get("source") or {}).get("repository_head") != repository_head:
    raise SystemExit("installed-toolchain child receipt uses another source commit")
if (child_receipt.get("stage_provenance") or {}).get("sha256") != provenance_sha256:
    raise SystemExit("installed-toolchain child receipt uses another Stage2 provenance receipt")
if provenance.get("schema") != "trust.stage-tool-provenance.v2":
    raise SystemExit("Stage2 provenance has the wrong schema")
if provenance.get("status") not in {"internal-release-ready", "release-ready"}:
    raise SystemExit(f"Stage2 provenance is not release-ready: {provenance.get('status')!r}")
if (provenance.get("compiler") or {}).get("source_commit") != repository_head:
    raise SystemExit("Stage2 provenance source commit does not match repository HEAD")
if (provenance.get("compiler") or {}).get("compiler_sha256") != stage2_trustc_sha256:
    raise SystemExit("Stage2 provenance compiler digest does not match selected trustc")

document = {
    "schema": "trust.e2e.dist-artifact-receipt.v1",
    "status": "passed",
    "finished_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source": {
        "repository_root": str(pathlib.Path(root_value).resolve()),
        "repository_head": repository_head,
        "repository_clean_before_and_after": True,
        "gate_script": "tests/e2e_trust_dist_artifacts.sh",
        "gate_script_sha256": script_sha256,
        "receipt_helper": "scripts/lib/trust_e2e_receipt.py",
        "receipt_helper_sha256": helper_sha256,
        "inputs_stable_before_and_after": True,
    },
    "compiler": {
        "stage2_sysroot": str(pathlib.Path(stage2_root_value).resolve()),
        "trustc_sha256": stage2_trustc_sha256,
        "verbose": pathlib.Path(stage2_verbose_value).read_text(encoding="utf-8").strip(),
        "installed_prefix": str(pathlib.Path(prefix_value).resolve()),
        "installed_verbose": pathlib.Path(installed_verbose_value).read_text(encoding="utf-8").strip(),
        "identity_matches_installed_archives": True,
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
    "distribution": {
        "directory": str(pathlib.Path(dist_dir_value).resolve()),
        "host": host,
        "version": version,
        "archive_manifest_schema": "trust.dist-archive-manifest.ndjson.v1",
        "archive_manifest_sha256": sha256(archive_manifest_path),
        "archives": archive_rows,
        "archives_rehashed_after_install": True,
        "umbrella_trust_archive_required": True,
    },
    "channel_manifest": channel_binding,
    "installed_toolchain_gate": {
        "receipt_sha256": sha256(child_path),
        "receipt": child_receipt,
        "exact_document_embedded": True,
    },
    "checks": {
        "archive_paths_and_entry_types": "passed",
        "archive_hashes_before_and_after_install": "passed",
        "source_archive_hygiene": "passed",
        "targo_trust_binary_and_docs_layout": "passed",
        "umbrella_trust_archive": "passed",
        "channel_default_profile": "passed",
        "channel_archive_urls_and_hashes": "passed",
        "channel_targo_trust_extension": "passed",
        "installed_compiler_identity": "passed",
        "immutable_installed_toolchain_child_gate": "passed",
    },
    "claim_scope": {
        "kind": "local-pre-publication-dist-rehearsal",
        "public_download_channel": False,
        "hosted_urls_exercised": False,
        "signatures_or_notarization": False,
        "multi_host_availability": False,
    },
}
pathlib.Path(candidate_value).write_text(
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
    printf '\nTrust dist artifacts: VALIDATION COMPLETE (non-authoritative)\n'
    printf '  host: %s\n' "$DIST_HOST"
    printf '  version: %s\n' "$DIST_VERSION"
    printf '  local artifacts: validated and installed; no public-release claim made\n'
    printf '  channel manifest: %s\n' "$CHANNEL_MANIFEST"
    printf '  committing local rehearsal record as the final action: %s\n' "$RECEIPT_OUT"
    if [ "$KEEP_TEMP" = "1" ]; then
        validate_private_temp_root "$TMP_ROOT" "$TMP_ROOT_ID" \
            || fail "temporary root changed before retained-record publication"
        printf '  keeping dist gate directory: %s\n' "$TMP_ROOT"
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
        --expected-prefix "trust-dist-e2e." \
        --expected-identity "$TMP_ROOT_ID"
fi

printf '\nTrust dist artifacts: LOCAL REHEARSAL PASS (non-authoritative)\n'
printf '  host: %s\n' "$DIST_HOST"
printf '  version: %s\n' "$DIST_VERSION"
printf '  local artifacts: validated and installed; no public-release claim made\n'
printf '  channel manifest: %s\n' "$CHANNEL_MANIFEST"
