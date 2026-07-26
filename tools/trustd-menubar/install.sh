#!/usr/bin/env bash
# Build, verify, and atomically install the local Trustd Monitor bundle.
# This installs only the read-only Swift companion, not the Trust toolchain.
set -euo pipefail

PATH=/usr/bin:/bin:/usr/sbin:/sbin
export PATH

SCRIPT_ROOT="$(cd -P "$(/usr/bin/dirname "$0")" && /bin/pwd -P)"
SOURCE_BUNDLE="$SCRIPT_ROOT/TrustdMenubar.app"
VERIFY_APP="$SCRIPT_ROOT/verify-app.sh"
OPEN_AFTER=0

usage() {
    printf '%s\n' \
        'usage: tools/trustd-menubar/install.sh [--open]' \
        '' \
        'Builds and verifies the universal ad-hoc-signed local companion, then' \
        'atomically publishes it to the current account Applications directory.' \
        'This is not Developer-ID-signed or notarized distribution.'
}

while [[ "$#" -gt 0 ]]; do
    case "$1" in
        --open)
            OPEN_AFTER=1
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            usage >&2
            printf 'unknown argument: %s\n' "$1" >&2
            exit 2
            ;;
    esac
done

CURRENT_UID="$(/usr/bin/id -u)"
account_record="$(/usr/bin/dscacheutil -q user -a uid "$CURRENT_UID")"
ACCOUNT_HOME="$(/usr/bin/sed -n 's/^dir: //p' <<<"$account_record")"
if [[ -z "$ACCOUNT_HOME" || "$ACCOUNT_HOME" != /* || "$ACCOUNT_HOME" == *$'\n'* ]]; then
    printf 'could not resolve one absolute home for uid %s\n' "$CURRENT_UID" >&2
    exit 1
fi

validate_private_directory() {
    local directory="$1"
    local label="$2"
    if [[ ! -d "$directory" || -L "$directory" ]]; then
        printf '%s must be a non-symlink directory: %s\n' "$label" "$directory" >&2
        return 1
    fi
    local physical
    physical="$(cd -P "$directory" && /bin/pwd -P)"
    if [[ "$physical" != "$directory" ]]; then
        printf '%s contains a symlink or non-canonical component: %s -> %s\n' \
            "$label" "$directory" "$physical" >&2
        return 1
    fi
    local owner
    local mode
    owner="$(/usr/bin/stat -f '%u' "$directory")"
    mode="$(/usr/bin/stat -f '%OLp' "$directory")"
    if [[ "$owner" != "$CURRENT_UID" ]]; then
        printf '%s is not owned by uid %s: %s\n' "$label" "$CURRENT_UID" "$directory" >&2
        return 1
    fi
    if (( (8#$mode & 0022) != 0 )); then
        printf '%s must not be group/world writable (mode %s): %s\n' \
            "$label" "$mode" "$directory" >&2
        return 1
    fi
}

validate_private_directory "$ACCOUNT_HOME" 'account home'
APPLICATIONS="$ACCOUNT_HOME/Applications"
if [[ ! -e "$APPLICATIONS" && ! -L "$APPLICATIONS" ]]; then
    /bin/mkdir -m 0755 "$APPLICATIONS"
fi
validate_private_directory "$APPLICATIONS" 'account Applications directory'

DESTINATION="$APPLICATIONS/TrustdMenubar.app"
INSTALL_LOCK="$APPLICATIONS/.name.andrewyates.trustd-menubar.install.lock"
if [[ -L "$INSTALL_LOCK" ]]; then
    printf 'refusing symlink install lock: %s\n' "$INSTALL_LOCK" >&2
    exit 1
fi
exec 8>>"$INSTALL_LOCK"
if ! /usr/bin/lockf -s -t 300 8; then
    printf 'timed out waiting for install lock: %s\n' "$INSTALL_LOCK" >&2
    exit 75
fi

# Recheck all path properties after acquiring the cross-repository lock.
validate_private_directory "$ACCOUNT_HOME" 'account home'
validate_private_directory "$APPLICATIONS" 'account Applications directory'
if [[ -L "$DESTINATION" ]]; then
    printf 'refusing to replace symlink destination: %s\n' "$DESTINATION" >&2
    exit 1
fi
prior_present=0
prior_fingerprint=""
if [[ -e "$DESTINATION" ]]; then
    if ! prior_fingerprint="$(/bin/bash "$VERIFY_APP" --identity-only "$DESTINATION")"; then
        printf 'refusing to replace an unrecognized destination: %s\n' "$DESTINATION" >&2
        exit 1
    fi
    prior_present=1
fi

"$SCRIPT_ROOT/build.sh"
source_fingerprint="$(/bin/bash "$VERIFY_APP" "$SOURCE_BUNDLE")"

install_tmp="$(/usr/bin/mktemp -d "$APPLICATIONS/.TrustdMenubar.install.XXXXXX")"
staged_bundle="$install_tmp/TrustdMenubar.app"
publish_tool="$install_tmp/atomic-publish"
CLEANUP_INSTALL_TMP=1
cleanup() {
    if [[ "$CLEANUP_INSTALL_TMP" -eq 1 ]]; then
        /bin/rm -rf -- "$install_tmp"
    else
        printf 'preserved recovery directory: %s\n' "$install_tmp" >&2
    fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

/usr/bin/xcrun --sdk macosx clang \
    -std=c11 \
    -Wall \
    -Wextra \
    -Werror \
    -mmacosx-version-min=13.0 \
    "$SCRIPT_ROOT/AtomicPublish.c" \
    -o "$publish_tool"

/usr/bin/ditto "$SOURCE_BUNDLE" "$staged_bundle"
staged_fingerprint="$(/bin/bash "$VERIFY_APP" "$staged_bundle")"
source_fingerprint_after_copy="$(/bin/bash "$VERIFY_APP" "$SOURCE_BUNDLE")"
if [[ "$staged_fingerprint" != "$source_fingerprint" || \
      "$source_fingerprint_after_copy" != "$source_fingerprint" ]]; then
    printf '%s\n' 'source bundle changed while it was being staged; refusing install' >&2
    exit 1
fi

# Recheck the leaf immediately before the fd-relative publisher opens its
# parents. Existing data must be a verified version of this exact app.
if [[ -e "$DESTINATION" || -L "$DESTINATION" ]]; then
    if ! prior_fingerprint="$(/bin/bash "$VERIFY_APP" --identity-only "$DESTINATION")"; then
        printf 'refusing to replace an unrecognized destination: %s\n' "$DESTINATION" >&2
        exit 1
    fi
    prior_present=1
else
    prior_present=0
    prior_fingerprint=""
fi

CLEANUP_INSTALL_TMP=0
if ! publish_result="$("$publish_tool" "$staged_bundle" "$DESTINATION")"; then
    CLEANUP_INSTALL_TMP=1
    exit 1
fi
if ! final_fingerprint="$(/bin/bash "$VERIFY_APP" "$DESTINATION")" || \
        [[ "$final_fingerprint" != "$staged_fingerprint" ]]; then
    rollback_succeeded=0
    if [[ -d "$staged_bundle" && ! -L "$staged_bundle" ]]; then
        if "$publish_tool" "$staged_bundle" "$DESTINATION" >/dev/null; then
            if [[ "$prior_present" -eq 1 ]] && \
                    restored_fingerprint="$(/bin/bash "$VERIFY_APP" --identity-only "$DESTINATION")" && \
                    [[ "$restored_fingerprint" == "$prior_fingerprint" ]]; then
                rollback_succeeded=1
            fi
        fi
    elif [[ -d "$DESTINATION" && ! -L "$DESTINATION" ]]; then
        if "$publish_tool" "$DESTINATION" "$staged_bundle" >/dev/null && \
                [[ "$prior_present" -eq 0 && ! -e "$DESTINATION" && ! -L "$DESTINATION" ]]; then
            rollback_succeeded=1
        fi
    fi
    if [[ "$rollback_succeeded" -ne 1 ]]; then
        CLEANUP_INSTALL_TMP=0
    fi
    printf 'installed bundle did not match staged fingerprint %s; publication rolled back=%s\n' \
        "$staged_fingerprint" "$rollback_succeeded" >&2
    exit 1
fi
CLEANUP_INSTALL_TMP=1

printf 'installed local companion: %s (%s)\n' "$DESTINATION" "$publish_result"
printf 'fingerprint: %s\n' "$final_fingerprint"
printf '%s\n' 'signature: ad hoc bundle coherence only (no publisher identity; not notarized)'

if [[ "$OPEN_AFTER" -eq 1 ]]; then
    if /usr/bin/pgrep -u "$CURRENT_UID" -x TrustdMenubar >/dev/null; then
        /usr/bin/pkill -TERM -u "$CURRENT_UID" -x TrustdMenubar || true
        for _ in {1..50}; do
            if ! /usr/bin/pgrep -u "$CURRENT_UID" -x TrustdMenubar >/dev/null; then
                break
            fi
            /bin/sleep 0.1
        done
    fi
    if ! /usr/bin/open -n "$DESTINATION"; then
        printf 'warning: install succeeded, but launch failed: %s\n' "$DESTINATION" >&2
    fi
fi
