#!/usr/bin/env bash
# Verify the exact local Trustd Monitor product and print its signed CDHash.
set -euo pipefail

EXPECTED_IDENTIFIER="name.andrewyates.trustd-menubar"
EXPECTED_EXECUTABLE="TrustdMenubar"
EXPECTED_SHORT_VERSION="1.4.1"
EXPECTED_BUILD_VERSION="7"

IDENTITY_ONLY=0
if [[ "${1:-}" == "--identity-only" ]]; then
    IDENTITY_ONLY=1
    shift
fi
if [[ "$#" -ne 1 ]]; then
    printf 'usage: %s [--identity-only] /absolute/path/TrustdMenubar.app\n' "$0" >&2
    exit 64
fi

BUNDLE="$1"
if [[ "$BUNDLE" != /* || ! -d "$BUNDLE" || -L "$BUNDLE" ]]; then
    printf 'bundle must be an absolute, non-symlink directory: %s\n' "$BUNDLE" >&2
    exit 65
fi

symlink_entry="$(/usr/bin/find "$BUNDLE" -type l -print -quit)"
if [[ -n "$symlink_entry" ]]; then
    printf 'bundle contains a symlink: %s\n' "$symlink_entry" >&2
    exit 65
fi

INFO_PLIST="$BUNDLE/Contents/Info.plist"
EXECUTABLE="$BUNDLE/Contents/MacOS/$EXPECTED_EXECUTABLE"
if [[ ! -f "$INFO_PLIST" || ! -f "$EXECUTABLE" || ! -x "$EXECUTABLE" ]]; then
    printf 'bundle is missing its exact plist or executable: %s\n' "$BUNDLE" >&2
    exit 65
fi

/usr/bin/plutil -lint "$INFO_PLIST" >/dev/null
plist_value() {
    /usr/libexec/PlistBuddy -c "Print :$1" "$INFO_PLIST"
}
require_plist_value() {
    local key="$1"
    local expected="$2"
    local actual
    actual="$(plist_value "$key")"
    if [[ "$actual" != "$expected" ]]; then
        printf 'unexpected %s in %s: expected %s, got %s\n' \
            "$key" "$BUNDLE" "$expected" "$actual" >&2
        exit 65
    fi
}

require_plist_value CFBundleIdentifier "$EXPECTED_IDENTIFIER"
require_plist_value CFBundleExecutable "$EXPECTED_EXECUTABLE"
require_plist_value CFBundlePackageType APPL
require_plist_value CFBundleName TrustdMenubar
require_plist_value LSUIElement true
if [[ "$IDENTITY_ONLY" -eq 0 ]]; then
    require_plist_value CFBundleShortVersionString "$EXPECTED_SHORT_VERSION"
    require_plist_value CFBundleVersion "$EXPECTED_BUILD_VERSION"
    require_plist_value LSMinimumSystemVersion 13.0
else
    short_version="$(plist_value CFBundleShortVersionString)"
    build_version="$(plist_value CFBundleVersion)"
    minimum_version="$(plist_value LSMinimumSystemVersion)"
    if [[ ! "$short_version" =~ ^[0-9]+([.][0-9]+)*$ || \
          ! "$build_version" =~ ^[0-9]+$ || \
          ! "$minimum_version" =~ ^[0-9]+([.][0-9]+)*$ ]]; then
        printf 'installed bundle has malformed version metadata: %s\n' "$BUNDLE" >&2
        exit 65
    fi
fi

/usr/bin/codesign --verify --deep --strict --all-architectures "$BUNDLE" >/dev/null 2>&1
/usr/bin/xcrun lipo "$EXECUTABLE" -verify_arch arm64 x86_64

fingerprint_parts=()
for architecture in arm64 x86_64; do
    signature_details="$(/usr/bin/codesign -d --arch "$architecture" --verbose=4 "$BUNDLE" 2>&1)"
    if ! /usr/bin/grep -Fx "Identifier=$EXPECTED_IDENTIFIER" <<<"$signature_details" >/dev/null; then
        printf 'code signature identifier is not %s for %s: %s\n' \
            "$EXPECTED_IDENTIFIER" "$architecture" "$BUNDLE" >&2
        exit 65
    fi
    if ! /usr/bin/grep -Fx 'Signature=adhoc' <<<"$signature_details" >/dev/null; then
        printf 'expected an ad-hoc local signature for %s: %s\n' \
            "$architecture" "$BUNDLE" >&2
        exit 65
    fi
    if ! /usr/bin/grep -Fx 'TeamIdentifier=not set' <<<"$signature_details" >/dev/null; then
        printf 'unexpected signing-team identity for %s: %s\n' \
            "$architecture" "$BUNDLE" >&2
        exit 65
    fi
    cdhash="$(/usr/bin/sed -n 's/^CDHash=//p' <<<"$signature_details")"
    if [[ ! "$cdhash" =~ ^[0-9a-f]{40}$ ]]; then
        printf 'missing unique SHA-256 CDHash for %s in %s\n' \
            "$architecture" "$BUNDLE" >&2
        exit 65
    fi
    fingerprint_parts+=("${architecture}:${cdhash}")
done
printf '%s;%s\n' "${fingerprint_parts[0]}" "${fingerprint_parts[1]}"
