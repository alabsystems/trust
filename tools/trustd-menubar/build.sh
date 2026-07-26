#!/usr/bin/env bash
# Trust: build TrustdMenubar.app with swiftc directly into a .app bundle.
#
# No xcodebuild / .xcodeproj required — this assembles a runnable bundle from
# the Apple Swift toolchain in CommandLineTools. This checks that the companion
# app compiles; it is not a Trust compiler self-verification claim.
#
# Usage: ./build.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache 2.0
set -euo pipefail

SCRIPT_ROOT="$(cd -P "$(/usr/bin/dirname "$0")" && /bin/pwd -P)"
BUILD_LOCK="$SCRIPT_ROOT/.TrustdMenubar.build.lock"
if [[ -L "$BUILD_LOCK" ]]; then
    printf 'refusing symlink build lock: %s\n' "$BUILD_LOCK" >&2
    exit 1
fi
exec 9>>"$BUILD_LOCK"
if ! /usr/bin/lockf -s -t 300 9; then
    printf 'timed out waiting for build lock: %s\n' "$BUILD_LOCK" >&2
    exit 75
fi
if [[ "$#" -ne 0 ]]; then
    printf 'usage: %s\n' "$0" >&2
    exit 64
fi
cd "$SCRIPT_ROOT"

APP_NAME="TrustdMenubar"
BUNDLE="$SCRIPT_ROOT/${APP_NAME}.app"
SDK="$(/usr/bin/xcrun --sdk macosx --show-sdk-path)"
SWIFTC="$(/usr/bin/xcrun --find swiftc)"
LIPO="$(/usr/bin/xcrun --find lipo)"
VERIFY_APP="$SCRIPT_ROOT/verify-app.sh"
# Stage beside the destination so the final directory rename cannot cross a
# filesystem boundary. Atomic swap keeps the prior app continuously runnable.
BUILD_TMP="$(/usr/bin/mktemp -d "$SCRIPT_ROOT/.${APP_NAME}.build.XXXXXX")"
STAGED_BUNDLE="${BUILD_TMP}/${APP_NAME}.app"
PUBLISH_TOOL="${BUILD_TMP}/atomic-publish"
CLEANUP_BUILD_TMP=1
cleanup() {
    if [[ "$CLEANUP_BUILD_TMP" -eq 1 ]]; then
        /bin/rm -rf -- "$BUILD_TMP"
    else
        printf 'preserved recovery directory: %s\n' "$BUILD_TMP" >&2
    fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Build both supported Mac CPU families. Deployment floor 13.0 keeps
# MenuBarExtra (introduced macOS 13) available.
ARCHITECTURES=(arm64 x86_64)

printf '==> SDK:    %s\n' "$SDK"
printf '==> target: universal macOS 13+ (%s)\n' "${ARCHITECTURES[*]}"
printf '==> swiftc: %s\n' "$("$SWIFTC" --version | /usr/bin/head -1)"

/usr/bin/xcrun --sdk macosx clang \
    -std=c11 \
    -Wall \
    -Wextra \
    -Werror \
    -mmacosx-version-min=13.0 \
    "$SCRIPT_ROOT/AtomicPublish.c" \
    -o "$PUBLISH_TOOL"

# Assemble away from the destination. The existing runnable bundle remains
# untouched until compilation, universal linking, and signature verification
# have all succeeded.
/bin/mkdir -p "$STAGED_BUNDLE/Contents/MacOS"
/bin/mkdir -p "$STAGED_BUNDLE/Contents/Resources"

# Compile each architecture independently, then combine the exact products.
thin_binaries=()
for architecture in "${ARCHITECTURES[@]}"; do
    thin_binary="${BUILD_TMP}/${APP_NAME}.${architecture}"
    printf '==> compiling %s…\n' "$architecture"
    "$SWIFTC" \
        -O \
        -swift-version 6 \
        -strict-concurrency=complete \
        -warnings-as-errors \
        -sdk "$SDK" \
        -target "${architecture}-apple-macosx13.0" \
        -framework AppKit \
        -framework SwiftUI \
        -framework Foundation \
        "$SCRIPT_ROOT"/Sources/${APP_NAME}/*.swift \
        -o "$thin_binary"
    thin_binaries+=("$thin_binary")
done
"$LIPO" -create "${thin_binaries[@]}" -output "$STAGED_BUNDLE/Contents/MacOS/${APP_NAME}"

# Install the Info.plist and make the executable runnable.
/bin/cp "$SCRIPT_ROOT/Resources/Info.plist" "$STAGED_BUNDLE/Contents/Info.plist"
/bin/chmod +x "$STAGED_BUNDLE/Contents/MacOS/${APP_NAME}"
/usr/bin/plutil -lint "$STAGED_BUNDLE/Contents/Info.plist"
"$LIPO" "$STAGED_BUNDLE/Contents/MacOS/${APP_NAME}" -verify_arch arm64 x86_64

# Seal the finished local bundle, including Info.plist. This ad-hoc signature
# catches assembly errors and lets macOS treat the output as one coherent app;
# it is intentionally not a Developer ID signature or notarization.
printf '%s\n' '==> ad-hoc signing…'
/usr/bin/codesign --force --sign - "$STAGED_BUNDLE"
staged_cdhash="$(/bin/bash "$VERIFY_APP" "$STAGED_BUNDLE")"

# Publish only the completely verified local bundle. Existing and staged app
# directories are exchanged atomically; a first publication uses no-replace.
prior_present=0
prior_fingerprint=""
if [[ -e "$BUNDLE" || -L "$BUNDLE" ]]; then
    if ! prior_fingerprint="$(/bin/bash "$VERIFY_APP" --identity-only "$BUNDLE")"; then
        printf 'ERROR: refusing to replace an unrecognized path: %s\n' "$BUNDLE" >&2
        exit 1
    fi
    prior_present=1
fi
CLEANUP_BUILD_TMP=0
if ! publish_result="$("$PUBLISH_TOOL" "$STAGED_BUNDLE" "$BUNDLE")"; then
    CLEANUP_BUILD_TMP=1
    exit 1
fi
if ! final_cdhash="$(/bin/bash "$VERIFY_APP" "$BUNDLE")" || \
        [[ "$final_cdhash" != "$staged_cdhash" ]]; then
    rollback_succeeded=0
    if [[ -d "$STAGED_BUNDLE" && ! -L "$STAGED_BUNDLE" ]]; then
        if "$PUBLISH_TOOL" "$STAGED_BUNDLE" "$BUNDLE" >/dev/null; then
            if [[ "$prior_present" -eq 1 ]] && \
                    restored_fingerprint="$(/bin/bash "$VERIFY_APP" --identity-only "$BUNDLE")" && \
                    [[ "$restored_fingerprint" == "$prior_fingerprint" ]]; then
                rollback_succeeded=1
            fi
        fi
    elif [[ -d "$BUNDLE" && ! -L "$BUNDLE" ]]; then
        if "$PUBLISH_TOOL" "$BUNDLE" "$STAGED_BUNDLE" >/dev/null && \
                [[ "$prior_present" -eq 0 && ! -e "$BUNDLE" && ! -L "$BUNDLE" ]]; then
            rollback_succeeded=1
        fi
    fi
    if [[ "$rollback_succeeded" -eq 1 ]]; then
        CLEANUP_BUILD_TMP=1
    fi
    printf 'ERROR: final bundle identity did not match staged CDHash %s\n' \
        "$staged_cdhash" >&2
    exit 1
fi
CLEANUP_BUILD_TMP=1

printf '==> built %s (%s, CDHash %s)\n' "$BUNDLE" "$publish_result" "$final_cdhash"
printf '    launch with: /usr/bin/open %s\n' "$BUNDLE"
