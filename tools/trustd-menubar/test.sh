#!/usr/bin/env bash
# Compile and run TrustdMenubar's source-level contracts without creating,
# signing, or launching an application bundle.
set -euo pipefail

cd "$(dirname "$0")"

TEST_TMP="$(/usr/bin/mktemp -d "${TMPDIR:-/tmp}/trustd-menubar-tests.XXXXXX")"
TEST_TMP="$(cd -P "$TEST_TMP" && /bin/pwd -P)"
cleanup() {
    rm -rf -- "$TEST_TMP"
}
trap cleanup EXIT INT TERM

SDK="$(/usr/bin/xcrun --sdk macosx --show-sdk-path)"
SWIFTC="$(/usr/bin/xcrun --find swiftc)"
ARCH="$(uname -m)"
case "$ARCH" in
    arm64|x86_64) ;;
    *)
        echo "unsupported test host architecture: $ARCH" >&2
        exit 1
        ;;
esac

COMMON_FLAGS=(
    -swift-version 6
    -strict-concurrency=complete
    -warnings-as-errors
    -sdk "$SDK"
    -target "${ARCH}-apple-macosx13.0"
)

# First compile-check the exact full production source set, including SwiftUI,
# app lifecycle, tour, and settings code. The executable build below then runs
# deterministic non-UI contracts.
"$SWIFTC" \
    -typecheck \
    "${COMMON_FLAGS[@]}" \
    -framework AppKit \
    -framework SwiftUI \
    -framework Foundation \
    Sources/TrustdMenubar/*.swift

"$SWIFTC" \
    -parse-as-library \
    "${COMMON_FLAGS[@]}" \
    -framework Foundation \
    -framework Combine \
    Sources/TrustdMenubar/Status.swift \
    Sources/TrustdMenubar/Poller.swift \
    Tests/ContractTests.swift \
    -o "$TEST_TMP/TrustdMenubarContractTests"

"$TEST_TMP/TrustdMenubarContractTests"

# UI/lifecycle wiring remains a deterministic source contract even though this
# lightweight harness intentionally does not assemble or launch a SwiftUI app.
if grep -R -F "aggregate budget is still enforced" Sources/TrustdMenubar >/dev/null; then
    echo "offline UI must not infer aggregate coordination" >&2
    exit 1
fi
grep -F "Task.detached(priority: .utility)" Sources/TrustdMenubar/Poller.swift >/dev/null
grep -F "guard pollingTask == nil" Sources/TrustdMenubar/Poller.swift >/dev/null
grep -F "_ = poller.start()" Sources/TrustdMenubar/TrustdMenubarApp.swift >/dev/null
grep -F "ConnectionSettingsPresenter.shared.show" Sources/TrustdMenubar/GuidedTour.swift >/dev/null
grep -F "private static let presentationVersion = 8" Sources/TrustdMenubar/GuidedTour.swift >/dev/null
grep -F "targo trust check" Sources/TrustdMenubar/GuidedTour.swift >/dev/null
grep -F -- "--recover-after-crash --confirm-no-solvers --socket" Sources/TrustdMenubar/GuidedTour.swift >/dev/null
grep -F 'the sibling of your selected, validated `targo`, never PATH `trustd`' Sources/TrustdMenubar/GuidedTour.swift >/dev/null
grep -F "If uncertain, reboot first" Sources/TrustdMenubar/GuidedTour.swift >/dev/null
grep -F "Same-user protocol-compatible endpoint" Sources/TrustdMenubar/MenuView.swift >/dev/null
grep -F "Exact packaged trustd identity is not established" Sources/TrustdMenubar/MenuView.swift >/dev/null
grep -F "Standard host endpoint" Sources/TrustdMenubar/ConnectionSettings.swift >/dev/null
grep -F "Copy Diagnostics" Sources/TrustdMenubar/ConnectionSettings.swift >/dev/null
grep -F '"bundled_toolchain=false"' Sources/TrustdMenubar/Poller.swift >/dev/null
grep -F 'static let runtimeRootPrefix = "trustd-runtime-locks"' Sources/TrustdMenubar/Poller.swift >/dev/null
grep -F 'pub const STATUS_VERSION: &str = "trustd.status.v1";' \
    ../../crates/trust-router/src/coordinator.rs >/dev/null
grep -F "ARCHITECTURES=(arm64 x86_64)" build.sh >/dev/null
grep -F '"$LIPO" -create' build.sh >/dev/null
bash -n install.sh
grep -F 'source_fingerprint_after_copy="$(/bin/bash "$VERIFY_APP" "$SOURCE_BUNDLE")"' install.sh >/dev/null
grep -F 'signature: ad hoc bundle coherence only (no publisher identity; not notarized)' install.sh >/dev/null
grep -F 'renameatx_np' AtomicPublish.c >/dev/null
/bin/bash Tests/InstallContracts.sh "$PWD" "$TEST_TMP/install-contracts"
/usr/bin/plutil -lint Resources/Info.plist >/dev/null
test "$(/usr/libexec/PlistBuddy -c 'Print :CFBundleShortVersionString' Resources/Info.plist)" = "1.4.1"
test "$(/usr/libexec/PlistBuddy -c 'Print :CFBundleVersion' Resources/Info.plist)" = "7"

echo "TrustdMenubar UI/lifecycle source contracts passed"
