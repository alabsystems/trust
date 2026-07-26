// Trust: TrustdMenubar — app entry point.
//
// A menubar-only (LSUIElement) SwiftUI app exposing the trustd memory
// coordinator's live STATUS as an NSStatusItem dropdown. The icon is an
// SF Symbol shield/gauge; clicking it shows daemon allowance vs reserved, active
// workers, queue depth, grant/release counts, and uptime. A 1.5 s poller
// (StatusPoller) talks the read-only STATUS/PING protocol over the daemon's
// AF_UNIX socket and reports only what a compatible endpoint establishes.
//
// Built with `swiftc` straight into a `.app` bundle (no xcodebuild / .xcodeproj);
// see build.sh.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

import SwiftUI
import AppKit

@main
struct TrustdMenubarApp: App {
    @NSApplicationDelegateAdaptor(AppDelegate.self) private var appDelegate

    var body: some Scene {
        // MenuBarExtra is backed by NSStatusItem. `.window` lets the rich
        // SwiftUI MenuView render (gauge, rows) rather than a plain NSMenu.
        MenuBarExtra {
            MenuView(poller: appDelegate.poller)
        } label: {
            MenubarStatusLabel(poller: appDelegate.poller)
        }
        .menuBarExtraStyle(.window)
    }
}

/// Observe the poller directly so the MenuBarExtra label changes even while its
/// dropdown content is closed.
private struct MenubarStatusLabel: View {
    @ObservedObject var poller: StatusPoller

    var body: some View {
        // SF Symbol → crisp at menubar size.
        Image(systemName: poller.isRunning ? "shield.lefthalf.filled" : "shield.slash")
    }
}

/// Forces menubar-only behavior at runtime (belt-and-suspenders with the
/// Info.plist `LSUIElement = true`): no Dock icon, no app menu.
@MainActor
final class AppDelegate: NSObject, NSApplicationDelegate {
    let poller = StatusPoller()

    func applicationDidFinishLaunching(_ notification: Notification) {
        NSApp.setActivationPolicy(.accessory)
        // Start once with the application lifecycle, not each time the dropdown
        // appears. Status is therefore live before the first menu click.
        _ = poller.start()
        // Present once per tour revision. Dispatching one turn lets SwiftUI
        // finish installing the MenuBarExtra before the accessory window opens.
        DispatchQueue.main.async {
            GuidedTourPresenter.shared.presentOnFirstLaunchIfNeeded(poller: self.poller)
        }
    }

    func applicationWillTerminate(_ notification: Notification) {
        poller.stop()
    }
}
