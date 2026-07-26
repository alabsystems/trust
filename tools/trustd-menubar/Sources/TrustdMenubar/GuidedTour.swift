// Trust: TrustdMenubar — first-run and on-demand guided tour.
//
// This window explains the observer's deliberately narrow responsibility. It
// is a status UI for trustd's memory coordinator; it is not the Trust compiler,
// an installer, a proof-result viewer, or a daemon controller.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

import SwiftUI
import AppKit

private struct GuidedTourPage {
    let symbol: String
    let title: String
    let summary: String
    let points: [String]
}

private let guidedTourPages = [
    GuidedTourPage(
        symbol: "shield.lefthalf.filled",
        title: "A focused Trust companion",
        summary: "Trustd Monitor is a standalone, read-only macOS companion for trustd, the daemon-backed admission coordinator for participating Trust workers.",
        points: [
            "It shows this daemon's current effective allowance, reservations, queue depth, worker activity, and uptime. A lowered allowance keeps existing work visible and shows zero free capacity.",
            "It does not contain, install, or configure the Trust compiler toolchain.",
            "Quitting this app does not stop trustd or change a running build.",
        ]
    ),
    GuidedTourPage(
        symbol: "point.3.connected.trianglepath.dotted",
        title: "Connect during a Trust build",
        summary: "Trust is installed separately. On macOS, verified crate mode requires and starts its selected same-sysroot trustd authority.",
        points: [
            "From any Trust crate, run `targo trust check`; the toolchain establishes one private per-user host endpoint shared across Cargo target directories.",
            "The app derives that endpoint from your effective user ID and discovers it automatically, including when launched from Finder. Connection Settings remains available for explicit test or manual endpoints.",
            "A filled shield means a same-user, protocol-compatible STATUS endpoint answered; the menu names the discovery source. This observer does not bind that endpoint to exact packaged daemon bytes. A slashed shield means only that no compatible endpoint answered. Neither state establishes that all processes participate or that physical host RSS is bounded.",
            "trustd exits after about five idle minutes, so offline between builds is expected; start the next build and choose Retry Now.",
            "Crash recovery must invoke `/absolute/path/to/selected/bin/trustd --recover-after-crash --confirm-no-solvers --socket <path>`: the sibling of your selected, validated `targo`, never PATH `trustd`. First attest every old solver is gone. If uncertain, reboot first. This observer validates neither tool bytes nor recovery.",
        ]
    ),
    GuidedTourPage(
        symbol: "checkmark.seal",
        title: "Coordinator status is not proof status",
        summary: "This app observes one endpoint's resource-admission ledger only. Verification and proof claims belong to the Trust compiler workflow.",
        points: [
            "A green daemon indicator says nothing about whether source code was verified.",
            "An explicitly unverified compiler run carries no proof claim.",
            "Use the toolchain's own receipts and diagnostics when evaluating verification results.",
        ]
    ),
    GuidedTourPage(
        symbol: "menubar.rectangle",
        title: "Keep it close",
        summary: "Open the shield for a quick view of this daemon's admission pressure and active reservations.",
        points: [
            "The observer uses only read-only STATUS/PING requests; it never grants, releases, cancels, starts, or stops work.",
            "If no daemon is visible, the menu explains the offline state instead of inventing data.",
            "Connection Settings shows the standard host endpoint, can test an explicit override, retry immediately, and copy diagnostics without changing the daemon.",
        ]
    ),
]

struct GuidedTourView: View {
    @State private var pageIndex = 0
    let onOpenConnectionSettings: () -> Void
    let onFinish: () -> Void

    private var page: GuidedTourPage { guidedTourPages[pageIndex] }
    private var isLastPage: Bool { pageIndex == guidedTourPages.count - 1 }

    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack(spacing: 10) {
                Image(systemName: "shield.lefthalf.filled")
                    .font(.title2)
                    .foregroundStyle(Color.accentColor)
                VStack(alignment: .leading, spacing: 1) {
                    Text("Trustd Monitor Guided Tour")
                        .font(.headline)
                    Text("Local macOS companion")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
                Spacer()
                Text("\(pageIndex + 1) of \(guidedTourPages.count)")
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
            }

            Divider()
                .padding(.vertical, 18)

            HStack(alignment: .top, spacing: 24) {
                Image(systemName: page.symbol)
                    .font(.system(size: 58, weight: .regular))
                    .foregroundStyle(Color.accentColor)
                    .frame(width: 76, height: 76)
                    .accessibilityHidden(true)

                VStack(alignment: .leading, spacing: 14) {
                    Text(page.title)
                        .font(.title2.bold())
                    Text(page.summary)
                        .font(.body)
                        .foregroundStyle(.secondary)
                        .fixedSize(horizontal: false, vertical: true)

                    VStack(alignment: .leading, spacing: 10) {
                        ForEach(Array(page.points.enumerated()), id: \.offset) { _, point in
                            HStack(alignment: .firstTextBaseline, spacing: 9) {
                                Image(systemName: "circle.fill")
                                    .font(.system(size: 5))
                                    .foregroundStyle(Color.accentColor)
                                Text(point)
                                    .fixedSize(horizontal: false, vertical: true)
                            }
                        }
                    }
                    .font(.callout)
                }
            }
            .frame(maxWidth: .infinity, maxHeight: .infinity, alignment: .topLeading)

            Divider()
                .padding(.vertical, 16)

            HStack {
                Button("Back") {
                    pageIndex = max(0, pageIndex - 1)
                }
                .disabled(pageIndex == 0)

                Button("Connection Settings…") {
                    onOpenConnectionSettings()
                }

                Spacer()

                HStack(spacing: 6) {
                    ForEach(guidedTourPages.indices, id: \.self) { index in
                        Circle()
                            .fill(index == pageIndex ? Color.accentColor : Color.secondary.opacity(0.25))
                            .frame(width: 7, height: 7)
                    }
                }
                .accessibilityLabel("Tour page \(pageIndex + 1) of \(guidedTourPages.count)")

                Spacer()

                Button(isLastPage ? "Done" : "Next") {
                    if isLastPage {
                        onFinish()
                    } else {
                        pageIndex += 1
                    }
                }
                .keyboardShortcut(.defaultAction)
            }
        }
        .padding(24)
        .frame(width: 620, height: 480)
    }
}

/// Owns the AppKit window because this is an LSUIElement/MenuBarExtra app with
/// no ordinary WindowGroup. Keeping presentation here makes first-run launch
/// and the menu's on-demand action use the same window.
@MainActor
final class GuidedTourPresenter {
    static let shared = GuidedTourPresenter()

    // Bump when onboarding content materially changes so existing installs see
    // the new connection workflow once.
    private static let presentationVersion = 8
    private static let presentedVersionKey = "guidedTourPresentedVersion"

    private var windowController: NSWindowController?

    private init() {}

    func presentOnFirstLaunchIfNeeded(poller: StatusPoller) {
        let defaults = UserDefaults.standard
        guard defaults.integer(forKey: Self.presentedVersionKey) < Self.presentationVersion else {
            return
        }

        // Record presentation, not completion: closing the window should not
        // nag on every launch. The menu always provides a way back in.
        defaults.set(Self.presentationVersion, forKey: Self.presentedVersionKey)
        show(poller: poller)
    }

    func show(poller: StatusPoller) {
        let rootView = GuidedTourView(
            onOpenConnectionSettings: {
                ConnectionSettingsPresenter.shared.show(poller: poller)
            },
            onFinish: { [weak self] in
                self?.windowController?.close()
            }
        )

        if let windowController {
            windowController.contentViewController = NSHostingController(rootView: rootView)
            reveal(windowController)
            return
        }

        let window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 620, height: 450),
            styleMask: [.titled, .closable, .miniaturizable],
            backing: .buffered,
            defer: false
        )
        window.title = "Trustd Monitor Guided Tour"
        window.isReleasedWhenClosed = false
        window.contentViewController = NSHostingController(rootView: rootView)
        window.center()

        let controller = NSWindowController(window: window)
        windowController = controller
        reveal(controller)
    }

    private func reveal(_ controller: NSWindowController) {
        controller.showWindow(nil)
        controller.window?.makeKeyAndOrderFront(nil)
        NSApplication.shared.activate(ignoringOtherApps: true)
    }
}
