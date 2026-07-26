// Trust: TrustdMenubar — persisted, Finder-launch-safe socket configuration.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

import SwiftUI
import AppKit

@MainActor
struct ConnectionSettingsView: View {
    @ObservedObject var poller: StatusPoller
    @State private var socketPath: String
    @State private var feedback: String?
    @State private var feedbackIsError = false
    @State private var isTesting = false
    private let standardSocketPath = SocketDiscovery.hostSocketPath()

    init(poller: StatusPoller) {
        self.poller = poller
        _socketPath = State(initialValue: poller.configuredSocketPath ?? "")
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            HStack(spacing: 10) {
                Image(systemName: "point.3.connected.trianglepath.dotted")
                    .font(.title2)
                    .foregroundStyle(Color.accentColor)
                VStack(alignment: .leading, spacing: 2) {
                    Text("Connection Settings")
                        .font(.headline)
                    Text("Choose how this observer finds trustd")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }

            Text("Automatic discovery uses Trust's fixed per-user host endpoint, including Finder launches. Save a path only to observe an explicit test or manual endpoint; if it does not answer, automatic discovery continues.")
                .font(.callout)
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)

            GroupBox("First connection") {
                VStack(alignment: .leading, spacing: 6) {
                    Text("1. Install the Trust toolchain separately; it is not bundled in this app.")
                    Text("2. In any Trust crate, run `targo trust check`. Crate mode establishes one private trustd endpoint shared by this user's verified builds.")
                    Text("3. The app discovers that endpoint automatically. Choose Retry Now if the menu has not refreshed yet.")
                    Text("trustd exits after about five idle minutes, so an offline monitor between builds is normal.")
                        .foregroundStyle(.secondary)
                    Text("Crash recovery must invoke `/absolute/path/to/selected/bin/trustd --recover-after-crash --confirm-no-solvers --socket \(standardSocketPath)`: the sibling of your selected, validated `targo`, never PATH `trustd`. First attest every old solver is gone. If uncertain, reboot first. This app validates neither tool bytes nor recovery and cannot clear the epoch.")
                        .foregroundStyle(.secondary)
                }
                .font(.caption)
                .frame(maxWidth: .infinity, alignment: .leading)
            }

            GroupBox("Standard host endpoint") {
                HStack(alignment: .firstTextBaseline, spacing: 10) {
                    Text(standardSocketPath)
                        .font(.caption.monospaced())
                        .lineLimit(1)
                        .truncationMode(.middle)
                    Spacer()
                    Button("Use This Path") {
                        socketPath = standardSocketPath
                        setFeedback("Standard endpoint copied into the optional override field.")
                    }
                    .controlSize(.small)
                }
                .frame(maxWidth: .infinity, alignment: .leading)
            }

            VStack(alignment: .leading, spacing: 6) {
                Text("Optional explicit socket override")
                    .font(.subheadline.bold())
                TextField(standardSocketPath, text: $socketPath)
                    .textFieldStyle(.roundedBorder)
                    .font(.body.monospaced())
                Text("Use an absolute path or ~/… . This changes only the observer; it does not start trustd, select worker authority, or install Trust.")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }

            if let connected = poller.socketPath {
                HStack(alignment: .firstTextBaseline) {
                    Label("Connected", systemImage: "checkmark.circle.fill")
                        .foregroundStyle(.green)
                    Text(connected)
                        .font(.caption.monospaced())
                        .lineLimit(1)
                        .truncationMode(.middle)
                    Spacer()
                    Button("Use This Path") {
                        socketPath = connected
                        setFeedback("Copied the connected path. Choose Save Path to persist it.")
                    }
                    .controlSize(.small)
                }
            }

            if let attempt = poller.lastProbe {
                VStack(alignment: .leading, spacing: 2) {
                    Text("Last probe · \(attempt.candidate.source.rawValue)")
                        .font(.caption.bold())
                    Text(attempt.candidate.path)
                        .font(.caption2.monospaced())
                        .lineLimit(1)
                        .truncationMode(.middle)
                    if case let .failed(failure) = attempt.outcome {
                        Text("\(failure.title): \(failure.detail)")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                            .fixedSize(horizontal: false, vertical: true)
                    }
                }
            }

            if let feedback {
                Text(feedback)
                    .font(.caption)
                    .foregroundStyle(feedbackIsError ? Color.red : Color.secondary)
                    .fixedSize(horizontal: false, vertical: true)
            }

            Divider()

            HStack {
                Button("Use Automatic Discovery") {
                    socketPath = ""
                    poller.clearConfiguredSocketPath()
                    setFeedback("Saved path cleared. Automatic discovery is active.")
                }

                Spacer()

                Button("Retry Now") {
                    poller.retryNow()
                    setFeedback("Retrying the saved and discovered socket paths now.")
                }

                Button("Copy Diagnostics") {
                    copyDiagnostics()
                }

                Button(isTesting ? "Testing…" : "Test") {
                    testPath()
                }
                .disabled(isTesting || socketPath.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)

                Button("Save Path") {
                    if poller.saveConfiguredSocketPath(socketPath) {
                        socketPath = poller.configuredSocketPath ?? socketPath
                        setFeedback("Saved. The observer is reconnecting now.")
                    } else {
                        setFeedback("Enter an absolute path or a path beginning with ~/.", isError: true)
                    }
                }
                .keyboardShortcut(.defaultAction)
                .disabled(socketPath.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty)
            }
        }
        .padding(22)
        .frame(width: 680)
    }

    private func copyDiagnostics() {
        let pasteboard = NSPasteboard.general
        pasteboard.clearContents()
        if pasteboard.setString(poller.diagnosticsText, forType: .string) {
            setFeedback("Copied read-only connection diagnostics to the clipboard.")
        } else {
            setFeedback("macOS did not accept the diagnostics clipboard write.", isError: true)
        }
    }

    private func testPath() {
        let pathToTest = socketPath
        isTesting = true
        feedback = nil
        Task {
            let result = await poller.testSocketPath(pathToTest)
            isTesting = false
            switch result {
            case let .compatible(version):
                setFeedback("Same-user compatible STATUS endpoint found (\(version)); exact packaged daemon identity was not established.")
            case let .failed(failure):
                setFeedback("\(failure.title). \(failure.detail)", isError: true)
            case .invalidPath:
                setFeedback("Enter an absolute path or a path beginning with ~/.", isError: true)
            }
        }
    }

    private func setFeedback(_ message: String, isError: Bool = false) {
        feedback = message
        feedbackIsError = isError
    }
}

/// Owns an AppKit window because this LSUIElement app has no ordinary Settings
/// scene. Reusing one presenter keeps menu and Guided Tour entry points aligned.
@MainActor
final class ConnectionSettingsPresenter {
    static let shared = ConnectionSettingsPresenter()

    private var windowController: NSWindowController?

    private init() {}

    func show(poller: StatusPoller) {
        let rootView = ConnectionSettingsView(poller: poller)
        if let windowController {
            windowController.contentViewController = NSHostingController(rootView: rootView)
            reveal(windowController)
            return
        }

        let window = NSWindow(
            contentRect: NSRect(x: 0, y: 0, width: 680, height: 560),
            styleMask: [.titled, .closable, .miniaturizable],
            backing: .buffered,
            defer: false
        )
        window.title = "Trust Connection Settings"
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
