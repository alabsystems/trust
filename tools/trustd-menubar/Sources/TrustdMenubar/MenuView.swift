// Trust: TrustdMenubar — the dropdown menu content (SwiftUI).
//
// Renders the daemon STATUS snapshot published by `StatusPoller`:
//   - compatible-connected / unavailable banner
//   - daemon-local configured allowance vs reserved + available GiB
//   - queue depth, lifetime granted / released counts
//   - uptime (from started_at)
//   - one row per active worker (label — pid — held MiB — age)
// Read-only: this view never sends RESERVE/RELEASE; it only displays what the
// poller fetched.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

import SwiftUI

struct MenuView: View {
    @ObservedObject var poller: StatusPoller

    var body: some View {
        VStack(alignment: .leading, spacing: 6) {
            header
            Divider()
            if let s = poller.status {
                runningBody(s)
            } else {
                offBody
            }
            Divider()
            footer
        }
        .padding(10)
        .frame(width: 320)
    }

    // MARK: - Header

    private var header: some View {
        HStack(spacing: 6) {
            Image(systemName: poller.isRunning ? "shield.lefthalf.filled" : "shield.slash")
                .foregroundStyle(poller.isRunning ? Color.accentColor : Color.secondary)
            Text("Trustd Monitor")
                .font(.headline)
            Spacer()
            Circle()
                .fill(poller.isRunning ? Color.green : Color.secondary)
                .frame(width: 8, height: 8)
        }
    }

    // MARK: - Running

    @ViewBuilder
    private func runningBody(_ s: DaemonStatus) -> some View {
        VStack(alignment: .leading, spacing: 1) {
            Text("Same-user protocol-compatible endpoint")
                .font(.caption).bold()
            Text("Source: \(poller.lastProbe?.candidate.source.rawValue ?? "connected path"). Exact packaged trustd identity is not established by this monitor.")
                .font(.caption2)
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)
        }

        // Daemon-local configured-allowance gauge.
        VStack(alignment: .leading, spacing: 3) {
            HStack {
                Text("Daemon allowance")
                    .font(.subheadline).bold()
                Spacer()
                if s.isOvercommitted {
                    Text("ceiling lowered · draining")
                        .font(.subheadline)
                        .foregroundStyle(.orange)
                } else if s.budgetEnabled {
                    Text("\(Format.percent(s.fillFraction)) full")
                        .font(.subheadline)
                        .foregroundStyle(gaugeColor(s.fillFraction))
                } else {
                    Text("disabled")
                        .font(.subheadline)
                        .foregroundStyle(.secondary)
                }
            }
            ProgressView(value: s.fillFraction)
                .tint(gaugeColor(s.fillFraction))
            HStack {
                Text("\(Format.gib(s.reserved_bytes)) reserved")
                Spacer()
                Text("\(Format.gib(s.free_bytes)) available")
                Spacer()
                Text("\(Format.gib(s.budget_bytes)) ceiling")
            }
            .font(.caption)
            .foregroundStyle(.secondary)
        }

        // Counters row.
        HStack {
            statCell("Queue", "\(s.queue_depth)")
            Divider().frame(height: 24)
            statCell("Granted", "\(s.granted_total)")
            Divider().frame(height: 24)
            statCell("Released", "\(s.released_total)")
            Divider().frame(height: 24)
            statCell("Uptime", Format.duration(uptimeSecs(s.started_at)))
        }
        .padding(.top, 2)

        // Active workers.
        Divider()
        HStack {
            Text("Active workers")
                .font(.subheadline).bold()
            Spacer()
            Text("\(s.active.count)")
                .font(.subheadline)
                .foregroundStyle(.secondary)
        }
        if s.active.isEmpty {
            Text("none — allowance idle")
                .font(.caption)
                .foregroundStyle(.secondary)
        } else {
            // Newest-last per schema; show up to a sane cap, then summarize.
            let shown = s.active.suffix(12)
            ForEach(Array(shown)) { r in
                workerRow(r)
            }
            if s.active.count > shown.count {
                Text("…and \(s.active.count - shown.count) more")
                    .font(.caption2)
                    .foregroundStyle(.secondary)
            }
        }
    }

    private func workerRow(_ r: ActiveReservation) -> some View {
        HStack(spacing: 6) {
            Text(r.label.isEmpty ? "(unlabeled)" : r.label)
                .font(.caption)
                .lineLimit(1)
                .truncationMode(.middle)
            Spacer()
            Text("pid \(r.pid)")
                .font(.caption2)
                .foregroundStyle(.secondary)
            Text(Format.mib(r.bytes))
                .font(.caption.monospacedDigit())
            Text(Format.duration(r.since_secs))
                .font(.caption2.monospacedDigit())
                .foregroundStyle(.secondary)
                .frame(width: 44, alignment: .trailing)
        }
    }

    // MARK: - Off

    private var offBody: some View {
        VStack(alignment: .leading, spacing: 4) {
            HStack(spacing: 6) {
                Image(systemName: poller.connectionState == .checking ? "arrow.triangle.2.circlepath" : "exclamationmark.circle")
                    .foregroundStyle(.secondary)
                Text(offlineTitle)
                    .font(.subheadline).bold()
            }
            Text(offlineDetail)
                .font(.caption)
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)
            Text("This app does not bundle or start Trust. A crate build restarts trustd after a clean idle shutdown. After an unclean exit, recover only after establishing prior solvers are gone; if uncertain, reboot first.")
                .font(.caption2)
                .foregroundStyle(.secondary)
                .fixedSize(horizontal: false, vertical: true)
        }
    }

    // MARK: - Footer

    private var footer: some View {
        VStack(alignment: .leading, spacing: 4) {
            if let sock = poller.socketPath {
                Text(sock)
                    .font(.caption2.monospaced())
                    .foregroundStyle(.secondary)
                    .lineLimit(1)
                    .truncationMode(.middle)
            } else if let attempt = poller.lastProbe {
                Text("\(attempt.candidate.source.rawValue): \(attempt.candidate.path)")
                    .font(.caption2.monospaced())
                    .foregroundStyle(.secondary)
                    .lineLimit(1)
                    .truncationMode(.middle)
            } else if let configured = poller.configuredSocketPath {
                Text("configured: \(configured)")
                    .font(.caption2.monospaced())
                    .foregroundStyle(.secondary)
                    .lineLimit(1)
                    .truncationMode(.middle)
            }
            HStack {
                if let v = poller.status?.version {
                    Text(v)
                        .font(.caption2)
                        .foregroundStyle(.secondary)
                }
                Spacer()
                Button("Retry") {
                    poller.retryNow()
                }
                .controlSize(.small)
                Button("Set Up…") {
                    ConnectionSettingsPresenter.shared.show(poller: poller)
                }
                .controlSize(.small)
                Button("Guided Tour…") {
                    GuidedTourPresenter.shared.show(poller: poller)
                }
                .controlSize(.small)
                Button("Quit") { NSApplication.shared.terminate(nil) }
                    .controlSize(.small)
            }
        }
    }

    private var offlineTitle: String {
        switch poller.connectionState {
        case .checking:
            return "Checking coordinator…"
        case .connected:
            return "Connected"
        case .noCandidates:
            return "Coordinator unavailable"
        case let .failed(failure, _):
            return failure.title
        }
    }

    private var offlineDetail: String {
        switch poller.connectionState {
        case .checking:
            return "Looking for a compatible trustd STATUS endpoint."
        case .noCandidates:
            return "The standard per-user trustd endpoint could not be derived. Open Set Up to inspect the path and copy diagnostics."
        case let .failed(failure, attempted):
            return "\(failure.detail) Tried \(attempted) configured or discovered path\(attempted == 1 ? "" : "s")."
        case .connected:
            return "A compatible coordinator is connected."
        }
    }

    // MARK: - Helpers

    private func statCell(_ title: String, _ value: String) -> some View {
        VStack(spacing: 1) {
            Text(value)
                .font(.callout.monospacedDigit()).bold()
            Text(title)
                .font(.caption2)
                .foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity)
    }

    /// Green → orange → red as this daemon's configured allowance fills.
    private func gaugeColor(_ frac: Double) -> Color {
        switch frac {
        case ..<0.75: return .green
        case ..<0.90: return .orange
        default:      return .red
        }
    }

    /// Seconds of uptime from a unix-seconds start stamp, clamped at 0.
    private func uptimeSecs(_ startedAt: UInt64) -> UInt64 {
        let now = UInt64(max(0, Date().timeIntervalSince1970))
        return now >= startedAt ? now - startedAt : 0
    }
}
