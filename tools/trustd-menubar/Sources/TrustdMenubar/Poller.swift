// Trust: TrustdMenubar — socket discovery + the 1.5 s STATUS poller.
//
// Locating the daemon socket (AF_UNIX in one private per-euid host runtime):
//   1. a socket path saved in Connection Settings
//   2. $TRUST_MEMORY_JOBSERVER_SOCK            (the env targo exports — exact)
//   3. $TRUSTD_MENUBAR_SOCK                    (observer-only override)
//   4. /tmp/trustd-runtime-locks-<euid>/trust-memory-jobserver.sock
// The first compatible STATUS answer wins, and the winner is sticky until it
// stops answering. All filesystem/socket work runs outside the main actor.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

import Foundation
import Combine
import Darwin

enum CoordinatorConnectionState: Equatable, Sendable {
    case checking
    case connected
    case noCandidates
    case failed(UnixSocketClient.EndpointFailure, attempted: Int)
}

enum SocketPathTestResult: Equatable, Sendable {
    case compatible(version: String)
    case failed(UnixSocketClient.EndpointFailure)
    case invalidPath
}

enum SocketCandidateSource: String, Equatable, Sendable {
    case lastConnected = "Last connected path"
    case configured = "Saved path"
    case workerEnvironment = "Trust worker environment"
    case observerEnvironment = "Observer environment"
    case hostRuntime = "Per-user host runtime"
}

struct SocketCandidate: Equatable, Sendable {
    let path: String
    let source: SocketCandidateSource
}

enum SocketProbeOutcome: Equatable, Sendable {
    case compatible(version: String)
    case failed(UnixSocketClient.EndpointFailure)

    var diagnosticCode: String {
        switch self {
        case let .compatible(version): return "compatible:\(version)"
        case let .failed(failure): return failure.diagnosticCode
        }
    }
}

struct SocketProbeAttempt: Equatable, Sendable {
    let candidate: SocketCandidate
    let outcome: SocketProbeOutcome
}

struct SocketProbeSummary: Sendable {
    let status: DaemonStatus?
    let socketPath: String?
    let attempted: Int
    /// Connected attempt, or the highest-precedence failure when all fail.
    let reportedAttempt: SocketProbeAttempt?
}

/// Pure discovery/probing helpers. These functions deliberately have no UI
/// state, so the poller can execute them in a detached utility task.
enum SocketDiscovery {
    static let configuredSocketDefaultsKey = "configuredSocketPath"
    static let runtimeRootPrefix = "trustd-runtime-locks"
    static let socketFileName = "trust-memory-jobserver.sock"

    /// Mirror `coordinator::host_socket_path`: use the canonical system `/tmp`,
    /// never Finder's or a shell's environment-specific `$TMPDIR`, then derive
    /// the fixed per-effective-user authority endpoint.
    static func hostSocketPath(
        effectiveUserID: uid_t = geteuid(),
        systemTemporaryDirectory: String = "/tmp"
    ) -> String {
        let canonicalRoot = systemTemporaryDirectory.withCString { path -> String? in
            guard let resolved = Darwin.realpath(path, nil) else { return nil }
            defer { Darwin.free(resolved) }
            return String(cString: resolved)
        } ?? systemTemporaryDirectory
        var root = canonicalRoot
        while root.count > 1 && root.hasSuffix("/") {
            root.removeLast()
        }
        let separator = root == "/" ? "" : "/"
        return "\(root)\(separator)\(runtimeRootPrefix)-\(effectiveUserID)/\(socketFileName)"
    }

    static func normalizeConfiguredPath(
        _ raw: String?,
        homeDirectory: String = FileManager.default.homeDirectoryForCurrentUser.path
    ) -> String? {
        guard let raw else { return nil }
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else { return nil }

        let expanded: String
        if trimmed == "~" {
            expanded = homeDirectory
        } else if trimmed.hasPrefix("~/") {
            expanded = homeDirectory + String(trimmed.dropFirst())
        } else {
            expanded = trimmed
        }
        guard expanded.hasPrefix("/") else { return nil }
        return URL(fileURLWithPath: expanded).standardizedFileURL.path
    }

    /// Ordered, de-duplicated socket paths. Arguments are injectable so path
    /// precedence can be regression-tested without touching the real home dir.
    static func candidateSockets(
        configuredSocketPath: String?,
        environment: [String: String] = ProcessInfo.processInfo.environment,
        homeDirectory: String = FileManager.default.homeDirectoryForCurrentUser.path,
        effectiveUserID: uid_t = geteuid(),
        systemTemporaryDirectory: String = "/tmp"
    ) -> [SocketCandidate] {
        var out = [SocketCandidate]()
        var seen = Set<String>()
        func add(_ path: String?, source: SocketCandidateSource) {
            guard let path, !path.isEmpty, !seen.contains(path) else { return }
            seen.insert(path)
            out.append(SocketCandidate(path: path, source: source))
        }

        // 1. A Finder-launch-safe, persisted setting.
        add(
            normalizeConfiguredPath(configuredSocketPath, homeDirectory: homeDirectory),
            source: .configured
        )

        // 2. Exact worker socket environment.
        add(environment["TRUST_MEMORY_JOBSERVER_SOCK"], source: .workerEnvironment)

        // 3. Optional observer-only environment override.
        add(environment["TRUSTD_MENUBAR_SOCK"], source: .observerEnvironment)

        // 4. The normal fixed host domain. Include it even while absent so the
        // UI reports one actionable path instead of asking users to hunt through
        // Cargo target directories that are no longer authority boundaries.
        add(
            hostSocketPath(
                effectiveUserID: effectiveUserID,
                systemTemporaryDirectory: systemTemporaryDirectory
            ),
            source: .hostRuntime
        )
        return out
    }

    static func probe(stickySocket: String?, configuredSocketPath: String?) -> SocketProbeSummary {
        var candidates = [SocketCandidate]()
        var seen = Set<String>()
        func add(_ candidate: SocketCandidate?) {
            guard let candidate else { return }
            let path = candidate.path
            guard !path.isEmpty, !seen.contains(path) else { return }
            seen.insert(path)
            candidates.append(candidate)
        }
        add(stickySocket.map { SocketCandidate(path: $0, source: .lastConnected) })
        for candidate in candidateSockets(configuredSocketPath: configuredSocketPath) {
            add(candidate)
        }

        var firstFailure: SocketProbeAttempt?
        for candidate in candidates {
            switch UnixSocketClient.probeStatus(candidate.path) {
            case let .compatible(status):
                return SocketProbeSummary(
                    status: status,
                    socketPath: candidate.path,
                    attempted: candidates.firstIndex(of: candidate).map { $0 + 1 } ?? 1,
                    reportedAttempt: SocketProbeAttempt(
                        candidate: candidate,
                        outcome: .compatible(version: status.version)
                    )
                )
            case let .failed(failure):
                if firstFailure == nil {
                    firstFailure = SocketProbeAttempt(candidate: candidate, outcome: .failed(failure))
                }
            }
        }
        return SocketProbeSummary(
            status: nil,
            socketPath: nil,
            attempted: candidates.count,
            reportedAttempt: firstFailure
        )
    }
}

/// Observable poller bound by the SwiftUI menu. One guarded task owns the whole
/// lifecycle; socket and filesystem work is detached so a stalled endpoint
/// cannot freeze menu interaction or the Guided Tour.
@MainActor
final class StatusPoller: ObservableObject {
    @Published private(set) var status: DaemonStatus?
    @Published private(set) var socketPath: String?
    @Published private(set) var lastUpdate: Date?
    @Published private(set) var lastProbe: SocketProbeAttempt?
    @Published private(set) var lastProbeAt: Date?
    @Published private(set) var connectionState: CoordinatorConnectionState = .checking
    @Published private(set) var configuredSocketPath: String?

    var isRunning: Bool { connectionState == .connected && status != nil }

    var diagnosticsText: String {
        let formatter = ISO8601DateFormatter()
        let state: String
        switch connectionState {
        case .checking:
            state = "checking"
        case .connected:
            state = "connected"
        case .noCandidates:
            state = "no_candidates"
        case let .failed(failure, attempted):
            state = "failed:\(failure.diagnosticCode):attempted=\(attempted)"
        }
        var lines = [
            "Trustd Monitor diagnostics",
            "observer=read_only",
            "bundled_toolchain=false",
            "authority_scope=per_euid_host_domain_participants",
            "machine_wide_rss_bound=false",
            "expected_protocol=\(DaemonStatus.expectedVersion)",
            "state=\(state)",
            "standard_socket=\(SocketDiscovery.hostSocketPath())",
            "configured_socket=\(configuredSocketPath ?? "none")",
            "connected_socket=\(socketPath ?? "none")",
            "last_success=\(lastUpdate.map { formatter.string(from: $0) } ?? "never")",
            "last_probe=\(lastProbeAt.map { formatter.string(from: $0) } ?? "never")",
        ]
        if let lastProbe {
            lines.append("probe_source=\(lastProbe.candidate.source.rawValue)")
            lines.append("probe_path=\(lastProbe.candidate.path)")
            lines.append("probe_outcome=\(lastProbe.outcome.diagnosticCode)")
        }
        return lines.joined(separator: "\n") + "\n"
    }

    private let intervalNanoseconds: UInt64 = 1_500_000_000
    private let defaults: UserDefaults
    private let probeFunction: @Sendable (String?, String?) -> SocketProbeSummary
    private var resolvedSocket: String?
    private var pollingTask: Task<Void, Never>?
    private var activeProbeTask: Task<SocketProbeSummary, Never>?
    private var pollingGeneration: UInt64 = 0

    init(
        defaults: UserDefaults = .standard,
        probeFunction: @escaping @Sendable (String?, String?) -> SocketProbeSummary = {
            stickySocket, configuredSocketPath in
            SocketDiscovery.probe(
                stickySocket: stickySocket,
                configuredSocketPath: configuredSocketPath
            )
        }
    ) {
        self.defaults = defaults
        self.probeFunction = probeFunction
        configuredSocketPath = SocketDiscovery.normalizeConfiguredPath(
            defaults.string(forKey: SocketDiscovery.configuredSocketDefaultsKey)
        )
    }

    /// Start exactly one polling lifecycle. Returning whether a task was created
    /// makes the idempotence contract directly testable.
    @discardableResult
    func start() -> Bool {
        guard pollingTask == nil else { return false }
        pollingGeneration &+= 1
        let generation = pollingGeneration
        pollingTask = Task { [weak self] in
            await self?.runPollingLoop(generation: generation)
        }
        return true
    }

    func stop() {
        pollingGeneration &+= 1
        pollingTask?.cancel()
        activeProbeTask?.cancel()
        pollingTask = nil
        activeProbeTask = nil
    }

    @discardableResult
    func saveConfiguredSocketPath(_ rawPath: String) -> Bool {
        guard let normalized = SocketDiscovery.normalizeConfiguredPath(rawPath) else {
            return false
        }
        defaults.set(normalized, forKey: SocketDiscovery.configuredSocketDefaultsKey)
        configuredSocketPath = normalized
        restartAfterConfigurationChange()
        return true
    }

    func clearConfiguredSocketPath() {
        defaults.removeObject(forKey: SocketDiscovery.configuredSocketDefaultsKey)
        configuredSocketPath = nil
        restartAfterConfigurationChange()
    }

    /// Cancel any in-flight generation and probe immediately. This does not
    /// start or stop trustd; it only refreshes the observer.
    func retryNow() {
        resetAndRestart(forceStart: true)
    }

    func testSocketPath(_ rawPath: String) async -> SocketPathTestResult {
        guard let normalized = SocketDiscovery.normalizeConfiguredPath(rawPath) else {
            return .invalidPath
        }
        let result = await Task.detached(priority: .utility) {
            UnixSocketClient.probeStatus(normalized)
        }.value
        switch result {
        case let .compatible(status):
            return .compatible(version: status.version)
        case let .failed(failure):
            return .failed(failure)
        }
    }

    private func restartAfterConfigurationChange() {
        resetAndRestart(forceStart: false)
    }

    private func resetAndRestart(forceStart: Bool) {
        let shouldStart = forceStart || pollingTask != nil
        stop()
        status = nil
        socketPath = nil
        resolvedSocket = nil
        lastProbe = nil
        lastProbeAt = nil
        connectionState = .checking
        if shouldStart { _ = start() }
    }

    private func runPollingLoop(generation: UInt64) async {
        while !Task.isCancelled && generation == pollingGeneration {
            await pollOnce(generation: generation)
            do {
                try await Task.sleep(nanoseconds: intervalNanoseconds)
            } catch {
                break
            }
        }
    }

    private func pollOnce(generation: UInt64) async {
        let stickySocket = resolvedSocket
        let configuredPath = configuredSocketPath
        let probeFunction = self.probeFunction
        let probe = Task.detached(priority: .utility) {
            probeFunction(stickySocket, configuredPath)
        }
        activeProbeTask = probe
        let summary = await probe.value
        guard !Task.isCancelled, generation == pollingGeneration else { return }
        activeProbeTask = nil
        lastProbe = summary.reportedAttempt
        lastProbeAt = Date()

        if let status = summary.status, let socket = summary.socketPath {
            self.status = status
            socketPath = socket
            resolvedSocket = socket
            lastUpdate = Date()
            connectionState = .connected
            return
        }

        status = nil
        socketPath = nil
        resolvedSocket = nil
        if summary.attempted == 0 {
            connectionState = .noCandidates
        } else if let attempt = summary.reportedAttempt,
                  case let .failed(failure) = attempt.outcome {
            connectionState = .failed(failure, attempted: summary.attempted)
        } else {
            connectionState = .failed(.ioFailure(0), attempted: summary.attempted)
        }
    }
}
