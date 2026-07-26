// TrustdMenubar deterministic contracts. This is a command-line harness, not
// an app bundle or UI test target.

import Foundation
import Darwin
import Dispatch

private enum SocketFixtureError: Error {
    case socket(Int32)
    case pathTooLong
    case bind(Int32)
    case listen(Int32)
}

/// Serve one raw response on a same-user AF_UNIX endpoint. This exercises the
/// production connect/deadline/peer-credential/framing path without trustd.
private func withUnixSocketResponse<T>(
    _ response: [UInt8],
    byteDelayMicroseconds: useconds_t = 0,
    body: (String) throws -> T
) throws -> T {
    let path = "/tmp/tdm-\(ProcessInfo.processInfo.processIdentifier)-\(UInt32.random(in: 0...UInt32.max)).sock"
    let listener = socket(AF_UNIX, SOCK_STREAM, 0)
    guard listener >= 0 else { throw SocketFixtureError.socket(errno) }
    _ = unlink(path)

    var address = sockaddr_un()
    address.sun_family = sa_family_t(AF_UNIX)
    let pathBytes = Array(path.utf8)
    let capacity = MemoryLayout.size(ofValue: address.sun_path)
    guard pathBytes.count < capacity else {
        close(listener)
        throw SocketFixtureError.pathTooLong
    }
    withUnsafeMutablePointer(to: &address.sun_path) { rawPointer in
        rawPointer.withMemoryRebound(to: CChar.self, capacity: capacity) { destination in
            for (index, byte) in pathBytes.enumerated() {
                destination[index] = CChar(bitPattern: byte)
            }
            destination[pathBytes.count] = 0
        }
    }
    let bindResult = withUnsafePointer(to: &address) { pointer -> Int32 in
        pointer.withMemoryRebound(to: sockaddr.self, capacity: 1) { socketAddress in
            Darwin.bind(listener, socketAddress, socklen_t(MemoryLayout<sockaddr_un>.size))
        }
    }
    guard bindResult == 0 else {
        let bindError = errno
        close(listener)
        throw SocketFixtureError.bind(bindError)
    }
    guard Darwin.listen(listener, 1) == 0 else {
        let listenError = errno
        close(listener)
        _ = unlink(path)
        throw SocketFixtureError.listen(listenError)
    }

    let finished = DispatchSemaphore(value: 0)
    Thread.detachNewThread {
        defer {
            close(listener)
            _ = unlink(path)
            finished.signal()
        }
        let peer = Darwin.accept(listener, nil, nil)
        guard peer >= 0 else { return }
        defer { close(peer) }
        var noSigPipe: Int32 = 1
        _ = setsockopt(
            peer,
            SOL_SOCKET,
            SO_NOSIGPIPE,
            &noSigPipe,
            socklen_t(MemoryLayout<Int32>.size)
        )
        for value in response {
            var byte = value
            let written = withUnsafePointer(to: &byte) { Darwin.write(peer, $0, 1) }
            if written != 1 { break }
            if byteDelayMicroseconds > 0 { usleep(byteDelayMicroseconds) }
        }
    }

    defer { finished.wait() }
    return try body(path)
}

@MainActor
private final class TestRunner {
    private var failures = 0

    func expect(_ condition: @autoclosure () -> Bool, _ message: String) {
        if condition() {
            print("ok - \(message)")
        } else {
            failures += 1
            fputs("not ok - \(message)\n", stderr)
        }
    }

    func expectThrows(_ message: String, _ operation: () throws -> Void) {
        do {
            try operation()
            expect(false, message)
        } catch {
            expect(true, message)
        }
    }

    func finish() -> Never? {
        if failures == 0 {
            print("all TrustdMenubar contract tests passed")
            return nil
        }
        fputs("\(failures) TrustdMenubar contract test(s) failed\n", stderr)
        exit(1)
    }
}

@main
struct ContractTests {
    @MainActor
    static func main() async {
        let test = TestRunner()

        let validStatus = """
        {"version":"trustd.status.v1","budget_bytes":100,"reserved_bytes":0,"free_bytes":100,"queue_depth":0,"granted_total":2,"released_total":2,"started_at":1,"active":[]}
        """
        if case let .compatible(status) = UnixSocketClient.decodeStatusLine(validStatus) {
            test.expect(status.version == DaemonStatus.expectedVersion, "exact STATUS schema is accepted")
            test.expect(status.free_bytes == 100, "STATUS payload is decoded")
        } else {
            test.expect(false, "exact STATUS schema is accepted")
        }

        let futureStatus = validStatus.replacingOccurrences(
            of: "trustd.status.v1",
            with: "trustd.status.v2"
        )
        if case let .failed(.incompatibleVersion(version)) = UnixSocketClient.decodeStatusLine(futureStatus) {
            test.expect(version == "trustd.status.v2", "incompatible STATUS schema fails closed")
        } else {
            test.expect(false, "incompatible STATUS schema fails closed")
        }
        test.expect(
            UnixSocketClient.decodeStatusLine("{not-json") == .failed(.malformedResponse),
            "malformed STATUS fails closed"
        )
        let extraTopLevel = validStatus.replacingOccurrences(
            of: "\"active\":[]}",
            with: "\"active\":[],\"unexpected\":true}"
        )
        test.expect(
            UnixSocketClient.decodeStatusLine(extraTopLevel) == .failed(.malformedResponse),
            "unknown top-level STATUS fields fail closed"
        )
        let activeStatus = """
        {"version":"trustd.status.v1","budget_bytes":100,"reserved_bytes":25,"free_bytes":75,"queue_depth":0,"granted_total":1,"released_total":0,"started_at":1,"active":[{"pid":1,"bytes":25,"label":"worker","since_secs":1,"token":1}]}
        """
        test.expect(
            {
                if case .compatible = UnixSocketClient.decodeStatusLine(activeStatus) { return true }
                return false
            }(),
            "semantically consistent active reservation is accepted"
        )
        let extraActiveField = activeStatus.replacingOccurrences(
            of: "\"token\":1}",
            with: "\"token\":1,\"unexpected\":true}"
        )
        test.expect(
            UnixSocketClient.decodeStatusLine(extraActiveField) == .failed(.malformedResponse),
            "unknown active-reservation fields fail closed"
        )
        let inconsistentFree = activeStatus.replacingOccurrences(
            of: "\"free_bytes\":75",
            with: "\"free_bytes\":74"
        )
        test.expect(
            UnixSocketClient.decodeStatusLine(inconsistentFree) == .failed(.malformedResponse),
            "inconsistent budget arithmetic fails closed"
        )
        let overcommittedStatus = """
        {"version":"trustd.status.v1","budget_bytes":100,"reserved_bytes":125,"free_bytes":0,"queue_depth":0,"granted_total":1,"released_total":0,"started_at":1,"active":[{"pid":1,"bytes":125,"label":"ceiling-lowered","since_secs":1,"token":1}]}
        """
        test.expect(
            {
                if case let .compatible(status) = UnixSocketClient.decodeStatusLine(overcommittedStatus) {
                    return status.fillFraction == 1 && status.isOvercommitted
                }
                return false
            }(),
            "a lowered ceiling preserves live grants and saturates free capacity at zero"
        )
        let zeroByteReservation = activeStatus.replacingOccurrences(
            of: "\"bytes\":25",
            with: "\"bytes\":0"
        ).replacingOccurrences(
            of: "\"reserved_bytes\":25",
            with: "\"reserved_bytes\":0"
        ).replacingOccurrences(
            of: "\"free_bytes\":75",
            with: "\"free_bytes\":100"
        )
        test.expect(
            UnixSocketClient.decodeStatusLine(zeroByteReservation) == .failed(.malformedResponse),
            "zero-byte active grants fail closed"
        )
        test.expect(
            UnixSocketClient.decodeStatusBytes([0x7b, 0xff, 0x7d]) == .failed(.malformedResponse),
            "invalid UTF-8 STATUS bytes fail closed"
        )
        test.expectThrows("response framing requires a newline") {
            _ = try UnixSocketClient.finalizeResponseBytes(
                Array(validStatus.utf8),
                sawNewline: false
            )
        }
        test.expectThrows("response framing enforces its byte ceiling") {
            _ = try UnixSocketClient.finalizeResponseBytes(
                Array(repeating: 0x20, count: 9),
                sawNewline: true,
                maxBytes: 8
            )
        }
        do {
            let liveLine = try withUnixSocketResponse(Array(validStatus.utf8) + [0x0a]) { path in
                try UnixSocketClient.send(request: "STATUS\n", to: path, timeoutSeconds: 0.5)
            }
            test.expect(liveLine == validStatus, "live same-user Unix socket response is framed")
        } catch {
            test.expect(false, "live same-user Unix socket response is framed: \(error)")
        }
        do {
            _ = try withUnixSocketResponse(
                [0x7b, 0x20, 0x20, 0x20],
                byteDelayMicroseconds: 40_000
            ) { path in
                try UnixSocketClient.send(request: "STATUS\n", to: path, timeoutSeconds: 0.05)
            }
            test.expect(false, "drip-fed response is bounded by one total deadline")
        } catch UnixSocketClient.ClientError.timedOut {
            test.expect(true, "drip-fed response is bounded by one total deadline")
        } catch {
            test.expect(false, "drip-fed response uses deadline classification: \(error)")
        }

        test.expect(
            SocketDiscovery.normalizeConfiguredPath(
                "~/custom/trustd.sock",
                homeDirectory: "/var/example-home"
            ) == "/var/example-home/custom/trustd.sock",
            "tilde path expands deterministically"
        )
        test.expect(
            SocketDiscovery.normalizeConfiguredPath(
                "relative/trustd.sock",
                homeDirectory: "/var/example-home"
            ) == nil,
            "ambiguous relative path is rejected"
        )
        test.expect(
            SocketDiscovery.hostSocketPath(
                effectiveUserID: 501,
                systemTemporaryDirectory: "/private/tmp"
            ) == "/private/tmp/trustd-runtime-locks-501/trust-memory-jobserver.sock",
            "effective user ID derives the fixed canonical host endpoint"
        )

        let classifiedPath = "/tmp/tdm-classify-\(ProcessInfo.processInfo.processIdentifier)"
        _ = unlink(classifiedPath)
        test.expect(
            UnixSocketClient.probeStatus(classifiedPath) == .failed(.missing),
            "missing socket remains an actionable failure"
        )
        _ = FileManager.default.createFile(atPath: classifiedPath, contents: Data("not a socket".utf8))
        test.expect(
            UnixSocketClient.probeStatus(classifiedPath) == .failed(.notSocket),
            "regular file is distinguished from an unavailable socket"
        )
        _ = unlink(classifiedPath)

        let candidates = SocketDiscovery.candidateSockets(
            configuredSocketPath: "~/saved.sock",
            environment: [
                "TRUST_MEMORY_JOBSERVER_SOCK": "/tmp/worker.sock",
                "TRUST_MEMORY_JOBSERVER": "/tmp/build.tokens",
                "TRUSTD_MENUBAR_SOCK": "/tmp/worker.sock",
            ],
            homeDirectory: "/var/example-home",
            effectiveUserID: 501,
            systemTemporaryDirectory: "/private/tmp"
        )
        test.expect(candidates.first?.path == "/var/example-home/saved.sock", "saved path has first precedence")
        test.expect(candidates.first?.source == .configured, "saved path retains its discovery source")
        test.expect(candidates.dropFirst().first?.path == "/tmp/worker.sock", "worker environment is second")
        test.expect(
            candidates.contains {
                $0.path == "/private/tmp/trustd-runtime-locks-501/trust-memory-jobserver.sock"
                    && $0.source == .hostRuntime
            },
            "normal host authority is always a discovery candidate"
        )
        test.expect(
            candidates.filter { $0.path == "/tmp/worker.sock" }.count == 1,
            "candidate paths are de-duplicated"
        )

        test.expect(
            !candidates.contains { $0.path == "/tmp/trust-memory-jobserver.sock" },
            "obsolete token-sibling domains are not auto-discovered"
        )

        let automaticCandidates = SocketDiscovery.candidateSockets(
            configuredSocketPath: nil,
            environment: [:],
            homeDirectory: "/var/example-home",
            effectiveUserID: 502,
            systemTemporaryDirectory: "/private/tmp"
        )
        test.expect(
            automaticCandidates == [
                SocketCandidate(
                    path: "/private/tmp/trustd-runtime-locks-502/trust-memory-jobserver.sock",
                    source: .hostRuntime
                )
            ],
            "Finder-safe discovery needs no saved path or filesystem scan"
        )

        let suiteName = "name.andrewyates.trustd-menubar.contract-tests.\(ProcessInfo.processInfo.processIdentifier)"
        guard let defaults = UserDefaults(suiteName: suiteName) else {
            test.expect(false, "isolated UserDefaults suite is available")
            _ = test.finish()
            return
        }
        defaults.removePersistentDomain(forName: suiteName)
        let poller = StatusPoller(defaults: defaults)
        test.expect(poller.start(), "first poller start creates a lifecycle")
        test.expect(!poller.start(), "second poller start is idempotent")
        poller.stop()
        test.expect(poller.start(), "poller can restart after stop")
        poller.stop()
        poller.retryNow()
        test.expect(!poller.start(), "Retry Now preserves the single polling lifecycle")
        poller.stop()

        test.expect(poller.saveConfiguredSocketPath("~/saved.sock"), "valid configured path saves")
        test.expect(
            poller.configuredSocketPath?.hasSuffix("/saved.sock") == true,
            "saved path is published"
        )
        test.expect(
            poller.diagnosticsText.contains("bundled_toolchain=false"),
            "copied diagnostics state the standalone observer boundary"
        )
        test.expect(
            poller.diagnosticsText.contains("authority_scope=per_euid_host_domain_participants")
                && poller.diagnosticsText.contains("machine_wide_rss_bound=false")
                && poller.diagnosticsText.contains("standard_socket="),
            "copied diagnostics state the host-domain, non-RSS authority boundary"
        )
        poller.clearConfiguredSocketPath()
        test.expect(poller.configuredSocketPath == nil, "automatic discovery clears saved path")
        let relativePathResult = await poller.testSocketPath("relative.sock")
        test.expect(
            relativePathResult == .invalidPath,
            "connection test rejects a relative path before I/O"
        )
        poller.stop()

        let connectedStatus = DaemonStatus(
            version: DaemonStatus.expectedVersion,
            budget_bytes: 100,
            reserved_bytes: 0,
            free_bytes: 100,
            queue_depth: 0,
            granted_total: 0,
            released_total: 0,
            started_at: 1,
            active: []
        )
        let transitionPoller = StatusPoller(defaults: defaults) { _, configured in
            if configured == nil {
                return SocketProbeSummary(
                    status: connectedStatus,
                    socketPath: "/tmp/old.sock",
                    attempted: 1,
                    reportedAttempt: SocketProbeAttempt(
                        candidate: SocketCandidate(path: "/tmp/old.sock", source: .configured),
                        outcome: .compatible(version: DaemonStatus.expectedVersion)
                    )
                )
            }
            Thread.sleep(forTimeInterval: 0.05)
            return SocketProbeSummary(
                status: nil,
                socketPath: nil,
                attempted: 1,
                reportedAttempt: SocketProbeAttempt(
                    candidate: SocketCandidate(path: configured ?? "/tmp/new.sock", source: .configured),
                    outcome: .failed(.missing)
                )
            )
        }
        _ = transitionPoller.start()
        try? await Task.sleep(nanoseconds: 30_000_000)
        test.expect(transitionPoller.isRunning, "fixture reaches a connected snapshot")
        test.expect(
            transitionPoller.saveConfiguredSocketPath("/tmp/new.sock"),
            "configuration change is accepted"
        )
        test.expect(
            transitionPoller.status == nil && transitionPoller.connectionState == .checking,
            "configuration restart clears the stale connected snapshot immediately"
        )
        try? await Task.sleep(nanoseconds: 100_000_000)
        test.expect(!transitionPoller.isRunning, "failed reconnect remains truthfully offline")
        transitionPoller.stop()

        defaults.removeObject(forKey: SocketDiscovery.configuredSocketDefaultsKey)
        let generationPoller = StatusPoller(defaults: defaults) { _, configured in
            if configured == nil {
                Thread.sleep(forTimeInterval: 0.15)
                return SocketProbeSummary(
                    status: connectedStatus,
                    socketPath: "/tmp/stale.sock",
                    attempted: 1,
                    reportedAttempt: SocketProbeAttempt(
                        candidate: SocketCandidate(path: "/tmp/stale.sock", source: .lastConnected),
                        outcome: .compatible(version: DaemonStatus.expectedVersion)
                    )
                )
            }
            return SocketProbeSummary(
                status: nil,
                socketPath: nil,
                attempted: 1,
                reportedAttempt: SocketProbeAttempt(
                    candidate: SocketCandidate(
                        path: configured ?? "/tmp/restarted.sock",
                        source: .configured
                    ),
                    outcome: .failed(.missing)
                )
            )
        }
        _ = generationPoller.start()
        try? await Task.sleep(nanoseconds: 20_000_000)
        _ = generationPoller.saveConfiguredSocketPath("/tmp/restarted.sock")
        try? await Task.sleep(nanoseconds: 220_000_000)
        test.expect(
            generationPoller.status == nil && !generationPoller.isRunning,
            "a cancelled older probe cannot publish into a newer configuration generation"
        )
        generationPoller.stop()
        defaults.removePersistentDomain(forName: suiteName)

        _ = test.finish()
    }
}
