// Trust: TrustdMenubar — STATUS wire model + Unix-socket client.
//
// Codable mirror of the frozen `trustd.status.v1` JSON schema (FINAL SPEC §2)
// plus a dependency-free POSIX AF_UNIX stream client. This file is the Swift
// side of the single wire contract; field names/types MUST match the daemon's
// `coordinator::DaemonStatus`/`ActiveReservation` serde structs exactly, or the
// JSONDecoder below will throw and the menubar reports an invalid endpoint.
//
// Read-only by construction: the client only ever writes the `STATUS\n` /
// `PING\n` probes — never `RESERVE`/`RELEASE` — so the observer can never
// perturb admission (FINAL SPEC, observer-cannot-perturb rule).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

import Foundation
import Darwin
import Dispatch

// MARK: - Wire model (trustd.status.v1)

/// One live reservation row, mirroring the `active[]` objects in STATUS JSON.
/// All byte/count fields decode as `UInt64` to be exact at RAM scale.
struct ActiveReservation: Codable, Identifiable, Equatable, Sendable {
    let pid: UInt32
    let bytes: UInt64
    let label: String
    let since_secs: UInt64
    let token: UInt64

    /// Stable identity for SwiftUI lists: the server-minted token is unique
    /// per live grant.
    var id: UInt64 { token }
}

/// Typed mirror of the one-line STATUS JSON object. Field names are frozen and
/// match `coordinator::DaemonStatus`.
struct DaemonStatus: Codable, Equatable, Sendable {
    static let expectedVersion = "trustd.status.v1"

    let version: String
    let budget_bytes: UInt64
    let reserved_bytes: UInt64
    let free_bytes: UInt64
    let queue_depth: UInt64
    let granted_total: UInt64
    let released_total: UInt64
    let started_at: UInt64
    let active: [ActiveReservation]

    /// Fraction of this daemon's current ceiling reserved, clamped to [0, 1].
    /// A zero ceiling with retained grants reports full while it drains.
    var fillFraction: Double {
        guard budget_bytes > 0 else { return reserved_bytes > 0 ? 1 : 0 }
        let f = Double(reserved_bytes) / Double(budget_bytes)
        return min(max(f, 0), 1)
    }

    /// Whether this daemon reports a nonzero configured allowance. `false` ⇒
    /// the daemon is up but its local admission ledger is disabled.
    var budgetEnabled: Bool { budget_bytes > 0 }

    /// Existing reservations can temporarily exceed a newly lowered ceiling;
    /// the daemon admits nothing else while this is true.
    var isOvercommitted: Bool { reserved_bytes > budget_bytes }
}

// MARK: - Byte / time formatting

enum Format {
    /// Human bytes in GiB with one decimal (RAM-scale values). The daemon emits
    /// raw bytes; all GiB conversion happens here, per the schema note.
    static func gib(_ bytes: UInt64) -> String {
        let g = Double(bytes) / 1_073_741_824.0
        if g >= 100 { return String(format: "%.0f GiB", g) }
        return String(format: "%.1f GiB", g)
    }

    /// Compact MiB for per-worker held memory (smaller magnitudes read better
    /// in MiB, matching the daemon's `--memory <mb>` vocabulary).
    static func mib(_ bytes: UInt64) -> String {
        let m = Double(bytes) / 1_048_576.0
        if m >= 1024 { return gib(bytes) }
        return String(format: "%.0f MiB", m)
    }

    static func percent(_ frac: Double) -> String {
        String(format: "%.0f%%", frac * 100)
    }

    /// Coarse human duration from a whole-seconds count (uptime / since).
    static func duration(_ secs: UInt64) -> String {
        if secs < 60 { return "\(secs)s" }
        let m = secs / 60
        if m < 60 { return "\(m)m \(secs % 60)s" }
        let h = m / 60
        if h < 24 { return "\(h)h \(m % 60)m" }
        let d = h / 24
        return "\(d)d \(h % 24)h"
    }
}

// MARK: - POSIX AF_UNIX stream client (no external deps)

/// Minimal, blocking, dependency-free Unix-domain-socket client used to probe
/// the daemon's line-oriented protocol (FINAL SPEC §1: AF_UNIX stream socket,
/// newline-framed). One request, one response line, then close — matching the
/// daemon's per-connection handling. A short send/receive timeout keeps the
/// poller's UI thread responsive even if the daemon stalls.
enum UnixSocketClient {

    enum ClientError: Error, Sendable {
        case socketCreateFailed(Int32)
        case socketSetupFailed(Int32)
        case pathTooLong
        case connectFailed(Int32)
        case peerCredentialFailed(Int32)
        case peerUIDMismatch(uid_t)
        case pollFailed(Int32)
        case timedOut
        case cancelled
        case writeFailed(Int32)
        case readFailed(Int32)
        case noResponse
        case unterminatedResponse
        case responseTooLarge
        case invalidUTF8
    }

    /// Actionable, stable failure categories retained through discovery and UI.
    /// These deliberately distinguish setup/lifecycle failures from an
    /// untrusted peer or a protocol-contract violation.
    enum EndpointFailure: Sendable, Equatable {
        case missing
        case notSocket
        case connectionRefused
        case permissionDenied
        case timedOut
        case untrustedPeer(uid: UInt32?)
        case pathTooLong
        case incompatibleVersion(String)
        case malformedResponse
        case cancelled
        case ioFailure(Int32)

        var diagnosticCode: String {
            switch self {
            case .missing: return "missing"
            case .notSocket: return "not_socket"
            case .connectionRefused: return "connection_refused"
            case .permissionDenied: return "permission_denied"
            case .timedOut: return "timeout"
            case let .untrustedPeer(uid): return "untrusted_peer:\(uid.map(String.init) ?? "unknown")"
            case .pathTooLong: return "path_too_long"
            case let .incompatibleVersion(version): return "incompatible_protocol:\(version)"
            case .malformedResponse: return "malformed_status"
            case .cancelled: return "cancelled"
            case let .ioFailure(code): return "io_error:\(code)"
            }
        }

        var title: String {
            switch self {
            case .missing: return "Socket not found"
            case .notSocket: return "Path is not a socket"
            case .connectionRefused: return "Coordinator is idle or stopped"
            case .permissionDenied: return "Socket access denied"
            case .timedOut: return "Coordinator timed out"
            case .untrustedPeer: return "Untrusted socket owner"
            case .pathTooLong: return "Socket path is too long"
            case .incompatibleVersion: return "Incompatible coordinator"
            case .malformedResponse: return "Invalid STATUS response"
            case .cancelled: return "Probe cancelled"
            case .ioFailure: return "Socket I/O failed"
            }
        }

        var detail: String {
            switch self {
            case .missing:
                return "No socket exists at this path. Run `targo trust check` in any Trust crate, then retry the standard per-user endpoint."
            case .notSocket:
                return "The path exists but is not a Unix socket. Clear any saved override so automatic per-user discovery can resume."
            case .connectionRefused:
                return "trustd may have shut down cleanly after being idle, or it may be refusing automatic restart after an unclean exit. Retry a crate build; if it remains offline, use the safety-qualified recovery steps in Guided Tour."
            case .permissionDenied:
                return "This user cannot access the socket or one of its parent folders. Choose a socket owned by your account."
            case let .untrustedPeer(uid):
                if let uid {
                    return "The endpoint belongs to user ID \(uid), so the observer refused it."
                }
                return "The endpoint owner could not be authenticated, so the observer refused it."
            case .timedOut:
                return "The endpoint accepted a connection but did not complete a STATUS reply within the one-second deadline."
            case .pathTooLong:
                return "The explicit Unix-socket path exceeds macOS's address limit. Clear it to use Trust's short standard host endpoint."
            case let .incompatibleVersion(version):
                return "The endpoint reports \(version); this app requires \(DaemonStatus.expectedVersion)."
            case .malformedResponse:
                return "The endpoint answered, but its closed STATUS schema, framing, encoding, or arithmetic was invalid."
            case .cancelled:
                return "A newer configuration or retry replaced this probe."
            case let .ioFailure(code):
                return "The socket operation failed with errno \(code). Retry, then copy diagnostics if it persists."
            }
        }
    }

    /// A STATUS endpoint must both answer and advertise the exact frozen schema.
    enum StatusProbeResult: Sendable, Equatable {
        case compatible(DaemonStatus)
        case failed(EndpointFailure)
    }

    private static let statusKeys: Set<String> = [
        "version", "budget_bytes", "reserved_bytes", "free_bytes", "queue_depth",
        "granted_total", "released_total", "started_at", "active",
    ]
    private static let activeReservationKeys: Set<String> = [
        "pid", "bytes", "label", "since_secs", "token",
    ]

    /// Wait for a nonblocking descriptor using one absolute monotonic deadline.
    /// A peer that drip-feeds bytes cannot reset this budget on every read.
    private static func waitFor(
        fd: Int32,
        events: Int16,
        deadlineNanoseconds: UInt64
    ) throws {
        while true {
            if Task.isCancelled { throw ClientError.cancelled }
            let now = DispatchTime.now().uptimeNanoseconds
            guard now < deadlineNanoseconds else { throw ClientError.timedOut }
            let remaining = deadlineNanoseconds - now
            let roundedMilliseconds = (remaining + 999_999) / 1_000_000
            let timeout = Int32(min(roundedMilliseconds, UInt64(Int32.max)))
            var descriptor = pollfd(fd: fd, events: events, revents: 0)
            let result = Darwin.poll(&descriptor, 1, timeout)
            if result > 0 {
                if descriptor.revents & events != 0 { return }
                if descriptor.revents & Int16(POLLERR | POLLHUP | POLLNVAL) != 0 {
                    // Let the pending connect/read/write recover the precise
                    // socket error (or EOF) rather than inventing one here.
                    return
                }
                continue
            }
            if result == 0 { throw ClientError.timedOut }
            if errno != EINTR { throw ClientError.pollFailed(errno) }
        }
    }

    /// Validate the framing and encoding of one collected response line. Kept
    /// separate from socket I/O so malformed-peer behavior is regression-tested.
    static func finalizeResponseBytes(
        _ bytes: [UInt8],
        sawNewline: Bool,
        maxBytes: Int = 1 << 20
    ) throws -> String {
        guard bytes.count <= maxBytes else { throw ClientError.responseTooLarge }
        guard !bytes.isEmpty else { throw ClientError.noResponse }
        guard sawNewline else { throw ClientError.unterminatedResponse }
        guard let response = String(bytes: bytes, encoding: .utf8) else {
            throw ClientError.invalidUTF8
        }
        return response
    }

    /// Connect to `path`, send `request` (a single newline-terminated line),
    /// and return the first response line (without the trailing newline).
    /// Throws on any connect/IO failure so the caller can render "unavailable".
    static func send(request: String, to path: String, timeoutSeconds: Double = 1.0) throws -> String {
        // AF_UNIX stream socket.
        let fd = socket(AF_UNIX, SOCK_STREAM, 0)
        if fd < 0 { throw ClientError.socketCreateFailed(errno) }
        defer { close(fd) }

        // One total deadline covers connect + write + the complete framed read.
        // Use nonblocking I/O so no individual syscall can exceed it.
        let boundedSeconds = timeoutSeconds.isFinite ? max(0.001, timeoutSeconds) : 1.0
        let budgetNanoseconds = UInt64(min(boundedSeconds * 1_000_000_000, 60_000_000_000))
        let start = DispatchTime.now().uptimeNanoseconds
        let deadline = start.addingReportingOverflow(budgetNanoseconds).overflow
            ? UInt64.max
            : start + budgetNanoseconds
        let descriptorFlags = fcntl(fd, F_GETFL)
        guard descriptorFlags >= 0,
              fcntl(fd, F_SETFL, descriptorFlags | O_NONBLOCK) == 0
        else {
            throw ClientError.socketSetupFailed(errno)
        }

        // A peer can disappear between connect and write. Suppress SIGPIPE so
        // that race becomes a normal write error instead of terminating the app.
        var noSigPipe: Int32 = 1
        guard setsockopt(
                  fd,
                  SOL_SOCKET,
                  SO_NOSIGPIPE,
                  &noSigPipe,
                  socklen_t(MemoryLayout<Int32>.size)
              ) == 0
        else {
            throw ClientError.socketSetupFailed(errno)
        }

        // Build sockaddr_un. sun_path is a fixed C char array; bail if the path
        // would overflow it (a stale/huge target dir) rather than truncating.
        var addr = sockaddr_un()
        addr.sun_family = sa_family_t(AF_UNIX)
        let pathBytes = Array(path.utf8)
        let capacity = MemoryLayout.size(ofValue: addr.sun_path)
        if pathBytes.count >= capacity { throw ClientError.pathTooLong }
        withUnsafeMutablePointer(to: &addr.sun_path) { rawPtr in
            rawPtr.withMemoryRebound(to: CChar.self, capacity: capacity) { dst in
                for (i, b) in pathBytes.enumerated() { dst[i] = CChar(bitPattern: b) }
                dst[pathBytes.count] = 0
            }
        }

        let connectResult = withUnsafePointer(to: &addr) { aptr -> Int32 in
            aptr.withMemoryRebound(to: sockaddr.self, capacity: 1) { sa in
                connect(fd, sa, socklen_t(MemoryLayout<sockaddr_un>.size))
            }
        }
        if connectResult != 0 {
            let connectError = errno
            guard connectError == EINPROGRESS else {
                throw ClientError.connectFailed(connectError)
            }
            try waitFor(fd: fd, events: Int16(POLLOUT), deadlineNanoseconds: deadline)
            var socketError: Int32 = 0
            var socketErrorLength = socklen_t(MemoryLayout<Int32>.size)
            guard getsockopt(
                      fd,
                      SOL_SOCKET,
                      SO_ERROR,
                      &socketError,
                      &socketErrorLength
                  ) == 0
            else {
                throw ClientError.connectFailed(errno)
            }
            if socketError != 0 { throw ClientError.connectFailed(socketError) }
        }

        // Filesystem permissions are not peer authentication. Only trust a
        // daemon owned by the same effective user as this observer.
        var peerUID: uid_t = 0
        var peerGID: gid_t = 0
        guard getpeereid(fd, &peerUID, &peerGID) == 0 else {
            throw ClientError.peerCredentialFailed(errno)
        }
        guard peerUID == geteuid() else { throw ClientError.peerUIDMismatch(peerUID) }

        // Send the request line.
        let out = Array(request.utf8)
        var sent = 0
        while sent < out.count {
            let n = out.withUnsafeBytes { raw -> Int in
                write(fd, raw.baseAddress!.advanced(by: sent), out.count - sent)
            }
            if n > 0 {
                sent += n
                continue
            }
            if n < 0 && errno == EINTR { continue }
            if n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK) {
                try waitFor(fd: fd, events: Int16(POLLOUT), deadlineNanoseconds: deadline)
                continue
            }
            throw ClientError.writeFailed(errno)
        }

        // Read until newline (one response line). Bounded buffer; the STATUS
        // reply is one JSON line, well under this cap.
        var collected = [UInt8]()
        collected.reserveCapacity(8192)
        var chunk = [UInt8](repeating: 0, count: 8192)
        let maxBytes = 1 << 20 // 1 MiB hard ceiling, defensive.
        var sawNewline = false
        readLoop: while true {
            try waitFor(fd: fd, events: Int16(POLLIN), deadlineNanoseconds: deadline)
            let n = chunk.withUnsafeMutableBytes { raw -> Int in
                read(fd, raw.baseAddress!, raw.count)
            }
            if n < 0 && errno == EINTR { continue }
            if n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK) { continue }
            if n < 0 { throw ClientError.readFailed(errno) }
            if n == 0 { break } // peer closed.
            for i in 0..<n {
                if chunk[i] == 0x0A {
                    sawNewline = true
                    break readLoop
                }
                guard collected.count < maxBytes else {
                    throw ClientError.responseTooLarge
                }
                collected.append(chunk[i])
            }
        }
        return try finalizeResponseBytes(collected, sawNewline: sawNewline, maxBytes: maxBytes)
    }

    /// Liveness probe: returns true iff the daemon answers `PING` with `PONG`.
    static func ping(_ path: String) -> Bool {
        (try? send(request: "PING\n", to: path)) == "PONG"
    }

    /// Decode a STATUS line and require the exact frozen schema version.
    /// Exposed independently of socket I/O so the compatibility contract has a
    /// deterministic regression test.
    static func decodeStatusBytes(_ bytes: [UInt8]) -> StatusProbeResult {
        guard String(bytes: bytes, encoding: .utf8) != nil else {
            return .failed(.malformedResponse)
        }
        return decodeStatusData(Data(bytes))
    }

    static func decodeStatusLine(_ line: String) -> StatusProbeResult {
        decodeStatusData(Data(line.utf8))
    }

    private static func decodeStatusData(_ data: Data) -> StatusProbeResult {
        guard let rawObject = try? JSONSerialization.jsonObject(with: data),
              let object = rawObject as? [String: Any],
              Set(object.keys) == statusKeys,
              let activeObjects = object["active"] as? [[String: Any]],
              activeObjects.allSatisfy({ Set($0.keys) == activeReservationKeys }),
              let decoded = try? JSONDecoder().decode(DaemonStatus.self, from: data),
              statusInvariantsHold(decoded)
        else {
            return .failed(.malformedResponse)
        }
        guard decoded.version == DaemonStatus.expectedVersion else {
            return .failed(.incompatibleVersion(decoded.version))
        }
        return .compatible(decoded)
    }

    private static func statusInvariantsHold(_ status: DaemonStatus) -> Bool {
        var activeBytes: UInt64 = 0
        var tokens = Set<UInt64>()
        for reservation in status.active {
            let sum = activeBytes.addingReportingOverflow(reservation.bytes)
            if sum.overflow
                || reservation.bytes == 0
                || reservation.token == 0
                || !tokens.insert(reservation.token).inserted
            {
                return false
            }
            if reservation.label.utf8.count > 128 { return false }
            activeBytes = sum.partialValue
        }
        // A cgroup ceiling may be lowered below already-granted work. Existing
        // grants remain visible and free capacity saturates at zero until they
        // leave; rejecting that safe overcommitted snapshot would make the app
        // disagree with the documented Rust STATUS schema.
        let expectedFree = status.budget_bytes >= status.reserved_bytes
            ? status.budget_bytes - status.reserved_bytes
            : 0
        guard activeBytes == status.reserved_bytes,
              status.free_bytes == expectedFree,
              status.granted_total >= status.released_total,
              status.granted_total - status.released_total == UInt64(status.active.count)
        else {
            return false
        }
        return true
    }

    /// Fetch, decode, and version-check a STATUS object.
    static func probeStatus(_ path: String) -> StatusProbeResult {
        var metadata = stat()
        if lstat(path, &metadata) != 0 {
            let code = errno
            if code == ENOENT || code == ENOTDIR { return .failed(.missing) }
            if code == EACCES || code == EPERM { return .failed(.permissionDenied) }
            return .failed(.ioFailure(code))
        }
        guard metadata.st_mode & mode_t(S_IFMT) == mode_t(S_IFSOCK) else {
            return .failed(.notSocket)
        }

        do {
            return decodeStatusLine(try send(request: "STATUS\n", to: path))
        } catch let error as ClientError {
            switch error {
            case .pathTooLong:
                return .failed(.pathTooLong)
            case let .connectFailed(code) where code == ENOENT || code == ENOTDIR:
                return .failed(.missing)
            case let .connectFailed(code) where code == ECONNREFUSED:
                return .failed(.connectionRefused)
            case let .connectFailed(code) where code == EACCES || code == EPERM:
                return .failed(.permissionDenied)
            case .timedOut:
                return .failed(.timedOut)
            case .peerCredentialFailed:
                return .failed(.untrustedPeer(uid: nil))
            case let .peerUIDMismatch(uid):
                return .failed(.untrustedPeer(uid: UInt32(uid)))
            case .noResponse, .unterminatedResponse, .responseTooLarge, .invalidUTF8:
                return .failed(.malformedResponse)
            case .cancelled:
                return .failed(.cancelled)
            case let .socketCreateFailed(code),
                 let .socketSetupFailed(code),
                 let .connectFailed(code),
                 let .pollFailed(code),
                 let .writeFailed(code),
                 let .readFailed(code):
                return .failed(.ioFailure(code))
            }
        } catch {
            return .failed(.ioFailure(0))
        }
    }

    /// Compatibility-preserving convenience for callers that only need a
    /// snapshot. Incompatible and malformed endpoints fail closed.
    static func status(_ path: String) -> DaemonStatus? {
        guard case let .compatible(status) = probeStatus(path) else { return nil }
        return status
    }
}
