# Native proc-macro ABI forwarding over B1

This compiler-workspace crate implements the existing native `proc_macro`
`Server` interface using the existing B1 protocol. It depends on the exact
in-tree `rustc_proc_macro` source. It does not load a native library, launch a
process, send `Ready`, admit a provider, or change proof authority.

`Worker::from_begin` checks the compiler-issued invocation metadata and handle
shapes without recharging received wire bytes. `Worker::run_declared` selects
the compiler-issued `Begin.declaration` index from the supplied native `Client`
table, uses the native C ABI and forwards every one of the 32 methods. An absent
index refuses before any Client executes. The caller must establish that the
whole table belongs to the admitted immutable artifact before supplying it.
The binding fields alone authenticate
nothing. Normal native method errors remain typed results; protocol/resource/
transport failures are sticky, close the invocation transport and prevent a
successful Finish, even if macro code catches the native unwind. Native Drop
cleanup cannot introduce a second unwind after a transport failure.

The same Budget is used for framing, local ownership/sequence checks and DTO
storage. Compiler dispatch still checks its original Session, binding and
cumulative grant. Canonical compiler Span handles preserve the native ABI's
implicit Eq/Hash interning. Stream consumption is checked as a complete set;
result handles cannot reuse a live stream or resurrect a stale generation.

A Transport implementation must bound receive storage before reading, use the
original absolute deadline, interrupt blocked I/O and close without panicking.
The generic interface does not prove those properties. Native `proc_macro`
Buffer allocation, symbol storage, arbitrary macro code and allocator/unwind
intervals are outside B1's accounting and need the separately confined worker
and OS resource owner. No hard latency, RSS, containment or cross-process shared
memory guarantee follows from these in-process tests.

Compiler unit tests exercise the native Client/Buffer/Closure path, B1 encoded
bytes, the real compiler Dispatcher and the reverse reply path, including all
32 methods, native Span equality, consuming handles, errors and hostile replies.
The ordinary unit cases use in-memory duplex transport and synthetic clients.
The explicitly selected `real_proc_macro_dso_preserves_declared_client_and_native_tokens`
case also loads a real compiler-built two-entry proc-macro DSO in its disposable
child and runs the shared 32-method exercise through the real Dispatcher. It
checks both declaration indices, an absent symbol and out-of-range indices,
requiring Finish, EOF and successful child exit for acceptance. See the fixture
instructions under `compiler/rustc_expand/tests/fixtures/`. This is native ABI
and process qualification, not sandbox or production-loader admission.
On macOS the compiler now uses this crate in production under
`-Ztrust-proc-macro-isolation` (D21): `compiler/rustc_expand`'s
`proc_macro_server/isolation/launch.rs` starts the compiler's own executable in
its worker role (`worker.rs`), which closes inherited descriptors, installs
`trust_exec_policy::restrict_current_to_macro_worker` and only then opens the
dylib, so constructors run contained. One worker serves one dylib for the
session; each expansion is one B1 invocation on the same socket
(`UnixTransport::into_stream` hands the socket back without shutting it down),
and a nested expansion gets a second worker. `Worker::run_reported` reports a
macro panic to the compiler as `Failure` with a `panic` or `panic:<message>`
reason (`panic_reason`, `parse_panic_reason`) and returns
`Completion::Panicked`, so the compiler reports it exactly as an in-process
panic and the worker stays usable; `run_declared` keeps refusing a panic.
`tests/ui/trust/proc_macro_isolation` holds the end-to-end tests.

Immutable native runtime/artifact closure, source/environment consumption
receipts, graph-wide build-script/scoped-out-derive containment, a Linux
launcher, and rustdoc/full certification remain required. The option is refused
on a host without the macOS sandbox. PM-1 and all ordinary provider refusals
remain in force.

On Linux and macOS, `unix::UnixTransport` supplies the bounded byte transport for
an already-owned Unix socket for parent/trusted-fixture use. It establishes
`O_NONBLOCK` and verifies it with F_GETFL at construction/operation entry. The
exclusive owner and all aliases must preserve it; readback cannot prevent a
concurrent flag mutator. The transport also uses
`MSG_DONTWAIT` plus `MSG_NOSIGNAL`. A real Darwin backpressure test showed that
DONTWAIT alone did not prevent a blocked send. SIGPIPE safety is independently
exercised with the child's default signal disposition. A small
explicitly audited syscall module contains those operations. It validates the
shared B1 length prefix before allocating, prices raw frame storage and I/O
work, retains the original Budget owner/deadline across partial I/O, and closes
permanently on refusal. It does not decode/re-encode frames or charge wire bytes
again; the existing B1 codec accounts for encoding and decoding.
A would-block operation waits in poll(2) on the socket, in slices of at most
50 ms bounded by the original deadline, so a call and its reply cost one
wake-up each.

The socket caller still establishes peer identity and exclusive protocol use;
the transport creates no launcher or containment authority. Its clean-EOF API
lets the external process owner require EOF and successful owned-child teardown
after Finish. Native subprocess tests use unnamed socket pairs and the actual
compiler Dispatcher, not an in-memory callback, but their statically selected
native clients and test runtime are not an admitted DSO/runtime closure. Parent
and child accounting objects remain distinct; a child-local Budget is never
claimed to be a shared cross-process grant. Kernel scheduling and teardown are
opaque, so no hard latency or process-containment claim follows.

This transport is not compatible with B2's protected worker FD3: its constructor,
I/O, wait and teardown use getpeername, ioctl(FIONBIO) for nonblocking setup,
sendto/recvfrom, poll, shutdown and close operations that the relevant profile
does not permit. The explicit fcntl(F_GETFL) readback is permitted; it does not
make those other operations legal. No
filter or protected-descriptor rule is relaxed here. A separately qualified
borrowed/retained endpoint is now supplied by Linux trusted entry's
`Installed::control()`, using this same Transport trait (re-exported from B1).
It uses admitted read/write plus ppoll and logical close, after trusted
nonblocking setup, without changing these filters. It requires terminal worker
exit and the existing outside Finish/EOF/status/kill/reap owner; plain-write
SIGPIPE is an abnormal terminal failure, or sticky EPIPE if ignored/handled.
Actual Linux-filter qualification and native loader/runtime/launcher integration
remain separate requirements; the owned UnixTransport is still parent-only.
