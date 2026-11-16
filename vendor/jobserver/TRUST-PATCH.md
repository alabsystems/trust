# Jobserver explicit pipe import

Upstream: `rust-lang/jobserver-rs` commit
`85ba04e3cf89e5c10e7b82de69f6be6dff9d3ec3`, crates.io `jobserver 0.1.35`.
The source bundle SHA-256 is
`1c00acbd29eabad4a2392fa0e921c874934dbbf4194312ad20f04a0ed67a3cb3`,
matching the cached crates.io archive and the former registry package in
Trust's frontend lockfiles.
The complete bundle, including both licenses and upstream tests, is retained.

The forward update from 0.1.34 preserves Trust's constructor and its two
regression tests byte-for-byte: upstream's `src/lib.rs` did not change. The
0.1.35 bundle raises its MSRV to 1.85, updates the Windows `getrandom` edge to
0.4 and test-only `nix` to 0.31.3, and exercises both GNU Make jobserver wire
formats where supported. Its standalone lock and upstream CI files advance
with the release. No scheduling or descriptor-ownership rule is changed.

Trust adds one Unix `Client::from_pipe` constructor, using borrowed endpoints
and the existing checked pipe importer. It validates read/write access, clones
owned CLOEXEC descriptors, and neither reads nor creates scheduling tokens.
The caller authenticates which pool the pair names. This lets the native build
driver use the existing authenticated descendant handoff without changing the
environment bytes authenticated by native fix-proxy dispatch.

`Acquired::belongs_to(&Client)` compares the actual originating client Arc,
including its clones. A newly imported client with the same transport does not
match. This read-only restriction lets the queued native Bootstrap adapter
retain the exact original supplementary guard through owning retirement; it
cannot acquire, transfer or reconstruct a credit. A real pipe regression covers
clone, foreign server, reimport and actual guard return.

Trust also adds explicit Unix `Client::from_fifo`: independent nonblocking
read/write opens, no environment import or token creation, atomic no-follow
opens and descriptor FIFO/device/inode checks. Paths must round-trip through
GNU metadata (absolute UTF-8 without whitespace); the caller retains namespace
ownership through every descendant use. Empty `acquire` remains blocking via
the existing readiness poll, while a full owner write reports `WouldBlock`.
Ordinary acquired-guard returns retry interruptions and poll writable capacity
on `WouldBlock`, avoiding silent token loss in the existing error-ignoring Drop.
Bounded owner steps use raw issuance and consume reclaimed guards without return.
Directional read/write opens also fix Darwin's read/write FIFO ioctl overwriting
the readable byte count with its write-end count. Ambient FIFO metadata grammar
and blocking behavior remain intact: open each directional end nonblocking,
then restore their blocking flags only after both are held. This is transport, not CPU allocation or
proof authority, and supplies no crash-lifetime guarantee for future backing.

Trust adds deterministic helper retirement (RUSTC-FRONTEND-TOKEN-LEAK-1). On
Unix the helper thread reads a token out of the pool and only then passes it to
the callback; `Drop` and `HelperThread::shutdown` stop waiting for the thread
after 100 rounds of 10 ms, and a helper that outlives them into process exit can
die holding a token it had read, which is then gone while the process exits 0.
Upstream's bounded `Drop` and `Helper::join` are unchanged. Added beside them:

* `HelperThread::shutdown_blocking(self) -> io::Result<()>` and, per platform,
  `Helper::join_blocking`. `Ok` is returned only once the thread is joined
  after finishing its request loop. On Unix it sends `SIGUSR1` every 10 ms for
  as long as the thread lives (one signal can arrive before the `read` it was
  meant to interrupt) and also stops when `JoinHandle::is_finished` reports a
  thread that ended without finishing its request loop, which is a panicked
  callback and is reported as `Err`. A token read while this runs still reaches
  the callback. The caller must not hold a lock the callback takes. `Err` can
  also mean the thread was not joined, and then says so: on Windows when
  `SetEvent` fails and the thread has not already ended, and under Miri, which
  cannot send the signal, where the wait stays bounded and reports `TimedOut`.
  On Unix the wait has no bound by design, so two states make it permanent: a
  `SIGUSR1` disposition replaced after the helper started, and a callback that
  never returns. After 10 seconds it prints one line to stderr naming what it
  waits for, and keeps waiting; giving up is what loses the token.
* The Unix helper thread unblocks `SIGUSR1` in its own signal mask when it
  starts. A thread inherits its mask, and with the signal blocked nothing could
  interrupt its `read`: the bounded join silently gave up, and an unbounded one
  would never return.
* `HelperThread::cancel_request(&self) -> bool` withdraws one request the helper
  has not started to serve, and `HelperThread::queued_requests(&self) -> usize`
  reports how many there are. A request already being served is not interrupted.
  A caller that satisfies a waiter some other way uses this so the helper does
  not take a token out of the pool only to put it back.

`tests/helper.rs` covers each: a helper blocked on an empty pipe and on an empty
FIFO is joined; a token that arrives during retirement is conserved (500
rounds); a queued request is withdrawn and the one being served is not; a
panicked callback is reported instead of waited for; a helper started with
`SIGUSR1` blocked is still retired (this one fails by timeout without the mask
change); and a helper holding a token for 1.5 s is abandoned, token inside, by
the bounded `shutdown` but outwaited by `shutdown_blocking`.

An independent workspace keeps the foreign package's own tests runnable without
resolving the compiler graph. The root, Bootstrap and Targo workspace patches
select this same package so their shared client types and locks agree.

`Client::same_origin` compares the retained original client Arc, including
clones but excluding a separate import of the same pipe. Ready-token admission
binds this identity once, including across helper retirement, so a request for
another client cannot receive an earlier client's fetched guard.
