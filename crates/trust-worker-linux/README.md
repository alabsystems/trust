# B2: Linux worker restrictions, not macro admission

This crate installs restrictions in a trusted, single-threaded worker entry,
before any user DSO or its dependency constructors run. The feature-gated
`native-entry-fixture` additionally qualifies a real Linux C DSO through two
roles of one pinned static image; see the final section below. The compiler's
macro refusal remains in place. A returned local installation
token is not a proof, an authenticated worker receipt, or compiler authority.

The worker must start with an empty environment. Its retained descriptors are
dense: read-only `/dev/null` at 0, write-only diagnostic pipes at 1 and 2, a
parent-bound Unix stream at 3, an empty private scratch directory at 4, then
explicit size/SHA-256-bound sealed read-only inputs at 5 onward. Inputs require
WRITE/GROW/SHRINK/SEAL seals; an ordinary file or future-write seal is insufficient.
The owner assigns which immutable inputs may be mapped executable. The core
checks their actual open descriptor contents without reopening an artifact path.
All other descriptors close before user code; retained descriptors cannot close,
duplicate, change flags or be replaced after installation. This prevents an FD
number being recycled from an executable input into a writable scratch file.
The descriptor limit reserves one additional slot for Landlock setup after all
undeclared descriptors close and before user code is allowed.

Landlock ABI 3 is mandatory: ABI 1 provides filesystem rights, ABI 2 handles
cross-directory REFER, and ABI 3 covers TRUNCATE. All rights through TRUNCATE are
handled. This narrow core grants no filesystem paths, including scratch. File
creation/access needs a future typed broker or preopened bounded data capability.
Landlock cannot constrain all anonymous-object procfs reopenings, so seccomp
independently denies every open/openat/openat2 and directory enumeration/creation.
Inherited immutable inputs are descriptor
capabilities, not ambient filesystem paths. Network/process authority is denied
independently by seccomp, so this core does not require Landlock's later network
ABI. An unsupported kernel, failed restriction or incomplete descriptor contract
refuses; there is no namespace or unrestricted fallback.

Seccomp checks the native audit architecture and then kills on every syscall
without an explicit rule. Allowed operations are descriptor data I/O, bounded
runtime allocation/signals/clocks, private futexes and process exit. Data I/O
observes descriptor roles. mmap with
EXEC requires a declared immutable executable input, forbids WRITE and anonymous
mapping. mprotect cannot grant EXEC; pkey_mprotect is denied. Process creation,
exec, networking, socket descriptor passing, namespaces, mounting, ptrace, bpf,
ioctl, descriptor duplication and post-install policy changes are denied.
Admission requires exact native Linux personality, rejecting READ_IMPLIES_EXEC,
and rejects existing writable executable mappings. This entry check is not a
complete mapping provenance proof: the later immutable launcher must establish
that every existing executable mapping is from its pinned trusted runtime and
that no user code or concurrent thread existed before restriction installation.

The shared original Budget deadline is checked during input admission and around
restriction installation. Kernel address-space, stack, descriptor and individual
scratch-file limits supplement that admission. They do not establish a hard wall
deadline, aggregate RSS, aggregate scratch quota or bounded diagnostic capture.
The parent still must own kill/reap on every error/panic, cap IPC and diagnostics,
enforce the original tree envelope and provide a bounded scratch mount/quota.
An installation error after any irreversible step must terminate this worker,
never continue into loading or retry a weaker profile.

The adversarial fixture is an unverified development test, not an executable
macro route. Before activating any loader, the owned parent launcher must bind
the worker executable and its complete runtime/DSO closure to immutable open
inputs, close inherited authority before exec, clear environment in the parent,
and establish consumption-time identities. Native dynamic-loader reopening of
paths and its runtime closure are deliberately unresolved here. No LD_PRELOAD,
loader environment, expansion cache or worker proof-success bit is supported.
The fixture pre-exec cleanup closes std::process's private exec-error pipe too;
exec failures surface as worker exit/status rather than the usual precise spawn
io::Error. Its WNOWAIT/group cleanup exercises lifecycle behavior but is not a
production launcher or an authenticated executable receipt.

Historical B2 test measurement scope: its kernel fixture deliberately creates a
private process group. The prior outer diagnostic watchdog capped and sampled
the Targo launch group, so its reported peak is that group's peak and does not
attest aggregate worker-tree RSS. The fixture's own kernel limits, parent deadline,
output caps and kill/reap checks remain separately exercised. None of those
observations is promoted by this scope correction.

## B3a: owned static-worker diagnostics

The launcher module copies owner-named inputs into sealed read-only memfds and
admits only bounded native ELF64 static ET_EXEC workers, with no interpreter or
dynamic segment. It checks native page congruence and rejects rounded LOAD overlap,
writable executable pages and executable stacks. The complete static worker and
its startup/runtime remain pinned trusted code until B2 installs. This route cannot
sandbox arbitrary executable constructors and does not load native Rust macros.
Static glibc can still contain helpers that load libraries (the fixture link warns
about NSS helpers); trusted fixture startup does not call them, and installed B2
denies every ambient open. General static-runtime support is not established.

PreparedStaticWorker carries one original shared Budget and deadline through
snapshot/ELF preflight, cycle-safe FD preparation, fork/execveat, bounded nonblocking
capture and B1 callbacks, explicit kill/reap and owned teardown. Its separate
CLOEXEC status pipe reports setup/exec errors without relying on std::process's
private error channel. The child creates a private process group; the parent acquires a
pidfd when supported and retains the unreaped leader through group termination.
Every error, cancellation or unwind keeps cleanup ownership. No blocked reader
thread is joined. Kernel scheduling can delay cleanup; receipts include elapsed
through teardown and a final original-deadline check, not a hard latency promise.

Memory measurements explicitly sample the leader only. Trusted startup must create
no threads/descendants before B2, which then denies process creation. Finite AS,
stack, descriptor and per-file limits are kernel restrictions; sampled RSS and
logical input/capture reservations are separately named. There is no hard aggregate
tree-RSS or scratch-quota claim. Opaque owner callbacks require bounded semantic
accounting and cannot be preempted by this loop; late returns refuse. Normal nested
completion does not cancel a parent's grant, while failure/cancel cannot resume it.

The typed receipt is local structural evidence. Expected owner provenance is not
established by echoing it from the worker. Ready/Finished are protocol transitions,
not sandbox/proof credentials. Complete compiler-owned handle/Span/hygiene admission,
the immutable dynamic loader/runtime/DSO closure and authenticated host/build evidence
are still required before any native macro route can be enabled.

Run the Linux static-fixture diagnostics separately from ordinary pure tests. The
parent tests are visibly ignored by default because they require this pinned
separate artifact; explicitly running them without the artifact fails. These are
unverified compiler-development commands, never required-build substitutes:

```sh
RUSTFLAGS='-C target-feature=+crt-static -C relocation-model=static -C panic=abort' \
  CARGO_TARGET_DIR=/owned/static-target \
  targo --unverified build --manifest-path crates/trust-worker-linux/Cargo.toml \
    --features static-fixture --bin static-launch-fixture --locked -j1
targo --unverified test --manifest-path crates/trust-worker-linux/Cargo.toml --lib --locked -j1
TRUST_STATIC_WORKER_FIXTURE=/owned/static-target/debug/static-launch-fixture \
  targo --unverified test --manifest-path crates/trust-worker-linux/Cargo.toml \
    --test launcher --locked -j1 -- --ignored --test-threads=1
```

Apply a real owner-selected tree-memory/deadline backstop to these development runs.
These static-fixture commands perform no signing, publishing, installed link
changes or native DSO loading.

## B3b1: immutable native-object capability service substrate

The native module binds at most 27 owner-declared ELF objects to the original
Binding and shared Budget before snapshot allocation. It copies exact SHA-256
and size-bound bytes into sealed read-only memfds and checks bounded native
ET_DYN headers, page-separated non-W+X LOAD segments, non-executable stack,
SONAME and the declared DT_NEEDED graph. Unknown program/dynamic tags, loader
path overrides, text relocations and incompatible flags refuse. Literal aliases
are exact virtual names; they never become host paths. Structural admission is
not authenticated provenance, relocation validation or loader compatibility.

The private notification service validates the exact task, audit architecture,
phase and notification ID, copies bounded arguments through an owner-retained
read-only mm FD, and accepts only read-only literal-alias opens with explicit
flags and AT_FDCWD semantics. Every issuance uses a fresh read-only description
of the still-owned sealed memfd, preserving independent offsets. ADDFD uses
SETFD|SEND atomically into the one-use 33..63 bank; no CONTINUE, target-selected
FD, ambient path open or write to target memory exists. Fixed executable inputs
and admitted native bank objects alone may be mapped executable.

The separate broker profile grants no Landlock paths and denies process creation,
exec, network, descriptor duplication and policy mutation. Trusted entry must
create the listener at its predicted slot, hand it over once using a private
SOCK_SEQPACKET channel with kernel credentials, and close both bootstrap slots
before any user code. The parent must retain the unreaped single-thread child
and its exact post-exec mm, own kill/reap and enforce the original deadline.
The module cannot establish those caller obligations by itself. Invalid protocol
or resource state is sticky across shared owners; no replacement grant is opened.

Five real kernel service fixtures exercise retained-mm reads after dumpability
is disabled, credential/FD handoff rejection, virtual open refusal, independent
open offsets, owner cancellation, target death and nonfatal interruption after
listener readiness. Kernel ioctl/pread can block: the eventual production owner
must independently watch the child/broker and retain kill/reap through these
opaque intervals; finite admission is not a hard syscall-latency guarantee. They use a fork-only fixed
trusted entry and synthetic structurally valid ELF bytes; they do not load a
DSO or establish native loader behavior. Existing B3a sealed exec diagnostics
and the separate retained-mm kernel probe cover distinct boundaries. No native
Rust macro, bridge ABI, Span/hygiene, production launcher or compiler admission
is qualified by this milestone.

## Shared native-entry restriction installer

The private native entry now reuses B2's exact environment, personality, mapping,
dense immutable-input, descriptor-role, limits and mandatory Landlock checks.
It preserves only one additional high SOCK_SEQPACKET descriptor bound to the
direct parent's PID and effective credentials. It checks SIGKILL parent-death
handling, rechecks the socket inode/role after the clamp, closes every other
ambient descriptor, and requires NEW_LISTENER|WAIT_KILLABLE_RECV to return the
predicted free slot. A mismatch or partial installation is terminal; the caller
must terminate. Its local marker is not an authenticated receipt or permission
to load native code. The native path requires NOFILE64 for its fixed one-use
33..63 bank; B2's smaller descriptor envelopes remain supported separately.

The existing real kernel fixture calls this shared installer instead of its
duplicate restriction sequence. Two added kernel fixtures check refusal before
a fixed continuation marker and cleanup of an occupied listener slot. Two added
source tests check identity substitution, including replacement of a real socket
on the same descriptor number. The September 29 Linux development run passed the
two native-entry identity tests and seven native kernel tests, together with the
six existing B2 kernel integration tests. The fixed continuation marker remains
diagnostic code, not an actual DSO constructor test.

An immutable post-exec loader/runtime closure, exact mm custody, independent
owned broker watchdog and actual constructor adversaries remain mandatory before
native activation. The helper assumes no untrusted signal handler, thread or FD
mutator executes during admission. A Budget clone inherited through fork is
process-local and cannot stand in for a cross-process prepaid or shared grant.
The compiler still refuses native macros; authenticated rustdoc is also pending.


## Private worker and broker cleanup owner

The private owner starts an independent monitor before it accepts either of the
two exclusive direct-child guards. It charges monitor stack and bookkeeping to
the original in-process Budget, requires the same accounting owner for both
children, and preserves the original deadline. Equal numerical limits do not
establish shared ownership. Forked Budget copies are not cross-process grants.

Cancellation, expiry, child exit, monitor failure and unwinding latch refusal.
Cleanup signals both children before entering either opaque wait interval; the
unreaped guards and pidfds retain custody until both are reaped. The caller never
joins blocked broker IO or a pending kernel reap. Incomplete cleanup retains its
monitor owner and cannot publish successful completion. A cleanup receipt says
only whether the children were reaped and the original grant survived teardown;
it carries no native macro, solver or proof authority.

The September 29 diagnostic passed all 20 owner tests and the shared-budget
identity test in addition to the 15 entry/kernel tests above. It used Trust
source `268b79222d` with the recorded Linux source overlay and sealed compiler
`6986546e`, explicitly through `targo --unverified`. The committed Rust files in
this change match those tested source bytes. The run had a 2 GiB no-swap cgroup,
original deadline and child RSS monitoring, no OOM event, and independently
confirmed process cleanup. Its final receipt is
`trust-linux-ay-qualification-native-20260929T071718Z-3ad9c142.plan.json.final.json`,
SHA256 `0eee4b4588290572f8c18e1688d203a63797e0b701b31e97442791911724534f`.
These selected tests do not qualify the full crate, latest compiler build,
dynamic loader closure or native proc-macro route.


## Fixed checker thread restrictions

`install_checker_threads` is a fixed restriction-only entry for a trusted
single-threaded checker startup. It permits GNU pthread creation with the exact
full-width clone flag word, bounded futex operation classes, robust/rseq setup,
thread naming and sleep. `clone3` and optional runtime metadata probes return
ENOSYS to their audited fallbacks. Other process creation, execution, signal and
namespace operations remain denied; the original single-thread and native
loader profiles retain their existing restrictions. This API authenticates no
worker executable, resource receipt or solver result.

The parent must set finite address-space limits before exec, enforce aggregate
memory and task limits, retain stable leader ownership, preserve the original
deadline, and kill/reap all worker threads before completion. A leader that has
exited while a sibling still runs is not a completed worker. The profile does
not admit ambient resource-file reads: an actual solver's live `/proc`/cgroup
observations need a separately admitted resource mechanism before activation.

The September 29 Linux development run passed 54 selected tests: 29 native
entry/kernel/owner unit tests, 12 original/checker filter tests, 12 original and
checker kernel integration tests, and one shared-budget test. It exercised real
thread naming/TLS/join, address-space refusal, forbidden clone variants and a
leader-exit/live-sibling case under the original parent deadline. Source was
`c224b22d5c` plus the recorded 24-file overlay; the nine manifest/Rust files in
this change match that tested overlay. The compiler was sealed Trust
`6986546e`, using `targo --unverified`, one build job and a 2 GiB no-swap cgroup.
The run took 53.530 seconds including cleanup, with no OOM event and independent
external cleanup confirmation. Final receipt
`trust-linux-ay-qualification-native-20260929T081105Z-7f158002.plan.json.final.json`
has SHA256 `beaf4d9f79485d358e797ee048b9948dd3dfae80e5c3432f0d92fad1d5a1359e`.
These selected development tests do not establish static worker runtime
compatibility, complete solver containment, native macro admission or a verified
compiler/workspace build.

## Fixed live resource observations

`install_checker_resources` extends the checker-thread profile with two
read-only, authenticated procfs roles: descriptor 6 is this worker's numeric
PID `statm`, and descriptor 7 is global `meminfo`. Only bounded offset-zero
`pread64` and self `getrusage` are admitted. The executable input remains at
descriptor 5. Role substitution, mutation, aliasing and executable-memory
creation are refused. The parent still owns aggregate limits, the original
deadline and complete kill/reap cleanup. This restriction API grants no proof
authority.

The September 30 Linux development run passed all 64 selected tests, including
ten new filter, identity and actual-kernel resource controls. It measured live
RSS growth and pthread reads, and tested swapped/imitation roles and denied
syscalls. Source was `659e4af235` plus its recorded overlay; the eleven source
files in this change match those exercised bytes. Sealed Trust `6986546e` ran
`targo --unverified`, with one build job, a 2 GiB
cgroup and swap disabled. The run took 59.370 seconds including cleanup,
peaked at 731,672,576 bytes, recorded no OOM, and confirmed external cleanup.
Final receipt
`trust-linux-ay-qualification-native-20260930T182522Z-2b9ba712.plan.json.final.json`
has SHA256 `0162144882d8d63d19be34a417bbbd23843ca1f0131ce84b132a1d65d2f2d24c`.
Static AY worker and complete verified-build qualification remain outstanding.


## Additive contained static-worker source route (runtime unqualified)

`PreparedStaticWorker::launch_contained` is an additive B3a API. It creates a fresh
ordinary cgroup-v2 domain beneath a caller-retained delegated parent; an existing
name, imitation filesystem, unlimited/missing parent limits, missing controls or
unsupported clone3 refuses. The parent must expose usable memory/pids controllers
for its child. A populated normal terminal scope is not automatically such a
parent: the invoker must first own a legal delegated hierarchy within its original
kernel grant. This API does not move the invoker or widen that grant.

The child memory limit tightens the existing finite parent/profile limit; swap is
zero and `pids.max=1` is the existing single-thread trusted startup/B2 profile.
`CLONE_INTO_CGROUP|CLONE_PIDFD` confines birth before any worker instruction.
The existing FD remap/close-range, empty environment, sealed static ELF/inputs,
Landlock and seccomp remain in force. No control-file capability reaches exec.
Fixed held directory/control descriptors identify the exact owned group even
when its pathname is renamed. Limits are reread before birth, during ordinary
status polling and before closure credit.

Retirement requests `cgroup.kill` through the original descriptor, reaps only the
birth pidfd, and requires the recursive `populated=0` observation. Cleanup polling
is prepaid from the same original Budget work limit and absolute endpoint; no
refund, new timeout or renewal exists. Callback unwind uses this same cleanup.
After expiry or any failed/opaque kernel operation, the request remains a negative
and the caller's outside hard kernel owner must finish custody. Creating a group
never authorizes deleting an existing name. The caller retains removal of its
exact fresh namespace, including a partial creation that spawned no child.

No structural receipt authenticates source, a proof, a Trust seal, release input,
a dynamic runtime closure or independently replayed semantic results. The old
`launch` API and native-worker route retain their previous behavior. The two
existing release-isolated-child refusals remain unchanged. Integrating an actual
compiler/Targo release child still needs a genuine dynamic immutable runtime/input
broker, an admitted finite/delegated invoker and independent result replay.

Source-only controls include ordinary non-cgroup/grammar/work-accounting negatives
and separately selected real cgroup/clone3/setsid/hard-exit/cap-mutation controls.
The explicit ignored OS controls require `TRUST_WORKER_TEST_CGROUP_PARENT`, an
exclusive finite delegated parent under an outside original kernel owner; the
three protocol controls also require the already-pinned static ET_EXEC
`TRUST_STATIC_WORKER_FIXTURE`. They must be selected with `--ignored` in the
actual qualification owner; their source existence is no executed evidence.
All original controls remain exact. No test ran for this source packet; its
only check is a stock-cargo type-check for `aarch64-unknown-linux-gnu` on macOS
(2026-10-17, docs/DECISION_QUEUE.md).

Kernel contracts used here are the recursive cgroup events/kill semantics in
[the cgroup-v2 documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html)
and birth cgroup/pidfd behavior in
[clone(2)](https://man7.org/linux/man-pages/man2/clone.2.html). The numeric variadic
arguments in the two static setup `prctl` sites and two restriction sites now use
`libc::c_ulong`, following
[prctl(2) CAVEATS](https://man7.org/linux/man-pages/man2/prctl.2.html). Other native
and test-only sites are retained and explicitly listed as a separate ABI remainder.

## Retained worker control IPC

Successful trusted entry can lend `Installed::control()` to the native ABI
bridge's existing B1 `Transport` interface. This is distinct from the owned
parent `UnixTransport`. The B3 launcher establishes O_NONBLOCK on the worker
endpoint before remapping/exec; entry authenticates FD3/its parent, sets and
verifies O_NONBLOCK before seccomp, then retains the original local Budget in
its unforgeable installation marker. Trusted startup must exclude constructors,
threads, handlers and aliases that mutate descriptors/status flags until entry
completes. The installed filters still deny protected close/dup/F_SETFL.

The borrowed adapter uses only read/write, F_GETFL and finite ppoll waits. Raw
frame allocation and I/O work use that original Budget/deadline; existing B1
encode/decode alone charges wire bytes. Owner substitution, EOF/truncation,
oversized frames, resource/deadline and I/O failures latch refusal. Close/Drop
only latch the connection terminal in Installed; dropping and reborrowing the
marker cannot reopen it. No shutdown, close, duplicate, peer probe, ioctl, sleep
or new descriptor occurs after installation. FD3 is released only by terminal
process exit, so its numeric role cannot be recycled.

Trusted worker entry must terminate after bridge success or refusal; returning
to arbitrary code is not completion. Plain write intentionally has explicit
SIGPIPE semantics: an unblocked default signal terminates the worker abnormally;
an ignored/handled signal produces sticky EPIPE refusal. The adapter does not
change signal policy. The outside owner must reject either failure, require
Finish plus actual EOF plus successful reaped exit for success, and cancel,
kill and reap a worker that remains alive or misses the original deadline. A
child-local Budget is not cross-process shared accounting.

The existing static B3 fixture now uses this adapter and retains its original
diagnostic Ready behavior; no new production Ready/loader path is introduced.
Additional controls use the existing native-filter fork fixture with real B3
FD0/FD3/scratch/diagnostic roles and an empty environment. They cover Finish/EOF/
exit, partial prefix, owner substitution, drop/reborrow, cancellation, malformed
and truncated frames, read/full-buffer deadlines, and explicit SIGPIPE default/
ignored dispositions under the actual native filter. They are Linux-kernel
tests, not a simulation or native DSO-load qualification. The fork fixture does
not establish a new sealed exec mm or runtime closure. These tests must be run
on an admitted Linux owner; a Darwin build cannot execute them.

This component changes no filter, provider authorization, PM-1 refusal or proof
grade. Native Client/declaration binding, immutable DSO/runtime closure, broker/
launcher lifecycle, containment before constructors, persistent per-dylib and
nested ownership, consumption receipts, graph-wide build-script/scoped-out-derive
containment, other platforms and authenticated rustdoc remain unfinished. The
compiler Dispatcher and B3 owner now share the original compiler-issued Session:
`prepare` captures its opaque owner and Budget, `launch` consumes that exact
unstarted Session before spawning, and callbacks receive its mutable reference.
Equal binding fields and the same Budget do not admit a reconstructed Session.
The owner is checked again after every callback, before replying; a callback
cannot replace the borrowed Session and replay the pending call on another one.
The dispatcher returns an admitted typed value; only the transport advances the
pending call with `Session::reply`. Neither successful local dispatch nor a
worker's Ready grants macro or proof authority.

The Linux compiler tests in
`compiler/rustc_expand/src/proc_macro_server/isolation/dispatch/tests/owned.rs`
connect the real Dispatcher to this owned static child and retained FD3. They
require the separately built static ET_EXEC fixture and explicit `--ignored`
selection; a host build or a run reporting them ignored is not executed Linux
evidence. They cover token cloning/consumption, source spans, original Session
ownership, cancellation, stale handles, abnormal completion and reaping. They
still do not exercise native DSO loading, constructors, or a qualified worker
runtime. The normal compiler macro loader remains unchanged and fail closed.


## Composite prepared input identity

`InputClosureIdentity::from_plan` binds the static executable/ordered inputs and
an optional native-object graph under one domain-separated digest. Its digest,
not either component alone, occupies `Binding.input_closure`. The optional
component has an explicit presence tag; there is no legacy static-only or
native-only fallback.

`NativeClosure::prepare` accepts this identity and the original unstarted B1
Session. It checks the declared native graph, copies and admits its ELF objects,
and records the opaque SessionOwner. `PreparedStaticWorker::prepare` consumes
that closure, recomputes the static component and checks the complete identity,
Binding, owner and shared Budget before it can spawn. Native backing bytes also
count against the launcher's input-byte limit. The native snapshots remain
owned until child cleanup; receipt storage is reserved before launch.

The resulting `Receipt.native` records **prepared** object hashes, sizes, roles,
SONAMEs, aliases and declared dependency edges. It does not claim that a child
loaded or consumed those objects. The static fixture still loads no DSO, and
neither native service activation nor constructor containment is added here.

For the native positive/control tests, independently build the small ELF input
on Linux:

```sh
cc -fPIC -shared -nostdlib \
  -Wl,-soname,libfixture.so,-z,noexecstack,-z,max-page-size=4096 \
  crates/trust-worker-linux/tests/fixtures/native_input.c -o /owned/libfixture.so
```

Set `TRUST_NATIVE_OBJECT_FIXTURE=/owned/libfixture.so` alongside the existing
`TRUST_STATIC_WORKER_FIXTURE` when explicitly selecting ignored launcher and
compiler-owned tests. The native file is structurally admitted and retained;
this command is not a proc-macro build or loader qualification. Native Trust
availability and any authorized stock diagnostic exception must be recorded.

## Actual pinned native worker/broker C diagnostic

`native-entry-fixture` now has real worker and broker roles. Both execute from
the same pinned sealed static image. The parent retains the original Session,
prepared snapshots, finite shared allowance and independent two-child monitor.
It prepays role/context/absolute-endpoint helper suballowances; a local helper
meter cannot reconstruct or renew compiler accounting. Trusted post-exec startup
authenticates fixed channels and pauses for exact mm/maps capture. The worker
installs the unchanged native profile before transferring its listener or
loading any DSO. An authenticated private relay binds listener/mm/maps to the
owned task and broker capsule. Procfs roles are validated before map reads.

Both helpers recompute the composite static/native graph. Initial artifact
descriptors are sealed data inputs; executable mappings come from immutable
broker issuance. The broker preopens finite independent source descriptions,
then installs its own fixed Landlock/seccomp role before load permission.
Notification ioctls and retained-mm/map reads stay in that supervised child.
There is no CONTINUE, ambient path reopen, descriptor mutation/duplication,
network/exec/clone or executable mmap/mprotect authority in the broker. Its only
fcntl observation is F_GETFD inside the validated1024FD envelope, required by
Rust's owned-FD destructor. Worker policy remains unchanged.

The actual C constructor/function probe supplies issuance and separate
historical RX-map observations, bound to complete context/graph/capsule/sequence.
The parent validates required roots, exact source hashes/inodes/bank and
cumulative progress before Ready; terminal receipt, Finish, actual EOF, zero
exit and both reaps retain original-budget checks. Listener HUP retires service
without success authority; the monitor decides completion. Both processes reuse
the existing Capture quotas. No worker marker or structural receipt is a proof.

Explicit native tests require `TRUST_NATIVE_ENTRY_FIXTURE` naming the separately
built static image and `TRUST_NATIVE_CONSTRUCTOR_DIR` naming the independently
compiled matrix from `tests/fixtures/native_constructor.c`. Source and artifacts
are frozen by hash before execution. Ordinary runs visibly ignore these cases.
The qualified matrix includes real constructors, unknown opens, forbidden
network/process/exec/mapping/input-write authority, handoff substitution,
capture overflow, startup deadline and owned cleanup. Synthetic receipt tests
separately cover parser binding/replay/oversize/truncation and terminal failure.

This is a Linux C ABI diagnostic with one dependency-free DSO. It does not
qualify Rust Client/declaration binding, a general native runtime/dependency
closure, macOS, aggregate containment, the production provider or a sealed SDK.
General PM-1 and AY release remain closed.
