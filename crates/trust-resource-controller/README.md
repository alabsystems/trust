# Native resource member controller

The canonical metadata implementation was recovered from the maintained aterm
source at `77bd657741` after its advertised vendor commits could not be resolved
through the Trust repository's commit API. Metadata request role `3` and the
separate syntax-only Mach-O linker loan role `4` coexist; neither syntax is a
resource grant. Refresh consumers from a qualified canonical commit, preserving
both protocols rather than overwriting one with an older vendor snapshot.

The linker loan still requires an independently quiescent parent, authenticated
actual CPU backing, a durable host return, a strict paired-linker recipe and a
qualified native supervisor. Prefix and final cap strings alone do not establish
that the linker parsed them as options. This library enables none of that work.

`sealed-metadata-v1` is a separately negotiated metadata-only protocol. Its
canonical capability data and startup/query arguments are Rust constants;
they confer no admission and must not be advertised by an incomplete executor.
The existing compile, version, context and telemetry protocols retain their
original semantics. The matched host/native-Targo implementation is required
before any paired probe stage can execute.

The exact HELLO has `version:3`, `role:"sealed-metadata-v1"`, canonical `session`
and the original resource-root hex `attempt`. After PREPARE `0x50`, kind12
`SealedMetadataRequest` binds the existing Request (role3) to a canonical SDK
root and expected image SHA256. That SDK root is distinct from the original
resource-root capability. Shared borrowing supplies one original CPU right;
fixed borrowing supplies none and must match the host's actual retained one-CPU
grant. Both require the original GNU context and refuse lifetime fences. A
decoded mode/count never creates a resource owner. Unsupported ancestor custody
refuses; it must never trigger a fresh root or replacement GNU server.

After live native-peer/job authorization and READY `0x41`, one `0x46` marker
carries actual rights in this order: stdin, stdout, stderr, events, optional
shared CPU, GNU read, GNU write. Source numbers label the producer's actual
owned bundle; the host uses received rights, never environment-selected source
descriptors. ACK `0x01` is attachment only. The host retains CPU/GNU, original
memory and input descriptions through preparation, GO, cancellation and actual
scope retirement. Ambiguous delivery never permits replay.

The event protocol requires one kind13 `MetadataPrepared` inventory before
Started. Its bounded file/runtime/path/host observations are data, not image,
source, writer, resource or proof authority. Kind14 `MetadataCompletion` wraps
the actual Finished status and post-drain input-validation result, preserving
the actual failing exit/signal even when changed inputs invalidate comparison.
Plain Finished is invalid for this purpose. The native executor owns ordering,
exact attempts, finite stream/deadline checks and final drain; a codec cannot
establish them. Closed argv are `-vV`, `--print sysroot`, and
`--unverified --version`, with at most 30 target seconds and 64 KiB combined tool
output. The complete semantic environment admits only `LANG=C`/`LC_ALL=C`;
the actual owner regenerates checked runtime and scheduling transports.

The capability explicitly advertises `metadata_role:3`. Published role2
`MetadataProbe` remains the separate borrowed-CPU, no-GNU, eight-second
single-argument built-in print query. It does not authorize this sealed-root
runtime profile or genuine two-argument Targo version probe. Unpublished
private role2 sealed-metadata baselines remain retained evidence; current
producers/hosts neither reinterpret those bytes nor retry another role.

With `client`, `Client::metadata` sends the negotiated request directly over
the original pinned native ancestor connection and transfers only the caller's
actual owned descriptions. It creates no helper or scheduler. After request
delivery, an attachment failure returns the still-owned `MetadataMember` with
unknown delivery; it must not cause replay. `MetadataMember::poll` retains
those descriptions and the authenticated host through exactly one Attached,
Prepared and Started sequence and Completed after real drain. Missing,
duplicate, foreign-policy and contradictory events refuse. A plain Finished
cannot substitute for Completed. A terminal record also requires clean event
EOF and stdout/stderr EOF, so trailing or truncated frames cannot hide behind
successful exit. Combined output collection is bounded at64KiB; excess sends
Cancel and still waits for the same actual retirement. The target outcome and
post-drain input integrity remain separate results. These source controls do
not establish that a native Targo service or the complete paired runner has
been qualified; that requires actual host/service integration.

The metadata service explicitly advertises
`context_sdk:"inherited-sdk-keeper-v1"` and negotiates with
`Client::metadata_context`, HELLO role `native-metadata-ready-v1`, after its
actual root is registered and durably ARM-tracked. The four HELLO fields are
version, role, canonical session and the complete fixed capabilities object.
The host validates its actual original peer/job/SDK/GNU/memory and records
one readiness on that same root before authorizing any sealed member. Generic
context lookups never activate it. There is no preparatory metadata capability
subprocess outside the root's durable tracked lifetime. The service requires
the current Context SDK field and separately verifies the actual early
inherited keeper. It never retries an
older role or strips the field. Existing ordinary context/telemetry entry
points retain their behavior; their broader unversioned codec cutover remains
a separate migration concern. Private native qualification is not permission
to publish or replace an installed custodian.

Kinds15/16 are bounded frontend-to-service data for one finite batch of at most
six closed probes, distinct from the host's kinds12/13/14 and carrying no root
capability. The input binds the service executable bytes separately from each
target root, uses that target root as cwd and optionally names one explicit
host discovery store. Explicit discovery uses the same private store, actual
native ancestor, peer, image and original backing checks as account discovery;
failure never creates/repairs a store, selects a pool, retries another host or
falls back to account state. No ambient store override is accepted. A response
retains the current service's held native input observations and exact
authenticated Context frame, actual completed outcomes/output and any start
known for the one incomplete failing member. Saved records confer no authority.

An incomplete client exchange can expose its original bounded stream bytes
once with `MetadataMember::take_failure_observation`. This poisons the same
client unit and never supplies completion, exit, input or retirement authority.
The observation retains combined target output up to 64 KiB, actual EOF and
overflow, and the first 64 KiB of received length-framed native events with an
explicit total/truncation count. Partial or malformed frames remain raw data.
Report16 appends this strict kind17/version1 data annex only on incomplete
failure; successful legacy bytes are unchanged. Aggregate report data is
bounded at 8 MiB for six finite input inventories; native control/event frames
remain bounded at 1 MiB. This annex is never a host lifecycle event or request.

Metadata cancellation travels on the transferred bidirectional events socket,
not the completed handshake. After attachment, the client revalidates its
original held `PinnedHelper` image/host/boot/ancestry/backing; it never asks a
closed handshake for Darwin peer credentials or reselects another host.

One private binary protocol shared by the native Targo/Trust proxy adapter and
aterm's cached immutable helper. It carries no new-root admission authority.

The actual helper is a local child of the compiler/driver, remaining in its
existing owned group. Its canonical entry is formatted by `HelperFds::arguments`: the private entry
and protocol version are fixed, with explicit decimal control/proof socket
locators. Production inherits actual held source numbers (at least 5) with
child-only CLOEXEC clearing, without overwriting parent or runtime-private
descriptors. `HELPER_ARGUMENTS` retains the convenient fixed 3/4 fixture shape.
Descriptors 0/1/2 are target stdio. Delegated source descriptors start at 5 and
must be disjoint from the actual control/proof sockets BEFORE duplication. Target CPU/GNU
descriptors belong to a different child namespace and may start at 3. The helper
must close its duplicate stdio ends after attachment and never pass control or
proof endpoints to the target.

The optional client can be compiled with stock Rust for consumers' portable
builds. Native member launch requires Trust std's explicit descriptor inheritance
and returns `io::ErrorKind::Unsupported` before spawning a helper when that
capability is absent. A build-time compiler identity probe selects the Trust
extension; metadata/context APIs do not require it. There is no process-wide
CLOEXEC mutation or implicit-inheritance fallback on stock std.

Request and lifecycle frames carry distinct original-root and member attempts.
The command environment is a complete lossless Unix-byte snapshot, never merged
with helper ambient state. Capabilities have no Debug implementation. The host
must authenticate actual native producer identity/image and current scope,
verify original retained memory and actual CPU/GNU descriptions, and validate
its own recipe before launch. Descriptor integers, decoded bytes and environment
locators alone establish no authority.

The producer challenge binds one pending request, actual helper native identity
and a fresh host nonce. The native parent must match its actual owned helper
before answering. The host must independently verify received socket credentials
and recheck native parent/helper relationships before accepting the answer.
Challenge/answer decoding alone proves no process identity.

`Attached` is not launch. `Started` uses BSD wall-microsecond birth on macOS or
start ticks on Linux, plus actual host GO clocks. `Finished` is sent only after
authenticated target scope retirement and resource return; target runtime
excludes cleanup. `Refused` requires affirmative prelaunch proof. `Unknown`
preserves available Started facts and never authorizes replay. Helper exit is
helper health, never the target result. Unknown delivery poisons the borrowed
logical unit/root execution context: do not return that unit to dispatch, retry
with an argfile or start another attempt while a target may still execute.
Independent positively owned units can finish cleanup. Cancellation and control EOF must cause
the actual custodian to cancel the retained target scope.

`Channel` frames with a big-endian u32 payload length; payloads use magic
`TRPCV003`, u64 big-endian tags/counts, bounded byte fields and exact trailing-byte
refusal. It uses per-call nonblocking Unix I/O and monotonic deadlines without
changing shared descriptor flags. Writes use per-call `MSG_NOSIGNAL` on Linux and macOS (the native Apple
SDK socket header defines it as suppressing SIGPIPE), without mutating socket
options or process-wide signal disposition. Any failed exchange
poisons the channel because partial delivery may already have happened.

This library does not activate v3, launch processes, validate CPU ownership or
establish a memory quota. Metadata syntax may omit a CPU descriptor, but the
host must still validate actual original cooperative CPU coverage for the
version-probe phase; syntax never authorizes an unbacked execution. Current production v3 policy rejects lifetime fences
and unsupported foreign compiler phases even though the codec retains explicit
bounded fence representation for protocol validation.

`Call` classifies the first private frame as `Member(Request)` or
`Context(ContextQuery)` before any effect. Context queries use the same private
producer challenge and exact cached host boundary. A host converts its checked
live Inspection to `ContextReply`; native startup must also check current
host/boot and actual external-debt/native-manifest binding before any CPU wait.
`Context::may_acquire_initial_cpu` expresses only the identity rule AFTER these
checks: the actual producer must equal the original root and its root subject.
Nested callers and registered members borrow the existing CPU capability.
Retained-fixed contexts cannot start shared native workers. Every context
carries the same original memory claim, never a new per-member reservation.
`JobBinding` owns the strict private environment-locator codec, shared with the
binary requests; a locator never proves custody.

Optional `client` support links the canonical provenance reader. Its `Client`
retains one original pinned host selection and queries context DIRECTLY as the
actual kernel peer: canonical `native-context` HELLO, private binary query and
response, post-response native revalidation, then ACK. No process is spawned
for read-only lookup. `ContextUnavailable` is distinct from transport ambiguity
and says nothing about original-root execution or resource release. The native
consumer must validate debt/manifest and initial-vs-borrowed CPU rules before
admission. The optional path has no role in the default host codec dependency
closure and does not activate v3.

The distinct resolver root negotiates `sealed-resolver-v1` and
`query_environment=resolver-root-fixed-env4-v1` before configuration. Query role5
requires exactly LANG=C, LC_ALL=C, CARGO, RUSTC, CARGO_HOME and
CARGO_CACHE_RUSTC_INFO=0; the host additionally matches those four semantic
values to its original admitted root. Role3 metadata and role4 linker stay closed.
`ResolverReport` kind34 is bounded root-output data (96MiB aggregate,64MiB
semantic metadata), separate from the unchanged 1MiB native socket and64KiB
field limits. It retains completed/incomplete query observations without private
request capabilities. Decoded reports create no SDK, CPU, memory, execution,
retirement, source authentication or proof authority.

Tests run on stock std as well as Trust's; a test that needs Trust's descriptor
inheritance is `#[cfg(trust_std)]`. On Linux, `host_boot` opens `/etc/machine-id`,
which a container image may lack (the `rust` image does). There, every
`client::metadata` test whose fixture calls `host_boot().unwrap()` panics with
`NotFound`, under any feature set that enables `client`. Mount the host's file
read-only (`-v /etc/machine-id:/etc/machine-id:ro`).
