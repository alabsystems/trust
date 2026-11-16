# B1: bounded worker protocol core

This dependency-free standalone crate implements one checked binary frame
schema, the compiler-side conversation state, invocation-local typed handles and
shared cumulative budgets with an absolute caller-established deadline. It does
not start a process, install a sandbox, load a macro, admit compiler evidence or
relax the current no-in-process-macro refusal. Its development tests use an
explicit unverified Trust lane; they establish no required certification.

Each frame is a four-byte little-endian payload length, followed by `TMP1`, a
versioned full identity binding and one typed message. Frames are consumed whole;
unknown/truncated/trailing data fails. The incremental decoder never reads a
stream itself: the future owned nonblocking transport must use `needed()`, debit
the same absolute deadline, interrupt idle/blocked I/O, capture diagnostics
separately, and kill/reap on every terminal outcome. Decode checks happen before
allocation; counters charge requested storage and reported capacity slack, not
process RSS.

Compiler-issued handle tables distinguish streams from spans and borrowed from
consuming uses. A complete transaction is validated before any handle is taken;
duplicate consume or borrow/consume aliases fail without taking earlier values.
Generation overflow retires a slot. Clearing a table permanently closes it.
Shared budgets also share the live-handle cap across nested tables and return
credits on consume/cleanup. A resource, depth, overflow, deadline, cancellation or
poison refusal latches across every clone; only cleanup remains permitted.
Session identity, schema, sequence and phase refusal also abort this shared
invocation grant: an existing nested session or a new session cannot resume it.
Normal child completion does not abort the parent's grant. A reported worker
failure returns a terminal local admission for the owning launcher to abort;
it is diagnostic data, never proof authority.
Counters are monotonic; a failed allocation still spends its reservation.
Frame vectors grow geometrically, prepricing the entire replacement capacity
and possible old-capacity copy, with a postcheck of reported slack. Handle slot
capacity is prepaid at construction. Decoder copy/UTF-8 passes debit byte work.
Allocator calls, UTF-8 validation and individual copies are bounded opaque
intervals with deadline checks around them; this is not a hard latency guarantee.
Compiler-owned `T` payloads outside the table's inline storage require separate
adapter accounting. Scope identifiers/digests must be assigned by the owner;
no worker readiness/version/digest echo is authority.

The 32 frozen method schemas match `library/proc_macro/src/bridge/mod.rs`'s
`with_api!` at Trust `6986546eaafc7620e49331269685dbd1b2900ba3`. The repository
integration test compares the live declaration's names, argument cardinality,
types and consuming ownership with these schemas. Changes to the native API
require an explicit protocol/schema version change and regenerated review.
Globals are explicit three span handles; symbol conversions use bounded strings.
The native C-ABI Client/Buffer/Closure remains outside this wire schema.

DTOs preserve delimiter open/close/entire spans, punctuation jointness, raw
identifiers, literal kind/suffix and diagnostics. They carry opaque handles,
never raw compiler span/hygiene IDs. The compiler adapter must still perform
literal lexical/kind/suffix, punctuation and NFC/raw identifier validation,
checked quoted-span lookup, source/environment snapshot admission, actual eager
expression expansion and per-call semantic validation before creating compiler
objects. A worker cannot send ErrWithGuar (non-error literal kinds only).

Next integration: Landlock/seccomp launcher before every macro/dependent-library
constructor; exact immutable worker/runtime/artifact closure; compiler-owned
expander metadata and all-method dispatcher; worker forwarding Server; nested
invocation ownership and cleanup; consumption-time input receipts; complete
macro/build-support compilation and rustdoc certification. No expansion cache
or proof-success field is introduced here.

## Compiler token adapter (D21, 2026-10-27)

`compiler/rustc_expand/src/proc_macro_server/isolation.rs` supplies a private,
bounded conversion between these DTOs/handles and real compiler token streams
and spans. It reuses the native bridge conversion and literal parser after a
nonrecursive lexical precheck. It rejects unsupported forced-keyword and
error-guaranteed tokens, validates whole handle transactions before consuming,
and keeps quoted-span lookup fallible. The adjacent `isolation/dispatch.rs`
forwards all 32 existing methods to the real Rustc server, bound to one compiler
context, B1 Session and original shared Budget. It checks the pending admitted
call and all argument handles before consuming streams. A pending call retains
an exact snapshot of all argument fields using the same bounded field encoder
as the wire format; snapshot storage, encoding and comparison work spend the
original budget without charging another call or pretending to send bytes.
An opaque per-Session owner token distinguishes reconstructions that reuse the
same Binding and shared Budget, and remains stable when the original Session
moves. It is an in-process identity, not a wire or containment credential. This is still not an
activated worker path; no additional proc-macro provider is admitted.

The dispatcher refuses representations the native host cannot preserve:
forced-keyword/error-guaranteed tokens, nested diagnostic grandchildren, and
non-UTF8 local source paths. Native semantic errors remain typed method results.
Native parser/expander calls are opaque intervals with deadline checks around
them; this does not establish an interruptible call or a process RSS bound.

The native worker forwarding implementation is in `crates/trust-proc-macro-bridge`;
its compiler duplex tests use this protocol and the real dispatcher. It is not a
loader or Ready producer. Native DSO/runtime closure loading, persistent per-dylib
ownership, source/environment consumption receipts, build-script and scoped-out
dependency containment, and platform qualification remain required.
The current PM-1 refusal and proof-authority rules remain in force.

The B3 static-child owner now accepts the compiler's original Session during
preparation and moves it into the child owner at launch. It no longer creates a
second Session behind its callback. The compiler Dispatcher returns the typed
method value and the owning transport creates the reply on that same Session.
This repairs an integration prerequisite; neither B3 nor the dispatcher is an
activated native macro loader. See B3's README for the explicitly selected Linux
child tests and their limits.

Compiler Span handles are canonical for their live native values: the adapter
reuses a handle only when the underlying rustc Span is equal. This preserves the
native ABI's interned Span Eq/Hash behavior without exposing raw hygiene IDs or
adding a wire method. Lookup work spends the original budget; stream ownership,
generation checks and terminal cleanup remain unchanged.


B3's prepared input closure now combines the static-worker/ordered-input digest
with the optional declared native graph. The compiler-issued Session binds the
same composite through native preparation, static preparation and the final
structural receipt. Equal Binding or Budget values still do not replace the
original SessionOwner. A prepared native-input receipt is not evidence of DSO
loading, constructor containment or worker consumption; PM-1 remains closed.
