# Native CPU leases

This leaf library provides one kernel-held lease per executing build unit.
Native workers have no whole-build CPU reservation. Explicit external custodians
can retain fixed-width bundles through `ExternalDebt`. Production dependencies
are `std`, `libc`, and the dependency-free first-party `trust-sha2` commitment
leaf; no UI or verification-engine crate is required.

`Pool::for_current_user` resolves the account's home from the Unix account
database and opens `Library/Caches/aterm/capacity/build-cpu-v1` on macOS or
`.cache/aterm/capacity/build-cpu-v1` on other Unix systems. A scratch `HOME`
does not create a separate pool. The pool width is machine capacity, not a
single build's `-j` limit. Conflicting widths are rejected.

The computer-level aterm/Aos resource service owns that capacity and pool
initialization. Targo and compiler workers are clients of its policy. This
crate supplies the shared lease mechanism; it is not an independent machine
scheduler or authority for choosing how much work the computer admits.

The optional `member` feature provides `MemberScheduling`, retaining the
original `Lease`, `LegacyFence`, selected GNU jobserver and authenticated
CPU handoff together. It creates no pool, epoch or GNU credits. Targo's ordinary
compiler and authenticated test dispatch use this same backing; a retained test
capsule also holds its actual dispatch owner so borrowed-credit exclusion and
descriptor admission last through the capsule's final close. A scheduling
capsule supplies no memory reservation or member-launch authority. Those still
belong to the execution custodian, through actual descendant retirement.

`Pool::try_acquire` returns one available `Lease`, or `None` without waiting.
The caller supplies scheduling, fairness, cancellation, and memory admission.
It must not hold a CPU lease while waiting for nested work that needs the
same pool. The primitive alone does not enforce all compiler, build-script,
or foreign GNU jobserver CPU use.

A lease's raw file remains locked until its final duplicated or inherited
descriptor closes. There is no explicit unlock on `Drop`; a parent releasing
its copy cannot release its still-running child's copy. `into_file` and
`AsFd` let existing checked launch code transfer it without changing global
descriptor-inheritance flags.

The versioned manifest records slot device/inode identities. Replacing a
slot file cannot create another usable copy of that slot: old and new pool
handles refuse the mismatch. New files are private, regular, single-link
files. The owner-owned capacity parent may be readable by others but cannot
be writable by them. Do not remove or replace a live pool directory.

`Pool::open_existing` and `snapshot` are nonblocking, read-only observation.
They report an initializing or inconsistent pool as unavailable. An unlocked
slot is available regardless of its stale metadata. A held slot's owner is
reported metadata, not independently authenticated ownership or proof
authority. Other platforms currently expose only the record types; the
native pool implementation is Unix-only.

`RetainedPool` is a separate mechanism for an explicitly new private domain,
before any host-wide migration. `create_private` requires an absent path and
places a regular-file fence at the legacy pool name before publishing the
retained backend. It neither changes the account default nor permits two
global CPU budgets. Its physical root, fence, manifest and slot identities are
validated on use; incomplete or malformed state fails closed.

Acquiring a `RetainedLease` syncs retained debt before returning its controller.
The controller cannot be cloned or exported as a writable descriptor. Drop
and process death leave the debt recorded, even after the kernel lock is gone.
No API recovers release authority from a path, PID or decoded record.

The caller must establish that **all work backed by the credit has ended**
before calling `settle(self)`. Settlement consumes the original controller,
checks its identity and claim, and writes and syncs an explicit Free record.
Successful settlement confirms durable Free. An error or crash once writing
starts can leave Retained, malformed or Free state, so an error does not promise
continued debt. The library does not establish descendant completion or supply
a production host scheduler, global migration, or post-crash recovery policy.

## Original recovery authority

`ExternalDebt::prepare_recoverable` generates private material before grant. Its
`persist` creates and flushes an original private authority file and its directory
before returning a one-use `PreparedRecovery`; room refusal preserves that token.
Only then can `try_reserve_recoverable` publish nonce-and-secret commitments under
the shared native manifest transaction. The custodian must separately persist
its actual memory-cohort epoch and attempt context before issuance.

After controller death, `restore_recovery` verifies the original private secret,
actual native/retained domain, context, width, slot and generation. The returned
`RecoveredReservation` restores original settlement ownership and cannot issue
or launch new work. Public identities and nonces cannot construct it. The host
must establish authenticated original memory closure or applicable later-boot
closure **before** settlement; neither a PID nor the secret proves completion.
Partial or malformed records remain unavailable. No recovery path repairs them
or interprets damaged/missing data as free capacity.

An unused `NativeCapacityBank` can be consumed into
`ScopedNativeCapacityBank`. Each loan rekeys the SAME occupied shadow unit to a
newly persisted, immutable per-unit recovery capability before exposing native
backing. Safe return rekeys it again to fresh idle-bank custody; no Free record
or additional capacity appears. Old bank/borrower keys cannot settle a later
borrower's nonce, even when bookkeeping omits that borrower. Partial writes and
lost ACKs retain the same capability/transition and accept only its original
preparation for retry. Existing v1 and recoverable-v2 encodings are preserved;
fixed v1 custody cannot be converted. The host must bind borrower contexts to
actual original memory scopes, retain token/phase/group ownership, and prove
closure or loss-safe exclusion before a return. These primitives do not supply
that Host/SDK authority, activate a domain, or establish default readiness.
