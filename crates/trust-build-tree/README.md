# Native build-tree custody

This standalone package owns Trust's existing build-tree guard implementations.
Its manifest declares a literal `[workspace]`; it does not inherit the compiler
workspace or require its first-party submodule graph. Production dependencies
are `libc`, `tempfile`, `serde`, `serde_derive` and `serde_json`. The derive
dependency is separate, preserving Bootstrap's serde feature/parallel-build
policy. Bootstrap's `build_helper` reexports the same public
modules rather than maintaining a second implementation.

The optional `machine-admission` feature shares the existing `trust-build-cpu`
and its native hash library, plus the existing native descriptor courier in
`jobserver_utils` without constructing a GNU token client. Bootstrap and Targo enable this feature through
build_helper. Packaging this feature includes those sibling native libraries;
it does not compile the Rust compiler or require first-party solver sources.

| Module | Resource and scope |
| --- | --- |
| `trust_build_lock` | `NamespaceGuard` serializes short transactions on the persistent `.trust-build-lock.guard` inode. It is not a build-lifetime lock. |
| `trust_repo_lock` | `BuildLease` owns an exact `.trust-build-lock/info` holder in the existing build/measurement protocol. Independent acquisition owns its release; validated parent handoffs retain their explicit outer-owner release contract. `gone_independent_holder` only reads: it names a holder of a given purpose that is provably gone (the lock script's stale rule), so a stage-1 seed need not wait for it; it reclaims nothing. |
| `trust_repo_lock::management` | On macOS and Linux, `Manager` owns build/measurement acquisition, checked family reentry, native writer discovery/adoption, stale-owner recovery, bounded waiting, status, audited explicit recovery and surviving-writer handover in that SAME namespace. Native `BuildLease` drop uses its original pinned holder through this manager; it never rebuilds release authority from a matching pathname or token. |
| `trust_repo_lock::management::cli` | Shared native administrative parser and dispatch for `targo trust repo lock` and Bootstrap's early `--trust-build-tree-lock` entry. Both use the same manager without starting the shell facade or an interpreter. |
| `trust_repo_lock::incremental` | Inspects or reclaims only `crates/target*/debug/incremental`. Native root/profile checks, actual allocated blocks, volume thresholds, all three Cargo profile locks, detached-directory cleanup and one bounded observation request replace the Python reclaimer. |
| `trust_output_lock` | `OutputLock` owns the actual exclusive `<output>/lock` OS lock. It supports logical output-directory symlinks, refuses unsafe lock leaves, and can probe existing donor state without creating it. |
| `admission` | Native priority tickets and original worktree/slot claims in an explicitly selected existing build-slot namespace. Current native process births retain persistent adopted debt across exec and UID transitions. Unknown live requirements remain barriers; partial claims release every lock. Exclusive reservations retain admission/worktree while draining every historical numeric slot. |

Keep the actual guard values until all protected work settles. `check_current`
detects changes to the original identities and records; an error never adopts a
replacement or establishes that work has finished. PID text, paths and holder
descriptions cannot reconstruct ownership. The namespace mutex, repository
holder and output lock have distinct purposes; one does not substitute for the
others.

These are live-process mechanisms for cooperating build and cleanup actors.
They do not freeze source bytes, stop arbitrary filesystem edits/deletion,
provide SDK or Cargo-cache custody, establish descendant closure, or supply
crash-safe quarantine. Callers own child supervision and must retain the guards
through uncertain cleanup. A record left after process death is not proof that
its work ended. No installed toolchain, release tier or global resource pool is
changed by this package.

Native management enumerates the current account with the kernel's process
interfaces; it starts no `ps`, `pgrep`, `lsof` or interpreter child. Bootstrap
writers and Python/PyPy producer-scorecard invocations are scoped by physical
cwd or command path boundaries. This is discovery of known cooperating actors,
not a guarantee against arbitrary writers. Unknown records, uncertain process
identity, changed roots and unsafe audit files retain exclusion. Parent-managed
records keep their existing outer-owner settlement contract, including when
their holder PID is dead. Other platforms retain the pre-existing `BuildLease`
implementation; this is no native-management qualification claim for them.

The shell facade and its callers still remain. Native acquisition serves the
library API and the two administrative entries. `x.py` uses the native manager;
incremental maintenance callers use the native reclaimer. Other shell-facade
callers must migrate before that facade can be deleted.
Passing these controls does not satisfy the complete helper-retirement contract.

The native admission component does not yet activate a replacement launcher.
Its coordination locks are not CPU grants, original GNU credits, Host loans,
SDK/output custody or evidence that descendants settled. Canonical account
namespace selection, worker/fixed CPU bridging, measured exclusive quietness,
status/adoption publication, command supervision and all active callers must
migrate before deleting `build-slot`. No ambient job count or held-marker can
establish those permissions.

Fixed publication retains actual slot/worktree locks and writes the native
legacy-compatible full claim before releasing shared admission. Historical
indices remain representable without creating nonexistent gap slots. Native
room observations use only the current account's existing canonical pool;
a custom coordination directory cannot select machine authority. No actual
command launcher, original GNU-credit handoff or helper retirement follows
from these readiness observations alone.

With `machine-admission`, `Coordinator::attempt_fixed` publishes and judges a
complete unlaunched claim under the original native CPU manifest transaction,
before the queue ticket retires. CPU contention, unknown live metadata and
over-capacity totals release every partial worktree/slot/admission claim and
preserve the original ticket. The structured `Waiting::NativeCpu` value keeps
those causes distinct. An older eligible exclusive request retains queue
priority while releasing incomplete resource claims. Callers cannot construct
a `FixedClaim` by publishing a reservation and then waiting on CPU capacity.

`FixedClaim::prepare_command` owns a single shared command and the complete
original claim through exec and direct-child wait. A bounded anonymous packet
carries original descriptors; native SHA-256 binds the full path/device/inode/
role set in each constant-sized original record. The child duplicates and checks
every original, including the actual exclusive lock and same open description.
Omitted, foreign, replaced or changed members refuse. A smaller caller ceiling
is published in all original records before handoff, so nested commands cannot
restore an older larger budget. Positional reads preserve shared file offsets.
Only the forked child makes these descriptors inheritable; parent descriptor
flags stay unchanged. An inherited descriptor does not grant GNU/SDK/Host rights.
The running supervisor owns cancellation and the actual direct-child wait.
Dropping it cancels and reaps a live direct child before releasing the claim,
including when that executable has closed all inherited lock descriptors.
Natural exit codes survive repeated observations and cancellation after exit.
If owning retirement becomes unknown, the error is returned and Drop retains
the actual original descriptions for the remainder of the process lifetime.
This does not establish whole-descendant retirement or hosted-root closure.
Resource attribution and full descendant supervision remain pending. No global
command front door or caller migration is activated by these component APIs.

Native Targo now retains an `InheritedFixedClaim` in its invocation context.
The ordinary CLI validates it before project configuration or compiler discovery;
library callers validate before scheduler configuration. A fixed ceiling takes
precedence over generated worker hints, and explicit widening or mixed native
worker modes refuse. For an inherited GNU server, the build runner starts an
empty restricted FIFO. Each supplementary byte is funded by a retained actual
original GNU guard, up to the fixed ceiling minus the existing implicit credit.
Original anonymous pipes retain their descriptor flags. Retirement stops new
issuance and acquires/burns every restricted byte before returning the original
guards. Missing or unfunded bytes withhold retirement; unknown Drop retains
the original guards and fixed-resource custody. The ordinary no-inherited-server
path uses its existing scheduler within the checked ceiling. No Host/SDK
permission follows from the record or this scheduling transport.

Targo's opt-in `fixed-admission-system-tests` feature builds the maintained
`fixed_admission` integration harness and its associated actual CLI. Compile it
under `build-slot` with `--test fixed_admission --no-run`; run the printed test
executable outside that compiler's retained epoch. Its lightweight planning case
takes a real canonical slot with measured memory, accepts one job, rejects two,
and asserts no fixture units compiled. It uses no private machine pool or SDK
activation, and does not replace ordinary build/verification qualification.
Its GNU compilation case takes its own complete canonical three-CPU claim,
executes a real Rust build script through the associated Targo, observes actual
restricted credits, and requires all original inherited credits and descriptor
flags to match after the owning wait. Run this self-admitted case outside an
already retained compiler epoch; it does not create a second machine pool.

## Administrative commands

With `machine-admission`, `admission::status::current` observes the account's
existing canonical native CPU and legacy namespaces. The native Targo entry is
`targo --unverified resource status [--json]`, before project configuration or
aliases. Output is versioned JSON; the default is pretty JSON and `--json` is
compact. It accepts no pool, directory, CPU, memory or adoption option.

Native physical slots, retained external debt, legacy slots, the exclusive
admission fence, FIFO tickets and adopted records have separate graded outcomes.
Missing, busy and unavailable observations remain explicit. A successful shared
lock probe is called `shared_compatible`, never free admission. Owner records
are diagnostic data. Unlocked stale tickets and dead/reused adoption records
remain on disk. Status neither creates protocol files nor registers, repairs,
retires, adopts or acquires execution resources. Sequential rows are not an
atomic capacity or queue-eligibility decision; physical and retained CPU scopes
must not be added as independent execution credits. Non-UTF-8 path observations
remain original bytes. The status slice alone does not retire `build-slot`.

`admission::Adoption` publishes an existing same-account process as logical
legacy coordination debt. The thin native entry is
`targo --unverified resource adopt PID [--exclusive] [--memory-mib N] [--wait-seconds N]`.
It requires the process's current native working directory to match the caller's
held directory, and checks its original birth, executable and directory around
publication. The original FIFO coordinator must first hold the actual worktree
and slot locks. A shared adoption records one slot; an exclusive adoption drains
the complete historical slot population. The temporary admission fence is not
persisted as shared debt. Publication is create-only under the original registry
lock, with a synchronized complete record before the transient locks close.

Only the existing canonical legacy domain is supported. Activated mixed or
retired domains, inherited admissions and foreign namespace selectors refuse.
The PID supplies observation data, never CPU/GNU credits, process control,
descriptor custody, Host/SDK authority or release permission. The record tracks
the direct process's birth; it does not certify arbitrary descendant retirement.
Waiting retains the same ticket. A repeat observes one complete original record
without upgrading a shared record or replacing incomplete debt. A possibly
published error permanently poisons that attempt and preserves visible debt;
neither an output failure nor a missing reply authorizes automatic replay.
The core native tests and the thin frontend have separate qualification scopes.

The native fixed-command owner also provides `prepare_exclusive_command`.
It retains the original drained exclusive claim while measuring ten seconds
of host quietness: conservative native memory, finite one-minute load at most
35% of machine CPU width, and no other live cargo/targo/rustc/trustc process.
System PID/name observations use native APIs and never inspect other accounts'
arguments or working directories. Unknown facts, slow samples, observation gaps
and busy samples reset readiness. The actual spawn reobserves these conditions.
The nested fixed handoff retains the real exclusive fence and every historical
slot. These observations grant no Host/SDK authority and do not establish
arbitrary descendant completion. General launcher/caller migration remains open.

`PreparedFixedCommand::spawn_group` launches its actual child in a new session
and owns that original process group under the same complete resource claim.
`spawn_group_with_signal_forwarding` additionally installs a scoped standalone
launcher relay for INT, TERM and HUP. The relay refuses existing custom handlers;
call it at launcher startup without concurrent external signal-handler setup.
Its handler only records atomic pending bits. Ordinary owner polling forwards
them to the actual group and restores prior dispositions when custody ends.

`RunningFixedGroup` keeps its direct child unreaped while forwarding or cancelling,
so a supplied PID or recycled process-group number cannot select a signal target.
Its one owner must also be the child's only waiter. Completion requires the
original group to drain, the actual owning child wait, and a negative kernel
group-existence observation after reaping. No group signal follows that reap.
Keep the owner through IO drain as well as the wait. Cancellation targets only
the created group; uncertain retirement retains the actual original claim for
the process lifetime. Descendants escaping to another session/group require
the separate native workload protocol and do not become covered by this API.

The maintained integration harness also compiles real Rust and a build script
through the public grouped launch with signal forwarding, checking restricted
GNU credits and original descriptor flags after group retirement and IO drain.
These controls grant no Host/SDK authority or formal proof grade. General
launcher/caller migration and helper deletion require their own qualification.

`FixedCommandAdmission` owns admission-time fixed sizing as native policy. Its
automatic mode borrows only successfully acquired original shares, with fresh
measured memory for each share. An explicit CPU ceiling reserves enough shares
without borrowing idle extras. Budget selection and publication happen under
the same actual native manifest transaction; the retained original pool supplies
machine width. Unknown memory keeps the queue ticket without a resource claim.
Exclusive automatic sizing retains all original/historical slots but uses the
original CPU width. This API starts no command and grants no runtime resizing,
worker protocol, quietness, SDK custody or permission to retire callers.

`FixedClaim::into_runtime` is the separate **unlaunched-only** native owner
prerequisite. It withholds actual idle supplementary GNU tokens before returning
borrowed slot capacity, retains the request's original minimum/worktree and
memory floor, and uses the existing fair queue plus native manifest transaction
to reacquire physical backing before restoring bytes to the same FIFO.
`RuntimeClaimCurrency` checks original in-process identity and resize generation;
it is DATA, not a serialized courier or Host/SDK grant. Failed partial publication
poisons the owner; unknown exposed-owner Drop retains physical backing and burns
withheld bytes instead of silently refunding them.

This is not enabled by the ordinary fixed entry. V1 couriers export the original
slot OFDs to descendants, so dropping a parent's copy cannot release their locks.
There is intentionally no running/imported-V1 conversion or runtime launch API.
Cross-process activation needs the real retained group/host and versioned courier
to preserve backing across controller death and settle actual descendant work.
The current in-process owner/drop controls do not establish that crash protocol,
installed worker compatibility, machine-wide deployment or a performance gain.

The native Targo source entry is
`targo --unverified resource fixed [--cpus N] [--exclusive] -- <command> [args]`.
It admits before aliases/project configuration and launches the ordinary Targo
compile/test command under the original group supervisor and GNU handoff.
Worktree discovery uses libgit2 and the existing `<git-dir>/build-slot.lock`.
The supervisor keeps its actual claim until the original group retires; an
uncertain wait starts owned cancellation and retains resources until retirement
can be established. Hosted/root/SDK and existing fixed locators refuse a second
admission. This standalone fixed entry does not supply the separate hosted
worker/SDK protocol, resource attribution, status/adoption or general helper
retirement. Its source and actual CLI qualification are recorded separately.

Nested commands use a distinct authenticated ancestor courier for the complete
original fixed claim. An environment locator supplies routing only. Fresh SCM
rights must pass the same canonical pool, complete-file fingerprint, current
record, original open-description lock and budget checks; remote descriptor
numbers are never interpreted locally. Ordinary std descriptor isolation stays
enabled. Older readers receive a refusing legacy locator rather than silently
proceeding without the fixed ceiling. This courier grants no GNU credit or SDK
authority. Ignored launcher signals stay ignored across exec, and unsupported
SIGCHLD reapers refuse before group delivery.

`src/main.rs` also exposes this exact dispatcher as the standalone
`trust-build-tree` binary, including Bootstrap's `--trust-build-tree-lock` entry.
It adds no ownership or recovery implementation, and `x.py` neither builds nor
selects it: since 2026-11-09 an old toolchain must not compile a second
administrative program as a fallback. Unless `TRUST_BUILD_TREE_MANAGER_TARGO`
names one manager explicitly (no fallback), `x.py` probes, in order, this tree's
`build/bootstrap/{debug,release}/bootstrap`, then
`build-tree-manager.noindex/debug/bootstrap`, then PATH `targo trust repo lock`,
and refuses before any build-tree write when none answers protocol v2. The
second is this tree's own Bootstrap, which `scripts/build-tree-manager.sh`
builds with an installed Trust Targo for a tree that has no Bootstrap yet: an
explicit step, run before x.py, that writes nothing under `build/` and takes no
lease (FRESH-TREE-LOCK-FRONTEND-1 in `docs/DECISION_QUEUE.md`). The ordinary
native manager still decides every acquire, reentry and release.

```sh
targo trust repo lock --protocol
targo trust repo lock acquire --kind build --pid "$batch_owner_pid" --purpose build --repo-root "$checkout"
targo trust repo lock status --repo-root "$checkout"
targo trust repo lock release "$original_token" --repo-root "$checkout"
targo trust repo lock reclaim-incremental --repo-root "$checkout"
targo trust repo lock reclaim-incremental --repo-root "$checkout" --apply
```

Acquisition requires an explicit durable owner PID that spans the protected work;
a short-lived CLI process must not create a holder that is stale at birth.
Acquisition writes only its token to stdout. Exit 0 succeeds, 3 means busy,
4 retains a foreign or parent-managed holder, and 2 rejects invalid requests or
unavailable observations. Status returns 0 only for a free tree and never prints
a release token. Recovery requires an explicit meaningful `--reason`; an ambient
`TRUST_BUILD_LOCK_BREAK` does not authorize it. Root, wait and borrowed-token
defaults use `TRUST_REPO`, `TRUST_BUILD_LOCK_WAIT` and `TRUST_BUILD_LOCK_TOKEN`.

Bootstrap accepts the same arguments after `--trust-build-tree-lock`, before
configuration, lease acquisition or the build graph. Its administrative entry
and the existing namespace-guard entry are excluded from writer discovery:
neither starts build work. Actual Bootstrap build commands remain writers.

Incremental inspection is read-only by default. Reclamation starts at50GiB,
or below100GiB of volume free space when the cache occupies at least1GiB.
`--max-gib`/`--min-free-gib` and their `TRUST_INCREMENTAL_*_GIB` defaults select
thresholds; nonfinite, negative or unrepresentable values refuse. A valid zero
allocated-block count remains zero, including sparse files. Target aliases are
deduplicated; escaping aliases, unsafe locks and unknown observations refuse.
Applying cleanup first takes a separate reclaimer lock and tries all three Cargo
profile locks. A live builder yields Busy before recursive observation. Current
cache rename happens under those locks; all deletion follows their release, so
the next builder's new cache survives. One shared entry/depth/time budget covers
root discovery and every profile, checked between synchronous filesystem calls.
Neither blocked kernel calls nor detached-tree deletion have a hard deadline.
The supported builders must honor Cargo locks; hostile concurrent parent-directory
renames remain outside this protocol. No SDK/output execution grant follows.

## Test boundary

`management::Lease::into_withheld` consumes only owned, same-process original
custody. It atomically publishes `WITHHELD` in the same holder directory and
retains both original and new record descriptions. `WithheldLease` has no
release, import, serialization or Host transfer API. An actual open protected
scope can mint an opaque close-only source offer: same original root/holder
and acquired/WITHHELD record descriptions, all readonly, with the original
creator/deadline and before/after custody checks. Its bounded observations are
DATA, not Manager, execution, release or foreign-scope authority. The freshly
staged WITHHELD record becomes readonly before publication; exporting an old
writable original refuses rather than reopening it.
Drop, producer death, missing transport, ordinary token release and generic
break cannot release it. The active legacy facade likewise refuses this state,
including explicit break. Original Host closure/recovery is unavailable until
separately integrated and qualified. Conversion failures retain their owners;
only a proved unattempted, unchanged original can explicitly recover ordinary
lease custody. These are exclusion guarantees for cooperating actors, not a
source snapshot, execution grant or proof authority.

The default Unix harness executes the actual native management CLI in child
processes of the current test image. A test-only entry runs before libtest so
stdout is the production token/protocol response, with no harness text mixed in.
No shell facade, copied source script, newly invented helper binary or optional
external provider is involved. The initializer race, persistent namespace inode,
empty-directory release window, stale takeover and audit, exact token refusal,
seed wait and unknown WITHHELD records all run by default. Bootstrap compiles
those same native regression bodies and actors, rather than maintaining a
second policy implementation. Cold x.py invalid-guard controls remain separate.

The explicit `native-cli-tests` feature requires both `TRUST_BUILD_TREE_TARGO`
and `TRUST_BUILD_TREE_BOOTSTRAP` to name actual compiled executables. Namespace,
seed and WITHHELD administrative requests then use the selected Targo's real
`trust repo lock` frontdoor. Bootstrap's actual administrative protocol/status
and incremental reclamation controls remain. Missing inputs fail rather than
skip. Reclamation is synchronous before acquisition returns its one-line token;
there is no detached script or log-polling substitute. Native policy actors still
check exact original descriptors without pretending regular files are GNU pipes.

Bootstrap's own `native-cli-tests` feature additionally requires
`TRUST_NAMESPACE_BOOTSTRAP_CONTROL` and
`TRUST_NAMESPACE_OLD_BOOTSTRAP_CONTROL` for actual current/old parent-release
parser controls. An old image must refuse the new spelling; current missing,
partial and foreign-parent handoffs must refuse before reading configuration.
The default parser unit control makes no actual-executable claim.

The former `repository-tests` feature is removed: the native initializer and
WITHHELD controls no longer depend on a surrounding copy of the shell facade.
The standalone leaf remains independently testable. Historical inventory and
source-qualified runs in dated validation records retain their original scope;
current counts come from the actual test image, not these instructions.

The `machine-admission` feature adds genuine fixed-claim, handoff and group
lifecycle controls. Original process actors retain their own actual native
children through reap. Positive last-close assertions observe physical lock
release, including inherited CLOEXEC copies held until concurrent children exec;
live/unknown/held negatives remain immediate. These are coordination tests, not
proof, SDK, arbitrary descendant closure or release authorization.

Each output-lock entry but the actor runs alone in a fresh process of the same
test binary, because a concurrent spawn keeps a closed lock's description alive
until the child's exec; the harness may therefore run in parallel too. The
`EPERM` lease entry needs a user that is not root and a pid 1 of another user
(as on macOS); elsewhere it fails, saying so, rather than skip.

Use the genuine SDK Targo at its explicit path for these commands from the Trust
root (`SDK_TARGO` below denotes that selected executable):

```sh
"$SDK_TARGO" --unverified test --manifest-path crates/trust-build-tree/Cargo.toml --frozen --lib
TRUST_BUILD_TREE_TARGO="$compiled_targo" TRUST_BUILD_TREE_BOOTSTRAP="$compiled_bootstrap" "$SDK_TARGO" --unverified test --manifest-path crates/trust-build-tree/Cargo.toml --frozen --lib --features native-cli-tests
"$SDK_TARGO" tippy --manifest-path crates/trust-build-tree/Cargo.toml --frozen --all-targets --all-features -- -D warnings
```

Run the all-feature lint command in the full Trust source layout. Execute heavy
qualification through the existing machine-wide `build-slot` admission. The
explicitly unverified test lane and passing checks confer no formal proof grade.

This package adds no importer or consumer-specific source copy. Any later
packaging must preserve the canonical implementations and their dependency,
licence and test boundaries; that integration needs its own qualification.
