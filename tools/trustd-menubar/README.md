# Trustd Monitor for macOS

A standalone macOS menubar monitor that shows the live status of the **Trust
memory-coordination daemon** (`trustd`) — the per-user host-domain admission
coordinator for participating crate-mode `trustc` workers. It was introduced in
response to the 2026-06-17 143 GB-on-36 GB OOM incident.

This `.app` is a focused coordinator/status companion, not a standalone Trust
toolchain app. It does **not** bundle, install, or configure the Trust compiler
toolchain, and a healthy coordinator indicator is not a proof or verification
result. The universal app itself is compiled by Apple Swift; separate Stage2
provenance applies only to the Trust compiler/daemon artifacts it observes.

The menubar dropdown shows:

- **compatible STATUS connected / unavailable** (filled or slashed shield)
- **configured allowance vs reserved** — this daemon's ledger, not host free RAM
- **active workers** — one row per live reservation in this daemon
- **queue depth** — this daemon's RESERVE waiters currently parked on admission
- **granted / released** counters from this daemon's lifetime
- **uptime** — from this daemon's `started_at`
- a **four-page Guided Tour**, shown on first launch and available from the menu

## First connection

Trustd Monitor is an installable `.app`, but it is intentionally not a Trust
toolchain distribution. To see live data:

1. Install the Trust toolchain separately using the repository's supported
   installation workflow.
2. From a Trust crate, run `targo trust check`. Crate mode starts the packaged
   `trustd` companion at one private endpoint shared across this user's Cargo
   target directories.
3. The app derives and discovers that endpoint automatically, including from
   Finder. Open **Set Up…** only to inspect it or configure an explicit manual
   endpoint.
4. Choose **Retry Now** if needed. The menu should show the compatible
   coordinator within the next poll interval.

`trustd` shuts itself down after about five minutes with no worker activity.
An offline shield between builds is therefore expected; starting the next
crate-mode build and choosing **Retry** reconnects the observer. The app never
starts, stops, installs, or upgrades the daemon itself. **Copy Diagnostics**
captures the selected/discovered path, source, last outcome, and timestamps for
troubleshooting without changing daemon state.

A clean idle shutdown records a durable CLEAN epoch and the next build starts
normally. An unclean trustd exit (SIGKILL, OOM, abort, or unexpected server
failure) deliberately leaves DIRTY and blocks automatic restart so a fresh empty
ledger cannot overlap an older solver. The monitor remains read-only and cannot
clear this state. First establish that **all solvers admitted by the prior daemon
are gone**. Set `TARGO` to the absolute Targo path already selected and validated
for that toolchain, then derive and run its same-sysroot sibling; do not run a
bare `trustd` from `PATH`:

```sh
TARGO=/absolute/path/to/selected/sysroot/bin/targo
case "$TARGO" in /*) ;; *) echo "TARGO must be absolute" >&2; exit 2;; esac
TRUSTD=${TARGO%/*}/trustd
test -x "$TRUSTD" || { echo "missing sibling trustd: $TRUSTD" >&2; exit 2; }
"$TRUSTD" --recover-after-crash --confirm-no-solvers \
  --socket /tmp/trustd-runtime-locks-$(id -u)/trust-memory-jobserver.sock
```

Do not run recovery while any prior solver remains; the confirmation is the
operator's safety attestation, not a mechanically checked proof. The daemon's
durable epoch records CLEAN/DIRTY only and cannot enumerate processes admitted
by the crashed instance. If you did not retain enough operational context to
establish that every prior solver exited, reboot the host first; then run
recovery before starting another Trust build. Deriving an absolute sibling
prevents ambient-`PATH` selection; it does not by itself prove distribution
provenance, packaged byte identity, or which bytes executed. Those remain claims
of the separate toolchain-validation process, not of this observer.

It polls the daemon's `STATUS` endpoint every **1.5 s** over the daemon's
`AF_UNIX` socket (`/tmp/trustd-runtime-locks-<euid>/trust-memory-jobserver.sock`;
`/tmp` is canonicalized on macOS), requires the exact frozen
`trustd.status.v1` JSON schema, and updates the menu. It rejects malformed
framing, unknown fields, inconsistent
budget arithmetic, invalid UTF-8, oversized/drip-fed responses, and endpoints
owned by another user. A connected indicator is prominently labeled as a
same-user, protocol-compatible endpoint and shows its discovery source. The
observer does not compare `IDENTITY` to exact packaged daemon bytes, so the
green state is deliberately not a packaged-daemon identity claim. Socket
discovery and I/O run outside the main UI actor.
If trustd's current host/cgroup ceiling falls below already-granted work, the
schema retains those reservations and reports zero free capacity; the app shows
the pressure as full instead of discarding the safe overcommitted snapshot.
`STATUS` covers only this daemon's configured allowance and participating
clients. It does not observe a separately selected file-bucket ledger,
nonparticipating or raw workers, or physical host RSS. A compatible endpoint
therefore does not prove a machine-wide memory ceiling or that every worker is
participating. When no compatible endpoint answers, the UI says only that this
coordinator is unavailable to the observer; it does not infer that `trustd` is
stopped or that another admission lane is active.

## Read-only by design

The app **only ever sends `STATUS` and `PING`** — never `RESERVE` or `RELEASE`.
The observer can never perturb admission control. There is no UI to grant, free,
or shut down anything (a `Quit` button only terminates the menubar app itself).

## Guided Tour

The first launch opens a short walkthrough covering the separate Trust install,
crate-mode auto-start and idle lifecycle, per-user endpoint discovery, shield
states, the distinction between coordinator health and verification, and its
read-only protocol. Choose **Guided Tour…** in the menu to reopen it at any time.
The tour links directly to Connection Settings.

For development, reset the first-run marker with:

```sh
defaults delete name.andrewyates.trustd-menubar guidedTourPresentedVersion
```

## Socket discovery

In order, the first path that answers a `STATUS` wins (and is then sticky):

1. The path saved in **Connection Settings…** (absolute or `~/…`).
2. `$TRUST_MEMORY_JOBSERVER_SOCK` — the env `targo` exports for workers (exact).
3. `$TRUSTD_MENUBAR_SOCK` — explicit override for the observer.
4. The fixed per-euid host endpoint used by normal verified builds.

Automatic host-endpoint discovery is Finder-safe and requires no saved setting.
Open **Connection Settings…** from the Guided Tour (or **Set Up…** from the menu)
to inspect the standard path or save, test, retry, reuse, or clear an explicit
override. Saving a path does not start `trustd`; if the saved endpoint is down,
discovery continues so an active standard endpoint can still be shown.

## Build

No Xcode project, no `xcodebuild` — just Apple's CommandLineTools `swiftc`:

```sh
./build.sh
```

This compiles `Sources/TrustdMenubar/*.swift` and assembles
`TrustdMenubar.app` (with `Contents/MacOS/TrustdMenubar` + `Contents/Info.plist`,
`LSUIElement = true` so it is menubar-only). A non-zero `swiftc` exit fails the
companion-app build; this is not a Trust compiler self-verification claim.
The build script ad-hoc signs and verifies the local bundle after assembly. It
does not provide a Developer ID signature or Apple notarization. Launch with:

```sh
open TrustdMenubar.app
```

For an atomic current-user publication followed by a fresh launch, use:

```sh
./install.sh --open
```

The fixed destination is the current account's
`~/Applications/TrustdMenubar.app`, derived from the macOS account database
rather than `$HOME`. The installer verifies that an existing leaf belongs to
this app, takes cooperative build/install locks, and binds source, staged, and
final bundles to the same ordered `arm64`/`x86_64` CDHashes. Publication uses
descriptor-relative `RENAME_EXCL` or `RENAME_SWAP`; an existing app remains one
complete old-or-new directory across the namespace operation. `--open` asks an
existing current-user `TrustdMenubar` process to terminate and launches a new
instance from the installed path. A launch failure is a warning after install.

The ad-hoc signature checks bundle coherence, not publisher identity. This is
not Developer-ID/notarized distribution or a fully durable storage transaction:
a power loss may leave a hidden staging directory, although the destination
rename cannot expose the old two-move missing-app window.

The build emits a universal `arm64 + x86_64` executable with a macOS 13
deployment floor. Each slice is compiled with Swift 6 strict concurrency and
warnings-as-errors. The completed bundle is architecture-checked, ad-hoc signed,
and atomically published with verified rollback to the prior app on failure. The
generated bundle is ignored by Git. This is a local developer
build, not a downloadable release artifact, and it is compiled by Apple's Swift
compiler—not by the Trust Rust toolchain.

## Tests

Run the source-level contract suite without producing or signing an app bundle:

```sh
./test.sh
```

It Swift-6 typechecks the complete production source set, then compiles a
temporary contract executable. Tests cover strict STATUS parsing and a live
same-user socket deadline, configured-path normalization/discovery precedence,
typed missing/non-socket failures, per-euid host-path derivation, truthful reconnect
transitions, cancellation generations, diagnostics, and the single-task polling
lifecycle. They also execute atomic swap/no-replace and rollback behavior,
symlink refusal, and cooperative lock contention. A source contract checks the Swift schema literal
against the Rust coordinator. The temporary directory is removed on exit.

## Layout

| Path | Role |
|---|---|
| `Sources/TrustdMenubar/TrustdMenubarApp.swift` | `@main App` + `MenuBarExtra` (NSStatusItem) + accessory activation policy |
| `Sources/TrustdMenubar/MenuView.swift`         | SwiftUI dropdown content (gauge, counters, worker rows, off-state) |
| `Sources/TrustdMenubar/GuidedTour.swift`       | first-run/on-demand four-page tour + accessory window presenter |
| `Sources/TrustdMenubar/ConnectionSettings.swift` | persisted path UI + test/save/automatic-discovery actions |
| `Sources/TrustdMenubar/Poller.swift`           | single-lifecycle async `StatusPoller` + socket discovery |
| `Sources/TrustdMenubar/Status.swift`           | `Codable` `trustd.status.v1` model + raw POSIX `AF_UNIX` client + formatting |
| `Resources/Info.plist`                         | bundle metadata, `LSUIElement = true` |
| `Tests/ContractTests.swift`                     | deterministic schema, configuration, and lifecycle contracts |
| `test.sh`                                       | temp-only Swift and atomic-install contract runner |
| `AtomicPublish.c`                               | fd-relative atomic no-replace/swap publisher |
| `verify-app.sh`                                 | exact two-architecture local bundle verifier |
| `build.sh`                                      | Apple `swiftc` → atomically published local `.app` build |
| `install.sh`                                    | verified atomic current-user publication + optional fresh launch |
