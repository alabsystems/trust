# Windows genesis bootstrap (x86_64-pc-windows-msvc)

Builds Trust natively on Windows by **genesis-bootstrapping from the pinned stock
Rust nightly** — the same upstream commit as the mac/Linux genesis roots
(`14cae68132`, `nightly-2026-07-09`, `1.99.0-nightly` — the recorded genesis
trust root #3). The genesis pin is host-invariant:
rustup ships that nightly for `x86_64-pc-windows-msvc`, and it is within one minor
of `src/version` (1.99) so bootstrap's `check_stage0_version` accepts it. This is
the Windows equivalent of `scripts/create_local_genesis_stage0.py` (POSIX-only:
`#!/bin/sh` wrappers + `os.symlink`).

> **Version note.** `win_genesis.py` is version-agnostic: it wraps *whatever*
> `rustc` is on PATH and stamps with `compiler_date` from `src/stage0`. Install
> the pinned nightly below and it produces a current (1.99) genesis. The original
> validation used stock stable `1.96` when `src/version` was 1.96; the compiler
> core was proven to build then and needs a re-run at 1.99 on a Windows box.

Compiler-core build validated on `x86_64-pc-windows-msvc`, 2026-06-29 (at 1.96;
see Status). 1.99 re-validation pending Windows compute.

## What's here

- **`genesis_wrapper.rs`** — a tiny compiled `.exe` wrapper. Each genesis stage0
  bin is a copy of this exe; it reads a sidecar `<name>.wrap` to learn the real
  stock tool to drive. It strips only Trust-owned `-Ztrust-verify=off` and
  `-Ztrust-*` flags (stock rustc can't parse them) and forwards everything else.
  Compiler `--version` remains `rustc …` because `libc`'s build script asserts
  that identity. The three Tippy sidecars instead normalize supported version
  probes to canonical `tippy` product identity; both frontends supply
  cargo-clippy's private marker, and `targo-tippy` first strips Targo's public
  marker so direct options are never discarded.
- **`win_genesis.py`** — lays out `build/x86_64-pc-windows-msvc/stage0`: compiles
  the wrapper, writes the canonical bin `.exe`s + `.wrap` sidecars (with only
  `rustc` and `cargo` retained as stock compatibility aliases), a `lib/`
  **directory junction** to the stock sysroot lib (no admin needed), and the
  `.trustc-stamp` / `.rustc-stamp` stamps. The coherence check keeps this surface
  identical to both bootstrap implementations.

## Prerequisites (no Rust install is required to *consume* a real seed; this
genesis path uses a stock Rust as the seed)

1. **MSVC C++ build tools** (`cl`/`link`) + Windows SDK, **CMake**, **Ninja**:
   `winget install Microsoft.VisualStudio.2022.BuildTools --override "--quiet --wait --add Microsoft.VisualStudio.Workload.VCTools --includeRecommended"`,
   `winget install Kitware.CMake`, `winget install Ninja-build.Ninja`.
2. **Python 3.11+** (invoke as `py -3`; `python3` is the Store stub).
3. **The pinned stock Rust nightly (msvc)** as the genesis seed:
   `rustup-init -y --default-host x86_64-pc-windows-msvc --default-toolchain nightly-2026-07-09 --profile minimal`
   then `rustup component add rustfmt clippy rust-analyzer`. Verify
   `rustc --version` shows `1.99.0-nightly (14cae68132 …)`. (Any nightly within one
   minor of `src/version` works; `nightly-2026-07-09` is the recorded pin.)
4. **`~/.cargo/config.toml`**: `[http]\ncheck-revoke = false` (Windows blocks the
   cert-revocation check in some networks; cargo's index fetch fails otherwise).
   Use `curl --ssl-no-revoke` for the same reason.
5. An authenticated superproject-only checkout. Run
   `py -3 scripts\recreate_bootstrap.py --genesis --no-build --no-register`
   once to let the canonical recreator materialize only missing indexed
   gitlinks; do not run a recursive ambient submodule updater.

## Build

```bat
py -3 scripts\win-genesis\win_genesis.py
```

Write a repo-root **`bootstrap.toml`** (gitignored) pointing each stage0 tool at
the genesis adapter (the `.exe` suffix is required on Windows; relative `file://`
seed download is skipped because these are present):

```toml
change-id = "ignore"
[build]
docs = false
compiler-docs = false
rustc        = "<repo>/build/x86_64-pc-windows-msvc/stage0/bin/trustc.exe"
cargo        = "<repo>/build/x86_64-pc-windows-msvc/stage0/bin/cargo.exe"
rustdoc      = "<repo>/build/x86_64-pc-windows-msvc/stage0/bin/trustdoc.exe"
rustfmt      = "<repo>/build/x86_64-pc-windows-msvc/stage0/bin/trustfmt.exe"
cargo-clippy = "<repo>/build/x86_64-pc-windows-msvc/stage0/bin/targo-tippy.exe"
[llvm]
download-ci-llvm = false
ninja = true
targets = "X86"
[rust]
download-rustc = false
channel = "trust"
deny-warnings = false
```

Then, with `cmake`/`ninja`/`~/.cargo/bin` on `PATH` and
`CARGO_HTTP_CHECK_REVOKE=false`:

```bat
py -3 x.py build --stage 2 --build x86_64-pc-windows-msvc
```

> Always pass `--build x86_64-pc-windows-msvc`: from Git Bash, bootstrap's
> `uname`-based triple detection defaults to `x86_64-pc-windows-gnu`.

## Status

**Compiler core — validated 2026-06-29 (at src/version 1.96); needs a 1.99 re-run.**
The 1.99 update is data-only (pinned nightly + this doc); `win_genesis.py`'s logic
is unchanged, so re-running the steps above with the pinned nightly on a Windows
box should reproduce the result at 1.99. That re-run needs Windows compute a
maintainer macOS/aarch64 host does not have.

**Builds natively on Windows from the genesis seed (as of the 2026-06-29 run):**
the genesis stage0 is accepted (no download), **LLVM** builds from source
(CMake 4.x OK), the **entire `rustc`/`trustc` compiler crate set** compiles,
**`std`** compiles, and the build reaches **stage1 compiler artifacts** — i.e.
`trustc` itself is compiling.

**Verifier-stack Windows port — pure-Rust surface DONE + cross-check-verified;
native backends need a Windows box.**

The Trust-owned verifier crates now cross-check clean for `x86_64-pc-windows-msvc`
via `cargo check` (type/borrow-checks without linking, so it runs from a Unix
host with no MSVC linker). Gate: **`scripts/win_cross_check.sh`** — 17 pure-Rust
crates green (`trust-router`, `trust-cache`, `trust-deps`, `trust-wp`,
`trust-loop`, `trust-vcgen`, `trust-report`, `trust-proof-cert`, … ).

- `crates/trust-router/src/coordinator.rs` — **DONE.** The `std::os::unix::net`
  (`UnixListener`/`UnixStream`) transport was already `#[cfg(unix)]`-gated with a
  `Reservation::inert()` fallback off-Unix; the only real gap was the daemon
  binary `src/bin/trustd.rs`, which called the `#[cfg(unix)]` `coordinator::serve`
  unconditionally (broke the Windows build). Now gated: on non-Unix, `trustd` is a
  documented no-op (there is no Unix-socket daemon; clients use inert reservations).
  Cross-check green.
- `first-party/trust-wp/.../verify/process_isolation.rs` — **PORTED** (POSIX
  `fork`/`waitpid`/`RawFd` confined to `#[cfg(unix)] mod unix_impl`, inline-verifier
  fallback off-Unix).

Remaining — the **native ay/trust-mc/clean backends**, which a maintainer macOS
host cannot cross-verify (their C deps — `stacker`/`cc`, GMP via `rug` — need a
Windows C cross-toolchain, and the trust-mc issue is a *link* failure `check`
cannot observe). These need a real Windows box:

- `first-party/trust-mc/trust-mc-driver` fails to link `ay-chc`/`ay_bindings`
  under the **documented `ay` source-id resolver nondeterminism**
  (root `Cargo.toml:209-231`). `trust-router/trust-build` is coupled to the full
  native trust-mc adapter, so there is no clean metadata-only fallback.
- `crates/trust-router/src/full_verification/.../bundle_evidence.rs` and peers
  call native-only adapter methods under `cfg(feature = "trust-build")` — behind
  the same native-backend features that don't cross-compile off-Windows.

The compiler core (LLVM + rustc/trustc + std) is proven to build on Windows, and
the pure-Rust verifier surface (incl. the coordinator IPC) is Windows-ported and
cross-check-verified; the native backends need a focused Windows pass + the
ay-resolver fix, on Windows hardware.
