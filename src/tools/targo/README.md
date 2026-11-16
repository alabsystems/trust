# Targo

Targo is Trust's Cargo-derived package manager and build orchestrator. It
resolves dependencies and drives the selected Trust toolchain as one coherent
unit.

Branded Targo compilation never silently chooses an unverified lane, and for
the verbs whose artifact outlives the invocation it does not choose one at all.
Use `targo trust check` (or another authenticated `targo trust ...` workflow)
when verification and proof artifacts are the intended result. The unverified
lane prints an `UNVERIFIED` warning and makes no proof claim.

**Which verbs refuse, and which proceed.** `build`, `check` and `test` are
refused until a lane is named — the verifier driver has a counterpart for each,
so the refusal steers (`targo trust build` / `targo --unverified build`).
`install`, `package`, `publish` and `miri` are also refused: they have no
verified lane, but their output leaves the machine (a binary on a `PATH`, a
crate at a registry) or mints a verdict someone will read as checked, so the
typed `--unverified` is a human owning the choice the artifact's consumers
inherit. The local development verbs — `run`, `fix`, `clippy`, `bench`, `doc`,
`rustc`, `rustdoc`, and `-Zscript` — proceed on their only lane and announce
it: for them a refusal could only make the operator retype the identical
command, a toll that builds the type-`--unverified`-without-reading reflex.

This boundary is the resolution of a drift that stood for a month: between
2026-08-20 (`4c0c5e9f66`) and 2026-09-01 *every* single-lane verb proceeded —
`targo publish` included — while this README promised the old refusal and the
integration suite still pinned `miri` refusing. The width-vs-argument analysis
is `docs/2026-09-01-targo-single-lane-selection-blast-radius.md`; the code now
implements its disposition 1, which is what the integration tests asserted all
along.

`targo tippy` selects its explicit unverified lint transport itself and is not
a native compilation command, so it neither warns nor starts a broker. Its
alias `targo clippy` IS one, so `clippy` prints the `UNVERIFIED` warning where
`tippy` stays silent — interchangeable in what they run, not in what they say.
In a branded invocation the target-info probe runs the selected compiler, never
`RUSTC_WORKSPACE_WRAPPER`, so `targo tippy` (tippy-driver as that wrapper)
matches `[target.'cfg(..)']` tables, platform dependencies and build scripts'
`CARGO_CFG_*` exactly as `targo --unverified check` does, a
`[target.'cfg(trust_verify)']` table included. `cfg(trust_verify)` itself stays
false in a lint compile, whose verification is off, and lint compiles of
workspace members run one front-end thread whatever `-Zthreads` asks
(DECISION_QUEUE T14-TIPPY-1). In the explicitly unverified lane
(`targo --unverified`, and `targo tippy`, which runs it) the probe keeps the
lane's `-Ztrust-verify=off`, so every other cfg (`overflow_checks`,
`ub_checks`, `contract_checks`, …) follows the lane's units, and so does a
refusal that depends only on whether they verify; the probe still drops the
lane's other `-Ztrust-*` options and the MIR-pipeline options, so a refusal
that depends on one of those fires at the first unit instead. `trust_verify`
alone comes from one more `--print=cfg` query at the compiler's default, with
the Trust options and those a Trust compilation refuses dropped from it; that
query is a verifying compile, so it still refuses the compiler's legacy Trust
environment variables (`AY_PATH`, `TRUST_LEVEL`, …) the lane's units accept
(DECISION_QUEUE TARGO-PROBE-LANE-1). The verified lane's probe is unchanged,
and so is the probe of `targo trust`'s unit-graph preflight, which runs in the
unverified lane with a lane handed to it and resolves the verified build's
graph. Commands outside every lane (`targo tree`, `targo metadata`) still probe
at the compiler's default.

`targo trust` hands Cargo its lane in the private variable
`TRUST_TARGO_LANE_RUSTFLAGS`. A branded invocation appends it to the project's
rustflags, resolved by Cargo's own precedence, so a verified unit compiles with
`<project> <lane>`; the lane owns the codegen backend, LLVM plugins,
`-Cllvm-args`, and the safety checks and codegen contract it sets, and a project
spelling of one is dropped with a notice naming its source (DECISION_QUEUE
T14-APPEND-1/2). Under a lane an argument file (`@path`) or a `--` in the
project's flags is refused, naming its source: rustc expands the file wherever
it sits, so its flags could not be classified. An environment value that
replaces configured tables (Cargo's precedence) is named in a note. No child
process sees the variable: it is scrubbed from compilers, trustdoc, build
scripts and tests. Outside the verified lane it may carry only what `targo
trust` hands its probes (trust-cg's codegen contract and the strict safety
checks), so it is no second ambient rustflags channel.

When code run by an explicitly authorized command recursively invokes the
`$CARGO` frontend (for example, a compile-test harness), Targo preserves that
same unverified lane through a live authority broker started only by the exact
explicit CLI lane. Nested Targo does not trust the broker address, an inherited
descriptor, or Cargo configuration: client and server authenticate each
other's kernel PID, opened executable identity, PID lifetime, and ancestry on a
fresh connection. Nested Targo prints its own `UNVERIFIED` warning and keeps
verified invocations fail-closed. Linux uses abstract Unix sockets and pidfds,
so abnormal exit leaves no socket path behind. macOS (DECISION_QUEUE
T14-EXPORT-2) authenticates the same facts through other handles: the peer's
audit token (pid and pid version) for process identity, the code-directory hash
read through that token for executable identity (an image without one is
refused), and `proc_pidinfo` unique ids for ancestry; its endpoint is a socket in
a fresh `0700` directory under the per-user temporary directory, removed when
the root exits. Other platforms do not propagate this authority until
equivalent handle-bound checks exist. The address travels in
`TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT` (before T14c,
`TRUST_TARGO_NESTED_UNVERIFIED_BROKER`, which is no longer read and is removed
wherever the new name is, so a pre-T14c Targo, which stops when an address does
not authenticate, never sees one it cannot authenticate). An address that does
not authenticate (a path a killed root left, another Targo build's root, a
replayed environment) grants nothing and stops nothing: a typed `--unverified`,
the verified lane and every verb that compiles nothing proceed on their own,
and a compile verb naming no lane is refused with a note naming the address.
An explicit lane beats an inherited one: `targo trust` run under an
explicit-unverified ancestor keeps its verified lane, and never asks the
broker. Each client binds an
unpredictable one-shot callback address; the broker must actively connect back,
and the kernel-reported callback peer must be the authenticated Targo ancestor.
This broker boundary assumes the ancestor Targo process itself has not already
been compromised by injected code (for example, a preload constructor or
ptrace). No secret or state held inside a process can distinguish Targo from
arbitrary code already executing as Targo; release-grade resistance to that
class requires an external, handle-bound launcher/attester. The broker does
reject forged environment/configuration values, inherited listeners serviced
by helper processes, unrelated executables, stale PIDs, and reparented peers.
Propagation also requires broker and client to share a Linux PID namespace and
usable procfs/pidfd view; container-boundary mismatches fail closed. The root
`targo --unverified run` keeps its broker alive by supervising its target
instead of replacing itself. It forwards SIGHUP, SIGUSR1/2, SIGALRM and
SIGTERM; it does not forward SIGINT or SIGQUIT, which a terminal (or a
job-control parent) sends to the whole process group, target included, so a
forwarded copy would arrive twice. Like `system(3)` it outlives them and ends as
its target does; a SIGINT sent to the supervisor's pid alone therefore does not
reach the target (signal the group, or send SIGTERM). On macOS, which has no
parent-death signal, a supervisor killed with SIGKILL leaves its target running.
On macOS a target ended by a signal that writes a crash report (SIGQUIT,
SIGILL, SIGTRAP, SIGABRT, SIGFPE, SIGBUS, SIGSEGV, SIGSYS) ends the supervisor
with one line and exit `128 + n`, so no second report is written for targo. The
verified lane exports no authority, and neither does the `cargo` compatibility
name.

Trust's Rust and Lean frontends are moving to direct TrustIR lowering. MIR is a
Rust compatibility path, not the architectural proof boundary. Targo owns the
toolchain selection and proof-session transport; compiler flags or ambient
Cargo configuration are not alternative verifier front doors.

The distributed `targo` executable is the Trust-native frontend. A `cargo`
compatibility alias is also shipped for ecosystem tooling, but it deliberately
retains ordinary Cargo behavior and does not silently activate Trust's private
verified-Targo protocol.

For Trust usage and verification workflows, see the repository's
the internal verification-workflow notes. For
the inherited package-manager surface, [The Cargo Book] remains applicable.

**To start developing Cargo itself**, read the [Cargo Contributor Guide].

[The Cargo Book]: https://doc.rust-lang.org/cargo/
[Cargo Contributor Guide]: https://rust-lang.github.io/cargo/contrib/

> Targo carries a large upstream Cargo codebase. The library API remains
> primarily maintained by the Cargo team and is not a stable external API.
> Trust-specific frontend identity, toolchain selection, and verifier transport
> live on top of that compatibility base.


## Compiling from Source

### Requirements

Cargo requires the following tools and packages to build:

* `cargo` and `rustc`
* A C compiler [for your platform](https://github.com/rust-lang/cc-rs#compile-time-requirements)
* `git` (to clone this repository)

**Other requirements:**

The following are optional based on your platform and needs.

* `pkg-config` — This is used to help locate system packages, such as `libssl` headers/libraries. This may not be required in all cases, such as using vendored OpenSSL, or on Windows.
* OpenSSL — Only needed on Unix-like systems and only if the `vendored-openssl` Cargo feature is not used.

  This requires the development headers, which can be obtained from the `libssl-dev` package on Ubuntu or `openssl-devel` with apk or yum or the `openssl` package from Homebrew on macOS.

  If using the `vendored-openssl` Cargo feature, then a static copy of OpenSSL will be built from source instead of using the system OpenSSL.
  This may require additional tools such as `perl` and `make`.

  On macOS, common installation directories from Homebrew, MacPorts, or pkgsrc will be checked. Otherwise it will fall back to `pkg-config`.

  On Windows, the system-provided Schannel will be used instead.

  LibreSSL is also supported.

**Optional system libraries:**

The build will automatically use vendored versions of the following libraries. However, if they are provided by the system and can be found with `pkg-config`, then the system libraries will be used instead:

* [`libcurl`](https://curl.se/libcurl/) — Used for network transfers.
* [`libgit2`](https://libgit2.org/) — Used for fetching git dependencies.
* [`libssh2`](https://www.libssh2.org/) — Used for SSH access to git repositories.
* [`libz`](https://zlib.net/) (AKA zlib) — Used by the above C libraries for data compression. (Rust code uses [`zlib-rs`](https://github.com/trifectatechfoundation/zlib-rs) instead.)

It is recommended to use the vendored versions as they are the versions that are tested to work with Cargo.

### Compiling

Build Targo as part of the Trust checkout so it is paired with the matching
compiler, standard library, verifier supervisor, and Tippy driver:

```
./x build src/tools/targo --set build.submodules=false
```

For a complete user-facing stage2 toolchain, use the repository's normal stage2
build instead of installing this crate independently.

Upstream standalone Cargo development instructions still apply when working on
the inherited compatibility base, but such a build is not a complete Trust
toolchain.

## Adding new subcommands to Cargo

Cargo is designed to be extensible with new subcommands without having to modify
Cargo itself. See [the Wiki page][third-party-subcommands] for more details and
a list of known community-developed subcommands.

[third-party-subcommands]: https://github.com/rust-lang/cargo/wiki/Third-party-cargo-subcommands


## Releases

Cargo compatibility updates in Trust are inherited from upstream Cargo and the
Rust release train. High level upstream release notes are available as part of
[Rust's release notes][rel]. Detailed Cargo release notes are available in the
[changelog].

[rel]: https://github.com/rust-lang/rust/blob/master/RELEASES.md
[changelog]: https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html

## Reporting issues

Found a bug? We'd love to know about it!

Please report all issues on the GitHub [issue tracker][issues].

[issues]: https://github.com/rust-lang/cargo/issues

## Contributing

See the **[Cargo Contributor Guide]** for a complete introduction
to contributing to Cargo.

Code documentation: <https://doc.rust-lang.org/nightly/nightly-rustc/cargo/>

## License

Cargo is primarily distributed under the terms of both the MIT license
and the Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for details.

### Third party software

This product includes software developed by the OpenSSL Project
for use in the OpenSSL Toolkit (https://www.openssl.org/).

In binary form, this product includes software that is licensed under the
terms of the GNU General Public License, version 2, with a linking exception,
which can be obtained from the [upstream repository][1].

See [LICENSE-THIRD-PARTY](LICENSE-THIRD-PARTY) for details.

[1]: https://github.com/libgit2/libgit2
