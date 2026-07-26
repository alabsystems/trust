# Targo

Targo is Trust's Cargo-derived package manager and build orchestrator. It
resolves dependencies and drives the selected Trust toolchain as one coherent
unit.

Branded Targo compilation never silently chooses an unverified lane. Use
`targo trust check` (or another authenticated `targo trust ...` workflow) when
verification and proof artifacts are the intended result. Native compatibility
work must be explicit—for example, `targo --unverified build`; that lane prints
an `UNVERIFIED` warning and makes no proof claim. Plain `targo build`, `check`,
`test`, `install`, `package`, and `publish` commands are refused until a lane is
selected. `targo tippy` selects its explicit unverified lint transport itself.

When code run by an explicitly authorized command recursively invokes the
`$CARGO` frontend (for example, a compile-test harness), Targo preserves that
same unverified lane through a live authority broker started only by the exact
explicit CLI lane. Nested Targo does not trust the broker address, an inherited
descriptor, or Cargo configuration: client and server authenticate each
other's kernel PID, opened executable identity, PID lifetime, and ancestry on a
fresh connection. Nested Targo prints its own `UNVERIFIED` warning and keeps
verified invocations fail-closed. Linux uses abstract Unix sockets and pidfds,
so abnormal exit leaves no socket path behind. Other platforms do not propagate
this authority until equivalent handle-bound checks exist. Each client binds an
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
usable procfs/pidfd view; container-boundary mismatches fail closed.

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

## Code Status

[![CI](https://github.com/rust-lang/cargo/actions/workflows/main.yml/badge.svg?branch=auto-cargo)](https://github.com/rust-lang/cargo/actions/workflows/main.yml)

Code documentation: <https://doc.rust-lang.org/nightly/nightly-rustc/cargo/>

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
TRUST_SEED_STAIRCASE=1 ./x build src/tools/targo --set build.submodules=false
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
