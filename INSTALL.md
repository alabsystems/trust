# Install Trust

Trust has public, ledger-attested source releases (signed
`SHA256SUMS`/`SHA256SUMS.sig`) with an anonymous public build lane
(`scripts/fetch-first-party.sh`), a private seed-first source-build path for
`aarch64-apple-darwin`, and one packaged binary install: on Apple-silicon macOS,
install [aterm](https://github.com/alabsystems/aterm#install) and its package
manager, atpkg, installs Trust from this repository's signed
`atpkg-trust-<build>` releases and links rustup's `trust` toolchain to it
(`aterm pkg install trust` does it by hand). There is no Linux or Windows
install. A Stage 2 sysroot you build is usable only after the current commit's
inventory and acceptance gates pass; this page does not claim they have.

Trust descends from `rust-lang/rust`, but its canonical tool names are
`trustc`, `targo`, `targo-trust`, `trustd`, `trustdoc`, `trustfmt`, `tippy`, and
`trust-analyzer`. Same-sysroot Rust-compatible names are compatibility surface,
not independent Trust evidence.

Publishing a toolchain needs the release credential and runs only after the cut's gates pass.

## Authoritative references

- [README.md](README.md): product boundary and source-build quick start
- [bootstrap/trust-stage0/README.md](bootstrap/trust-stage0/README.md): exact
  private seed identity, authenticated acquisition, and why a stock stage0 is
  not supported (it used to document a genesis fallback)
- [patches/README.md](patches/README.md): building the external LLVM this
  snapshot links against, and the one patch Trust requires in it
- Internal maintainer documents, named here because they are not part of the
  published snapshot: `install.md` (detailed maintainer/install evidence
  model) and `testing-strategy.md` (what each gate proves).

## What this snapshot does and does not carry

Two things a source build needs are deliberately **not** in the published tree,
and both have a documented substitute:

- **LLVM.** Trust's development tree vendors `src/llvm-project` and builds it
  in-tree; the snapshot does not republish ~1.9 GB of upstream LLVM. Build (or
  install) an LLVM 21+ yourself, apply
  `patches/0001-llvm-scalarevolution-guard-cross-phi-addrec-recursion.patch`,
  and point Trust at it with `--llvm-config`. That patch is required for a
  self-hosting build: without it the compiler can die with SIGBUS inside LLVM's
  ScalarEvolution while compiling itself. Full instructions:
  [patches/README.md](patches/README.md).
- **The nine first-party backend repositories** under `first-party/`. All nine
  are published. The public snapshot cannot carry submodule gitlinks, so it
  ships `first-party/PINS.txt` — each sibling pinned at a ledger-attested
  public release — and a materializer:

  ```bash
  scripts/fetch-first-party.sh   # clones the nine siblings at their pinned revisions
  ```

  Run it once after cloning; afterwards both Cargo workspaces resolve
  (`targo metadata`; a `--locked` re-lock). The 50 upstream-Rust crates of the
  release gate's scoped `-p` list (recorded in the internal
  `publish/config.sh`) are meant to check with the Trust toolchain (the aterm
  install above): the release gate runs `targo trust check --allow-l0-gaps
  --manifest-path crates/Cargo.toml --locked -p …`, and `targo --unverified
  check …` is the compile-only pass. Neither has been run on the
  published pack yet. Two crate
  families build only through the self-hosted lane below: `trust-hex`,
  `trust-ratio`, and `trust-utf` are Trust-language source (grammar `ensures`
  clauses stock rustc cannot parse), and
  `trust-mir-extract`/`trust-thir-lower`/`trust-witness` plus their 11
  dependents link the fork's own compiler internals. `x.py build`
  additionally needs the external patched LLVM above. In a development
  checkout (real submodules), use `git submodule update --init` instead.

```bash
# with an LLVM built and patched per patches/README.md
python3 scripts/recreate_bootstrap.py --require-seed --fresh-seed \
  --llvm-config /path/to/llvm-project/build/bin/llvm-config --stage 2
```

`--llvm-config` links that LLVM instead of building one in-tree, so `cmake` and
`ninja` are not needed for the Trust build itself. The same setting can be
written by hand into `bootstrap.toml` as `[target.<host-triple>] llvm-config`
with `[llvm] download-ci-llvm = false`.

The two seed flags matter here. The seed release is private, so on a public
clone the seed fetch fails. Without the flags, the recreator then uses an installed atpkg `trust`
pack if there is one, which is not the pinned seed. Otherwise it falls back to
its stock-Rust genesis mode, which wraps the `rustc`/`cargo` already installed.
Neither is the supported stage0, the pinned seed described next. With both
flags, a clone that cannot fetch the seed stops with an error, so a public
clone cannot build the compiler from source yet.

## Supported private source-build path

The authoritative seed is the private/internal
`trust-stage0-2026-07-13` release: `1.99.0-trust`, compiler commit
`629729f69eefb1cfe6ed766c6c01ee38aa7b0484`, nine checksum-pinned
archives for `aarch64-apple-darwin`. The authoritative admission record is
`bootstrap/trust-stage0/seed-ledger.toml`; its placeholder signature and
`admit-internal` decision deliberately do not qualify as public-release
evidence.

On an Apple Silicon macOS host with authenticated access to this private
repository and all nine HTTPS first-party submodules:

```bash
# one-time host setup; Python 3.11+ is mandatory
brew install gh cmake ninja python@3.14 rustup coreutils
# a Stage 2 build also binds the Xcode Command Line Tools and a `pkg-config`,
# which neither macOS nor the line above provides: see "Native tools of the
# Stage 2 build" below

# authenticate before the private clone, submodules, and seed-release fetch
gh auth login
# clone only the superproject; the recreator initializes pinned submodules
# through its bounded, credential-scoped acquisition path
gh repo clone https://github.com/alabsystems/trust trust -- --no-recurse-submodules
cd trust
python3 scripts/recreate_bootstrap.py --require-seed --fresh-seed --stage 2
```

`--require-seed` refuses to fall back to the stock-Rust genesis adapter. The
recreator authenticates the private release, verifies the seed payloads, and
drives Stage2. `--fresh-seed` safely quarantines only the previously extracted
`build/<host>/stage0`, if present, and requires x.py to hydrate it from those
validated archives during the recorded build. The quarantine is removed only
after the immutable provenance gate passes. This may reuse Stage1/Stage2 build
caches; it is not a clean-room rebuild or self-proof. The command directly
audits its Stage2 tool set, but a claim still needs the retained and reviewed
identity, doctor, provenance, and acceptance outputs below:

```bash
python3 scripts/recreate_bootstrap.py \
  --verify-stage-provenance --stage 2 --host aarch64-apple-darwin \
  --require-immutable-lineage
build/aarch64-apple-darwin/stage2/bin/trustc -Vv
build/aarch64-apple-darwin/stage2/bin/targo trust doctor --format json
bash tests/e2e_trust_toolchain.sh
```

These commands are the evidence bar, not a statement that the current checkout
has already passed it. The source-build registration points rustup at a mutable
build tree and is not immutable installed-toolchain or dist evidence.

### Native tools of the Stage 2 build

A Stage 2 build binds its native build tools into its provenance receipt and
refuses to start unless each one resolves: `cc`, `c++`, `ar`, `ld`, `nm`,
`ranlib`, `strip`, `make` and `git` (Xcode Command Line Tools:
`xcode-select --install`), `perl` and `sh` (ship with macOS), `cmake`, `ninja`,
`python` (the interpreter running the recreator), and a `pkg-config`. On macOS
the same capture also resolves `xcrun` and `xcode-select` and binds what they
select inside the active developer directory (`clang`, `clang++`, `otool`,
`python3`, and that directory's own `ar`, `ld`, `nm`, `ranlib`, `strip`, `git`,
`make`) together with the SDK; the Command Line Tools provide all of those. It
refuses ambient build overrides as well (`CC`, `RUSTFLAGS`, every
`PKG_CONFIG_*`, `HOST_PKG_CONFIG*` and `TARGET_PKG_CONFIG*` variable, and the
rest of its list) and Cargo configuration in a directory above the checkout.

`--check` with the build's flags runs that capture read-only and prints its
answer first, before it looks for a stage0: whenever the build would be
refused there it exits 1 with the capture's own reasons, and the build itself
is refused at the same point, before it fetches anything.
`--check --require-seed --fresh-seed --stage 2`, the build command above with
`--check`, is its report: it selects the stage0 as that build does, from the
pinned archives and never from an installed atpkg pack, and sets nothing aside.
`--check` never fetches, so on a
new clone it goes on to report the pinned seed unavailable; the table above that
line is the answer. With the archives on disk a failing report ends with the
stage0 it would use: `--check: prerequisites NOT met (stage0 mode: seed).`

macOS ships no `pkg-config`, and neither do the Command Line Tools or the
`brew install` line of the host setup. `brew install pkgconf` supplies one
that searches Homebrew's .pc files, so a build script that probes can resolve,
and link, a Homebrew library. To satisfy the binding without them, build
pkgconf with a private prefix and link it yourself, because its install
creates `bin/pkgconf` and no file named `pkg-config`:

```bash
./configure --prefix="$P" --disable-shared && make && make install
mkdir "$P/pathbin" && ln -s ../bin/pkgconf "$P/pathbin/pkg-config"
PATH="$PATH:$P/pathbin" python3 scripts/recreate_bootstrap.py --check --require-seed --no-atpkg
```

Keep `$P/pathbin` LAST on PATH, for the recreator only, and in place for
`--verify-stage-provenance`, which binds the same file at the same path again.

### Register the toolchain: link rustup at a SEALED artifact (default)

A stage2 under `build/` is a LIVE build directory: every `x.py` run empties
`bin/` and the stdlib for its duration, so a rustup link pointed there makes
every repo pinning `channel = "trust"` fail intermittently with
`error[E0463]` / `'rustc' is not installed` whenever a rebuild is in flight.
A plain link also loses the `rustc-private-sysroots` pairing that out-of-tree
`rustc_private` driver tools (trust-wp) resolve beside the compiler's sysroot.
Seal first, then link. The seal's gates start the compiler and every shipped tool
through one small program, `trust-serial-command`, and that program starts nothing
for a caller that holds no build slot. Build it with the stage2 you are sealing,
then seal inside a slot:

```bash
# after the stage2 build above
STAGE2="$PWD/build/host/stage2"
HELPER="$HOME/.cache/trust-serial-command"      # any directory outside the checkout
(cd crates/trust-resource-controller && PATH="$STAGE2/bin:$PATH" CARGO_TARGET_DIR="$HELPER" \
    targo --unverified build --locked --release --features serial-command --bin trust-serial-command)
TRUST_TOOLCHAIN_SERIAL_COMMAND="$HELPER/release/trust-serial-command" \
    python3 scripts/build-slot --cpus 1 -- bash scripts/promote-toolchain.sh
```

`TRUST_TOOLCHAIN_SERIAL_COMMAND` is the absolute path of a regular executable, not
a symlink. Every form that runs a gate needs it and the slot: a seal, `--no-flip`
and `--gate-only`. `--provenance` and `--help` need neither. A slot is held by
running under `scripts/build-slot`; never set `BUILD_SLOT_HELD` by hand. Without
either, the script refuses before any gate runs, says which is missing and prints
these commands. On a Linux host, `scripts/linux_refresh_toolchain.py --seal` does
both itself.

`promote-toolchain.sh` copies the finished stage2 into an immutable artifact
under `$TRUST_TOOLCHAIN_HOME` (default `~/toolchains`), seals the byte-matched
rustc-private sysroot beside it — fail-closed, using the private wrapper's own
selection rule (commit-hash equality plus a byte-identical `librustc_driver`) —
verifies the pair including a replay of that resolution against the sealed
root, and atomically flips `${RUSTUP_HOME:-~/.rustup}/toolchains/trust` onto
the artifact. Rebuilds then never tear the channel down, and promoting the
next build is one command and one atomic symlink flip.

The direct registration (`scripts/rustup-link-trust.sh`, which links rustup at
the mutable build tree) remains available for throwaway iteration on a machine
where nothing pins the channel, but the sealed lane above supersedes it as the
default. Either way the result is local convenience state, not immutable
installed-toolchain or dist evidence.

## Optional macOS coordinator companion

After installing Trust, the repository can locally build and atomically publish
its universal read-only `trustd` monitor:

```bash
tools/trustd-menubar/install.sh --open
```

This places `TrustdMenubar.app` in `~/Applications` and requests a fresh launch. Its
Guided Tour appears for a new onboarding revision and remains available from
the menu. It does not install or configure Trust, start or recover `trustd`, or
display proof results. The ad-hoc signature and two-architecture CDHash checks
test bundle coherence, not publisher identity; no Developer ID, notarization,
or public distribution claim is made.

## Verification and native compatibility

Use the authenticated Trust workflow for verification:

```bash
build/aarch64-apple-darwin/stage2/bin/targo trust check
build/aarch64-apple-darwin/stage2/bin/targo trust check --format json
```

Branded native Targo compile commands refuse implicit unverified work. When the
goal is Cargo-compatible native behavior rather than proof evidence, authorize
that boundary explicitly:

```bash
build/aarch64-apple-darwin/stage2/bin/targo --unverified check
build/aarch64-apple-darwin/stage2/bin/targo --unverified build
build/aarch64-apple-darwin/stage2/bin/targo --unverified test
```

Those commands emit an `UNVERIFIED` warning and make no proof claim. Bootstrap
builds the compiler with verification off (`-Ztrust-verify=off`). That is not
on yet: a defect, not policy. The owner, 2026-11-09: "what check-waiving? that
sounds wrong. we want verification on and for it to work." Stage2
self-hosting is not self-proof.

## Packaging status

The repository contains local immutable-prefix and dist-artifact gates. Their
existence is not a pass. Before any packaged-install claim, run them against
fresh artifacts from the reviewed commit and retain their receipts. Before any
native Cargo ecosystem-compatibility claim, also retain the locked serde/derive
result and the complete 123-crate native-compatibility diagnostic. The
shell/Python diagnostic is explicitly unauthenticated and release-inadmissible;
a release claim also needs an independent native authenticated replay over the
same bound inputs and results. Neither compatibility lane is verifier-coverage
evidence. Verified third-party proc macros,
Linux/Windows seeds, public distribution, and strict-superiority evidence remain
open boundaries.

The recreator still has a stock-Rust genesis mode (`--genesis`). Without
`--require-seed`, with no seed-mode `bootstrap.toml` already present and no
usable atpkg pack, it falls back to that mode on its own when the seed cannot
be materialized, printing one line. It is not a supported lane: no stock Rust
is in the Trust toolchain. Pass `--require-seed --fresh-seed`. `x.py build`
does not refuse a genesis or other stock stage0 yet.
`scripts/check_seed_freshness.py` refuses it in tidy and in the fast profile;
the push profile does not run it yet, and it stops no build. The seals built
through one on a maintainer host record no stage0 in their `PROVENANCE`.
