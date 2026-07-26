# Install Trust

> **Current boundary, 2026-07-20:** Trust has a private seed-first source-build
> path for `aarch64-apple-darwin`. It does not have an authorized public package
> or a demonstrated Linux/Windows install. A produced Stage2 sysroot is usable
> only after current-commit inventory and acceptance gates pass; this document
> does not assert that those gates have passed.

Trust descends from `rust-lang/rust`, but its canonical tool names are
`trustc`, `targo`, `targo-trust`, `trustd`, `trustdoc`, `trustfmt`, `tippy`, and
`trust-analyzer`. Same-sysroot Rust-compatible names are compatibility surface,
not independent Trust evidence.

No workflow is authorized to publish automatically. Local dist and install
rehearsals may prepare and validate artifacts, but changing repository
visibility, uploading artifacts, creating a public release, or updating a
production channel requires explicit owner authorization after the evidence is
reviewed.

## Authoritative references

- [README.md](README.md): product boundary and source-build quick start
- [bootstrap/trust-stage0/README.md](bootstrap/trust-stage0/README.md): exact
  private seed identity, authenticated acquisition, and genesis fallback
- [patches/README.md](patches/README.md): building the external LLVM this
  snapshot links against, and the one patch Trust requires in it
- Internal maintainer documents, named here because they are not part of the
  published snapshot: `install.md` (detailed maintainer/install evidence
  model), `testing-strategy.md` (what each gate proves), and
  `DAILY_DRIVER_LAUNCH.md` (the current simulated HN-comment disposition
  ledger).

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
- **The nine first-party backend repositories** under `first-party/`. They are
  submodules, and not all of them have been published yet. Until they are, a
  `git clone --recurse-submodules` of this snapshot cannot complete, and no
  command that loads either Cargo workspace (`cargo metadata`, `cargo test`,
  `x.py build`) can run from the snapshot alone. This is a publication-ordering
  boundary, not a missing-file bug; the compiler and verification sources
  themselves are all here.

```bash
# with an LLVM built and patched per patches/README.md
python3 scripts/recreate_bootstrap.py \
  --llvm-config /path/to/llvm-project/build/bin/llvm-config --stage 2
```

`--llvm-config` links that LLVM instead of building one in-tree, so `cmake` and
`ninja` are not needed for the Trust build itself. The same setting can be
written by hand into `bootstrap.toml` as `[target.<host-triple>] llvm-config`
with `[llvm] download-ci-llvm = false`.

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
brew install gh cmake ninja python@3.14 rustup libgit2 coreutils

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
also disables verification explicitly for stability; Stage2 self-hosting is not
self-proof.

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

The stock-Rust genesis adapter remains available only as an explicit developer
fallback:

```bash
python3 scripts/recreate_bootstrap.py --genesis --stage 2
```

Anything produced through that fallback must identify genesis lineage and must
not be described as Trust-from-Trust or release evidence.
