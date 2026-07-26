# Trust Stage0 Seed

This directory is the tracked, repo-local bootstrap metadata seed referenced by
`src/stage0`.

It contains the Trust stage0 manifests and checksum pins needed to identify the
default bootstrap payloads. Archive payloads under `bootstrap/trust-stage0/dist/`
are generated local build artifacts and are not tracked in git. `src/stage0`
points directly at this repo-local Trust-owned dist root, so a plain
`./x.py build` does not need a stage0 override environment variable once the
pinned payloads have been materialized locally.

The currently pinned seed is **2026-07-13, `1.99.0-trust`** (compiler commit
`629729f69eefb1cfe6ed766c6c01ee38aa7b0484`), minted from local dist artifacts
with:

```bash
python3 src/tools/trust-stage0-dist/prepare.py \
  --input-dist build/dist \
  --source-channel trust \
  --owned-channel trust \
  --archive-format xz \
  --stage0-seed-only \
  --git-commit-hash 629729f69eefb1cfe6ed766c6c01ee38aa7b0484 \
  --output-root bootstrap/trust-stage0 \
  --stage0-output src/stage0
```

The generated manifest, filenames, version files, installer product names, and
`src/stage0` metadata are all on the owned `trust` channel. (Older seeds were
minted with `--source-channel dev` and rewritten to `trust`; fresh Trust-native
dist output uses `--source-channel trust` as shown.)

This seed emits the canonical `tippy` component and archive directly — the
retired `trust-clippy-preview` input spelling is gone from the pinned payloads.

The seed contains nine checksum-pinned archives for
`aarch64-apple-darwin`: `targo`, `targo-trust`, `tippy`, `trust-analyzer`,
`trust-src`, `trust-std`, `trustc`, `trustc-dev`, and `trustfmt`. The
authoritative admission and acquisition record is `seed-ledger.toml`. It marks
the release `scope = "internal"`, `promotion_decision = "admit-internal"`, and
uses a placeholder non-public signature. It therefore proves neither public
availability nor public signature admission.

No command in this flow uploads, publishes, or downloads from upstream Rust.
The payloads are hosted on the **private** repo (release
`trust-stage0-2026-07-13`); see "Declared payload acquisition" below. Any new
upload or publication requires explicit owner authorization after the producer
and consume gates pass.

## Declared payload acquisition

The canonical seed-first build command is:

```bash
python3 scripts/recreate_bootstrap.py --require-seed --fresh-seed --stage 2
```

`--require-seed` fails instead of silently selecting the stock-Rust genesis
adapter. `--fresh-seed` validates the pinned payloads before quarantining only
an extracted `build/<host>/stage0`, then requires x.py to rehydrate it and the
resulting receipt to pass immutable internal-lineage verification before
registration. A normal retry without the flag honestly remains
`candidate-ready` / `preexisting-unproven`. The flag may reuse Stage1/Stage2
caches; it is not a clean-room build, public-release admission, notarization,
or self-proof. Review the generated Stage2 receipt separately.

If the local `dist/` tree has manifests and checksum pins but is missing the
archive payloads, audit whether the checked-in Trust metadata declares a safe
payload source:

```bash
python3 scripts/fetch_trust_stage0_payloads.py
```

The command writes nothing by default. With `--fetch`, it materializes only
payloads whose `xz_url` is present in the Trust channel manifest and whose
bytes match the SHA-256 pinned in `src/stage0`. It does not invent URLs or fall
back to upstream Rust distribution metadata.

The manifest keeps repo-local `file://` `xz_url`s, so this script's `--fetch` is
the *anonymous-`https`* path a future public bucket will use. **While the repo
is private, the seed is retrieved with authenticated `gh` instead:**

```bash
gh release download trust-stage0-2026-07-13 --repo alabsystems/trust \
  --dir bootstrap/trust-stage0/dist/2026-07-13 --pattern '*.tar.xz' --clobber
python3 scripts/check_seed_freshness.py --require-payloads   # fail-closed digest check
```

## Producer command preflight

Before scheduling a long stage0 producer build, run the CI-safe command
preflight:

```bash
python3 src/tools/trust-stage0-dist/prepare.py \
  --check-producer-command-only
```

This does not run `x.py`, read dist payloads, or write output files. It checks
that bootstrap still declares the global `--dry-run` flag, that the Trust-owned
`x.py dist` producer aliases are registered or path-addressable, that those
steps are described under `Kind::Dist`, and that the config docs/defaults still
cover the required channel, extended-tool, sign-folder, upload-addr, and
compression settings. Its reported dry-run command is the gate to run in a
materialized stage0 environment before the long producer build:

```bash
./x.py dist --dry-run --stage 2 \
  trustc trustc-dev trust-std targo targo-trust trust-docs trustfmt \
  tippy trust-analyzer trust-src trust-llvm-tools
```

## Input preflight contract

Before materializing a fresh seed, run the check-only preflight against the
candidate dist root:

```bash
python3 src/tools/trust-stage0-dist/prepare.py \
  --input-dist build/dist \
  --archive-format xz \
  --stage0-seed-only \
  --check-inputs-only \
  --report-producer-plan
```

For `channel-rust-trust.toml`, this validates that the required Trust packages
are present, referenced archive files exist under `--input-dist`, archive names
are Trust-owned names such as `trustc`, `targo`, and `trustfmt`, manifest hashes
match the local archive bytes, and the compiler/cargo payloads expose the
canonical `trustc`, `trustdoc`, and `targo` entrypoints. It exits before writing
the output root or `src/stage0`. The producer-plan report also prints the
`./x.py dist --dry-run --stage 2 ...` gate, the corresponding producer command,
the `build-manifest` invocation, and the exact stage0 archive filenames the
preflight accepted, including the internal `rustc-dev` support archive needed
by prepared `+trust` toolchains.

The full local producer path is:

```bash
./x.py dist --stage 2 \
  trustc trustc-dev trust-std targo targo-trust trust-docs trustfmt \
  tippy trust-analyzer trust-src trust-llvm-tools

# With [dist].sign-folder pointed at build/dist and [dist].upload-addr pointed
# at the owned local dist URL:
./x.py run src/tools/build-manifest
```

## Local bootstrap when the stage0 payloads are absent (bring-your-own toolchain)

The `dist/` archive payloads are local build artifacts not tracked in git. To
bootstrap Trust-from-Trust on a fresh machine, first fetch the seed from the
private release (`gh release download trust-stage0-2026-07-13 …`, see "Declared
payload acquisition" above). If instead you
only need to build/check locally without the seed (e.g. validate the build-gated
compiler crates like `rustc_mir_transform`), bootstrap from a system toolchain
as below. That path is a developer fallback, not Trust lineage or release
evidence.

Requirements: system `rustc`/`cargo`/`rustfmt`/`rustdoc` at version N-1 of
`src/version` (e.g. 1.98 for a 1.99 source — `download_beta_toolchain` is skipped
when `[build] rustc`/`cargo` are set, and `check_stage0_version` accepts N-1), a
system LLVM satisfying `check_llvm_version` (currently `>= 21`; e.g. homebrew
`llvm@22`), and a C++ compiler (system `clang++`). The fork's
`check_stage0_version` accepts a stock upstream `rustc`/`cargo`/`rustfmt` in place
of the Trust-native `trustc`/`targo`/`trustfmt` (see the `// Trust:` note in
`src/bootstrap/src/core/config/config.rs`).

Create a (gitignored) `bootstrap.toml`:

```toml
[build]
rustc   = "/opt/homebrew/bin/rustc"      # system rustc (N-1)
cargo   = "/opt/homebrew/bin/cargo"
rustfmt = "/opt/homebrew/bin/rustfmt"    # skips the trustfmt stage0 download
rustdoc = "/opt/homebrew/bin/rustdoc"    # optional explicit stock rustdoc selection
docs = false
submodules = false

[llvm]
download-ci-llvm = false                 # can't resolve a commit on rewritten fork history

[target.aarch64-apple-darwin]
llvm-config = "/opt/homebrew/opt/llvm/bin/llvm-config"   # system LLVM >= 21

[rust]
channel = "trust"
deny-warnings = false
```

Then `./x.py check compiler/rustc_mir_transform` (or a full `./x.py build`). The
stage1 `trustc` is still built entirely from Trust's source; the system toolchain
is only the bootstrap stage0. This is the standard rustc "bring-your-own
compiler" path adapted to the Trust fork — it downloads no Trust compiler/std.
