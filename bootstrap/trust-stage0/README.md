# Trust Stage0 Seed

This directory is the tracked, repo-local bootstrap metadata seed referenced by
`src/stage0`.

It contains the Trust stage0 manifests and checksum pins needed to identify the
default bootstrap payloads. Archive payloads under `bootstrap/trust-stage0/dist/`
are generated local build artifacts and are not tracked in git. `src/stage0`
points directly at this repo-local Trust-owned dist root, so a plain
`./x.py build` does not need a stage0 override environment variable once the
pinned payloads have been materialized locally. A `[build]` stage0 override in
`bootstrap.toml` bypasses this root entirely. `x.py build` accepts one today;
`scripts/check_seed_freshness.py`, run by tidy and a pre-push row, refuses it,
but that is not a build step (see "No bring-your-own-toolchain stage0" below).
The script's last line says which seed is red: "re-seed" only for the committed
pin; "configures its own seed" for this checkout's override, whose fix is to
delete the override line (fetch the payloads first with the ledger's
`authenticated_fetch` when `dist/` is empty) and re-run, never a hook bypass.

The currently pinned seed is **2026-11-07, `0.13.0-trust`** (compiler commit
`82bb867eddb94599f68194f701c766f2b6f5a02f`, release
`trust-stage0-2026-11-07-82bb867ed`). `src/stage0` and `seed-ledger.toml` are
the record; this paragraph only restates them, and `scripts/check_seed_freshness.py`
holds the payloads to `src/stage0`'s pins. The pack-cut record
(`scripts/mint_and_prove_seed.sh`; `seed-ledger.toml` `[release.mint]`) names
the preceding Trust seed `29ebb403de7a102850d6cb10a62d5cc3baf723ed`
and the stock DDC input `fd8e211ae301c84a86d13cf52a6d3ce08c589e2e`.
The historical 2026-07-13 seed was prepared from local dist artifacts with
the call below, which illustrates the manifest-generation shape; it is not
the command for acquiring today's pinned seed:

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
`trust-stage0-2026-11-07-82bb867ed`); see "Declared payload acquisition" below. A new
upload or publication happens only after the producer and consume gates pass,
through the cut and its gates (`docs/CUTTING-A-TOOLCHAIN.md` §3.9): the agent
running the cut performs it on a machine that holds the release
credential, with no person in the loop (the owner, 2026-10-16: "AGENTS DO
PERFORM THEM!"; docs/OWNER_RULINGS.md OW-39).

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

The command writes nothing by default. With `--fetch`, it materializes missing
payloads from a declared channel source or the admitted internal release in
`seed-ledger.toml`. Missing repo-local `file://` payloads use authenticated
`agh`, routed by the declared repository. Each named archive must match its
SHA-256 pin in `src/stage0` before installation; an existing checksum mismatch
refuses rather than being overwritten. It invents neither URLs nor a fallback
to upstream Rust metadata.

For the current private release, use the maintained acquisition command:

```bash
python3 scripts/fetch_trust_stage0_payloads.py --fetch
python3 scripts/check_seed_freshness.py --require-payloads   # fail-closed digest check
```

The release repository/tag and exact archive names come from the checked-in
ledger and `src/stage0`, so this command follows a later seed pin without
copying an old release name or requiring `gh`.

**The historical 2026-10-19 seed's `cargo` loads no Homebrew library**: its source
commit descends from `8336ef81e9`, which vendored libgit2 into targo, and
`otool -L` of its `targo/bin/cargo` names only system libraries (measured
2026-10-24). **The previous 2026-07-13 seed's `cargo`/`targo` load Homebrew's
libgit2** (`/opt/homebrew/opt/libgit2/lib/libgit2.1.9.dylib`; that seed was
minted before `8336ef81e9`), so building from it on a host without that keg
dies at `dyld: Library not loaded` before compiling anything, and on a host
with it that seed's cargo runs a package manager's library. Neither is needed:
`scripts/seed_staircase.py libgit2-compat` builds that one C library from the
`Cargo.lock`-pinned `libgit2-sys` crate with the system C compiler, and the
staircase runner loads it through `DYLD_LIBRARY_PATH`, which dyld searches
before the absolute path. `docs/SEED_STAIRCASE.md`
is the whole seed-only procedure — stage0 admission by content, a scrubbed
environment, the staircase for a tree the seed cannot build in one step, and
sealing with the lineage.

## An upstream port carries its own seed shims

The pinned seed is older than the tree: main ports upstream releases past it
(the 1.101 line since 2026-10-22), and each port can use a language feature or
std API that upstream stabilized after the seed's line. The seed still gates
it, so the port no longer compiles from `src/stage0`. The pre-push hook's
`scoped.compiler-check` (`x.py check --stage 1` with no `[build]` override)
refuses such a port, so the port carries its shims in the same change:
`#![cfg_attr(bootstrap, feature(X))]` in the crate root that uses `X`, or a
`#[cfg(bootstrap)]` twin that does what the non-bootstrap code does, spelled
for the seed's std. Gate on `bootstrap` alone: a version- or probe-keyed cfg
(`version(..)`, a stage0-version env, a std-API probe) is a third state the
tree must keep compiling, and it outlives the seed it served. Use upstream's spelling of the same gate where it has
one (`git log -S` in the tree), give each shim a `// Trust:` line naming the
seed it serves, never change the non-bootstrap side, and keep each twin's
behaviour equal to it: the seed compiles the stage-1 compiler from the
bootstrap side, and stage 1 compiles stage 2 from the other. Measure with `x.py check --stage 1` from a `bootstrap.toml`
written by `scripts/recreate_bootstrap.py --require-seed` (no override);
`fast.seed-freshness` keeps refusing an override, so there is no other green
push. The shims go in the change right after `src/stage0` is re-pinned to a
seed minted from a tree that has them (the re-pin is the mint's own commit, so
it cannot carry the drop), and `min_stage0_rustc_version` rises with them to
the oldest line still measured to compile the tree
(docs/DECISION_QUEUE.md SEED-BRIDGE-1 records each set and its drop).

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

## No bring-your-own-toolchain stage0

Until 2026-09-29 this README documented a "bring-your-own toolchain" bootstrap. It
was a gitignored `bootstrap.toml` whose `[build]` `rustc`/`cargo`/`rustfmt`/
`rustdoc` named a system (stock) Rust. That section is removed. The owner's
words of that date are "NO STOCK RUST IN THE TOOLCHAIN FOR TRUST" (docs/OWNER_RULINGS.md OW-38), and the
path was not the harmless developer fallback it claimed to be. An override of
the same shape, naming the genesis adapter (rustup's stock `stable` behind
Trust-named shell wrappers), seeded the builds and seals of one of the
maintainer's hosts from at least 2026-08-15 until 2026-09-29. The internal
record `reports/2026-09-29-stage0-stock-rust-on-m2.md` (§S2-§S5, §S10) has the
measurement.

Until stage0 admission lands, the build path (`x.py build`) still accepts such
an override (same record, §S7):

- An override outside `build/<host>/stage0` bypasses `src/stage0` entirely.
  `src/bootstrap/bootstrap.py` downloads and hash-checks the pinned payloads
  only for paths under that directory.
- `check_stage0_version` (`src/bootstrap/src/core/config/config.rs`) accepts a
  stage0 that names itself `rustc` or `cargo`. It checks only the version
  window from `min_stage0_rustc_version` (`src/stage0`) to
  `src/rust-compat-version`, and a stock toolchain passes that.

The supported stage0 is the pinned seed described above. Fetch it with `gh`,
then run `check_seed_freshness.py --require-payloads`. Leave `[build]`
`rustc`/`cargo`/`rustdoc`/`rustfmt`/`cargo-clippy` unset, so that `x.py` uses
the pinned seed. `x.py build` does not refuse a stock path there yet, so check
before you build: `python3 scripts/check_seed_freshness.py` fails on any
`[build]` `rustc` or `cargo` (D12 rule (d)). It fails on a stock one (measured
2026-09-30 against rustup's `stable`; same record, §S11). It also fails on a
Trust toolchain other than the pin, such as a sealed toolchain or an atpkg pack
(measured 2026-09-29 against a seal; §S10). The push row `fast.seed-freshness`
and tidy run that script; neither is a build step.

To tell a stock stage0 from a Trust one: a Trust `trustc` is a native
executable (Mach-O, ELF or PE), not a shell script. In a development clone, its
`-vV` `commit-hash` is a commit of this repository (`git cat-file -e <hash>`);
the public snapshot's history is rewritten, so the check does not work there.
The pinned seed's hash is `compiler_git_commit_hash` in `src/stage0`. The stock
compilers seen so far report hashes this repository does not contain (measured
2026-09-29: stable 1.98.0's `88d9e12ae` and the genesis nightly's `14cae6813`
are both absent; same record, §S6). The banner is self-reported, so this is a
first check, not an admission. Do not look for a `trust:` line: the pinned seed
predates it (the line was added on 2026-07-24).
