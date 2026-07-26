# build-manifest

This tool generates rustup channel manifests from local `x dist` outputs. In
Trust, the supported ownership path is local-first: generate artifacts under
`build/dist`, convert them to a `trust` channel with
`src/tools/trust-stage0-dist/prepare.py`, and rehearse the resulting local
`file://{trust-root}` dist root before changing `src/stage0`.

We auto-generate the host targets (those with full compiler toolchains) and
target targets (a superset of hosts, some of which only support std) through
`build.rs`, which internally uses a stage 1 rustc to produce the target list
and uses the `TargetMetadata` to determine whether host tools are expected and
whether artifacts are expected. This list is not currently verified against the
actually produced artifacts by CI, though that may change in the future.

The inherited upstream release machinery used `promote-release` and a
remote static dist host. That is historical context only for this fork; do not
publish Trust artifacts to remote hosts unless release ownership explicitly
requires it.

## Adding a new component

1. Add a new `Step` to `dist.rs`. This should usually be named after the filename of the uploaded tarball. See https://github.com/rust-lang/rust/pull/101799/files#diff-2c56335faa24486df09ba392d8900c57e2fac4633e1f7038469bcf9ed3feb871 for an example.
    a. If appropriate, call `tarball.is_preview(true)` for the component.
2. Add a new `PkgType` to build-manifest. Fix all the compile errors as appropriate.

## Testing changes locally with rustup

In order to test the changes locally you need to have a valid dist directory
available locally. Build it from this checkout; do not mix in upstream Rust nightly
artifacts for a Trust ownership proof.

Then, you can generate the manifest and add it to `build/dist`:

```sh
cargo +trust run --release -p build-manifest build/dist build/dist 1970-01-01 file://$PWD/build/trust-stage0 nightly
```

After that, generate a SHA256 stamp for the manifest file, and create a symlink to point to the right directory:
```sh
sha256sum build/dist/channel-rust-nightly.toml > build/dist/channel-rust-nightly.toml.sha256
ln -s ${PWD}/build/dist build/1970-01-01
```

For an owned-bootstrap rehearsal, convert the local manifest to `trust` and
validate the candidate stage0 file:
```sh
python3 src/tools/trust-stage0-dist/prepare.py \
  --input-dist build/dist \
  --output-root build/trust-stage0 \
  --stage0-output build/trust-stage0/src-stage0
bash tests/e2e_trust_stage0_lineage.sh --rehearsal build/trust-stage0/src-stage0
```

For the current rustup install rehearsal, use the checked gate. It installs
from the local dist output into a temporary `RUSTUP_HOME`, then links the
resulting sysroot as `trust`:
```
bash tests/e2e_trust_local_rustup_install.sh
```

Do not combine components built locally with inherited upstream Rust CI artifacts for a
Trust ownership proof.
