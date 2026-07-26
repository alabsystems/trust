# targo-trust

**Author:** Andrew Yates <andrewyates.name@gmail.com>
**Version:** 0.1.0
**License:** MIT OR Apache-2.0

<!--
cite:
- Cargo.toml
- Cargo.lock
- ../Cargo.toml
-->

`targo trust` is the canonical verifier interface for Trust. It is normally run
from the standalone stage2 Trust sysroot. If `targo` is not on `PATH`, use the
explicit form `build/<host>/stage2/bin/targo trust ...`.

`targo trust` verifies through Trust-owned binaries inside that sysroot,
including Trust-preferred `targo`, `targo-trust`, `trustc`, `trustd`, `trustdoc`,
`trustfmt`, `targo-fmt`, `tippy`, `targo-tippy`, `tippy-driver`,
`trust-analyzer`, and optional `trust-miri`/`targo-miri` when Miri ships. A
complete Trust sysroot retains only the `cargo` and `rustc` compatibility
entrypoints. Ambient external Rust-named binaries are not Trust evidence.

The public verifier commands to optimize around today are:

- `targo trust check`
- `targo trust check --format json`
- `targo trust report`
- `targo trust report-query`
- `targo trust hardened-lab`

The public maintainer entry points for release full-verify evidence are:

- `targo trust verify cargo-cache` for isolated seed-cache materialization
- `targo trust verify repo-gate` for the Rust-owned repository sanity gate
- `targo trust verify self --full-verifier` for native compiler
  self-verification evidence
- `targo trust release check` for release metadata, publication, and
  product-proof gates

The product-proof solver lanes currently validate checklist structure only and
then fail closed with `product-proof-solver-evidence-unverified`. Self-declared
runner metadata, proof counts, and transcript hashes are not release proof; a
kind-specific candidate-bound Rust collector and strict obligation replayer are
still required. The trustd protocol smoke collector is operational evidence,
not a generic solver-proof escape hatch. That live smoke is the trustd
component's single required artifact because it already binds and rechecks the
canonical daemon's path, digest, version, commit, identity response, and
protocol transition; a second self-declared binary-identity JSON would add no
independent authority. On macOS the collector also requires a canonical,
symlink-free candidate path whose leaf and ancestors are not group/world
writable and whose ownership is an immutable root prefix followed by an
effective-user-owned tree. Path-based `exec` still has a same-UID
replace-and-restore race that pre/post hashing cannot atomically eliminate, so
admissible collection requires an exclusive release account with no concurrent
same-UID writer for the complete collection and validation interval. Root
and host ACL policy remain part of the release-host TCB; the release account
must not grant another writer outside ordinary mode bits.

The old `targo trust verify full`, `preflight`, and `full-preflight` aliases
are removed Python/shell-era release adapters. If `./scripts/build.sh
full-verify` is used as an outer collector, cite the Rust-owned gate artifacts
it retains rather than the shell wrapper itself.

`targo trust verify examples`, `targo trust gate check-all`, `targo trust
repo check`, and `targo trust bootstrap recreate` are
source/example/regression/bootstrap helpers. They do not replace release
full-verify evidence.

The public release and launch gates built on top of that verifier/evidence surface are:

- `targo trust domination`
- `targo trust domination upstream-tests`
- `targo trust proof-concurrency-producer`
- `targo trust gate check-all`
- `targo trust gate verify-examples`

Everything else in this package is secondary to that front door.

Current-checkout rule: never infer stage2 readiness from an existing build
directory. Inventory, sibling-tool identity, and provenance must all bind the
selected toolchain to the exact clean commit. `targo-trust trust domination
--json` is the authority for the live verdict and dimension counts; required
unknown or blocked dimensions mean `not_superior`, and feature-surface passes
are not proof/performance superiority evidence. `targo trust verify examples
--metadata-only` validates headers only. Treat stage1 passes as developer
diagnostics. Every `targo trust verify examples` mode, including a fresh stage2
run, is regression-diagnostic-only: its v2 report does not authenticate source
and tool provenance and explicitly sets `proof_evidence=false` and
`release_evidence=false`.

## Install From This Checkout

Use the root README quick start for the full build flow. The short version is
below. The `compiler/rustc` build target is the upstream-named compiler crate
inside this Trust checkout, not a user-facing `rustc` command.

```bash
./x.py build --stage 2
build/host/stage2/bin/targo trust --help
```

The default Trust build profile is expected to install `targo`,
`targo-trust`, `trustc`, and the extended Trust tools into the standalone
stage2 sysroot, plus the `cargo`/`rustc` compatibility entrypoints. That
sysroot is the normal compiler-discovery path. `targo` itself resolves
Trust-preferred `trustc`/`trustdoc`; the same-sysroot `rustc` alias is
compatibility surface, while ambient external Rust tools are not release
evidence.

## Canonical Usage

These examples assume `targo` from the standalone Trust sysroot is on `PATH`.
Use `build/<host>/stage2/bin/targo trust ...` when it is not.

Current crate:

```bash
targo trust check
targo trust check --format json
targo trust report --format json
targo trust check --no-hardened
targo trust check --trust-profile coreutils_hardened
targo trust check --standalone --format json
targo trust check --standalone --no-hardened --format json
targo trust report-query --report target/trust/report.json --function divide_safe
targo trust hardened-lab
targo trust hardened-lab --manifest-path examples/hardened/Cargo.toml --format json
targo trust hardened-lab --json --show-vcs
targo trust verify cargo-cache --repo-root "$PWD" --cargo-home "$PWD/build/full-verify/cargo-seed-home" --json-output "$PWD/build/full-verify/cargo-cache-materialization.json"
targo trust verify examples --metadata-only
targo trust gate check-all
targo trust repo dev-test trust-vcgen
targo trust bootstrap recreate --check
targo trust domination
targo trust domination upstream-tests
```

Single file:

```bash
targo trust check path/to/file.rs
targo trust check --format json path/to/file.rs
```

From the Trust repo root, the intended checked example path is:

```bash
targo trust check examples/midpoint.rs
targo trust check --format json examples/midpoint.rs
```

Single Clean/Lean file:

```bash
targo trust check proofs/trust-soundness/discharge_soundness.lean
targo trust check --json proofs/codegen-equivalence/*.lean
```

Trust accepts two authoritative languages, so `check` dispatches on the
operand's language before it dispatches on cargo semantics: a `.lean` operand
is parsed, elaborated, and kernel-checked by the Clean CIC kernel that is
LINKED INTO this binary, not by a `clean` executable found on `PATH`. There is
therefore no state in which a missing or mismatched subprocess turns an
unchecked file into a pass, and the verdict does not move when the machine's
installed toolchain does.

What that lane accepts is narrower than `clean check`, in two directions that
both fail closed:

- External `.olean` import search is disabled. Only Clean's built-in preludes
  resolve, so a file that depends on an outside library is rejected, never
  silently checked against a smaller environment.
- The strict island policy applies: an `axiom`, a `sorry`, a valueless
  `opaque`, a `partial`/`unsafe` marker, or any trust debt in a theorem's
  reachable closure is a rejection even where the kernel alone would accept it.

`targo trust build` has no Lean lane. Compiling Clean to an artifact judges
nothing, and a successful compile must not be readable as a discharged proof.

A nonzero expected-obligation count is necessary but not sufficient for those
single-file Rust commands to contribute proof evidence. The report must also contain
accepted structured native proof results, no unresolved/advisory result, and
source/tool authority authenticated by the applicable release gate. The live
corpus command, `targo trust verify examples --trustc <stage2 trustc>`, is only
a regression diagnostic; if it fails, cite the failure, and if it passes, do
not promote that result to proof or release evidence.

## Current Contract

- `targo trust check` is the canonical human-readable report surface.
- `targo trust check --format json` is the canonical machine-readable report surface.
- `targo trust check` uses the integrated fail-closed verifier by default and
  keeps native trust-mc/trust-wp/trust-vc diagnostics visible in the report.
  `--allow-l0-gaps` is the explicit advisory development loosener.
- Native `targo trust check`, `targo trust build`, and `targo trust report`
  are hardened by default. The default profile label is `unix_hardened`; native
  mode passes tracked hardened/profile compiler options so `trustc` emits
  hardened obligations from MIR.
- `--trust-profile <name>` selects the hardened profile label for the run and
  keeps hardened mode enabled. `--hardened` is accepted as an explicit spelling
  of the default hardened behavior. `--no-hardened` is the explicit opt-out for
  legacy/non-hardened comparison evidence and should not be used for hardened
  proof claims.
- In `--standalone` mode, hardened source inventory is also the default unless
  `--no-hardened` is present. The standalone analyzer reports raw path APIs,
  path identity, permission create/change/window hazards, lossy/strict UTF-8
  boundaries, discarded errors, panic boundaries, trust-domain calls/order,
  Unicode-only CLI argument boundaries, process/SIGPIPE semantics,
  unsafe-operation inventory, and FFI-boundary inventory.
- Native hardened report JSON includes `hardened.profile.name`,
  `hardened.profile.enabled_categories`, `hardened.assurance`,
  `hardened.summary`, and `hardened.boundary_inventory`. The built-in category
  set is `raw_path_api`, `path_identity`, `permission_change`,
  `permission_create`, `permission_window`, `utf8_reject`, `byte_loss`,
  `error_discard`, `panic_boundary`, `compat_observable`,
  `process_semantics`, `trust_domain`, `trust_domain_order`,
  `unsafe_operation`, and `ffi_boundary`.
  Minimal shape:

  ```json
  {
    "hardened": {
      "profile": {
        "name": "coreutils_hardened",
        "enabled_categories": ["raw_path_api", "unsafe_operation", "ffi_boundary"]
      },
      "assurance": {
        "level": "inventory_only",
        "proof_evidence_required": true
      },
      "summary": {
        "hardened_obligations": 1,
        "inventory_entries": 1
      },
      "boundary_inventory": []
    }
  }
  ```
- Native unsafe and FFI obligations now round-trip as hardened categories:
  `hardened_unsafe_operation` and `hardened_ffi_boundary`.
- Under the default strict route (`targo trust check`), custom API obligations
  in namespace `trust.vc.hardened`
  are reconstructed as typed `hardened_<category>` rows and routed to trust-mc
  as native TRUST_IR translation-validation work. This does not make
  `--solver trust-mc` a direct CLI routing selector.
- Native `check`/`report` keep the normal JSON, report-directory, and
  exit-code behavior. `--format json` is the compiler-backed proof report when
  a native compiler is used, and `--report-dir` writes `report.json`,
  `report.html`, and `report.ndjson` fail-closed. Compiler-backed verifier
  entrypoints always collect fresh structured evidence. Because hardened mode
  is default, native
  exit code `0` also requires every emitted hardened obligation to have
  publishable structured native proof evidence; `inventory_only` or
  `partial_proof_evidence` hardened summaries are not publishable hardened
  success.
- `targo trust report-query` is a read-only inspection command for saved proof
  reports. `--require proved` exits `0` only when the selector matches at least
  one obligation and every selected obligation is proved; a matched function
  with zero obligations exits non-zero. It does not rerun verification or
  upgrade standalone/lab inventory into proof evidence.
- Explicit `--standalone` is source inventory. With default hardened standalone
  inventory enabled,
  `--format json` emits a standalone payload with `mode: "standalone"`;
  `--report-dir` does not write report files, and the output is not native proof
  evidence.
- `targo trust hardened-lab` validates the hardened example corpus and exits
  `0` only when every advertised hardened claim has a matching standalone
  analyzer finding and matching per-claim rootless walkthrough transcript
  evidence.
  Use `--manifest-path <Cargo.toml>` to select the corpus manifest,
  `--format terminal|json` or `--json` to choose output, and `--show-vcs` to
  include the underlying standalone VC/finding rows.
- `targo trust check --standalone --format json` is the raw analyzer
  surface behind `hardened-lab`; the lab command adds corpus source-inventory
  finding coverage, per-claim rootless walkthrough transcript checks, and the
  dedicated coverage exit-code contract.
- `targo trust verify cargo-cache` is the unified full-verification cache
  materialization entry point. It should be run with a dedicated seed cache
  such as `build/full-verify/cargo-seed-home`, not `$HOME/.cargo`, so retained
  JSON evidence describes the release cache closure instead of ambient user
  state.
- Loose repository scripts are compatibility implementation details, not the
  public command surface. Use `targo trust verify ...` for verifier helpers,
  `targo trust gate ...` for repo gates, `targo trust repo ...` for build and
  maintenance helpers, and `targo trust bootstrap ...` for stage0/bootstrap
  lifecycle helpers.
- `targo trust domination` is the launch-facing Rust-vs-Trust scorecard. It is
  fail-closed: it exits `0` only when required compatibility, compile-time,
  runtime, binary-efficiency, architecture, and proof-capability lanes prove
  Trust is Rust-compatible, strictly faster on required performance lanes, and
  has evidence-backed proof advantages. Its
  `--json` mode is the AI work queue for closing the remaining blockers.
  The scorecard evaluates declared suite/summary data and evidence strings; it
  does not itself rerun or authenticate arbitrary referenced benchmark/proof
  artifacts. Program-index rows used for runtime, binary-size, and compile lanes
  must carry matching `source_sha256` source identity. Compatibility summaries
  must carry proof-grade provenance (`generated_on`, `run_id`, full `repo_head`,
  `repo_dirty = false`, `upstream_revision`, and a Rust-owned
  `trust-upstream-compat` runner with `python_used = false`).
- `targo trust domination upstream-tests` is the canonical upstream Rust test
  porting entry point; it dispatches the Rust porting engine and does not use
  Python.
- `targo trust proof-concurrency-producer` is the Rust-owned entry point for
  auditing the missing release concurrency producer/validator. It currently
  fails closed with a structured `missing_trust_concurrency_release_producer`
  report. `targo trust proof-concurrency` can only emit non-proof artifact or
  demo audits with authority `none`; presence and hash bindings are never
  promoted to a proof claim.
- Crate-mode `check`/`report` use Trust-owned `targo` build-mode orchestration
  through the discovered Trust toolchain. Rust + Lean are transitioning to
  direct typed TrustIr production; until that lane reaches proof-capability
  parity, Targo retains the authenticated optimized-MIR compatibility proof
  path and never promotes direct structural output to proof authority.
- Default configuration is `L1`, but obligation generation still depends on
  crate policy, MIR supportability, and skips. An empty report is not proof.
- Exit code `0` on native `check`/`report` means the compiler succeeded and the
  emitted obligations satisfied the CLI gate; it does not prove code for which
  no obligations were generated.
  On the default hardened native path, every emitted hardened obligation must
  also have publishable structured native proof evidence in the report.
  For `hardened-lab`, it means all advertised hardened claims have matching
  standalone analyzer findings and matching per-claim rootless walkthrough
  transcript evidence.
- Exit code `1` means at least one native obligation failed, was
  runtime-checked, was inconclusive, or the compiler itself failed. In explicit
  standalone mode it means at least one source-inventory finding is failed;
  standalone `UNKNOWN` inventory remains visible but does not fail the process.
  Hardened source findings are fail-closed `FAILED` rows, so default
  standalone hardened inventory exits non-zero when any hardened hazard is
  present. Use `--standalone --no-hardened` only for contract-only source
  inventory.
- For `hardened-lab`, exit code `1` means standalone analyzer finding coverage
  or per-claim walkthrough transcript evidence is missing for at least one
  advertised hardened claim, no walkthrough binary was discovered, or a
  walkthrough binary failed.
- Exit code `2` means `targo-trust` hit an internal setup or argument error,
  including invalid `hardened-lab` usage or unreadable corpus setup.
- `targo trust check` and `targo trust report` require native verification through Trust-preferred `trustc` driven with Trust-owned verifier flags. Rust-compatible aliases inside the same Trust sysroot are compatibility surface; ambient external Rust tools are not Trust evidence.
- `--standalone` is an explicit source-inventory mode for `check` and `report`; it is never selected silently.
- Hardened mode is the default for native `check`/`build`/`report` and explicit
  standalone source inventory. `--trust-profile <name>` selects the profile
  label exposed to compiler and source checks; `--no-hardened` disables
  hardened obligations/findings for that invocation.
- Raw `trustc` verifies its local crate in the default `unscoped` role and is
  fail-closed by default; `-Z trust-verify=off` is the sole verification
  opt-out. Cargo-mode `targo trust check` additionally authenticates each
  compilation unit with a primary/dependency/build-script role, package name,
  and per-run session nonce.
- Native evidence-grade checks require structured `TRUST_JSON` transport;
  human-readable diagnostics alone are never accepted as proof evidence.
- `build` and rewrite-loop flows require a discoverable native Trust compiler.
- LLVM remains the default backend; trust-cg is experimental and opt-in.

## trust-cg

trust-cg is not the normal path. It is an experimental alternate backend tracked under `#829`.

- default: LLVM
- opt-in CLI: `targo trust check --backend trust-cg`
- opt-in config: `codegen_backend = "trust-cg"` in the `[trust]` table

## `[trust]`

Trust policy lives in the `[trust]` table of the project manifest —
`Targo.toml`, or `Cargo.toml` for a project that still ships the compatibility
manifest:

```toml
[package]
name = "demo"
version = "0.1.0"

[trust]
level = "L1"
function_budget_ms = 45000
```

`targo-trust` accepts `enabled`, `level`, `timeout_ms`, `function_budget_ms`,
`skip_functions`, `codegen_backend`, `hardened`, `trust_profile`, and `intent`.
The former `verify_functions` placeholder was never wired into verification and
is rejected as an unknown key. Use `targo trust check --function <selector>`
when you need focused report and exit semantics; the compiler still verifies the
complete selected target.

`timeout_ms` is required to be positive and is enforced through the compiler's
tracked per-obligation timeout option; it is not an advisory/report-only field.

In a workspace, a `[trust]` table in the root manifest fills only the keys a
member left unwritten. A member's own declaration always wins, so a permissive
workspace root cannot lower the level a member crate asked to be proved at.

For verifier entrypoints (`check`, `build`, and `report`), a present policy must
be readable and valid; invalid TOML, unknown keys, invalid levels, or invalid
`codegen_backend` values fail closed before invoking the compiler. A project that
declares nothing uses defaults.

The stand-alone `trust.toml` is the retired spelling of the same keys. It is
still read for one release and warns, naming the table to move it to. Declaring
policy in both places is an error rather than a silent choice between them.
`intent` likewise replaces `[package.metadata.trust] intent`, which is read for
one more release with a warning.
`hardened = true` enables hardened mode from config. `trust_profile =
"coreutils_hardened"` selects the hardened profile label from config and is
exposed to the compiler through a tracked option; CLI `--hardened` and
`--trust-profile` enable or relabel config hardening, and `--no-hardened`
disables hardened mode for that invocation. Native JSON records the selected
label under
`hardened.profile.name` and the active category list under
`hardened.profile.enabled_categories`. `--backend` overrides
`codegen_backend`.

## Maintainer/Debug Transport

Use `targo trust gate` for repository maintenance gates that used to be run as
loose scripts:

```bash
targo trust gate check-all --repo-root .
targo trust gate scripts --repo-root .
targo trust gate verify-examples --metadata-only
```

`gate check-all` is Rust-owned orchestration for script syntax,
verify-example metadata, `crates/` checks, integration-test checks, and
`targo-trust` all-target checks. `gate scripts` runs only the syntax and
metadata portion for fast iteration. `gate verify-examples` is an alias for the
Rust-owned verifier-example command.

These are useful while working on the repo, but they are not the public front door:

- `build/<host>/stage2/bin/targo --unverified run --manifest-path targo-trust/Cargo.toml -- trust ...`
- raw fail-closed compiler transport via batteries-on `trustc ...`
- direct stage toolchain paths under `build/.../stage2/bin/*` for evidence or
  transport debugging

For the full CLI surface beyond the canonical `check` and JSON modes, run
`targo trust --help` or consult the full repo docs checkout.

Packaged-release work for `targo-trust` builds on the existing `x install` /
`x dist` pipeline and must be backed by the install/dist gates before it is
treated as a finished product path.
