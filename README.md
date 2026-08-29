# Trust

Trust is a verifying compiler and toolchain. You write the program and what the
program is supposed to do in the same file, in two languages — Rust for the code
and its contracts, Lean (via Clean) for the mathematics — and the compiler tries
to prove the obligations before it emits a binary. A proof that does not go
through is a build error, not a warning in a separate report.

- **Author:** Andrew Yates
- **License:** Apache-2.0 OR MIT
- **Copyright:** © 2026 Andrew Yates
- **Repo:** <https://github.com/alabsystems/trust>

## What Trust is

A compiler (`trustc`), a package manager (`targo`), a verification driver
(`targo trust`), an SMT solver (`ay`), a theorem prover (`clean`), and a typed
IR (trust-ir) that both source languages target. Verification is a pass inside
the compiler, not a tool that runs beside it: `trustc` and `targo trust` verify
fail-closed by default, and there is no `--verify` flag to remember. Bare
`targo` is the package manager and makes no proof claim; it refuses to compile
at all until you name a lane.

trust-ir has a proof-certificate lane in its format, and no production path
populates it in a *published* module — the direct-artifact inventory hard-fails
on a non-zero certificate count. Modules the compiler builds carry proof
*claims*; the kernel-checked proof term ships on the report row answering them,
content-addressed and independently re-checkable. Read "proof-carrying" as the
IR's design, not as a property of the artifacts this checkout emits.

Trust began as a fork of `rust-lang/rust` and still merges from it, because
compiling all valid Rust identically is a promise we intend to keep. That is
lineage and a compatibility obligation, not the architecture: Trust has its own
version line, IR, solvers, prover, and a second authoritative language upstream
Rust does not have.

The design of record is **one program, two languages**: Rust and Lean are two
syntaxes contributing to the same trust-ir module, and the Clean kernel — a CIC
kernel that re-checks every proof term it is handed — is the sole trust root.
The languages do now meet in one module: under verification a Clean-origin
producer appends Clean-authored functions to the per-crate trust-ir module and
re-points Rust→Clean call edges onto them. Those rows are claim-free and
body-ungated — no codegen consumes them — and obligations are still proved on
the authenticated MIR-derived lane. Most of them do not end at the kernel;
"What counts as evidence" below is the boundary, and [VISION.md](VISION.md) has
the architecture with an itemized what-is-and-is-not-built table.

## The two languages

Contracts are **grammar**. A `requires` / `ensures` / `decreases` clause sits in
the function signature, where the type is:

```rust
fn midpoint(a: u32, b: u32) -> u32
    requires a <= b
    ensures result >= a
    ensures result <= b
{
    a + (b - a) / 2
}
```

`while` and `loop` carry clauses of their own — `invariant` and `decreases`;
`for` has no clause position and is refused with a named blocker rather than
compiled unverified. An `ensures` may cite a Clean theorem by path:
`ensures P by path::to::thm`.

The attribute spelling works too — `#[core::contracts::requires(..)]` /
`#[core::contracts::ensures(..)]`, which in-tree crates use because grammar is
syntax and cannot be `cfg_attr`-stripped for a stable stage0.
`#[trust::decreases(e)]` is literally the same desugaring as
`fn f(..) decreases e`, not a second lane. `#[trust::invariant(..)]` at item
position is refused rather than erased: it once produced a bit-identical
obligation set to deleting it, so it can never mint a vacuous proved row.

Lean enters through a `clean { … }` **parser island** at item position — a
grammar form vanilla Rust rejects, so no valid Rust program changes meaning. The
Rust compiler never name-resolves or type-checks the island body; the real Clean
parser does, and elaboration registers it into a kernel environment. A rejected
island fails the build with a source-spanned diagnostic. Rust clauses may then
name what the island defined:

```rust
clean {
    def ident_isl (x : UInt64) : UInt64 := x
}

fn pass_through(x: u64) -> u64
    ensures result == ident_isl(x)
{
    x
}
```

An uncited `ensures` that calls an island definition can discharge by kernel
definitional equality: admission imports the Rust function's defining equation
into the kernel environment, the island supplies the definition, and the kernel
checks the constructed term. Bodies that only look alike are structurally not
definitionally equal and stay failed.
`tests/ui/trust/e9_island_defeq_discharge.rs` and its two paired RED batteries
pin both directions.

### What actually works today

Three states, honestly:

1. **Pure Rust works.** Clause grammar, safety obligations, contract
   obligations, and the fail-closed verdict machinery are live and exercised by
   the UI test suite. Postconditions now compose across calls: a callee's
   `ensures` this compilation already discharged is *assumed* at the caller
   (local, non-generic, precondition-free callee), and a postcondition may name
   a call to a transparent helper and still discharge automatically, where the
   only route used to be a Clean theorem cited with `by`.
2. **The mixture works, over a narrow Lean subset.** Islands are parsed,
   elaborated, and kernel-checked, and the two languages share a namespace, but
   the Rust token tree delimiting an island bounds it hard:
   - **ASCII only.** Lean's Unicode notation (`→`, `∀`, `≤`) does not lex as
     Rust and is rejected before the island checker sees it. Write `->`,
     `forall`.
   - **No external `.olean` import.** `CleanIslandSession` permanently disables
     external import search, so the environment is Clean's built-in prelude plus
     whatever this crate's own islands declare. An `import` line parses and
     brings in nothing; Mathlib is not reachable.
   - **A `}` inside a Lean comment can end the island early.** It fails closed
     rather than silently moving the boundary; a lexer-level opaque-island mode
     is not built. (A `}` inside a Lean *string* is safe — Rust token trees keep
     a braced quote opaque.)

   Term mode is what the fixtures exercise (`:= rfl`); the island parser is also
   wired to Clean's built-in tactic set.
3. **A pure `.lean` front door exists — in `targo trust`, not in `trustc`.**
   `targo trust check <file.lean>` kernel-checks a standalone Clean/Lean file
   *in process*, through the same parser, elaborator, and CIC kernel the islands
   use, so the verdict cannot depend on which `clean` binary is on `PATH`. It
   fails closed in every direction — an `axiom`, a `sorry`, a false theorem, a
   parse error, and an unreadable file all exit non-zero — and because the
   operand is a file rather than a Rust token tree, Unicode Lean checks here.
   External `.olean` import search is disabled here too, and `targo trust build`
   *refuses* a `.lean` operand rather than let a successful compile read as a
   discharged proof. `trustc` itself has no Lean input path — hand it a `.lean`
   file and it parses it as Rust.

Not built, in those words: PROOF/CALL proof-only visibility, and the TrustJS /
TrustPy / TrustZig frontends. By design those are untrusted, zero-authority
inputs — they must elaborate fail-closed into an inspectable Rust+Lean/trust-ir
artifact with independently fixed fidelity evidence, and may never assert a
proposition. `trust-types`' frontend firewall enforces that structurally, and no
frontend is wired into the compiler or the driver here.

## Versioning

Trust versions itself: `major.minor.dev`, starting at `0.1.0`. `dev == 0` is
public, `dev > 0` is internal, the channel is derived from the dev counter and
never authored, and there are no `-rc` / `-preview` / `-nightly` suffixes. This
line is independent of Rust's: `release/trust-version.toml` is authoritative,
`src/version` is the same number in the form bootstrap reads, and
`src/rust-compat-version` carries the Rust release the `rustc -V` compatibility
protocol reports. `[rust_alignment]` records the last-merged upstream revision as
a compatibility record only — no version, channel, gate, or proof claim derives
from it. Full rules, including what may serve as a stage0, are in the internal
`VERSIONING.md`.

## Build

Trust builds on top of a Trust-named stage0 seed — a previous Trust release, not
upstream Rust nightly.

```bash
# one login covers the repository, its submodules, and the seed release
gh auth login

# clone only the superproject; the recreator owns credential-scoped
# initialization of the pinned backends under first-party/
gh repo clone https://github.com/alabsystems/trust -- --no-recurse-submodules
cd trust

# validate the admitted seed and build Stage2 without falling back to stock Rust
python3 scripts/recreate_bootstrap.py --require-seed --fresh-seed --stage 2
```

The seed path is currently private and supports `aarch64-apple-darwin`; its
payloads are checked against `src/stage0` and
`bootstrap/trust-stage0/seed-ledger.toml`. When no seed is available, `--genesis`
wraps a stock `rustc`/`cargo` as a developer adapter — convenience, never
release evidence. Seed details are in
[bootstrap/trust-stage0/README.md](bootstrap/trust-stage0/README.md),
[INSTALL.md](INSTALL.md) states the current install boundary, and the full
from-scratch runbook is the internal `BOOTSTRAP_FROM_SCRATCH.md`.

**LLVM comes from outside this tree.** Development vendors `src/llvm-project`
and builds it in-tree; the published snapshot does not. Build an LLVM 21+
(22.1.x is what Trust develops against), apply the one patch Trust needs —
`patches/0001-llvm-scalarevolution-guard-cross-phi-addrec-recursion.patch`,
without which the compiler can crash inside `ScalarEvolution` while compiling
itself — and pass `--llvm-config /path/to/llvm-config` to the recreator.
[patches/README.md](patches/README.md) has the exact commands.

Useful recreator flags:

```bash
python3 scripts/recreate_bootstrap.py --check      # prereq report only
python3 scripts/recreate_bootstrap.py --no-fetch   # offline: on-disk payloads only
python3 scripts/recreate_bootstrap.py --no-register  # Stage2, no rustup mutation
python3 scripts/recreate_bootstrap.py -j 8         # cap parallelism
```

Stage2+ recreator runs reject forwarded `x.py` arguments; arbitrary `--set`
overrides are not part of the provenance receipt. Use `x.py` directly for
non-provenance experiments.

Outputs land in `build/<host>/stage2/bin`. The sysroot ships Trust-branded names
only — `trustc`, `targo`, `targo-trust`, `trustd`, `trustdoc`, `trustfmt`,
`targo-fmt`, `tippy`, `targo-tippy`, `tippy-driver`, `trust-analyzer`, `trustup`,
plus the backend binaries below. Three upstream compatibility names are kept as
byte-identical copies: `rustc` and `cargo`, because rustup requires them, and
`rustdoc`, because cargo spawns that name for doctests.

### One command for the `trust` toolchain on a machine that has none

Three repositories — `clean`, `trust-vc`, `aterm` — pin `channel = "trust"` in
their `rust-toolchain.toml`, and their format and lint gates need `trustfmt` and
`tippy` out of a Trust sysroot. Where that channel does not resolve those gates
refuse to run rather than fall back to stock `rustfmt`/`clippy` and report a
green from a different lint set. To make it resolve, from a Trust checkout:

```bash
scripts/install-trust-toolchain.sh     # --dry-run prints the whole plan first
```

It generates a `bootstrap.toml` with `extended = true` and deliberately no
`[build] tools` list (that list is an allowlist — naming any tool silently drops
the verification backends), builds stage 1 (15-36 minutes cold), checks the
output against `tools/verify-toolchain.sh`, links it with
`scripts/rustup-link-trust.sh`, then proves a real format and lint gate runs
through the linked toolchain — and still fails on broken source. It is
idempotent and resumable; a re-run over a linked toolchain re-verifies,
re-links, and re-proves in about two seconds. `--build-dir DIR` builds in a
detached worktree; `--link-only` skips to verify-and-link.

Two things it cannot do for you:

- **`~/.cargo/bin` must be on `PATH`, ahead of any other `rustc`.** The rustup
  shim is the only thing that reads `rust-toolchain.toml`; with a real `rustc`
  in front of it the pin is never consulted. Only your shell rc can fix that:
  `export PATH="$HOME/.cargo/bin:$PATH"`.
- **Do not delete or move the build tree afterwards.** The rustup toolchain is a
  symlink into `build/<host>/stage1`, not a copy, so removing that directory
  breaks every repository that pins the channel.

`scripts/prove-trust-frontend-gate.sh` re-runs the proof at any time. Stage 1 is
a developer artifact, not release evidence.

### Backends

Every backend is built into the sysroot without a per-backend opt-in. `ay`, `ty`
and `clean` ship as binaries; `trust-mc`, `trust-vc` and `ty` also run in-process
behind bridge crates, and `ay` is linked into `trustc` as well.

| Backend | Role |
|---|---|
| `ay` | Primary SMT solver for supported L0 obligations. No general routing or coverage percentage is claimed. |
| `trust-mc` | Bounded model checking, counterexamples |
| `trust-vc` | Auto-active SMT proof calculus; mir-memory certificates |
| `trust-wp` | Zero-capability. Still a registered router backend claiming contract-bearing L1 VCs, but the engine behind it advertises no obligation kinds, so beyond canonical constant folding the lane fail-closes to `Unknown`. The TrustWP proof-authority classes were removed; a historical wire record stays readable for compatibility and cannot mint compiler authority. |
| `ty` | Temporal logic (liveness, fairness). Diagnostics only — no proof credit until input/checker/output binding is authenticated; `targo trust temporal` exits 2 rather than pretend. |
| `clean` | Higher-order theorem prover; its CIC kernel is the trust root for the verdicts that reach it, which today means the `Certified` classes in the internal `TCB.md` |

Each lives under `first-party/` as a pinned submodule, compiled from source by
the same build. The per-VC router additionally consults an unverified in-tree
abstract interpreter (`trust-router`'s interval backend) *ahead* of `ay` for L0;
it is a trusted producer, not an audited engine. The build contract is not
evidence that a given sysroot contains all six — inventory the one you produced:

```bash
build/host/stage2/bin/targo trust doctor    # reported inventory
build/host/stage2/bin/targo trust solvers   # per-backend FOUND/MISSING + routing
```

### Verified codegen (`trust-cg`)

LLVM is the default backend and carries no Trust edits: the machine code a normal
Trust build ships is as unverified as any other compiler's. `trust-cg` is the
experimental alternative — it lowers to its own LIR and emits machine code
directly, so it can decode the bytes it just wrote, compute their machine
semantics, and prove them equal to the semantics derived from the IR for every
input, with the Clean kernel re-checking the certificate where the obligation
lowers into the bit-blast fragment. It is **not in a default build**: the builtin
is `#[cfg(feature = "trust-cg")]`-gated and the default `codegen-backends` list
is LLVM alone, so `-Zcodegen-backend=trust-cg` fails on a stock `./x.py build`.

The fragment is small and enforced: codegen aborts on anything outside it rather
than quietly emitting something weaker.

| | |
|---|---|
| Targets | `aarch64` and `x86_64`, and only the exact audited built-in triples — `*-apple-darwin`, `*-unknown-linux-gnu`, `*-unknown-linux-musl`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`. `wasm32-unknown-unknown` answers target queries and emits MIR but cannot link. Custom JSON targets are rejected even when the file stem matches. |
| Crate types | `rlib` only when linking; executables, dylibs, cdylibs, staticlibs, and proc macros are refused. |
| Panics | `-Cpanic=abort`. Unwinding needs invoke, cleanup, personality, LSDA, and resume semantics — none emitted. |
| Codegen units | exactly one. |
| Refused | debuginfo, LTO (thin, fat, or linker-plugin), incremental, PGO, coverage instrumentation, sanitizers, stack protectors, control-flow/branch/return mitigations, patchable function entries, `-Ctarget-cpu`, `-Ctarget-feature`, code/relocation-model overrides, and LLVM pass controls. |
| ABI | `extern "Rust"` and non-unwinding `extern "C"`. Every argument and the return value must pass directly in an integer register — `bool`, `iN`, or `uN` of at most 64 bits — with no `InReg`, no argument extension, no stack arguments, no variadics, and no hidden or spread arguments. |
| Items | functions only. A reachable `static` or `global_asm!` item is refused. |

The byte-level proof is narrower still than the code the backend compiles: its
machine semantics are wired for AArch64 over straight-line integer scalar shapes.
Outside that, `#[trust::verified_codegen]` reports in those words that only the
structural round-trip check held — a necessary condition on a faithful lowering
that never inspects an instruction. Either way the attribute claims something
about trust-cg's emission, never about the LLVM bytes a default build ships.

## Use

Put `build/<host>/stage2/bin` on your `PATH` and use the Trust names.

```bash
targo trust check                    # verify the current crate
targo trust check --format json      # one row per function
targo trust check --workspace        # whole crate graph
targo trust test                     # verify, then run tests
targo trust report-query --report target/trust/report.json --require proved

targo --unverified build --release   # explicit native build; makes no proof claim
```

`targo trust check` runs the verification pass during compilation and decodes
the per-function rows the compiler emits on stderr. Each row names the function,
the obligation, the backend that handled it, and the verdict: `proved`,
`failed`, `runtime_checked`, `unknown`, `timeout`, `skipped`, `unsupported`,
`canceled`, or `rejected`. The assurance a proved row carries (`Trusted` vs
`Certified`) is a separate axis — see below.

`targo trust check|build|test|report|loop` run the fail-closed verifier with the
`unix_hardened` boundary profile enabled. Dial down only for triage:
`--allow-l0-gaps`, `--no-hardened`, or `[trust]` `level = "L0"|"L1"` in the
project manifest. `trustc -Z trust-verify=off` is the low-level
vanilla-compatibility switch used by bootstrap and upstream-bisecting lanes.

A branded `targo` compile command that names no lane is refused, and the refusal
names both: `targo trust build` verifies fail-closed and produces a proof claim,
`targo --unverified build` prints `UNVERIFIED` and claims nothing. Which claim a
build makes stays a decision the person running it made on purpose.
`targo trust --help` lists the rest of the surface.

## What counts as evidence

Trust's honesty about what it has and has not proved is a feature. Read this
once; the rest of the docs do not re-qualify every sentence.

**An empty report is not a proof.** Policy and supportability filters can
produce zero obligations for a function; use `report-query --require proved`, or
the relevant gate, when you need a positive claim.

**A verdict counts at the assurance level its own gate authenticated.** Adding a
script or retaining a JSON record does not turn a result green: ordinary solver
`UNSAT` without artifact-backed full-verifier evidence is advisory, not
`Trusted` and not transport `proved`.

**`Trusted` does not mean kernel-checked.** Seven of the nine proof-authority
classes the compiler can seal to a row report `Trusted`; two report `Certified`,
and only `Certified` can license codegen check elision — a necessary condition
that today only the kernel-certified class earns. Upstream of all nine sit
unverified trusted producers — contract lowering, MIR extraction, VC generation,
bundle construction, an abstract interpreter, and the bignum carrier runtime —
that decide *which* proposition gets proved and are checked by nothing. The
internal `TCB.md` enumerates them, kept honest by a test here.

**A `proved` count is not the `Trusted` set.** `targo trust` does not publish the
compiler's verdict vector as-is: a favorable row carrying no attachable kernel or
publishable native proof evidence is rewritten to `unknown` first, so the rows
that survive are approximately the `Certified` set. The `--json` report keeps the
demotion reason per row; the terminal report carries an aggregate
`Publication boundary:` line.

**Local build state is not release evidence.** Stage2 readiness is machine-local
and per-commit: a claim must be regenerated on a clean reviewed commit and bind
the compiler identity, tool inventory, source/seed/bootstrap lineage, and the
resulting sysroot. `trustc`'s version stamp embeds HEAD, so a build and the
harness run citing it must share one commit. Stage0 `trustc` is deliberately
rejected for release proof evidence, and no frozen build-directory audit is
current.

**Trust is not strictly superior to Rust** unless a fresh exact-commit run says
so, and that gate is fail-closed. Missing or unknown compatibility, performance,
functional-proof, unsafe-memory, concurrency, and source-to-binary evidence
cannot be converted into passes by feature inventory. Only structured JSON is
admissible: `targo trust domination upstream-tests` (with `--release
--proof-mode full --summary-out --run-id` and explicit target/host provenance),
`targo trust benchmark program-index`, and the `--proof-*-report` /
`--product-proof-release-report` lanes — not manual closure, not shell
transcripts.

**Do not cite the example corpus as proof.** `targo trust verify examples` is a
fail-closed declared-status regression diagnostic: it checks the `VcKind STATUS`
assertions each example names, nothing more, and its report sets
`proof_evidence=false` and `release_evidence=false` because source and tool
provenance are not authenticated. Release proof requires the gate sequence —
`targo trust verify cargo-cache`, `verify repo-gate`, `verify self
--full-verifier`, and the relevant `targo trust release check` profiles.

**Bootstrap is not self-proof.** The compiler currently bootstraps with
verification explicitly disabled. Self-proof is the goal, not a present claim.

## Upstream compatibility

Drop-in behavior relative to upstream Rust is a release gate. Trust must either
pass an upstream Rust test or carry a reviewed, narrowly-scoped, time-bounded
ledger entry. A failure without a ledger entry is a regression, not a deviation.
The baseline still records surfaces as `unknown`, so this is a gate, not a
completed claim.

The ledgers live under `tests/upstream-rust/`: `baseline.toml` pins the upstream
revision; `test-exceptions.toml` holds per-test exceptions (the schema rejects an
entry with no `expires_on`); `divergence-audit.toml` is the category-level audit;
`patches.toml` records every reviewed edit to an upstream test;
`upstream-fixes.toml` tracks drift and adopted fixes.

```bash
targo trust domination upstream-tests      # canonical runner
python3 scripts/check_ledger_expirations.py  # non-zero on any expired entry
```

The runner claims success only on a fully green, complete-artifact scorecard,
modulo active exceptions. All Trust modifications to upstream files are marked
`// Trust:` so merges stay tractable, and we fix bugs at the root cause — every
fix lands with a regression test. A `compiler/` change that causes new
upstream-test failures must fix them or land a `kind = "intentional_divergence"`
exception carrying a reason, an issue link, and an `expires_on` date.

## Repository layout

```
trust/
├── compiler/       # rustc crates (upstream + Trust modifications marked `// Trust:`)
├── crates/         # 70 Trust-owned packages: the verification pipeline, the
│                   #   Clean bridges, and the unwired TrustJS/TrustTS lanes
├── targo-trust/    # the `targo trust` verification driver
├── first-party/    # pinned submodules: ay, clean, ny, ty, trust-cg, trust-ir,
│                   #   trust-mc, trust-vc, trust-wp
├── vendor/         # foreign vendored deps (carcara, lean-core-oleans, rustc_version)
├── library/        # Rust standard library (upstream)
├── src/            # driver, bootstrap, tools (upstream + modifications)
├── tests/          # test suite (upstream layout + Trust verification tests)
└── x.py            # build system entry point
```

`first-party/trust` is a symlink back to the superproject root, not a tenth
submodule. Clone with `--no-recurse-submodules`; the bootstrap recreator
materializes only a *missing* indexed gitlink and never moves one already
materialized. Do not run recursive submodule updates or pull inside an occupied
`first-party/<name>`.

## macOS coordinator companion

`tools/trustd-menubar` is a standalone universal macOS 13+ menubar app — a
read-only, same-user STATUS observer for `trustd`, never a compiler, installer,
daemon controller, or proof UI, and it changes no toolchain or daemon state.
`tools/trustd-menubar/install.sh --open` publishes
`~/Applications/TrustdMenubar.app` atomically under a current-user lock and
checks both architecture CDHashes; that ad-hoc signature checks bundle coherence
only — it identifies no publisher, and the app is not Developer-ID signed,
notarized, or a downloadable release artifact. See
`tools/trustd-menubar/README.md`.

## License

Trust is dual-licensed under Apache-2.0 and MIT. See `LICENSE-APACHE` and
`LICENSE-MIT`.

## Security

See [SECURITY.md](SECURITY.md). Report vulnerabilities privately via GitHub
Security Advisories.
