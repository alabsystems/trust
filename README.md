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
IR (trust-ir) that both source languages target. Verification is a
pass inside the compiler, not a tool that runs beside it: `trustc` and
`targo trust` verify fail-closed by default, and there is no `--verify` flag to
remember. Bare `targo` is the package manager and makes no proof claim; it
refuses to compile at all until you name a lane.

trust-ir has a proof-certificate lane in its format, and no production path
populates it. Modules the compiler builds carry proof *claims*; the
kernel-checked proof term ships on the report row that answers them, which is
content-addressed and independently re-checkable. Read "proof-carrying" as the
IR's design, not as a property of the artifacts this checkout emits.

Trust began as a fork of `rust-lang/rust` and still merges from it, because
compiling all valid Rust identically is a promise we intend to keep. That is
lineage and a compatibility obligation. It is not the architecture. Trust has
its own version line, its own IR, its own solvers, its own prover, and a second
authoritative language that upstream Rust does not have.

The design of record is **one program, two languages** (specified internally
by the two-language spec-surface document and its companion language-design
paper): Rust and Lean are two
syntaxes contributing to the same trust-ir module, and the Clean kernel — a CIC
kernel that re-checks every proof term it is handed — is the sole trust root.
Both halves of that sentence are the target, not the whole of today:
authenticated MIR-derived lanes still carry real verdicts while the direct
producers finish, and of the eleven ways an obligation can pass verification
today, nine end at a trusted engine, an adapter, or a compiler-composed
derivation instead of a kernel re-check of that obligation.
The internal `TCB.md` enumerates them one per row, with the trusted
producers that sit upstream of every one of them; the "Proof authority" section
below carries the same boundary in summary.
[VISION.md](VISION.md) has the architecture and an itemized what-is-and-is-not-
built table. The internal `DESIGN_PHILOSOPHY.md` is the
standing ruleset every plan and PR is held to — verification by default, no
flags-heavy designs, trust-ir as the target universal IR, drop-in by
construction, own the supply chain.
The internal `READINESS.md` answers the two questions this page will
raise — is it usable yet, is it publishable yet — from measurements, and names
the command behind each answer so it can be re-measured rather than argued.

## The two languages

Contracts are **grammar**, not attributes. A `requires` / `ensures` / `decreases`
clause sits in the function signature, where the type is:

```rust
fn midpoint(a: u32, b: u32) -> u32
    requires a <= b
    ensures result >= a
    ensures result <= b
{
    a + (b - a) / 2
}
```

Lean enters through a `clean { … }` **parser island** at item position — a
grammar form vanilla Rust rejects, so no valid Rust program changes meaning. The
island body is never name-resolved or type-checked by the Rust compiler; it is
parsed by the real Clean parser, elaborated, and registered into a kernel
environment, and a rejected island fails the build with a source-spanned
diagnostic. Rust clauses may then name what the island defined:

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
definitionally equal and stay failed —
`tests/ui/trust/e9_island_defeq_discharge.rs` and its two paired RED batteries
pin both directions.

### What actually works today

Three states, honestly:

1. **Pure Rust works.** Clause grammar, safety obligations, contract
   obligations, and the fail-closed verdict machinery are live and exercised by
   the UI test suite.
2. **The mixture works, over a narrow Lean subset.** `clean { … }` islands are
   parsed, elaborated, and kernel-checked, and the two languages share a
   namespace. But the island is still delimited by a *Rust* token tree, which
   bounds it hard:
   - **ASCII only.** Lean's Unicode notation (`→`, `∀`, `≤`) does not lex as
     Rust and is rejected before the island checker ever sees it. Write `->`,
     `forall`.
   - **No external `.olean` import.** `CleanIslandSession` permanently disables
     external import search, so the environment is Clean's built-in prelude plus
     whatever this crate's own islands declare. An `import` line parses and
     brings in nothing. Mathlib is not reachable.
   - **A `}` inside a Lean comment or string can end the island early.** These
     cases fail closed rather than silently moving the boundary; a real
     lexer-level opaque-island mode is not built.

   Term-mode and the built-in tactics both work inside an island (`:= rfl`,
   `:= by induction n with …`).
3. **A pure `.lean` front door exists — in `targo trust`, not in `trustc`.**
   `targo trust check <file.lean>` kernel-checks a standalone Clean/Lean file
   *in process*, through the same parser, elaborator, and CIC kernel the islands
   use, so the verdict cannot depend on which `clean` binary is on `PATH`. It
   fails closed in every direction — an `axiom`, a `sorry`, a false theorem, a
   parse error, and an unreadable file all exit non-zero — and because the
   operand is a file rather than a Rust token tree, Unicode Lean checks here
   even though it cannot appear in an island. Two boundaries hold: external
   `.olean` import search is disabled, so only crate-local Clean is authority,
   and `targo trust build` *refuses* a `.lean` operand rather than let a
   successful compile read as a discharged proof. `trustc` itself still has no
   Lean input path — hand it a `.lean` file and it parses it as Rust.

Not built, in those words: PROOF/CALL proof-only visibility, and the TrustJS /
TrustPy / TrustZig frontends. The frontend campaigns are admitted by design only
as untrusted, zero-authority inputs — they must elaborate fail-closed into an
inspectable Rust+Lean/trust-ir artifact with independently fixed fidelity
evidence, and may never assert a proposition. None of them ships here.

## Versioning

Trust versions itself: `major.minor.dev`, starting at `0.1.0`. `dev == 0` is
public, `dev > 0` is internal, the channel is derived from the dev counter and
never authored, and there are no `-rc` / `-preview` / `-nightly` suffixes. This
line is independent of Rust's: `release/trust-version.toml` is authoritative,
`src/version` is the same number in the form bootstrap reads, and
`src/rust-compat-version` carries the Rust release that the `rustc -V`
compatibility protocol reports. The last-merged upstream revision is recorded in
`[rust_alignment]` as a compatibility record only — nothing derives a version,
channel, gate, or proof claim from it.

Full rules, including what may serve as a stage0, are kept in the internal
`VERSIONING.md`.

## Build

Trust builds on top of a Trust-named stage0 seed — a previous Trust release, not
upstream Rust nightly.

```bash
# one login covers the private repo, its submodules, and the seed release
gh auth login

# clone only the superproject; the recreator owns bounded, credential-scoped
# initialization of the pinned backends under first-party/
gh repo clone https://github.com/alabsystems/trust -- --no-recurse-submodules
cd trust

# validate the admitted seed and build Stage2 without falling back to stock Rust
python3 scripts/recreate_bootstrap.py --require-seed --fresh-seed --stage 2
```

The seed path is currently private and supports `aarch64-apple-darwin`; its
payloads are checked against `src/stage0` and
`bootstrap/trust-stage0/seed-ledger.toml`. When no seed is available, `--genesis`
wraps a stock `rustc`/`cargo` as a developer adapter. A genesis build is
convenience, never release evidence. The full from-scratch runbook is the
internal `BOOTSTRAP_FROM_SCRATCH.md`; seed details are in
[bootstrap/trust-stage0/README.md](bootstrap/trust-stage0/README.md).

**LLVM comes from outside this tree.** Development vendors `src/llvm-project`
and builds it in-tree; the published snapshot does not carry it. Build an LLVM
21+ (22.1.x is what Trust develops against), apply the one patch Trust needs —
`patches/0001-llvm-scalarevolution-guard-cross-phi-addrec-recursion.patch`,
without which the compiler can crash inside `ScalarEvolution` while compiling
itself — and pass `--llvm-config /path/to/llvm-config` to the recreator. See
[patches/README.md](patches/README.md) for the exact commands.

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
`targo-fmt`, `tippy`, `tippy-driver`, `trust-analyzer`, plus the backend binaries
below. Only `cargo` and `rustc` survive as symlinks, because rustup requires
them.

### Backends

Every backend is built into the sysroot without a per-backend opt-in. Three ship
as binaries (`ay`, `ty`, `clean`); three run in-process behind bridge crates.

| Backend | Kind | Role |
|---|---|---|
| `ay` | binary | Primary SMT solver for supported L0 obligations. No general routing or coverage percentage is claimed. |
| `trust-mc` | in-process | Bounded model checking, counterexamples |
| `trust-vc` | in-process | Auto-active SMT proof calculus; mir-memory certificates |
| `trust-wp` | in-process | Deductive WP, RustHorn prophecy `&mut` encoding |
| `ty` | binary | Temporal logic (liveness, fairness). Diagnostics only — no proof credit until input/checker/output binding is authenticated; `targo trust temporal` exits 2 rather than pretend. |
| `clean` | binary | Higher-order theorem prover; its CIC kernel is the trust root for the verdicts that reach it, which today means the `Certified` classes in the internal `TCB.md` |

Each lives under `first-party/` as a pinned submodule and is compiled from
source by the same build. That build contract is not evidence that a particular
sysroot contains all six — inventory the one you produced:

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
lowers into the bit-blast fragment.

The fragment it covers is small, and it is enforced rather than advertised:
codegen aborts on anything outside it instead of quietly emitting something
weaker. The exact conditions:

| | |
|---|---|
| Targets | `aarch64` and `x86_64`, and only the exact audited built-in triples — `*-apple-darwin`, `*-unknown-linux-gnu`, `*-unknown-linux-musl`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`. `wasm32-unknown-unknown` answers target queries and emits MIR but cannot link. Custom JSON targets are rejected even when the file stem matches. |
| Crate types | `rlib` only, when linking. Executables, dylibs, cdylibs, staticlibs, and proc macros are refused rather than advertised as usable. |
| Panics | `-Cpanic=abort`. Unwinding needs invoke, cleanup, personality, LSDA, and resume semantics, none of which is emitted. |
| Codegen units | exactly one. |
| Refused | debuginfo, LTO (thin, fat, or linker-plugin), incremental, PGO, coverage instrumentation, sanitizers, stack protectors, control-flow/branch/return mitigations, patchable function entries, `-Ctarget-cpu`, `-Ctarget-feature`, code/relocation-model overrides, and LLVM pass controls. |
| ABI | `extern "Rust"` and non-unwinding `extern "C"`. Every argument and the return value must pass directly in an integer register — `bool`, `iN`, or `uN` of at most 64 bits — with no `InReg`, no argument extension, no stack arguments, no variadics, and no hidden or spread arguments. |
| Items | functions only. A reachable `static` or `global_asm!` item is refused. |

The byte-level proof is narrower still than the code the backend compiles: its
machine semantics are wired for AArch64 over straight-line integer scalar shapes.
Outside that, `#[trust::verified_codegen]` reports that only the structural
round-trip check held — a necessary condition on a faithful lowering that never
inspects an instruction — and says so in those words rather than borrowing the
stronger sentence. The attribute is a claim about trust-cg's emission for the
compilation's target; a build on the default LLVM backend still ships LLVM's
bytes, which the attribute does not certify.

## Use

Put `build/<host>/stage2/bin` on your `PATH` and use the Trust names.

```bash
targo trust check                    # verify the current crate
targo trust check --format json      # one row per function
targo trust check --workspace        # whole crate graph
targo trust report-query --report target/trust/report.json --require proved

targo --unverified build --release   # explicit native build; makes no proof claim
```

`targo trust check` runs the verification pass during compilation and decodes
the per-function rows the compiler emits on stderr. Each row names the function,
the obligation, the backend that handled it, and the verdict — proved,
kernel-certified, runtime-checked, failed, or unknown.

Verification front doors are batteries-on. `targo trust check|build|report|loop`
run the fail-closed verifier with the `unix_hardened` boundary profile enabled,
and there is no activation flag to remember. Dial down only for triage:
`--allow-l0-gaps`, `--no-hardened`, or `[trust]` `level = "L0"|"L1"` in the
project manifest.
`trustc -Z trust-verify=off` is the low-level vanilla-compatibility switch used by
bootstrap and upstream-bisecting lanes.

Branded native `targo` compile commands refuse an implicit unverified mode, and
the refusal names both lanes and the claim each one's artifact carries:
`targo trust build` verifies fail-closed and produces a proof claim;
`targo --unverified build` prints `UNVERIFIED` and claims nothing. `targo` never
elevates itself into the verified lane — it is the package manager, and which
claim a build makes stays a decision the person running it made on purpose.

## What counts as evidence

Trust's honesty about what it has and has not proved is a feature, and this
section is where that discipline lives. Read it once; the rest of the docs do
not re-qualify every sentence.

**An empty report is not a proof.** Policy and supportability filters can
produce zero obligations for a function. Use `report-query --require proved`, or
the relevant gate, when you need a positive claim.

**A verdict counts at the assurance level its own gate authenticated.** Adding a
script or retaining a JSON record does not turn a result green. Ordinary solver
`UNSAT` without artifact-backed full-verifier evidence is advisory, not
`Trusted` and not transport `proved`. `Proved` is commonly `Trusted`;
certificate-grade kernel re-checking is not the default result path.

**`Trusted` does not mean kernel-checked.** Nine of the eleven proof-authority
classes the compiler can seal to a row report `Trusted`; only two report
`Certified`, and only `Certified` licenses codegen check elision. Upstream of
all eleven sit unverified trusted producers — contract lowering, MIR
extraction, VC generation, bundle construction, and an abstract interpreter —
that decide *which* proposition gets proved and are checked by nothing.
The internal `TCB.md` is the enumeration, kept honest by a test in this
repository; the eleven classes and their statuses are summarized above.

**Local build state is not release evidence.** Stage2 readiness is machine-local
and per-commit: a claim must be regenerated on a clean reviewed commit and bind
the compiler identity, tool inventory, source/seed/bootstrap lineage, and the
resulting sysroot. `trustc`'s version stamp embeds HEAD, so a build and the
harness run that cites it must share one commit. Stage0 `trustc` is deliberately
rejected for release proof evidence, and no frozen build-directory audit is
current evidence.

**Trust is not strictly superior to Rust** unless a fresh exact-commit run says
so, and that gate is fail-closed. Missing or unknown AArch64/x86-64
compatibility, performance, functional-proof, unsafe-memory, concurrency, and
source-to-binary evidence cannot be converted into passes by feature inventory.
The admissible evidence is structured JSON from
`targo trust domination upstream-tests` (with `--release --proof-mode full
--summary-out --run-id` and explicit target/host provenance),
`targo trust benchmark program-index`, and the `--proof-*-report` /
`--product-proof-release-report` lanes — not manual closure, not shell
transcripts.

**Do not cite the example corpus as proof.** `targo trust verify examples` is a
fail-closed declared-status regression diagnostic: it checks the `VcKind STATUS`
assertions each example names, nothing more, and its report sets
`proof_evidence=false` and `release_evidence=false` because source and tool
provenance are not authenticated. Release proof requires the gate sequence —
`targo trust verify cargo-cache`, `targo trust verify repo-gate`,
`targo trust verify self --full-verifier`, and the relevant
`targo trust release check` profiles.

**Bootstrap is not self-proof.** The compiler currently bootstraps with
verification explicitly disabled. Self-proof is the goal, not a present claim.

The current disposition ledger is kept internally as `DAILY_DRIVER_LAUNCH.md`.

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
fix lands with a regression test.

Working rule for any PR touching `compiler/`: a change that causes new
upstream-test failures must either fix the regression or land a
`test-exceptions.toml` entry with `kind = "intentional_divergence"`, a reason
arguing the divergence is intentional and superior, an issue link, and an
`expires_on` date.

## Repository layout

```
trust/
├── compiler/       # rustc crates (upstream + Trust modifications marked `// Trust:`)
├── crates/         # 65 Trust-owned packages: the verification pipeline, the
│                   #   Clean bridges, and the TrustJS/TrustTS lanes
├── targo-trust/    # the `targo trust` verification driver
├── first-party/    # pinned submodules: ay, clean, ny, ty, trust-cg, trust-ir,
│                   #   trust-mc, trust-vc, trust-wp
├── vendor/         # foreign vendored deps (carcara, lean-core-oleans, rustc_version)
├── library/        # Rust standard library (upstream)
├── src/            # driver, bootstrap, tools (upstream + modifications)
├── tests/          # test suite (upstream layout + Trust verification tests)
└── x.py            # build system entry point
```

Clone the superproject with `--no-recurse-submodules`; the bootstrap recreator
materializes only a *missing* indexed gitlink and never moves a sibling that is
already materialized. Do not run recursive submodule updates or pull inside an
occupied `first-party/<name>`.

## macOS coordinator companion

`tools/trustd-menubar` is a standalone universal macOS 13+ menubar app: a
read-only, same-user STATUS observer for `trustd`. It is not the compiler,
installer, daemon controller, or proof UI, and it never changes toolchain or
daemon state.

```bash
tools/trustd-menubar/install.sh --open
```

The script atomically publishes `~/Applications/TrustdMenubar.app` under a
cooperative current-user lock and checks both signed architecture CDHashes. The
ad-hoc signature checks bundle coherence only — it identifies no publisher, and
the app is not Developer-ID signed, notarized, or a downloadable release
artifact. See `tools/trustd-menubar/README.md`.

## License

Trust is dual-licensed under Apache-2.0 and MIT. See `LICENSE-APACHE` and
`LICENSE-MIT`.

## Security

See [SECURITY.md](SECURITY.md). Report vulnerabilities privately via GitHub
Security Advisories.
