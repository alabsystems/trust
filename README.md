# Trust

Trust is a compiler for Rust and Lean, built as a drop-in replacement for rustc
and Lean 4. It is built to make builds and binaries faster—and prove what it
builds: never compile or test the same thing twice, and take an optimization
only with a proof, up to replacing an algorithm across the whole program.

Specs are part of the language: `requires`, `ensures`, and `decreases` sit in
the signature, and Lean theorems sit in `clean { }` blocks next to the code.
The goal is that every flaw is a compile error that shows the input that
triggers it and the ways to fix it.

Trust is built for a future where AI writes nearly all code and the compiler
is the reviewer: a language model in the compiler loop proposes proofs, fixes,
specs, and faster code, while a small kernel accepts only what it can check.

This page is the short version, and [VISION.md](VISION.md) is the full vision.
Trust is in active development, and these are its goals.

Apache-2.0 OR MIT · <https://github.com/alabsystems/trust> · attribution in
[COPYRIGHT](COPYRIGHT)

## One example

A binary search, with its spec in the signature:

```rust
fn search(v: &[u32], x: u32) -> Option<usize>
    requires is_sorted(v)
    ensures match result {
        Some(i) => i < v.len() && v[i] == x,
        None    => !v.contains(&x),
    }
{
    let (mut lo, mut hi) = (0, v.len());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < x { lo = mid + 1; }
        else if v[mid] > x { hi = mid; }
        else { return Some(mid); }
    }
    None
}
```

The `requires` line is what callers must guarantee: the slice is sorted. The
`ensures` lines are what the function promises: an index it returns holds `x`,
and `None` means `x` is nowhere in the slice.

What Trust will prove about it:

- **On its own.** Every `v[mid]` is in bounds, nothing overflows, and the loop
  ends, because `hi - lo` shrinks on every turn. No annotation is needed.
- **With help.** The `ensures` needs one fact about the loop: `x` is not in
  `v[..lo]` and not in `v[hi..]`. A solver or the model in the loop proposes
  it. The kernel checks that it holds on entry, holds after every turn, and
  implies the promise when the loop ends.
- **Down to the binary.** The compiler-correctness theorem carries the proof to
  the machine code. The binary itself is proved to meet the spec.
- **For every caller.** Code that calls `search` relies only on its spec. If
  the loop later finds a faster version, Trust proves it meets the same spec,
  and nothing that calls `search` is re-proved or re-tested.

[examples/demo/](examples/demo/README.md) walks through Trust on a binary
search.

## The big ideas

### The seed and the self-proved compiler

Everything Trust proves rests on a small seed, the only thing taken on faith:
Lean's three standard axioms (propositional extensionality, quotient soundness
and the axiom of choice), a formal model of what every Rust program means, and
formal models of the Arm and x86 instruction sets. The kernel, the small checker
that verifies every proof, is not taken on faith. Its first job is to prove
itself from the three axioms. By design that checker is written in Lean,
compiled by Trust and proved against a model built from sets, one bound on
universe levels at a time; Clean's large kernel only proposes the steps it
replays. Today the large kernel still decides.

On the seed sits one theorem: for every Rust program Trust accepts, the binary
does only what the Rust model allows. Trust proves it once, pass by pass, about
its own source, because the compiler is a Rust program. Then the compiler
compiles itself, which carries the theorem to the binary you run. Ken Thompson's
*Reflections on Trusting Trust* showed that a compiler binary can hide behavior
its source does not show. A compiler that is proved correct and compiles itself
has nowhere to hide it. Clean, Trust's implementation of Lean 4, gets the same
treatment.

Each proved program becomes a building block of a proof tower. The kernel
proves the verifier, the verifier proves the compiler, and the compiler builds
proved tools: a solver, an optimizer, a build cache, a model checker. Each layer
adds capability and nothing to what must be trusted.

### Specs in the language

A spec is part of the program, checked on every build. `requires`, `ensures`
and `decreases` sit in the signature, where the types are. `while` and `loop`
carry `invariant` and `decreases`. A `clean { }` block holds real Lean, and Rust
clauses can name what it defines:

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

Clean's parser and kernel check the island, and a rejected island fails the
Rust build. Vanilla Rust rejects this form, so no valid Rust program changes
meaning.

A program uses as many of three layers as it needs:

1. **The language.** With no spec at all, Trust proves the program never
   panics, overflows, indexes out of bounds, divides by zero, hits undefined
   behavior in `unsafe` code, races or deadlocks, in your code and every
   dependency.
2. **Library contracts.** Library functions carry `requires` and `ensures`, so
   injection, broken access control and leaked resources become compile errors.
3. **Your requirements.** Clauses on your own functions, and Lean theorems for
   anything mathematical.

### An LLM in the compiler loop

AI writes code faster than anyone can review it, so the reviewer has to be the
compiler. Trust puts a language model inside the compiler loop, with the kernel
behind it. The model is creative and untrusted; the kernel accepts only what it
can check.

1. **Prove.** Solvers discharge most obligations. Where one gets stuck, the
   model proposes the missing piece, such as a loop invariant, and the kernel
   checks it.
2. **Fix.** A false obligation becomes an error that names the rule, shows the
   input that breaks it and lists the ways to fix it. Errors are written for an
   AI reader first.
3. **Make it provable.** Code too tangled to prove is rewritten into code that
   does the same thing and can be proved.
4. **Strengthen.** The model infers the strongest spec the code supports, and
   accepted specs go into the source.
5. **Improve.** The model proposes faster versions. Each lands only with a
   proof that it meets the same spec.
6. **Check every change.** Every edit comes with its behavior diff: the inputs
   where old and new code disagree, summed up as a few named changes. The diff
   goes back to the model that made the change and to a reviewer model.

This is the original design of Trust: prove, strengthen, backpropagate (rewrite
the program until the proof goes through), prove again. The result is a
compiler that improves your program, not one that only translates it.

### Faster builds, faster binaries

A change proved to leave behavior the same rebuilds nothing, re-proves nothing
and re-runs no tests downstream. A spec says what must stay the same, so the
compiler is free to change everything else: delete checks that can never fire,
spread loops across cores, change data layouts, replace a slow algorithm with a
fast one. Most code needs only the first two layers and a few promises. Full
functional specs pay in the foundations everything stands on and in the hot
spots you want faster, where the spec licenses the optimization.

### Proven software consumes software

Proven software grows by absorbing what exists, not by rewriting it. Rust code
compiles with Trust unchanged. The loop fixes every place it can fail, gives it
a spec and proves it, and from then on its users rely on the theorem, not the
code. Each program absorbed makes the next one cheaper, because a proved
library's spec is what makes its users provable.

### Autoformalization

Every proof is about Rust or Lean, so other languages come in by translation.
Autoformalization, offered as a service, turns a program in any language into
idiomatic Rust, and turns what it is meant to do, from its docs, tickets,
schemas and tests, into `requires`, `ensures` and Lean theorems. A behavior diff
against the original checks the translation. Then the compiler loop reports
every bug the old language let through, as a compile error with a proposed fix.

## The goals

- **A drop-in compiler.** Every valid Rust program and every Lean 4 project
  builds with Trust unchanged.
- **Every flaw a compile error**, in your code and in every dependency, with the
  input that triggers it and the ways to fix it.
- **Every proof kernel-checked.** Every one of the eighteen proof-authority
  classes is to be re-checked by the kernel's checker (by design the proved
  Lean checker `kcheck`; until then the Clean kernel), so every result is
  `Certified`. That is the goal, not today's default lane: see
  `docs/TCB.md`'s "Current verdict boundary".
- **A self-proved compiler.** The kernel proves itself from three axioms, the
  compiler is proved once, pass by pass, and then compiles itself.
- **Never build or test the same thing twice.** From save to test result in
  under a second.
- **Speed from proof.** trust-cg replaces LLVM, and every optimization, up to
  replacing an algorithm across the whole program, ships with its proof.
- **An LLM in the compiler loop** that proves, fixes, strengthens and improves
  your program, with a kernel it cannot fool.
- **Every language comes in.** Autoformalization turns a program in any
  language into proved Rust and Lean.

## Install

On Apple-silicon macOS, install [aterm](https://github.com/alabsystems/aterm#install).
Its package manager, atpkg, installs Trust from this repository's signed
releases and links rustup's `trust` toolchain to it (`aterm pkg install trust`
does it by hand). [INSTALL.md](INSTALL.md) has the full contract.

## Build

Building from source needs:

- **rustup on `PATH` ahead of any other `rustc`.**
- **LLVM 21 or newer** (Trust develops against 22.1.x), built outside this tree
  with the one patch in [patches/](patches/README.md) applied. Without it the
  compiler can crash inside LLVM's `ScalarEvolution` while compiling itself.
- **A bootstrap compiler (stage0).** Its release is private today, so a public
  clone cannot build the compiler yet. A stock `rustc`/`cargo` stage0 is not
  supported ([bootstrap/trust-stage0/README.md](bootstrap/trust-stage0/README.md),
  "No bring-your-own-toolchain stage0").

```bash
gh repo clone https://github.com/alabsystems/trust -- --no-recurse-submodules
cd trust
scripts/fetch-first-party.sh            # the nine first-party repos

python3 scripts/recreate_bootstrap.py \
    --stage 2 --require-seed --fresh-seed \
    --llvm-config /path/to/llvm-config
```

`--require-seed --fresh-seed` fetches the pinned seed with an authenticated
`gh`, checks it against the `src/stage0` pins, and refuses rather than fall back
to a stock compiler. Outputs land in `build/<host>/stage2/bin`. Useful flags:
`--no-fetch` (offline), `--no-register` (no rustup change), `-j N`. Development
checkouts have real submodules under `first-party/` and skip
`fetch-first-party.sh`.

To check prerequisites without building, run
`python3 scripts/recreate_bootstrap.py --require-seed --no-atpkg --check`. It
never fetches, so it reports the seed unavailable until the pinned payloads are
on disk, and it cannot be combined with `--fresh-seed`. For a Stage 2 build it
also checks the native tools and SDK the build needs, and exits 1 if one is
missing (INSTALL.md, "Native tools of the Stage 2 build", says how to supply
them). Once it has selected a stage0, its last line names it, pass or fail:
`--check: prerequisites OK (stage0 mode: seed).` or
`--check: prerequisites NOT met (stage0 mode: seed).`

The sysroot ships Trust names: `trustc`, `targo`, `tippy`, `trustfmt`,
`trustdoc` and `trust-analyzer`. `rustc` and `cargo` stay as compatibility names
because rustup spawns them. `rustc` is `trustc`. `cargo` is the `targo`
executable running plain upstream Cargo semantics, so it is not a way to run
`targo`.

To make sibling repositories that pin `channel = "trust"` resolve:

```bash
scripts/install-trust-toolchain.sh      # --dry-run prints the plan first
```

Once you have a stage 2, prefer a sealed artifact. A live `build/` tree empties
`bin/` during every `x.py` run, so a channel pointed there fails intermittently
with `error[E0463]`:

```bash
# immutable artifact + atomic channel flip; needs a helper program and a build
# slot, both given in INSTALL.md, "Register the toolchain"
TRUST_TOOLCHAIN_SERIAL_COMMAND=<absolute path of trust-serial-command> \
  python3 scripts/build-slot --cpus 1 -- bash scripts/promote-toolchain.sh
```

## Use

```bash
targo trust check                     # verify the current crate
targo trust check --format json       # one row per function
targo trust check --workspace         # every workspace member (not dependencies)
targo trust check --certify           # every unproved obligation fails the build
targo trust test                      # verify, then run tests
targo trust loop file.rs              # prove, strengthen, backpropagate, prove again
targo trust diff --baseline FILE      # fail on any proof lost against a baseline
targo trust doctor                    # what this sysroot contains
targo trust solvers                   # which solvers are found

targo trust check file.lean                                  # kernel-check a Lean file
targo trust build file.lean --emit=trust-ir --out lib.json    # build a Lean IR library

targo --unverified build --release    # a native build that claims nothing
```

`trustc` and `targo trust` verify by default. Bare `targo` is the package
manager and makes no proof claim: verbs with a verified `targo trust`
counterpart refuse until you name a lane, and the rest run unverified and print
an `UNVERIFIED:` notice. Dial down only for triage: `--allow-l0-gaps`,
`--no-hardened`, or `[trust] level = "L0"` in the manifest. Budget for the
cost: the verifier allows each obligation 5 s by default under `targo trust`
(`[trust] timeout_ms`, passed as `-Ztrust-verify-timeout-ms`; raw `trustc`
defaults to 20 s since `40220cd450f`), so a crate's check time scales with how
many obligations miss rather than with how many it has.

You pick properties, not provers. Engines such as the ay SMT solver, the
trust-mc model checker and the Clean prover sit behind one router. Their output
is untrusted, and only a Clean kernel re-check of a row's own goal earns
`Certified`.

## Repository layout

```
compiler/      rustc crates (upstream + Trust edits marked `// Trust:`)
library/       Rust standard library (upstream)
src/           driver, bootstrap, tools
crates/        Trust-owned packages: the verification pipeline and Clean bridges
targo-trust/   the `targo trust` verification driver
first-party/   the nine first-party repos: ay, clean, ny, ty, trust-cg,
               trust-ir, trust-mc, trust-vc, trust-wp
tests/         upstream layout + Trust verification tests
scripts/       bootstrap recreator, toolchain install, gates
patches/       the LLVM patch Trust requires
examples/      contract and island fixtures
x.py           build system entry point
```

`first-party/trust` is a symlink back to the superproject root, not a tenth
submodule. Clone with `--no-recurse-submodules`, and do not run recursive
submodule updates inside an occupied `first-party/<name>`.

Trust began as a fork of `rust-lang/rust` and still merges from it. Every Trust
edit to an upstream file is marked `// Trust:`, and bugs are fixed at the root
cause with a regression test. Harness exceptions need reviewed, expiring ledger
entries under `tests/upstream-rust/`; they cannot waive a valid Rust program.
The upstream test runner is `targo trust domination upstream-tests`.

## Contributing

[CONTRIBUTING.md](CONTRIBUTING.md) · [SUPPORT.md](SUPPORT.md) ·
[CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md)

Report vulnerabilities privately via GitHub Security Advisories — see
[SECURITY.md](SECURITY.md).

## License

Dual-licensed under Apache-2.0 and MIT. See [LICENSE-APACHE](LICENSE-APACHE),
[LICENSE-MIT](LICENSE-MIT), and [COPYRIGHT](COPYRIGHT) for the upstream
`rust-lang/rust` attribution this fork carries.
