# Trust — Vision

Trust is a compiler for Rust and Lean, built to be a drop-in replacement for
rustc and for Lean 4. It will make builds much faster, because it will never
compile or test the same thing twice. It will make binaries faster, because it
will prove an optimization correct before it takes it, up to replacing an
algorithm across the whole program. And it will prove what it builds. The spec
is part of the program, and every flaw will be a compile error.

A language model inside the compiler will propose proofs, fixes and faster code,
and a small kernel will accept only what it can check. Trust is built for a
future where AI writes nearly all code.

This document states the goals of Trust and the design that reaches them.

- **Author:** Andrew Yates
- **Repo:** <https://github.com/alabsystems/trust>

## Proven software

Software today is written, tested and trusted. Tests check the cases someone
thought of. Reviews check what someone had time to read. Everything else is
hope.

Trust makes a different kind of software: **proven software**. Every program
carries a machine-checked proof of the promises it makes and of the failures
it can never have. The proofs start from three axioms and build upward, layer
by layer. Each proved program becomes a building block for the next.

Proven software does not replace ordinary software by rewriting it. It
**consumes** it. Existing programs are pulled in, given a precise statement of
what they do, proved, and from then on used only through that proof. Each
program absorbed makes the next one cheaper. The proven world grows, and
nothing it has proved is ever lost.

Trust is the compiler that makes this possible. It compiles Rust and Lean, it
proves itself correct, and then it proves everything it builds. Rust will
compile a program that can still crash. Trust refuses it.

AI authors write code faster than any person can review it, so the reviewer
has to be the compiler. In Trust the spec lives in the program, written in the
language. A language model inside the compiler proposes proofs, fixes and
faster code. A small kernel accepts only what it can check. The result is a
compiler that improves your program, not one that only translates it.

## The seed

Everything rests on a small seed. These are the only things taken on faith.

1. **Three axioms.** Lean's standard axioms: propositional extensionality
   (`propext`), quotient soundness (`Quot.sound`) and the axiom of choice
   (`Classical.choice`). Every proof in the system follows from them by rules a
   machine checks.
2. **The Rust model.** A formal definition, written in Lean, of what every Rust
   program means. One half says which programs are valid: types, traits and
   borrows. The other half says what a valid program does: arithmetic and
   overflow, memory and pointers, aliasing, panics, drops and threads. The
   model runs programs, so we can test it. We run rustc's whole test suite and
   millions of generated programs through both the model and rustc, and fix
   every disagreement.
3. **The machine model.** Formal specifications of the Arm and x86 instruction
   sets: what every instruction does to registers and memory.

One small program completes the seed: **the kernel**, the checker that verifies
every proof. It comes from Clean, our implementation of Lean 4, and it is not
taken on faith either. Its first job is to prove itself. The checker is written
in Lean and compiled by Trust, so the program that is proved is the program
that is compiled. We write Lean's type theory down as rules and build a model
of those rules out of sets, and the kernel proves that every statement it
accepts is true in that model, using nothing but the three axioms. The proof
goes one bound on universe levels at a time. No system can prove its own
consistency outright, so the statement for every level at once rests on set
theory.

The checker is small because it does not search. Clean's large, fast kernel
does the searching and hands the checker each answer with the steps that
justify it. The checker trusts none of that. It replays the steps and decides,
so the large kernel can be rewritten freely: a wrong answer is refused. Lean's
own kernel and an independent third checker re-check the checker's proof. Until
the compiler's theorem covers the checker's compiled bytes, those bytes are
covered only by the agreement of the independent checkers, so for now the proved
checker being the one that runs is true by design, not yet in fact
(the proven-core plan, `docs/plans/2026-10-15-proven-core.md`, §2.1).

That is the whole seed. Everything else is proved from it.

## The first theorem: the compiler is correct

The first thing built on the seed is one theorem:

> For every Rust program P that Trust accepts, every behavior of the binary
> Trust produces for P is a behavior the Rust model allows for P.

The machine code does what the source means, and nothing else. It cannot add a
crash, change a result, or touch memory the program never touched. This
theorem is about the compiler, not your program. A correct compiler faithfully
compiles your bug. Proving your program does what you want is a separate
theorem, built on this one.

**It is proved once, pass by pass.** A compiler is a chain of passes: parse,
type check, borrow check, lower, optimize, choose instructions, assign
registers, emit machine code. For each pass we prove one small theorem: if the
input means X, the output means X. Chaining the small theorems gives the big
one. The proof is about the compiler's source and is done once. After that no
compile needs checking: every output is correct because the compiler is.

**It is proved by Trust itself.** The compiler is a Rust program, and Trust
proves Rust programs. So first we prove the verifier, the part of Trust that
turns code into proof obligations, directly against the Rust model. Then we
point the verifier at the compiler's own source.

**It is closed by self-compilation.** The theorem is about source code, but you
run a binary. So the compiler compiles itself. The theorem, applied to the
compiler's own source, says the new compiler binary does exactly what that
source says. The very first binary has to come from somewhere, so that one
compile is checked once, by building it with two independent compilers and
comparing the results. After that the loop is closed.

In 1984 Ken Thompson's Turing Award lecture, *Reflections on Trusting Trust*,
showed that a compiler binary can carry behavior its source does not show, and
that no amount of reading source can rule it out. A compiler that is proved
correct and compiles itself has nowhere to hide it.

Lean gets the same treatment. Lean code compiled to native code is proved to
compute what its definition says. The kernel's checker is such code, so the
theorem that covers the compiler's output covers the checker's bytes too. No
checker that always answers can accept exactly the proofs Lean's rules allow:
checking Lean's types is undecidable, and the procedure that decides when two
terms are equal is not transitive. So the checker is proved to accept only true
statements, and, given the large kernel's steps, to accept every proof that a
stated checking procedure derives.

This is where the two languages meet. Every checker Trust has to trust is
written in Lean, proved, and compiled by Trust. Rust is for the fast producers
whose answers get checked, and for a thin shell around the checkers. At the
end Clean is part of Trust, and Trust verifies and compiles its own source as
Trust plus Lean.

## How proof builds on proof

With the compiler proved, every new program takes the same four steps.

1. **Say what it should do.** Write a spec: `requires` and `ensures` clauses on
   its functions, or a theorem in Lean about what it computes.
2. **Prove the program meets it.** With no annotations, Trust proves the
   program has no undefined behavior, panics, overflows or data races, or shows
   the input that breaks it. Your own spec you prove with Trust's help: the
   solvers do most of it, and you or an AI write the rest in Lean.
3. **Compile it.** The compiler theorem carries the proof from the source to
   the binary. You now hold a theorem about the binary itself.
4. **Use it.** Every program that calls it relies only on its proved spec, and
   never needs to look inside.

This is recursive. Some proved programs are tools: a solver, an optimizer, a
cache, a model checker. Once a tool is proved, its answers are theorems with no
further checking, and it proves the next programs faster. The toolchain itself
is built this way, as a proof tower, each layer proved by the layers below it:

- The kernel proves itself from the three axioms.
- The kernel proves the verifier.
- The verifier proves the compiler.
- The compiler builds a proved solver, ay. From then on the solver's answers
  need no certificate.
- The proved solver and compiler prove the optimizer. From then on every
  optimization is correct by construction.
- They prove the build cache. From then on reusing a stored result is a
  theorem, not a hope.
- They prove ty, the model checker for concurrent systems. From then on a proof
  about a protocol is a theorem about the running program.
- Then every program anyone writes: a parser, a database, an operating system,
  a model's training code.

Each layer adds capability and adds nothing to what must be trusted.

```text
            programs anyone writes      ordinary software, absorbed by proof
                          \                   /
   +-------------------------------------------------------------------+
   | proved tools: the solver (ay), the optimizer, the build cache, ty |
   | the compiler: proved pass by pass, then compiled by itself        |
   | the verifier: proved against the Rust model                       |
   | the kernel: proves itself from the three axioms                   |
   +===================================================================+
   | the seed, the only thing trusted:                                 |
   |   three axioms . the Rust model . the machine model               |
   +-------------------------------------------------------------------+
```

## Specs are part of the program

A proof needs a statement of what is being proved. In Trust that statement is
not a separate document. It is part of the program, written in the language
and checked on every build.

`requires`, `ensures` and `decreases` sit in the function signature, where the
type is. `while` and `loop` carry `invariant` and `decreases`. Mathematics goes
in a `clean { }` block: real Lean, inside a Rust file, that Rust clauses can
cite.

```rust
clean {
    def fee (cents : UInt64) : UInt64 := cents / 50
}

fn platform_fee(cents: u64) -> u64
    ensures result == fee(cents)
    ensures result <= cents
{
    cents / 50
}
```

A program uses as many of three layers as it needs.

1. **The language.** With no spec at all, Trust proves that the program never
   panics, overflows, indexes out of bounds, divides by zero, hits undefined
   behavior in `unsafe` code, races on shared memory or deadlocks. That covers
   its own code and every dependency. Trust stops the build and shows the
   input that triggers each one.
2. **Library contracts.** Every library function carries `requires` and
   `ensures`, so its rules are checked at every call. Build a database query
   from user input, or read an account without checking who is asking, and the
   call does not compile. Injection, broken access control and leaked resources
   become compile errors, like type errors.
3. **Your requirements.** `requires` and `ensures` on your own functions state
   what they promise. A `clean { }` block states anything mathematical as a
   Lean theorem: a pricing formula, a scheduling rule, the meaning of a query.

**Full specs where they pay.** Most programs need only the first two layers and
a few promises. A full functional spec says exactly what a function computes.
It is worth writing in two places: the foundations everything stands on, such
as compilers, solvers, cryptography and operating system kernels, and the hot
spots you want made much faster. There the spec is what licenses the
optimization. It says what must stay the same, so the compiler is free to
change everything else. A function that promises
`ensures is_shortest_path(result, g, a, b)` can have its body replaced by
whatever finds shortest paths fastest on the graphs it actually sees.

**The last version is a spec too.** Every change is checked against the code
before it. Trust searches for inputs where the old and new versions disagree,
and sums up the differences as a few named changes, each with its smallest
example: *JPY amounts now round half to even; 2.5 becomes 2, not 3.* It proves
nothing else changed. This **behavior diff** checks a change even where nobody
wrote a spec.

## An LLM in the compiler loop

Trust puts a language model inside the compiler, with the proof kernel behind
it. The model is creative and untrusted. The kernel accepts only what it can
check. Together they run a loop on every build.

1. **Prove.** The compiler turns the program into proof obligations: every
   index in bounds, every contract met at every call, every `ensures` true.
   Solvers discharge most of them. Where a solver gets stuck, the model
   proposes the missing piece, such as a loop invariant or a lemma, and the
   kernel checks it. A wrong proposal costs a retry.
2. **Fix.** Where an obligation is false, the compiler has the input that
   breaks it. The error names the rule, shows the input and lists the ways to
   fix it. The model applies one and the loop runs again. Errors are written
   for an AI reader first, because an AI is who reads them. A refusal that
   names no fix is a compiler bug.
3. **Make it provable.** When code is too tangled to prove, the model rewrites
   it into code that is provable and does the same thing, and the behavior diff
   confirms nothing changed.
4. **Strengthen.** The model reads the code, its documentation and how it is
   used, and proposes the strongest spec the code supports. Accepted specs go
   into the source as `requires` and `ensures`, so every later change is held
   to them.
5. **Improve.** Once a program is proved, the model proposes faster versions: a
   better algorithm, a better data layout, a loop spread across cores or moved
   to the GPU. Each lands only with a proof that it meets the same spec.
6. **Check every change.** Every edit, from a person, an agent or the compiler
   itself, comes with its behavior diff. The diff goes back to the model that
   made the change, and to a second model acting as reviewer, together with
   what the change was meant to do. A change nobody intended is a bug, caught
   before merge. The diff covers specs too: an agent that weakens an `ensures`
   to get a green build shows exactly which behaviors it just allowed.

This is the original design of Trust: the compiler proves the code, AI infers
the strongest spec, and backpropagation rewrites the program until the proof
goes through. **prove → strengthen → backpropagate → re-prove.** The loop
converges by changing the program or the spec, never by lowering the bar. A
compiler used to be a translator that hoped its input was right. Trust finds
what is wrong, says how to fix it and makes the program faster, and no amount of
persuasion gets it to accept something false.

## Autoformalize to Rust and Lean

Every proof in Trust is about Rust or Lean. Code in any other language enters
by being turned into Rust and Lean, as a service. Then the proof tower needs
formal models of only two languages, Rust and Lean, not one for every source
language.

1. **Translate the code.** Agents translate the program into idiomatic Rust,
   module by module, keeping its structure, names and interfaces so the team
   can still read it.
2. **Formalize the intent.** Documentation, comments, tickets, API schemas and
   tests say what the program is meant to do. Agents turn them into
   `requires`, `ensures` and Lean theorems.
3. **Compile.** Trust reports every bug the old language let through, each as
   a compile error with the input that triggers it and a proposed fix.
4. **Check the translation.** The behavior diff between the original and the
   Rust, run on generated inputs and recorded traffic, lists every difference.
   Each is a translation bug, which the loop fixes, or a bug in the original,
   which the team decides to keep or fix. Where a formal model of the original
   language exists, Trust proves the two versions do the same thing.
5. **Switch over.** The Rust is what runs, so the proofs are about the code in
   production. From then on the team and its agents work in Trust.

Take a checkout service in TypeScript. The TypeScript compiler accepts every
line below. After translation, Trust rejects each one and shows the input.

- `order.items[0].price` reads past the end of an empty cart.
- Money is a floating-point number, so the charged total stops matching the
  receipt.
- `JSON.parse(body) as Order` checks nothing, so an order with no `currency`
  reaches the payment provider as `undefined`.
- `parseInt(qty)` returns `NaN` for `"abc"`, and `NaN` flows into the total.
- A missing `await` on the stock reservation lets a payment through when the
  reservation fails.
- The order lookup never checks that the order belongs to the caller.

None of these is exotic. They are the normal state of a working program. The
hard parts are dynamic features such as `eval` and reflection, and the large
frameworks programs are built on. Each framework gets a proved Rust
counterpart once, shared by everyone who uses it.

## Proof as a service

A team using Trust never has to write Lean or a proof. It connects its
repositories, in any language.

- **Day one: its bugs.** The service autoformalizes the code and returns every
  bug it found, each as a pull request with the triggering input, a fix and a
  test.
- **Every pull request after that.** Each change goes through the compiler
  loop. The review comment is the behavior diff, already checked by a second
  model against what the change was meant to do. A change whose specs all
  prove, and whose behavior diff matches its intent, merges without anyone
  reading the code. Only what a change can reach is re-checked.
- **Fast where it matters.** The team names a slow path. The service writes its
  full spec, the team reads the spec, and the compiler replaces the code with a
  faster version proved to meet it.
- **Certificates.** A certificate names a binary by its hash and lists the
  properties it is proved to have. Auditors and insurers re-check it offline,
  and deploys refuse a binary that does not match.

Checking a proof costs almost nothing. Searching for one is the work. Most of a
program is its dependencies, proved once per version for everyone, so the cost
falls as more programs join.

## Software that consumes software

The tower grows upward with new tools. It also grows outward, by absorbing
software that already exists.

1. **Bring it in.** Rust code compiles with Trust unchanged. Code in any other
   language is autoformalized into Rust and Lean.
2. **Find out what it does.** The compiler loop fixes every place it could fail
   at runtime. Then the program gets a spec: from its authors, from an AI
   reading its documentation and tests, or inferred from how the code is used.
   A wrong spec fails to prove.
3. **Prove it.** From then on, every program that uses it relies on the
   theorem, not on the code.

Each program absorbed makes the next one cheaper. A proved library's spec is
what makes its users provable. Every proof is stored and reused, so nothing is
proved twice. The order follows that leverage: Rust's standard library first,
because everything uses it; then the most-used libraries; then the software
that matters most when it breaks, such as cryptography, parsers, databases and
operating systems; then everything else.

A proof, once checked, is permanent. A later change that breaks it fails to
compile, with the input that breaks it. That is how AI makes lasting progress
on a program too large to hold in its head: as theorems the next step stands
on.

## One program, end to end

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

1. **The spec.** `requires` says what callers must guarantee: the slice is
   sorted. `ensures` says what the function promises: an index it returns holds
   the value, and `None` means the value is nowhere in the slice.
2. **What Trust proves on its own.** Every `v[mid]` is in bounds, because
   `lo <= mid < hi <= v.len()`. The midpoint cannot overflow. The loop ends,
   because `hi - lo` shrinks on every turn.
3. **What Trust proves with help.** The `ensures` needs one fact about the
   loop: the value is not in `v[..lo]` and not in `v[hi..]`. A solver or an AI
   proposes it, and the kernel checks that it holds on entry, holds after every
   turn, and implies the promise when the loop ends.
4. **Compile.** The compiler theorem carries all of this to the machine code.
   On any sorted slice, the binary returns a correct answer and never crashes.
5. **Build on it.** A database index calls `search`. Its own proof, that every
   stored key can be found, uses only the `ensures` of `search`.
6. **Change it.** The compiler loop proposes a faster, branch-free version.
   Trust proves it meets the same spec. Nothing that relies on `search` has to
   be re-proved or re-tested.

## What proven software can do

Once a system is proved, it can take shortcuts no ordinary system can safely
take, because every shortcut comes with a guarantee.

**Speed**

- **Never build or test the same thing twice.** A change proved to leave
  behavior the same rebuilds nothing, re-proves nothing and re-runs no tests
  downstream. Compiled code and proofs are stored by what they mean and
  shared, so a function anyone has compiled before is a download.
- **Optimizations no compiler dares.** Trust deletes checks that can never
  fire, runs loops on every core, moves work to the GPU, changes data layouts
  and replaces a slow algorithm with a fast one across the whole program. Each
  step is proved to give the same answer. Where the code had the wrong
  algorithm, that is 10x to 1000x.
- **Compile to anything.** The same proved program targets a CPU, a GPU,
  WebAssembly or a new chip, and each translation is proved.
- **No safety tax.** Components proved not to interfere need no sandboxes,
  process boundaries or defensive checks between them.

**Change without fear**

- **Merge without reading the diff.** Reviewers read the behavior diff, not ten
  thousand lines.
- **Upgrade anything.** A dependency bump or a language migration comes with a
  proof that nothing changed, or the exact inputs where something did.
- **Patch production live.** A fix proved to change only the broken behavior
  can be swapped into a running system.
- **Refactor for free.** A refactor proved equivalent needs no test run and no
  review.

**Security**

- **Whole classes of attack disappear.** Memory corruption, injection, broken
  access control and data leaks are compile errors.
- **Answer a new vulnerability in minutes.** The proofs say whether your code
  can reach a flawed library function, with the input that does if it can.
- **Run only proved code.** Binaries carry their proofs. An operating system,
  a cloud or an app store can refuse any binary whose proofs do not check.
- **Evidence instead of audits.** Compliance teams and insurers get
  machine-checked certificates instead of questionnaires.

**AI**

- **AI that builds large systems.** Every proof an agent completes is
  permanent, so a fleet of agents can build programs far larger than any model
  can hold in mind, without regressing.
- **A reward that cannot be gamed.** The kernel accepts a proof or it does not.
  Coding models trained on it learn to write code that is right, not code that
  merely passes tests.
- **Specs in, programs out.** A person states what they want. Agents produce
  the program and its proof. The kernel decides.

**The system improves itself**

- **The compiler gets better on its own.** Agents propose faster passes and
  better optimizations for Trust itself. Each lands only with its proof, so the
  compiler improves every day and never becomes less correct.
- **Mathematics runs.** Lean theorems and Rust programs live in one compiler.
  Proved mathematics becomes running code, and running code can be proved with
  all of mathematics.

## Why now

Proving real software has been done, one heroic project at a time. CompCert
proved a C compiler correct. seL4 proved an operating system kernel correct,
at about eleven person-years for under nine thousand lines of C. CakeML proved
an ML compiler correct down to machine code. Each took years of expert proof
for one program, and the next project started from scratch. Proof stayed rare
because it was expensive and it did not compound.

Three things change that.

1. **Solvers do most of the work.** Most facts a real program needs, such as
   an index in bounds or a loop that ends, are proved automatically.
2. **AI writes the rest.** Agents write specs, loop facts and proofs at machine
   speed. The kernel checks every one, so a wrong attempt costs a retry.
3. **Proofs compound.** When every proved program is a building block and
   every proof is reused, each new proof is cheaper than the last.

Together these push the cost of proving a line of code toward the cost of
writing it. When proving is about as cheap as testing, proven software wins.

## What we build first

Most of the pieces exist as working software that is not yet proved. **Trust**
is a Rust compiler with a verifier inside it, contracts in the language, Lean
blocks inside Rust files, and early versions of the loop that strengthens specs
and rewrites code. **Clean** is our implementation of Lean 4, with its own
kernel. **trust-ir** is the shared internal form for both languages, with its
meaning written in Lean. **trust-cg** is our own backend, built to emit a proof
for each function it compiles. **ay** is our SMT solver. **ty** is a model
checker for concurrent systems. The plan puts all of it on the seed, in
dependency order.

1. **The seed.** The kernel proves itself from the three axioms. The Rust
   model is written, runs programs and agrees with rustc across its whole test
   suite. The machine models are in place.
2. **The verifier**, proved correct against the Rust model.
3. **The compiler**, proved pass by pass and then compiled by itself. The same
   for Clean's compiler for Lean.
4. **The first proved tools**: the solver, the optimizer, the build cache and
   the model checker.
5. **The first absorption**: Rust's standard library, then the most-used
   libraries.
6. **Open the doors**: the compiler loop and autoformalization for every
   language, agents absorbing software at scale, and anyone building on the
   tower.

The first milestone is small and decisive: a kernel that proves itself, and a
Rust model that agrees with rustc.

## Architecture

This is the target design. Today LLVM is still the default backend, and MIR is
still on every production path.

```text
         Rust source                           Lean source
   (specs in the signature)          (clean { } islands, .lean files)
              |                                     |
            THIR                    Clean parser, elaborator, kernel
              |                                     |
              +-------------> trust-ir <------------+
                      one module for both languages,
                      its meaning written in Lean
                       /                          \
            proof obligations                   the program
                    |                                |
               trust-router                       trust-cg
     ay | trust-mc | trust-vc | ty | clean           |
                    |                                |
          kernel re-check: kcheck,            machine code, with a
          a proved Lean checker               proof for each function
          (it decides every proof)
```

- **trust-ir** is the one internal form both languages produce: Rust from THIR,
  rustc's typed syntax tree, and Lean from Clean. Code generation and
  verification read trust-ir and nothing else, so the bytes that ship come from
  the object that was proved.
- **trust-cg** is Trust's own backend: instruction selection, register
  allocation, encoders and object writers. It decodes the bytes it emits and
  proves they mean what the trust-ir means.
- **Users pick properties, not provers.** `trust-router` sends each obligation
  to the engine best at it:
  - **ay**, a fast solver, for most obligations;
  - **trust-mc**, a model checker: it follows every path through a loop,
    proves the loop ends, and finds the failing input when there is one;
  - **trust-vc**, proofs guided by short hints in the code;
  - **ty**, properties of concurrent systems over time, such as no deadlock
    and no data race;
  - **clean**, Lean proofs for the mathematics.
- **The kernel's checker decides.** Engines are fast and sometimes wrong, so
  their output is untrusted. A result is `Certified` only when the kernel's
  checker re-checks it. In this design that checker is `kcheck`, written in Lean,
  proved against a model built from sets and compiled by Trust; Clean's large
  kernel only proposes the steps it replays. Today the Clean kernel decides,
  through its fenced entry.
- **MIR and LLVM leave production.** MIR, rustc's own internal form, and LLVM
  stay as test oracles, run side by side with trust-ir and trust-cg to catch
  disagreements. They ship no bytes. LLVM leaves one target at a time, as
  trust-cg covers each.

## Design decisions

- **Verification lives in the compiler, not around it.** A tool outside the
  compiler cannot see what the compiler knows, and cannot stop the build.
- **Specs are grammar.** The `#[trust::…]` attribute spellings desugar into the
  same grammar, so a spec has one meaning.
- **Lean enters as a parser island.** `clean { }` is a form Rust rejects, so no
  valid Rust program changes meaning. Clean's own parser reads the body, and
  the declarations the kernel admits become items the Rust code can call and
  cite.
- **trust-ir is never worse than MIR.** MIR leaves a path only when trust-ir is
  at least as good there on every axis: what compiles, compile time, code speed
  and size, memory, diagnostics, debug information and what can be verified.
- **Track upstream Rust.** Trust merges `rust-lang/rust` instead of vendoring
  it. Every edit to an upstream file is marked `// Trust:`. Compiling every
  valid Rust program identically is a release gate.
- **Engines are separate repositories behind one router.** Each has its own
  scope and cadence. The router decides which runs; the user does not. Clean is
  the exception at the end: the kernel's checker and the Lean compiler are part
  of Trust itself, so Clean's tree merges into Trust once both check into one
  Lean environment.
- **A refusal carries the fix.** When the compiler enforces a rule, it says
  which rule, why this program broke it and what the options are. The lever is
  compiler capability, never user restriction.
- **Only Rust and Lean carry proof authority.** Other languages enter by
  autoformalization. Their source, annotations and inferred intent are never
  proof evidence on their own.

[README.md](README.md) covers installing and using Trust.
