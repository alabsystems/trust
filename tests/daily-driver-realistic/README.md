# Realistic multi-function programs

The daily-driver bench is 71 single-function programs, most of them one line.
That measures whether a construct lowers, not whether the toolchain is a daily
driver, and the number has been read as if it measured the second.

These six are ordinary multi-function Rust: a struct with an inherent impl and a
bounded loop, a `checked_*` fold over an enum, a `&str` line parser, a `dyn Trait`
sum, a `HashMap` word counter, and a `Result`-returning validator.

Measured 2026-09-18 on stage-1 `1.99.0-dev (d32480619)`, default policy, binary
sha256 identical before and after:

    bench, 71 one-liners ............ 64 verified
    these, 6 programs ...............  2 verified

Run them with the same compiler the bench uses:

    for f in tests/daily-driver-realistic/p*.rs; do
      build/host/stage1/bin/trustc --crate-type=lib --edition 2024 \
        --out-dir "$(mktemp -d)" "$f" >/dev/null 2>&1 \
        && echo "PASS $f" || echo "fail $f"
    done

`p5.rs` is a FALSE REFUTATION and the reason this directory exists: the counter
increment in the word-count loop is reported `[overflow:add] FAILED` with the
counterexample setting it to `usize::MAX`, which a local map filled by counting
the words of one `&str` cannot reach. The value was READ BACK from a container
the analysis does not model, so the load havocs to full range. The same shape
appears with a `Vec` accumulator or a counter behind a method.

Findings and the full argument: `reports/2026-09-18-the-one-liner-bench-flatters-the-toolchain.md`.

## The derive finding

`derive_debug_alone.rs` is two lines and does not verify. `derive_hash_alone.rs`
is the same for `Hash`. `derive_others_alone.rs` carries
`Clone, Copy, PartialEq, Eq, Default` together and verifies, and a bare struct
with no derive verifies, so the pair is `Debug` and `Hash` specifically.

Both generated bodies call a method on a sink the CALLER chose: `Debug::fmt`
writes through the `&mut dyn fmt::Write` in its `Formatter`, and `Hash::hash`
calls `Hasher::write_*` on a generic `H`. The refusal is the same root as the
bench's `fmt/m3` and `fmt/m4`, and re-admitting it is an owner decision that has
been made and retired once already.

`p6.rs` in this directory fails ONLY because of its `#[derive(Debug)]`. Delete
the derive and it verifies. Read any pass rate on `Debug`-deriving code with that
in mind.

Argument and full table: `reports/2026-09-18-derive-debug-blocks-every-crate.md`.

## The loop-accumulator class (added 2026-09-18)

    loop_accumulator_minimal_witness.rs   MUST FAIL -- u64 counter, 3 iterations
    loop_accumulator_constant_bound.rs    MUST FAIL -- second counter, const bound
    loop_induction_variable_passes.rs     passes -- the control

    pub fn f() -> u64 {
        let mut c = 0u64; let mut i = 0u64;
        while i < 3 { c += 1; i += 1; }
        c
    }                                     // [overflow:add] FAILED

Three iterations. `c` reaches 3. Refuted.

The analysis bounds the loop's INDUCTION VARIABLE, because the loop condition
mentions it. Any OTHER loop-carried variable gets no invariant, so its arithmetic
is refuted, and a small literal trip count does not help. `wrapping_add` and
`saturating_add` pass only because they emit no overflow obligation.

NOT in this class: `for x in xs { s += *x; }` is refuted CORRECTLY -- summing
arbitrary u32 really can overflow.

This corrects two earlier diagnoses in this directory's history: the HashMap
counter failure is NOT about reading back from an opaque container (no container
is needed), and ctrl/c5 is NOT about constant-vs-variable bounds (a constant bound
fails too). Both are this one class.

Argument: `reports/2026-09-18-only-the-induction-variable-gets-a-bound.md`.

## Running all of these

    scripts/daily_driver_probes.sh

Every row encodes its expected outcome, including the ones expected to FAIL. A
must-fail probe that starts PASSING is as much a divergence as a passing one that
breaks: `derive_debug_alone` failing is a measured policy consequence, and
`false_theorem_must_be_rejected` passing would mean the Clean kernel had stopped
refusing a false proof. The script is red in both directions on purpose, and its
own failure path was verified by flipping one expectation.

A divergence is not automatically a regression — it may be a fix. Re-read the
row's report under `reports/2026-09-18-*` before editing an expectation, and move
it only with the measurement that justifies it.

## Guard rails for the trip-count refinement

    loop_accumulator_correct_refusal_unbounded_addend.rs   MUST STAY refuted
    loop_accumulator_correct_refusal_unbounded_n.rs        MUST STAY refuted

These exist so a future trip-count refinement cannot pass by over-firing. A trip
count bounds how MANY additions happen, not how large each addend is, so summing
arbitrary `u32` values must stay refuted. And an unconstrained `n` gives no finite
trip count at all, so `while i < n { c += 1; i += 1 }` must stay refuted while the
`n.min(10)` sibling must become provable. A refinement that cannot tell those two
apart is unsound.

Specification, with seven traps that make a naive version unsound:
`reports/2026-09-18-trip-count-bound-spec.md`.

## `checked_add` in a helper (added 2026-09-18)

    checked_add_helper_poisons_caller.rs   MUST FAIL
    saturating_add_helper_is_fine.rs       passes -- the contrast

    pub fn g(a: i32, b: i32) -> Option<i32> { a.checked_add(b) }
    pub fn f(a: i32, b: i32) -> Option<i32> { g(a, b) }

Two functions, no loop, no unsafe, no user types. `g` alone compiles with
warnings: one obligation, never proved, retained as a runtime check. That is
tolerated in `g` and FATAL in anything that calls `g`.

`saturating_add` emits no such row and `wrapping_add` proves its row, so among the
three operations the overflow diagnostic recommends, `checked_*` is the one that
leaves the unproved row. Used INLINE it is fine; the call boundary is what makes
it fatal.

This is what `p2.rs` fails on. Argument, including four wrong guesses that
preceded the bisect: `reports/2026-09-18-checked-add-poisons-its-callers.md`.

## Open dispatch (added 2026-09-18) — the largest single boundary

    opendispatch_trait_dyn_single.rs        MUST FAIL -- s.area() via &dyn Shape
    opendispatch_generic_static.rs          conditional -- s.area() via <T: Shape>
                                            (OD-1 instance hypothesis since
                                            2026-10-04; certify must refuse)
    opendispatch_closure_call.rs            MUST FAIL -- g(x) via impl Fn
    opendispatch_bound_unused_is_fine.rs    passes    -- the control

**Calling a method whose body the verifier cannot pin is fail-closed.** Generics
are fine, trait bounds are fine, declaring any of it is fine. INVOKING through it
is not. A crate-private trait with exactly one impl fails the same way, so no
closed-world devirtualization is attempted.

NOT A DEFECT. The rule is stated in the compiler's own note: the default policy
tolerates only a sysroot callee at foundational types, because anything else "may
dispatch into a user body whose panic this row does not cover". A generic function
is verified once against every `T` a downstream crate might supply.

It UNIFIES three separately-filed findings: `p4`, the bench's `fmt/m3` and
`fmt/m4`, and `#[derive(Debug)]` blocking a crate -- the derive reaches the same
`dyn Write` dispatch from generated code. Two of the four realistic failures are
this one rule, so "2 of 6" is largely a measurement of open dispatch.

Argument: `reports/2026-09-18-open-dispatch-is-the-boundary.md`.

### Which `checked_*` are affected, and what locates it

    checked_add / checked_sub / checked_mul   fail, unsupported=1
    checked_div / checked_rem / checked_neg   pass
    overflowing_add                           pass  <- the locating contrast
    slice::get                                pass

The row's status is `unsupported`, not `unknown`: a model the native lane does not
have, rather than a solver that gave up. The three that fail are exactly those std
implements over the `*_with_overflow` intrinsics; the others use explicit
comparisons.

`overflowing_add_helper_is_fine.rs` is the row that locates it. Same intrinsic,
passes, differing only in returning `(i32, bool)` instead of branching on the flag
to build an `Option`. So what is unsupported is the BRANCH that turns the overflow
flag into `Some`/`None`, not the intrinsic.
