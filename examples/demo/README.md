# Trust Demo: Catching Bugs and Tracking Proof Progress

This demo walks through Trust's core verification capabilities in six steps.
It shows how Trust catches real bugs with counterexamples, proves fixed code
safe, runs standalone self-analysis over one Trust crate, and generates proof
reports.

**Time:** ~5 minutes
**Prerequisites:** Build Trust, put the Trust sysroot `bin` directory on `PATH`,
and run the examples through `targo trust ...`. Use `--standalone` only when
you explicitly want source analysis instead of compiler-backed verification.

---

## Step 1: The Buggy Program

Open `buggy_binary_search.rs`. This is a textbook binary search with two
classic bugs that have caused real-world failures (including in Java's
`Arrays.binarySearch` -- see Bloch 2006):

```rust
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;   // BUG: underflows on empty array

    while low <= high {
        let mid = (low + high) / 2;         // BUG: overflows for large indices
        // ...
    }
    None
}
```

**Bug 1:** `arr.len() - 1` underflows when the array is empty (`0_usize - 1` wraps to `usize::MAX`).

**Bug 2:** `(low + high) / 2` overflows when `low + high > usize::MAX`.

Both bugs are silent in release mode (wrapping arithmetic) and panic only in
debug mode. Standard Rust compilation catches neither at compile time.

## Step 2: Trust Catches the Bugs

Run Trust on the buggy program:

```bash
targo trust check examples/demo/buggy_binary_search.rs
```

Trust analyzes every arithmetic operation, generates verification conditions,
and dispatches them to ay (SMT solver). Output:

```
note: Trust [overflow:sub]: arithmetic overflow (Sub) -- FAILED (ay-smtlib, 50ms)
  counterexample: arr.len() = 0  (empty array triggers underflow)

note: Trust [overflow:add]: arithmetic overflow (Add) -- FAILED (ay-smtlib, 12ms)
  counterexample: low = 9223372036854775807, high = 9223372036854775807

=== Trust Verification Report ===
Summary: 0 proved, 2 failed, 0 unknown (2 total)
Result: FAIL
```

Trust found both bugs and produced concrete counterexamples -- values that
trigger each overflow. No tests needed. No fuzzing. Mathematical proof.

## Step 3: The Fixed Program

Open `safe_binary_search.rs`. Three fixes eliminate all bugs:

```rust
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    if arr.is_empty() { return None; }          // FIX 1: empty guard

    let mut low: usize = 0;
    let mut high: usize = arr.len() - 1;        // safe: len >= 1

    while low <= high {
        let mid = low + (high - low) / 2;       // FIX 2: safe midpoint
        // ...
        match mid.checked_sub(1) {               // FIX 3: checked decrement
            Some(new_high) => high = new_high,
            None => break,
        }
    }
    None
}
```

## Step 4: Trust Re-checks the Fixed Program

Run Trust on the fixed program:

```bash
targo trust check examples/demo/safe_binary_search.rs
```

On the current checked toolchain, this example is still a frontier case rather
than a clean PASS example. The fixed source removes the obvious bugs, but the
prover still leaves open obligations in this binary-search workflow.

That makes the file useful for:

- exercising a realistic before/after case study
- generating proof reports
- tracking future improvements in the prover frontier

If you want a small example that currently passes end to end, start with one of:

- `../verify_div_zero_safe.rs`
- `../verify_cast_overflow_safe.rs`
- `../verify_postcondition_safe.rs`

Representative output:

```
note: Trust [overflow:add]: arithmetic overflow (Add) -- FAILED (ay-smtlib, 0ms)
note: Trust [overflow:sub]: arithmetic overflow (Sub) -- FAILED (ay-smtlib, 0ms)
note: Trust [slice]: slice bounds check -- RUNTIME-CHECKED (ay-incremental, 0ms)

=== Trust Verification Report ===
Summary: 0 proved, 7 failed, 2 runtime-checked, 0 inconclusive (9 total)
Result: FAIL
```

This is a good example of the distinction between “source fixed” and “currently
proved by the checked toolchain”.

## Step 5: Standalone Self-Analysis

Trust can analyze one of its own crates. Run standalone analysis on the trust-types
crate (the core type definitions used throughout the verification pipeline):

```bash
targo trust check --standalone -p trust-types
```

This demonstrates that Trust can analyze one of its own crates with the public
standalone workflow. It is useful as a self-hosting smoke test, but it is not a
whole-crate semantic proof of Trust itself.

## Step 6: Proof Report

Generate an HTML proof report with a visual dashboard:

```bash
targo trust check examples/demo/safe_binary_search.rs \
    --report-dir examples/demo/report
```

This writes three files to `examples/demo/report/`:
- `report.json` -- machine-readable verification results
- `report.html` -- visual dashboard with proof status, timing, and solver info
- `report.ndjson` -- newline-delimited JSON for streaming/CI integration

Open `report.html` in a browser to see the proof dashboard.

`--report-dir` is part of the compiler-backed workflow. Standalone mode is
source analysis and does not currently emit the same artifact set.

---

## Maintainer Demo Evidence

The normal demo interface is the `targo trust ...` commands above. Collect
demo evidence by running those Trust-owned commands directly and preserving the
terminal transcript with the repo commit and toolchain paths.

## Key Concepts

| Concept | What It Means |
|---------|---------------|
| **Verification Condition (VC)** | A logical formula that must hold for a property to be safe. Trust generates VCs for every arithmetic op, array access, and user annotation. |
| **PROVED** | ay found a mathematical proof that no input violates the VC. |
| **FAILED + counterexample** | ay found a concrete input that violates the VC. This is a real bug. |
| **ay** | The primary SMT solver in the dMATH tool suite. Handles ~90% of obligations. |
| **Standalone mode** | Source-level analysis without the full compiler. Useful for quick checks. |

## What Trust Catches Today

- Integer overflow and underflow (signed and unsigned)
- Division by zero and remainder by zero
- Array/slice index out of bounds
- Unreachable code assertions
- User-specified pre/postconditions (`#[requires(...)]`, `#[ensures(...)]`)

As of the 2026-06-01 audit, the stage1 compiler-backed `examples/verify_*.rs`
gate catches these single-file cases and passes 32/32. Broader crates can still
surface skipped, unsupported, runtime-checked, unknown, or empty proof rows.

## Further Reading

- `VISION.md` -- full design document (three big ideas, proof levels, milestones)
- `examples/` -- more verification examples (overflow, division, bounds, etc.)
- `crates/trust-report/` -- proof report generation
- `targo-trust/` -- the `targo trust` verifier implementation
