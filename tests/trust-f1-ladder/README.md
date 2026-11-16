# The F1 ladder

A fixed corpus of ordinary Rust for one measurement: how much of it compiles on the production
target lane, Rust → THIR → trust-ir → trust-cg (`Compiler::compile`), and prints what the LLVM
build of the same source prints. `scripts/trust_f1_ladder.py` runs it; its docstring defines the
columns, modes and result words. The current counts are in
`docs/STATUS.md`, "Compile path".

- `programs/` — 20 rungs of increasing difficulty: arithmetic, branches, a loop, structs by
  value and by reference, an enum and `match`, array indexing, overflow, a generic function,
  static trait dispatch, a closure, `dyn`, `Box`, `Vec`, `String`/`format!`, `println!`, an
  iterator chain, `Result` and `?`, slices and `str`, and a small tokenizer plus n-queens.
- `micro/` — 28 rungs with one construct each, to locate the frontier.
- `lean/` — an island-only subject, Rust calling Lean, and Lean calling a private Rust
  function. F1 success also requires the compiler’s MIR reach counters to report zero
  codegen, inventory and recorder reads. Missing counters fail the measurement. The
  LLVM-built driver must also report its inventory and compile no `rung::` body
  from metadata; the subject must supply its machine code.
- `driver.rs` — the executable every rung is linked into.

Each Rust rung is a library exporting `#[no_mangle] pub extern "C" fn rung(x: u64) -> u64`, while the island-only rung exposes a Lean `rung` to the same driver. This library
shape is used because the builtin trust-cg backend emits rlibs at `-Cpanic=abort` only. When it can emit an
executable, the rungs become programs with their own `main` and this sentence is deleted.

Rules for the corpus:

- A rung is never edited to make a lane accept it. A refusal is the measurement.
- A rung's result must be a pure function of its `u64` input, so the LLVM build is an oracle.
- Add rungs at the end of a set; the counts in STATUS.md name the totals.
