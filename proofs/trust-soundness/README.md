# Trust soundness proofs (the apex corpus)

Machine-checked proofs, in `clean` (Trust's CIC kernel / Lean-successor), that Trust's
verification **discharge encoding is sound** — the `realPanics(f) ⊆ models(P_f)` contract and its
per-obligation-class arms. This is the formal core of the apex ("verify the verifier"): turning the
false-proofs found by hand into a class that cannot exist by construction.

## Why these live in Trust (not only in the `clean` repo)

They are *Trust's* soundness proofs. Keeping the canonical copy here makes them:
- **reproducible from a Trust checkout** (no dependency on a separate `~/clean` working clone), and
- **re-verified on every `cargo test`** by the ouroboros gate
  (`crates/trust-integration-tests/tests/trust_soundness_ouroboros_gate.rs`), which shells out to the
  `clean` binary Trust builds from the **pinned** `first-party/clean` submodule.

The corpus currently contains 33 proof files. The ouroboros gate must
kernel-check all 33 with the pinned `clean` before a current-checkout pass is
cited; the file count alone is not proof evidence. This decouples the proofs
from clean's fast-moving math-library churn — no submodule bump is required to
keep a passing gate green. (Advancing the `first-party/clean` pin is a separate,
owner-managed decision.)

## What is and is NOT established (read before citing)

- **Established:** the contract (`whole_program_contract.lean`), per-class soundness arms
  (arithmetic / shift / div / bounds / neg / assert / calls / recursion / control-flow), the
  declaration-marker relaxation soundness (`declaration_marker_relaxation.lean`), and the first
  **UnsupportedMir exhaustiveness** brick. Several arms carry fidelity links to the literal
  `ay_bindings::Expr` the encoder emits (`expr_obligation_semantics.lean`, `memory_bounds_obligation.lean`).
- **NOT yet established (the open frontier):** full **encoding-fidelity exhaustiveness** — a proof
  that the real encoder's MIR→VcKind dispatch image is covered by `P ∪ F` for *every* construct. The
  per-class proofs are over a model; closing the model↔real-encoder gap end-to-end on each class, and
  the dispatch-coverage meta-theorem, are the remaining work. See `reports/apex-soundness-roadmap.md`.

## Workflow

Develop proofs against a full `clean` checkout (e.g. `~/clean`), then copy the `.lean` file here and
confirm the gate stays green:

```
cargo test -p trust-integration-tests --test trust_soundness_ouroboros_gate -- --nocapture
```
