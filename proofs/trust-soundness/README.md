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

The corpus currently contains 34 proof files. The ouroboros gate must
kernel-check all 34 with the pinned `clean` before a current-checkout pass is
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

`quantified_projection_certificate.lean` is the first non-circular semantic
slice for AY's quantified-SAT projection certificate. It proves total projection
rewrite fidelity, ordinary and conditional premise substitution, Boolean/ITE
reduction, and the accepted-certificate-to-model composition theorem in the
pinned Clean kernel. Its modeled authority layer additionally requires three
dependent inputs for the same exact subject before SAT can be minted: checked
semantic evidence, a positive free-UF binding at the same stable declaration ID
and full signature/source stamp/frozen ordered roots, and an authored plain-hard
`check-sat` permit. That permit also binds a separate public query-authority
epoch, scope depth, and term count. Executable theorems reject missing or stale
bindings, replacement IDs or signatures, every non-free kind (including
datatype constructor/selector/tester), changed roots/depth/count/epochs,
assumptions, soft assertions, objectives, empty `check-sat-assuming`, and
generic/internal dispatches. Semantic evidence for another subject,
stopped/resource-limited outcomes, and literal `true` values cannot be
substituted into the authority constructor.

The semantic/authority model now uses an exact nonempty finite multi-head map,
unique by stable declaration reference; each entry binds declaration/signature,
application-pattern identity, selector, and argument function. The closed green
witness contains two heads. This still does **not** prove that AY's live Rust
map construction, iteration, or consumption refines the modeled functions.

It does **not** yet establish that AY's live Rust AST traversal, identity
allocation, checker, or dispatch code faithfully implements that model; that
source/MIR conformance remains a separately gated obligation. The semantic and
authority red-control fragments live outside the green corpus in
`proofs/trust-soundness-negative/`. Run
`scripts/check_ay_projection_certificate.sh`: it kernel-checks the 264 green
declarations, appends and separately rejects the one semantic declaration, then
checks each of seven authority fragments independently and requires all 43
named impossible constructors to appear in structured failure feedback, with
exact counts and no unknown-name diagnostics.

## Workflow

Develop proofs against a full `clean` checkout (e.g. `~/clean`), then copy the `.lean` file here and
confirm the gate stays green:

```
cargo test -p trust-integration-tests --test trust_soundness_ouroboros_gate -- --nocapture
```
