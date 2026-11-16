# Actual Rust-callee IR value mathematics

This fixture consumes the unchanged `u64::wrapping_add` metadata module captured
by `../source_word64_addition.rs` while analyzing the original Lean-to-Rust ladder
subject. It constructs no Module, rewrites no instruction and changes no calling
convention. The full input must validate and reserialize exactly. Its only result
is a kernel-checked returned-value equation in the existing Nat denotation:
for every pair of inputs, the reflected IR result is their sum modulo 2^64.

This is **not Rust source TV**. It proves no source/model correspondence, Rust
entry or physical ABI, world preservation, NoUB, machine bytes or compiler
admission. It creates no gate token, certificate binding or proof obligation.
The original Rust body and the linked caller still need their own evidence.

Materialize `Cargo.toml.in` in an owned external directory by replacing
`@TRUST_ROOT@` with the actual source root, and copy this `Cargo.lock` there.
Keep one source-built Clean/IR graph; no private SDK extern is imported into it.
Under the ordinary machine admission and original SDK/input leases, select:

- `TRUST_RUST_CALLEE_CAPTURES`: the 19-case output of the actual compiler harness;
- `TRUST_RUST_CALLEE_MATH_OUT`: a fresh, nonexistent owned evidence directory.

Run the two phases in separate processes with genuine Targo. Both use
`--all-targets`, the materialized `--manifest-path` and the locked graph:

```sh
targo --unverified test --offline --locked --all-targets --manifest-path <owned>/Cargo.toml tests::actual_metadata_word64_value_equation_checked_and_retained -- --exact
TRUST_RUST_CALLEE_FORBID_PRODUCER=1 targo --unverified test --offline --locked --all-targets --manifest-path <owned>/Cargo.toml tests::fresh_actual_metadata_word64_replay_refuses_real_word32_module -- --exact
```

The first phase checks the universal equation, audits every proof dependency
for empty axiom/foundational-axiom/trust-marker sets, rejects a duplicated-operand
claim, and retains the term. The fresh reader decodes that retained term with
resource limits, independently reconstructs the expected goal, checks/audits it,
and gets an actual kernel TypeMismatch against a different valid `u32` module
captured by the same compiler. It never calls the proof producer. Retain input
and proof hashes across the two phases; neither a zero exit with zero tests nor
a copied subject/claim is qualification. Targo's unverified lane makes no proof
claim; the explicit Clean kernel checks establish this mathematical result only.
