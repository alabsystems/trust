# Canonical carrier mutation controls

`run_adversarial.py` runs nine intended importer refusals through the official
compiler's explicit `Compiler::compile` and strict output path. It requires a
completed matching SDK, its immutable source commit/build receipt and coherent
private metadata/native libraries. It starts no compiler/std build.

The embedded Rustc observer only reads actual canonical producer entries and
actual Rust owner/nominal identities. `rustc_driver::run_compiler` has
`EmbeddedNoOfficialEvidence` authority; its analysis/LLVM output is never counted
as canonical F1 admission. The runner copies the actual producer rlib and replaces
one exact opaque entry occurrence, preserving its length and every byte outside
that range. The official `stage1/bin/trustc` consumes each owned copy. There is no
query override, test-only production option, validator change or weaker-policy
retry. The original rlib and SDK remain unchanged.

| Mutation | Required importer result |
| --- | --- |
| Stale complete-envelope digest | Named digest refusal |
| Rehashed binding to another actual same-signature Rust owner | Named binding refusal |
| Missing or duplicate retained callee ledger row | Named retained-evidence refusal |
| Ledger or source-call identity drift against the other side | `effect-not-conserved`, `NotConserved(Call)` |
| IR call replaced by a typed copy while its source-call fact remains | `effect-not-conserved`, `NotConserved(Call)` |
| Actual nested nominal Marker key replaced by an actual function key | Named actual ADT-kind refusal |
| Actual nested nominal key replaced by a loaded-crate absent hash | Named actual identity-lookup refusal |

The nested cases change the call census and ledger together, retaining their
agreement so recovery must inspect actual Rust metadata. Their unmodified
reference still refuses level S/6.6; no generic positive is manufactured.
`-Zshare-generics=no` requests local instantiation so an externally shared generic
cannot bypass that reference condition. The ordinary R control must actually
ship through the compiler lane, disclose two R bodies and carry a kernel-closed
call-refinement certificate bound to its shipped object's SHA256.

Changing an evidence row's size also deliberately changes one debug filename to
balance the complete frame length. The old/new images, exact adjustment, complete
digests and changed rlib offsets are retained. The subject has no panic sites;
the filename change does not erase a panic location. If exact same-length unique
replacement is impossible, the run fails instead of patching Rust metadata's
lengths or lazy offsets.

The source matcher intentionally ignores extra IR effects. A separate
`census_call_omitted_observe` run removes a source-call census row while retaining
the IR call and ledger, and records both retained-checker and canonical codegen
outcomes. This is an open limitation, never a required-negative pass or a claim
that arbitrary census deletions are detected. The synthetic standalone
`rmeta_census_asymmetry.rs` reproduces that checker behavior without TCX; it grants
no Rust-source, admission or proof evidence.

Prepare without executing:

```sh
python3 tests/run-make/trust-cg-f1-upstream-entry/adversarial/run_adversarial.py \
  --plan --out /absolute/fresh-plan
```

With Root's completed frozen SDK:

```sh
build-slot -- python3 tests/run-make/trust-cg-f1-upstream-entry/adversarial/run_adversarial.py \
  --out /absolute/fresh-run --sdk-root /absolute/build/host \
  --compiler-source /absolute/frozen-source --compiler-commit FULL_COMMIT \
  --build-receipt /absolute/immutable-build-receipt.json \
  --private-deps /absolute/stamp-selected-deps \
  --private-host-deps /absolute/stamp-selected-host-deps
```

Every failure and output remains in the owned run directory. A failed unmodified
control does not suppress the intended negative cases. Existing handoff/native
transport and compiler residue refusals remain in force. These controls do not
establish full 6.3, source refinement, S admission, NoUB, R8 or G1–G8.
