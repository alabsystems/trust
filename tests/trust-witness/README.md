# trust-witness replay regressions

Durable regression coverage for the typeck-moonshot warm-replay lane
(`-Ztrust-witness=mint:<dir>` / `-Ztrust-witness=replay:<dir>`, crate `crates/trust-witness`).

The mechanism mints a per-root witness of `TypeckResults` on a cold compile and,
on a warm compile, decodes + re-interns + runs the linear checker and replays
instead of re-inferring. It is fail-safe (any miss/decode/check failure falls
back to real typeck) and checked-not-trusted (the checker is the mandatory
authority). These fixtures pin the invariants a regression would break.

## Run

```bash
./x.py build --stage 2
TRUST_SEED_STAIRCASE=1 python3 tests/trust-witness/replay_regression.py
```

Set `TRUST_WITNESS_TRUSTC=/path/to/stage2/bin/trustc` to exercise a staged
compiler from another clean worktree without copying build artifacts.

## Fixtures (one per confirmed 2026-07-22 audit finding + a positive)

| fixture | class | contract |
|---|---|---|
| `pos_method.rs`     | positive (Follow-on 2) | root-body monomorphic method/operator picks ACCEPT; rmeta+obj byte-identical to no-flag |
| `extern_c_fnptr.rs` | rank 1 (soundness) | non-Rust-ABI fn-ptr type is escaped at encode → MISS, not a wrong-ABI ACCEPT / equate ICE |
| `offset_of.rs`      | rank 3 (fail-safe) | `offset_of!` root excluded by `mintable()` → MISS, not a `None.unwrap()` ICE in the child const |
| `child_pick.rs`     | rank 2 (soundness) | a pick inside `const { .. }` (a child body the checker never walks) → rejected by the coverage guard |
| `child_plain.rs`    | rank 2 follow-up (soundness) | a child body without a pick is also rejected; every child-owned `TypeckResults` map is unchecked by the one-body checker |
| `transmute.rs`      | v4 completeness (soundness) | nonempty `transmutes_to_check` blocks minting because the decoder cannot reconstruct that downstream-consumed list |
| `warning_unreachable.rs` | diagnostic parity | a root that emits `unreachable_code` is mint-excluded, so replay cold-typechecks it and preserves stderr |
| `expect_unreachable.rs` | diagnostic parity | a root that silently fulfills `#[expect(unreachable_code)]` is mint-excluded, so replay cold-typechecks it and preserves fulfilled-expectation state |
| `borrow_bad.rs`     | fail-safe | a borrow-invalid crate still reports the identical error under replay |

The universal assertion is same-answers: warm replay's normalized stderr,
emitted `rmeta`+`obj`, and exit code match a no-flag build, so a suppressed
diagnostic, crash, or silent codegen divergence all fail the test.

A `tests/run-make/` port (multi-invocation `rmake.rs`) is the intended CI home;
this script is the portable interim driver (see the audit's rank-6 item).
