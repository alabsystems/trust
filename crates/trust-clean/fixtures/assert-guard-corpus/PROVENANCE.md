# assert-guard-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Trust: assert-guard soundness. Frontier:
`reports/real-code-coverage-frontier-2026-07-04.md`.

## Empirical finding (the honest headline)

The stated gap — "`bounded_double` (`assert!(x < K); x + x`) DECLINES 0/1
because its `x + x` carries its OWN overflow `Assert`" — is **already closed at
HEAD**. The straight-line-return recognizer (`straight_line_ir_body`, `prove.rs`)
is **control-flow-BLIND**: it takes the UNIQUE `_0 := <rvalue>` statement
anywhere in the body. For all three positive controls that single `_0` write IS
the happy-path return, so the leading `assert!` `SwitchInt`-to-panic guard and
the arithmetic's own overflow `Assert` are simply skipped (they carry no
`_0 :=`). This is SOUND precisely because MIR guarantees `_0` is initialized
before every `Return`, so a body with exactly ONE write to `_0` has that write
dominate the return — the value is unambiguous regardless of the intervening
(guard) control flow. No divergence-chain navigation is needed.

## What this increment actually changes — a latent soundness fix

That same control-flow blindness had a **latent unsoundness**: `_0` can also be
written by a `Terminator::Call`'s `dest` (a call-return branch arm), which is
NOT a `Statement::Assign` and is therefore INVISIBLE to the statement scan. A
branch `if c { x } else { helper(x) }` whose else arm writes `_0` via the CALL
terminator was seen as a SINGLE statement write (`_0 := x` in the then arm) and
would have been FALSELY certified as `return x`. This increment adds a
fail-closed guard (`ret_written_via_call` in `straight_line_ir_body`): DECLINE if
`_0` is written by any `Terminator::Call` `dest`. The `weird_guard` negative
control below has REAL teeth — `assert_guard_latent_unsoundness_is_real` pins
that it false-certified before the guard.

## Dumps

All SEVEN dumps are REAL, UNMODIFIED `trustc` MIR — never hand-transcribed —
originally compiled by the then-current `regenerate.sh` from `SOURCE.rs`
(positive controls) and `NEG_SOURCE.rs` (negative controls). Historical
invocation (recorded verbatim for provenance, not as a current recipe):

```
build/host/stage2/bin/trustc -Ztrust-policy=advisory \
  -Ztrust-dump=mir-only:<dir> --crate-type lib \
  -Zcontract-checks=yes SOURCE.rs -o <out>.rlib
```

That inherited exec-projection flag is now retired for Trust-active
compilations. The live `regenerate.sh` intentionally omits it; these sources
carry no upstream contract attributes, so it did not change their bodies.

### Positive controls (`SOURCE.rs`) — all certify fully-faithful, trust-ir-primary

| fixture | shape | blocks | note |
|---|---|---|---|
| `checked_id.json` | `assert!(x < K); x` | 3 (`SwitchInt → Return(x) \| panic-Call`) | single `_0 := Use(x)`; guard block carries no `_0 :=` |
| `bounded_double.json` | `assert!(x < K); x + x` | 4 (`SwitchInt → Assert → panic-Call → Return`) | single `_0 := Use(_t.0)`, `_t := CheckedBinaryOp(Add,x,x)`; the `SwitchInt`-to-panic AND overflow `Assert` are both skipped |
| `bounded_sum.json` | `assert!(a<K); assert!(b<K); a+b` | 6 | single `_0` write past THREE guard blocks (two asserts + the add's overflow assert) |

Each emits its `ArithmeticOverflow` safety VC (the in-MIR `Assert` IS the
runtime check); `trust_vcgen::generate_vcs` threads the guard's semantic fact
(`x < K` / `a<K ∧ b<K`) into the VC formula via its path-assumption map, so
`vc_refute` discharges it modulo 3. This discharge was already true before this
increment (`function_safety_vcs_all_discharged` is unchanged).

### Negative controls (`NEG_SOURCE.rs`) — with teeth

| fixture | shape | verdict | why |
|---|---|---|---|
| `either.json` | `if c { x } else { y }` | declines | TWO `Statement::Assign` writes to `_0` ⇒ `assign_count != 1`. The separate guarded-return frontier's territory. |
| `weird_guard.json` (+ its callee `non_panic_helper.json`) | `if x < K { x } else { non_panic_helper(x) }` | declines (via the NEW guard) | the else arm writes `_0` via `Terminator::Call{dest: _0, target: Some(3)}`; the then arm writes `_0 := Use(x)` via `Statement::Assign`. **Exactly ONE statement `_0 :=`** ⇒ the pre-guard scan would have false-certified `return x` — the latent unsoundness `ret_written_via_call` closes. |
| `unsafe_double.json` | `x + x` (NO leading `assert!`) | shape recovers, but stays SAFETY-GATED (not counted fully faithful) | `function_safety_vcs_all_discharged` is `false` — no guard fact to discharge the overflow VC. Confirms adequacy ≠ safety (mirrors the pre-existing `unsafe_add` control). |

`non_panic_helper.json` is dumped only as `weird_guard`'s real callee (for
re-dumpability); it is not asserted on directly.

Re-dump with `regenerate.sh` (requires a built stage2 `trustc` — see the repo
root `CLAUDE.md` build section).

## Re-dump audit resolution (2026-07-07)

The 2026-07-07 honesty audit (`reports/honesty-and-ladder-2026-07-07.md` §1.5,
§2 item 9) recorded one unresolved re-dump DIFF for `bounded_sum.json`
(6/7 siblings byte-reproduced; the recheck did not complete on the contended
host). The follow-up `cmp` was re-run on 2026-07-07 with the stage2 `trustc`
(`rustc 1.96.0-dev (340e45e50 2026-06-22) (trustc)`), re-dumping `SOURCE.rs`
into a fresh temp dir (never overwriting in place):
`checked_id.json`, `bounded_double.json`, and **`bounded_sum.json` are all
BYTE-IDENTICAL** to the checked-in fixtures. The earlier DIFF was a transient
artifact of the interrupted audit run, not a provenance bug — the committed
sources byte-reproduce their dumps.
