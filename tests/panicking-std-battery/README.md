# The panicking-std battery

Fifteen calls to std functions that PANIC on a caller-supplied value — a
mismatched length, an out-of-range index, a zero divisor, a `None`. Every one of
these programs can panic at runtime for some input.

**Why it exists.** The highest-frequency blocker in ordinary Rust
(`reports/2026-09-19-eighty-unaimed-programs-rank-the-decisions.md`) is the
absent-callee tolerance ledger being ROOT-scoped. Widening it measures bench
67/71 and was reverted twice for soundness reasons. The obvious worry about any
such widening is that it starts tolerating callees whose panic is a SAFETY
obligation about the caller's own value — not "std's own defined behaviour
reacting to the environment", which is what the vanilla class's argument rests
on.

This battery is the falsification gate for exactly that. It is not a wish list:
it records what the compiler does TODAY, so a widening that changes any row is
visible immediately.

## Measured behaviour, 2026-09-19

Fourteen are REFUSED. Each carries a second, dedicated row beside the
absent-callee one — e.g.

```
unsupported MIR `Call::remove::panic-freedom-unverified`: bb0: `remove` panics on
an out-of-range index ... and its panic-freedom is not modeled — guard the index
```

so the tolerance of the absent-callee row is already harmless for them: the
family recognizer (`is_index_panicking_container_mutator` and siblings) keeps the
function fail-closed independently. That is the property a widening must not
disturb.

`p07` (`copy_from_slice`) COMPILES, with warnings, and that is NOT a false proof:
its single obligation is reported `runtime-checked`, nothing claims proof, and
rustc's own assertion is retained. Verified end to end — the built binary panics
with `source slice length (5) does not match destination slice length (3)` and
exits 101. This is the ruled policy-B conditional pass.

## The rule for anyone changing the tolerance

Run `scripts/panicking_std_battery.sh` before and after. Fourteen must stay
refused. `p07` must keep compiling AND keep its runtime check — a version that
made it compile with the obligation PROVED rather than runtime-checked would be
the false proof this battery exists to catch.


## A related shape that is ALSO not a false proof

`pub fn f(x: &i32) -> i32 { x + 1 }` compiles (warnings only, no obligation row
charged) and its binary panics at `i32::MAX`, while the by-VALUE twin
`fn f(x: i32) -> i32 { x + 1 }` is a build error. That asymmetry looks exactly
like a hole and is not one: `&i32 + i32` routes through
`<&i32 as core::ops::arith::Add<i32>>::add`, which is core's own body with core's
own overflow check, and the bundled-foundational-member tolerance reports rather
than fails such a member's internal Assert.

`tests/ui/trust/foundational_member_qualified_path.rs` is `check-pass` and states
the rule outright — "`map(|x| x + 1)` reaches core's addition as
`<&u32 as core::ops::arith::Add<u32>>::add` … Both halves are core's own code" —
and `foundational_member_user_impl_stays_refused.rs` guards the other side, where
the soundness content is: the same spelling naming USER code stays refused.

Recorded here because both shapes in this directory (`p07` and this one) are
programs that compile and can panic, and in both cases the reason is a ruled
disclosure rather than a false claim. **Before reporting a tolerance as a defect,
grep `tests/ui/trust/` for a fixture naming the same member spelling.**
