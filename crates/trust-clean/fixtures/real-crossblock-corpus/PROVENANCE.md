# real-crossblock-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Trust: the §6 cross-block copy-back loop recognizer
(`resolve_guard_counter_update`, `prove.rs`), commit `a4ea5c0876`.

Classification (honesty ledger `reports/honesty-and-ladder-2026-07-07.md` §1.4):
**SYNTHETIC_EXTRACT** — both dumps are genuine, unmodified `TRUST_DUMP_MIR`
output from `trustc` ("real" = real compiler MIR, notably the real cross-block
overflow-checked lowering), but the source is authored micro-fixture Rust, not
published-crate code. Spec-free: no contracts; the loop invariants are fully
inferred — the honest shape.

| fixture | fn | role |
|---|---|---|
| `count_ret.json` | `count_ret(n: u32) -> u32` | **POSITIVE.** `while i < n { i += 1; w = w.wrapping_mul(3); }` — the counter commit `_2 := Move(_6.0)` lands in bb3 while the `Goto`-header back-edge is in bb4 (the trailing `wrapping_mul` call intervenes). The off-back-edge shape the fallback recognizer closes. |
| `double_bump.json` | `double_bump(n: u32, flag: bool) -> u32` | **NEGATIVE (fail-closed control).** TWO checked-increment commit sites for the same counter (one per `if flag` arm) — ambiguous, the fallback must DECLINE. |

## Reconstructed generating sources (2026-07-07)

The dumps were originally made (2026-07-01) from scratch files
`xblock_src.rs` / `xblock_neg.rs` in a session scratchpad
(`<dump-root>`)
that were **never checked in** and were later cleaned from disk — the
2026-07-07 honesty audit (§2 item 7) flagged this corpus as commit-message-only
provenance. The sources were reconstructed from the spans + MIR embedded in the
checked-in JSONs (the fn text is exactly pinned by the recorded spans — down to
`let mut w: u32 = 7;`, which the commit message does not mention; the comment
headers above the fns are *not* span-pinned and are authored) and are checked
in here as **`SOURCE.rs`** (count_ret) and **`NEG_SOURCE.rs`** (double_bump).

**Verification (2026-07-07):** the JSONs embed the *absolute* scratchpad paths
in every span, so the reconstructions were written back to those exact paths
and re-dumped with the stage2 `trustc`
(`rustc 1.96.0-dev (340e45e50 2026-06-22) (trustc)`):

```
LIBRARY_PATH=/opt/homebrew/lib \
  trustc --crate-type lib -Zcontract-checks=yes \
  -Ztrust-dump=mir-only:<out> -Ztrust-policy=advisory \
  <dump-root>   # and xblock_neg.rs
cmp <out>/count_ret.json   fixtures/real-crossblock-corpus/count_ret.json
cmp <out>/double_bump.json fixtures/real-crossblock-corpus/double_bump.json
```

This block records the historical byte-identity invocation. The inherited
exec-projection flag is now retired for Trust-active compilations; the live
`regenerate.sh` omits it. Both sources are spec-free, so it did not affect the
two bodies.

→ both **BYTE-IDENTICAL**. `regenerate.sh` reruns the same source/path/dump
procedure without the retired flag (it recreates the recorded absolute path —
required for byte-identity, since the span `file`
fields are absolute; on a machine where that path is not creatable the dump is
identical except those path strings).

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
