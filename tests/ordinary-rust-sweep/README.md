# The ordinary-Rust sweep

Eighty small programs of the kind people actually write — struct methods, slices,
iterator chains, `Option`/`Result` plumbing, string handling, arithmetic — none
of them chosen to probe a known boundary.

**Why it exists.** On 2026-09-19 the curated instruments read
`bench 66/71, 0 false refutations` and `probes 40 as documented, 0 diverged`, and
every remaining gap had been classified as an owner decision. This sweep was
written to test that classification, by measuring code nobody had aimed at a
known edge. It immediately found two things the curated sets did not cover:

* `is_sorted` — `v.windows(2).all(|w| w[0] <= w[1])` — is refuted, because the
  CLOSURE is verified as its own root where `w` is an arbitrary slice
  (`w__slice_len = 1` in the counterexample). `windows(2)` only ever yields
  length-2 slices, so the program is safe. This is the universal-root policy
  charging a body an obligation only its call site can discharge — the same
  shape as the derived `Debug` refusal, and far more general than "derives".
* `(0..n.min(8) as u32).collect()` was `[unbounded_allocation] FAILED` with a
  counterexample of 33554432 for an allocation bounded by 8.

The lesson is the instrument's, not the compiler's: a curated probe set measures
the boundaries you already know about. Keep this sweep UNAIMED — when adding to
it, write what you would actually write, not what you suspect will fail.

## The classification, at 80 programs (2026-09-19)

69 verify (2026-09-19, after the tolerance-ledger and constructor-FnDef fixes;
68 when this table was first written). The eleven that do not are **two genuine
bugs in the sweep's own programs** — `i32::MIN.abs()` panics (`s01`), and `part.min(whole) * 100`
overflows at `u32::MAX` (`t24`), both correctly refused — and nine failures in
exactly three causes:

| cause | count | witnesses |
|---|---|---|
| callees that GENUINELY panic on a caller value (correct refusals) | 5 | s03 s12 t09 t22 t23 |
| the universal-root policy on closures | 3 | s19 s23 t37 |
| proof AUTHORITY for an interval-lane bound | 1 | s20 |

*Correction 2026-09-24 (D5-C):* `s03` (`find(|x| x % 2 == 0)`) does not belong
in the first row. Its divisor is the constant `2`. Its closure row was an
unsummarized `Load` in the bundled `<&u32 as Rem<u32>>::rem`, which D5-C fixed.
Its root is refused by the transitive-member `Assert` gate. See
`tests/idiomatic-rust-sample/README.md` (`i04`, the same shape).

*2026-09-25 (measured):* that gate now credits a call site owned by a local body
whose own accepted run charged and proved it
(`trust_verify/member_assert_ownership.rs`). BEFORE, on stage 1 `43b8fe6ab`:
**72 / 80**, `s03` refused as `lowering did not complete` by that gate. AFTER, on
stage 1 `49bfcf5d0`: **73 / 80** — `s03` moved and nothing else did. The seven
that still fail are `s01` `s12` `t09` `t22` `t23` `t24` `t37`: five correct
refusals (`s01` and `t24` witnessed below; `s12` `t09` `t22` `t23` are callees
that panic on a caller value, retained as runtime assertions) and `t37`, which
waits on D2 tier 2.

That ranking was the point, and it drove the work: the six-row group was the
root-scoped tolerance ledger, which is now CLOSED (bench 68/71) — `t31`
(`checked_add(1).map(Id)`) moved with the constructor-FnDef fix, and the other
five turn out to be callees that genuinely panic on a caller-supplied value
(`v.remove(0)`, `s.repeat(n)`, `String::with_capacity(n)`), which the widened
tolerance correctly still refuses. The universal-root policy on closures is now
the largest remaining group. `derive(Debug)` does not appear at all.

**2026-09-24 — D2 tier 1 (`ADAPTER_YIELD`, docs/TCB.md).** `s19` and `s23` are
exactly the tier-1 shapes (`windows(2)` under `filter`+`count` and under `all`):
their closure rows prove and kernel-certify on their real MIR under the premise,
and the closure names the modeled fact it rests on. `t37` stays until tier 2
(capture-relative bounds), which waits on the struct-field slice-length work item
W-D2a (docs/DECISION_QUEUE.md, D2). **Measured 2026-09-25** (stage 1
`50bc1adc4`, the wave-2 build): **72 / 80 verify** — `s19` and `s23` moved; the
eight that still fail are `s01` `s03` `s12` `t09` `t22` `t23` `t24` `t37`.

**2026-09-25 — the integer-fold charge.** Stage 1 `ab7e41892`: 73 / 80 (the
seven failing are `s01` `s12` `t09` `t22` `t23` `t24` `t37`). After the fix:
**69 / 80**, and the four that moved (`s24` `s36` `t19` `t29`) are WITNESSED
overflows — see the section below. They join the correct-refusal row of the
table (`s12 t09 t22 t23`), which is now eight programs; `s01`/`t24` remain the
sweep's own bugs and `t37` the universal-root row.

**2026-09-25 — W4 VEC-INSERT: `t22` was never a correct refusal.** `t22`
(`if !v.is_empty() { let f = v.remove(0); v.push(f); }`) is GUARDED: `remove(0)`
on a non-empty `Vec` cannot panic. It sat in the first row because the mutator's
row was an unconditional `UnsupportedMir` that no guard could discharge, and the
compiler excluded `Vec::remove` from the vanilla class by name. vcgen now states
the real index precondition over the base's pre-mutation region, and the compiler
drops the exclusion at exactly that charged call (docs/TCB.md). Measured on stage 1
`b4bc7cdf9` + the W4 VEC-AS-SLICE/VEC-INSERT branch: **74 / 80 verify** (baseline
at `b4bc7cdf9`, same machine: 73 / 80) — `t22` moved and nothing else did. An
unguarded `v.remove(i)` is refused on `[slice] FAILED`, and one reached after
another mutation of its `Vec` keeps the old row.

## The two correct refusals are WITNESSED, not asserted (2026-09-20)

"Correctly refused" is a claim about the program, so it was run:

```
P { x: i32::MIN, y: 0 }.manhattan()   ->  attempt to negate with overflow
pct(100_000_000, 100_000_000)         ->  attempt to multiply with overflow
```

`i32::MIN.abs()` and `part.min(whole) * 100` both really do panic. **So 80/80 is
not this corpus's target and never was** — seven of its eighty programs are ones
Trust is RIGHT to refuse. Read against the table above, the current 69 sits four
rows under the ceiling this policy allows, and those four are the three closure
rows plus `s20`'s proof-authority question. Anyone quoting "69 / 80" as an
eleven-row deficit is reading it wrong.

## Four integer sums are correct refusals, WITNESSED (2026-09-25)

The integer `sum`/`product` overflow row never fired before 2026-09-25: its
recognizer matched the bare `…::Iterator::sum` spelling and rustc renders the
qualified `<I as core::iter::traits::iterator::Iterator>::sum::<T>` (see
`docs/KNOWN_HAZARDS.md`, "the integer `sum`/`product` recognizer never fired").
Once it fired, four programs that "verified" moved to refused — **73 / 80 → 69 / 80**
on the same day's build — and every one of them was run verify-off
(`-Ztrust-verify=off`, overflow checks on) on an input that overflows it:

| program | input | outcome |
|---|---|---|
| `s24` `zip_sum` | two slices of 8 500 000 × `255u8` | `attempt to add with overflow` (core `accum.rs`) |
| `s36` `take_while_sum` | 44 000 000 × `99u8` | `attempt to add with overflow` |
| `t19` `sum_pairs` | 8 500 000 × `(255, 255)` | `attempt to add with overflow` |
| `t29` `sum_u64` | `2^32 + 2` × `u32::MAX` (16 GiB; `-O -C overflow-checks=on`) | `attempt to add with overflow` |

So all four are **correct refusals**, in the same row as `s01`/`t24`: each sums a
slice of any length, and a length bound is what the program does not have. The
item values are small in `s24`/`s36`/`t19` (at most 510 / 99 / 510), but the
closure that widens them is a separate body, so its result range is not
visible to the caller's obligation — the refusal would stand even for a
fixed-length array (measured: `[u8; 16]` widened to `u32` and summed is refused,
which no input can overflow). That is the one over-refusal this charge carries,
and it is a missing closure-result range, not a verdict error.

`t23` was re-checked on the same pass and its row is `[unbounded_allocation]`,
not a callee panic — but the classification above still holds, and for a reason
worth writing down rather than rediscovering: that lane is the `with_capacity`
CAPACITY-OVERFLOW bound (`alloc_bounds.rs`), and `a.len() + b.len()` can exceed
`isize::MAX` because each operand only individually cannot. The panic is
unreachable on any real machine and reachable in the type model, and Trust
refuses on the model. The published counterexample (`2^28`, a 256 MB allocation
that does not panic) is a weak witness for a correct refusal — which is a
diagnostic gap, not a verdict gap.

*2026-09-25 (W4 ALLOC-LEN):* the diagnostic gap is closed and the verdict is
unchanged. A capacity that is a sum of live-sequence lengths no longer carries
the availability ceiling (`crates/trust-vcgen/src/generate/alloc_len.rs`,
`docs/TCB.md` "Live-length capacity"); it keeps ONLY the capacity-overflow
disjunct unless `T * (S1 + S2) <= S1 * S2` proves it, which two same-stride
`&str` lengths do not. `t23` is refused by that row, with the counterexample
`_3 = 9223372036854775808` (`2^63`, past `isize::MAX`) instead of `2^28`. Pinned
as revision `same_stride_sum` of `tests/ui/trust/alloc_capacity_from_live_length.rs`.

Runner: `scripts/ordinary_rust_sweep.sh`. It reports a count and classifies each
failure; it deliberately pins NO per-file expectation, because its job is to
surface surprises rather than to lock in a verdict.
