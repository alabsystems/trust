# record-witness-2026-07-22 — fresh MIR dumps for the RECORD witness (increment 1)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Fresh-format monomorphized MIR dumps for `mirsem::SemStructReturn` (the single-variant
struct-constructor return witness, increment 1 — `expr::types::BinderData::new`-class).
These are the FIRST validation step for the recognizer: the only prior corpus form of a
`BinderData::new`-style struct constructor is the legacy `__tag`/`__v`-flattened
census-m6 dump, which the recognizer's fresh-metadata gate must decline.

## Recipe (byte-reproducible)

Source: `main.rs` (in this directory), built with the shared stage2 trustc:

```
TRUST_DUMP_MONO=1 <trustc> --edition 2021 \
  -Ztrust-dump=mir-only:<dir> -Ztrust-policy=advisory main.rs -o <bin>
```

Each `<name>.json` is the `trust_types::VerifiableFunction` for that fixture, extracted
from the survey dump directory by `body.name`.

## Fixtures

- **mk_pair** — `fn mk_pair(a: i64, b: i64) -> Pair { Pair { a, b } }`. The anchor: a
  single-block `_0 = Aggregate(Adt{main::Pair, variant 0, active_field: None}, [Copy _1,
  Copy _2]); Return`, fresh `fields` metadata, `variants: []`. **Certifies** (mk_pair
  FULLY_FAITHFUL).
- **mk_three** — a 3-field struct with a `PhantomData<u32>` marker field:
  `Three { a: i64, m: PhantomData<u32>, b: i64 }`. The Aggregate is `[Copy _1,
  Constant Unit, Copy _2]`; the marker field type is a fieldless `Adt
  "core::marker::PhantomData"` (reflecting to kernel `Unit`), and its operand is a
  `ConstValue::Unit`. **Certifies** — the marker is the closed `Unit.unit` `.mk` argument.
- **mk_swap** — `fn mk_swap(x: i64, y: i64) -> Pair { Pair { a: y, b: x } }`. The
  distinct-operand (`[Copy _2, Copy _1]`) two-same-sorted-field fixture for the
  MIR-order-fidelity differential probe (gate D): transposing the operand vector yields
  a DIFFERENT `.mk` application, never vacuously def-eq. **Certifies**.
- **mk_bad** — `fn mk_bad(mut a: i64, b: i64) -> Pair { a = a & b; Pair { a, b } }`, the
  reassigned-param forgery fixture. **DECLINES**.

## Finding: real rustc lowering does not emit the reassigned-param-operand forgery

The adversarial gate-A hazard is a `Copy(_p)` Aggregate operand whose parameter root `_p`
was reassigned before the read (an entry-time `Var(p)` denotation would then certify the
WRONG, pre-reassign value). Real trustc lowering does NOT produce that shape:

- `a = 77;` (a constant) is **const-folded** — the operand becomes `Constant(Int 77)`,
  `_1` is never written, and the body is genuinely sound (operand literally is 77).
- `a = a & b;` routes the computed value through a **fresh temp** `_3 = BitAnd(_1, _2)`;
  the Aggregate operand for `a` is `Copy(_3)`, and `_1` (the parameter) stays pristine.
  `mk_bad.json` is this form. It DECLINES because `_3` is a non-parameter derived temp
  outside the increment-1 bare-scalar operand fragment (`sem_operand_of_mir` resolves
  only bare parameters / constants / deref-of-scalar-ref) — not because of gate A.

So the reassigned-param-operand forgery is effectively non-producible by the real
frontend (itself a soundness margin). Gate A (route every operand through the
`sem_operand_of_mir` PARAM-ROOT chokepoint, which fails closed on
`param_reassigned_by_stmt`) is retained as defense-in-depth and is pinned CRISPLY by a
SYNTHETIC unit test (`mirsem::tests`) that hand-builds the exact `_1 := <op>; _0 =
Aggregate(S, [Copy _1, Copy _2]); Return` shape and asserts it declines.
