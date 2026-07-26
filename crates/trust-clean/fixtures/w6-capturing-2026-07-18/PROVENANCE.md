# w6-capturing-2026-07-18 — the W6 increment-3 CAPTURING-closure corpus

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

The FIRST capturing-closure `Option::map` / `Option::and_then` certificates.
12 W16 mono dumps: 4 wrappers, 4 monomorphized `Option::<{u8,i32}>::{map,and_then}`
instances, 4 closure bodies — 3 legitimate capturing probes + 1 FnMut-in-practice
forgery.

## Probe

`probe.rs` (assert-free capturing closures — NO arithmetic that emits overflow VCs,
except the FnMut forgery which uses `wrapping_add`, no VC either). Input flows from
`std::env::args().count()` so nothing folds to a constant.

```rust
fn cap_and(o: Option<u8>, k: u8) -> Option<u8>  { o.map(move |x| x & k) }
fn cap_or (o: Option<u8>, k: u8) -> Option<u8>  { o.map(move |x| x | k) }
fn cap_min_flag(o: Option<i32>, k: i32) -> Option<i32> {
    o.and_then(move |x| if x > k { Some(x) } else { None })   // stretch
}
// FORGERY (a): a capture-MUTATING closure. `Option::map` accepts it (FnMut: FnOnce),
// so its recorded ClosureCallKind is FnOnce — but the body WRITES `_1.0`.
fn cap_fnmut(o: Option<i32>, k: i32) -> Option<i32> {
    let mut acc = k;
    o.map(move |x| { acc = acc.wrapping_add(x); acc })
}
```

## Dump recipe (NO -O)

```
TRUST_DUMP_MONO=1 trustc --edition 2021 \
  -Ztrust-dump=mir-only:dumps -Ztrust-policy=advisory probe.rs -o probe
```

## KEY MIR FACTS

- `cap_and::{closure#0}` / `cap_or::{closure#0}`: `arg_count=2`, `_1` = BY-VALUE
  `Closure{upvars:[u8], call{kind:FnOnce}}` env, `_2` = x. Body:
  `_3 = copy _1.0; _0 = BinaryOp(BitAnd|BitOr, copy _2, move _3); Return`.
  The upvar field read `_1.0` is the sole shape blocker — resolved by W6 inc-3's
  `sem_field_read_operand` Closure arm to the MODEL-ONLY `Field(Var 0, 0)` carrier;
  the bitwise `Bin` arm chases the temp `_3` to it. No overflow VC → FULLY_FAITHFUL.
- `cap_min_flag::{closure#0}` (STRETCH): guarded ADT-return `if x > k { Some(x) }
  else { None }` with the upvar `k` in the GUARD (`_4 = copy _1.0; _3 = Gt(copy _2,
  move _4)`). The guarded-ADT-return lane resolves the upvar field and certifies —
  no arithmetic VC.
- `cap_fnmut::{closure#0}` (FORGERY): recorded `call_kind=FnOnce` (map's bound
  coerces it), but the body MUTATES its capture — `_1[Field 0] = move _3`. The
  capturing-leaf gate's PROJECTED-WRITE (env-mutation) clause declines the read, so
  the closure never certifies. (The call-KIND FnMut clause is defense-in-depth for a
  genuinely FnMut-typed env; real map-capture-mutating closures present as FnOnce +
  env-mutation, and the mutation gate catches them.)
- Capturing behavior at the compose lane: the mono `map`/`and_then` body passes the
  env WHOLE (`_e := Move(_2)`, no projections — TRUE for capturing instances too);
  captures ride inside the env VALUE the callResult carrier pins. MODEL-ONLY, NOT an
  `f(x, k)` value claim over the captures.

## Verdicts (`ff-gate-diagnose-2026-07-10 dumps`)

| function | verdict | lane |
|---|---|---|
| `cap_and::{closure#0}`  | **FULLY_FAITHFUL** | mirsem bitwise leaf (upvar Field) |
| `cap_or::{closure#0}`   | **FULLY_FAITHFUL** | mirsem bitwise leaf (upvar Field) |
| `cap_min_flag::{closure#0}` | **FULLY_FAITHFUL** | ir guarded-ADT-return (upvar-in-guard) |
| `Option::<u8>::map::<…7:11>`  (cap_and)   | **FULLY_FAITHFUL** | ir W6 map-compose — **FIRST CAPTURING MAP CERT** |
| `Option::<u8>::map::<…12:11>` (cap_or)    | **FULLY_FAITHFUL** | ir W6 map-compose |
| `Option::<i32>::and_then::<…17:16>` (cap_min_flag) | **FULLY_FAITHFUL** | ir W6 and_then-compose (capturing) |
| `cap_fnmut::{closure#0}` | SHAPE_GAP | env-mutation gate declines (FORGERY a) |
| `Option::<i32>::map::<…26:11>` (cap_fnmut) | SHAPE_GAP | closure uncertified ⇒ compose declines (FORGERY a) |
| `cap_and`/`cap_or`/`cap_min_flag`/`cap_fnmut` (wrappers) | SHAPE_GAP | closure-aggregate construction is unmodeled (not the deliverable) |

Baseline for grading: 6 FULLY_FAITHFUL (3 capturing closures + 3 capturing mono
instances) / 6 SHAPE_GAP (4 bin wrappers + the FnMut closure + its map instance).

## Design + honesty tier

MODEL-ONLY, split-claims (same tier as W6 inc-1/2). The env operand carries the
captures deterministically; the callResult is the opaque total function of
`(pinned callee, env VALUE)` — the SAME claim every certified call lane already makes
for a value-carrying arg. NOT an `f(x, k)` value claim. Capture soundness rests on
the type-authoritative call-kind gate (FnMut declines) + the env-mutation
(projected-write) gate.
