# container-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Trust: a REALISTIC BOUNDED-STACK CONTAINER benchmark — the first multi-method
"real container API" corpus (as opposed to `leaf-call-corpus`'s single
external-crate leaf/composition/is_empty triad). Unlike `leaf-call-corpus`
(dumps copied verbatim from a real, unmodified external crate), this corpus's
`SOURCE.rs` is HAND-AUTHORED (mirroring `call-spine-corpus`'s convention) —
but the 8 JSON dumps are still REAL `trustc` MIR, never hand-transcribed:
produced by compiling `SOURCE.rs` with a real stage2 `trustc` under
`-Ztrust-dump=mir:<dir>` (`regenerate.sh` reproduces them byte-for-byte).

Historical provenance: the original checked-in dump invocation also passed
`-Zcontract-checks=yes`. That inherited exec-projection flag is now retired
for Trust-active compilations and did not affect these spec-free methods; the
live regeneration script intentionally omits it.

```
pub struct Stack { buf: [u64; 32], len: u32, cap: u32 }
impl Stack {
    pub fn len(&self) -> u64 { self.len as u64 }
    pub fn capacity(&self) -> u64 { self.cap as u64 }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn is_full(&self) -> bool { self.len() == self.capacity() }
    pub fn remaining(&self) -> u64 { self.capacity() - self.len() }
    pub fn has_len(&self, n: u64) -> bool { self.len() == n }
    pub fn at_least(&self, n: u64) -> bool { self.len() >= n }
    pub fn double_len(&self) -> u64 { self.len() + self.len() }
}
```

(`buf` is never read by any of these 8 methods — `trustc` correctly warns
`field \`buf\` is never read`; it exists to make `Stack` a genuinely
capacity-bounded container shape, not just a two-`u32`-field struct. `remaining`
and `double_len` also emit expected Level-0 `[overflow:sub]`/`[overflow:add]`
warnings — `Stack` carries no invariant tying `len ≤ cap`, so those two
methods' arithmetic is genuinely unguarded. The MIR-SHAPE recognizers this
corpus exercises reason about the SHAPE of the return computation, not whether
its arithmetic is provably safe — that adequacy/safety split is exactly what
`remaining`/`double_len`'s own row below demonstrates: shape now RECOGNIZED,
safety correctly NOT discharged.)

## Per-method shape split (callees-first `prove_dump_dir` census)

| fixture | shape | lane |
|---|---|---|
| `Stack__len.json` | **LEAF** — field-read (`(*self).1`, the `len: u32` field) + `u32→u64` widening cast. Byte-identical shape to `leaf-call-corpus/arrayvec_len.json` (field index differs: 1, not 0). | `sem_field_read_operand`/`resolve_widening_cast_rvalue` (pre-existing; unrelated to CALL-THEN-PUREOP). |
| `Stack__capacity.json` | **LEAF** — same shape as `len`, over the `cap: u32` field (index 2). | same as `len`. |
| `Stack__is_empty.json` | **CALL-THEN-PUREOP, CONST operand** — `_2 := Stack::len(self); _0 := (Move _2 == 0u64)`. Byte-identical shape to `leaf-call-corpus/arrayvec_is_empty.json` (the CONST-operand fragment closed by commit `198b581a61`). | `sem_call_then_pureop_of_mir`, CONST path (pre-existing). |
| `Stack__has_len.json` | **CALL-THEN-PUREOP, PARAM operand — THIS increment.** `_3 := Stack::len(self); _0 := (Move _3 == Copy _2)` where `_2` is the SECOND parameter `n: u64`. Structurally identical to `is_empty` except the non-call operand is a function PARAMETER, not a closed constant — the residue `is_empty`'s own commit disclosed ("a param-valued OTHER operand … is deferred fail-closed on both lanes") and this increment closes. | `sem_call_then_pureop_of_mir`, PARAM path (NEW). |
| `Stack__at_least.json` | **CALL-THEN-PUREOP, PARAM operand — THIS increment.** `_3 := Stack::len(self); _0 := (Move _3 >= Copy _2)` — same shape as `has_len`, comparison op `Ge` instead of `Eq` (exercises the OTHER `SemCmpOp` swapped-operand case, `call_is_lhs = true`). | `sem_call_then_pureop_of_mir`, PARAM path (NEW). |
| `Stack__is_full.json` | **CALL-OP-CALL, DIRECT — CLOSED this increment.** `_2 := Stack::len(self); _3 := Stack::capacity(self); _0 := (Move _2 == Move _3)` — TWO `Call` terminators, one feeding EACH operand of the comparison. `sem_call_op_call_of_mir` recognizes it: both `_2`/`_3` sole-written by a certified call, `_0`'s sole write a bare `BinaryOp(Eq, …)` consuming BOTH. 0 safety VCs (`==` never overflows) ⇒ **fully faithful**, both lanes. | `sem_call_op_call_of_mir` (NEW). |
| `Stack__remaining.json` | **CALL-OP-CALL, VIA THE CHECKED-ARITH TUPLE — CLOSED this increment (adequacy), safety-gated.** `_2 := Stack::capacity(self); _3 := Stack::len(self); _4 := CheckedBinaryOp(Sub, Copy _2, Copy _3); …; _0 := Use(Move _4.0)`. `sem_call_op_call_of_mir` NOW recognizes this (generalizing the EXISTING checked-arith tuple/`.0`-field modeling — previously only admitted a param/const operand — to BOTH operands being call-result temps): the return computation `capacity() - len()` is kernel-proven ADEQUATE (`callOpCallInstance` modulo 3, both lanes). It does **NOT** count as fully faithful: `Stack` carries no `len ≤ cap` invariant, so the `Sub` overflow VC is a REAL, unguarded panic risk — `function_safety_vcs_all_discharged` genuinely returns `false` (`vc_refute` cannot refute `capacity < len`, which IS satisfiable). Honest — the SAME class as the `unsafe_add` negative control elsewhere in this codebase, not a recognizer gap. | `sem_call_op_call_of_mir` (NEW) — adequacy-certified, safety-gated. |
| `Stack__double_len.json` | **CALL-OP-CALL, VIA THE CHECKED-ARITH TUPLE — CLOSED this increment (adequacy), safety-gated.** `_2 := Stack::len(self); _3 := Stack::len(self); _4 := CheckedBinaryOp(Add, Copy _2, Copy _3); …` — TWO calls to the SAME callee (explicitly allowed) feeding a checked add. Same closure/gating as `remaining`: the return computation `len() + len()` adequacy-certifies (kernel-proven modulo 3), but the `Add` overflow VC is genuinely undischarged (the caller's own locals are typed `u64` with no narrower tracked range from the call, so `vc_refute` cannot rule out the worst case) — safety-gated, not shape-gated. | `sem_call_op_call_of_mir` (NEW) — adequacy-certified, safety-gated. |

**Census (callees-first, `prove_dump_dir` over this directory):**
`fully_faithful = 6` (`len`, `capacity`, `is_empty`, `has_len`, `at_least`,
`is_full`) — `fully_faithful_via_trustir = 6` (all six are trust-ir-primary:
the two leaves are MODEL-ONLY grounder-connected field-reads, the other four
route through the wrapped `callRefinesContract` instance — `is_full` through
the NEW `callOpCallInstance`, two nested transports) —
`fully_faithful_mirsem_fallback = 0`. `len` and `capacity` are LEAVES (no
callee dependency); `is_empty`/`has_len`/`at_least`/`is_full`/`remaining`/
`double_len` each require `Stack::len` (and, for `is_full`/`remaining`,
`Stack::capacity`) already certified in the callees-first registry —
`prove_dump_dir` resolves this ordering automatically (Tarjan-SCC + post-order
DFS over the `Terminator::Call` edges).

**Before this increment**, `fully_faithful` was 5/8 (`len`, `capacity`,
`is_empty`, `has_len`, `at_least` — everything the CALL-THEN-PUREOP CONST/PARAM
paths already covered); `is_full`/`remaining`/`double_len` declined because
`sem_call_then_pureop_of_mir`'s "exactly one `Call` terminator" gate rejects a
TWO-call body outright — BOTH operands being call results (rather than one
call result + a param/const) is a structurally different shape. This increment
adds a SIBLING recognizer, `sem_call_op_call_of_mir` (wired via disjunction;
`sem_call_then_pureop_of_mir` stays byte-identical, tried first at every
return site): EXACTLY TWO `Call` terminators, each sole-writing its own temp to
a certified callee (the SAME callee twice is explicitly allowed —
`double_len`), whose results are BOTH operands of `_0`'s pure op — either
DIRECTLY (`is_full`'s bare `BinaryOp`) or through the EXISTING checked-arith
tuple/`.0`-field modeling generalized to two call-result operands
(`remaining`/`double_len`'s `CheckedBinaryOp`). The kernel certificate
transports BOTH calls' opaque results through TWO NESTED applications of the
SAME proven `callRefinesContract` (never a new axiom — the same posture as the
PARAM-OPERAND widening's extra ∀-bound binder, just two of them: `∀ post ∀ retA
∀ retB`).

**HONEST OUTCOME — the SHAPE residue is closed for all 3 (`is_full`/
`remaining`/`double_len` all now RECOGNIZE and kernel-prove their return
adequacy modulo 3, both lanes), but only `is_full` reaches `fully_faithful`.**
`remaining`/`double_len` stay OUT of the count because their `CheckedBinaryOp`
overflow VC is GENUINELY undischargeable — `Stack` carries no `len ≤ cap`
invariant, so `capacity() - len()` / `len() + len()` really can panic, and
`vc_refute` correctly cannot refute that. This is NOT a gap in the CALL-OP-CALL
recognizer (confirmed: `crate::mirsem::function_fully_faithful_witness_with_
callees` mints a modulo-3 adequacy certificate for both) — it is the SAME
"adequate but not fully faithful" class the `unsafe_add` negative control
demonstrates elsewhere in this codebase (an unguarded operation whose RETURN
VALUE is faithfully modeled but whose SAFETY is not, and correctly, provable).
Closing a MIR-shape residue must never silently paper over a genuine,
unguarded overflow — the corpus deliberately keeps `remaining`/`double_len`'s
unguarded arithmetic in place (rather than adding an invariant to `Stack`) so
this honest split stays measured and visible.

Re-dump with `regenerate.sh` (requires a built stage2 `trustc` — see the repo
root `CLAUDE.md` build section). `TRUSTC=/path/to/trustc ./regenerate.sh` to
override the default `build/host/stage2/bin/trustc` resolution.

## `vec_get.json` relocation

This directory used to ALSO hold an unrelated single fixture, `vec_get.json`
(a `Vec<u32>` bounds-check dump from the GOAL-ITEM #2 structural-container
work, `fce134b7ef`) — reusing `container-corpus` for the Stack benchmark would
have corrupted BOTH corpora's own `prove_dump_dir` census (that fixture's own
test expects `total == 1`; this one expects `total == 8`). It has been
relocated (`git mv`, history preserved) to `fixtures/vec-get-corpus/
vec_get.json`; `prove.rs`'s
`prove_container_corpus_grounds_vec_structurally_and_discharges_bounds_modulo_3`
test was updated to point at the new path — its own assertions are otherwise
unchanged.
