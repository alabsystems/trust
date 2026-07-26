# W19 mutators inc-1 fixture — &mut-self field setters (2026-07-24)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Dumped from the pinned stage2 trustc (READ-ONLY), `--crate-type lib -Ztrust-policy=advisory
-Ztrust-dump=mir-only:<dir>`, from `main.rs`. Three shapes, identified by def_path:

| dump | method | shape | inc-1 role |
|---|---|---|---|
| `trust-mir-e22e2087665ccf84-*` | `S::set_x` | 1 block, single `[Deref, Field(0)]` write of a bare param `Copy` | **inc-1 TARGET** — the minimal single-scalar-field setter (post = independent param) |
| `trust-mir-3ac4998cc27549d8-*` | `S::set_both` | 1 block, two sequential field writes (Field 0 then Field 1) | multi-field BOUNDARY — a single-field `SemFieldSet` must NOT match it (or must frame both) |
| `trust-mir-60072d01ccb95541-*` | `S::bump` | 2 blocks, `self.x += 1` read-modify-write with an overflow-check | **inc-1.5** (deferred) — post = f(pre), needs the arithmetic-tie-on-frame |

Verified MIR shape of `set_x` (from the dump):
- `body.locals = [ _0 Unit, _1 self Ref{mutable:true, inner:Adt S{[(x,i64),(y,i64)]}}, _2 v Int{64,signed} ]`
- `bb0.stmts = [ Assign{ place:{local:1, projections:["Deref", {Field:0}]}, rvalue:Use(Copy{local:2}) } ]`
- `bb0.terminator = "Return"` (the `()` return is implicit — `_0:Unit` + `Return`, no explicit `_0 = ()`).

All three currently raise exactly one obligation each that returns UNKNOWN under
`-Ztrust-dump=mir-only:<dir>` — a setter certifies NOTHING today (the honest havocked floor). W19 inc-1
lands the INERT post-state SURFACE (a generation-re-keyed `idx_elem'` opaque + T-SET/T-FRAME
theorems, call-site-inert, verdict-neutral — mirroring W-PRIMED inc-1); the caller-visible
read-after-set that would flip a verdict is F12-blocked and deferred.
