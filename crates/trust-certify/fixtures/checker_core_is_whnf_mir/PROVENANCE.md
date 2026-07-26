# Real clean-kernel MIR fixtures — `is_whnf` MIR-grounded discharge (Blocker-A)

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

These are REAL, fork-extracted MIR (`trust_types::VerifiableFunction`) for
literal `clean-kernel` `Expr` constructors. They ground the WHNF-head extraction
in `crates/trust-certify/src/checker_core_is_whnf.rs` (the `*_from_mir` lane) on
the actual kernel Rust, not a declared fixture string.

## Source

- clean submodule: recorded at `f9f8024d` (this run extracted at the checked-out
  `first-party/clean`); the constructors live in
  `crates/clean-kernel/src/expr/constructors.rs` and `.../expr/mod.rs`.
- Compiler: the in-tree stage2 Trust rustc fork
  (`build/aarch64-apple-darwin/stage2/bin/rustc`, `rustc 1.96.0-dev`).

## Extraction command (reproduce)

```bash
FORK="$PWD/build/aarch64-apple-darwin/stage2/bin/rustc"
RUSTC="$FORK" RUSTC_BOOTSTRAP=1 \
  cargo rustc --manifest-path first-party/clean/Cargo.toml -p clean-kernel --lib -- \
  -Ztrust-policy=advisory -Ztrust-verify-output=human \
  -Ztrust-dump=mir-only:<dir>
```

`cargo rustc -- <flags>` applies the Trust policy/dump flags to ONLY the top crate
(`clean-kernel`), so deps compile normally and only clean-kernel functions dump.
The per-function files are named `<module>__<Type>__<fn>.json`; the constructors
appear as `expr__constructors__<impl expr__Expr>__<fn>.json`.

## What was preserved vs. compacted

- `body.blocks` (statements, `Rvalue::Aggregate` with the `ExprKind` variant,
  the `Expr::from_kind` call, terminators) and `body.arg_count` are VERBATIM from
  the extraction — this is the load-bearing MIR the analysis reads.
- ONLY `body.return_ty` and each `body.locals[].ty` were stubbed to `"Bool"`
  (`Ty::Bool`). These type annotations are NEVER read by
  `extract_whnf_head_from_mir` / `mir_from_kind_is_kind_preserving`; stubbing
  them shrinks each fixture from 2.5–7.4 MB (recursive `Expr`/`ExprKind` type
  expansion) to 1–6 KB. No MIR instruction was hand-authored or altered.

## The fixtures

These cover the FULL `ExprKind` classification: the WHNF heads (Sort via
prop/sort, Pi via arrow) and one real literal constructor for each EXTRACTABLE
representative NON-WHNF variant (BVar/FVar/Const/App/Let/Lit/Proj). Every
non-WHNF fixture MUST extract to `None` (fail closed) — the no-masquerade
witness. `MData` (variant 10) has no fixture — its constructor is not
monomorphized in the crate-lib dump, so it cannot be fork-extracted; its
classification is asserted at the mapping level and its extraction-level witness
is skipped VISIBLY (see `EXTRACTION_SKIPPED` in the test).

| File | fn | ExprKind aggregate | head | role |
|---|---|---|---|---|
| `clean_kernel.expr.Expr.prop.json` | `Expr::prop` | variant 2 (Sort) | Sort | POSITIVE (WHNF) |
| `clean_kernel.expr.Expr.sort.json` | `Expr::sort` | variant 2 (Sort) | Sort | POSITIVE (WHNF) |
| `clean_kernel.expr.Expr.arrow.json` | `Expr::arrow` | variant 6 (Pi) | Pi | POSITIVE (WHNF) |
| `clean_kernel.expr.Expr.bvar.json` | `Expr::bvar` | variant 0 (BVar) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.fvar.json` | `Expr::fvar` | variant 1 (FVar) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.const_str.json` | `Expr::const_str` | variant 3 (Const) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.app.json` | `Expr::app` | variant 4 (App) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.let_named.json` | `Expr::let_named` | variant 7 (Let) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.nat_lit.json` | `Expr::nat_lit` | variant 8 (Lit) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.proj.json` | `Expr::proj` | variant 9 (Proj) | — | NEGATIVE (fail closed) |
| `clean_kernel.expr.Expr.from_kind.json` | `Expr::from_kind` | `Expr` variant 0 | n/a | kind-preservation check |

(`Expr::mdata`, variant 10 MData, is absent — see below.)

The full index<->classification table (all real + future variants, with the
exhaustive fail-closed range) is asserted by
`checker_core_is_whnf::tests::full_exprkind_classification_is_complete_and_fails_closed`.

`Expr::lam` / `Expr::pi` / `Expr::type_` / `Expr::mdata` are absent because they
are generic (`impl Into<BinderData>`) / uninstantiated in the crate lib and so
were not monomorphized into the dump; the fixture-string lane already covers the
`lam`/`pi` heads, and `arrow` supplies the MIR-grounded `Pi` positive. For the
non-WHNF `mdata` (variant 10), the mapping-level classification (variant ->
`None`, fail closed) is asserted unconditionally and the extraction-level witness
is recorded as SKIPPED in the test's `EXTRACTION_SKIPPED` register (pending
monomorphization). There is NO
statically-dischargeable WHNF head beyond Sort/Lam/Pi (the `is_whnf` model's
`neutral` case needs an `is_neutral` proof, which this lane does not construct;
neutral-headed variants therefore correctly fail closed).

## The LITERAL-`whnf` identity fixture (first property about the reducer)

| File | fn | role |
|---|---|---|
| `clean_kernel.tc.whnf.whnf_impl.json` | `TypeChecker::whnf_impl` | the early-return identity match (whnf.rs:145-165) |

This is the REAL, fork-extracted MIR of the literal reducer
`tc::whnf::<impl tc::TypeChecker<'env>>::whnf_impl` (the function `whnf` delegates
to). It grounds the `whnf_identity_path_head` / `certify_whnf_identity_from_mir`
lane — the FIRST property about the literal `whnf` FUNCTION rather than a
constructor. The load-bearing slice (verbatim from the extraction) is the
early-return match:

```text
bb0:  _3 = &((*e).kind)                        // e = arg local _2
      _4 = Discriminant((*_3))                 // discriminant of (*e).kind
      SwitchInt(move _4) -> [ 0: bb2,  1: bb1,  2: bb2,
                              5: bb2,  6: bb2,  8: bb2 ], otherwise: bb11
bb2:  _0 = <Expr as Clone>::clone(Copy _2) -> bb16    // return e.clone()  (IDENTITY)
bb16: return
bb1:  ... FVar arm: &self.ctx borrow, RefCell::borrow ...   // CONDITIONAL, non-identity
bb11: ... inc_heartbeat ... whnf_inner ...                  // fall-through, RECURSIVE core
```

The SwitchInt targets are exactly the source's `Sort|Pi|Lam|Lit|BVar` early-return
arm (variants 2/6/5/8/0 -> the identity block bb2), the `FVar` arm (variant 1 ->
the conditional bb1), and the `_ =>` fall-through (App/Const/Let/Proj/MData/... ->
otherwise bb11, which enters the recursive core). The analyzer confirms, PER INPUT
VARIANT, that the SwitchInt-selected block returns `_0 = clone(e)` where the clone
argument is the SAME argument `e` the discriminant was read from. Sort/Lam/Pi then
discharge `is_whnf`; Lit/BVar prove identity but fail closed at discharge (no
`is_whnf.lit`/`is_whnf.bvar` ctor); FVar (conditional) and App (fall-through)
FAIL the identity check — the load-bearing witnesses that the brick claims nothing
about the recursive core.

The compaction recipe is the same (only `return_ty` / `locals[].ty` and any
embedded `Cast`/`OpaqueCast` `Ty` stubbed to `Bool` — never read by the analyzer);
`body.blocks` are verbatim. Extracted at clean submodule
`a786ad24` (the recorded pin at extraction time; the WHNF-head variant indices
2/5/6 and the non-WHNF 0/1/4/8 are unchanged from the `f9f8024d`/`97950495`
layouts the sibling constructor fixtures pin).

## 2026-07-17 addition — the recursive whnf core (8 bodies)

`clean_kernel.tc.whnf.{whnf_impl.closure0,whnf_impl.closure1,whnf_inner,whnf_core,
whnf_core_inner,whnf_core_no_delta,beta_or_iota_step,try_path_beta_step}.json`:
REAL fork-extracted MIR of the whnf REDUCTION CORE (the `stack_safe` closure payload
and everything it reaches), captured 2026-07-17 from the in-tree stage2 fork at the
`first-party/clean` checkout `883c59d65` (Brick-A pin).

Extraction (the recipe CHANGED since the section above — measured):

```bash
FORK="$PWD/build/aarch64-apple-darwin/stage2/bin/rustc"
RUSTC="$FORK" RUSTC_BOOTSTRAP=1 \
  RUSTFLAGS="-Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir>" \
  CARGO_TARGET_DIR=<tmp> cargo build --manifest-path first-party/clean/Cargo.toml -p clean-kernel
```

Notes: `-Ztrust-dump=mir-only:<dir>` must be GLOBAL (per-crate `cargo rustc --` flags dump
nothing on a contract-free crate, and plain survey ICEs the embedded AY solver on
rayon's deps — ay-bindings/expr/bool.rs:28); dump filenames are now
CONTENT-ADDRESSED (`trust-mir-<hash>.json`) — select by the `def_path` INSIDE each
JSON, never by filename; a full dump is ~6 GB — prune concurrently
(`grep -L '"def_path": "tc::whnf'`) with a `df` guard. Same minimization as above:
ONLY `body.return_ty` and `body.locals[].ty` stubbed to `"Bool"`
(2.3 MB -> 1.4 KB for closure1); blocks/statements/terminators VERBATIM. The fork
encodes unwind-carrying calls as `Terminator::Opaque` whose `kind` string preserves
the callee path (`Call::tc::whnf::…::whnf_inner::UnsupportedUnwind(Continue)`) —
the payload witness reads the callee from that string.

## Extraction round 3 (2026-07-18): the projection/δ step-function family

Same fork (stage2, in-tree), same GLOBAL-flags recipe, dump dir on the session
scratchpad with a 20 s content pruner. clean-kernel checkout at X11 `ea7b6dd3d`
(branch `trust-brick-a-const-whnf-reducible`). Six new fixtures, same
minimization (ONLY `body.return_ty` + `body.locals[].ty` stubbed to `"Bool"`;
blocks VERBATIM):

- `clean_kernel.tc.whnf_proj.reduce_proj_with_mode.json` (45 blocks) — the
  ι-projection step: mode-routed struct normalization, string-literal
  constructor path, constructor lookup + field-index arithmetic
  (`saturating_add` + `get_app_args` + `slice::get`), stuck `proj` rebuild.
- `clean_kernel.tc.whnf_proj.reduce_proj_with_mode.closure{0,1}.json` — its
  two `stack_safe` payload closures.
- `clean_kernel.tc.whnf_proj.whnf_reduce_proj.json` (2 blocks) — the shim
  `whnf_core_inner` actually calls: sole callee `reduce_proj_with_mode`,
  tail-to-Return.
- `clean_kernel.tc.whnf_proj.unfold_definition_cached.json` (30 blocks) — the
  δ step: cache get/hit/miss, the Const-kind test (variant 3) GATING the env
  `unfold_definition` call, Option-try success/failure, conditional insert.
- `clean_kernel.tc.whnf_proj.try_unfold_definition.json` (48 blocks) — the
  uncached δ helper.

CROSS-CHECK: the same dump reproduced `tc::whnf::whnf_core_inner` and its
`body.blocks` are BYTE-IDENTICAL to the committed
`clean_kernel.tc.whnf.whnf_core_inner.json` — the fixture set remains faithful
to the pinned upstream.
