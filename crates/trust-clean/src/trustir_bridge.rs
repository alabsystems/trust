// Trust: the SHIPPED Lean↔Clean bridge gate — kernel-checked agreement between
// trust-ir's REAL Lean 4.8 operational semantics (`TrustIr.semIntBinOp`, built
// unmodified by `lake build` from the pinned `first-party/trust-ir` sources and
// machine-imported from VENDORED `.olean` artifacts) and trust-clean's Clean
// denotation of the same `trust_ir::BinOp` syntax (the `Int.add/sub/mul/…`
// family the live grounder emits, `clean_ground.rs`). This module is the
// integration of the 18-op agreement theorem
// (reports/bridge-assembly-11arms-2026-07-02.md §5, recommendation (i)):
// the `.olean`s are checked in with a provenance manifest, and the gate is a
// default-on test — no Lean toolchain is needed at test time.
//
// EXTENSION (this increment): `TrustIr.semIntUnOp` — trust-ir's UNARY-op
// semantics (`Neg`/`Not`/`CtPop`/`FNeg`). `UnOp` and `semIntUnOp` are declared
// in the SAME Lean module as `BinOp`/`semIntBinOp`
// (`TrustIr/BinOp.lean` + `TrustIr/Semantics/Arith.lean`, both already
// vendored under `BRIDGE_ROOT_MODULE`), so this needed NO manifest/olean
// regeneration — only new agreement theorems against the already-imported
// constants. Bridged: `Neg` (form b), `Not` (form b), `FNeg` (form a).
// Honestly NOT bridged: `CtPop` — Clean has no popcount denotation anywhere
// (neither the live grounder nor `trustir_anchor.rs`'s `TrustIrUnOp` model
// it), so no agreement claim is made (see [`UNOP_UNBRIDGED`]). See the
// "semIntUnOp" constants section below for the per-arm detail, including the
// `Int.neg` vs. `Int.sub (Int.ofNat 0) ·` spelling subtlety that does not
// arise anywhere in the BinOp arms.
//
// WHAT IS PROVEN, PER OP (the honest per-arm form):
//   * form (a) — plain agreement (the 5 float BinOp arms + the UnOp `FNeg`
//     arm): on the integer path the imported semantics is unconditionally the
//     `typeError` value; the integer denotation's domain excludes float ops
//     by construction.
//   * form (b) — agreement UNDER THE NO-OVERFLOW / IN-RANGE SIDE CONDITION
//     (the 6 unguarded integer arms + the 7 guarded arms, which additionally
//     take the arm's own UB guards as hypotheses; plus the UnOp `Neg`/`Not`
//     arms, unguarded): trust-ir's semantics is width-aware (`wrap v = ((v %
//     2^w) + 2^w) % 2^w`); the wrap layer is elided exactly when the
//     mathematical result is already in `[0, 2^w)` — the side condition the
//     safety-VC tier separately discharges (the L0 NoOverflow VCs, and for
//     `Neg` specifically the negation-overflow VC, Lemma 6). The wrap-elision
//     lemma `wrap_eq_self` is proven AGAINST THE IMPORTED SEMANTICS' own
//     reduct, not a Clean re-statement of it.
//
// FAIL-CLOSED CONTROLS (every one hard-fails the gate, never a silent pass):
//   * MANIFEST: every vendored `.olean` must match its per-file sha256 in
//     MANIFEST.toml; a missing/tampered/unlisted file is a hard error.
//   * PIN DRIFT: the manifest's `trustir_commit` must equal the checked-out
//     `first-party/trust-ir` submodule HEAD (and the pinned Lean sources must
//     be clean) — stale artifacts = stale semantics = the gate is meaningless,
//     so it refuses to run rather than certify against the wrong pin.
//   * IMPORT HYGIENE: the loaded module set must equal the manifested set, and
//     the imported TrustIr constants must pass local type/value consistency
//     checks with 0 failures in that imported environment. This is NOT fresh
//     `add_decl` replay: a populated context can supply self references or
//     unchecked dependencies. The imported closure remains part of the TCB.
//   * AXIOM RESIDUE: every proven theorem must have `axiom_deps = ∅` (no
//     domain axioms, no sorry/trust markers; only the foundational trio is
//     filtered by `Environment::axiom_deps`) — the "modulo exactly 3"
//     discipline.
//   * FORGERY PROBES: deliberately-wrong claims (Add-agrees-with-`Int.sub`,
//     FAdd-with-the-wrong-error-string, and — for UnOp — Neg-agrees-with-the-
//     Not/xor-term, FNeg-with-the-wrong-error-string) must be kernel-REJECTED
//     each run — the bridge is a genuine check, not a tautology.
//   * An arm that fails to prove is NOT an error of the gate: it is recorded
//     in `ops_pinned`/`unop_pinned` (with the failure head), so the count
//     flips automatically with a clean pin bump — and the default-on test
//     asserts `ops_pinned == 0` / `unop_ops_pinned == 0`, so any regression
//     fails loudly.
//
// RESIDUAL TRUST, stated plainly (see the module tests + `ProveScorecard::
// bridge_line`): (1) builder trust on the vendored oleans is mitigated by the
// behavioral pinning above (every BRIDGED arm of the imported definition is
// constrained by at least one kernel-checked theorem) + the manifest + the
// regeneration audit lane (scripts/regen-trustir-oleans.sh); (2) the complete
// imported Init/TrustIr closure is an assumed environment, not independently
// reconstructed by fresh dependency-closed declaration replay. Local checks
// cannot reduce that trust boundary to a selected diagnostic failure cluster;
// (3) the bridge equates
// constants IN THE IMPORTED Lean-core environment with the same-named
// constants the shipped witness grounds to in clean's prelude environment —
// a name-keyed identification of ~6 basic constants (`Int`, `Int.add/sub/mul`,
// …), with the imported side's T-division behavior witnessed by the
// characterization rows; (4) the agreement covers `semIntBinOp` and (as of
// this increment) `semIntUnOp`'s Neg/Not/FNeg arms — trust-ir's WIDER
// Inst/statement-level semantics (evalBody/evalCfg/loops), and `UnOp::CtPop`
// specifically, are NOT bridged; CtPop is reported honestly as un-bridged,
// never faked.
//
// EXTENSION 2 (this increment): `TrustIr.semOverflowOp` — the OVERFLOW-CHECKED
// arithmetic semantics (`AddOverflow`/`SubOverflow`/`MulOverflow`, each
// returning `(result, overflow_flag)`). `OverflowOp` and `semOverflowOp` are
// declared in the SAME already-vendored Lean files as `BinOp`/`UnOp`
// (`TrustIr/BinOp.lean` + `TrustIr/Semantics/Arith.lean`) — no manifest/olean
// regeneration needed. This is the checked-arith semantics the recognizers
// model everywhere (MIR `CheckedBinaryOp`'s `.0` value + `.1` overflow flag),
// and it underpins the L0 safety-VC overflow discharge
// (`trustir_safety.rs`/`mirsem.rs` Lemmas 2/5/8). Two components per op are
// bridged separately:
//   * VALUE (`.0`): `wrap(exact)` — this is the SAME wrapped-BinOp value
//     `semIntBinOp` already computes, so the agreement theorem is a genuine
//     COMPOSITION (`Eq.trans` with `add_reduces`/`sub_reduces`/`mul_reduces`),
//     not an independently re-proven fact. Bridged for all 6 (op × signedness)
//     combinations: unsigned/signed × Add/Sub/Mul (signed evaluates the
//     already-proven reduction lemma at the `toSigned` operands — reuse, not
//     restatement).
//   * OVERFLOW FLAG (`.1`): the imported semantics computes it as `exact ≥
//     half || exact < -half` (signed) / `exact ≥ modulus || exact < 0`
//     (unsigned) — trust-ir's OWN spelling of the threshold. The safety-VC
//     tier's Lemmas state the mathematically-equivalent but differently-
//     spelled threshold (Lemma 2 unsigned-add: `(2^w-1) < a+b`; Lemma 5
//     signed add/sub/mul: `a∘b < -2^(w-1) ∨ (2^(w-1)-1) < a∘b`; Lemma 8
//     unsigned-sub: `(a-b) < 0`). Bridged in TWO steps per op: a `reduces`
//     PIN (rfl, trust-ir's own `≥`/`<` spelling, kernel-pinning the exact
//     computed Bool) and a `bridge_*_flag` CONNECT (the further identity to
//     the Lemma's textbook spelling, via the shared `overflow_threshold_*`
//     shift lemmas — a genuine arithmetic fact, `a ≥ b ↔ (b-1) < a` for `Int`,
//     proven from imported Lean-core `Int.lt_iff_add_one_le` +
//     `Int.sub_add_cancel` + `decide_eq_decide`, NOT assumed). All six generic
//     Int flags bridge: unsigned-Add (Lemma 2), unsigned-Sub (Lemma 8, with
//     its existing residue guard), unsigned-Mul (#53), and signed Add/Sub/Mul.
//     Unsigned-Mul additionally connects all four actual registered production
//     Int predicates through their ONE shared constructor. The separate BV
//     predicates are not proved equivalent. Foundational footprints are reported;
//     empty axiom residue means no non-foundational axioms, not no axioms.
//   * A NOTATIONAL SUBTLETY DISCOVERED HERE (real finding, like the
//     `Int.sub (Int.ofNat 0) ·` one for `Neg`): a bare `decide` identifier is
//     NOT resolvable by clean's elaborator when writing NEW source against
//     the imported environment (it resolves to an unbound auto-implicit
//     rather than `Decidable.decide`) — the FULLY QUALIFIED `Decidable.decide`
//     must be used in all overflow-flag sources below. Likewise, re-stating
//     the imported semantics' own `binrel%`-elaborated `exact ≥ half || …`
//     term VERBATIM (unqualified `≥`/`<` directly coerced to `Bool`) hits a
//     `Coe`/universe-level mismatch in clean's elaborator; wrapping each
//     comparison in `Decidable.decide` sidesteps it while remaining
//     definitionally identical to what the imported `.olean` term reduces to
//     (confirmed by the `rfl` reduction pins below).
//
// EXTENSION 3 (this increment): `TrustIr.semICmp` — the INTEGER-COMPARISON
// semantics (the pure `Int × Int → Bool` predicate underlying every branch
// guard, every `CondBr` discriminant, and every safety-VC threshold
// condition): `Eq`/`Ne`/`Ult`/`Ule`/`Ugt`/`Uge` (unsigned + sign-independent)
// and `Slt`/`Sle`/`Sgt`/`Sge` (signed). UNLIKE the BinOp/UnOp/OverflowOp
// increments, `ICmpOp` and `semICmp` are declared in NEW Lean modules
// (`TrustIr/CmpOp.lean` + `TrustIr/Semantics/Compare.lean`) that were NOT in
// the old bridge closure (whose root was `TrustIr.Semantics.Arith`).
// `Compare.lean` imports `Arith` (not the reverse), so this increment
// RETARGETS [`BRIDGE_ROOT_MODULE`] to `TrustIr.Semantics.Compare`: its
// transitive closure is Arith's whole closure UNION `{CmpOp, Compare}` (a
// strict superset — 11 TrustIr modules vs. the previous 9 — at the SAME
// trust-ir pin `26379f8`), and the vendored oleans + MANIFEST.toml were
// REGENERATED with `scripts/regen-trustir-oleans.sh --write` to add exactly
// the two new TrustIr modules (the Lean-core closure was already a superset —
// `Arith` already pulled in `Int.Order`/`Int.decLt`/`Int.decLe`/`Int.decEq`,
// so no new Lean-core olean was needed).
//
// WHAT IS PROVEN, PER ARM — all 10, each an UNCONDITIONAL `rfl` agreement
// (`semICmp` is a TOTAL Bool-valued comparison; there is no wrap layer and no
// UB guard, so no side condition is ever needed — this is the ONLY increment
// with no form-(b) arm):
//   * UNSIGNED (`Ult`/`Ule`/`Ugt`/`Uge`): the raw operands are ALREADY in
//     `[0, 2^w)` (they are the machine values), so the raw `Int` comparison IS
//     the denotation. `Ult`/`Ule` agree with Clean's `Int.lt`/`Int.le`
//     directly (`carrier_to_kernel`: `PROP_LT → "Int.lt"`, `PROP_LE →
//     "Int.le"`, `clean_ground.rs:133-135`); `Ugt`/`Uge` agree with the SAME
//     relations ARG-SWAPPED, matching Clean's `Gt a b ≡ Int.lt b a` / `Ge a b
//     ≡ Int.le b a` (`clean_ground.rs:2377-2385`, the `to_clean_expr` /
//     `ground_bool` swap).
//   * SIGN-INDEPENDENT (`Eq`/`Ne`): `Eq` agrees with `Decidable.decide (l = r)`
//     — Clean's `@Eq Int` equality denotation under `decide` (the `PROP_EQ`
//     carrier, `clean_ground.rs:2403-2411`); trust-ir's own `lhs == rhs` IS
//     `decide (l = r)` (Lean-core has no dedicated `Int` `BEq`; the generic
//     `instance [DecidableEq α] : BEq α := decide ∘ Eq` at `Int.decEq`).
//     `Ne` agrees with its negation `Bool.not (Decidable.decide (l = r))` —
//     byte-identical to `ground_bool`'s `Not (Eq …)` → `Bool.not (Int.beq …)`
//     shape.
//   * SIGNED (`Slt`/`Sle`/`Sgt`/`Sge`): Clean has NO separate "signed"
//     comparison primitive — it has ONE mathematical-`Int` order (`Int.lt`/
//     `Int.le`). The faithful bridge is that primitive evaluated at the
//     operands' SIGNED value, i.e. the `TrustIr.toSigned` image — EXACTLY the
//     established precedent of the semIntBinOp bridge's `SDiv`/`SRem`/`AShr`
//     arms, which feed `toSigned` images to Lean-core `Int.div`/`Int.mod`/
//     `Int.fdiv` (the same primitives Clean's own signed grounding uses). So
//     `Slt`/`Sle` agree with `Int.lt`/`Int.le` at `(toSigned l w, toSigned r
//     w)`, and `Sgt`/`Sge` with the arg-SWAPPED form — a GENUINE agreement
//     with Clean's one comparison denotation at the right operand values, NOT
//     a re-statement of trust-ir's own `def`. Because this is a real
//     agreement, there is NO honestly-un-bridged ICmp residue (contrast
//     `UnOp::CtPop`): all 10 arms bridge.
//   * SAME NOTATIONAL SUBTLETY as EXTENSION 2: a bare `decide` is unresolvable
//     in clean's elaborator against the imported env; every ICmp arm below
//     uses the FULLY QUALIFIED `Decidable.decide`, def-eq to what the compiled
//     `semICmp` olean term reduces to (confirmed by the real Lean-toolchain
//     probe harness — all 10 arms `rfl`, all 3 forgeries kernel-REJECTED).
//
// EXTENSION 4 (this increment): `TrustIr.semCast` — the INTEGER-CAST value
// semantics (`Trunc`/`ZExt`/`SExt`, the width-conversion instructions behind
// every MIR numeric coercion, including the field-read+cast leaf). `semCast`
// is declared `Sem ValueId` — MONADIC (it threads `MachineState` via
// `Sem.lookupValue`/`Sem.bindFresh`), UNLIKE every prior bridged function
// (`semIntBinOp`/`semIntUnOp`/`semOverflowOp`/`semICmp`, all plain `Except`
// functions with no state) — but its three integer arms each compute via a
// PURE VALUE CORE: `Trunc`/`ZExt` both reduce to `TrustIr.truncateUnsigned v
// dstW` (zero-extension of an already-unsigned value IS truncation to a wider
// modulus); `SExt` reduces to the wrap-of-`toSigned` expression
// `((toSigned v srcW % 2^dstW) + 2^dstW) % 2^dstW`. `CastOp`/`semCast` live in
// the NEW `TrustIr/CastOp.lean` + `TrustIr/Semantics/Cast.lean` modules.
// UNLIKE the semICmp retarget (where `Compare` strictly imports `Arith`),
// `Cast` and `Compare` import EACH OTHER's dependency (`Arith`) but NOT each
// other, so no single-root retarget covers both — [`BRIDGE_ROOT_MODULES`]
// (new) is the UNION-closure root SET `[Compare, Cast]`, loaded via
// `clean_olean::load_modules_with_deps` (see the const's doc comment).
//
// WHY THE ARMS ARE CONCRETE-STATE, NOT FULLY PARAMETRIC (a real finding, like
// the `Int.sub (Int.ofNat 0) ·` / bare-`decide` subtleties documented above):
// bridging `semCast` means literally RUNNING it (`TrustIr.Sem.run (semCast
// …) state`), which requires a concrete `ValueId`/`Ty`/`MachineState` shape —
// `Sem.lookupValue` looks the operand up via `ValueMap.get`, whose `==` check
// (`instBEqOfDecidableEq` on `ValueId`, i.e. `Nat` structural equality) is
// STUCK (cannot reduce via `rfl`) for a fully free/symbolic `ValueId`, exactly
// the same class of "free-variable-blocks-iota-reduction" issue as the
// `Int.sub 0 x` non-reduction noted for `UnOp::Neg`. The FIX (confirmed
// against the real Lean-toolchain probe harness): pin `ValueId`/`Ty`/the
// `MachineState` SHAPE to literals (so every constructor match is on a known
// tag) while leaving the operand's INTEGER PAYLOAD `v : Int` and the
// `MachineState`'s OTHER fields fully SYMBOLIC — `Value.int _ v` for a free
// `v` never needs to pattern-match `v`'s own shape, only Int arithmetic
// (`%`, `+`), which is exactly what the whole file already relies on
// elsewhere. So each arm below is `∀ (v : Int), …` — a genuine per-VALUE
// universal statement, at one representative concrete width pair, NOT a
// single numeric pin (that weaker form is used only for the extra anchor
// rows in [`CAST_CONC_SRC`]).
//
// TIER 2 — CONNECTING COROLLARIES to the ACTUAL existing Clean-side cast
// model: unlike BinOp/UnOp/ICmp (which bridge against `clean_ground.rs`'s
// live grounder) there is currently NO `clean_ground.rs`/`trustir_anchor.rs`
// Formula/Expr denotation for ANY `CastOp` variant — grepping both files
// for Cast/Trunc/ZExt/SExt finds nothing (confirmed). The one REAL
// Clean-side cast model in this repo is `mirsem.rs::resolve_widening_cast_rvalue`
// (the "trust-ir Field/Cast straight-line denotation" task, commit
// `5f110a5e77`): a WIDENING (`dst_width ≥ src_width`), SAME-SIGNEDNESS
// integer cast is modeled as the IDENTITY on Trust's unbounded-`Int` MIR
// value carrier — "zero-/sign-extension changes representation, not value".
// [`bridge_cast_zext_widening_identity`] is a GENUINE connecting corollary
// proving that claim TRUE against trust-ir's real pure core: `ZExt`
// (unsigned) preserves the value directly (`truncateUnsigned v dstW = v`
// whenever `v` already fits `[0, 2^dstW)`, `Int.emod_eq_of_lt`) — pure `Int`
// arithmetic (no monad), so — unlike the arms — it IS fully parametric over
// widths. The analogous SExt corollary (sign-extension preserves the SIGNED
// value via an encode/decode round-trip) is mathematically real and was
// fully proven against a genuine Lean 4.8.0 toolchain, but is NOT delivered
// here: it needs one extra fact (`(0:Int) < (2:Int)^n` for symbolic `n`) that
// hits a confirmed, reproducible clean-elaborator limitation (`Int.le`/
// `Int.NonNeg`'s definitional-equality checker does not fully normalize
// `Int.sub` on a symbolic `HPow.hPow` term consistently — see the doc
// comment directly above `CAST_COMPOSED_SRC` below for the full finding).
// Reported honestly rather than faked or silently dropped.
//
// HONEST RESIDUE: the 14 non-integer `CastOp` variants (`FPTrunc`/`FPExt`/
// `FPToUI`/`FPToSI`/`UIToFP`/`SIToFP`/`FPToSISat`/`FPToUISat` plus the
// pointer/closure operations;
// `PtrToInt`/`IntToPtr`/`Bitcast`/`PtrToPtr`/`Transmute`/`ReifyFnPointer` —
// pointer/closure reinterpretation with no Clean denotation to agree
// against) are surfaced honestly as un-bridged (see [`CAST_UNBRIDGED`]),
// exactly like `UnOp::CtPop`. Never faked.
//
// EXTENSION 5 (this increment) — THE STATEMENT-LEVEL BREAKTHROUGH: `TrustIr.
// stepInst`, the FIRST bridged INSTRUCTION (not operation-VALUE) agreement.
// Every prior extension bridged an operation's pure or monadic VALUE
// (`semIntBinOp`/`semIntUnOp`/`semOverflowOp`/`semICmp`/`semCast`); this one
// bridges `stepInst`'s `.BinOp op ty lhs rhs` ARM — the monadic dispatch that
// (1) READS both operand `ValueId`s out of `MachineState` via
// `Sem.lookupValue`, (2) COMPUTES `semBinOp`'s `.int` branch (which for two
// `Value.int` operands of equal width is exactly the ALREADY-BRIDGED
// `semIntBinOp`), and (3) WRITES the fresh result back via `Sem.bindFresh`,
// finally returning `InstrResult.value (some freshId)`. `stepInst` lives in
// the NEW `TrustIr/Semantics/Step.lean` module — [`BRIDGE_ROOT_MODULES`] is
// extended to `[Compare, Cast, Step]` (Step's own closure is a STRICT
// SUPERSET of the prior union: it imports Arith/Compare/Cast plus Control/
// Memory/Borrow/ARC/Atomic/Aggregate/Call/Frame/Coroutine, needed just to
// TYPECHECK the one big `stepInst` `match` over all 57 `Inst` variants, even
// though only the `.BinOp` arm is bridged here) — 26 TrustIr modules total
// (up from 13), vendored via `scripts/regen-trustir-oleans.sh --write`; the
// Lean-core Init closure is UNCHANGED (158 oleans, byte-identical — `Arith`
// already pulled in the same Init cone).
//
// THE TECHNIQUE (generalizes semCast's "concrete-state, symbolic-payload"
// monadic bridge from ONE operand to TWO plus explicit read→compute→write
// THREADING): each arm literally runs `TrustIr.Sem.run (TrustIr.stepInst
// (.BinOp op ty lhsId rhsId)) state` at a CONCRETE `ValueId`/`Ty`/
// `MachineState` shape — `lhsId = ValueId.mk 0`, `rhsId = ValueId.mk 1`, both
// bound in `state.locals` to `Value.int 8 v_l` / `Value.int 8 v_r` for FULLY
// SYMBOLIC `v_l v_r : Int` (width pinned to a literal `8`, exactly like
// semCast's pinned widths, so the `w1 != w2` / `ValueId ==` equality checks
// inside `semBinOp`/`ValueMap.get` are never stuck on a free variable) —
// pinning the otherwise-stuck free-variable state while leaving the
// operands' integer PAYLOADS fully symbolic. The proof-only transport first
// splits the actual Except result, preserving failure and the full fresh-SSA
// state. A generic chain theorem then connects the imported stepInst/semBinOp
// dispatch to that transport, requiring op.isMinMax = false. Each operation's
// connect theorem consumes its existing ARMS value proof; no arithmetic is
// reimplemented by the instruction bridge.
//
// Seven arms are composed: Add/Sub/Mul/UDiv/SDiv/URem/SRem. The division and
// remainder theorems retain the exact value-layer nonzero and signed-overflow
// guards, as well as the existing nonnegative/in-range result premises.
// Signed results outside those premises are not newly covered. Width remains
// the concrete I8 fixture; this does not prove every integer width or state.
// The composed bridge_stepInst_binop_agreement_all conjoins all seven.
//
// ANTI-FORGERY: (1) wrong-op-agreement — `stepInst`'s `.BinOp .Add` chain
// claimed to agree with `semIntBinOp .Sub` instead of `.Add` (a same-shape
// swap of the op fed to the `match`, the direct analogue of [`FORGERY_
// PROBES`]'s `Add`-agrees-with-`Int.sub`); (2) swapped-operand — `.Sub`'s
// connect theorem claimed to bind `Int.sub v_r v_l` (operands SWAPPED)
// instead of `Int.sub v_l v_r`, which matters precisely because `Sub` is
// non-commutative (unlike `Add`, where a swap would be vacuously equal) —
// this is the READ-side analogue of the ICmp bridge's signed/unsigned
// confusion probe. Both confirmed kernel-REJECTED for symbolic `v_l`/`v_r`
// against a real Lean 4.8.0 toolchain before being pinned here.
//
// HONEST RESIDUE, stated precisely (never silently dropped):
//   * 15 other `semIntBinOp` ops reachable through this SAME `stepInst`
//     `.BinOp` arm (`UDiv`/`SDiv`/`URem`/`SRem`/`FAdd`/`FSub`/`FMul`/`FDiv`/
//     `FRem`/`And`/`Or`/`Xor`/`Shl`/`LShr`/`AShr`) are bridged at the VALUE
//     level ([`ARMS`]) but NOT yet chained through `stepInst`: the identical
//     chain+connect technique demonstrated here generalizes directly (reuse
//     the corresponding `bridge_*` arm exactly as `Sub`/`Mul` reuse
//     `bridge_sub`/`bridge_mul`) — named as concrete next work, not faked.
//   * The other 56 (of 57) `Inst` variants' `stepInst` arms (`UnOp`,
//     `Overflow`, `ICmp`, `FCmp`, `Cast`, and every non-arithmetic
//     instruction — constants, control-flow terminators, memory, atomics,
//     aggregates, borrow/ARC, binding frames, coroutine suspend, calls,
//     exception handling, dialect ops) are NOT bridged at the stepInst
//     level. For `UnOp`/`Overflow`/`ICmp`/`Cast` the underlying VALUE
//     semantics IS already bridged (see the respective extensions above);
//     only the monadic read→compute→write chain itself remains. The other
//     51 variants have no value-level bridge at all yet (many — `Load`/
//     `Store`/`Call`/ARC/coroutine — read and write `MachineState` fields
//     entirely outside the scalar-arithmetic cone this bridge covers).
//     `evalBody`/`evalCfg` (the multi-instruction / control-flow / loop
//     layer above `stepInst`) remain entirely unbridged.
//
// EXTENSION 7 (this increment) — THE CONTROL-FLOW BREAKTHROUGH: `TrustIr.
// stepN`'s `.CondBr` terminator dispatch + `.Continue` RECURSIVE case — the
// FIRST BRANCHING whole-body agreement. Every prior extension (including
// EXTENSION 6's stepblock) exercised only stepN's `.Ret` BASE case (fuel = 1,
// no recursion); this bridges the case the straight-line proof never
// touched: a real 2-target `CondBr`, `semCondBr`'s bool-guard dispatch, and
// stepN's `fuel > 1` recursive re-entry into a SECOND block.
//
// SCOPE: the smallest real branching body, `if _0 { return _1 } else {
// return _2 }`, as a fixed 3-block CFG (`bb0`: params `[_0:Bool, _1:I8,
// _2:I8]`, terminator `CondBr _0 bb1 [_1] bb2 [_2]`; `bb1`: param `[x:I8]`,
// terminator `Return [x]`; `bb2`: param `[y:I8]`, terminator `Return [y]`),
// at `fuel = 2` (stepN's outer call handles bb0's CondBr and its
// `.Continue` recursion into the chosen target block; the recursive call
// handles that block's `Return` at `fuel = 1`, the already-proven stepblock
// base case). `TrustIr.Semantics.Control` (`semBr`/`semCondBr`/`semReturn`/
// `StepResult`) is ALREADY part of the vendored closure (`Step` imports
// `Control` directly, and `Eval` imports `Step`) — [`BRIDGE_ROOT_MODULES`]
// needs NO further change; `MANIFEST.toml` already lists
// `TrustIr/Semantics/Control.olean`. Verified: no regen was needed.
//
// THE TECHNIQUE: unlike every arithmetic extension, this fragment has no
// wrap/overflow side condition and no previously-proven VALUE lemma to
// reuse via `Eq.trans` — the guard is pinned to a CONCRETE `Value.bool
// true`/`false` literal (not symbolic), so the entire `bindBlockParams ->
// stepInst (CondBr) -> semCondBr's bool match -> StepResult.Continue ->
// stepN's recursive re-entry -> bindBlockParams -> stepInst (Return) ->
// semReturn` computation reduces by a single unconditional `rfl` — no
// operand ever needs its OWN shape inspected, only the (concrete) guard's.
// Two theorems per path, mirroring the chain+connect shape one level up:
//   * `stepN_branch_<true|false>_chain` — the unconditional `rfl` outer
//     factoring, whose RHS is stated in the exact `Bool.rec (fun _ => Int)
//     elseVal thenVal cond` SHAPE `clean_ground.rs`'s `ground_int` `F::Ite`
//     arm emits for a guarded return (`Bool.rec`'s minor-premise order is
//     (false, true), matching `eval_ite`'s reduct exactly) — so the chain
//     theorem ties the raw evaluator reduction to Clean's Ite/guarded-return
//     grounding SHAPE, not merely to a bare returned value.
//   * `bridge_stepN_branch_<true|false>` — composes the chain with a tiny
//     proven `bool_rec_true`/`bool_rec_false` iota-reduction lemma (`Bool.rec
//     (fun _ => Int) e t true = t` / `... false = e`, each itself an
//     unconditional `rfl`) via `Eq.trans`/`congrArg`, landing on the taken
//     branch's concrete payload (`Value.int 8 a` / `Value.int 8 b`).
//
// This is the Clean analogue of `guarded_return_formula`/
// `nested_guarded_return_formula` (`clean_ground.rs`) and `IrCfg::
// inlined_return_formula` (`trustir_anchor.rs`, whose `Switch` arm builds
// EXACTLY this `Formula::Ite(cond, then_f, else_f)` for a 2-way branch) —
// the trust-ir CFG evaluator agreeing with the SAME `Ite`/`Bool.rec` shape
// those Rust-side denotations already commit to.
//
// COMPOSED `bridge_stepN_branch_agreement_all` (true ∧ false), axiom_deps
// ∅. ANTI-FORGERY: (1) true-guard claimed to yield the ELSE value `b`
// instead of `a`; (2) false-guard claimed to yield the THEN value `a`
// instead of `b` — both kernel-REJECTED for symbolic `a b : Int`.
//
// HONEST RESIDUE: `Switch` (N-way branch); nested/chained CondBrs (the
// `nested_guarded_return_formula` multi-`Ite` shape); loops (any cfg with a
// back-edge); non-empty bodies on either arm (composing this technique with
// EXTENSION 6's fold-over-body one); the `.int _ v` nonzero-as-true guard
// arm of `semCondBr` (only the `.bool` guard is bridged); the
// interprocedural evaluator (`stepNWithContext`).
//
// EXTENSION 8 (this increment) — THE BRANCH-ARM COMPUTES: closing EXTENSION
// 7's own named residue ("non-empty bodies on either arm") by COMPOSING
// EXTENSION 7's control-flow technique (CondBr dispatch + stepN's
// `.Continue` recursive re-entry) with EXTENSION 6's body-fold technique
// (fold `stepInst` over a block's body before its terminator) — a pure
// composition of two already-proven pieces, no new evaluator case is
// exercised. SCOPE: `if _0 { return _1 + _2 } else { return _1 - _2 }` — the
// smallest branching body where EACH arm actually COMPUTES (rather than
// merely returning a bare parameter, as EXTENSION 7's fixture did): a fixed
// 3-block CFG (`bb0`: params `[_0:Bool, _1:I8, _2:I8]`, terminator `CondBr
// _0 bb1 [_1,_2] bb2 [_1,_2]`; `bb1`: params `[x,y:I8]`, body `[BinOp Add I8
// x y]`, terminator `Return [<Add's dest>]`; `bb2`: params `[x,y:I8]`, body
// `[BinOp Sub I8 x y]`, terminator `Return [<Sub's dest>]`), at `fuel = 2`.
//
// THE TECHNIQUE: because BOTH arms' block params are declared AFTER `bb0`'s
// own 3 params consume `ValueId.mk 0/1/2` (`bindBlockParams`'s `nextValueId`
// counter is a single value threaded across the WHOLE CFG, not reset per
// block — confirmed against `TrustIr/Semantics/Eval.lean`'s `bindBlockParams`
// directly), the taken arm's `BinOp` instruction necessarily operates on
// `ValueId.mk 3/4` (`bb1`) or `mk 5/6` (`bb2`) — NEVER `mk 0/1`, the exact
// ids `bridge_stepInst_binop_add`/`bridge_stepInst_binop_sub` (EXTENSION 5)
// are pinned to at a PRISTINE 2-entry `MachineState`. So, unlike EXTENSION
// 6's `stepblock_add_return_outer_chain` (whose fixture was built so its
// block's OWN params literally ARE `mk 0/1`, letting it reuse
// `bridge_stepInst_binop_add` as a literal congrArg/Eq.trans term), that
// EXACT term-level reuse is not available one layer up through a real
// CondBr dispatch (the accumulated locals/nextValueId are provably
// different from that pinned fixture's). Instead, each arm's CHAIN theorem
// (`stepN_branch_body_<true|false>_chain`, an unconditional `rfl` — the
// whole `bindBlockParams -> stepInst (CondBr) -> semCondBr ->
// StepResult.Continue -> stepN's recursive re-entry -> bindBlockParams ->
// fold stepInst over the 1-instruction body -> stepInst (Return)` reduction,
// generic in the already-bridged `semIntBinOp`, exactly mirroring
// EXTENSION 5's `stepinst_binop_<op>_chain` shape one level up) is composed
// via `Eq.trans`/`congrArg` DIRECTLY with `bridge_add`/`bridge_sub` (the
// VALUE-level arm from [`ARMS`], reused here exactly as EXTENSION 5 itself
// reused them, at one further remove) — landing on `Int.add a b` /
// `Int.sub a b`, the SAME `Int.add`/`Int.sub` head `clean_ground.rs`'s
// `ground_int` grounds `F::Add`/`F::Sub` to. Under `Bool.rec (fun _ => Int)
// (g else_) (g then_) (ground_bool cond)` (`ground_int`'s `F::Ite` arm) with
// a CONCRETE `cond`, `g then_ = Int.add (g _1) (g _2)` / `g else_ = Int.sub
// (g _1) (g _2)` when the taken arm is itself an `F::Add`/`F::Sub` — so the
// value each connect theorem lands on IS Clean's guarded-return-WITH-
// COMPUTATION denotation for the taken branch (the `Bool.rec` iota-reduces
// to exactly that arm regardless of the untaken one, so no `Bool.rec` term
// needs to appear in our own statement for the value-level agreement to
// hold; the already-proven `bool_rec_true`/`bool_rec_false` iota lemmas
// from EXTENSION 7 remain available in-environment for anyone composing
// further toward the literal `Bool.rec`-wrapped `Formula::Ite` shape).
//
// SPOT-MODE ASYMMETRY (matches EXTENSION 5's own precedent): `bridge_sub`
// is only loaded when [`ARMS`]' full set runs (Spot mode's arm_set is
// `[Add, FAdd, UDiv]` — `Sub` is absent), so the FALSE (Sub) arm is only
// attempted in Full mode; Spot mode attempts the TRUE (Add) arm only,
// exactly as EXTENSION 5's own `STEPINST_BINOP_ARMS` Spot slice is `Add`
// only for the identical reason.
//
// COMPOSED `bridge_stepN_branch_body_agreement_all` (true ∧ false, Full
// mode only — needs both arms). ANTI-FORGERY: (1) true-arm claimed to
// compute the ELSE arm's `Int.sub a b` instead of `Int.add a b`; (2)
// false-arm claimed to compute the THEN arm's `Int.add a b` instead of
// `Int.sub a b` — both kernel-REJECTED for symbolic `a b : Int`.
//
// HONEST RESIDUE: `Switch`; nested/chained CondBrs; loops; the `.int _ v`
// nonzero-as-true guard arm of `semCondBr`; the interprocedural evaluator
// (`stepNWithContext`) — all unchanged from EXTENSION 7. NEW residue this
// increment: multi-instruction arm bodies (>1 instruction before an arm's
// `Return` — the SAME fold technique composes one more `Except.bind`, not
// executed); asymmetric arm shapes (one arm computing, the other a bare
// `Return` of a parameter, or arms with a differing instruction count —
// only the SYMMETRIC both-arms-compute-one-BinOp shape was executed); arm
// bodies built from a non-`BinOp` instruction (`UnOp`/`ICmp`/`Cast`/
// `Overflow` before an arm's `Return` — only `BinOp` bodies were composed
// here, though the identical fold technique generalizes to any
// already-bridged `stepInst` category).
//
// EXTENSION 9 (this increment) — INSTRUCTION-EXECUTION BREADTH: closing
// EXTENSION 5's own named residue ("the other 56 (of 57) `Inst` variants ...
// For `UnOp`/`Overflow`/`ICmp`/`Cast` the underlying VALUE semantics IS
// already bridged ... only the monadic read->compute->write chain itself
// remains") for the 4 categories whose VALUE core the bridge already proves:
// `stepInst`'s `.UnOp`, `.Overflow`, `.ICmp`, and `.Cast` arms, one
// representative op each (`Neg`, unsigned `AddOverflow`, `Ult`, `Trunc`) —
// the SAME chain+connect technique EXTENSION 5 demonstrated for `.BinOp`,
// applied to every OTHER value-bridged instruction category. No new
// `TrustIr` module is needed: `Step.lean`'s `stepInst` already dispatches
// `.UnOp op ty operand => semUnOp op ty operand`, `.Overflow op ty lhs rhs =>
// semOverflow op ty lhs rhs`, `.ICmp op ty lhs rhs => semICmpInst op ty lhs
// rhs`, and `.Cast op srcTy dstTy operand => semCast op srcTy dstTy operand`
// — all four dispatch targets live in `Arith.lean`/`Compare.lean`/`Cast.lean`,
// already inside the vendored `Step`/`Eval` closure; [`BRIDGE_ROOT_MODULES`]
// is UNCHANGED.
//
// PER CATEGORY:
//   * `.UnOp` (`Neg`) — `semUnOp` unwraps the looked-up operand's `.int w v`
//     shape then calls the ALREADY-BRIDGED `semIntUnOp`; the chain+connect
//     pair composes with `bridge_neg` (EXTENSION 1) exactly as EXTENSION 5
//     composed with `bridge_add`, PLUS a second connect corollary composing
//     with `bridge_neg_sub_zero_form` (the `Int.sub (Int.ofNat 0) operand`
//     spelling) — both reused, neither re-proven.
//   * `.Overflow` (unsigned `AddOverflow`) — `semOverflow` binds TWO
//     fresh SSA values, the wrapped integer then the boolean overflow flag,
//     and `stepInst` returns their ordered identities in `InstrResult.values`.
//     The state advances `nextValueId` twice (TrustIR WS2.24). The connect
//     composes with the ALREADY-PROVEN `bridge_overflow_uadd_flag`
//     (EXTENSION 2's unconditional full-pair arm), retaining both separate
//     bindings and the complete resulting machine state. The integer binding
//     is the same wrapped-add formula established by
//     `bridge_overflow_uadd_value`; there is no packed aggregate convention.
//   * `.ICmp` (`Ult`) — `semICmpInst` binds a fresh `ValueId` to `Value.bool
//     (semICmp op w l r)`; `semICmp` is TOTAL (a `Bool`, not `Except`), so
//     the connect is a direct `congrArg` over `Bool` (no `Except`-match
//     dispatch needed) composed with the ALREADY-PROVEN `bridge_icmp_ult`
//     (EXTENSION 3), landing on `Value.bool (Decidable.decide (Int.lt l r))`.
//   * `.Cast` (`Trunc`) — `stepInst`'s `.Cast` arm calls `semCast` DIRECTLY
//     (no intermediate wrapper, unlike the other three categories); the
//     chain therefore collapses stepInst's OWN monadic layer with `semCast`'s
//     (both `Sem ValueId`-shaped) in one `Sem.run_bind`/`Sem.run_pure`
//     reduction, then the connect composes with the ALREADY-PROVEN
//     `bridge_cast_trunc` (EXTENSION 4) — the same monadic technique EXTENSION
//     4 itself introduced, now demonstrated to compose ACROSS a further
//     `stepInst` dispatch layer rather than stopping at `semCast` alone.
//
// COMPOSED theorem per category (`bridge_stepInst_unop_agreement_all` — Neg ∧
// its sub-zero corollary; `bridge_stepInst_overflow_agreement_all`,
// `bridge_stepInst_icmp_agreement_all`, `bridge_stepInst_cast_agreement_all`
// — each restating its one proven arm under a category-level name) PLUS one
// overall `bridge_stepInst_categories_agreement_all` conjoining all 4
// categories' primary connect theorems, axiom_deps = ∅ throughout.
//
// ANTI-FORGERY, 2 per category (8 total), every one a genuine distinct claim
// kernel-REJECTED for symbolic operands: UnOp — wrong-op-agreement (Neg vs
// Not) + dropped-negation (claims the untouched operand); Overflow —
// wrong-op-agreement (AddOverflow vs SubOverflow) + wrong-threshold (the
// signed half-width threshold used for an unsigned check, EXTENSION 2's own
// precedent lifted one layer); ICmp — wrong-relation (Ult vs Ugt) +
// swapped-operand (`Int.lt r l` instead of `Int.lt l r`); Cast —
// wrong-destination-width (`truncateUnsigned v 16`, srcW, instead of `v 8`,
// dstW — EXTENSION 4's own precedent lifted one layer) + dropped-truncation
// (claims the untouched operand).
//
// HONEST RESIDUE: within each of these 4 categories, only the ONE named op is
// stepInst-chained; the OTHER value-bridged ops in the SAME category (UnOp's
// `Not`/`FNeg`; Overflow's other 5 of 6 op×signedness combos; ICmp's other 9
// comparison arms; Cast's `ZExt`/`SExt`) are honestly reported as un-chained
// — the identical technique generalizes, but was not executed for them (the
// SAME discipline [`STEPINST_BINOP_UNBRIDGED`] already applies to BinOp's
// other 11 ops). Beyond these 5 categories: `FCmp` has no VALUE-level bridge
// yet (so no chain is possible for it); the other 51 `Inst` variants remain
// entirely unbridged, as before; `evalBody`/`evalCfg`'s WHOLE-PROGRAM
// evaluator (beyond the concrete single-block/branch/loop fixtures EXTENSIONS
// 6-9 above already cover) remains open.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;
use std::sync::Mutex;
use std::time::Instant;

use clean_kernel::{Environment, Name, TypeChecker};

mod unsigned_mul;
use clean_olean::replay_census::{replay_declaration_census, DeclarationReplayVerdict};
use clean_olean::verify_batch_full::typecheck_constants_full;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

// One root set drives bridge replay and the lightweight regeneration utility.
pub use trust_bridge_closure::{BRIDGE_ROOT_MODULE, BRIDGE_ROOT_MODULES};

mod runtime_frontier;
pub use runtime_frontier::RuntimeFrontier;

/// Manifest schema ids (versioned, one per vendored tree).
// v2 partitions the file table by build platform (see `ManifestDoc`). The
// version is matched EXACTLY, not as a minimum: a v1 manifest has a single
// flat `[files]` table with no platform dimension, so reading one here would
// silently verify another platform's bytes as if they were ours.
pub const TRUSTIR_MANIFEST_SCHEMA: &str = "trust.trust-clean.trustir-oleans.manifest.v2";
pub const LEAN_CORE_MANIFEST_SCHEMA: &str = "trust.vendor.lean-core-oleans.manifest.v2";

// ---------------------------------------------------------------------------
// Lean sources elaborated by clean against the IMPORTED constants.
// Ported from the stage-2 bridge-assembly driver (the winning spellings only;
// reports/bridge-assembly-11arms-2026-07-02.md §§1-2). Arithmetic sides are in
// FUNCTION form (`Int.add l r`, not `l + r`): it is the exact constant the
// live grounder emits (`clean_ground.rs`), and it is the Lean-faithful
// spelling clean's elaborator handles uniformly.
// ---------------------------------------------------------------------------

/// Checked source instance aliases for this bridge's integer arithmetic/order,
/// natural width subtraction, numeric literals, and integer/Bool/Ty equality.
/// Every value is the exact instance term synthesized by the vendored Lean 4.8
/// artifacts. Carrier class metadata must come from the manifest-verified
/// imported closure; redeclaring a restored class correctly refuses. This
/// bounded notation setup does not qualify generic Lean-v1 class/instance
/// extension decoding.
///
/// Retain the source's reducibility declarations and checked aliases:
/// `GE.ge` and `GT.gt` are `@[reducible]` defs in
/// `Init/Prelude.lean`, and `Int.instLEInt`/`Int.instLTInt` are `instance`
/// defs, which Lean makes reducible. Clean's instance search and `rw`'s
/// closing `rfl` run at Lean's `.instances`/reducible transparency (Clean G47),
/// so without it `Decidable (half - 1 < exact)` stops at
/// `Int.instLTInt.1 (half - 1) exact`, never reaching `bridgeIntDecLt`, and
/// `decide (x ≥ y)` never meets `decide (y ≤ x)`.
/// Keep decidability available for both canonical `Int.le`/`Int.lt` and the
/// `LE`/`LT` projections and reversed comparison notation: elaboration may
/// retain any of these heads, while the kernel checks the same imported procedure.
const BRIDGE_INSTANCE_SRC: &str = r#"instance bridgeIntLE : LE Int := Int.instLEInt
instance bridgeIntLT : LT Int := Int.instLTInt
attribute [reducible] GE.ge GT.gt Int.instLEInt Int.instLTInt
instance bridgeIntDecLe (a b : Int) : Decidable (Int.le a b) := Int.decLe a b
instance bridgeIntDecLt (a b : Int) : Decidable (Int.lt a b) := Int.decLt a b
instance bridgeIntDecLeNotation (a b : Int) : Decidable (a ≤ b) := Int.decLe a b
instance bridgeIntDecLtNotation (a b : Int) : Decidable (a < b) := Int.decLt a b
instance bridgeIntDecGeNotation (a b : Int) : Decidable (a ≥ b) := Int.decLe b a
instance bridgeIntAdd : HAdd Int Int Int := @instHAdd Int Int.instAdd
instance bridgeIntSub : HSub Int Int Int := @instHSub Int Int.instSub
instance bridgeNatSub : HSub Nat Nat Nat := @instHSub Nat instSubNat
instance bridgeIntMul : HMul Int Int Int := @instHMul Int Int.instMul
instance bridgeIntMod : HMod Int Int Int := @instHMod Int Int.instMod
instance bridgeIntPow : HPow Int Nat Int := Int.instHPowNat
instance bridgeIntNeg : Neg Int := Int.instNegInt
instance bridgeIntOfNat (n : Nat) : OfNat Int n := @instOfNat n
instance bridgeNatOfNat (n : Nat) : OfNat Nat n := instOfNatNat n
instance bridgeIntDecEq (a b : Int) : Decidable (a = b) := Int.instDecidableEq a b
instance bridgeBoolDecEq (a b : Bool) : Decidable (a = b) := instDecidableEqBool a b
instance bridgeIntBEq : BEq Int := @instBEqOfDecidableEq Int Int.instDecidableEq
instance bridgeTyBEq : BEq TrustIr.Ty := TrustIr.instBEqTy
"#;

/// The wrap-elision prelude: `wrap v = v` exactly when `0 ≤ v < m` — the one
/// conditional-rewrite lemma every form-(b) arm composes with. Proven from
/// imported Lean-core `Int.emod_eq_of_lt` / `Int.add_mul_emod_self_left` /
/// `Int.mul_one` by a pure term proof (no tactics).
const PRELUDE_SRC: &str = r#"theorem wrap_eq_self (m v : Int) (h0 : 0 ≤ v) (h1 : v < m) : (v % m + m) % m = v :=
  Eq.trans (congrArg (fun x => (v % m + x) % m) (Eq.symm (Int.mul_one m)))
    (Eq.trans (Int.add_mul_emod_self_left (v % m) m 1)
      (Eq.trans (congrArg (fun x => x % m) (Int.emod_eq_of_lt h0 h1)) (Int.emod_eq_of_lt h0 h1)))
theorem ok_wrap_eq (m v : Int) (h0 : 0 ≤ v) (h1 : v < m) :
    (Except.ok ((v % m + m) % m) : Except TrustIr.SemError Int) = Except.ok v :=
  congrArg Except.ok (wrap_eq_self m v h0 h1)
"#;

/// Reduction lemmas: pure `rfl` over the IMPORTED constant, pinning each
/// unguarded integer arm's definitional behavior in `Int.*` function form.
const REDUCTION_SRCS: &[(&str, &str)] = &[
    (
        "add_reduces",
        r#"theorem add_reduces (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.Add w l r =
      Except.ok ((Int.add l r % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
    (
        "sub_reduces",
        r#"theorem sub_reduces (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.Sub w l r =
      Except.ok ((Int.sub l r % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
    (
        "mul_reduces",
        r#"theorem mul_reduces (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.Mul w l r =
      Except.ok ((Int.mul l r % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
    (
        "and_reduces",
        r#"theorem and_reduces (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.And w l r =
      Except.ok ((Int.land l r % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
    (
        "or_reduces",
        r#"theorem or_reduces (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.Or w l r =
      Except.ok ((Int.lor l r % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
    (
        "xor_reduces",
        r#"theorem xor_reduces (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.Xor w l r =
      Except.ok ((Int.xor l r % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
];

/// The per-op form of an agreement arm (report §1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArmForm {
    /// Plain agreement, no side condition (the float arms).
    A,
    /// Agreement under the no-overflow / in-range side condition.
    B,
    /// Form (b) plus the arm's own UB-guard hypotheses.
    BGuarded,
}

impl ArmForm {
    fn label(self) -> &'static str {
        match self {
            ArmForm::A => "a",
            ArmForm::B => "b",
            ArmForm::BGuarded => "b+guard",
        }
    }
}

/// One agreement arm: `(op, theorem name, form, Lean source)`. Ordered as the
/// 18 arms of `semIntBinOp` itself.
struct ArmSpec {
    op: &'static str,
    theorem: &'static str,
    form: ArmForm,
    src: &'static str,
}

const ARMS: &[ArmSpec] = &[
    ArmSpec {
        op: "Add",
        theorem: "bridge_add",
        form: ArmForm::B,
        src: r#"theorem bridge_add (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.add l r) (h1 : Int.add l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Add w l r = Except.ok (Int.add l r) :=
  Eq.trans (add_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.add l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "Sub",
        theorem: "bridge_sub",
        form: ArmForm::B,
        src: r#"theorem bridge_sub (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.sub l r) (h1 : Int.sub l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Sub w l r = Except.ok (Int.sub l r) :=
  Eq.trans (sub_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.sub l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "Mul",
        theorem: "bridge_mul",
        form: ArmForm::B,
        src: r#"theorem bridge_mul (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.mul l r) (h1 : Int.mul l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Mul w l r = Except.ok (Int.mul l r) :=
  Eq.trans (mul_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.mul l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "UDiv",
        theorem: "bridge_udiv",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_udiv (w : Nat) (l r : Int) (hz : (r == 0) = false)
    (h0 : 0 ≤ Int.ediv l r) (h1 : Int.ediv l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.UDiv w l r = Except.ok (Int.ediv l r) :=
  Eq.trans (if_neg (ne_true_of_eq_false hz)) (ok_wrap_eq ((2 : Int) ^ w) (Int.ediv l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "SDiv",
        theorem: "bridge_sdiv",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_sdiv (w : Nat) (l r : Int) (hz : (r == 0) = false)
    (hmin : ((TrustIr.toSigned l w == -((2 : Int) ^ (w - 1))) && (TrustIr.toSigned r w == -1)) = false)
    (h0 : 0 ≤ Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w))
    (h1 : Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w) < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.SDiv w l r =
      Except.ok (Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w)) :=
  Eq.trans (if_neg (ne_true_of_eq_false hz))
    (Eq.trans (if_neg (ne_true_of_eq_false hmin))
      (ok_wrap_eq ((2 : Int) ^ w) (Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w)) h0 h1))
"#,
    },
    ArmSpec {
        op: "URem",
        theorem: "bridge_urem",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_urem (w : Nat) (l r : Int) (hz : (r == 0) = false)
    (h0 : 0 ≤ Int.emod l r) (h1 : Int.emod l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.URem w l r = Except.ok (Int.emod l r) :=
  Eq.trans (if_neg (ne_true_of_eq_false hz)) (ok_wrap_eq ((2 : Int) ^ w) (Int.emod l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "SRem",
        theorem: "bridge_srem",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_srem (w : Nat) (l r : Int) (hz : (r == 0) = false)
    (hmin : ((TrustIr.toSigned l w == -((2 : Int) ^ (w - 1))) && (TrustIr.toSigned r w == -1)) = false)
    (h0 : 0 ≤ Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w))
    (h1 : Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w) < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.SRem w l r =
      Except.ok (Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w)) :=
  Eq.trans (if_neg (ne_true_of_eq_false hz))
    (Eq.trans (if_neg (ne_true_of_eq_false hmin))
      (ok_wrap_eq ((2 : Int) ^ w) (Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w)) h0 h1))
"#,
    },
    ArmSpec {
        op: "FAdd",
        theorem: "bridge_fadd",
        form: ArmForm::A,
        src: r#"theorem bridge_fadd (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.FAdd w l r =
      Except.error (TrustIr.SemError.typeError "float operation on integer operands") := rfl
"#,
    },
    ArmSpec {
        op: "FSub",
        theorem: "bridge_fsub",
        form: ArmForm::A,
        src: r#"theorem bridge_fsub (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.FSub w l r =
      Except.error (TrustIr.SemError.typeError "float operation on integer operands") := rfl
"#,
    },
    ArmSpec {
        op: "FMul",
        theorem: "bridge_fmul",
        form: ArmForm::A,
        src: r#"theorem bridge_fmul (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.FMul w l r =
      Except.error (TrustIr.SemError.typeError "float operation on integer operands") := rfl
"#,
    },
    ArmSpec {
        op: "FDiv",
        theorem: "bridge_fdiv",
        form: ArmForm::A,
        src: r#"theorem bridge_fdiv (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.FDiv w l r =
      Except.error (TrustIr.SemError.typeError "float operation on integer operands") := rfl
"#,
    },
    ArmSpec {
        op: "FRem",
        theorem: "bridge_frem",
        form: ArmForm::A,
        src: r#"theorem bridge_frem (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.FRem w l r =
      Except.error (TrustIr.SemError.typeError "float operation on integer operands") := rfl
"#,
    },
    ArmSpec {
        op: "And",
        theorem: "bridge_and",
        form: ArmForm::B,
        src: r#"theorem bridge_and (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.land l r) (h1 : Int.land l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.And w l r = Except.ok (Int.land l r) :=
  Eq.trans (and_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.land l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "Or",
        theorem: "bridge_or",
        form: ArmForm::B,
        src: r#"theorem bridge_or (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.lor l r) (h1 : Int.lor l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Or w l r = Except.ok (Int.lor l r) :=
  Eq.trans (or_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.lor l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "Xor",
        theorem: "bridge_xor",
        form: ArmForm::B,
        src: r#"theorem bridge_xor (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.xor l r) (h1 : Int.xor l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Xor w l r = Except.ok (Int.xor l r) :=
  Eq.trans (xor_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.xor l r) h0 h1)
"#,
    },
    ArmSpec {
        op: "Shl",
        theorem: "bridge_shl",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_shl (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w))
    (h0 : 0 ≤ Int.mul l ((2 : Int) ^ r.toNat))
    (h1 : Int.mul l ((2 : Int) ^ r.toNat) < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Shl w l r = Except.ok (Int.mul l ((2 : Int) ^ r.toNat)) :=
  Eq.trans (if_neg hs) (ok_wrap_eq ((2 : Int) ^ w) (Int.mul l ((2 : Int) ^ r.toNat)) h0 h1)
"#,
    },
    ArmSpec {
        op: "LShr",
        theorem: "bridge_lshr",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_lshr (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w))
    (h0 : 0 ≤ Int.ediv l ((2 : Int) ^ r.toNat))
    (h1 : Int.ediv l ((2 : Int) ^ r.toNat) < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.LShr w l r = Except.ok (Int.ediv l ((2 : Int) ^ r.toNat)) :=
  Eq.trans (if_neg hs) (ok_wrap_eq ((2 : Int) ^ w) (Int.ediv l ((2 : Int) ^ r.toNat)) h0 h1)
"#,
    },
    ArmSpec {
        op: "AShr",
        theorem: "bridge_ashr",
        form: ArmForm::BGuarded,
        src: r#"theorem bridge_ashr (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w))
    (h0 : 0 ≤ Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat))
    (h1 : Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat) < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.AShr w l r =
      Except.ok (Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat)) :=
  Eq.trans (if_neg hs)
    (ok_wrap_eq ((2 : Int) ^ w) (Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat)) h0 h1)
"#,
    },
];

/// Behavioral characterization rows: universal UB rows for all four
/// zero-divisor guards, both `INT_MIN / -1` UB rows, T-division/T-remainder
/// conformance rows (pinning `Int.div`/`Int.mod` T-rounding per
/// docs/ub-numerics-policy.md §1), and the Shl out-of-range row. Together
/// with the 18 arms these constrain EVERY arm of the imported definition —
/// the anti-forgery layer for the checked-in artifacts.
const CHARACTERIZATION_SRC: &str = r#"theorem udiv_zero_ub (w : Nat) (l : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.UDiv w l 0 =
      Except.error (TrustIr.SemError.ub "unsigned division by zero") := rfl
theorem urem_zero_ub (w : Nat) (l : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.URem w l 0 =
      Except.error (TrustIr.SemError.ub "unsigned remainder by zero") := rfl
theorem sdiv_zero_ub (w : Nat) (l : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.SDiv w l 0 =
      Except.error (TrustIr.SemError.ub "signed division by zero") := rfl
theorem srem_zero_ub (w : Nat) (l : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.SRem w l 0 =
      Except.error (TrustIr.SemError.ub "signed remainder by zero") := rfl
theorem udiv_conc : TrustIr.semIntBinOp TrustIr.BinOp.UDiv 8 7 2 = Except.ok 3 := rfl
theorem urem_conc : TrustIr.semIntBinOp TrustIr.BinOp.URem 8 7 2 = Except.ok 1 := rfl
theorem sdiv_conc : TrustIr.semIntBinOp TrustIr.BinOp.SDiv 8 250 2 = Except.ok 253 := rfl
theorem srem_conc : TrustIr.semIntBinOp TrustIr.BinOp.SRem 8 249 2 = Except.ok 255 := rfl
theorem sdiv_intmin_ub :
    TrustIr.semIntBinOp TrustIr.BinOp.SDiv 8 128 255 =
      Except.error (TrustIr.SemError.ub "signed division overflow (INT_MIN / -1)") := rfl
theorem srem_intmin_ub :
    TrustIr.semIntBinOp TrustIr.BinOp.SRem 8 128 255 =
      Except.error (TrustIr.SemError.ub "signed remainder overflow (INT_MIN % -1)") := rfl
theorem shl_oob_ub (l : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.Shl 8 l 8 =
      Except.error (TrustIr.SemError.ub "shift amount out of range") := rfl
"#;

/// Number of characterization rows in [`CHARACTERIZATION_SRC`].
pub const CHARACTERIZATION_ROWS: usize = 11;

/// The COMPOSED 18-op agreement theorem: one proposition, the conjunction of
/// all 18 per-arm agreement statements (each restated verbatim in ∀-binder
/// form), proved by the 18 already-kernel-checked arm theorems. This is the
/// headline artifact the §6 `bridge_line` cites.
const COMPOSED_ALL18_NAME: &str = "bridge_semIntBinOp_agreement_all18";
const COMPOSED_ALL18_SRC: &str = r#"theorem bridge_semIntBinOp_agreement_all18 :
    (∀ (w : Nat) (l r : Int) (h0 : 0 ≤ Int.add l r) (h1 : Int.add l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.Add w l r = Except.ok (Int.add l r))
  ∧ (∀ (w : Nat) (l r : Int) (h0 : 0 ≤ Int.sub l r) (h1 : Int.sub l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.Sub w l r = Except.ok (Int.sub l r))
  ∧ (∀ (w : Nat) (l r : Int) (h0 : 0 ≤ Int.mul l r) (h1 : Int.mul l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.Mul w l r = Except.ok (Int.mul l r))
  ∧ (∀ (w : Nat) (l r : Int) (hz : (r == 0) = false)
      (h0 : 0 ≤ Int.ediv l r) (h1 : Int.ediv l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.UDiv w l r = Except.ok (Int.ediv l r))
  ∧ (∀ (w : Nat) (l r : Int) (hz : (r == 0) = false)
      (hmin : ((TrustIr.toSigned l w == -((2 : Int) ^ (w - 1))) && (TrustIr.toSigned r w == -1)) = false)
      (h0 : 0 ≤ Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w))
      (h1 : Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w) < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.SDiv w l r =
        Except.ok (Int.div (TrustIr.toSigned l w) (TrustIr.toSigned r w)))
  ∧ (∀ (w : Nat) (l r : Int) (hz : (r == 0) = false)
      (h0 : 0 ≤ Int.emod l r) (h1 : Int.emod l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.URem w l r = Except.ok (Int.emod l r))
  ∧ (∀ (w : Nat) (l r : Int) (hz : (r == 0) = false)
      (hmin : ((TrustIr.toSigned l w == -((2 : Int) ^ (w - 1))) && (TrustIr.toSigned r w == -1)) = false)
      (h0 : 0 ≤ Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w))
      (h1 : Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w) < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.SRem w l r =
        Except.ok (Int.mod (TrustIr.toSigned l w) (TrustIr.toSigned r w)))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semIntBinOp TrustIr.BinOp.FAdd w l r =
        Except.error (TrustIr.SemError.typeError "float operation on integer operands"))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semIntBinOp TrustIr.BinOp.FSub w l r =
        Except.error (TrustIr.SemError.typeError "float operation on integer operands"))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semIntBinOp TrustIr.BinOp.FMul w l r =
        Except.error (TrustIr.SemError.typeError "float operation on integer operands"))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semIntBinOp TrustIr.BinOp.FDiv w l r =
        Except.error (TrustIr.SemError.typeError "float operation on integer operands"))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semIntBinOp TrustIr.BinOp.FRem w l r =
        Except.error (TrustIr.SemError.typeError "float operation on integer operands"))
  ∧ (∀ (w : Nat) (l r : Int) (h0 : 0 ≤ Int.land l r) (h1 : Int.land l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.And w l r = Except.ok (Int.land l r))
  ∧ (∀ (w : Nat) (l r : Int) (h0 : 0 ≤ Int.lor l r) (h1 : Int.lor l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.Or w l r = Except.ok (Int.lor l r))
  ∧ (∀ (w : Nat) (l r : Int) (h0 : 0 ≤ Int.xor l r) (h1 : Int.xor l r < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.Xor w l r = Except.ok (Int.xor l r))
  ∧ (∀ (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w))
      (h0 : 0 ≤ Int.mul l ((2 : Int) ^ r.toNat))
      (h1 : Int.mul l ((2 : Int) ^ r.toNat) < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.Shl w l r = Except.ok (Int.mul l ((2 : Int) ^ r.toNat)))
  ∧ (∀ (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w))
      (h0 : 0 ≤ Int.ediv l ((2 : Int) ^ r.toNat))
      (h1 : Int.ediv l ((2 : Int) ^ r.toNat) < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.LShr w l r = Except.ok (Int.ediv l ((2 : Int) ^ r.toNat)))
  ∧ (∀ (w : Nat) (l r : Int) (hs : ¬(r ≥ Int.ofNat w))
      (h0 : 0 ≤ Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat))
      (h1 : Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat) < (2 : Int) ^ w),
      TrustIr.semIntBinOp TrustIr.BinOp.AShr w l r =
        Except.ok (Int.fdiv (TrustIr.toSigned l w) ((2 : Int) ^ r.toNat))) :=
  And.intro bridge_add (And.intro bridge_sub (And.intro bridge_mul (And.intro bridge_udiv
    (And.intro bridge_sdiv (And.intro bridge_urem (And.intro bridge_srem (And.intro bridge_fadd
      (And.intro bridge_fsub (And.intro bridge_fmul (And.intro bridge_fdiv (And.intro bridge_frem
        (And.intro bridge_and (And.intro bridge_or (And.intro bridge_xor (And.intro bridge_shl
          (And.intro bridge_lshr bridge_ashr))))))))))))))))
"#;

/// Forgery probes: deliberately-WRONG claims that must be kernel-REJECTED
/// every run. If any is accepted the gate hard-fails (soundness bug).
const FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-op-agreement (Add claimed to agree with Int.sub)",
        r#"theorem bridge_add_wrong (w : Nat) (l r : Int)
    (h0 : 0 ≤ Int.sub l r) (h1 : Int.sub l r < (2 : Int) ^ w) :
    TrustIr.semIntBinOp TrustIr.BinOp.Add w l r = Except.ok (Int.sub l r) :=
  Eq.trans (add_reduces w l r) (ok_wrap_eq ((2 : Int) ^ w) (Int.sub l r) h0 h1)
"#,
    ),
    (
        "wrong-error-string (FAdd claimed to raise a different message)",
        r#"theorem bridge_fadd_wrong (w : Nat) (l r : Int) :
    TrustIr.semIntBinOp TrustIr.BinOp.FAdd w l r =
      Except.error (TrustIr.SemError.typeError "integer operation on float operands") := rfl
"#,
    ),
];

/// Constants the bridge sources reference; every one must be present in the
/// imported closure (fail-closed if the vendored closure ever regresses).
const BRIDGE_INPUTS: &[&str] = &[
    "TrustIr.semIntBinOp",
    "TrustIr.toSigned",
    "TrustIr.SemError",
    "TrustIr.BinOp",
    "Int.land",
    "Int.lor",
    "Int.xor",
    "Int.emod_eq_of_lt",
    "Int.add_mul_emod_self_left",
    "Int.mul_one",
    "ne_true_of_eq_false",
    "if_neg",
    "congrArg",
    "Eq.trans",
    "Eq.symm",
    "And.intro",
    // UnOp bridge inputs (semIntUnOp / UnOp live in the SAME already-vendored
    // TrustIr.Semantics.Arith module as semIntBinOp/BinOp — no closure change).
    "TrustIr.semIntUnOp",
    "TrustIr.UnOp",
    "Int.neg",
    "Int.zero_sub",
    // OverflowOp bridge inputs (semOverflowOp / OverflowOp live in the SAME
    // already-vendored TrustIr.Semantics.Arith module — no closure change).
    // The flag-connect proofs additionally reach for a handful of Lean-core
    // order/decide lemmas beyond the BinOp/UnOp bridge's set.
    "TrustIr.semOverflowOp",
    "TrustIr.OverflowOp",
    "Decidable.decide",
    "decide_eq_decide",
    "decide_eq_false",
    "Int.lt_iff_add_one_le",
    "Int.sub_add_cancel",
    "Int.not_le",
    "Int.lt_of_le_of_lt",
    "Int.sub_le_self",
    "Bool.false_or",
    // semICmp bridge inputs (semICmp / ICmpOp live in the NEW TrustIr.CmpOp +
    // TrustIr.Semantics.Compare modules the retargeted closure now vendors; the
    // decide instances + Bool.not come from the Lean-core Init closure that
    // Arith already pulled in).
    "TrustIr.semICmp",
    "TrustIr.ICmpOp",
    "Int.decLt",
    "Int.decLe",
    "Int.decEq",
    "Bool.not",
    // stepInst-BinOp bridge inputs (`stepInst` lives in the NEW
    // TrustIr.Semantics.Step module the Step-retargeted closure now vendors;
    // `Inst`/`InstrResult` are its match subject / result type).
    "TrustIr.stepInst",
    "TrustIr.Inst",
    "TrustIr.InstrResult",
];

// ---------------------------------------------------------------------------
// semIntUnOp — the UnOp agreement arms (extends the bridge from
// `semIntBinOp` to trust-ir's UNARY-op semantics). `UnOp` and `semIntUnOp`
// are declared in the SAME Lean source file as `BinOp`/`semIntBinOp`
// (first-party/trust-ir/lean/trust_ir-semantics/TrustIr/BinOp.lean +
// TrustIr/Semantics/Arith.lean), so the already-vendored `.olean` closure
// (root module `TrustIr.Semantics.Arith`) already contains everything this
// section needs — NO manifest/olean regeneration was required to add it.
//
// WHAT IS PROVEN, PER OP (mirrors the semIntBinOp discipline exactly):
//   * Neg  — form (b): agrees with `Int.neg operand` (the exact term Lean's
//     own `-operand` unfolds to via the `Neg Int` instance) under the
//     no-overflow/in-range side condition. NOTE: `clean_ground.rs`'s
//     `F::Neg` formula grounds to the PROPOSITIONALLY (not definitionally)
//     equal `Int.sub (Int.ofNat 0) operand` — `Int.sub 0 x` does not
//     iota-reduce to `Int.neg x` for a free `x` (`Int.add`/`Int.sub`/`Int.neg`
//     are all defined by cases on the constructor, which is stuck on a free
//     variable), so a bare `rfl` cannot close that shape. `bridge_neg` states
//     the term that DOES reduce (`Int.neg operand`, exactly parallel to how
//     `bridge_add` states `Int.add l r`, the function-form unfold of `+`);
//     `bridge_neg_sub_zero_form` is the CONNECTING corollary that additionally
//     rewrites to the exact `Int.sub (Int.ofNat 0) operand` term
//     `clean_ground::ground_int`'s `F::Neg` arm emits, via the imported
//     Lean-core `Int.zero_sub` lemma — so the bridge covers BOTH spellings,
//     genuinely, not by re-statement.
//   * Not  — form (b): agrees with `Int.xor ((2:Int)^w - 1) operand` (the
//     literal mask-xor Lean computes) under the same side condition. Like
//     the BinOp bridge's And/Or/Xor arms, this is a raw Lean-core term, not
//     one `clean_ground.rs` emits today (its `Formula` has no integer
//     bitwise-NOT arm — `Formula::Not` is bool-sorted only, see
//     `trustir_anchor.rs`'s module note) — the same honest gap already
//     documented for the BinOp bitwise trio.
//   * FNeg — form (a): agrees UNCONDITIONALLY; the integer path is the
//     `typeError` value on both sides (mirrors the 5 float BinOp arms).
//   * CtPop — Trust: Clean models NEITHER a live-grounder Formula arm NOR a
//     `trustir_anchor.rs` denotation for population count (its `TrustIrUnOp`
//     enum is `{Neg, Not}` only). Faking an agreement theorem against a
//     denotation that does not exist would be dishonest, so CtPop is left
//     DELIBERATELY UN-BRIDGED — reported plainly via [`UNOP_UNBRIDGED`] /
//     [`BridgeAgreement::unop_unbridged`], exactly like an un-modeled arm.
// ---------------------------------------------------------------------------

/// Reduction lemmas (pure `rfl` over the imported constant) for the two
/// wrap-shaped UnOp arms. FNeg needs none (its `rfl` is direct, like the
/// float BinOp arms); CtPop has no arm at all (see the module note).
const UNOP_REDUCTION_SRCS: &[(&str, &str)] = &[
    (
        "neg_reduces",
        r#"theorem neg_reduces (w : Nat) (operand : Int) :
    TrustIr.semIntUnOp TrustIr.UnOp.Neg w operand =
      Except.ok ((Int.neg operand % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
    (
        "not_reduces",
        r#"theorem not_reduces (w : Nat) (operand : Int) :
    TrustIr.semIntUnOp TrustIr.UnOp.Not w operand =
      Except.ok ((Int.xor ((2 : Int) ^ w - 1) operand % ((2 : Int) ^ w) + (2 : Int) ^ w) % ((2 : Int) ^ w)) := rfl
"#,
    ),
];

/// One UnOp agreement arm: `(op, theorem name, form, Lean source)`. Ordered
/// as the 3 bridged arms of `semIntUnOp` (CtPop is intentionally absent).
struct UnOpArmSpec {
    op: &'static str,
    theorem: &'static str,
    form: ArmForm,
    src: &'static str,
}

const UNOP_ARMS: &[UnOpArmSpec] = &[
    UnOpArmSpec {
        op: "Neg",
        theorem: "bridge_neg",
        form: ArmForm::B,
        src: r#"theorem bridge_neg (w : Nat) (operand : Int)
    (h0 : 0 ≤ Int.neg operand) (h1 : Int.neg operand < (2 : Int) ^ w) :
    TrustIr.semIntUnOp TrustIr.UnOp.Neg w operand = Except.ok (Int.neg operand) :=
  Eq.trans (neg_reduces w operand) (ok_wrap_eq ((2 : Int) ^ w) (Int.neg operand) h0 h1)
"#,
    },
    UnOpArmSpec {
        op: "Not",
        theorem: "bridge_not",
        form: ArmForm::B,
        src: r#"theorem bridge_not (w : Nat) (operand : Int)
    (h0 : 0 ≤ Int.xor ((2 : Int) ^ w - 1) operand)
    (h1 : Int.xor ((2 : Int) ^ w - 1) operand < (2 : Int) ^ w) :
    TrustIr.semIntUnOp TrustIr.UnOp.Not w operand = Except.ok (Int.xor ((2 : Int) ^ w - 1) operand) :=
  Eq.trans (not_reduces w operand)
    (ok_wrap_eq ((2 : Int) ^ w) (Int.xor ((2 : Int) ^ w - 1) operand) h0 h1)
"#,
    },
    UnOpArmSpec {
        op: "FNeg",
        theorem: "bridge_fneg",
        form: ArmForm::A,
        src: r#"theorem bridge_fneg (w : Nat) (operand : Int) :
    TrustIr.semIntUnOp TrustIr.UnOp.FNeg w operand =
      Except.error (TrustIr.SemError.typeError "float negation on integer operand") := rfl
"#,
    },
];

/// The CONNECTING corollary for Neg: restates `bridge_neg`'s conclusion in
/// the EXACT term `clean_ground::ground_int`'s `F::Neg` arm emits
/// (`Int.sub (Int.ofNat 0) operand`), via the imported Lean-core
/// `Int.zero_sub` lemma. Proven, not re-declared: a genuine second corollary,
/// not a relaxation of `bridge_neg`.
const NEG_SUB_ZERO_FORM_NAME: &str = "bridge_neg_sub_zero_form";
const NEG_SUB_ZERO_FORM_SRC: &str = r#"theorem bridge_neg_sub_zero_form (w : Nat) (operand : Int)
    (h0 : 0 ≤ Int.neg operand) (h1 : Int.neg operand < (2 : Int) ^ w) :
    TrustIr.semIntUnOp TrustIr.UnOp.Neg w operand = Except.ok (Int.sub (Int.ofNat 0) operand) :=
  Eq.trans (bridge_neg w operand h0 h1) (congrArg Except.ok (Int.zero_sub operand).symm)
"#;

/// Concrete-value pin rows for the two total wrap-shaped arms (width 8,
/// operand 5): `neg_conc` locks `wrap(-5) = 251`, `not_conc` locks
/// `wrap(0xFF xor 5) = 250`. Cheap sanity anchors, same spirit as the
/// BinOp bridge's `udiv_conc`/`sdiv_conc` rows.
const UNOP_CONC_SRC: &str = r#"theorem neg_conc : TrustIr.semIntUnOp TrustIr.UnOp.Neg 8 5 = Except.ok 251 := rfl
theorem not_conc : TrustIr.semIntUnOp TrustIr.UnOp.Not 8 5 = Except.ok 250 := rfl
"#;
/// Number of concrete rows in [`UNOP_CONC_SRC`].
pub const UNOP_CONC_ROWS: usize = 2;

/// The COMPOSED UnOp agreement theorem: one proposition, the conjunction of
/// the 3 bridged per-arm agreement statements (Neg/Not/FNeg — CtPop is
/// excluded, it is not bridged), proved by the already-kernel-checked arm
/// theorems.
const UNOP_COMPOSED_NAME: &str = "bridge_semIntUnOp_agreement_all";
const UNOP_COMPOSED_SRC: &str = r#"theorem bridge_semIntUnOp_agreement_all :
    (∀ (w : Nat) (operand : Int) (h0 : 0 ≤ Int.neg operand) (h1 : Int.neg operand < (2 : Int) ^ w),
      TrustIr.semIntUnOp TrustIr.UnOp.Neg w operand = Except.ok (Int.neg operand))
  ∧ (∀ (w : Nat) (operand : Int)
      (h0 : 0 ≤ Int.xor ((2 : Int) ^ w - 1) operand)
      (h1 : Int.xor ((2 : Int) ^ w - 1) operand < (2 : Int) ^ w),
      TrustIr.semIntUnOp TrustIr.UnOp.Not w operand = Except.ok (Int.xor ((2 : Int) ^ w - 1) operand))
  ∧ (∀ (w : Nat) (operand : Int),
      TrustIr.semIntUnOp TrustIr.UnOp.FNeg w operand =
        Except.error (TrustIr.SemError.typeError "float negation on integer operand")) :=
  And.intro bridge_neg (And.intro bridge_not bridge_fneg)
"#;

/// UnOp forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run, mirroring [`FORGERY_PROBES`] for the unary
/// layer.
const UNOP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-op-agreement (Neg claimed to agree with the Not/xor term)",
        r#"theorem bridge_neg_wrong (w : Nat) (operand : Int)
    (h0 : 0 ≤ Int.xor ((2 : Int) ^ w - 1) operand)
    (h1 : Int.xor ((2 : Int) ^ w - 1) operand < (2 : Int) ^ w) :
    TrustIr.semIntUnOp TrustIr.UnOp.Neg w operand = Except.ok (Int.xor ((2 : Int) ^ w - 1) operand) :=
  Eq.trans (neg_reduces w operand)
    (ok_wrap_eq ((2 : Int) ^ w) (Int.xor ((2 : Int) ^ w - 1) operand) h0 h1)
"#,
    ),
    (
        "wrong-error-string (FNeg claimed to raise a different message)",
        r#"theorem bridge_fneg_wrong (w : Nat) (operand : Int) :
    TrustIr.semIntUnOp TrustIr.UnOp.FNeg w operand =
      Except.error (TrustIr.SemError.typeError "integer negation on float operand") := rfl
"#,
    ),
];

/// Un-bridged UnOp arms, reported honestly (never faked): `(op, reason)`.
const UNOP_UNBRIDGED: &[(&str, &str)] = &[(
    "CtPop",
    "Clean models neither a live-grounder Formula arm nor a trustir_anchor.rs \
     denotation for population count (TrustIrUnOp is {Neg, Not} only) — no \
     agreement claim is made; faking one would be dishonest",
)];

// ---------------------------------------------------------------------------
// semOverflowOp — the OverflowOp agreement arms (extends the bridge to
// trust-ir's OVERFLOW-CHECKED arithmetic semantics: `AddOverflow`/
// `SubOverflow`/`MulOverflow`, each returning `(result, overflow_flag)`).
// `OverflowOp` and `semOverflowOp` are declared in the SAME already-vendored
// Lean source as `BinOp`/`UnOp` (TrustIr/BinOp.lean + TrustIr/Semantics/
// Arith.lean) — no manifest/olean regeneration needed. See the module-level
// "EXTENSION 2" doc comment above for the full per-op breakdown.
// ---------------------------------------------------------------------------

/// The shared "threshold shift" lemmas: connects trust-ir's own `exact ≥
/// half` spelling of the overflow threshold to the safety-VC tier's `(half -
/// 1) < exact` textbook spelling (Lemma 2 / Lemma 5's stated form) — a
/// genuine arithmetic fact for `Int`, proven directly from imported Lean-core
/// `Int.le_of_sub_one_lt` + `Int.sub_one_lt_of_le` + `decide_eq_decide`, not
/// assumed or re-declared.  The direct iff avoids asking clean-elab to infer
/// the dependent motive of an `Eq.mp` over `Int.sub_add_cancel`.
const OVERFLOW_THRESHOLD_PRELUDE_SRC: &str = r#"theorem overflow_threshold_iff2 (half exact : Int) :
    Iff (half - 1 < exact) (half ≤ exact) :=
  Iff.intro
    (fun (h : half - 1 < exact) => Int.le_of_sub_one_lt h)
    (fun (h : half ≤ exact) => Int.sub_one_lt_of_le h)
theorem overflow_threshold_decide_eq (half exact : Int) :
    Decidable.decide (half - 1 < exact) = Decidable.decide (half ≤ exact) :=
  (@decide_eq_decide (half - 1 < exact) (half ≤ exact)
    (Int.decLt (half - 1) exact) (Int.decLe half exact)).mpr (overflow_threshold_iff2 half exact)
"#;

/// One overflow-op VALUE arm: the `.1` (Lean `Prod.fst`) component of
/// `semOverflowOp`'s `(result, flag)` pair is ALWAYS `wrap(exact)` — the SAME
/// wrapped value `semIntBinOp` already computes (Add/Sub/Mul), evaluated at
/// the raw operands (unsigned) or their `toSigned` images (signed). Proven by
/// genuine COMPOSITION with the already-proven `add_reduces`/`sub_reduces`/
/// `mul_reduces` reduction lemmas (`Eq.trans …(_reduces …).symm`), not an
/// independently-reproven coincidence.
struct OverflowValueArmSpec {
    op: &'static str,
    signed: bool,
    theorem: &'static str,
    src: &'static str,
}

const OVERFLOW_VALUE_ARMS: &[OverflowValueArmSpec] = &[
    OverflowValueArmSpec {
        op: "AddOverflow",
        signed: false,
        theorem: "bridge_overflow_uadd_value",
        src: r#"theorem bridge_overflow_uadd_value (w : Nat) (l r : Int) :
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w false l r with
       | .ok p => Except.ok p.1 | .error e => Except.error e) =
    TrustIr.semIntBinOp TrustIr.BinOp.Add w l r :=
  Eq.trans rfl (add_reduces w l r).symm
"#,
    },
    OverflowValueArmSpec {
        op: "SubOverflow",
        signed: false,
        theorem: "bridge_overflow_usub_value",
        src: r#"theorem bridge_overflow_usub_value (w : Nat) (l r : Int) :
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w false l r with
       | .ok p => Except.ok p.1 | .error e => Except.error e) =
    TrustIr.semIntBinOp TrustIr.BinOp.Sub w l r :=
  Eq.trans rfl (sub_reduces w l r).symm
"#,
    },
    OverflowValueArmSpec {
        op: "MulOverflow",
        signed: false,
        theorem: "bridge_overflow_umul_value",
        src: r#"theorem bridge_overflow_umul_value (w : Nat) (l r : Int) :
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w false l r with
       | .ok p => Except.ok p.1 | .error e => Except.error e) =
    TrustIr.semIntBinOp TrustIr.BinOp.Mul w l r :=
  Eq.trans rfl (mul_reduces w l r).symm
"#,
    },
    OverflowValueArmSpec {
        op: "AddOverflow",
        signed: true,
        theorem: "bridge_overflow_sadd_value",
        src: r#"theorem bridge_overflow_sadd_value (w : Nat) (l r : Int) :
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w true l r with
       | .ok p => Except.ok p.1 | .error e => Except.error e) =
    TrustIr.semIntBinOp TrustIr.BinOp.Add w (TrustIr.toSigned l w) (TrustIr.toSigned r w) :=
  Eq.trans rfl (add_reduces w (TrustIr.toSigned l w) (TrustIr.toSigned r w)).symm
"#,
    },
    OverflowValueArmSpec {
        op: "SubOverflow",
        signed: true,
        theorem: "bridge_overflow_ssub_value",
        src: r#"theorem bridge_overflow_ssub_value (w : Nat) (l r : Int) :
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w true l r with
       | .ok p => Except.ok p.1 | .error e => Except.error e) =
    TrustIr.semIntBinOp TrustIr.BinOp.Sub w (TrustIr.toSigned l w) (TrustIr.toSigned r w) :=
  Eq.trans rfl (sub_reduces w (TrustIr.toSigned l w) (TrustIr.toSigned r w)).symm
"#,
    },
    OverflowValueArmSpec {
        op: "MulOverflow",
        signed: true,
        theorem: "bridge_overflow_smul_value",
        src: r#"theorem bridge_overflow_smul_value (w : Nat) (l r : Int) :
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w true l r with
       | .ok p => Except.ok p.1 | .error e => Except.error e) =
    TrustIr.semIntBinOp TrustIr.BinOp.Mul w (TrustIr.toSigned l w) (TrustIr.toSigned r w) :=
  Eq.trans rfl (mul_reduces w (TrustIr.toSigned l w) (TrustIr.toSigned r w)).symm
"#,
    },
];

/// One overflow-op FLAG arm: the `.2` (Lean `Prod.snd`) component's agreement
/// with the Clean safety-VC overflow CONDITION (Lemma 2 unsigned-add, Lemma 5
/// signed add/sub/mul, Lemma 8 unsigned-sub). Two theorems: `reduces_src`
/// PINS the exact Bool trust-ir computes (rfl, trust-ir's own `≥`/`<`
/// spelling); `connect_src` proves the further identity to the Lemma's
/// textbook spelling. `guard_hyps` is the guarded arm's extra hypothesis list
/// (empty for the three unconditional Lemma-5 arms and the Lemma-2 arm;
/// non-empty for unsigned-Sub's Lemma-8 arm, which needs the documented
/// `lhs,rhs ∈ [0,2^w)` residue precondition to discharge the vacuous `exact ≥
/// modulus` disjunct — mirrors the existing form-BGuarded arms' discipline).
struct OverflowFlagArmSpec {
    op: &'static str,
    signed: bool,
    lemma: &'static str,
    form: ArmForm,
    reduces_theorem: &'static str,
    reduces_src: &'static str,
    /// Non-empty only for unsigned-Sub: the extra `overflow_usub_flag_vacuous`
    /// helper lemma proven before the `connect_src` theorem can cite it.
    extra_src: &'static str,
    connect_theorem: &'static str,
    connect_src: &'static str,
}

// With the imported notation decisions, these connecting rewrites close their
// equality goals. A subsequent `rfl` is an error because no goal remains.
const OVERFLOW_FLAG_ARMS: &[OverflowFlagArmSpec] = &[
    OverflowFlagArmSpec {
        op: "AddOverflow",
        signed: false,
        lemma: "Lemma 2 (unsigned-add overflow)",
        form: ArmForm::B,
        reduces_theorem: "overflow_uadd_flag_reduces",
        // The underflow disjunct's `Decidable` instance is pinned explicitly
        // (`@Decidable.decide (… < 0) (Int.decLt … 0)`): on a comparison with
        // a GROUND side (here the literal `0`), clean-elab's instance search
        // whnf-unfolds the goal past `Int.lt` to `Int.NonNeg …`, misses
        // `Int.decLt`, and falls back to the noncomputable
        // `Classical.propDecidable` — which the kernel cannot reduce (rfl
        // dies) and which drags `Classical.choice` into the axiom closure.
        // `Int.decLt` is the very instance the imported def carries, so the
        // pinned statement is the SAME proposition with the SAME decision
        // procedure — the flag semantics (overflow iff exact ≥ 2^w or
        // exact < 0) are unchanged and nothing is weakened.
        reduces_src: r#"theorem overflow_uadd_flag_reduces (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w false l r =
      Except.ok ((((l + r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (l + r ≥ (2:Int)^w) ||
                 @Decidable.decide (l + r < 0) (Int.decLt (l + r) 0)) := rfl
"#,
        extra_src: "",
        connect_theorem: "bridge_overflow_uadd_flag",
        connect_src: r#"theorem bridge_overflow_uadd_flag (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w false l r =
      Except.ok ((((l + r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (((2:Int)^w - 1) < (l + r)) ||
                 @Decidable.decide (l + r < 0) (Int.decLt (l + r) 0)) := by
  rw [overflow_uadd_flag_reduces, overflow_threshold_decide_eq]
"#,
    },
    OverflowFlagArmSpec {
        op: "SubOverflow",
        signed: false,
        lemma: "Lemma 8 (unsigned-sub underflow)",
        form: ArmForm::BGuarded,
        reduces_theorem: "overflow_usub_flag_reduces",
        // Underflow disjunct instance pinned for the same reason as the
        // AddOverflow[u] arm above.
        reduces_src: r#"theorem overflow_usub_flag_reduces (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w false l r =
      Except.ok ((((l - r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (l - r ≥ (2:Int)^w) ||
                 @Decidable.decide (l - r < 0) (Int.decLt (l - r) 0)) := rfl
"#,
        extra_src: r#"theorem overflow_usub_flag_vacuous (w : Nat) (l r : Int)
    (hl1 : l < (2:Int)^w) (hr0 : (0:Int) ≤ r) :
    (Decidable.decide (l - r ≥ (2:Int)^w) || @Decidable.decide (l - r < 0) (Int.decLt (l - r) 0)) =
      @Decidable.decide (l - r < 0) (Int.decLt (l - r) 0) := by
  rw [@decide_eq_false (l - r ≥ (2:Int)^w) (Int.decLe ((2:Int)^w) (l - r))
        ((@Int.not_le ((2:Int)^w) (l - r)).mpr (Int.lt_of_le_of_lt (@Int.sub_le_self l r hr0) hl1)),
      Bool.false_or]
"#,
        connect_theorem: "bridge_overflow_usub_flag",
        connect_src: r#"theorem bridge_overflow_usub_flag (w : Nat) (l r : Int)
    (hl1 : l < (2:Int)^w) (hr0 : (0:Int) ≤ r) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w false l r =
      Except.ok ((((l - r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 @Decidable.decide (l - r < 0) (Int.decLt (l - r) 0)) := by
  rw [overflow_usub_flag_reduces, overflow_usub_flag_vacuous w l r hl1 hr0]
"#,
    },
    unsigned_mul::FLAG_ARM,
    OverflowFlagArmSpec {
        op: "AddOverflow",
        signed: true,
        lemma: "Lemma 5 (signed add/sub/mul overflow)",
        form: ArmForm::B,
        reduces_theorem: "overflow_sadd_flag_reduces",
        reduces_src: r#"theorem overflow_sadd_flag_reduces (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w true l r =
      Except.ok (((((TrustIr.toSigned l w) + (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide ((TrustIr.toSigned l w) + (TrustIr.toSigned r w) ≥ (2:Int)^(w-1)) ||
                 Decidable.decide ((TrustIr.toSigned l w) + (TrustIr.toSigned r w) < -((2:Int)^(w-1)))) := rfl
"#,
        extra_src: "",
        connect_theorem: "bridge_overflow_sadd_flag",
        connect_src: r#"theorem bridge_overflow_sadd_flag (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w true l r =
      Except.ok (((((TrustIr.toSigned l w) + (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (((2:Int)^(w-1) - 1) < ((TrustIr.toSigned l w) + (TrustIr.toSigned r w))) ||
                 Decidable.decide ((TrustIr.toSigned l w) + (TrustIr.toSigned r w) < -((2:Int)^(w-1)))) := by
  rw [overflow_sadd_flag_reduces, overflow_threshold_decide_eq]
"#,
    },
    OverflowFlagArmSpec {
        op: "SubOverflow",
        signed: true,
        lemma: "Lemma 5 (signed add/sub/mul overflow)",
        form: ArmForm::B,
        reduces_theorem: "overflow_ssub_flag_reduces",
        reduces_src: r#"theorem overflow_ssub_flag_reduces (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w true l r =
      Except.ok (((((TrustIr.toSigned l w) - (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide ((TrustIr.toSigned l w) - (TrustIr.toSigned r w) ≥ (2:Int)^(w-1)) ||
                 Decidable.decide ((TrustIr.toSigned l w) - (TrustIr.toSigned r w) < -((2:Int)^(w-1)))) := rfl
"#,
        extra_src: "",
        connect_theorem: "bridge_overflow_ssub_flag",
        connect_src: r#"theorem bridge_overflow_ssub_flag (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w true l r =
      Except.ok (((((TrustIr.toSigned l w) - (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (((2:Int)^(w-1) - 1) < ((TrustIr.toSigned l w) - (TrustIr.toSigned r w))) ||
                 Decidable.decide ((TrustIr.toSigned l w) - (TrustIr.toSigned r w) < -((2:Int)^(w-1)))) := by
  rw [overflow_ssub_flag_reduces, overflow_threshold_decide_eq]
"#,
    },
    OverflowFlagArmSpec {
        op: "MulOverflow",
        signed: true,
        lemma: "Lemma 5 (signed add/sub/mul overflow)",
        form: ArmForm::B,
        reduces_theorem: "overflow_smul_flag_reduces",
        reduces_src: r#"theorem overflow_smul_flag_reduces (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w true l r =
      Except.ok (((((TrustIr.toSigned l w) * (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide ((TrustIr.toSigned l w) * (TrustIr.toSigned r w) ≥ (2:Int)^(w-1)) ||
                 Decidable.decide ((TrustIr.toSigned l w) * (TrustIr.toSigned r w) < -((2:Int)^(w-1)))) := rfl
"#,
        extra_src: "",
        connect_theorem: "bridge_overflow_smul_flag",
        connect_src: r#"theorem bridge_overflow_smul_flag (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w true l r =
      Except.ok (((((TrustIr.toSigned l w) * (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (((2:Int)^(w-1) - 1) < ((TrustIr.toSigned l w) * (TrustIr.toSigned r w))) ||
                 Decidable.decide ((TrustIr.toSigned l w) * (TrustIr.toSigned r w) < -((2:Int)^(w-1)))) := by
  rw [overflow_smul_flag_reduces, overflow_threshold_decide_eq]
"#,
    },
];

/// The COMPOSED overflow agreement theorem: all 6 VALUE and all 6 FLAG
/// statements (12 conjuncts), composed from the actual checked arm theorems.
/// The gate also requires the four registered unsigned-Mul Int predicate links.
const OVERFLOW_COMPOSED_NAME: &str = "bridge_semOverflowOp_agreement_all";
const OVERFLOW_COMPOSED_SRC: &str = r#"theorem bridge_semOverflowOp_agreement_all :
    (∀ (w : Nat) (l r : Int),
      (match TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w false l r with
         | .ok p => Except.ok p.1 | .error e => Except.error e) =
      TrustIr.semIntBinOp TrustIr.BinOp.Add w l r)
  ∧ (∀ (w : Nat) (l r : Int),
      (match TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w false l r with
         | .ok p => Except.ok p.1 | .error e => Except.error e) =
      TrustIr.semIntBinOp TrustIr.BinOp.Sub w l r)
  ∧ (∀ (w : Nat) (l r : Int),
      (match TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w false l r with
         | .ok p => Except.ok p.1 | .error e => Except.error e) =
      TrustIr.semIntBinOp TrustIr.BinOp.Mul w l r)
  ∧ (∀ (w : Nat) (l r : Int),
      (match TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w true l r with
         | .ok p => Except.ok p.1 | .error e => Except.error e) =
      TrustIr.semIntBinOp TrustIr.BinOp.Add w (TrustIr.toSigned l w) (TrustIr.toSigned r w))
  ∧ (∀ (w : Nat) (l r : Int),
      (match TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w true l r with
         | .ok p => Except.ok p.1 | .error e => Except.error e) =
      TrustIr.semIntBinOp TrustIr.BinOp.Sub w (TrustIr.toSigned l w) (TrustIr.toSigned r w))
  ∧ (∀ (w : Nat) (l r : Int),
      (match TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w true l r with
         | .ok p => Except.ok p.1 | .error e => Except.error e) =
      TrustIr.semIntBinOp TrustIr.BinOp.Mul w (TrustIr.toSigned l w) (TrustIr.toSigned r w))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w false l r =
        Except.ok ((((l + r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                   Decidable.decide (((2:Int)^w - 1) < (l + r)) ||
                   @Decidable.decide (l + r < 0) (Int.decLt (l + r) 0)))
  ∧ (∀ (w : Nat) (l r : Int) (hl1 : l < (2:Int)^w) (hr0 : (0:Int) ≤ r),
      TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w false l r =
        Except.ok ((((l - r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                   @Decidable.decide (l - r < 0) (Int.decLt (l - r) 0)))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w false l r =
        Except.ok ((((l * r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                   @Decidable.decide (l * r < 0) (Int.decLt (l * r) 0) ||
                   Decidable.decide (((2:Int)^w - 1) < (l * r))))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w true l r =
        Except.ok (((((TrustIr.toSigned l w) + (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                   Decidable.decide (((2:Int)^(w-1) - 1) < ((TrustIr.toSigned l w) + (TrustIr.toSigned r w))) ||
                   Decidable.decide ((TrustIr.toSigned l w) + (TrustIr.toSigned r w) < -((2:Int)^(w-1)))))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w true l r =
        Except.ok (((((TrustIr.toSigned l w) - (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                   Decidable.decide (((2:Int)^(w-1) - 1) < ((TrustIr.toSigned l w) - (TrustIr.toSigned r w))) ||
                   Decidable.decide ((TrustIr.toSigned l w) - (TrustIr.toSigned r w) < -((2:Int)^(w-1)))))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w true l r =
        Except.ok (((((TrustIr.toSigned l w) * (TrustIr.toSigned r w)) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                   Decidable.decide (((2:Int)^(w-1) - 1) < ((TrustIr.toSigned l w) * (TrustIr.toSigned r w))) ||
                   Decidable.decide ((TrustIr.toSigned l w) * (TrustIr.toSigned r w) < -((2:Int)^(w-1))))) :=
  And.intro bridge_overflow_uadd_value (And.intro bridge_overflow_usub_value (And.intro bridge_overflow_umul_value
    (And.intro bridge_overflow_sadd_value (And.intro bridge_overflow_ssub_value (And.intro bridge_overflow_smul_value
      (And.intro bridge_overflow_uadd_flag (And.intro bridge_overflow_usub_flag
        (And.intro bridge_overflow_umul_flag (And.intro bridge_overflow_sadd_flag
          (And.intro bridge_overflow_ssub_flag bridge_overflow_smul_flag))))))))))
"#;

/// Overflow forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run, mirroring [`FORGERY_PROBES`] /
/// [`UNOP_FORGERY_PROBES`] for the overflow layer. One wrong-threshold claim
/// (unsigned-add's flag claimed to use the SIGNED half-width threshold) and
/// one signed/unsigned-swap claim (signed-sub's flag claimed to agree with
/// the raw unsigned-style operands, no `toSigned`).
const OVERFLOW_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-threshold (unsigned AddOverflow claimed to use the signed half-width 2^(w-1) threshold)",
        r#"theorem bridge_overflow_uadd_flag_wrong (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow w false l r =
      Except.ok ((((l + r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (l + r ≥ (2:Int)^(w-1)) || Decidable.decide (l + r < 0)) := rfl
"#,
    ),
    (
        "signed-unsigned-swap (signed SubOverflow claimed to agree with the raw un-toSigned operand threshold)",
        r#"theorem bridge_overflow_ssub_flag_wrong (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow w true l r =
      Except.ok ((((l - r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (l - r ≥ (2:Int)^(w-1)) || Decidable.decide (l - r < -((2:Int)^(w-1)))) := rfl
"#,
    ),
];

/// All six generic Int overflow flags now have bridges. This empty roster says
/// nothing about BV-predicate equivalence or unregistered u128 safety predicates.
const OVERFLOW_FLAG_UNBRIDGED: &[(&str, &str)] = &[];

// ---------------------------------------------------------------------------
// semICmp — the ICmp agreement arms (extends the bridge to trust-ir's
// INTEGER-COMPARISON semantics: Eq/Ne/Ult/Ule/Ugt/Uge/Slt/Sle/Sgt/Sge, the
// pure `Int × Int → Bool` predicate under every branch guard). `ICmpOp` and
// `semICmp` live in the NEW `TrustIr/CmpOp.lean` + `TrustIr/Semantics/
// Compare.lean` modules that the RETARGETED bridge closure (root
// `TrustIr.Semantics.Compare`) now vendors. See the module-level "EXTENSION 3"
// doc comment above for the full per-arm breakdown. All 10 arms are
// UNCONDITIONAL `rfl` agreements — `semICmp` is total Bool-valued, so no
// wrap/UB side condition ever arises.
// ---------------------------------------------------------------------------

/// Which family of Clean's ONE comparison denotation an ICmp arm maps to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum IcmpArmKind {
    /// Ult/Ule/Ugt/Uge: the raw operands (already in [0,2^w)) ARE the values
    /// Clean's `Int.lt`/`Int.le` compare — no adjustment (Ugt/Uge arg-swap).
    Unsigned,
    /// Eq/Ne: raw-operand equality (`Decidable.decide (l = r)`, Clean's
    /// `@Eq Int` under `decide`) / its `Bool.not` negation.
    SignIndependent,
    /// Slt/Sle/Sgt/Sge: the SAME `Int.lt`/`Int.le`, evaluated at the
    /// `TrustIr.toSigned` images (mirrors the SDiv/SRem/AShr toSigned
    /// precedent; Sgt/Sge arg-swap).
    Signed,
}

impl IcmpArmKind {
    fn label(self) -> &'static str {
        match self {
            IcmpArmKind::Unsigned => "u",
            IcmpArmKind::SignIndependent => "eq",
            IcmpArmKind::Signed => "s",
        }
    }
}

/// One ICmp agreement arm: `(op, kind, theorem name, Lean source)`. Ordered as
/// the 10 arms of `semICmp` / the `ICmpOp` enum
/// (Eq,Ne,Ult,Ule,Ugt,Uge,Slt,Sle,Sgt,Sge).
struct IcmpArmSpec {
    op: &'static str,
    kind: IcmpArmKind,
    theorem: &'static str,
    src: &'static str,
}

const ICMP_ARMS: &[IcmpArmSpec] = &[
    IcmpArmSpec {
        op: "Eq",
        kind: IcmpArmKind::SignIndependent,
        theorem: "bridge_icmp_eq",
        src: r#"theorem bridge_icmp_eq (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Eq w l r = Decidable.decide (l = r) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Ne",
        kind: IcmpArmKind::SignIndependent,
        theorem: "bridge_icmp_ne",
        src: r#"theorem bridge_icmp_ne (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Ne w l r = Bool.not (Decidable.decide (l = r)) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Ult",
        kind: IcmpArmKind::Unsigned,
        theorem: "bridge_icmp_ult",
        src: r#"theorem bridge_icmp_ult (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Ult w l r = Decidable.decide (Int.lt l r) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Ule",
        kind: IcmpArmKind::Unsigned,
        theorem: "bridge_icmp_ule",
        src: r#"theorem bridge_icmp_ule (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Ule w l r = Decidable.decide (Int.le l r) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Ugt",
        kind: IcmpArmKind::Unsigned,
        theorem: "bridge_icmp_ugt",
        src: r#"theorem bridge_icmp_ugt (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Ugt w l r = Decidable.decide (Int.lt r l) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Uge",
        kind: IcmpArmKind::Unsigned,
        theorem: "bridge_icmp_uge",
        src: r#"theorem bridge_icmp_uge (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Uge w l r = Decidable.decide (Int.le r l) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Slt",
        kind: IcmpArmKind::Signed,
        theorem: "bridge_icmp_slt",
        src: r#"theorem bridge_icmp_slt (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Slt w l r =
      Decidable.decide (Int.lt (TrustIr.toSigned l w) (TrustIr.toSigned r w)) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Sle",
        kind: IcmpArmKind::Signed,
        theorem: "bridge_icmp_sle",
        src: r#"theorem bridge_icmp_sle (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Sle w l r =
      Decidable.decide (Int.le (TrustIr.toSigned l w) (TrustIr.toSigned r w)) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Sgt",
        kind: IcmpArmKind::Signed,
        theorem: "bridge_icmp_sgt",
        src: r#"theorem bridge_icmp_sgt (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Sgt w l r =
      Decidable.decide (Int.lt (TrustIr.toSigned r w) (TrustIr.toSigned l w)) := rfl
"#,
    },
    IcmpArmSpec {
        op: "Sge",
        kind: IcmpArmKind::Signed,
        theorem: "bridge_icmp_sge",
        src: r#"theorem bridge_icmp_sge (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Sge w l r =
      Decidable.decide (Int.le (TrustIr.toSigned r w) (TrustIr.toSigned l w)) := rfl
"#,
    },
];

/// Concrete-value pin rows (width 8) that ANCHOR the signed/unsigned
/// distinction: on the SAME operands `(3, 200)`, `Ult` is true (`3 < 200`) but
/// `Slt` is false (`toSigned 3 8 = 3`, `toSigned 200 8 = 200 - 256 = -56`, and
/// `3 < -56` is false) — so a bridge that confused signed with unsigned would
/// fail these. Plus an Eq/Ne pair. Same spirit as the UnOp `neg_conc`/
/// `not_conc` rows.
const ICMP_CONC_SRC: &str = r#"theorem icmp_ult_conc : TrustIr.semICmp TrustIr.ICmpOp.Ult 8 3 200 = true := rfl
theorem icmp_slt_conc : TrustIr.semICmp TrustIr.ICmpOp.Slt 8 3 200 = false := rfl
theorem icmp_eq_conc : TrustIr.semICmp TrustIr.ICmpOp.Eq 8 5 5 = true := rfl
theorem icmp_ne_conc : TrustIr.semICmp TrustIr.ICmpOp.Ne 8 5 5 = false := rfl
"#;
/// Number of concrete rows in [`ICMP_CONC_SRC`].
pub const ICMP_CONC_ROWS: usize = 4;

/// The COMPOSED ICmp agreement theorem: one proposition, the conjunction of
/// all 10 per-arm agreement statements (each restated verbatim in ∀-binder
/// form), proved by the 10 already-kernel-checked arm theorems.
const ICMP_COMPOSED_NAME: &str = "bridge_semICmp_agreement_all";
const ICMP_COMPOSED_SRC: &str = r#"theorem bridge_semICmp_agreement_all :
    (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Eq w l r = Decidable.decide (l = r))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Ne w l r = Bool.not (Decidable.decide (l = r)))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Ult w l r = Decidable.decide (Int.lt l r))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Ule w l r = Decidable.decide (Int.le l r))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Ugt w l r = Decidable.decide (Int.lt r l))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Uge w l r = Decidable.decide (Int.le r l))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Slt w l r =
        Decidable.decide (Int.lt (TrustIr.toSigned l w) (TrustIr.toSigned r w)))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Sle w l r =
        Decidable.decide (Int.le (TrustIr.toSigned l w) (TrustIr.toSigned r w)))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Sgt w l r =
        Decidable.decide (Int.lt (TrustIr.toSigned r w) (TrustIr.toSigned l w)))
  ∧ (∀ (w : Nat) (l r : Int),
      TrustIr.semICmp TrustIr.ICmpOp.Sge w l r =
        Decidable.decide (Int.le (TrustIr.toSigned r w) (TrustIr.toSigned l w))) :=
  And.intro bridge_icmp_eq (And.intro bridge_icmp_ne (And.intro bridge_icmp_ult
    (And.intro bridge_icmp_ule (And.intro bridge_icmp_ugt (And.intro bridge_icmp_uge
      (And.intro bridge_icmp_slt (And.intro bridge_icmp_sle
        (And.intro bridge_icmp_sgt bridge_icmp_sge))))))))
"#;

/// ICmp forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run, mirroring [`FORGERY_PROBES`] /
/// [`UNOP_FORGERY_PROBES`] / [`OVERFLOW_FORGERY_PROBES`]. (1) Ult claimed to
/// agree with `Int.le` (wrong relation); (2) Slt claimed to agree with raw
/// `Int.lt` WITHOUT the `toSigned` images (signed/unsigned confusion — the
/// #1 real-world comparison bug); (3) Eq claimed to be its own Ne negation
/// (Eq/Ne swap).
const ICMP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-relation (Ult claimed to agree with Int.le)",
        r#"theorem bridge_icmp_ult_wrong (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Ult w l r = Decidable.decide (Int.le l r) := rfl
"#,
    ),
    (
        "signed-without-toSigned (Slt claimed to agree with raw Int.lt, no toSigned)",
        r#"theorem bridge_icmp_slt_wrong (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Slt w l r = Decidable.decide (Int.lt l r) := rfl
"#,
    ),
    (
        "eq-ne-swap (Eq claimed to agree with the Ne negation term)",
        r#"theorem bridge_icmp_eq_wrong (w : Nat) (l r : Int) :
    TrustIr.semICmp TrustIr.ICmpOp.Eq w l r = Bool.not (Decidable.decide (l = r)) := rfl
"#,
    ),
];

/// Un-bridged ICmp arms, reported honestly (never faked): `(op, reason)`.
/// EMPTY — all 10 arms bridge. The signed arms are a GENUINE agreement with
/// Clean's one `Int.lt`/`Int.le` comparison denotation at the `toSigned`
/// operand images (the established SDiv/SRem/AShr precedent), NOT a faked
/// claim against a non-existent "signed comparison" primitive — so unlike
/// `UnOp::CtPop`, there is no honest residue here.
const ICMP_UNBRIDGED: &[(&str, &str)] = &[];

// ---------------------------------------------------------------------------
// semCast — the Cast agreement arms (extends the bridge to trust-ir's
// INTEGER-CAST value semantics: Trunc/ZExt/SExt, the width-conversion pure
// cores `semCast`'s monadic dispatch computes). `CastOp`/`semCast` live in the
// NEW `TrustIr/CastOp.lean` + `TrustIr/Semantics/Cast.lean` modules the
// UNION-closure root set [`BRIDGE_ROOT_MODULES`] now vendors. See the
// module-level "EXTENSION 4" doc comment above for the full breakdown
// (why the arms are concrete-state/parametric-over-`v`, not fully symbolic;
// the Tier-2 widening-identity connecting corollaries; the honest float/ptr
// residue). All Lean sources below were checked against a REAL Lean 4.8.0
// toolchain (not just clean) before being pinned here.
// ---------------------------------------------------------------------------

/// One Cast agreement arm: `(op, theorem name, Lean source)`. Ordered as
/// Trunc/ZExt/SExt — the 3 integer arms of `semCast` (the 12 float/pointer
/// arms are honestly un-bridged, see [`CAST_UNBRIDGED`]). Each is `∀ (v :
/// Int), …`: the operand's integer PAYLOAD is symbolic; the `ValueId`/`Ty`/
/// `MachineState` SHAPE is pinned to literals (see the module doc "WHY THE
/// ARMS ARE CONCRETE-STATE" note) at one representative width pair
/// (Trunc 16→8, ZExt 8→16 unsigned, SExt 8→16 signed).
///
/// The shared model's Trunc guard uses `Ty.isBool`, whose concrete `I8`
/// case reduces definitionally. The old theorem's `hbool` premise remains
/// part of its original statement and downstream compositions, but the proof
/// no longer rewrites the retired structural-BEq guard. `rfl` checks the whole
/// monadic result, including the original destination value and state, against
/// the imported model. It introduces no assumption about the guard or result.
/// ZExt/SExt retain their original unconditional statements and proofs.
struct CastArmSpec {
    op: &'static str,
    theorem: &'static str,
    src: &'static str,
}

const CAST_ARMS: &[CastArmSpec] = &[
    CastArmSpec {
        op: "Trunc",
        theorem: "bridge_cast_trunc",
        src: r#"theorem bridge_cast_trunc (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false) :
    TrustIr.Sem.run
      (TrustIr.semCast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.ValueId.mk 1,
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 8)),
          nextValueId := 2 }) := rfl
"#,
    },
    CastArmSpec {
        op: "ZExt",
        theorem: "bridge_cast_zext",
        src: r#"theorem bridge_cast_zext (v : Int) :
    TrustIr.Sem.run
      (TrustIr.semCast TrustIr.CastOp.ZExt TrustIr.Ty.U8 TrustIr.Ty.U16 (TrustIr.ValueId.mk 0))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.ValueId.mk 1,
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 16 (TrustIr.truncateUnsigned v 16)),
          nextValueId := 2 }) := rfl
"#,
    },
    CastArmSpec {
        op: "SExt",
        theorem: "bridge_cast_sext",
        src: r#"theorem bridge_cast_sext (v : Int) :
    TrustIr.Sem.run
      (TrustIr.semCast TrustIr.CastOp.SExt TrustIr.Ty.I8 TrustIr.Ty.I16 (TrustIr.ValueId.mk 0))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.ValueId.mk 1,
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
              (TrustIr.ValueId.mk 1)
              (TrustIr.Value.int 16
                (((TrustIr.toSigned v 8 % (2:Int)^16) + (2:Int)^16) % (2:Int)^16)),
          nextValueId := 2 }) := rfl
"#,
    },
];

/// Extra concrete-value anchor rows (Full mode only), same spirit as
/// [`UNOP_CONC_SRC`] / [`ICMP_CONC_SRC`]: `truncateUnsigned` exercised both
/// wrapping (300 at width 8 → 44) and as a no-op (44 already fits), and the
/// SExt wrap formula exercised both branches of its internal `if` (a
/// NEGATIVE signed value at 200/width-8 → -56, re-encoded as 65480 at
/// width 16; a POSITIVE signed value at 5/width-8 stays 5). A bridge that
/// only handled one branch of the SExt `if` would fail one of these.
const CAST_CONC_SRC: &str = r#"theorem cast_trunc_wrap_conc : TrustIr.truncateUnsigned 300 8 = 44 := rfl
theorem cast_trunc_noop_conc : TrustIr.truncateUnsigned 44 8 = 44 := rfl
theorem cast_sext_neg_conc :
    ((TrustIr.toSigned 200 8 % (2:Int)^16) + (2:Int)^16) % (2:Int)^16 = 65480 := rfl
theorem cast_sext_pos_conc :
    ((TrustIr.toSigned 5 8 % (2:Int)^16) + (2:Int)^16) % (2:Int)^16 = 5 := rfl
"#;
/// Number of concrete rows in [`CAST_CONC_SRC`].
pub const CAST_CONC_ROWS: usize = 4;

/// TIER 2 — the ZExt widening-identity connecting corollary (pure `Int`
/// arithmetic, no monad): a WIDENING (already-in-range) unsigned cast is the
/// IDENTITY on the value, genuinely proving `mirsem.rs::
/// resolve_widening_cast_rvalue`'s claim ("zero-/sign-extension changes
/// representation, not value") for the unsigned case. Proven directly from
/// imported Lean-core `Int.emod_eq_of_lt` — no helper lemmas needed.
const CAST_ZEXT_WIDENING_NAME: &str = "bridge_cast_zext_widening_identity";
const CAST_ZEXT_WIDENING_SRC: &str = r#"theorem bridge_cast_zext_widening_identity (v : Int) (dstW : Nat) (h0 : 0 ≤ v) (h1 : v < (2:Int) ^ dstW) :
    TrustIr.truncateUnsigned v dstW = v := Int.emod_eq_of_lt h0 h1
"#;

/// TIER 2 (GAP-CROSS-SIGN-WIDEN, 2026-07-16) — the SIGN-CROSSING widening-identity
/// connecting corollary, kernel-anchoring the NEW clause in
/// `mirsem::resolve_widening_cast_rvalue` / `prove::ir_resolve_widening_cast_rvalue`
/// (a widening `u_w -> i_W`, `W > w`, modeled as the value-IDENTITY). In the
/// vendored `semCast` model such a cast ZERO-EXTENDS (raw encode
/// `truncateUnsigned v dstW`), and the SIGNED observation of that width-`dstW`
/// value is `toSigned (truncateUnsigned v dstW) dstW`. For a source value
/// `v ∈ [0, 2^w)` with `w < W` we have `0 ≤ v`, `v < 2^dstW` (encode is the
/// identity — the SAME `Int.emod_eq_of_lt` fact the unsigned corollary uses) AND
/// `v < 2^(dstW-1)` (top bit clear ⇒ the reinterpret is the identity), so the
/// composed cast is `= v`. Genuinely proving mirsem/prove's "zero-extend then
/// reinterpret is value-preserving for a STRICT widening" claim against trust-ir's
/// real pure core. Crucially it needs NO `0 < 2^n`-for-symbolic-`n` fact (the exact
/// obstacle that blocked the SExt corollary — see the doc above `CAST_COMPOSED_SRC`):
/// both range hypotheses are supplied directly, and the `if`-reduction closes on the
/// decidable `¬(2^(dstW-1) ≤ v)` from `hhalf`.
const CAST_ZEXT_SIGNCROSS_NAME: &str = "bridge_cast_zext_signcross_widening_identity";
const CAST_ZEXT_SIGNCROSS_SRC: &str = r#"theorem bridge_cast_zext_signcross_widening_identity (v : Int) (dstW : Nat) (h0 : 0 ≤ v) (hmod : v < (2:Int) ^ dstW) (hhalf : v < (2:Int) ^ (dstW - 1)) :
    TrustIr.toSigned (TrustIr.truncateUnsigned v dstW) dstW = v := by
  have ht : TrustIr.truncateUnsigned v dstW = v := Int.emod_eq_of_lt h0 hmod
  rw [ht]
  simp only [TrustIr.toSigned]
  rw [Int.emod_eq_of_lt h0 hmod]
  have hnot : ¬ (v ≥ (2:Int) ^ (dstW - 1)) := fun hc => absurd hhalf (Int.not_lt.mpr hc)
  exact if_neg hnot
"#;

/// TIER 2, ATTEMPTED BUT NOT DELIVERED — the analogous SExt widening-identity
/// corollary (sign-extension preserves the SIGNED value via an encode→decode
/// round-trip, `toSigned (wrap (toSigned v srcW)) dstW = toSigned v srcW`) is
/// mathematically real and was fully proven against a genuine Lean 4.8.0
/// toolchain (case-split on the sign of the intermediate value, using only
/// imported Lean-core `Int.emod_eq_of_lt` / `Int.emod_nonneg` /
/// `Int.emod_lt_of_pos` / `Int.add_mul_emod_self_left` / `Int.pow_succ` /
/// `Int.mul_pos` / `Int.NonNeg.mk`). It is NOT included here: proving the one
/// extra fact it needs beyond `bridge_cast_zext_widening_identity` — `(0:Int)
/// < (2:Int)^n` for a SYMBOLIC `n` — hits a genuine clean-elaborator
/// limitation confirmed by direct probing (isolated, reproducible): clean's
/// kernel definitional-equality checker for `Int.le`/`Int.NonNeg` (`Int.le a b
/// := (b - a).NonNeg`) does not fully normalize `Int.sub` on a term built from
/// `HPow.hPow` with a symbolic Nat exponent consistently between the
/// expected- and inferred-type derivations of an `Eq.mpr`/`congrArg` step —
/// observed as a `rigid head/arity mismatch: Int.rec vs Int.ofNat` kernel
/// rejection of a term REAL Lean 4.8 accepts outright. This is a genuine
/// clean-side gap (not a mathematical error, not a soundness issue — clean
/// correctly REFUSES rather than mis-accepts), reported here rather than
/// worked around with a weaker or dishonest substitute. `truncateUnsigned`'s
/// ZExt corollary needs no such fact (its hypothesis is `v < 2^dstW`
/// directly, no `2^n > 0` detour), which is why it delivers cleanly.
///
/// The COMPOSED Cast agreement theorem: one proposition, the conjunction of
/// the 3 arms + the 1 Tier-2 widening-identity corollary (4 conjuncts),
/// proved by the already-kernel-checked theorems above.
const CAST_COMPOSED_NAME: &str = "bridge_semCast_agreement_all";
const CAST_COMPOSED_SRC: &str = r#"theorem bridge_semCast_agreement_all :
    (∀ (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false),
      TrustIr.Sem.run
        (TrustIr.semCast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.ValueId.mk 1,
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 8)),
            nextValueId := 2 }))
  ∧ (∀ (v : Int),
      TrustIr.Sem.run
        (TrustIr.semCast TrustIr.CastOp.ZExt TrustIr.Ty.U8 TrustIr.Ty.U16 (TrustIr.ValueId.mk 0))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.ValueId.mk 1,
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 16 (TrustIr.truncateUnsigned v 16)),
            nextValueId := 2 }))
  ∧ (∀ (v : Int),
      TrustIr.Sem.run
        (TrustIr.semCast TrustIr.CastOp.SExt TrustIr.Ty.I8 TrustIr.Ty.I16 (TrustIr.ValueId.mk 0))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.ValueId.mk 1,
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                (TrustIr.ValueId.mk 1)
                (TrustIr.Value.int 16
                  (((TrustIr.toSigned v 8 % (2:Int)^16) + (2:Int)^16) % (2:Int)^16)),
            nextValueId := 2 }))
  ∧ (∀ (v : Int) (dstW : Nat) (h0 : 0 ≤ v) (h1 : v < (2:Int) ^ dstW),
      TrustIr.truncateUnsigned v dstW = v) :=
  by
    constructor
    exact bridge_cast_trunc
    constructor
    exact bridge_cast_zext
    constructor
    exact bridge_cast_sext
    exact bridge_cast_zext_widening_identity
"#;

/// Cast forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run, mirroring [`FORGERY_PROBES`] / [`UNOP_FORGERY_
/// PROBES`] / [`OVERFLOW_FORGERY_PROBES`] / [`ICMP_FORGERY_PROBES`]. Named in
/// the mission brief: (1) `SExt` claimed to agree with `truncateUnsigned`
/// WITHOUT `toSigned` (signed/unsigned confusion, the same #1 real-world bug
/// class as the ICmp forgery); (2) `Trunc` claimed to truncate to the WRONG
/// width (`srcW` instead of `dstW`). Both are `∀ (v : Int), …` — REJECTED for
/// a fully symbolic `v`, a stronger check than a single numeric
/// counterexample (confirmed kernel-REJECTED against the real Lean-toolchain
/// probe harness). The wrong-width probe observes only the exact destination
/// slot. Comparing whole `MachineState`s after the fat-pointer memory model
/// landed made defeq eagerly normalize unrelated memory fields before reaching
/// the intended width mismatch.
const CAST_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "signed-without-toSigned (SExt claimed to agree with truncateUnsigned, no toSigned)",
        r#"theorem bridge_cast_sext_wrong (v : Int) :
    TrustIr.Sem.run
      (TrustIr.semCast TrustIr.CastOp.SExt TrustIr.Ty.I8 TrustIr.Ty.I16 (TrustIr.ValueId.mk 0))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.ValueId.mk 1,
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 16 (TrustIr.truncateUnsigned v 16)),
          nextValueId := 2 }) := rfl
"#,
    ),
    (
        "wrong-width (Trunc claimed to truncate to srcW instead of dstW)",
        r#"theorem bridge_cast_trunc_wrong_width (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false) :
    (match TrustIr.Sem.run
        (TrustIr.semCast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 } with
      | .ok p => Except.ok (p.2.locals.get (TrustIr.ValueId.mk 1))
      | .error e => Except.error e) =
    Except.ok (some (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 16))) :=
  Eq.trans
    (congrArg
      (fun p : Except TrustIr.SemError (TrustIr.ValueId × TrustIr.MachineState) =>
        match p with
        | .ok p => Except.ok (p.2.locals.get (TrustIr.ValueId.mk 1))
        | .error e => Except.error e)
      (bridge_cast_trunc v hbool))
    (congrArg
      (fun x : Int => Except.ok (some (TrustIr.Value.int 8 x)))
      (Eq.refl (TrustIr.truncateUnsigned v 8) :
        TrustIr.truncateUnsigned v 8 = TrustIr.truncateUnsigned v 16))
"#,
    ),
    // GAP-CROSS-SIGN-WIDEN (2026-07-16): the sign-crossing widening identity
    // claimed WITHOUT the strict-widening (top-bit-clear) hypothesis. Drop
    // `v < 2^(dstW-1)` and the claim is FALSE — a value `v ∈ [2^(dstW-1), 2^dstW)`
    // fits the width but reinterprets NEGATIVE (`toSigned v dstW = v - 2^dstW ≠ v`,
    // e.g. `u16 40000 -> i16` at width 16 is `-25536`). This is EXACTLY the
    // accepting-but-wrong variant a same-width / non-strict-widening sign cross
    // would be: the mirsem/prove clause is gated to `dw > sw` precisely to exclude
    // it. Stated at width 16 with `:= rfl`; clean must REJECT (the `if` cannot
    // reduce for a symbolic `v` whose sign is undetermined).
    (
        "signcross-without-half-bound (u_w -> i_w reinterpret claimed value-preserving, no strict widening)",
        r#"theorem bridge_cast_signcross_wrong (v : Int) (dstW : Nat) (h0 : 0 ≤ v) (hmod : v < (2:Int) ^ dstW) :
    TrustIr.toSigned (TrustIr.truncateUnsigned v dstW) dstW = v := by
  have ht : TrustIr.truncateUnsigned v dstW = v := Int.emod_eq_of_lt h0 hmod
  rw [ht]
  simp only [TrustIr.toSigned]
  rw [Int.emod_eq_of_lt h0 hmod]
  have hnot : ¬ (v ≥ (2:Int) ^ (dstW - 1)) := fun hc => absurd hmod (Int.not_lt.mpr hc)
  exact if_neg hnot
"#,
    ),
];

/// Un-bridged Cast arms, reported honestly (never faked): `(op, reason)`. The
/// 14 non-integer `CastOp` variants — neither `clean_ground.rs` nor
/// `trustir_anchor.rs` models ANY cast Formula/Expr (confirmed by grep), so
/// no agreement claim is made for any of them; this mirrors `UnOp::CtPop` /
/// unsigned-`MulOverflow`'s flag.
const CAST_UNBRIDGED: &[(&str, &str)] = &[
    (
        "FPTrunc",
        "float-precision truncation axiomatized via Lean's Float (always f64 in the model; no \
         rounding-mode denotation to agree against)",
    ),
    ("FPExt", "float-precision extension axiomatized via Lean's Float (always f64 in the model)"),
    (
        "FPToUI",
        "raw float-to-unsigned-int conversion has an exact frExp truncation and a NaN/out-of-range \
         UB guard in trust-ir, but Clean has no float-to-int denotation to agree against",
    ),
    (
        "FPToSI",
        "raw float-to-signed-int conversion has exact frExp truncation plus two's-complement \
         re-encoding and UB guards in trust-ir, but no matching Clean denotation",
    ),
    (
        "UIToFP",
        "unsigned-int-to-float conversion axiomatized (Float.ofNat); not a bit-exact IEEE 754 \
         rounding proof",
    ),
    (
        "SIToFP",
        "signed-int-to-float conversion axiomatized (Float.ofInt at the toSigned image); same \
         opaque rounding gap as UIToFP",
    ),
    (
        "PtrToInt",
        "pointer-to-integer address reinterpretation; Clean has no denotation for trust-ir's \
         pointer/address model",
    ),
    ("IntToPtr", "integer-to-pointer reinterpretation; same pointer-model gap as PtrToInt"),
    ("Bitcast", "polymorphic same-width int/ptr reinterpret; Clean models no bitcast denotation"),
    (
        "PtrToPtr",
        "provenance retag only (address unchanged, no arithmetic content) — Clean has no \
         pointer-provenance denotation to agree against",
    ),
    (
        "Transmute",
        "scalar-only partial byte-reinterpret model (mirrors Bitcast); same honest gap, plus the \
         model itself rejects every non-scalar shape (aggregate/float/vector/…)",
    ),
    (
        "ReifyFnPointer",
        "function-item-to-pointer reification (fn item -> Value.closure, unchanged pending \
         FuncPtrTable access); Clean has no closure/function-pointer denotation",
    ),
    (
        "FPToSISat",
        "total saturating float-to-signed-int conversion (NaN -> 0, clamp, exact frExp \
         truncation) exists in trust-ir, but Clean has no matching float-to-int denotation",
    ),
    (
        "FPToUISat",
        "total saturating float-to-unsigned-int conversion (NaN/negative -> 0, clamp, exact \
         frExp truncation) exists in trust-ir, but Clean has no matching denotation",
    ),
];

// ---------------------------------------------------------------------------
// stepInst .BinOp — the FIRST statement/instruction-level agreement (extends
// the bridge from operation VALUES to the monadic INSTRUCTION dispatch
// itself: `stepInst`'s READ-both-operands -> COMPUTE (`semIntBinOp`,
// ALREADY bridged) -> WRITE-fresh-result chain). `stepInst` lives in the NEW
// `TrustIr/Semantics/Step.lean` module the Step-retargeted closure now
// vendors. See the module-level "EXTENSION 5" doc comment above for the full
// technique / residue breakdown.
// ---------------------------------------------------------------------------

/// One stepInst-BinOp agreement arm: `(op, chain theorem, chain src, connect
/// theorem, connect src)`. The seven integer arithmetic
/// arms preserve each existing value theorem's exact side conditions. Division
/// and remainder additionally require their original nonzero and signed
/// overflow guards; none of those premises is discharged by the transport.
struct StepBinOpArmSpec {
    op: &'static str,
    /// The READ->COMPUTE->WRITE chain identity, stated
    /// generically in terms of the already-bridged `semIntBinOp` (not a
    /// hand-inlined wrap formula).
    chain_theorem: &'static str,
    chain_src: &'static str,
    /// The CONNECT theorem: composes the chain lemma with the
    /// already-proven matching value theorem from [`ARMS`]. The arithmetic
    /// operation and its guards remain exactly those of the shared semantics.
    connect_theorem: &'static str,
    connect_src: &'static str,
}

/// Shared proof-only transport: actual Sem.bindFresh, full state and error preservation.
/// No operation is evaluated by this helper; each connect consumes an existing value theorem.
const STEPINST_BINOP_TRANSPORT_SRC: &str = r#"theorem stepinst_binop_result_transport (r : Except TrustIr.SemError Int) (v_l v_r : Int) :
    TrustIr.Sem.run
      (@StateT.bind TrustIr.MachineState (Except TrustIr.SemError) (@Except.instMonad TrustIr.SemError)
        TrustIr.ValueId TrustIr.InstrResult
        (match Except.bind r (fun result => Except.ok (TrustIr.Value.int 8 result)) with
          | .ok value => TrustIr.Sem.bindFresh value
          | .error e => (fun _ => Except.error e))
        (fun vid => @StateT.pure TrustIr.MachineState (Except TrustIr.SemError)
          (@Except.instMonad TrustIr.SemError) TrustIr.InstrResult
          (TrustIr.InstrResult.value (some vid))))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e)  := Except.rec
  (fun e => @Eq.refl (Except TrustIr.SemError (TrustIr.InstrResult × TrustIr.MachineState)) (Except.error e))
  (fun result => @Eq.refl (Except TrustIr.SemError (TrustIr.InstrResult × TrustIr.MachineState))
    (Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 }))) r

theorem stepinst_binop_int_chain (op : TrustIr.BinOp) (hnot : op.isMinMax = false) (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp op TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp op 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e)  := Eq.trans
  (congrArg (fun flag : Bool => TrustIr.Sem.run
      (@StateT.bind TrustIr.MachineState (Except TrustIr.SemError) (@Except.instMonad TrustIr.SemError)
        TrustIr.ValueId TrustIr.InstrResult
        (@ite (TrustIr.Sem TrustIr.ValueId) (flag = Bool.true) (instDecidableEqBool flag Bool.true)
          (TrustIr.semFloatMinMax op TrustIr.Ty.I8 (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1))
          (TrustIr.semBinOpDeterministic op TrustIr.Ty.I8 (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
        (fun vid => @StateT.pure TrustIr.MachineState (Except TrustIr.SemError)
          (@Except.instMonad TrustIr.SemError) TrustIr.InstrResult
          (TrustIr.InstrResult.value (some vid))))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 }) hnot)
  (stepinst_binop_result_transport (TrustIr.semIntBinOp op 8 v_l v_r) v_l v_r)

theorem stepinst_binop_int_of_value (op : TrustIr.BinOp) (hnot : op.isMinMax = false)
    (v_l v_r result : Int) (hvalue : TrustIr.semIntBinOp op 8 v_l v_r = Except.ok result) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp op TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (result)),
          nextValueId := 3 }) := by
  rw [stepinst_binop_int_chain op hnot v_l v_r, hvalue]
"#;

const STEPINST_BINOP_ARMS: &[StepBinOpArmSpec] = &[
    StepBinOpArmSpec {
        op: "Add",
        chain_theorem: "stepinst_binop_add_chain",
        chain_src: r#"theorem stepinst_binop_add_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Add 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.Add rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_add",
        connect_src: r#"theorem bridge_stepInst_binop_add (v_l v_r : Int)
    (h0 : 0 ≤ Int.add v_l v_r) (h1 : Int.add v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.add v_l v_r)),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.Add rfl v_l v_r (Int.add v_l v_r)
    (bridge_add 8 v_l v_r h0 h1)
"#,
    },
    StepBinOpArmSpec {
        op: "Sub",
        chain_theorem: "stepinst_binop_sub_chain",
        chain_src: r#"theorem stepinst_binop_sub_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Sub TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Sub 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.Sub rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_sub",
        connect_src: r#"theorem bridge_stepInst_binop_sub (v_l v_r : Int)
    (h0 : 0 ≤ Int.sub v_l v_r) (h1 : Int.sub v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Sub TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.sub v_l v_r)),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.Sub rfl v_l v_r (Int.sub v_l v_r)
    (bridge_sub 8 v_l v_r h0 h1)
"#,
    },
    StepBinOpArmSpec {
        op: "Mul",
        chain_theorem: "stepinst_binop_mul_chain",
        chain_src: r#"theorem stepinst_binop_mul_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Mul TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Mul 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.Mul rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_mul",
        connect_src: r#"theorem bridge_stepInst_binop_mul (v_l v_r : Int)
    (h0 : 0 ≤ Int.mul v_l v_r) (h1 : Int.mul v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Mul TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.mul v_l v_r)),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.Mul rfl v_l v_r (Int.mul v_l v_r)
    (bridge_mul 8 v_l v_r h0 h1)
"#,
    },
    StepBinOpArmSpec {
        op: "UDiv",
        chain_theorem: "stepinst_binop_udiv_chain",
        chain_src: r#"theorem stepinst_binop_udiv_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.UDiv 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.UDiv rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_udiv",
        connect_src: r#"theorem bridge_stepInst_binop_udiv (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (h0 : 0 ≤ Int.ediv v_l v_r) (h1 : Int.ediv v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.ediv v_l v_r)),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.UDiv rfl v_l v_r (Int.ediv v_l v_r)
    (bridge_udiv 8 v_l v_r hz h0 h1)
"#,
    },
    StepBinOpArmSpec {
        op: "SDiv",
        chain_theorem: "stepinst_binop_sdiv_chain",
        chain_src: r#"theorem stepinst_binop_sdiv_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.SDiv 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.SDiv rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_sdiv",
        connect_src: r#"theorem bridge_stepInst_binop_sdiv (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (hmin : ((TrustIr.toSigned v_l 8 == -((2 : Int) ^ (8 - 1))) && (TrustIr.toSigned v_r 8 == -1)) = false)
    (h0 : 0 ≤ Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8)) (h1 : Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8) < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8))),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.SDiv rfl v_l v_r (Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8))
    (bridge_sdiv 8 v_l v_r hz hmin h0 h1)
"#,
    },
    StepBinOpArmSpec {
        op: "URem",
        chain_theorem: "stepinst_binop_urem_chain",
        chain_src: r#"theorem stepinst_binop_urem_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.URem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.URem 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.URem rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_urem",
        connect_src: r#"theorem bridge_stepInst_binop_urem (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (h0 : 0 ≤ Int.emod v_l v_r) (h1 : Int.emod v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.URem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.emod v_l v_r)),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.URem rfl v_l v_r (Int.emod v_l v_r)
    (bridge_urem 8 v_l v_r hz h0 h1)
"#,
    },
    StepBinOpArmSpec {
        op: "SRem",
        chain_theorem: "stepinst_binop_srem_chain",
        chain_src: r#"theorem stepinst_binop_srem_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SRem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.SRem 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := stepinst_binop_int_chain TrustIr.BinOp.SRem rfl v_l v_r
"#,
        connect_theorem: "bridge_stepInst_binop_srem",
        connect_src: r#"theorem bridge_stepInst_binop_srem (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (hmin : ((TrustIr.toSigned v_l 8 == -((2 : Int) ^ (8 - 1))) && (TrustIr.toSigned v_r 8 == -1)) = false)
    (h0 : 0 ≤ Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8)) (h1 : Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8) < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SRem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8))),
          nextValueId := 3 }) :=
  stepinst_binop_int_of_value TrustIr.BinOp.SRem rfl v_l v_r (Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8))
    (bridge_srem 8 v_l v_r hz hmin h0 h1)
"#,
    },
];

/// The COMPOSED stepInst-BinOp agreement theorem: one proposition, the
/// conjunction of the seven CONNECT theorems, proved by the
/// already-kernel-checked theorems above.
const STEPINST_BINOP_COMPOSED_NAME: &str = "bridge_stepInst_binop_agreement_all";
const STEPINST_BINOP_COMPOSED_SRC: &str = r#"theorem bridge_stepInst_binop_agreement_all :
    (∀ (v_l v_r : Int)
    (h0 : 0 ≤ Int.add v_l v_r) (h1 : Int.add v_l v_r < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.add v_l v_r)),
          nextValueId := 3 }))
  ∧ (∀ (v_l v_r : Int)
    (h0 : 0 ≤ Int.sub v_l v_r) (h1 : Int.sub v_l v_r < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Sub TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.sub v_l v_r)),
          nextValueId := 3 }))
  ∧ (∀ (v_l v_r : Int)
    (h0 : 0 ≤ Int.mul v_l v_r) (h1 : Int.mul v_l v_r < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Mul TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.mul v_l v_r)),
          nextValueId := 3 }))
  ∧ (∀ (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (h0 : 0 ≤ Int.ediv v_l v_r) (h1 : Int.ediv v_l v_r < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.ediv v_l v_r)),
          nextValueId := 3 }))
  ∧ (∀ (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (hmin : ((TrustIr.toSigned v_l 8 == -((2 : Int) ^ (8 - 1))) && (TrustIr.toSigned v_r 8 == -1)) = false)
    (h0 : 0 ≤ Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8)) (h1 : Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8) < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.div (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8))),
          nextValueId := 3 }))
  ∧ (∀ (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (h0 : 0 ≤ Int.emod v_l v_r) (h1 : Int.emod v_l v_r < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.URem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.emod v_l v_r)),
          nextValueId := 3 }))
  ∧ (∀ (v_l v_r : Int)
    (hz : (v_r == 0) = false)
    (hmin : ((TrustIr.toSigned v_l 8 == -((2 : Int) ^ (8 - 1))) && (TrustIr.toSigned v_r 8 == -1)) = false)
    (h0 : 0 ≤ Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8)) (h1 : Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8) < (2 : Int) ^ 8),
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SRem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.mod (TrustIr.toSigned v_l 8) (TrustIr.toSigned v_r 8))),
          nextValueId := 3 })) :=
  And.intro bridge_stepInst_binop_add (And.intro bridge_stepInst_binop_sub (And.intro bridge_stepInst_binop_mul (And.intro bridge_stepInst_binop_udiv (And.intro bridge_stepInst_binop_sdiv (And.intro bridge_stepInst_binop_urem (bridge_stepInst_binop_srem))))))
"#;

/// stepInst-BinOp forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run, mirroring [`FORGERY_PROBES`] / [`ICMP_FORGERY_
/// PROBES`] / [`CAST_FORGERY_PROBES`]. Index 0 (used alone in Spot mode)
/// depends only on `stepInst`/`semIntBinOp` (always present); index 1
/// additionally depends on the `Sub` chain/connect arms, so it only runs in
/// Full mode.
const STEPINST_BINOP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-op-agreement (stepInst's BinOp.Add chain claimed to agree with semIntBinOp .Sub)",
        r#"theorem bridge_stepInst_binop_add_wrong_op (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Sub 8 v_l v_r with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
              nextValueId := 3 })
      | .error e => Except.error e) := rfl
"#,
    ),
    (
        "swapped-operand (Sub's connect theorem claimed to bind Int.sub v_r v_l, operands swapped)",
        r#"theorem bridge_stepInst_binop_sub_swapped (v_l v_r : Int)
    (h0 : 0 ≤ Int.sub v_l v_r) (h1 : Int.sub v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.Sub TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.sub v_r v_l)),
          nextValueId := 3 }) :=
  Eq.trans (stepinst_binop_sub_chain v_l v_r)
    (congrArg (fun (x : Except TrustIr.SemError Int) => match x with
        | .ok result =>
          Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
            { TrustIr.MachineState.empty with
                locals :=
                  ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                      (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                    (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 result),
                nextValueId := 3 })
        | .error e => Except.error e)
      (bridge_sub 8 v_l v_r h0 h1))
"#,
    ),
    ("UDiv false result", r#"theorem stepinst_udiv_false_result :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (4)),
          nextValueId := 3 }) := rfl
"#),
    ("SDiv false result", r#"theorem stepinst_sdiv_false_result :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 249)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 249)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (4)),
          nextValueId := 3 }) := rfl
"#),
    ("URem false result", r#"theorem stepinst_urem_false_result :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.URem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (0)),
          nextValueId := 3 }) := rfl
"#),
    ("SRem false result", r#"theorem stepinst_srem_false_result :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SRem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (0)),
          nextValueId := 3 }) := rfl
"#),
    ("zero divisor cannot succeed", r#"theorem stepinst_udiv_zero_divisor :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 0),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 0)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (0)),
          nextValueId := 3 }) := rfl
"#),
    ("signed INT_MIN / -1 cannot succeed", r#"theorem stepinst_sdiv_overflow_guard :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 128)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 255),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 128)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 255)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (128)),
          nextValueId := 3 }) := rfl
"#),
    ("signed INT_MIN % -1 cannot succeed", r#"theorem stepinst_srem_overflow_guard :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SRem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 128)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 255),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 128)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 255)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (0)),
          nextValueId := 3 }) := rfl
"#),
    ("wrong divisor in result", r#"theorem stepinst_udiv_wrong_divisor :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.ediv 7 3)),
          nextValueId := 3 }) := rfl
"#),
    ("wrong result destination", r#"theorem stepinst_udiv_wrong_destination :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 3)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 (3)),
          nextValueId := 3 }) := rfl
"#),
    ("wrong allocation cursor", r#"theorem stepinst_udiv_wrong_cursor :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (3)),
          nextValueId := 4 }) := rfl
"#),
    ("input operand must be preserved", r#"theorem stepinst_udiv_wrong_preserved_input :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 9)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (3)),
          nextValueId := 3 }) := rfl
"#),
];

const STEPINST_DIVREM_CONCRETE_SRC: &str = r#"theorem stepinst_divrem_concrete_udiv :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.UDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (3)),
          nextValueId := 3 }) := rfl

theorem stepinst_divrem_concrete_sdiv :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SDiv TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 249)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 249)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (3)),
          nextValueId := 3 }) := rfl

theorem stepinst_divrem_concrete_urem :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.URem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (1)),
          nextValueId := 3 }) := rfl

theorem stepinst_divrem_concrete_srem :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.BinOp TrustIr.BinOp.SRem TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 7)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 254)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (1)),
          nextValueId := 3 }) := rfl
"#;

/// Un-bridged stepInst-BinOp ops, reported honestly (never faked): `(op,
/// reason)`. The other 11 `semIntBinOp` ops reachable through this SAME
/// `stepInst` `.BinOp` arm — bridged at the VALUE level ([`ARMS`]) but not
/// yet chained through `stepInst` (the technique generalizes directly; not
/// yet executed for these).
const STEPINST_BINOP_UNBRIDGED: &[(&str, &str)] = &[(
    "FAdd/FSub/FMul/FDiv/FRem/And/Or/Xor/Shl/LShr/AShr",
    "these 11 semIntBinOp ops are already bridged at the VALUE level (ARMS); the \
     stepInst chain+connect transport used by the seven integer arithmetic arms generalizes \
     directly (reuse the corresponding bridge_* arm) but has not yet been executed \
     for them — named as concrete next work, not faked",
)];

/// Un-bridged stepInst Inst CATEGORIES (beyond `.BinOp`), reported honestly
/// (never faked): `(category, reason)`. 52 of `Inst`'s 57 variants (UnOp/
/// Overflow/ICmp/Cast are chained as of EXTENSION 9, one representative op
/// each — see [`STEPINST_UNOP_UNBRIDGED`] / [`STEPINST_OVERFLOW_UNBRIDGED`] /
/// [`STEPINST_ICMP_UNBRIDGED`] / [`STEPINST_CAST_UNBRIDGED`] for the other
/// ops in each of those categories, honestly still un-chained).
const STEPINST_CATEGORIES_UNBRIDGED: &[(&str, &str)] = &[
    (
        "FCmp (1 category)",
        "the underlying VALUE semantics (semFCmpInst/semFCmp, IEEE 754 ordered/unordered \
         float comparison) is NOT bridged at the value level at all yet (Phase 1 \
         axiomatizes float comparison via Lean's Float type) — no stepInst chain is \
         possible until the value layer is bridged first. UnOp/Overflow/ICmp/Cast, the \
         other 4 of the original 5 value-bridged-but-unchained categories named here, are \
         now stepInst-chained (EXTENSION 9, one representative op each)",
    ),
    (
        "the other 51 Inst variants",
        "constants (Const/NullPtr/Undef), pseudo-ops (Copy/Select), proof instructions \
         (Assume/Assert), control-flow terminators (Br/CondBr/Switch/Return/Unreachable), \
         memory (Load/Store/Alloca/HeapAlloc/GEP/PtrData/PtrMetadata/PtrFromParts/Dealloc), \
         atomics (AtomicLoad/AtomicStore/AtomicRMW/CmpXchg/Fence), aggregates \
         (ExtractField/InsertField/ExtractElement/InsertElement/SeqMap/SeqMapAddK/ \
         SeqMapNot), borrow/ARC (Borrow/BorrowMut/EndBorrow/Retain/Release/IsUnique), \
         binding frames (OpenFrame/BindSlot/LoadSlot/CloseFrame), calls (Call/ \
         CallIndirect), exception handling (Invoke/LandingPad/Resume), coroutines \
         (CoroSuspend), and dialect ops (DialectOp) — none of these has a value-level \
         bridge yet either (many read/write MachineState fields entirely outside the \
         scalar-arithmetic cone this bridge covers); evalBody/evalCfg (the \
         multi-instruction / control-flow / loop layer above stepInst) remain entirely \
         unbridged",
    ),
];

// ---------------------------------------------------------------------------
// stepInst .UnOp / .Overflow / .ICmp / .Cast — EXTENSION 9: completing
// EXTENSION 5's instruction-execution technique for every OTHER Inst
// category whose VALUE core is already bridged, one representative op each
// (Neg / unsigned-AddOverflow / Ult / Trunc). See the module-level
// "EXTENSION 9" doc comment above for the full per-category technique and
// residue breakdown.
// ---------------------------------------------------------------------------

/// stepInst-UnOp: `.UnOp Neg` — `semUnOp` unwraps the operand's `.int w v`
/// shape then calls the ALREADY-BRIDGED `semIntUnOp`. Mirrors
/// [`StepBinOpArmSpec`] one operand narrower.
struct StepUnOpArmSpec {
    op: &'static str,
    chain_theorem: &'static str,
    chain_src: &'static str,
    connect_theorem: &'static str,
    connect_src: &'static str,
}

const STEPINST_UNOP_ARMS: &[StepUnOpArmSpec] = &[StepUnOpArmSpec {
    op: "Neg",
    chain_theorem: "stepinst_unop_neg_chain",
    chain_src: r#"theorem stepinst_unop_neg_chain (v : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    (match TrustIr.semIntUnOp TrustIr.UnOp.Neg 8 v with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
          { TrustIr.MachineState.empty with
              locals :=
                (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 result),
              nextValueId := 2 })
      | .error e => Except.error e) := rfl
"#,
    connect_theorem: "bridge_stepInst_unop_neg",
    connect_src: r#"theorem bridge_stepInst_unop_neg (v : Int)
    (h0 : 0 ≤ Int.neg v) (h1 : Int.neg v < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (Int.neg v)),
          nextValueId := 2 }) :=
  by
    rw [stepinst_unop_neg_chain v, bridge_neg 8 v h0 h1]
"#,
}];

/// The bonus sub-zero-form corollary (Neg only): composes the SAME chain
/// with `bridge_neg_sub_zero_form` (EXTENSION 1's connecting corollary to
/// clean_ground's exact `Int.sub (Int.ofNat 0) operand` spelling) instead of
/// `bridge_neg` — a genuine second connect, not a relaxation.
const STEPINST_UNOP_NEG_SUBZERO_NAME: &str = "bridge_stepInst_unop_neg_sub_zero_form";
const STEPINST_UNOP_NEG_SUBZERO_SRC: &str = r#"theorem bridge_stepInst_unop_neg_sub_zero_form (v : Int)
    (h0 : 0 ≤ Int.neg v) (h1 : Int.neg v < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (Int.sub (Int.ofNat 0) v)),
          nextValueId := 2 }) :=
  by
    rw [stepinst_unop_neg_chain v, bridge_neg_sub_zero_form 8 v h0 h1]
"#;

const STEPINST_UNOP_COMPOSED_NAME: &str = "bridge_stepInst_unop_agreement_all";
const STEPINST_UNOP_COMPOSED_SRC: &str = r#"theorem bridge_stepInst_unop_agreement_all :
    (∀ (v : Int) (h0 : 0 ≤ Int.neg v) (h1 : Int.neg v < (2 : Int) ^ 8),
      TrustIr.Sem.run
        (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (Int.neg v)),
            nextValueId := 2 }))
  ∧ (∀ (v : Int) (h0 : 0 ≤ Int.neg v) (h1 : Int.neg v < (2 : Int) ^ 8),
      TrustIr.Sem.run
        (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (Int.sub (Int.ofNat 0) v)),
            nextValueId := 2 })) :=
  And.intro bridge_stepInst_unop_neg bridge_stepInst_unop_neg_sub_zero_form
"#;

/// stepInst-UnOp forgery probes: mirrors [`STEPINST_BINOP_FORGERY_PROBES`].
const STEPINST_UNOP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-op-agreement (stepInst's UnOp.Neg chain claimed to agree with semIntUnOp .Not)",
        r#"theorem bridge_stepInst_unop_neg_wrong_op (v : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    (match TrustIr.semIntUnOp TrustIr.UnOp.Not 8 v with
      | .ok result =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
          { TrustIr.MachineState.empty with
              locals :=
                (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 result),
              nextValueId := 2 })
      | .error e => Except.error e) := rfl
"#,
    ),
    (
        "dropped-negation (Neg's destination claimed to be the untouched operand v)",
        r#"theorem bridge_stepInst_unop_neg_identity_wrong (v : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v),
          nextValueId := 2 }) := rfl
"#,
    ),
];

/// Un-bridged stepInst-UnOp ops (value-bridged via [`UNOP_ARMS`], chain not
/// yet executed): `(op, reason)`.
const STEPINST_UNOP_UNBRIDGED: &[(&str, &str)] = &[(
    "Not/FNeg",
    "both are already bridged at the VALUE level (UNOP_ARMS); the stepInst chain+connect \
     technique demonstrated for Neg generalizes directly (reuse bridge_not/bridge_fneg) but \
     has not yet been executed for them",
)];

/// stepInst-Overflow: unsigned `.Overflow AddOverflow` — `semOverflow` binds
/// TWO fresh SSA values in order: the integer result, then the boolean flag.
/// `InstrResult.values` carries both identities and the allocation cursor
/// advances twice, matching TrustIR WS2.24 and the Rust interpreter.
/// The connect composes with the
/// ALREADY-PROVEN `bridge_overflow_uadd_flag` (EXTENSION 2's FULL-pair FLAG
/// arm, itself UNCONDITIONAL — no side condition), so this connect is
/// unconditional too.
const STEPINST_OVERFLOW_CHAIN_THEOREM: &str = "stepinst_overflow_add_unsigned_chain";
const STEPINST_OVERFLOW_CHAIN_SRC: &str = r#"theorem stepinst_overflow_add_unsigned_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.Overflow TrustIr.OverflowOp.AddOverflow TrustIr.Ty.U8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow 8 false v_l v_r with
      | .ok p =>
        Except.ok (TrustIr.InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3],
          { TrustIr.MachineState.empty with
              locals :=
                (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0)
                      (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 p.1)).set
                  (TrustIr.ValueId.mk 3) (TrustIr.Value.bool p.2),
              nextValueId := 4 })
      | .error e => Except.error e) := rfl
"#;
const STEPINST_OVERFLOW_CONNECT_THEOREM: &str = "bridge_stepInst_overflow_add_unsigned";
const STEPINST_OVERFLOW_CONNECT_SRC: &str = r#"theorem bridge_stepInst_overflow_add_unsigned (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.Overflow TrustIr.OverflowOp.AddOverflow TrustIr.Ty.U8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0)
                  (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8
                    ((((v_l + v_r) % ((2:Int)^8) + (2:Int)^8) % ((2:Int)^8))))).set
              (TrustIr.ValueId.mk 3) (TrustIr.Value.bool
                    (@Decidable.decide (((2:Int)^8 - 1) < (v_l + v_r))
                        (Int.decLt ((2:Int)^8 - 1) (v_l + v_r)) ||
                      @Decidable.decide (v_l + v_r < 0) (Int.decLt (v_l + v_r) 0))),
          nextValueId := 4 }) :=
  by
    rw [stepinst_overflow_add_unsigned_chain v_l v_r, bridge_overflow_uadd_flag 8 v_l v_r]
"#;

const STEPINST_OVERFLOW_COMPOSED_NAME: &str = "bridge_stepInst_overflow_agreement_all";
const STEPINST_OVERFLOW_COMPOSED_SRC: &str = r#"theorem bridge_stepInst_overflow_agreement_all :
    ∀ (v_l v_r : Int),
      TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.Overflow TrustIr.OverflowOp.AddOverflow TrustIr.Ty.U8
            (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
            nextValueId := 2 } =
      Except.ok (TrustIr.InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3],
        { TrustIr.MachineState.empty with
            locals :=
              (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0)
                    (TrustIr.Value.int 8 v_l)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8
                      ((((v_l + v_r) % ((2:Int)^8) + (2:Int)^8) % ((2:Int)^8))))).set
                (TrustIr.ValueId.mk 3) (TrustIr.Value.bool
                      (@Decidable.decide (((2:Int)^8 - 1) < (v_l + v_r))
                          (Int.decLt ((2:Int)^8 - 1) (v_l + v_r)) ||
                        @Decidable.decide (v_l + v_r < 0) (Int.decLt (v_l + v_r) 0))),
            nextValueId := 4 }) :=
  bridge_stepInst_overflow_add_unsigned
"#;

/// stepInst-Overflow forgery probes.
const STEPINST_OVERFLOW_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-op-agreement (unsigned AddOverflow's chain claimed to agree with semOverflowOp SubOverflow)",
        r#"theorem bridge_stepInst_overflow_add_unsigned_wrong_op (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.Overflow TrustIr.OverflowOp.AddOverflow TrustIr.Ty.U8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    (match TrustIr.semOverflowOp TrustIr.OverflowOp.SubOverflow 8 false v_l v_r with
      | .ok p =>
        Except.ok (TrustIr.InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3],
          { TrustIr.MachineState.empty with
              locals :=
                (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 p.1)).set
                  (TrustIr.ValueId.mk 3) (TrustIr.Value.bool p.2),
              nextValueId := 4 })
      | .error e => Except.error e) := rfl
"#,
    ),
    (
        "wrong-threshold (unsigned AddOverflow's flag claimed to use the signed half-width 2^(w-1) threshold)",
        r#"theorem bridge_stepInst_overflow_add_unsigned_wrong_threshold (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.Overflow TrustIr.OverflowOp.AddOverflow TrustIr.Ty.U8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2)
              (TrustIr.Value.int 8
                  ((((v_l + v_r) % ((2:Int)^8) + (2:Int)^8) % ((2:Int)^8))))).set
              (TrustIr.ValueId.mk 3)
              (TrustIr.Value.bool
                  (Decidable.decide (v_l + v_r ≥ (2:Int)^(8-1)) ||
                    Decidable.decide (v_l + v_r < 0))),
          nextValueId := 4 }) := rfl
"#,
    ),
];

/// Un-bridged stepInst-Overflow op×signedness combos (value-bridged via
/// [`OVERFLOW_VALUE_ARMS`]/[`OVERFLOW_FLAG_ARMS`], chain not yet executed):
/// `(combo, reason)`.
const STEPINST_OVERFLOW_UNBRIDGED: &[(&str, &str)] = &[(
    "SubOverflow[u]/MulOverflow[u]/AddOverflow[s]/SubOverflow[s]/MulOverflow[s]",
    "all 5 are already bridged at both VALUE and FLAG levels \
     (OVERFLOW_VALUE_ARMS / OVERFLOW_FLAG_ARMS); the stepInst chain+connect technique \
     demonstrated for unsigned-AddOverflow generalizes directly but has not yet been \
     executed for them",
)];

/// stepInst-ICmp: `.ICmp Ult` — `semICmpInst` binds a fresh `ValueId` to
/// `Value.bool (semICmp op w l r)`; `semICmp` is TOTAL (a `Bool`, not
/// `Except`), so the connect is a direct `congrArg` over `Bool` (no
/// `Except`-match dispatch needed).
const STEPINST_ICMP_CHAIN_THEOREM: &str = "stepinst_icmp_ult_chain";
const STEPINST_ICMP_CHAIN_SRC: &str = r#"theorem stepinst_icmp_ult_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2)
              (TrustIr.Value.bool (TrustIr.semICmp TrustIr.ICmpOp.Ult 8 v_l v_r)),
          nextValueId := 3 }) := rfl
"#;
const STEPINST_ICMP_CONNECT_THEOREM: &str = "bridge_stepInst_icmp_ult";
const STEPINST_ICMP_CONNECT_SRC: &str = r#"theorem bridge_stepInst_icmp_ult (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.bool (Decidable.decide (Int.lt v_l v_r))),
          nextValueId := 3 }) :=
  by
    rw [stepinst_icmp_ult_chain v_l v_r, bridge_icmp_ult 8 v_l v_r]
"#;

const STEPINST_ICMP_COMPOSED_NAME: &str = "bridge_stepInst_icmp_agreement_all";
const STEPINST_ICMP_COMPOSED_SRC: &str = r#"theorem bridge_stepInst_icmp_agreement_all :
    ∀ (v_l v_r : Int),
      TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8
            (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
            nextValueId := 2 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
        { TrustIr.MachineState.empty with
            locals :=
              ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.bool (Decidable.decide (Int.lt v_l v_r))),
            nextValueId := 3 }) :=
  bridge_stepInst_icmp_ult
"#;

/// stepInst-ICmp forgery probes.
const STEPINST_ICMP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-relation (stepInst's ICmp.Ult chain claimed to agree with semICmp .Ugt)",
        r#"theorem bridge_stepInst_icmp_ult_wrong_op (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2)
              (TrustIr.Value.bool (TrustIr.semICmp TrustIr.ICmpOp.Ugt 8 v_l v_r)),
          nextValueId := 3 }) := rfl
"#,
    ),
    (
        "swapped-operand (Ult's connect theorem claimed to bind Int.lt v_r v_l, operands swapped)",
        r#"theorem bridge_stepInst_icmp_ult_swapped (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8
          (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
          nextValueId := 2 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.bool (Decidable.decide (Int.lt v_r v_l))),
          nextValueId := 3 }) :=
  Eq.trans (stepinst_icmp_ult_chain v_l v_r)
    (congrArg
      (fun (b : Bool) =>
        Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.bool b),
              nextValueId := 3 }))
      (bridge_icmp_ult 8 v_l v_r))
"#,
    ),
];

/// Un-bridged stepInst-ICmp ops (value-bridged via [`ICMP_ARMS`], chain not
/// yet executed): `(op, reason)`.
const STEPINST_ICMP_UNBRIDGED: &[(&str, &str)] = &[(
    "Eq/Ne/Ule/Ugt/Uge/Slt/Sle/Sgt/Sge",
    "all 9 are already bridged at the VALUE level (ICMP_ARMS); the stepInst chain+connect \
     technique demonstrated for Ult generalizes directly (reuse the corresponding \
     bridge_icmp_* arm) but has not yet been executed for them",
)];

/// stepInst-Cast: `.Cast Trunc` — UNLIKE `.UnOp`/`.Overflow`/`.ICmp`,
/// `stepInst`'s `.Cast` arm calls `semCast` DIRECTLY (no intermediate
/// wrapper), so the chain collapses stepInst's own monadic layer with
/// `semCast`'s (both `Sem ValueId`-shaped) in one `Sem.run_bind`/
/// `Sem.run_pure` reduction — the mission's "two monadic layers" collapse.
const STEPINST_CAST_CHAIN_THEOREM: &str = "stepinst_cast_trunc_chain";
const STEPINST_CAST_CHAIN_SRC: &str = r#"theorem stepinst_cast_trunc_chain (v : Int) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.Cast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
          nextValueId := 1 } =
    (match TrustIr.Sem.run
        (TrustIr.semCast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 }
      with
      | .ok (vid, state') => Except.ok (TrustIr.InstrResult.value (some vid), state')
      | .error e => Except.error e) := rfl
"#;
const STEPINST_CAST_CONNECT_THEOREM: &str = "bridge_stepInst_cast_trunc";
const STEPINST_CAST_CONNECT_SRC: &str = r#"theorem bridge_stepInst_cast_trunc (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false) :
    TrustIr.Sem.run
      (TrustIr.stepInst
        (TrustIr.Inst.Cast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
      { TrustIr.MachineState.empty with
          locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
          nextValueId := 1 } =
    Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
      { TrustIr.MachineState.empty with
          locals :=
            (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v)).set
              (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 8)),
          nextValueId := 2 }) :=
  by
    rw [stepinst_cast_trunc_chain v, bridge_cast_trunc v hbool]
"#;

const STEPINST_CAST_COMPOSED_NAME: &str = "bridge_stepInst_cast_agreement_all";
const STEPINST_CAST_COMPOSED_SRC: &str = r#"theorem bridge_stepInst_cast_agreement_all :
    ∀ (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false),
      TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.Cast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 8)),
            nextValueId := 2 }) :=
  bridge_stepInst_cast_trunc
"#;

/// stepInst-Cast forgery probes: mirrors [`CAST_FORGERY_PROBES`]' own
/// wrong-width precedent, lifted one layer to stepInst, plus a
/// dropped-truncation (identity) probe.  The first probe observes the exact
/// destination slot instead of comparing whole `MachineState`s: after the
/// fat-pointer memory model landed, asking defeq to disprove two otherwise
/// identical full states eagerly normalized the unrelated memory fields and
/// made this fail-closed control effectively nonterminating.  Its attempted
/// proof still has to forge the precise false equality `truncate 8 =
/// truncate 16`, so the semantic negative control is unchanged while the
/// kernel reaches the mismatch directly.
const STEPINST_CAST_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-destination-width (Trunc claimed to truncate to srcW=16 instead of dstW=8)",
        r#"theorem bridge_stepInst_cast_trunc_wrong_width (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false) :
    (match TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.Cast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8
            (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 } with
      | .ok p => Except.ok (p.2.locals.get (TrustIr.ValueId.mk 1))
      | .error e => Except.error e) =
    Except.ok (some (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 16))) :=
  Eq.trans
    (congrArg
      (fun p : Except TrustIr.SemError (TrustIr.InstrResult × TrustIr.MachineState) =>
        match p with
        | .ok p => Except.ok (p.2.locals.get (TrustIr.ValueId.mk 1))
        | .error e => Except.error e)
      (bridge_stepInst_cast_trunc v hbool))
    (congrArg
      (fun x : Int => Except.ok (some (TrustIr.Value.int 8 x)))
      (Eq.refl (TrustIr.truncateUnsigned v 8) :
        TrustIr.truncateUnsigned v 8 = TrustIr.truncateUnsigned v 16))
"#,
    ),
    (
        "dropped-truncation (Trunc's destination claimed to be the untouched operand v)",
        r#"theorem bridge_stepInst_cast_trunc_identity_wrong (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false) :
    (match TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.Cast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8
            (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 } with
      | .ok p => Except.ok (p.2.locals.get (TrustIr.ValueId.mk 1))
      | .error e => Except.error e) =
    Except.ok (some (TrustIr.Value.int 8 v)) :=
  Eq.trans
    (congrArg
      (fun p : Except TrustIr.SemError (TrustIr.InstrResult × TrustIr.MachineState) =>
        match p with
        | .ok p => Except.ok (p.2.locals.get (TrustIr.ValueId.mk 1))
        | .error e => Except.error e)
      (bridge_stepInst_cast_trunc v hbool))
    (congrArg
      (fun x : Int => Except.ok (some (TrustIr.Value.int 8 x)))
      (Eq.refl (TrustIr.truncateUnsigned v 8) : TrustIr.truncateUnsigned v 8 = v))
"#,
    ),
];

/// Un-bridged stepInst-Cast integer ops (value-bridged via [`CAST_ARMS`],
/// chain not yet executed): `(op, reason)`.
const STEPINST_CAST_UNBRIDGED: &[(&str, &str)] = &[(
    "ZExt/SExt",
    "both are already bridged at the VALUE level (CAST_ARMS); the stepInst chain+connect \
     technique demonstrated for Trunc generalizes directly (reuse bridge_cast_zext/ \
     bridge_cast_sext) but has not yet been executed for them",
)];

/// The OVERALL umbrella conjoining all 4 categories' primary connect
/// theorems (Neg ∧ unsigned-AddOverflow ∧ Ult ∧ Trunc) — the mission's
/// closing "one overall bridge_stepInst_categories_agreement_all" theorem.
const STEPINST_CATEGORIES_COMPOSED_NAME: &str = "bridge_stepInst_categories_agreement_all";
const STEPINST_CATEGORIES_COMPOSED_SRC: &str = r#"theorem bridge_stepInst_categories_agreement_all :
    (∀ (v : Int) (h0 : 0 ≤ Int.neg v) (h1 : Int.neg v < (2 : Int) ^ 8),
      TrustIr.Sem.run
        (TrustIr.stepInst (TrustIr.Inst.UnOp TrustIr.UnOp.Neg TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (Int.neg v)),
            nextValueId := 2 }))
  ∧ (∀ (v_l v_r : Int),
      TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.Overflow TrustIr.OverflowOp.AddOverflow TrustIr.Ty.U8
            (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
            nextValueId := 2 } =
      Except.ok (TrustIr.InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3],
        { TrustIr.MachineState.empty with
            locals :=
              (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                (TrustIr.ValueId.mk 2)
                (TrustIr.Value.int 8
                    ((((v_l + v_r) % ((2:Int)^8) + (2:Int)^8) % ((2:Int)^8))))).set
                (TrustIr.ValueId.mk 3)
                (TrustIr.Value.bool
                    (@Decidable.decide (((2:Int)^8 - 1) < (v_l + v_r))
                        (Int.decLt ((2:Int)^8 - 1) (v_l + v_r)) ||
                      @Decidable.decide (v_l + v_r < 0) (Int.decLt (v_l + v_r) 0))),
            nextValueId := 4 }))
  ∧ (∀ (v_l v_r : Int),
      TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8
            (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
            nextValueId := 2 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 2)),
        { TrustIr.MachineState.empty with
            locals :=
              ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.bool (Decidable.decide (Int.lt v_l v_r))),
            nextValueId := 3 }))
  ∧ (∀ (v : Int) (hbool : (TrustIr.Ty.I8 == TrustIr.Ty.Bool) = false),
      TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.Cast TrustIr.CastOp.Trunc TrustIr.Ty.I16 TrustIr.Ty.I8 (TrustIr.ValueId.mk 0)))
        { TrustIr.MachineState.empty with
            locals := TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v),
            nextValueId := 1 } =
      Except.ok (TrustIr.InstrResult.value (some (TrustIr.ValueId.mk 1)),
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 16 v)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 (TrustIr.truncateUnsigned v 8)),
            nextValueId := 2 })) :=
  And.intro bridge_stepInst_unop_neg
    (And.intro bridge_stepInst_overflow_add_unsigned
      (And.intro bridge_stepInst_icmp_ult bridge_stepInst_cast_trunc))
"#;

// ---------------------------------------------------------------------------
// stepN/stepBlock — the FIRST WHOLE-BLOCK (multi-instruction,
// terminator-inclusive) agreement, one layer above `stepInst`. `stepBlock`
// folds `stepInst` over a block's body then dispatches the terminator
// through `stepInst` too; `stepN` is the fuel-driven driver
// (`TrustIr/Semantics/Eval.lean`, the NEW module this increment vendors —
// [`BRIDGE_ROOT_MODULES`] extended to include `TrustIr.Semantics.Eval`,
// whose closure is `Step`'s closure plus `Eval` itself: 27 TrustIr modules,
// up from 26).
//
// SCOPE (the mission-minimum "smallest real whole-body"): a FIXED,
// single-block, single-instruction-body straight-line function: `_2 := _0 +
// _1; return _2`. Concretely: `cfg` is a constant total `BlockId -> Option
// BasicBlock` (there is exactly one block, so the CFG lookup ignores its
// argument — a real, total CFG, just a trivial one); the block's `params`
// bind two I8 operands directly into locals (`ValueId.mk 0`/`1`, mirroring
// the stepInst arms' own `state0` exactly); `body` is the single
// already-bridged `BinOp Add` instruction; `terminator` is `Return` of the
// BinOp's own fresh destination (`ValueId.mk 2`). `fuel = 1` is sufficient:
// `stepN`'s `.Ret` branch never recurses, so the `fuel` parameter's
// well-founded structure is never exercised beyond the base unfold.
//
// THE TECHNIQUE: two theorems, mirroring the stepInst-BinOp shape one layer
// up:
//   * `stepblock_add_return_outer_chain` — an UNCONDITIONAL `rfl`
//     "outer factoring": the WHOLE `stepN`/`stepBlock` computation
//     (`bindBlockParams` -> fold `stepInst` over the 1-instruction body ->
//     `stepInst` the `Return` terminator) equals `Sem.run (stepInst (.BinOp
//     Add I8 …)) state0` — the EXACT LHS `bridge_stepInst_binop_add` already
//     pins — bound (`Except.bind`) to an EXPLICIT continuation that looks up
//     the BinOp's fresh destination (`ValueId.mk 2`) in the resulting state
//     and wraps it as the `Return` terminator's value list (`semReturn`'s own
//     `mapM Sem.lookupValue`, specialized to this one destination). This is
//     `stepBlock`'s body-fold-then-terminator made an explicit bind, generic
//     in the intermediate `(InstrResult × MachineState)` pair so it composes
//     with ANY proof of the instruction-level step — not a coincidence of
//     this one arm.
//   * `bridge_stepblock_add_return` — the CONNECT theorem: composes the
//     outer factoring with the ALREADY-PROVEN `bridge_stepInst_binop_add`
//     (from the stepInst-BinOp extension above — REUSED as a black-box term
//     via `congrArg`/`Eq.trans`, NOT re-proven) to land on the exact value
//     `int_binop_expr`'s `Int.add` head denotes for the corresponding
//     straight-line Clean whole-body (`trustir_anchor.rs`'s
//     `IrBody::inlined_return_formula`: `_2 := _0 + _1; return _2` inlines to
//     `F::Add(Var 0, Var 1)`, grounding to `Int.add`). This is a GENUINE
//     three-layer tie: imported Lean `stepN`/`stepBlock` ≡ imported Lean
//     `stepInst` (via the outer-chain's own LHS-matching factoring) ≡
//     Clean's whole-body denotation — composed, not independently reproven.
//     A closing `rfl` evaluates the remaining `Except.bind` of the `.ok`
//     step result into the `Return` continuation: Clean's `rw`, like Lean's,
//     closes a goal only by REDUCIBLE `rfl`.
//
// Both theorems were checked against a REAL Lean 4.8.0 toolchain AND against
// clean's own elaborator (machine-imported vendored oleans) before being
// pinned here; both have `axiom_deps = ∅`.
//
// ANTI-FORGERY: (1) wrong final value — the block claimed to return
// `Int.sub v_l v_r` instead of `Int.add v_l v_r` (non-commutative, so a real
// distinct claim); (2) wrong operand threaded to the terminator — the block
// claimed to return the RAW `v_l` operand (`ValueId.mk 0`, untouched by the
// BinOp) instead of the BinOp's own fresh destination (`ValueId.mk 2`).
// Both confirmed kernel-REJECTED for symbolic `v_l`/`v_r` against a real
// Lean 4.8.0 toolchain AND clean's own elaborator before being pinned here.
//
// HONEST RESIDUE, stated precisely (never silently dropped): Sub/Mul-return
// blocks (value- and stepInst-level bridged; the identical technique
// generalizes but was not executed); multi-instruction bodies (>1
// instruction before the terminator — the SAME fold technique composes one
// more `Except.bind` per instruction, not executed); branching bodies
// (`CondBr`/`Switch`, multi-block CFGs — `stepN`'s `.Continue` recursive
// case, fuel > 1, entirely unbridged); loops (no agreement attempted for any
// CFG with a back-edge); `stepNWithContext`/`evalFunctionInContext` (the
// interprocedural evaluator added alongside `stepN` in `Eval.lean` — calls,
// indirect calls, invoke, SeqMap dispatch — untouched by this bridge).
// ---------------------------------------------------------------------------

/// The concrete block/cfg fixture for the `Add`-then-`Return` arm, loaded
/// ONCE before the per-arm theorems (which reference `evalBlockAddReturn` /
/// `evalCfgAddReturn` by name, exactly as `STEPINST_BINOP_ARMS`' connect
/// sources reference the already-loaded `bridge_add`/`bridge_sub`/
/// `bridge_mul`).
const STEPBLOCK_FIXTURES_SRC: &str = r#"def evalBlockAddReturn : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.I8), (TrustIr.ValueId.mk 1, TrustIr.Ty.I8)]
  , body := [TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
      (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)]
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 2]
  , terminatorResultDests := [] }
def evalCfgAddReturn : TrustIr.CFG := fun _ => some evalBlockAddReturn
"#;

/// One stepblock agreement arm: `(op, outer-chain theorem, src, connect
/// theorem, src)`. Currently just `Add` — the mission-minimum "smallest real
/// whole-body": ONE `BinOp` instruction in the block body, followed by
/// `Return` of its result.
struct StepBlockArmSpec {
    op: &'static str,
    outer_chain_theorem: &'static str,
    outer_chain_src: &'static str,
    connect_theorem: &'static str,
    connect_src: &'static str,
}

const STEPBLOCK_ARMS: &[StepBlockArmSpec] = &[StepBlockArmSpec {
    op: "Add",
    outer_chain_theorem: "stepblock_add_return_outer_chain",
    outer_chain_src: r#"theorem stepblock_add_return_outer_chain (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 1 evalCfgAddReturn (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 v_l, TrustIr.Value.int 8 v_r])
      TrustIr.MachineState.empty
    =
    (TrustIr.Sem.run
        (TrustIr.stepInst
          (TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
            (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)))
        { TrustIr.MachineState.empty with
            locals :=
              (TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r),
            nextValueId := 2 }).bind
      (fun (p : TrustIr.InstrResult × TrustIr.MachineState) =>
        match p.2.locals.get (TrustIr.ValueId.mk 2) with
        | some v => Except.ok ([v], p.2)
        | none => Except.error (TrustIr.SemError.typeError "undefined SSA value")) := rfl
"#,
    connect_theorem: "bridge_stepblock_add_return",
    connect_src: r#"theorem bridge_stepblock_add_return (v_l v_r : Int)
    (h0 : 0 ≤ Int.add v_l v_r) (h1 : Int.add v_l v_r < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepN 1 evalCfgAddReturn (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 v_l, TrustIr.Value.int 8 v_r])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 (Int.add v_l v_r)],
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.add v_l v_r)),
          nextValueId := 3 }) :=
  by
    rw [stepblock_add_return_outer_chain v_l v_r, bridge_stepInst_binop_add v_l v_r h0 h1]
    rfl
"#,
}];

/// The COMPOSED stepblock agreement theorem. With only one arm proven, this
/// restates it as a closed universal (the singleton "conjunction") — the
/// same shape the multi-arm composed theorems take, degenerate at n=1.
const STEPBLOCK_COMPOSED_NAME: &str = "bridge_stepblock_agreement_all";
const STEPBLOCK_COMPOSED_SRC: &str = r#"theorem bridge_stepblock_agreement_all :
    ∀ (v_l v_r : Int) (h0 : 0 ≤ Int.add v_l v_r) (h1 : Int.add v_l v_r < (2 : Int) ^ 8),
      TrustIr.Sem.run
        (TrustIr.stepN 1 evalCfgAddReturn (TrustIr.BlockId.mk 0)
          [TrustIr.Value.int 8 v_l, TrustIr.Value.int 8 v_r])
        TrustIr.MachineState.empty
      =
      Except.ok ([TrustIr.Value.int 8 (Int.add v_l v_r)],
        { TrustIr.MachineState.empty with
            locals :=
              ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.add v_l v_r)),
            nextValueId := 3 }) :=
  fun v_l v_r h0 h1 => bridge_stepblock_add_return v_l v_r h0 h1
"#;

/// stepblock forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run. Index 0 (used alone in Spot mode): the wrong
/// FINAL VALUE. Index 1 (Full mode only): the wrong OPERAND threaded to the
/// terminator.
const STEPBLOCK_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "wrong-final-value (block claimed to return Int.sub instead of Int.add)",
        r#"theorem bridge_stepblock_add_return_WRONG_VALUE (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 1 evalCfgAddReturn (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 v_l, TrustIr.Value.int 8 v_r])
      TrustIr.MachineState.empty
    =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Add 8 v_l v_r with
      | .ok _ =>
        Except.ok ([TrustIr.Value.int 8 (Int.sub v_l v_r)],
          { TrustIr.MachineState.empty with
              locals :=
                ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.sub v_l v_r)),
              nextValueId := 3 })
      | .error e => Except.error e) := rfl
"#,
    ),
    (
        "wrong-operand-threaded-to-terminator (returns raw v_l / ValueId.mk 0, not the BinOp's ValueId.mk 2)",
        r#"theorem bridge_stepblock_add_return_WRONG_OPERAND (v_l v_r : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 1 evalCfgAddReturn (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 v_l, TrustIr.Value.int 8 v_r])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 v_l],
      { TrustIr.MachineState.empty with
          locals :=
            ((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 v_l)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 v_r)).set
              (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 (Int.add v_l v_r)),
          nextValueId := 3 }) := rfl
"#,
    ),
];

/// Un-bridged stepblock residue, reported honestly (never faked): `(shape,
/// reason)`.
const STEPBLOCK_UNBRIDGED: &[(&str, &str)] = &[
    (
        "Sub/Mul-return blocks",
        "value- and stepInst-level bridged (bridge_stepInst_binop_sub/mul already prove the \
         instruction-level step); the identical outer-chain+connect technique demonstrated \
         here for Add generalizes directly but was not executed for them",
    ),
    (
        "multi-instruction bodies (>1 instruction before the terminator)",
        "the fold-over-body technique (bindBlockParams -> stepInst per body inst -> terminator) \
         is demonstrated for a body of length 1; a length-2+ body composes the SAME \
         outer-factoring one more time (an additional Except.bind through a second stepInst) \
         but was not executed",
    ),
    (
        "branching bodies (CondBr/Switch, multi-block CFGs, stepN's .Continue recursion)",
        "this increment's cfg is a single constant block exercising only stepN's fuel=1 base \
         case (.Ret branch); the .Continue recursive case (a real multi-block CFG, fuel > 1) is \
         entirely unbridged",
    ),
    (
        "loops (evalCfg / loop convergence)",
        "no agreement attempted for any cfg with a back-edge; loop termination/convergence is \
         outside this bridge's scope entirely",
    ),
    (
        "stepNWithContext / evalFunctionInContext (interprocedural evaluation)",
        "the contextual (Call/CallIndirect/Invoke/SeqMap-dispatching) evaluator added alongside \
         stepN in Eval.lean is untouched by this bridge; only the historical fail-closed-on-calls \
         stepN is bridged",
    ),
];

// ---------------------------------------------------------------------------
// stepN .CondBr / .Continue — the FIRST BRANCHING whole-body agreement.
// Every prior stepN extension (stepblock, above) exercised only the fuel=1
// `.Ret` BASE case; this exercises the `.Continue` RECURSIVE case (fuel ≥
// 2) via a real 2-target `CondBr`. See the module-level "EXTENSION 7" doc
// comment above for the full technique / residue breakdown.
// ---------------------------------------------------------------------------

/// The concrete 3-block branching CFG fixture: `if _0 { return _1 } else {
/// return _2 }`. Loaded ONCE before the per-path (true/false) theorems,
/// exactly as [`STEPBLOCK_FIXTURES_SRC`] loads its single-block fixture.
/// Also carries the two `Bool.rec` iota-reduction helper lemmas both paths'
/// connect theorems cite (the SAME `Bool.rec (fun _ => Int) else then cond`
/// shape `clean_ground.rs`'s `ground_int` `F::Ite` arm emits).
const STEPBRANCH_FIXTURES_SRC: &str = r#"def branchBlockGuard : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.Bool), (TrustIr.ValueId.mk 1, TrustIr.Ty.I8),
      (TrustIr.ValueId.mk 2, TrustIr.Ty.I8)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.CondBr (TrustIr.ValueId.mk 0)
      (TrustIr.BlockId.mk 1) [TrustIr.ValueId.mk 1]
      (TrustIr.BlockId.mk 2) [TrustIr.ValueId.mk 2]
  , terminatorResultDests := [] }
def branchBlockThen : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 3, TrustIr.Ty.I8)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 3]
  , terminatorResultDests := [] }
def branchBlockElse : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 4, TrustIr.Ty.I8)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 4]
  , terminatorResultDests := [] }
def branchCfg : TrustIr.CFG := fun bb =>
  match bb.index with
  | 0 => some branchBlockGuard
  | 1 => some branchBlockThen
  | 2 => some branchBlockElse
  | _ => none
theorem bool_rec_true (e t : Int) : (@Bool.rec (fun _ => Int) e t true : Int) = t := rfl
theorem bool_rec_false (e t : Int) : (@Bool.rec (fun _ => Int) e t false : Int) = e := rfl
"#;

/// One stepN-branch agreement arm: `(guard label, chain theorem, chain src,
/// connect theorem, connect src)`. Two arms — `true` (the THEN path) and
/// `false` (the ELSE path).
struct StepBranchArmSpec {
    guard: &'static str,
    chain_theorem: &'static str,
    chain_src: &'static str,
    connect_theorem: &'static str,
    connect_src: &'static str,
}

const STEPBRANCH_ARMS: &[StepBranchArmSpec] = &[
    StepBranchArmSpec {
        guard: "true",
        chain_theorem: "stepN_branch_true_chain",
        chain_src: r#"theorem stepN_branch_true_chain (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 (@Bool.rec (fun _ => Int) b a true)],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a),
          nextValueId := 4 }) := rfl
"#,
        connect_theorem: "bridge_stepN_branch_true",
        connect_src: r#"theorem bridge_stepN_branch_true (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 a],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a),
          nextValueId := 4 }) :=
  by
    rw [stepN_branch_true_chain a b, bool_rec_true b a]
"#,
    },
    StepBranchArmSpec {
        guard: "false",
        chain_theorem: "stepN_branch_false_chain",
        chain_src: r#"theorem stepN_branch_false_chain (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 (@Bool.rec (fun _ => Int) b a false)],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b),
          nextValueId := 5 }) := rfl
"#,
        connect_theorem: "bridge_stepN_branch_false",
        connect_src: r#"theorem bridge_stepN_branch_false (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 b],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b),
          nextValueId := 5 }) :=
  by
    rw [stepN_branch_false_chain a b, bool_rec_false b a]
"#,
    },
];

/// The COMPOSED stepN-branch agreement theorem: the conjunction of BOTH
/// paths (true ∧ false) — the first branching whole-body agreement to cover
/// every path through a real CFG.
const STEPBRANCH_COMPOSED_NAME: &str = "bridge_stepN_branch_agreement_all";
const STEPBRANCH_COMPOSED_SRC: &str = r#"theorem bridge_stepN_branch_agreement_all :
    (∀ (a b : Int),
      TrustIr.Sem.run
        (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
          [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
        TrustIr.MachineState.empty
      =
      Except.ok ([TrustIr.Value.int 8 a],
        { TrustIr.MachineState.empty with
            locals :=
              (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a),
            nextValueId := 4 }))
  ∧ (∀ (a b : Int),
      TrustIr.Sem.run
        (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
          [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
        TrustIr.MachineState.empty
      =
      Except.ok ([TrustIr.Value.int 8 b],
        { TrustIr.MachineState.empty with
            locals :=
              (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b),
            nextValueId := 5 })) :=
  And.intro bridge_stepN_branch_true bridge_stepN_branch_false
"#;

/// stepN-branch forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run. Index 0 (used alone in Spot mode): the
/// true-guard claimed to yield the ELSE value. Index 1 (Full mode only):
/// the false-guard claimed to yield the THEN value.
const STEPBRANCH_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "true-guard-yields-else-value (CondBr true claimed to return b, not a)",
        r#"theorem bridge_stepN_branch_true_WRONG_VALUE (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 b],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a),
          nextValueId := 4 }) := rfl
"#,
    ),
    (
        "false-guard-yields-then-value (CondBr false claimed to return a, not b)",
        r#"theorem bridge_stepN_branch_false_WRONG_VALUE (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 a],
      { TrustIr.MachineState.empty with
          locals :=
            (((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b),
          nextValueId := 5 }) := rfl
"#,
    ),
];

/// Un-bridged stepN-branch residue, reported honestly (never faked):
/// `(shape, reason)`.
const STEPBRANCH_UNBRIDGED: &[(&str, &str)] = &[
    (
        "Switch (N-way multi-target branch)",
        "only the 2-way CondBr is bridged; Switch's N-way dispatch and its \
         exhaustive_enum_unreachable flag are untouched",
    ),
    (
        "nested / chained CondBrs (>1 guard, the if/else-if/else shape)",
        "clean_ground's nested_guarded_return_formula recognizes a SwitchInt tree as a \
         nested Formula::Ite; the single-CondBr technique here generalizes (one more \
         Bool.rec layer per nesting level) but was not executed",
    ),
    (
        "loops (any CFG with a back-edge)",
        "this increment's cfg is a DAG (bb0 -> bb1 | bb2, no cycle); no agreement attempted \
         for a cfg where stepN's .Continue case revisits an already-executed block",
    ),
    (
        "non-empty bodies on either branch arm",
        "this cfg's bb1/bb2 have empty bodies (bindBlockParams -> Return directly); \
         composing this technique with EXTENSION 6's fold-over-body technique (a body \
         before the arm's Return) was not executed",
    ),
    (
        "semCondBr's `.int _ v` nonzero-as-true guard arm",
        "only the `.bool true`/`.bool false` guard arms are bridged; semCondBr's own \
         integer-condition arm (nonzero = true) is untouched",
    ),
    (
        "stepNWithContext / evalFunctionInContext (interprocedural evaluation)",
        "the contextual (Call/CallIndirect/Invoke/SeqMap-dispatching) evaluator is \
         untouched by this bridge; only the historical fail-closed-on-calls stepN is \
         bridged",
    ),
];

// ---------------------------------------------------------------------------
// stepN branch-WITH-BODY — closing EXTENSION 7's own named residue
// ("non-empty bodies on either arm") by composing EXTENSION 7's control-flow
// technique (CondBr dispatch + `.Continue` recursion) with EXTENSION 6's
// body-fold technique (fold `stepInst` over a block's body before its
// terminator). See the module-level "EXTENSION 8" doc comment above for the
// full technique / residue breakdown.
// ---------------------------------------------------------------------------

/// The concrete 3-block branching-WITH-COMPUTATION CFG fixture: `if _0 {
/// return _1 + _2 } else { return _1 - _2 }`. Distinct `def` names from
/// [`STEPBRANCH_FIXTURES_SRC`] (`branchBodyBlock*`/`branchBodyCfg`, not
/// `branchBlock*`/`branchCfg`) so both extensions' fixtures coexist in the
/// SAME environment without name clashes (both are loaded, in order, by the
/// same gate run). `bb1`'s params are `ValueId.mk 3/4` and `bb2`'s are
/// `mk 5/6` — `bindBlockParams`'s `nextValueId` counter is threaded across
/// the WHOLE cfg (not reset per block: `Eval.lean`'s `bindBlockParams`
/// folds `max next (param.index + 1)` starting from the INCOMING state's
/// own `nextValueId`), so these are the ids a real fresh-id assignment
/// would produce after `bb0`'s own 3 params (`mk 0/1/2`) — NOT `mk 0/1`,
/// the ids [`STEPINST_BINOP_ARMS`]' `bridge_stepInst_binop_add`/`_sub` are
/// pinned to at a pristine 2-entry state (see the EXTENSION 8 doc comment
/// for why that precludes literal term-level reuse of those theorems here).
const STEPBRANCH_BODY_FIXTURES_SRC: &str = r#"def branchBodyBlockGuard : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.Bool), (TrustIr.ValueId.mk 1, TrustIr.Ty.I8),
      (TrustIr.ValueId.mk 2, TrustIr.Ty.I8)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.CondBr (TrustIr.ValueId.mk 0)
      (TrustIr.BlockId.mk 1) [TrustIr.ValueId.mk 1, TrustIr.ValueId.mk 2]
      (TrustIr.BlockId.mk 2) [TrustIr.ValueId.mk 1, TrustIr.ValueId.mk 2]
  , terminatorResultDests := [] }
def branchBodyBlockThen : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 3, TrustIr.Ty.I8), (TrustIr.ValueId.mk 4, TrustIr.Ty.I8)]
  , body := [TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8
      (TrustIr.ValueId.mk 3) (TrustIr.ValueId.mk 4)]
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 5]
  , terminatorResultDests := [] }
def branchBodyBlockElse : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 5, TrustIr.Ty.I8), (TrustIr.ValueId.mk 6, TrustIr.Ty.I8)]
  , body := [TrustIr.Inst.BinOp TrustIr.BinOp.Sub TrustIr.Ty.I8
      (TrustIr.ValueId.mk 5) (TrustIr.ValueId.mk 6)]
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 7]
  , terminatorResultDests := [] }
def branchBodyCfg : TrustIr.CFG := fun bb =>
  match bb.index with
  | 0 => some branchBodyBlockGuard
  | 1 => some branchBodyBlockThen
  | 2 => some branchBodyBlockElse
  | _ => none
"#;

/// One stepN branch-WITH-BODY agreement arm: `(guard, op reused, chain
/// theorem, chain src, connect theorem, connect src)`. Two arms — `true`
/// (the THEN path, reusing `bridge_add`) and `false` (the ELSE path,
/// reusing `bridge_sub`).
struct StepBranchBodyArmSpec {
    guard: &'static str,
    chain_theorem: &'static str,
    chain_src: &'static str,
    connect_theorem: &'static str,
    connect_src: &'static str,
}

const STEPBRANCH_BODY_ARMS: &[StepBranchBodyArmSpec] = &[
    StepBranchBodyArmSpec {
        guard: "true",
        chain_theorem: "stepN_branch_body_true_chain",
        chain_src: r#"theorem stepN_branch_body_true_chain (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Add 8 a b with
      | .ok result =>
        Except.ok ([TrustIr.Value.int 8 result],
          { TrustIr.MachineState.empty with
              locals :=
                (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                    (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b)).set
                  (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 result),
              nextValueId := 6 })
      | .error e => Except.error e) := rfl
"#,
        connect_theorem: "bridge_stepN_branch_body_true",
        connect_src: r#"theorem bridge_stepN_branch_body_true (a b : Int)
    (h0 : 0 ≤ Int.add a b) (h1 : Int.add a b < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 (Int.add a b)],
      { TrustIr.MachineState.empty with
          locals :=
            (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 (Int.add a b)),
          nextValueId := 6 }) :=
  by
    rw [stepN_branch_body_true_chain a b, bridge_add 8 a b h0 h1]
"#,
    },
    StepBranchBodyArmSpec {
        guard: "false",
        chain_theorem: "stepN_branch_body_false_chain",
        chain_src: r#"theorem stepN_branch_body_false_chain (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Sub 8 a b with
      | .ok result =>
        Except.ok ([TrustIr.Value.int 8 result],
          { TrustIr.MachineState.empty with
              locals :=
                (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                    (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 6) (TrustIr.Value.int 8 b)).set
                  (TrustIr.ValueId.mk 7) (TrustIr.Value.int 8 result),
              nextValueId := 8 })
      | .error e => Except.error e) := rfl
"#,
        connect_theorem: "bridge_stepN_branch_body_false",
        connect_src: r#"theorem bridge_stepN_branch_body_false (a b : Int)
    (h0 : 0 ≤ Int.sub a b) (h1 : Int.sub a b < (2 : Int) ^ 8) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    Except.ok ([TrustIr.Value.int 8 (Int.sub a b)],
      { TrustIr.MachineState.empty with
          locals :=
            (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 a)).set
                (TrustIr.ValueId.mk 6) (TrustIr.Value.int 8 b)).set
              (TrustIr.ValueId.mk 7) (TrustIr.Value.int 8 (Int.sub a b)),
          nextValueId := 8 }) :=
  by
    rw [stepN_branch_body_false_chain a b, bridge_sub 8 a b h0 h1]
"#,
    },
];

/// The COMPOSED stepN branch-WITH-BODY agreement theorem: the conjunction of
/// BOTH paths (true ∧ false, each generic over the taken arm's own
/// no-overflow/in-range side condition). Full mode only (needs both arms;
/// Spot mode never loads `bridge_sub`, so the false arm is never attempted —
/// see the module-level "EXTENSION 8" doc comment).
const STEPBRANCH_BODY_COMPOSED_NAME: &str = "bridge_stepN_branch_body_agreement_all";
const STEPBRANCH_BODY_COMPOSED_SRC: &str = r#"theorem bridge_stepN_branch_body_agreement_all :
    (∀ (a b : Int) (h0 : 0 ≤ Int.add a b) (h1 : Int.add a b < (2 : Int) ^ 8),
      TrustIr.Sem.run
        (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
          [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
        TrustIr.MachineState.empty
      =
      Except.ok ([TrustIr.Value.int 8 (Int.add a b)],
        { TrustIr.MachineState.empty with
            locals :=
              (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                  (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a)).set
                  (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b)).set
                (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 (Int.add a b)),
            nextValueId := 6 }))
  ∧ (∀ (c d : Int) (h2 : 0 ≤ Int.sub c d) (h3 : Int.sub c d < (2 : Int) ^ 8),
      TrustIr.Sem.run
        (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
          [TrustIr.Value.bool false, TrustIr.Value.int 8 c, TrustIr.Value.int 8 d])
        TrustIr.MachineState.empty
      =
      Except.ok ([TrustIr.Value.int 8 (Int.sub c d)],
        { TrustIr.MachineState.empty with
            locals :=
              (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                  (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 c)).set
                  (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 d)).set
                  (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 c)).set
                  (TrustIr.ValueId.mk 6) (TrustIr.Value.int 8 d)).set
                (TrustIr.ValueId.mk 7) (TrustIr.Value.int 8 (Int.sub c d)),
            nextValueId := 8 })) :=
  And.intro bridge_stepN_branch_body_true bridge_stepN_branch_body_false
"#;

/// stepN branch-WITH-BODY forgery probes: deliberately-WRONG claims that
/// must be kernel-REJECTED every run. Index 0 (used alone in Spot mode,
/// since it depends only on `bridge_add`): the TRUE arm claimed to compute
/// the ELSE arm's `Int.sub a b`. Index 1 (Full mode only, needs
/// `bridge_sub`): the FALSE arm claimed to compute the THEN arm's
/// `Int.add a b`.
const STEPBRANCH_BODY_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "true-arm-computes-else-arithmetic (CondBr true claimed to compute Int.sub a b, not Int.add a b)",
        r#"theorem bridge_stepN_branch_body_true_WRONG_VALUE (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool true, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Add 8 a b with
      | .ok _ =>
        Except.ok ([TrustIr.Value.int 8 (Int.sub a b)],
          { TrustIr.MachineState.empty with
              locals :=
                (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool true)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                    (TrustIr.ValueId.mk 3) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 b)).set
                  (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 (Int.sub a b)),
              nextValueId := 6 })
      | .error e => Except.error e) := rfl
"#,
    ),
    (
        "false-arm-computes-then-arithmetic (CondBr false claimed to compute Int.add a b, not Int.sub a b)",
        r#"theorem bridge_stepN_branch_body_false_WRONG_VALUE (a b : Int) :
    TrustIr.Sem.run
      (TrustIr.stepN 2 branchBodyCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.bool false, TrustIr.Value.int 8 a, TrustIr.Value.int 8 b])
      TrustIr.MachineState.empty
    =
    (match TrustIr.semIntBinOp TrustIr.BinOp.Sub 8 a b with
      | .ok _ =>
        Except.ok ([TrustIr.Value.int 8 (Int.add a b)],
          { TrustIr.MachineState.empty with
              locals :=
                (((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.bool false)).set
                    (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 b)).set
                    (TrustIr.ValueId.mk 5) (TrustIr.Value.int 8 a)).set
                    (TrustIr.ValueId.mk 6) (TrustIr.Value.int 8 b)).set
                  (TrustIr.ValueId.mk 7) (TrustIr.Value.int 8 (Int.add a b)),
              nextValueId := 8 })
      | .error e => Except.error e) := rfl
"#,
    ),
];

/// Un-bridged stepN branch-WITH-BODY residue, reported honestly (never
/// faked): `(shape, reason)`.
const STEPBRANCH_BODY_UNBRIDGED: &[(&str, &str)] = &[
    (
        "Switch (N-way multi-target branch)",
        "unchanged from the stepN-branch extension; only the 2-way CondBr is bridged",
    ),
    (
        "nested / chained CondBrs (>1 guard, the if/else-if/else shape)",
        "unchanged from the stepN-branch extension; the single-CondBr technique generalizes \
         (one more Bool.rec layer per nesting level) but was not executed",
    ),
    (
        "loops (any CFG with a back-edge)",
        "unchanged from the stepN-branch extension; this increment's cfg is still a DAG",
    ),
    (
        "semCondBr's `.int _ v` nonzero-as-true guard arm",
        "unchanged from the stepN-branch extension; only the `.bool true`/`.bool false` guard \
         arms are bridged",
    ),
    (
        "stepNWithContext / evalFunctionInContext (interprocedural evaluation)",
        "unchanged from the stepN-branch extension; the contextual evaluator is untouched",
    ),
    (
        "multi-instruction arm bodies (>1 instruction before an arm's Return)",
        "each arm here has EXACTLY one BinOp before its Return; the SAME fold technique \
         composes one more Except.bind per additional instruction (as EXTENSION 6 itself \
         notes for its own single-instruction body) but was not executed",
    ),
    (
        "asymmetric arm shapes (one arm computing, the other a bare Return of a parameter; \
         or arms with a differing instruction count)",
        "only the SYMMETRIC both-arms-compute-one-BinOp shape (this increment) and the \
         SYMMETRIC both-arms-bare-Return shape (the stepN-branch extension) were executed; \
         a mixed CFG (one empty arm, one computing arm) was not attempted",
    ),
    (
        "arm bodies built from a non-BinOp instruction (UnOp/ICmp/Cast/Overflow before an \
         arm's Return)",
        "only BinOp (Add/Sub) arm bodies were composed here; the identical fold technique \
         generalizes to any already-bridged stepInst category (UnOp/ICmp/Cast/Overflow all \
         have a proven stepInst-level or value-level bridge to reuse) but was not executed",
    ),
];

// ---------------------------------------------------------------------------
// STEPLOOP EXTENSION — the FIRST agreement over a GENUINE back-edge CFG
// (`stepN`'s `.Continue` re-entering a block it has already visited), proven
// by NAT INDUCTION on the fuel with a per-step lemma, NOT by rfl-unrolling a
// deep recursion (the loop-bridge-faithfulness-audit's own named cliff risk,
// reports/loop-bridge-faithfulness-audit-2026-07-06.md §4). Every prior
// extension's honest-residue table says, verbatim, "loops (any CFG with a
// back-edge): no agreement attempted" — this is the first crossing.
//
// THE FIXTURE (`loopCfg`): a 2-block CFG with a REAL cycle — `bb0` has ONE
// `Bool` param and an EMPTY body; its terminator `CondBr` branches back to
// `BlockId.mk 0` itself (the guard true arm, passing the SAME param through
// unchanged) or to `bb1` (the guard false arm, the exit, `Return []`). This
// is a genuine back-edge: `cfg (BlockId.mk 0) pc-loops-to-cfg (BlockId.mk 0)`
// — the FIRST CFG in this bridge whose block graph has a cycle at all.
//
// ARM 1 (`steploop_true_diverges`) — THE PER-STEP LEMMA + INDUCTION, exactly
// the mission's shape: `∀ (n : Nat) (st : MachineState), Sem.run (stepN n
// loopCfg (BlockId.mk 0) [Value.bool true]) st = Except.error outOfFuel`.
// Proven by `induction n generalizing st`: the base case (`n = 0`) is
// `stepN 0 = throw outOfFuel`, an unconditional `rfl`; the step case
// (`n = k+1`) is `exact ih _` — a SINGLE unfold of `stepN`'s own
// `.Continue`-recursion (cheap: `bb0`'s empty body + a literal-key
// get-after-set on `ValueId.mk 0`, both `rfl`-transparent) lands EXACTLY on
// `stepN k loopCfg (BlockId.mk 0) [Value.bool true] st'` for the machine
// state `st'` bindBlockParams produces — the elaborator's own defeq check
// unifies `st'` against `ih`'s expected argument, so the IH is applied AT THE
// STEPPED STATE, the hallmark of a genuine induction (never `Eq.refl` on a
// large unrolled term; the per-step unfold is O(1), independent of `n`).
// This is the per-step lemma the mission asks for: ONE block-step of
// `stepN`'s `.Continue` dispatch, for a SYMBOLIC state, composed by
// induction to cover ARBITRARY fuel.
//
// ARM 2 (`steploop_false_exits`) — the base/exit case: `∀ st, ∃ st', Sem.run
// (stepN 2 loopCfg (BlockId.mk 0) [Value.bool false]) st = Except.ok
// ([], st')` — an unconditional `rfl` (existentially quantifying the final
// state, since `bindBlockParams` DOES thread/modify the incoming `st` even
// though no instruction runs — the state is NOT literally preserved, only
// the RETURN VALUE is pinned).
//
// THE GET-SET TECHNIQUE (used throughout): `ValueMap.set`/`.get` resolve
// `==` via the GENERIC `instBEqOfDecidableEq` (`a == b := decide (a = b)`,
// Lean 4 core, confirmed present in this vendored closure). For a LITERAL
// key (e.g. `ValueId.mk 0`) this is `rfl`-transparent (iota reduces through
// `Nat.decEq`'s zero/zero case directly). For a SYMBOLIC key it is NOT
// (`Nat.decEq` is stuck on a free variable) — the reusable fix, confirmed
// against this closure, is `decide_eq_true (rfl : id = id) : (id == id) =
// true`, then `congrArg (fun b => if b then … else …) that_proof` — citing
// the GENERIC `decide_eq_true` fact (proven once, for ANY `Decidable p`),
// never re-deriving Nat/ValueId (in)equality from scratch. This unlocks
// symbolic-state reasoning generally, but is NOT enough on its own to bridge
// a DATA-COMPUTING loop — see the staleness witness below.
//
// THE STALENESS WITNESS (`countup_naive_never_terminates`) — a NEW, HONEST,
// NEGATIVE finding this increment surfaces (beyond the audit's own fuel-
// mapping gap): `stepN`/`stepBlock` (`TrustIr/Semantics/Eval.lean`, the
// "historical", context-free evaluator — NOT `stepNWithContext`, which
// honors `bodyResultDests` and is out of scope per every prior residue
// table) assigns EVERY value-producing instruction's destination via
// `Sem.bindFresh`/`MachineState.bindValue`: `ValueId.mk s.nextValueId`,
// where `nextValueId` MONOTONICALLY GROWS (never resets) across the WHOLE
// run. For a STRAIGHT-LINE or DAG cfg (every prior arm), this is harmless —
// each block is visited at most once, so the destination a body instruction
// gets is fully deterministic and can be hardcoded in the CFG's own
// terminator. For a BACK-EDGE cfg whose revisited block computes a value
// referenced by ITS OWN terminator (e.g. `i := i + 1; if i < bound …`, the
// textbook `count_up`), the destination differs EVERY visit (visit 1's
// `BinOp` lands at `ValueId.mk 3`, visit 2's at `ValueId.mk 5`, …) while the
// CFG's terminator is a FIXED Lean term that can only hardcode ONE literal —
// so from the SECOND visit onward it reads a STALE binding from an earlier
// visit instead of the freshly-computed one. `countUpCfg` below is exactly
// this "naive count_up" attempt (header: `_3 := _0 + _2; _4 := _3 < _1;
// CondBr _4 …`, terminator hardcoded for visit 1's ids 3/4); the kernel-
// checked theorem proves it runs `stepN 8 …` and produces `outOfFuel` — NOT
// the intended "count to 3 then return 3" — because the stale guard (`_4`,
// frozen at visit 1's `true`) never flips false, so it loops forever instead
// of exiting after 3 iterations. This is a REAL, previously-undocumented
// structural fact about the CURRENT vendored `stepN`/`Sem.bindFresh`
// discipline, not a proof-engineering inconvenience: NO fixed-size CFG
// (independent of the iteration count) can encode a genuine data-computing
// `while` loop through this specific evaluator, because the only VALUE
// changes achievable WITHOUT an instruction (and hence without the
// staleness hazard) are FIXED-PERIOD PERMUTATIONS of the incoming params
// (swap positions across the back-edge) — which cannot encode a SYMBOLIC
// iteration count either (the CFG's param arity is fixed, independent of
// `n`). `stepNWithContext`'s `bodyResultDests` (explicit, compiler-assigned
// STATIC destinations, stable across revisits) is the evaluator that WOULD
// avoid this — but it is the interprocedural evaluator, out of scope here
// exactly as it has been for every prior extension.
//
// TIE TO CLEAN'S SIDE: `Trust.MirSem.step_cfg`/`exec_cfg`/`execCfgUnrollLaw`
// (§6U, `mirsem.rs`) already use the CORRECT block-fuel discipline for this
// correspondence (one unit per block visit, matching `stepN` exactly) and
// its own doc says it "SUBSUMES the structured loop refinement" — it remains
// the right target for a FUTURE full loop bridge, but (a) it has no
// `Trust.TrustIr.*` mirror and (b) connecting it to `stepN` needs the
// SSA↔slot (`Env : Nat → Int` ↔ `MachineState.locals : ValueId → Option
// Value`) projection the audit named as the first missing lemma — NOT
// executed here; this increment closes the "0% of any back-edge attempted"
// gap with a genuine per-step+induction result and documents PRECISELY where
// the data-computing case is blocked, rather than faking the full bridge.
// ---------------------------------------------------------------------------

/// The back-edge loop CFG fixture: `bb0` (one `Bool` param, empty body,
/// `CondBr` to itself or to the exit); `bb1` (the exit, `Return []`).
const STEPLOOP_FIXTURES_SRC: &str = r#"def loopSelfBlock : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.Bool)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.CondBr (TrustIr.ValueId.mk 0)
      (TrustIr.BlockId.mk 0) [TrustIr.ValueId.mk 0]
      (TrustIr.BlockId.mk 1) []
  , terminatorResultDests := [] }
def loopExitBlock : TrustIr.BasicBlock :=
  { params := []
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return []
  , terminatorResultDests := [] }
def loopCfg : TrustIr.CFG := fun bb =>
  match bb.index with
  | 0 => some loopSelfBlock
  | 1 => some loopExitBlock
  | _ => none
"#;

/// ARM 1 — the per-step lemma + fuel induction: the guard-always-true path
/// NEVER terminates, for ANY fuel, from ANY starting state.
const STEPLOOP_TRUE_THEOREM: &str = "steploop_true_diverges";
const STEPLOOP_TRUE_SRC: &str = r#"theorem steploop_true_diverges (n : Nat) (st : TrustIr.MachineState) :
    TrustIr.Sem.run (TrustIr.stepN n loopCfg (TrustIr.BlockId.mk 0) [TrustIr.Value.bool true]) st
    = Except.error TrustIr.SemError.outOfFuel := by
  induction n generalizing st with
  | zero => rfl
  | succ k ih => exact ih _
"#;

/// ARM 2 — the exit case: the guard-always-false path exits within fuel 2,
/// from ANY starting state (existential over the resulting machine state,
/// since `bindBlockParams` still threads/modifies it even with an empty
/// body — only the RETURN VALUE is pinned).
const STEPLOOP_FALSE_THEOREM: &str = "steploop_false_exits";
const STEPLOOP_FALSE_SRC: &str = r#"theorem steploop_false_exits (st : TrustIr.MachineState) :
    ∃ st', TrustIr.Sem.run (TrustIr.stepN 2 loopCfg (TrustIr.BlockId.mk 0) [TrustIr.Value.bool false]) st
    = Except.ok ([], st') := ⟨_, rfl⟩
"#;

/// The COMPOSED steploop agreement theorem: the conjunction of both arms.
const STEPLOOP_COMPOSED_NAME: &str = "bridge_stepN_loop_agreement_all";
const STEPLOOP_COMPOSED_SRC: &str = r#"theorem bridge_stepN_loop_agreement_all :
    (∀ (n : Nat) (st : TrustIr.MachineState),
      TrustIr.Sem.run (TrustIr.stepN n loopCfg (TrustIr.BlockId.mk 0) [TrustIr.Value.bool true]) st
      = Except.error TrustIr.SemError.outOfFuel)
  ∧ (∀ (st : TrustIr.MachineState),
      ∃ st', TrustIr.Sem.run (TrustIr.stepN 2 loopCfg (TrustIr.BlockId.mk 0) [TrustIr.Value.bool false]) st
      = Except.ok ([], st')) :=
  And.intro steploop_true_diverges steploop_false_exits
"#;

/// steploop forgery probes: deliberately-WRONG claims that must be
/// kernel-REJECTED every run. Index 0 (used alone in Spot mode): claims the
/// always-true guard TERMINATES within fixed fuel (it never does — an
/// `Except.ok` vs `Except.error` head mismatch, confirmed kernel-rejected
/// with a "rigid head/arity mismatch" error). Index 1 (Full mode only):
/// claims the always-false guard exits with INSUFFICIENT fuel (1, not 2).
const STEPLOOP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "true-guard-claimed-to-terminate (stepN 5 loopCfg … [true] claimed to reach Except.ok)",
        r#"theorem steploop_true_WRONG_terminates (st : TrustIr.MachineState) :
    ∃ vs st', TrustIr.Sem.run (TrustIr.stepN 5 loopCfg (TrustIr.BlockId.mk 0) [TrustIr.Value.bool true]) st
    = Except.ok (vs, st') := ⟨_, _, rfl⟩
"#,
    ),
    (
        "false-guard-claimed-sufficient-at-fuel-1 (needs fuel 2: one visit to bb0, one to bb1)",
        r#"theorem steploop_false_WRONG_fuel (st : TrustIr.MachineState) :
    ∃ st', TrustIr.Sem.run (TrustIr.stepN 1 loopCfg (TrustIr.BlockId.mk 0) [TrustIr.Value.bool false]) st
    = Except.ok ([], st') := ⟨_, rfl⟩
"#,
    ),
];

/// The staleness-witness fixture + theorem (Full mode only — a documentation
/// theorem, not a forgery probe: it PROVES the newly-discovered
/// `Sem.bindFresh`/`nextValueId` obstruction is real, not asserted prose).
/// `countUpCfg` is the naive `i := i+1; if i < bound …` encoding with the
/// terminator's ids hardcoded for visit 1 only; the theorem shows it runs
/// forever (`outOfFuel`) instead of the intended "count to 3, return 3".
const STEPLOOP_STALENESS_THEOREM: &str = "countup_naive_never_terminates";
const STEPLOOP_STALENESS_SRC: &str = r#"def countUpHeader : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.I32), (TrustIr.ValueId.mk 1, TrustIr.Ty.I32),
      (TrustIr.ValueId.mk 2, TrustIr.Ty.I32)]
  , body := [TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I32 (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 2)
            , TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I32 (TrustIr.ValueId.mk 3) (TrustIr.ValueId.mk 1)]
  , bodyResultDests := []
  , terminator := TrustIr.Inst.CondBr (TrustIr.ValueId.mk 4)
      (TrustIr.BlockId.mk 0) [TrustIr.ValueId.mk 3, TrustIr.ValueId.mk 1, TrustIr.ValueId.mk 2]
      (TrustIr.BlockId.mk 1) [TrustIr.ValueId.mk 3]
  , terminatorResultDests := [] }
def countUpExit : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 5, TrustIr.Ty.I32)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 5]
  , terminatorResultDests := [] }
def countUpCfg : TrustIr.CFG := fun bb =>
  match bb.index with
  | 0 => some countUpHeader
  | 1 => some countUpExit
  | _ => none
theorem countup_naive_never_terminates :
    TrustIr.Sem.run
      (TrustIr.stepN 8 countUpCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 32 0, TrustIr.Value.int 32 3, TrustIr.Value.int 32 1])
      TrustIr.MachineState.empty
    = Except.error TrustIr.SemError.outOfFuel := rfl
"#;

/// Un-bridged steploop residue, reported honestly (never faked): `(shape,
/// reason)`.
const STEPLOOP_UNBRIDGED: &[(&str, &str)] = &[
    (
        "data-computing loops (a genuine count_up incrementing a loop-carried value)",
        "BLOCKED by the newly-discovered Sem.bindFresh/nextValueId staleness obstruction \
         (kernel-proven witness: countup_naive_never_terminates) — no fixed-size CFG can \
         reference a revisited block's freshly-computed value via this evaluator; \
         stepNWithContext's bodyResultDests would avoid it but is the interprocedural \
         evaluator, out of scope",
    ),
    (
        "the SSA↔slot projection (Env : Nat → Int ↔ MachineState.locals : ValueId → Option Value)",
        "the audit's first missing lemma; not written here — this increment's loop carries no \
         DATA (a Bool flag passed through unchanged), so no projection is needed for it, but a \
         data-computing bridge would require one",
    ),
    (
        "tying to Trust.MirSem.step_cfg/exec_cfg (§6U) or a Trust.TrustIr.* mirror",
        "step_cfg/exec_cfg already have the correct block-fuel discipline (the audit's own \
         recommended proof vehicle) but have no trust-ir-keyed mirror and are not instantiated \
         per-function; not connected here",
    ),
    (
        "irreducible / multi-back-edge / nested loops",
        "this cfg is the smallest possible cycle (one self-looping block); nested or \
         multi-entry back-edges were not attempted",
    ),
    (
        "semCondBr's `.int _ v` nonzero-as-true guard arm",
        "unchanged from the stepN-branch extension; only the `.bool true`/`.bool false` guard \
         arms are bridged",
    ),
    (
        "stepNWithContext / evalFunctionInContext (interprocedural evaluation)",
        "unchanged from every prior extension; the contextual evaluator is untouched",
    ),
];

// ---------------------------------------------------------------------------
// DATALOOP EXTENSION (Full mode only) — the FIRST agreement over a back-edge
// CFG whose body COMPUTES (a genuine data-carrying counter, not steploop's
// Bool passthrough), through `stepNWithContext`/`bodyResultDests` — the
// INTERPROCEDURAL, context-honoring evaluator every prior extension
// (including steploop) left unbridged, per `STEPLOOP_UNBRIDGED`'s own
// "stepNWithContext / evalFunctionInContext (interprocedural evaluation)"
// residue line.
//
// THE FIXTURE (`dataLoopCfg`): a genuine `while (i < bound) { i := i + one }`
// 3-block CFG, one instruction per block, `bodyResultDests`-pinned so a
// revisited block's terminator always reads the CURRENT visit's freshly
// computed value (never `stepN`'s bare `Sem.bindFresh`, whose monotonically-
// growing destination is exactly the staleness hole `countup_naive_never_
// terminates` proved fatal for a data-computing loop): `dloopHeaderBlock`
// (params `i, bound, one`; body `ICmp Ult i bound` pinned to `ValueId.mk 3`;
// `CondBr` to the body block on true, the exit block on false);
// `dloopBodyBlock` (same params; body `BinOp Add i one` pinned to
// `ValueId.mk 4`; `Br` back to the header, passing the UPDATED `i`);
// `dloopExitBlock` (`Return [i]`). At `i0=0, bound=2, one=1` the walk is
// H(0<2)->B(i=1)->H(1<2)->B(i=2)->H(2<2 false)->X(return 2): 6 block-visits,
// fuel=6.
//
// THE PER-VISIT CHAIN, WITH SYMBOLIC TAIL FUEL (why this avoids the mapped
// `clean_kernel` defeq-performance wall,
// reports/clean-kernel-defeq-stepnwithcontext-2026-07-06.md +
// reports/dataloop-kernel-fix-landed-cross-attempted-2026-07-06.md): every
// prior attempt at this cross let ONE kernel obligation reduce
// `stepNWithContext` through TWO OR MORE instruction-bearing block-visits —
// catastrophic (17-24GB, even post-FoldMemo-fix) regardless of chain
// decomposition strategy. Crucially, the prior session's own chain-shaped
// probes (its `dloopSt4_chain`, tests G/J) show that even a lemma whose two
// sides are `stepNWithContext` applications ONE visit apart can blow up
// when both fuels are CONCRETE: the kernel's height-directed lazy-delta may
// unfold the RHS's own recursion too, and once both sides diverge
// structurally they only reconverge at full normalization (all remaining
// visits, both sides). `dloop_visit1` .. `dloop_visit6` below close that
// hole BY CONSTRUCTION: each is `∀ (f : Nat), Sem.run (stepNWithContext ctx
// (Nat.succ f) 0 dataLoopCfg pc args) st_k = Sem.run (stepNWithContext ctx
// f 0 dataLoopCfg pc' args') st_{k+1}` (the terminal visit returns before
// fuel is consumed, so its RHS is the literal `Except.ok (...)`). The LHS's
// fuel `Nat.succ f` iota-reduces exactly ONE level — the visit itself runs
// on fully concrete data — and lands on `stepNWithContext ctx f …` at the
// stepped state; the RHS is stuck on the SYMBOLIC `f` fuel match, so the
// kernel CANNOT unfold it past the visit boundary no matter how its
// lazy-delta orders unfolds. One block-visit per obligation is therefore a
// structural guarantee, not a hope — and a wrong state literal fails FAST
// (args-only mismatch at two stuck heads) instead of via the 17-24GB
// unfold-both-sides path. `st_{k+1}` is a NAMED `def` (`dloopState1` ..
// `dloopState6`) written via structure-update syntax REFERENCING the prior
// state by name, never re-inlining earlier history, and mirroring the TRUE
// reduct exactly — including the bindFresh+bindResultDests DOUBLE `.set`
// when the fresh id coincides with the pinned dest (visits 1-2) and the
// separate fresh-id/pinned-id sets followed by retirement of the private
// fresh id when it does not (visits 3-5), matching bindInstrResultDests.
//
// THE COMPOSITION WALL (measured 2026-07-07, three independent kills at the
// 12GB watchdog ceiling): composing the 6 proven visit lemmas into the
// single ground-fuel statement `run (stepNWithContext … 6 … from empty) =
// Except.ok (…)` is BLOCKED IN CLEAN, and the blockage is provably not a
// spelling problem. Escalation ladder, each formulation killed at ~12GB:
//   (1) `Eq.trans` at literal fuels (`dloop_visit1 5` splices `5` vs
//       `Nat.succ 4`)                                  — 12.16GB/241s;
//   (2) `Eq.trans` at succ-tower fuels (every splice BYTE-IDENTICAL,
//       two-lemma minimal chain `dloop_c12`)           — 12.13GB/166s;
//   (3) `dloop_probe_self_id_at`: `<GROUND> = <GROUND>` with the SAME
//       spelling on both sides, proven by `@rfl` with ALL arguments
//       explicit — ZERO metavariables, nothing to compare beyond
//       structural identity                            — 12.20GB/180s.
// (3) is the smoking gun: the clean declaration-loading path eagerly
// normalizes ground statement terms even when a structural-equality
// short-circuit would answer instantly, and a ground fuel-6-from-empty
// `stepNWithContext` term's normal form is the whole 6-visit interpreter
// run with inlined states (the original 17-24GB wall). Binder-stuck
// statements (∀ f, … Nat.succ f …) normalize one visit and stop — which is
// exactly why the per-visit lemmas land and every ground composition dies.
// The full composed chain (fuel_six / probes / c12..c15 / tower / literal
// congrArg bridge, all spellings above) is preserved in
// DATALOOP_COMPOSED_STEPS and exercised by `dataloop_composed_wall_
// reproducer` (env-gated) — when a clean pin makes `probe_self_id_at`
// cheap, the chain is expected to land as-is and the gate should be
// extended to assert `bridge_dataloop_counter_reaches_2`.
//
// ANTI-FORGERY (visit-level, active in the gate): `dloop_WRONG_exit_
// returns_1` (final counter claimed 1, refuted at the exit visit's
// returned value) and `dloop_WRONG_visit5_continues` (the i=2 guard visit
// claimed to re-enter the body; refuted at the stuck-head comparison —
// BlockId.mk 2 ≠ BlockId.mk 1 on the two `stepNWithContext f …`
// applications). Both are ∀-f statements in the SAME symbolic-tail-fuel
// shape as the positive lemmas, so refutation stays exactly as cheap as
// the proofs.
//
// PIN-BUMP REGRESSION (2026-07-12; fixed in clean be5ab5c92): after the clean
// pin moved ab1c8ab3 → 4abc79f0 (trust cd40de4f00), every dloop_visit lemma
// failed elaboration with "Type mismatch: expected Sort(Succ(Zero)), got Bind
// TrustIr.Sem". NOT a trust-ir v25/Ty-ctor effect — A/B-verified: the v24
// oleans fail identically under that clean pin. Root cause: clean-elab's B07
// monad-materialization pass (stub `Bind.bind`/`Pure.pure` → instance
// projection) began recognizing the machine-imported Init `Bind`/`Monad`
// classes (classExtension decode restored instance resolution) and rewrote
// the REAL 6-arg `@Bind.bind Sem self α β ma f` class-projection spines
// embedded by the per-visit one-step reduction with its 5-arg
// instance-less-stub arity — emitting `Proj(Bind,0,synthesized-inst) self α β
// ma f` (first arg of type `Bind Sem` where `{α : Type}` is expected), which
// the fail-closed kernel check rejected. Fixed at the root in clean
// (`is_instanceless_monad_stub` gates the rewrite to genuine value-less,
// instance-binder-less stubs). Post-fix visit cost at v25: ~1.1s each.
// ---------------------------------------------------------------------------

const DATALOOP_FIXTURES_SRC: &str = r#"def dloopHeaderBlock : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.I8), (TrustIr.ValueId.mk 1, TrustIr.Ty.I8),
      (TrustIr.ValueId.mk 2, TrustIr.Ty.I8)]
  , body := [TrustIr.Inst.ICmp TrustIr.ICmpOp.Ult TrustIr.Ty.I8 (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 1)]
  , bodyResultDests := [[TrustIr.ValueId.mk 3]]
  , terminator := TrustIr.Inst.CondBr (TrustIr.ValueId.mk 3)
      (TrustIr.BlockId.mk 1) [TrustIr.ValueId.mk 0, TrustIr.ValueId.mk 1, TrustIr.ValueId.mk 2]
      (TrustIr.BlockId.mk 2) [TrustIr.ValueId.mk 0]
  , terminatorResultDests := [] }
def dloopBodyBlock : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.I8), (TrustIr.ValueId.mk 1, TrustIr.Ty.I8),
      (TrustIr.ValueId.mk 2, TrustIr.Ty.I8)]
  , body := [TrustIr.Inst.BinOp TrustIr.BinOp.Add TrustIr.Ty.I8 (TrustIr.ValueId.mk 0) (TrustIr.ValueId.mk 2)]
  , bodyResultDests := [[TrustIr.ValueId.mk 4]]
  , terminator := TrustIr.Inst.Br (TrustIr.BlockId.mk 0)
      [TrustIr.ValueId.mk 4, TrustIr.ValueId.mk 1, TrustIr.ValueId.mk 2]
  , terminatorResultDests := [] }
def dloopExitBlock : TrustIr.BasicBlock :=
  { params := [(TrustIr.ValueId.mk 0, TrustIr.Ty.I8)]
  , body := []
  , bodyResultDests := []
  , terminator := TrustIr.Inst.Return [TrustIr.ValueId.mk 0]
  , terminatorResultDests := [] }
def dataLoopCfg : TrustIr.CFG := fun bb =>
  match bb.index with
  | 0 => some dloopHeaderBlock
  | 1 => some dloopBodyBlock
  | 2 => some dloopExitBlock
  | _ => none
def dloopState1 : TrustIr.MachineState :=
  { TrustIr.MachineState.empty with
      locals :=
        ((((TrustIr.ValueMap.empty.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 0)).set
            (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
            (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 1)).set
            (TrustIr.ValueId.mk 3) (TrustIr.Value.bool true)).set
            (TrustIr.ValueId.mk 3) (TrustIr.Value.bool true),
      nextValueId := 4 }
def dloopState2 : TrustIr.MachineState :=
  { dloopState1 with
      locals :=
        ((((dloopState1.locals.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 0)).set
            (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
            (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 1)).set
            (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 1)).set
            (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 1),
      nextValueId := 5 }
def dloopState3 : TrustIr.MachineState :=
  { dloopState2 with
      locals :=
        let afterResult :=
            ((((dloopState2.locals.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 1)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 1)).set
                (TrustIr.ValueId.mk 5) (TrustIr.Value.bool true)).set
                (TrustIr.ValueId.mk 3) (TrustIr.Value.bool true)
        fun id => if @BEq.beq TrustIr.ValueId (@instBEqOfDecidableEq TrustIr.ValueId TrustIr.instDecidableEqValueId) id (TrustIr.ValueId.mk 5) then none else afterResult id,
      nextValueId := 6 }
def dloopState4 : TrustIr.MachineState :=
  { dloopState3 with
      locals :=
        let afterResult :=
            ((((dloopState3.locals.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 1)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 1)).set
                (TrustIr.ValueId.mk 6) (TrustIr.Value.int 8 2)).set
                (TrustIr.ValueId.mk 4) (TrustIr.Value.int 8 2)
        fun id => if @BEq.beq TrustIr.ValueId (@instBEqOfDecidableEq TrustIr.ValueId TrustIr.instDecidableEqValueId) id (TrustIr.ValueId.mk 6) then none else afterResult id,
      nextValueId := 7 }
def dloopState5 : TrustIr.MachineState :=
  { dloopState4 with
      locals :=
        let afterResult :=
            ((((dloopState4.locals.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 2)).set
                (TrustIr.ValueId.mk 1) (TrustIr.Value.int 8 2)).set
                (TrustIr.ValueId.mk 2) (TrustIr.Value.int 8 1)).set
                (TrustIr.ValueId.mk 7) (TrustIr.Value.bool false)).set
                (TrustIr.ValueId.mk 3) (TrustIr.Value.bool false)
        fun id => if @BEq.beq TrustIr.ValueId (@instBEqOfDecidableEq TrustIr.ValueId TrustIr.instDecidableEqValueId) id (TrustIr.ValueId.mk 7) then none else afterResult id,
      nextValueId := 8 }
def dloopState6 : TrustIr.MachineState :=
  { dloopState5 with
      locals := dloopState5.locals.set (TrustIr.ValueId.mk 0) (TrustIr.Value.int 8 2),
      nextValueId := 8 }
"#;

const DATALOOP_VISITS: &[(&str, &str)] = &[
    (
        "visit1",
        r#"theorem dloop_visit1 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState1 := rfl
"#,
    ),
    (
        "visit2",
        r#"theorem dloop_visit2 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState1
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 1, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState2 := rfl
"#,
    ),
    (
        "visit3",
        r#"theorem dloop_visit3 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 1, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState2
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 1, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState3 := rfl
"#,
    ),
    (
        "visit4",
        r#"theorem dloop_visit4 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 1, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState3
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 2, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState4 := rfl
"#,
    ),
    (
        "visit5",
        r#"theorem dloop_visit5 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 2, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState4
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 dataLoopCfg (TrustIr.BlockId.mk 2)
        [TrustIr.Value.int 8 2])
      dloopState5 := rfl
"#,
    ),
    (
        "visit6",
        r#"theorem dloop_visit6 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 2)
        [TrustIr.Value.int 8 2])
      dloopState5
    = Except.ok ([TrustIr.Value.int 8 2], dloopState6) := rfl
"#,
    ),
];

#[cfg(test)]
const DATALOOP_COMPOSED_STEPS: &[(&str, &str)] = &[
    (
        "fuel_six",
        r#"theorem dloop_fuel_six :
    (6 : Nat)
    = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) := rfl
"#,
    ),
    // MECHANISM PROBES (each ~0s when the pipeline is healthy; the first one
    // to blow up localizes any remaining ground-term wall — these are the
    // probes that pinned the three clean-elab hot sites now fixed:
    // reduce-before-compare in the unifier, tree-rebuilding instantiate,
    // path-exponential meta scans):
    // probe_self_id — ground self-identity via bare `rfl`: the elaborator
    // solves rfl's implicit metas against the full ground term and the
    // unifier compares the two byte-identical sides.
    (
        "probe_self_id",
        r#"theorem dloop_probe_self_id :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty := rfl
"#,
    ),
    // probe_cited — visit1's instantiated statement proven by plain
    // CITATION (no Eq.trans, no rfl, no metas). Death here = check_type of
    // a constant citation re-normalizes the instantiated type.
    (
        "probe_cited",
        r#"theorem dloop_probe_cited :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
        0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState1 :=
  dloop_visit1 (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
"#,
    ),
    (
        "c12",
        r#"theorem dloop_c12 :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 1, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState2 :=
  Eq.trans (dloop_visit1 (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
    (dloop_visit2 (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
"#,
    ),
    (
        "c13",
        r#"theorem dloop_c13 :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
        0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 1, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState3 :=
  Eq.trans dloop_c12 (dloop_visit3 (Nat.succ (Nat.succ (Nat.succ Nat.zero))))
"#,
    ),
    (
        "c14",
        r#"theorem dloop_c14 :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ Nat.zero))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 2, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState4 :=
  Eq.trans dloop_c13 (dloop_visit4 (Nat.succ (Nat.succ Nat.zero)))
"#,
    ),
    (
        "c15",
        r#"theorem dloop_c15 :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ Nat.zero)
        0 dataLoopCfg (TrustIr.BlockId.mk 2)
        [TrustIr.Value.int 8 2])
      dloopState5 :=
  Eq.trans dloop_c14 (dloop_visit5 (Nat.succ Nat.zero))
"#,
    ),
    (
        "tower",
        r#"theorem bridge_dataloop_counter_reaches_2_tower :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))
        0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    = Except.ok ([TrustIr.Value.int 8 2], dloopState6) :=
  Eq.trans dloop_c15 (dloop_visit6 Nat.zero)
"#,
    ),
    (
        "literal",
        r#"theorem bridge_dataloop_counter_reaches_2 :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty 6 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      TrustIr.MachineState.empty
    = Except.ok ([TrustIr.Value.int 8 2], dloopState6) :=
  Eq.trans
    (congrArg
      (fun (n : Nat) =>
        TrustIr.Sem.run
          (TrustIr.stepNWithContext TrustIr.EvalContext.empty n 0 dataLoopCfg (TrustIr.BlockId.mk 0)
            [TrustIr.Value.int 8 0, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
          TrustIr.MachineState.empty)
      dloop_fuel_six)
    bridge_dataloop_counter_reaches_2_tower
"#,
    ),
];

const DATALOOP_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "exit-returns-1 (final counter claimed to be 1, not 2)",
        r#"theorem dloop_WRONG_exit_returns_1 (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 2)
        [TrustIr.Value.int 8 2])
      dloopState5
    = Except.ok ([TrustIr.Value.int 8 1], dloopState6) := rfl
"#,
    ),
    (
        "loop-never-exits (visit-5 guard claimed to re-enter the body at i=2)",
        r#"theorem dloop_WRONG_visit5_continues (f : Nat) :
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty (Nat.succ f) 0 dataLoopCfg (TrustIr.BlockId.mk 0)
        [TrustIr.Value.int 8 2, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState4
    =
    TrustIr.Sem.run
      (TrustIr.stepNWithContext TrustIr.EvalContext.empty f 0 dataLoopCfg (TrustIr.BlockId.mk 1)
        [TrustIr.Value.int 8 2, TrustIr.Value.int 8 2, TrustIr.Value.int 8 1])
      dloopState5 := rfl
"#,
    ),
];

// ---------------------------------------------------------------------------
// Errors — every variant is a FAIL-CLOSED outcome of the gate.
// ---------------------------------------------------------------------------

/// Fail-closed gate failures. An `Err` means the gate REFUSED to certify —
/// missing/tampered/stale artifacts, broken import, axiom residue, or an
/// accepted or unqualified forgery probe. (An arm that merely fails to prove is NOT an `Err`; it
/// is reported in [`BridgeAgreement::ops_pinned`].)
#[derive(Debug, thiserror::Error)]
pub enum BridgeGateError {
    #[error("olean manifest missing or unreadable at {path}: {detail}")]
    ManifestUnreadable { path: PathBuf, detail: String },
    #[error("olean manifest at {path} failed to parse: {detail}")]
    ManifestParse { path: PathBuf, detail: String },
    #[error("olean manifest at {path} has schema {found:?}, expected {expected:?}")]
    ManifestSchema { path: PathBuf, found: String, expected: String },
    #[error("olean manifest at {path} lacks required provenance field {field}")]
    ManifestProvenance { path: PathBuf, field: String },
    #[error("vendored olean {rel} (listed in {manifest}) is missing on disk")]
    OleanMissing { rel: String, manifest: PathBuf },
    #[error("vendored olean {rel} sha256 mismatch: manifest {expected}, on-disk {actual}")]
    ShaMismatch { rel: String, expected: String, actual: String },
    #[error(
        "trust-ir pin drift: vendored oleans were built from {manifest_commit} but the \
         checked-out first-party/trust-ir is {checkout_commit} — stale artifacts are stale \
         semantics; regenerate with scripts/regen-trustir-oleans.sh and update the manifest"
    )]
    PinDrift { manifest_commit: String, checkout_commit: String },
    #[error(
        "cannot resolve the checked-out first-party/trust-ir commit (fail-closed: without it \
         pin drift cannot be excluded): {detail}"
    )]
    PinUnresolvable { detail: String },
    #[error(
        "first-party/trust-ir/lean/trust_ir-semantics has local modifications (fail-closed: \
         the vendored oleans may not match the checked-out sources): {status}"
    )]
    DirtyLeanSources { status: String },
    #[error("olean import failed: {detail}")]
    Import { detail: String },
    #[error("source-bound runtime disclosure refused: {detail}")]
    RuntimeBoundary { detail: String },
    #[error("loaded module {module} maps to {rel}, which is not listed in any manifest")]
    UnmanifestedModule { module: String, rel: String },
    #[error("manifested olean {rel} was never loaded by the {root} closure (vendored-set drift)")]
    UnloadedManifestEntry { rel: String, root: String },
    #[error("bridge input constant {name} is missing from the imported closure")]
    InputMissing { name: String },
    #[error(
        "full kernel recheck of imported TrustIr constants FAILED: {fail} of {total} \
         (first: {first})"
    )]
    RecheckFailed { fail: usize, total: usize, first: String },
    #[error("wrap-elision prelude failed to prove against the imported semantics: {detail}")]
    PreludeFailed { detail: String },
    #[error("theorem {name} proved but its axiom residue is NON-EMPTY: {deps} (must be ∅)")]
    AxiomResidue { name: String, deps: String },
    #[error("FORGERY PROBE ACCEPTED ({probe}): the bridge accepted a wrong claim — soundness bug")]
    ForgeryAccepted { probe: String },
    #[error("forgery probe {probe} did not establish a semantic refutation (budget exhausted: {incomplete}): {detail}")]
    ForgeryUnqualified { probe: String, incomplete: bool, detail: String },
    #[error(
        "M4 generated family {family:?} REFUSED by the static envelope checker (plan time, \
         before any Lean was emitted or loaded): {detail}"
    )]
    GeneratedFamilyEnvelopeRefused { family: String, detail: String },
    #[error(
        "vendored oleans in {manifest} are not built for this platform: the manifest \
         vendors [{available}] but this build is {wanted}. Regenerate on this platform \
         with scripts/regen-trustir-oleans.sh --write (non-destructive — other platforms \
         are carried forward). This FAILS CLOSED on purpose: falling back to another \
         platform's bytes would feed foreign artifacts into the kernel replay path, \
         which is the exact thing the manifest exists to prevent."
    )]
    PlatformNotVendored { manifest: PathBuf, available: String, wanted: String },
    #[error(
        "vendored oleans for {triple} in {manifest} were built from trust-ir {built_from} but \
         the manifest's trustir_commit is {manifest_commit}: this platform's bytes were CARRIED \
         FORWARD, not rebuilt, so replaying them under {manifest_commit}'s name would state a \
         false provenance. Rebuild on {triple} with scripts/regen-trustir-oleans.sh --write."
    )]
    PlatformStale { manifest: PathBuf, triple: String, built_from: String, manifest_commit: String },
    #[error(
        "TIMEOUT: bridge gate step {steps_begun} ({step}) did not finish within its \
         {budget_secs}s wall-clock step budget. This is neither a proof nor a refutation: the \
         gate did not complete, so NO Lean↔Clean agreement is claimed"
    )]
    BudgetExceeded { budget_secs: u64, step: String, steps_begun: u64 },
    #[error(
        "the budgeted bridge gate could not run its bounded worker ({detail}); running it \
         unbounded instead would silently drop the --budget-secs bound, so NO Lean↔Clean \
         agreement is claimed"
    )]
    BudgetWorkerUnavailable { detail: String },
}

impl BridgeGateError {
    /// Whether the gate stopped WITHOUT a verdict — its wall-clock budget ran
    /// out ([`Self::BudgetExceeded`], a TIMEOUT), its worker could not run, or
    /// a required forgery probe did not establish a semantic refutation.
    /// Nothing is claimed; this distinguishes an unknown from a rejection.
    #[must_use]
    pub fn is_incomplete(&self) -> bool {
        matches!(self, Self::BudgetExceeded { .. } | Self::BudgetWorkerUnavailable { .. }
            | Self::ForgeryUnqualified { .. })
    }
}

// ---------------------------------------------------------------------------
// Manifest verification
// ---------------------------------------------------------------------------

#[derive(Debug, Deserialize)]
struct ManifestDoc {
    schema: String,
    provenance: ManifestProvenance,
    /// Files whose bytes are identical on every vendored platform.
    files: BTreeMap<String, String>,
    /// Per-platform artifacts, keyed by target triple. A file appears here
    /// only when the vendored platforms actually DISAGREE about its bytes; its
    /// on-disk path is `platform/<triple>/<key>`. Empty on a single-platform
    /// tree, which is why it defaults rather than being required.
    #[serde(default)]
    platforms: BTreeMap<String, ManifestPlatform>,
    #[serde(default)]
    source_reuse: Option<toml::Value>,
}

#[derive(Debug, Deserialize)]
struct ManifestPlatform {
    #[serde(default)]
    files: BTreeMap<String, String>,
    /// The trust-ir revision THIS platform's bytes were built from. A
    /// regeneration on one platform carries every other platform's bytes
    /// forward unchanged, so this can lag `[provenance] trustir_commit`; the
    /// gate refuses such a platform rather than replay it under the newer name.
    #[serde(default)]
    built_from_trustir_commit: Option<String>,
    // (lean_version / built_on are recorded per platform for humans; the gate
    // does not read them.)
}

#[derive(Debug, Deserialize)]
struct ManifestProvenance {
    #[serde(default)]
    trustir_commit: Option<String>,
    lean_toolchain: String,
    // (The manifests carry further human-facing provenance — root_module,
    // build_command — not needed by the gate logic. `lean_version`/`built_on`
    // moved into the per-platform tables in schema v2: a single stamp here
    // necessarily named one platform while claiming to describe every byte.)
}

/// The target triple this build verifies vendored oleans for.
///
/// Must match the triple `scripts/regen-trustir-oleans.sh` derives from Lean's
/// own version string, because that is what names the `platform/<triple>/`
/// directories.
fn host_triple() -> String {
    format!(
        "{}-{}",
        std::env::consts::ARCH,
        match (std::env::consts::OS, std::env::consts::FAMILY) {
            ("macos", _) => "apple-darwin",
            ("linux", _) => "unknown-linux-gnu",
            ("windows", _) => "pc-windows-msvc",
            (other, _) => other,
        }
    )
}

/// A verified vendored-olean tree: files listed in the manifest, each with a
/// matching on-disk sha256.
#[derive(Debug)]
struct VerifiedTree {
    dir: PathBuf,
    /// `<dir>/platform/<host triple>` — where artifacts whose bytes differ per
    /// platform live. Searched BEFORE `dir` so a platform-specific olean
    /// shadows the shared one; absent (and simply never matching) on a tree
    /// with no platform-specific files.
    platform_dir: PathBuf,
    files: BTreeSet<String>,
    // Typed logical module -> the exact physical file selected by this host.
    selected: BTreeMap<Name, manifest_inputs::SelectedModule>,
    trustir_commit: Option<String>,
    lean_toolchain: String,
    source_reuse: bool,
    /// Complete bytes actually parsed above; includes the optional reuse record.
    manifest_sha256: String,
}

impl VerifiedTree {
    /// Directories to search for this tree's oleans, most specific first.
    fn search_dirs(&self) -> Vec<PathBuf> {
        vec![self.platform_dir.clone(), self.dir.clone()]
    }
}

fn sha256_file(path: &Path) -> std::io::Result<String> {
    let bytes = std::fs::read(path)?;
    let mut h = Sha256::new();
    h.update(&bytes);
    Ok(format!("{:x}", h.finalize()))
}

fn verify_manifest(
    dir: &Path,
    expected_schema: &str,
    require_commit: bool,
) -> Result<VerifiedTree, BridgeGateError> {
    let root = manifest_inputs::canonical_root(dir)?;
    let dir = root.as_path();
    let manifest_path = dir.join("MANIFEST.toml");
    let text = std::fs::read_to_string(&manifest_path).map_err(|e| {
        BridgeGateError::ManifestUnreadable { path: manifest_path.clone(), detail: e.to_string() }
    })?;
    let doc: ManifestDoc = toml::from_str(&text).map_err(|e| BridgeGateError::ManifestParse {
        path: manifest_path.clone(),
        detail: e.to_string(),
    })?;
    if doc.schema != expected_schema {
        return Err(BridgeGateError::ManifestSchema {
            path: manifest_path,
            found: doc.schema,
            expected: expected_schema.to_string(),
        });
    }
    if require_commit && doc.provenance.trustir_commit.is_none() {
        return Err(BridgeGateError::ManifestProvenance {
            path: manifest_path,
            field: "trustir_commit".to_string(),
        });
    }
    // Schema v2 partitions the file table by build platform. Verify the shared
    // set plus THIS platform's overrides, and nothing else: another platform's
    // bytes are legitimately present on disk but are not ours to check.
    let triple = host_triple();
    let mine = doc.platforms.get(&triple);
    if !doc.platforms.is_empty() && mine.is_none() {
        return Err(BridgeGateError::PlatformNotVendored {
            manifest: manifest_path,
            available: doc.platforms.keys().cloned().collect::<Vec<_>>().join(", "),
            wanted: triple,
        });
    }

    // The host platform's bytes must have been BUILT from the manifest's
    // trust-ir revision. A platform table that does not say what it was built
    // from is refused too when a commit is required: absent provenance cannot
    // be told apart from carried-forward bytes.
    if let (Some(platform), Some(manifest_commit)) = (mine, &doc.provenance.trustir_commit) {
        match &platform.built_from_trustir_commit {
            Some(built_from) if built_from == manifest_commit => {}
            Some(built_from) => {
                return Err(BridgeGateError::PlatformStale {
                    manifest: manifest_path,
                    triple,
                    built_from: built_from.clone(),
                    manifest_commit: manifest_commit.clone(),
                });
            }
            None if require_commit => {
                return Err(BridgeGateError::ManifestProvenance {
                    path: manifest_path,
                    field: format!("platforms.\"{triple}\".built_from_trustir_commit"),
                });
            }
            None => {}
        }
    }

    let mut files = BTreeSet::new();
    let mut selected = BTreeMap::new();
    let shared = doc.files.iter().map(|(r, s)| (r, s, false));
    let specific = mine.into_iter().flat_map(|p| p.files.iter().map(|(r, s)| (r, s, true)));
    for (rel, expected_sha, is_platform) in shared.chain(specific) {
        let module = manifest_inputs::module_key(rel)?;
        // A platform-specific artifact lives under platform/<triple>/, so that
        // two platforms can vendor the same logical module without one
        // overwriting the other at a shared path.
        let full =
            if is_platform { dir.join("platform").join(&triple).join(rel) } else { dir.join(rel) };
        if std::fs::symlink_metadata(&full).is_err() {
            return Err(BridgeGateError::OleanMissing { rel:rel.clone(),manifest:manifest_path.clone() });
        }
        let selection = manifest_inputs::select(dir, full.clone(), expected_sha)?;
        let actual = sha256_file(&full).map_err(|_| BridgeGateError::OleanMissing {
            rel: rel.clone(),
            manifest: manifest_path.clone(),
        })?;
        if &actual != expected_sha {
            return Err(BridgeGateError::ShaMismatch {
                rel: rel.clone(),
                expected: expected_sha.clone(),
                actual,
            });
        }
        // Keyed by LOGICAL module path in both cases — callers look modules up
        // by name and must not have to know which platform provided the bytes.
        files.insert(rel.clone());
        // Declared platform overrides intentionally win over the shared row.
        selected.insert(module, selection);
    }
    manifest_inputs::require_unambiguous_paths(&selected)?;
    Ok(VerifiedTree {
        dir: dir.to_path_buf(),
        platform_dir: dir.join("platform").join(&triple),
        files,
        selected,
        trustir_commit: doc.provenance.trustir_commit,
        lean_toolchain: doc.provenance.lean_toolchain,
        source_reuse: doc.source_reuse.is_some(),
        manifest_sha256: format!("{:x}", Sha256::digest(text.as_bytes())),
    })
}

// ---------------------------------------------------------------------------
// Pin resolution (the checked-out trust-ir commit)
// ---------------------------------------------------------------------------

fn git_stdout(args: &[&str], cwd: &Path) -> Option<String> {
    let out = Command::new("git").args(args).current_dir(cwd).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn looks_like_commit(s: &str) -> bool {
    s.len() == 40 && s.chars().all(|c| c.is_ascii_hexdigit())
}

/// Resolve the commit of the checked-out `first-party/trust-ir` submodule:
/// (a) the submodule working tree's own HEAD (what the sources actually are),
/// falling back to (b) the superproject's recorded gitlink. Fail-closed when
/// neither resolves — without the commit, pin drift cannot be excluded.
fn resolve_trustir_checkout(repo_root: &Path) -> Result<String, BridgeGateError> {
    let sub = repo_root.join("first-party").join("trust-ir");
    if let Some(head) = git_stdout(&["rev-parse", "HEAD"], &sub) {
        if looks_like_commit(&head) {
            return Ok(head);
        }
    }
    if let Some(line) = git_stdout(&["ls-tree", "HEAD", "first-party/trust-ir"], repo_root) {
        // format: "160000 commit <sha>\tfirst-party/trust-ir"
        if let Some(sha) = line.split_whitespace().nth(2) {
            if looks_like_commit(sha) {
                return Ok(sha.to_string());
            }
        }
    }
    Err(BridgeGateError::PinUnresolvable {
        detail: format!(
            "git rev-parse HEAD in {} and git ls-tree HEAD first-party/trust-ir in {} both \
             failed (is the submodule initialized and git available?)",
            sub.display(),
            repo_root.display()
        ),
    })
}

/// Fail-closed control: the pinned Lean sources must not carry local edits
/// (the vendored oleans certify the COMMITTED sources only). Only enforced
/// when git can answer; an unanswerable status falls back to the commit
/// comparison already performed.
fn check_lean_sources_clean(repo_root: &Path) -> Result<(), BridgeGateError> {
    let sub = repo_root.join("first-party").join("trust-ir");
    if let Some(status) =
        git_stdout(&["status", "--porcelain", "--", "lean/trust_ir-semantics"], &sub)
    {
        if !status.is_empty() {
            return Err(BridgeGateError::DirtyLeanSources {
                status: status.lines().take(5).collect::<Vec<_>>().join("; "),
            });
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The thin check seam: parse → elaborate+register → kernel-typecheck Lean
// source against the already-imported environment. Ported (Apache-2.0, same
// author) from first-party/clean/crates/clean/src/check.rs `load_source_into`
// — depending on the `clean` facade crate would pull clean-cli/tokio/server
// into the trust workspace for one function.
// ---------------------------------------------------------------------------

/// clean-elab / clean-kernel keep GLOBAL counters (sorry, kernel-check
/// failures) that are not reentrant; serialize bridge elaboration exactly as
/// clean's own check pipeline does.
///
/// # This lock is why a stalled bridge test names the wrong test
///
/// The lock is held for the WHOLE parse+elaborate+kernel-recheck of a source
/// fragment, and several `#[test]`s in this module call
/// [`load_bridge_source`]; libtest runs them concurrently and names each OS
/// thread after its test. So `sample <pid>` on a slow run prints a fat,
/// *idle* stack under the name of whichever test is BLOCKED in
/// `__psynch_mutexwait`, while the kernel frames in the same sample belong to
/// the other thread — the one actually holding this lock. Measured
/// 2026-09-19: `imported_int_order_instances_preserve_relations` takes 3.7 s
/// alone, 53.8 s beside its module, 205 s in the full suite, and 3265 of 3265
/// samples of that delta are lock wait, not work. Read the OWNER of the lock
/// before attributing time to a test name.
fn elab_lock() -> &'static Mutex<()> {
    static LOCK: std::sync::OnceLock<Mutex<()>> = std::sync::OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

/// Ambient per-declaration kernel budget armed around every bridge
/// declaration (see [`load_bridge_source`]).
///
/// # Why a bound is needed here at all
///
/// clean-kernel's own guards do not bound a bridge declaration:
///
/// * `TypeChecker::set_heartbeat_limit` bounds ONE checker, and the tactic
///   engine, the unifier, instance resolution and `add_decl` each mint their
///   own at `DEFAULT_HEARTBEAT_LIMIT`; a declaration that keeps minting
///   checkers runs forever while no heartbeat is ever exceeded. That is the
///   hole `clean_kernel::tc::decl_budget` exists to close, and it is DISABLED
///   by default (limit `0` = unlimited) on every thread.
/// * `MAX_LAZY_DELTA_ITERATIONS = 10_000` in
///   `clean-kernel/src/tc/def_eq/delta.rs` counts iterations of ONE
///   `lazy_delta_reduction` call. The structure-eta path re-enters
///   `is_def_eq_impl`, which starts a fresh delta loop with a fresh counter,
///   so on a mutually recursive defeq query the cap never binds — measured
///   60 289 nested `is_def_eq_inner` frames on `bridge_cast_zext`
///   (`docs/issues/2026-09-19-clean-defeq-structure-eta-escapes-delta-cap.md`).
///
/// This ambient counter is thread-local and every checker on the thread draws
/// from the same pot, so it bounds the DECLARATION rather than a step.
///
/// # How this number was chosen (measured 2026-09-19 at 86fdb2ff19)
///
/// Armed at `u64::MAX` — counted, unreachable — over the whole
/// `trustir_bridge::` module, single threaded, debug build, on a 14-core
/// arm64 box. Peak ticks spent by any ONE bridge declaration: **13 714 632**,
/// spent by one of the two `:= rfl` cast arms (`bridge_cast_zext` 107.4 s,
/// `bridge_cast_sext` 95.3 s); every other declaration in the corpus is
/// orders of magnitude cheaper — `bridge_cast_trunc` 8.8 s, the 17 notation
/// instances 0.22 s together. This constant clears that peak by ~4.7x.
///
/// The counter is deterministic — the same input spends the same ticks on any
/// machine at any load — so the headroom is for a bridge corpus that GROWS,
/// not for a slow box. At the measured tick rate (~10^5/s on the pathological
/// arms) this bounds one runaway declaration at roughly 10 minutes of wall
/// clock.
///
/// Re-measure by setting this to `u64::MAX` and reading
/// [`bridge_peak_decl_ticks`], which the deadlined bridge tests print on
/// every run: it is the calibration instrument, not a knob.
///
/// # What it does and does not bound
///
/// Exhaustion is neither a pass nor a refutation: clean-kernel raises its own
/// `TypeError::DeclarationBudgetExhausted`, and [`load_bridge_source`] turns
/// it into a named per-declaration ERROR. A resource bound can only refuse a
/// declaration, never accept one, so this is TCB-neutral. It does NOT bound a
/// pathology whose cost is per-tick ALLOCATION SIZE rather than tick count —
/// `clean-kernel/src/tc/decl_budget.rs` is explicit about that, and it is why
/// the heavy bridge tests also carry a wall-clock deadline
/// ([`run_with_bridge_deadline`]).
const BRIDGE_DECL_BUDGET: u64 = 64_000_000;

/// Peak ambient ticks any single bridge declaration has spent in this
/// process — the calibration reading behind [`BRIDGE_DECL_BUDGET`].
static BRIDGE_PEAK_DECL_TICKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The peak ambient tick count observed by [`load_bridge_source`] so far.
///
/// Public because it is the calibration instrument for
/// [`BRIDGE_DECL_BUDGET`]: re-measure by raising that constant to `u64::MAX`
/// (counted, unreachable), running the bridge corpus, and reading this.
#[must_use]
pub fn bridge_peak_decl_ticks() -> u64 {
    BRIDGE_PEAK_DECL_TICKS.load(std::sync::atomic::Ordering::Relaxed)
}

/// The bridge declaration currently being elaborated, for the deadline
/// diagnosis: a wall-clock timeout must be able to NAME what did not finish,
/// and the elaborating thread cannot report that about itself.
fn bridge_decl_in_flight() -> &'static Mutex<String> {
    static IN_FLIGHT: std::sync::OnceLock<Mutex<String>> = std::sync::OnceLock::new();
    IN_FLIGHT.get_or_init(|| Mutex::new("(no bridge declaration started)".to_owned()))
}

/// The declaration [`load_bridge_source`] most recently began, as a label.
///
/// Public so an out-of-process or integration-level watchdog can name what
/// did not finish; the elaborating thread cannot report that about itself.
#[must_use]
pub fn bridge_decl_in_flight_label() -> String {
    bridge_decl_in_flight()
        .lock()
        .map_or_else(|poisoned| poisoned.into_inner().clone(), |guard| guard.clone())
}

/// Surface name of a parsed declaration, before elaboration can report one.
fn bridge_decl_label(decl: &clean_parser::SurfaceDecl) -> String {
    use clean_parser::SurfaceDecl;
    fn spelled(name: &clean_parser::SurfaceName) -> String {
        name.source_spelling().unwrap_or_else(|| format!("{:?}", name.name()))
    }
    match decl {
        SurfaceDecl::Def { name, .. }
        | SurfaceDecl::Theorem { name, .. }
        | SurfaceDecl::Axiom { name, .. }
        | SurfaceDecl::Opaque { name, .. }
        | SurfaceDecl::Inductive { name, .. }
        | SurfaceDecl::Structure { name, .. } => spelled(name),
        SurfaceDecl::Instance { name, .. } => {
            name.as_ref().map_or_else(|| "(anonymous instance)".to_owned(), spelled)
        }
        _ => "(unnamed declaration)".to_owned(),
    }
}

/// Arms the ambient per-declaration budget for the current thread and
/// disarms it on drop.
///
/// The budget is thread-local and latching, so leaving it armed would apply
/// this crate's limit to unrelated later work on the same libtest thread.
/// Restores the previous LIMIT; nothing in trust-clean arms an outer budget,
/// so the previous limit is `0` (disabled) at every call site today — a
/// future nested caller would find its own declaration refilled rather than
/// resumed, which is why this is a scope guard and not a bare pair of calls.
struct BridgeDeclBudgetScope {
    previous_limit: u64,
}

impl BridgeDeclBudgetScope {
    fn enter(limit: u64) -> Self {
        let previous_limit = clean_kernel::tc::declaration_budget_limit();
        clean_kernel::tc::set_declaration_budget(limit);
        Self { previous_limit }
    }
}

impl Drop for BridgeDeclBudgetScope {
    fn drop(&mut self) {
        clean_kernel::tc::set_declaration_budget(self.previous_limit);
    }
}

// ---------------------------------------------------------------------------
// The per-step WALL-CLOCK budget of a budgeted gate run
// ---------------------------------------------------------------------------

/// Where one budgeted gate run stands: which step it is in and when that step
/// began. Shared between the gate's worker thread (which advances it) and the
/// watchdog on the calling thread (which reads it).
struct BridgeStepState {
    /// Steps begun so far (the gate's prologue is step 1).
    index: u64,
    /// When the CURRENT step began.
    started: Instant,
    /// What the current step is doing, so a timeout NAMES what did not finish.
    label: String,
    /// The slowest step completed so far, for `TRUST_PROVE_TIMING`.
    peak: (std::time::Duration, String),
}

/// The step clock of one budgeted gate run (see [`run_bridge_gate_with_step_budget`]).
struct BridgeStepClock {
    state: Mutex<BridgeStepState>,
    /// Print each completed step's wall time to stderr (`TRUST_PROVE_TIMING`,
    /// the prove driver's existing localization switch). Diagnostics only: it
    /// never changes which step runs or what it proves.
    timing: bool,
}

impl BridgeStepClock {
    fn new(label: &str) -> Self {
        Self {
            state: Mutex::new(BridgeStepState {
                index: 1,
                started: Instant::now(),
                label: label.to_owned(),
                peak: (std::time::Duration::ZERO, String::new()),
            }),
            timing: std::env::var_os("TRUST_PROVE_TIMING").is_some(),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BridgeStepState> {
        self.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn begin(&self, label: String) {
        let mut state = self.lock();
        let now = Instant::now();
        let spent = now.duration_since(state.started);
        if self.timing {
            eprintln!("  [bridge-gate step {:>4}] {:>10.2?}  {}", state.index, spent, state.label);
        }
        if spent > state.peak.0 {
            let finished = std::mem::replace(&mut state.label, label);
            state.peak = (spent, finished);
        } else {
            state.label = label;
        }
        state.index += 1;
        state.started = now;
    }
}

thread_local! {
    /// The step clock of the budgeted gate run executing on THIS thread, if
    /// any. Thread-local so concurrent gate runs (libtest) never see each
    /// other's progress: a stalled run cannot be kept alive by a sibling's
    /// ticks.
    static BRIDGE_STEP_CLOCK: std::cell::RefCell<Option<std::sync::Arc<BridgeStepClock>>> =
        const { std::cell::RefCell::new(None) };
}

/// Mark the start of a new unit of gate work. Every unit that can take
/// noticeable time — each manifest verification, the olean import, the
/// imported-constant recheck, every elaborated declaration, every axiom-residue
/// walk — begins with this call, so a budgeted run bounds EACH of them by the
/// step budget. A no-op (the label is never built) outside a budgeted run.
fn bridge_gate_step(label: impl FnOnce() -> String) {
    BRIDGE_STEP_CLOCK.with(|slot| {
        if let Some(clock) = slot.borrow().as_ref() {
            clock.begin(label());
        }
    });
}

/// Stack for the budgeted gate's worker. The gate ran on `targo trust
/// prove`'s 512 MiB main worker before it was budgeted; keep that headroom
/// (a reservation, not a commitment) so moving it cannot change its depth
/// behavior.
const BRIDGE_GATE_WORKER_STACK: usize = 512 * 1024 * 1024;

/// How many per-function budgets (`targo trust prove --budget-secs`) ONE
/// bridge-gate step may spend.
///
/// # Why the gate's unit is not the function's unit
///
/// The gate is ~600 steps (measured 2026-09-25, Full mode), nearly all far
/// cheaper than a function; one is not. The `wrong_threshold` stepInst-Overflow
/// forgery probe (`bridge_stepInst_overflow_add_unsigned_wrong_threshold`) is
/// genuinely rejected by the kernel after 108.7 s and 133.5 s in two runs of an
/// opt-level-2 clean build, and after 129.6 s in a release `targo-trust`, on a
/// loaded 18-core host (no declaration of the run spent more than 5.4 M ticks,
/// far inside [`BRIDGE_DECL_BUDGET`] — slow, not runaway); the next slowest
/// step took 5.8–10.7 s. Bounding each gate step by the bare per-function
/// default (30 s) would therefore time the default gate out on that probe and
/// leave every default scorecard without its bridge evidence — a capability
/// loss, not a bound.
///
/// At this scale the default per-function budget gives each gate step 600 s,
/// ~4.5x that peak (the same calibration discipline as `BRIDGE_DECL_BUDGET`),
/// while an explicit tight budget still stops a gate step promptly
/// (`--budget-secs=1` gives each step 20 s). Re-measure with
/// `TRUST_PROVE_TIMING=1`, which prints every step's wall time, before
/// changing it: it is a calibration, not a knob.
pub const BRIDGE_STEP_BUDGET_SCALE: u64 = 20;

/// [`run_bridge_gate`] under a per-step WALL-CLOCK budget of
/// `step_budget_secs` seconds — how `targo trust prove --budget-secs` bounds
/// the bridge gate.
///
/// `targo trust prove` gives each function in the dump population
/// `--budget-secs` of wall clock; it gives each unit of bridge-gate work (see
/// [`bridge_gate_step`]) [`BRIDGE_STEP_BUDGET_SCALE`] times that. The gate is
/// ~600 such units, so the bound is per unit, exactly as it is per function: a
/// unit that exceeds it ends the run with [`BridgeGateError::BudgetExceeded`]
/// naming the unit. That outcome is a TIMEOUT — neither proved nor refuted —
/// and attaches NO agreement: it can only withhold the bridge claim, never
/// mint one. Without this, `prove --budget-secs=1` waited on the whole
/// unbudgeted gate (measured 2026-09-25: 116 s in a release build, and more
/// than 8 minutes, unfinished, in a debug build, both on a loaded 18-core
/// host).
///
/// `step_budget_secs == 0` runs the gate inline with no wall-clock bound, as
/// `prove_dump_dir_with_budget(_, 0)` does for functions.
///
/// Rust cannot stop a running thread, so on a timeout the worker is DETACHED:
/// it keeps computing, and keeps holding the elaboration lock, until it
/// finishes or the process exits. A process that timed a gate out should not
/// run bridge work again; `targo trust prove` exits right after reporting.
///
/// # Errors
///
/// Every [`run_bridge_gate`] error, plus [`BridgeGateError::BudgetExceeded`]
/// and [`BridgeGateError::BudgetWorkerUnavailable`]. A panic inside the gate is
/// re-raised on the calling thread, exactly as the unbudgeted call would raise
/// it.
pub fn run_bridge_gate_with_step_budget(
    config: &BridgeGateConfig,
    step_budget_secs: u64,
) -> Result<BridgeAgreement, BridgeGateError> {
    if step_budget_secs == 0 {
        return run_bridge_gate(config);
    }
    let config = config.clone();
    run_with_step_budget(step_budget_secs, "bridge gate start", move || run_bridge_gate(&config))?
}

/// Run `work` on a worker thread, bounding every step it begins (via
/// [`bridge_gate_step`]) by `step_budget_secs` of wall clock. The first step
/// begins at spawn, labeled `first_step`.
fn run_with_step_budget<T: Send + 'static>(
    step_budget_secs: u64,
    first_step: &str,
    work: impl FnOnce() -> T + Send + 'static,
) -> Result<T, BridgeGateError> {
    use std::sync::Arc;
    use std::sync::mpsc::{RecvTimeoutError, channel};

    let budget = std::time::Duration::from_secs(step_budget_secs);
    let clock = Arc::new(BridgeStepClock::new(first_step));
    let worker_clock = Arc::clone(&clock);
    let (done_tx, done_rx) = channel();
    let worker = std::thread::Builder::new()
        .name("trust-bridge-gate".to_owned())
        .stack_size(BRIDGE_GATE_WORKER_STACK)
        .spawn(move || {
            BRIDGE_STEP_CLOCK.with(|slot| *slot.borrow_mut() = Some(worker_clock));
            // A send error means the watchdog already timed this run out and
            // stopped listening: the late result is discarded, never counted.
            let _ = done_tx.send(work());
        })
        .map_err(|error| BridgeGateError::BudgetWorkerUnavailable { detail: error.to_string() })?;
    loop {
        let (index, deadline) = {
            let state = clock.lock();
            (state.index, state.started + budget)
        };
        match done_rx.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
            Ok(value) => {
                // The worker sent its result as its last act; reap it.
                let _ = worker.join();
                if clock.timing {
                    clock.begin("(end)".to_owned());
                    let state = clock.lock();
                    eprintln!(
                        "  [bridge-gate] {} steps; slowest {:.2?} ({}); budget {budget:?} per step",
                        state.index - 1,
                        state.peak.0,
                        state.peak.1
                    );
                }
                return Ok(value);
            }
            Err(RecvTimeoutError::Timeout) => {
                let state = clock.lock();
                if state.index != index {
                    // A new step began while we waited; its own deadline applies.
                    continue;
                }
                return Err(BridgeGateError::BudgetExceeded {
                    budget_secs: step_budget_secs,
                    step: state.label.clone(),
                    steps_begun: state.index,
                });
            }
            // The worker ended without sending: `work` panicked. Surface that
            // panic here, as the unbudgeted call would have.
            Err(RecvTimeoutError::Disconnected) => {
                return match worker.join() {
                    Err(panic) => std::panic::resume_unwind(panic),
                    Ok(()) => Err(BridgeGateError::BudgetWorkerUnavailable {
                        detail: "the gate worker ended without reporting a result".to_owned(),
                    }),
                };
            }
        }
    }
}

fn elab_result_name(result: &clean_elab::ElabResult) -> String {
    use clean_elab::ElabResult;
    match result {
        ElabResult::Diagnosed { result, .. } => elab_result_name(result),
        ElabResult::Definition { name, .. }
        | ElabResult::Theorem { name, .. }
        | ElabResult::Axiom { name, .. }
        | ElabResult::Opaque { name, .. }
        | ElabResult::Structure { name, .. }
        | ElabResult::Instance { name, .. }
        | ElabResult::Inductive { name, .. } => name.to_string(),
        ElabResult::MutualInductive { decl, .. } => decl
            .types
            .first()
            .map_or_else(|| "(mutual inductive)".to_string(), |t| t.name.to_string()),
        ElabResult::Failed { name, .. } => name.clone(),
        // Trust: anonymous by construction (clean's own `name()` returns None for it).
        ElabResult::Example { .. } => "(example)".to_string(),
        ElabResult::Command(_) | ElabResult::Multiple(_) | ElabResult::Skipped => {
            "(skipped)".to_string()
        }
    }
}

fn typecheck_elab_result(
    result: &clean_elab::ElabResult,
    tc: &TypeChecker<'_>,
    env: &Environment,
) -> Result<(), String> {
    use clean_elab::ElabResult;
    match result {
        // Source diagnostics do not revoke registration. This mathematical
        // bridge must still recheck the actual enclosed declaration.
        ElabResult::Diagnosed { result, .. } => typecheck_elab_result(result, tc, env),
        ElabResult::Skipped | ElabResult::Command(_) | ElabResult::Multiple(_) => Ok(()),
        ElabResult::Failed { name, error, .. } => Err(format!("{name}: {error}")),
        // Trust: `Example` claims its `val` was already kernel-checked against
        // `ty` upstream — this function's job is to RE-check, so it gets the
        // Definition treatment, not a waiver.
        ElabResult::Definition { ty, val, .. }
        | ElabResult::Instance { ty, val, .. }
        | ElabResult::Example { ty, val, .. } => {
            let _ = tc.infer_sort(ty).map_err(|e| format!("type check error on type: {e}"))?;
            tc.check_type(val, ty).map_err(|e| format!("type check error on value: {e}"))?;
            Ok(())
        }
        ElabResult::Theorem { ty, proof, .. } => {
            let sort = tc.infer_sort(ty).map_err(|e| format!("type check error on type: {e}"))?;
            if !sort.is_zero() {
                return Err(format!(
                    "{}: type must be a Prop (Sort 0), got Sort {sort}",
                    elab_result_name(result)
                ));
            }
            tc.check_type(proof, ty).map_err(|e| format!("type check error on proof: {e}"))?;
            Ok(())
        }
        ElabResult::Axiom { ty, .. }
        | ElabResult::Opaque { ty, .. }
        | ElabResult::Structure { ty, .. } => {
            let _ = tc.infer_sort(ty).map_err(|e| format!("type check error: {e}"))?;
            Ok(())
        }
        ElabResult::Inductive { name, .. } => {
            if env.get_const(&Name::from_string(&name.to_string())).is_none() {
                return Err(format!(
                    "inductive {name} not found in environment after registration"
                ));
            }
            Ok(())
        }
        ElabResult::MutualInductive { decl, .. } => {
            for ind_ty in &decl.types {
                if env.get_const(&Name::from_string(&ind_ty.name.to_string())).is_none() {
                    return Err(format!(
                        "mutual inductive {} not found in environment after registration",
                        ind_ty.name
                    ));
                }
            }
            Ok(())
        }
    }
}

/// Elaborate + kernel-check one source fragment against the imported
/// environment. Returns the registered declaration names, or the per-decl
/// failure report. `sorry` is a failure (there is no allow_sorry here: a
/// bridge theorem with a hole is not a bridge theorem).
///
/// Every declaration is bounded by [`BRIDGE_DECL_BUDGET`]; a declaration that
/// spends it is reported as NOT FINISHED, which is neither a pass nor a
/// refutation.
pub(crate) fn load_bridge_source(
    env: &mut Environment,
    source: &str,
) -> Result<Vec<String>, String> {
    load_bridge_source_with_budget(env, source, BRIDGE_DECL_BUDGET)
}

/// [`load_bridge_source`] with the per-declaration budget spelled out, so the
/// bound itself can be tested: a test passes a deliberately tiny budget and
/// asserts the refusal is a NAMED non-convergence report rather than a pass.
fn load_bridge_source_with_budget(
    env: &mut Environment,
    source: &str,
    budget: u64,
) -> Result<Vec<String>, String> {
    load_bridge_source_with_budget_observed(env, source, budget, |_, _| {})
}

/// Observe the original typed elaboration failure before rendering it. The
/// observer runs under the same elaboration lock and receives the declaration
/// budget latch, so tests can distinguish a semantic refutation from an
/// incomplete check without parsing diagnostics or changing admission.
fn load_bridge_source_with_budget_observed(
    env: &mut Environment,
    source: &str,
    budget: u64,
    mut observe_error: impl FnMut(&clean_elab::ElabError, bool),
) -> Result<Vec<String>, String> {
    use clean_elab::{
        FileContext, elaborate_decl_and_register_with_warning, kernel_check_failure_count,
        preprocess_decl_with_context,
    };
    use clean_kernel::sorry::reset_sorry_counter;
    use clean_parser::parse_file_with_tactics;

    let _guard = elab_lock().lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    reset_sorry_counter();
    clean_elab::register::reset_kernel_check_counter();

    bridge_gate_step(|| {
        let head = source.trim_start().lines().next().unwrap_or_default();
        format!("parse bridge source `{}`", head.chars().take(80).collect::<String>())
    });
    let patterns = clean_elab::tactic::builtins::builtin_tactic_patterns();
    let decls = match parse_file_with_tactics(source, &patterns) {
        Ok(d) => d,
        Err(e) => return Err(format!("parse error: {e}")),
    };

    let mut file_ctx = FileContext::new();
    let mut names = Vec::new();
    let mut errors = Vec::new();
    // Bound each declaration. See `BRIDGE_DECL_BUDGET`: without this, a defeq
    // query that does not converge is an unbounded hang with no diagnosis,
    // because every guard clean-kernel arms by default is per-checker or
    // per-call and this work spans many of both.
    let _budget = BridgeDeclBudgetScope::enter(budget);
    for decl in &decls {
        clean_kernel::tc::reset_declaration_budget();
        let label = bridge_decl_label(decl);
        bridge_gate_step(|| format!("elaborate + kernel-check `{label}`"));
        if let Ok(mut in_flight) = bridge_decl_in_flight().lock() {
            label.clone_into(&mut in_flight);
        }
        let kernel_failures_before = kernel_check_failure_count();
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_warning(env, &processed) {
            Ok(registered) => {
                let name = elab_result_name(&registered.result);
                if let Some(error) = registered.result.source_error_message() {
                    errors.push(format!("{name}: source diagnostics: {error}"));
                }
                if name == "(skipped)" {
                    note_declaration_budget(&label, &mut errors);
                    continue;
                }
                let tc = TypeChecker::with_mode(env, env.mode());
                match typecheck_elab_result(&registered.result, &tc, env) {
                    Ok(()) => {
                        let kernel_delta =
                            kernel_check_failure_count().saturating_sub(kernel_failures_before);
                        if kernel_delta > 0 {
                            errors.push(format!("{name}: kernel check failures: {kernel_delta}"));
                        } else if registered.warning.as_ref().is_some_and(|w| {
                            matches!(
                                w.kind,
                                clean_elab::RegistrationWarningKind::ExplicitSorry
                                    | clean_elab::RegistrationWarningKind::SyntheticSorry
                                    | clean_elab::RegistrationWarningKind::TrustedArith
                                    | clean_elab::RegistrationWarningKind::TrustedAy
                            )
                        }) {
                            errors
                                .push(format!("{name}: carries trust debt (sorry/trusted marker)"));
                        } else {
                            names.push(name);
                        }
                    }
                    Err(e) => errors.push(format!("{name}: {e}")),
                }
            }
            Err(e) => {
                observe_error(&e, clean_kernel::tc::declaration_budget_exhausted());
                errors.push(format!("(elaboration): {e:?}"));
            }
        }
        note_declaration_budget(&label, &mut errors);
    }

    reset_sorry_counter();
    clean_elab::register::reset_kernel_check_counter();

    if errors.is_empty() { Ok(names) } else { Err(errors.join(" | ")) }
}

fn semantic_type_mismatch(error: &clean_elab::ElabError) -> bool {
    use clean_elab::{ElabError, tactic::TacticError};
    match error {
        ElabError::TypeMismatch { .. } | ElabError::ProofTypeMismatch { .. } => true,
        ElabError::InTactic { source, .. }
        | ElabError::TacticFailed(TacticError::UpstreamElabError { source }) => {
            semantic_type_mismatch(source)
        }
        ElabError::TacticFailed(TacticError::TypeMismatch { .. }) => true,
        _ => false,
    }
}

/// These fixed probes have checked positive premises and a false proof term.
/// Missing input, trust debt, or spent budgets cannot count as their refutation.
fn check_semantic_forgery_with_budget(
    env: &mut Environment,
    label: &str,
    source: &str,
    budget: u64,
) -> Result<(), BridgeGateError> {
    let mut classified = Vec::new();
    let result = load_bridge_source_with_budget_observed(env, source, budget, |error, incomplete| {
        classified.push((semantic_type_mismatch(error), incomplete));
    });
    match result {
        Ok(_) => Err(BridgeGateError::ForgeryAccepted { probe: label.to_owned() }),
        Err(_) if classified == [(true, false)] => Ok(()),
        Err(detail) => Err(BridgeGateError::ForgeryUnqualified {
            probe: label.to_owned(),
            incomplete: classified.iter().any(|(_, incomplete)| *incomplete),
            detail,
        }),
    }
}

/// Close out one declaration's ambient budget: record its cost, and report
/// non-convergence as a named error.
///
/// Asked AFTER the fact and unconditionally, because the ambient budget
/// LATCHES: even when the kernel's typed `DeclarationBudgetExhausted` was
/// swallowed on the way up and the declaration reported an ordinary pass, the
/// latch still says the work was cut short, and that reading wins over both a
/// pass and a refutation.
fn note_declaration_budget(label: &str, errors: &mut Vec<String>) {
    use std::sync::atomic::Ordering;

    let spent = clean_kernel::tc::declaration_budget_used();
    BRIDGE_PEAK_DECL_TICKS.fetch_max(spent, Ordering::Relaxed);
    if clean_kernel::tc::declaration_budget_exhausted() {
        errors.push(format!(
            "{label}: DID NOT FINISH — spent the whole per-declaration kernel budget of {} \
             operations without converging. This is neither proved nor refuted: the \
             declaration's kernel query did not terminate inside the bound. Either it \
             diverges (see BRIDGE_DECL_BUDGET and \
             docs/issues/2026-09-19-clean-defeq-structure-eta-escapes-delta-cap.md), or \
             the bridge corpus has grown past what that budget was calibrated on — \
             re-measure with bridge_peak_decl_ticks() before raising it.",
            clean_kernel::tc::declaration_budget_limit()
        ));
    }
}

/// The non-foundational axiom residue of `name`, rendered for reporting.
/// `Some("[]")` is the required outcome for every bridge theorem.
fn axiom_deps_str(env: &Environment, name: &str) -> String {
    match Name::from_str(name).ok().and_then(|n| env.axiom_deps(&n)) {
        None => "<not found>".to_string(),
        Some(deps) => {
            let mut v: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            v.sort();
            format!("{v:?}")
        }
    }
}

pub(crate) fn require_empty_axiom_deps(
    env: &Environment,
    name: &str,
) -> Result<(), BridgeGateError> {
    bridge_gate_step(|| format!("axiom residue of `{name}`"));
    let deps = axiom_deps_str(env, name);
    if deps == "[]" {
        Ok(())
    } else {
        Err(BridgeGateError::AxiomResidue { name: name.to_string(), deps })
    }
}

// ---------------------------------------------------------------------------
// Gate configuration + summary
// ---------------------------------------------------------------------------

/// How much of the gate to run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BridgeGateMode {
    /// Manifest + pin + import + a SPOT arm set (one arm per form family:
    /// Add [b], FAdd [a], UDiv [b+guard]) + one forgery probe, with the
    /// kernel recheck restricted to the bridge-input constants. Seconds, for
    /// quick iteration; `ops_*` counts refer to the spot set only. Also
    /// attempts the UnOp Neg arm (+ its connecting corollary) and one UnOp
    /// forgery probe (`unop_*` counts refer to that spot slice only). Also
    /// attempts one Overflow VALUE arm (unsigned AddOverflow) + one Overflow
    /// FLAG arm (unsigned AddOverflow, Lemma 2) + one Overflow forgery probe
    /// (`overflow_*` counts refer to that spot slice only). Also attempts one
    /// ICmp arm per kind family (Ult[u], Eq[eq], Slt[s]) + one ICmp forgery
    /// probe (`icmp_*` counts refer to that spot slice only). Also attempts
    /// one Cast arm (Trunc) + one Cast forgery probe, skipping the conc rows,
    /// the Tier-2 widening corollaries, and the composed theorem (`cast_*`
    /// counts refer to that spot slice only).
    Spot,
    /// Everything: full TrustIr recheck (0 failures required), all 18 arms,
    /// all 6 reduction lemmas, all 11 characterization rows, the composed
    /// all-18 theorem, both forgery probes. The default-on gate. Also proves
    /// all 3 bridged UnOp arms (Neg/Not/FNeg), Neg's connecting corollary,
    /// the 2 UnOp concrete rows, the composed UnOp conjunction, and both
    /// UnOp forgery probes. Also proves all 6 Overflow VALUE arms
    /// (unsigned/signed × Add/Sub/Mul), all 6 Overflow FLAG arms, four
    /// actual unsigned-Mul Int predicate links, the twelve-statement composed
    /// Overflow conjunction, and five qualified Overflow forgery probes. Also proves all 10 ICmp arms (Eq/Ne/Ult/Ule/Ugt/Uge/
    /// Slt/Sle/Sgt/Sge — each an unconditional rfl agreement), the 4 ICmp
    /// concrete pin rows, the composed ICmp conjunction, and all 3 ICmp
    /// forgery probes. Also proves all 3 Cast arms (Trunc/ZExt/SExt — each
    /// `∀ v, …` at a concrete `ValueId`/`Ty`/`MachineState` shape), the 4
    /// Cast concrete anchor rows, the ZExt Tier-2 widening-identity
    /// connecting corollary (the analogous SExt corollary is mathematically
    /// real but hits a confirmed clean-elaborator limitation, honestly not
    /// attempted — see the module doc), the composed Cast conjunction, and
    /// both Cast forgery probes.
    Full,
}

/// Where the vendored artifacts and the pinned submodule live.
#[derive(Debug, Clone)]
pub struct BridgeGateConfig {
    /// Directory of the vendored TrustIr `.olean`s (+ MANIFEST.toml).
    pub trustir_olean_dir: PathBuf,
    /// Directory of the vendored Lean-core Init `.olean`s (+ MANIFEST.toml).
    pub lean_core_olean_dir: PathBuf,
    /// Repo root (for resolving the checked-out trust-ir commit).
    pub repo_root: PathBuf,
    /// Test override for the "checked-out trust-ir commit". `None` (the
    /// shipped default) resolves via git and ALSO enforces the clean-sources
    /// control; `Some` compares the manifest against the given value only.
    pub expected_trustir_commit: Option<String>,
    pub mode: BridgeGateMode,
}

impl BridgeGateConfig {
    /// The shipped locations: fixtures under this crate, Lean-core under
    /// `vendor/`, repo root two levels above `crates/trust-clean`.
    #[must_use]
    pub fn locate(mode: BridgeGateMode) -> Self {
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let repo_root = manifest_dir
            .parent()
            .and_then(Path::parent)
            .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
        Self {
            trustir_olean_dir: manifest_dir.join("fixtures").join("trustir-oleans"),
            lean_core_olean_dir: repo_root.join("vendor").join("lean-core-oleans"),
            repo_root,
            expected_trustir_commit: None,
            mode,
        }
    }
}

/// The §6-citable summary of one gate run. Only produced when every
/// fail-closed control passed; arms that did not prove are in
/// [`Self::ops_pinned`] / [`Self::pinned`].
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeAgreement {
    /// Arms whose agreement theorem kernel-checked THIS RUN with empty axiom
    /// residue (18 = the whole `semIntBinOp` surface; Spot mode attempts 3).
    pub ops_bridged: usize,
    /// Arms attempted but NOT proven — recorded, never silently dropped. The
    /// default-on test asserts this is 0, so a pin regression fails loudly.
    pub ops_pinned: usize,
    /// `op: failure head` for every pinned arm.
    pub pinned: Vec<String>,
    /// The proven ops, in `semIntBinOp` arm order, as `op[form]`.
    pub bridged: Vec<String>,
    /// Proven arms of form (a) — plain agreement, no side condition.
    pub form_a: usize,
    /// Proven arms of form (b) — agreement under the no-overflow side
    /// condition (includes the guarded arms, which are (b) + UB guards).
    pub form_b: usize,
    /// Of `form_b`, how many additionally carry the arm's UB guards.
    pub form_b_guarded: usize,
    /// Reduction lemmas proven (6 in Full mode, 1 in Spot).
    pub reduction_lemmas: usize,
    /// Characterization rows proven (11 in Full mode, 0 in Spot).
    pub characterization_rows: usize,
    /// Whether the COMPOSED all-18 conjunction theorem
    /// (`bridge_semIntBinOp_agreement_all18`) kernel-checked with empty
    /// residue (Full mode only; requires all 18 arms).
    pub composed_all18: bool,
    /// Original trust-ir producer commit. Reuse never rewrites this origin.
    pub trustir_commit: String,
    /// Actual selected revision, either identical or checked input-equivalent.
    #[serde(default)]
    pub selected_trustir_commit: String,
    /// Original artifact commit used by the checked source-reuse path.
    #[serde(default)]
    pub source_reuse_anchor: Option<String>,
    /// Open runtime obligations from the selected immutable producer input.
    /// None means unreported, never zero obligations or runtime certification.
    #[serde(default)]
    pub runtime_frontier: Option<RuntimeFrontier>,
    /// The pinned Lean toolchain that built the artifacts.
    pub lean_toolchain: String,
    /// Both manifests verified: schema, provenance, per-file sha256, and
    /// loaded-modules == manifested-files. Always true on `Ok`.
    pub manifest_ok: bool,
    /// Total vendored files across both manifests.
    pub manifest_files: usize,
    /// Modules / constants machine-imported from the vendored oleans.
    pub modules_loaded: usize,
    pub constants_loaded: usize,
    /// Safe declarations admitted by local type/value replay (Full mode;
    /// Spot checks the bridge-input slice), under the assumed imported
    /// environment. Not fresh dependency-closed kernel admission.
    pub trustir_recheck_pass: usize,
    /// Fatal declaration or census-accounting failures, never runtime refusals.
    /// A successful gate always reports zero.
    pub trustir_recheck_fail: usize,
    /// Entire selected declaration roster, including explicitly refused runtime
    /// implementations. These are not all kernel admissions.
    pub trustir_recheck_seen: usize,
    /// Original artifact unsafe/partial declarations explicitly refused by the
    /// same replay graph. They supply no kernel admission or proof authority.
    pub trustir_runtime_refused: usize,
    /// Every proven theorem this run had `axiom_deps = ∅`. Always true on
    /// `Ok` (a nonempty residue is a hard failure).
    pub axiom_deps_empty: bool,
    /// Deliberately-wrong claims kernel-REJECTED this run (2 in Full mode,
    /// 1 in Spot). An accepted forgery is a hard failure.
    pub fail_closed_controls: usize,
    /// Which mode produced this summary ("full" / "spot").
    pub mode: String,
    /// Wall-clock seconds for the whole gate run.
    pub gate_seconds: f64,

    // -- semIntUnOp (the UnOp extension; same shape as the BinOp fields \
    //    above, scoped to the 3 bridged arms Neg/Not/FNeg). --
    /// UnOp arms whose agreement theorem kernel-checked THIS RUN with empty
    /// axiom residue (3 = Neg/Not/FNeg in Full mode; Spot attempts 1: Neg).
    pub unop_ops_bridged: usize,
    /// UnOp arms attempted but NOT proven — never silently dropped.
    pub unop_ops_pinned: usize,
    /// `op: failure head` for every pinned UnOp arm.
    pub unop_pinned: Vec<String>,
    /// The proven UnOp ops, in `semIntUnOp` arm order, as `op[form]`.
    pub unop_bridged: Vec<String>,
    /// Proven UnOp arms of form (a) — plain agreement (FNeg).
    pub unop_form_a: usize,
    /// Proven UnOp arms of form (b) — agreement under the no-overflow/
    /// in-range side condition (Neg, Not).
    pub unop_form_b: usize,
    /// Whether the CONNECTING corollary `bridge_neg_sub_zero_form` (Neg
    /// restated in the exact `Int.sub (Int.ofNat 0) operand` term
    /// `clean_ground::ground_int`'s `F::Neg` arm emits) kernel-checked.
    pub unop_neg_sub_zero_form: bool,
    /// Concrete-value pin rows proven (2 in Full mode: `neg_conc`/`not_conc`).
    pub unop_conc_rows: usize,
    /// Whether the COMPOSED `bridge_semIntUnOp_agreement_all` conjunction
    /// (Neg ∧ Not ∧ FNeg) kernel-checked with empty residue (Full mode only;
    /// requires all 3 UnOp arms).
    pub unop_composed: bool,
    /// UnOp deliberately-wrong claims kernel-REJECTED this run (2 in Full
    /// mode, 1 in Spot). An accepted forgery is a hard failure.
    pub unop_fail_closed_controls: usize,
    /// UnOp arms Clean intentionally does NOT bridge, honestly reported as
    /// `"op: reason"` (currently just CtPop — no popcount denotation
    /// exists to agree against).
    pub unop_unbridged: Vec<String>,

    // -- semOverflowOp (the OverflowOp extension: the OVERFLOW-CHECKED
    //    arithmetic semantics, `.1` VALUE + `.2` overflow-FLAG components,
    //    each op×signedness combination reported separately). --
    /// Overflow VALUE arms whose agreement theorem kernel-checked THIS RUN
    /// with empty axiom residue (6 = unsigned/signed × Add/Sub/Mul in Full
    /// mode; Spot attempts 1: unsigned AddOverflow).
    pub overflow_value_bridged: usize,
    /// Overflow VALUE arms attempted but NOT proven — never silently dropped.
    pub overflow_value_pinned: usize,
    /// `op[signed?]: failure head` for every pinned Overflow VALUE arm.
    pub overflow_value_pinned_list: Vec<String>,
    /// The proven Overflow VALUE ops, as `op[u]`/`op[s]` (unsigned/signed).
    pub overflow_value_bridged_list: Vec<String>,
    /// Overflow FLAG arms whose `reduces` PIN + `connect` theorem BOTH
    /// kernel-checked THIS RUN with empty NON-FOUNDATIONAL residue (6 in
    /// Full mode; Spot attempts 1: unsigned AddOverflow).
    pub overflow_flag_bridged: usize,
    /// Overflow FLAG arms attempted but NOT proven — never silently dropped.
    pub overflow_flag_pinned: usize,
    /// `op[signed?]: failure head` for every pinned Overflow FLAG arm.
    pub overflow_flag_pinned_list: Vec<String>,
    /// The proven Overflow FLAG ops, as `op[u]`/`op[s]`, with the cited Lemma
    /// (e.g. `"AddOverflow[u]:Lemma 2"`).
    pub overflow_flag_bridged_list: Vec<String>,
    /// Of `overflow_flag_bridged`, how many are GUARDED (take the documented
    /// `lhs,rhs ∈ [0,2^w)` residue precondition as hypotheses — currently
    /// just unsigned-Sub's Lemma 8 arm, to discharge its vacuous disjunct).
    pub overflow_flag_guarded: usize,
    /// Whether the COMPOSED `bridge_semOverflowOp_agreement_all` conjunction
    /// (6 VALUE ∧ 6 FLAG statements) checked with empty non-foundational residue.
    /// Full only; also requires the four actual unsigned-Mul Int predicate links.
    pub overflow_composed: bool,
    /// Qualified semantic Overflow refusals (5 in Full, 1 in Spot).
    /// Missing inputs, parser errors and spent budgets cannot count as refutations.
    pub overflow_fail_closed_controls: usize,
    /// Overflow-flag arms Clean intentionally does NOT bridge, honestly
    /// reported as `"op: reason"` (none for the six generic Int flags).
    /// This does not grant a BV-equivalence or unregistered-width claim.
    pub overflow_flag_unbridged: Vec<String>,
    /// Actual canonical production Int predicates registered/checked this run
    /// (four in Full, none in Spot); this does not bind the separate BV family.
    #[serde(default)]
    pub overflow_umul_predicates_bound: Vec<String>,
    /// Per-width universal flag theorems checked against those actual declarations.
    #[serde(default)]
    pub overflow_umul_predicate_bridged: Vec<String>,
    /// Per-width Int predicate links not proved; never silently dropped.
    #[serde(default)]
    pub overflow_umul_predicate_pinned: Vec<String>,
    /// Actual foundational axiom closure of the proved four predicate links.
    /// Empty non-foundational residue does not imply this set is empty.
    #[serde(default)]
    pub overflow_umul_foundational_axioms: Vec<String>,
    /// Actual foundational closure consumed by checked overflow statements/prelude.
    /// Existing canonical foundational policy is unchanged.
    #[serde(default)]
    pub overflow_foundational_axioms: Vec<String>,

    // -- semICmp (the ICmp extension: trust-ir's INTEGER-COMPARISON
    //    semantics — the pure Int×Int→Bool predicate under every branch
    //    guard, every CondBr discriminant, and every safety-VC threshold). --
    /// ICmp arms whose agreement theorem kernel-checked THIS RUN with empty
    /// axiom residue (10 = all of Eq/Ne/Ult/Ule/Ugt/Uge/Slt/Sle/Sgt/Sge in
    /// Full mode; Spot attempts 3: Ult[u], Eq[eq], Slt[s]).
    pub icmp_ops_bridged: usize,
    /// ICmp arms attempted but NOT proven — never silently dropped.
    pub icmp_ops_pinned: usize,
    /// `op: failure head` for every pinned ICmp arm.
    pub icmp_pinned: Vec<String>,
    /// The proven ICmp ops, in `semICmp`/`ICmpOp` arm order, as `op[kind]`
    /// (`u`=unsigned, `eq`=sign-independent, `s`=signed).
    pub icmp_bridged: Vec<String>,
    /// Proven ICmp arms of kind Unsigned (Ult/Ule/Ugt/Uge — raw-operand
    /// `Int.lt`/`Int.le`, Ugt/Uge arg-swapped).
    pub icmp_kind_unsigned: usize,
    /// Proven ICmp arms of kind SignIndependent (Eq/Ne).
    pub icmp_kind_sign_independent: usize,
    /// Proven ICmp arms of kind Signed (Slt/Sle/Sgt/Sge — `Int.lt`/`Int.le`
    /// at the `toSigned` operand images, Sgt/Sge arg-swapped).
    pub icmp_kind_signed: usize,
    /// Concrete-value pin rows proven (4 in Full mode: the Ult/Slt
    /// sign-distinction pair + Eq/Ne).
    pub icmp_conc_rows: usize,
    /// Whether the COMPOSED `bridge_semICmp_agreement_all` conjunction (all 10
    /// arms) kernel-checked with empty residue (Full mode only; requires all
    /// 10 arms).
    pub icmp_composed: bool,
    /// ICmp deliberately-wrong claims kernel-REJECTED this run (3 in Full
    /// mode, 1 in Spot). An accepted forgery is a hard failure.
    pub icmp_fail_closed_controls: usize,
    /// ICmp arms Clean intentionally does NOT bridge, honestly reported as
    /// `"op: reason"`. EMPTY — all 10 arms bridge (the signed arms are a
    /// genuine agreement at the `toSigned` images, not a faked claim).
    pub icmp_unbridged: Vec<String>,

    // -- semCast (the Cast extension: trust-ir's INTEGER-CAST value
    //    semantics — Trunc/ZExt/SExt, the width-conversion pure cores
    //    `semCast`'s monadic dispatch computes). --
    /// Cast arms whose agreement theorem kernel-checked THIS RUN with empty
    /// axiom residue (3 = Trunc/ZExt/SExt in Full mode; Spot attempts 1:
    /// Trunc).
    pub cast_ops_bridged: usize,
    /// Cast arms attempted but NOT proven — never silently dropped.
    pub cast_ops_pinned: usize,
    /// `op: failure head` for every pinned Cast arm.
    pub cast_pinned: Vec<String>,
    /// The proven Cast ops, in `semCast`/`CastOp` arm order (Trunc/ZExt/
    /// SExt).
    pub cast_bridged: Vec<String>,
    /// Concrete-value anchor rows proven (4 in Full mode: Trunc wrap/no-op +
    /// SExt negative/positive branch).
    pub cast_conc_rows: usize,
    /// TIER 2 widening-identity connecting corollaries kernel-checked THIS
    /// RUN (1 in Full mode: ZExt — Full mode only, pure `Int` arithmetic with
    /// no monad involved). The analogous SExt corollary is mathematically
    /// real (proven against a genuine Lean 4.8.0 toolchain) but is NOT
    /// attempted here — it hits a confirmed clean-elaborator limitation
    /// around `Int.le`/`Int.NonNeg` definitional equality for a symbolic
    /// `HPow.hPow` term; see the doc comment above `CAST_COMPOSED_SRC`.
    pub cast_widening_bridged: usize,
    /// The proven Cast widening corollaries, by name.
    pub cast_widening_list: Vec<String>,
    /// GAP-CROSS-SIGN-WIDEN (2026-07-16) — TIER 2 SIGN-CROSSING widening-identity
    /// connecting corollaries kernel-checked THIS RUN (1 in Full mode:
    /// `bridge_cast_zext_signcross_widening_identity`, proving `u_w -> i_W`
    /// (`W > w`) is value-preserving — `toSigned (truncateUnsigned v dstW) dstW = v`
    /// under `0 ≤ v < 2^(dstW-1)`). Full mode only; empty in Spot.
    pub cast_signcross_widening_bridged: usize,
    /// The proven sign-crossing widening corollaries, by name.
    pub cast_signcross_widening_list: Vec<String>,
    /// Whether the COMPOSED `bridge_semCast_agreement_all` conjunction (3
    /// arms + 1 widening corollary) kernel-checked with empty residue (Full
    /// mode only; requires all 3 arms + the ZExt widening corollary).
    pub cast_composed: bool,
    /// Cast deliberately-wrong claims kernel-REJECTED this run (2 in Full
    /// mode, 1 in Spot). An accepted forgery is a hard failure.
    pub cast_fail_closed_controls: usize,
    /// Cast arms Clean intentionally does NOT bridge, honestly reported as
    /// `"op: reason"` (the 14 non-integer CastOp variants — no Clean
    /// denotation exists for any of them, faking one would be dishonest).
    pub cast_unbridged: Vec<String>,

    // -- stepInst .BinOp (the FIRST statement/instruction-level extension: --
    //    the monadic READ->COMPUTE->WRITE chain of `stepInst` dispatching a --
    //    `.BinOp` instruction, connected to the ALREADY-BRIDGED semIntBinOp --
    //    value arms). --
    /// stepInst-BinOp arms whose chain+connect theorems BOTH kernel-checked
    /// THIS RUN with empty axiom residue (7 = Add/Sub/Mul/UDiv/SDiv/URem/SRem in Full mode; Spot
    /// attempts 1: Add).
    pub stepinst_binop_bridged: usize,
    /// stepInst-BinOp arms attempted but NOT proven — never silently dropped.
    pub stepinst_binop_pinned: usize,
    /// `op: chain|connect: failure head` for every pinned stepInst-BinOp arm.
    pub stepinst_binop_pinned_list: Vec<String>,
    /// The proven stepInst-BinOp ops, in `semIntBinOp` arm order (`["Add",
    /// "Sub", "Mul", "UDiv", "SDiv", "URem", "SRem"]` in Full mode).
    pub stepinst_binop_bridged_list: Vec<String>,
    /// Whether the COMPOSED `bridge_stepInst_binop_agreement_all` conjunction
    /// (all seven integer arithmetic arms) kernel-checked with empty residue
    /// (Full mode only; requires all seven arms proven).
    pub stepinst_binop_composed: bool,
    /// stepInst-BinOp deliberately-wrong claims semantically REJECTED this run
    /// (13 in Full mode; 1 in Spot). Includes result, guard, divisor and
    /// full-state/SSA mutations. Missing input or exhausted budget is incomplete;
    /// an accepted forgery is a hard failure.
    pub stepinst_binop_fail_closed_controls: usize,
    /// The other 11 `semIntBinOp` ops reachable through this same `stepInst`
    /// `.BinOp` arm, honestly reported as un-chained (value-bridged via
    /// ARMS; the technique generalizes but was not executed for them).
    pub stepinst_binop_unbridged: Vec<String>,
    /// The other 52 (of 57) `Inst` variant categories whose `stepInst` arm
    /// is not bridged at all (grouped: `FCmp`, the one remaining category
    /// with an already-bridged... no, NOT-yet-bridged VALUE semantics
    /// awaiting its own value bridge first, and the 51 with none).
    pub stepinst_categories_unbridged: Vec<String>,

    // -- stepInst .UnOp/.Overflow/.ICmp/.Cast (EXTENSION 9: completing --
    //    EXTENSION 5's instruction-execution technique for every OTHER --
    //    Inst category whose VALUE core is already bridged, one --
    //    representative op each). --
    /// stepInst-UnOp arms whose chain+connect theorems BOTH kernel-checked
    /// THIS RUN with empty axiom residue (1 = Neg, both modes).
    pub stepinst_unop_bridged: usize,
    /// stepInst-UnOp arms attempted but NOT proven — never silently dropped.
    pub stepinst_unop_pinned: usize,
    /// `op: chain|connect: failure head` for every pinned stepInst-UnOp arm.
    pub stepinst_unop_pinned_list: Vec<String>,
    /// The proven stepInst-UnOp ops (`["Neg"]`).
    pub stepinst_unop_bridged_list: Vec<String>,
    /// Whether Neg's bonus sub-zero-form corollary
    /// (`bridge_stepInst_unop_neg_sub_zero_form`) kernel-checked THIS RUN.
    pub stepinst_unop_neg_sub_zero_form: bool,
    /// Whether the COMPOSED `bridge_stepInst_unop_agreement_all` conjunction
    /// (Neg ∧ its sub-zero corollary) kernel-checked with empty residue.
    pub stepinst_unop_composed: bool,
    /// stepInst-UnOp deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode: wrong-op-agreement + dropped-negation; 1 in Spot).
    pub stepinst_unop_fail_closed_controls: usize,
    /// `Not`/`FNeg`, honestly reported as un-chained (value-bridged via
    /// UNOP_ARMS; the technique generalizes but was not executed for them).
    pub stepinst_unop_unbridged: Vec<String>,

    /// stepInst-Overflow arms whose chain+connect theorems BOTH
    /// kernel-checked THIS RUN with empty axiom residue (1 = unsigned
    /// AddOverflow, both modes).
    pub stepinst_overflow_bridged: usize,
    /// stepInst-Overflow arms attempted but NOT proven — never silently
    /// dropped.
    pub stepinst_overflow_pinned: usize,
    /// `combo: chain|connect: failure head` for every pinned stepInst-Overflow
    /// arm.
    pub stepinst_overflow_pinned_list: Vec<String>,
    /// The proven stepInst-Overflow combos (`["AddOverflow[u]"]`).
    pub stepinst_overflow_bridged_list: Vec<String>,
    /// Whether the (trivially-restated, single-arm) COMPOSED
    /// `bridge_stepInst_overflow_agreement_all` theorem kernel-checked with
    /// empty residue.
    pub stepinst_overflow_composed: bool,
    /// stepInst-Overflow deliberately-wrong claims kernel-REJECTED this run
    /// (2 in Full mode: wrong-op-agreement + wrong-threshold; 1 in Spot).
    pub stepinst_overflow_fail_closed_controls: usize,
    /// The other 5 op×signedness combos, honestly reported as un-chained
    /// (value-bridged via OVERFLOW_VALUE_ARMS/OVERFLOW_FLAG_ARMS; the
    /// technique generalizes but was not executed for them).
    pub stepinst_overflow_unbridged: Vec<String>,

    /// stepInst-ICmp arms whose chain+connect theorems BOTH kernel-checked
    /// THIS RUN with empty axiom residue (1 = Ult, both modes).
    pub stepinst_icmp_bridged: usize,
    /// stepInst-ICmp arms attempted but NOT proven — never silently dropped.
    pub stepinst_icmp_pinned: usize,
    /// `op: chain|connect: failure head` for every pinned stepInst-ICmp arm.
    pub stepinst_icmp_pinned_list: Vec<String>,
    /// The proven stepInst-ICmp ops (`["Ult"]`).
    pub stepinst_icmp_bridged_list: Vec<String>,
    /// Whether the (trivially-restated, single-arm) COMPOSED
    /// `bridge_stepInst_icmp_agreement_all` theorem kernel-checked with
    /// empty residue.
    pub stepinst_icmp_composed: bool,
    /// stepInst-ICmp deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode: wrong-relation + swapped-operand; 1 in Spot).
    pub stepinst_icmp_fail_closed_controls: usize,
    /// The other 9 comparison ops, honestly reported as un-chained
    /// (value-bridged via ICMP_ARMS; the technique generalizes but was not
    /// executed for them).
    pub stepinst_icmp_unbridged: Vec<String>,

    /// stepInst-Cast arms whose chain+connect theorems BOTH kernel-checked
    /// THIS RUN with empty axiom residue (1 = Trunc, both modes).
    pub stepinst_cast_bridged: usize,
    /// stepInst-Cast arms attempted but NOT proven — never silently dropped.
    pub stepinst_cast_pinned: usize,
    /// `op: chain|connect: failure head` for every pinned stepInst-Cast arm.
    pub stepinst_cast_pinned_list: Vec<String>,
    /// The proven stepInst-Cast ops (`["Trunc"]`).
    pub stepinst_cast_bridged_list: Vec<String>,
    /// Whether the (trivially-restated, single-arm) COMPOSED
    /// `bridge_stepInst_cast_agreement_all` theorem kernel-checked with empty
    /// residue.
    pub stepinst_cast_composed: bool,
    /// stepInst-Cast deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode: wrong-destination-width + dropped-truncation; 1 in Spot).
    pub stepinst_cast_fail_closed_controls: usize,
    /// `ZExt`/`SExt`, honestly reported as un-chained (value-bridged via
    /// CAST_ARMS; the technique generalizes but was not executed for them).
    pub stepinst_cast_unbridged: Vec<String>,

    /// Whether the OVERALL `bridge_stepInst_categories_agreement_all`
    /// conjunction (Neg ∧ unsigned-AddOverflow ∧ Ult ∧ Trunc, spanning all 4
    /// categories above) kernel-checked with empty residue (requires all 4
    /// categories' primary connect theorems proven).
    pub stepinst_categories_composed: bool,

    // -- stepN/stepBlock (the FIRST WHOLE-BLOCK extension: multi- --
    //    instruction, terminator-inclusive agreement, one layer above --
    //    stepInst). --
    /// stepblock arms whose outer-chain + connect theorems BOTH
    /// kernel-checked THIS RUN with empty axiom residue (1 = Add in both
    /// Full and Spot mode — there is only one arm currently).
    pub stepblock_bridged: usize,
    /// stepblock arms attempted but NOT proven — never silently dropped.
    pub stepblock_pinned: usize,
    /// `op: outer_chain|connect: failure head` for every pinned stepblock
    /// arm.
    pub stepblock_pinned_list: Vec<String>,
    /// The proven stepblock ops (`["Add"]` when bridged).
    pub stepblock_bridged_list: Vec<String>,
    /// Whether the COMPOSED `bridge_stepblock_agreement_all` theorem
    /// kernel-checked with empty residue (requires the Add arm proven; runs
    /// in both Full and Spot mode since there is only one arm).
    pub stepblock_composed: bool,
    /// stepblock deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode: wrong-final-value + wrong-operand-threaded-to-terminator;
    /// 1 in Spot). An accepted forgery is a hard failure.
    pub stepblock_fail_closed_controls: usize,
    /// Un-bridged stepblock residue, honestly reported as `"shape: reason"`
    /// (Sub/Mul-return blocks, multi-instruction bodies, branching/
    /// multi-block CFGs, loops, the interprocedural evaluator).
    pub stepblock_unbridged: Vec<String>,

    // -- stepN .CondBr / .Continue (the FIRST BRANCHING whole-body --
    //    extension: the recursive case stepblock's fuel=1 base case never --
    //    touched). --
    /// stepN-branch arms (true/false path) whose chain + connect theorems
    /// BOTH kernel-checked THIS RUN with empty axiom residue (2 = both
    /// paths, in both Full and Spot mode — there are only two arms).
    pub stepbranch_bridged: usize,
    /// stepN-branch arms attempted but NOT proven — never silently dropped.
    pub stepbranch_pinned: usize,
    /// `guard: chain|connect: failure head` for every pinned stepN-branch
    /// arm.
    pub stepbranch_pinned_list: Vec<String>,
    /// The proven stepN-branch guards (`["true", "false"]` when both
    /// bridged).
    pub stepbranch_bridged_list: Vec<String>,
    /// Whether the COMPOSED `bridge_stepN_branch_agreement_all` theorem
    /// (true ∧ false) kernel-checked with empty residue (requires both arms
    /// proven; runs in both Full and Spot mode).
    pub stepbranch_composed: bool,
    /// stepN-branch deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode: true-guard-yields-else-value + false-guard-yields-then-value;
    /// 1 in Spot). An accepted forgery is a hard failure.
    pub stepbranch_fail_closed_controls: usize,
    /// Un-bridged stepN-branch residue, honestly reported as `"shape:
    /// reason"` (Switch, nested/chained CondBrs, loops, non-empty arm
    /// bodies, the integer-guard semCondBr arm, the interprocedural
    /// evaluator).
    pub stepbranch_unbridged: Vec<String>,

    // -- stepN branch-WITH-BODY (the composition of EXTENSION 7's --
    //    control-flow technique with EXTENSION 6's body-fold technique — --
    //    closing EXTENSION 7's own named "non-empty bodies on either arm" --
    //    residue). --
    /// stepN branch-WITH-BODY arms (true/false path) whose chain + connect
    /// theorems BOTH kernel-checked THIS RUN with empty axiom residue (2 in
    /// Full mode; Spot attempts 1 — the true/Add arm only, since `bridge_sub`
    /// is never loaded in Spot mode).
    pub stepbranch_body_bridged: usize,
    /// stepN branch-WITH-BODY arms attempted but NOT proven — never
    /// silently dropped (in Spot mode this also counts the false arm, which
    /// is never attempted, matching the stepInst-BinOp Spot-mode precedent).
    pub stepbranch_body_pinned: usize,
    /// `guard: chain|connect: failure head` for every pinned stepN
    /// branch-WITH-BODY arm.
    pub stepbranch_body_pinned_list: Vec<String>,
    /// The proven stepN branch-WITH-BODY guards (`["true", "false"]` when
    /// both bridged; `["true"]` in Spot mode).
    pub stepbranch_body_bridged_list: Vec<String>,
    /// Whether the COMPOSED `bridge_stepN_branch_body_agreement_all`
    /// theorem (true ∧ false) kernel-checked with empty residue (Full mode
    /// only; requires both arms proven).
    pub stepbranch_body_composed: bool,
    /// stepN branch-WITH-BODY deliberately-wrong claims kernel-REJECTED this
    /// run (2 in Full mode: true-arm-computes-else-arithmetic +
    /// false-arm-computes-then-arithmetic; 1 in Spot). An accepted forgery
    /// is a hard failure.
    pub stepbranch_body_fail_closed_controls: usize,
    /// Un-bridged stepN branch-WITH-BODY residue, honestly reported as
    /// `"shape: reason"` (Switch, nested/chained CondBrs, loops, the
    /// integer-guard semCondBr arm, the interprocedural evaluator,
    /// multi-instruction arm bodies, asymmetric arm shapes, non-BinOp arm
    /// bodies).
    pub stepbranch_body_unbridged: Vec<String>,

    // -- steploop (the FIRST agreement over a GENUINE back-edge CFG, by --
    // -- fuel induction with a per-step lemma; scoped to a data-trivial --
    // -- Bool-flag loop — see steploop_unbridged for the data-computing --
    // -- case's newly-discovered blocker). --
    /// steploop arms whose theorem kernel-checked THIS RUN with empty axiom
    /// residue (2 = `true_diverges` (the per-step + induction) and
    /// `false_exits` (the base case); both run in every mode).
    pub steploop_bridged: usize,
    /// steploop arms attempted but NOT proven — never silently dropped.
    pub steploop_pinned: usize,
    /// `arm: failure head` for every pinned steploop arm (or the fixtures/
    /// composed/staleness-witness failure, prefixed accordingly).
    pub steploop_pinned_list: Vec<String>,
    /// The proven steploop arms: `["true_diverges", "false_exits"]` when
    /// both check.
    pub steploop_bridged_list: Vec<String>,
    /// Whether the COMPOSED `bridge_stepN_loop_agreement_all` conjunction
    /// (`true_diverges ∧ false_exits`) kernel-checked with empty residue
    /// (requires both arms proven).
    pub steploop_composed: bool,
    /// steploop deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode, 1 in Spot: true-guard-claimed-to-terminate,
    /// false-guard-claimed-sufficient-at-fuel-1). An accepted forgery is a
    /// hard failure.
    pub steploop_fail_closed_controls: usize,
    /// Whether the STALENESS-WITNESS theorem `countup_naive_never_terminates`
    /// kernel-checked (Full mode only) — a POSITIVE, kernel-proven finding
    /// that the naive data-computing `count_up` encoding through this
    /// evaluator runs forever instead of terminating, due to the
    /// `Sem.bindFresh`/`nextValueId` staleness obstruction this increment
    /// discovered (not a forgery probe: this theorem is EXPECTED to prove).
    pub steploop_staleness_witness: bool,
    /// Un-bridged steploop residue, honestly reported as `"shape: reason"`
    /// (data-computing loops — the newly-discovered blocker — the SSA↔slot
    /// projection, the `Trust.MirSem.step_cfg`/`exec_cfg` tie-in, irreducible/
    /// nested loops, the integer-guard semCondBr arm, the interprocedural
    /// evaluator).
    pub steploop_unbridged: Vec<String>,

    // -- DATALOOP (Full mode only): the FIRST agreement over a back-edge --
    // -- CFG whose body COMPUTES (a genuine data-carrying counter, not a --
    // -- Bool passthrough), through `stepNWithContext`/`bodyResultDests` --
    // -- (the interprocedural, context-honoring evaluator every prior --
    // -- extension left unbridged). Proven by a PER-VISIT CHAIN: 6 --
    // -- unconditional single-block-visit `rfl` lemmas composed via --
    // -- `Eq.trans`, never asking the kernel to reduce more than one --
    // -- block-visit per obligation (the technique that avoids the mapped --
    // -- `clean_kernel` defeq-performance wall). --
    /// Whether `bridge_dataloop_counter_reaches_2` (the composed per-visit
    /// chain: `i0=0, bound=2` reaches `i=2` in exactly 2 iterations) kernel-
    /// checked with empty axiom residue this run (Full mode only).
    pub dataloop_bridged: bool,
    /// The failure head of the DATALOOP fixtures/arm/composed theorem, if any
    /// step did not prove (never silently dropped). Empty when
    /// `dataloop_bridged` is true.
    pub dataloop_pinned_list: Vec<String>,
    /// DATALOOP deliberately-wrong claims kernel-REJECTED this run (2 in
    /// Full mode: `counter-reaches-1`, `counter-reaches-3` — both reuse the
    /// SAME proven per-visit prefix chain and are refuted only at the final,
    /// single-block-visit step, so refutation stays as cheap as the positive
    /// arm). An accepted forgery is a hard failure.
    pub dataloop_fail_closed_controls: usize,

    // -- M4 v0 — the general bounded-CFG induction FRAMEWORK --
    // -- (crates/trust-clean/src/cfg_family/, --
    // -- reports/m4-general-cfg-induction-framework-design-2026-07-07.md). --
    // -- ONE Vec entry per registered `CfgFamilySpec` --
    // -- (`cfg_family::GENERATED_FAMILIES`), replacing what a new hand- --
    // -- written family would otherwise cost: 7+ new `BridgeAgreement` --
    // -- fields and a ~85-line copy-pasted gate block. --
    /// Per-generated-family reports, in `GENERATED_FAMILIES` order. v0
    /// registers `gen_block_add` (ground) and `gen_block_add_sym` (symbolic
    /// — the mechanical regeneration of the hand-written stepblock arm
    /// above, `STEPBLOCK_ARMS`).
    pub generated_families: Vec<crate::cfg_family::gate::GeneratedFamilyReport>,
}

// ---------------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------------

/// Import the actual manifest-verified package pair. Production and focused
/// input-boundary tests share this exact consumer; no theorem/proof is minted.
fn load_verified_modules(
    env: &mut Environment,
    roots: &[String],
    trustir_tree: &VerifiedTree,
    core_tree: &VerifiedTree,
) -> Result<Vec<clean_olean::LoadSummary>, BridgeGateError> {
    manifest_inputs::load(env, roots, trustir_tree, core_tree)
}

/// Run the Lean↔Clean bridge gate over the VENDORED artifacts. Fail-closed:
fn bind_source_reuse(
    selected: trust_bridge_closure::source_reuse::Selection,
    trustir_tree: &VerifiedTree,
    core_tree: &VerifiedTree,
) -> Result<trust_bridge_closure::source_reuse::Selection, BridgeGateError> {
    if selected.trustir_manifest_sha256 != trustir_tree.manifest_sha256
        || selected.core_manifest_sha256 != core_tree.manifest_sha256
    {
        return Err(BridgeGateError::PinUnresolvable {
            detail: "source reuse manifests differ from the exact runtime captures".to_owned(),
        });
    }
    Ok(selected)
}

/// any tampered/missing/stale artifact, import failure, recheck failure,
/// axiom residue, or accepted forgery returns `Err`. Arms that fail to prove
/// are returned honestly in the summary (`ops_pinned`), never silently.
pub fn run_bridge_gate(config: &BridgeGateConfig) -> Result<BridgeAgreement, BridgeGateError> {
    let t0 = Instant::now();

    // -- 1. Manifests: schema + provenance + per-file sha256 (fail-closed). --
    bridge_gate_step(|| "verify the vendored TrustIr olean manifest".to_owned());
    let trustir_tree = verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)?;
    bridge_gate_step(|| "verify the vendored Lean-core olean manifest".to_owned());
    let core_tree = verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)?;
    let manifest_commit = trustir_tree.trustir_commit.clone().unwrap_or_default();

    // -- 2. Pin drift: manifest commit must equal the checked-out submodule. --
    bridge_gate_step(|| "resolve the checked-out trust-ir pin".to_owned());
    let mut source_reuse_anchor = None;
    let checkout_commit = if trustir_tree.source_reuse {
        if config.expected_trustir_commit.is_some() {
            return Err(BridgeGateError::PinUnresolvable {
                detail: "source reuse requires actual source repositories, not an expected-pin override".to_owned(),
            });
        }
        let root = std::fs::canonicalize(&config.repo_root).map_err(|e| BridgeGateError::PinUnresolvable { detail: e.to_string() })?;
        if std::fs::canonicalize(&config.trustir_olean_dir).ok()
            != Some(root.join("crates/trust-clean/fixtures/trustir-oleans"))
            || std::fs::canonicalize(&config.lean_core_olean_dir).ok()
                != Some(root.join("vendor/lean-core-oleans"))
        {
            return Err(BridgeGateError::PinUnresolvable { detail: "source reuse requires the actual source-bound artifact locations".to_owned() });
        }
        let selected = trust_bridge_closure::source_reuse::verify(
            &root, trust_bridge_closure::source_reuse::Subject::Checkout,
        ).map_err(|e| BridgeGateError::PinUnresolvable { detail: format!("source reuse refused: {e}") })?
            .ok_or_else(|| BridgeGateError::PinUnresolvable { detail: "source reuse record disappeared".to_owned() })?;
        let selected = bind_source_reuse(selected, &trustir_tree, &core_tree)?;
        source_reuse_anchor = Some(selected.anchor_commit);
        selected.trustir_commit
    } else { match &config.expected_trustir_commit {
        Some(c) => c.clone(),
        None => {
            let c = resolve_trustir_checkout(&config.repo_root)?;
            check_lean_sources_clean(&config.repo_root)?;
            c
        }
    }};
    if source_reuse_anchor.is_none() && manifest_commit != checkout_commit {
        return Err(BridgeGateError::PinDrift { manifest_commit, checkout_commit });
    }
    // An expected-pin override supplies no source authority for runtime data.
    // Such a diagnostic reports the frontier as unreported, never certified.
    let runtime_frontier = if config.expected_trustir_commit.is_none() {
        RuntimeFrontier::read(&config.repo_root.join("first-party/trust-ir"), &checkout_commit)
            .map_err(|detail| BridgeGateError::RuntimeBoundary { detail })?
    } else {
        None
    };

    // -- 3. Machine-import the vendored closure (the UNION of both roots). --
    bridge_gate_step(|| "import the vendored olean closure".to_owned());
    let mut env = Environment::default();
    env.ensure_native_reducers();
    let root_modules: Vec<String> = BRIDGE_ROOT_MODULES.iter().map(|s| (*s).to_string()).collect();
    let summaries = load_verified_modules(&mut env, &root_modules, &trustir_tree, &core_tree)?;

    // Import hygiene: the loaded module set must EQUAL the manifested set.
    let mut trustir_names: BTreeSet<String> = BTreeSet::new();
    let mut trustir_modules: BTreeSet<String> = BTreeSet::new();
    let mut loaded_rels: BTreeSet<(bool, String)> = BTreeSet::new();
    let mut constants_loaded = 0usize;
    for s in &summaries {
        constants_loaded += s.added_constants;
        let Some(module) = s.module_name.as_deref() else { continue };
        let rel = format!("{}.olean", module.replace('.', "/"));
        let is_trustir = module.starts_with("TrustIr");
        let manifested = if is_trustir {
            trustir_tree.files.contains(&rel)
        } else {
            core_tree.files.contains(&rel)
        };
        if !manifested {
            return Err(BridgeGateError::UnmanifestedModule { module: module.to_string(), rel });
        }
        loaded_rels.insert((is_trustir, rel));
        if is_trustir {
            trustir_modules.insert(module.to_owned());
            for n in &s.added_names {
                trustir_names.insert(n.to_string());
            }
        }
    }
    for rel in &trustir_tree.files {
        if !loaded_rels.contains(&(true, rel.clone())) {
            return Err(BridgeGateError::UnloadedManifestEntry {
                rel: rel.clone(),
                root: BRIDGE_ROOT_MODULES.join(", "),
            });
        }
    }
    for rel in &core_tree.files {
        if !loaded_rels.contains(&(false, rel.clone())) {
            return Err(BridgeGateError::UnloadedManifestEntry {
                rel: rel.clone(),
                root: BRIDGE_ROOT_MODULES.join(", "),
            });
        }
    }

    // -- 4. Bridge inputs present + local checks under the imported TCB. --
    // The proofs below intentionally continue in this imported environment.
    // Replacing only this counter with fresh replay would NOT change their
    // basis: a future closed-replay mode must use the newly checked environment
    // for every downstream proof and retain its complete dependency inventory.
    for c in BRIDGE_INPUTS {
        let present = Name::from_str(c).ok().and_then(|n| env.get_const(&n).map(|_| ())).is_some();
        if !present {
            return Err(BridgeGateError::InputMissing { name: (*c).to_string() });
        }
    }
    let recheck_targets: BTreeSet<String> = match config.mode {
        BridgeGateMode::Full => trustir_names.clone(),
        BridgeGateMode::Spot => BRIDGE_INPUTS.iter().map(|s| (*s).to_string()).collect(),
    };
    // The third argument is `max_heartbeats`, and `0` there means UNLIMITED:
    // this re-check was the one gate path with no per-constant bound AND no
    // ambient declaration budget (the budget covers `load_bridge_source`, not
    // this batch). `typecheck_constants_full` resets the heartbeat per
    // constant (clean-olean `local_check_roster`), so the kernel's own
    // default is a per-constant bound here, not a whole-batch one, and the
    // gate's constants check well inside it — no verdict moves.
    bridge_gate_step(|| match config.mode {
        BridgeGateMode::Full => format!("replay census of {} imported TrustIr declarations", recheck_targets.len()),
        BridgeGateMode::Spot => format!("strict kernel recheck of {} imported TrustIr constants", recheck_targets.len()),
    });
    let (recheck_pass, recheck_fail, recheck_seen, runtime_refused, first) = match config.mode {
        BridgeGateMode::Full => {
            // Every original/requested name stays in the SAME replay graph.
            // Only artifact-backed unsafe/partial rows with an exact typed
            // NotReplayable refusal are non-authoritative runtime outcomes.
            // Safe stubs, missing rows and refused dependencies remain fatal.
            let census = replay_declaration_census(
                &env, &summaries, &trustir_modules, &recheck_targets,
                clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT,
            );
            let first = census.verdicts().iter().find_map(|(name, verdict)| match verdict {
                DeclarationReplayVerdict::Failed(reason) => Some(format!("{name}: {reason:?}")),
                _ => None,
            }).or_else(|| census.accounting_errors().first().map(|error| format!("{error:?}")))
                .unwrap_or_default();
            (census.admitted(), census.failures(), census.seen(), census.not_replayable(), first)
        }
        BridgeGateMode::Spot => {
            // Spot remains a strict check of the requested mathematical inputs;
            // it cannot classify a partial population as a complete census.
            let (pass, fail, errors) = typecheck_constants_full(
                &env, &recheck_targets, clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT,
            );
            let first = errors.iter().next().map(|(name, error)| format!("{name}: {error}"))
                .unwrap_or_default();
            (pass, fail, pass + fail, 0, first)
        }
    };
    if recheck_fail != 0 {
        return Err(BridgeGateError::RecheckFailed {
            fail: recheck_fail,
            total: recheck_seen,
            first: first.chars().take(200).collect(),
        });
    }

    // Trust: checked, bridge-owned aliases supply the exact imported notation
    // instances. This does not infer any missing v1 extension entries.
    let instance_names = load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).map_err(|detail| {
        BridgeGateError::PreludeFailed { detail: format!("bridge notation instances: {detail}") }
    })?;
    for name in &instance_names {
        require_empty_axiom_deps(&env, name)?;
    }

    // -- 5. Wrap-elision prelude (the gate's own machinery: hard failure). --
    let prelude_names = load_bridge_source(&mut env, PRELUDE_SRC)
        .map_err(|detail| BridgeGateError::PreludeFailed { detail })?;
    for n in &prelude_names {
        require_empty_axiom_deps(&env, n)?;
    }

    // -- 6. Reduction lemmas (rfl over the imported constant). --
    let reductions: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => REDUCTION_SRCS,
        BridgeGateMode::Spot => &REDUCTION_SRCS[..1], // add_reduces only
    };
    let mut reduction_lemmas = 0usize;
    let mut pinned: Vec<String> = Vec::new();
    for (name, src) in reductions {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, name)?;
                reduction_lemmas += 1;
            }
            Err(e) => pinned
                .push(format!("reduction {name}: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 7. The agreement arms. Failure to prove is PINNED, not fatal. --
    let arm_set: Vec<&ArmSpec> = match config.mode {
        BridgeGateMode::Full => ARMS.iter().collect(),
        BridgeGateMode::Spot => {
            ARMS.iter().filter(|a| matches!(a.op, "Add" | "FAdd" | "UDiv")).collect()
        }
    };
    let mut bridged: Vec<String> = Vec::new();
    let mut proved_theorems: BTreeSet<&str> = BTreeSet::new();
    let (mut form_a, mut form_b, mut form_b_guarded) = (0usize, 0usize, 0usize);
    for arm in &arm_set {
        match load_bridge_source(&mut env, arm.src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.theorem)?;
                bridged.push(format!("{}[{}]", arm.op, arm.form.label()));
                proved_theorems.insert(arm.theorem);
                match arm.form {
                    ArmForm::A => form_a += 1,
                    ArmForm::B => form_b += 1,
                    ArmForm::BGuarded => {
                        form_b += 1;
                        form_b_guarded += 1;
                    }
                }
            }
            Err(e) => {
                pinned.push(format!("{}: {}", arm.op, e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 8. Characterization rows (Full mode): pin every arm's behavior. --
    let mut characterization_rows = 0usize;
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, CHARACTERIZATION_SRC) {
            Ok(names) => {
                for n in &names {
                    require_empty_axiom_deps(&env, n)?;
                }
                characterization_rows = names.len();
            }
            Err(e) => pinned
                .push(format!("characterization: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 9. The composed all-18 conjunction (Full mode, all arms proven). --
    let mut composed_all18 = false;
    if config.mode == BridgeGateMode::Full && proved_theorems.len() == ARMS.len() {
        match load_bridge_source(&mut env, COMPOSED_ALL18_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, COMPOSED_ALL18_NAME)?;
                composed_all18 = true;
            }
            Err(e) => {
                pinned.push(format!("composed all-18: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 10. Forgery probes: wrong claims MUST be rejected. --
    let probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => FORGERY_PROBES,
        BridgeGateMode::Spot => &FORGERY_PROBES[..1],
    };
    let mut fail_closed_controls = 0usize;
    for (label, src) in probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => fail_closed_controls += 1,
        }
    }

    // -- 11. UnOp reduction lemmas (rfl over the imported constant). --
    let mut unop_pinned: Vec<String> = Vec::new();
    let unop_reductions: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => UNOP_REDUCTION_SRCS,
        BridgeGateMode::Spot => &UNOP_REDUCTION_SRCS[..1], // neg_reduces only
    };
    for (name, src) in unop_reductions {
        match load_bridge_source(&mut env, src) {
            Ok(_) => require_empty_axiom_deps(&env, name)?,
            Err(e) => unop_pinned
                .push(format!("reduction {name}: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 12. The UnOp agreement arms. Failure to prove is PINNED, not fatal. --
    let unop_arm_set: Vec<&UnOpArmSpec> = match config.mode {
        BridgeGateMode::Full => UNOP_ARMS.iter().collect(),
        BridgeGateMode::Spot => UNOP_ARMS.iter().filter(|a| a.op == "Neg").collect(),
    };
    let mut unop_bridged: Vec<String> = Vec::new();
    let mut unop_proved: BTreeSet<&str> = BTreeSet::new();
    let (mut unop_form_a, mut unop_form_b) = (0usize, 0usize);
    for arm in &unop_arm_set {
        match load_bridge_source(&mut env, arm.src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.theorem)?;
                unop_bridged.push(format!("{}[{}]", arm.op, arm.form.label()));
                unop_proved.insert(arm.theorem);
                match arm.form {
                    ArmForm::A => unop_form_a += 1,
                    ArmForm::B | ArmForm::BGuarded => unop_form_b += 1,
                }
            }
            Err(e) => {
                unop_pinned.push(format!("{}: {}", arm.op, e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 13. Neg's connecting corollary: the EXACT term clean_ground's --
    // -- F::Neg emits (`Int.sub (Int.ofNat 0) operand`), via Int.zero_sub. --
    let mut unop_neg_sub_zero_form = false;
    if unop_proved.contains("bridge_neg") {
        match load_bridge_source(&mut env, NEG_SUB_ZERO_FORM_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, NEG_SUB_ZERO_FORM_NAME)?;
                unop_neg_sub_zero_form = true;
            }
            Err(e) => unop_pinned.push(format!(
                "{NEG_SUB_ZERO_FORM_NAME}: {}",
                e.chars().take(200).collect::<String>()
            )),
        }
    }

    // -- 14. UnOp concrete-value pin rows (Full mode). --
    let mut unop_conc_rows = 0usize;
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, UNOP_CONC_SRC) {
            Ok(names) => {
                for n in &names {
                    require_empty_axiom_deps(&env, n)?;
                }
                unop_conc_rows = names.len();
            }
            Err(e) => {
                unop_pinned.push(format!("conc rows: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 15. The composed UnOp conjunction (Full mode, all 3 arms proven). --
    let mut unop_composed = false;
    if config.mode == BridgeGateMode::Full && unop_proved.len() == UNOP_ARMS.len() {
        match load_bridge_source(&mut env, UNOP_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, UNOP_COMPOSED_NAME)?;
                unop_composed = true;
            }
            Err(e) => {
                unop_pinned.push(format!("composed: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 16. UnOp forgery probes: wrong claims MUST be rejected. --
    let unop_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => UNOP_FORGERY_PROBES,
        BridgeGateMode::Spot => &UNOP_FORGERY_PROBES[..1],
    };
    let mut unop_fail_closed_controls = 0usize;
    for (label, src) in unop_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => unop_fail_closed_controls += 1,
        }
    }
    let unop_unbridged: Vec<String> =
        UNOP_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // One actual implementation for Full/Spot and the focused overflow test.
    let unsigned_mul::OverflowEvidence {
        overflow_value_bridged,
        overflow_value_pinned,
        overflow_value_pinned_list,
        overflow_value_bridged_list,
        overflow_flag_bridged,
        overflow_flag_pinned,
        overflow_flag_pinned_list,
        overflow_flag_bridged_list,
        overflow_flag_guarded,
        overflow_composed,
        overflow_fail_closed_controls,
        overflow_flag_unbridged,
        overflow_umul_predicates_bound,
        overflow_umul_predicate_bridged,
        overflow_umul_predicate_pinned,
        overflow_umul_foundational_axioms,
        overflow_foundational_axioms,
    } = unsigned_mul::check_overflow_layer(&mut env, config.mode)?;

    // -- 22. The ICmp agreement arms. Failure to prove is PINNED, not fatal. --
    let icmp_arm_set: Vec<&IcmpArmSpec> = match config.mode {
        BridgeGateMode::Full => ICMP_ARMS.iter().collect(),
        // Spot: one arm per kind family — Ult[u], Eq[eq], Slt[s].
        BridgeGateMode::Spot => {
            ICMP_ARMS.iter().filter(|a| matches!(a.op, "Ult" | "Eq" | "Slt")).collect()
        }
    };
    let mut icmp_bridged: Vec<String> = Vec::new();
    let mut icmp_pinned: Vec<String> = Vec::new();
    let mut icmp_proved: BTreeSet<&str> = BTreeSet::new();
    let (mut icmp_kind_unsigned, mut icmp_kind_sign_independent, mut icmp_kind_signed) =
        (0usize, 0usize, 0usize);
    for arm in &icmp_arm_set {
        match load_bridge_source(&mut env, arm.src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.theorem)?;
                icmp_bridged.push(format!("{}[{}]", arm.op, arm.kind.label()));
                icmp_proved.insert(arm.theorem);
                match arm.kind {
                    IcmpArmKind::Unsigned => icmp_kind_unsigned += 1,
                    IcmpArmKind::SignIndependent => icmp_kind_sign_independent += 1,
                    IcmpArmKind::Signed => icmp_kind_signed += 1,
                }
            }
            Err(e) => {
                icmp_pinned.push(format!("{}: {}", arm.op, e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 23. ICmp concrete-value pin rows (Full mode). --
    let mut icmp_conc_rows = 0usize;
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, ICMP_CONC_SRC) {
            Ok(names) => {
                for n in &names {
                    require_empty_axiom_deps(&env, n)?;
                }
                icmp_conc_rows = names.len();
            }
            Err(e) => {
                icmp_pinned.push(format!("conc rows: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 24. The composed ICmp conjunction (Full mode, all 10 arms proven). --
    let mut icmp_composed = false;
    if config.mode == BridgeGateMode::Full && icmp_proved.len() == ICMP_ARMS.len() {
        match load_bridge_source(&mut env, ICMP_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, ICMP_COMPOSED_NAME)?;
                icmp_composed = true;
            }
            Err(e) => {
                icmp_pinned.push(format!("composed: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 25. ICmp forgery probes: wrong claims MUST be rejected. --
    let icmp_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => ICMP_FORGERY_PROBES,
        BridgeGateMode::Spot => &ICMP_FORGERY_PROBES[..1],
    };
    let mut icmp_fail_closed_controls = 0usize;
    for (label, src) in icmp_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => icmp_fail_closed_controls += 1,
        }
    }
    let icmp_unbridged: Vec<String> =
        ICMP_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- 26. The Cast agreement arms. Failure to prove is PINNED, not fatal. --
    let cast_arm_set: Vec<&CastArmSpec> = match config.mode {
        BridgeGateMode::Full => CAST_ARMS.iter().collect(),
        // Spot: one arm only — Trunc.
        BridgeGateMode::Spot => CAST_ARMS.iter().filter(|a| a.op == "Trunc").collect(),
    };
    let mut cast_bridged: Vec<String> = Vec::new();
    let mut cast_pinned: Vec<String> = Vec::new();
    let mut cast_proved: BTreeSet<&str> = BTreeSet::new();
    for arm in &cast_arm_set {
        match load_bridge_source(&mut env, arm.src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.theorem)?;
                cast_bridged.push(arm.op.to_string());
                cast_proved.insert(arm.theorem);
            }
            Err(e) => {
                cast_pinned.push(format!("{}: {}", arm.op, e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 27. Cast concrete-value anchor rows (Full mode). --
    let mut cast_conc_rows = 0usize;
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, CAST_CONC_SRC) {
            Ok(names) => {
                for n in &names {
                    require_empty_axiom_deps(&env, n)?;
                }
                cast_conc_rows = names.len();
            }
            Err(e) => {
                cast_pinned.push(format!("conc rows: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 28. TIER 2: the Cast widening-identity connecting corollaries --
    // -- (Full mode; pure Int arithmetic, no monad involved). --
    let mut cast_widening_list: Vec<String> = Vec::new();
    let mut cast_signcross_list: Vec<String> = Vec::new();
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, CAST_ZEXT_WIDENING_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, CAST_ZEXT_WIDENING_NAME)?;
                cast_widening_list.push(CAST_ZEXT_WIDENING_NAME.to_string());
            }
            Err(e) => cast_pinned.push(format!(
                "{CAST_ZEXT_WIDENING_NAME}: {}",
                e.chars().take(200).collect::<String>()
            )),
        }
        // GAP-CROSS-SIGN-WIDEN (2026-07-16): the sign-crossing widening-identity
        // connecting corollary (`u_w -> i_W`, `W > w`, is value-preserving),
        // kernel-anchoring the new mirsem/prove cast clause against the vendored
        // `semCast`/`toSigned`/`truncateUnsigned` semantics. Unlike the SExt
        // corollary this delivers cleanly (no `0 < 2^n`-for-symbolic-`n` detour).
        match load_bridge_source(&mut env, CAST_ZEXT_SIGNCROSS_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, CAST_ZEXT_SIGNCROSS_NAME)?;
                cast_signcross_list.push(CAST_ZEXT_SIGNCROSS_NAME.to_string());
            }
            Err(e) => cast_pinned.push(format!(
                "{CAST_ZEXT_SIGNCROSS_NAME}: {}",
                e.chars().take(200).collect::<String>()
            )),
        }
        // The analogous SExt widening corollary is NOT attempted here: it is
        // mathematically real (proven against a genuine Lean 4.8.0 toolchain)
        // but hits a confirmed clean-elaborator limitation — see the doc
        // comment above `CAST_COMPOSED_SRC`. Reported honestly, not faked.
    }

    // -- 29. The composed Cast conjunction (Full mode, all 3 arms + the --
    // -- one widening corollary proven). --
    let mut cast_composed = false;
    if config.mode == BridgeGateMode::Full
        && cast_proved.len() == CAST_ARMS.len()
        && cast_widening_list.len() == 1
    {
        match load_bridge_source(&mut env, CAST_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, CAST_COMPOSED_NAME)?;
                cast_composed = true;
            }
            Err(e) => {
                cast_pinned.push(format!("composed: {}", e.chars().take(200).collect::<String>()))
            }
        }
    }

    // -- 30. Cast forgery probes: wrong claims MUST be rejected. --
    let cast_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => CAST_FORGERY_PROBES,
        BridgeGateMode::Spot => &CAST_FORGERY_PROBES[..1],
    };
    let mut cast_fail_closed_controls = 0usize;
    for (label, src) in cast_probes {
        check_semantic_forgery_with_budget(&mut env, label, src, BRIDGE_DECL_BUDGET)?;
        cast_fail_closed_controls += 1;
    }
    let cast_unbridged: Vec<String> =
        CAST_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- 31. The stepInst-BinOp chain+connect arms (the FIRST statement/ --
    // -- instruction-level extension). Each arm is TWO theorems: the --
    // -- shared state transport then the connect (reuses the matching --
    // -- already-proven value theorem from ARMS). Failure --
    // -- to prove either half is PINNED, not fatal. --
    let transport_names = load_bridge_source(&mut env, STEPINST_BINOP_TRANSPORT_SRC)
        .map_err(|detail| BridgeGateError::PreludeFailed { detail })?;
    for name in transport_names {
        require_empty_axiom_deps(&env, &name)?;
    }
    let stepinst_binop_arm_set: Vec<&StepBinOpArmSpec> = match config.mode {
        BridgeGateMode::Full => STEPINST_BINOP_ARMS.iter().collect(),
        BridgeGateMode::Spot => STEPINST_BINOP_ARMS.iter().filter(|a| a.op == "Add").collect(),
    };
    let mut stepinst_binop_bridged_list: Vec<String> = Vec::new();
    let mut stepinst_binop_pinned_list: Vec<String> = Vec::new();
    let mut stepinst_binop_proved: BTreeSet<&str> = BTreeSet::new();
    for arm in &stepinst_binop_arm_set {
        let chain_ok = match load_bridge_source(&mut env, arm.chain_src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.chain_theorem)?;
                true
            }
            Err(e) => {
                stepinst_binop_pinned_list.push(format!(
                    "{}: chain: {}",
                    arm.op,
                    e.chars().take(200).collect::<String>()
                ));
                false
            }
        };
        if chain_ok {
            match load_bridge_source(&mut env, arm.connect_src) {
                Ok(_) => {
                    require_empty_axiom_deps(&env, arm.connect_theorem)?;
                    stepinst_binop_bridged_list.push(arm.op.to_string());
                    stepinst_binop_proved.insert(arm.connect_theorem);
                }
                Err(e) => stepinst_binop_pinned_list.push(format!(
                    "{}: connect: {}",
                    arm.op,
                    e.chars().take(200).collect::<String>()
                )),
            }
        }
    }

    // -- 32. The composed stepInst-BinOp conjunction (Full mode, all 7 --
    // -- arms proven). --
    let mut stepinst_binop_composed = false;
    if config.mode == BridgeGateMode::Full
        && stepinst_binop_proved.len() == STEPINST_BINOP_ARMS.len()
    {
        match load_bridge_source(&mut env, STEPINST_BINOP_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_BINOP_COMPOSED_NAME)?;
                stepinst_binop_composed = true;
            }
            Err(e) => stepinst_binop_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 33. stepInst-BinOp forgery probes: wrong claims MUST be rejected. --
    let stepinst_binop_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPINST_BINOP_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPINST_BINOP_FORGERY_PROBES[..1],
    };
    let mut stepinst_binop_fail_closed_controls = 0usize;
    for (label, src) in stepinst_binop_probes {
        check_semantic_forgery_with_budget(&mut env, label, src, BRIDGE_DECL_BUDGET)?;
        stepinst_binop_fail_closed_controls += 1;
    }
    let stepinst_binop_unbridged: Vec<String> =
        STEPINST_BINOP_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();
    let stepinst_categories_unbridged: Vec<String> = STEPINST_CATEGORIES_UNBRIDGED
        .iter()
        .map(|(op, reason)| format!("{op}: {reason}"))
        .collect();

    // -- stepInst .UnOp (EXTENSION 9): the chain+connect arm (Neg) + its --
    // -- bonus sub-zero-form corollary. Runs in both Full and Spot mode --
    // -- (there is only one arm). --
    let mut stepinst_unop_bridged_list: Vec<String> = Vec::new();
    let mut stepinst_unop_pinned_list: Vec<String> = Vec::new();
    let mut stepinst_unop_proved: BTreeSet<&str> = BTreeSet::new();
    for arm in STEPINST_UNOP_ARMS {
        let chain_ok = match load_bridge_source(&mut env, arm.chain_src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.chain_theorem)?;
                true
            }
            Err(e) => {
                stepinst_unop_pinned_list.push(format!(
                    "{}: chain: {}",
                    arm.op,
                    e.chars().take(200).collect::<String>()
                ));
                false
            }
        };
        if chain_ok {
            match load_bridge_source(&mut env, arm.connect_src) {
                Ok(_) => {
                    require_empty_axiom_deps(&env, arm.connect_theorem)?;
                    stepinst_unop_bridged_list.push(arm.op.to_string());
                    stepinst_unop_proved.insert(arm.connect_theorem);
                }
                Err(e) => stepinst_unop_pinned_list.push(format!(
                    "{}: connect: {}",
                    arm.op,
                    e.chars().take(200).collect::<String>()
                )),
            }
        }
    }
    let mut stepinst_unop_neg_sub_zero_form = false;
    if stepinst_unop_proved.contains("bridge_stepInst_unop_neg") {
        match load_bridge_source(&mut env, STEPINST_UNOP_NEG_SUBZERO_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_UNOP_NEG_SUBZERO_NAME)?;
                stepinst_unop_neg_sub_zero_form = true;
            }
            Err(e) => stepinst_unop_pinned_list.push(format!(
                "{STEPINST_UNOP_NEG_SUBZERO_NAME}: {}",
                e.chars().take(200).collect::<String>()
            )),
        }
    }
    let mut stepinst_unop_composed = false;
    if stepinst_unop_proved.contains("bridge_stepInst_unop_neg") && stepinst_unop_neg_sub_zero_form
    {
        match load_bridge_source(&mut env, STEPINST_UNOP_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_UNOP_COMPOSED_NAME)?;
                stepinst_unop_composed = true;
            }
            Err(e) => stepinst_unop_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }
    let stepinst_unop_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPINST_UNOP_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPINST_UNOP_FORGERY_PROBES[..1],
    };
    let mut stepinst_unop_fail_closed_controls = 0usize;
    for (label, src) in stepinst_unop_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => stepinst_unop_fail_closed_controls += 1,
        }
    }
    let stepinst_unop_unbridged: Vec<String> =
        STEPINST_UNOP_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- stepInst .Overflow (EXTENSION 9): the chain+connect arm (unsigned --
    // -- AddOverflow) — fully unconditional (bridge_overflow_uadd_flag has --
    // -- no side condition). Runs in both Full and Spot mode. --
    let mut stepinst_overflow_bridged_list: Vec<String> = Vec::new();
    let mut stepinst_overflow_pinned_list: Vec<String> = Vec::new();
    let mut stepinst_overflow_proved = false;
    let overflow_chain_ok = match load_bridge_source(&mut env, STEPINST_OVERFLOW_CHAIN_SRC) {
        Ok(_) => {
            require_empty_axiom_deps(&env, STEPINST_OVERFLOW_CHAIN_THEOREM)?;
            true
        }
        Err(e) => {
            stepinst_overflow_pinned_list.push(format!(
                "AddOverflow[u]: chain: {}",
                e.chars().take(200).collect::<String>()
            ));
            false
        }
    };
    if overflow_chain_ok {
        match load_bridge_source(&mut env, STEPINST_OVERFLOW_CONNECT_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_OVERFLOW_CONNECT_THEOREM)?;
                stepinst_overflow_bridged_list.push("AddOverflow[u]".to_string());
                stepinst_overflow_proved = true;
            }
            Err(e) => stepinst_overflow_pinned_list.push(format!(
                "AddOverflow[u]: connect: {}",
                e.chars().take(200).collect::<String>()
            )),
        }
    }
    let mut stepinst_overflow_composed = false;
    if stepinst_overflow_proved {
        match load_bridge_source(&mut env, STEPINST_OVERFLOW_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_OVERFLOW_COMPOSED_NAME)?;
                stepinst_overflow_composed = true;
            }
            Err(e) => stepinst_overflow_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }
    let stepinst_overflow_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPINST_OVERFLOW_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPINST_OVERFLOW_FORGERY_PROBES[..1],
    };
    let mut stepinst_overflow_fail_closed_controls = 0usize;
    for (label, src) in stepinst_overflow_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => stepinst_overflow_fail_closed_controls += 1,
        }
    }
    let stepinst_overflow_unbridged: Vec<String> =
        STEPINST_OVERFLOW_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- stepInst .ICmp (EXTENSION 9): the chain+connect arm (Ult) — --
    // -- semICmp is TOTAL, so the connect is a direct congrArg over Bool. --
    // -- Runs in both Full and Spot mode. --
    let mut stepinst_icmp_bridged_list: Vec<String> = Vec::new();
    let mut stepinst_icmp_pinned_list: Vec<String> = Vec::new();
    let mut stepinst_icmp_proved = false;
    let icmp_chain_ok = match load_bridge_source(&mut env, STEPINST_ICMP_CHAIN_SRC) {
        Ok(_) => {
            require_empty_axiom_deps(&env, STEPINST_ICMP_CHAIN_THEOREM)?;
            true
        }
        Err(e) => {
            stepinst_icmp_pinned_list
                .push(format!("Ult: chain: {}", e.chars().take(200).collect::<String>()));
            false
        }
    };
    if icmp_chain_ok {
        match load_bridge_source(&mut env, STEPINST_ICMP_CONNECT_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_ICMP_CONNECT_THEOREM)?;
                stepinst_icmp_bridged_list.push("Ult".to_string());
                stepinst_icmp_proved = true;
            }
            Err(e) => stepinst_icmp_pinned_list
                .push(format!("Ult: connect: {}", e.chars().take(200).collect::<String>())),
        }
    }
    let mut stepinst_icmp_composed = false;
    if stepinst_icmp_proved {
        match load_bridge_source(&mut env, STEPINST_ICMP_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_ICMP_COMPOSED_NAME)?;
                stepinst_icmp_composed = true;
            }
            Err(e) => stepinst_icmp_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }
    let stepinst_icmp_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPINST_ICMP_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPINST_ICMP_FORGERY_PROBES[..1],
    };
    let mut stepinst_icmp_fail_closed_controls = 0usize;
    for (label, src) in stepinst_icmp_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => stepinst_icmp_fail_closed_controls += 1,
        }
    }
    let stepinst_icmp_unbridged: Vec<String> =
        STEPINST_ICMP_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- stepInst .Cast (EXTENSION 9): the chain+connect arm (Trunc) — --
    // -- stepInst's .Cast arm calls semCast DIRECTLY, so the chain collapses --
    // -- two monadic layers in one Sem.run_bind/Sem.run_pure reduction. --
    // -- Runs in both Full and Spot mode. --
    let mut stepinst_cast_bridged_list: Vec<String> = Vec::new();
    let mut stepinst_cast_pinned_list: Vec<String> = Vec::new();
    let mut stepinst_cast_proved = false;
    let cast_chain_ok = match load_bridge_source(&mut env, STEPINST_CAST_CHAIN_SRC) {
        Ok(_) => {
            require_empty_axiom_deps(&env, STEPINST_CAST_CHAIN_THEOREM)?;
            true
        }
        Err(e) => {
            stepinst_cast_pinned_list
                .push(format!("Trunc: chain: {}", e.chars().take(200).collect::<String>()));
            false
        }
    };
    if cast_chain_ok {
        match load_bridge_source(&mut env, STEPINST_CAST_CONNECT_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_CAST_CONNECT_THEOREM)?;
                stepinst_cast_bridged_list.push("Trunc".to_string());
                stepinst_cast_proved = true;
            }
            Err(e) => stepinst_cast_pinned_list
                .push(format!("Trunc: connect: {}", e.chars().take(200).collect::<String>())),
        }
    }
    let mut stepinst_cast_composed = false;
    if stepinst_cast_proved {
        match load_bridge_source(&mut env, STEPINST_CAST_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_CAST_COMPOSED_NAME)?;
                stepinst_cast_composed = true;
            }
            Err(e) => stepinst_cast_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }
    let stepinst_cast_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPINST_CAST_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPINST_CAST_FORGERY_PROBES[..1],
    };
    let mut stepinst_cast_fail_closed_controls = 0usize;
    for (label, src) in stepinst_cast_probes {
        check_semantic_forgery_with_budget(&mut env, label, src, BRIDGE_DECL_BUDGET)?;
        stepinst_cast_fail_closed_controls += 1;
    }
    let stepinst_cast_unbridged: Vec<String> =
        STEPINST_CAST_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- The OVERALL umbrella conjoining all 4 categories (EXTENSION 9): --
    // -- Neg ∧ unsigned-AddOverflow ∧ Ult ∧ Trunc. Requires all 4 primary --
    // -- connect theorems proven; any failure is pinned onto the Cast list --
    // -- (never silently dropped). --
    let mut stepinst_categories_composed = false;
    if stepinst_unop_proved.contains("bridge_stepInst_unop_neg")
        && stepinst_overflow_proved
        && stepinst_icmp_proved
        && stepinst_cast_proved
    {
        match load_bridge_source(&mut env, STEPINST_CATEGORIES_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPINST_CATEGORIES_COMPOSED_NAME)?;
                stepinst_categories_composed = true;
            }
            Err(e) => stepinst_cast_pinned_list
                .push(format!("categories-composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 34. The stepblock (stepN/stepBlock, whole-BLOCK) outer-chain+ --
    // -- connect arm(s) — the FIRST agreement above the single-instruction --
    // -- level. The fixture defs are loaded once; each arm's connect_src --
    // -- reuses the ALREADY-LOADED `bridge_stepInst_binop_<op>` (step 31 --
    // -- above) as a black-box term. Failure to prove any half is PINNED, --
    // -- not fatal. Runs in BOTH Full and Spot mode (there is only one arm, --
    // -- Add, so there is no mode-based filtering to do). --
    let mut stepblock_bridged_list: Vec<String> = Vec::new();
    let mut stepblock_pinned_list: Vec<String> = Vec::new();
    let mut stepblock_proved: BTreeSet<&str> = BTreeSet::new();
    match load_bridge_source(&mut env, STEPBLOCK_FIXTURES_SRC) {
        Ok(_) => {
            for arm in STEPBLOCK_ARMS {
                let chain_ok = match load_bridge_source(&mut env, arm.outer_chain_src) {
                    Ok(_) => {
                        require_empty_axiom_deps(&env, arm.outer_chain_theorem)?;
                        true
                    }
                    Err(e) => {
                        stepblock_pinned_list.push(format!(
                            "{}: outer_chain: {}",
                            arm.op,
                            e.chars().take(200).collect::<String>()
                        ));
                        false
                    }
                };
                if chain_ok {
                    match load_bridge_source(&mut env, arm.connect_src) {
                        Ok(_) => {
                            require_empty_axiom_deps(&env, arm.connect_theorem)?;
                            stepblock_bridged_list.push(arm.op.to_string());
                            stepblock_proved.insert(arm.connect_theorem);
                        }
                        Err(e) => stepblock_pinned_list.push(format!(
                            "{}: connect: {}",
                            arm.op,
                            e.chars().take(200).collect::<String>()
                        )),
                    }
                }
            }
        }
        Err(e) => stepblock_pinned_list
            .push(format!("fixtures: {}", e.chars().take(200).collect::<String>())),
    }

    // -- 35. The composed stepblock theorem (requires the Add arm proven; --
    // -- runs in both Full and Spot mode). --
    let mut stepblock_composed = false;
    if stepblock_proved.len() == STEPBLOCK_ARMS.len() && !STEPBLOCK_ARMS.is_empty() {
        match load_bridge_source(&mut env, STEPBLOCK_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPBLOCK_COMPOSED_NAME)?;
                stepblock_composed = true;
            }
            Err(e) => stepblock_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 36. stepblock forgery probes: wrong claims MUST be rejected. --
    let stepblock_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPBLOCK_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPBLOCK_FORGERY_PROBES[..1],
    };
    let mut stepblock_fail_closed_controls = 0usize;
    for (label, src) in stepblock_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => stepblock_fail_closed_controls += 1,
        }
    }
    let stepblock_unbridged: Vec<String> =
        STEPBLOCK_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- 37. The stepN-branch (CondBr/.Continue, whole-BRANCHING-BODY) --
    // -- chain+connect arms — the FIRST agreement exercising stepN's --
    // -- recursive case. The fixture defs (+ the two Bool.rec helper --
    // -- lemmas) are loaded once; runs in BOTH Full and Spot mode (there --
    // -- are only two arms, true/false, so there is no mode-based --
    // -- filtering to do — mirrors stepblock's single-arm precedent). --
    let mut stepbranch_bridged_list: Vec<String> = Vec::new();
    let mut stepbranch_pinned_list: Vec<String> = Vec::new();
    let mut stepbranch_proved: BTreeSet<&str> = BTreeSet::new();
    match load_bridge_source(&mut env, STEPBRANCH_FIXTURES_SRC) {
        Ok(_) => {
            for arm in STEPBRANCH_ARMS {
                let chain_ok = match load_bridge_source(&mut env, arm.chain_src) {
                    Ok(_) => {
                        require_empty_axiom_deps(&env, arm.chain_theorem)?;
                        true
                    }
                    Err(e) => {
                        stepbranch_pinned_list.push(format!(
                            "{}: chain: {}",
                            arm.guard,
                            e.chars().take(200).collect::<String>()
                        ));
                        false
                    }
                };
                if chain_ok {
                    match load_bridge_source(&mut env, arm.connect_src) {
                        Ok(_) => {
                            require_empty_axiom_deps(&env, arm.connect_theorem)?;
                            stepbranch_bridged_list.push(arm.guard.to_string());
                            stepbranch_proved.insert(arm.connect_theorem);
                        }
                        Err(e) => stepbranch_pinned_list.push(format!(
                            "{}: connect: {}",
                            arm.guard,
                            e.chars().take(200).collect::<String>()
                        )),
                    }
                }
            }
        }
        Err(e) => stepbranch_pinned_list
            .push(format!("fixtures: {}", e.chars().take(200).collect::<String>())),
    }

    // -- 38. The composed stepN-branch theorem (requires BOTH arms proven; --
    // -- runs in both Full and Spot mode). --
    let mut stepbranch_composed = false;
    if stepbranch_proved.len() == STEPBRANCH_ARMS.len() && !STEPBRANCH_ARMS.is_empty() {
        match load_bridge_source(&mut env, STEPBRANCH_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPBRANCH_COMPOSED_NAME)?;
                stepbranch_composed = true;
            }
            Err(e) => stepbranch_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 39. stepN-branch forgery probes: wrong claims MUST be rejected. --
    let stepbranch_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPBRANCH_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPBRANCH_FORGERY_PROBES[..1],
    };
    let mut stepbranch_fail_closed_controls = 0usize;
    for (label, src) in stepbranch_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => stepbranch_fail_closed_controls += 1,
        }
    }
    let stepbranch_unbridged: Vec<String> =
        STEPBRANCH_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- 40. The stepN branch-WITH-BODY chain+connect arms — composing --
    // -- EXTENSION 7's control-flow technique with EXTENSION 6's --
    // -- body-fold technique. The fixture defs are loaded once; the true --
    // -- (Add) arm reuses `bridge_add`, always loaded; the false (Sub) arm --
    // -- reuses `bridge_sub`, which is ONLY loaded when the full ARMS set --
    // -- ran (Full mode) — so Spot mode attempts the true arm only, --
    // -- exactly mirroring STEPINST_BINOP_ARMS' own Spot-mode precedent. --
    let stepbranch_body_arm_set: Vec<&StepBranchBodyArmSpec> = match config.mode {
        BridgeGateMode::Full => STEPBRANCH_BODY_ARMS.iter().collect(),
        BridgeGateMode::Spot => STEPBRANCH_BODY_ARMS.iter().filter(|a| a.guard == "true").collect(),
    };
    let mut stepbranch_body_bridged_list: Vec<String> = Vec::new();
    let mut stepbranch_body_pinned_list: Vec<String> = Vec::new();
    let mut stepbranch_body_proved: BTreeSet<&str> = BTreeSet::new();
    match load_bridge_source(&mut env, STEPBRANCH_BODY_FIXTURES_SRC) {
        Ok(_) => {
            for arm in stepbranch_body_arm_set {
                let chain_ok = match load_bridge_source(&mut env, arm.chain_src) {
                    Ok(_) => {
                        require_empty_axiom_deps(&env, arm.chain_theorem)?;
                        true
                    }
                    Err(e) => {
                        stepbranch_body_pinned_list.push(format!(
                            "{}: chain: {}",
                            arm.guard,
                            e.chars().take(200).collect::<String>()
                        ));
                        false
                    }
                };
                if chain_ok {
                    match load_bridge_source(&mut env, arm.connect_src) {
                        Ok(_) => {
                            require_empty_axiom_deps(&env, arm.connect_theorem)?;
                            stepbranch_body_bridged_list.push(arm.guard.to_string());
                            stepbranch_body_proved.insert(arm.connect_theorem);
                        }
                        Err(e) => stepbranch_body_pinned_list.push(format!(
                            "{}: connect: {}",
                            arm.guard,
                            e.chars().take(200).collect::<String>()
                        )),
                    }
                }
            }
        }
        Err(e) => stepbranch_body_pinned_list
            .push(format!("fixtures: {}", e.chars().take(200).collect::<String>())),
    }

    // -- 41. The composed stepN branch-WITH-BODY theorem (requires BOTH --
    // -- arms proven; Full mode only — Spot never attempts the false arm). --
    let mut stepbranch_body_composed = false;
    if stepbranch_body_proved.len() == STEPBRANCH_BODY_ARMS.len()
        && !STEPBRANCH_BODY_ARMS.is_empty()
    {
        match load_bridge_source(&mut env, STEPBRANCH_BODY_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPBRANCH_BODY_COMPOSED_NAME)?;
                stepbranch_body_composed = true;
            }
            Err(e) => stepbranch_body_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 42. stepN branch-WITH-BODY forgery probes: wrong claims MUST be --
    // -- rejected. --
    let stepbranch_body_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPBRANCH_BODY_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPBRANCH_BODY_FORGERY_PROBES[..1],
    };
    let mut stepbranch_body_fail_closed_controls = 0usize;
    for (label, src) in stepbranch_body_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => stepbranch_body_fail_closed_controls += 1,
        }
    }
    let stepbranch_body_unbridged: Vec<String> =
        STEPBRANCH_BODY_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- 43. The steploop fixtures + both arms — the FIRST agreement over a --
    // -- GENUINE back-edge CFG, by fuel induction with a per-step lemma. --
    let mut steploop_bridged_list: Vec<String> = Vec::new();
    let mut steploop_pinned_list: Vec<String> = Vec::new();
    let mut steploop_proved: BTreeSet<&str> = BTreeSet::new();
    match load_bridge_source(&mut env, STEPLOOP_FIXTURES_SRC) {
        Ok(_) => {
            match load_bridge_source(&mut env, STEPLOOP_TRUE_SRC) {
                Ok(_) => {
                    require_empty_axiom_deps(&env, STEPLOOP_TRUE_THEOREM)?;
                    steploop_bridged_list.push("true_diverges".to_string());
                    steploop_proved.insert(STEPLOOP_TRUE_THEOREM);
                }
                Err(e) => steploop_pinned_list
                    .push(format!("true_diverges: {}", e.chars().take(200).collect::<String>())),
            }
            match load_bridge_source(&mut env, STEPLOOP_FALSE_SRC) {
                Ok(_) => {
                    require_empty_axiom_deps(&env, STEPLOOP_FALSE_THEOREM)?;
                    steploop_bridged_list.push("false_exits".to_string());
                    steploop_proved.insert(STEPLOOP_FALSE_THEOREM);
                }
                Err(e) => steploop_pinned_list
                    .push(format!("false_exits: {}", e.chars().take(200).collect::<String>())),
            }
        }
        Err(e) => steploop_pinned_list
            .push(format!("fixtures: {}", e.chars().take(200).collect::<String>())),
    }

    // -- 44. The composed steploop theorem (requires both arms proven). --
    let mut steploop_composed = false;
    if steploop_proved.len() == 2 {
        match load_bridge_source(&mut env, STEPLOOP_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPLOOP_COMPOSED_NAME)?;
                steploop_composed = true;
            }
            Err(e) => steploop_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 45. steploop forgery probes: wrong claims MUST be rejected. --
    let steploop_probes: &[(&str, &str)] = match config.mode {
        BridgeGateMode::Full => STEPLOOP_FORGERY_PROBES,
        BridgeGateMode::Spot => &STEPLOOP_FORGERY_PROBES[..1],
    };
    let mut steploop_fail_closed_controls = 0usize;
    for (label, src) in steploop_probes {
        match load_bridge_source(&mut env, src) {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted { probe: (*label).to_string() });
            }
            Err(_) => steploop_fail_closed_controls += 1,
        }
    }

    // -- 46. The staleness witness (Full mode only): a kernel-checked proof --
    // -- that the newly-discovered bindFresh/nextValueId obstruction is real. --
    let mut steploop_staleness_witness = false;
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, STEPLOOP_STALENESS_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, STEPLOOP_STALENESS_THEOREM)?;
                steploop_staleness_witness = true;
            }
            Err(e) => steploop_pinned_list
                .push(format!("staleness witness: {}", e.chars().take(200).collect::<String>())),
        }
    }

    let steploop_unbridged: Vec<String> =
        STEPLOOP_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    // -- 47. DATALOOP (Full mode only): the FIRST agreement over a --
    // -- back-edge CFG whose body COMPUTES, through stepNWithContext / --
    // -- bodyResultDests. Every kernel obligation below is confined to --
    // -- EXACTLY ONE block-visit (the per-visit chain design) — the --
    // -- mapped clean_kernel defeq-performance wall only fires when a --
    // -- SINGLE equality asks the kernel to reduce through 2+ --
    // -- instruction-bearing block-visits, which this design never does. --
    let mut dataloop_bridged = false;
    let mut dataloop_pinned_list: Vec<String> = Vec::new();
    let mut dataloop_fail_closed_controls = 0usize;
    if config.mode == BridgeGateMode::Full {
        match load_bridge_source(&mut env, DATALOOP_FIXTURES_SRC) {
            Ok(_) => {
                let mut visits_ok = true;
                for (label, src) in DATALOOP_VISITS {
                    match load_bridge_source(&mut env, src) {
                        Ok(_) => {
                            require_empty_axiom_deps(&env, &format!("dloop_{label}"))?;
                        }
                        Err(e) => {
                            visits_ok = false;
                            dataloop_pinned_list.push(format!(
                                "{label}: {}",
                                e.chars().take(200).collect::<String>()
                            ));
                        }
                    }
                }
                // The COMPOSED ground-fuel chain (DATALOOP_COMPOSED_STEPS) is
                // deliberately NOT attempted here: ground statements over the
                // full fuel-6-from-empty run still hit a memory-explosive
                // elaboration path (>12GB, watchdog-killed) — four profiled
                // sites are already fixed (clean-elab's reduce-before-compare
                // unifier ordering, tree-rebuilding instantiate, and
                // path-exponential meta scans; clean-kernel's debug-cert
                // inference sidestepped via the release-shaped dev profile),
                // and the residual site is documented in the module comment
                // and the landing report. Attempting the chain would OOM
                // every default gate run. The 6 per-visit lemmas above ARE
                // the loop cross, one kernel-checked block-visit at a time;
                // the composition is pure Eq.trans plumbing, preserved with
                // its mechanism probes in DATALOOP_COMPOSED_STEPS and
                // exercised by the env-gated dataloop_composed_wall_reproducer
                // (the fix-validation harness for the remaining clean-side
                // work).
                dataloop_bridged = visits_ok;
                if dataloop_bridged {
                    for (label, src) in DATALOOP_FORGERY_PROBES {
                        check_semantic_forgery_with_budget(&mut env, label, src, BRIDGE_DECL_BUDGET)?;
                        dataloop_fail_closed_controls += 1;
                    }
                }
            }
            Err(e) => dataloop_pinned_list
                .push(format!("fixtures: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 48. M4 v0 — GENERATED_FAMILIES (crates/trust-clean/src/cfg_family/). --
    // -- E7 (name uniqueness) over the whole registry BEFORE planning any --
    // -- one family, so a collision refuses the run deterministically --
    // -- rather than depending on iteration order. Each family's planning --
    // -- failure is a HARD error (registered-family discipline, design --
    // -- §4.3) — never a silently smaller generated-family set. --
    crate::cfg_family::gate::check_registry(crate::cfg_family::GENERATED_FAMILIES)?;
    let mut generated_families = Vec::with_capacity(crate::cfg_family::GENERATED_FAMILIES.len());
    for family_spec in crate::cfg_family::GENERATED_FAMILIES {
        generated_families.push(crate::cfg_family::gate::run_generated_family(
            &mut env,
            family_spec,
            config.mode,
        )?);
    }

    Ok(BridgeAgreement {
        ops_bridged: bridged.len(),
        ops_pinned: arm_set.len() - bridged.len(),
        pinned,
        bridged,
        form_a,
        form_b,
        form_b_guarded,
        reduction_lemmas,
        characterization_rows,
        composed_all18,
        trustir_commit: manifest_commit,
        selected_trustir_commit: checkout_commit,
        source_reuse_anchor,
        runtime_frontier,
        lean_toolchain: trustir_tree.lean_toolchain,
        manifest_ok: true,
        manifest_files: trustir_tree.files.len() + core_tree.files.len(),
        modules_loaded: summaries.len(),
        constants_loaded,
        trustir_recheck_pass: recheck_pass,
        trustir_recheck_fail: recheck_fail,
        trustir_recheck_seen: recheck_seen,
        trustir_runtime_refused: runtime_refused,
        axiom_deps_empty: true,
        fail_closed_controls,
        mode: match config.mode {
            BridgeGateMode::Full => "full".to_string(),
            BridgeGateMode::Spot => "spot".to_string(),
        },
        gate_seconds: t0.elapsed().as_secs_f64(),
        unop_ops_bridged: unop_bridged.len(),
        unop_ops_pinned: unop_arm_set.len() - unop_bridged.len(),
        unop_pinned,
        unop_bridged,
        unop_form_a,
        unop_form_b,
        unop_neg_sub_zero_form,
        unop_conc_rows,
        unop_composed,
        unop_fail_closed_controls,
        unop_unbridged,
        overflow_value_bridged,
        overflow_value_pinned,
        overflow_value_pinned_list,
        overflow_value_bridged_list,
        overflow_flag_bridged,
        overflow_flag_pinned,
        overflow_flag_pinned_list,
        overflow_flag_bridged_list,
        overflow_flag_guarded,
        overflow_composed,
        overflow_fail_closed_controls,
        overflow_flag_unbridged,
        overflow_umul_predicates_bound,
        overflow_umul_predicate_bridged,
        overflow_umul_predicate_pinned,
        overflow_umul_foundational_axioms,
        overflow_foundational_axioms,
        icmp_ops_bridged: icmp_bridged.len(),
        icmp_ops_pinned: icmp_arm_set.len() - icmp_bridged.len(),
        icmp_pinned,
        icmp_bridged,
        icmp_kind_unsigned,
        icmp_kind_sign_independent,
        icmp_kind_signed,
        icmp_conc_rows,
        icmp_composed,
        icmp_fail_closed_controls,
        icmp_unbridged,
        cast_ops_bridged: cast_bridged.len(),
        cast_ops_pinned: cast_arm_set.len() - cast_bridged.len(),
        cast_pinned,
        cast_bridged,
        cast_conc_rows,
        cast_widening_bridged: cast_widening_list.len(),
        cast_widening_list,
        cast_signcross_widening_bridged: cast_signcross_list.len(),
        cast_signcross_widening_list: cast_signcross_list,
        cast_composed,
        cast_fail_closed_controls,
        cast_unbridged,
        stepinst_binop_bridged: stepinst_binop_bridged_list.len(),
        stepinst_binop_pinned: stepinst_binop_arm_set.len() - stepinst_binop_bridged_list.len(),
        stepinst_binop_pinned_list,
        stepinst_binop_bridged_list,
        stepinst_binop_composed,
        stepinst_binop_fail_closed_controls,
        stepinst_binop_unbridged,
        stepinst_categories_unbridged,
        stepinst_unop_bridged: stepinst_unop_bridged_list.len(),
        stepinst_unop_pinned: STEPINST_UNOP_ARMS.len() - stepinst_unop_bridged_list.len(),
        stepinst_unop_pinned_list,
        stepinst_unop_bridged_list,
        stepinst_unop_neg_sub_zero_form,
        stepinst_unop_composed,
        stepinst_unop_fail_closed_controls,
        stepinst_unop_unbridged,
        stepinst_overflow_bridged: stepinst_overflow_bridged_list.len(),
        stepinst_overflow_pinned: 1 - stepinst_overflow_bridged_list.len(),
        stepinst_overflow_pinned_list,
        stepinst_overflow_bridged_list,
        stepinst_overflow_composed,
        stepinst_overflow_fail_closed_controls,
        stepinst_overflow_unbridged,
        stepinst_icmp_bridged: stepinst_icmp_bridged_list.len(),
        stepinst_icmp_pinned: 1 - stepinst_icmp_bridged_list.len(),
        stepinst_icmp_pinned_list,
        stepinst_icmp_bridged_list,
        stepinst_icmp_composed,
        stepinst_icmp_fail_closed_controls,
        stepinst_icmp_unbridged,
        stepinst_cast_bridged: stepinst_cast_bridged_list.len(),
        stepinst_cast_pinned: 1 - stepinst_cast_bridged_list.len(),
        stepinst_cast_pinned_list,
        stepinst_cast_bridged_list,
        stepinst_cast_composed,
        stepinst_cast_fail_closed_controls,
        stepinst_cast_unbridged,
        stepinst_categories_composed,
        stepblock_bridged: stepblock_bridged_list.len(),
        stepblock_pinned: STEPBLOCK_ARMS.len() - stepblock_bridged_list.len(),
        stepblock_pinned_list,
        stepblock_bridged_list,
        stepblock_composed,
        stepblock_fail_closed_controls,
        stepblock_unbridged,
        stepbranch_bridged: stepbranch_bridged_list.len(),
        stepbranch_pinned: STEPBRANCH_ARMS.len() - stepbranch_bridged_list.len(),
        stepbranch_pinned_list,
        stepbranch_bridged_list,
        stepbranch_composed,
        stepbranch_fail_closed_controls,
        stepbranch_unbridged,
        stepbranch_body_bridged: stepbranch_body_bridged_list.len(),
        stepbranch_body_pinned: STEPBRANCH_BODY_ARMS.len() - stepbranch_body_bridged_list.len(),
        stepbranch_body_pinned_list,
        stepbranch_body_bridged_list,
        stepbranch_body_composed,
        stepbranch_body_fail_closed_controls,
        stepbranch_body_unbridged,
        steploop_bridged: steploop_bridged_list.len(),
        steploop_pinned: 2 - steploop_proved.len(),
        steploop_pinned_list,
        steploop_bridged_list,
        steploop_composed,
        steploop_fail_closed_controls,
        steploop_staleness_witness,
        steploop_unbridged,
        dataloop_bridged,
        dataloop_pinned_list,
        dataloop_fail_closed_controls,
        generated_families,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The step budget bounds EACH step, not the run: six steps of 0.5 s under a
    /// 2 s per-step budget spend 3 s in total and still complete. (A whole-run
    /// bound would time this out; the gate is hundreds of steps, so it must
    /// not be one.)
    #[test]
    fn step_budget_bounds_each_step_not_the_whole_run() {
        let started = Instant::now();
        let steps = run_with_step_budget(2, "step 0", || {
            for step in 1..=6 {
                bridge_gate_step(|| format!("step {step}"));
                std::thread::sleep(std::time::Duration::from_millis(500));
            }
            6
        })
        .expect("no single step came near the per-step budget");
        assert_eq!(steps, 6);
        assert!(started.elapsed() >= std::time::Duration::from_secs(3));
    }

    /// A step that outlives the budget ends the run as a named TIMEOUT —
    /// promptly, while the stalled work is still running — and the outcome is
    /// incomplete, never a verdict.
    #[test]
    fn step_budget_times_out_a_stalled_step_by_name() {
        let started = Instant::now();
        let outcome = run_with_step_budget(1, "prologue", || {
            bridge_gate_step(|| "a step that stalls".to_owned());
            std::thread::sleep(std::time::Duration::from_secs(60));
            "late verdict"
        });
        let elapsed = started.elapsed();
        let Err(error) = outcome else {
            panic!("a 60 s step under a 1 s budget must time out, got {outcome:?}");
        };
        assert!(
            matches!(
                &error,
                BridgeGateError::BudgetExceeded { budget_secs: 1, step, steps_begun: 2 }
                    if step == "a step that stalls"
            ),
            "the timeout must name the stalled step, got {error:?}"
        );
        assert!(error.is_incomplete(), "a spent budget is an unknown outcome, not a refusal");
        assert!(error.to_string().starts_with("TIMEOUT"));
        // Reported at the 1 s budget, not after the 60 s step; the slack is for
        // a loaded host.
        assert!(elapsed < std::time::Duration::from_secs(30), "timed out only after {elapsed:?}");
    }

    /// A panic inside budgeted work surfaces on the caller exactly as the
    /// unbudgeted call would raise it — never as a timeout or a verdict.
    #[test]
    #[should_panic(expected = "gate work panicked")]
    fn step_budget_reraises_a_panic_in_the_work() {
        let _ = run_with_step_budget(30, "prologue", || -> u8 { panic!("gate work panicked") });
    }

    /// Outside a budgeted run a step mark is a no-op: its label is never even
    /// built, so the unbudgeted gate pays nothing for the instrumentation.
    #[test]
    fn step_mark_is_inert_outside_a_budgeted_run() {
        let built = std::cell::Cell::new(false);
        bridge_gate_step(|| {
            built.set(true);
            String::new()
        });
        assert!(!built.get());
    }

    /// GAP-CROSS-SIGN-WIDEN isolation probe (gated behind `TRUST_SIGNCROSS_PROBE=1`
    /// to keep the default suite fast): set up the bridge env exactly like
    /// `run_bridge_gate` and TIME-load ONLY the sign-cross corollary + its forgery
    /// probe, so the corollary's elaboration cost can be measured without running
    /// the whole (multi-minute) Full-mode gate. Prints timings + outcomes.
    /// `#[ignore]`d, and it panics without `TRUST_SIGNCROSS_PROBE=1`, so a bare
    /// `--ignored` run cannot pass having measured nothing.
    #[test]
    #[ignore = "measurement driver: set TRUST_SIGNCROSS_PROBE=1 and run with --ignored --nocapture"]
    fn signcross_corollary_probe() {
        if std::env::var("TRUST_SIGNCROSS_PROBE").as_deref() != Ok("1") {
            panic!(
                "signcross_corollary_probe is a measurement driver and TRUST_SIGNCROSS_PROBE \
                 is not 1, so it measured nothing. Run: TRUST_SIGNCROSS_PROBE=1 \
                 targo --unverified test --manifest-path crates/Cargo.toml -p trust-clean \
                 --lib -- --ignored --exact \
                 trustir_bridge::tests::signcross_corollary_probe --nocapture"
            );
        }
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir_tree =
            verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
                .expect("manifest");
        let core_tree =
            verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
                .expect("core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let root_modules: Vec<String> =
            BRIDGE_ROOT_MODULES.iter().map(|s| (*s).to_string()).collect();
        load_verified_modules(&mut env, &root_modules, &trustir_tree, &core_tree).expect("closure import");
        load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).expect("bridge order instances");

        // The NEW sign-cross corollary MUST kernel-check with empty axiom residue.
        let t = std::time::Instant::now();
        let s = load_bridge_source(&mut env, CAST_ZEXT_SIGNCROSS_SRC);
        eprintln!("PROBE signcross-corollary ({:.3}s): {s:?}", t.elapsed().as_secs_f64());
        assert!(s.is_ok(), "sign-cross corollary must kernel-check: {s:?}");
        assert_eq!(
            axiom_deps_str(&env, CAST_ZEXT_SIGNCROSS_NAME),
            "[]",
            "sign-cross corollary must have empty axiom residue"
        );

        // The forgery probe (identity claimed WITHOUT the strict-widening bound)
        // MUST fail to elaborate — rejected, fail-closed.
        let forgery_src = CAST_FORGERY_PROBES
            .iter()
            .find(|(l, _)| l.starts_with("signcross-without-half-bound"))
            .map(|(_, src)| *src)
            .expect("signcross forgery present");
        let t = std::time::Instant::now();
        let f = load_bridge_source(&mut env, forgery_src);
        eprintln!(
            "PROBE signcross-forgery (MUST be Err) ({:.3}s): {}",
            t.elapsed().as_secs_f64(),
            match &f {
                Ok(n) => format!("ACCEPTED(bad): {n:?}"),
                Err(e) => e.chars().take(120).collect::<String>(),
            }
        );
        assert!(f.is_err(), "sign-cross forgery MUST be rejected (fail-closed)");
    }

    /// Stack for a deadlined bridge worker.
    ///
    /// clean-kernel wraps its defeq recursion in `stacker::maybe_grow`, so it
    /// grows past whatever it is given; this only keeps the common depth off
    /// the growth path, matching what libtest hands an ordinary test thread.
    const BRIDGE_WORKER_STACK: usize = 64 * 1024 * 1024;

    /// Run a heavy bridge test body under a wall-clock deadline, so that a
    /// kernel query which does not converge FAILS WITH A DIAGNOSIS instead of
    /// hanging the suite with no verdict and no name.
    ///
    /// # Why this exists on top of `BRIDGE_DECL_BUDGET`
    ///
    /// The ambient per-declaration budget is the real bound and is
    /// deterministic; this is the net under the one case the budget's own
    /// documentation excludes — a pathology whose cost is per-tick
    /// ALLOCATION SIZE rather than tick count (measured here once as 1.4 GB
    /// RSS at 49 s growing to 3.8 GB at 4 min).
    ///
    /// # What it can and cannot do
    ///
    /// A synchronous Rust call cannot be interrupted from outside, so on
    /// expiry the body's thread is DETACHED, not stopped: it keeps running
    /// and keeps holding `elab_lock`. Any later bridge test then blocks on
    /// that lock — which is why the diagnosis below reports the declaration
    /// in flight and the tick peak, and why a deadline expiry should be read
    /// as "this process is now unreliable for bridge work", not as one
    /// isolated failure. The worker is NAMED after the test so that `sample`
    /// attributes its stack correctly (see `elab_lock`: libtest's own thread
    /// naming is exactly what once misattributed this module's stall to the
    /// test that was merely blocked).
    ///
    /// The deadline is wall clock, so it is contention-sensitive: these two
    /// tests spend most of a full-suite run waiting on `elab_lock`, not
    /// working. The bounds below are therefore set at several times the
    /// measured contended wall time, and the failure text tells the reader
    /// how to tell a genuine divergence from a loaded machine.
    fn run_with_bridge_deadline(
        test: &'static str,
        deadline: std::time::Duration,
        body: impl FnOnce() + Send + 'static,
    ) {
        let started = Instant::now();
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        let worker = std::thread::Builder::new()
            .name(test.to_owned())
            .stack_size(BRIDGE_WORKER_STACK)
            .spawn(move || {
                let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(body));
                let _ = done_tx.send(());
                outcome
            })
            .expect("spawn the deadlined bridge worker");
        if done_rx.recv_timeout(deadline).is_err() {
            panic!(
                "{test}: DID NOT FINISH within {deadline:?}.\n  \
                 declaration in flight: {in_flight}\n  \
                 peak per-declaration kernel ticks so far: {peak} of a budget of \
                 {budget}\n  \
                 Reading it: a peak at the budget means a declaration was CUT OFF \
                 (non-convergence, neither proved nor refuted — see \
                 docs/issues/2026-09-19-clean-defeq-structure-eta-escapes-delta-cap.md). \
                 A peak far below it means the work was progressing and this box is \
                 either heavily loaded or hit the allocation-size pathology the tick \
                 budget cannot bound. Either way the worker thread is still running \
                 and still holds elab_lock, so later bridge tests in this process are \
                 no longer meaningful.",
                in_flight = bridge_decl_in_flight_label(),
                peak = bridge_peak_decl_ticks(),
                budget = BRIDGE_DECL_BUDGET,
            );
        }
        let elapsed = started.elapsed();
        let outcome = worker.join().expect("the bridge worker thread must not vanish");
        eprintln!(
            "{test}: finished in {elapsed:?}; peak per-declaration kernel ticks {} of {}",
            bridge_peak_decl_ticks(),
            BRIDGE_DECL_BUDGET
        );
        if let Err(panic) = outcome {
            std::panic::resume_unwind(panic);
        }
    }

    /// Deadline for [`imported_int_order_instances_preserve_relations`].
    ///
    /// Measured 2026-09-19: 4.2 s alone, 53.8 s beside its own module, 205 s
    /// in a full contended suite run — and ~100 % of that delta is
    /// `elab_lock` wait, not work (see `elab_lock`). The bound is set on the
    /// contended figure, not the isolated one, because contention is the
    /// normal case for this test.
    const IMPORTED_INT_ORDER_DEADLINE: std::time::Duration =
        std::time::Duration::from_secs(20 * 60);

    /// Deadline for [`cast_composition_rechecks_every_conjunct`].
    ///
    /// Measured 2026-09-19: 368 s alone (of which `bridge_cast_zext` 107 s
    /// and `bridge_cast_sext` 95 s), 357 s in a full contended suite run.
    /// Sized above `BRIDGE_DECL_BUDGET`'s own worst case (~10 min for one
    /// runaway declaration) so the budget, which names the declaration,
    /// reports first whenever it can.
    const CAST_COMPOSITION_DEADLINE: std::time::Duration = std::time::Duration::from_secs(30 * 60);

    /// The deadline is the net under the budget; prove it reports rather
    /// than hangs. The body outlives the deadline on purpose.
    #[test]
    #[should_panic(expected = "DID NOT FINISH within")]
    fn bridge_deadline_diagnoses_instead_of_hanging() {
        run_with_bridge_deadline(
            "bridge_deadline_diagnoses_instead_of_hanging",
            std::time::Duration::from_millis(50),
            || std::thread::sleep(std::time::Duration::from_secs(2)),
        );
    }

    /// The per-declaration budget must refuse a declaration it cut off, by
    /// NAME, and must never round a cut-off declaration up into a pass. Run
    /// at a budget of 1 tick so the cut-off is certain and cheap.
    #[test]
    fn bridge_decl_budget_refuses_by_name_instead_of_passing() {
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir_tree =
            verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
                .expect("trust-ir manifest");
        let core_tree =
            verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
                .expect("core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
        load_verified_modules(&mut env, &roots, &trustir_tree, &core_tree).expect("actual vendored import");

        // Deliberately instance-free and notation-free: this test is about the
        // BOUND, so the declaration must not depend on the bridge's own
        // notation aliases (`BRIDGE_INSTANCE_SRC`) being loaded first.
        let source =
            "theorem bridge_decl_budget_probe (a b : Int) : Int.le a b = Int.le a b := rfl";
        let starved = load_bridge_source_with_budget(&mut env, source, 1)
            .expect_err("a declaration cut off by the budget must never report a pass");
        assert!(
            starved.contains("bridge_decl_budget_probe") && starved.contains("DID NOT FINISH"),
            "the refusal must name the declaration that did not converge, got: {starved}"
        );
        // ... and the same declaration under the real budget is a pass, so
        // the bound refuses only what it actually cut off.
        let names = load_bridge_source(&mut env, source)
            .expect("the same declaration converges inside the production budget");
        assert_eq!(names, vec!["bridge_decl_budget_probe".to_owned()]);
    }

    #[test]
    fn stepinst_overflow_binds_two_ssa_results() {
        run_with_bridge_deadline(
            "stepinst_overflow_binds_two_ssa_results",
            IMPORTED_INT_ORDER_DEADLINE,
            stepinst_overflow_binds_two_ssa_results_body,
        );
    }

    fn stepinst_overflow_binds_two_ssa_results_body() {
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir_tree =
            verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
                .expect("trust-ir manifest");
        let core_tree =
            verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
                .expect("core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
        load_verified_modules(&mut env, &roots, &trustir_tree, &core_tree).expect("actual vendored import");
        load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).expect("checked notation instances");

        let names = load_bridge_source(&mut env, STEPINST_OVERFLOW_CHAIN_SRC)
            .expect("the actual instruction binds result and overflow as separate SSA values");
        assert_eq!(names, vec![STEPINST_OVERFLOW_CHAIN_THEOREM.to_owned()]);
        require_empty_axiom_deps(&env, STEPINST_OVERFLOW_CHAIN_THEOREM)
            .expect("the chain theorem has no axiom residue");

        // Every mutant still parses the same instruction and initial state.
        // The kernel must notice each wrong component of its complete result.
        for (index, (from, to)) in [
            (
                "InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3]",
                "InstrResult.value (some (TrustIr.ValueId.mk 2))",
            ),
            (
                "InstrResult.values [TrustIr.ValueId.mk 2, TrustIr.ValueId.mk 3]",
                "InstrResult.values [TrustIr.ValueId.mk 3, TrustIr.ValueId.mk 2]",
            ),
            ("nextValueId := 4", "nextValueId := 3"),
            ("(TrustIr.Value.bool p.2)", "(TrustIr.Value.bool true)"),
        ]
        .into_iter()
        .enumerate()
        {
            assert_eq!(STEPINST_OVERFLOW_CHAIN_SRC.matches(from).count(), 1);
            let mutant = STEPINST_OVERFLOW_CHAIN_SRC.replace(from, to).replace(
                STEPINST_OVERFLOW_CHAIN_THEOREM,
                &format!("stepinst_overflow_wrong_result_{index}"),
            );
            let err = load_bridge_source(&mut env, &mutant)
                .expect_err("an incorrect result identity, cursor or value must refuse");
            assert!(err.contains("TypeMismatch"), "mutation {index}: {err}");
        }
    }

    #[test]
    fn imported_int_order_instances_preserve_relations() {
        run_with_bridge_deadline(
            "imported_int_order_instances_preserve_relations",
            IMPORTED_INT_ORDER_DEADLINE,
            imported_int_order_instances_preserve_relations_body,
        );
    }

    fn imported_int_order_instances_preserve_relations_body() {
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir_tree =
            verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
                .expect("trust-ir manifest");
        let core_tree =
            verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
                .expect("core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
        load_verified_modules(&mut env, &roots, &trustir_tree, &core_tree).expect("actual vendored import");

        // Per-source probes, same as `cast_composition_rechecks_every_conjunct`:
        // a regression here must be localisable to a source fragment without a
        // debugger, and these numbers are what distinguishes real work from
        // `elab_lock` wait when the module runs concurrently.
        let started = Instant::now();
        let instance_names = load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC)
            .expect("checked aliases of the actual imported order instances");
        eprintln!(
            "notation instances: {} checked declarations in {:?}",
            instance_names.len(),
            started.elapsed()
        );
        // Check the actual declaration roster, including the three notation
        // decisions added beside the canonical Int.le/Int.lt instances. A
        // count alone could miss a removed alias replaced by an unrelated one.
        assert_eq!(
            instance_names.iter().map(String::as_str).collect::<Vec<_>>(),
            vec![
                "bridgeIntLE",
                "bridgeIntLT",
                "bridgeIntDecLe",
                "bridgeIntDecLt",
                "bridgeIntDecLeNotation",
                "bridgeIntDecLtNotation",
                "bridgeIntDecGeNotation",
                "bridgeIntAdd",
                "bridgeIntSub",
                "bridgeNatSub",
                "bridgeIntMul",
                "bridgeIntMod",
                "bridgeIntPow",
                "bridgeIntNeg",
                "bridgeIntOfNat",
                "bridgeNatOfNat",
                "bridgeIntDecEq",
                "bridgeBoolDecEq",
                "bridgeIntBEq",
                "bridgeTyBEq",
            ]
        );
        for name in &instance_names {
            require_empty_axiom_deps(&env, name).expect("instance alias has no axiom residue");
        }
        let started = Instant::now();
        let names = load_bridge_source(
            &mut env,
            r#"theorem bridge_imported_le_identity (a b : Int) :
                (@LE.le Int Int.instLEInt a b) = Int.le a b := rfl
            theorem bridge_order_le_identity (a b : Int) : (a ≤ b) = Int.le a b := rfl
            theorem bridge_order_lt_identity (a b : Int) : (a < b) = Int.lt a b := rfl
            theorem bridge_order_dec_le_identity (a b : Int) :
                Decidable.decide (a ≤ b) = @Decidable.decide (Int.le a b) (Int.decLe a b) := rfl
            theorem bridge_order_dec_lt_identity (a b : Int) :
                Decidable.decide (a < b) = @Decidable.decide (Int.lt a b) (Int.decLt a b) := rfl
            theorem bridge_order_dec_ge_identity (a b : Int) :
                Decidable.decide (a ≥ b) = @Decidable.decide (Int.le b a) (Int.decLe b a) := rfl
            theorem bridge_int_add_identity (a b : Int) : (a + b) = Int.add a b := rfl
            theorem bridge_int_sub_identity (a b : Int) : (a - b) = Int.sub a b := rfl
            theorem bridge_nat_sub_identity (a b : Nat) : (a - b) = Nat.sub a b := rfl
            theorem bridge_int_mul_identity (a b : Int) : (a * b) = Int.mul a b := rfl
            theorem bridge_int_mod_identity (a b : Int) : (a % b) = Int.emod a b := rfl
            theorem bridge_int_pow_identity (a : Int) (n : Nat) : (a ^ n) = Int.pow a n := rfl
            theorem bridge_int_neg_identity (a : Int) : (-a) = Int.neg a := rfl
            theorem bridge_int_literal_identity (n : Nat) :
                @OfNat.ofNat Int n (bridgeIntOfNat n) = @OfNat.ofNat Int n (@instOfNat n) := rfl
            theorem bridge_nat_literal_identity (n : Nat) :
                @OfNat.ofNat Nat n (bridgeNatOfNat n) = n := rfl
            theorem bridge_int_dec_eq_identity (a b : Int) :
                Decidable.decide (a = b) = @Decidable.decide (a = b) (Int.decEq a b) := rfl
            theorem bridge_bool_dec_eq_identity (a b : Bool) :
                Decidable.decide (a = b) = @Decidable.decide (a = b) (Bool.decEq a b) := rfl
            theorem bridge_int_beq_identity (a b : Int) :
                (a == b) = @Decidable.decide (a = b) (Int.decEq a b) := rfl
            theorem bridge_ty_beq_identity (a b : TrustIr.Ty) :
                (a == b) = @BEq.beq TrustIr.Ty TrustIr.instBEqTy a b := rfl
            "#,
        )
        .expect("bridge notation and decisions must denote the exact imported functions");
        eprintln!(
            "int/order identities: {} checked declarations in {:?}",
            names.len(),
            started.elapsed()
        );
        assert_eq!(names.len(), 19);
        for name in &names {
            require_empty_axiom_deps(&env, name).expect("identity proof has no axiom residue");
        }
        let started = Instant::now();
        let reversed = load_bridge_source(
            &mut env,
            "theorem bridge_imported_le_reversed (a b : Int) : \
             (a ≤ b) = Int.le b a := rfl",
        );
        eprintln!("reversed-relation refusal probe in {:?}", started.elapsed());
        assert!(reversed.is_err(), "reversing the relation must not be definitionally equal");
        let wrong_ge = load_bridge_source(
            &mut env,
            "theorem bridge_order_dec_ge_wrong_direction (a b : Int) : \
             Decidable.decide (a ≥ b) = \
             @Decidable.decide (Int.le a b) (Int.decLe a b) := rfl",
        );
        assert!(wrong_ge.is_err(), "the reversed notation must retain its argument order");
    }


    #[test]
    fn multi_scrutinee_decidable_or() {
        run_with_bridge_deadline(
            "multi_scrutinee_decidable_or",
            IMPORTED_INT_ORDER_DEADLINE,
            unsigned_mul::check_imported_multi_scrutinee_decidable_or_for_test,
        );
    }

    #[test]
    fn unsigned_mul_int_predicates_and_overflow_composition_are_kernel_checked() {
        run_with_bridge_deadline(
            "unsigned_mul_int_predicates_and_overflow_composition",
            IMPORTED_INT_ORDER_DEADLINE,
            unsigned_mul::check_imported_overflow_layer_for_test,
        );
    }

    #[test]
    fn stepinst_divrem_composition_rechecks_state_guards_and_identity() {
        run_with_bridge_deadline(
            "stepinst_divrem_composition",
            CAST_COMPOSITION_DEADLINE,
            stepinst_divrem_composition_body,
        );
    }

    fn stepinst_divrem_composition_body() {
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir = verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect("original TrustIR manifest");
        let core = verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
            .expect("original Lean-core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
        load_verified_modules(&mut env, &roots, &trustir, &core).expect("actual shared model import");
        let check = |env: &mut Environment, label: &str, source: &str| {
            let names = load_bridge_source(env, source)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            for name in names {
                require_empty_axiom_deps(env, &name)
                    .unwrap_or_else(|error| panic!("{label}: {error}"));
            }
        };
        check(&mut env, "original instances", BRIDGE_INSTANCE_SRC);
        check(&mut env, "original value prelude", PRELUDE_SRC);
        for (name, source) in REDUCTION_SRCS { check(&mut env, name, source); }
        for arm in ARMS.iter().take(7) { check(&mut env, arm.theorem, arm.src); }
        check(&mut env, "shared state transport", STEPINST_BINOP_TRANSPORT_SRC);
        for arm in STEPINST_BINOP_ARMS {
            check(&mut env, arm.chain_theorem, arm.chain_src);
            check(&mut env, arm.connect_theorem, arm.connect_src);
            eprintln!("{}: original value proof composed with exact state/SSA transport", arm.op);
        }
        check(&mut env, "all seven composed", STEPINST_BINOP_COMPOSED_SRC);
        check(&mut env, "actual concrete division and remainder", STEPINST_DIVREM_CONCRETE_SRC);
        for (label, source) in STEPINST_BINOP_FORGERY_PROBES {
            check_semantic_forgery_with_budget(&mut env, label, source, BRIDGE_DECL_BUDGET)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            eprintln!("{label}: typed semantic mismatch, budget not exhausted");
        }
        let honest = check_semantic_forgery_with_budget(&mut env, "accepted control",
            "theorem stepinst_honest_control : True := True.intro", BRIDGE_DECL_BUDGET)
            .expect_err("an accepted proof is not a refutation");
        assert!(matches!(honest, BridgeGateError::ForgeryAccepted { .. }));
        let missing = check_semantic_forgery_with_budget(&mut env, "missing input",
            "theorem stepinst_missing_control : True := stepinst_absent_input", BRIDGE_DECL_BUDGET)
            .expect_err("missing input is not a semantic refutation");
        assert!(matches!(missing, BridgeGateError::ForgeryUnqualified { incomplete: false, .. }));
        let budget_source = STEPINST_BINOP_ARMS[3].connect_src.replace(
            "bridge_stepInst_binop_udiv", "stepinst_budget_control");
        let exhausted = check_semantic_forgery_with_budget(&mut env, "budget", &budget_source, 1)
            .expect_err("budget exhaustion is not a semantic refutation");
        assert!(matches!(exhausted, BridgeGateError::ForgeryUnqualified { incomplete: true, .. }));
    }

    #[test]
    fn cast_composition_rechecks_every_conjunct() {
        run_with_bridge_deadline(
            "cast_composition_rechecks_every_conjunct",
            CAST_COMPOSITION_DEADLINE,
            cast_composition_rechecks_every_conjunct_body,
        );
    }

    fn cast_composition_rechecks_every_conjunct_body() {
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir_tree =
            verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
                .expect("trust-ir manifest");
        let core_tree =
            verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
                .expect("core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
        load_verified_modules(&mut env, &roots, &trustir_tree, &core_tree).expect("actual vendored import");

        // Replay the actual Cast sources in their production order, preserving
        // every theorem statement. This isolates a composition refusal from
        // the other bridge families and reports its complete diagnostic.
        let sources = std::iter::once(("notation instances", BRIDGE_INSTANCE_SRC))
            .chain(CAST_ARMS.iter().map(|arm| (arm.theorem, arm.src)))
            .chain([
                ("cast concrete rows", CAST_CONC_SRC),
                (CAST_ZEXT_WIDENING_NAME, CAST_ZEXT_WIDENING_SRC),
                (CAST_ZEXT_SIGNCROSS_NAME, CAST_ZEXT_SIGNCROSS_SRC),
                (CAST_COMPOSED_NAME, CAST_COMPOSED_SRC),
                (STEPINST_CAST_CHAIN_THEOREM, STEPINST_CAST_CHAIN_SRC),
                (STEPINST_CAST_CONNECT_THEOREM, STEPINST_CAST_CONNECT_SRC),
                (STEPINST_CAST_COMPOSED_NAME, STEPINST_CAST_COMPOSED_SRC),
            ]);
        for (label, source) in sources {
            let started = std::time::Instant::now();
            let names = load_bridge_source(&mut env, source)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            for name in &names {
                require_empty_axiom_deps(&env, name)
                    .unwrap_or_else(|error| panic!("{label}: {error:?}"));
            }
            eprintln!("{label}: {} checked declarations in {:?}", names.len(), started.elapsed());
        }
        require_empty_axiom_deps(&env, CAST_COMPOSED_NAME)
            .expect("the exact composed Cast theorem must be registered and checked");
        require_empty_axiom_deps(&env, STEPINST_CAST_COMPOSED_NAME)
            .expect("the exact composed stepInst Cast theorem must be registered and checked");
        // Positive premises are registered first: a missing agreement lemma
        // cannot masquerade as rejection of a wrong width or result value.
        for (label, source) in CAST_FORGERY_PROBES.iter().chain(STEPINST_CAST_FORGERY_PROBES) {
            check_semantic_forgery_with_budget(&mut env, label, source, BRIDGE_DECL_BUDGET)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            eprintln!("{label}: typed semantic mismatch; declaration budget not exhausted");
        }

        let honest_result = check_semantic_forgery_with_budget(
            &mut env,
            "honest proof",
            "theorem bridge_honest_probe : True := True.intro",
            BRIDGE_DECL_BUDGET,
        ).expect_err("an accepted proof cannot qualify as a refutation");
        assert!(matches!(honest_result, BridgeGateError::ForgeryAccepted { .. }));
        assert!(!honest_result.is_incomplete());

        let missing_result = check_semantic_forgery_with_budget(
            &mut env,
            "missing input",
            "theorem bridge_missing_input_probe : True := absent_bridge_input",
            BRIDGE_DECL_BUDGET,
        ).expect_err("missing input is not a semantic refutation");
        assert!(matches!(missing_result, BridgeGateError::ForgeryUnqualified { incomplete: false, .. }));
        assert!(missing_result.is_incomplete());

        let budget_source = CAST_ARMS[0].src.replace("bridge_cast_trunc", "bridge_cast_budget_probe");
        let budget_result = check_semantic_forgery_with_budget(&mut env, "budget", &budget_source, 1)
            .expect_err("a truncated check cannot qualify a semantic refutation");
        assert!(matches!(budget_result, BridgeGateError::ForgeryUnqualified { incomplete: true, .. }));
        assert!(budget_result.is_incomplete());
    }

    #[test]
    fn dataloop_visits_follow_exact_current_ssa_bindings() {
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir = verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect("current TrustIR manifest");
        let core = verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
            .expect("current core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
        load_verified_modules(&mut env, &roots, &trustir, &core).expect("current complete import");
        load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).expect("original notation");
        load_bridge_source(&mut env, PRELUDE_SRC).expect("original prelude");
        load_bridge_source(&mut env, DATALOOP_FIXTURES_SRC).expect("original loop and current states");
        for (label, source) in DATALOOP_VISITS {
            let names = load_bridge_source(&mut env, source)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            for name in names {
                require_empty_axiom_deps(&env, &name).expect("visit adds no axiom residue");
            }
            eprintln!("{label}: current whole-state transition checked");
        }
        let retired = r#"theorem dloop_retired3 : dloopState3.locals (TrustIr.ValueId.mk 5) = none := rfl
theorem dloop_retired4 : dloopState4.locals (TrustIr.ValueId.mk 6) = none := rfl
theorem dloop_retired5 : dloopState5.locals (TrustIr.ValueId.mk 7) = none := rfl
"#;
        for name in load_bridge_source(&mut env, retired).expect("private temporaries are absent") {
            require_empty_axiom_deps(&env, &name).expect("retirement adds no axiom residue");
        }
        for (label, source) in DATALOOP_FORGERY_PROBES {
            check_semantic_forgery_with_budget(&mut env, label, source, BRIDGE_DECL_BUDGET)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
        }
        check_semantic_forgery_with_budget(&mut env, "old temporary remains defined",
            "theorem dloop_retained_temp_wrong : dloopState3.locals (TrustIr.ValueId.mk 5) = some (TrustIr.Value.bool true) := rfl",
            BRIDGE_DECL_BUDGET).expect("old state must fail by semantic mismatch");
    }

    #[test]
    fn manifest_schema_mismatch_fails_closed() {
        let dir = std::env::temp_dir().join(format!("bridge-schema-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        std::fs::write(
            dir.join("MANIFEST.toml"),
            "schema = \"wrong.schema.v0\"\n[provenance]\nlean_toolchain = \"x\"\n[files]\n",
        )
        .expect("write manifest");
        let err = verify_manifest(&dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect_err("wrong schema must fail closed");
        assert!(matches!(err, BridgeGateError::ManifestSchema { .. }), "got {err:?}");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn manifest_missing_fails_closed() {
        let dir = std::env::temp_dir().join(format!("bridge-missing-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        let err = verify_manifest(&dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect_err("absent manifest must fail closed");
        assert!(matches!(err, BridgeGateError::ManifestUnreadable { .. }), "got {err:?}");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn manifest_without_trustir_commit_fails_closed_when_required() {
        let dir = std::env::temp_dir().join(format!("bridge-nocommit-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        std::fs::write(
            dir.join("MANIFEST.toml"),
            format!(
                "schema = \"{TRUSTIR_MANIFEST_SCHEMA}\"\n[provenance]\nlean_toolchain = \"x\"\n[files]\n"
            ),
        )
        .expect("write manifest");
        let err = verify_manifest(&dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect_err("missing trustir_commit must fail closed");
        assert!(matches!(err, BridgeGateError::ManifestProvenance { .. }), "got {err:?}");
        std::fs::remove_dir_all(&dir).ok();
    }

    /// A manifest whose HOST platform table names the trust-ir revision its
    /// bytes were built from; files are empty so only provenance is judged.
    fn platform_provenance_manifest(dir: &Path, built_from: Option<&str>) {
        let triple = host_triple();
        let built_from = built_from
            .map(|c| format!("built_from_trustir_commit = \"{c}\"\n"))
            .unwrap_or_default();
        std::fs::write(
            dir.join("MANIFEST.toml"),
            format!(
                "schema = \"{TRUSTIR_MANIFEST_SCHEMA}\"\n[provenance]\n\
                 trustir_commit = \"{new}\"\nlean_toolchain = \"x\"\n[files]\n\
                 [platforms.\"{triple}\"]\n{built_from}",
                new = "a".repeat(40),
            ),
        )
        .expect("write manifest");
    }

    /// 2026-09-24: a regeneration on one platform carried the other platform's
    /// bytes forward under the NEW trustir_commit (Linux oleans built from
    /// trust-ir 00180257 were labelled 29744d5f). The host platform must name
    /// what it was built from, and must have been built from the manifest's
    /// commit; otherwise the bridge refuses instead of replaying stale semantics.
    #[test]
    fn a_platform_built_from_another_trustir_commit_fails_closed() {
        let dir = std::env::temp_dir().join(format!("bridge-stale-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");

        platform_provenance_manifest(&dir, Some(&"b".repeat(40)));
        let err = verify_manifest(&dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect_err("carried-forward bytes must not replay under the new commit");
        assert!(matches!(err, BridgeGateError::PlatformStale { .. }), "got {err:?}");

        platform_provenance_manifest(&dir, None);
        let err = verify_manifest(&dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect_err("a platform that does not say what it was built from fails closed");
        assert!(matches!(err, BridgeGateError::ManifestProvenance { .. }), "got {err:?}");

        platform_provenance_manifest(&dir, Some(&"a".repeat(40)));
        verify_manifest(&dir, TRUSTIR_MANIFEST_SCHEMA, true)
            .expect("bytes built from the manifest's own commit are admitted");
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn source_reuse_binds_the_exact_captured_manifests() {
        let root = std::env::temp_dir().join(format!("bridge-reuse-capture-{}", std::process::id()));
        let ir = root.join("ir");
        let core = root.join("core");
        std::fs::create_dir_all(&ir).unwrap();
        std::fs::create_dir_all(&core).unwrap();
        platform_provenance_manifest(&ir, Some(&"a".repeat(40)));
        let mut ir_b = std::fs::read_to_string(ir.join("MANIFEST.toml")).unwrap();
        ir_b.push_str("\n[source_reuse]\nschema='binding-test'\n");
        std::fs::write(ir.join("MANIFEST.toml"), &ir_b).unwrap();
        let core_b = format!("schema='{LEAN_CORE_MANIFEST_SCHEMA}'\n[provenance]\nlean_toolchain='x'\n[files]\n");
        std::fs::write(core.join("MANIFEST.toml"), &core_b).unwrap();
        let selected = trust_bridge_closure::source_reuse::Selection {
            trustir_commit: "c".repeat(40), clean_commit: "d".repeat(40), anchor_commit: "e".repeat(40),
            trustir_manifest_sha256: format!("{:x}", Sha256::digest(ir_b.as_bytes())),
            core_manifest_sha256: format!("{:x}", Sha256::digest(core_b.as_bytes())),
        };
        let ir_tree_b = verify_manifest(&ir, TRUSTIR_MANIFEST_SCHEMA, true).unwrap();
        let core_tree_b = verify_manifest(&core, LEAN_CORE_MANIFEST_SCHEMA, false).unwrap();
        assert!(bind_source_reuse(selected.clone(), &ir_tree_b, &core_tree_b).is_ok());
        // Capture A, then restore B. No timing or mathematical checker is
        // involved: the association must reject the retained A parse.
        for ir_a in [ir_b.replace(&"a".repeat(40), &"b".repeat(40)), ir_b.replace("binding-test", "changed-record")] {
            std::fs::write(ir.join("MANIFEST.toml"), ir_a).unwrap();
            let captured_a = verify_manifest(&ir, TRUSTIR_MANIFEST_SCHEMA, true).unwrap();
            std::fs::write(ir.join("MANIFEST.toml"), &ir_b).unwrap();
            assert!(bind_source_reuse(selected.clone(), &captured_a, &core_tree_b).is_err());
        }
        std::fs::write(core.join("MANIFEST.toml"), core_b.replace("='x'", "='changed'")).unwrap();
        let core_a = verify_manifest(&core, LEAN_CORE_MANIFEST_SCHEMA, false).unwrap();
        std::fs::write(core.join("MANIFEST.toml"), &core_b).unwrap();
        assert!(bind_source_reuse(selected, &ir_tree_b, &core_a).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn arm_table_covers_all_18_ops_in_semintbinop_order() {
        let ops: Vec<&str> = ARMS.iter().map(|a| a.op).collect();
        assert_eq!(
            ops,
            vec![
                "Add", "Sub", "Mul", "UDiv", "SDiv", "URem", "SRem", "FAdd", "FSub", "FMul",
                "FDiv", "FRem", "And", "Or", "Xor", "Shl", "LShr", "AShr"
            ]
        );
        let form_a = ARMS.iter().filter(|a| a.form == ArmForm::A).count();
        let guarded = ARMS.iter().filter(|a| a.form == ArmForm::BGuarded).count();
        assert_eq!(form_a, 5, "the five float arms are plain agreement");
        assert_eq!(guarded, 7, "the seven guarded arms carry their UB guards");
    }

    #[test]
    fn unop_arm_table_covers_the_3_bridged_ops_in_semintunop_order() {
        let ops: Vec<&str> = UNOP_ARMS.iter().map(|a| a.op).collect();
        assert_eq!(ops, vec!["Neg", "Not", "FNeg"], "CtPop is intentionally un-bridged");
        let form_a = UNOP_ARMS.iter().filter(|a| a.form == ArmForm::A).count();
        let form_b = UNOP_ARMS.iter().filter(|a| a.form == ArmForm::B).count();
        assert_eq!(form_a, 1, "FNeg is the one plain-agreement arm");
        assert_eq!(form_b, 2, "Neg and Not agree under the no-overflow/in-range side condition");
        assert_eq!(UNOP_UNBRIDGED.len(), 1, "CtPop is the one honestly un-bridged UnOp arm");
        assert_eq!(UNOP_UNBRIDGED[0].0, "CtPop");
    }

    #[test]
    fn overflow_value_arm_table_covers_all_6_op_signedness_combinations() {
        let combos: Vec<(&str, bool)> =
            OVERFLOW_VALUE_ARMS.iter().map(|a| (a.op, a.signed)).collect();
        assert_eq!(
            combos,
            vec![
                ("AddOverflow", false),
                ("SubOverflow", false),
                ("MulOverflow", false),
                ("AddOverflow", true),
                ("SubOverflow", true),
                ("MulOverflow", true),
            ],
            "VALUE is bridged for every (op, signedness) combination — it never depends on \
             whether Clean's safety-VC tier models that combination's FLAG"
        );
    }

    #[test]
    fn overflow_flag_arm_table_covers_all_6_int_combinations() {
        let combos: Vec<(&str, bool)> =
            OVERFLOW_FLAG_ARMS.iter().map(|a| (a.op, a.signed)).collect();
        assert_eq!(
            combos,
            vec![
                ("AddOverflow", false),
                ("SubOverflow", false),
                ("MulOverflow", false),
                ("AddOverflow", true),
                ("SubOverflow", true),
                ("MulOverflow", true),
            ],
            "all six generic Int flags have actual connecting statements"
        );
        let guarded = OVERFLOW_FLAG_ARMS.iter().filter(|a| a.form == ArmForm::BGuarded).count();
        assert_eq!(guarded, 1, "unsigned SubOverflow (Lemma 8) is the one guarded flag arm");
        assert!(OVERFLOW_FLAG_UNBRIDGED.is_empty(), "no generic Int overflow-flag residue");
    }

    #[test]
    fn icmp_arm_table_covers_all_10_ops_in_icmpop_order() {
        let ops: Vec<&str> = ICMP_ARMS.iter().map(|a| a.op).collect();
        assert_eq!(
            ops,
            vec!["Eq", "Ne", "Ult", "Ule", "Ugt", "Uge", "Slt", "Sle", "Sgt", "Sge"],
            "the 10 semICmp arms in ICmpOp enum order"
        );
        let unsigned = ICMP_ARMS.iter().filter(|a| a.kind == IcmpArmKind::Unsigned).count();
        let sign_indep =
            ICMP_ARMS.iter().filter(|a| a.kind == IcmpArmKind::SignIndependent).count();
        let signed = ICMP_ARMS.iter().filter(|a| a.kind == IcmpArmKind::Signed).count();
        assert_eq!(unsigned, 4, "Ult/Ule/Ugt/Uge — raw-operand Int.lt/Int.le");
        assert_eq!(sign_indep, 2, "Eq/Ne — sign-independent");
        assert_eq!(signed, 4, "Slt/Sle/Sgt/Sge — Int.lt/Int.le at toSigned images");
        assert!(
            ICMP_UNBRIDGED.is_empty(),
            "all 10 ICmp arms bridge — the signed arms are a genuine agreement at the \
             toSigned images, not a faked claim, so there is no honest residue"
        );
    }

    #[test]
    fn cast_arm_table_covers_the_3_integer_ops_in_castop_order() {
        let ops: Vec<&str> = CAST_ARMS.iter().map(|a| a.op).collect();
        assert_eq!(ops, vec!["Trunc", "ZExt", "SExt"], "the 3 bridged semCast integer arms");
        assert_eq!(
            CAST_UNBRIDGED.len(),
            14,
            "the 14 non-integer CastOp variants (float + pointer/closure) are honestly un-bridged"
        );
        let unbridged_ops: Vec<&str> = CAST_UNBRIDGED.iter().map(|(op, _)| *op).collect();
        assert_eq!(
            unbridged_ops,
            vec![
                "FPTrunc",
                "FPExt",
                "FPToUI",
                "FPToSI",
                "UIToFP",
                "SIToFP",
                "PtrToInt",
                "IntToPtr",
                "Bitcast",
                "PtrToPtr",
                "Transmute",
                "ReifyFnPointer",
                "FPToSISat",
                "FPToUISat",
            ],
            "3 bridged + 14 un-bridged = all 17 CastOp variants accounted for"
        );
    }

    #[test]
    fn stepinst_binop_arm_table_preserves_all_eighteen_operations() {
        let ops: Vec<&str> = STEPINST_BINOP_ARMS.iter().map(|a| a.op).collect();
        assert_eq!(ops, vec!["Add", "Sub", "Mul", "UDiv", "SDiv", "URem", "SRem"]);
        assert_eq!(ops.len() + STEPINST_BINOP_UNBRIDGED[0].0.split('/').count(), 18);
        assert_eq!(
            STEPINST_BINOP_UNBRIDGED.len(),
            1,
            "the other 11 semIntBinOp ops remain in the honest-residue entry"
        );
        assert_eq!(
            STEPINST_CATEGORIES_UNBRIDGED.len(),
            2,
            "the other 52 Inst variant categories are grouped in two honest-residue entries \
             (FCmp with no value bridge at all + 51 others with no value bridge at all — \
             UnOp/Overflow/ICmp/Cast are now stepInst-chained, EXTENSION 9)"
        );
    }

    #[test]
    fn stepinst_categories_arm_tables_cover_one_representative_op_each() {
        let unop_ops: Vec<&str> = STEPINST_UNOP_ARMS.iter().map(|a| a.op).collect();
        assert_eq!(unop_ops, vec!["Neg"], "the one bridged stepInst-UnOp arm");
        assert_eq!(
            STEPINST_UNOP_UNBRIDGED.len(),
            1,
            "Not/FNeg are grouped in one honest-residue entry"
        );
        assert_eq!(
            STEPINST_OVERFLOW_UNBRIDGED.len(),
            1,
            "the other 5 op×signedness combos are grouped in one honest-residue entry"
        );
        assert_eq!(
            STEPINST_ICMP_UNBRIDGED.len(),
            1,
            "the other 9 comparison ops are grouped in one honest-residue entry"
        );
        assert_eq!(
            STEPINST_CAST_UNBRIDGED.len(),
            1,
            "ZExt/SExt are grouped in one honest-residue entry"
        );
    }

    #[test]
    fn stepbranch_body_arm_table_covers_true_and_false_arms() {
        let guards: Vec<&str> = STEPBRANCH_BODY_ARMS.iter().map(|a| a.guard).collect();
        assert_eq!(guards, vec!["true", "false"], "the true(Add)/false(Sub) branch-body arms");
        assert_eq!(
            STEPBRANCH_BODY_UNBRIDGED.len(),
            8,
            "8 honest residue entries: Switch, nested/chained CondBrs, loops, the \
             integer-guard semCondBr arm, the interprocedural evaluator, multi-instruction \
             arm bodies, asymmetric arm shapes, non-BinOp arm bodies"
        );
    }

    // THE DATALOOP COMPOSED-CHAIN WALL REPRODUCER (permanent; run manually
    // after any clean pin bump with TRUST_DATALOOP_WALL_REPRO=1 under an
    // RSS watchdog — earlier reproduction scripts used 12GB/50min):
    // the 6 per-visit lemmas load cheaply (~15-21s each, ≤3GB); the
    // DATALOOP_COMPOSED_STEPS sequence then hits the measured clean wall —
    // `probe_self_id_at`, a ZERO-metavariable `@rfl` at a ground
    // fuel-6-from-empty statement with BYTE-IDENTICAL sides, is eagerly
    // normalized (>12GB RSS, watchdog-killed at ~180s; 2026-07-07). When a
    // clean pin makes probe_self_id_at cheap, the rest of the chain is
    // expected to land and the gate's DATALOOP section should be extended
    // to load DATALOOP_COMPOSED_STEPS and assert
    // `bridge_dataloop_counter_reaches_2`.
    //
    // `#[ignore]`d, so the default suite never OOMs by design; and without
    // TRUST_DATALOOP_WALL_REPRO=1 it panics with the recipe, so a bare
    // `--ignored` run cannot pass having reproduced nothing.
    #[test]
    #[ignore = "measurement driver: set TRUST_DATALOOP_WALL_REPRO=1 and run with --ignored \
                under an RSS watchdog"]
    fn dataloop_composed_wall_reproducer() {
        if std::env::var("TRUST_DATALOOP_WALL_REPRO").as_deref() != Ok("1") {
            panic!(
                "dataloop_composed_wall_reproducer is a reproducer and \
                 TRUST_DATALOOP_WALL_REPRO is not 1, so it reproduced nothing. Run, under an \
                 RSS watchdog (earlier runs used 12GB/50min): TRUST_DATALOOP_WALL_REPRO=1 \
                 targo --unverified test --manifest-path crates/Cargo.toml -p trust-clean \
                 --lib -- --ignored --exact \
                 trustir_bridge::tests::dataloop_composed_wall_reproducer --nocapture"
            );
        }
        let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
        let trustir_tree =
            verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
                .expect("manifest");
        let core_tree =
            verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
                .expect("core manifest");
        let mut env = Environment::default();
        env.ensure_native_reducers();
        let root_modules: Vec<String> =
            BRIDGE_ROOT_MODULES.iter().map(|s| (*s).to_string()).collect();
        load_verified_modules(&mut env, &root_modules, &trustir_tree, &core_tree).expect("closure import");
        load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).expect("bridge order instances");
        load_bridge_source(&mut env, PRELUDE_SRC).expect("prelude");

        let t_fixtures = std::time::Instant::now();
        match load_bridge_source(&mut env, DATALOOP_FIXTURES_SRC) {
            Ok(names) => eprintln!(
                "SCRATCH fixtures OK ({:.2}s): {names:?}",
                t_fixtures.elapsed().as_secs_f64()
            ),
            Err(e) => panic!("SCRATCH fixtures failed: {e}"),
        }

        for (label, src) in DATALOOP_VISITS {
            let t = std::time::Instant::now();
            match load_bridge_source(&mut env, src) {
                Ok(names) => {
                    eprintln!("SCRATCH {label} OK ({:.3}s): {names:?}", t.elapsed().as_secs_f64())
                }
                Err(e) => panic!("SCRATCH {label} FAILED ({:.3}s): {e}", t.elapsed().as_secs_f64()),
            }
        }

        for (label, src) in DATALOOP_COMPOSED_STEPS {
            let t = std::time::Instant::now();
            match load_bridge_source(&mut env, src) {
                Ok(names) => eprintln!(
                    "SCRATCH composed[{label}] OK ({:.3}s): {names:?}",
                    t.elapsed().as_secs_f64()
                ),
                Err(e) => panic!(
                    "SCRATCH composed[{label}] FAILED ({:.3}s): {e}",
                    t.elapsed().as_secs_f64()
                ),
            }
        }
        require_empty_axiom_deps(&env, "bridge_dataloop_counter_reaches_2_tower")
            .expect("tower axiom_deps must be empty");
        require_empty_axiom_deps(&env, "bridge_dataloop_counter_reaches_2")
            .expect("axiom_deps must be empty");
        eprintln!("SCRATCH axiom_deps empty: confirmed");

        for (label, src) in DATALOOP_FORGERY_PROBES {
            let t = std::time::Instant::now();
            match load_bridge_source(&mut env, src) {
                Ok(_) => panic!("SCRATCH forgery probe {label} WAS ACCEPTED — soundness bug"),
                Err(e) => eprintln!(
                    "SCRATCH forgery probe {label} correctly REJECTED ({:.3}s): {}",
                    t.elapsed().as_secs_f64(),
                    e.chars().take(200).collect::<String>()
                ),
            }
        }
    }
}

#[cfg(test)]
#[path = "trustir_bridge/manifest_binding_tests.rs"]
mod manifest_binding_tests;

#[cfg(test)]
#[path = "trustir_bridge/elab_result_tests.rs"]
mod elab_result_tests;

#[cfg(test)]
#[path = "trustir_bridge/notation_class_tests.rs"]
mod notation_class_tests;

#[path = "trustir_bridge/manifest_inputs.rs"]
mod manifest_inputs;
