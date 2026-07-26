// The MirSem object language as a Clean environment: the inductive datatypes
// for operands, rvalues, statements and conditions, and the `eval`/`exec`
// functions over them. Every later family builds terms in this environment, so
// a name minted here is part of the kernel-checked surface -- renaming one
// silently invalidates every proof term that references it.

use super::*;

// ---------------------------------------------------------------------------
// Small kernel-term builders (shared de-Bruijn convention with clean_ground.rs)
// ---------------------------------------------------------------------------
pub(super) fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

/// `Int` literal `n` → `Int.ofNat n` / `Int.negSucc (-n-1)` — IDENTICAL to
/// `clean_ground::int_lit_to_expr`, so the operand-adequacy statement compares the
/// MirSem evaluation against the exact term the reflection grounder produces.
pub(super) fn int_lit(n: i128) -> Expr {
    // Trust: EXACT ENCODING (2026-07-24) — `Expr::nat_lit_u128` covers the FULL
    // magnitude range. The former `as u64` was `n mod 2^64`, a SILENT TRUNCATION that
    // made this map NON-INJECTIVE and caused a demonstrated LIVE FALSE ACCEPT (see
    // `clean_ground::int_lit_to_expr`). Byte-identity with the other encoders is
    // PRESERVED, and so is every existing term: `BigNat::from_limbs` normalizes a
    // trailing zero limb back to `BigNat::Small`, so `nat_lit_u128(k) == nat_lit(k)`
    // for every `k <= u64::MAX` (asserted by `int_lit_encoders_agree_and_are_exact`).
    // `Int.negSucc` carries `|n| - 1`, which fits `u128` for every `i128` (including
    // `i128::MIN`, where `-n` is not representable).
    if n >= 0 {
        Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(n.unsigned_abs()))
    } else {
        Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(n.unsigned_abs() - 1))
    }
}

/// The type `Env = Nat → Int` (the parameter binding: index ↦ value).
pub(super) fn env_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), cst("Nat"), cst("Int"))
}

pub(super) fn int_ty() -> Expr {
    cst("Int")
}

pub(super) fn operand_ty() -> Expr {
    cst(MIRSEM_OPERAND)
}

pub(super) fn binop_ty() -> Expr {
    cst(MIRSEM_BINOP)
}

pub(super) fn rvalue_ty() -> Expr {
    cst(MIRSEM_RVALUE)
}

/// The grounded Int term for a binary op `Int.<op> a b` — IDENTICAL in head and
/// argument order to what `clean_ground::ground_int` produces for `Formula::Add /
/// Sub / Mul / Div / Rem` (`app2("Int.add", g(a), g(b))`, …). `Int.add`/`sub`/`mul`
/// are the prelude's real `Int.rec`/`Nat.rec` DEFINITIONS; `Int.div` and `Int.mod`
/// are the prelude's `Opaque` (native-reduced) constants — NONE is an `Axiom`, so
/// this term carries no non-foundational axiom (`axiom_deps` counts only
/// `ConstantKind::Axiom`). The `Div` head matches `ground_int`'s `F::Div(a,b) =>
/// app2("Int.div", g(a), g(b))` arm EXACTLY (clean_ground.rs), and — Trust:
/// witness-tier Rem arm — the `Rem` head matches `ground_int`'s `F::Rem(a,b) =>
/// app2("Int.mod", g(a), g(b))` arm EXACTLY (the TRUNCATED T-remainder, the same
/// `Int.mod` the M3 value-semantics three-way pinned against trust-ir's
/// `semIntBinOp .SRem` and rustc's `%`); both the eval-rvalue reduct and the
/// grounded RHS name the SAME opaque constant, so adequacy is `Eq.refl`
/// (congruence) without ever unfolding `Int.div`/`Int.mod` — division/remainder
/// SEMANTICS are not needed, only that both sides denote the same term.
pub(super) fn int_binop_expr(op: &SemBinOp, a: Expr, b: Expr) -> Expr {
    let head = match op {
        SemBinOp::Add => "Int.add",
        SemBinOp::Sub => "Int.sub",
        SemBinOp::Mul => "Int.mul",
        SemBinOp::Div => "Int.div",
        // Trust: witness-tier Rem arm — the TRUNCATED `Int.mod` (ground_int's F::Rem head).
        SemBinOp::Rem => "Int.mod",
        // Trust: BITWISE SHAPE LANE — the Opaque `Int.land`/`Int.lor`/`Int.xor`/
        // `Int.shiftLeft` heads, matching `ground_int`'s new `F::Pred(name, [a,b])`
        // arms EXACTLY (see `register_int_bitwise`'s doc for why these are
        // registered by MirSem itself rather than shared with the base prelude).
        SemBinOp::BitAnd => "Int.land",
        SemBinOp::BitOr => "Int.lor",
        SemBinOp::BitXor => "Int.xor",
        SemBinOp::Shl => "Int.shiftLeft",
        // Trust: M6 rung 6, UNSIGNED-Shr arm — the Opaque `Int.shiftRight`
        // head, matching `ground_int`'s matching `F::Pred` arm EXACTLY.
        SemBinOp::Shr => "Int.shiftRight",
    };
    Expr::apps(cst(head), [a, b])
}

/// Trust: CALL-THEN-PUREOP — the Bool-valued term for a comparison `SemCmpOp`
/// applied to two ALREADY-BUILT Int-valued exprs `a`/`b`. Built DIRECTLY by a Rust
/// `match` (mirrors [`int_binop_expr`]'s own direct-match construction — no
/// `CmpOp.rec` dispatch needed), reproducing the EXACT closed-form ground term
/// `register_eval_cond`'s `CmpOp.rec` minor premises reduce to for each op: `Lt`/`Le`
/// → `decide (Int.lt/le a b) (Int.decLt/decLe a b)`; `Eq` → `Int.beq a b`; `Ne` →
/// `Bool.not (Int.beq a b)`; `Gt`/`Ge` → the SWAPPED `Lt`/`Le` case. So this term is
/// DEFINITIONALLY the value `Trust.MirSem.eval_cond` produces for `Cmp op a b` once
/// `a`/`b` are the operands' own evaluated denotations — reusing ONLY the existing
/// prelude primitives (`decide`/`Int.lt`/`Int.le`/`Int.beq`/`Bool.not`/`Int.decLt`/
/// `Int.decLe`, all used elsewhere in this file with proven-empty axiom residue), no
/// new declaration.
pub(crate) fn cmp_bool_expr(op: SemCmpOp, a: Expr, b: Expr) -> Expr {
    let decide_lt = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.lt"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLt"), [x, y]),
            ],
        )
    };
    let decide_le = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.le"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLe"), [x, y]),
            ],
        )
    };
    match op {
        SemCmpOp::Lt => decide_lt(a, b),
        SemCmpOp::Le => decide_le(a, b),
        SemCmpOp::Eq => Expr::apps(cst("Int.beq"), [a, b]),
        SemCmpOp::Ne => Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [a, b])),
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED operands (matches
        // `register_eval_cond`'s `gt_case`/`ge_case`).
        SemCmpOp::Gt => decide_lt(b, a),
        SemCmpOp::Ge => decide_le(b, a),
    }
}

/// Trust: CALL-THEN-PUREOP — encode a Bool-valued expr as 0/1 on the `Int` carrier:
/// the SAME "a Rust `bool` is modeled by the opaque Int carrier, 0/1 by convention"
/// idiom the call-spine increment's Bool-dest/ret widening already documents (see
/// `sem_call_return_of_mir`'s `local_is_int_or_bool` comment). Built via the
/// STANDARD `Bool.rec` eliminator, ctor order (false, true) — the EXACT idiom
/// `register_set` already uses to dispatch `Nat.beq` (see its doc). `Bool.rec` is a
/// prelude definition, so this carries no new axiom.
pub(crate) fn bool_as_int(b: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Bool"), int_ty());
    // @Bool.rec.{1} (λ_.Int) (false-case = 0) (true-case = 1) b
    Expr::apps(bool_rec, [motive, int_lit(0), int_lit(1), b])
}

// ---------------------------------------------------------------------------
// Step 1 — the `Trust.MirSem.Operand` inductive and `eval`
// ---------------------------------------------------------------------------
/// Register the `Trust.MirSem.Operand` inductive in `env` (idempotent):
///
/// ```text
/// inductive Operand : Type where
///   | Var      : Nat     → Operand
///   | Const    : Int     → Operand
///   | Move     : Operand → Operand
///   | Index    : Operand → Operand → Operand     -- ADDITIVE (slice-element `s[i]`)
///   | Len      : Operand → Operand               -- ADDITIVE (slice length `s.len()`)
///   | PreOpNot : Operand → Operand               -- pure `!s` call argument
///   | PreOpNeg : Operand → Operand               -- pure `-s` call argument
/// ```
///
/// Built on the prelude's axiom-free `Nat` / `Int` inductives, so the inductive's
/// transitive axiom closure is `⊆ {propext, Quot.sound, Classical.choice}`. Returns
/// `Ok(())` if the inductive is present after the call (registered or already there).
///
/// `Var`/`Const`/`Move` are the original constructors (#0/#1/#2, BYTE-IDENTICAL).
/// `Index` is the ADDITIVE FOURTH constructor, RECURSIVE in both arguments (the
/// slice operand and the index operand) — modeling a slice-element access `s[i]`.
/// Adding it does NOT change `Var`/`Const`/`Move` (same constructors, same types);
/// the auto-derived recursor simply gains a fourth minor premise (`Index` case) that
/// existing `Var`/`Const`/`Move`-only reductions ignore, so every prior operand
/// certificate stays def-eq.
pub(super) fn register_operand_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_OPERAND);
    if env.get_inductive(&name).is_some() {
        return Ok(()); // already registered this session
    }
    let bd = || BinderData::from(BinderInfo::Default);

    // Constructor arrows: each ends in the inductive head `Operand` (de-Bruijn: the
    // recursive `Move` field references `Operand` the constant, not a bound var,
    // since `num_params = 0`).
    let var_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_VAR),
        type_: Expr::pi(bd(), cst("Nat"), operand_ty()),
    };
    let const_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_CONST),
        type_: Expr::pi(bd(), cst("Int"), operand_ty()),
    };
    let move_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_MOVE),
        type_: Expr::pi(bd(), operand_ty(), operand_ty()),
    };
    // Index : Operand → Operand → Operand — recursive in BOTH fields (the slice and
    // the index operand). The auto-derived recursor threads an induction hypothesis
    // through each, exactly like `Cond.And`.
    let index_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_INDEX),
        type_: Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), operand_ty())),
    };
    // Len : Operand → Operand — recursive in its single field (the slice). The
    // recursor threads one induction hypothesis, exactly like `Move`.
    let len_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_LEN),
        type_: Expr::pi(bd(), operand_ty(), operand_ty()),
    };
    // The pure pre-operation constructors are appended after every existing
    // constructor, preserving all prior constructor indices and reductions.
    let preop_not_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_PREOP_NOT),
        type_: Expr::pi(bd(), operand_ty(), operand_ty()),
    };
    let preop_neg_ctor = Constructor {
        name: Name::from_string(MIRSEM_OPERAND_PREOP_NEG),
        type_: Expr::pi(bd(), operand_ty(), operand_ty()),
    };

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                var_ctor,
                const_ctor,
                move_ctor,
                index_ctor,
                len_ctor,
                preop_not_ctor,
                preop_neg_ctor,
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(Operand): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.eval : Env → Operand → Int` (idempotent), defined by the
/// operand recursor:
///
/// ```text
/// eval (e : Env) : Operand → Int
///   | Var idx   => e idx
///   | Const c   => c
///   | Move src  => eval e src   -- via the recursor's IH on the Move field
/// ```
///
/// Register `Trust.MirSem.idx_elem : Int → Int → Int` (idempotent) as a
/// `Declaration::Opaque` — the UNINTERPRETED total slice-element selector. The body
/// is a type-correct placeholder (`λ _ _. Int.ofNat 0`) the kernel NEVER unfolds
/// (`Opaque`-kind constants do not δ-reduce in `whnf`/`is_def_eq`), so two terms
/// `idx_elem a b` and `idx_elem a' b'` are def-eq IFF `a ≡ a'` and `b ≡ b'` —
/// i.e. `idx_elem` behaves as a fresh uninterpreted function symbol. EXACTLY the
/// `Int.div`/`Int.mod` treatment (`data_types_arithmetic.rs`): `Opaque` is NOT a
/// `ConstantKind::Axiom`, so a term referencing `idx_elem` gains NO axiom dependency.
pub(super) fn register_idx_elem(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    // idx_elem : Int → Int → Int — placeholder `λ (_ _ : Int). Int.ofNat 0`.
    if env.get_const(&Name::from_string(MIRSEM_IDX_ELEM)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
        let placeholder = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), int_lit(0)));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(MIRSEM_IDX_ELEM),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(idx_elem): {e:?}"))?;
    }
    // slice_len : Int → Int — placeholder `λ (_ : Int). Int.ofNat 0`.
    if env.get_const(&Name::from_string(MIRSEM_SLICE_LEN)).is_none() {
        let ty = Expr::pi(bd(), int_ty(), int_ty());
        let placeholder = Expr::lam(bd(), int_ty(), int_lit(0));
        env.add_decl(Declaration::Opaque {
            name: Name::from_string(MIRSEM_SLICE_LEN),
            level_params: vec![],
            type_: ty,
            value: placeholder,
        })
        .map_err(|e| format!("add_decl(slice_len): {e:?}"))?;
    }
    Ok(())
}

/// The recursor `Operand.rec.{1}` takes: the motive `λ_:Operand. Int`, then one
/// minor premise per constructor (in declaration order: Var, Const, Move, Index,
/// Len, PreOpNot, PreOpNeg). Recursive unary cases take their field and its `Int`
/// induction hypothesis; Index takes both fields and both hypotheses.
/// Because the codomain `Int` does not depend on the scrutinee, the motive is
/// constant (a non-dependent recursor use) — exactly an `Operand → Int` fold.
pub(super) fn register_eval(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EVAL);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);

    // eval : Env → Operand → Int
    let eval_ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), operand_ty(), int_ty()));

    // The recursor instantiated at the motive's universe. The motive lands in
    // `Int : Type`, so the recursor is at `Sort 1` ⇒ Level 1 (`Level::succ zero`).
    let operand_rec =
        Expr::const_(Name::from_string(MIRSEM_OPERAND_REC), vec![Level::succ(Level::zero())]);

    // Inside `λ(e:Env). λ(op:Operand). …` de-Bruijn depth-2 context:
    //   bvar(0) = op, bvar(1) = e.
    // The recursor minor premises are themselves under their own field binders, so
    // each is built relative to its own local depth; references to `e` must account
    // for the binders introduced inside the case.

    // motive : λ(_ : Operand) → Int   (constant codomain; non-dependent fold)
    let motive = Expr::lam(bd(), operand_ty(), int_ty());

    // Var case: λ(idx : Nat). e idx
    //   under this case's binder, idx = bvar(0); `e` is lifted past op + idx:
    //     idx = bvar(0), op = bvar(1), e = bvar(2).
    let var_case = {
        let e_ref = Expr::bvar(2); // e, lifted past op + idx
        let idx_ref = Expr::bvar(0); // idx
        Expr::lam(bd(), cst("Nat"), Expr::app(e_ref, idx_ref))
    };

    // Const case: λ(c : Int). c
    //   c = bvar(0).
    let const_case = Expr::lam(bd(), int_ty(), Expr::bvar(0));

    // Move case: λ(src : Operand). λ(ih : Int). ih
    //   the IH `ih` is exactly `eval e src` supplied by the recursor, so returning
    //   it realizes `eval (Move src) = eval e src`. src = bvar(1), ih = bvar(0).
    let move_case = Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(0)));

    // ADDITIVE Index case (the new minor premise the recursor gains for
    // `Index : Operand → Operand → Operand`). A recursive ctor with two recursive
    // fields binds the two fields THEN the two induction hypotheses (the `Cond.And`
    // convention): λ(s:Operand). λ(i:Operand). λ(ih_s:Int). λ(ih_i:Int).
    // idx_elem ih_s ih_i. With the constant `Int` motive the IHs ARE `eval e s` /
    // `eval e i`, so the arm computes `idx_elem (eval e s) (eval e i)` — exactly what
    // `ground_int(Select(s,i))` emits. de-Bruijn at the body:
    //   ih_i = bvar(0), ih_s = bvar(1), i = bvar(2), s = bvar(3).
    let index_case = {
        let body = Expr::apps(cst(MIRSEM_IDX_ELEM), [Expr::bvar(1), Expr::bvar(0)]);
        Expr::lam(
            bd(),
            operand_ty(),
            Expr::lam(
                bd(),
                operand_ty(),
                Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
            ),
        )
    };

    // ADDITIVE Len case (the new minor premise for `Len : Operand → Operand`). One
    // recursive field, so it binds the field THEN its IH (like `Move`):
    // λ(s:Operand). λ(ih_s:Int). slice_len ih_s. With the constant `Int` motive the IH
    // is `eval e s`, so the arm computes `slice_len (eval e s)` — exactly what
    // `ground_int` emits for the length term. s = bvar(1), ih_s = bvar(0).
    let len_case = {
        let body = Expr::app(cst(MIRSEM_SLICE_LEN), Expr::bvar(0));
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), body))
    };

    // PreOpNot: λ(_s). λ(ih_s). Int.xor ih_s (-1). The constant motive makes
    // `ih_s` definitionally equal to `eval e s`.
    let preop_not_case = {
        let body = Expr::apps(cst("Int.xor"), [Expr::bvar(0), int_lit(-1)]);
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), body))
    };

    // PreOpNeg: λ(_s). λ(ih_s). Int.sub 0 ih_s.
    let preop_neg_case = {
        let zero = Expr::app(cst("Int.ofNat"), Expr::nat_lit(0));
        let body = Expr::apps(cst("Int.sub"), [zero, Expr::bvar(0)]);
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), body))
    };

    // All additive minors follow the unchanged Var/Const/Move prefix.
    let rec_app = Expr::apps(
        operand_rec,
        [
            motive,
            var_case,
            const_case,
            move_case,
            index_case,
            len_case,
            preop_not_case,
            preop_neg_case,
            Expr::bvar(0),
        ],
    );
    // λ(e : Env). λ(op : Operand). rec_app
    let eval_val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), operand_ty(), rec_app));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: eval_ty,
        value: eval_val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(eval): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 1B — the `Trust.MirSem.BinOp` / `Rvalue` inductives and `eval_rvalue`
// ---------------------------------------------------------------------------
/// Register the `Trust.MirSem.BinOp` inductive (idempotent):
///
/// ```text
/// inductive BinOp : Type where
///   | Add : BinOp
///   | Sub : BinOp
///   | Mul : BinOp
///   | Div : BinOp
///   | Rem : BinOp
///   | BitAnd : BinOp   -- Trust: BITWISE SHAPE LANE
///   | BitOr : BinOp
///   | BitXor : BinOp
///   | Shl : BinOp
/// ```
///
/// An enumeration (all constructors nullary), so its transitive axiom closure is
/// `⊆ {propext, Quot.sound, Classical.choice}`. `Rem` — Trust: witness-tier Rem
/// arm — is the FIFTH constructor (grounds to the prelude's `Opaque` TRUNCATED
/// `Int.mod`, exactly as `Div` grounds to the `Opaque` `Int.div`). Trust:
/// BITWISE SHAPE LANE (2026-07-08) — `BitAnd`/`BitOr`/`BitXor`/`Shl` are FOUR
/// more nullary constructors (sixth through ninth), grounding to MirSem's OWN
/// `Int.land`/`Int.lor`/`Int.xor`/`Int.shiftLeft` Opaque placeholders
/// (`register_int_bitwise`) — the same wrapped-semantics denotations
/// `trustir_bridge.rs`'s kernel bridge already proves. Each new nullary
/// constructor keeps the enumeration axiom-free, and the auto-derived recursor
/// simply gains one more minor premise that every existing `Add`/`Sub`/`Mul`/
/// `Div`/`Rem` ι-reduction ignores, so every prior binop certificate stays
/// def-eq.
pub(super) fn register_binop_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_BINOP);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: binop_ty() };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                ctor(MIRSEM_BINOP_ADD),
                ctor(MIRSEM_BINOP_SUB),
                ctor(MIRSEM_BINOP_MUL),
                ctor(MIRSEM_BINOP_DIV),
                // Trust: witness-tier Rem arm — the fifth (nullary) constructor.
                ctor(MIRSEM_BINOP_REM),
                // Trust: BITWISE SHAPE LANE — four more nullary constructors,
                // APPENDED after `Rem` so every existing `BinOp.rec` minor-premise
                // POSITION (Add/Sub/Mul/Div/Rem) is unchanged — the SAME additive
                // discipline `Rem` itself landed under.
                ctor(MIRSEM_BINOP_BITAND),
                ctor(MIRSEM_BINOP_BITOR),
                ctor(MIRSEM_BINOP_BITXOR),
                ctor(MIRSEM_BINOP_SHL),
                // Trust: M6 rung 6, UNSIGNED-Shr arm — the tenth (nullary)
                // constructor, APPENDED after `Shl` so every existing
                // `BinOp.rec` minor-premise POSITION is unchanged — the SAME
                // additive discipline `Rem` and the bitwise four landed under.
                ctor(MIRSEM_BINOP_SHR),
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(BinOp): {e:?}"))?;
    Ok(())
}

/// Register the `Trust.MirSem.Rvalue` inductive (idempotent):
///
/// ```text
/// inductive Rvalue : Type where
///   | Use : Operand → Rvalue
///   | Bin : BinOp → Operand → Operand → Rvalue
///   | Sel : Cond → Operand → Operand → Rvalue
///   | Cmp : CmpOp → Rvalue → Rvalue → Rvalue         -- ADDITIVE (COMPARE-AS-VALUE)
/// ```
///
/// `Use`/`Bin`/`Sel`'s fields are all OTHER inductives (`Operand`, `BinOp`, `Cond`), so
/// none of those THREE is recursive. `Cmp` is the ADDITIVE fourth constructor: its
/// `CmpOp` field is non-recursive (like `Sel`'s `Cond`), but its TWO `Rvalue` fields
/// ARE recursive (the SAME `Cond.And : Cond → Cond → Cond` pattern already
/// established) — so the auto-derived recursor's `Cmp` minor premise gains TWO
/// induction hypotheses (`eval_rvalue e ra`/`eval_rvalue e rb`), while `Use`/`Bin`/
/// `Sel`'s minors are UNCHANGED (no IH, since none of their fields is `Rvalue`) —
/// every prior `Use`/`Bin`/`Sel` reduction stays byte-identical. The `Sel` arm
/// references `Cond`, so `Cond` must be registered FIRST (the `mirsem_env` order
/// places `CmpOp`/`Cond`/`eval_cond`/`iteI` before `Rvalue`) — `Cmp`'s `CmpOp` field
/// reuses that SAME already-registered inductive. Requires `Operand`, `BinOp`,
/// `CmpOp`, and `Cond` already registered.
pub(super) fn register_rvalue_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_RVALUE);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // Use : Operand → Rvalue
    let use_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_USE),
        type_: Expr::pi(bd(), operand_ty(), rvalue_ty()),
    };
    // Bin : BinOp → Operand → Operand → Rvalue
    let bin_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_BIN),
        type_: Expr::pi(
            bd(),
            binop_ty(),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), rvalue_ty())),
        ),
    };
    // Sel : Cond → Operand → Operand → Rvalue  (the conditional-update `if c then a else b`).
    let sel_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_SEL),
        type_: Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), rvalue_ty())),
        ),
    };
    // Trust: COMPARE-AS-VALUE — Cmp : CmpOp → Rvalue → Rvalue → Rvalue. RECURSIVE in
    // the two `Rvalue` fields (the kernel's `add_inductive` detects this from the
    // field types matching the inductive being defined, the SAME mechanism
    // `Cond.And : Cond → Cond → Cond` already exercises).
    let cmp_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_CMP),
        type_: Expr::pi(
            bd(),
            cst(MIRSEM_CMPOP),
            Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), rvalue_ty())),
        ),
    };
    // Trust: BOOL-CONNECTIVE (BitOr-on-Bool multi-join) — Or/And : Rvalue → Rvalue →
    // Rvalue. RECURSIVE in BOTH fields (the SAME mechanism `Cmp`'s two `Rvalue`
    // fields already exercise).
    let or_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_OR),
        type_: Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), rvalue_ty())),
    };
    let and_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_AND),
        type_: Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), rvalue_ty())),
    };
    // Trust: BIT_FIELD NESTED-RVALUE — BitBin : BinOp → Rvalue → Rvalue → Rvalue.
    // RECURSIVE in the two `Rvalue` fields (the SAME mechanism `Cmp`'s two
    // `Rvalue` fields already exercise), op-parameterized like `Cmp`'s `CmpOp`
    // field (reusing the EXISTING `BinOp` inductive rather than a new enum).
    let bitbin_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_BITBIN),
        type_: Expr::pi(
            bd(),
            binop_ty(),
            Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), rvalue_ty())),
        ),
    };
    // Trust: W-CMP-DISCR — ArithBin : BinOp → Rvalue → Rvalue → Rvalue. The
    // ARITHMETIC twin of `BitBin` (SAME signature), RECURSIVE in the two
    // `Rvalue` fields — the `signum` sign-value `(self>0) - (self<0)` combines
    // two computed `Cmp` sub-rvalues with a `Sub`. EIGHTH (last) constructor, so
    // constructors #0..#6 keep their tags and every prior certificate stays
    // def-eq.
    let arithbin_ctor = Constructor {
        name: Name::from_string(MIRSEM_RVALUE_ARITHBIN),
        type_: Expr::pi(
            bd(),
            binop_ty(),
            Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), rvalue_ty())),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                use_ctor,
                bin_ctor,
                sel_ctor,
                cmp_ctor,
                or_ctor,
                and_ctor,
                bitbin_ctor,
                arithbin_ctor,
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(Rvalue): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.eval_rvalue : Env → Rvalue → Int` (idempotent):
///
/// ```text
/// eval_rvalue (e : Env) : Rvalue → Int
///   | Use op        => eval e op
///   | Bin op a b    => match op with
///                        | Add => Int.add (eval e a) (eval e b)
///                        | Sub => Int.sub (eval e a) (eval e b)
///                        | Mul => Int.mul (eval e a) (eval e b)
///                        | Div => Int.div (eval e a) (eval e b)
///                        | Rem => Int.mod (eval e a) (eval e b)
///   | Sel c a b     => iteI e c (eval e a) (eval e b)   -- if c then a else b
/// ```
///
/// Built by the `Rvalue.rec` fold; the `Bin` case dispatches the `BinOp` field with
/// `BinOp.rec` (now FIVE minor premises — one per constructor). The codomain `Int`
/// is constant (non-dependent fold). The grounded shape `Int.add (eval e a)
/// (eval e b)` is EXACTLY `ground_int`'s output for `Formula::Add`, the `Div` case
/// `Int.div (eval e a) (eval e b)` is EXACTLY `ground_int`'s `F::Div` arm, and —
/// Trust: witness-tier Rem arm — the `Rem` case `Int.mod (eval e a) (eval e b)` is
/// EXACTLY `ground_int`'s `F::Rem` arm (the TRUNCATED T-remainder), so adequacy is
/// `Eq.refl` by ι-reduction. `Int.div`/`Int.mod` are the prelude's `Opaque`
/// constants (native-reduced), never unfolded by the kernel here — adequacy
/// needs only that both the eval reduct and the grounded RHS name them.
pub(super) fn register_eval_rvalue(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EVAL_RVALUE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let lvl1 = || vec![Level::succ(Level::zero())];

    // eval_rvalue : Env → Rvalue → Int
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), rvalue_ty(), int_ty()));

    let rvalue_rec = Expr::const_(Name::from_string(MIRSEM_RVALUE_REC), lvl1());
    let binop_rec = Expr::const_(Name::from_string(MIRSEM_BINOP_REC), lvl1());
    let eval = cst(MIRSEM_EVAL);

    // motive : λ(_ : Rvalue) → Int   (constant codomain; non-dependent fold)
    let motive = Expr::lam(bd(), rvalue_ty(), int_ty());

    // Use case: λ(op : Operand). eval e op
    //   under this case's binder: op = bvar(0), rv = bvar(1), e = bvar(2).
    let use_case = {
        let e_ref = Expr::bvar(2); // e, lifted past rv + op
        let op_ref = Expr::bvar(0); // op
        Expr::lam(bd(), operand_ty(), Expr::apps(eval.clone(), [e_ref, op_ref]))
    };

    // Bin case: λ(op:BinOp). λ(a:Operand). λ(b:Operand).
    //              BinOp.rec.{1} (λ_:BinOp.Int) (Int.add (eval e a) (eval e b))
    //                                            (Int.sub …) (Int.mul …) (Int.div …)
    //                                            (Int.mod …) op
    //   under the three case binders: b=bvar(0), a=bvar(1), op=bvar(2), rv=bvar(3),
    //   e=bvar(4). Inside the BinOp.rec minor premises (no further binders — each
    //   BinOp ctor is nullary) the same de-Bruijn depth holds.
    let bin_case = {
        let e_ref = || Expr::bvar(4);
        let a_ref = || Expr::bvar(1);
        let b_ref = || Expr::bvar(0);
        let eval_a = || Expr::apps(eval.clone(), [e_ref(), a_ref()]);
        let eval_b = || Expr::apps(eval.clone(), [e_ref(), b_ref()]);
        let binop_motive = Expr::lam(bd(), binop_ty(), int_ty());
        let add_case = int_binop_expr(&SemBinOp::Add, eval_a(), eval_b());
        let sub_case = int_binop_expr(&SemBinOp::Sub, eval_a(), eval_b());
        let mul_case = int_binop_expr(&SemBinOp::Mul, eval_a(), eval_b());
        let div_case = int_binop_expr(&SemBinOp::Div, eval_a(), eval_b());
        // Trust: witness-tier Rem arm — the fifth minor premise (Opaque `Int.mod`).
        let rem_case = int_binop_expr(&SemBinOp::Rem, eval_a(), eval_b());
        // Trust: BITWISE SHAPE LANE — four more minor premises (sixth through
        // ninth), APPENDED after `rem_case` — the SAME additive discipline `Rem`
        // itself landed under. Each is the Opaque `Int.land`/`Int.lor`/`Int.xor`/
        // `Int.shiftLeft` applied to the ALREADY-EVALUATED operands, EXACTLY what
        // `int_binop_expr` (shared with `denotation()`) produces for the SAME op.
        let bitand_case = int_binop_expr(&SemBinOp::BitAnd, eval_a(), eval_b());
        let bitor_case = int_binop_expr(&SemBinOp::BitOr, eval_a(), eval_b());
        let bitxor_case = int_binop_expr(&SemBinOp::BitXor, eval_a(), eval_b());
        let shl_case = int_binop_expr(&SemBinOp::Shl, eval_a(), eval_b());
        // Trust: M6 rung 6, UNSIGNED-Shr arm — the tenth minor premise,
        // APPENDED after `shl_case` (the same additive discipline as above).
        let shr_case = int_binop_expr(&SemBinOp::Shr, eval_a(), eval_b());
        // BinOp.rec.{1} motive add_case sub_case mul_case div_case rem_case
        //   bitand_case bitor_case bitxor_case shl_case shr_case op
        let dispatch = Expr::apps(
            binop_rec,
            [
                binop_motive,
                add_case,
                sub_case,
                mul_case,
                div_case,
                rem_case,
                bitand_case,
                bitor_case,
                bitxor_case,
                shl_case,
                shr_case,
                Expr::bvar(2),
            ],
        );
        Expr::lam(
            bd(),
            binop_ty(),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), dispatch)),
        )
    };

    // Sel case: λ(c:Cond). λ(a:Operand). λ(b:Operand). iteI e c (eval e a) (eval e b)
    //   — the CONDITIONAL-UPDATE `if c then a else b`. `iteI e c t f` is the
    //   `Bool.rec`-driven if-then-else over already-evaluated `Int` arms, so this
    //   grounds to `if eval_cond e c then eval e a else eval e b`. Under the three case
    //   binders: b=bvar(0), a=bvar(1), c=bvar(2), rv=bvar(3), e=bvar(4).
    let sel_case = {
        let e_ref = || Expr::bvar(4);
        let eval_a = Expr::apps(eval.clone(), [e_ref(), Expr::bvar(1)]);
        let eval_b = Expr::apps(eval.clone(), [e_ref(), Expr::bvar(0)]);
        // iteI e c (eval e a) (eval e b)
        let ite = Expr::apps(cst(MIRSEM_ITE_I), [e_ref(), Expr::bvar(2), eval_a, eval_b]);
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), ite)),
        )
    };
    // Trust: COMPARE-AS-VALUE — Cmp case: λ(op:CmpOp). λ(ra:Rvalue). λ(rb:Rvalue).
    //   λ(iha:Int). λ(ihb:Int). bool_as_int (CmpOp.rec (λ_.Bool) <lt> <le> <eq> <ne>
    //   <gt> <ge> op), dispatching over the ALREADY-COMPUTED induction hypotheses
    //   `iha`/`ihb` (`eval_rvalue e ra`/`eval_rvalue e rb`, SUPPLIED by the recursor
    //   for the two recursive `Rvalue` fields — never re-evaluated here). The
    //   per-op dispatch is the KERNEL-SIDE twin of the Rust `cmp_bool_expr` helper
    //   (itself documented as reproducing `register_eval_cond`'s OWN `CmpOp.rec`
    //   minor premises), applied to Int VALUES instead of `Operand` evaluations;
    //   the final `bool_as_int` wrap is the SAME `Bool.rec (λ_.Int) 0 1 …` idiom
    //   `bool_as_int` builds Rust-side. Under the five case binders: ihb=bvar(0),
    //   iha=bvar(1), rb=bvar(2), ra=bvar(3), op=bvar(4), rv=bvar(5), e=bvar(6).
    let cmp_case = {
        let iha = || Expr::bvar(1);
        let ihb = || Expr::bvar(0);
        let decide_lt = |x: Expr, y: Expr| {
            Expr::apps(
                cst("decide"),
                [
                    Expr::apps(cst("Int.lt"), [x.clone(), y.clone()]),
                    Expr::apps(cst("Int.decLt"), [x, y]),
                ],
            )
        };
        let decide_le = |x: Expr, y: Expr| {
            Expr::apps(
                cst("decide"),
                [
                    Expr::apps(cst("Int.le"), [x.clone(), y.clone()]),
                    Expr::apps(cst("Int.decLe"), [x, y]),
                ],
            )
        };
        let lt_case = decide_lt(iha(), ihb());
        let le_case = decide_le(iha(), ihb());
        let eq_case = Expr::apps(cst("Int.beq"), [iha(), ihb()]);
        let ne_case = Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [iha(), ihb()]));
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED (matches `register_eval_cond`).
        let gt_case = decide_lt(ihb(), iha());
        let ge_case = decide_le(ihb(), iha());
        let cmpop_motive = Expr::lam(bd(), cst(MIRSEM_CMPOP), cst("Bool"));
        let cmpop_rec = Expr::const_(Name::from_string(MIRSEM_CMPOP_REC), lvl1());
        let dispatch = Expr::apps(
            cmpop_rec,
            [cmpop_motive, lt_case, le_case, eq_case, ne_case, gt_case, ge_case, Expr::bvar(4)],
        );
        let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let bool_rec =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let body = Expr::apps(bool_rec, [int_motive, int_lit(0), int_lit(1), dispatch]);
        Expr::lam(
            bd(),
            cst(MIRSEM_CMPOP),
            Expr::lam(
                bd(),
                rvalue_ty(),
                Expr::lam(
                    bd(),
                    rvalue_ty(),
                    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
                ),
            ),
        )
    };
    // Trust: BOOL-CONNECTIVE (BitOr-on-Bool multi-join) — Or/And case: λ(ra:Rvalue).
    //   λ(rb:Rvalue). λ(iha:Int). λ(ihb:Int). bool_as_int (Bool.or/and (decide_bool
    //   iha) (decide_bool ihb)), dispatching over the ALREADY-COMPUTED induction
    //   hypotheses `iha`/`ihb` (`eval_rvalue e ra`/`eval_rvalue e rb`) — NO further
    //   evaluation needed, mirroring `cmp_case`'s OWN "no e_ref, only iha/ihb" shape.
    //   `iha`/`ihb` are GUARANTEED `bool_as_int`-encoded (0 or 1) by the RECOGNIZER's
    //   OWN invariant (`mir_operand_is_bool_typed` gates every operand this
    //   constructor is EVER built from to a genuinely `Ty::Bool` MIR value, whose
    //   OWN `eval_rvalue` reduct is therefore ALWAYS a `Cmp`/`Or`/`And`/bool-`Use`
    //   arm — every one of which already 0/1-encodes via this SAME `bool_as_int`
    //   idiom) — so `decide_bool n := Int.beq n 1` faithfully recovers the `Bool`.
    //   Under the four case binders: ihb=bvar(0), iha=bvar(1), rb=bvar(2), ra=bvar(3).
    // Trust: BOOL-CONNECTIVE — PURE ARITHMETIC on the 0/1 `Int` encoding, NOT a
    // `Bool.rec`/decide round-trip: `And a b := a * b` (1 only when BOTH are 1),
    // `Or a b := a + b - a*b` (inclusion-exclusion; 0 only when BOTH are 0) — both
    // ARE 0/1 whenever `iha`/`ihb` ARE (which the RECOGNIZER guarantees — see
    // `mir_operand_is_bool_typed`). This is DELIBERATE: an EARLIER design tried
    // `bool_as_int(Bool.or (Int.beq iha 1) (Int.beq ihb 1))` (decode-combine-
    // re-encode), which FAILS to kernel-check — `Int.beq (Bool.rec (λ_.Int) 0 1 X) 1`
    // does NOT definitionally reduce back to the NEUTRAL Bool `X` for an opaque
    // (non-literal) `X` (a genuine mathematical fact, not a free reduction), so it
    // is NOT def-eq to what the live grounder's `to_formula`/`ground_int` computes
    // (which never leaves Int-space at all for a `SemRvalue::Or`/`And`'s OWN
    // grounding — see `to_formula`'s `F::Sub(F::Add(..),F::Mul(..))`/`F::Mul(..)`
    // shape, reusing the ALREADY-grounded `Int.add`/`Int.sub`/`Int.mul` arms, no
    // NEW `ground_bool`/`ground_int` case needed). Pure arithmetic sidesteps the
    // mismatch entirely: `Int.mul`/`Int.add`/`Int.sub` are the SAME opaque prelude
    // primitives on BOTH sides, so `eval_rvalue`'s reduct is SYNTACTICALLY the same
    // term the live grounder emits.
    let and_case = {
        let iha = || Expr::bvar(1);
        let ihb = || Expr::bvar(0);
        let body = Expr::apps(cst("Int.mul"), [iha(), ihb()]);
        Expr::lam(
            bd(),
            rvalue_ty(),
            Expr::lam(
                bd(),
                rvalue_ty(),
                Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
            ),
        )
    };
    let or_case = {
        let iha = || Expr::bvar(1);
        let ihb = || Expr::bvar(0);
        let sum = Expr::apps(cst("Int.add"), [iha(), ihb()]);
        let prod = Expr::apps(cst("Int.mul"), [iha(), ihb()]);
        let body = Expr::apps(cst("Int.sub"), [sum, prod]);
        Expr::lam(
            bd(),
            rvalue_ty(),
            Expr::lam(
                bd(),
                rvalue_ty(),
                Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
            ),
        )
    };
    // Trust: BIT_FIELD NESTED-RVALUE — BitBin case: λ(op:BinOp). λ(ra:Rvalue).
    //   λ(rb:Rvalue). λ(iha:Int). λ(ihb:Int). BinOp.rec (λ_.Int) <add> <sub>
    //   <mul> <div> <rem> <bitand> <bitor> <bitxor> <shl> op — dispatching
    //   over the ALREADY-COMPUTED induction hypotheses `iha`/`ihb`
    //   (`eval_rvalue e ra`/`eval_rvalue e rb`, SUPPLIED by the recursor for
    //   the two recursive `Rvalue` fields), EXACT SAME `BinOp.rec` dispatch
    //   `bin_case` performs, with `iha`/`ihb` in place of `eval_a()`/
    //   `eval_b()` (no `e` reference needed at all — like `cmp_case`/
    //   `and_case`/`or_case`). Under the five case binders: ihb=bvar(0),
    //   iha=bvar(1), rb=bvar(2), ra=bvar(3), op=bvar(4) — matches `cmp_case`'s
    //   OWN five-binder depth convention exactly.
    let bitbin_case = {
        let iha = || Expr::bvar(1);
        let ihb = || Expr::bvar(0);
        let binop_motive = Expr::lam(bd(), binop_ty(), int_ty());
        let binop_rec2 = Expr::const_(Name::from_string(MIRSEM_BINOP_REC), lvl1());
        let add_case = int_binop_expr(&SemBinOp::Add, iha(), ihb());
        let sub_case = int_binop_expr(&SemBinOp::Sub, iha(), ihb());
        let mul_case = int_binop_expr(&SemBinOp::Mul, iha(), ihb());
        let div_case = int_binop_expr(&SemBinOp::Div, iha(), ihb());
        let rem_case = int_binop_expr(&SemBinOp::Rem, iha(), ihb());
        let bitand_case = int_binop_expr(&SemBinOp::BitAnd, iha(), ihb());
        let bitor_case = int_binop_expr(&SemBinOp::BitOr, iha(), ihb());
        let bitxor_case = int_binop_expr(&SemBinOp::BitXor, iha(), ihb());
        let shl_case = int_binop_expr(&SemBinOp::Shl, iha(), ihb());
        // Trust: M6 rung 6, UNSIGNED-Shr arm — the tenth minor premise (same
        // additive append as the `bin_case` table above).
        let shr_case = int_binop_expr(&SemBinOp::Shr, iha(), ihb());
        let dispatch = Expr::apps(
            binop_rec2,
            [
                binop_motive,
                add_case,
                sub_case,
                mul_case,
                div_case,
                rem_case,
                bitand_case,
                bitor_case,
                bitxor_case,
                shl_case,
                shr_case,
                Expr::bvar(4),
            ],
        );
        Expr::lam(
            bd(),
            binop_ty(),
            Expr::lam(
                bd(),
                rvalue_ty(),
                Expr::lam(
                    bd(),
                    rvalue_ty(),
                    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), dispatch)),
                ),
            ),
        )
    };
    // Trust: W-CMP-DISCR — ArithBin case: BYTE-IDENTICAL to `bitbin_case` (both
    // dispatch `BinOp.rec` over the two already-computed IHs via
    // `int_binop_expr`). The two constructors differ ONLY in their `to_formula`
    // reflection, not their operational reduct — so `eval_rvalue e (ArithBin Sub
    // ra rb)` reduces to `Int.sub (eval_rvalue e ra) (eval_rvalue e rb)`, the
    // SAME `Int.sub` term the live grounder emits for `F::Sub(ra, rb)`, and
    // adequacy closes reflexively. Under the five case binders: ihb=bvar(0),
    // iha=bvar(1), rb=bvar(2), ra=bvar(3), op=bvar(4) — the SAME depth as
    // `bitbin_case`.
    let arithbin_case = {
        let iha = || Expr::bvar(1);
        let ihb = || Expr::bvar(0);
        let binop_motive = Expr::lam(bd(), binop_ty(), int_ty());
        let binop_rec3 = Expr::const_(Name::from_string(MIRSEM_BINOP_REC), lvl1());
        let add_case = int_binop_expr(&SemBinOp::Add, iha(), ihb());
        let sub_case = int_binop_expr(&SemBinOp::Sub, iha(), ihb());
        let mul_case = int_binop_expr(&SemBinOp::Mul, iha(), ihb());
        let div_case = int_binop_expr(&SemBinOp::Div, iha(), ihb());
        let rem_case = int_binop_expr(&SemBinOp::Rem, iha(), ihb());
        let bitand_case = int_binop_expr(&SemBinOp::BitAnd, iha(), ihb());
        let bitor_case = int_binop_expr(&SemBinOp::BitOr, iha(), ihb());
        let bitxor_case = int_binop_expr(&SemBinOp::BitXor, iha(), ihb());
        let shl_case = int_binop_expr(&SemBinOp::Shl, iha(), ihb());
        let shr_case = int_binop_expr(&SemBinOp::Shr, iha(), ihb());
        let dispatch = Expr::apps(
            binop_rec3,
            [
                binop_motive,
                add_case,
                sub_case,
                mul_case,
                div_case,
                rem_case,
                bitand_case,
                bitor_case,
                bitxor_case,
                shl_case,
                shr_case,
                Expr::bvar(4),
            ],
        );
        Expr::lam(
            bd(),
            binop_ty(),
            Expr::lam(
                bd(),
                rvalue_ty(),
                Expr::lam(
                    bd(),
                    rvalue_ty(),
                    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), dispatch)),
                ),
            ),
        )
    };
    // Rvalue.rec.{1} motive use_case bin_case sel_case cmp_case or_case
    //   and_case bitbin_case arithbin_case rv
    let rec_app = Expr::apps(
        rvalue_rec,
        [
            motive,
            use_case,
            bin_case,
            sel_case,
            cmp_case,
            or_case,
            and_case,
            bitbin_case,
            arithbin_case,
            Expr::bvar(0),
        ],
    );
    // λ(e : Env). λ(rv : Rvalue). rec_app
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), rvalue_ty(), rec_app));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(eval_rvalue): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 1C — the `Trust.MirSem.Stmt` inductive and `exec`
// ---------------------------------------------------------------------------
/// Register the `Trust.MirSem.Stmt` inductive (idempotent):
///
/// ```text
/// inductive Stmt : Type where
///   | Assign : Nat → Rvalue → Stmt
/// ```
///
/// A single-constructor record over `Nat` (the assigned local index) and `Rvalue`.
/// Both fields are non-recursive (`Nat`, `Rvalue`), so the auto-derived recursor's
/// minor premise takes them with NO induction hypothesis. Requires `Rvalue` already
/// registered. We model the assignment *list* with the prelude's `List Stmt`, whose
/// `List.rec` fold drives `exec`.
pub(super) fn register_stmt_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STMT);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let assign_ctor = Constructor {
        name: Name::from_string(MIRSEM_STMT_ASSIGN),
        type_: Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), rvalue_ty(), cst(MIRSEM_STMT))),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![assign_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(Stmt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.set : Env → Nat → Int → Env` (idempotent):
///
/// ```text
/// set (e : Env) (i : Nat) (v : Int) : Env :=
///   fun (j : Nat) => @Bool.rec (fun _ => Int) (e j) v (Nat.beq i j)
/// ```
///
/// The point-wise env update: `set e i v` agrees with `e` everywhere except index
/// `i`, where it is `v`. Built from the prelude's `Nat.beq` (a native-reduced
/// decidable equality on `Nat` literals → `Bool.true`/`Bool.false`) dispatched by
/// `Bool.rec` (ctor order false, true ⇒ minors `(e j)` then `v`). For the closed
/// literal indices the SSA-temp-return lemma uses, `Nat.beq i i ι-reduces to
/// `Bool.true`, so `set e i v i` ι-reduces to `v` definitionally — the reduction
/// the adequacy witness rests on. `Nat.beq`/`Bool.rec` are prelude DEFINITIONS, so
/// `set` carries no non-foundational axiom.
pub(super) fn register_set(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_SET);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);

    // set : Env → Nat → Int → Env   (= Env → Nat → Int → (Nat → Int))
    let ty =
        Expr::pi(bd(), env_ty(), Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), env_ty())));

    // Bool.rec.{1} into Int (a Type-level motive ⇒ Sort 1).
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    // motive : λ(_ : Bool) → Int  (constant codomain).
    let bool_motive = Expr::lam(bd(), cst("Bool"), int_ty());

    // Inside `λ(e:Env). λ(i:Nat). λ(v:Int). λ(j:Nat). …` de-Bruijn:
    //   j = bvar(0), v = bvar(1), i = bvar(2), e = bvar(3).
    let e_ref = Expr::bvar(3);
    let i_ref = Expr::bvar(2);
    let v_ref = Expr::bvar(1);
    let j_ref = Expr::bvar(0);
    // Nat.beq i j  (native-reduces to Bool.true/Bool.false on literals).
    let beq = Expr::apps(cst("Nat.beq"), [i_ref, j_ref.clone()]);
    // false-case = e j  (index differs ⇒ original binding); true-case = v.
    let e_at_j = Expr::app(e_ref, j_ref);
    // @Bool.rec.{1} (λ_.Int) (e j) v (Nat.beq i j)
    let dispatch = Expr::apps(bool_rec, [bool_motive, e_at_j, v_ref, beq]);
    // λ(e).λ(i).λ(v).λ(j). dispatch
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), cst("Nat"), dispatch)),
        ),
    );

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(set): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.exec : Env → List Stmt → Env` (idempotent):
///
/// ```text
/// exec (e : Env) : List Stmt → Env :=        -- left-fold the env through the trace
///   @List.rec Stmt (fun _ => Env → Env)
///     (fun e' => e')                                              -- nil  : id
///     (fun (s : Stmt) (rest : List Stmt) (ih : Env → Env) (e' : Env) =>
///        ih (@Stmt.rec (fun _ => Env)
///              (fun (i : Nat) (R : Rvalue) => set e' i (eval_rvalue e' R)) s))
///     stmts e
/// ```
///
/// Threads the env LEFT-TO-RIGHT: `exec e (cons s rest)` runs `s`'s update on `e`
/// (`step e s = set e i (eval_rvalue e R)`) then folds `rest` over the result. The
/// motive is the FUNCTION type `Env → Env`, so the `List.rec` fold accumulates a
/// state transformer and is applied to the initial env last — the standard
/// fold-as-CPS trick that makes a `List.rec` right-recursion a left fold. For a
/// single `Assign(k, R)`: `exec e [Assign k R] ι-reduces to `set e k (eval_rvalue e R)`.
/// All of `List.rec`/`Stmt.rec`/`set`/`eval_rvalue` are prelude/Trust DEFINITIONS,
/// so `exec` carries no non-foundational axiom. Requires `set`, `eval_rvalue`, and
/// the `Stmt`/`List` inductives registered.
pub(super) fn register_exec(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let stmt_ty = cst(MIRSEM_STMT);
    // Env → Env, the motive's codomain (a state transformer).
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());

    // exec : Env → List Stmt → Env
    let list_stmt =
        Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), stmt_ty.clone());
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), list_stmt.clone(), env_ty()));

    // @List.rec.{1, 0} : levels [motiveLevel=1 (Env→Env : Sort 1), elemUniv=0].
    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    // @Stmt.rec.{1} : motive lands in Env : Type ⇒ Sort 1.
    let stmt_rec =
        Expr::const_(Name::from_string(MIRSEM_STMT_REC), vec![Level::succ(Level::zero())]);
    let set = cst(MIRSEM_SET);
    let eval_rvalue = cst(MIRSEM_EVAL_RVALUE);

    // motive : λ(_ : List Stmt) → (Env → Env)
    let motive = Expr::lam(bd(), list_stmt.clone(), env_to_env.clone());

    // nil case : λ(e' : Env). e'    (identity transformer)
    let nil_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));

    // cons case : λ(s:Stmt). λ(rest:List Stmt). λ(ih:Env→Env). λ(e':Env). ih (step e' s)
    //   de-Bruijn at the body: e' = bvar(0), ih = bvar(1), rest = bvar(2), s = bvar(3).
    let cons_case = {
        // step e' s = @Stmt.rec.{1} (λ_:Stmt. Env)
        //                (λ(i:Nat). λ(R:Rvalue). set e' i (eval_rvalue e' R)) s
        // Inside the Assign minor (under i, R binders):
        //   R = bvar(0), i = bvar(1), e' = bvar(2) (lifted past i,R),
        //   ih = bvar(3), rest = bvar(4), s = bvar(5).
        let stmt_motive = Expr::lam(bd(), stmt_ty.clone(), env_ty());
        let assign_minor = {
            let e_inner = Expr::bvar(2); // e', lifted past i + R
            let i_inner = Expr::bvar(1); // i
            let r_inner = Expr::bvar(0); // R
            let evald = Expr::apps(eval_rvalue.clone(), [e_inner.clone(), r_inner]);
            // set e' i (eval_rvalue e' R)
            let set_app = Expr::apps(set.clone(), [e_inner, i_inner, evald]);
            // λ(i:Nat). λ(R:Rvalue). set_app
            Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), rvalue_ty(), set_app))
        };
        // @Stmt.rec.{1} motive assign_minor s   (s = bvar(3) here, before the e' binder)
        // NOTE: this term is built UNDER the `λ(e':Env)` binder, so at this depth:
        //   e' = bvar(0), ih = bvar(1), rest = bvar(2), s = bvar(3).
        let s_ref = Expr::bvar(3);
        let step = Expr::apps(stmt_rec.clone(), [stmt_motive, assign_minor, s_ref]);
        let ih_ref = Expr::bvar(1);
        // ih (step e' s)
        let body = Expr::app(ih_ref, step);
        // λ(s:Stmt). λ(rest:List Stmt). λ(ih:Env→Env). λ(e':Env). body
        Expr::lam(
            bd(),
            stmt_ty.clone(),
            Expr::lam(
                bd(),
                list_stmt.clone(),
                Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), body)),
            ),
        )
    };

    // @List.rec.{1,0} Stmt motive nil_case cons_case stmts e
    //   under `λ(e:Env). λ(stmts:List Stmt). …` : stmts = bvar(0), e = bvar(1).
    let rec_app =
        Expr::apps(list_rec, [stmt_ty.clone(), motive, nil_case, cons_case, Expr::bvar(0)]);
    // exec e stmts = (List.rec … stmts) e    (apply the accumulated transformer to e)
    let applied = Expr::app(rec_app, Expr::bvar(1));
    // λ(e : Env). λ(stmts : List Stmt). applied
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), list_stmt, applied));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(exec): {e:?}"))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Step 1C-cf — the `Trust.MirSem.CmpOp` / `Cond` inductives, `eval_cond`, `eval_ite`
// (the CONTROL-FLOW return: `if cmp(a,b) { then } else { else }`)
// ---------------------------------------------------------------------------
/// Register the `Trust.MirSem.CmpOp` inductive (idempotent):
///
/// ```text
/// inductive CmpOp : Type where
///   | Lt | Le | Eq | Ne | Gt | Ge : CmpOp
/// ```
///
/// An enumeration (all constructors nullary), so its transitive axiom closure is
/// `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_cmpop_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CMPOP);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let cmpop_ty = cst(MIRSEM_CMPOP);
    let ctor = |n: &str| Constructor { name: Name::from_string(n), type_: cmpop_ty.clone() };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![
                ctor(MIRSEM_CMPOP_LT),
                ctor(MIRSEM_CMPOP_LE),
                ctor(MIRSEM_CMPOP_EQ),
                ctor(MIRSEM_CMPOP_NE),
                ctor(MIRSEM_CMPOP_GT),
                ctor(MIRSEM_CMPOP_GE),
            ],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(CmpOp): {e:?}"))?;
    Ok(())
}

/// Register the `Trust.MirSem.Cond` inductive (idempotent):
///
/// ```text
/// inductive Cond : Type where
///   | Cmp : CmpOp → Operand → Operand → Cond
///   | And : Cond → Cond → Cond                  -- ADDITIVE (short-circuit `&&`)
/// ```
///
/// `Cmp` is the original single-constructor record over `CmpOp` and two `Operand`
/// fields (non-recursive). `And` is the ADDITIVE second constructor, RECURSIVE in
/// both arguments — modeling a conjunctive guard `c1 && c2`. Adding it does NOT
/// change `Cmp` (still constructor #0, byte-identical type); the auto-derived
/// recursor simply gains a second minor premise (`And` case) that existing
/// `Cmp`-only reductions ignore, so every prior `Cmp` certificate stays def-eq.
/// Requires `CmpOp` and `Operand` already registered.
pub(super) fn register_cond_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_COND);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let cmp_ctor = Constructor {
        name: Name::from_string(MIRSEM_COND_CMP),
        type_: Expr::pi(
            bd(),
            cst(MIRSEM_CMPOP),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), operand_ty(), cst(MIRSEM_COND))),
        ),
    };
    // And : Cond → Cond → Cond — recursive in both fields (the induction the
    // auto-derived recursor threads an induction hypothesis through).
    let and_ctor = Constructor {
        name: Name::from_string(MIRSEM_COND_AND),
        type_: Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), cst(MIRSEM_COND), cst(MIRSEM_COND))),
    };
    // Trust: RANGE+DISJUNCTION guard — Or : Cond → Cond → Cond, the ADDITIVE third
    // constructor (the `||` dual of `And`, same recursive field shape). Appended
    // AFTER `And` so `Cmp`/`And` keep constructor slots 0/1 and every existing
    // recursor reduction is untouched.
    let or_ctor = Constructor {
        name: Name::from_string(MIRSEM_COND_OR),
        type_: Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), cst(MIRSEM_COND), cst(MIRSEM_COND))),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![cmp_ctor, and_ctor, or_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(Cond): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.eval_cond : Env → Cond → Bool` (idempotent):
///
/// ```text
/// eval_cond (e : Env) : Cond → Bool
///   | Cmp op a b => match op with
///       | Lt => decide (Int.lt (eval e a) (eval e b))   -- via Int.decLt
///       | Le => decide (Int.le (eval e a) (eval e b))   -- via Int.decLe
///       | Eq => Int.beq (eval e a) (eval e b)
///       | Ne => Bool.not (Int.beq (eval e a) (eval e b))
///       | Gt => decide (Int.lt (eval e b) (eval e a))   -- SWAPPED
///       | Ge => decide (Int.le (eval e b) (eval e a))   -- SWAPPED
///   | And c1 c2 => Bool.and (eval_cond e c1) (eval_cond e c2)   -- ADDITIVE arm
/// ```
///
/// Built by the `Cond.rec` fold; the `Cmp` case dispatches the `CmpOp` field with
/// `CmpOp.rec` (six nullary minor premises). The codomain `Bool` is constant
/// (non-dependent fold). Each comparison grounds to a Bool-valued, AXIOM-FREE
/// prelude term: `decide`/`Int.decLt`/`Int.decLe` are prelude DEFINITIONS, `Int.beq`
/// is a native reducer, `Bool.not` is a prelude DEFINITION — none is an `Axiom`, so
/// `eval_cond` carries no non-foundational axiom.
///
/// The ADDITIVE `And` arm is the new minor premise the recursor gains for the
/// `And : Cond → Cond → Cond` constructor: with the constant `Bool` motive its IHs
/// are already `eval_cond e c1` / `eval_cond e c2`, and it folds them with
/// `Bool.and` (a prelude definition with a native reducer — still no axiom). The
/// `Cmp` minor is BYTE-IDENTICAL to before; on a `Cmp` value the recursor ignores
/// the new `And` minor, so every prior `Cmp` reflexivity/refinement reduces exactly
/// as it did, preserving each existing certificate def-eq.
pub(super) fn register_eval_cond(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EVAL_COND);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let lvl1 = || vec![Level::succ(Level::zero())];

    // eval_cond : Env → Cond → Bool
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), cst(MIRSEM_COND), cst("Bool")));

    let cond_rec = Expr::const_(Name::from_string(MIRSEM_COND_REC), lvl1());
    let cmpop_rec = Expr::const_(Name::from_string(MIRSEM_CMPOP_REC), lvl1());
    let eval = cst(MIRSEM_EVAL);

    // motive : λ(_ : Cond) → Bool   (constant codomain; non-dependent fold)
    let motive = Expr::lam(bd(), cst(MIRSEM_COND), cst("Bool"));

    // Cmp case: λ(op:CmpOp). λ(a:Operand). λ(b:Operand). CmpOp.rec.{1} (λ_.Bool) … op
    //   under the three case binders: b=bvar(0), a=bvar(1), op=bvar(2),
    //   cond=bvar(3), e=bvar(4). The six CmpOp minor premises add no binders (each
    //   CmpOp ctor is nullary) so the same de-Bruijn depth holds inside them.
    let cmp_case = {
        let e_ref = || Expr::bvar(4);
        let eval_a = || Expr::apps(eval.clone(), [e_ref(), Expr::bvar(1)]);
        let eval_b = || Expr::apps(eval.clone(), [e_ref(), Expr::bvar(0)]);
        // decide P inst  — `decide : (p:Prop) → [Decidable p] → Bool`.
        let decide_lt = |x: Expr, y: Expr| {
            Expr::apps(
                cst("decide"),
                [
                    Expr::apps(cst("Int.lt"), [x.clone(), y.clone()]),
                    Expr::apps(cst("Int.decLt"), [x, y]),
                ],
            )
        };
        let decide_le = |x: Expr, y: Expr| {
            Expr::apps(
                cst("decide"),
                [
                    Expr::apps(cst("Int.le"), [x.clone(), y.clone()]),
                    Expr::apps(cst("Int.decLe"), [x, y]),
                ],
            )
        };
        let lt_case = decide_lt(eval_a(), eval_b());
        let le_case = decide_le(eval_a(), eval_b());
        let eq_case = Expr::apps(cst("Int.beq"), [eval_a(), eval_b()]);
        let ne_case = Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [eval_a(), eval_b()]));
        // Gt(a,b) ≡ Lt(b,a); Ge(a,b) ≡ Le(b,a) — SWAPPED operands.
        let gt_case = decide_lt(eval_b(), eval_a());
        let ge_case = decide_le(eval_b(), eval_a());
        let cmpop_motive = Expr::lam(bd(), cst(MIRSEM_CMPOP), cst("Bool"));
        let dispatch = Expr::apps(
            cmpop_rec,
            [cmpop_motive, lt_case, le_case, eq_case, ne_case, gt_case, ge_case, Expr::bvar(2)],
        );
        Expr::lam(
            bd(),
            cst(MIRSEM_CMPOP),
            Expr::lam(bd(), operand_ty(), Expr::lam(bd(), operand_ty(), dispatch)),
        )
    };

    // ADDITIVE And case (the new minor premise the recursor gains for
    // `And : Cond → Cond → Cond`). For a recursive ctor the minor premise binds the
    // two fields then the two induction hypotheses (the `List.cons` convention used
    // by `exec`): λ(c1:Cond). λ(c2:Cond). λ(ih1:Bool). λ(ih2:Bool). Bool.and ih1 ih2.
    // With the constant `Bool` motive the IHs ARE `eval_cond e c1` / `eval_cond e c2`,
    // so the arm computes `Bool.and (eval_cond e c1) (eval_cond e c2)` — exactly the
    // conjunction `ground_bool(And(c1,c2))` emits. de-Bruijn at the body:
    //   ih2=bvar(0), ih1=bvar(1), c2=bvar(2), c1=bvar(3).
    let and_case = {
        let body = Expr::apps(cst("Bool.and"), [Expr::bvar(1), Expr::bvar(0)]);
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), cst("Bool"), body)),
            ),
        )
    };

    // Trust: RANGE+DISJUNCTION guard — the ADDITIVE Or case, the exact `Bool.or`
    // dual of `and_case` (same binder shape: two Cond fields, two Bool IHs).
    let or_case = {
        let body = Expr::apps(cst("Bool.or"), [Expr::bvar(1), Expr::bvar(0)]);
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), cst("Bool"), body)),
            ),
        )
    };

    // Cond.rec.{1} motive cmp_case and_case or_case cond — each new minor is APPENDED
    // after the unchanged earlier ones, so the `Cmp`/`And` reductions are preserved
    // byte-for-byte.
    let rec_app = Expr::apps(cond_rec, [motive, cmp_case, and_case, or_case, Expr::bvar(0)]);
    // λ(e : Env). λ(cond : Cond). rec_app
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), cst(MIRSEM_COND), rec_app));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(eval_cond): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.eval_ite : Env → Cond → Rvalue → Rvalue → Int`
/// (idempotent):
///
/// ```text
/// eval_ite (e : Env) (c : Cond) (t f : Rvalue) : Int :=
///   Bool.rec (λ_:Bool. Int) (eval_rvalue e f) (eval_rvalue e t) (eval_cond e c)
/// ```
///
/// i.e. `if eval_cond e c then eval_rvalue e t else eval_rvalue e f` — the
/// if-then-else over a comparison the guarded control-flow return folds. `Bool.rec`
/// minor-premise order is (false, true), so the FALSE arm is `eval_rvalue e f` (the
/// else value) and the TRUE arm is `eval_rvalue e t` (the then value). The arm
/// values reuse `eval_rvalue` (already Lemma-1B-adequate), and the conditional
/// structure is the new content. `Bool.rec`/`eval_cond`/`eval_rvalue` are prelude /
/// MirSem DEFINITIONS, so `eval_ite` carries no non-foundational axiom.
pub(super) fn register_eval_ite(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EVAL_ITE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);

    // eval_ite : Env → Cond → Rvalue → Rvalue → Int
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), int_ty())),
        ),
    );

    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    let eval_rvalue = cst(MIRSEM_EVAL_RVALUE);

    // λ(e:Env).λ(c:Cond).λ(t:Rvalue).λ(f:Rvalue). … de-Bruijn: f=0, t=1, c=2, e=3.
    let e_ref = || Expr::bvar(3);
    let eval_f = Expr::apps(eval_rvalue.clone(), [e_ref(), Expr::bvar(0)]);
    let eval_t = Expr::apps(eval_rvalue.clone(), [e_ref(), Expr::bvar(1)]);
    let cond_b = Expr::apps(cst(MIRSEM_EVAL_COND), [e_ref(), Expr::bvar(2)]);
    // Bool.rec.{1} (λ_.Int) (eval_rvalue e f) (eval_rvalue e t) (eval_cond e c)
    let body = Expr::apps(bool_rec, [int_motive, eval_f, eval_t, cond_b]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), rvalue_ty(), Expr::lam(bd(), rvalue_ty(), body)),
        ),
    );

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(eval_ite): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.iteI : Env → Cond → Int → Int → Int` (idempotent):
///
/// ```text
/// iteI (e : Env) (c : Cond) (t f : Int) : Int :=
///   Bool.rec (λ_:Bool. Int) f t (eval_cond e c)
/// ```
///
/// i.e. `if eval_cond e c then t else f` over ALREADY-EVALUATED `Int` arms (NOT
/// `Rvalue` syntax, the one difference from `eval_ite`). This is the half a NESTED /
/// multi-way guarded return needs: the ELSE arm of an outer `iteI` can itself be a
/// (recursive) `iteI` term, so a `if x>0 {1} else if x<0 {-1} else {0}` return reflects
/// to `iteI e c1 (eval_rvalue e t1) (iteI e c2 (eval_rvalue e t2) (eval_rvalue e e2))`
/// WITHOUT extending the `Rvalue` inductive (no recursor-arity change, no env
/// reordering — strictly additive). `Bool.rec` minor order is (false, true), so the
/// FALSE arm is `f` and the TRUE arm is `t` — matching `eval_ite`/`ground_int`'s `Ite`
/// arm. `Bool.rec`/`eval_cond` are prelude / MirSem definitions, so `iteI` carries no
/// non-foundational axiom.
pub(super) fn register_ite_i(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_ITE_I);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);

    // iteI : Env → Cond → Int → Int → Int
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty())),
        ),
    );

    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    // λ(e:Env).λ(c:Cond).λ(t:Int).λ(f:Int). … de-Bruijn: f=0, t=1, c=2, e=3.
    let cond_b = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(3), Expr::bvar(2)]);
    // Bool.rec.{1} (λ_.Int) (false ↦ f) (true ↦ t) (eval_cond e c)
    let body = Expr::apps(bool_rec, [int_motive, Expr::bvar(0), Expr::bvar(1), cond_b]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
        ),
    );

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(iteI): {e:?}"))?;
    Ok(())
}

/// Trust: BITWISE SHAPE LANE (2026-07-08) — register `Int.land`/`Int.lor`/
/// `Int.xor`/`Int.shiftLeft : Int → Int → Int` (idempotent) as `Declaration::
/// Opaque` total-function placeholders — EXACTLY the `Int.div`/`Int.mod`
/// discipline `data_types_arithmetic.rs` establishes (a type-correct
/// never-unfolded body; `Opaque` is NOT a `ConstantKind::Axiom`, so a term
/// referencing these gains NO axiom dependency).
///
/// WHY MIRSEM REGISTERS ITS OWN COPY rather than sharing a base-prelude
/// registration: `data_types_arithmetic.rs` DELIBERATELY does NOT register
/// `Int.land`/`Int.lor`/`Int.xor` in `Environment::with_prelude()` — trust-ir's
/// OWN `Basic.lean` defines these names with GENUINE (non-opaque) semantics,
/// and a prelude copy would collide (`Duplicate declaration`) when Basic.lean
/// is checked into the SAME environment the trust-ir bridge builds. `mirsem_env`
/// is a SEPARATE `Environment` instance that never loads Basic.lean (it only
/// ever calls `Environment::with_prelude()` plus MirSem's own registrations —
/// see `mirsem_env`'s body), so there is no cross-registration to collide with:
/// each `Environment` value is independent, and `add_decl_if_absent` keeps this
/// idempotent within a single build. `Int.shiftLeft` mirrors the SAME name the
/// `clean-compiler` const-folder already spells for the UNBOUNDED `a * 2^n`
/// shift denotation (`crates/clean-compiler/src/const_fold_ext2.rs`), chosen
/// for consistency rather than any code-level dependency (that crate operates
/// on a different, unrelated compiled representation).
///
/// These are UNINTERPRETED (no native reducer is registered here — unlike
/// `Int.div`/`Int.mod`, which the kernel's `native_reducers_int.rs` DOES
/// concretely reduce): the adequacy proofs below rest on REFLEXIVITY between
/// two SYMBOLIC terms (`eval_rvalue`'s reduct vs. the live grounder's output),
/// never on evaluating a concrete numeric value — the SAME "opaque, total,
/// asserts nothing about the value" honesty tier `Int.div`/`Int.mod` and
/// `idx_elem`/`slice_len` already establish elsewhere in this file. A future
/// increment MAY add native reducers (or bridge to trust-ir's genuine
/// definitions) without touching any certificate that rests on these opaque
/// placeholders — reflexivity survives strengthening the RHS.
pub(super) fn register_int_bitwise(env: &mut Environment) -> Result<(), String> {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_binop_ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty()));
    let placeholder = {
        let zero = int_lit(0);
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), zero))
    };
    // Trust: M6 rung 6, UNSIGNED-Shr arm — `Int.shiftRight` joins the same
    // Opaque-placeholder discipline (see this fn's doc; the name is the exact
    // spelling the full clean-kernel prelude's own discharged
    // `Nat.shiftRight`-backed definition family uses).
    for op in ["Int.land", "Int.lor", "Int.xor", "Int.shiftLeft", "Int.shiftRight"] {
        env.add_decl_if_absent(Declaration::Opaque {
            name: Name::from_string(op),
            level_params: vec![],
            type_: int_binop_ty.clone(),
            value: placeholder.clone(),
        })
        .map_err(|e| format!("add_decl(Int bitwise {op}): {e:?}"))?;
    }
    Ok(())
}

/// Build a fresh kernel `Environment` with the prelude, the `MirSem.Operand`
/// inductive, and `eval` registered — the semantic anchor's environment. Also pins
/// the Lemma-1B (`BinOp`/`Rvalue`/`eval_rvalue`) and Lemma-1C (`Stmt`) anchors so
/// the whole faithfulness fragment shares one environment.
pub fn mirsem_env() -> Result<Environment, String> {
    // Trust (perf): this MirSem prelude is fixed and VC-INDEPENDENT but was
    // rebuilt (full kernel re-typecheck) on every one of the ~13 MirSem witness
    // lanes per corpus function. Memoize once behind a `OnceLock`, hand out an
    // `Arc`-backed clone — the proven `certification_env` pattern. Soundness
    // unchanged: a clone is byte-identical and every real VC term is still fully
    // kernel-checked (callers clone-then-mutate a local env).
    static MEMO: std::sync::OnceLock<Result<Environment, String>> = std::sync::OnceLock::new();
    MEMO.get_or_init(mirsem_env_uncached).clone()
}

pub(super) fn mirsem_env_uncached() -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    // Trust: BITWISE SHAPE LANE (2026-07-08) — registered FIRST (before any decl
    // that might reference these names) so `Int.land`/`Int.lor`/`Int.xor`/
    // `Int.shiftLeft` are resolvable constants by the time `register_eval_rvalue`
    // syntactically references them.
    register_int_bitwise(&mut env)?;
    register_operand_inductive(&mut env)?;
    register_idx_elem(&mut env)?;
    register_eval(&mut env)?;
    register_binop_inductive(&mut env)?;
    // Lemma 1C-cf (control-flow return): the comparison / condition / if-then-else
    // anchor for guarded `if cmp(a,b) { then } else { else }` returns. Trust (Step 6CU):
    // `CmpOp`/`Cond`/`eval_cond`/`iteI` now register BEFORE `Rvalue` because the new
    // `Rvalue.Sel : Cond → Operand → Operand → Rvalue` constructor references `Cond` (and
    // its `eval_rvalue` arm grounds through `iteI`). `Cond`/`eval_cond` depend only on
    // `CmpOp`/`Operand`/`eval` (NOT `Rvalue`), and `iteI : Env → Cond → Int → Int → Int`
    // depends only on `Cond`/`eval_cond`, so the reorder is sound and strictly additive —
    // every decl below still rests on ⊆ the 3 foundational axioms. `eval_ite` (whose arms
    // are `Rvalue` SYNTAX) is the ONE def that genuinely needs `Rvalue`, so it stays AFTER.
    register_cmpop_inductive(&mut env)?;
    register_cond_inductive(&mut env)?;
    register_eval_cond(&mut env)?;
    // NESTED / multi-way guarded return: the Int-armed if-then-else `iteI` whose ELSE
    // arm can itself be an `iteI` (so `sign`/3-arm-clamp returns reflect to a NESTED
    // Ite). Additive — depends only on `Bool.rec`/`eval_cond`/`Int`, registered above.
    // ALSO the grounding target of the new `Rvalue.Sel` arm, so it must precede `Rvalue`.
    register_ite_i(&mut env)?;
    register_rvalue_inductive(&mut env)?;
    register_eval_rvalue(&mut env)?;
    register_stmt_inductive(&mut env)?;
    register_set(&mut env)?;
    register_exec(&mut env)?;
    // `eval_ite : Env → Cond → Rvalue → Rvalue → Int` — the Rvalue-armed if-then-else the
    // guarded-return path folds; needs `Rvalue`/`eval_rvalue`, so it registers LAST.
    register_eval_ite(&mut env)?;
    Ok(env)
}

/// Pin the `MirSem` anchor and audit its axiom closure via the kernel's own
/// `axiom_deps`. Confirms BOTH the inductive and `eval` rest on exactly the 3
/// foundational axioms (modulo 3, no 4th axiom).
#[must_use]
pub fn pin_mirsem_anchor() -> AnchorVerdict {
    let env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [
        MIRSEM_OPERAND,
        MIRSEM_OPERAND_REC,
        MIRSEM_IDX_ELEM,
        MIRSEM_SLICE_LEN,
        MIRSEM_EVAL,
        MIRSEM_BINOP,
        MIRSEM_BINOP_REC,
        MIRSEM_RVALUE,
        MIRSEM_RVALUE_REC,
        // Trust (Step 6CU): `eval_rvalue`'s new `Sel` arm grounds through `iteI`, so the
        // anchor audits `iteI` too — confirming the conditional-update grounding rests on
        // ⊆ the 3 foundational axioms.
        MIRSEM_ITE_I,
        MIRSEM_EVAL_RVALUE,
        MIRSEM_STMT,
        MIRSEM_STMT_REC,
        MIRSEM_SET,
        MIRSEM_EXEC,
        MIRSEM_CMPOP,
        MIRSEM_CMPOP_REC,
        MIRSEM_COND,
        MIRSEM_COND_REC,
        MIRSEM_EVAL_COND,
        MIRSEM_EVAL_ITE,
    ] {
        match env.axiom_deps(&Name::from_string(n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return AnchorVerdict::Residue(names);
            }
            None => {
                return AnchorVerdict::KernelRejected(format!("decl not found: {n}"));
            }
        }
    }
    AnchorVerdict::Modulo3
}

/// Trust: CAST-TEMP GUARD READ — the RESERVED opaque-carrier key
/// [`SemOperand::Cast`] uses: distinct per `(dest_width, dest_signed)` pair
/// (so a function casting the SAME source to two DIFFERENT destination shapes
/// is never mis-equated across them), and UNREACHABLE by any real
/// `Field(_, fld: u64)` (`fld` unsigned, always ≥ 0) or by
/// [`MIRSEM_DISCRIMINANT_TAG_KEY`] (`-1`): the formula `-(2 + 2*width +
/// signed)` is always `<= -2` for any `width: u64`.
pub(super) const fn mirsem_cast_tag_key(dest_width: u64, dest_signed: bool) -> i128 {
    -(2 + 2 * (dest_width as i128) + (dest_signed as i128))
}
