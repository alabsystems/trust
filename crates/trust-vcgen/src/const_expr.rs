// The CLOSED CONSTANT EXPRESSION resolver, shared by every lane that needs the
// exact integer a constant expression rustc left unfolded computes.
//
// WHY IT IS ITS OWN MODULE. It landed on 2026-09-18 inside
// `generate::overflow_vc`, for the guard-fact miner
// (`generate::overflow_vc::v2_comparison_formula`): a guard bound spelled
// `-(1i64 << 31)` mined no var-vs-const fact, so the strict lane REFUTED a safe
// multiply. The very same resolution is what the NEGATION lanes need —
// `guards::extract_block_definitions_until_impl` (the Int lane's block definition
// of `(1u64 << 20) as i64`, and the 128-bit lane's of `1i128 << 62`) and
// `generate::overflow_vc::v2_collect_bv_shl_blockdef` (the >= 128-bit BV lane's
// fresh operand var for that same shift) — and `guards` is not a child of
// `generate`, so a `pub(super)` item in `overflow_vc` could not be reached from
// it. Moved here VERBATIM rather than copied: a second folder is a second place
// for the exactness contract below to be got wrong.
//
// EXACTNESS IS THE CONTRACT. Every function here returns the value the machine
// computes, or `None`. Nothing partially evaluates and nothing approximates —
// see [`v2_const_expr_int_fits`], [`v2_const_expr_binop`] and
// [`v2_const_expr_cast_int`]. Declining is sound at every call site (a missing
// hypothesis can only under-prove); returning a WRONG value would be a FALSE
// PROVE, which is why each arm fails closed.
//
// EXACT IS NOT THE SAME AS VALUE-PRESERVING — the 2026-09-21 widening. Until
// this date the `Cast` arm admitted only a cast that carried its source value
// through unchanged, so `let lim = (-1i32) as u32 as i64` mined NO bound at all
// and the refutation it sat under had no deliverable witness (the row
// `counterexample_grounding` is named for). That refusal conflated two different
// questions. A REINTERPRETING `as` between integer types is not an
// approximation: it is a total, exactly computable function of the source value
// and the destination type, and `lim == 4294967295` is TRUE on every execution
// that reaches it — so it is a sound hypothesis, which is the only thing this
// module has ever had to be. What must stay refused is a cast whose value this
// module cannot compute EXACTLY (a float, a pointer, a source that is not itself
// closed) and a value that is not the one the destination LOCAL receives; those
// are the arms of [`v2_const_expr_cast_int`] and its call site.
//
// What this widening deliberately does NOT touch: the `local_defs` escape gate.
// A bound assigned and then `&mut`-escaped still declines, because the alias may
// have written it — that refusal is `local_defs::unique_value_def`'s and is
// load-bearing (`local_defs_tests::the_resolver_refuses_an_escaped_local`), and
// `an_escaped_local_still_declines_through_a_cast` below pins that a cast is not
// a way around it.

use trust_types::{BinOp, ConstValue, Operand, Rvalue, Ty, VerifiableFunction};

/// Fuel for [`v2_const_expr_operand_int`]: the longest chain of MIR temporaries
/// this fold will walk before giving up. The shapes it exists for are short —
/// `-(1i64 << 31)` is `Shl` -> `Neg` -> the comparison operand (3), and a checked
/// `65536i64 * 32768i64` is `CheckedMul` -> `.0` -> `Neg` (3) — so 8 leaves room
/// for nesting without letting a pathological body make the walk unbounded.
pub(crate) const V2_CONST_EXPR_FUEL: u32 = 8;

/// Does `value` fit `ty` EXACTLY, as the value of that integer type?
///
/// This is the whole fail-closed discipline of [`v2_const_expr_operand_int`] in
/// one place: every folded step is checked here against its own destination type,
/// so a fold that the machine would wrap or truncate yields `None` instead of a
/// bound. `1i64 << 63` is `2^63`, one past `i64::MAX`, and is refused here.
pub(crate) fn v2_const_expr_int_fits(ty: &Ty, value: i128) -> Option<i128> {
    let Ty::Int { width, signed } = ty else {
        return None;
    };
    let (width, signed) = (*width, *signed);
    if width == 0 || width > 128 {
        return None;
    }
    if signed {
        if value < crate::range::signed_min(width) || value > crate::range::signed_max(width) {
            return None;
        }
    } else if value < 0 || (value as u128) > crate::range::unsigned_max(width) {
        return None;
    }
    Some(value)
}

/// One folded binary operation over two already-folded constants, evaluated
/// EXACTLY in `i128` and then range-checked against the destination type `ty`.
///
/// Every arm is the machine's own semantics or nothing:
///  * `Add`/`Sub`/`Mul` use the checked `i128` operations, so an intermediate
///    that leaves `i128` declines rather than wrapping;
///  * `Div`/`Rem` refuse a zero divisor (the machine traps; there is no value);
///  * `Shl` refuses a shift amount `>= width` (`1i64 << 64` is not a bound, it is
///    a panic) and otherwise multiplies by two exactly `amount` times, so a
///    shift whose mathematical result leaves the type is refused by the fit
///    below instead of silently becoming the truncated machine value;
///  * `Shr` is likewise width-checked; `i128`'s `>>` is the arithmetic shift Rust
///    specifies for a signed type, and an unsigned operand is non-negative by the
///    fit that produced it, so the same expression is exact for both;
///  * the bitwise ops are admitted only for NON-NEGATIVE operands, where the
///    `i128` result is width-independent; a negative operand's answer depends on
///    the two's-complement width and is refused rather than approximated.
///
/// `ty` is the DESTINATION type, which for every arm here (shifts included) is
/// also the left operand's type.
pub(crate) fn v2_const_expr_binop(op: BinOp, lhs: i128, rhs: i128, ty: &Ty) -> Option<i128> {
    let Ty::Int { width, .. } = ty else {
        return None;
    };
    let width = *width;
    let shift_amount = |amount: i128| -> Option<u32> {
        let amount = u32::try_from(amount).ok()?;
        if amount >= width { None } else { Some(amount) }
    };
    let value = match op {
        BinOp::Add => lhs.checked_add(rhs)?,
        BinOp::Sub => lhs.checked_sub(rhs)?,
        BinOp::Mul => lhs.checked_mul(rhs)?,
        BinOp::Div => lhs.checked_div(rhs)?,
        BinOp::Rem => lhs.checked_rem(rhs)?,
        BinOp::BitAnd if lhs >= 0 && rhs >= 0 => lhs & rhs,
        BinOp::BitOr if lhs >= 0 && rhs >= 0 => lhs | rhs,
        BinOp::BitXor if lhs >= 0 && rhs >= 0 => lhs ^ rhs,
        BinOp::Shl => {
            let amount = shift_amount(rhs)?;
            if lhs == 0 {
                0
            } else if amount < 127 {
                lhs.checked_mul(1i128 << amount)?
            } else {
                return None;
            }
        }
        BinOp::Shr => lhs >> shift_amount(rhs)?,
        _ => return None,
    };
    v2_const_expr_int_fits(ty, value)
}

/// Trust: 2026-09-21 — Rust's `as` between two INTEGER types, computed exactly.
///
/// THE MODEL, stated once so every arm below can be read against it. `v as T`
/// for integer `T` of width `w` is: take the two's-complement representation of
/// the mathematical value `v`, keep its low `w` bits, and read those bits at
/// `T`'s signedness. Truncation and sign/zero extension are both special cases
/// of that one sentence, which is why this function needs the DESTINATION type
/// and not the source one: `value` is already the exact mathematical value of a
/// well-typed source (every producer in this module range-checks it against its
/// own type through [`v2_const_expr_int_fits`]), and the low `w` bits of a
/// value's two's-complement representation do not depend on how many bits the
/// source carried it in. `(-1i8) as u64` and `(-1i64) as u64` are both
/// `u64::MAX` for exactly that reason.
///
/// FAIL CLOSED, every arm:
///  * a non-integer destination (a float, a pointer, `bool`, `char`,
///    `PtrSizedInt`) returns `None` — this module models integer `as` and
///    nothing else, and a float cast is not even a total function of the bits;
///  * a width of `0` or above `128` is not a Rust integer type and returns
///    `None`;
///  * a `u128` destination whose bit pattern exceeds `i128::MAX` returns `None`
///    rather than a wrapped answer: this module carries values in `i128`, and
///    `(-1i64) as u128` is `2^128 - 1`, which it cannot hold. Declining costs a
///    hypothesis; guessing would be a false prove;
///  * the result is put back through [`v2_const_expr_int_fits`], so a value this
///    function somehow computed outside the destination type never escapes.
///
/// The arithmetic is done in `u128` and converted once, so no intermediate
/// overflows at any admitted width — `1i128 << width` would wrap at `width ==
/// 127` and silently change the sign of the answer.
pub(crate) fn v2_const_expr_cast_int(value: i128, target: &Ty) -> Option<i128> {
    let Ty::Int { width, signed } = target else {
        return None;
    };
    let (width, signed) = (*width, *signed);
    if width == 0 || width > 128 {
        return None;
    }
    if width == 128 {
        // Every bit survives. Signed: the value is already an `i128`. Unsigned:
        // a NEGATIVE value's `u128` pattern is past `i128::MAX` and cannot be
        // carried here at all, so it declines instead of being approximated.
        let folded = if signed || value >= 0 { value } else { return None };
        return v2_const_expr_int_fits(target, folded);
    }
    let mask = (1u128 << width) - 1;
    // `value as u128` IS the two's-complement representation at 128 bits (Rust's
    // `as` between `i128` and `u128` is the identity on bits), so masking it
    // yields the destination's bits for a negative and a positive value alike.
    let bits = (value as u128) & mask;
    let folded = if signed && (bits >> (width - 1)) & 1 == 1 {
        // Negative at the destination width: the value is `bits - 2^width`.
        // Computed as a magnitude in `u128` (at most `2^(width-1)`, so it always
        // fits `i128`) and then negated, rather than as an `i128` subtraction
        // whose `2^width` term would itself overflow at the top widths.
        let magnitude = (1u128 << width) - bits;
        i128::try_from(magnitude).ok()?.checked_neg()?
    } else {
        i128::try_from(bits).ok()?
    };
    v2_const_expr_int_fits(target, folded)
}

/// The folded value of one `Rvalue` that defines a constant-expression temporary,
/// range-checked against `dest_ty` (the defined local's own declared type).
pub(crate) fn v2_const_expr_rvalue_int(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    dest_ty: &Ty,
    fuel: u32,
) -> Option<i128> {
    let value = match rvalue {
        Rvalue::Use(inner) => v2_const_expr_operand_int(func, inner, fuel)?,
        // Int-to-int only, modeled EXACTLY by [`v2_const_expr_cast_int`] — see
        // this module's header for why a reinterpreting cast is a sound
        // hypothesis and not an approximation. Three conditions gate it, and
        // each one of them is a way the answer could otherwise be wrong:
        //
        //  * the cast's TARGET type must be the destination local's own declared
        //    type. `v2_const_expr_cast_int` computes the value at the target
        //    type, and it is the LOCAL that the hypothesis will be stated about;
        //    where those two disagree the MIR is not well typed and this module
        //    has no business inventing which one the machine stored.
        //  * the source operand's type must itself be an integer, and the folded
        //    source value must FIT it. `v2_const_expr_cast_int` takes the exact
        //    mathematical value of a WELL-TYPED source — that is the premise
        //    that makes the destination's low bits independent of the source
        //    width — and this is where the premise is checked rather than
        //    assumed. Every value `v2_const_expr_operand_int` produces already
        //    satisfies it (each producer range-checks against its own type, and
        //    a constant's `operand_ty` is read off its own encoding), so this is
        //    defence in depth rather than a live filter: a float or pointer
        //    source, or a malformed constant whose value its own type cannot
        //    hold, declines here instead of being reinterpreted.
        //  * the source operand must be CLOSED, which is
        //    `v2_const_expr_operand_int`'s own question: a parameter, a call
        //    result or anything with a variable inside it resolves to nothing
        //    here exactly as it does everywhere else in this module.
        Rvalue::Cast(inner, cast_ty @ Ty::Int { .. }) => {
            if cast_ty != dest_ty {
                return None;
            }
            let source_ty = crate::operand_ty_cow(func, inner)?;
            if !matches!(source_ty.as_ref(), Ty::Int { .. }) {
                return None;
            }
            let source = v2_const_expr_int_fits(
                source_ty.as_ref(),
                v2_const_expr_operand_int(func, inner, fuel)?,
            )?;
            v2_const_expr_cast_int(source, cast_ty)?
        }
        Rvalue::UnaryOp(trust_types::UnOp::Neg, inner) => {
            v2_const_expr_operand_int(func, inner, fuel)?.checked_neg()?
        }
        Rvalue::BinaryOp(op, lhs, rhs) => v2_const_expr_binop(
            *op,
            v2_const_expr_operand_int(func, lhs, fuel)?,
            v2_const_expr_operand_int(func, rhs, fuel)?,
            dest_ty,
        )?,
        _ => return None,
    };
    v2_const_expr_int_fits(dest_ty, value)
}

/// Trust: 2026-09-18 (the SPELLING-dependent false refutation) — the exact
/// integer value of a guard operand that is a CLOSED CONSTANT EXPRESSION rustc
/// left unfolded in the un-optimized MIR, or `None`.
///
/// WHY THIS EXISTS.
///
/// ```ignore (illustrative)
/// pub fn ctl_pow31(a: i64, mut b: i64) -> i64 {
///     if a > -(1i64 << 31) && a < (1i64 << 31) && b > -(1i64 << 31) && b < (1i64 << 31) {
///         b = a * b;
///     }
///     b
/// }
/// ```
///
/// is safe (`|a * b| <= 2^62`, a whole bit inside `i64::MAX`) and the strict
/// DEFAULT lane REFUTED it — exit 1, with a counterexample, on valid Rust. Under
/// `-O` the identical function is PROVED, and so is the identical function
/// written with the literal bounds `-2147483648` / `2147483648` in BOTH lanes.
/// The entire difference is the debug lowering of the bound:
///
/// ```text
/// bb1: _5 = Shl(const 1i64, const 31i32)
/// bb2: _4 = Neg(move _5);  _3 = Gt(copy _1, move _4)
/// ```
///
/// `generate::overflow_vc::v2_comparison_formula` rendered that guard as
/// `Gt(Var(a), Var(_4))`, `v2_linear_var_const_fact` found no constant on either
/// side and mined NO var-vs-const fact at all, so the multiply's fresh BV var stayed free
/// and ay refuted the row at `a = b = i64::MIN`. `-O` const-folds the shift into
/// a literal and the same source proves. A verdict must not depend on how a
/// constant bound is SPELLED, so the fact miner resolves the constant itself.
///
/// EXACTNESS IS THE CONTRACT — the value returned is the value the machine
/// computes, or nothing:
///  * every step is range-checked against its own destination integer type
///    ([`v2_const_expr_int_fits`]), so a fold the machine would wrap or truncate
///    declines: `1i64 << 63` is `2^63` and yields no bound;
///  * a shift by `>= width` (`1i64 << 64`) is refused, not masked
///    ([`v2_const_expr_binop`]);
///  * an `as` cast between integer types is the machine's own reinterpretation
///    ([`v2_const_expr_cast_int`]): `(-1i32) as u32 as i64` is exactly
///    `4294967295` and mints that bound, while a cast to or from a float, a
///    pointer cast, a cast whose target disagrees with the destination local and
///    a cast of a non-closed operand all decline;
///  * only a whole-local read with a UNIQUE value definition
///    (`local_defs::unique_value_def`, which disqualifies a local whose address
///    escapes through `&mut`) and the VALUE half `.0` of a `CheckedBinaryOp`
///    tuple are walked — the two shapes rustc actually emits for an unfolded
///    constant expression — plus (2026-09-29) the one CALL whose value is exactly
///    its argument's, a lossless std integer conversion (`i128::from(u64::MAX)`,
///    `generate::lossless_int_conversion_arg`), under the same unique-value rule;
///  * anything else returns `None`: any other call, a parameter, a deeper
///    projection, a float, and above all any term with a VARIABLE anywhere inside
///    it. Nothing here partially evaluates.
///
/// The `.0` of a `CheckedBinaryOp` is the WRAPPED value when the operation
/// overflows, so reading it would be wrong in general — but `v2_const_expr_binop`
/// hands back a value only when the MATHEMATICAL result fits the type, i.e. only
/// when the operation does not overflow and `.0` is exactly that result. On a
/// constant-expression tuple that is a static property of the two literals, so no
/// path condition is involved.
///
/// DECLINING IS ALWAYS SOUND at every call site: every caller turns the value
/// into a HYPOTHESIS — a dominating path fact, or an unconditional block
/// definition of the statement that computes it — and a hypothesis only REMOVES
/// infeasible counterexamples, so a missing one can under-prove and never hide an
/// overflow. Returning a WRONG value would not be sound — which is why each arm
/// above fails closed instead of approximating.
pub(crate) fn v2_const_expr_operand_int(
    func: &VerifiableFunction,
    op: &Operand,
    fuel: u32,
) -> Option<i128> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(place) | Operand::Move(place)) = op else {
        return match op {
            Operand::Constant(ConstValue::Int(value)) => Some(*value),
            Operand::Constant(ConstValue::Uint(value, _)) => i128::try_from(*value).ok(),
            _ => None,
        };
    };
    // PERF-COMPILER-VCGEN-587: parameters have an implicit entry definition, so
    // `unique_value_def` and `lossless_int_conversion_arg` always return `None`
    // after scanning the body. Reject parameters in O(1).
    if crate::local_defs::is_parameter(func, place.local) {
        return None;
    }
    match place.projections.as_slice() {
        [] => {
            let dest_ty = crate::local_ty_ref(func, place.local)?;
            if let Some(rvalue) = crate::local_defs::unique_value_def(func, place.local) {
                return v2_const_expr_rvalue_int(func, rvalue, dest_ty, fuel - 1);
            }
            // Trust (2026-09-29): a lossless std integer conversion CALL of a closed
            // constant expression — `i128::from(u64::MAX)` — computes its argument's
            // value (`generate::lossless_int_conversion_arg`: the local's one value
            // is `<B as From<A>>::from(a)` / `<A as Into<B>>::into(a)` between
            // primitive integers). Exact, and range-checked against the
            // destination type like every other step here, so it declines rather
            // than approximates; without it `let wide = i128::from(u64::MAX) + 1;
            // -wide` refuted the negation at `wide = i128::MIN`.
            let arg = crate::generate::lossless_int_conversion_arg(func, place.local)?;
            v2_const_expr_int_fits(dest_ty, v2_const_expr_operand_int(func, arg, fuel - 1)?)
        }
        // The VALUE half of a checked-arithmetic tuple: `_6 = CheckedMul(const
        // 65536i64, const 32768i64); _5 = move (_6.0)`, which is how debug rustc
        // lowers `65536i64 * 32768i64` in a guard position.
        [trust_types::Projection::Field(0)] => {
            let Rvalue::CheckedBinaryOp(op, lhs, rhs) =
                crate::local_defs::unique_value_def(func, place.local)?
            else {
                return None;
            };
            let dest_ty = crate::place_ty_cow(func, place)?;
            v2_const_expr_binop(
                *op,
                v2_const_expr_operand_int(func, lhs, fuel - 1)?,
                v2_const_expr_operand_int(func, rhs, fuel - 1)?,
                dest_ty.as_ref(),
            )
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The CAST half of the fold, pinned on the resolver's own inputs.
//
// WHY HERE AND NOT IN A FIXTURE. Two of these shapes cannot be measured through
// a compiled program at all: `v2_const_expr_cast_int`'s 128-bit and zero-width
// edges have no Rust spelling, and the destination-disagrees case is MIR that a
// well-typed program never produces. The rest are pinned against RUST'S OWN `as`
// rather than against a restatement of the model — the oracle for "what does the
// machine compute" is the language, and a test that recomputed the answer the
// same way the implementation does would agree with a wrong implementation.
//
// The fail-closed half is the point: a wrong value mined here is conjoined into
// a proof as a hypothesis the machine never established, which is a FALSE PROVE.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, LocalDecl, Place, Projection, SourceSpan, Statement, Terminator,
        VerifiableBody,
    };

    use super::*;

    fn i(width: u32) -> Ty {
        Ty::Int { width, signed: true }
    }
    fn u(width: u32) -> Ty {
        Ty::Int { width, signed: false }
    }
    fn int(value: i128) -> Operand {
        Operand::Constant(ConstValue::Int(value))
    }
    fn uint(value: u128, width: u32) -> Operand {
        Operand::Constant(ConstValue::Uint(value, width))
    }
    fn local(n: usize) -> Operand {
        Operand::Copy(Place::local(n))
    }
    fn assign(dest: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(dest), rvalue, span: SourceSpan::default() }
    }

    /// A one-block function whose locals are `(index, ty)` and whose statements
    /// are `stmts`; `_0` is the return local and `arg_count` locals after it are
    /// parameters. Same shape as `generate::const_expr_bound_tests::func`.
    fn func(locals: &[(usize, Ty)], stmts: Vec<Statement>, arg_count: usize) -> VerifiableFunction {
        let locals: Vec<LocalDecl> = locals
            .iter()
            .map(|(index, ty)| LocalDecl { index: *index, ty: ty.clone(), name: None })
            .collect();
        let return_ty = locals.iter().find(|l| l.index == 0).expect("_0").ty.clone();
        VerifiableFunction {
            name: "synthetic".to_string(),
            def_path: "synthetic::synthetic".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
                arg_count,
                return_ty,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn fold(f: &VerifiableFunction, n: usize) -> Option<i128> {
        v2_const_expr_operand_int(f, &local(n), V2_CONST_EXPR_FUEL)
    }

    // -----------------------------------------------------------------------
    // The model, against the language.
    // -----------------------------------------------------------------------

    /// Rust's own `as`, on the table that decides this module. Every expected
    /// value is written as a real Rust cast so the oracle is the language and
    /// not a second copy of the implementation.
    #[test]
    fn the_cast_fold_is_rusts_own_as() {
        assert_eq!(v2_const_expr_cast_int(-1, &u(32)), Some(i128::from((-1i32) as u32)));
        assert_eq!(
            v2_const_expr_cast_int(4_294_967_295, &i(64)),
            Some(i128::from(4_294_967_295u32 as i64))
        );
        assert_eq!(
            v2_const_expr_cast_int(1i128 << 63, &i(64)),
            Some(i128::from((1u64 << 63) as i64))
        );
        assert_eq!(v2_const_expr_cast_int(255, &i(8)), Some(i128::from(255u8 as i8)));
        assert_eq!(v2_const_expr_cast_int(-1, &u(64)), Some(i128::from((-1i8) as u64)));
        assert_eq!(v2_const_expr_cast_int(-1, &u(8)), Some(i128::from((-1i8) as u8)));
        assert_eq!(v2_const_expr_cast_int(300, &u(8)), Some(i128::from(300u32 as u8)));
        assert_eq!(v2_const_expr_cast_int(300, &i(8)), Some(i128::from(300i32 as i8)));
        assert_eq!(v2_const_expr_cast_int(-129, &i(8)), Some(i128::from((-129i32) as i8)));
        assert_eq!(v2_const_expr_cast_int(-1, &i(16)), Some(i128::from((-1i64) as i16)));
        assert_eq!(v2_const_expr_cast_int(-1, &u(16)), Some(i128::from((-1i64) as u16)));
        assert_eq!(
            v2_const_expr_cast_int(i64::MIN.into(), &i(32)),
            Some(i128::from(i64::MIN as i32))
        );
        assert_eq!(v2_const_expr_cast_int(i128::MIN, &i(128)), Some(i128::MIN));
        assert_eq!(v2_const_expr_cast_int(7, &u(128)), Some(7));
        assert_eq!(v2_const_expr_cast_int(i64::MAX.into(), &i(64)), Some(i128::from(i64::MAX)));
        // A widening cast of a NON-NEGATIVE value is the identity, which is the
        // behaviour that existed before the widening and must be unchanged.
        assert_eq!(v2_const_expr_cast_int(100, &i(8)), Some(100));
        assert_eq!(v2_const_expr_cast_int(1 << 31, &i(64)), Some(1 << 31));
    }

    /// THE MODEL AGAINST THE LANGUAGE, EXHAUSTIVELY over the type pairs and the
    /// boundary values (Trust 2026-10-01, review of cf9ce551b45: the table above is
    /// seventeen hand-picked rows, and a wrong value from this function is a false
    /// prove). Every source value of every Rust integer type in the sample — each power
    /// of two, its neighbours, complements and negations, plus a fixed pseudo-random
    /// spread — is cast to every Rust integer type BY THE LANGUAGE (`as`), and
    /// `v2_const_expr_cast_int` must agree: the same value, or `None` exactly where the
    /// true result is a `u128` past `i128::MAX`, which this module cannot carry.
    #[test]
    fn the_cast_fold_agrees_with_rusts_as_on_every_type_pair_and_boundary() {
        fn samples() -> Vec<u128> {
            let mut v = vec![0u128, 1, 2, 3, u128::MAX, u128::MAX - 1];
            for k in 0..128u32 {
                let p = 1u128 << k;
                for d in [0i128, 1, -1, 2, -2] {
                    let d = d as u128;
                    v.push(p.wrapping_add(d));
                    v.push((!p).wrapping_add(d));
                    v.push(p.wrapping_neg().wrapping_add(d));
                }
            }
            let mut x: u128 = 0x9E37_79B9_7F4A_7C15_F39C_C060_5CED_C834;
            for _ in 0..2000 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                v.push(x);
            }
            v
        }
        let samples = samples();
        let mut checked = 0u64;
        macro_rules! from_source {
            ($s:ty) => {
                for &raw in &samples {
                    // A well-typed source value; a `u128` past `i128::MAX` is a value
                    // this module never holds, so it has no input to compare.
                    let source = raw as $s;
                    let Ok(exact) = i128::try_from(source) else { continue };
                    macro_rules! to_dest {
                        ($d:ty, $w:expr, $signed:expr) => {{
                            let want = i128::try_from(source as $d).ok();
                            let got = v2_const_expr_cast_int(
                                exact,
                                &Ty::Int { width: $w, signed: $signed },
                            );
                            assert_eq!(
                                got,
                                want,
                                "`{source}{}` as `{}`",
                                stringify!($s),
                                stringify!($d)
                            );
                            checked += 1;
                        }};
                    }
                    to_dest!(i8, 8, true);
                    to_dest!(i16, 16, true);
                    to_dest!(i32, 32, true);
                    to_dest!(i64, 64, true);
                    to_dest!(i128, 128, true);
                    to_dest!(u8, 8, false);
                    to_dest!(u16, 16, false);
                    to_dest!(u32, 32, false);
                    to_dest!(u64, 64, false);
                    to_dest!(u128, 128, false);
                }
            };
        }
        from_source!(i8);
        from_source!(i16);
        from_source!(i32);
        from_source!(i64);
        from_source!(i128);
        from_source!(u8);
        from_source!(u16);
        from_source!(u32);
        from_source!(u64);
        from_source!(u128);
        assert!(checked > 200_000, "the sample is the test's whole value: {checked} pairs");

        // The widths Rust has no type for (1..=127), against an INDEPENDENT model: the
        // low `w` bits, sign-extended by an arithmetic shift for a signed destination.
        for width in 1..=127u32 {
            for signed in [true, false] {
                for &raw in samples.iter().take(800) {
                    let bits = raw & ((1u128 << width) - 1);
                    let want = if signed {
                        Some(((bits << (128 - width)) as i128) >> (128 - width))
                    } else {
                        i128::try_from(bits).ok()
                    };
                    assert_eq!(
                        v2_const_expr_cast_int(raw as i128, &Ty::Int { width, signed }),
                        want,
                        "{raw} at width {width}, signed {signed}"
                    );
                }
            }
        }
    }

    /// FAIL CLOSED. Each of these, answered with a value, would be a bound the
    /// machine never computes.
    #[test]
    fn the_cast_fold_declines_every_type_it_cannot_compute_exactly() {
        // A `u128` destination whose pattern leaves `i128`: `(-1i64) as u128` is
        // `2^128 - 1`, which this module cannot carry. Declining costs a
        // hypothesis; a wrapped answer would be a false prove.
        assert_eq!(v2_const_expr_cast_int(-1, &u(128)), None);
        assert_eq!(v2_const_expr_cast_int(i128::MIN, &u(128)), None);
        // Not integer types at all.
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Float { width: 64 }), None);
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Float { width: 32 }), None);
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Bool), None);
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Char), None);
        assert_eq!(v2_const_expr_cast_int(1, &Ty::PtrSizedInt { signed: false }), None);
        assert_eq!(
            v2_const_expr_cast_int(1, &Ty::RawPtr { mutable: false, pointee: Box::new(i(64)) }),
            None
        );
        // Not Rust integer widths.
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Int { width: 0, signed: true }), None);
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Int { width: 129, signed: true }), None);
        assert_eq!(v2_const_expr_cast_int(1, &Ty::Int { width: u32::MAX, signed: false }), None);
    }

    // -----------------------------------------------------------------------
    // The shapes the widening exists for, end to end through the resolver.
    // -----------------------------------------------------------------------

    /// THE ROW THIS LANDED FOR. `let lim = (-1i32) as u32 as i64` is a closed
    /// expression whose value is exactly `4294967295`; before 2026-09-21 the
    /// resolver declined it, so the guard it bounded mined no fact and the
    /// refutation that followed had no deliverable witness.
    #[test]
    fn a_reinterpreting_cast_chain_folds_to_the_machine_value() {
        let f = func(
            &[(0, i(64)), (1, u(32)), (2, i(64))],
            vec![assign(1, Rvalue::Cast(int(-1), u(32))), assign(2, Rvalue::Cast(local(1), i(64)))],
            0,
        );
        assert_eq!(fold(&f, 1), Some(i128::from((-1i32) as u32)));
        assert_eq!(
            fold(&f, 2),
            Some(4_294_967_295),
            "`(-1i32) as u32 as i64` IS 4294967295 — the bound the row could not mine"
        );
    }

    /// `(1u64 << 63) as i64` is `i64::MIN`. The SHIFT half is value-preserving at
    /// `u64` (`2^63` fits it) and the CAST half is the reinterpretation, so this
    /// pins the two folds composing rather than either alone.
    #[test]
    fn a_shift_that_reinterprets_through_a_cast_folds() {
        let f = func(
            &[(0, i(64)), (1, u(64)), (2, i(64))],
            vec![
                assign(1, Rvalue::BinaryOp(BinOp::Shl, uint(1, 64), int(63))),
                assign(2, Rvalue::Cast(local(1), i(64))),
            ],
            0,
        );
        assert_eq!(fold(&f, 1), Some(1i128 << 63));
        assert_eq!(fold(&f, 2), Some(i128::from(i64::MIN)));
    }

    /// `(255u8) as i8` is `-1`, and `(-1i8) as u64` is `u64::MAX`: narrowing into
    /// a signed type and widening out of one, both reinterpreting.
    #[test]
    fn a_narrowing_and_a_widening_reinterpretation_both_fold() {
        let f = func(&[(0, i(8)), (1, i(8))], vec![assign(1, Rvalue::Cast(uint(255, 8), i(8)))], 0);
        assert_eq!(fold(&f, 1), Some(i128::from(255u8 as i8)));

        let f = func(
            &[(0, u(64)), (1, i(8)), (2, u(64))],
            vec![assign(1, Rvalue::Use(int(-1))), assign(2, Rvalue::Cast(local(1), u(64)))],
            0,
        );
        assert_eq!(fold(&f, 2), Some(i128::from((-1i8) as u64)));
    }

    // -----------------------------------------------------------------------
    // FAIL CLOSED at the call site.
    // -----------------------------------------------------------------------

    /// A cast to or from a FLOAT is not modeled here at all. The `to` half falls
    /// out of the `Ty::Int` target pattern; the `from` half is the source-type
    /// gate, and it is the one a future refactor could quietly drop.
    #[test]
    fn a_float_cast_declines_in_both_directions() {
        let f = func(
            &[(0, Ty::Float { width: 64 }), (1, Ty::Float { width: 64 })],
            vec![assign(1, Rvalue::Cast(int(3), Ty::Float { width: 64 }))],
            0,
        );
        assert_eq!(fold(&f, 1), None, "an integer -> float cast has no integer value");

        let f = func(
            &[(0, i(64)), (1, Ty::Float { width: 64 }), (2, i(64))],
            vec![
                assign(1, Rvalue::Use(Operand::Constant(ConstValue::Float(3.0)))),
                assign(2, Rvalue::Cast(local(1), i(64))),
            ],
            0,
        );
        assert_eq!(fold(&f, 2), None, "a float -> integer cast is not this module's model");
        let f = func(
            &[(0, i(64)), (1, i(64))],
            vec![assign(1, Rvalue::Cast(Operand::Constant(ConstValue::Float(3.0)), i(64)))],
            0,
        );
        assert_eq!(fold(&f, 1), None, "and not from a float CONSTANT either");
    }

    /// The model's PREMISE, checked rather than assumed: the source value must be
    /// one its own type can hold. A `u8` constant carrying `300` is not a value
    /// any execution produces — reinterpreting it would mint `300` (or, through a
    /// narrowing cast, `44`) for a local the machine never wrote that into — so
    /// the cast declines. The well-formed twin folds, which is what keeps this
    /// row measuring the premise and not the cast.
    #[test]
    fn a_source_value_its_own_type_cannot_hold_declines() {
        let f =
            func(&[(0, i(64)), (1, i(64))], vec![assign(1, Rvalue::Cast(uint(300, 8), i(64)))], 0);
        assert_eq!(fold(&f, 1), None, "300 is not a u8, so `300u8 as i64` has no machine value");

        let f =
            func(&[(0, i(64)), (1, i(64))], vec![assign(1, Rvalue::Cast(uint(255, 8), i(64)))], 0);
        assert_eq!(fold(&f, 1), Some(i128::from(255u8 as i64)), "CONTROL: a real u8 folds");
    }

    /// A POINTER cast has no integer value here: the address is not a constant
    /// this module can compute, at any width.
    #[test]
    fn a_pointer_cast_declines() {
        let ptr = Ty::RawPtr { mutable: false, pointee: Box::new(i(64)) };
        let f = func(
            &[(0, i(64)), (1, i(64)), (2, ptr.clone()), (3, i(64))],
            vec![
                assign(1, Rvalue::Use(int(7))),
                assign(2, Rvalue::AddressOf(false, Place::local(1))),
                assign(3, Rvalue::Cast(local(2), i(64))),
            ],
            0,
        );
        assert_eq!(fold(&f, 3), None, "a pointer's address is not a closed constant");
    }

    /// THE CENTRAL REFUSAL, through a cast: nothing with a VARIABLE inside it
    /// folds. A cast is not a way to launder a parameter into a bound.
    #[test]
    fn a_cast_of_a_non_closed_operand_declines() {
        // `_1` is the parameter itself.
        let f = func(
            &[(0, i(64)), (1, i(32)), (2, i(64))],
            vec![assign(2, Rvalue::Cast(local(1), i(64)))],
            1,
        );
        assert_eq!(fold(&f, 2), None);

        // And one level deeper: a cast of a cast of a parameter.
        let f = func(
            &[(0, i(64)), (1, i(32)), (2, u(32)), (3, i(64))],
            vec![
                assign(2, Rvalue::Cast(local(1), u(32))),
                assign(3, Rvalue::Cast(local(2), i(64))),
            ],
            1,
        );
        assert_eq!(fold(&f, 3), None);
    }

    /// THE UNSAFE TWIN of the widening, and the reason this file names it. The
    /// `&mut` escape channel is `local_defs::unique_value_def`'s refusal, and a
    /// bound that is assigned and then aliased is NOT the value the local holds
    /// — the alias may have written it. Modeling the cast exactly must not open
    /// a path around that gate.
    ///
    /// The CONTROL is the same function with the borrow removed: it folds. If
    /// that control ever fails, this test has stopped measuring the alias.
    #[test]
    fn an_escaped_local_still_declines_through_a_cast() {
        let escaped = func(
            &[
                (0, i(64)),
                (1, u(32)),
                (2, i(64)),
                (3, Ty::Ref { mutable: true, inner: Box::new(u(32)) }),
            ],
            vec![
                assign(1, Rvalue::Cast(int(-1), u(32))),
                assign(3, Rvalue::Ref { mutable: true, place: Place::local(1) }),
                assign(2, Rvalue::Cast(local(1), i(64))),
            ],
            0,
        );
        assert_eq!(
            fold(&escaped, 1),
            None,
            "SOUNDNESS: a write may have arrived through the `&mut`, so the one `Assign` \
             this scan saw is not the local's value"
        );
        assert_eq!(fold(&escaped, 2), None, "and the cast that reads it declines with it");

        let unaliased = func(
            &[(0, i(64)), (1, u(32)), (2, i(64))],
            vec![assign(1, Rvalue::Cast(int(-1), u(32))), assign(2, Rvalue::Cast(local(1), i(64)))],
            0,
        );
        assert_eq!(
            fold(&unaliased, 2),
            Some(4_294_967_295),
            "CONTROL: without the borrow the identical chain folds, so the refusal above \
             is the ALIAS and not the cast"
        );
    }

    /// A cast whose TARGET type disagrees with the destination local's own
    /// declared type is MIR a well-typed program does not produce, and this
    /// module does not guess which of the two the machine stored.
    #[test]
    fn a_cast_whose_target_disagrees_with_its_destination_declines() {
        let f = func(&[(0, i(64)), (1, i(64))], vec![assign(1, Rvalue::Cast(int(-1), u(32)))], 0);
        assert_eq!(fold(&f, 1), None);

        // Same width, different SIGNEDNESS is the same refusal.
        let f = func(&[(0, u(32)), (1, u(32))], vec![assign(1, Rvalue::Cast(int(-1), i(32)))], 0);
        assert_eq!(fold(&f, 1), None);
    }

    /// The CAST walk TERMINATES on a cyclic definition — `_1 = _2 as i64; _2 = _1 as
    /// i64`, each the other's unique value definition — and answers nothing, because
    /// there is no closed constant to answer.
    ///
    /// Trust (2026-10-01, review of cf9ce551b45): this row used to assert that a
    /// closed constant reached through `V2_CONST_EXPR_FUEL + 4` casts folds to `None`.
    /// That decline is produced by the depth cap alone (the true value is 7), so the
    /// row made a spelling-dependent miss REQUIRED behaviour and pinned the cap it
    /// should be pinning against. Termination is the property; a cycle is where it is
    /// at stake.
    #[test]
    fn a_cyclic_cast_definition_terminates_and_declines() {
        let f = func(
            &[(0, i(64)), (1, i(64)), (2, i(64))],
            vec![
                assign(1, Rvalue::Cast(local(2), i(64))),
                assign(2, Rvalue::Cast(local(1), i(64))),
            ],
            0,
        );
        assert_eq!(fold(&f, 1), None);
        assert_eq!(fold(&f, 2), None);
    }

    /// A short closed chain of value-preserving casts folds to its value.
    #[test]
    fn a_closed_cast_chain_folds_to_its_value() {
        let mut locals = vec![(0usize, i(64)), (1usize, i(64))];
        let mut stmts = vec![assign(1, Rvalue::Use(int(7)))];
        for n in 2..=4 {
            locals.push((n, i(64)));
            stmts.push(assign(n, Rvalue::Cast(local(n - 1), i(64))));
        }
        let f = func(&locals, stmts, 0);
        assert_eq!(fold(&f, 4), Some(7));
    }

    /// The `.0` of a checked tuple reached THROUGH a cast still obeys the
    /// overflow rule: `2^32 * 2^32` does not fit `i64`, so `.0` is the wrapped
    /// value and is not that product — and casting it does not make it one.
    #[test]
    fn a_cast_over_an_overflowing_checked_tuple_still_declines() {
        let tuple = Ty::Tuple(vec![i(64), Ty::Bool]);
        let field0 = Operand::Copy(Place { local: 1, projections: vec![Projection::Field(0)] });
        let f = func(
            &[(0, i(32)), (1, tuple), (2, i(32))],
            vec![
                assign(1, Rvalue::CheckedBinaryOp(BinOp::Mul, int(1 << 32), int(1 << 32))),
                assign(2, Rvalue::Cast(field0, i(32))),
            ],
            0,
        );
        assert_eq!(fold(&f, 2), None);
    }
}
