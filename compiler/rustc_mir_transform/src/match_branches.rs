use rustc_abi::Integer;
use rustc_const_eval::const_eval::mk_eval_cx_for_const_val;
use rustc_middle::mir::interpret::Scalar; // Trust: for the simplify_switch_comparison rewrite
use rustc_middle::mir::visit::{PlaceContext, Visitor}; // Trust: liveness check for the range fold
use rustc_middle::mir::*;
use rustc_middle::ty::layout::{IntegerExt, TyAndLayout};
use rustc_middle::ty::util::Discr;
use rustc_middle::ty::{self, ScalarInt, Ty, TyCtxt};

use super::simplify::simplify_cfg;
use crate::patch::MirPatch;
use crate::unreachable_prop::remove_successors_from_switch;

/// Unifies all targets into one basic block if each statement can have the same statement.
pub(super) struct MatchBranchSimplification;

impl<'tcx> crate::MirPass<'tcx> for MatchBranchSimplification {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        // Enable only under -Zmir-opt-level=2 as this can make programs less debuggable.
        sess.mir_opt_level() >= 2
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let typing_env = body.typing_env(tcx);
        let mut changed = false;
        for bb in body.basic_blocks.indices() {
            // Trust: arms that unify collapse via `simplify_match`; a switch whose arms
            // cannot unify (unequal bodies) but whose *condition* is a single value or a
            // contiguous range is rewritten to the comparison shape if/else produces.
            if candidate_match(body, bb) {
                changed |= simplify_match(tcx, typing_env, body, bb);
            } else if simplify_switch_comparison(tcx, body, bb) {
                changed = true;
            } else if simplify_range_comparison(tcx, body, bb) {
                changed = true;
            }
        }

        if changed {
            simplify_cfg(tcx, body);
        }
    }

    fn is_required(&self) -> bool {
        false
    }
}

struct SimplifyMatch<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    patch: MirPatch<'tcx>,
    body: &'a Body<'tcx>,
    switch_bb: BasicBlock,
    discr: &'a Operand<'tcx>,
    discr_local: Option<Local>,
    discr_ty: Ty<'tcx>,
}

impl<'tcx, 'a> SimplifyMatch<'tcx, 'a> {
    fn discr_local(&mut self) -> Local {
        *self.discr_local.get_or_insert_with(|| {
            // Introduce a temporary for the discriminant value.
            let source_info = self.body.basic_blocks[self.switch_bb].terminator().source_info;
            self.patch.new_temp(self.discr_ty, source_info.span)
        })
    }

    /// Unifies the assignments if all rvalues are constants and equal.
    fn unify_if_equal_const(
        &self,
        dest: Place<'tcx>,
        consts: &[(u128, &ConstOperand<'tcx>)],
        otherwise: Option<&ConstOperand<'tcx>>,
    ) -> Option<StatementKind<'tcx>> {
        let (_, first_const, mut others) = split_first_case(consts, otherwise);
        let first_scalar_int = first_const.const_.try_eval_scalar_int(self.tcx, self.typing_env)?;
        if others.all(|const_| {
            const_.const_.try_eval_scalar_int(self.tcx, self.typing_env) == Some(first_scalar_int)
        }) {
            Some(StatementKind::Assign(Box::new((
                dest,
                // We didn't remember the `WithRetag` of the original assignments, so in case
                // one of them had "no", we also have to use "no" here.
                Rvalue::Use(Operand::Constant(Box::new(first_const.clone())), WithRetag::No),
            ))))
        } else {
            None
        }
    }

    /// If a source block is found that switches between two blocks that are exactly
    /// the same modulo const bool assignments (e.g., one assigns true another false
    /// to the same place), unify a target block statements into the source block,
    /// using Eq / Ne comparison with switch value where const bools value differ.
    ///
    /// For example:
    ///
    /// ```ignore (MIR)
    /// bb0: {
    ///     switchInt(move _3) -> [42_isize: bb1, otherwise: bb2];
    /// }
    ///
    /// bb1: {
    ///     _2 = const true;
    ///     goto -> bb3;
    /// }
    ///
    /// bb2: {
    ///     _2 = const false;
    ///     goto -> bb3;
    /// }
    /// ```
    ///
    /// into:
    ///
    /// ```ignore (MIR)
    /// bb0: {
    ///    _2 = Eq(move _3, const 42_isize);
    ///    goto -> bb3;
    /// }
    /// ```
    fn unify_by_eq_op(
        &mut self,
        dest: Place<'tcx>,
        consts: &[(u128, &ConstOperand<'tcx>)],
        otherwise: Option<&ConstOperand<'tcx>>,
    ) -> Option<StatementKind<'tcx>> {
        // FIXME: extend to any case.
        let (first_case, first_const, mut others) = split_first_case(consts, otherwise);
        if !first_const.ty().is_bool() {
            return None;
        }
        let first_bool = first_const.const_.try_eval_bool(self.tcx, self.typing_env)?;
        if others.all(|const_| {
            const_.const_.try_eval_bool(self.tcx, self.typing_env) == Some(!first_bool)
        }) {
            // Make value conditional on switch condition.
            let size =
                self.tcx.layout_of(self.typing_env.as_query_input(self.discr_ty)).unwrap().size;
            let const_cmp = Operand::const_from_scalar(
                self.tcx,
                self.discr_ty,
                rustc_const_eval::interpret::Scalar::from_uint(first_case, size),
                rustc_span::DUMMY_SP,
            );
            let op = if first_bool { BinOp::Eq } else { BinOp::Ne };
            let rval = Rvalue::BinaryOp(
                op,
                Box::new((Operand::Copy(Place::from(self.discr_local())), const_cmp)),
            );
            Some(StatementKind::Assign(Box::new((dest, rval))))
        } else {
            None
        }
    }

    /// Unifies the assignments if all rvalues can be cast from the discriminant value by IntToInt.
    ///
    /// For example:
    ///
    /// ```ignore (MIR)
    /// bb0: {
    ///     switchInt(_1) -> [1: bb2, 2: bb3, 3: bb4, otherwise: bb1];
    /// }
    ///
    /// bb1: {
    ///     unreachable;
    /// }
    ///
    /// bb2: {
    ///     _0 = const 1_i16;
    ///     goto -> bb5;
    /// }
    ///
    /// bb3: {
    ///     _0 = const 2_i16;
    ///     goto -> bb5;
    /// }
    ///
    /// bb4: {
    ///     _0 = const 3_i16;
    ///     goto -> bb5;
    /// }
    /// ```
    ///
    /// into:
    ///
    /// ```ignore (MIR)
    /// bb0: {
    ///    _0 = _1 as i16 (IntToInt);
    ///    goto -> bb5;
    /// }
    /// ```
    fn unify_by_int_to_int(
        &mut self,
        dest: Place<'tcx>,
        consts: &[(u128, &ConstOperand<'tcx>)],
    ) -> Option<StatementKind<'tcx>> {
        let (_, first_const) = consts[0];
        if !first_const.ty().is_integral() {
            return None;
        }
        let discr_layout =
            self.tcx.layout_of(self.typing_env.as_query_input(self.discr_ty)).unwrap();
        if consts.iter().all(|&(case, const_)| {
            let Some(scalar_int) = const_.const_.try_eval_scalar_int(self.tcx, self.typing_env)
            else {
                return false;
            };
            can_cast(self.tcx, case, discr_layout, const_.ty(), scalar_int)
        }) {
            let operand = Operand::Copy(Place::from(self.discr_local()));
            let rval = if first_const.ty() == self.discr_ty {
                Rvalue::Use(operand, WithRetag::No)
            } else {
                Rvalue::Cast(CastKind::IntToInt, operand, first_const.ty())
            };
            Some(StatementKind::Assign(Box::new((dest, rval))))
        } else {
            None
        }
    }

    /// This is primarily used to unify these copy statements that simplified the canonical enum clone method by GVN.
    /// The GVN simplified
    /// ```ignore (syntax-highlighting-only)
    /// match a {
    ///     Foo::A(x) => Foo::A(*x),
    ///     Foo::B => Foo::B
    /// }
    /// ```
    /// to
    /// ```ignore (syntax-highlighting-only)
    /// match a {
    ///     Foo::A(_x) => a, // copy a
    ///     Foo::B => Foo::B
    /// }
    /// ```
    /// This will simplify into a copy statement.
    fn unify_by_copy(
        &self,
        dest: Place<'tcx>,
        rvals: &[(u128, &Rvalue<'tcx>)],
    ) -> Option<StatementKind<'tcx>> {
        let bbs = &self.body.basic_blocks;
        // Check if the copy source matches the following pattern.
        // _2 = discriminant(*_1); // "*_1" is the expected the copy source.
        // switchInt(move _2) -> [0: bb3, 1: bb2, otherwise: bb1];
        let &Statement {
            kind: StatementKind::Assign((discr_place, Rvalue::Discriminant(copy_src_place))),
            ..
        } = bbs[self.switch_bb].statements.last()?
        else {
            return None;
        };
        if self.discr.place() != Some(discr_place) {
            return None;
        }
        let src_ty = copy_src_place.ty(self.body.local_decls(), self.tcx);
        if !src_ty.ty.is_enum() || src_ty.variant_index.is_some() {
            return None;
        }
        let dest_ty = dest.ty(self.body.local_decls(), self.tcx);
        if dest_ty.ty != src_ty.ty || dest_ty.variant_index.is_some() {
            return None;
        }
        let ty::Adt(def, _) = dest_ty.ty.kind() else {
            return None;
        };

        for &(case, rvalue) in rvals.iter() {
            match rvalue {
                // Check if `_3 = const Foo::B` can be transformed to `_3 = copy *_1`.
                Rvalue::Use(Operand::Constant(constant), _)
                    if let Const::Val(const_, ty) = constant.const_ =>
                {
                    let (ecx, op) = mk_eval_cx_for_const_val(
                        self.tcx.at(constant.span),
                        self.typing_env,
                        const_,
                        ty,
                    )?;
                    let variant = ecx.read_discriminant(&op).discard_err()?;
                    if !def.variants()[variant].fields.is_empty() {
                        return None;
                    }
                    let Discr { val, .. } = ty.discriminant_for_variant(self.tcx, variant)?;
                    if val != case {
                        return None;
                    }
                }
                Rvalue::Use(Operand::Copy(src_place), _) if *src_place == copy_src_place => {}
                // Check if `_3 = Foo::B` can be transformed to `_3 = copy *_1`.
                Rvalue::Aggregate(AggregateKind::Adt(_, variant_index, _, _, None), fields)
                    if fields.is_empty()
                        && let Some(Discr { val, .. }) =
                            src_ty.ty.discriminant_for_variant(self.tcx, *variant_index)
                        && val == case => {}
                _ => return None,
            }
        }
        // We didn't remember the `WithRetag` of the original assignments, so in case
        // one of them had "no", we also have to use "no" here.
        Some(StatementKind::Assign(Box::new((
            dest,
            Rvalue::Use(Operand::Copy(copy_src_place), WithRetag::No),
        ))))
    }

    /// Returns a new statement if we can use the statement replace all statements.
    fn try_unify_stmts(
        &mut self,
        index: usize,
        stmts: &[(u128, &StatementKind<'tcx>)],
        otherwise: Option<&StatementKind<'tcx>>,
    ) -> Option<StatementKind<'tcx>> {
        if let Some(new_stmt) = identical_stmts(stmts, otherwise) {
            return Some(new_stmt);
        }

        let (dest, rvals, otherwise) = candidate_assign(stmts, otherwise)?;
        if let Some((consts, otherwise)) = candidate_const(&rvals, otherwise) {
            if let Some(new_stmt) = self.unify_if_equal_const(dest, &consts, otherwise) {
                return Some(new_stmt);
            }
            if let Some(new_stmt) = self.unify_by_eq_op(dest, &consts, otherwise) {
                return Some(new_stmt);
            }
            // Requires the otherwise is unreachable.
            if otherwise.is_none()
                && let Some(new_stmt) = self.unify_by_int_to_int(dest, &consts)
            {
                return Some(new_stmt);
            }
        }

        // We only know the first statement is safe to introduce new dereferences.
        if index == 0
            // We cannot create overlapping assignments.
            && dest.is_stable_offset()
            // Requires the otherwise is unreachable.
            && otherwise.is_none()
            && let Some(new_stmt) = self.unify_by_copy(dest, &rvals)
        {
            return Some(new_stmt);
        }
        None
    }
}

/// Trust (rust-lang#110737): rewrite a 2-target integer `SwitchInt` (one value + otherwise)
/// whose arms `simplify_match` could not unify — because the successor blocks differ — into
/// the `Eq` comparison shape that an equivalent `if`/`else` produces, so downstream codegen
/// sees a canonical comparison:
///   `switchInt(discr) -> [val: val_bb, otherwise: other]`
///     becomes  `_eq = Eq(discr, val); switchInt(move _eq) -> [0: other, otherwise: val_bb]`.
fn simplify_switch_comparison<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    switch_bb: BasicBlock,
) -> bool {
    let TerminatorKind::SwitchInt { discr, targets } =
        &body.basic_blocks[switch_bb].terminator().kind
    else {
        return false;
    };
    // Only a runtime scrutinee that is a plain local is worth a comparison: a constant switch
    // is folded elsewhere (rewriting it to `Eq(const, val)` is pointless churn), and restricting
    // to a bare local keeps the rewrite to ordinary `match x { .. }` scrutinees rather than
    // reshaping projected switches (e.g. an array element) whose surrounding code other passes
    // and tests still expect in switch form.
    let Some(discr_place) = discr.place() else { return false };
    if discr_place.as_local().is_none() {
        return false;
    }
    // Exactly one value + otherwise.
    let mut cases = targets.iter();
    let (Some((val, val_bb)), None) = (cases.next(), cases.next()) else {
        return false;
    };
    let otherwise = targets.otherwise();
    // A target that is the switch block itself would create a self-referential temp def.
    if val_bb == switch_bb || otherwise == switch_bb {
        return false;
    }
    let discr_ty = discr.ty(body.local_decls(), tcx);
    // Restrict to plain integer discriminants (SwitchInt is also used on bool/char/enum tags;
    // a bool value is already the comparison, and a fresh Eq would just re-enter this pass).
    let size = match discr_ty.kind() {
        ty::Uint(t) => Integer::from_uint_ty(&tcx, *t).size(),
        ty::Int(t) => Integer::from_int_ty(&tcx, *t).size(),
        _ => return false,
    };
    // Don't preempt `EarlyOtherwiseBranch` (which runs after this pass and folds nested
    // enum-discriminant matches into a `select`): skip a switch whose scrutinee is read from
    // an enum `Discriminant` in this block. Rewriting those to `Eq` would defeat that pass.
    if let Operand::Copy(place) | Operand::Move(place) = discr
        && let Some(local) = place.as_local()
        && body.basic_blocks[switch_bb].statements.iter().any(|stmt| {
            stmt.kind.as_assign().is_some_and(|(dest, rvalue)| {
                dest.as_local() == Some(local) && matches!(rvalue, Rvalue::Discriminant(_))
            })
        })
    {
        return false;
    }
    let source_info = body.basic_blocks[switch_bb].terminator().source_info;
    let span = source_info.span;
    let discr = discr.clone();

    let val_const = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: Const::Val(
            ConstValue::Scalar(Scalar::Int(ScalarInt::try_from_uint(size.truncate(val), size).unwrap())),
            discr_ty,
        ),
    }));

    let mut patch = MirPatch::new(body);
    let eq = patch.new_temp(tcx.types.bool, span);
    let loc = Location {
        block: switch_bb,
        statement_index: body.basic_blocks[switch_bb].statements.len(),
    };
    patch.add_assign(loc, Place::from(eq), Rvalue::BinaryOp(BinOp::Eq, Box::new((discr, val_const))));
    // bool switch: 0 (discr != val) -> otherwise ; otherwise (== 1, discr == val) -> val_bb.
    patch.patch_terminator(
        switch_bb,
        TerminatorKind::SwitchInt {
            discr: Operand::Move(Place::from(eq)),
            targets: SwitchTargets::new(std::iter::once((0, otherwise)), val_bb),
        },
    );
    patch.apply(body);
    true
}

/// A `SwitchTargets` of exactly one value `0` plus an otherwise: returns `(zero_target, otherwise)`.
fn switch_zero_otherwise(targets: &SwitchTargets) -> Option<(BasicBlock, BasicBlock)> {
    let mut it = targets.iter();
    match (it.next(), it.next()) {
        (Some((0, zero_target)), None) => Some((zero_target, targets.otherwise())),
        _ => None,
    }
}

/// Trust (rust-lang#123305): fold a two-block `lo <= x && x <= hi` range test — the shape a
/// byte-range `matches!(x, lo..=hi)` lowers to — into a single subtract-and-compare, for an
/// unsigned scrutinee `x`:
/// ```text
///   bb0: _c1 = Le(const lo, copy x); switchInt(_c1) -> [0: out, otherwise: mid]
///   mid: _c2 = Le(copy x, const hi); switchInt(_c2) -> [0: out, otherwise: in]
/// ```
/// becomes
/// ```text
///   bb0: _sub = Sub(copy x, const lo); _cmp = Le(copy _sub, const hi-lo);
///        switchInt(_cmp) -> [0: out, otherwise: in]
/// ```
/// (`mid` becomes unreachable and is removed by the trailing `simplify_cfg`). Sound because the
/// wrapping `x - lo` maps every out-of-range `x` (below `lo` OR above `hi`) above `hi - lo` for an
/// unsigned type, so the single `Le` reproduces both bounds.
///
/// Trust: `_c1`'s defining statement may only be dropped when nothing else reads `_c1`. It is NOT
/// always a single-use temp: `GVN` runs before this pass and CSEs identical comparisons, so a
/// chain of ranges sharing a bound (`match x { 0..=0xff => .., 0..=0xffff => .., .. }`) leaves one
/// `_c1` defined here and read by several later blocks. Dropping the definition then leaves those
/// blocks switching on an uninitialized local — a silent wrong-code bug, which is how a released
/// `trustc` miscompiled `rustc_abi::Integer::fit_unsigned` and gave every enum a 1-byte tag. When
/// `_c1` is live out, keep the (side-effect-free) comparison and rewrite only the terminator;
/// `SimplifyLocals`/LLVM drop it when it really is dead.
fn simplify_range_comparison<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    bb0: BasicBlock,
) -> bool {
    // Recognize the pattern with immutable borrows, extracting owned/`Copy` data.
    let (lo, hi, discr, out, in_bb, discr_ty, size, source_info, drop_c1) = {
        let blocks = &body.basic_blocks;
        let bb0_data = &blocks[bb0];
        let TerminatorKind::SwitchInt { discr: c1, targets: t0 } = &bb0_data.terminator().kind
        else {
            return false;
        };
        let Some(c1_local) = c1.place().and_then(|p| p.as_local()) else { return false };
        let Some((out, mid)) = switch_zero_otherwise(t0) else { return false };
        if mid == bb0 || out == bb0 {
            return false;
        }

        // bb0's last statement: `c1_local = Le(const lo, copy x)`.
        let Some(last) = bb0_data.statements.last() else { return false };
        let Some((c1_dest, c1_rvalue)) = last.kind.as_assign() else { return false };
        if c1_dest.as_local() != Some(c1_local) {
            return false;
        }
        let Rvalue::BinaryOp(BinOp::Le, ops1) = c1_rvalue else { return false };
        let Operand::Copy(discr) = &ops1.1 else { return false };
        let discr = *discr;
        let discr_ty = discr.ty(&body.local_decls, tcx).ty;
        let size = match discr_ty.kind() {
            ty::Uint(t) => Integer::from_uint_ty(&tcx, *t).size(),
            _ => return false,
        };
        let Some(lo) = ops1.0.constant().and_then(|c| c.const_.try_to_bits(size)) else {
            return false;
        };

        // mid: exactly `c2_local = Le(copy x, const hi)` then `switchInt(_c2) -> [0: out, else: in]`.
        let mid_data = &blocks[mid];
        if mid_data.statements.len() != 1 {
            return false;
        }
        let TerminatorKind::SwitchInt { discr: c2, targets: t1 } = &mid_data.terminator().kind
        else {
            return false;
        };
        let Some(c2_local) = c2.place().and_then(|p| p.as_local()) else { return false };
        let Some((out2, in_bb)) = switch_zero_otherwise(t1) else { return false };
        if out2 != out {
            return false;
        }
        let Some((c2_dest, c2_rvalue)) = mid_data.statements[0].kind.as_assign() else {
            return false;
        };
        if c2_dest.as_local() != Some(c2_local) {
            return false;
        }
        let Rvalue::BinaryOp(BinOp::Le, ops2) = c2_rvalue else { return false };
        let Operand::Copy(discr2) = &ops2.0 else { return false };
        if *discr2 != discr {
            return false;
        }
        let Some(hi) = ops2.1.constant().and_then(|c| c.const_.try_to_bits(size)) else {
            return false;
        };
        if lo > hi {
            return false;
        }
        // `_c1`'s definition is `bb0`'s last statement; `bb0`'s terminator sits one index past it.
        // Those two locations are the ones this rewrite replaces — any *other* read of `_c1`
        // means the definition has to stay. See the soundness note on this function.
        let c1_def = bb0_data.statements.len() - 1;
        let drop_c1 = !local_read_outside(body, c1_local, bb0, c1_def);
        (lo, hi, discr, out, in_bb, discr_ty, size, bb0_data.terminator().source_info, drop_c1)
    };

    let span = source_info.span;
    let width = hi - lo;
    let sub = body.local_decls.push(LocalDecl::new(discr_ty, span));
    let cmp = body.local_decls.push(LocalDecl::new(tcx.types.bool, span));
    let int_const = |v: u128| {
        Operand::Constant(Box::new(ConstOperand {
            span,
            user_ty: None,
            const_: Const::Val(
                ConstValue::Scalar(Scalar::Int(ScalarInt::try_from_uint(size.truncate(v), size).unwrap())),
                discr_ty,
            ),
        }))
    };
    let bb0_mut = &mut body.basic_blocks.as_mut()[bb0];
    if drop_c1 {
        bb0_mut.statements.pop(); // drop `_c1 = Le(const lo, copy x)` — nothing else reads it
    }
    bb0_mut.statements.push(Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(sub),
            Rvalue::BinaryOp(BinOp::Sub, Box::new((Operand::Copy(discr), int_const(lo)))),
        ))),
    ));
    bb0_mut.statements.push(Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(cmp),
            Rvalue::BinaryOp(
                BinOp::Le,
                Box::new((Operand::Copy(Place::from(sub)), int_const(width))),
            ),
        ))),
    ));
    bb0_mut.terminator_mut().kind = TerminatorKind::SwitchInt {
        discr: Operand::Copy(Place::from(cmp)),
        targets: SwitchTargets::new(std::iter::once((0, out)), in_bb),
    };
    true
}

/// Trust: does `local` appear anywhere in `body` other than at the two locations
/// `simplify_range_comparison` is about to rewrite — the `_c1 = Le(const lo, copy x)` statement at
/// `(def_block, def_stmt)` and `def_block`'s terminator, which immediately follows it?
///
/// Deliberately a whole-body scan rather than a dominance or liveness query: MIR locals are not in
/// SSA form, so "is this local read anywhere else" is the only question that makes the statement
/// safe to delete, and it is the cheap one.
fn local_read_outside<'tcx>(
    body: &Body<'tcx>,
    local: Local,
    def_block: BasicBlock,
    def_stmt: usize,
) -> bool {
    struct Search {
        local: Local,
        def_block: BasicBlock,
        def_stmt: usize,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for Search {
        fn visit_local(&mut self, local: Local, _context: PlaceContext, location: Location) {
            if local != self.local || self.found {
                return;
            }
            // The def statement itself and the terminator one index past it are being replaced.
            let rewritten = location.block == self.def_block
                && (location.statement_index == self.def_stmt
                    || location.statement_index == self.def_stmt + 1);
            if !rewritten {
                self.found = true;
            }
        }
    }
    let mut search = Search { local, def_block, def_stmt, found: false };
    search.visit_body(body);
    search.found
}

/// Returns the first case target if all targets have an equal number of statements and identical destination.
fn candidate_match<'tcx>(body: &Body<'tcx>, switch_bb: BasicBlock) -> bool {
    use itertools::Itertools;
    let targets = match &body.basic_blocks[switch_bb].terminator().kind {
        TerminatorKind::SwitchInt {
            discr: Operand::Copy(_) | Operand::Move(_), targets, ..
        } => targets,
        // Only optimize switch int statements
        _ => return false,
    };
    // We require that the possible target blocks don't contain this block.
    if targets.all_targets().contains(&switch_bb) {
        return false;
    }
    // We require that the possible target blocks all be distinct.
    if !targets.is_distinct() {
        return false;
    }
    // Check that destinations are identical, and if not, then don't optimize this block
    targets
        .all_targets()
        .iter()
        .map(|&bb| &body.basic_blocks[bb])
        .filter(|bb| !bb.is_empty_unreachable())
        .map(|bb| (bb.statements.len(), &bb.terminator().kind))
        .all_equal()
}

fn simplify_match<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    body: &mut Body<'tcx>,
    switch_bb: BasicBlock,
) -> bool {
    let (discr, targets) = match &body.basic_blocks[switch_bb].terminator().kind {
        TerminatorKind::SwitchInt { discr, targets, .. } => (discr, targets),
        _ => unreachable!(),
    };
    let mut simplify_match = SimplifyMatch {
        tcx,
        typing_env,
        patch: MirPatch::new(body),
        body,
        switch_bb,
        discr,
        discr_local: None,
        discr_ty: discr.ty(body.local_decls(), tcx),
    };
    let reachable_cases: Vec<_> =
        targets.iter().filter(|&(_, bb)| !body.basic_blocks[bb].is_empty_unreachable()).collect();
    let mut new_stmts = Vec::new();
    let otherwise = if body.basic_blocks[targets.otherwise()].is_empty_unreachable() {
        None
    } else {
        Some(targets.otherwise())
    };
    // We can patch the terminator to goto because there is a single target.
    match (reachable_cases.len(), otherwise.is_none()) {
        (1, true) | (0, false) => {
            let mut patch = simplify_match.patch;
            remove_successors_from_switch(tcx, switch_bb, body, &mut patch, |bb| {
                body.basic_blocks[bb].is_empty_unreachable()
            });
            patch.apply(body);
            return true;
        }
        _ => {}
    }
    let Some(&(_, first_case_bb)) = reachable_cases.first() else {
        return false;
    };
    let stmt_len = body.basic_blocks[first_case_bb].statements.len();
    let mut cases = Vec::with_capacity(stmt_len);
    // Check at each position in the basic blocks whether these statements can be unified.
    for index in 0..stmt_len {
        cases.clear();
        let otherwise = otherwise.map(|bb| &body.basic_blocks[bb].statements[index].kind);
        for &(case, bb) in &reachable_cases {
            cases.push((case, &body.basic_blocks[bb].statements[index].kind));
        }
        let Some(new_stmt) = simplify_match.try_unify_stmts(index, &cases, otherwise) else {
            return false;
        };
        new_stmts.push(new_stmt);
    }
    // Take ownership of items now that we know we can optimize.
    let discr = discr.clone();

    let statement_index = body.basic_blocks[switch_bb].statements.len();
    let parent_end = Location { block: switch_bb, statement_index };
    let mut patch = simplify_match.patch;
    if let Some(discr_local) = simplify_match.discr_local {
        patch.add_statement(parent_end, StatementKind::StorageLive(discr_local));
        patch.add_assign(parent_end, Place::from(discr_local), Rvalue::Use(discr, WithRetag::No));
    }
    for new_stmt in new_stmts {
        patch.add_statement(parent_end, new_stmt);
    }
    if let Some(discr_local) = simplify_match.discr_local {
        patch.add_statement(parent_end, StatementKind::StorageDead(discr_local));
    }
    patch.patch_terminator(switch_bb, body.basic_blocks[first_case_bb].terminator().kind.clone());
    patch.apply(body);
    true
}

/// Check if the cast constant using `IntToInt` is equal to the target constant.
fn can_cast(
    tcx: TyCtxt<'_>,
    src_val: impl Into<u128>,
    src_layout: TyAndLayout<'_>,
    cast_ty: Ty<'_>,
    target_scalar: ScalarInt,
) -> bool {
    let from_scalar = ScalarInt::try_from_uint(src_val.into(), src_layout.size).unwrap();
    let v = match src_layout.ty.kind() {
        ty::Uint(_) => from_scalar.to_uint(src_layout.size),
        ty::Int(_) => from_scalar.to_int(src_layout.size) as u128,
        // We can also transform the values of other integer representations (such as char),
        // although this may not be practical in real-world scenarios.
        _ => return false,
    };
    let size = match *cast_ty.kind() {
        ty::Int(t) => Integer::from_int_ty(&tcx, t).size(),
        ty::Uint(t) => Integer::from_uint_ty(&tcx, t).size(),
        _ => return false,
    };
    let v = size.truncate(v);
    let cast_scalar = ScalarInt::try_from_uint(v, size).unwrap();
    cast_scalar == target_scalar
}

fn candidate_assign<'tcx, 'a>(
    stmts: &'a [(u128, &'a StatementKind<'tcx>)],
    otherwise: Option<&'a StatementKind<'tcx>>,
) -> Option<(Place<'tcx>, Vec<(u128, &'a Rvalue<'tcx>)>, Option<&'a Rvalue<'tcx>>)> {
    let (_, first_stmt) = stmts[0];
    let (dest, _) = first_stmt.as_assign()?;
    let otherwise = if let Some(otherwise) = otherwise {
        let Some((otherwise_dest, rval)) = otherwise.as_assign() else {
            return None;
        };
        if otherwise_dest != dest {
            return None;
        }
        Some(rval)
    } else {
        None
    };
    let rvals = stmts
        .into_iter()
        .map(|&(case, stmt)| {
            let (other_dest, rval) = stmt.as_assign()?;
            if other_dest != dest {
                return None;
            }
            Some((case, rval))
        })
        .try_collect()?;
    Some((*dest, rvals, otherwise))
}

// Returns all ConstOperands if all Rvalues are ConstOperands.
fn candidate_const<'tcx, 'a>(
    rvals: &'a [(u128, &'a Rvalue<'tcx>)],
    otherwise: Option<&'a Rvalue<'tcx>>,
) -> Option<(Vec<(u128, &'a ConstOperand<'tcx>)>, Option<&'a ConstOperand<'tcx>>)> {
    // We ignore the retag mode here, which means the `Use` we insert later must be without retag.
    let otherwise = if let Some(otherwise) = otherwise {
        let Rvalue::Use(Operand::Constant(const_), _) = otherwise else {
            return None;
        };
        Some(&**const_)
    } else {
        None
    };
    let consts = rvals
        .into_iter()
        .map(|&(case, rval)| {
            let Rvalue::Use(Operand::Constant(const_), _) = rval else { return None };
            Some((case, &**const_))
        })
        .try_collect()?;
    Some((consts, otherwise))
}

// Returns the first case and others (including otherwise if present).
fn split_first_case<'a, T>(
    stmts: &'a [(u128, &'a T)],
    otherwise: Option<&'a T>,
) -> (u128, &'a T, impl Iterator<Item = &'a T>) {
    let (first_case, first) = stmts[0];
    (first_case, first, stmts[1..].into_iter().map(|&(_, val)| val).chain(otherwise))
}

// If all statements are identical, we can optimize.
fn identical_stmts<'tcx>(
    stmts: &[(u128, &StatementKind<'tcx>)],
    otherwise: Option<&StatementKind<'tcx>>,
) -> Option<StatementKind<'tcx>> {
    use itertools::Itertools;
    let (_, first_stmt, others) = split_first_case(stmts, otherwise);
    if std::iter::once(first_stmt).chain(others).all_equal() {
        return Some(first_stmt.clone());
    }
    None
}
