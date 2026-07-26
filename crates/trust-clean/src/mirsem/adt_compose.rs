// Composed ADT shapes: payload extraction, map and filter over a discriminant
// switch, decision-DAG and conjunctive chains, and the fieldless-enum clone /
// eq / then shapes. These recognise a callee's result being threaded through a
// second match without materialising an intermediate.

use super::*;

/// Recognize the ADT PAYLOAD-EXTRACTION SELECT shape (section comment above).
/// ALL of the following must hold — anything else fails closed (`None`),
/// leaving the return/VC ungrounded rather than mis-certified:
///
///   (1) `_0` is written by EXACTLY TWO `Statement::Assign`s (one per arm),
///       NEVER via a `Terminator::Call` dest — the latter excludes the
///       `unwrap_or_default` `__trust_total_clone` None arm outright.
///   (2) EXACTLY ONE `SwitchInt` in the body whose two explicit targets are
///       EXACTLY the two `_0`-writing arm blocks (a drop-elaboration switch —
///       `Result`'s post-join `Discriminant` glue — routes to non-`_0` blocks
///       and is thus not chosen; two matching switches ⇒ ambiguous ⇒ decline).
///   (3) that switch is EXHAUSTIVE with `otherwise -> Unreachable`
///       (`exhaustive_two_arm_discriminant_switch`), its discr is a
///       projectionless temp with EXACTLY ONE static `Rvalue::Discriminant(self)`
///       assignment, and `sem_discriminant_base_of_mir` resolves the base to a
///       BARE (by-value) `self` PARAMETER — which fronts `param_reassigned_by_stmt`,
///       closing the base/field reassignment attack.
///   (4) `disc_index_safe` on the `self` `Ty::Adt` — a plain `0..n` Direct tag,
///       so the switch literals ARE the variant indices (EXCLUDES niche layouts
///       `Option<&T>`/`Option<NonZero>`, where the off-MIR "which arm is which"
///       reading would be unsound).
///   (5) the PAYLOAD arm's sole `_0` write is `_0 := Use(self.Downcast(v).Field(f))`
///       off the SAME `self` local with `v == that block's switch tag` (the
///       TAG↔DOWNCAST provenance link); the DEFAULT arm's sole `_0` write is
///       `_0 := Use(Move/Copy <param>)` for a parameter OTHER than `self`.
///       EXACTLY one of each (a `_0 := Discriminant(_1)` raw-tag read, a
///       `Downcast(v) != tag`, a projection off another local, or two same-kind
///       arms all decline).
///   (6) MONOMORPHIZED + SCALAR: `reflect_enum(self_ty)` succeeds and is
///       `!is_parameterized()` (generic `Option<T>` declines); the enum has
///       EXACTLY 2 variants; the extracted field, the default parameter, and the
///       return are the exact same scalar `Ty::Int` (including width and
///       signedness); the default parameter is not reassigned; and the body has
///       a `Return` block.
#[must_use]
pub fn sem_adt_payload_extract_of_discriminant_switch(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtPayloadExtract> {
    use trust_types::{
        BasicBlock, BlockId, Operand, Projection, Rvalue, Statement, Terminator, Ty,
    };
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // No UNMODELED statement anywhere (fail-closed, like `sem_scalar_sentinel_select_shape_of`).
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // (1) `_0` written EXACTLY twice (one per arm), NEVER via a Call dest. The
    //     Call-dest gate is the `__trust_total_clone` None-arm decline: that arm
    //     writes `_0` through a `Terminator::Call` (a HAVOC sentinel), which is
    //     NOT the value-faithful `Use(<param>)` default this recognizer admits.
    if crate::prove::local_write_count(body, 0) != 2 {
        return None;
    }
    if body
        .blocks
        .iter()
        .any(|b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == 0))
    {
        return None;
    }

    // A block's SOLE projectionless `_0` write rvalue (None if it writes `_0`
    // zero or more-than-once times). A nested `fn` (not a closure) so the returned
    // borrow's lifetime is tied to the `block` argument by elision.
    fn sole_zero_write(block: &BasicBlock) -> Option<&Rvalue> {
        let mut found: Option<&Rvalue> = None;
        for s in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                if place.local == 0 && place.projections.is_empty() {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(rvalue);
                }
            }
        }
        found
    }

    // The two arm blocks are exactly the `_0`-writing blocks.
    let arm_blocks: Vec<BlockId> = body
        .blocks
        .iter()
        .filter(|b| {
            b.stmts.iter().any(|s| matches!(s, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty()))
        })
        .map(|b| b.id)
        .collect();
    if arm_blocks.len() != 2 {
        return None;
    }
    let arm_set: std::collections::HashSet<BlockId> = arm_blocks.iter().copied().collect();

    // (2) THE unique 2-target switch whose explicit targets are EXACTLY the two
    //     arm blocks (a drop-glue switch routes elsewhere; two matches ⇒ decline).
    let mut chosen: Option<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = None;
    for b in &body.blocks {
        if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b.terminator {
            if targets.len() != 2 {
                continue;
            }
            let tset: std::collections::HashSet<BlockId> =
                targets.iter().map(|(_, t)| *t).collect();
            if tset == arm_set {
                if chosen.is_some() {
                    return None; // ambiguous — two switches route to the arm blocks.
                }
                chosen = Some((discr, targets, *otherwise, b.id));
            }
        }
    }
    let (discr, targets, otherwise, switch_bid) = chosen?;

    // This is an executable entry-shape certificate, not a block-table search:
    // an otherwise-matching unreachable switch must never grant authority.
    if switch_bid != BlockId(0) {
        return None;
    }

    // (3) Exhaustive with `otherwise -> Unreachable`.
    if !exhaustive_two_arm_discriminant_switch(body, switch_bid, otherwise) {
        return None;
    }
    // The discriminant temp: projectionless Copy/Move, EXACTLY ONE static assign
    // whose rvalue is `Rvalue::Discriminant(place)`.
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
    if !dp.projections.is_empty() {
        return None;
    }
    if body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| matches!(s, Statement::Assign { place, .. } if place.local == dp.local && place.projections.is_empty()))
        .count()
        != 1
    {
        return None;
    }
    let disc_rvalue = body.blocks.iter().flat_map(|b| &b.stmts).find_map(|s| match s {
        Statement::Assign { place, rvalue, .. }
            if place.local == dp.local && place.projections.is_empty() =>
        {
            Some(rvalue)
        }
        _ => None,
    })?;
    let Rvalue::Discriminant(disc_place) = disc_rvalue else { return None };
    let switch_block = body.blocks.iter().find(|block| block.id == switch_bid)?;
    let mut entry_disc_definitions = 0usize;
    for statement in &switch_block.stmts {
        if payload_extract_cfg_marker(statement) {
            continue;
        }
        match statement {
            Statement::Assign { place, rvalue: Rvalue::Discriminant(_), .. }
                if place.local == dp.local && place.projections.is_empty() =>
            {
                entry_disc_definitions += 1;
            }
            _ => return None,
        }
    }
    if entry_disc_definitions != 1 {
        return None;
    }
    // Base resolves to a genuine parameter (this FRONTS `param_reassigned_by_stmt`,
    // closing the base/field reassignment attack — the switched value equals the
    // projected value). The by-value `self` is a BARE projectionless param.
    let _base =
        sem_discriminant_base_of_mir(body, disc_place, &param_index, Some((switch_bid, None)))?;
    if !disc_place.projections.is_empty() {
        return None;
    }
    let self_local = disc_place.local;
    if param_index(self_local).is_none() {
        return None;
    }

    // (4) `self_ty` is that param's `Ty::Adt`; `disc_index_safe` excludes niche.
    let self_ty = body.locals.get(self_local)?.ty.clone();
    let Ty::Adt { variants, .. } = &self_ty else { return None };
    if variants.is_empty() {
        return None; // not an enum.
    }
    if !self_ty.disc_index_safe() {
        return None; // niche layout — the off-MIR arm reading would be unsound.
    }

    // (5) Classify the two arms: EXACTLY one PAYLOAD arm and one DEFAULT arm, with
    //     the TAG↔DOWNCAST↔self provenance pinned equal.
    let mut payload: Option<(usize, usize)> = None; // (extract_variant, field_idx)
    let mut default_var: Option<u64> = None;
    let mut payload_block: Option<BlockId> = None;
    let mut default_block: Option<BlockId> = None;
    for (tag, blk) in targets {
        let block = body.blocks.iter().find(|b| b.id == *blk)?;
        let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = sole_zero_write(block)? else {
            return None; // e.g. `_0 := Discriminant(_1)` (raw tag) declines here.
        };
        if p.local == self_local {
            // PAYLOAD arm: `self.Downcast(v).Field(f)` with `v == tag`.
            let [Projection::Downcast(v), Projection::Field(f)] = p.projections.as_slice() else {
                return None;
            };
            if *v != usize::try_from(*tag).ok()? {
                return None; // TAG↔DOWNCAST provenance broken.
            }
            if payload.is_some() {
                return None; // two payload arms.
            }
            payload = Some((*v, *f));
            payload_block = Some(*blk);
        } else if p.projections.is_empty() {
            // DEFAULT arm: a bare parameter OTHER than `self`.
            let idx = param_index(p.local)?;
            if default_var.is_some() {
                return None; // two default arms.
            }
            default_var = Some(idx);
            default_block = Some(*blk);
        } else {
            return None; // a projection off some other local.
        }
    }
    let (extract_variant, extract_field_idx) = payload?;
    let default_var = default_var?;
    let payload_block = payload_block?;
    let default_block = default_block?;

    // (6) MONOMORPHIZED + SCALAR gates.
    if variants.len() != 2 {
        return None;
    }
    let is_scalar_int = |t: &Ty| matches!(t, Ty::Int { .. });
    let ext_variant_def = variants.get(extract_variant)?;
    let (_, field_ty) = ext_variant_def.fields.get(extract_field_idx)?;
    if !is_scalar_int(field_ty) {
        return None; // non-scalar payload (e.g. `Option<String>`) declines.
    }
    let default_local = usize::try_from(default_var).ok()?.checked_add(1)?;
    let default_ty = &body.locals.get(default_local)?.ty;
    if !is_scalar_int(default_ty) {
        return None;
    }
    if !is_scalar_int(&body.return_ty) {
        return None;
    }
    if default_ty != field_ty || &body.return_ty != field_ty {
        return None; // the recursor carrier must equal both executable arm/result types.
    }
    if param_reassigned_by_stmt(body, default_local) {
        return None; // a reassigned default param is not entry-time value-faithful.
    }
    // Generic `Option<T>` declines (its variant-field types need the enum's Type
    // params in scope — deferred, fail-closed).
    let carrier = crate::reflect::reflect_enum(&self_ty)?;
    if carrier.is_parameterized() {
        return None;
    }
    // Bind the recognized equations to the complete reachable executable CFG.
    // This also proves that the function actually reaches a return after either
    // arm and rejects an unreachable decoy switch or an unmodeled tail.
    if !payload_extract_cfg_is_exact(
        body,
        switch_bid,
        otherwise,
        payload_block,
        default_block,
        self_local,
        default_local,
        extract_variant,
    ) {
        return None;
    }

    Some(SemAdtPayloadExtract { self_ty, extract_variant, extract_field_idx, default_var })
}

/// EXACT-ONLY certified-callee resolution for the CLOSURE-composition lane — the
/// MANDATORY adversarial gate (2026-07-18). Unlike [`resolve_certified_callee`],
/// this NEVER falls through to the unique-`::`-suffix arm.
///
/// WHY (2 of 3 skeptics converged): on the closure lane `Ty::Closure.name` and the
/// per-run registry keys (`func.def_path`) come from the SAME def-path printer, so
/// a certified closure ALWAYS has an EXACT key — any `::`-suffix hit is therefore,
/// BY CONSTRUCTION, a DIFFERENT closure (a nested-module `inner::map_add1::{closure#0}`
/// whose key is a proper suffix-superstring of a top-level `map_add1::{closure#0}`).
/// Resolving to it borrows the WRONG closure's certificate — e.g. certifying the map
/// over the uncertified `|x| x+1` (which aborts on `Some(i32::MAX)`) by matching the
/// certified `|x| x` sibling — a false certification. Exact def-path equality only;
/// exact-miss means "not certified", NEVER "less qualified". Returns
/// `(resolved_key, fact, registry_index)`.
pub(super) fn resolve_certified_callee_exact<'a>(
    callees: &'a std::collections::BTreeMap<String, CalleeFact>,
    callee: &str,
) -> Option<(&'a str, &'a CalleeFact, u64)> {
    let (k, f) = callees.get_key_value(callee)?;
    let id = callees.keys().position(|x| x == k)?;
    Some((k.as_str(), f, u64::try_from(id).ok()?))
}

/// Recognize the W6 increment-1 CLOSURE-COMPOSITION shape (section comment above).
/// ALL of the following gates must hold — anything else fails closed (`None`),
/// leaving the mono map instance ungrounded rather than mis-certified:
///
///   (1) EXACTLY two params: a by-value 2-variant enum `self` and an IMMUTABLE-kind
///       closure — `Ty::Closure { call: Fn|FnOnce([Int]) -> Int }`. Trust: W6
///       increment-3 (2026-07-18) — CAPTURING closures (`upvars.len() > 0`) are now
///       ADMITTED: the env is passed WHOLE (gate 4) and the captures ride inside the
///       env VALUE the callResult carrier pins (MODEL-ONLY, not an `f(x, k)` value
///       claim). `FnMut` (mutable-borrow env) STILL DECLINES. Neither param is
///       reassigned (`param_reassigned_by_stmt`, mutable-alias/call-dest hardened).
///   (2) THE unique 2-target `SwitchInt` whose discr is a projectionless temp with
///       EXACTLY ONE static `Rvalue::Discriminant(self)` assignment; EXHAUSTIVE with
///       `otherwise -> Unreachable`; `disc_index_safe` (EXCLUDES niche layouts); the
///       enum reflects to a `!is_parameterized()` 2-constructor carrier.
///   (3) TAG↔DOWNCAST provenance: the CALL arm reads `_x := Use(Move/Copy
///       self.Downcast(v).Field(f))` off the SAME `self` local with `v == the CALL
///       arm's switch tag`; `_x` sole-writer.
///   (4) env chain `_e := Move(_2)` sole-writer single step, NO field projections on
///       `_2`/`_e` (a capturing `_2.0` field read would decline here too).
///   (5) args-tuple `_t := Aggregate(Tuple, [Copy/Move _x])` sole-writer, EXACTLY one
///       element that IS the gate-3 payload temp `_x`; tuple arity (1) == the
///       `Closure.call.params` arity (1).
///   (6) the Call actuals are EXACTLY `(Move _e, Move _t)`; the callee is resolved
///       EXACT-ONLY on the env operand's `Ty::Closure.name`
///       ([`resolve_certified_callee_exact`] — NEVER the span-shaped `func` string,
///       NEVER a `::`-suffix fallback); the `CalleeFact` is present with
///       `arg_count == 2` (env + untupled x) and `requires == Some(vec![])`
///       (spec-free; requires-bearing closures are DEFERRED); `_y` (the call dest)
///       is a projectionless Int sole-written by this one Call; `atomic`/`is_foreign`
///       decline.
///   (7) construction: the CALL arm's continuation writes `_0 := Aggregate(Adt{E,
///       call_variant}, [Move/Copy _y])` (variant tag == the CALL switch tag) then
///       `Goto JOIN`; the NONE arm writes `_0 := Aggregate(Adt{E, none_variant}, [])`
///       (nullary, variant tag == the NONE switch tag) then `Drop(_2) -> JOIN` (the
///       bare zero-upvar closure param — the ONLY admitted Drop anywhere); `_0`
///       written EXACTLY twice, NEVER a Call dest; JOIN is `Return`. The BLOCK SET is
///       the 6-block whitelist and the projectionless-Assign SET is exactly
///       `{disc, _x, _e, _t, _0×2}` (any projected write, extra block, or extra
///       statement declines) — closing "self used after the move-out", alias writes,
///       and rogue-block attacks.
///
/// `callees` is the certified registry (the SAME the call-return lane consumes); the
/// closure must already be a certified FULLY_FAITHFUL leaf for gate 6 to resolve.
#[must_use]
pub fn sem_adt_map_compose_of_discriminant_switch(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemAdtMapCompose> {
    use trust_types::{
        AggregateKind, BasicBlock, BlockId, ClosureCallKind, Operand, Projection, Rvalue, Statement,
        Terminator, Ty,
    };
    if callees.is_empty() {
        return None; // no certified callee ⇒ the closure can never resolve.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let is_int = |t: &Ty| matches!(t, Ty::Int { .. });

    // Every block-table lookup below must be unambiguous. A duplicate id would let
    // `find` validate one block while CFG traversal observes the same id as that
    // validated block, silently quarantining the duplicate's effects.
    let block_ids: std::collections::HashSet<BlockId> =
        body.blocks.iter().map(|block| block.id).collect();
    if block_ids.len() != body.blocks.len() {
        return None;
    }

    // Exact statement vocabulary: assignments plus storage-lifetime markers only.
    // In particular, an `Intrinsic`, `SetDiscriminant`, `Deinit`, or `Retag` is
    // executable/effectful residue and must not be skipped merely because the loop
    // below is looking for Assigns. Also reject projected Assign writes outright.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
        !matches!(s, Statement::Assign { .. } | Statement::StorageLive(_) | Statement::StorageDead(_))
    })
    {
        return None;
    }
    if body.blocks.iter().flat_map(|b| &b.stmts).any(
        |s| matches!(s, Statement::Assign { place, .. } if !place.projections.is_empty()),
    ) {
        return None;
    }

    // (1a) EXACTLY two params.
    if arg_count != 2 {
        return None;
    }

    // A block's SOLE projectionless `_0` write rvalue (None if it writes `_0` zero or
    // more than once).
    fn sole_zero_write(block: &BasicBlock) -> Option<&Rvalue> {
        let mut found: Option<&Rvalue> = None;
        for s in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                if place.local == 0 && place.projections.is_empty() {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(rvalue);
                }
            }
        }
        found
    }

    // (7a) `_0` statement-written 1 or 2 times (the MapWrap CALL-continuation adds a
    // second `_0 := Some(dest)` statement; the AndThenFlat continuation writes `_0`
    // via the CALL dest instead). The EXACT per-mode count + the call-dest-`_0`
    // discipline are asserted below, once the closure's return type fixes the mode.
    if !matches!(crate::prove::local_write_count(body, 0), 1 | 2) {
        return None;
    }

    // (2) THE unique 2-target SwitchInt (any second one ⇒ ambiguous ⇒ decline).
    let mut switch: Option<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = None;
    for b in &body.blocks {
        if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b.terminator {
            if targets.len() != 2 {
                continue;
            }
            if switch.is_some() {
                return None;
            }
            switch = Some((discr, targets, *otherwise, b.id));
        }
    }
    let (discr, targets, otherwise, switch_bid) = switch?;
    if !exhaustive_two_arm_discriminant_switch(body, switch_bid, otherwise) {
        return None;
    }
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
    if !dp.projections.is_empty() {
        return None;
    }
    let (disc_definition_block, disc_definition_statement, disc_rvalue) =
        unique_local_definition_dominating(body, dp.local, switch_bid, None)?;
    let Rvalue::Discriminant(disc_place) = disc_rvalue else { return None };
    // Base resolves to a bare by-value `self` PARAMETER (fronts `param_reassigned_by_stmt`).
    let _base = sem_discriminant_base_of_mir(
        body,
        disc_place,
        &param_index,
        Some((disc_definition_block, Some(disc_definition_statement))),
    )?;
    if !disc_place.projections.is_empty() {
        return None;
    }
    let self_local = disc_place.local;
    if param_index(self_local).is_none() {
        return None;
    }
    let self_ty = body.locals.get(self_local)?.ty.clone();
    let Ty::Adt { name: enum_name, variants, .. } = &self_ty else { return None };
    if variants.len() != 2 {
        return None;
    }
    if !self_ty.disc_index_safe() {
        return None;
    }
    let carrier = crate::reflect::reflect_enum(&self_ty)?;
    if carrier.is_parameterized() || carrier.constructors.len() != 2 {
        return None;
    }
    let enum_name = enum_name.clone();

    // (1b) the OTHER param is the NON-CAPTURING FnOnce closure `_2`.
    let closure_local = (1..=arg_count).find(|&l| l != self_local)?;
    if param_reassigned_by_stmt(body, self_local) || param_reassigned_by_stmt(body, closure_local) {
        return None;
    }
    let Ty::Closure { name: closure_name, upvars: _upvars, call } = &body.locals.get(closure_local)?.ty
    else {
        return None;
    };
    // Trust: W6 increment-3 (CAPTURING closures, 2026-07-18) — the increment-1
    // `upvars == []` gate was launch conservatism, NOW RELAXED. The mono map body
    // passes the closure env WHOLE (`_e := Move(_2)`, no field projections — gate 4
    // below, TRUE for capturing instances too), and the callResult carrier is keyed
    // on `(callee_id, env-operand)` where the env operand resolves to the bare
    // closure-param `Var` (sole-writer Move chain — the `env_operand` built below).
    // Captures live INSIDE that env VALUE, so the callResult being an opaque TOTAL
    // function of the pinned callee + the env value is the SAME MODEL-ONLY claim every
    // certified call lane already makes for a value-carrying arg — the env operand now
    // carries captures, deterministically; this is MODEL-ONLY and NOT an `f(x, k)`
    // value claim over the individual captures. Admit `upvars.len() > 0` WHEN:
    //   (i)   the env operand resolves to the bare closure-param `Var` (sole-writer
    //         Move chain, no projections — enforced by gate 4 + the `env_operand`
    //         construction below, UNCHANGED);
    //   (ii)  the call kind is IMMUTABLE (`Fn`/`FnOnce`); `FnMut` STILL DECLINES — a
    //         mutable env could rebind captures between calls, breaking the stable
    //         value model (matches the capturing-leaf-read gate in
    //         `sem_field_read_operand`);
    //   (iii) every OTHER gate is BYTE-IDENTICAL (exact-match callee, TAG↔DOWNCAST,
    //         tuple arity, the 6-block whitelist, …) — unchanged below.
    // Non-capturing behavior is unaffected: the increment-1/2 corpora are all `FnOnce`,
    // for which `Fn | FnOnce` is a superset that admits exactly as before.
    let Some(call_sig) = call else { return None };
    if !matches!(call_sig.kind, ClosureCallKind::Fn | ClosureCallKind::FnOnce) {
        return None; // FnMut (mutable-borrow env) — DEFERRED / fail closed.
    }
    let [p0] = call_sig.params.as_slice() else {
        return None; // EXACTLY one untupled call param.
    };
    if !is_int(p0) {
        return None;
    }
    // The closure's declared RETURN fixes the composition mode:
    //   * `Int`                       ⇒ `map`      (`MapWrap`)   — Some-rewrap continuation.
    //   * the SAME 2-variant `Option` ⇒ `and_then` (`AndThenFlat`) — bare-return continuation.
    // Any other return type declines fail-closed (`filter`'s `Bool` predicate is a
    // DIFFERENT lane; a foreign enum is outside the modeled carrier).
    let kind = match &call_sig.ret {
        Some(t) if is_int(t) => ComposeReturn::MapWrap,
        Some(t) => {
            let Some(ret_carrier) = crate::reflect::reflect_enum(t) else { return None };
            if ret_carrier.name != carrier.name
                || ret_carrier.is_parameterized()
                || ret_carrier.constructors.len() != 2
            {
                return None; // not the SAME registered Option carrier — decline.
            }
            ComposeReturn::AndThenFlat
        }
        None => return None,
    };
    let closure_params_arity = call_sig.params.len(); // == 1
    let closure_name = closure_name.clone();

    // The two switch arms: EXACTLY one writes `_0` directly (the NONE arm); the other
    // is the CALL-setup block (whose `_0` write lives in its Call continuation).
    let writes_zero = |bid: BlockId| -> bool {
        body.blocks
            .iter()
            .find(|b| b.id == bid)
            .is_some_and(|b| b.stmts.iter().any(|s| matches!(s, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty())))
    };
    let mut none_arm: Option<(usize, BlockId)> = None;
    let mut call_arm: Option<(usize, BlockId)> = None;
    for (tag, blk) in targets {
        let tag = usize::try_from(*tag).ok()?;
        if writes_zero(*blk) {
            if none_arm.is_some() {
                return None;
            }
            none_arm = Some((tag, *blk));
        } else {
            if call_arm.is_some() {
                return None;
            }
            call_arm = Some((tag, *blk));
        }
    }
    let (none_tag, none_bid) = none_arm?;
    let (call_tag, call_setup_bid) = call_arm?;
    if none_tag == call_tag {
        return None;
    }

    // (7b) NONE arm: `_0 := Aggregate(Adt{E, none_tag}, [])` (nullary) + `Drop(_2) -> JOIN`.
    let none_block = body.blocks.iter().find(|b| b.id == none_bid)?;
    let Rvalue::Aggregate(AggregateKind::Adt { name: nname, variant: nvar, .. }, nops) =
        sole_zero_write(none_block)?
    else {
        return None;
    };
    if *nname != enum_name || *nvar != none_tag || !nops.is_empty() {
        return None;
    }
    let Terminator::Drop { place: drop_place, target: none_join, .. } = &none_block.terminator else {
        return None;
    };
    if drop_place.local != closure_local || !drop_place.projections.is_empty() {
        return None; // Drop admitted ONLY for the bare zero-upvar closure param.
    }
    // The ONLY Drop anywhere is this one (a Drop of any other place declines).
    if body.blocks.iter().filter(|b| matches!(&b.terminator, Terminator::Drop { .. })).count() != 1 {
        return None;
    }

    // (3)(4)(5) CALL-setup block: payload extract, env chain, args tuple, then Call.
    let call_setup = body.blocks.iter().find(|b| b.id == call_setup_bid)?;
    let mut payload_temp: Option<usize> = None;
    let mut env_temp: Option<usize> = None;
    let mut tuple_temp: Option<usize> = None;
    let mut tuple_elem_local: Option<usize> = None;
    let mut payload_statement: Option<usize> = None;
    let mut tuple_statement: Option<usize> = None;
    for (statement_index, s) in call_setup.stmts.iter().enumerate() {
        let Statement::Assign { place, rvalue, .. } = s else { continue }; // Storage-transparent.
        let dst = place.local; // projectionless (rejected above otherwise).
        match rvalue {
            // (3) payload extract: `_x := Use(Move/Copy self.Downcast(call_tag).Field(f))`.
            Rvalue::Use(Operand::Move(p) | Operand::Copy(p)) if p.local == self_local => {
                let [Projection::Downcast(v), Projection::Field(_f)] = p.projections.as_slice()
                else {
                    return None;
                };
                if *v != call_tag {
                    return None; // TAG↔DOWNCAST provenance broken.
                }
                if payload_temp.is_some() {
                    return None;
                }
                payload_temp = Some(dst);
                payload_statement = Some(statement_index);
            }
            // (4) env chain: `_e := Move/Copy(_2)`, NO field projections on `_2`.
            Rvalue::Use(Operand::Move(p) | Operand::Copy(p)) if p.local == closure_local => {
                if !p.projections.is_empty() {
                    return None; // a `_2.0` upvar field read (capturing) declines.
                }
                if env_temp.is_some() {
                    return None;
                }
                env_temp = Some(dst);
            }
            // (5) args tuple: `_t := Aggregate(Tuple, [Copy/Move _x])`, EXACTLY one elem.
            Rvalue::Aggregate(AggregateKind::Tuple, elems) => {
                // (5) tuple arity must equal the closure's untupled call arity (1).
                if elems.len() != closure_params_arity {
                    return None;
                }
                let [Operand::Copy(e) | Operand::Move(e)] = elems.as_slice() else {
                    return None;
                };
                if !e.projections.is_empty() {
                    return None;
                }
                if tuple_temp.is_some() {
                    return None;
                }
                tuple_temp = Some(dst);
                tuple_elem_local = Some(e.local);
                tuple_statement = Some(statement_index);
            }
            _ => return None, // any other statement in the CALL arm ⇒ fail closed.
        }
    }
    let payload_temp = payload_temp?;
    let env_temp = env_temp?;
    let tuple_temp = tuple_temp?;
    let tuple_elem_local = tuple_elem_local?;
    if payload_statement? >= tuple_statement? {
        return None; // the payload value must be defined before the tuple reads it.
    }
    // (5) the tuple's sole element IS the gate-3 Downcast-field payload temp.
    if tuple_elem_local != payload_temp {
        return None;
    }
    // sole-writer discipline on the three temps.
    for t in [payload_temp, env_temp, tuple_temp] {
        if crate::prove::local_write_count(body, t) != 1 {
            return None;
        }
    }
    // the payload temp is Int.
    if !matches!(body.locals.get(payload_temp).map(|l| &l.ty), Some(Ty::Int { .. })) {
        return None;
    }

    // (6) the Call terminator.
    let Terminator::Call {
        func: _call_func,
        args: call_args,
        dest: call_dest,
        target: call_target,
        atomic,
        is_foreign,
        ..
    } = &call_setup.terminator
    else {
        return None;
    };
    if atomic.is_some() || *is_foreign {
        return None;
    }
    let call_target = (*call_target)?;
    if !call_dest.projections.is_empty() {
        return None;
    }
    let call_dest_local = call_dest.local;
    // The CALL dest type + write discipline are mode-specific:
    //   * MapWrap     — dest is a fresh `Int` temp (the Some-payload), NEVER
    //     statement-written, sole-written by THIS one Call; `_0` is NEVER a Call dest
    //     (its two writes are the None-arm + the Some-rewrap statements).
    //   * AndThenFlat — dest IS `_0` (the SAME `Option` carrier); `_0`'s ONLY
    //     statement write is the None arm (count 1) and its ONLY Call-dest write is here.
    match kind {
        ComposeReturn::MapWrap => {
            if !matches!(body.locals.get(call_dest_local).map(|l| &l.ty), Some(Ty::Int { .. })) {
                return None;
            }
            if crate::prove::local_write_count(body, call_dest_local) != 0 {
                return None;
            }
            if body.blocks.iter().any(|b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == 0)) {
                return None; // `_0` is never a Call dest in the Some-rewrap shape.
            }
        }
        ComposeReturn::AndThenFlat => {
            if call_dest_local != 0 {
                return None; // the flat return writes `_0` directly.
            }
            let Some(Ty::Adt { name: dname, .. }) = body.locals.get(0).map(|l| &l.ty) else {
                return None;
            };
            if *dname != enum_name {
                return None; // the dest must be the SAME `Option` carrier.
            }
            if crate::prove::local_write_count(body, 0) != 1 {
                return None; // `_0`'s ONLY statement write is the None arm.
            }
        }
    }
    // EXACTLY one Call whose dest is `call_dest_local` (a second call declines).
    if body.blocks.iter().filter(|b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == call_dest_local && dest.projections.is_empty())).count() != 1
    {
        return None;
    }
    // Actuals EXACTLY `(Move _e, Move _t)`.
    let [Operand::Move(a0), Operand::Move(a1)] = call_args.as_slice() else {
        return None;
    };
    if a0.local != env_temp
        || !a0.projections.is_empty()
        || a1.local != tuple_temp
        || !a1.projections.is_empty()
    {
        return None;
    }

    // (7c) CALL continuation — mode-specific:
    let cont_block = body.blocks.iter().find(|b| b.id == call_target)?;
    let cont_join: BlockId = match kind {
        ComposeReturn::MapWrap => {
            // `_0 := Aggregate(Adt{E, call_tag}, [Move/Copy _y])` + Goto JOIN.
            let Rvalue::Aggregate(AggregateKind::Adt { name: cname, variant: cvar, .. }, cops) =
                sole_zero_write(cont_block)?
            else {
                return None;
            };
            if *cname != enum_name || *cvar != call_tag {
                return None;
            }
            let [Operand::Move(cp) | Operand::Copy(cp)] = cops.as_slice() else {
                return None;
            };
            if cp.local != call_dest_local || !cp.projections.is_empty() {
                return None;
            }
            let Terminator::Goto(j) = &cont_block.terminator else {
                return None;
            };
            *j
        }
        ComposeReturn::AndThenFlat => {
            // The flat return already wrote `_0` via the CALL dest; the continuation
            // ONLY drops storage (NO `Statement::Assign` at all) before joining.
            if cont_block.stmts.iter().any(|s| matches!(s, Statement::Assign { .. })) {
                return None;
            }
            let Terminator::Goto(j) = &cont_block.terminator else {
                return None;
            };
            *j
        }
    };

    // JOIN: the SAME block for both arms, terminating in `Return`.
    if *none_join != cont_join {
        return None;
    }
    let join_block = body.blocks.iter().find(|b| b.id == cont_join)?;
    if !matches!(join_block.terminator, Terminator::Return) {
        return None;
    }

    // Robustness: EXACTLY the 6-block whitelist, and the projectionless-Assign SET is
    // exactly {disc, _x, _e, _t, _0(none)} PLUS the MapWrap Some-rewrap `_0` write
    // (closes "self used after move-out", extra blocks, and stray statements —
    // anything else declines fail-closed).
    let recognized: std::collections::HashSet<BlockId> =
        [switch_bid, otherwise, none_bid, call_setup_bid, call_target, cont_join]
            .into_iter()
            .collect();
    if recognized.len() != 6 || block_ids != recognized {
        return None;
    }
    let total_assigns = body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| matches!(s, Statement::Assign { place, .. } if place.projections.is_empty()))
        .count();
    // MapWrap: disc, _x, _e, _t, _0(none), _0(some-rewrap) = 6.
    // AndThenFlat: disc, _x, _e, _t, _0(none) = 5 (the CALL writes `_0` via its dest).
    let expected_assigns = match kind {
        ComposeReturn::MapWrap => 6,
        ComposeReturn::AndThenFlat => 5,
    };
    if total_assigns != expected_assigns {
        return None;
    }

    // (6) EXACT-ONLY closure-callee resolution + spec-free CalleeFact.
    let (resolved, fact, callee_id) = resolve_certified_callee_exact(callees, &closure_name)?;
    if resolved == func.def_path {
        return None; // self-recursion (defensive) — fail closed.
    }
    if fact.arg_count != 2 {
        return None; // env + untupled x.
    }
    match &fact.requires {
        Some(v) if v.is_empty() => {}
        _ => return None, // requires-bearing OR unknown precondition — DEFERRED / fail closed.
    }

    let env_operand = SemOperand::Var(param_index(closure_local)?);
    Some(SemAdtMapCompose {
        kind,
        self_ty,
        call_variant: call_tag,
        none_variant: none_tag,
        callee: resolved.to_string(),
        callee_id,
        env_operand,
    })
}

/// Recognize the W6 increment-2 PREDICATE-FILTER shape (section comment above). ALL
/// gates must hold — anything else fails closed (`None`). Reuses every base gate of
/// the `map`/`and_then` recognizer (EXACTLY two params, a non-capturing spec-free
/// FnOnce closure, THE exhaustive discriminant SwitchInt, TAG↔DOWNCAST provenance,
/// env-chain no-projections, args-tuple arity, EXACT-only callee resolution) and
/// ADDS: (i) the closure signature is `FnOnce(&Int) -> Bool`; (ii) the args tuple
/// packs a `Ref(false, payload)` (immutable, the W-REF-FWD ref-transparency); (iii)
/// a SECOND `SwitchInt` on the `Bool` call result orients keep-vs-drop; (iv) the KEEP
/// arm RECONSTRUCTS `Some(payload)` from the SAME extracted payload local; (v) the
/// DROP arm drops the payload and constructs `None`; (vi) every `Drop` targets the
/// bare payload or closure param; (vii) the unwind `Resume` block is UNREACHABLE from
/// entry (the fail-closed reachability walk); (viii) the entry-reachable block set is
/// EXACTLY the 9 recognized roles with EXACTLY 9 projectionless `Assign`s.
#[must_use]
pub fn sem_adt_filter_compose_of_discriminant_switch(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemAdtFilterCompose> {
    use trust_types::{
        AggregateKind, BasicBlock, BlockId, ClosureCallKind, Operand, Projection, Rvalue, Statement,
        Terminator, Ty,
    };
    if callees.is_empty() {
        return None;
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let is_int = |t: &Ty| matches!(t, Ty::Int { .. });

    // No UNMODELED statement, and NO projected `Assign` write anywhere.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }
    if body.blocks.iter().flat_map(|b| &b.stmts).any(
        |s| matches!(s, Statement::Assign { place, .. } if !place.projections.is_empty()),
    ) {
        return None;
    }
    if arg_count != 2 {
        return None;
    }

    fn sole_zero_write(block: &BasicBlock) -> Option<&Rvalue> {
        let mut found: Option<&Rvalue> = None;
        for s in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                if place.local == 0 && place.projections.is_empty() {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(rvalue);
                }
            }
        }
        found
    }

    // The two SwitchInts: THE discriminant switch (unique 2-target) and THE Bool
    // switch (unique 1-target). Any other switch cardinality declines.
    let mut disc_switch: Option<BlockId> = None;
    let mut bool_switch: Option<BlockId> = None;
    for b in &body.blocks {
        if let Terminator::SwitchInt { targets, .. } = &b.terminator {
            match targets.len() {
                2 => {
                    if disc_switch.is_some() {
                        return None;
                    }
                    disc_switch = Some(b.id);
                }
                1 => {
                    if bool_switch.is_some() {
                        return None;
                    }
                    bool_switch = Some(b.id);
                }
                _ => return None,
            }
        }
    }
    let switch_bid = disc_switch?;
    let bool_switch_bid = bool_switch?;
    if switch_bid != BlockId(0) {
        return None; // the discriminant switch must be the ENTRY (the reachability root).
    }

    let disc_block = body.blocks.iter().find(|b| b.id == switch_bid)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &disc_block.terminator else {
        return None;
    };
    if !exhaustive_two_arm_discriminant_switch(body, switch_bid, *otherwise) {
        return None;
    }
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
    if !dp.projections.is_empty() {
        return None;
    }
    if body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| matches!(s, Statement::Assign { place, .. } if place.local == dp.local && place.projections.is_empty()))
        .count()
        != 1
    {
        return None;
    }
    let disc_rvalue = body.blocks.iter().flat_map(|b| &b.stmts).find_map(|s| match s {
        Statement::Assign { place, rvalue, .. }
            if place.local == dp.local && place.projections.is_empty() =>
        {
            Some(rvalue)
        }
        _ => None,
    })?;
    let Rvalue::Discriminant(disc_place) = disc_rvalue else { return None };
    let _base = sem_discriminant_base_of_mir(
        body,
        disc_place,
        &param_index,
        Some((switch_bid, None)),
    )?;
    if !disc_place.projections.is_empty() {
        return None;
    }
    let self_local = disc_place.local;
    if param_index(self_local).is_none() {
        return None;
    }
    let self_ty = body.locals.get(self_local)?.ty.clone();
    let Ty::Adt { name: enum_name, variants, .. } = &self_ty else { return None };
    if variants.len() != 2 {
        return None;
    }
    if !self_ty.disc_index_safe() {
        return None;
    }
    let carrier = crate::reflect::reflect_enum(&self_ty)?;
    if carrier.is_parameterized() || carrier.constructors.len() != 2 {
        return None;
    }
    let enum_name = enum_name.clone();

    // The OTHER param is the NON-CAPTURING `FnOnce(&Int) -> Bool` predicate closure.
    let closure_local = (1..=arg_count).find(|&l| l != self_local)?;
    if param_reassigned_by_stmt(body, self_local) || param_reassigned_by_stmt(body, closure_local) {
        return None;
    }
    let Ty::Closure { name: closure_name, upvars: _upvars, call } = &body.locals.get(closure_local)?.ty
    else {
        return None;
    };
    // Trust: W6 increment-3 (CAPTURING closures, 2026-07-18) — the increment-2
    // `upvars == []` gate is RELAXED on the SAME reasoning as the map/and_then lane:
    // the mono filter body passes the closure env WHOLE (gate below), captures live
    // inside that env value, and the callResult carrier is an opaque total function of
    // `(callee_id, env-value)` — MODEL-ONLY, NOT a `predicate(x, k)` value claim. Admit
    // `upvars.len() > 0` for IMMUTABLE call kinds only; `FnMut` STILL DECLINES (a
    // mutable env breaks the stable-value model). Every other gate is byte-identical.
    let Some(call_sig) = call else { return None };
    if !matches!(call_sig.kind, ClosureCallKind::Fn | ClosureCallKind::FnOnce) {
        return None; // FnMut (mutable-borrow env) — DEFERRED / fail closed.
    }
    // EXACTLY one param: an IMMUTABLE ref to Int (`&i32`).
    let [p0] = call_sig.params.as_slice() else { return None };
    let Ty::Ref { mutable: false, inner } = p0 else { return None };
    if !is_int(&**inner) {
        return None;
    }
    // The predicate returns Bool.
    if !matches!(&call_sig.ret, Some(Ty::Bool)) {
        return None;
    }
    let closure_name = closure_name.clone();

    // The two discriminant arms: the NONE arm writes `_0` directly; the SETUP arm
    // sets up the predicate call (writes NO `_0`).
    let writes_zero_stmt = |bid: BlockId| -> bool {
        body.blocks
            .iter()
            .find(|b| b.id == bid)
            .is_some_and(|b| b.stmts.iter().any(|s| matches!(s, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty())))
    };
    let mut none_arm: Option<(usize, BlockId)> = None;
    let mut some_arm: Option<(usize, BlockId)> = None;
    for (tag, blk) in targets {
        let tag = usize::try_from(*tag).ok()?;
        if writes_zero_stmt(*blk) {
            if none_arm.is_some() {
                return None;
            }
            none_arm = Some((tag, *blk));
        } else {
            if some_arm.is_some() {
                return None;
            }
            some_arm = Some((tag, *blk));
        }
    }
    let (none_tag, none_bid) = none_arm?;
    let (some_tag, setup_bid) = some_arm?;
    if none_tag == some_tag {
        return None;
    }

    // NONE arm: `_0 := Aggregate(Adt{E, none_tag}, [])` (nullary) + `Drop(_2) -> JOIN`.
    let none_block = body.blocks.iter().find(|b| b.id == none_bid)?;
    let Rvalue::Aggregate(AggregateKind::Adt { name: nname, variant: nvar, .. }, nops) =
        sole_zero_write(none_block)?
    else {
        return None;
    };
    if *nname != enum_name || *nvar != none_tag || !nops.is_empty() {
        return None;
    }
    let Terminator::Drop { place: ndrop, target: none_join, .. } = &none_block.terminator else {
        return None;
    };
    if ndrop.local != closure_local || !ndrop.projections.is_empty() {
        return None;
    }

    // SETUP arm: payload extract, env chain, REF packing, args tuple, then the Call.
    let setup = body.blocks.iter().find(|b| b.id == setup_bid)?;
    let mut payload_temp: Option<usize> = None;
    let mut env_temp: Option<usize> = None;
    let mut ref_temp: Option<(usize, usize)> = None; // (dst, referent)
    let mut tuple_temp: Option<usize> = None;
    let mut tuple_elem_local: Option<usize> = None;
    for s in &setup.stmts {
        let Statement::Assign { place, rvalue, .. } = s else { continue };
        let dst = place.local;
        match rvalue {
            // payload extract: `_x := Use(Move/Copy self.Downcast(some_tag).Field(f))`.
            Rvalue::Use(Operand::Move(p) | Operand::Copy(p)) if p.local == self_local => {
                let [Projection::Downcast(v), Projection::Field(_f)] = p.projections.as_slice()
                else {
                    return None;
                };
                if *v != some_tag {
                    return None;
                }
                if payload_temp.is_some() {
                    return None;
                }
                payload_temp = Some(dst);
            }
            // env chain: `_e := Move/Copy(_2)`, NO field projections.
            Rvalue::Use(Operand::Move(p) | Operand::Copy(p)) if p.local == closure_local => {
                if !p.projections.is_empty() {
                    return None;
                }
                if env_temp.is_some() {
                    return None;
                }
                env_temp = Some(dst);
            }
            // ref packing: `_r := Ref(mutable:false, <payload>)` (immutable ONLY).
            Rvalue::Ref { mutable: false, place: referent } => {
                if !referent.projections.is_empty() {
                    return None;
                }
                if ref_temp.is_some() {
                    return None;
                }
                ref_temp = Some((dst, referent.local));
            }
            // args tuple: `_t := Aggregate(Tuple, [Copy/Move _r])`, EXACTLY one elem.
            Rvalue::Aggregate(AggregateKind::Tuple, elems) => {
                if elems.len() != call_sig.params.len() {
                    return None;
                }
                let [Operand::Copy(e) | Operand::Move(e)] = elems.as_slice() else {
                    return None;
                };
                if !e.projections.is_empty() {
                    return None;
                }
                if tuple_temp.is_some() {
                    return None;
                }
                tuple_temp = Some(dst);
                tuple_elem_local = Some(e.local);
            }
            _ => return None,
        }
    }
    let payload_temp = payload_temp?;
    let env_temp = env_temp?;
    let (ref_temp, ref_referent) = ref_temp?;
    let tuple_temp = tuple_temp?;
    let tuple_elem_local = tuple_elem_local?;
    // the ref is `&payload`; the tuple's sole element IS the ref temp.
    if ref_referent != payload_temp || tuple_elem_local != ref_temp {
        return None;
    }
    for t in [payload_temp, env_temp, ref_temp, tuple_temp] {
        if crate::prove::local_write_count(body, t) != 1 {
            return None;
        }
    }
    if !matches!(body.locals.get(payload_temp).map(|l| &l.ty), Some(Ty::Int { .. })) {
        return None;
    }
    if !matches!(body.locals.get(ref_temp).map(|l| &l.ty), Some(Ty::Ref { mutable: false, inner }) if is_int(&**inner))
    {
        return None;
    }

    // The Call: `_b = call_once(Move _e, Move _t)` → BOOLSW, dest a bare `Bool`.
    let Terminator::Call {
        args: call_args,
        dest: call_dest,
        target: call_target,
        atomic,
        is_foreign,
        ..
    } = &setup.terminator
    else {
        return None;
    };
    if atomic.is_some() || *is_foreign {
        return None;
    }
    let call_target = (*call_target)?;
    if call_target != bool_switch_bid {
        return None; // the call flows to the Bool switch.
    }
    if !call_dest.projections.is_empty() {
        return None;
    }
    let bool_temp = call_dest.local;
    if !matches!(body.locals.get(bool_temp).map(|l| &l.ty), Some(Ty::Bool)) {
        return None;
    }
    if crate::prove::local_write_count(body, bool_temp) != 0 {
        return None;
    }
    // EXACTLY one Call in the body; its dest is `_b`; `_0` is NEVER a Call dest.
    if body.blocks.iter().filter(|b| matches!(&b.terminator, Terminator::Call { .. })).count() != 1 {
        return None;
    }
    if body.blocks.iter().any(|b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == 0))
    {
        return None;
    }
    let [Operand::Move(a0), Operand::Move(a1)] = call_args.as_slice() else {
        return None;
    };
    if a0.local != env_temp
        || !a0.projections.is_empty()
        || a1.local != tuple_temp
        || !a1.projections.is_empty()
    {
        return None;
    }

    // BOOL switch: `SwitchInt(_b)` on the predicate result, ONE explicit target that
    // orients keep(true)-vs-drop(false). No statements.
    let bool_block = body.blocks.iter().find(|b| b.id == bool_switch_bid)?;
    if bool_block.stmts.iter().any(|s| matches!(s, Statement::Assign { .. })) {
        return None;
    }
    let Terminator::SwitchInt { discr: bdiscr, targets: btargets, otherwise: botherwise, .. } =
        &bool_block.terminator
    else {
        return None;
    };
    let (Operand::Copy(bdp) | Operand::Move(bdp)) = bdiscr else { return None };
    if bdp.local != bool_temp || !bdp.projections.is_empty() {
        return None;
    }
    let [(bt_val, bt_blk)] = btargets.as_slice() else { return None };
    let (keep_bid, drop_bid) = match *bt_val {
        0 => (*botherwise, *bt_blk), // explicit 0(false) → DROP; otherwise(true) → KEEP.
        1 => (*bt_blk, *botherwise), // explicit 1(true) → KEEP; otherwise(false) → DROP.
        _ => return None,
    };

    // KEEP arm: reconstruct `_y := Use(Move/Copy _x)` from the ORIGINAL payload, then
    // `_0 := Aggregate(Adt{E, some_tag}, [Move/Copy _y])` + Goto JOIN.
    let keep_block = body.blocks.iter().find(|b| b.id == keep_bid)?;
    let mut recon_temp: Option<usize> = None;
    for s in &keep_block.stmts {
        let Statement::Assign { place, rvalue, .. } = s else { continue };
        if place.local == 0 {
            continue; // the `_0` write is checked via `sole_zero_write`.
        }
        match rvalue {
            Rvalue::Use(Operand::Move(p) | Operand::Copy(p))
                if p.projections.is_empty() && p.local == payload_temp =>
            {
                if recon_temp.is_some() {
                    return None;
                }
                recon_temp = Some(place.local);
            }
            _ => return None, // any non-reconstruct statement declines.
        }
    }
    let recon_temp = recon_temp?;
    if crate::prove::local_write_count(body, recon_temp) != 1 {
        return None;
    }
    let Rvalue::Aggregate(AggregateKind::Adt { name: kname, variant: kvar, .. }, kops) =
        sole_zero_write(keep_block)?
    else {
        return None;
    };
    if *kname != enum_name || *kvar != some_tag {
        return None;
    }
    let [Operand::Move(kp) | Operand::Copy(kp)] = kops.as_slice() else {
        return None;
    };
    // the reconstructed Some payload IS the original extracted payload (requirement #3).
    if kp.local != recon_temp || !kp.projections.is_empty() {
        return None;
    }
    let Terminator::Goto(keep_join) = &keep_block.terminator else {
        return None;
    };

    // DROP arm: `Drop(_x) -> NONE2`; NONE2: `_0 := Aggregate(Adt{E, none_tag}, [])` + Goto JOIN.
    let drop_block = body.blocks.iter().find(|b| b.id == drop_bid)?;
    if drop_block.stmts.iter().any(|s| matches!(s, Statement::Assign { .. })) {
        return None;
    }
    let Terminator::Drop { place: pdrop, target: drop_none_bid, .. } = &drop_block.terminator else {
        return None;
    };
    if pdrop.local != payload_temp || !pdrop.projections.is_empty() {
        return None;
    }
    let drop_none_block = body.blocks.iter().find(|b| b.id == *drop_none_bid)?;
    let Rvalue::Aggregate(AggregateKind::Adt { name: dnname, variant: dnvar, .. }, dnops) =
        sole_zero_write(drop_none_block)?
    else {
        return None;
    };
    if *dnname != enum_name || *dnvar != none_tag || !dnops.is_empty() {
        return None;
    }
    let Terminator::Goto(drop_join) = &drop_none_block.terminator else {
        return None;
    };

    // JOIN: the SAME block for all three arms, terminating in a bare `Return`.
    if *none_join != *keep_join || *keep_join != *drop_join {
        return None;
    }
    let join_block = body.blocks.iter().find(|b| b.id == *keep_join)?;
    if !matches!(join_block.terminator, Terminator::Return) {
        return None;
    }
    if join_block.stmts.iter().any(|s| matches!(s, Statement::Assign { .. })) {
        return None;
    }

    // `_0` written EXACTLY three times (KEEP, DROP-NONE, NONE), never a Call dest.
    if crate::prove::local_write_count(body, 0) != 3 {
        return None;
    }

    // EVERY `Drop` anywhere targets the bare payload or the bare closure param — the
    // ONLY admitted drops (covers the reachable DROP/NONE drops AND the unreachable
    // unwind-cleanup Drop).
    for b in &body.blocks {
        if let Terminator::Drop { place, .. } = &b.terminator {
            if !place.projections.is_empty()
                || (place.local != payload_temp && place.local != closure_local)
            {
                return None;
            }
        }
    }

    // REACHABILITY: the unwind `Resume` sink is UNREACHABLE from entry, and the
    // entry-reachable set is EXACTLY the 9 recognized roles (any stray reachable
    // block — an unmodeled cleanup path, a rogue block — declines fail-closed).
    let reachable = cfg_reachable_from(body, BlockId(0))?;
    if reachable.iter().any(|id| {
        body.blocks
            .iter()
            .find(|b| b.id == *id)
            .is_some_and(|b| matches!(b.terminator, Terminator::Resume))
    }) {
        return None;
    }
    let recognized: std::collections::HashSet<BlockId> = [
        switch_bid,
        *otherwise,
        none_bid,
        setup_bid,
        bool_switch_bid,
        keep_bid,
        drop_bid,
        *drop_none_bid,
        *keep_join,
    ]
    .into_iter()
    .collect();
    if recognized.len() != 9 || reachable != recognized {
        return None;
    }
    // EXACTLY 9 projectionless `Assign`s across the recognized blocks (disc, _x, _e,
    // _r, _t, recon, _0(keep), _0(drop-none), _0(none)).
    let recognized_assigns: usize = body
        .blocks
        .iter()
        .filter(|b| recognized.contains(&b.id))
        .flat_map(|b| &b.stmts)
        .filter(|s| matches!(s, Statement::Assign { place, .. } if place.projections.is_empty()))
        .count();
    if recognized_assigns != 9 {
        return None;
    }

    // EXACT-ONLY closure-callee resolution + spec-free CalleeFact.
    let (resolved, fact, callee_id) = resolve_certified_callee_exact(callees, &closure_name)?;
    if resolved == func.def_path {
        return None;
    }
    if fact.arg_count != 2 {
        return None; // env + the untupled `&x`.
    }
    match &fact.requires {
        Some(v) if v.is_empty() => {}
        _ => return None,
    }

    let env_operand = SemOperand::Var(param_index(closure_local)?);
    Some(SemAdtFilterCompose {
        self_ty,
        some_variant: some_tag,
        none_variant: none_tag,
        callee: resolved.to_string(),
        callee_id,
        env_operand,
    })
}

/// Recognize the DIVERGENCE-GUARDED ADT PAYLOAD-EXTRACTION shape (`unwrap`/`expect`;
/// section comment above). ALL of the following must hold — anything else fails
/// closed (`None`), leaving the return/VC ungrounded rather than mis-certified.
/// Mirrors the six paired-lane gates, with the DEFAULT arm replaced by a verifiably
/// DIVERGING panic arm:
///
///   (1) `_0` is written by EXACTLY ONE `Statement::Assign` (the sole happy arm),
///       NEVER via a `Terminator::Call` dest (excludes the `unwrap_or_default`
///       `__trust_total_clone` havoc sentinel outright).
///   (2) EXACTLY ONE `SwitchInt` routes to the happy arm block; its OTHER explicit
///       target is the panic arm (two matching switches ⇒ ambiguous ⇒ decline).
///   (3) that switch is EXHAUSTIVE with `otherwise -> Unreachable`
///       (`exhaustive_two_arm_discriminant_switch`), its discr is a projectionless
///       temp with EXACTLY ONE static `Rvalue::Discriminant(self)` assignment, and
///       `sem_discriminant_base_of_mir` resolves the base to a BARE (by-value)
///       `self` PARAMETER (fronting `param_reassigned_by_stmt`).
///   (4) `disc_index_safe` on the `self` `Ty::Adt` (EXCLUDES niche layouts, where
///       the off-MIR "which arm is which" reading would be unsound).
///   (5) the PAYLOAD arm's sole `_0` write is `_0 := Use(self.Downcast(v).Field(f))`
///       off the SAME `self` local with `v == that block's switch tag` (the
///       TAG↔DOWNCAST provenance link); the OTHER arm must verifiably DIVERGE —
///       every block reachable from it (fail-closed CFG-closure walk
///       [`cfg_reachable_from`]) writes NO `_0` and is NOT a `Return`.
///   (6) MONOMORPHIZED + SCALAR: `reflect_enum(self_ty)` succeeds and is
///       `!is_parameterized()`; the enum has EXACTLY 2 variants; the extracted field
///       and the return are scalar `Ty::Int`; and the body has a `Return` block.
#[must_use]
pub fn sem_adt_payload_extract_diverging_of_discriminant_switch(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtPayloadExtractDiverging> {
    use trust_types::{
        BasicBlock, BlockId, Operand, Projection, Rvalue, Statement, Terminator, Ty,
    };
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // Every block-table lookup below must be unambiguous.  The complete set is
    // retained for the executable-entry reachability check after both arms are
    // classified.
    let block_ids: std::collections::HashSet<BlockId> =
        body.blocks.iter().map(|block| block.id).collect();
    if block_ids.len() != body.blocks.len() {
        return None;
    }

    // No UNMODELED statement anywhere (fail-closed).
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // (1) `_0` written EXACTLY once (the sole happy arm), NEVER via a Call dest.
    if crate::prove::local_write_count(body, 0) != 1 {
        return None;
    }
    if body
        .blocks
        .iter()
        .any(|b| matches!(&b.terminator, Terminator::Call { dest, .. } if dest.local == 0))
    {
        return None;
    }

    // A block's SOLE projectionless `_0` write rvalue (None if it writes `_0` zero
    // or more-than-once times).
    fn sole_zero_write(block: &BasicBlock) -> Option<&Rvalue> {
        let mut found: Option<&Rvalue> = None;
        for s in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                if place.local == 0 && place.projections.is_empty() {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(rvalue);
                }
            }
        }
        found
    }

    // The SOLE arm block is the one block writing `_0`.
    let arm_blocks: Vec<BlockId> = body
        .blocks
        .iter()
        .filter(|b| {
            b.stmts.iter().any(|s| matches!(s, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty()))
        })
        .map(|b| b.id)
        .collect();
    let [happy_bid] = arm_blocks.as_slice() else {
        return None;
    };
    let happy_bid = *happy_bid;

    // (2) THE unique 2-target switch ONE of whose explicit targets is the happy arm
    //     block; its OTHER target is the panic arm (two matches ⇒ ambiguous ⇒ decline).
    let mut chosen: Option<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = None;
    for b in &body.blocks {
        if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b.terminator {
            if targets.len() != 2 {
                continue;
            }
            if targets.iter().any(|(_, t)| *t == happy_bid) {
                if chosen.is_some() {
                    return None; // ambiguous — two switches route to the happy arm.
                }
                chosen = Some((discr, targets, *otherwise, b.id));
            }
        }
    }
    let (discr, targets, otherwise, switch_bid) = chosen?;

    // This is an executable entry-shape certificate, not a matching block-table
    // search.  An unreachable copy of a genuine switch grants no authority.
    if switch_bid != BlockId(0) {
        return None;
    }

    // (3) Exhaustive with `otherwise -> Unreachable`.
    if !exhaustive_two_arm_discriminant_switch(body, switch_bid, otherwise) {
        return None;
    }
    let unreachable = body.blocks.iter().find(|block| block.id == otherwise)?;
    if !unreachable.stmts.is_empty() || !matches!(unreachable.terminator, Terminator::Unreachable) {
        return None;
    }
    // The discriminant temp: projectionless Copy/Move, EXACTLY ONE static assign
    // whose rvalue is `Rvalue::Discriminant(place)`.
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
    if !dp.projections.is_empty() {
        return None;
    }
    if body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| matches!(s, Statement::Assign { place, .. } if place.local == dp.local && place.projections.is_empty()))
        .count()
        != 1
    {
        return None;
    }
    let disc_rvalue = body.blocks.iter().flat_map(|b| &b.stmts).find_map(|s| match s {
        Statement::Assign { place, rvalue, .. }
            if place.local == dp.local && place.projections.is_empty() =>
        {
            Some(rvalue)
        }
        _ => None,
    })?;
    let Rvalue::Discriminant(disc_place) = disc_rvalue else { return None };
    let switch_block = body.blocks.iter().find(|block| block.id == switch_bid)?;
    let mut entry_disc_definitions = 0usize;
    for statement in &switch_block.stmts {
        if payload_extract_cfg_marker(statement) {
            continue;
        }
        match statement {
            Statement::Assign { place, rvalue: Rvalue::Discriminant(_), .. }
                if place.local == dp.local && place.projections.is_empty() =>
            {
                entry_disc_definitions += 1;
            }
            _ => return None,
        }
    }
    if entry_disc_definitions != 1 {
        return None;
    }
    // Base resolves to a genuine parameter (this FRONTS `param_reassigned_by_stmt`).
    let _base =
        sem_discriminant_base_of_mir(body, disc_place, &param_index, Some((switch_bid, None)))?;
    if !disc_place.projections.is_empty() {
        return None;
    }
    let self_local = disc_place.local;
    if param_index(self_local).is_none() {
        return None;
    }

    // (4) `self_ty` is that param's `Ty::Adt`; `disc_index_safe` excludes niche.
    let self_ty = body.locals.get(self_local)?.ty.clone();
    let Ty::Adt { variants, .. } = &self_ty else { return None };
    if variants.is_empty() {
        return None; // not an enum.
    }
    if !self_ty.disc_index_safe() {
        return None; // niche layout — the off-MIR arm reading would be unsound.
    }

    // (5) Classify the two switch targets: EXACTLY one PAYLOAD arm (the happy arm,
    //     with the TAG↔DOWNCAST↔self provenance pinned equal) and one DIVERGING arm.
    let mut payload: Option<(usize, usize)> = None; // (extract_variant, field_idx)
    let mut panic_bid: Option<BlockId> = None;
    for (tag, blk) in targets {
        if *blk == happy_bid {
            // PAYLOAD arm: `self.Downcast(v).Field(f)` with `v == tag`.
            let block = body.blocks.iter().find(|b| b.id == *blk)?;
            if block.stmts.iter().any(|statement| {
                !payload_extract_cfg_marker(statement)
                    && !matches!(
                        statement,
                        Statement::Assign { place, .. }
                            if place.local == 0 && place.projections.is_empty()
                    )
            }) {
                return None;
            }
            let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = sole_zero_write(block)? else {
                return None; // e.g. `_0 := Discriminant(_1)` (raw tag) declines here.
            };
            if p.local != self_local {
                return None; // the payload must be read off `self`, not another local.
            }
            let [Projection::Downcast(v), Projection::Field(f)] = p.projections.as_slice() else {
                return None;
            };
            if *v != usize::try_from(*tag).ok()? {
                return None; // TAG↔DOWNCAST provenance broken.
            }
            if payload.is_some() {
                return None; // two payload arms.
            }
            payload = Some((*v, *f));
        } else {
            // The OTHER target is the panic arm.
            if panic_bid.is_some() {
                return None; // two non-happy arms (a 2-target switch has exactly one).
            }
            panic_bid = Some(*blk);
        }
    }
    let (extract_variant, extract_field_idx) = payload?;
    let panic_bid = panic_bid?;

    // (5b) The panic arm must verifiably DIVERGE: every block reachable from it
    //      (fail-closed CFG-closure walk — `None` on ANY unmodeled terminator) writes
    //      NO `_0` and is NOT a `Return`. This is the divergence-guard discipline: the
    //      certificate covers ONLY the happy path; the panic path never produces a value.
    let reachable = cfg_reachable_from(body, panic_bid)?;
    for bid in &reachable {
        let block = body.blocks.iter().find(|b| b.id == *bid)?;
        if matches!(block.terminator, Terminator::Return) {
            return None; // the panic arm can REACH a Return ⇒ it does NOT diverge.
        }
        if block
            .stmts
            .iter()
            .any(|s| matches!(s, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty()))
        {
            return None; // the panic arm writes `_0` on some path ⇒ not a pure divergence.
        }
    }

    // Bind both classified arms to the complete executable body.  The happy arm
    // must reach the function's unique Return, and no disconnected block (in
    // particular a dead Return paired with an opaque happy tail) may supply it.
    let entry_reachable = cfg_reachable_from(body, BlockId(0))?;
    if entry_reachable != block_ids {
        return None;
    }
    let return_block = unique_return_block(body)?;
    if !cfg_reachable_from(body, happy_bid)?.contains(&return_block.id) {
        return None;
    }

    // (6) MONOMORPHIZED + SCALAR gates.
    if variants.len() != 2 {
        return None;
    }
    let is_scalar_int = |t: &Ty| matches!(t, Ty::Int { .. });
    let ext_variant_def = variants.get(extract_variant)?;
    let (_, field_ty) = ext_variant_def.fields.get(extract_field_idx)?;
    if !is_scalar_int(field_ty) {
        return None; // non-scalar payload (e.g. `Option<String>`) declines.
    }
    if !is_scalar_int(&body.return_ty) {
        return None;
    }
    if &body.return_ty != field_ty || &body.locals.first()?.ty != field_ty {
        return None; // the executable return carrier must be exactly the payload carrier.
    }
    // Generic `Option<T>` declines (its variant-field types need the enum's type
    // params in scope — deferred, fail-closed).
    let carrier = crate::reflect::reflect_enum(&self_ty)?;
    if carrier.is_parameterized() {
        return None;
    }
    Some(SemAdtPayloadExtractDiverging { self_ty, extract_variant, extract_field_idx })
}

/// Recognize a SHORT-CIRCUIT chain of `SwitchInt`s as a conjunctive guard and return
/// `(And-tree cond, else_arm_id, then_arm_id)`. The MIR analogue of
/// `clean_ground::conjunctive_chain_cond`, producing the SAME left-nested `And`
/// structure (so `SemCondTree::And(…).to_formula()` equals the `Formula::And` the live
/// `clean_ground::conjunctive_chain_cond`, producing the SAME left-nested `And`
/// structure (so `SemCondTree::And(…).to_formula()` equals the `Formula::And` the live
/// `guarded_return_formula` reflects, and the branch refinement's reflexivity holds).
/// Each switch's value-0 path must reach a SINGLE common else arm; the chain's
/// `otherwise` edges link test→test, ending at the then arm. Fail closed (`None`) for
/// anything outside that single linear short-circuit.
pub(super) fn sem_conjunctive_chain(
    body: &trust_types::VerifiableBody,
    switches: &[(
        &trust_types::Operand,
        &Vec<(u128, trust_types::BlockId)>,
        trust_types::BlockId,
        trust_types::BlockId,
    )],
    arm_ids: &[trust_types::BlockId],
    switch_leaf: &dyn Fn(&trust_types::Operand, u128) -> Option<SemCond>,
) -> Option<(SemCondTree, trust_types::BlockId, trust_types::BlockId)> {
    use trust_types::{BlockId, Terminator};
    let idx_of = |bid: BlockId| switches.iter().position(|(_, _, _, b)| *b == bid);
    let next_switch_block = |start: BlockId| -> Option<BlockId> {
        let mut cur = start;
        for _ in 0..=body.blocks.len() {
            if idx_of(cur).is_some() {
                return Some(cur);
            }
            let block = body.blocks.iter().find(|b| b.id == cur)?;
            cur = match &block.terminator {
                Terminator::Goto(t) => *t,
                Terminator::Assert { target, .. } => *target,
                _ => return None,
            };
        }
        None
    };
    // Chain HEAD = the switch no other switch's otherwise reaches.
    let mut is_successor = vec![false; switches.len()];
    for (_, _, otherwise, _) in switches {
        if let Some(nb) = next_switch_block(*otherwise) {
            if let Some(j) = idx_of(nb) {
                is_successor[j] = true;
            }
        }
    }
    let head = (0..switches.len()).find(|&i| !is_successor[i])?;
    // Walk the chain, accumulating the left-nested conjunction.
    let mut order = Vec::new();
    let mut seen = vec![false; switches.len()];
    let mut cur = head;
    loop {
        if seen[cur] {
            return None; // cycle.
        }
        seen[cur] = true;
        order.push(cur);
        let (_, _, otherwise, _) = switches[cur];
        match next_switch_block(otherwise) {
            Some(nb) => match idx_of(nb) {
                Some(j) => cur = j,
                None => break,
            },
            None => break,
        }
    }
    if order.len() != switches.len() {
        return None;
    }
    // Common ELSE arm (every value-0 path) and THEN arm (final otherwise).
    let mut else_id: Option<BlockId> = None;
    for &i in &order {
        let (_, targets, _, _) = switches[i];
        let [(zero_val, else_target)] = targets.as_slice() else { return None };
        if *zero_val != 0 {
            return None;
        }
        let e = first_arm_on_path(body, *else_target, arm_ids)?;
        match else_id {
            None => else_id = Some(e),
            Some(prev) if prev == e => {}
            Some(_) => return None,
        }
    }
    let else_id = else_id?;
    let (_, _, last_otherwise, _) = switches[*order.last()?];
    if next_switch_block(last_otherwise).and_then(idx_of).is_some() {
        return None; // last otherwise still reaches a test, not the then arm.
    }
    let then_id = first_arm_on_path(body, last_otherwise, arm_ids)?;
    if then_id == else_id {
        return None;
    }
    // Build the left-nested And tree over the chain's comparison leaves.
    let mut cond: Option<SemCondTree> = None;
    for &i in &order {
        let (discr, _, _, _) = switches[i];
        // Every switch in this chain was just checked above to have `zero_val == 0`
        // (a single explicit target) — the conjunctive-chain shape is UNCHANGED (not
        // extended to the enum-discriminant shape), so `tag` is always `0` here.
        let leaf = SemCondTree::Leaf(switch_leaf(discr, 0)?);
        cond = Some(match cond {
            None => leaf,
            Some(acc) => SemCondTree::And(Box::new(acc), Box::new(leaf)),
        });
    }
    Some((cond?, else_id, then_id))
}

/// Recognize a 2-arm boolean DECISION DAG over comparison-temp and raw-value
/// equality switches (module doc above) and return the same
/// `(cond, else_arm_id, then_arm_id)` triple [`sem_conjunctive_chain`] produces.
/// Tried ONLY after the conjunctive chain declines (see the caller), so every
/// existing conjunctive witness is byte-identical. Fail-closed (`None`) outside
/// the recognized fragment.
pub(super) fn sem_decision_dag_chain(
    body: &trust_types::VerifiableBody,
    switches: &[(
        &trust_types::Operand,
        &Vec<(u128, trust_types::BlockId)>,
        trust_types::BlockId,
        trust_types::BlockId,
    )],
    arm_ids: &[trust_types::BlockId],
    switch_leaf: &dyn Fn(&trust_types::Operand, u128) -> Option<SemCond>,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<(SemCondTree, trust_types::BlockId, trust_types::BlockId)> {
    use trust_types::BlockId;
    if switches.len() < 2 || switches.len() > DISJ_DAG_MAX_SWITCHES {
        return None;
    }
    let [else_candidate, then_candidate] = arm_ids else { return None };

    // Resolve each switch to (cond leaf, success edge, failure edge). Two leaf kinds:
    //   * BOOL-TEMP: one explicit target with VALUE 0 (the false edge), `otherwise`
    //     the success edge, discriminant a comparison temp — the EXISTING
    //     `switch_leaf` resolution, byte-identical.
    //   * RAW-VALUE EQ: one explicit target with ANY value `v`, the discriminant a
    //     modeled scalar operand ITSELF (param / deref-self / a length- or
    //     CAST-temp, via `sem_guard_operand_of_mir` — Trust: CAST-TEMP GUARD READ,
    //     2026-07-08, widened from the bare `sem_operand_of_mir` fragment so a
    //     `SwitchInt` reading a cast temp DIRECTLY, e.g. `_2 = self as u8;
    //     switchInt(_2) { 127 => … }` — the `<char as Check>::is_control`-class
    //     shape — resolves here too) — cond `discr == v`, success = the `v`
    //     target, failure = `otherwise`. Tried only when the bool-temp resolution
    //     declines, so a Bool temp switch never mis-denotes through the raw-value
    //     path.
    let resolve_switch = |i: usize| -> Option<(SemCond, BlockId, BlockId)> {
        let (discr, targets, otherwise, switch_id) = switches[i];
        let [(value, explicit_target)] = targets.as_slice() else { return None };
        if *value == 0 {
            if let Some(leaf) = switch_leaf(discr, 0) {
                // SCALAR-COMPARISON leaves only: an ENUM-DISCRIMINANT leaf
                // (`switch_leaf`'s `Rvalue::Discriminant` arm) has TAG semantics
                // (value 0 = variant 0, not falsehood) — the Bool-temp
                // "value-0 = failure edge" convention below would misread it.
                // Out of this fragment; decline.
                if matches!(leaf.a, SemOperand::Discriminant(_)) {
                    return None;
                }
                return Some((leaf, otherwise, *explicit_target));
            }
        }
        // RAW-VALUE equality: the discriminant must be a modeled scalar READ (a
        // parameter, deref-self, a length-temp, or — Trust: CAST-TEMP GUARD READ —
        // a cast-temp, via `sem_guard_operand_of_mir`'s fragment, with all its
        // reassignment/deref-write/uniqueness gates).
        let discr_op = sem_guard_operand_of_mir(body, discr, param_index, Some((switch_id, None)))?;
        let leaf = SemCond {
            op: SemCmpOp::Eq,
            a: discr_op,
            b: SemOperand::Const(i128::try_from(*value).ok()?),
        };
        Some((leaf, *explicit_target, otherwise))
    };

    // Unique head: the switch no OTHER switch's outgoing edge reaches (via the
    // Goto/Assert chase). Mirrors `sem_conjunctive_chain`'s head-finding, widened
    // to BOTH edges.
    let idx_of = |bid: BlockId| switches.iter().position(|(_, _, _, b)| *b == bid);
    let next_switch_block = |start: BlockId| -> Option<BlockId> {
        use trust_types::Terminator;
        let mut cur = start;
        for _ in 0..=body.blocks.len() {
            if idx_of(cur).is_some() {
                return Some(cur);
            }
            let block = body.blocks.iter().find(|b| b.id == cur)?;
            cur = match &block.terminator {
                Terminator::Goto(t) => *t,
                Terminator::Assert { target, .. } => *target,
                _ => return None,
            };
        }
        None
    };
    let mut is_successor = vec![false; switches.len()];
    for i in 0..switches.len() {
        let (_, targets, otherwise, _) = switches[i];
        for edge in targets.iter().map(|(_, t)| *t).chain([otherwise]) {
            if let Some(nb) = next_switch_block(edge) {
                if let Some(j) = idx_of(nb) {
                    if j != i {
                        is_successor[j] = true;
                    }
                }
            }
        }
    }
    let heads: Vec<usize> = (0..switches.len()).filter(|&i| !is_successor[i]).collect();
    let [head] = heads.as_slice() else { return None };

    // Denote the DAG from `head` for a candidate (then, else) assignment.
    // `visited` is the GLOBAL per-walk switch set (each switch denoted at most
    // once — the ABSORB rule handles the one legitimate shared-continuation
    // pattern by structural equality, so a genuine second visit is either a cycle
    // or a shape outside the fragment: decline). `path` guards against cycles.
    fn denote(
        i: usize,
        then_id: trust_types::BlockId,
        else_id: trust_types::BlockId,
        resolve_switch: &dyn Fn(
            usize,
        )
            -> Option<(SemCond, trust_types::BlockId, trust_types::BlockId)>,
        next_switch_block: &dyn Fn(trust_types::BlockId) -> Option<trust_types::BlockId>,
        idx_of: &dyn Fn(trust_types::BlockId) -> Option<usize>,
        first_arm: &dyn Fn(trust_types::BlockId) -> Option<trust_types::BlockId>,
        path: &mut Vec<usize>,
        visited: &mut Vec<usize>,
        budget: &mut usize,
    ) -> Option<DagDenote> {
        if path.contains(&i) || *budget == 0 {
            return None; // cycle / budget exhausted — decline, never diverge.
        }
        *budget -= 1;
        path.push(i);
        if !visited.contains(&i) {
            visited.push(i);
        }
        let (leaf, s_edge, f_edge) = resolve_switch(i)?;
        let eval_edge = |e: trust_types::BlockId,
                         path: &mut Vec<usize>,
                         visited: &mut Vec<usize>,
                         budget: &mut usize|
         -> Option<DagDenote> {
            // A switch first (an arm-block id can never also be a switch block —
            // arms are Goto-terminated), then an arm.
            if let Some(nb) = next_switch_block(e) {
                if let Some(j) = idx_of(nb) {
                    return denote(
                        j,
                        then_id,
                        else_id,
                        resolve_switch,
                        next_switch_block,
                        idx_of,
                        first_arm,
                        path,
                        visited,
                        budget,
                    );
                }
            }
            match first_arm(e) {
                Some(a) if a == then_id => Some(DagDenote::True),
                Some(a) if a == else_id => Some(DagDenote::False),
                _ => None,
            }
        };
        let ds = eval_edge(s_edge, path, visited, budget)?;
        let df = eval_edge(f_edge, path, visited, budget)?;
        path.pop();
        let c = SemCondTree::Leaf(leaf);
        Some(match (ds, df) {
            (DagDenote::True, DagDenote::False) => DagDenote::Cond(c),
            (DagDenote::True, DagDenote::Cond(d)) => {
                DagDenote::Cond(SemCondTree::Or(Box::new(c), Box::new(d)))
            }
            (DagDenote::Cond(d), DagDenote::False) => {
                DagDenote::Cond(SemCondTree::And(Box::new(c), Box::new(d)))
            }
            // ABSORB: `if c { x || e } else { e }` ≡ `(c && x) || e` — the conjunct-
            // inside-a-clause pattern, where BOTH the conjunct's failure and its
            // successor's failure fall into the SAME next clause `e` (structural
            // equality).
            (DagDenote::Cond(SemCondTree::Or(x, e)), DagDenote::Cond(e2)) if *e == e2 => {
                DagDenote::Cond(SemCondTree::Or(Box::new(SemCondTree::And(Box::new(c), x)), e))
            }
            _ => return None, // needs Not / degenerate — outside the fragment.
        })
    }

    let first_arm = |start: BlockId| first_arm_on_path(body, start, arm_ids);
    for (then_id, else_id) in
        [(*then_candidate, *else_candidate), (*else_candidate, *then_candidate)]
    {
        let mut path = Vec::new();
        let mut visited = Vec::new();
        let mut budget = 4 * DISJ_DAG_MAX_SWITCHES;
        if let Some(DagDenote::Cond(cond)) = denote(
            *head,
            then_id,
            else_id,
            &resolve_switch,
            &next_switch_block,
            &idx_of,
            &first_arm,
            &mut path,
            &mut visited,
            &mut budget,
        ) {
            // EVERY switch in the body must have been consumed by the walk — a
            // stray switch means unmodeled control flow: decline.
            if visited.len() == switches.len() {
                // The disjunctive fragment requires at least one Or (a pure
                // conjunction/leaf belongs to the EXISTING recognizers — reaching
                // here for one would mean they declined it for a reason).
                fn has_or(t: &SemCondTree) -> bool {
                    match t {
                        SemCondTree::Leaf(_) => false,
                        SemCondTree::Or(..) => true,
                        SemCondTree::And(a, b) => has_or(a) || has_or(b),
                        // Trust: ITER-NEXT VALUE-PATH — an opaque iter dispatch head is
                        // not a disjunction; never reaches this recognizer (fail-closed).
                        SemCondTree::IterHasNext(_) => false,
                    }
                }
                if has_or(&cond) {
                    return Some((cond, else_id, then_id));
                }
            }
        }
    }
    None
}

/// From a `SwitchInt` exit block `start`, follow the linear chain of
/// `Goto`/`Assert`(success) edges and return the FIRST block in `arm_ids` reached.
/// Bounded (≤ block count) to avoid cycles. `None` if no arm block is reached on the
/// path (e.g. the path diverges or hits an unmodeled terminator first).
pub(super) fn first_arm_on_path(
    body: &trust_types::VerifiableBody,
    start: trust_types::BlockId,
    arm_ids: &[trust_types::BlockId],
) -> Option<trust_types::BlockId> {
    use trust_types::Terminator;
    let mut cur = start;
    for _ in 0..=body.blocks.len() {
        if arm_ids.contains(&cur) {
            return Some(cur);
        }
        let block = body.blocks.iter().find(|b| b.id == cur)?;
        cur = match &block.terminator {
            Terminator::Goto(t) => *t,
            // An Assert on the success path continues to its target (the guard's
            // bounds/overflow check on the THEN path — e.g. `guarded_div`'s div-by-zero
            // assert, `guarded_sub`'s overflow assert).
            Terminator::Assert { target, .. } => *target,
            _ => return None, // unmodeled terminator on the path.
        };
    }
    None
}

/// From a `SwitchInt` exit block `start`, follow the linear chain of `Goto`/
/// `Assert`(success) edges and report whether `target` is reached (zero hops
/// counts). Bounded (≤ block count) to avoid a cycle running unbounded.
pub(super) fn goto_chain_reaches(
    body: &trust_types::VerifiableBody,
    start: trust_types::BlockId,
    target: trust_types::BlockId,
) -> bool {
    use trust_types::Terminator;
    let mut cur = start;
    for _ in 0..=body.blocks.len() {
        if cur == target {
            return true;
        }
        let Some(block) = body.blocks.iter().find(|b| b.id == cur) else { return false };
        cur = match &block.terminator {
            Terminator::Goto(t) => *t,
            Terminator::Assert { target, .. } => *target,
            _ => return false,
        };
    }
    false
}

/// Like [`crate::prove::local_soundly_resolvable`]'s call-dest / mutable-alias
/// guards, WITHOUT its whole-body single-assignment clause: [`chain_arm_value_for`]
/// enforces single-assignment WITHIN ITS OWN WALK (a SIBLING arm's walk may
/// legitimately write the SAME local — the shared-sink shape this recognizer
/// targets). The call-dest/mutable-alias hazards are not walk-scoped (a call or a
/// `&mut` alias anywhere could invisibly clobber the value), so those two clauses
/// stay whole-body, fail-closed.
pub(super) fn chain_local_not_aliased(body: &trust_types::VerifiableBody, local: usize) -> bool {
    use trust_types::{Rvalue, Statement, Terminator};
    let call_dest_written = body.blocks.iter().any(|b| {
        matches!(&b.terminator,
            Terminator::Call { dest, .. } if dest.local == local)
    });
    if call_dest_written {
        return false;
    }
    let mutably_aliased = body.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
        matches!(s,
            Statement::Assign { rvalue: Rvalue::Ref { mutable: true, place }, .. }
                | Statement::Assign { rvalue: Rvalue::AddressOf(true, place), .. }
            if place.local == local)
    });
    !mutably_aliased
}

/// Resolve ONE arm of a guard chain: walk `Goto`/`Assert` edges from `start` until
/// reaching a block with a bare `_0 := …` assignment (the sink), then recognize
/// that assignment as an `Aggregate` variant construction — SAME shape
/// [`arm_adt_ctor_value_for`] recognizes (nullary, or a single scalar/Cast/Use/
/// nested-nullary-Aggregate payload) — except a scratch payload temp resolves via
/// the WALK's OWN statements (module doc above), not a whole-body search. Fail-
/// closed on a cycle, an unmodeled terminator before the sink, an out-of-fragment
/// sink rvalue, or a payload temp that's multiply-assigned WITHIN the walk, a call
/// dest, or mutably-aliased anywhere.
pub(super) fn chain_arm_value_for(
    body: &trust_types::VerifiableBody,
    start: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<ChainArm> {
    use trust_types::{AggregateKind, Operand, Rvalue, Statement, Terminator};
    let writes_0 = |b: &trust_types::BasicBlock| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == 0 && place.projections.is_empty())
        })
    };
    let mut visited: Vec<&trust_types::BasicBlock> = Vec::new();
    let mut cur = start;
    let sink = loop {
        if visited.len() > body.blocks.len() {
            return None; // cycle guard.
        }
        let block = body.blocks.iter().find(|b| b.id == cur)?;
        if visited.iter().any(|b| b.id == block.id) {
            return None; // revisits an already-walked block — not a straight-line walk.
        }
        visited.push(block);
        if writes_0(block) {
            break block.id;
        }
        cur = match &block.terminator {
            Terminator::Goto(t) => *t,
            Terminator::Assert { target, .. } => *target,
            _ => return None, // unmodeled terminator before reaching a sink.
        };
    };
    let sink_block = *visited.last()?;
    let (sink_statement, rv) =
        sink_block.stmts.iter().enumerate().rev().find_map(|(statement_index, statement)| {
            crate::assignment_types::assigned_local_rvalue(body, statement, 0)
                .map(|rvalue| (statement_index, rvalue))
        })?;
    let Rvalue::Aggregate(
        AggregateKind::Adt { name, variant: variant_index, active_field, .. },
        operands,
    ) = rv
    else {
        return None;
    };
    if active_field.is_some() {
        return None;
    }
    if operands.len() > 1 {
        return None;
    }
    let return_local_ty = &body.locals.first()?.ty;
    if return_local_ty != &body.return_ty {
        return None;
    }
    let variant = aggregate_variant_discriminant(return_local_ty, name, *variant_index)?;
    let Some(payload_op) = operands.first() else {
        return Some(ChainArm { arm: SemAdtArm { variant, payload: None }, sink });
    };
    let (Operand::Copy(p) | Operand::Move(p)) = payload_op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    if let Some(direct) = sem_operand_of_mir(body, payload_op, param_index) {
        return Some(ChainArm {
            arm: SemAdtArm { variant, payload: Some(SemAdtPayload::Scalar(direct)) },
            sink,
        });
    }
    if param_index(p.local).is_some() || !chain_local_not_aliased(body, p.local) {
        return None;
    }
    // WALK-LOCAL complete-definition search (this arm's own visited blocks only —
    // see the module doc for why a sibling arm may write the same local).  Every
    // rooted effect on the modeled path participates: projected writes,
    // discriminant/deinit/retag effects, and a second bare assignment all decline.
    // The unique definition must also execute before the Aggregate that consumes it.
    let mut found: Option<(trust_types::BlockId, usize, &Rvalue)> = None;
    for block in &visited {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            match statement {
                Statement::Assign { place, .. } if place.local == p.local => {
                    if !place.projections.is_empty() || found.is_some() {
                        return None;
                    }
                    let rvalue =
                        crate::assignment_types::assigned_local_rvalue(body, statement, p.local)?;
                    found = Some((block.id, statement_index, rvalue));
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                    if place.local == p.local =>
                {
                    return None;
                }
                _ => {}
            }
        }
    }
    let (definition_block, definition_statement, definition) = found?;
    if definition_block == sink && definition_statement >= sink_statement {
        return None;
    }
    let definition_site = Some((definition_block, Some(definition_statement)));
    let payload = match definition {
        Rvalue::Cast(op, dest_ty) => {
            let trust_types::Ty::Int { width, signed } = dest_ty else { return None };
            if !matches!(*width, 8 | 16 | 32 | 64 | 128)
                || !matches!(op,
                    Operand::Copy(source) | Operand::Move(source)
                        if source.projections.is_empty()
                            && matches!(body.locals.get(source.local).map(|local| &local.ty),
                                Some(trust_types::Ty::Int { .. })))
            {
                return None;
            }
            SemAdtPayload::IntCast {
                source: resolve_cast_source_operand(body, op, param_index, definition_site)?,
                width: *width,
                signed: *signed,
            }
        }
        Rvalue::Use(op) => SemAdtPayload::Scalar(resolve_cast_source_operand(
            body,
            op,
            param_index,
            definition_site,
        )?),
        Rvalue::Aggregate(
            AggregateKind::Adt {
                name: nested_name,
                variant: nested_variant,
                active_field: nested_active, .. },
            nested_ops,
        ) if nested_active.is_none() && nested_ops.is_empty() => SemAdtPayload::NullaryNested {
            enum_name: nested_name.clone(),
            variant: aggregate_variant_discriminant(
                &body.locals.get(p.local)?.ty,
                nested_name,
                *nested_variant,
            )?,
        },
        _ => return None,
    };
    Some(ChainArm { arm: SemAdtArm { variant, payload: Some(payload) }, sink })
}

/// Recognize the 3-OUTCOME GUARD-CHAIN ADT-RETURN shape (module doc above). Fail-
/// closed (`None`) on anything outside the recognized fragment — not EXACTLY two
/// single-target `SwitchInt`s, no linear chain link between them, an unresolvable
/// guard or arm, or an extra `_0` write beyond the arms' own (possibly shared)
/// sinks.
#[must_use]
pub fn sem_adt_return_shape_of_chain(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtReturn3> {
    use trust_types::{Operand, Rvalue, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // (1) exactly TWO single-target `SwitchInt`s (`[(0, else_target)]` + `otherwise`)
    // — a chained guard is always a bare compare in the target family; no more, no
    // fewer (a genuine 2-arm or 4+-outcome shape is a DIFFERENT recognizer's job).
    let all_switches: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::SwitchInt { .. }))
        .collect();
    let [switch0, switch1] = all_switches.as_slice() else { return None };
    let Terminator::SwitchInt {
        discr: s0_discr, targets: s0_targets, otherwise: s0_otherwise, ..
    } = &switch0.terminator
    else {
        return None;
    };
    let [(0, s0_else)] = s0_targets.as_slice() else { return None };
    let Terminator::SwitchInt {
        discr: s1_discr, targets: s1_targets, otherwise: s1_otherwise, ..
    } = &switch1.terminator
    else {
        return None;
    };
    let [(0, s1_else)] = s1_targets.as_slice() else { return None };
    let (s0_else, s0_otherwise, s0_id) = (*s0_else, *s0_otherwise, switch0.id);
    let (s1_else, s1_otherwise, s1_id) = (*s1_else, *s1_otherwise, switch1.id);

    // (2) the CHAIN LINK: exactly one ordering's head switch value-0 edge reaches
    // the tail switch's OWN block via a Goto/Assert-only walk (no intervening
    // decision) — this is what distinguishes a genuine linear guard chain from two
    // unrelated switches that happen to coexist in the function.
    let (discr1, otherwise1, discr2, else2, otherwise2, head_id, tail_id) =
        if goto_chain_reaches(body, s0_else, s1_id) {
            (s0_discr, s0_otherwise, s1_discr, s1_else, s1_otherwise, s0_id, s1_id)
        } else if goto_chain_reaches(body, s1_else, s0_id) {
            (s1_discr, s1_otherwise, s0_discr, s0_else, s0_otherwise, s1_id, s0_id)
        } else {
            return None;
        };

    // switch_leaf — a bare comparison only (no discriminant-guard/conjunctive-
    // chain composition for this shape; out of scope, declines).
    let switch_leaf = |discr: &Operand| -> Option<SemCond> {
        let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
        if !dp.projections.is_empty() {
            return None;
        }
        let (definition_block, definition_statement, cmp_rvalue) =
            dominating_switch_discriminant_rvalue(body, dp.local)?;
        let Rvalue::BinaryOp(cmp_op, ca, cb) = cmp_rvalue else { return None };
        // Trust: FLOAT-GUARD fail-closed gate (gap-queue #2 follow-up #2 investigation,
        // 2026-07-08) — the downstream kernel denotation
        // (`trustir_adt::guard_bool`, mirroring `clean_ground::ground_bool`) hardcodes
        // `Int.lt`/`Int.le`/`Int.beq` — there is NO verified Float comparison
        // semantics anywhere in this pipeline (`reflect::reflect_float` only
        // structures the IEEE-754 BIT PATTERN for ADT-field STORAGE, it defines no
        // comparison operator). A float-typed comparison (`from_float!`/
        // `from_float_dst!`'s `src != src`/`src == INFINITY`/`src <= -1.0` guards)
        // would otherwise silently misdenote as an INT comparison over the SAME env
        // slot — never unsound today only because those shapes' >2-switch ladders
        // fail this recognizer's OWN `switches.len() != 2` gate first (an
        // INCIDENTAL, not designed, defense) — so this is an EXPLICIT, load-bearing
        // fail-closed gate: BOTH compared operands must be `Ty::Int`-typed (a bare
        // parameter place of Int type, or an Int/Uint constant); anything else
        // (Float, FloatBits, Bool, a non-parameter place) declines the WHOLE shape.
        let is_int_typed = |op: &Operand| -> bool {
            match op {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    matches!(
                        body.locals.get(p.local).map(|l| &l.ty),
                        Some(trust_types::Ty::Int { .. })
                    )
                }
                Operand::Constant(
                    trust_types::ConstValue::Int(_) | trust_types::ConstValue::Uint(_, _),
                ) => true,
                _ => false,
            }
        };
        if !is_int_typed(ca) || !is_int_typed(cb) {
            return None;
        }
        Some(SemCond {
            op: sem_cmpop_of_mir(cmp_op)?,
            a: sem_adt_guard_operand_of_mir(
                body,
                ca,
                &param_index,
                Some((definition_block, Some(definition_statement))),
            )?,
            b: sem_adt_guard_operand_of_mir(
                body,
                cb,
                &param_index,
                Some((definition_block, Some(definition_statement))),
            )?,
        })
    };
    let cond1 = SemCondTree::Leaf(switch_leaf(discr1)?);
    let cond2 = SemCondTree::Leaf(switch_leaf(discr2)?);

    // (3) the three arms — WALK-LOCAL resolution (module doc above).
    let arm_a = chain_arm_value_for(body, otherwise1, &param_index)?;
    let arm_b = chain_arm_value_for(body, otherwise2, &param_index)?;
    let arm_c = chain_arm_value_for(body, else2, &param_index)?;

    let ret = unique_return_block(body)?;
    let branch_starts = [otherwise1, otherwise2, else2];
    if !guarded_cfg_is_entry_rooted(body, ret.id, &branch_starts, &[head_id, tail_id])
        || [arm_a.sink, arm_b.sink, arm_c.sink]
            .iter()
            .any(|sink| !goto_chain_reaches(body, *sink, ret.id))
    {
        return None;
    }

    // (4) well-formedness: the total `_0`-write count anywhere in the function
    // must equal exactly the number of DISTINCT sinks the three walks landed on
    // — never more (an extra spurious write, reachable or not, must decline the
    // whole shape, generalizing `sem_adt_return_shape_of`'s fixed `== 2` gate to
    // this shape's variable — possibly-shared — sink count).
    let distinct_sinks: std::collections::HashSet<_> =
        [arm_a.sink, arm_b.sink, arm_c.sink].into_iter().collect();
    if !local_has_only_guarded_writes(body, 0, distinct_sinks.len(), 0) {
        return None;
    }

    let trust_types::Ty::Adt { name: enum_name, .. } = &body.return_ty else { return None };
    Some(SemAdtReturn3 {
        cond1,
        cond2,
        arm_a: arm_a.arm,
        arm_b: arm_b.arm,
        arm_c: arm_c.arm,
        enum_name: enum_name.clone(),
    })
}

// ---------------------------------------------------------------------------
// Trust: DISCRIMINANT-SWITCH ADT-RETURN, 3-ARM (M5 residue #1, 2026-07-08) —
// `Ordering::reverse`'s own shape: a SINGLE `SwitchInt(Discriminant(place))`
// with THREE EXPLICIT tag targets (`[255→Greater, 0→Equal, 1→Less]`), an
// exhaustive (TyCtxt-vetted) enum match — `otherwise` reaches `Unreachable` —
// each arm CONSTRUCTING a (nullary, this target's own shape) variant of the
// SAME outer enum. This is the FLAT sibling of [`sem_adt_return_shape_of_chain`]
// (which recovers the SAME "if c1 {A} else if c2 {B} else {C}" shape from TWO
// chained single-target `SwitchInt`s, the `from_signed!`-class bool-guard
// family): here the recognizer's OWN job is only to translate the switch's
// FIRST TWO explicit targets into the equivalent NESTED encoding
// `cond1 = (discr == tag_a)`, `cond2 = (discr == tag_b)` — sound precisely
// BECAUSE the switch is EXHAUSTIVE over exactly these three tags (any OTHER
// discriminant value is `Unreachable` by rustc's own vetting), so "neither
// cond1 nor cond2" is exactly "the third target was taken" within every
// REACHABLE state — produces a [`SemAdtReturn3`] DIRECTLY and reuses
// [`crate::trustir_adt::check_adt_return3_refinement`] UNCHANGED (the SAME
// kernel witness `sem_adt_return_shape_of_chain` feeds — zero new Clean
// declarations, zero new axioms, just a different Rust-side extraction of the
// SAME struct). Each arm resolves via [`chain_arm_value_for`] (the SAME
// WALK-based, possibly-shared-sink arm resolver the chain shape uses),
// requiring the three arms construct THREE DISTINCT variants (a genuine
// 3-way dispatch) and that `_0`'s total write count matches exactly the
// distinct-sink count (no extra spurious write anywhere in the function).
// Fail-closed (`None`) on: not EXACTLY one 3-explicit-target `SwitchInt`; a
// non-exhaustive or non-`Unreachable`-otherwise switch; a multiply-assigned
// or unresolvable discriminant temp; a non-`Discriminant` discriminant
// rvalue (a bare 3-way INT comparison switch is a DIFFERENT, unmodeled
// shape — this recognizer is enum-tag-only); an unresolvable arm; two arms
// sharing a variant; or an extra `_0` write.
// ---------------------------------------------------------------------------
/// See the module doc above.
#[must_use]
pub fn sem_adt_return_shape_of_discriminant_switch3(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtReturn3> {
    use trust_types::{Operand, Rvalue, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // Exactly ONE `SwitchInt` with EXACTLY THREE explicit targets.
    let switches: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::SwitchInt { .. }))
        .collect();
    let [switch] = switches.as_slice() else { return None };
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &switch.terminator else {
        return None;
    };
    if targets.len() != 3 {
        return None;
    }
    let bid = switch.id;

    // Exhaustive (TyCtxt-vetted) enum match: `otherwise` is `Unreachable` — the
    // SAME gate [`sem_adt_return_shape_of`]'s 2-target discriminant arm applies
    // (the helper is arity-agnostic despite its name — it inspects only the
    // switch block's OWN `exhaustive_enum_unreachable` flag and the otherwise
    // block's terminator, never the target count).
    if !exhaustive_two_arm_discriminant_switch(body, bid, *otherwise) {
        return None;
    }

    // The discriminant temp: block-order-first SOUNDNESS — exactly ONE static
    // assignment — whose rvalue must be `Rvalue::Discriminant(place)` (an
    // enum-tag read; a bare INT/bool comparison temp is a DIFFERENT, unmodeled
    // shape at 3 explicit targets — declines, never mis-denoted).
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
    if !dp.projections.is_empty() {
        return None;
    }
    let (definition_block, definition_statement, cmp_rvalue) =
        dominating_switch_discriminant_rvalue(body, dp.local)?;
    let Rvalue::Discriminant(place) = cmp_rvalue else { return None };
    let base = sem_discriminant_base_of_mir(
        body,
        place,
        &param_index,
        Some((definition_block, Some(definition_statement))),
    )?;

    let [(tag_a, block_a), (tag_b, block_b), (_tag_c, block_c)] = targets.as_slice() else {
        unreachable!("targets.len() == 3 checked above")
    };
    let cond1 = SemCondTree::Leaf(SemCond {
        op: SemCmpOp::Eq,
        a: SemOperand::Discriminant(Box::new(base.clone())),
        b: SemOperand::Const(i128::try_from(*tag_a).ok()?),
    });
    let cond2 = SemCondTree::Leaf(SemCond {
        op: SemCmpOp::Eq,
        a: SemOperand::Discriminant(Box::new(base)),
        b: SemOperand::Const(i128::try_from(*tag_b).ok()?),
    });

    // Each arm — the SAME WALK-based (possibly-shared-sink) resolver the
    // 2-switch chain shape uses.
    let arm_a = chain_arm_value_for(body, *block_a, &param_index)?;
    let arm_b = chain_arm_value_for(body, *block_b, &param_index)?;
    let arm_c = chain_arm_value_for(body, *block_c, &param_index)?;
    if arm_a.arm.variant == arm_b.arm.variant
        || arm_b.arm.variant == arm_c.arm.variant
        || arm_a.arm.variant == arm_c.arm.variant
    {
        return None; // not a genuine three-way dispatch.
    }

    let ret = unique_return_block(body)?;
    let branch_starts = [*block_a, *block_b, *block_c];
    if !guarded_cfg_is_entry_rooted(body, ret.id, &branch_starts, &[bid])
        || [arm_a.sink, arm_b.sink, arm_c.sink]
            .iter()
            .any(|sink| !goto_chain_reaches(body, *sink, ret.id))
    {
        return None;
    }

    // Well-formedness: `_0`'s total write count must equal exactly the number of
    // DISTINCT sinks the three walks landed on (no extra spurious write).
    let distinct_sinks: std::collections::HashSet<_> =
        [arm_a.sink, arm_b.sink, arm_c.sink].into_iter().collect();
    if !local_has_only_guarded_writes(body, 0, distinct_sinks.len(), 0) {
        return None;
    }

    let trust_types::Ty::Adt { name: enum_name, .. } = &body.return_ty else { return None };
    Some(SemAdtReturn3 {
        cond1,
        cond2,
        arm_a: arm_a.arm,
        arm_b: arm_b.arm,
        arm_c: arm_c.arm,
        enum_name: enum_name.clone(),
    })
}

// ---------------------------------------------------------------------------
// Trust: Ord::cmp THREE-WAY COMPARE (M5 residue #2, 2026-07-08) — the
// `Ord::cmp` primitive-int impls' OWN shape: a STRAIGHT-LINE, single-block
// body whose SOLE return-defining rvalue is `Rvalue::BinaryOp(BinOp::Cmp, a,
// b)` — rustc's THREE-WAY COMPARE intrinsic, `trust-vcgen`'s OWN
// documentation confirms is "formula-only (three-way comparison is safe)"
// (`crates/trust-vcgen/src/coverage.rs`; it raises NO overflow/safety VC —
// `chc.rs`'s `BinOp::Cmp => Ok(Formula::Ite(...))` arm). `Cmp(a,b)`'s runtime
// semantics ARE, by definition, `if a<b {Less} else if a==b {Equal} else
// {Greater}}` (the exact three-way compare this MIR opcode computes for any
// `Ord`-primitive pair) — asserting this is EXACTLY the same kind of
// foundational MIR-opcode-semantics modeling step `sem_binop_of_mir` already
// makes for every OTHER `BinOp` (`Add ↦ Int.add`, `Lt ↦ Int.lt`, …): not an
// assumption smuggled past the recognizer, but the documented meaning of the
// opcode itself.
//
// Modeled by producing a [`SemAdtReturn3`] DIRECTLY — `cond1 = (a < b)`,
// `cond2 = (a == b)`, and three NULLARY (`payload: None`) arms labeled by
// FIXED ARM POSITION (`0 = Less, 1 = Equal, 2 = Greater`, Rust's own
// declaration order for `cmp::Ordering`), with each position mapped through
// the return type's first-class variant metadata to its ACTUAL discriminant —
// and reuses
// [`crate::trustir_adt::check_adt_return3_refinement`] UNCHANGED: the SAME
// kernel witness [`sem_adt_return_shape_of_chain`]/
// [`sem_adt_return_shape_of_discriminant_switch3`] feed, since there is no
// REAL `Aggregate` here to inspect (there is no switch/construction at all — ONE
// instruction computes the whole three-way result), but `all_assignments_match`
// already requires the exact `Ordering` declaration.  Mapping its positions here
// keeps the model honest for explicit/negative discriminants too.
//
// Fail-closed (`None`) for: more than one block (a guard/switch present —
// out of THIS straight-line recognizer's scope, a different shape's job); a
// non-bare-`Return` terminator; a return-local write that is not
// `BinaryOp(Cmp, a, b)`; more than one write to `_0`; or an unresolvable
// operand (through [`resolve_cast_source_operand`]'s existing at-most-one-
// level temp inlining, covering the observed `_3 := Use(Copy((*self)))`
// deref-temp indirection).
// ---------------------------------------------------------------------------
/// See the module doc above.
#[must_use]
pub fn sem_cmp_binop_adt_return3_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtReturn3> {
    use trust_types::{BinOp, Operand, Rvalue, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // STRAIGHT-LINE ONLY: exactly one block, terminated by a bare `Return` — a
    // guard/switch anywhere is a DIFFERENT (unmodeled by this recognizer) shape.
    let [block] = body.blocks.as_slice() else { return None };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }

    // `_0`'s total write count must be EXACTLY one — no extra spurious write.
    if !local_has_only_guarded_writes(body, 0, 1, 0) {
        return None;
    }
    let (return_index, rv) = block.stmts.iter().enumerate().find_map(|(index, statement)| {
        crate::assignment_types::assigned_local_rvalue(body, statement, 0)
            .map(|rvalue| (index, rvalue))
    })?;
    let Rvalue::BinaryOp(BinOp::Cmp, a_op, b_op) = rv else { return None };
    let resolve_before_return = |op: &Operand| -> Option<SemOperand> {
        if let Some(direct) = sem_operand_of_mir(body, op, &param_index)
            .or_else(|| sem_field_read_operand(body, op, &param_index))
        {
            return Some(direct);
        }
        let (Operand::Copy(place) | Operand::Move(place)) = op else { return None };
        if !place.projections.is_empty()
            || param_index(place.local).is_some()
            || !crate::prove::local_soundly_resolvable(body, place.local)
        {
            return None;
        }
        let (definition_index, definition) =
            block.stmts.iter().enumerate().find_map(|(index, statement)| {
                crate::assignment_types::assigned_local_rvalue(body, statement, place.local)
                    .map(|rvalue| (index, rvalue))
            })?;
        if definition_index >= return_index {
            return None;
        }
        let Rvalue::Use(inner) = definition else { return None };
        sem_operand_of_mir(body, inner, &param_index)
            .or_else(|| sem_field_read_operand(body, inner, &param_index))
    };
    let a = resolve_before_return(a_op)?;
    let b = resolve_before_return(b_op)?;

    let cond1 = SemCondTree::Leaf(SemCond { op: SemCmpOp::Lt, a: a.clone(), b: b.clone() });
    let cond2 = SemCondTree::Leaf(SemCond { op: SemCmpOp::Eq, a, b });

    let trust_types::Ty::Adt { name: enum_name, variants, .. } = &body.return_ty else {
        return None;
    };
    let [less, equal, greater] = variants.as_slice() else { return None };
    if less.name != "Less"
        || equal.name != "Equal"
        || greater.name != "Greater"
        || !less.fields.is_empty()
        || !equal.fields.is_empty()
        || !greater.fields.is_empty()
    {
        return None;
    }
    Some(SemAdtReturn3 {
        cond1,
        cond2,
        arm_a: SemAdtArm { variant: less.discriminant, payload: None },
        arm_b: SemAdtArm { variant: equal.discriminant, payload: None },
        arm_c: SemAdtArm { variant: greater.discriminant, payload: None },
        enum_name: enum_name.clone(),
    })
}

/// The arm's SOLE assignment to `join_local`, restricted to a bare `Use`
/// rvalue. `None` (fail-closed) for anything richer (`BinaryOp`/`Cast`/
/// `Aggregate`/…) or for no assignment at all.
pub(super) fn arm_bare_use_value_for(
    body: &trust_types::VerifiableBody,
    arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::Rvalue;
    let rv = arm
        .stmts
        .iter()
        .rev()
        .find_map(|s| crate::assignment_types::assigned_local_rvalue(body, s, join_local))?;
    let Rvalue::Use(op) = rv else { return None };
    sem_operand_of_mir(body, op, param_index)
}

/// Recognize the MULTI-VALUE SwitchInt shape (module doc above). Fail-closed on
/// anything outside the fragment: not exactly one `SwitchInt` in the whole
/// function, fewer than two explicit targets, explicit targets reaching more
/// than one distinct block (or the same block as `otherwise`), an unresolvable
/// discriminant, or an arm value outside the bare-`Use` fragment.
#[must_use]
pub fn sem_cf_return_of_mir_multi_eq(
    func: &trust_types::VerifiableFunction,
) -> Option<SemMultiEqReturn> {
    use trust_types::{BlockId, Statement, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // (1)-(2): VERBATIM copy of `sem_cf_return_of_mir`'s convergence-local + 2-arm
    // extraction.
    let ret_block = unique_return_block(body)?;
    let assigns_local = |b: &trust_types::BasicBlock, loc: usize| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == loc && place.projections.is_empty())
        })
    };
    let join_local = guarded_return_join_local(body, ret_block)?;
    let assigns_0 = |b: &trust_types::BasicBlock| assigns_local(b, join_local);
    let arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Goto(_)) && assigns_0(b))
        .collect();
    if arms.len() != 2 {
        return None;
    }
    let Terminator::Goto(j0) = arms[0].terminator else { return None };
    let Terminator::Goto(j1) = arms[1].terminator else { return None };
    if j0 != j1 {
        return None;
    }

    // (3) exactly ONE `SwitchInt` in the whole function, with 2+ explicit targets.
    let switches: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::SwitchInt { .. }))
        .collect();
    let [switch] = switches.as_slice() else { return None };
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &switch.terminator else {
        return None;
    };
    if targets.len() < 2 {
        return None; // a single-target switch is a DIFFERENT (existing) shape's job.
    }

    let arm_ids: Vec<BlockId> = arms.iter().map(|b| b.id).collect();
    if !guarded_cfg_is_entry_rooted(body, j0, &arm_ids, &[switch.id]) {
        return None;
    }
    if !local_has_only_guarded_writes(body, join_local, arms.len(), 0) {
        return None;
    }
    if join_local != 0 && !local_has_only_guarded_writes(body, 0, 1, 0) {
        return None;
    }
    let then_id = first_arm_on_path(body, targets[0].1, &arm_ids)?;
    for (_, t) in &targets[1..] {
        if first_arm_on_path(body, *t, &arm_ids)? != then_id {
            return None; // every explicit target must converge on the SAME arm.
        }
    }
    let else_id = first_arm_on_path(body, *otherwise, &arm_ids)?;
    if then_id == else_id {
        return None;
    }

    // Distinct values (a well-formed `SwitchInt`'s targets already carry distinct
    // values; dedupe here anyway for defense in depth against a malformed probe).
    let mut values: Vec<i128> = Vec::with_capacity(targets.len());
    for (v, _) in targets {
        let v = i128::try_from(*v).ok()?;
        if values.contains(&v) {
            return None;
        }
        values.push(v);
    }

    let discr_op = sem_operand_of_mir(body, discr, &param_index)?;
    let then_arm = arms.iter().find(|b| b.id == then_id)?;
    let else_arm = arms.iter().find(|b| b.id == else_id)?;
    let then_op = arm_bare_use_value_for(body, then_arm, join_local, &param_index)?;
    let else_op = arm_bare_use_value_for(body, else_arm, join_local, &param_index)?;

    Some(SemMultiEqReturn { discr: discr_op, values, then_op, else_op })
}

// ===========================================================================
// FIELDLESS-ENUM Clone/eq lane (2026-07-16) — the derived `Clone::clone` and
// `PartialEq::eq` of a C-LIKE (fieldless, all-nullary-variant) enum. The value
// of a fieldless enum IS its discriminant (there is no payload to carry), so:
//   * `clone(&self) -> E { *self }` is the IDENTITY on that discriminant, and
//   * `eq(&self, &other) -> bool { disc(*self) == disc(*other) }` is a single
//     `Int` compare of the two enum tags.
// Both are near the existing discriminant/ADT-carrier machinery
// (`SemOperand::Discriminant`, keyed at `MIRSEM_DISCRIMINANT_TAG_KEY`). The
// KERNEL WITNESS + soundness argument live in `trustir_fieldless.rs`; the
// RECOGNIZERS below read the shape DIRECTLY off the MIR and FAIL CLOSED on any
// near-miss (missing explicit variant metadata, a PAYLOAD-bearing enum, an extra
// statement, a non-`Eq` compare, a non-discriminant operand, a rebuild-not-copy
// clone, or an `&mut self`).
// ===========================================================================
/// If `ty` is a FIELDLESS enum ADT — an `Adt` with explicit, nonempty variant
/// metadata whose variants are all nullary with unique, representable tags and
/// whose reflected `fields` is EXACTLY the single signed discriminant field
/// `("__tag", Int{.., signed:true})` — return the complete type descriptor;
/// `None` otherwise (fail-closed).
///
/// The `__tag`-only signature is the extractor's OWN marker for a fieldless
/// enum: `trust-mir-extract` names the discriminant field `__tag` and each
/// variant-`i` field-`j` PAYLOAD `__vi_j`; a fieldless enum has no payload, so
/// only `__tag` survives. The explicit `variants` check is load-bearing: old
/// pre-P4 dumps deserialize enums with `variants: []`, which is intentionally
/// indistinguishable from a struct, and Rust permits a real struct field named
/// `__tag`. Such legacy/ambiguous data MUST decline rather than infer enum-ness
/// from a forgeable field name. A PAYLOAD-bearing enum (e.g. `ProverSystem`
/// with `__v3_0`, `Literal` with `__v0_0`/`__v1_0`) is also declined — modeling
/// its value as just its discriminant would drop the payload.
pub(super) fn explicit_fieldless_enum_ty(ty: &trust_types::Ty) -> Option<&trust_types::Ty> {
    use trust_types::Ty;
    let Ty::Adt { fields, variants, .. } = ty else { return None };
    if variants.is_empty() || variants.iter().any(|variant| !variant.fields.is_empty()) {
        return None;
    }
    let [(fname, Ty::Int { width, signed: true })] = fields.as_slice() else {
        return None;
    };
    if fname != "__tag" || !matches!(*width, 1..=128) {
        return None;
    }
    let fits_tag = |value: i128| match *width {
        1..=127 => {
            let half = 1i128 << (*width - 1);
            (-half..half).contains(&value)
        }
        128 => true,
        _ => false,
    };
    for (index, variant) in variants.iter().enumerate() {
        if !fits_tag(variant.discriminant)
            || variants[..index].iter().any(|prior| prior.discriminant == variant.discriminant)
        {
            return None;
        }
    }
    Some(ty)
}

/// Recognize the FIELDLESS-ENUM `Clone::clone` shape (module doc above).
/// Fail-closed on anything outside the fragment: a non-fieldless (payload-
/// bearing) return enum, more than one block/statement, a non-`Return`
/// terminator, a return rvalue that is not a deref-COPY of the `&self` param
/// (a rebuild via `Aggregate`/`Call`/`SwitchInt` — the payload-enum clone
/// shape — declines here), an `&mut self` base, or a referent enum that
/// differs from the return enum.
#[must_use]
pub fn sem_fieldless_enum_clone_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemFieldlessEnumClone> {
    use trust_types::{Operand, Projection, Rvalue, Statement, Terminator, Ty};
    let body = &func.body;
    if body.arg_count != 1 {
        return None;
    }
    // (1) the RETURN type is a FIELDLESS enum.
    let ret_ty = explicit_fieldless_enum_ty(&body.return_ty)?;
    // Structural identity includes name/fields/variants/discriminants; only the
    // extractor-context flags (`disc_index_safe`, `faithful_enum_repr`) are
    // intentionally ignored by this purpose-built comparator.
    if !body.locals.get(0)?.ty.eq_ignoring_disc_index_safe(ret_ty) {
        return None;
    }
    // (2) EXACTLY one block, terminating in `Return`, with EXACTLY one statement.
    let [block] = body.blocks.as_slice() else { return None };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    let [stmt] = block.stmts.as_slice() else { return None };
    // (3) that statement assigns `_0 := *self` (a deref-copy, or `CopyForDeref`).
    let Statement::Assign { place, rvalue, .. } = stmt else { return None };
    if place.local != 0 || !place.projections.is_empty() {
        return None;
    }
    let src_place = match rvalue {
        Rvalue::Use(Operand::Copy(p)) => p,
        Rvalue::CopyForDeref(p) => p,
        _ => return None,
    };
    if src_place.projections.as_slice() != [Projection::Deref] {
        return None;
    }
    // (4) the deref base is an IMMUTABLE-reference PARAMETER whose referent is
    //     the SAME fieldless enum as the return type.
    let arg_count = body.arg_count;
    let self_param = if (1..=arg_count).contains(&src_place.local) {
        u64::try_from(src_place.local - 1).ok()?
    } else {
        return None;
    };
    let Ty::Ref { mutable: false, inner } = &body.locals.get(src_place.local)?.ty else {
        return None;
    };
    let self_ty = explicit_fieldless_enum_ty(inner)?;
    if !self_ty.eq_ignoring_disc_index_safe(ret_ty) {
        return None;
    }
    Some(SemFieldlessEnumClone { self_param })
}

/// Recognize the FIELDLESS-ENUM `PartialEq::eq` shape (module doc above).
/// Fail-closed on anything outside the fragment: a return rvalue that is not a
/// single `BinOp::Eq` (a `Lt`/`Ne`/… compare, or a payload-comparing `Call`
/// chain — the payload-enum eq shape — declines), an operand that is not a
/// freshly-`Discriminant`-assigned temp (a field read or arbitrary value
/// declines), an `&mut` base, both operands the SAME value/param, or the two
/// enums differing / not fieldless.
#[must_use]
pub fn sem_fieldless_enum_eq_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemFieldlessEnumEq> {
    use trust_types::{BinOp, Operand, Projection, Rvalue, Statement, Terminator, Ty};
    let body = &func.body;
    if body.arg_count != 2 {
        return None;
    }
    if !matches!(body.return_ty, Ty::Bool) {
        return None;
    }
    if !matches!(body.locals.first()?.ty, Ty::Bool) {
        return None;
    }
    let [block] = body.blocks.as_slice() else { return None };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    let arg_count = body.arg_count;
    let is_param = |local: usize| (1..=arg_count).contains(&local);
    // (A) EXACTLY two discriminant assignments followed by the SOLE return
    //     assignment. Reject every extra statement, projected write, lifetime
    //     marker, intrinsic, or reordered use: the witness below models exactly
    //     this three-assignment skeleton and nothing else.
    let [first_disc, second_disc, ret_stmt] = block.stmts.as_slice() else { return None };
    let Statement::Assign { place: ret_place, rvalue: ret_rv, .. } = ret_stmt else {
        return None;
    };
    if ret_place.local != 0 || !ret_place.projections.is_empty() {
        return None;
    }
    let Rvalue::BinaryOp(BinOp::Eq, lop, rop) = ret_rv else { return None };
    let bare_temp = |op: &Operand| -> Option<usize> {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if !p.projections.is_empty() || is_param(p.local) {
            return None;
        }
        Some(p.local)
    };
    let a = bare_temp(lop)?;
    let b = bare_temp(rop)?;
    if a == b {
        return None; // `x == x` is not a two-operand fieldless-enum eq.
    }
    // (B) the first two statements define exactly the two Eq operand temps as
    //     `Discriminant((*param))`, over immutable references to fieldless enums.
    let disc_assignment = |stmt: &Statement| -> Option<(usize, u64, Ty, Ty)> {
        let Statement::Assign { place, rvalue: Rvalue::Discriminant(dp), .. } = stmt else {
            return None;
        };
        if !place.projections.is_empty() || place.local == 0 || is_param(place.local) {
            return None;
        }
        if dp.projections.as_slice() != [Projection::Deref] {
            return None;
        }
        if !is_param(dp.local) {
            return None;
        }
        let disc_ty = body.locals.get(place.local)?.ty.clone();
        if !matches!(disc_ty, Ty::Int { .. }) {
            return None;
        }
        let pidx = u64::try_from(dp.local - 1).ok()?;
        let Ty::Ref { mutable: false, inner } = &body.locals.get(dp.local)?.ty else {
            return None;
        };
        let enum_ty = explicit_fieldless_enum_ty(inner)?.clone();
        let Ty::Adt { fields, .. } = &enum_ty else { unreachable!() };
        if fields.first().map(|(_, ty)| ty) != Some(&disc_ty) {
            return None;
        }
        Some((place.local, pidx, disc_ty, enum_ty))
    };
    let first = disc_assignment(first_disc)?;
    let second = disc_assignment(second_disc)?;
    let ((self_param, self_disc_ty, self_ty), (other_param, other_disc_ty, other_ty)) =
        if first.0 == a && second.0 == b {
            ((first.1, first.2, first.3), (second.1, second.2, second.3))
        } else if first.0 == b && second.0 == a {
            ((second.1, second.2, second.3), (first.1, first.2, first.3))
        } else {
            return None;
        };
    if self_disc_ty != other_disc_ty || !self_ty.eq_ignoring_disc_index_safe(&other_ty) {
        return None; // both operands must use the same discriminant and enum types.
    }
    if self_param == other_param {
        return None; // must be two DISTINCT params (self and other).
    }
    Some(SemFieldlessEnumEq { self_param, other_param })
}

/// Decode one `SwitchInt` case literal according to the exact integer type of
/// its discriminant temporary. `SwitchInt` stores the raw bits as `u128`; the
/// fieldless witness models the enum discriminant as an unbounded signed `Int`,
/// so sign extension is load-bearing. Values with bits outside the declared
/// width, zero-width integers, or unsigned values outside `i128` decline.
pub(super) fn switch_int_literal(raw: u128, width: u32, signed: bool) -> Option<i128> {
    if !(1..=128).contains(&width) {
        return None;
    }
    if width < 128 && raw >= (1u128 << width) {
        return None;
    }
    if !signed {
        return i128::try_from(raw).ok();
    }
    if width == 128 {
        return Some(raw as i128);
    }
    let shift = 128 - width;
    Some(((raw << shift) as i128) >> shift)
}

/// Recognize the exact fieldless-enum guarded identity-select used by
/// `cmp::Ordering::then`. Every clause is structural and fail-closed:
///
/// * exactly two by-value parameters, `_0`, the declared return, and both
///   parameters have one identical explicit fieldless-enum type;
/// * exactly four entry-reachable blocks exist: entry, selected arm, fallback
///   arm, and one empty `Return` join;
/// * entry contains the sole statement, a bare discriminant read of `self`,
///   immediately consumed by the sole one-target `SwitchInt`;
/// * that literal is one of the enum's declared unique tags, its target writes
///   `_0 := other`, `otherwise` writes `_0 := self`, and both go directly to
///   the common join;
/// * no parameter reassignment/alias, projected/extra return write, call
///   destination, marker/effect statement, or malformed assignment typing is
///   admitted.
///
/// The target literal is modeled generically as `k`: the resulting semantics is
/// `if disc(self) == k { other } else { self }`. This is sound even when variant
/// names differ, and avoids treating diagnostic names as type authority.
#[must_use]
pub fn sem_fieldless_enum_then_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemFieldlessEnumThen> {
    use std::collections::HashSet;

    use trust_types::{BlockId, Operand, Place, Rvalue, Statement, Terminator, Ty};

    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) || body.arg_count != 2 {
        return None;
    }

    let ret_ty = explicit_fieldless_enum_ty(&body.return_ty)?;
    for local in 0..=2 {
        let local_ty = &body.locals.get(local)?.ty;
        explicit_fieldless_enum_ty(local_ty)?;
        if !local_ty.eq_ignoring_disc_index_safe(ret_ty) {
            return None;
        }
    }
    if param_reassigned_by_stmt(body, 1) || param_reassigned_by_stmt(body, 2) {
        return None;
    }
    if !local_has_only_guarded_writes(body, 0, 2, 0) || body.blocks.len() != 4 {
        return None;
    }

    let ids: HashSet<BlockId> = body.blocks.iter().map(|block| block.id).collect();
    if ids.len() != 4 {
        return None;
    }
    let block = |id| body.blocks.iter().find(|candidate| candidate.id == id);
    let entry = block(BlockId(0))?;
    let [disc_stmt] = entry.stmts.as_slice() else { return None };
    let Statement::Assign { place: disc_dest, rvalue: Rvalue::Discriminant(disc_source), .. } =
        disc_stmt
    else {
        return None;
    };
    if !disc_dest.projections.is_empty()
        || disc_dest.local == 0
        || (1..=2).contains(&disc_dest.local)
        || disc_source != &Place::local(1)
    {
        return None;
    }
    let (width, signed) = match &body.locals.get(disc_dest.local)?.ty {
        Ty::Int { width, signed } => (*width, *signed),
        _ => return None,
    };
    // Every declared discriminant must be exactly representable by the MIR
    // discriminant temporary. Otherwise interpreting its raw switch literal as
    // the enum's mathematical tag would be unjustified.
    let Ty::Adt { variants, .. } = ret_ty else { unreachable!() };
    for variant in variants {
        let encoded = if width == 128 {
            variant.discriminant as u128
        } else {
            (variant.discriminant as u128) & ((1u128 << width) - 1)
        };
        if switch_int_literal(encoded, width, signed) != Some(variant.discriminant) {
            return None;
        }
    }

    let Terminator::SwitchInt {
        discr, targets, otherwise, exhaustive_enum_unreachable: false, ..
    } = &entry.terminator
    else {
        return None;
    };
    let (Operand::Copy(switch_place) | Operand::Move(switch_place)) = discr else {
        return None;
    };
    if !switch_place.projections.is_empty() || switch_place.local != disc_dest.local {
        return None;
    }
    let [(raw_tag, selected_id)] = targets.as_slice() else { return None };
    let selected_tag = switch_int_literal(*raw_tag, width, signed)?;
    if !variants.iter().any(|variant| variant.discriminant == selected_tag) {
        return None;
    }
    let fallback_id = *otherwise;

    let read_arm = |id: BlockId, wanted_param: usize| -> Option<BlockId> {
        let arm = block(id)?;
        let [statement] = arm.stmts.as_slice() else { return None };
        let Statement::Assign {
            place,
            rvalue: Rvalue::Use(Operand::Copy(source) | Operand::Move(source)),
            ..
        } = statement
        else {
            return None;
        };
        if place != &Place::local(0) || source != &Place::local(wanted_param) {
            return None;
        }
        let Terminator::Goto(join) = &arm.terminator else { return None };
        Some(*join)
    };
    let selected_join = read_arm(*selected_id, 2)?;
    let fallback_join = read_arm(fallback_id, 1)?;
    if selected_join != fallback_join {
        return None;
    }
    let join = block(selected_join)?;
    if !join.stmts.is_empty() || !matches!(join.terminator, Terminator::Return) {
        return None;
    }

    let expected: HashSet<BlockId> =
        [BlockId(0), *selected_id, fallback_id, selected_join].into_iter().collect();
    if expected.len() != 4 || expected != ids || cfg_reachable_from(body, BlockId(0))? != expected {
        return None;
    }

    Some(SemFieldlessEnumThen { self_param: 0, other_param: 1, selected_tag })
}
