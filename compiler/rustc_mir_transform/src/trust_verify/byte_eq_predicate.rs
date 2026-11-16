//! Trust (STR_BYTE_POSITION, 2026-10-04): the char-boundary premise for
//! `s.bytes().position(|b| b == K)`, COMPILER side.
//!
//! ## What is decided here (everything by `DefId` / type / lang item)
//!
//! 1. CLOSURE SHAPE, at the analysis seam (`trust_init_byte_eq_predicates`). A local
//!    plain closure with NO captures whose pre-inlining MIR
//!    (`mir_drops_elaborated_and_const_checked`, never a stolen body) is exactly
//!    `_0 = Eq(_2, K)` (either side, optionally through one `_k = copy _2` hop) in its
//!    one reachable block, which returns: `_2: u8`, `_0: bool`, `K` a fully evaluated
//!    `u8` constant with no generic parameter, `_2` never written, the environment
//!    `_1` never read. Such a closure returns `true` exactly for the item `K`.
//! 2. CALL SITE, per verified body (`ascii_eq_bytes_position_calls`), over the SAME
//!    `body` vcgen is handed: a `Call` whose callee is the `Iterator` lang item's
//!    `position` resolving into an authentic foundational crate
//!    (`adapter_yield::authenticated_iterator_method`), whose `Self` is core's
//!    `str::Bytes`, whose closure argument is a certified closure with `K < 0x80`.
//!    The answer is `BlockId -> K` for those call blocks.
//!
//! What it does NOT decide: that the iterator is a fresh `str::bytes(s)` consumed
//! by exactly one dynamic execution of that call, that the index is used on the same
//! string, or which endpoints are credited. All of that is re-gated in `trust_vcgen`
//! (`generate::str_offset`, the `IteratorPosition` arm of `wrapped_search_origin`).
//! The premise is `docs/TCB.md`'s `STR_BYTE_POSITION`.
//!
//! Everything fails CLOSED: any mismatch installs nothing.
//! `-Ztrust-no-str-byte-position` installs nothing at all.

use rustc_middle::mir::traversal;

use super::*;

/// The analysis-seam initializer, called from `rustc_interface::passes::analysis`
/// beside `trust_init_adapter_yield_premises`, while each closure's
/// `mir_drops_elaborated_and_const_checked` is still borrowable. A body verified
/// before this seam sees an empty map and fails closed.
pub fn trust_init_byte_eq_predicates(tcx: TyCtxt<'_>) {
    if !verification_enabled(tcx.sess)
        || with_crate_verification_state(tcx.sess, |state| state.byte_eq_initialized)
    {
        return;
    }
    let predicates = if tcx.sess.opts.unstable_opts.trust_no_str_byte_position {
        FxHashMap::default()
    } else {
        collect_byte_eq_closures(tcx)
    };
    with_crate_verification_state(tcx.sess, |state| {
        state.byte_eq_predicates = predicates;
        state.byte_eq_initialized = true;
    });
}

fn collect_byte_eq_closures(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, u8> {
    let mut out = FxHashMap::default();
    for &def in tcx.mir_keys(()) {
        if tcx.def_kind(def) != DefKind::Closure {
            continue;
        }
        if let Some(k) = byte_eq_closure_constant(tcx, def) {
            out.insert(def, k);
        }
    }
    out
}

/// `Some(K)` when `def` is a capture-free plain closure whose whole body is
/// `item == K` over a `u8` item (module banner, point 1).
// `is_stolen()` is untracked, exactly as at the other pre-steal seams: a stolen
// body admits nothing (fail-closed).
#[allow(rustc::untracked_query_information)]
fn byte_eq_closure_constant<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Option<u8> {
    let closure_ty = tcx.type_of(def).instantiate_identity().skip_normalization();
    let ty::Closure(_, closure_args) = closure_ty.kind() else {
        return None;
    };
    if !closure_args.as_closure().upvar_tys().is_empty() {
        return None;
    }
    let elaborated = tcx.mir_drops_elaborated_and_const_checked(def);
    if elaborated.is_stolen() {
        return None;
    }
    let body = elaborated.borrow();
    if body.tainted_by_errors.is_some() || body.arg_count != 2 {
        return None;
    }
    let item = Local::from_usize(2);
    if body.local_decls[item].ty != tcx.types.u8
        || body.local_decls[rustc_middle::mir::RETURN_PLACE].ty != tcx.types.bool
    {
        return None;
    }
    let reachable: Vec<BasicBlock> = traversal::reachable(&body).map(|(bb, _)| bb).collect();
    let [bb] = reachable[..] else {
        return None;
    };
    let data = &body.basic_blocks[bb];
    if !matches!(data.terminator().kind, TerminatorKind::Return) {
        return None;
    }
    let typing_env = body.typing_env(tcx);
    let mut hop: Option<Local> = None;
    let mut constant: Option<u8> = None;
    for statement in &data.statements {
        match &statement.kind {
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::ConstEvalCounter => {}
            StatementKind::Assign(assign) => {
                let (dest, rvalue) = &**assign;
                match rvalue {
                    // `_k = copy _2`, once, before the comparison, into a temp.
                    Rvalue::Use(Operand::Copy(place), _)
                        if place.as_local() == Some(item)
                            && hop.is_none()
                            && constant.is_none() =>
                    {
                        let temp = dest.as_local()?;
                        if temp.as_usize() <= body.arg_count {
                            return None;
                        }
                        hop = Some(temp);
                    }
                    // `_0 = Eq(item, K)` / `Eq(K, item)`, once.
                    Rvalue::BinaryOp(MirBinOp::Eq, operands)
                        if dest.as_local() == Some(rustc_middle::mir::RETURN_PLACE)
                            && constant.is_none() =>
                    {
                        let (a, b) = &**operands;
                        let is_item = |operand: &Operand<'tcx>| match operand {
                            Operand::Copy(place) | Operand::Move(place) => place
                                .as_local()
                                .is_some_and(|local| local == item || Some(local) == hop),
                            _ => false,
                        };
                        let byte = |operand: &Operand<'tcx>| -> Option<u8> {
                            let Operand::Constant(c) = operand else { return None };
                            if c.const_.ty() != tcx.types.u8 || c.const_.has_param() {
                                return None;
                            }
                            let scalar = c.const_.try_eval_scalar_int(tcx, typing_env)?;
                            (scalar.size().bytes() == 1).then(|| scalar.to_u8())
                        };
                        constant = match (is_item(a), is_item(b)) {
                            (true, false) => Some(byte(b)?),
                            (false, true) => Some(byte(a)?),
                            _ => return None,
                        };
                    }
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    constant
}

/// The `position` call blocks of `body` that pass a certified `|b| b == K` closure,
/// `K < 0x80`, to core's `Iterator::position` on `str::Bytes` (module banner,
/// point 2). Empty for every other body, and for a promoted or a shim.
pub(super) fn ascii_eq_bytes_position_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashMap<trust_types::BlockId, u8> {
    let mut out = FxHashMap::default();
    if body.source.promoted.is_some() || !matches!(body.source.instance, ty::InstanceKind::Item(_))
    {
        return out;
    }
    let predicates =
        with_crate_verification_state(tcx.sess, |state| state.byte_eq_predicates.clone());
    if predicates.is_empty() {
        return out;
    }
    let Some(iterator) = tcx.lang_items().iterator_trait() else {
        return out;
    };
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
            continue;
        };
        let Some((_, generic_args, name)) =
            adapter_yield::authenticated_iterator_method(tcx, body, iterator, func)
        else {
            continue;
        };
        if name != "position" || args.len() != 2 {
            continue;
        }
        let ty::Adt(adt, _) = generic_args.type_at(0).kind() else {
            continue;
        };
        if !is_core_str_bytes(tcx, adt.did()) {
            continue;
        }
        let ty::Closure(closure, _) = args[1].node.ty(&body.local_decls, tcx).kind() else {
            continue;
        };
        let Some(&k) = closure.as_local().and_then(|local| predicates.get(&local)) else {
            continue;
        };
        if k < 0x80 {
            out.insert(trust_types::BlockId(bb.as_usize()), k);
        }
    }
    out
}

/// Whether `body` was handed any byte-position premise. Such a body is never
/// check-elided (`elide_kernel_certified_checks`), the `ADAPTER_YIELD` precedent.
pub(super) fn body_carries_premise<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    !ascii_eq_bytes_position_calls(tcx, body).is_empty()
}

/// The disclosure strings for `body` (JSON `modeled_facts` and the human note), in
/// block order.
// The map is SORTED before use.
#[allow(rustc::potential_query_instability)]
pub(super) fn modeled_facts<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<String> {
    let calls = ascii_eq_bytes_position_calls(tcx, body);
    let mut rows: Vec<(usize, u8)> = calls.into_iter().map(|(block, k)| (block.0, k)).collect();
    rows.sort_unstable();
    rows.into_iter()
        .map(|(block, k)| {
            format!("STR_BYTE_POSITION(bb{block}: str::Bytes::position(|b| b == {k:#04x}))")
        })
        .collect()
}

/// core's `str::Bytes` (`core::str::iter::Bytes`), by crate and def path.
fn is_core_str_bytes(tcx: TyCtxt<'_>, did: DefId) -> bool {
    crate_is_authentic_foundational(tcx, did.krate)
        && tcx.crate_name(did.krate) == rustc_span::sym::core
        && tcx.def_path(did).to_string_no_crate_verbose() == "::str::iter::Bytes"
}
