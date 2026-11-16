//! Byte-length bounds for immutable results of compiler-authenticated primitive
//! integer formatting. No path/marker spelling supplies identity or width.

use super::*;

/// Trace a shared String receiver through whole-value aliases/moves to its
/// actual compiler-recorded ToString call. The complete value seam refuses
/// second writes, partial stores, unknown writes and mutable/raw escapes at
/// EVERY hop. Whole Drop terminators are ignored only for this origin question:
/// the fact is about an actual successful `String::len` return, never the String
/// after its destruction. Nothing is asserted on the String's bare heap length.
pub(super) fn decimal_string_origin(
    func: &VerifiableFunction,
    local: usize,
    fuel: usize,
) -> Option<BlockId> {
    if fuel == 0 {
        return None;
    }
    // This is an origin search, not an unconditional value fact. Before its
    // result is consumed, the caller requires the exact compiler-recorded
    // primitive formatting call and its returned std String Freeze license.
    // That license supplies the cell detail opaque/Seq lowering loses. The
    // cell-blind stability guard still refuses every mutable/raw escape and
    // partial/second/unknown write at EACH hop, including moves and aliases.
    if !crate::local_defs::body_slot_is_stable_modulo_whole_drops(&func.body, local) {
        return None;
    }
    match crate::local_defs::unique_initializing_modulo_whole_drops(func, local)? {
        crate::local_defs::WholeDefinition::Assign(rvalue) => {
            let place = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Ref { mutable: false, place }
                | Rvalue::CopyForDeref(place) => place,
                _ => return None,
            };
            if !place.projections.is_empty() {
                return None;
            }
            decimal_string_origin(func, place.local, fuel - 1)
        }
        crate::local_defs::WholeDefinition::Call(call) => {
            // This is the exact call from this immutable body, not a matching
            // display name or the first textual write to the local.
            func.body
                .blocks
                .iter()
                .find(|block| std::ptr::eq(&block.terminator, call))
                .map(|block| block.id)
        }
    }
}

/// Add bounds only to a single-valued numeric length result. Existing payload
/// attachment and the statement-version oracle keep the facts on that result;
/// no bound is exported onto a mutable/reseated String or another length call.
pub(super) fn build_primitive_decimal_len_guard_map(
    func: &VerifiableFunction,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let Some(table) = crate::compiler_primitive_decimal_strings(func) else {
        return FxHashMap::default();
    };
    build_primitive_decimal_len_guard_map_with_table(func, &table)
}

pub(super) fn build_primitive_decimal_len_guard_map_with_table(
    func: &VerifiableFunction,
    table: &crate::PrimitiveDecimalStringTable,
) -> FxHashMap<BlockId, Vec<Formula>> {
    let mut payloads = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call {
            args,
            dest,
            target: Some(_),
            callee_key,
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            ..
        } = &block.terminator
        else {
            continue;
        };
        if args.len() != 1
            || !dest.projections.is_empty()
            || !trust_types::CalleeKey::opt_is_one_of(
                callee_key.as_ref(),
                &[trust_types::SysrootItem::StringLen],
            )
            || !super::iterator_yield::payload_carries_global_fact(func, dest.local)
        {
            continue;
        }
        let (Operand::Copy(receiver) | Operand::Move(receiver)) = &args[0] else {
            continue;
        };
        if !receiver.projections.is_empty() {
            continue;
        }
        let Some(receiver_ty) = crate::place_ty_cow(func, receiver) else {
            continue;
        };
        if !matches!(receiver_ty.as_ref(), Ty::Ref { mutable: false, inner }
            if matches!(inner.as_ref(), Ty::Adt { name, .. }
                if super::collection_range::is_std_string_adt_name(name)))
        {
            continue;
        }
        let Some(origin) = decimal_string_origin(func, receiver.local, func.body.locals.len() + 1)
        else {
            continue;
        };
        let Some(max_bytes) = table.max_bytes_at(func, origin) else {
            continue;
        };
        let len = Formula::var_owned(place_to_var_name(func, dest), Sort::Int);
        payloads.push((
            dest.local,
            vec![
                Formula::Ge(Box::new(len.clone()), Box::new(Formula::Int(0))),
                Formula::Le(Box::new(len), Box::new(Formula::Int(i128::from(max_bytes)))),
            ],
        ));
    }
    super::iterator_yield::attach_payload_facts(func, payloads)
}
