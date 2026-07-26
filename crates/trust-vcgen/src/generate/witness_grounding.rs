// Return-value grounding for functions returning `Option`/`Result` and for
// paired length and ordering witnesses. An ungrounded return leaves the
// postcondition talking about a model variable nothing pins, so the credited
// pairs here are what make an `ensures` over a returned container provable.

use super::*;

/// Whether `name` is EXACTLY the std/core `Option` ADT path — never a substring
/// match. A substring gate (`name.contains("Option")`) is a FALSE-PROVE hole: a
/// user enum whose path merely contains "Option" (`ConfigOption`, `Optional`, a
/// type in a module named `option`) with an INVERTED variant order (payload
/// variant declared first = index 0) would be wrongly credited, and the spec
/// parser lowers `.is_some()`/`.is_none()`/`.unwrap()` PURELY BY METHOD NAME
/// regardless of receiver type — so `#[ensures(|r| r.is_some())]` over a body
/// returning that enum's index-0 payload variant would prove a FALSE post
/// (`_0_discr==1` pinned, `Not(post)` = `_0_discr==0`, `1==0` UNSAT ⇒ vacuous
/// PROVE). `core`/`std` are reserved, so an exact canonical-path match is sound.
/// The `name` carries no generic args (they are resolved into the ADT's
/// `fields`/`variants`), so `==` is correct (verified via -Ztrust-dump=mir:<dir>:
/// `std::option::Option`).
pub(super) fn is_std_option_name(name: &str) -> bool {
    name == "std::option::Option" || name == "core::option::Option"
}

/// Whether `name` is EXACTLY the std/core `Result` ADT path — the same
/// exact-canonical-path discipline as [`is_std_option_name`] (a substring gate
/// is a FALSE-PROVE hole; see that doc — the argument carries over verbatim,
/// with the added twist that Result's MODEL discriminant convention is INVERTED
/// vs its machine variant order, so misclassifying a user enum here would flip
/// `is_ok`/`is_err` polarity outright).
pub(super) fn is_std_result_name(name: &str) -> bool {
    name == "std::result::Result" || name == "core::result::Result"
}

/// The PARSER-convention model discriminant for a return-slot construction of
/// std enum `kind` via machine variant index `variant` (0 or 1).
///
/// The spec parser (`trust_types::spec_parse::map_method_call`) models BOTH
/// wrappers with ONE convention — `{base}_discr == 0` = the "empty" variant:
///   `is_none()`/`is_err()` => `_0_discr == 0`;
///   `is_some()`/`is_ok()`  => `_0_discr != 0`.
/// For `Option` the machine variant order matches (None = variant 0, Some =
/// variant 1), so the mapping is the identity. For `Result` it is INVERTED:
/// `Ok` is machine variant 0 and `Err` is variant 1 (`Result { Ok(T), Err(E) }`
/// declaration order — pinned by the `std_result_ty` lowering fixtures), so an
/// `Ok` construction must pin the MODEL discr to 1 and an `Err` to 0. Pinning
/// the raw variant index instead would make an `Ok` return satisfy `is_err()`
/// and refute `is_ok()` — a polarity swap that both false-PROVES and
/// false-FAILS. Only ever called with `variant <= 1` (the resolver's gate).
pub(super) fn std_enum_model_discr(kind: StdEnumReturn, variant: usize) -> i128 {
    match kind {
        StdEnumReturn::Option => variant as i128,
        StdEnumReturn::Result => {
            if variant == 0 { 1 } else { 0 }
        }
    }
}

/// The machine variant index of `kind`'s PAYLOAD-carrying variant (`Some` /
/// `Ok`) — the only variant whose single operand the return pin may credit as
/// the parser's `_0_value` payload term.
pub(super) fn std_enum_payload_variant(kind: StdEnumReturn) -> usize {
    match kind {
        StdEnumReturn::Option => 1, // Some
        StdEnumReturn::Result => 0, // Ok
    }
}

// ======================================================================
// Len-witness / enum-return debug instrumentation (env `TRUST_LENWITNESS_DEBUG`)
// ======================================================================
// PURE DIAGNOSTICS — no grounding logic reads any of this. Every print is
// behind `lenwitness_debug()` (resolved once per process via `OnceLock`), so
// with the env var UNSET (the `targo test` baseline) nothing fires, the
// thread-local is never touched, and behavior is byte-identical. The
// current function's def-path is stashed in a thread-local at the lane entry
// so the two `func`-less helpers (`resolve_enum_return_aggregate_with_block`,
// `len_pair_coverage`) can still tag their lines. Every line is
// `LENWITNESS: [<def_path>] <fact>` so the coordinator can
// `grep LENWITNESS | grep -E 'certify_upper|::certify\b'` and diff the failing
// `certify_upper` reason against the succeeding crown `certify`.
/// Whether the len-witness debug instrumentation is enabled. Cached once per
/// process (the coordinator sets the env for its single run; tests never do).
#[inline]
pub(super) fn lenwitness_debug() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("TRUST_LENWITNESS_DEBUG").is_ok())
}

/// Stash the current function's def-path for the `func`-less helpers. No-op
/// unless `TRUST_LENWITNESS_DEBUG` is set.
pub(super) fn lenwitness_dbg_set_fn(def_path: &str) {
    if lenwitness_debug() {
        LENWITNESS_DBG_FN.with(|c| {
            let mut s = c.borrow_mut();
            s.clear();
            s.push_str(def_path);
        });
    }
}

pub(super) fn lenwitness_dbg_fn() -> String {
    LENWITNESS_DBG_FN.with(|c| c.borrow().clone())
}

/// Compact one-token description of the whole-local definition of `_0` in a
/// block, for the enum-return resolver trace (why a return path did / didn't
/// resolve to an in-body `Ok(..)`/`Some(..)` aggregate).
pub(super) fn lenwitness_rvalue_tag(rv: &Rvalue) -> String {
    match rv {
        Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, ops) => {
            format!("Aggregate(Adt name={name} variant={variant} ops={})", ops.len())
        }
        Rvalue::Aggregate(kind, ops) => format!("Aggregate({kind:?} ops={})", ops.len()),
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => {
            format!("Use(move/copy _{} proj={})", p.local, p.projections.len())
        }
        Rvalue::Use(Operand::Constant(_)) => "Use(const)".to_string(),
        Rvalue::BinaryOp(op, ..) => format!("BinaryOp({op:?})"),
        Rvalue::CheckedBinaryOp(op, ..) => format!("CheckedBinaryOp({op:?})"),
        Rvalue::UnaryOp(op, _) => format!("UnaryOp({op:?})"),
        Rvalue::Cast(..) => "Cast".to_string(),
        Rvalue::Ref { .. } => "Ref".to_string(),
        _ => "other-rvalue".to_string(),
    }
}

/// Resolve the return DISCRIMINANT for a return path that FORWARDS a callee
/// `Call` result whole into `_0` (`_0 = move call_dest`, where `call_dest` is
/// the dest of a `Call` terminator). The optimizer emits this shape — instead
/// of a fresh in-body `Err(e)` aggregate — for the `match inner() { Ok(v) =>
/// .., Err(e) => return Err(e) }` arm when `inner()` and the caller share the
/// `Result<_, E>` return type (crown escapes only because its optimizer
/// happened to rebuild an in-body `Err` aggregate on every path). Without this,
/// `resolve_enum_return_aggregate` finds NO in-body wrapper aggregate on the
/// forward-return path, `_0`'s def bottoms out at a Call-dest with no
/// whole-local def, and the whole discr gate fails closed (`_0_discr`
/// UNGROUNDED for the entire function — the b62 `certify_upper` bug).
///
/// Returns `(kind, variant)` — the std enum kind (from the return type) and the
/// EMPTY (non-payload) variant the dominating `match inner()` discriminant
/// switch PROVABLY forces for the edge reaching `fwd_block` — or `None`
/// (fail-closed) otherwise.
///
/// SOUNDNESS (why only forced-EMPTY-variant edges ground): the pin is
/// `_0_discr == std_enum_model_discr(kind, EMPTY)`, TRUE on this path iff
/// reaching `fwd_block` implies `discriminant(call_dest) == EMPTY_tag`. This
/// holds when (1) `call_dest` is a `Call` dest whose value is stable
/// (`place_source_is_stable` — so its discriminant is IDENTICAL at the switch
/// and at the forward, even across loops), (2) a `SwitchInt` on
/// `discriminant(call_dest)` DOMINATES `fwd_block` and EXACTLY ONE of its edges
/// reaches `fwd_block` while AVOIDING the switch (so every execution reaching
/// `fwd_block` left the switch on that edge — with `call_dest` stable, its
/// discriminant equals that edge's tag), and (3) that tag's variant is the
/// EMPTY (non-payload) variant. Grounding the EMPTY variant needs NO
/// payload/len pins — leaving those terms free is the sound direction (a free
/// var only adds refutability, never manufactures a proof), exactly as the
/// in-body `Err` (`bb3`) path is handled today. A forwarded PAYLOAD
/// (`Ok`/`Some`) value would leave its payload/len terms free-yet-unpinnable in
/// a REFUTABLE VC — a false-PROVE — so a payload-variant-forced edge (and any
/// non-forcing, unstable, non-`discriminant(call_dest)`, or unknown edge) stays
/// UNGROUNDED (fail-closed).
pub(super) fn resolve_forwarded_call_return_variant(
    func: &VerifiableFunction,
    call_dest: usize,
    fwd_block: usize,
) -> Option<(StdEnumReturn, usize)> {
    const FUEL: u32 = 8;
    // (1) `call_dest` is a `Call` dest, and its value is stable end-to-end (so
    // `discriminant(call_dest)` at the switch equals `_0`'s discriminant at the
    // forward). A param / undefined / mutated local is NOT a forwarded call
    // result and stays fail-closed.
    let is_call_dest = func.body.blocks.iter().any(|b| {
        matches!(&b.terminator, Terminator::Call { dest, .. }
            if dest.local == call_dest && dest.projections.is_empty())
    });
    // NOTE: no GLOBAL stability requirement here — when the optimizer writes
    // the callee result straight into `_0`, every OTHER return path also
    // writes `_0` (their in-body aggregates), so global single-def can never
    // hold. Soundness instead comes from the PATH-REGION no-write check below
    // (2d): discriminant(call_dest) at the switch equals its value at Return
    // along this path iff nothing writes `call_dest` between the switch edge
    // and Return — the only segment that matters.
    if !is_call_dest {
        return None;
    }
    // The return type fixes the std enum + its variant defs; the forwarded value
    // shares this type, so `discriminant(call_dest)` reads the SAME layout.
    let Some(Ty::Adt { name, variants, .. }) = crate::local_ty_ref(func, 0) else {
        return None;
    };
    let kind = if is_std_option_name(name) {
        StdEnumReturn::Option
    } else if is_std_result_name(name) {
        StdEnumReturn::Result
    } else {
        return None;
    };
    let payload_variant = std_enum_payload_variant(kind);
    for gblock in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &gblock.terminator else {
            continue;
        };
        let g = gblock.id.0;
        // A switch AT the forward block conditions nothing about the value
        // already being forwarded there.
        if g == fwd_block {
            continue;
        }
        // (2a) the switch discriminant is `discriminant(call_dest)`.
        let Some(d) = operand_root_local(func, discr, FUEL) else { continue };
        let Some(Rvalue::Discriminant(p)) = crate::unique_whole_local_def(func, d) else {
            continue;
        };
        if p.local != call_dest || !p.projections.is_empty() {
            continue;
        }
        // (2b) the switch DOMINATES the forward block (it is unreachable from
        // entry while avoiding the switch — every path to it passes the switch).
        if reachable_avoiding(func, 0, &one_block_set(g)).contains(&fwd_block) {
            continue;
        }
        // (2c) EXACTLY ONE switch edge reaches the forward block avoiding the
        // switch; that edge's selected variant is forced on this return path.
        let avoid_g = one_block_set(g);
        let mut n_reaching = 0usize;
        let mut forced: Option<usize> = None;
        let mut edge_target: Option<usize> = None;
        for (tag, tgt) in targets {
            if !reachable_avoiding(func, tgt.0, &avoid_g).contains(&fwd_block) {
                continue;
            }
            n_reaching += 1;
            edge_target = Some(tgt.0);
            forced = i128::try_from(*tag)
                .ok()
                .and_then(|t| variants.iter().position(|v| v.discriminant == t));
        }
        if reachable_avoiding(func, otherwise.0, &avoid_g).contains(&fwd_block) {
            n_reaching += 1;
            edge_target = Some(otherwise.0);
            // `otherwise` selects the COMPLEMENT of the explicit tags; force a
            // variant only when that complement is a SINGLE variant (the exact
            // 2-variant / `n-1`-explicit-target enum partition — e.g. Result's
            // `switchInt(discr) -> [0: Ok]` with `otherwise` = Err).
            let covered: FxHashSet<i128> =
                targets.iter().filter_map(|(t, _)| i128::try_from(*t).ok()).collect();
            let remaining: Vec<usize> = variants
                .iter()
                .enumerate()
                .filter(|(_, v)| !covered.contains(&v.discriminant))
                .map(|(i, _)| i)
                .collect();
            forced = if remaining.len() == 1 { Some(remaining[0]) } else { None };
        }
        if n_reaching != 1 {
            continue;
        }
        let Some(variant) = forced else { continue };
        // (3) ground ONLY the EMPTY (non-payload) variant — a forwarded payload
        // value's len/value terms cannot be pinned, so leaving them free would
        // false-PROVE.
        if variant == payload_variant {
            continue;
        }
        // (2d) PATH-REGION NO-WRITE: `discriminant(call_dest)` at the switch
        // equals its discriminant at `Return` along this path iff no block
        // reachable from the chosen edge (avoiding the switch — the region S
        // every switch->Return path on this edge stays inside, since the
        // switch dominates `fwd_block`) writes `call_dest` — by statement
        // (ANY projection: a field write also perturbs the value) or as a
        // Call dest. The other return paths' `_0` writes live OUTSIDE S, so
        // this is exactly the sound scope. Fail closed on any write.
        let Some(et) = edge_target else { continue };
        let region = reachable_avoiding(func, et, &avoid_g);
        let region_writes = func.body.blocks.iter().any(|b| {
            if !region.contains(&b.id.0) {
                return false;
            }
            let stmt_write = b.stmts.iter().any(|s| {
                matches!(s, Statement::Assign { place, .. } if place.local == call_dest)
            });
            let call_write = matches!(&b.terminator, Terminator::Call { dest, .. }
                if dest.local == call_dest);
            stmt_write || call_write
        });
        if region_writes {
            continue;
        }
        return Some((kind, variant));
    }
    None
}

/// Resolve the std-`Option`/`Result` aggregate that defines the return value
/// `_0` on the path through `vc_block` into the `Return` block `block`,
/// following up to a few `_0 = move/copy _k` indirections. The common
/// `if c { Some(x) } else { None }` tail lowers each arm's aggregate onto a
/// temp `_k` in the predecessor block, then `_0 = _k` in the return block, so a
/// DIRECT `_0 = Aggregate` check would miss it. Returns
/// `(enum_kind, variant_index, aggregate_operands)`, or `None` (fail-closed:
/// a Call-dest `_0` — the `?`-desugar `from_residual`, `and_then`/`checked_*` —
/// a non-`Option`/`Result` / multi-variant aggregate, or a chain that does not
/// bottom out in an in-body wrapper aggregate within the bound all yield
/// `None`).
pub(super) fn resolve_enum_return_aggregate<'a>(
    func: &'a VerifiableFunction,
    vc_block: &'a trust_types::BasicBlock,
    block: &'a trust_types::BasicBlock,
) -> Option<(StdEnumReturn, usize, &'a [trust_types::Operand])> {
    resolve_enum_return_aggregate_with_block(func, vc_block, block).map(|(k, v, ops, _)| (k, v, ops))
}

/// [`resolve_enum_return_aggregate`] plus the `BlockId` CONTAINING the resolved
/// aggregate assignment — the len-witness lane's dominance target (a length
/// guard must dominate the CONSTRUCTION of the returned value, which may sit in
/// the predecessor or in the return block itself).
pub(super) fn resolve_enum_return_aggregate_with_block<'a>(
    func: &'a VerifiableFunction,
    vc_block: &'a trust_types::BasicBlock,
    block: &'a trust_types::BasicBlock,
) -> Option<(StdEnumReturn, usize, &'a [trust_types::Operand], BlockId)> {
    // The unique whole-local definition of `local` (no field projection),
    // searched across the predecessor then the return block — the two blocks the
    // pin loop threads. The aggregate lives in `vc_block`, the `_0 = _k` move in
    // `block`; searching both, nearest-def-wins per block, recovers the chain.
    let whole_def = |local: usize| -> Option<(&'a Rvalue, BlockId)> {
        [vc_block, block].into_iter().find_map(|b| {
            b.stmts.iter().find_map(|stmt| match stmt {
                Statement::Assign { place, rvalue, .. }
                    if place.local == local && place.projections.is_empty() =>
                {
                    Some((rvalue, b.id))
                }
                _ => None,
            })
        })
    };
    let mut local = 0usize;
    // The block holding the `_.. = move _local` that fed the CURRENT alias
    // `local` — updated on each alias hop. When the chain bottoms out at a
    // Call-dest with no whole-local def, this is the block where the callee
    // result is forwarded into `_0`'s chain (the dominance target for the
    // forwarded-call switch resolution). Initialized to the PATH-SPECIFIC
    // predecessor `vc_block` — NOT the shared `Return` block, which every
    // return path reaches, so the forwarded-switch resolver's unique-edge
    // check could never pass against it (the real-pipeline sbar trace).
    let mut fwd_block = vc_block.id.0;
    for _ in 0..4 {
        let wd = whole_def(local);
        if lenwitness_debug() {
            let desc = if let Some((rv, b)) = wd {
                format!("{} @bb{}", lenwitness_rvalue_tag(rv), b.0)
            } else {
                "NONE (Call-dest / param / no in-block whole-local def)".to_string()
            };
            eprintln!(
                "LENWITNESS: [{}] resolve bb{}->bb{}: hop _{local} def={desc}",
                lenwitness_dbg_fn(),
                vc_block.id.0,
                block.id.0
            );
        }
        let Some((rv, def_block)) = wd else {
            // No in-block whole-local def for `local` in the [vc_block, block]
            // window. Before giving up, try a GLOBAL unique forward-move hop:
            // the optimizer's `Err(e) => return Err(e)` arm lowers to
            // `_local = move _src; goto Return` where `_src` is the callee
            // `Call` dest — but that assign can sit in a block ABOVE this
            // window (the Err arm's block, with a bare Drop-landing between it
            // and Return). Search the WHOLE function for the UNIQUE whole-local
            // `_local = move/copy _src`; if exactly one exists, hop to `_src`
            // (recording its block as the forward point) and retry. Gated to
            // EXACTLY ONE such def (unambiguous) and runs ONLY on the None path,
            // so a normally-resolving return (crown's in-window aggregates) is
            // never touched — no regression to working functions.
            {
                // Walk the UNIQUE-predecessor chain up from `fwd_block` (fuel 6)
                // looking for THIS path's whole-local def of `local`. Only
                // single-predecessor hops are taken, so every visited block is
                // on this return path — a merge point stops the walk (fail
                // closed). This is path-specific (unlike a global search, which
                // can't tell `_0 = move _srcN` on one path from another) and
                // runs ONLY here in the None branch, so crown's in-window
                // resolution never uses it — no regression.
                let mut cur = fwd_block;
                let mut hopped = false;
                for _ in 0..6 {
                    let preds: Vec<&trust_types::BasicBlock> = func
                        .body
                        .blocks
                        .iter()
                        .filter(|b| {
                            v2_terminator_targets(&b.terminator).iter().any(|t| t.0 == cur)
                        })
                        .collect();
                    let [only] = preds.as_slice() else { break };
                    let def = only.stmts.iter().find_map(|stmt| match stmt {
                        Statement::Assign { place, rvalue, .. }
                            if place.local == local && place.projections.is_empty() =>
                        {
                            Some(rvalue)
                        }
                        _ => None,
                    });
                    if let Some(Rvalue::Use(Operand::Move(p) | Operand::Copy(p))) = def {
                        if p.projections.is_empty() {
                            lenwitness_dbg!(
                                &lenwitness_dbg_fn(),
                                "resolve bb{}->bb{}: PRED-CHAIN forward-move hop _{local} -> _{} @bb{}",
                                vc_block.id.0,
                                block.id.0,
                                p.local,
                                only.id.0
                            );
                            local = p.local;
                            fwd_block = only.id.0;
                            hopped = true;
                        }
                        break;
                    }
                    if def.is_some() {
                        break; // a non-Use def on this path — let the normal arms handle it
                    }
                    cur = only.id.0;
                }
                if hopped {
                    continue;
                }
            }
            // If `local` is a callee `Call` dest forwarded whole into `_0`,
            // resolve the return discriminant via the dominating `match inner()`
            // switch — grounding this forward-return path exactly as an in-body
            // `Err` aggregate would.
            if let Some((k, variant)) =
                resolve_forwarded_call_return_variant(func, local, fwd_block)
            {
                lenwitness_dbg!(
                    &lenwitness_dbg_fn(),
                    "resolve bb{}->bb{}: forwarded Call-dest _{local} RESOLVED kind={k:?} variant={variant} (via dominating switch) @bb{fwd_block}",
                    vc_block.id.0,
                    block.id.0
                );
                return Some((k, variant, &[], BlockId(fwd_block)));
            }
            return None;
        };
        match rv {
            Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, ops)
                if *variant <= 1 =>
            {
                let kind = if is_std_option_name(name) {
                    StdEnumReturn::Option
                } else if is_std_result_name(name) {
                    StdEnumReturn::Result
                } else {
                    lenwitness_dbg!(
                        &lenwitness_dbg_fn(),
                        "resolve bb{}->bb{}: aggregate name={name} is NOT std Option/Result -> None",
                        vc_block.id.0,
                        block.id.0
                    );
                    return None;
                };
                lenwitness_dbg!(
                    &lenwitness_dbg_fn(),
                    "resolve bb{}->bb{}: RESOLVED kind={kind:?} variant={variant} ops={} @bb{}",
                    vc_block.id.0,
                    block.id.0,
                    ops.len(),
                    def_block.0
                );
                return Some((kind, *variant, ops, def_block));
            }
            Rvalue::Use(trust_types::Operand::Copy(p) | trust_types::Operand::Move(p))
                if p.projections.is_empty() =>
            {
                lenwitness_dbg!(
                    &lenwitness_dbg_fn(),
                    "resolve bb{}->bb{}: alias hop _{local} -> _{}",
                    vc_block.id.0,
                    block.id.0,
                    p.local
                );
                // The block holding THIS `_local = move _p` is where the value
                // (ultimately a Call-dest) is forwarded — record it so a
                // bottomed-out Call-dest resolves its switch against this block.
                fwd_block = def_block.0;
                local = p.local;
            }
            _ => {
                lenwitness_dbg!(
                    &lenwitness_dbg_fn(),
                    "resolve bb{}->bb{}: def is not aggregate/alias (Aggregate w/ proj, non-move Use, or variant>1) -> None",
                    vc_block.id.0,
                    block.id.0
                );
                return None;
            }
        }
    }
    lenwitness_dbg!(
        &lenwitness_dbg_fn(),
        "resolve bb{}->bb{}: fuel exhausted (>4 alias hops) -> None",
        vc_block.id.0,
        block.id.0
    );
    None
}

/// The groundability GATE for Option/Result-return postconditions. Returns the
/// set of synthetic spec-model names (`_0_discr`, `_0_value`) that the
/// body-aware contract lane can now GROUND — i.e. connect to the return slot's
/// real construction — or an EMPTY set (fail-closed) when it cannot.
///
/// Credited ONLY when BOTH hold, so the "no free-and-havocked model term on any
/// reachable return path" invariant is preserved unconditionally:
///  (a) the return type is the std/core `Option` or `Result` ADT (exact
///      canonical path — see `is_std_option_name` / `is_std_result_name`) whose
///      lowered variant defs carry the std machine tags (`None`=0/`Some`=1,
///      `Ok`=0/`Err`=1 — a degraded lowering refuses the whole gate), and
///  (b) EVERY `Return`-terminated block's grounding path (its predecessors, or
///      the block itself when it has none — the SAME `vc_blocks` reconstruction
///      the pin loop uses) assigns `_0` via an IN-BODY
///      `Rvalue::Aggregate(Adt{the SAME std enum, variant∈{0,1}})`.
/// If any return path routes `_0` through a `Call` dest (e.g. `and_then` /
/// `checked_*` — `index_midpoint` — or the `?`-desugar `from_residual`), a
/// copy/move of a temp, or a non-wrapper / multi-variant aggregate, the gate
/// returns empty and the postcondition keeps today's fail-closed `Unknown` —
/// strictly no regression, and never a term left free (which would
/// false-refute) or credited-but-unpinned.
///
/// WHICH names are credited:
///  * `_0_discr` — always (once (a)+(b) hold): the pin loop pins it on every
///    return path to the PARSER-convention value (`std_enum_model_discr` —
///    Result's mapping is INVERTED vs its machine variant order).
///  * `_0_value` — only when the payload variant (`Some`/`Ok`) is a single
///    INTEGER field, so the pinned term matches the `Sort::Int` the parser
///    mints. For `Option` a non-integer payload refuses the WHOLE gate
///    (pre-existing behavior, kept: no regression risk in this change); for
///    `Result` — the ny-cert selfcheck/crown shapes, whose payloads are Rat
///    handles / Vec aggregates — `_0_discr` alone is credited and every
///    `_0_value*` / `*_sign` / `.__trust_ok_i` term stays UNGROUNDED, so any
///    postcondition referencing them still routes to the fail-closed
///    SpecModelUngrounded Unknown (never a refutable havoc'd VC).
pub(super) fn enum_return_grounded_model_vars(func: &VerifiableFunction) -> FxHashSet<String> {
    lenwitness_dbg_set_fn(&func.def_path);
    let empty = FxHashSet::default();
    // (a) return type is std/core Option or Result with std variant tags.
    let Some(Ty::Adt { name, variants, .. }) = crate::local_ty_ref(func, 0) else {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: return type of _0 is not Ty::Adt -> _0_discr UNGROUNDED"
        );
        return empty;
    };
    // (kind, payload variant name, payload machine tag, empty-variant name+tag)
    let (kind, payload_name, payload_tag, empty_name, empty_tag) =
        if is_std_option_name(name) {
            (StdEnumReturn::Option, "Some", 1, "None", 0)
        } else if is_std_result_name(name) {
            (StdEnumReturn::Result, "Ok", 0, "Err", 1)
        } else {
            lenwitness_dbg!(
                &func.def_path,
                "discr-gate: return adt name={name} is NOT std Option/Result -> _0_discr UNGROUNDED"
            );
            return empty;
        };
    // Both variant defs present with their std machine tags — the pin loop maps
    // the aggregate's variant INDEX through `std_enum_model_discr`, which is
    // only meaningful for the genuine std layout; a degraded/partial lowering
    // refuses everything (fail-closed).
    let Some(payload_variant) =
        variants.iter().find(|v| v.name == payload_name && v.discriminant == payload_tag)
    else {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: payload variant {payload_name}(tag {payload_tag}) missing from lowered variant defs -> _0_discr UNGROUNDED"
        );
        return empty;
    };
    if !variants.iter().any(|v| v.name == empty_name && v.discriminant == empty_tag) {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: empty variant {empty_name}(tag {empty_tag}) missing from lowered variant defs -> _0_discr UNGROUNDED"
        );
        return empty;
    }
    let int_payload =
        payload_variant.fields.len() == 1 && matches!(payload_variant.fields[0].1, Ty::Int { .. });
    lenwitness_dbg!(
        &func.def_path,
        "discr-gate: kind={kind:?} int_payload={int_payload} (payload fields={})",
        payload_variant.fields.len()
    );
    // Option keeps its pre-existing stricter all-or-nothing gate: a non-integer
    // `Some` payload credits NOTHING (behavior pinned before Result support).
    if kind == StdEnumReturn::Option && !int_payload {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: Option with non-integer Some payload -> whole gate refused, _0_discr UNGROUNDED"
        );
        return empty;
    }
    // (b) every Return path assigns _0 via an in-body aggregate of the SAME
    // std enum as the return type.
    let mut n_return_paths = 0usize;
    for block in &func.body.blocks {
        if !matches!(block.terminator, Terminator::Return) {
            continue;
        }
        let predecessors: Vec<&trust_types::BasicBlock> = func
            .body
            .blocks
            .iter()
            .filter(|pred| v2_terminator_targets(&pred.terminator).contains(&block.id))
            .collect();
        let vc_blocks: Vec<&trust_types::BasicBlock> =
            if predecessors.is_empty() { vec![block] } else { predecessors };
        for &vc_block in &vc_blocks {
            n_return_paths += 1;
            match resolve_enum_return_aggregate(func, vc_block, block) {
                Some((resolved_kind, variant, _)) if resolved_kind == kind => {
                    lenwitness_dbg!(
                        &func.def_path,
                        "discr-gate: return path bb{}->bb{} OK (in-body {resolved_kind:?} variant={variant})",
                        vc_block.id.0,
                        block.id.0
                    );
                }
                other => {
                    lenwitness_dbg!(
                        &func.def_path,
                        "discr-gate: return path bb{}->bb{} FAILS gate ({}) -> _0_discr UNGROUNDED for the WHOLE function",
                        vc_block.id.0,
                        block.id.0,
                        match other {
                            Some((k, _, _)) => format!("resolved kind={k:?} != return kind={kind:?}"),
                            None => "resolve_enum_return_aggregate returned None".to_string(),
                        }
                    );
                    return empty;
                }
            }
        }
    }
    let mut set = FxHashSet::default();
    set.insert("_0_discr".to_string());
    if int_payload {
        set.insert("_0_value".to_string());
    }
    lenwitness_dbg!(
        &func.def_path,
        "discr-gate: ALL {n_return_paths} return path(s) grounded -> credited {set:?}"
    );
    set
}

/// Parse `_0_value.<i>.<j>…_len` (any `#version` token stripped) into its
/// positional field path. `None` for every other shape — the bare `_0_value_len`,
/// non-numeric segments, other bases — which keep today's fail-closed routing.
pub(super) fn parse_len_model_var(name: &str) -> Option<LenModelVar> {
    let base = name.split('#').next().unwrap_or(name);
    let core = base.strip_prefix("_0_value.")?.strip_suffix("_len")?;
    if core.is_empty() {
        return None;
    }
    let path = core.split('.').map(|s| s.parse::<usize>().ok()).collect::<Option<Vec<usize>>>()?;
    Some(LenModelVar { name: base.to_string(), path })
}

/// The COVERED length-term pairs of the declared postconditions: pairs of
/// distinct parseable len model vars appearing together in `Eq` atoms, where
/// NEITHER var occurs anywhere else (see the section banner — an occurrence
/// outside a len/len `Eq` atom would leave the term under-constrained by the
/// equality pin, flipping an honest Unknown into a refutable FAILED).
pub(super) fn len_pair_coverage(posts: &[&Formula]) -> Vec<(LenModelVar, LenModelVar)> {
    let mut total: FxHashMap<String, usize> = FxHashMap::default();
    let mut paired: FxHashMap<String, usize> = FxHashMap::default();
    let mut pairs: Vec<(LenModelVar, LenModelVar)> = Vec::new();
    for post in posts {
        post.visit(&mut |f| match f {
            Formula::Var(n, _) => {
                if let Some(v) = parse_len_model_var(n) {
                    *total.entry(v.name).or_default() += 1;
                }
            }
            Formula::Eq(l, r) => {
                if let (Formula::Var(a, _), Formula::Var(b, _)) = (&**l, &**r)
                    && let (Some(va), Some(vb)) = (parse_len_model_var(a), parse_len_model_var(b))
                    && va.name != vb.name
                {
                    *paired.entry(va.name.clone()).or_default() += 1;
                    *paired.entry(vb.name.clone()).or_default() += 1;
                    let seen = pairs.iter().any(|(x, y)| {
                        (x.name == va.name && y.name == vb.name)
                            || (x.name == vb.name && y.name == va.name)
                    });
                    if !seen {
                        pairs.push((va, vb));
                    }
                }
            }
            _ => {}
        });
    }
    if lenwitness_debug() {
        let who = lenwitness_dbg_fn();
        for (a, b) in &pairs {
            let cov_a = total.get(&a.name).copied().unwrap_or(0);
            let par_a = paired.get(&a.name).copied().unwrap_or(0);
            let cov_b = total.get(&b.name).copied().unwrap_or(0);
            let par_b = paired.get(&b.name).copied().unwrap_or(0);
            let ok = cov_a == par_a && cov_b == par_b;
            eprintln!(
                "LENWITNESS: [{who}] coverage: pair ({} path={:?} / {} path={:?}) totals(a occ={cov_a} paired={par_a}, b occ={cov_b} paired={par_b}) covered={ok}",
                a.name, a.path, b.name, b.path
            );
        }
        if pairs.is_empty() {
            eprintln!(
                "LENWITNESS: [{who}] coverage: NO len/len Eq pairs extracted from postconditions (all parseable len vars total={:?})",
                total.keys().collect::<Vec<_>>()
            );
        }
    }
    pairs.retain(|(a, b)| {
        total.get(&a.name) == paired.get(&a.name) && total.get(&b.name) == paired.get(&b.name)
    });
    pairs
}

/// The single-field payload type (`Ok`/`Some`) of a std `Result`/`Option`
/// return, from the lowered return-type VariantDefs (same std-tag discipline
/// as `enum_return_grounded_model_vars`). `None` refuses the whole lane.
pub(super) fn return_payload_ty(func: &VerifiableFunction) -> Option<&Ty> {
    let Some(Ty::Adt { name, variants, .. }) = crate::local_ty_ref(func, 0) else {
        return None;
    };
    let (payload_name, payload_tag) = if is_std_option_name(name) {
        ("Some", 1)
    } else if is_std_result_name(name) {
        ("Ok", 0)
    } else {
        return None;
    };
    let v = variants.iter().find(|v| v.name == payload_name && v.discriminant == payload_tag)?;
    if v.fields.len() != 1 {
        return None;
    }
    Some(&v.fields[0].1)
}

/// True iff the payload component at positional `path` — walked through plain
/// STRUCT (`variants.is_empty()`) and tuple types only — is an owned `Vec`
/// container, so a `len` witness on it has the std `Vec::len` semantics. Any
/// enum/opaque hop fails closed (positional indices under a variant are not
/// the field path the contract lowering minted).
pub(super) fn component_ty_is_owned_vec(func: &VerifiableFunction, path: &[usize]) -> bool {
    let Some(mut ty) = return_payload_ty(func) else {
        return false;
    };
    for &i in path {
        ty = match ty {
            Ty::Tuple(elems) => match elems.get(i) {
                Some(t) => t,
                None => return false,
            },
            Ty::Adt { fields, variants, .. } if variants.is_empty() => match fields.get(i) {
                Some((_, t)) => t,
                None => return false,
            },
            _ => return false,
        };
    }
    matches!(ty, Ty::Adt { name, .. } if is_owned_slice_container_name(name))
}

/// The places that denote the payload component `src.<path>`, unfolded through
/// the source's single-def positional aggregate constructions AND whole-value
/// aliases: `src.<i>.<j>` itself, then (when `src = Aggregate(.., ops)`
/// uniquely) `ops[i].<j>`, down to the leaf local; a whole-local
/// `src = move/copy other` hop keeps the SAME remaining path (`other.<i>.<j>`
/// denotes the identical value under another name — this is the ny
/// extract-then-guard wrapper shape, whose `_0 = Ok(move t)` operand is
/// `t = move c` while the guard's `Vec::len` calls borrow `c.<path>`). A
/// candidate is admitted ONLY while every root on the unfold — including every
/// alias hop's source — is `place_source_is_stable` (single construction, no
/// projected write, no `&mut`/raw-mut anywhere) — so a length observed on ANY
/// candidate equals the returned component's length (no mutation can intervene
/// between the witness and the return). An unstable/unresolvable hop stops
/// the unfold (keeping the shallower, still-valid candidates); an unstable
/// `src` yields NO candidates at all. Fuel-bounded: alias hops do not consume
/// a path index, so the walk needs an explicit bound (which also breaks a
/// pathological `_a = move _b; _b = move _a` single-def cycle).
pub(super) fn component_candidate_places(func: &VerifiableFunction, src: usize, path: &[usize]) -> Vec<Place> {
    const FUEL: usize = 16;
    let mut out = Vec::new();
    let mut local = src;
    let mut idx = 0usize;
    // Debug-only: WHY the descent stopped (never read unless `lenwitness_debug`).
    let mut stop_reason = "fuel exhausted (>16 hops)";
    for _ in 0..FUEL {
        if !crate::place_source_is_stable(func, local) {
            stop_reason = "root _local not place_source_is_stable (multi-def / projected write / &mut / raw-mut)";
            break;
        }
        out.push(Place {
            local,
            projections: path[idx..].iter().map(|&i| trust_types::Projection::Field(i)).collect(),
        });
        match crate::unique_whole_local_def(func, local) {
            // Positional aggregate: descend into the component's source operand.
            // Only while path components remain — at the leaf (`idx ==
            // path.len()`) there is no field left to index (and `path[idx]`
            // would be an out-of-bounds read).
            Some(Rvalue::Aggregate(kind, ops))
                if idx < path.len()
                    && matches!(
                        kind,
                        AggregateKind::Tuple | AggregateKind::Adt { variant: 0, .. }
                    ) =>
            {
                let Some(Operand::Copy(p) | Operand::Move(p)) = ops.get(path[idx]) else {
                    stop_reason = "aggregate operand at path index is const/symbolic/missing";
                    break;
                };
                if !p.projections.is_empty() {
                    stop_reason = "aggregate operand carries a projection (not a whole-local move)";
                    break;
                }
                local = p.local;
                idx += 1;
            }
            // Whole-value alias: the same value under another name; the loop
            // head re-checks `place_source_is_stable` on the new root before
            // admitting any candidate through it. Followed at ANY idx, INCLUDING
            // the leaf (`idx == path.len()`): a FLAT top-level field pair whose
            // rebuilt-aggregate operand is a fresh move-temp of the guard
            // receiver (`agg.field_i = move _t`, `_t = move _v`, while the guard
            // borrows `_v`) must resolve THROUGH that terminal move to `_v` —
            // exactly as a NESTED pair already follows the identical whole-value
            // move mid-path. Without this, the flat `.2`/`.3` pair stopped at
            // `_t` and never reached the guard receiver `_v`, leaving it
            // ungrounded while the nested `.4.0`/`.4.1` pair grounded (the
            // `sbar::SimplexSupportLp::certify_upper` destructure-rebuild
            // asymmetry). FUEL still bounds the walk (and a `_a=move _b;
            // _b=move _a` single-def alias cycle).
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) if p.projections.is_empty() => {
                local = p.local;
            }
            _ => {
                stop_reason =
                    "def is not a positional aggregate or whole-local move alias (leaf reached, or Call-dest / projected / non-variant-0)";
                break;
            }
        }
    }
    if lenwitness_debug() {
        let places: Vec<String> = out
            .iter()
            .map(|pl| {
                let proj: String = pl
                    .projections
                    .iter()
                    .map(|p| match p {
                        trust_types::Projection::Field(i) => format!(".{i}"),
                        _ => ".<proj>".to_string(),
                    })
                    .collect();
                format!("_{}{proj}", pl.local)
            })
            .collect();
        eprintln!(
            "LENWITNESS: [{}] candidates: src=_{src} path={path:?} -> {} place(s) {places:?} (stop: {stop_reason})",
            func.def_path,
            out.len()
        );
    }
    out
}

/// The LEAF local the payload component `src.<path>` was constructed from,
/// through single-def positional aggregates whose holders are all
/// `place_source_is_stable` (a post-construction in-place mutation of a holder
/// would divorce the leaf's length history from the returned component).
/// `None` fails the construction lane closed.
pub(super) fn component_source_leaf(func: &VerifiableFunction, src: usize, path: &[usize]) -> Option<usize> {
    let mut local = src;
    for &i in path {
        if !crate::place_source_is_stable(func, local) {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP at _{local} not place_source_is_stable -> None"
            );
            return None;
        }
        let Some(Rvalue::Aggregate(kind, ops)) = crate::unique_whole_local_def(func, local) else {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP _{local} has no unique-whole-def aggregate (alias/Call-dest/multi-def) -> None"
            );
            return None;
        };
        if !matches!(kind, AggregateKind::Tuple | AggregateKind::Adt { variant: 0, .. }) {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP _{local} aggregate is not Tuple/variant-0 Adt -> None"
            );
            return None;
        }
        let Some(Operand::Copy(p) | Operand::Move(p)) = ops.get(i) else {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP _{local} field {i} operand const/missing -> None"
            );
            return None;
        };
        if !p.projections.is_empty() {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP _{local} field {i} operand has projection -> None"
            );
            return None;
        }
        local = p.local;
    }
    lenwitness_dbg!(
        &func.def_path,
        "source-leaf: src=_{src} path={path:?} -> leaf _{local}"
    );
    Some(local)
}

/// A dominating length-EQUALITY guard over the two components: a `SwitchInt`
/// on `Eq/Ne(len_a, len_b)` — each side the unique, stable dest of a `Vec::len`
/// call whose receiver borrows one of the component's candidate places — whose
/// EQUALITY edge dominates the aggregate block while the inequality edge
/// cannot reach it (the `push_guarded_bound` structural-dominance discipline).
/// Returns the two len-call dest locals `(len_a, len_b)` in pair order.
pub(super) fn dominating_len_equality_guard(
    func: &VerifiableFunction,
    agg_block: usize,
    cand_a: &[Place],
    cand_b: &[Place],
) -> Option<(usize, usize)> {
    const FUEL: u32 = 8;
    // The unique def of `l` is an INHERENT `Vec::len` call (`std::vec::Vec::<T>::len`
    // — no `as`-qualified trait path, which a user `len` impl over a `&Vec`
    // receiver would carry), so the dest genuinely denotes the container length.
    // `operand_is_len_of_place` alone admits ANY `len`-tailed callee; combined
    // with the component-type gate this pins the std semantics.
    let inherent_vec_len_dest = |l: usize| -> bool {
        func.body.blocks.iter().any(|b| {
            matches!(&b.terminator,
                Terminator::Call { func: callee, dest, .. }
                    if dest.local == l
                        && dest.projections.is_empty()
                        && method_tail(callee) == "len"
                        && callee.contains("Vec")
                        && !callee.contains(" as "))
        })
    };
    let len_local_for = |op: &Operand, cands: &[Place]| -> Option<usize> {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if !p.projections.is_empty()
            || !crate::place_source_is_stable(func, p.local)
            || !inherent_vec_len_dest(p.local)
        {
            return None;
        }
        cands.iter().any(|c| operand_is_len_of_place(func, op, c)).then_some(p.local)
    };
    for gblock in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &gblock.terminator else {
            continue;
        };
        let g = gblock.id.0;
        // A switch AFTER the construction (same block) conditions nothing about
        // the already-built value — the aggregate block must be strictly under
        // the equality edge.
        if g == agg_block {
            continue;
        }
        let Some(c) = operand_root_local(func, discr, FUEL) else { continue };
        let Some(Rvalue::BinaryOp(cmp, opl, opr)) = crate::unique_whole_local_def(func, c) else {
            continue;
        };
        if !matches!(cmp, BinOp::Eq | BinOp::Ne) {
            continue;
        }
        let sides = if let (Some(la), Some(lb)) =
            (len_local_for(opl, cand_a), len_local_for(opr, cand_b))
        {
            Some((la, lb))
        } else if let (Some(la), Some(lb)) = (len_local_for(opr, cand_a), len_local_for(opl, cand_b))
        {
            Some((la, lb))
        } else {
            None
        };
        let Some((la, lb)) = sides else { continue };
        let Some((true_t, false_t)) = bool_switch_branch_targets(targets, *otherwise) else {
            lenwitness_dbg!(
                &func.def_path,
                "guard: bb{g} len-eq compare(_{la}/_{lb}) but SwitchInt targets not boolean -> skip"
            );
            continue;
        };
        let (good, bad) =
            if matches!(cmp, BinOp::Eq) { (true_t, false_t) } else { (false_t, true_t) };
        // The guard dominates the aggregate block (every path to it passes g)…
        if reachable_avoiding(func, 0, &one_block_set(g)).contains(&agg_block) {
            lenwitness_dbg!(
                &func.def_path,
                "guard: bb{g} len-eq compare(_{la}/_{lb}) does NOT dominate agg bb{agg_block} (agg reachable from entry avoiding bb{g}) -> skip"
            );
            continue;
        }
        // …the INEQUALITY edge cannot reach it, and the equality edge can.
        let avoid_g = one_block_set(g);
        if reachable_avoiding(func, bad.0, &avoid_g).contains(&agg_block) {
            lenwitness_dbg!(
                &func.def_path,
                "guard: bb{g} INEQUALITY edge bb{} reaches agg bb{agg_block} (not a fail-closed guard) -> skip",
                bad.0
            );
            continue;
        }
        if !reachable_avoiding(func, good.0, &avoid_g).contains(&agg_block) {
            lenwitness_dbg!(
                &func.def_path,
                "guard: bb{g} EQUALITY edge bb{} cannot reach agg bb{agg_block} (out of window) -> skip",
                good.0
            );
            continue;
        }
        lenwitness_dbg!(
            &func.def_path,
            "guard: bb{g} DOMINATING len-eq guard MATCHED (len dests _{la}/_{lb}, agg bb{agg_block})"
        );
        return Some((la, lb));
    }
    lenwitness_dbg!(
        &func.def_path,
        "guard: NO dominating len-equality guard over agg bb{agg_block} (cand_a={}, cand_b={})",
        cand_a.len(),
        cand_b.len()
    );
    None
}

/// The push-only equal-length leaf discipline — EXACTLY the push-guard lane's
/// gate (see `build_push_guard_elem_len_map` step (A)): an owned `Vec`,
/// created EMPTY, single whole-local def, never written through a projection,
/// every `&mut`/raw borrow feeding only `Vec::push`.
pub(super) fn leaf_push_disciplined(func: &VerifiableFunction, leaf: usize) -> bool {
    matches!(crate::local_ty_ref(func, leaf), Some(Ty::Adt { name, .. })
        if is_owned_slice_container_name(name))
        && guards::whole_local_def_count(func, leaf) == 1
        && vec_created_empty(func, leaf)
        && !local_has_projected_write(func, leaf)
        && vec_mut_borrows_only_feed_push(func, leaf)
}

/// The blocks whose terminator is a `Vec::push` whose receiver conduit is the
/// unique whole-local `&mut leaf` borrow. Under `vec_mut_borrows_only_feed_push`
/// every push-mutation of `leaf` has exactly this shape (projected/reused
/// conduits already failed the discipline), so this enumeration is COMPLETE —
/// a missed push cannot silently skew the pairing count.
pub(super) fn leaf_push_blocks(func: &VerifiableFunction, leaf: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, .. } = &block.terminator else { continue };
        if method_tail(callee) != "push" || !callee.contains("Vec") {
            continue;
        }
        let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else { continue };
        if recv.projections.is_empty()
            && matches!(ref_target_of_local(func, recv.local),
                Some((p, _)) if p.local == leaf && p.projections.is_empty())
        {
            out.push(block.id.0);
        }
    }
    out
}

/// Normal-flow predecessor COUNTS per block (`v2_terminator_targets` view —
/// unwind edges excluded, matching the reachability helpers: a panic path
/// never reaches `Return`, so postcondition facts are vacuous there).
pub(super) fn block_pred_counts(func: &VerifiableFunction) -> FxHashMap<usize, usize> {
    let mut preds: FxHashMap<usize, usize> = FxHashMap::default();
    for b in &func.body.blocks {
        for t in v2_terminator_targets(&b.terminator) {
            *preds.entry(t.0).or_default() += 1;
        }
    }
    preds
}

/// From the push at `from_push`, walk the mandatory single-successor /
/// single-predecessor block chain to the mate push: every chain block executes
/// iff `from_push` did (sole in-edge) and control cannot leave the chain (sole
/// out-edge), so the mate's push count equals `from_push`'s on EVERY execution.
/// Interior blocks must never TOUCH either leaf (`block_mentions_local`): a
/// move/copy of a leaf between the paired pushes would snapshot the lengths at
/// an interior point where they are UNEQUAL. Any other push (either leaf)
/// before the mate, a branch, or fuel exhaustion fails the pair closed.
pub(super) fn push_chain_mate(
    func: &VerifiableFunction,
    preds: &FxHashMap<usize, usize>,
    from_push: usize,
    to_pushes: &FxHashSet<usize>,
    all_pushes: &FxHashSet<usize>,
    leaf_a: usize,
    leaf_b: usize,
) -> Option<usize> {
    const FUEL: usize = 8;
    let Some(Terminator::Call { target: Some(t), .. }) =
        func.body.blocks.get(from_push).map(|b| &b.terminator)
    else {
        return None;
    };
    let mut cur = t.0;
    for _ in 0..FUEL {
        if preds.get(&cur).copied().unwrap_or(0) != 1 {
            return None;
        }
        if to_pushes.contains(&cur) {
            return Some(cur);
        }
        if all_pushes.contains(&cur) {
            return None;
        }
        let b = func.body.blocks.get(cur)?;
        if block_mentions_local(b, leaf_a) || block_mentions_local(b, leaf_b) {
            return None;
        }
        let succs = v2_terminator_targets(&b.terminator);
        if succs.len() != 1 {
            return None;
        }
        cur = succs[0].0;
    }
    None
}

/// True iff `leaf_a` and `leaf_b` have provably EQUAL lengths at every block
/// outside a push-pair interior: both satisfy the push-only empty-start
/// discipline and their pushes are 1:1 chain-coupled (either orientation).
/// Zero pushes on both sides is the trivially-equal `0 == 0` case.
pub(super) fn paired_push_equal_lengths(func: &VerifiableFunction, leaf_a: usize, leaf_b: usize) -> bool {
    if leaf_a == leaf_b {
        return false;
    }
    if !leaf_push_disciplined(func, leaf_a) || !leaf_push_disciplined(func, leaf_b) {
        return false;
    }
    let pa = leaf_push_blocks(func, leaf_a);
    let pb = leaf_push_blocks(func, leaf_b);
    if pa.len() != pb.len() {
        return false;
    }
    if pa.is_empty() {
        return true;
    }
    let preds = block_pred_counts(func);
    let all: FxHashSet<usize> = pa.iter().chain(pb.iter()).copied().collect();
    let couple = |from: &[usize], to: &[usize]| -> bool {
        let to_set: FxHashSet<usize> = to.iter().copied().collect();
        let mut consumed: FxHashSet<usize> = FxHashSet::default();
        for &p in from {
            match push_chain_mate(func, &preds, p, &to_set, &all, leaf_a, leaf_b) {
                Some(mate) if consumed.insert(mate) => {}
                _ => return false,
            }
        }
        consumed.len() == to.len()
    };
    couple(&pa, &pb) || couple(&pb, &pa)
}

/// The len-witness pins for ONE return path (the `(vc_block, block)` pair the
/// discr pin threads) and ONE covered pair. `Some(pins)` = the path is soundly
/// handled (EMPTY-variant paths need no pins — the terms have no denotation
/// there and stay free, which only adds refutability); `None` = the path
/// cannot be grounded, failing the whole pair closed at the gate. Shared by
/// the GATE and the PIN LOOP so they cannot disagree (a credited-but-unpinned
/// term would be a free var in a refutable VC — the false-FAIL hazard).
pub(super) fn len_witness_path_pins(
    func: &VerifiableFunction,
    vc_block: &trust_types::BasicBlock,
    block: &trust_types::BasicBlock,
    pair: &(LenModelVar, LenModelVar),
) -> Option<Vec<Formula>> {
    let dp = &func.def_path;
    let bb = (vc_block.id.0, block.id.0);
    let names = (&pair.0.name, &pair.1.name);
    let Some((kind, variant, ops, agg_block)) =
        resolve_enum_return_aggregate_with_block(func, vc_block, block)
    else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): resolve_enum_return_aggregate=None -> pair FAILS (path _0 unresolved)",
            bb.0, bb.1, names.0, names.1
        );
        return None;
    };
    if variant != std_enum_payload_variant(kind) {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): EMPTY variant (variant={variant} {kind:?}) -> Some(no pins; terms free is sound here)",
            bb.0, bb.1, names.0, names.1
        );
        return Some(Vec::new());
    }
    if ops.len() != 1 {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): payload aggregate ops.len()={} != 1 -> None",
            bb.0, bb.1, names.0, names.1, ops.len()
        );
        return None;
    }
    let (Operand::Copy(sp) | Operand::Move(sp)) = &ops[0] else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): payload operand is const/symbolic (not move/copy place) -> None",
            bb.0, bb.1, names.0, names.1
        );
        return None;
    };
    if !sp.projections.is_empty() {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): payload operand _{}.<proj> carries a projection -> None",
            bb.0, bb.1, names.0, names.1, sp.local
        );
        return None;
    }
    let src = sp.local;
    // Both components must be owned-Vec-typed per the DECLARED payload type,
    // so the witness `len` has the std container semantics.
    if !component_ty_is_owned_vec(func, &pair.0.path) || !component_ty_is_owned_vec(func, &pair.1.path)
    {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): component type not owned Vec (a_ok={}, b_ok={}) -> None",
            bb.0, bb.1, names.0, names.1,
            component_ty_is_owned_vec(func, &pair.0.path),
            component_ty_is_owned_vec(func, &pair.1.path)
        );
        return None;
    }
    let a_var = Formula::var_owned(pair.0.name.clone(), Sort::Int);
    let b_var = Formula::var_owned(pair.1.name.clone(), Sort::Int);
    let eq = Formula::Eq(Box::new(a_var.clone()), Box::new(b_var.clone()));
    // Lane (1): dominating length-equality guard, with individual witness pins.
    let cand_a = component_candidate_places(func, src, &pair.0.path);
    let cand_b = component_candidate_places(func, src, &pair.1.path);
    let guard = if !cand_a.is_empty() && !cand_b.is_empty() {
        dominating_len_equality_guard(func, agg_block.0, &cand_a, &cand_b)
    } else {
        None
    };
    lenwitness_dbg!(
        dp,
        "path-pins bb{}->bb{} pair({}/{}): src=_{src} agg_block=bb{} cand_a={} cand_b={} guard={guard:?}",
        bb.0, bb.1, names.0, names.1, agg_block.0, cand_a.len(), cand_b.len()
    );
    if let Some((la, lb)) = guard {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): GUARD LANE grounded (len dests _{la}/_{lb}) -> Some(guard pins)",
            bb.0, bb.1, names.0, names.1
        );
        return Some(vec![
            eq,
            Formula::Eq(
                Box::new(a_var),
                Box::new(operand_to_formula(func, &Operand::Copy(Place::local(la)))),
            ),
            Formula::Eq(
                Box::new(b_var),
                Box::new(operand_to_formula(func, &Operand::Copy(Place::local(lb)))),
            ),
        ]);
    }
    // Lane (2): equal-by-construction chain-coupled push leaves.
    let Some(leaf_a) = component_source_leaf(func, src, &pair.0.path) else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): no guard AND component_source_leaf(a)=None -> pair FAILS",
            bb.0, bb.1, names.0, names.1
        );
        return None;
    };
    let Some(leaf_b) = component_source_leaf(func, src, &pair.1.path) else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): no guard AND component_source_leaf(b)=None -> pair FAILS",
            bb.0, bb.1, names.0, names.1
        );
        return None;
    };
    if paired_push_equal_lengths(func, leaf_a, leaf_b) {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): PUSH LANE grounded (leaves _{leaf_a}/_{leaf_b}) -> Some(eq pin)",
            bb.0, bb.1, names.0, names.1
        );
        return Some(vec![eq]);
    }
    lenwitness_dbg!(
        dp,
        "path-pins bb{}->bb{} pair({}/{}): neither guard nor paired-push (leaves _{leaf_a}/_{leaf_b}) -> pair FAILS",
        bb.0, bb.1, names.0, names.1
    );
    None
}

/// The GATE for the len-witness lane: the covered pairs (see
/// `len_pair_coverage`) for which EVERY Return path — the same
/// `Return`-block/predecessor enumeration the pin loop and the discr gate use
/// — yields `Some` pins. Credited names are removed from the per-post
/// ungrounded set so the postcondition survives into the body-aware refutable
/// lane, where `len_witness_path_pins` (same resolver) grounds them per path.
pub(super) fn len_witness_credited_pairs(
    func: &VerifiableFunction,
    posts: &[(Formula, String, SourceSpan, Option<usize>)],
) -> Vec<(LenModelVar, LenModelVar)> {
    lenwitness_dbg_set_fn(&func.def_path);
    let refs: Vec<&Formula> = posts.iter().map(|(f, _, _, _)| f).collect();
    let mut pairs = len_pair_coverage(&refs);
    if pairs.is_empty() {
        lenwitness_dbg!(
            &func.def_path,
            "gate: NO covered len pairs -> len_groundable EMPTY (all _len postconditions stay SpecModelUngrounded)"
        );
        return pairs;
    }
    let before: Vec<(String, String)> =
        pairs.iter().map(|(a, b)| (a.name.clone(), b.name.clone())).collect();
    pairs.retain(|pair| {
        for block in &func.body.blocks {
            if !matches!(block.terminator, Terminator::Return) {
                continue;
            }
            let predecessors: Vec<&trust_types::BasicBlock> = func
                .body
                .blocks
                .iter()
                .filter(|pred| v2_terminator_targets(&pred.terminator).contains(&block.id))
                .collect();
            let vc_blocks: Vec<&trust_types::BasicBlock> =
                if predecessors.is_empty() { vec![block] } else { predecessors };
            for vc_block in vc_blocks {
                if len_witness_path_pins(func, vc_block, block, pair).is_none() {
                    return false;
                }
            }
        }
        true
    });
    if lenwitness_debug() {
        let dropped: Vec<&(String, String)> = before
            .iter()
            .filter(|(a, b)| !pairs.iter().any(|(x, y)| &x.name == a && &y.name == b))
            .collect();
        eprintln!(
            "LENWITNESS: [{}] gate: covered={} CREDITED={} dropped(a return path failed path-pins)={dropped:?}",
            func.def_path,
            before.len(),
            pairs.len()
        );
    }
    pairs
}

/// Parse `_0_value.__trust_ok_<i>` (any `#version` token stripped).
pub(super) fn parse_ok_pair_model_var(name: &str) -> Option<OkPairModelVar> {
    let base = name.split('#').next().unwrap_or(name);
    let index = base.strip_prefix("_0_value.__trust_ok_")?.parse::<usize>().ok()?;
    Some(OkPairModelVar { name: base.to_string(), index })
}

/// Parse the RETURN-payload sign term `_0_value_sign` (any `#version` token
/// stripped). Other `{base}_sign` names (params, deeper projections) stay
/// fail-closed: only the returned payload's own construction is grounded.
pub(super) fn parse_sign_model_var(name: &str) -> Option<String> {
    let base = name.split('#').next().unwrap_or(name);
    (base == "_0_value_sign").then(|| base.to_string())
}

/// The two sides of an ordering ATOM (`Lt/Le/Gt/Ge/Eq`) — the only formula
/// shapes the F4 coverage gates admit an occurrence inside. The parser lowers
/// `!=` to `Not(Eq(..))`, so both polarities of every comparison reduce to
/// these five.
pub(super) fn ordering_atom_sides(f: &Formula) -> Option<(&Formula, &Formula)> {
    match f {
        Formula::Lt(l, r)
        | Formula::Le(l, r)
        | Formula::Gt(l, r)
        | Formula::Ge(l, r)
        | Formula::Eq(l, r) => Some((l, r)),
        _ => None,
    }
}

/// The COVERED `__trust_ok` pairs of the declared postconditions: pairs of
/// distinct parseable pair vars appearing together in ordering atoms, where
/// NEITHER var occurs anywhere else (see the section banner — an occurrence
/// outside a pair ordering atom would leave the term under-constrained by
/// the single pinned fact, flipping an honest Unknown into a refutable
/// FAILED, and could smuggle in a discreteness-bearing atom).
pub(super) fn ordering_pair_coverage(posts: &[&Formula]) -> Vec<(OkPairModelVar, OkPairModelVar)> {
    let mut total: FxHashMap<String, usize> = FxHashMap::default();
    let mut paired: FxHashMap<String, usize> = FxHashMap::default();
    let mut pairs: Vec<(OkPairModelVar, OkPairModelVar)> = Vec::new();
    for post in posts {
        post.visit(&mut |f| {
            if let Formula::Var(n, _) = f
                && let Some(v) = parse_ok_pair_model_var(n)
            {
                *total.entry(v.name).or_default() += 1;
            }
            if let Some((l, r)) = ordering_atom_sides(f)
                && let (Formula::Var(a, _), Formula::Var(b, _)) = (l, r)
                && let (Some(va), Some(vb)) = (parse_ok_pair_model_var(a), parse_ok_pair_model_var(b))
                && va.index != vb.index
            {
                *paired.entry(va.name.clone()).or_default() += 1;
                *paired.entry(vb.name.clone()).or_default() += 1;
                let seen = pairs.iter().any(|(x, y)| {
                    (x.name == va.name && y.name == vb.name)
                        || (x.name == vb.name && y.name == va.name)
                });
                if !seen {
                    pairs.push((va, vb));
                }
            }
        });
    }
    pairs.retain(|(a, b)| {
        total.get(&a.name) == paired.get(&a.name) && total.get(&b.name) == paired.get(&b.name)
    });
    pairs
}

/// True iff `_0_value_sign` occurs in the declared postconditions and EVERY
/// occurrence sits inside an ordering atom against the LITERAL 0 (either
/// side). Any other position — a nonzero constant (which would need Int
/// discreteness), another variable, arithmetic — keeps the term uncredited.
pub(super) fn sign_var_covered(posts: &[&Formula]) -> bool {
    let mut total = 0usize;
    let mut covered = 0usize;
    for post in posts {
        post.visit(&mut |f| {
            if let Formula::Var(n, _) = f
                && parse_sign_model_var(n).is_some()
            {
                total += 1;
            }
            if let Some((l, r)) = ordering_atom_sides(f) {
                let hit = matches!(
                    (l, r),
                    (Formula::Var(n, _), Formula::Int(0)) if parse_sign_model_var(n).is_some()
                ) || matches!(
                    (l, r),
                    (Formula::Int(0), Formula::Var(n, _)) if parse_sign_model_var(n).is_some()
                );
                if hit {
                    covered += 1;
                }
            }
        });
    }
    total > 0 && total == covered
}

/// The ADT NAME of the payload component at positional `path` — walked
/// through plain STRUCT (`variants.is_empty()`) and tuple types only, exactly
/// like `component_ty_is_owned_vec`. The name keys the witness-callee
/// allowlist (the component type's OWN `PartialOrd` impl / inherent sign
/// predicates — the same functions the contract's runtime check denotes).
/// `Ref`/slice/other component types fail closed: a by-ref component's
/// REFERENT mutability is not closed by `place_source_is_stable` on the
/// place roots.
pub(super) fn payload_component_adt_name(func: &VerifiableFunction, path: &[usize]) -> Option<String> {
    let mut ty = return_payload_ty(func)?;
    for &i in path {
        ty = match ty {
            Ty::Tuple(elems) => elems.get(i)?,
            Ty::Adt { fields, variants, .. } if variants.is_empty() => &fields.get(i)?.1,
            _ => return None,
        };
    }
    match ty {
        Ty::Adt { name, .. } => Some(name.clone()),
        _ => None,
    }
}

/// Classify an allowlisted PAIR witness callee: the component type's own
/// `PartialOrd` operator method — `<{ty_name} as std::cmp::PartialOrd>::{m}`
/// (or `core::cmp::`) — returning the outcome set its TRUE result admits for
/// the argument pair IN CALL ORDER. Exact-prefix matching against the full
/// rendered self type prevents a partial type-name match.
pub(super) fn partial_ord_witness_facts(callee: &str, ty_name: &str) -> Option<OrderFacts> {
    let rest = callee.strip_prefix('<')?.strip_prefix(ty_name)?;
    let method = rest
        .strip_prefix(" as std::cmp::PartialOrd>::")
        .or_else(|| rest.strip_prefix(" as core::cmp::PartialOrd>::"))?;
    match method {
        "lt" => Some(OrderFacts::LT),
        "le" => Some(OrderFacts::LE),
        "gt" => Some(OrderFacts::GT),
        "ge" => Some(OrderFacts::GE),
        _ => None,
    }
}

/// Classify an allowlisted SIGN witness callee: the payload type's own
/// INHERENT sign predicate `{ty_name}::{is_positive,is_negative,is_zero}`,
/// returning the outcome set its TRUE result admits for `(payload, 0)`.
/// These are the exact predicates the spec parser's `{base}_sign` convention
/// denotes (all three share one sign term — the parser's own trichotomy
/// reading, see `spec_parse`).
pub(super) fn sign_witness_facts(callee: &str, ty_name: &str) -> Option<OrderFacts> {
    let method = callee.strip_prefix(ty_name)?.strip_prefix("::")?;
    match method {
        "is_positive" => Some(OrderFacts::GT),
        "is_negative" => Some(OrderFacts::LT),
        "is_zero" => Some(OrderFacts::EQ),
        _ => None,
    }
}

/// True iff witness-call operand `op` denotes one of the component's
/// candidate places: the place itself, a single-def SHARED borrow of it, or a
/// chain of projection-free stable `Use` hops bottoming out in either.
/// Every hop local must be `place_source_is_stable` (a call-dest or projected
/// rewrite of a hop would divorce the operand's value from the candidate);
/// the candidates' own roots were stability-checked by
/// `component_candidate_places`, so a match means the compared value IS the
/// returned component's value.
pub(super) fn f4_operand_denotes_candidate(
    func: &VerifiableFunction,
    op: &Operand,
    cands: &[Place],
    fuel: u32,
) -> bool {
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return false;
    };
    if cands.contains(p) {
        return true;
    }
    if fuel == 0 || !p.projections.is_empty() || !crate::place_source_is_stable(func, p.local) {
        return false;
    }
    match crate::unique_whole_local_def(func, p.local) {
        Some(Rvalue::Ref { mutable: false, place }) => cands.contains(place),
        Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
            f4_operand_denotes_candidate(func, &Operand::Copy(q.clone()), cands, fuel - 1)
        }
        _ => false,
    }
}

/// The outcome set a single allowlisted witness CALL's true result admits for
/// `target`, or `None` (fail-closed: wrong callee, wrong arity, operands not
/// resolving to the candidate places). A pair call matching in REVERSED
/// order contributes the mirrored set; matching in BOTH orders (aliased
/// components) is admitted only when the set is symmetric.
pub(super) fn f4_call_witness_facts(
    func: &VerifiableFunction,
    callee: &str,
    args: &[Operand],
    target: &OrdWitnessTarget<'_>,
) -> Option<OrderFacts> {
    const FUEL: u32 = 4;
    match target {
        OrdWitnessTarget::Pair { ty_name, cand_a, cand_b } => {
            let base = partial_ord_witness_facts(callee, ty_name)?;
            let [a0, a1] = args else {
                return None;
            };
            let fwd = f4_operand_denotes_candidate(func, a0, cand_a, FUEL)
                && f4_operand_denotes_candidate(func, a1, cand_b, FUEL);
            let rev = f4_operand_denotes_candidate(func, a0, cand_b, FUEL)
                && f4_operand_denotes_candidate(func, a1, cand_a, FUEL);
            match (fwd, rev) {
                (true, false) => Some(base),
                (false, true) => Some(base.mirrored()),
                (true, true) if base == base.mirrored() => Some(base),
                _ => None,
            }
        }
        OrdWitnessTarget::Sign { ty_name, cands } => {
            let base = sign_witness_facts(callee, ty_name)?;
            let [a0] = args else {
                return None;
            };
            f4_operand_denotes_candidate(func, a0, cands, FUEL).then_some(base)
        }
    }
}

/// EVERY whole-local def of `local` — statement assigns AND call dests.
/// `None` (fail-closed) on any projected write, `SetDiscriminant`/`Deinit`,
/// any `&mut`/raw-mut borrow (an invisible reseat channel), or when there is
/// no def at all (a parameter — its value is no witness).
pub(super) fn f4_whole_local_defs<'a>(
    func: &'a VerifiableFunction,
    local: usize,
) -> Option<Vec<F4LocalDef<'a>>> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == local {
                        if !place.projections.is_empty() {
                            return None;
                        }
                        out.push(F4LocalDef::Rv(rvalue));
                    }
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(true, borrowed) = rvalue
                        && borrowed.local == local
                    {
                        return None;
                    }
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place }
                    if place.local == local =>
                {
                    return None;
                }
                _ => {}
            }
        }
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
        {
            if !dest.projections.is_empty() {
                return None;
            }
            out.push(F4LocalDef::Call { callee, args });
        }
    }
    if out.is_empty() { None } else { Some(out) }
}

/// The outcome set the guard EDGE (`true_edge`) admits for `target`, joined
/// over EVERY whole-local def of `local`: per def, the witness call's true
/// set (or its complement on the false edge — complemented PER DEF, before
/// the union, so a mixed-def bool only WEAKENS), through projection-free
/// `Use` hops and polarity-flipping `Not` hops. One unrecognized def fails
/// the whole bool closed.
pub(super) fn f4_local_edge_facts(
    func: &VerifiableFunction,
    local: usize,
    target: &OrdWitnessTarget<'_>,
    true_edge: bool,
    fuel: u32,
) -> Option<OrderFacts> {
    if fuel == 0 {
        return None;
    }
    let defs = f4_whole_local_defs(func, local)?;
    let mut acc: Option<OrderFacts> = None;
    for def in defs {
        let facts = match def {
            F4LocalDef::Call { callee, args } => {
                let t = f4_call_witness_facts(func, callee, args, target)?;
                if true_edge { t } else { t.complement() }
            }
            F4LocalDef::Rv(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
                if q.projections.is_empty() =>
            {
                f4_local_edge_facts(func, q.local, target, true_edge, fuel - 1)?
            }
            F4LocalDef::Rv(Rvalue::UnaryOp(
                trust_types::UnOp::Not,
                Operand::Copy(q) | Operand::Move(q),
            )) if q.projections.is_empty() => {
                f4_local_edge_facts(func, q.local, target, !true_edge, fuel - 1)?
            }
            F4LocalDef::Rv(_) => return None,
        };
        acc = Some(match acc {
            Some(a) => a.union(facts),
            None => facts,
        });
    }
    acc
}

/// The root bool local a `SwitchInt` discriminant reads, through
/// projection-free STABLE `Use` hops only (an unstable hop — a call-dest or
/// second write — stops the walk at the hop itself, whose defs then fail the
/// witness classification closed). The multi-def witness bool itself is NOT
/// stable (several call-dest defs), so the walk stops exactly there.
pub(super) fn f4_switch_root_local(func: &VerifiableFunction, discr: &Operand, fuel: u32) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = discr else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    let mut local = p.local;
    for _ in 0..fuel {
        if crate::place_source_is_stable(func, local)
            && let Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) =
                crate::unique_whole_local_def(func, local)
            && q.projections.is_empty()
        {
            local = q.local;
        } else {
            break;
        }
    }
    Some(local)
}

/// A dominating ordering/sign witness guard for `target`: a `SwitchInt` on a
/// recognized witness bool, one of whose edges dominates the aggregate block
/// while the other cannot reach it (the `dominating_len_equality_guard`
/// structural-dominance discipline). Returns the dominating edge's joined
/// outcome set — refusing the FULL set (uninformative) and the EMPTY set
/// (a `false` pin would vacuously prove; see `OrderFacts::to_formula`).
pub(super) fn dominating_ordering_witness_guard(
    func: &VerifiableFunction,
    agg_block: usize,
    target: &OrdWitnessTarget<'_>,
) -> Option<OrderFacts> {
    const FUEL: u32 = 8;
    for gblock in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &gblock.terminator else {
            continue;
        };
        let g = gblock.id.0;
        // A switch AFTER the construction (same block) conditions nothing
        // about the already-built value.
        if g == agg_block {
            continue;
        }
        let Some(root) = f4_switch_root_local(func, discr, FUEL) else { continue };
        let Some((true_t, false_t)) = bool_switch_branch_targets(targets, *otherwise) else {
            continue;
        };
        // The guard dominates the aggregate block (every path passes g)…
        if reachable_avoiding(func, 0, &one_block_set(g)).contains(&agg_block) {
            continue;
        }
        // …and exactly ONE edge reaches it.
        let avoid_g = one_block_set(g);
        let true_reaches = reachable_avoiding(func, true_t.0, &avoid_g).contains(&agg_block);
        let false_reaches = reachable_avoiding(func, false_t.0, &avoid_g).contains(&agg_block);
        let edge_is_true = match (true_reaches, false_reaches) {
            (true, false) => true,
            (false, true) => false,
            _ => continue,
        };
        let Some(facts) = f4_local_edge_facts(func, root, target, edge_is_true, FUEL) else {
            continue;
        };
        // Full = no information; empty = contradictory edge — both refuse
        // (to_formula would also refuse, but refusing HERE lets a later,
        // informative guard still match).
        if !facts.is_informative() {
            continue;
        }
        return Some(facts);
    }
    None
}

/// The F4 pins for ONE return path (the `(vc_block, block)` pair the discr
/// pin threads) and ONE credited item. `Some(pins)` = the path is soundly
/// handled (EMPTY-variant paths need no pins — the payload terms have no
/// denotation there and stay free, which only adds refutability); `None` =
/// the path cannot be grounded, failing the item closed at the gate. Shared
/// by the GATE and the PIN LOOP so they cannot disagree (a
/// credited-but-unpinned term would be a free var in a refutable VC — the
/// false-FAIL hazard).
pub(super) fn ordering_witness_path_pins(
    func: &VerifiableFunction,
    vc_block: &trust_types::BasicBlock,
    block: &trust_types::BasicBlock,
    item: &OrdWitnessItem,
) -> Option<Vec<Formula>> {
    let (kind, variant, ops, agg_block) =
        resolve_enum_return_aggregate_with_block(func, vc_block, block)?;
    if variant != std_enum_payload_variant(kind) {
        return Some(Vec::new());
    }
    if ops.len() != 1 {
        return None;
    }
    let (Operand::Copy(sp) | Operand::Move(sp)) = &ops[0] else {
        return None;
    };
    if !sp.projections.is_empty() {
        return None;
    }
    let src = sp.local;
    match item {
        OrdWitnessItem::Pair(va, vb) => {
            // Both components must be the SAME non-ref ADT per the DECLARED
            // payload type — the callee allowlist key (`PartialOrd<Self>`
            // could not compare two different types anyway; fail closed).
            let ty_a = payload_component_adt_name(func, &[va.index])?;
            let ty_b = payload_component_adt_name(func, &[vb.index])?;
            if ty_a != ty_b {
                return None;
            }
            let cand_a = component_candidate_places(func, src, &[va.index]);
            let cand_b = component_candidate_places(func, src, &[vb.index]);
            if cand_a.is_empty() || cand_b.is_empty() {
                return None;
            }
            let target =
                OrdWitnessTarget::Pair { ty_name: &ty_a, cand_a: &cand_a, cand_b: &cand_b };
            let facts = dominating_ordering_witness_guard(func, agg_block.0, &target)?;
            let pin = facts.to_formula(
                Formula::var_owned(va.name.clone(), Sort::Int),
                Formula::var_owned(vb.name.clone(), Sort::Int),
            )?;
            Some(vec![pin])
        }
        OrdWitnessItem::Sign(name) => {
            let ty_name = payload_component_adt_name(func, &[])?;
            let cands = component_candidate_places(func, src, &[]);
            if cands.is_empty() {
                return None;
            }
            let target = OrdWitnessTarget::Sign { ty_name: &ty_name, cands: &cands };
            let facts = dominating_ordering_witness_guard(func, agg_block.0, &target)?;
            let pin = facts
                .to_formula(Formula::var_owned(name.clone(), Sort::Int), Formula::Int(0))?;
            Some(vec![pin])
        }
    }
}

/// The GATE for the F4 lane: the covered items (see `ordering_pair_coverage`
/// / `sign_var_covered`) for which EVERY Return path — the same
/// `Return`-block/predecessor enumeration the pin loop, the discr gate, and
/// the len gate use — yields `Some` pins. Credited names are removed from
/// the per-post ungrounded set so the postcondition survives into the
/// body-aware refutable lane, where `ordering_witness_path_pins` (same
/// resolver) grounds them per path.
pub(super) fn ordering_witness_credited_items(
    func: &VerifiableFunction,
    posts: &[(Formula, String, SourceSpan, Option<usize>)],
) -> Vec<OrdWitnessItem> {
    let refs: Vec<&Formula> = posts.iter().map(|(f, _, _, _)| f).collect();
    let mut items: Vec<OrdWitnessItem> =
        ordering_pair_coverage(&refs).into_iter().map(|(a, b)| OrdWitnessItem::Pair(a, b)).collect();
    if sign_var_covered(&refs) {
        items.push(OrdWitnessItem::Sign("_0_value_sign".to_string()));
    }
    if items.is_empty() {
        return items;
    }
    items.retain(|item| {
        for block in &func.body.blocks {
            if !matches!(block.terminator, Terminator::Return) {
                continue;
            }
            let predecessors: Vec<&trust_types::BasicBlock> = func
                .body
                .blocks
                .iter()
                .filter(|pred| v2_terminator_targets(&pred.terminator).contains(&block.id))
                .collect();
            let vc_blocks: Vec<&trust_types::BasicBlock> =
                if predecessors.is_empty() { vec![block] } else { predecessors };
            for vc_block in vc_blocks {
                if ordering_witness_path_pins(func, vc_block, block, item).is_none() {
                    return false;
                }
            }
        }
        true
    });
    items
}
