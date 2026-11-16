// ignore-tidy-file-dbg -- `lenwitness_dbg!` is a gated debug channel, not std dbg!; tidy's check is textual
// Return-value grounding for functions returning `Option`/`Result` and for
// paired length and ordering witnesses. An ungrounded return leaves the
// postcondition talking about a model variable nothing pins, so the credited
// pairs here are what make an `ensures` over a returned container provable.

use super::*;

/// How far [`return_producer_ancestors`] will walk. Drop elaboration splices at
/// most a handful of join blocks; the bound stops a pathological chain, and
/// exhausting it simply yields a shorter search list (today's behaviour).
const RETURN_PRODUCER_WALK_FUEL: u32 = 8;

/// Whether `block`'s STATEMENTS provably leave the return slot `_0` UNTOUCHED.
///
/// FAIL-CLOSED BY CONSTRUCTION: only statements that cannot write a place are
/// allowed through; every other statement kind — including
/// `Retag`/`Intrinsic`/`CopyNonOverlapping`/`Unsupported`, whose write sets this
/// function does not model — returns `false`. A `false` answer only stops the
/// walk early, which is today's behaviour; a wrong `true` would let a STALE `_0`
/// definition be attributed to a return path, so the asymmetry is deliberate.
///
/// Projected writes count: `_0.f = ..` mutates the return value just as `_0 = ..`
/// does, so the test is on `place.local`, never on `projections.is_empty()`.
fn statements_preserve_return_place(block: &trust_types::BasicBlock) -> bool {
    for statement in &block.stmts {
        match statement {
            Statement::Assign { place, .. }
            | Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place } => {
                if place.local == 0 {
                    return false;
                }
            }
            // Storage markers carry no value, but a marker naming local 0 means
            // the return slot's storage is changing under us — refuse.
            Statement::StorageLive(local) | Statement::StorageDead(local) => {
                if *local == 0 {
                    return false;
                }
            }
            Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            _ => return false,
        }
    }
    true
}

/// Whether `terminator` provably leaves the return slot `_0` UNTOUCHED.
///
/// ALLOW-LIST, symmetric with [`statements_preserve_return_place`]. This was a
/// two-entry DENY-LIST (`Call{dest:_0}`, `Drop{place:_0}`) under a doc that
/// promised the opposite asymmetry, and `Terminator::Opaque` walked straight
/// through the hole: `opaque_terminator(kind, targets, span)`
/// (`trust-mir-extract/src/convert.rs:1976`) has NO destination parameter, so
/// every one of its call sites DISCARDS the MIR terminator's destination place
/// while keeping the normal successor. `_0 = <indirect>()` (convert.rs:1704),
/// `_0 = <atomic>()` when the intrinsic's metadata does not parse
/// (convert.rs:1752), and an `InlineAsm` `out(reg) _0` / a coroutine `Yield`
/// (the `_ =>` arm, convert.rs:1943) all arrive here as a block whose whole
/// effect is a write to `_0` and whose model records only "some successor".
/// `Terminator::TailCall` is the same class by a different route: its
/// destination is the return place IMPLICITLY (`convert.rs:1838`,
/// `let implicit_return = Place::local(0)`), so it has no `dest` field to test.
/// Under the old deny-list both answered `true` and the walk stepped past a
/// real `_0` write to attribute an earlier, STALE definition to the return
/// path — verbatim the direction [`statements_preserve_return_place`]'s doc
/// names.
///
/// The default arm delegates to [`trust_types::Terminator::write_effect`],
/// which is WILDCARD-FREE in the crate that owns the `#[non_exhaustive]` enum:
/// a new terminator variant cannot reach `true` here by accident, because it
/// must first be classified `NoValueWrite` there, and that classification does
/// not compile until someone writes it. `Opaque` is `FailClosedOrBackstopped`
/// and `TailCall` is `Captured`, so both now refuse — which is also what
/// `path_defs.rs:297` already concluded about `Opaque` ("can run arbitrary code
/// — same conservative havoc as a Call, MINUS A DEST, WHICH OPAQUE DOES NOT
/// MODEL") from the same fact.
pub(super) fn terminator_preserves_return_place(terminator: &Terminator) -> bool {
    terminator_preserves_local(terminator, 0)
}

/// The same allow-list, resolved onto ANY local — `_0` is just the caller that
/// needed it first.
///
/// Trust: 2026-09-01 — generalized so the forwarded-call path-region check can
/// reuse ONE rule instead of spelling a second, weaker one. That check protects
/// "`discriminant(call_dest)` at the switch equals its discriminant at `Return`"
/// and used to scan for `Statement::Assign` and a `Call` dest only, so a
/// `SetDiscriminant` on `call_dest` — the statement whose entire job is to change
/// a discriminant — passed straight through the guard that exists to protect one.
/// `Deinit`, `Drop` glue and the dest-discarding `Opaque` were missed with it.
pub(super) fn terminator_preserves_local(terminator: &Terminator, local: usize) -> bool {
    match terminator {
        // The two place-BEARING writes the model spells out. Admitted exactly
        // when the place they name is not this local.
        Terminator::Call { dest, .. } => dest.local != local,
        Terminator::Drop { place, .. } => place.local != local,
        // Everything else is admitted ONLY on the owning crate's own testimony
        // that it writes no value at all.
        other => matches!(other.write_effect(), trust_types::WriteEffect::NoValueWrite),
    }
}

/// Whether `block` provably leaves the return slot `_0` UNTOUCHED — statements
/// AND terminator. See the two halves for the fail-closed argument each makes.
fn block_preserves_return_place(block: &trust_types::BasicBlock) -> bool {
    statements_preserve_return_place(block) && terminator_preserves_return_place(&block.terminator)
}

/// The `_0`-preserving ancestors of `from`, nearest first.
///
/// WHY. Drop elaboration can splice a join block between the block that actually
/// builds the returned value and the `Return`. The return path's predecessor
/// then assigns nothing, the aggregate resolvers find no definition, and the
/// WHOLE function's witness is refused. These ancestors let the resolvers keep
/// looking past such blocks.
///
/// SOUNDNESS. A step is taken only when the current block provably does not
/// touch `_0` ([`block_preserves_return_place`]) AND has EXACTLY ONE
/// predecessor — so every execution reaching the return through `from` passed
/// through that predecessor, and the `_0` it defined is the `_0` observed at
/// `Return`. Multiple predecessors, a back edge, exhausted fuel, or any
/// unmodeled statement all end the walk.
///
/// AND the candidate's OWN TERMINATOR is checked BEFORE it is pushed. That
/// order is load-bearing and used to be wrong: the loop pushed the sole
/// predecessor and only then made it `current`, so the block that HOLDS the
/// definition — the one whose `_0` statement ends the walk on the next
/// iteration — never reached the terminator test at all. `bb = { _0 = Ok(5);
/// Call { dest: _0, target: .. } }` was therefore admitted, and the stale
/// `Ok(5)` was attributed to a return path its own terminator had already
/// overwritten, using the very shape [`terminator_preserves_return_place`]
/// names. A pushed block's STATEMENTS still only need checking when the walk
/// steps FURTHER past it, which is exactly where the next iteration's
/// [`block_preserves_return_place`] looks.
///
/// CALLERS MUST APPEND, NEVER PREPEND. These blocks extend the resolver's
/// search window BACKWARDS, and that window is read LATEST-FIRST, so they
/// belong at its far end: an ancestor is by construction older than the
/// `vc_block` it was reached from. Prepending them would hand the resolver a
/// definition the return path has already overwritten — the same class of
/// mistake the window's own ordering used to make; see
/// `resolve_enum_return_aggregate_with_block`.
///
/// This does NOT change any caller's `vc_block`: the per-predecessor VC
/// quantification domain and every `version_token_at` derivation stay exactly as
/// they are (see `contract_vcs.rs`, "Both facts are PER-PREDECESSOR").
fn return_producer_ancestors<'a>(
    func: &'a VerifiableFunction,
    from: &'a trust_types::BasicBlock,
) -> Vec<&'a trust_types::BasicBlock> {
    if !block_preserves_return_place(from) {
        return Vec::new();
    }
    let mut chain = Vec::new();
    let mut current = from;
    let mut visited: FxHashSet<BlockId> = FxHashSet::default();
    visited.insert(from.id);
    let v2_preds = crate::fn_memo::v2_predecessors(func);
    for step in 0..RETURN_PRODUCER_WALK_FUEL {
        if step > 0 && !block_preserves_return_place(current) {
            break;
        }
        // Sole predecessor only: a join would need ALL of its predecessors.
        let Some(only) = (match v2_preds.as_deref() {
            Some(preds) => preds.sole_predecessor(func, current.id),
            None => {
                let mut preds = func
                    .body
                    .blocks
                    .iter()
                    .filter(|pred| v2_terminator_has_target(&pred.terminator, current.id));
                match (preds.next(), preds.next()) {
                    (Some(only), None) => Some(only),
                    _ => None,
                }
            }
        }) else {
            break;
        };
        if !visited.insert(only.id) {
            break;
        }
        // Whatever `only` defines for `_0` must survive `only`'s OWN exit into
        // `current`. Checked here, before the push, because a chain tail is
        // never re-examined: see this function's SOUNDNESS note.
        if !terminator_preserves_return_place(&only.terminator) {
            break;
        }
        chain.push(only);
        current = only;
    }
    chain
}

/// Whether `name` is EXACTLY the std/core `Option` ADT path — never a substring
/// match. A substring gate (`name.contains("Option")`) is a FALSE-PROVE hole: a
/// user enum whose path merely contains "Option" (`ConfigOption`, `Optional`, a
/// type in a module named `option`) with an INVERTED variant order (payload
/// variant declared first = index 0) would be wrongly credited, and the spec
/// parser lowers `.is_some()`/`.is_none()`/`.unwrap()` PURELY BY METHOD NAME
/// regardless of receiver type — so `#[ensures(|r| r.is_some())]` over a body
/// returning that enum's index-0 payload variant would prove a FALSE post
/// (`_0__discr==1` pinned, `Not(post)` = `_0__discr==0`, `1==0` UNSAT ⇒ vacuous
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
/// wrappers with ONE convention — `{base}__discr == 0` = the "empty" variant:
///   `is_none()`/`is_err()` => `_0__discr == 0`;
///   `is_some()`/`is_ok()`  => `_0__discr != 0`.
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
            if variant == 0 {
                1
            } else {
                0
            }
        }
    }
}

/// The machine variant index of `kind`'s PAYLOAD-carrying variant (`Some` /
/// `Ok`) — the only variant whose single operand the return pin may credit as
/// the parser's `_0__value` payload term.
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
/// whole-local def, and the whole discr gate fails closed (`_0__discr`
/// UNGROUNDED for the entire function — the b62 `certify_upper` bug).
///
/// Returns `(kind, variant)` — the std enum kind (from the return type) and the
/// EMPTY (non-payload) variant the dominating `match inner()` discriminant
/// switch PROVABLY forces for the edge reaching `fwd_block` — or `None`
/// (fail-closed) otherwise.
///
/// SOUNDNESS (why only forced-EMPTY-variant edges ground): the pin is
/// `_0__discr == std_enum_model_discr(kind, EMPTY)`, TRUE on this path iff
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
    let tp = super::terminator_presence_for(func);
    if !tp.has_bare_dest_call || !tp.has_switch_int {
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
    // (1) `call_dest` is a `Call` dest, and its value is stable end-to-end (so
    // `discriminant(call_dest)` at the switch equals `_0`'s discriminant at the
    // forward). A param / undefined / mutated local is NOT a forwarded call
    // result and stays fail-closed.
    let is_call_dest = crate::any_local_write_term(
        func,
        &func.body.blocks,
        call_dest,
        |_b, term| {
            matches!(term, Terminator::Call { dest, .. }
                if dest.local == call_dest && dest.projections.is_empty())
        },
    );
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
        if crate::local_defs::is_parameter(func, d) {
            continue;
        }
        let Some(Rvalue::Discriminant(p)) = crate::local_defs::unique_value_def(func, d) else {
            continue;
        };
        if p.local != call_dest || !p.projections.is_empty() {
            continue;
        }
        // (2b) the switch DOMINATES the forward block (it is unreachable from
        // entry while avoiding the switch — every path to it passes the switch).
        if reachable_avoiding_one_contains(func, 0, Some(g), fwd_block) {
            continue;
        }
        // (2c) EXACTLY ONE switch edge reaches the forward block avoiding the
        // switch; that edge's selected variant is forced on this return path.
        let discr_ty = crate::operand_ty_cow(func, discr);
        let mut n_reaching = 0usize;
        let mut forced: Option<usize> = None;
        let mut reaching_start: Option<usize> = None;
        for (tag, tgt) in targets {
            if !reachable_avoiding_one_contains(func, tgt.0, Some(g), fwd_block) {
                continue;
            }
            n_reaching += 1;
            if n_reaching > 1 {
                break;
            }
            reaching_start = Some(tgt.0);
            // `VariantDef::discriminant` is DECODED at the extraction boundary,
            // so the raw MIR arm label must be decoded too before the two can be
            // compared. (They used to be raw-vs-raw, which agreed by accident.)
            // An undecodable label leaves `forced` at `None`, which drops this
            // grounding — fail closed.
            forced = discr_ty
                .as_deref()
                .and_then(|ty| ty.decode_switch_label(*tag))
                .and_then(|t| variants.iter().position(|v| v.discriminant == t));
        }
        if n_reaching > 1
            || (n_reaching == 1 && forced.is_none_or(|v| v == payload_variant))
        {
            continue;
        }
        if reachable_avoiding_one_contains(func, otherwise.0, Some(g), fwd_block) {
            n_reaching += 1;
            if n_reaching != 1 {
                continue;
            }
            reaching_start = Some(otherwise.0);
            // `otherwise` selects the COMPLEMENT of the explicit tags; force a
            // variant only when that complement is a SINGLE variant (the exact
            // 2-variant / `n-1`-explicit-target enum partition — e.g. Result's
            // `switchInt(discr) -> [0: Ok]` with `otherwise` = Err).
            // Same decode as the explicit-arm branch above: the complement is
            // taken over DECODED tags, so the labels must be decoded too.
            // ALL-OR-NOTHING: a dropped label would SHRINK `covered` and so
            // GROW `remaining`, and a `remaining` that grows from 0 to 1 would
            // force a variant on a path whose `otherwise` is in fact
            // unreachable. Decline the whole complement instead.
            let Some(covered) = discr_ty.as_deref().and_then(|ty| {
                targets
                    .iter()
                    .map(|(t, _)| ty.decode_switch_label(*t))
                    .collect::<Option<FxHashSet<i128>>>()
            }) else {
                continue;
            };
            let mut rem = variants
                .iter()
                .enumerate()
                .filter(|(_, v)| !covered.contains(&v.discriminant))
                .map(|(i, _)| i);
            forced = match (rem.next(), rem.next()) {
                (Some(only), None) => Some(only),
                _ => None,
            };
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
        let Some(start_block) = reaching_start else { continue };
        let avoid_g = one_block_set(g);
        let region = reachable_avoiding(func, start_block, &avoid_g);
        let region_writes = func.body.blocks.iter().any(|b| {
            if !region.contains(&b.id.0) {
                return false;
            }
            // Trust: SOUNDNESS (2026-09-01) — ask the owning crate's EXHAUSTIVE
            // per-local classifier, not a two-case deny-list. The fact under
            // protection is discriminant stability, and the old spelling matched
            // `Statement::Assign` + a `Call` dest only: `SetDiscriminant` on
            // `call_dest` (a discriminant write with no `Rvalue` to name),
            // `Deinit`, a `Drop` whose glue takes `&mut call_dest`, and the
            // dest-discarding `Opaque` all passed the guard. `local_write` and
            // `write_effect` are wildcard-free in `trust-types`, so a new MIR
            // write channel cannot reach `false` here without being classified
            // there first.
            let stmt_write = b
                .stmts
                .iter()
                .any(|s| !matches!(s.local_write(call_dest), trust_types::LocalWrite::Untouched));
            let term_write = !terminator_preserves_local(&b.terminator, call_dest);
            stmt_write || term_write
        });
        if region_writes {
            continue;
        }
        return Some((kind, variant));
    }
    None
}

/// Trust: 2026-09-14 — SOUNDNESS (kernel-`Certified` FALSE-VERIFY closure).
/// True iff ANY statement in the function hands out a MUTABLE or RAW alias of
/// `local` — `&mut local` / `&raw [const|mut] local` — via
/// [`trust_types::Statement::escapes_local`], the affirmative escape test the
/// owning crate spells out (`Rvalue::Ref { mutable: true }` | `Rvalue::AddressOf`,
/// with `borrowed.local == local`; a `*const` is a valid `*const -> *mut` cast
/// root, so a raw-const address-of qualifies, while a plain shared `&local`
/// cannot mutate and does not).
///
/// WHY THE RESOLVER NEEDS IT. Once `local` has been mutably aliased, its value
/// can be RESEATED through that alias (`*p = None`) AFTER its whole-local
/// initializer runs, so an earlier `Rvalue::Aggregate`/`Use` definition can no
/// longer be attributed to it as the value observed at `Return`. That is exactly
/// the `let mut r = Some(5); let p = &mut r; *p = None; r` shape, which
/// previously certified `is_some()` on a body returning `None` (and the polarity
/// twin certified `is_none()` on a body returning `Some`): the resolver hopped
/// `_0 -> _1` and read `_1`'s STALE `Some(5)` aggregate, blind to the
/// `_2 = &mut _1; (*_2) = None` reseat that the discriminant model then
/// contradicts (`_0__discr == 1` pinned against a `_0__discr == 0` fact from the
/// deref store — an inconsistent context the kernel certifies vacuously).
/// [`statements_preserve_return_place`] cannot catch it: the borrow's place-local
/// is `_2` and the deref store's is `_2` (a `Deref` projection), never `_0`.
///
/// SCOPE. Whole-function, and conservative on purpose: the value reaching `_0`
/// IS this tracked local's, this resolver has no region/liveness model of where
/// the reseat happens relative to the definition, and the gates this feeds
/// already fail the WHOLE function closed when any return path is unresolved. It
/// withholds ONLY when a mutable/raw borrow of the tracked local actually exists,
/// so a plain non-aliased `Some(..)`/`None`/`Ok(..)`/`Err(..)` return — whose
/// holder is never borrowed — still grounds exactly as before. This mirrors the
/// discipline [`f4_whole_local_defs`] already applies to its own witness local.
fn local_escapes_anywhere(func: &VerifiableFunction, local: usize) -> bool {
    crate::any_local_write_stmt(func, &func.body.blocks, local, |_b, s| {
        crate::stmt_escapes_local(func, s, local)
    })
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
    resolve_enum_return_aggregate_with_block(func, vc_block, block)
        .map(|(k, v, ops, _)| (k, v, ops))
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
    resolve_enum_return_aggregate_located(func, vc_block, block)
        .map(|(kind, variant, ops, b, _)| (kind, variant, ops, b))
}

/// Fast whole-function pre-check for [`resolve_enum_return_aggregate_located`]:
/// returns `true` iff the function's return local `_0` is a std `Option`/`Result`
/// ADT or any statement in the body constructs a 2-variant std `Option`/`Result`
/// aggregate. Without either, `resolve_enum_return_aggregate_located` is
/// guaranteed to return `None` on every return path.
pub(super) fn body_may_have_std_enum_return(func: &VerifiableFunction) -> bool {
    if let Some(Ty::Adt { name, .. }) = crate::local_ty_ref(func, 0)
        && (is_std_option_name(name) || is_std_result_name(name))
    {
        return true;
    }
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, _),
                    ..
                } if *variant <= 1 && (is_std_option_name(name) || is_std_result_name(name))
            )
        })
    })
}

/// [`resolve_enum_return_aggregate_with_block`] plus the STATEMENT index of the
/// resolved aggregate assignment inside that block (`None` for the forwarded
/// Call-dest resolution, which has no aggregate statement and no operands).
///
/// Trust (2026-09-30, P2 of the `vac` root cause): the postcondition lane stamps
/// the payload pin's reads at this statement, so a later whole-formula rename
/// cannot re-read them against a post-write value.
pub(super) fn resolve_enum_return_aggregate_located<'a>(
    func: &'a VerifiableFunction,
    vc_block: &'a trust_types::BasicBlock,
    block: &'a trust_types::BasicBlock,
) -> Option<(StdEnumReturn, usize, &'a [trust_types::Operand], BlockId, Option<usize>)> {
    // The whole-local definition of `local` (no field projection) that REACHES
    // the return, searched over the window the pin loop threads: the aggregate
    // lives in `vc_block`, the `_0 = _k` move in `block`; the
    // `_0`-preserving ancestors extend the window backwards for the
    // drop-elaboration join case, where the aggregate sits further back.
    //
    // LATEST-FIRST, and that order is the whole point. Every caller passes a
    // `vc_block` drawn from `predecessors(block)` (or `block` itself when it has
    // none), and each ancestor is the SOLE predecessor of the block before it,
    // so the window is one linear path:
    //
    //     anc_k -> .. -> anc_1 -> vc_block -> block
    //
    // The definition observed at `Return` is therefore the LAST one on that
    // path. This list used to be built EARLIEST-first (`[vc_block, block]` then
    // the ancestors) and `find_map` took the first hit, statement order
    // included — so a DEAD store beat the live definition below it. Measured
    // end to end against the PRE-FIX stage1 driver on 2026-09-01, that was a
    // live false verify on three lines of ordinary Rust:
    //
    //     #[core::contracts::ensures(|r: &Option<i64>| r.is_some())]
    //     pub fn h(g: fn() -> Option<i64>) -> Option<i64> {
    //         let mut r = Some(5);   // bb0: `_3 = Some(5)` — rustc itself warns
    //         r = g();               // bb1: `_3 = move _4`  — the LIVE def
    //         r                      // bb1: `_0 = move _3`
    //     }
    //
    // `2 proved, 0 failed, 0 unknown`, exit 0 — for a postcondition the compiled
    // program then violates whenever `g()` returns `None`. The alias hop
    // `_0 -> _3` read `_3`'s definition out of the PREDECESSOR because the
    // predecessor came first in this list, even though the return block's
    // definition of `_3` is the one that runs last. Deleting the dead store made
    // the same function fail closed (`0 proved, 2 unknown`), and flipping it to
    // `None` made the SAME body prove the OPPOSITE postcondition.
    //
    // The regression pins in `return_walk_preservation_tests` transcribe that
    // dumped MIR one-for-one, because re-running the end-to-end repro needs a
    // driver rebuild.
    //
    // `block_preserves_return_place` cannot reach this: it guards `place.local
    // == 0`, and the local being read here is the alias, not the return slot.
    // Order is the only thing that decides it, so order is what is fixed.
    // `contract_vcs.rs` already states the intended rule for the pin it feeds —
    // "Pin at MOST ONE discriminant per return path (last / nearest-to-return
    // wins)"; this makes the resolver agree with it.
    let mut search: Vec<&'a trust_types::BasicBlock> = vec![block, vc_block];
    search.extend(return_producer_ancestors(func, vc_block));
    let whole_def = |local: usize| -> Option<(&'a Rvalue, BlockId, usize, usize)> {
        search.iter().copied().enumerate().find_map(|(bi, b)| {
            b.stmts.iter().enumerate().rev().find_map(|(k, stmt)| match stmt {
                Statement::Assign { place, rvalue, .. }
                    if place.local == local && place.projections.is_empty() =>
                {
                    Some((rvalue, b.id, bi, k))
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
        // Trust: SOUNDNESS (2026-09-14) — WITHHOLD when the tracked local can be
        // reseated through a `&mut`/`&raw` alias. Checked BEFORE `whole_def` so it
        // covers `_0` itself, every whole-local alias hop below, and a bottomed-out
        // Call-dest before it reaches `resolve_forwarded_call_return_variant`
        // (whose discriminant-stability argument the same reseat would break). A
        // `false` here changes nothing; a missed `true` re-attributes a stale
        // initializer to a value the alias overwrote — the enum-return
        // false-`Certified` this closes. See `local_escapes_anywhere`.
        if local_escapes_anywhere(func, local) {
            lenwitness_dbg!(
                &lenwitness_dbg_fn(),
                "resolve bb{}->bb{}: tracked _{local} is mutably/raw aliased (&mut/&raw) in-body -> WITHHELD (fail-closed, no stale-def grounding through an alias)",
                vc_block.id.0,
                block.id.0
            );
            return None;
        }
        let wd = whole_def(local);
        if lenwitness_debug() {
            let desc = if let Some((rv, b, _, _)) = wd {
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
        let Some((rv, def_block, def_bi, def_stmt)) = wd else {
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
                let v2_preds = crate::fn_memo::v2_predecessors(func);
                for _ in 0..6 {
                    let Some(only) = (match v2_preds.as_deref() {
                        Some(preds) => preds.sole_predecessor(func, BlockId(cur)),
                        None => {
                            let mut preds = func
                                .body
                                .blocks
                                .iter()
                                .filter(|b| v2_terminator_has_target(&b.terminator, BlockId(cur)));
                            match (preds.next(), preds.next()) {
                                (Some(only), None) => Some(only),
                                _ => None,
                            }
                        }
                    }) else {
                        break;
                    };
                    // Trust: SOUNDNESS (2026-09-01) — this walk previously inspected
                    // ONLY `Assign` statements, so it would hop into, or step through,
                    // a block whose TERMINATOR writes `local` (`Call { dest: local }`,
                    // a `Drop` of it, or the dest-discarding `Opaque`) and attribute a
                    // definition from further up to this path — the same stale-value
                    // class as the `_0` walk's terminator hole. The terminator runs
                    // AFTER the statements, so it decides what leaves the block.
                    if !terminator_preserves_local(&only.terminator, local) {
                        break;
                    }
                    // The write that REACHES the successor is the LAST one in the
                    // block, over EVERY channel — not the first `Assign` (the same
                    // earliest-first defect fixed in `whole_def`). Ask the exhaustive
                    // per-local classifier, then require that last write to be exactly
                    // the forward-move this hop models; anything else (a partial store,
                    // a `SetDiscriminant`, a `Deinit`, an unlocatable write) fails
                    // closed rather than being hopped over.
                    let last_write = only.stmts.iter().rev().find(|s| {
                        !matches!(s.local_write(local), trust_types::LocalWrite::Untouched)
                    });
                    let def = match last_write {
                        None => None,
                        Some(Statement::Assign { place, rvalue, .. })
                            if place.local == local && place.projections.is_empty() =>
                        {
                            Some(rvalue)
                        }
                        Some(_) => break,
                    };
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
                return Some((k, variant, &[], BlockId(fwd_block), None));
            }
            return None;
        };
        match rv {
            Rvalue::Aggregate(AggregateKind::Adt { name, variant, .. }, ops) if *variant <= 1 => {
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
                return Some((kind, *variant, ops, def_block, Some(def_stmt)));
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
                // Review round 44: `whole_def` reads the LAST def in the window,
                // which can follow the copy being hopped through (`let t = r; r =
                // Some(a); t` pinned `Some` for a `None` return, certified). Hop
                // only when nothing writes the target AFTER the copy on this path:
                // later statements of the copy's block, its terminator, and every
                // block nearer the return (earlier in `search`). The last def found
                // is then the value the copy read.
                let target = p.local;
                let writes_target = |stmt: &Statement| {
                    !matches!(stmt.local_write(target), trust_types::LocalWrite::Untouched)
                        || crate::stmt_escapes_local(func, stmt, target)
                };
                let written_after_copy =
                    search[def_bi].stmts[def_stmt + 1..].iter().any(writes_target)
                        || search[..=def_bi].iter().any(|b| {
                            !matches!(
                                b.terminator.local_write(target),
                                trust_types::LocalWrite::Untouched
                            )
                        })
                        || search[..def_bi].iter().any(|b| b.stmts.iter().any(writes_target));
                if written_after_copy {
                    lenwitness_dbg!(
                        &lenwitness_dbg_fn(),
                        "resolve bb{}->bb{}: alias hop target _{} is written after the copy -> WITHHELD",
                        vc_block.id.0,
                        block.id.0,
                        p.local
                    );
                    return None;
                }
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
/// set of synthetic spec-model names (`_0__discr`, `_0__value`) that the
/// body-aware contract lane can now GROUND — i.e. connect to the return slot's
/// real construction — or an EMPTY set (fail-closed) when it cannot.
///
/// Credited ONLY when ALL THREE hold, so the "no free-and-havocked model term
/// on any reachable return path" invariant is preserved unconditionally:
///  (a) the return type is the std/core `Option` or `Result` ADT (exact
///      canonical path — see `is_std_option_name` / `is_std_result_name`) whose
///      lowered variant defs carry the std machine tags (`None`=0/`Some`=1,
///      `Ok`=0/`Err`=1 — a degraded lowering refuses the whole gate), and
///  (b) EVERY `Return`-terminated block's grounding path (its predecessors, or
///      the block itself when it has none — the SAME `vc_blocks` reconstruction
///      the pin loop uses) assigns `_0` via an IN-BODY
///      `Rvalue::Aggregate(Adt{the SAME std enum, variant∈{0,1}})`, and
///  (c) there is at least one such path, and no exit this gate cannot inspect
///      (a `TailCall`, whose destination is the return place implicitly) — see
///      the guard's own comment for the vacuous credit that closed.
/// If any return path routes `_0` through a `Call` dest (e.g. `and_then` /
/// `checked_*` — `index_midpoint` — or the `?`-desugar `from_residual`), a
/// copy/move of a temp, or a non-wrapper / multi-variant aggregate, the gate
/// returns empty and the postcondition keeps today's fail-closed `Unknown` —
/// strictly no regression, and never a term left free (which would
/// false-refute) or credited-but-unpinned.
///
/// WHICH names are credited:
///  * `_0__discr` — always (once (a)+(b)+(c) hold): the pin loop pins it on every
///    return path to the PARSER-convention value (`std_enum_model_discr` —
///    Result's mapping is INVERTED vs its machine variant order).
///  * `_0__value` — only when the payload variant (`Some`/`Ok`) is a single
///    INTEGER field, so the pinned term matches the `Sort::Int` the parser
///    mints. For `Option` a non-integer payload refuses the WHOLE gate
///    (pre-existing behavior, kept: no regression risk in this change); for
///    `Result` — the ny-cert selfcheck/crown shapes, whose payloads are Rat
///    handles / Vec aggregates — `_0__discr` alone is credited and every
///    `_0__value*` / `*__sign` / `.__trust_ok_i` term stays UNGROUNDED, so any
///    postcondition referencing them still routes to the fail-closed
///    SpecModelUngrounded Unknown (never a refutable havoc'd VC).
pub(super) fn enum_return_grounded_model_vars(func: &VerifiableFunction) -> FxHashSet<String> {
    lenwitness_dbg_set_fn(&func.def_path);
    let empty = FxHashSet::default();
    // (a) return type is std/core Option or Result with std variant tags.
    let Some(Ty::Adt { name, variants, .. }) = crate::local_ty_ref(func, 0) else {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: return type of _0 is not Ty::Adt -> _0__discr UNGROUNDED"
        );
        return empty;
    };
    // (kind, payload variant name, payload machine tag, empty-variant name+tag)
    let (kind, payload_name, payload_tag, empty_name, empty_tag) = if is_std_option_name(name) {
        (StdEnumReturn::Option, "Some", 1, "None", 0)
    } else if is_std_result_name(name) {
        (StdEnumReturn::Result, "Ok", 0, "Err", 1)
    } else {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: return adt name={name} is NOT std Option/Result -> _0__discr UNGROUNDED"
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
            "discr-gate: payload variant {payload_name}(tag {payload_tag}) missing from lowered variant defs -> _0__discr UNGROUNDED"
        );
        return empty;
    };
    if !variants.iter().any(|v| v.name == empty_name && v.discriminant == empty_tag) {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: empty variant {empty_name}(tag {empty_tag}) missing from lowered variant defs -> _0__discr UNGROUNDED"
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
            "discr-gate: Option with non-integer Some payload -> whole gate refused, _0__discr UNGROUNDED"
        );
        return empty;
    }
    // (c) FAIL CLOSED ON AN EXIT THIS GATE CANNOT INSPECT. The loop below walks
    // `Terminator::Return` blocks only, while the pin loop it feeds
    // (`contract_vcs.rs`) pins over `Return | TailCall` — so a tail-call exit is
    // pinned without ever being gated, and a body with no `Return` at all is
    // credited having inspected nothing. Neither can be grounded even in
    // principle: a `TailCall`'s destination IS the return place, implicitly
    // (`convert.rs:1838`, `let implicit_return = Place::local(0)`), so every
    // `_0` definition reaching it is stale by construction — the same fact
    // [`terminator_preserves_return_place`] refuses on. Measured before this
    // guard: a body whose only exit was a tail call credited BOTH `_0__discr`
    // and `_0__value` off `n_return_paths == 0`, and the pin loop then pinned
    // the pre-tail-call `Ok(5)` into a body-aware `Postcondition` VC that is
    // UNSAT on its own conjunction — a vacuous PROVE about a value the callee
    // replaced.
    if super::terminator_presence_for(func).has_tail_call {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: body has a TailCall exit (implicit `_0` dest, ungroundable) -> _0__discr UNGROUNDED"
        );
        return empty;
    }
    if !func.body.blocks.iter().any(|b| matches!(b.terminator, Terminator::Return)) {
        lenwitness_dbg!(
            &func.def_path,
            "discr-gate: NO `Return` block to ground -> _0__discr UNGROUNDED (nothing was inspected)"
        );
        return empty;
    }
    // (b) every Return path assigns _0 via an in-body aggregate of the SAME
    // std enum as the return type.
    let v2_preds = crate::fn_memo::v2_predecessors_or_build(func);
    let mut n_return_paths = 0usize;
    for block in &func.body.blocks {
        if !matches!(block.terminator, Terminator::Return) {
            continue;
        }
        let predecessors = v2_preds.predecessors(func, block.id);
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
                        "discr-gate: return path bb{}->bb{} FAILS gate ({}) -> _0__discr UNGROUNDED for the WHOLE function",
                        vc_block.id.0,
                        block.id.0,
                        match other {
                            Some((k, _, _)) =>
                                format!("resolved kind={k:?} != return kind={kind:?}"),
                            None => "resolve_enum_return_aggregate returned None".to_string(),
                        }
                    );
                    return empty;
                }
            }
        }
    }
    let mut set = FxHashSet::default();
    set.insert("_0__discr".to_string());
    if int_payload {
        set.insert("_0__value".to_string());
    }
    lenwitness_dbg!(
        &func.def_path,
        "discr-gate: ALL {n_return_paths} return path(s) grounded -> credited {set:?}"
    );
    set
}

/// Parse `_0__value.<i>.<j>…__len` (any `#version` token stripped) into its
/// positional field path. `None` for every other shape — the bare `_0__value__len`,
/// non-numeric segments, other bases — which keep today's fail-closed routing.
pub(super) fn parse_len_model_var(name: &str) -> Option<LenModelVar> {
    let base = name.split('#').next().unwrap_or(name);
    let core = base.strip_prefix("_0__value.")?.strip_suffix("__len")?;
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
pub(super) fn len_pair_coverage<'a>(posts: &[&'a Formula]) -> Vec<(LenModelVar, LenModelVar)> {
    let is_len_model_base = |base: &str| -> bool {
        let Some(core) = base.strip_prefix("_0__value.").and_then(|s| s.strip_suffix("__len"))
        else {
            return false;
        };
        !core.is_empty() && core.split('.').all(|s| s.parse::<usize>().is_ok())
    };
    let mut total: FxHashMap<&'a str, usize> = FxHashMap::default();
    let mut paired: FxHashMap<&'a str, usize> = FxHashMap::default();
    let mut pairs: Vec<(LenModelVar, LenModelVar)> = Vec::new();
    for &post in posts {
        trust_types::visit_formula_nodes(post, &mut |f| match f {
            Formula::Var(n, _) if n.starts_with("_0__value.") => {
                let base = n.split('#').next().unwrap_or(n);
                if is_len_model_base(base) {
                    *total.entry(base).or_default() += 1;
                }
            }
            Formula::Eq(l, r) => {
                if let (Formula::Var(a, _), Formula::Var(b, _)) = (&**l, &**r)
                    && a.starts_with("_0__value.")
                    && b.starts_with("_0__value.")
                {
                    let base_a = a.split('#').next().unwrap_or(a);
                    let base_b = b.split('#').next().unwrap_or(b);
                    if base_a != base_b && is_len_model_base(base_a) && is_len_model_base(base_b) {
                        for base in [base_a, base_b] {
                            *paired.entry(base).or_default() += 1;
                        }
                        let seen = pairs.iter().any(|(x, y)| {
                            (x.name == base_a && y.name == base_b)
                                || (x.name == base_b && y.name == base_a)
                        });
                        if !seen
                            && let (Some(va), Some(vb)) =
                                (parse_len_model_var(base_a), parse_len_model_var(base_b))
                        {
                            pairs.push((va, vb));
                        }
                    }
                }
            }
            _ => {}
        });
    }
    if lenwitness_debug() {
        let who = lenwitness_dbg_fn();
        for (a, b) in &pairs {
            let cov_a = total.get(a.name.as_str()).copied().unwrap_or(0);
            let par_a = paired.get(a.name.as_str()).copied().unwrap_or(0);
            let cov_b = total.get(b.name.as_str()).copied().unwrap_or(0);
            let par_b = paired.get(b.name.as_str()).copied().unwrap_or(0);
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
        total.get(a.name.as_str()) == paired.get(a.name.as_str())
            && total.get(b.name.as_str()) == paired.get(b.name.as_str())
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
    ty_is_owned_vec(ty)
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
/// alias hop's source — is `place_source_is_stable_modulo_whole_drops` (single
/// construction, no projected write, no `&mut`/raw-mut anywhere) — so a length
/// observed on ANY candidate equals the returned component's length (no mutation
/// can intervene between the witness and the return). A terminator `Drop` of a
/// WHOLE root is not such a mutation: it ends the value, and the witness borrow and
/// the returned construction both read the root while it is live (the guard-Err
/// path's `Drop(c)` in the ny wrapper; VCGEN-LIB-REDS-1). An unstable/unresolvable hop stops
/// the unfold (keeping the shallower, still-valid candidates); an unstable
/// `src` yields NO candidates at all. Fuel-bounded: alias hops do not consume
/// a path index, so the walk needs an explicit bound (which also breaks a
/// pathological `_a = move _b; _b = move _a` single-def cycle).
pub(super) fn component_candidate_places(
    func: &VerifiableFunction,
    src: usize,
    path: &[usize],
) -> Vec<Place> {
    const FUEL: usize = 16;
    let mut out = Vec::new();
    let mut local = src;
    let mut idx = 0usize;
    // Debug-only: WHY the descent stopped (never read unless `lenwitness_debug`).
    let mut stop_reason = "fuel exhausted (>16 hops)";
    for _ in 0..FUEL {
        if !crate::place_source_is_stable_modulo_whole_drops(func, local) {
            stop_reason = "root _local not place_source_is_stable_modulo_whole_drops (multi-def / projected write / slot-write channel)";
            break;
        }
        out.push(Place {
            local,
            projections: path[idx..].iter().map(|&i| trust_types::Projection::Field(i)).collect(),
        });
        if crate::local_defs::is_parameter(func, local) {
            stop_reason =
                "def is not a positional aggregate or whole-local move alias (leaf reached, or Call-dest / projected / non-variant-0)";
            break;
        }
        match crate::local_defs::unique_value_def(func, local) {
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
            // head re-checks `place_source_is_stable_modulo_whole_drops` on the new root before
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
                stop_reason = "def is not a positional aggregate or whole-local move alias (leaf reached, or Call-dest / projected / non-variant-0)";
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
pub(super) fn component_source_leaf(
    func: &VerifiableFunction,
    src: usize,
    path: &[usize],
) -> Option<usize> {
    let mut local = src;
    for &i in path {
        if !crate::place_source_is_stable(func, local) {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP at _{local} not place_source_is_stable -> None"
            );
            return None;
        }
        if crate::local_defs::is_parameter(func, local) {
            lenwitness_dbg!(
                &func.def_path,
                "source-leaf: src=_{src} path={path:?} STOP _{local} has no unique-whole-def aggregate (alias/Call-dest/multi-def) -> None"
            );
            return None;
        }
        let Some(Rvalue::Aggregate(kind, ops)) = crate::local_defs::unique_value_def(func, local)
        else {
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
    lenwitness_dbg!(&func.def_path, "source-leaf: src=_{src} path={path:?} -> leaf _{local}");
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
    let tp = super::terminator_presence_for(func);
    if !tp.has_switch_int || !tp.has_bare_dest_call {
        return None;
    }
    // The unique def of `l` is an INHERENT `Vec::len` call (`std::vec::Vec::<T>::len`
    // — no `as`-qualified trait path, which a user `len` impl over a `&Vec`
    // receiver would carry), so the dest genuinely denotes the container length.
    // `operand_is_len_of_place` admitted ANY `len`-tailed callee until 2026-10-03
    // (NAME-ANCHOR-1); it now admits only a std container length
    // (`is_std_inherent_len_call`), and this lane keeps its own narrower
    // inherent-`Vec` gate, which with the component-type gate pins the std semantics.
    let inherent_vec_len_dest = |l: usize| -> bool {
        crate::any_local_write_term(func, &func.body.blocks, l, |_b, term| {
            matches!(term,
                Terminator::Call { func: callee, dest, .. }
                    if dest.local == l
                        && dest.projections.is_empty()
                        && method_tail(callee) == "len"
                        && vc_callee_is_std_vec_inherent(callee))
        })
    };
    let len_local_for = |op: &Operand, cands: &[Place]| -> Option<usize> {
        let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
        if cands.is_empty()
            || !p.projections.is_empty()
            || !inherent_vec_len_dest(p.local)
            || !crate::place_source_is_stable(func, p.local)
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
        if crate::local_defs::is_parameter(func, c) {
            continue;
        }
        let Some(Rvalue::BinaryOp(cmp, opl, opr)) = crate::local_defs::unique_value_def(func, c)
        else {
            continue;
        };
        if !matches!(cmp, BinOp::Eq | BinOp::Ne) {
            continue;
        }
        let sides = len_local_for(opl, cand_a)
            .and_then(|la| len_local_for(opr, cand_b).map(|lb| (la, lb)))
            .or_else(|| {
                len_local_for(opr, cand_a)
                    .and_then(|la| len_local_for(opl, cand_b).map(|lb| (la, lb)))
            });
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
        if reachable_avoiding_one_contains(func, 0, Some(g), agg_block) {
            lenwitness_dbg!(
                &func.def_path,
                "guard: bb{g} len-eq compare(_{la}/_{lb}) does NOT dominate agg bb{agg_block} (agg reachable from entry avoiding bb{g}) -> skip"
            );
            continue;
        }
        // …the INEQUALITY edge cannot reach it, and the equality edge can.
        if reachable_avoiding_one_contains(func, bad.0, Some(g), agg_block) {
            lenwitness_dbg!(
                &func.def_path,
                "guard: bb{g} INEQUALITY edge bb{} reaches agg bb{agg_block} (not a fail-closed guard) -> skip",
                bad.0
            );
            continue;
        }
        if !reachable_avoiding_one_contains(func, good.0, Some(g), agg_block) {
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
    !crate::local_defs::is_parameter(func, leaf)
        && super::terminator_presence_for(func).has_bare_dest_call
        && crate::local_ty_ref(func, leaf).is_some_and(ty_is_owned_vec)
        && crate::local_defs::has_one_explicit_def(func, leaf)
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
        if method_tail(callee) != "push" || !vc_callee_is_std_vec_inherent(callee) {
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
    let mut preds: FxHashMap<usize, usize> =
        FxHashMap::with_capacity_and_hasher(func.body.blocks.len(), Default::default());
    for b in &func.body.blocks {
        for_each_v2_terminator_target(&b.terminator, |t| {
            *preds.entry(t.0).or_default() += 1;
        });
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
        let mut single_succ: Option<usize> = None;
        let mut multiple_succs = false;
        for_each_v2_terminator_target(&b.terminator, |target| {
            if single_succ.is_some() {
                multiple_succs = true;
            } else {
                single_succ = Some(target.0);
            }
        });
        if multiple_succs {
            return None;
        }
        cur = single_succ?;
    }
    None
}

/// True iff `leaf_a` and `leaf_b` have provably EQUAL lengths at every block
/// outside a push-pair interior: both satisfy the push-only empty-start
/// discipline and their pushes are 1:1 chain-coupled (either orientation).
/// Zero pushes on both sides is the trivially-equal `0 == 0` case.
pub(super) fn paired_push_equal_lengths(
    func: &VerifiableFunction,
    leaf_a: usize,
    leaf_b: usize,
) -> bool {
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
    if !lenwitness_debug()
        && (!component_ty_is_owned_vec(func, &pair.0.path)
            || !component_ty_is_owned_vec(func, &pair.1.path))
    {
        return None;
    }
    let dp = &func.def_path;
    let bb = (vc_block.id.0, block.id.0);
    let names = (&pair.0.name, &pair.1.name);
    let Some((kind, variant, ops, agg_block)) =
        resolve_enum_return_aggregate_with_block(func, vc_block, block)
    else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): resolve_enum_return_aggregate=None -> pair FAILS (path _0 unresolved)",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return None;
    };
    if variant != std_enum_payload_variant(kind) {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): EMPTY variant (variant={variant} {kind:?}) -> Some(no pins; terms free is sound here)",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return Some(Vec::new());
    }
    if ops.len() != 1 {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): payload aggregate ops.len()={} != 1 -> None",
            bb.0,
            bb.1,
            names.0,
            names.1,
            ops.len()
        );
        return None;
    }
    let (Operand::Copy(sp) | Operand::Move(sp)) = &ops[0] else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): payload operand is const/symbolic (not move/copy place) -> None",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return None;
    };
    if !sp.projections.is_empty() {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): payload operand _{}.<proj> carries a projection -> None",
            bb.0,
            bb.1,
            names.0,
            names.1,
            sp.local
        );
        return None;
    }
    let src = sp.local;
    // Both components must be owned-Vec-typed per the DECLARED payload type,
    // so the witness `len` has the std container semantics.
    let a_ok = component_ty_is_owned_vec(func, &pair.0.path);
    let b_ok = a_ok && component_ty_is_owned_vec(func, &pair.1.path);
    if !b_ok {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): component type not owned Vec (a_ok={}, b_ok={}) -> None",
            bb.0,
            bb.1,
            names.0,
            names.1,
            a_ok,
            b_ok
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
        bb.0,
        bb.1,
        names.0,
        names.1,
        agg_block.0,
        cand_a.len(),
        cand_b.len()
    );
    if let Some((la, lb)) = guard {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): GUARD LANE grounded (len dests _{la}/_{lb}) -> Some(guard pins)",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return Some(vec![
            eq,
            Formula::Eq(
                Box::new(a_var),
                Box::new(crate::place_to_formula(func, &Place::local(la))),
            ),
            Formula::Eq(
                Box::new(b_var),
                Box::new(crate::place_to_formula(func, &Place::local(lb))),
            ),
        ]);
    }
    // Lane (2): equal-by-construction chain-coupled push leaves.
    let Some(leaf_a) = component_source_leaf(func, src, &pair.0.path) else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): no guard AND component_source_leaf(a)=None -> pair FAILS",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return None;
    };
    let Some(leaf_b) = component_source_leaf(func, src, &pair.1.path) else {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): no guard AND component_source_leaf(b)=None -> pair FAILS",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return None;
    };
    if paired_push_equal_lengths(func, leaf_a, leaf_b) {
        lenwitness_dbg!(
            dp,
            "path-pins bb{}->bb{} pair({}/{}): PUSH LANE grounded (leaves _{leaf_a}/_{leaf_b}) -> Some(eq pin)",
            bb.0,
            bb.1,
            names.0,
            names.1
        );
        return Some(vec![eq]);
    }
    lenwitness_dbg!(
        dp,
        "path-pins bb{}->bb{} pair({}/{}): neither guard nor paired-push (leaves _{leaf_a}/_{leaf_b}) -> pair FAILS",
        bb.0,
        bb.1,
        names.0,
        names.1
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
    posts: &[&Formula],
) -> Vec<(LenModelVar, LenModelVar)> {
    lenwitness_dbg_set_fn(&func.def_path);
    if posts.is_empty() {
        return Vec::new();
    }
    let mut pairs = len_pair_coverage(posts);
    if !lenwitness_debug() {
        pairs.retain(|pair| {
            component_ty_is_owned_vec(func, &pair.0.path)
                && component_ty_is_owned_vec(func, &pair.1.path)
        });
    }
    if pairs.is_empty() {
        lenwitness_dbg!(
            &func.def_path,
            "gate: NO covered len pairs -> len_groundable EMPTY (all _len postconditions stay SpecModelUngrounded)"
        );
        return pairs;
    }
    let before: Vec<(String, String)> = if lenwitness_debug() {
        pairs.iter().map(|(a, b)| (a.name.clone(), b.name.clone())).collect()
    } else {
        Vec::new()
    };
    let v2_preds = crate::fn_memo::v2_predecessors_or_build(func);
    let return_paths: Vec<(&trust_types::BasicBlock, Vec<&trust_types::BasicBlock>)> = func
        .body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::Return))
        .map(|block| {
            let predecessors = v2_preds.predecessors(func, block.id);
            let vc_blocks = if predecessors.is_empty() { vec![block] } else { predecessors };
            (block, vc_blocks)
        })
        .collect();
    pairs.retain(|pair| {
        for (block, vc_blocks) in &return_paths {
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

/// Parse `_0__value.__trust_ok_<i>` (any `#version` token stripped).
pub(super) fn parse_ok_pair_model_var(name: &str) -> Option<OkPairModelVar> {
    let base = name.split('#').next().unwrap_or(name);
    let index = base.strip_prefix("_0__value.__trust_ok_")?.parse::<usize>().ok()?;
    Some(OkPairModelVar { name: base.to_string(), index })
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
pub(super) fn ordering_pair_coverage<'a>(
    posts: &[&'a Formula],
) -> Vec<(OkPairModelVar, OkPairModelVar)> {
    let parse_ok_pair_base = |base: &str| -> Option<usize> {
        base.strip_prefix("_0__value.__trust_ok_")?.parse::<usize>().ok()
    };
    let mut total: FxHashMap<&'a str, usize> = FxHashMap::default();
    let mut paired: FxHashMap<&'a str, usize> = FxHashMap::default();
    let mut pairs: Vec<(OkPairModelVar, OkPairModelVar)> = Vec::new();
    for &post in posts {
        trust_types::visit_formula_nodes(post, &mut |f| {
            if let Formula::Var(n, _) = f
                && n.starts_with("_0__value.__trust_ok_")
            {
                let base = n.split('#').next().unwrap_or(n);
                if parse_ok_pair_base(base).is_some() {
                    *total.entry(base).or_default() += 1;
                }
            }
            if let Some((l, r)) = ordering_atom_sides(f)
                && let (Formula::Var(a, _), Formula::Var(b, _)) = (l, r)
                && a.starts_with("_0__value.__trust_ok_")
                && b.starts_with("_0__value.__trust_ok_")
            {
                let base_a = a.split('#').next().unwrap_or(a);
                let base_b = b.split('#').next().unwrap_or(b);
                if let (Some(idx_a), Some(idx_b)) =
                    (parse_ok_pair_base(base_a), parse_ok_pair_base(base_b))
                    && idx_a != idx_b
                {
                    for base in [base_a, base_b] {
                        *paired.entry(base).or_default() += 1;
                    }
                    let seen = pairs.iter().any(|(x, y)| {
                        (x.name == base_a && y.name == base_b)
                            || (x.name == base_b && y.name == base_a)
                    });
                    if !seen {
                        pairs.push((
                            OkPairModelVar { name: base_a.to_string(), index: idx_a },
                            OkPairModelVar { name: base_b.to_string(), index: idx_b },
                        ));
                    }
                }
            }
        });
    }
    pairs.retain(|(a, b)| {
        total.get(a.name.as_str()) == paired.get(a.name.as_str())
            && total.get(b.name.as_str()) == paired.get(b.name.as_str())
    });
    pairs
}

/// The ADT NAME of the payload component at positional `path` — walked
/// through plain STRUCT (`variants.is_empty()`) and tuple types only, exactly
/// like `component_ty_is_owned_vec`. The name keys the witness-callee
/// allowlist (the component type's OWN `PartialOrd` impl — the same functions
/// the contract's runtime check denotes) and the compiler's order-consistency
/// set (`crate::is_order_consistent_adt`).
/// `Ref`/slice/other component types fail closed: a by-ref component's
/// REFERENT mutability is not closed by `place_source_is_stable` on the
/// place roots.
pub(super) fn payload_component_adt_name<'a>(
    func: &'a VerifiableFunction,
    path: &[usize],
) -> Option<&'a str> {
    let mut ty = return_payload_ty(func)?;
    for &i in path {
        ty = match ty {
            Ty::Tuple(elems) => elems.get(i)?,
            Ty::Adt { fields, variants, .. } if variants.is_empty() => &fields.get(i)?.1,
            _ => return None,
        };
    }
    match ty {
        Ty::Adt { name, .. } => Some(name.as_str()),
        _ => None,
    }
}

/// Classify an allowlisted PAIR witness callee: the component type's own
/// `PartialOrd` operator method — `<{ty_name} as std::cmp::PartialOrd>::{m}`
/// (or `core::cmp::`) — returning the outcome set its TRUE result admits for
/// the argument pair IN CALL ORDER. Exact-prefix matching against the full
/// rendered self type prevents a partial type-name match.
pub(super) fn partial_ord_witness_facts(callee: &str, ty_name: &str) -> Option<OrderFacts> {
    // Trust (ARGS-FINGERPRINT-READ-1 round 3, 2026-10-07): this is a TYPE-PATH
    // reader — it matches the rendered `Self` type `ty_name` and the trait path
    // `core::cmp::PartialOrd` — so it DECLINES on a callee carrying the
    // duplicate-crate-name argument tag, like every other type-path reader
    // (`trust_types::args_display_may_name_a_same_named_crate`). The producer
    // writes the tag exactly when a def in the call's generic arguments (for
    // this trait method, `Self` and `Rhs`) lives in a crate whose rendered name
    // does not identify it, so `<k::P as core::cmp::PartialOrd>::lt` may then be
    // a same-named crate's `P`, whose operators nothing makes consistent. Until
    // round 3 this reader stripped the tag and matched past it.
    if trust_types::args_display_may_name_a_same_named_crate(callee) {
        return None;
    }
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

// Trust (2026-10-05, ORD-WITNESS-CONSISTENT-1): the SIGN witness lane is
// retired. It credited a payload type's own inherent `is_positive` /
// `is_negative` / `is_zero` as one trichotomy over the payload's sign, read off
// the callee's rendered name alone. Nothing makes three user methods agree:
// with `is_negative` and `is_positive` both answering `true`, a body guarded by
// `c.is_negative()` had `!(Ok(c) if c.is_positive())` reported proved under
// certify (`tests/ui/trust/ordering_witness_inconsistent_partial_ord.rs`). No
// compiler fact establishes them consistent, so `_0__value__sign` stays
// ungrounded (`SpecModelUngrounded`), as every other unmodeled spec-model term
// does.

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
    fn place_denotes(
        func: &VerifiableFunction,
        p: &Place,
        cands: &[Place],
        fuel: u32,
    ) -> bool {
        if cands.contains(p) {
            return true;
        }
        if fuel == 0
            || !p.projections.is_empty()
            || crate::local_defs::is_parameter(func, p.local)
            || !crate::place_source_is_stable(func, p.local)
        {
            return false;
        }
        match crate::local_defs::unique_value_def(func, p.local) {
            Some(Rvalue::Ref { mutable: false, place }) => cands.contains(place),
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                place_denotes(func, q, cands, fuel - 1)
            }
            _ => false,
        }
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return false;
    };
    place_denotes(func, p, cands, fuel)
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
    let OrdWitnessTarget::Pair { ty_name, cand_a, cand_b } = target;
    let base = partial_ord_witness_facts(callee, ty_name)?;
    let [a0, a1] = args else {
        return None;
    };
    let fwd = f4_operand_denotes_candidate(func, a0, cand_a, FUEL)
        && f4_operand_denotes_candidate(func, a1, cand_b, FUEL);
    if fwd && base == base.mirrored() {
        return Some(base);
    }
    let rev = f4_operand_denotes_candidate(func, a0, cand_b, FUEL)
        && f4_operand_denotes_candidate(func, a1, cand_a, FUEL);
    match (fwd, rev) {
        (true, false) => Some(base),
        (false, true) => Some(base.mirrored()),
        (true, true) if base == base.mirrored() => Some(base),
        _ => None,
    }
}

/// EVERY whole-local def of `local` — statement assigns AND call dests.
/// `None` (fail-closed) on any projected write, `SetDiscriminant`/`Deinit`,
/// any slot-write channel of `local` (`path_defs::own_storage_write_borrow`: `&mut`,
/// `&raw mut`, and `&raw const` of an owned place — an invisible reseat channel;
/// `&raw const` was missing until 2026-09-30), or when there is no def at all (a
/// parameter — its value is no witness). The SLOT rule: this asks about
/// `local`'s own value, never about memory behind it.
pub(super) fn f4_whole_local_defs<'a>(
    func: &'a VerifiableFunction,
    local: usize,
) -> Option<Vec<F4LocalDef<'a>>> {
    // A PARAMETER is out, defs or no defs: with none its value is no witness, and with
    // some its implicit ENTRY definition is one this scan cannot carry, so the edge
    // facts joined over the visible defs would not cover every value a read can see.
    if local >= 1 && local <= func.body.arg_count {
        return None;
    }
    let mut out = Vec::new();
    let invalid =
        crate::any_local_write_candidate(func, &func.body.blocks, local, |block, item| match item {
            Some(stmt) => match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if place.local == local {
                        if !place.projections.is_empty() {
                            return true;
                        }
                        out.push(F4LocalDef::Rv(rvalue));
                    }
                    // `&raw const local` of its own storage too (2026-10-08 H2:
                    // `path_defs::own_storage_write_borrow`).
                    super::own_storage_write_borrow(func, rvalue)
                        .is_some_and(|borrowed| borrowed.local == local)
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    place.local == local
                }
                _ => false,
            },
            None => {
                if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
                    && dest.local == local
                {
                    if !dest.projections.is_empty() {
                        return true;
                    }
                    out.push(F4LocalDef::Call { callee, args });
                }
                false
            }
        });
    if invalid || out.is_empty() { None } else { Some(out) }
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
pub(super) fn f4_switch_root_local(
    func: &VerifiableFunction,
    discr: &Operand,
    fuel: u32,
) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = discr else {
        return None;
    };
    if !p.projections.is_empty() {
        return None;
    }
    let mut local = p.local;
    for _ in 0..fuel {
        if !crate::local_defs::is_parameter(func, local)
            && crate::place_source_is_stable(func, local)
            && let Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) =
                crate::local_defs::unique_value_def(func, local)
            && q.projections.is_empty()
        {
            local = q.local;
        } else {
            break;
        }
    }
    Some(local)
}

/// A dominating ordering witness guard for `target`: a `SwitchInt` on a
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
    let tp = super::terminator_presence_for(func);
    if !tp.has_switch_int || !tp.has_bare_dest_call {
        return None;
    }
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
        if true_t == false_t {
            continue;
        }
        // Check witness-bool edge facts BEFORE running the three full-CFG
        // `reachable_avoiding` BFS walks: most `SwitchInt`s in a body are not
        // ordering witnesses for `target`.
        let Some(true_facts) = f4_local_edge_facts(func, root, target, true, FUEL) else {
            continue;
        };
        // The guard dominates the aggregate block (every path passes g)…
        if reachable_avoiding_one_contains(func, 0, Some(g), agg_block) {
            continue;
        }
        // …and exactly ONE edge reaches it.
        let true_reaches = reachable_avoiding_one_contains(func, true_t.0, Some(g), agg_block);
        let false_reaches = reachable_avoiding_one_contains(func, false_t.0, Some(g), agg_block);
        let facts = match (true_reaches, false_reaches) {
            (true, false) => true_facts,
            (false, true) => {
                let Some(f) = f4_local_edge_facts(func, root, target, false, FUEL) else {
                    continue;
                };
                f
            }
            _ => continue,
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
    // Read-only, env-gated diagnostics (TRUST_ORDWIT_DEBUG) for the ordering-
    // witness grounding lane — never alters any verdict path.
    static ORDWIT_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let dbg = *ORDWIT_DEBUG.get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_ORDWIT_DEBUG"))
        && (func.def_path.contains("check_chain")
            || func.def_path.contains("check_entailment")
            || func.def_path.contains("check_branch_tree"));
    let OrdWitnessItem::Pair(va, vb) = item;
    if !dbg {
        let ty_a = payload_component_adt_name(func, &[va.index])?;
        let ty_b = payload_component_adt_name(func, &[vb.index])?;
        if ty_a != ty_b || !crate::is_order_consistent_adt(ty_a) {
            return None;
        }
    }
    let Some((kind, variant, ops, agg_block)) =
        resolve_enum_return_aggregate_with_block(func, vc_block, block)
    else {
        if dbg {
            eprintln!("[ORDWIT] {} resolve_enum_return_aggregate=None", func.def_path);
        }
        return None;
    };
    if variant != std_enum_payload_variant(kind) {
        return Some(Vec::new());
    }
    if ops.len() != 1 {
        if dbg {
            eprintln!("[ORDWIT] {} ops.len()={} (!=1)", func.def_path, ops.len());
        }
        return None;
    }
    let (Operand::Copy(sp) | Operand::Move(sp)) = &ops[0] else {
        if dbg {
            eprintln!("[ORDWIT] {} payload op is const/symbolic", func.def_path);
        }
        return None;
    };
    if !sp.projections.is_empty() {
        if dbg {
            eprintln!("[ORDWIT] {} payload op _{} carries projection", func.def_path, sp.local);
        }
        return None;
    }
    let src = sp.local;
    let OrdWitnessItem::Pair(va, vb) = item;
    // Both components must be the SAME non-ref ADT per the DECLARED
    // payload type — the callee allowlist key (`PartialOrd<Self>`
    // could not compare two different types anyway; fail closed).
    let ty_a = payload_component_adt_name(func, &[va.index])?;
    let ty_b = payload_component_adt_name(func, &[vb.index])?;
    if ty_a != ty_b {
        return None;
    }
    // Trust (2026-10-05, ORD-WITNESS-CONSISTENT-1): the type's comparison
    // operators must be ONE consistent total order, and only the compiler can
    // say so. The pin below reads a guard of one operator (`a <= b`) as a fact
    // about the integer order the contract atoms are encoded in, and the
    // contract's own atom names another operator (`d > c`); Rust does not
    // enforce the `PartialOrd` laws, so a user impl whose `le` and `gt` both
    // answer `true` had that `ensures` reported proved under certify, false at
    // run time. `is_order_consistent_adt` admits only the types the compiler
    // found builtin-derived over integer, `bool` and `char` fields (see
    // `trust_verify::order_consistent_adts`); anything else stays ungrounded.
    if !crate::is_order_consistent_adt(ty_a) {
        if dbg {
            eprintln!(
                "[ORDWIT] {} pair type `{ty_a}` is not a compiler-established consistent order",
                func.def_path
            );
        }
        return None;
    }
    let cand_a = component_candidate_places(func, src, &[va.index]);
    let cand_b = component_candidate_places(func, src, &[vb.index]);
    if dbg {
        eprintln!(
            "[ORDWIT] {} pair({},{}) src=_{} cand_a={} cand_b={}",
            func.def_path,
            va.name,
            vb.name,
            src,
            cand_a.len(),
            cand_b.len()
        );
    }
    if cand_a.is_empty() || cand_b.is_empty() {
        return None;
    }
    let target = OrdWitnessTarget::Pair { ty_name: ty_a, cand_a: &cand_a, cand_b: &cand_b };
    let facts = dominating_ordering_witness_guard(func, agg_block.0, &target);
    if dbg {
        eprintln!("[ORDWIT] {} pair guard_matched={}", func.def_path, facts.is_some());
    }
    let facts = facts?;
    let pin = facts.to_formula(
        Formula::var_owned(va.name.clone(), Sort::Int),
        Formula::var_owned(vb.name.clone(), Sort::Int),
    )?;
    Some(vec![pin])
}

/// The GATE for the F4 lane: the covered items (see `ordering_pair_coverage`;
/// the sign lane is retired, see ORD-WITNESS-CONSISTENT-1 above
/// `f4_operand_denotes_candidate`) for which EVERY Return path — the same
/// `Return`-block/predecessor enumeration the pin loop, the discr gate, and
/// the len gate use — yields `Some` pins. Credited names are removed from
/// the per-post ungrounded set so the postcondition survives into the
/// body-aware refutable lane, where `ordering_witness_path_pins` (same
/// resolver) grounds them per path.
pub(super) fn ordering_witness_credited_items(
    func: &VerifiableFunction,
    posts: &[&Formula],
) -> Vec<OrdWitnessItem> {
    if posts.is_empty() {
        return Vec::new();
    }
    let mut items: Vec<OrdWitnessItem> = ordering_pair_coverage(posts)
        .into_iter()
        .filter(|(va, vb)| {
            let Some(ty_a) = payload_component_adt_name(func, &[va.index]) else {
                return false;
            };
            let Some(ty_b) = payload_component_adt_name(func, &[vb.index]) else {
                return false;
            };
            ty_a == ty_b && crate::is_order_consistent_adt(ty_a)
        })
        .map(|(a, b)| OrdWitnessItem::Pair(a, b))
        .collect();
    if items.is_empty() {
        return items;
    }
    let v2_preds = crate::fn_memo::v2_predecessors_or_build(func);
    let return_paths: Vec<(&trust_types::BasicBlock, Vec<&trust_types::BasicBlock>)> = func
        .body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::Return))
        .map(|block| {
            let predecessors = v2_preds.predecessors(func, block.id);
            let vc_blocks = if predecessors.is_empty() { vec![block] } else { predecessors };
            (block, vc_blocks)
        })
        .collect();
    items.retain(|item| {
        for (block, vc_blocks) in &return_paths {
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
