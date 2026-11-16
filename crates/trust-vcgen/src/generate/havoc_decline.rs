// Reclassification of safety obligations whose REFUTATION is an artifact of an
// unmodelled callee return, not a property of the program.
//
// A `Terminator::Call` whose callee has no model writes its destination with
// nothing constraining it: the destination is a free variable of the violation
// formula. The solver then answers SAT by *choosing* that value, and the row is
// reported REFUTED with a "counterexample" that no execution can produce — the
// census recorded `max(x, 1) = 0` alongside `x = 0`. An unmodelled callee means
// "I do not know", which is UNKNOWN; reporting it as a counterexample is the
// verifier accusing correct code.
//
// This module reclassifies exactly that shape to `VcKind::UnsupportedMir`, which
// `discharge_body_vcs` preclassifies to `Unknown` and never dispatches. It adds
// NO fact and states NOTHING about any callee's return value: the only thing it
// can do to a row is turn it into an Unknown, so it can never produce a proof.
//
// The demotion goes through `unsupported::demote_to_unsupported_mir` so the
// declined row carries the SAME fail-closed (satisfiable) violation formula as
// every other `UnsupportedMir` emitter. That is not cosmetic: `UnsupportedMir`
// has `proof_level() == L0Safety`, so any consumer that selects obligations by
// proof level rather than by kind admits the row and then reads only its
// formula, and an UNSAT one means "no violation". `trust_clean::whole_program`'s
// kernel-discharge gates now refuse a declined row by KIND first, so there the
// polarity is a second defence; for a direct-solver caller it is the only one.
//
// The decline fires only when all four conditions hold, and each one exists to
// stop a different way of losing a decision the verifier can actually make:
//
//   1. the variable's ONLY value source in this body is a `Call` destination
//      (MIR-derived — a parameter or an `Assign`-defined local is never a
//      candidate, which is what keeps an all-local real bug refutable) — or, since
//      2026-09-16 (round A5), the `Some`-payload extraction of an `Option` local
//      whose only writes are such calls to std `Iterator::next`
//      (`is_unmodelled_next_payload`): one `Use` further down the same channel;
//   2. it survives substitution of the hypothesis definitions into the recorded
//      raw violation, i.e. the obligation genuinely depends on it;
//   3. NOTHING in the hypotheses pins it (see `conjunct_restricts`), so a
//      modelled callee or a program guard keeps its row exactly as it is today.
//      The two models measured to reach this seam on the fixture corpus are the
//      `leading_zeros` intrinsic's `0..=32` pin (`hv_div_leading_zeros` keeps its
//      refutation, `hv_idx_leading_zeros` keeps its proof) and the
//      `mem::size_of`/`align_of` layout facts (the four `hv_{div,idx}_*_of`
//      rows prove). NB the `Ord::min`/`max` model is NOT one of them: the
//      compiler emits `core::cmp::max::<u32>` for a monomorphized free-function
//      call and `call_facts::ord_method` does not recognize that spelling — see
//      `ord_method_spelling_tests::turbofish_free_function_spelling_is_not_recognized_today`;
//   4. moving that ONE variable across its declared type range flips the
//      obligation between true and false (see `havoc_flips_obligation`), with
//      every other variable eliminated. That is the operational meaning of "the
//      answer depends on a value I do not know". An obligation that is false at
//      every probed value (`arr[unmodelled() % 4]`) keeps its row and still
//      proves; one that is TRUE at every probed value is a violation whatever
//      the callee returns, and also keeps its row.

use super::*;

/// Cap on the number of top-level conjuncts a formula may have before the pass
/// declines to analyse it. The pinning scan is quadratic in this count (each
/// conjunct is tested against every other for the dead-variable side condition),
/// and giving up means "leave the row exactly as it is", so the cap can only
/// cost precision.
const MAX_CONJUNCTS: usize = 512;

/// Cap on substitution rounds when folding hypothesis definitions into the raw
/// violation. Definitions form a DAG in practice (MIR temps), so a handful of
/// rounds reaches the fixpoint; the cap bounds the pathological case.
const MAX_SUBST_ROUNDS: usize = 8;

/// Node cap on the folded obligation. Substituting a definition replaces a leaf
/// by a whole term, so a chain of them can grow the formula multiplicatively;
/// past this the fold is abandoned and the row keeps its current classification.
const MAX_FOLDED_NODES: usize = 4096;

/// Node count of `f`.
fn formula_node_count(f: &Formula) -> usize {
    let mut count = 0usize;
    trust_types::visit_formula_nodes(f, &mut |_| count += 1);
    count
}

/// The base var name of a formula variable — the `#`-version suffix stripped, so
/// `_2#s0_t` and `_2` compare equal. Mirrors the base-name convention used by
/// `conjoin_local_type_ranges_excluding` and `block_def_subject`.
fn var_full_and_base_str(f: &Formula) -> Option<(&str, &str)> {
    let name = match f {
        Formula::Var(name, _) => name.as_str(),
        Formula::SymVar(sym, _) => sym.as_str(),
        _ => return None,
    };
    let base = name.split('#').next().unwrap_or(name);
    Some((name, base))
}

/// Every `(full_name, base_name)` variable occurrence in `f`.
fn collect_vars(f: &Formula, out: &mut Vec<(String, String)>) {
    trust_types::visit_formula_nodes(f, &mut |node| {
        if let Some((name, base)) = var_full_and_base_str(node) {
            out.push((name.to_owned(), base.to_owned()));
        }
    });
}

/// Whether `f` mentions the base var name `base` anywhere.
fn mentions_base(f: &Formula, base: &str) -> bool {
    trust_types::any_formula_node(f, &mut |node| {
        var_full_and_base_str(node).is_some_and(|(_, b)| b == base)
    })
}

/// Flatten the top-level `And` chain of `f` into its conjuncts.
fn flatten_conjuncts<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
    if let Formula::And(parts) = f {
        for p in parts {
            flatten_conjuncts(p, out);
        }
    } else {
        out.push(f);
    }
}

/// The crate name of a def path — the segment before the first `::`.
fn crate_of(def_path: &str) -> &str {
    def_path.split("::").next().unwrap_or(def_path)
}

/// Type names that are concrete whatever the instantiation, plus the keywords a
/// rendered path may contain inside its angle brackets.
fn is_concrete_path_token(tok: &str) -> bool {
    matches!(
        tok,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f16"
            | "f32"
            | "f64"
            | "f128"
            | "bool"
            | "char"
            | "str"
            | "impl"
            | "dyn"
            | "as"
            | "const"
            | "mut"
            | "true"
            | "false"
    ) || tok.bytes().all(|b| b.is_ascii_digit())
}

/// Whether every generic argument spelled inside `callee`'s angle brackets is
/// CONCRETE — i.e. the callee is monomorphic at this call site.
///
/// `trust-mir-extract` renders a callee path with fully-qualified names for
/// every resolved type (`r3_generic_alias_tmethod_index::Feed`,
/// `core::convert::Into<usize>`), so an identifier inside angle brackets that is
/// neither a primitive/keyword nor part of a `::`-path is a GENERIC PARAMETER
/// still to be substituted — `core::mem::size_of::<T>`. That distinction is the
/// whole point here: `size_of::<T>()` is not an unmodelled deterministic
/// function, it is a value the CALLER of this generic function chooses, so its
/// obligation is genuinely refutable (there is a `T` that violates it) and must
/// keep its refutation. Fails closed: anything unrecognised reads as generic.
fn callee_path_is_monomorphic(callee: &str) -> bool {
    let bytes = callee.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'<' {
            depth += 1;
            i += 1;
            continue;
        }
        if c == b'>' {
            depth -= 1;
            i += 1;
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            if depth > 0 {
                let tok = &callee[start..i];
                let path_tail = start >= 1 && bytes[start - 1] == b':';
                let path_head = i + 1 < bytes.len() && bytes[i] == b':' && bytes[i + 1] == b':';
                if !path_tail && !path_head && !is_concrete_path_token(tok) {
                    return false;
                }
            }
            continue;
        }
        i += 1;
    }
    true
}

/// Whether `callee` is a function whose BODY this compilation does not have and
/// whose path carries no unsubstituted generic parameter.
///
/// A SAME-CRATE callee is excluded even though its result is havocked exactly
/// the same way: its body IS available, so the gap is a missing summary, not the
/// modularity boundary — and the corpus pins that distinction
/// (`mutant/contract_skip_ensures_launder` indexes `a[idx(n)]` with a same-crate
/// `idx` and must keep refuting; deleting this exclusion was measured to turn
/// that row into a decline, i.e. to let the mutant survive). The
/// `same_crate_callee_is_not_reclassified` fixture kills the same deletion. The
/// crate name is tested for CONTAINMENT, not
/// just as a prefix, so a qualified path that reaches back into this crate
/// (`<<S as this_crate::Feed>::Item as core::convert::Into<usize>>::into`) is
/// excluded too.
fn callee_is_foreign_monomorphic(func: &VerifiableFunction, callee: &str) -> bool {
    let home = crate_of(&func.def_path);
    if home.is_empty() || callee.contains(home) {
        return false;
    }
    callee_path_is_monomorphic(callee)
}

/// Trust (2026-10-16, S3): which unmodelled calls' `Option` results make their
/// `Some` payload a decline candidate (see [`unmodelled_next_payload_fields`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PayloadSources {
    /// Foreign `Iterator::next` only — the L0 reclassification pass, which rewrites
    /// rows.
    IteratorNext,
    /// Any foreign monomorphic value call — the generic refutation scope, which
    /// only withholds a counterexample.
    AnyForeignValueCall,
}

/// Trust (2026-10-16, S3): [`callee_is_foreign_monomorphic`] for a VALUE-returning
/// call whose `Option` result is read through its `Some` payload, with two spellings
/// that do not make the callee's value a caller's choice read as concrete:
///
/// * a LIFETIME (`'_`, `'a`) — regions are erased before execution and never change
///   a returned value; `<core::slice::iter::Iter<'_, u8> as Iterator>::position`
///   would otherwise read as generic on its `_` token;
/// * a CLOSURE type (`{closure@file.rs:L:C: L:C}`) — a concrete, already
///   monomorphized type at this call site; its span spells a FILE path that, in a
///   crate named after its file, would otherwise contain the home crate's name.
///
/// Everything else — the home-crate containment test and every other generic
/// argument — is exactly [`callee_is_foreign_monomorphic`]'s. Used only to admit
/// a payload as a decline CANDIDATE, which can turn a row into an Unknown and never
/// into a proof.
fn callee_is_foreign_monomorphic_value_call(func: &VerifiableFunction, callee: &str) -> bool {
    if !callee.contains('\'') && !callee.contains('{') {
        return callee_is_foreign_monomorphic(func, callee);
    }
    let mut normalized = String::with_capacity(callee.len());
    let mut chars = callee.char_indices().peekable();
    while let Some((idx, c)) = chars.next() {
        match c {
            '\'' => {
                // A lifetime: drop the tick and its identifier.
                while chars.peek().is_some_and(|(_, n)| n.is_ascii_alphanumeric() || *n == '_') {
                    chars.next();
                }
            }
            '{' => {
                // A `{closure@..}` / `{coroutine@..}` type: one concrete placeholder.
                // Anything else in braces (a fn-item `{path}`) is kept verbatim.
                let after_brace = &callee[idx + 1..];
                let rest = after_brace.split('}').next().unwrap_or(after_brace);
                if rest.starts_with("closure@") || rest.starts_with("coroutine@") {
                    let close_end = idx + 1 + rest.len();
                    while chars.peek().is_some_and(|(next_idx, _)| *next_idx <= close_end) {
                        chars.next();
                    }
                    normalized.push_str("()");
                } else {
                    normalized.push(c);
                }
            }
            _ => normalized.push(c),
        }
    }
    callee_is_foreign_monomorphic(func, &normalized)
}

/// Locals whose ONLY value source in this body is the destination of a call into
/// a FOREIGN, MONOMORPHIC callee, keyed by base var name and carrying the
/// local's declared integer `(width, signed)`.
///
/// A local qualifies only when nothing else can write it: no `Assign` statement
/// anywhere names it (whole-local or projected), it is not a parameter, and it
/// is neither mutably borrowed nor address-taken — the two channels through
/// which a callee or a later store could give it a value the def scan cannot
/// see. Restricting to fixed-width integer locals is what the probe in
/// [`havoc_flips_obligation`] needs: the declared type is the range the value
/// must lie in, and it is a fact of the input program's type, not an assumption
/// about any callee.
pub(super) fn call_only_int_dest_locals(
    func: &VerifiableFunction,
) -> FxHashMap<String, (u32, bool)> {
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return FxHashMap::default();
    }
    let n_locals = func.body.locals.len();
    let arg_count = func.body.arg_count;
    let has_candidate = func.body.blocks.iter().any(|block| {
        matches!(
            &block.terminator,
            Terminator::Call { func: callee, dest, target: Some(_), .. }
                if dest.projections.is_empty()
                    && dest.local > arg_count
                    && dest.local < n_locals
                    && crate::local_ty_ref(func, dest.local)
                        .is_some_and(|ty| ty.int_width().is_some())
                    && callee_is_foreign_monomorphic(func, callee)
        )
    });
    if !has_candidate {
        return FxHashMap::default();
    }
    let mut is_call_dest = vec![false; n_locals];
    let mut disqualified = vec![false; n_locals];
    let mark = |slot: &mut Vec<bool>, local: usize| {
        if local < slot.len() {
            slot[local] = true;
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                mark(&mut disqualified, place.local);
                // A mutable borrow / raw pointer to the local is a write channel
                // the whole-local def scan cannot see (`let p = &mut d; *p = e`),
                // exactly as `is_single_static_assignment` argues.
                if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) = rvalue
                {
                    mark(&mut disqualified, bp.local);
                }
            }
        }
        match &block.terminator {
            Terminator::Call { func: callee, dest, target: Some(_), .. } => {
                if dest.projections.is_empty() && callee_is_foreign_monomorphic(func, callee) {
                    mark(&mut is_call_dest, dest.local);
                } else {
                    mark(&mut disqualified, dest.local);
                }
            }
            // Any other terminator that writes a place makes the local's value
            // ambiguous for this pass; leave it out.
            Terminator::Call { dest, .. } => mark(&mut disqualified, dest.local),
            _ => {}
        }
    }
    let mut out: FxHashMap<String, (u32, bool)> = FxHashMap::default();
    for decl in &func.body.locals {
        let i = decl.index;
        if i >= func.body.locals.len() {
            continue;
        }
        // Parameters carry their own entry hypotheses and are never "only ever
        // written by a call" from the caller's point of view.
        if i >= 1 && i <= func.body.arg_count {
            continue;
        }
        let Some(width) = decl.ty.int_width() else {
            continue;
        };
        if !is_call_dest[i] || disqualified[i] {
            continue;
        }
        out.insert(place_to_var_name(func, &Place::local(i)), (width, decl.ty.is_signed()));
    }
    out
}

/// Trust: 2026-09-16 (round A5) — THE `Some`-PAYLOAD OF AN UNMODELLED `Iterator::next`.
///
/// The payload FIELD variables (`_o@1.0`, the formula name of `((_o as Some).0)`) of
/// every integer local `p` whose ONE whole write is `p = ((o as Some).0)` (or the
/// `enumerate` index `((o as Some).0).0`), where nothing else touches `p`
/// (`iterator_yield::payload_carries_global_fact` = `local_defs::is_single_static_assignment`)
/// and `o`'s writes on EVERY channel are `Iterator::next` calls into FOREIGN,
/// MONOMORPHIC callees (`local_defs::value_calls`: no `Assign`, projected store,
/// `SetDiscriminant`, alias or unlocatable write beside them). Keyed by the field's
/// base var name, carrying the payload's base var name — its ALIAS in the formula, `p
/// = field` being `p`'s one definition — and the declared integer `(width, signed)`.
///
/// The field is what the module banner's condition 1 names, one projection down: a
/// value whose only source in this body is an unmodelled callee's return. The
/// candidate is the FIELD, not `p`, because the fold in
/// [`HavocTables::reclassify`] substitutes `p`'s one definition into the raw
/// violation and the obligation is then stated over the field; `p` is carried as the
/// alias so that a hypothesis pinning `p` (a yield fact `start <= p < end`, a program
/// guard) is read as pinning the field, and the one equation `p = field` is read as
/// what it is — a definition — rather than as a constraint.
///
/// The row this exists for: `let o = if c { small.next() } else { big.next() }; if let
/// Some(i) = o { a[i] }` with `small = 0..5`, `big = 2..5`, `a: &[u8; 5]` — a CORRECT
/// program whose entrance the yield tracers DECLINE when either receiver does not
/// trace (both trace today and the JOINED fact proves it; with `big.nth(0)` before the
/// `if`, `big`'s conduit feeds `nth`, the join withholds, and this pass is what stands
/// between the row and a refutation over the unmodelled payload — the previous round's
/// measured `Failed` with `_8 = 1`, a value no execution reaches). Likewise `let mut n
/// = 5; for i in 0..n { n = 100; a[i] }`, whose range end no longer resolves. When the
/// tracers DO mint a fact on the payload — the single-receiver `for` loop, the joined
/// two-`next` witness `two_next_if` with `50..100` — that fact PINS the alias
/// (condition 3) and the row keeps its verdict: `two_next_if` stays refuted, on a
/// witness the program realises.
///
/// The deref'd payload of a by-reference iterator (`for &x in idxs { a[x] }`, `x = *((o
/// as Some).0)`) is NOT this shape and keeps its row: its value is an element of the
/// INPUT, and a model over it is an execution.
pub(super) fn unmodelled_next_payload_fields(
    func: &VerifiableFunction,
    sources: PayloadSources,
) -> FxHashMap<String, (String, u32, bool)> {
    let mut out: FxHashMap<String, (String, u32, bool)> = FxHashMap::default();
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return out;
    }
    if matches!(sources, PayloadSources::AnyForeignValueCall)
        && !func.body.locals.iter().any(|decl| {
            matches!(&decl.ty, trust_types::Ty::Adt { name, .. } if name.ends_with("::option::Option"))
        })
    {
        return out;
    }
    let int_decl = |local: usize| -> Option<(u32, bool)> {
        if local >= 1 && local <= func.body.arg_count {
            return None;
        }
        let ty = crate::local_ty_ref(func, local)?;
        Some((ty.int_width()?, ty.is_signed()))
    };
    // The `Option` locals whose writes, on every channel, are the calls `sources`
    // admits — the join question, memoised per local.
    //
    // Trust (2026-10-16, S3): [`PayloadSources::IteratorNext`] is the L0 pass's
    // historical set, `Iterator::next` only, recognised BY NAME
    // (`iterator_yield::callee_is_iterator_next`); the L0 pass REWRITES rows, and
    // widening what it rewrites moves verdicts (an unauthenticated `position`'s
    // genuine `i + 1` refutation, the `Option<usize>` payload rows of the corpus
    // fixtures), so it keeps that set. [`PayloadSources::AnyForeignValueCall`] is
    // the generic refutation scope's: nothing about the argument is specific to
    // `next` — the payload of ANY foreign call's `Option` result is a value whose
    // only source in this body is a callee this compilation has no body for.
    // `Iterator::position` over a reseated slice (`rest = &rest[k + 1..]`,
    // aterm-parser `dispatch.rs:751-752`) was refuted with `Some(1)` beside
    // `rest.len() == 0`, a payload no execution returns. A MODEL of such a callee
    // does not need to be named: whatever it writes about the payload is a
    // hypothesis conjunct over the field or its alias (the `position`/`next` yield
    // facts, a `checked_*` result equation), and conditions 2-3 of the module banner
    // keep the row — folded away by a definition, or pinned by a fact. The scope
    // only WITHHOLDS a counterexample, so this set can turn a Failed into a held
    // Unknown and nothing else.
    let option_decl = |o: usize| {
        crate::local_ty_ref(func, o).is_some_and(|ty| {
            matches!(ty, trust_types::Ty::Adt { name, .. } if name.ends_with("::option::Option"))
        })
    };
    let has_source_call = func.body.blocks.iter().any(|block| match &block.terminator {
        Terminator::Call { func: callee, dest, target: Some(_), .. }
            if dest.projections.is_empty() =>
        {
            match sources {
                PayloadSources::IteratorNext => {
                    super::iterator_yield::callee_is_iterator_next(callee)
                        && callee_is_foreign_monomorphic(func, callee)
                }
                PayloadSources::AnyForeignValueCall => {
                    option_decl(dest.local)
                        && callee_is_foreign_monomorphic_value_call(func, callee)
                }
            }
        }
        _ => false,
    });
    if !has_source_call {
        return out;
    }
    let mut next_options: FxHashMap<usize, bool> = FxHashMap::default();
    let mut is_unmodelled_next_option = |o: usize| -> bool {
        *next_options.entry(o).or_insert_with(|| match sources {
            PayloadSources::IteratorNext => {
                crate::local_defs::value_calls(func, o).is_some_and(|calls| {
                    calls.iter().all(|t| {
                        matches!(
                            t,
                            Terminator::Call { func: callee, dest, target: Some(_), .. }
                                if dest.projections.is_empty()
                                    && super::iterator_yield::callee_is_iterator_next(callee)
                                    && callee_is_foreign_monomorphic(func, callee)
                        )
                    })
                })
            }
            PayloadSources::AnyForeignValueCall => {
                option_decl(o)
                    && crate::local_defs::value_calls(func, o).is_some_and(|calls| {
                        !calls.is_empty() && calls.iter().all(|t| {
                            matches!(
                                t,
                                Terminator::Call { func: callee, dest, target: Some(_), .. }
                                    if dest.projections.is_empty()
                                        && callee_is_foreign_monomorphic_value_call(func, callee)
                            )
                        })
                    })
            }
        })
    };
    let is_whole_local = |op: &Operand, local: usize| -> bool {
        matches!(op, Operand::Copy(q) | Operand::Move(q) if q.local == local && q.projections.is_empty())
    };
    for block in &func.body.blocks {
        // Trust: 2026-09-16 (round A8) — THE REACHING DEFINITION WITHIN A BLOCK. The
        // payload locals whose LAST write so far in this block is the extraction from an
        // unmodelled-`next` Option, each with its field's var name. The extraction is
        // recorded for EVERY such local — a `mut` binding with a later second write
        // included — because the FIELD is what the candidate is, and the field stays a
        // call-only value whatever the alias does afterwards. Round A5 required the
        // alias to pass `payload_carries_global_fact` first; that made a gate miss
        // (`for mut i in 0..5 { i += 1; a[i] }` on `[u8; 6]`, a CORRECT program whose
        // payload has two writes) a refutation with an unrealisable witness — the
        // pristine driver proved it, and the round's own banner promised that refusing
        // the fact is a decline to Unknown, never an invented refutation
        // (`a8_ctl_incr_six_*`).
        let mut carrying: FxHashMap<usize, String> = FxHashMap::default();
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else {
                // Any other write or alias of a carried local ends its carry.
                if !carrying.is_empty() {
                    carrying.retain(|&p, _| {
                        matches!(stmt.local_write(p), trust_types::LocalWrite::Untouched)
                            && !crate::stmt_escapes_local(func, stmt, p)
                    });
                }
                continue;
            };
            // A DERIVED candidate: `d = p ± c` / `d = Checked(p ± c)` where `p` carries the
            // field and `c` is a constant, `d` written once on every channel. Its
            // value is a function of the callee's return and a constant alone; the
            // block encoder's loop-join weakening drops `d`'s definition from the VCs of
            // the blocks after the checked add, so the increment idiom's index
            // (`_9 = move (_10.0)`) reaches its bounds obligation as a free variable
            // whose only source is the unmodelled `next`. Registered before the carry
            // update so `p`'s own reaching definition is the one read here.
            if !carrying.is_empty()
                && dest.projections.is_empty()
                && let Rvalue::BinaryOp(op, x, y) | Rvalue::CheckedBinaryOp(op, x, y) = rvalue
                && matches!(op, trust_types::BinOp::Add | trust_types::BinOp::Sub)
            {
                let carried = carrying.keys().copied().find(|&p| {
                    (is_whole_local(x, p) && matches!(y, Operand::Constant(_)))
                        || (is_whole_local(y, p) && matches!(x, Operand::Constant(_)))
                });
                if let Some(p) = carried
                    && let Some((width, signed)) = int_decl(p)
                    && crate::local_defs::unique_value_def(func, dest.local).is_some()
                {
                    let derived = if matches!(rvalue, Rvalue::CheckedBinaryOp(..)) {
                        std::borrow::Cow::Owned(Place {
                            local: dest.local,
                            projections: vec![trust_types::Projection::Field(0)],
                        })
                    } else {
                        std::borrow::Cow::Borrowed(dest)
                    };
                    let name = place_to_var_name(func, &derived);
                    // The alias is the payload local the derived value is written
                    // back into (`p = move (d.0)`), when that is the next write of `p`
                    // in this block; otherwise the candidate is its own alias.
                    let alias = block.stmts[stmt_idx + 1..]
                        .iter()
                        .find_map(|s| match s {
                            Statement::Assign {
                                place: q,
                                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                                ..
                            } if q.projections.is_empty() && src == derived.as_ref() => {
                                Some(place_to_var_name(func, q))
                            }
                            _ => None,
                        })
                        .unwrap_or_else(|| name.clone());
                    out.entry(name).or_insert((alias, width, signed));
                }
            }
            // The carry update: this statement's destination ends any carry of its
            // local, and an alias it hands out ends the carry of the aliased local.
            if !carrying.is_empty() {
                carrying.retain(|&p, _| {
                    matches!(stmt.local_write(p), trust_types::LocalWrite::Untouched)
                        && !crate::stmt_escapes_local(func, stmt, p)
                });
            }
            // Trust: 2026-09-16 (round A9) — THE CARRY THROUGH A WHOLE-LOCAL COPY.
            // rustc spells `i = i + 1` at `-Copt-level=0` as `_10 = copy _9; _11 =
            // AddWithOverflow(move _10, 1)` — one `Use` copy between the payload and
            // the checked add — where `i += 1` reads the payload directly. The carry
            // stopped at the copy, the derived-candidate arm above saw no carried
            // operand, and `for mut i in 0..5usize { i = i + 1; t += a[i] }` on
            // `[u8; 6]` (`ctl_plus_one_six`, CORRECT) was REFUTED on the free `_10`
            // while its `+=` twin (`ctl_incr_six`) declined — a decision made by
            // spelling. A whole-local copy of a carried local into a local written
            // once on every channel holds the field's value exactly as its source
            // does, so it joins the carry with the same field. Registered AFTER the
            // retain (the copy's own destination is a fresh carrier, never a reseat of
            // one). The copy IS a candidate in its own name, with the field as its
            // alias: the block encoder keeps the checked add's definition `_11.0 =
            // _10 + 1` in the bounds VC but drops the copy `_10 = i` with the
            // loop-join weakening, so the fold reaches `_10` and stops there — a local
            // written once, whose one value is the field (MEASURED on
            // `ctl_plus_one_six` at `-O0`: `folded = Ge(Add(_10, 1), 6)`).
            if !carrying.is_empty()
                && dest.projections.is_empty()
                && let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue
                && src.projections.is_empty()
                && let Some(field) = carrying.get(&src.local).cloned()
                && let Some((width, signed)) = int_decl(dest.local)
                && crate::local_defs::unique_value_def(func, dest.local).is_some()
            {
                out.entry(place_to_var_name(func, dest)).or_insert((field.clone(), width, signed));
                carrying.insert(dest.local, field);
                continue;
            }
            // The extraction itself: `p = ((o as Some).0)` / the enumerate index.
            if !dest.projections.is_empty() {
                continue;
            }
            let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else { continue };
            if !(super::iterator_yield::is_some_payload_projection(&src.projections)
                || super::iterator_yield::is_enumerate_index_projection(&src.projections))
            {
                continue;
            }
            let Some((width, signed)) = int_decl(dest.local) else { continue };
            if !is_unmodelled_next_option(src.local) {
                continue;
            }
            let field = place_to_var_name(func, src);
            let alias = place_to_var_name(func, dest);
            carrying.insert(dest.local, field.clone());
            // Trust: 2026-09-16 (round A8) — a payload local whose ONE write on every
            // channel is this extraction (`payload_carries_global_fact`) IS the field at
            // every read, so it is a candidate in its own name too: the block encoder's
            // loop-join weakening drops the extraction `i = ((o as Some).0)` from the VC
            // of the guarded read that follows the bounds assert (`(*s)[i]` after
            // `assert(i < len)`), and without the definition the fold cannot reach the
            // field — `let mut s: &[u8] = a; for i in 0..s.len() { s = b; s[i] }` (both
            // arrays of length 5, correct) kept that row refuted on a free `i`
            // (`a8_ctl_unsize_*`). The two names are each other's alias, so the one
            // equation between them is read as the definition it is in either
            // orientation.
            if super::iterator_yield::payload_carries_global_fact(func, dest.local) {
                out.entry(alias.clone()).or_insert((field.clone(), width, signed));
            }
            out.entry(field).or_insert((alias, width, signed));
        }
    }
    out
}

/// Whether `conj` is exactly the alias DEFINITION `Var(alias) = Var(field)` (either
/// orientation) — the one equation between a payload and its field that
/// [`unmodelled_next_payload_fields`] vouches for, and which therefore constrains
/// neither side.
fn is_alias_definition(conj: &Formula, alias: &str, field: &str) -> bool {
    let Formula::Eq(a, b) = conj else { return false };
    let bases = (var_full_and_base_str(a), var_full_and_base_str(b));
    match bases {
        (Some((_, x)), Some((_, y))) => (x == alias && y == field) || (x == field && y == alias),
        _ => false,
    }
}

/// Whether `conj` is exactly a declared-type range bound on `base` — a fact
/// implied by the local's Rust type and satisfied by every inhabitant of it, so
/// it pins no value. Recognises both spellings the generator emits:
/// `input_range_constraint`'s `And([Le(min, v), Le(v, max)])` and the
/// argument-range lane's `Ge(v, min)` / `Le(v, max)`.
///
/// ORIENTATION IS LOAD-BEARING. Only the four vacuous readings count — `min<=v`,
/// `v<=max`, `v>=min`, `max>=v`. The REVERSED comparisons against the same two
/// literals say something entirely different: `max<=v` and `min>=v` each pin `v`
/// to an endpoint, and treating one as inert would let a genuinely constrained
/// value be mistaken for a free havoc.
fn is_declared_type_range_bound(conj: &Formula, base: &str, width: u32, signed: bool) -> bool {
    let is_var = |f: &Formula| var_full_and_base_str(f).is_some_and(|(_, b)| b == base);
    match conj {
        Formula::And(parts) => {
            !parts.is_empty()
                && parts.iter().all(|p| is_declared_type_range_bound(p, base, width, signed))
        }
        // `min <= v` / `v <= max`
        Formula::Le(a, b) => {
            (is_var(b) && **a == crate::range::type_min_formula(width, signed))
                || (is_var(a) && **b == crate::range::type_max_formula(width, signed))
        }
        // `v >= min` / `max >= v`
        Formula::Ge(a, b) => {
            (is_var(a) && **b == crate::range::type_min_formula(width, signed))
                || (is_var(b) && **a == crate::range::type_max_formula(width, signed))
        }
        _ => false,
    }
}

/// Trust: 2026-09-16 (round A9) — whether `conj` is the block encoder's RESULT RANGE
/// of a checked add/sub on `base`: `MIN_T <= base ± c` / `base ± c <= MAX_T` (either
/// orientation, the `And` wrapper included) with `c` a constant and the bounds the
/// declared type's — the fact `guards` pushes for every `CheckedBinaryOp` result
/// before its `dest == lhs ± rhs` equality. It is the no-overflow fact the preceding
/// assert established, not a program guard on `base`: it excludes at most the
/// endpoint of the type range. rustc spells `i = i + 1` at `-Copt-level=0` through a
/// single-write copy (`_10 = copy i; _11 = AddWithOverflow(move _10, 1)`), so the
/// checked add's definition — and this range with it — SURVIVE the loop-join
/// weakening into the bounds VC, where they mention the carried copy `_10`; the `+=`
/// spelling reads the loop-carried payload directly and the weakening drops both.
/// Read as a pin, this one fact was the whole difference between `ctl_plus_one_six`
/// (REFUTED on the free `_10`) and `ctl_incr_six` (declined): a decision made by
/// spelling. It is inert for the PINNING question — but not for the PROBE, which
/// must not witness a flip at the one value it excludes: [`havoc_flips_obligation`]
/// takes it as a filter and skips the probe points it rules out.
fn is_checked_op_result_range(conj: &Formula, base: &str, width: u32, signed: bool) -> bool {
    let is_var = |f: &Formula| var_full_and_base_str(f).is_some_and(|(_, b)| b == base);
    let is_const = |f: &Formula| matches!(f, Formula::Int(_) | Formula::UInt(_));
    let is_offset_of_base = |f: &Formula| match f {
        Formula::Add(a, b) | Formula::Sub(a, b) => {
            (is_var(a) && is_const(b)) || (is_const(a) && is_var(b))
        }
        _ => false,
    };
    match conj {
        Formula::And(parts) => {
            !parts.is_empty()
                && parts.iter().all(|p| is_checked_op_result_range(p, base, width, signed))
        }
        // `min <= base ± c` / `base ± c <= max`
        Formula::Le(a, b) => {
            (is_offset_of_base(b) && **a == crate::range::type_min_formula(width, signed))
                || (is_offset_of_base(a) && **b == crate::range::type_max_formula(width, signed))
        }
        // `base ± c >= min` / `max >= base ± c`
        Formula::Ge(a, b) => {
            (is_offset_of_base(a) && **b == crate::range::type_min_formula(width, signed))
                || (is_offset_of_base(b) && **a == crate::range::type_max_formula(width, signed))
        }
        _ => false,
    }
}

/// The variable a conjunct DEFINES, when the conjunct is an equation
/// `Var(n) = rhs` (or `rhs = Var(n)`) whose right-hand side does not mention
/// `n`. This is the MIR-temp definition shape: `_3 = (_2 == 0)`.
fn defined_var_str(conj: &Formula) -> Option<&str> {
    let Formula::Eq(a, b) = conj else {
        return None;
    };
    if let Some((_, base)) = var_full_and_base_str(a)
        && !mentions_base(b, base)
    {
        return Some(base);
    }
    if let Some((_, base)) = var_full_and_base_str(b)
        && !mentions_base(a, base)
    {
        return Some(base);
    }
    None
}

/// Whether hypothesis conjunct `conj` RESTRICTS the admissible values of `base`.
///
/// Three shapes provably restrict nothing, and all three are ubiquitous in the
/// generated formulas:
///
///   * a declared-type range bound on `base` itself — every inhabitant of the
///     type satisfies it, so it excludes no value (see
///     [`is_declared_type_range_bound`]);
///   * `Var(f) = rhs` where `f` occurs in no OTHER hypothesis conjunct. `f` is a
///     dead MIR temp: whatever value `base` takes, the equation is satisfied by
///     giving `f` the matching value, so it constrains `base` not at all. (The
///     divisor-is-zero flag `_3 = (_2 == 0)` is this shape: `_3` appears only in
///     the obligation, which is excluded from the hypotheses by the caller.)
///   * `Or([.., Var(f) = rhs, ..])` with the same side condition — the checked-op
///     semantics `(overflow) or (_0 = _2 + 1)`. That disjunct alone is
///     satisfiable for every `base`, so the whole disjunction is.
///
/// Anything else that mentions `base` counts as pinning it — a program guard, a
/// modelled callee's result bound, an intrinsic's value semantics. Misjudging in
/// that direction only leaves a row exactly as it is today.
fn conjunct_restricts(
    conj: &Formula,
    base: &str,
    width: u32,
    signed: bool,
    dead: &dyn Fn(&str) -> bool,
) -> bool {
    if !mentions_base(conj, base) {
        return false;
    }
    if is_declared_type_range_bound(conj, base, width, signed) {
        return false;
    }
    if let Some(def) = defined_var_str(conj)
        && def != base
        && dead(def)
    {
        return false;
    }
    if let Formula::Or(disjuncts) = conj
        && disjuncts
            .iter()
            .any(|d| defined_var_str(d).is_some_and(|def| def != base && dead(def)))
    {
        return false;
    }
    true
}

/// A concrete value the partial evaluator can carry.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Val {
    B(bool),
    I(i128),
}

/// Evaluate `f` with each variable of `env` (matched by FULL name) bound to its value
/// and NO other variable assigned. `None` means "not decided here" — a free variable,
/// an unsupported node, or an arithmetic overflow/zero-division in the evaluator
/// itself. Every `None` propagates, so the caller falls back to leaving the row
/// unchanged.
fn eval(f: &Formula, env: &[(&str, i128)]) -> Option<Val> {
    let int = |x: &Formula| match eval(x, env) {
        Some(Val::I(v)) => Some(v),
        _ => None,
    };
    let boolean = |x: &Formula| match eval(x, env) {
        Some(Val::B(v)) => Some(v),
        _ => None,
    };
    let lookup = |name: &str| env.iter().find(|(n, _)| *n == name).map(|(_, k)| Val::I(*k));
    match f {
        Formula::Bool(b) => Some(Val::B(*b)),
        Formula::Int(v) => Some(Val::I(*v)),
        Formula::UInt(v) => i128::try_from(*v).ok().map(Val::I),
        Formula::Var(name, _) => lookup(name),
        Formula::SymVar(sym, _) => lookup(sym.as_str()),
        Formula::Not(a) => boolean(a).map(|v| Val::B(!v)),
        Formula::And(parts) => {
            let mut acc = true;
            for p in parts {
                acc &= boolean(p)?;
            }
            Some(Val::B(acc))
        }
        Formula::Or(parts) => {
            let mut acc = false;
            for p in parts {
                acc |= boolean(p)?;
            }
            Some(Val::B(acc))
        }
        Formula::Implies(a, b) => Some(Val::B(!boolean(a)? || boolean(b)?)),
        Formula::Eq(a, b) => match (eval(a, env)?, eval(b, env)?) {
            (Val::I(x), Val::I(y)) => Some(Val::B(x == y)),
            (Val::B(x), Val::B(y)) => Some(Val::B(x == y)),
            _ => None,
        },
        Formula::Lt(a, b) => Some(Val::B(int(a)? < int(b)?)),
        Formula::Le(a, b) => Some(Val::B(int(a)? <= int(b)?)),
        Formula::Gt(a, b) => Some(Val::B(int(a)? > int(b)?)),
        Formula::Ge(a, b) => Some(Val::B(int(a)? >= int(b)?)),
        Formula::Add(a, b) => int(a)?.checked_add(int(b)?).map(Val::I),
        Formula::Sub(a, b) => int(a)?.checked_sub(int(b)?).map(Val::I),
        Formula::Mul(a, b) => int(a)?.checked_mul(int(b)?).map(Val::I),
        Formula::Div(a, b) => int(a)?.checked_div(int(b)?).map(Val::I),
        Formula::Rem(a, b) => int(a)?.checked_rem(int(b)?).map(Val::I),
        Formula::Neg(a) => int(a)?.checked_neg().map(Val::I),
        _ => None,
    }
}

/// The probe points for `havoc_flips_obligation`: the declared type's endpoints
/// and their neighbours, plus the small values every bounds/divisor obligation
/// turns on. Deterministic and duplicate-free.
fn probe_points(width: u32, signed: bool) -> Vec<i128> {
    let min = if signed { crate::range::signed_min(width) } else { 0 };
    let max = if signed {
        crate::range::signed_max(width)
    } else {
        i128::try_from(crate::range::unsigned_max(width)).unwrap_or(i128::MAX)
    };
    let mut pts = Vec::with_capacity(14);
    pts.push(min);
    pts.push(max);
    for candidate in [min.saturating_add(1), max.saturating_sub(1), -1, 0, 1, 2, 3, 4, 8, 16] {
        if candidate >= min && candidate <= max {
            pts.push(candidate);
        }
    }
    pts.sort_unstable();
    pts.dedup();
    pts
}

/// Whether moving `var` alone across its declared type range flips `raw` between
/// true and false — the operational meaning of "the obligation's answer is the
/// callee's return value, which I do not have".
///
/// Requires a definite verdict at EVERY probe point: a single `None` means some
/// other variable is still live in `raw`, and then the refutation is not
/// attributable to this variable alone. Requires BOTH a true and a false
/// verdict: an obligation that is false everywhere is provable and keeps its
/// row; one that is true everywhere is violated whatever the callee returns and
/// also keeps its row.
///
/// Trust: 2026-09-16 (round A8) — `free_len` is at most ONE `{s}__slice_len` symbol
/// that also occurs in `raw` and that NOTHING in the hypotheses constrains beyond the
/// length-range facts (see [`branch_declines`]): a slice length the verifier has no
/// fact about is a havoc of the same standing as the callee return, and `i >= len` with
/// both free is decided by neither. The question is then whether there is SOME value
/// of that length at which moving `var` alone flips the obligation; with `free_len`
/// absent this is exactly the single-variable probe.
///
/// Trust: 2026-09-16 (round A9) — `filters` are the checked-op RESULT RANGES on `var`
/// ([`is_checked_op_result_range`]): inert for the pinning question, but a probe point
/// they exclude (the type endpoint) is not an admissible value and may not witness the
/// flip. Every point is evaluated against them first; a `None` (a filter that mentions
/// another variable — not a shape the recogniser admits) keeps the point.
fn havoc_flips_obligation(
    raw: &Formula,
    var: &str,
    width: u32,
    signed: bool,
    free_len: Option<&str>,
    filters: &[&Formula],
) -> bool {
    let owned_len_points: Vec<Option<i128>>;
    let len_points: &[Option<i128>] = match free_len {
        None => &[None],
        // A length is a `usize` capped by the encoder at `isize::MAX` (`Ge(len, 0)`,
        // `Le(len, i64::MAX)`), so probe inside that range.
        Some(_) => {
            owned_len_points = probe_points(64, false)
                .into_iter()
                .filter(|k| *k <= i64::MAX as i128)
                .map(Some)
                .collect();
            &owned_len_points
        }
    };
    let pts = probe_points(width, signed);
    len_points.iter().copied().any(|len_value| {
        let mut saw_true = false;
        let mut saw_false = false;
        for &k in &pts {
            let env_buf = [(var, k), (free_len.unwrap_or(""), len_value.unwrap_or(0))];
            let env = if free_len.is_some() && len_value.is_some() {
                &env_buf[..2]
            } else {
                &env_buf[..1]
            };
            if filters.iter().any(|f| eval(f, env) == Some(Val::B(false))) {
                continue;
            }
            match eval(raw, env) {
                Some(Val::B(true)) => saw_true = true,
                Some(Val::B(false)) => saw_false = true,
                _ => return false,
            }
        }
        saw_true && saw_false
    })
}

/// Whether `conj` is one of the two LENGTH-RANGE facts the generator conjoins for
/// every modelled slice length (`value_facts::build_length_nonneg_facts`: `Ge(len, 0)`,
/// `Le(len, i64::MAX)`) on the base name `base` — true of every slice length, so it
/// pins no value. Orientation is load-bearing exactly as in
/// [`is_declared_type_range_bound`].
fn is_slice_len_range_fact(conj: &Formula, base: &str) -> bool {
    let is_var = |f: &Formula| var_full_and_base_str(f).is_some_and(|(_, b)| b == base);
    match conj {
        Formula::And(parts) => {
            !parts.is_empty() && parts.iter().all(|p| is_slice_len_range_fact(p, base))
        }
        Formula::Ge(a, b) => is_var(a) && **b == Formula::Int(0),
        Formula::Le(a, b) => {
            (is_var(a) && **b == Formula::Int(i64::MAX as i128))
                || (**a == Formula::Int(0) && is_var(b))
        }
        _ => false,
    }
}

/// Replace every occurrence of `Var(name)` (FULL name, so an SSA version is
/// never conflated with another) by `value`, in place.
fn substitute(f: Formula, name: &str, value: &Formula) -> Formula {
    if let Some((full, _)) = var_full_and_base_str(&f)
        && full == name
    {
        return value.clone();
    }
    f.map_children(&mut |c| substitute(c, name, value))
}

/// The kinds this pass may reclassify: the machine-safety obligations whose
/// violation formula is an integer predicate the probe can evaluate.
fn is_reclassifiable_kind(kind: &VcKind) -> bool {
    matches!(
        kind,
        VcKind::DivisionByZero
            | VcKind::RemainderByZero
            | VcKind::ArithmeticOverflow { .. }
            | VcKind::IndexOutOfBounds
            // Trust: 2026-09-16 (round A8) — the slice twin of `IndexOutOfBounds`: the
            // `assert(Lt(i, len))` row over a `{s}__slice_len` symbol. Admitted so that a
            // yield-fact miss on a slice index (`let mut s = a; for i in 0..s.len() { s[i]
            // } s = b;`, correct, root written after the loop) declines like the array
            // one instead of refuting on a free length (`a8_len_reseat_after_loop_*`).
            | VcKind::SliceBoundsCheck
    )
}

/// The reason string carried on a declined row. Named so the compiler's report
/// and the tests agree on one spelling.
pub(crate) const HAVOC_DECLINE_KIND: &str = "UnmodeledCalleeReturn";

/// The decline candidates of one body — the values whose only source is an
/// unmodelled foreign call — with what the pinning scan reads about them. Built once
/// per function: by the L0 pass's [`HavocTables`] as the generation's rows join its
/// sink (T3 C08s), and (Trust 2026-10-16, S3) by the generic refutation scope for the
/// bridge.
pub(crate) struct UnmodelledValues {
    /// Every candidate's base var name with its declared integer `(width, signed)`.
    candidates: FxHashMap<String, (u32, bool)>,
    /// The `Some`-payload FIELD candidates, each with the payload local aliasing it.
    payload_fields: FxHashMap<String, (String, u32, bool)>,
    /// The declared integer type of every local by base name (candidates win).
    int_types: FxHashMap<String, (u32, bool)>,
    debug: bool,
}

impl UnmodelledValues {
    pub(crate) fn of(func: &VerifiableFunction, sources: PayloadSources) -> Self {
        let mut candidates = call_only_int_dest_locals(func);
        // Round A5: the payload FIELDS of unmodelled foreign `Option` results, each
        // with the payload local that aliases it (see `unmodelled_next_payload_fields`).
        let payload_fields = unmodelled_next_payload_fields(func, sources);
        for (field, (_, width, signed)) in &payload_fields {
            candidates.entry(field.clone()).or_insert((*width, *signed));
        }
        static HAVOC_DEBUG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let debug = *HAVOC_DEBUG
            .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_HAVOC_DEBUG"));
        if debug {
            eprintln!(
                "[havoc] {} candidates={candidates:?} payload_fields={payload_fields:?}",
                func.def_path
            );
        }
        // The declared integer type of every local, by its formula base name — what
        // makes a declared-type range bound on a chained temp recognisable as inert
        // (see `dead` in `branch_declines`). Candidates carry their own widths and
        // take precedence.
        let mut int_types: FxHashMap<String, (u32, bool)> = FxHashMap::default();
        if !candidates.is_empty() {
            int_types = func
                .body
                .locals
                .iter()
                .filter_map(|d| {
                    // Trust (2026-10-16, S3): a checked operation's `(T, bool)` result
                    // is read through its field `_k.0`, whose declared range
                    // (`0 <= _k.0 <= T::MAX`) is as inert as a local's: without it the
                    // definition `_k.0 = k + 1` that the obligation itself folds through
                    // counted as a pin on `k` (`rest[k + 1..]` after a reseated
                    // `position`, `srh_split_fields`).
                    if let trust_types::Ty::Tuple(elems) = &d.ty
                        && let [elem, trust_types::Ty::Bool] = elems.as_slice()
                        && let Some(width) = elem.int_width()
                    {
                        let field = Place {
                            local: d.index,
                            projections: vec![trust_types::Projection::Field(0)],
                        };
                        return Some((place_to_var_name(func, &field), (width, elem.is_signed())));
                    }
                    let width = d.ty.int_width()?;
                    Some((
                        place_to_var_name(func, &Place::local(d.index)),
                        (width, d.ty.is_signed()),
                    ))
                })
                .collect();
            for (name, ws) in &candidates {
                int_types.insert(name.clone(), *ws);
            }
        }
        UnmodelledValues { candidates, payload_fields, int_types, debug }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.candidates.is_empty()
    }

    /// Conditions 2-4 of the module banner on a row WITH an obligation record: the
    /// base name of the candidate its refutation rests on, or `None`. Any kind; the
    /// L0 pass gates kinds itself ([`is_reclassifiable_kind`]).
    fn recorded_row_declines(&self, vc: &VerificationCondition) -> Option<String> {
        self.record_declines(vc.obligation.as_ref()?, &vc.formula, &vc.kind)
    }

    /// [`Self::recorded_row_declines`] for `record` read against `formula`: the
    /// recorded body is AUTHENTICATED against `formula`'s conjuncts (or, distributed,
    /// each path disjunct's) by [`branch_declines`], so a record that is not
    /// `formula`'s own violation declines nothing.
    fn record_declines(
        &self,
        record: &trust_types::ObligationRecord,
        formula: &Formula,
        kind: &VcKind,
    ) -> Option<String> {
        let raw = &record.body;
        let mut conjuncts = Vec::new();
        flatten_conjuncts(formula, &mut conjuncts);
        if conjuncts.len() > MAX_CONJUNCTS {
            return None;
        }
        // THE BRANCHES. A block with one predecessor encodes as `H ∧ body`; a block
        // with several (the `if let Some(i) = o` arm after two `next` blocks) encodes
        // as `∨_k (H_k ∧ body)`, one disjunct per path, possibly under a shared
        // conjunctive prefix (the declared-type ranges). Round A5: when the body is not
        // a top-level conjunct and exactly ONE top-level conjunct is an `Or`, each
        // disjunct is analysed as its own branch with the prefix, and the row is
        // declined only when EVERY branch declines — `∨_k (H_k ∧ body)` depends on
        // nothing but the unmodelled value iff each `H_k ∧ body` does. Any other shape
        // leaves the row untouched.
        let distributed = !conjuncts.iter().any(|c| *c == raw);
        let branches: Vec<Vec<&Formula>> = if !distributed {
            vec![conjuncts]
        } else {
            let mut ors = conjuncts
                .iter()
                .enumerate()
                .filter_map(|(i, c)| matches!(c, Formula::Or(_)).then_some(i));
            let at = ors.next()?;
            if ors.next().is_some() {
                return None;
            }
            let Formula::Or(disjuncts) = conjuncts[at] else { return None };
            let prefix: Vec<&Formula> =
                conjuncts.iter().enumerate().filter(|(i, _)| *i != at).map(|(_, c)| *c).collect();
            disjuncts
                .iter()
                .map(|d| {
                    let mut branch = prefix.clone();
                    flatten_conjuncts(d, &mut branch);
                    branch
                })
                .collect()
        };
        if branches.iter().any(|b| b.len() > MAX_CONJUNCTS) {
            return None;
        }
        let mut decline: Option<String> = None;
        for conjuncts in branches {
            let verdict = branch_declines(
                raw,
                &conjuncts,
                &self.candidates,
                &self.payload_fields,
                &self.int_types,
                self.debug,
            );
            if self.debug {
                eprintln!(
                    "[havoc]   row {kind:?} raw={raw:?} distributed={distributed} branch_declines={verdict:?}"
                );
            }
            let base = verdict?;
            // The per-branch reading is admitted for the PAYLOAD-FIELD candidates only
            // — the shape round A5 added it for. A direct call-destination candidate
            // under a path disjunction keeps the pass's historical behaviour (the row
            // is left as it is): `param_min_arg` (`if c { b = 3 } let n = a.min(b);
            // arr[n]`, a real panic) is refuted on that footing, and widening the
            // distribution to it would turn that refutation into an Unknown —
            // measured, and refused.
            if distributed && !self.payload_fields.contains_key(&base) {
                return None;
            }
            decline = Some(base);
        }
        decline
    }

    /// Trust (2026-10-16, S3): whether a generic solver model of `vc` rests on an
    /// unmodelled foreign call's value — the candidate's base name, or `None`.
    ///
    /// * A row WITH an obligation record: exactly the L0 pass's decision
    ///   ([`Self::recorded_row_declines`]), for every kind. The L0 pass gates kinds
    ///   because it REWRITES rows; the bridge only withholds a counterexample.
    /// * A row WITHOUT one — the `HardenedBoundary` panic-boundary twin
    ///   (`hardened.rs`, `obligation: None`), which carries the same violation as its
    ///   L0 sibling at the same span but no record of which conjunct it is. The twin
    ///   is read through its SIBLING's record (`sibling_records`): the recorded body
    ///   must occur verbatim in the twin's own query (authenticated exactly as for a
    ///   recorded row), and only that body is tried as the violation. A path guard
    ///   is never tried as the violation, so a genuine twin whose path runs under a
    ///   foreign-value guard keeps its refutation exactly when its L0 sibling does.
    ///   A twin with no authenticated sibling record is not this screen's.
    ///
    /// Negative-only: an answer can withhold a counterexample; `None` changes nothing.
    pub(crate) fn query_rests_on_unmodelled_value(
        &self,
        vc: &VerificationCondition,
        sibling_records: &[trust_types::ObligationRecord],
    ) -> Option<String> {
        if self.candidates.is_empty() {
            return None;
        }
        if vc.obligation.is_some() {
            return self.recorded_row_declines(vc);
        }
        sibling_records
            .iter()
            .find_map(|record| self.record_declines(record, &vc.formula, &vc.kind))
    }
}

/// The per-function tables of the L0 havoc decline (T3 C08s): what
/// [`HavocTables::reclassify`] reads besides the one row it decides. They are the
/// [`UnmodelledValues`] of `func` with the L0 pass's payload sources
/// ([`PayloadSources::IteratorNext`]), a function of `func` alone, so they are built once
/// per function and every row is decided on its own as it joins the generation's sink
/// (`super::row_sink`): the pass reads no other row and changes no row's position, which
/// is what lets it run per row.
pub(super) struct HavocTables {
    values: UnmodelledValues,
}

impl HavocTables {
    /// The tables of `func`.
    pub(super) fn for_function(func: &VerifiableFunction) -> HavocTables {
        HavocTables { values: UnmodelledValues::of(func, PayloadSources::IteratorNext) }
    }

    /// Reclassify `vc` if its refutation would rest on an unmodelled callee return:
    /// whether it was reclassified.
    ///
    /// The recorded [`ObligationRecord::body`] identifies the raw violation, and it
    /// is AUTHENTICATED before use: the body must appear verbatim as one of the
    /// formula's top-level conjuncts, or the row is left alone. Even an
    /// unauthenticated body could only cost a decision, never buy a proof — the sole
    /// edit this makes is `<safety kind>` → `UnsupportedMir`, which
    /// `discharge_body_vcs` turns into `Unknown` and never dispatches.
    pub(super) fn reclassify(&self, vc: &mut VerificationCondition) -> bool {
        if self.values.is_empty() {
            return false;
        }
        let declined = match self.declined_base(vc) {
            Some(base) => {
                // Demote through the shared constructor so this pass carries the SAME
                // fail-closed violation formula as every other `UnsupportedMir`
                // emitter. `Bool(false)` here would be UNSAT, and the kernel-discharge
                // gates in `trust_clean::whole_program` select rows by
                // `proof_level() == L0Safety` — which `UnsupportedMir` is — then hand
                // `vc.formula` to `check_refute_vc` and treat a refutation as
                // DISCHARGED. That would turn "I do not know" into a certification.
                super::unsupported::demote_to_unsupported_mir(
                    vc,
                    HAVOC_DECLINE_KIND.to_string(),
                    format!(
                        "the obligation's verdict is the return value of an unmodelled call \
                         (`{base}`), which nothing in this body constrains; a solver model over \
                         it is not an execution, so the row is Unknown rather than refuted"
                    ),
                );
                true
            }
            None => false,
        };
        // Post-condition on THIS pass's own rows: nothing it demoted carries a
        // formula a kind-blind consumer could read as discharged. Scoped to
        // `HAVOC_DECLINE_KIND` so it can only ever fire on a regression in this file
        // — it makes no claim about, and cannot be tripped by, another emitter.
        // Checked on each row as the pass leaves it, which is the whole list's check
        // (no later step of this pass touches a row it has passed).
        assert!(
            !(matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == HAVOC_DECLINE_KIND)
                && super::unsupported::is_unsupported_mir_with_wrong_formula(vc)),
            "a declined row must carry the fail-closed (SAT) violation formula; an UNSAT one is \
             read as DISCHARGED by the kind-blind kernel gates in trust_clean::whole_program"
        );
        // NOT asserted here: the same invariant across every OTHER emitter's
        // `UnsupportedMir` rows. This pass has no authority over rows it did not
        // create, and a `debug_assert!` over all of them turns any emitter's
        // polarity bug into a COMPILER PANIC on valid Rust rather than a decline —
        // strictly worse than the invariant it guards, because the rows in question
        // are already fail-honest Unknowns on the compiler path. The emitters own
        // that invariant at their own construction sites; the crate-wide sweep over
        // real MIR lives in `tests/havoc_dest_decline_realmir.rs`.
        declined
    }

    /// The base name of the candidate `vc`'s verdict rests on, when every branch of the
    /// row declines; `None` when the row keeps its verdict. The L0 pass REWRITES rows, so
    /// it gates kinds ([`is_reclassifiable_kind`]); the decision itself is
    /// [`UnmodelledValues`]'s, the one the generic refutation scope also reads.
    fn declined_base(&self, vc: &VerificationCondition) -> Option<String> {
        if !is_reclassifiable_kind(&vc.kind) {
            return None;
        }
        self.values.recorded_row_declines(vc)
    }
}

/// The havoc decline as `generate_vcs_impl_with_origins` ran it over its finished list
/// until T3 C08s, kept verbatim as the oracle of the per-pass parity tests
/// (`super::row_sink_tests`): [`HavocTables::reclassify`] is its split into per-function
/// tables and a per-row step, and the tests hold the two to the same rows. Returns the
/// number of rows reclassified.
#[cfg(test)]
pub(super) fn reclassify_havoc_only_refutations(
    func: &VerifiableFunction,
    vcs: &mut [VerificationCondition],
) -> usize {
    let values = UnmodelledValues::of(func, PayloadSources::IteratorNext);
    if values.candidates.is_empty() {
        return 0;
    }
    let mut reclassified = 0usize;
    for vc in vcs.iter_mut() {
        if !is_reclassifiable_kind(&vc.kind) {
            continue;
        }
        let decline = values.recorded_row_declines(vc);
        if let Some(base) = decline {
            // Demote through the shared constructor so this pass carries the SAME
            // fail-closed violation formula as every other `UnsupportedMir`
            // emitter. `Bool(false)` here would be UNSAT, and the kernel-discharge
            // gates in `trust_clean::whole_program` select rows by
            // `proof_level() == L0Safety` — which `UnsupportedMir` is — then hand
            // `vc.formula` to `check_refute_vc` and treat a refutation as
            // DISCHARGED. That would turn "I do not know" into a certification.
            super::unsupported::demote_to_unsupported_mir(
                vc,
                HAVOC_DECLINE_KIND.to_string(),
                format!(
                    "the obligation's verdict is the return value of an unmodelled call \
                     (`{base}`), which nothing in this body constrains; a solver model over \
                     it is not an execution, so the row is Unknown rather than refuted"
                ),
            );
            reclassified += 1;
        }
    }
    // Post-condition on THIS pass's own rows: nothing it demoted carries a
    // formula a kind-blind consumer could read as discharged. Scoped to
    // `HAVOC_DECLINE_KIND` so it can only ever fire on a regression in this file
    // — it makes no claim about, and cannot be tripped by, another emitter.
    assert!(
        !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
            if kind == HAVOC_DECLINE_KIND)
            && super::unsupported::is_unsupported_mir_with_wrong_formula(vc)),
        "a declined row must carry the fail-closed (SAT) violation formula; an UNSAT one is \
         read as DISCHARGED by the kind-blind kernel gates in trust_clean::whole_program"
    );
    // NOT asserted here: the same invariant across every OTHER emitter's
    // `UnsupportedMir` rows. This pass has no authority over rows it did not
    // create, and a `debug_assert!` over all of them turns any emitter's
    // polarity bug into a COMPILER PANIC on valid Rust rather than a decline —
    // strictly worse than the invariant it guards, because the rows in question
    // are already fail-honest Unknowns on the compiler path. The emitters own
    // that invariant at their own construction sites; the crate-wide sweep over
    // real MIR lives in `tests/havoc_dest_decline_realmir.rs`.
    reclassified
}

/// Exactly the conjunct `entry_sentinel_ties` emits: `Eq(Var(n#e), Var(n))`, either
/// orientation.
fn is_entry_sentinel_tie(conj: &Formula) -> bool {
    let Formula::Eq(a, b) = conj else { return false };
    let (Formula::Var(x, _), Formula::Var(y, _)) = (a.as_ref(), b.as_ref()) else {
        return false;
    };
    let tied = |sentinel: &str, bare: &str| {
        sentinel
            .strip_suffix(super::ENTRY_VERSION_SENTINEL)
            .and_then(|s| s.strip_suffix('#'))
            .is_some_and(|base| base == bare)
    };
    tied(x, y) || tied(y, x)
}

/// Conditions 2–4 of the module banner on ONE branch `∧ conjuncts` of a row whose raw
/// violation is `raw`: the base name of the candidate the branch's verdict is, or
/// `None` when the branch is decided by something the verifier knows.
fn branch_declines(
    raw: &Formula,
    conjuncts: &[&Formula],
    candidates: &FxHashMap<String, (u32, bool)>,
    payload_fields: &FxHashMap<String, (String, u32, bool)>,
    int_types: &FxHashMap<String, (u32, bool)>,
    debug: bool,
) -> Option<String> {
    {
        // Authenticate the recorded body against the branch, and split the
        // hypotheses off it. Exactly ONE occurrence is removed: a body that also
        // appears as a genuine hypothesis keeps that copy, so the pinning scan
        // still sees it.
        let body_at = conjuncts.iter().position(|c| **c == *raw)?;
        // Trust (2026-09-30, vac Phase 1.1): an ENTRY-SENTINEL TIE `n#e == n` is not a
        // hypothesis at this probe's granularity. Every question below is asked of BASE
        // names (`var_full_and_base` splits at `#`), and at that granularity the tie is
        // `n == n`: it restricts nothing. Kept, it read as a constraint on `n` and
        // silenced the free-length rule (round A8) — measured on
        // `a7_len_reseat_after_loop_o1` (tests/escaped_local_seam_realmir.rs), a CORRECT
        // program whose `SliceBoundsCheck` row was refuted on the unmodelled
        // `Iterator::next` payload once the widened tie tied the sealed
        // `s__slice_len#e` to the bare `s__slice_len`. Dropping a tie can only make
        // this pass decline MORE (a row becomes Unknown), never prove anything.
        let hypotheses: Vec<&Formula> = conjuncts
            .iter()
            .enumerate()
            .filter(|(i, c)| *i != body_at && !is_entry_sentinel_tie(c))
            .map(|(_, c)| *c)
            .collect();

        // Fold hypothesis definitions into the raw violation so the obligation is
        // expressed over the values it really depends on. Only definitions whose
        // subject is defined exactly once are used, so no equation is applied in
        // two contradictory directions.
        let hypothesis_defs: Vec<Option<&str>> =
            hypotheses.iter().map(|h| defined_var_str(h)).collect();
        let mut folded: std::borrow::Cow<'_, Formula> = std::borrow::Cow::Borrowed(raw);
        if hypothesis_defs.iter().any(Option::is_some) {
            let mut def_count: FxHashMap<&str, usize> = FxHashMap::default();
            for d in hypothesis_defs.iter().flatten() {
                let count = def_count.entry(*d).or_insert(0);
                *count += 1;
            }
            let single_defs: Vec<(&str, &Formula)> = hypotheses
                .iter()
                .zip(hypothesis_defs.iter())
                .filter_map(|(h, subject)| {
                    let Formula::Eq(a, b) = h else { return None };
                    let subject = (*subject)?;
                    if def_count.get(subject).copied().unwrap_or(0) != 1 {
                        return None;
                    }
                    match var_full_and_base_str(a) {
                        Some((full, base)) if base == subject => Some((full, b.as_ref())),
                        _ => match var_full_and_base_str(b) {
                            Some((full, base)) if base == subject => Some((full, a.as_ref())),
                            _ => None,
                        },
                    }
                })
                .collect();
            if !single_defs.is_empty() {
                for _ in 0..MAX_SUBST_ROUNDS {
                    let mut changed = false;
                    for &(var_side, value_side) in &single_defs {
                        if trust_types::any_formula_node(&folded, &mut |n| {
                            var_full_and_base_str(n).is_some_and(|(full, _)| full == var_side)
                        }) {
                            folded = std::borrow::Cow::Owned(substitute(
                                folded.into_owned(),
                                var_side,
                                value_side,
                            ));
                            changed = true;
                        }
                    }
                    if !changed {
                        break;
                    }
                    // Substitution replaces one node by a whole term, so a chain of
                    // definitions can grow the folded obligation multiplicatively. Give
                    // up (leaving the row untouched) rather than keep expanding.
                    if formula_node_count(&folded) > MAX_FOLDED_NODES {
                        folded = std::borrow::Cow::Borrowed(raw);
                        break;
                    }
                }
            }
        }

        if !debug
            && !trust_types::any_formula_node(&folded, &mut |n| {
                var_full_and_base_str(n).is_some_and(|(_, base)| candidates.contains_key(base))
            })
        {
            return None;
        }

        // The candidate variables the folded obligation actually depends on.
        let mut occurrences = Vec::new();
        collect_vars(&folded, &mut occurrences);
        if occurrences.len() > 1 {
            occurrences.sort_unstable();
            occurrences.dedup();
        }
        if debug {
            eprintln!(
                "[havoc]     folded={folded:?} occurrences={occurrences:?} hyps={hypotheses:?}"
            );
            if !occurrences.iter().any(|(_, base)| candidates.contains_key(base.as_str())) {
                return None;
            }
        }

        // verifier-perf: the base names each hypothesis conjunct mentions,
        // computed ONCE after verifying that the folded obligation actually
        // mentions at least one candidate variable. The dead-variable side
        // condition below asks "does any OTHER conjunct mention this name" for
        // every (candidate, conjunct) pair, which is quadratic in the conjunct
        // count; without this the query re-walks every conjunct's formula each
        // time, and a large body's VC has hundreds of conjuncts of hundreds of
        // nodes.
        let hypothesis_names: Vec<FxHashSet<&str>> = hypotheses
            .iter()
            .map(|h| {
                let mut set = FxHashSet::default();
                trust_types::visit_formula_nodes(h, &mut |node| {
                    if let Some((_, base)) = var_full_and_base_str(node) {
                        set.insert(base);
                    }
                });
                set
            })
            .collect();

        let mut decline: Option<String> = None;
        for (full, base) in &occurrences {
            let Some(&(width, signed)) = candidates.get(base) else {
                continue;
            };
            // `name` is DEAD in the hypotheses when every OTHER conjunct mentioning it
            // — every conjunct but the one under test (`at`), which would define it —
            // is itself an inert definition `Var(g) = rhs` of a dead `g`. Excluding
            // `at` is what makes the check "does anything ELSE constrain this temp";
            // without the exclusion every definition would count as an occurrence of
            // its own subject and no conjunct would ever be inert.
            //
            // Trust: 2026-09-16 (round A8) — TRANSITIVE. Round A5 asked "no other
            // conjunct mentions it", which is the depth-0 case. rustc spells a bounds
            // check as a COPY CHAIN, `_14 = copy i; _15 = Lt(_14, 6); assert(_15)`, so
            // `i` is mentioned by the definition of `_14`, `_14` by the definition of
            // `_15`, and `_15` by nothing: each link is satisfiable for any value of
            // the one before it by choosing its own subject, so the chain constrains
            // the head not at all. The A5 reading called `i` pinned by `_14`'s
            // definition and left `for mut i in 0..5 { i += 1; a[i] }` on `[u8; 6]` (a
            // correct program) refuted on a free index. A DECLARED-TYPE RANGE BOUND on
            // a link (`0 <= _14 <= u64::MAX`, conjoined for every integer local) is
            // inert for it exactly as for the candidate itself. Depth-bounded: an
            // unbounded recursion is refused, which leaves the row as it is.
            fn link_is_dead(
                name: &str,
                at: usize,
                hypotheses: &[&Formula],
                hypothesis_names: &[FxHashSet<&str>],
                hypothesis_defs: &[Option<&str>],
                int_types: &FxHashMap<String, (u32, bool)>,
                depth: usize,
            ) -> bool {
                if depth > 8 {
                    return false;
                }
                hypothesis_names.iter().enumerate().all(|(i, names)| {
                    if i == at || !names.contains(name) {
                        return true;
                    }
                    if let Some(&(w, s)) = int_types.get(name)
                        && is_declared_type_range_bound(hypotheses[i], name, w, s)
                    {
                        return true;
                    }
                    // A length name's own range facts (`0 <= _8__slice_len <= i64::MAX`)
                    // are inert for it exactly as a declared-type range is for a local.
                    if name.ends_with(SLICE_LEN_SUFFIX)
                        && is_slice_len_range_fact(hypotheses[i], name)
                    {
                        return true;
                    }
                    hypothesis_defs[i].is_some_and(|g| {
                        g != name
                            && link_is_dead(
                                g,
                                i,
                                hypotheses,
                                hypothesis_names,
                                hypothesis_defs,
                                int_types,
                                depth + 1,
                            )
                    })
                })
            }
            let dead_at = |name: &str, at: usize| {
                link_is_dead(
                    name,
                    at,
                    &hypotheses,
                    &hypothesis_names,
                    &hypothesis_defs,
                    int_types,
                    0,
                )
            };
            // A payload FIELD candidate is read together with its alias, the payload
            // local: a hypothesis pinning the alias pins the field (the yield facts and
            // guards are stated on the alias), and the alias's one definition
            // `alias = field` is a definition, not a constraint on either.
            let alias = payload_fields.get(base).map(|(alias, _, _)| alias.as_str());
            // Trust: 2026-09-16 (round A8) — a `{s}__slice_len` symbol that the folded
            // obligation does not mention and that nothing constrains beyond its range
            // facts and inert definitions is a FREE length: a yield fact `payload <
            // free_len` (or the `And` it comes in) bounds the candidate by an unknown
            // that never reaches the obligation, so it decides nothing about it — the
            // `Box<[u8]>` loop (`ctl_box_read`), whose three length reads are three
            // uncoupled casts of the same field, keeps its fact on one and its
            // obligation on another. Such a bound is inert for the pinning question;
            // a bound by a length the obligation DOES read stays a pin (`ctl_mut_store`).
            // `at` is the conjunct under test — the bound itself mentions the length,
            // so it is excluded from the "nothing constrains it" scan.
            let is_free_len_not_in_obligation = |name: &str, at: usize| -> bool {
                name.ends_with(SLICE_LEN_SUFFIX)
                    && !occurrences.iter().any(|(_, b)| b == name)
                    && !hypotheses.iter().enumerate().any(|(i, h)| {
                        i != at
                            && hypothesis_names[i].contains(name)
                            && !is_slice_len_range_fact(h, name)
                            && !hypothesis_defs[i].is_some_and(|g| g != name && dead_at(g, i))
                    })
            };
            let inert_bound = |h: &Formula, of: &str, at: usize| -> bool {
                fn go(
                    h: &Formula,
                    of: &str,
                    width: u32,
                    signed: bool,
                    free: &dyn Fn(&str) -> bool,
                ) -> bool {
                    match h {
                        Formula::And(parts) => {
                            !parts.is_empty()
                                && parts.iter().all(|p| go(p, of, width, signed, free))
                        }
                        Formula::Lt(a, b) | Formula::Le(a, b) => {
                            var_full_and_base_str(a).is_some_and(|(_, x)| x == of)
                                && var_full_and_base_str(b).is_some_and(|(_, y)| free(y))
                        }
                        other => is_declared_type_range_bound(other, of, width, signed),
                    }
                }
                go(h, of, width, signed, &|name: &str| is_free_len_not_in_obligation(name, at))
            };
            // Trust: 2026-09-16 (round A9) — the checked-op result ranges on the
            // candidate (or its alias) are inert for the pin and honoured by the probe.
            let range_filters: Vec<&Formula> = hypotheses
                .iter()
                .copied()
                .filter(|h| {
                    is_checked_op_result_range(h, base, width, signed)
                        || alias.is_some_and(|alias| {
                            is_checked_op_result_range(h, alias, width, signed)
                        })
                })
                .collect();
            if hypotheses.iter().enumerate().any(|(i, h)| {
                if let Some(alias) = alias
                    && is_alias_definition(h, alias, base)
                {
                    return false;
                }
                if inert_bound(h, base, i) || alias.is_some_and(|alias| inert_bound(h, alias, i)) {
                    return false;
                }
                if is_checked_op_result_range(h, base, width, signed)
                    || alias
                        .is_some_and(|alias| is_checked_op_result_range(h, alias, width, signed))
                {
                    return false;
                }
                conjunct_restricts(h, base, width, signed, &|name: &str| dead_at(name, i))
                    || alias.is_some_and(|alias| {
                        conjunct_restricts(h, alias, width, signed, &|name: &str| dead_at(name, i))
                    })
            }) {
                continue;
            }
            // Trust: 2026-09-16 (round A8) — a `{s}__slice_len` symbol in the folded
            // obligation that nothing constrains beyond the length-range facts and inert
            // definitions is a second havoc the probe may move; more than one, or one
            // that something pins, leaves the row as it is.
            let mut free_lens = occurrences.iter().filter(|(_, b)| {
                b != base
                    && b.ends_with(SLICE_LEN_SUFFIX)
                    && !hypotheses.iter().enumerate().any(|(i, h)| {
                        hypothesis_names[i].contains(b.as_str())
                            && !is_slice_len_range_fact(h, b)
                            && !hypothesis_defs[i].is_some_and(|g| g != b.as_str() && dead_at(g, i))
                    })
            });
            let free_len = free_lens.next().map(|(full, _)| full.as_str());
            if free_lens.next().is_some() {
                continue;
            }
            if havoc_flips_obligation(&folded, full, width, signed, free_len, &range_filters) {
                decline = Some(base.clone());
                break;
            }
        }
        decline
    }
}

#[cfg(test)]
mod fail_closed_polarity_tests {
    use super::*;

    /// A VC is a VIOLATION formula, so discharge means UNSAT. `Bool(true)` is
    /// SAT and can never be read as a proof; `Bool(false)` is UNSAT and is read
    /// as DISCHARGED by every consumer that selects rows by proof level instead
    /// of by kind — and `UnsupportedMir::proof_level()` is `L0Safety`, which is
    /// exactly what `trust_clean::whole_program`'s kernel gates select.
    #[test]
    fn the_unsupported_mir_formula_is_sat() {
        assert_eq!(
            super::super::unsupported::unsupported_mir_fail_closed_formula(),
            Formula::Bool(true),
            "an UNSAT formula on an `I do not know` row is a proof manufactured from a decline"
        );
    }

    /// `demote_to_unsupported_mir` rewrites the formula rather than leaving the
    /// row's original one in place, and drops the safety payload that no longer
    /// describes it.
    #[test]
    fn demotion_resets_the_formula_and_drops_the_payload() {
        let mut vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Eq(
                Box::new(Formula::Var("_2".to_string(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
            obligation: None,
        };
        super::super::unsupported::demote_to_unsupported_mir(
            &mut vc,
            HAVOC_DECLINE_KIND.to_string(),
            "d".to_string(),
        );
        assert!(
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == HAVOC_DECLINE_KIND)
        );
        assert_eq!(vc.formula, Formula::Bool(true));
        assert!(vc.obligation.is_none() && vc.contract_metadata.is_none());
        assert!(!super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
    }

    /// The oracle used by the pass's post-condition must actually flag an UNSAT
    /// `UnsupportedMir` row — an inert predicate would make the assert useless.
    #[test]
    fn the_polarity_oracle_flags_an_unsat_unsupported_row() {
        let mut vc = VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: "K".to_string(), detail: "d".to_string() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
        vc.formula = Formula::Bool(true);
        assert!(!super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
        // A non-UnsupportedMir row is never flagged, whatever its formula.
        vc.kind = VcKind::DivisionByZero;
        vc.formula = Formula::Bool(false);
        assert!(!super::super::unsupported::is_unsupported_mir_with_wrong_formula(&vc));
    }
}

#[cfg(test)]
mod type_range_orientation_tests {
    use super::*;

    fn v() -> Formula {
        Formula::Var("_2".to_string(), Sort::Int)
    }
    const U32_MAX: i128 = 4_294_967_295;

    /// The four spellings that every `u32` satisfies are inert.
    #[test]
    fn vacuous_u32_bounds_are_inert() {
        for f in [
            Formula::Le(Box::new(Formula::Int(0)), Box::new(v())),
            Formula::Le(Box::new(v()), Box::new(Formula::Int(U32_MAX))),
            Formula::Ge(Box::new(v()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(Formula::Int(U32_MAX)), Box::new(v())),
        ] {
            assert!(
                is_declared_type_range_bound(&f, "_2", 32, false),
                "{f:?} holds for every u32 and must not count as pinning"
            );
        }
    }

    /// The REVERSED comparisons against the same literals pin `_2` to an
    /// endpoint. Accepting one would let a constrained value be read as a free
    /// havoc, which is the direction that costs a decision.
    #[test]
    fn reversed_bounds_are_not_inert() {
        for f in [
            Formula::Le(Box::new(Formula::Int(U32_MAX)), Box::new(v())),
            Formula::Ge(Box::new(Formula::Int(0)), Box::new(v())),
            Formula::Le(Box::new(v()), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(v()), Box::new(Formula::Int(U32_MAX))),
        ] {
            assert!(
                !is_declared_type_range_bound(&f, "_2", 32, false),
                "{f:?} pins _2 to an endpoint and must count as a constraint"
            );
        }
    }

    /// A bound at a value that is NOT the declared type's endpoint is real
    /// information — this is what keeps `leading_zeros`'s modelled `_2 <= 32`
    /// from being mistaken for a `u32` type bound.
    #[test]
    fn a_tighter_bound_is_not_a_type_bound() {
        let f = Formula::Le(Box::new(v()), Box::new(Formula::Int(32)));
        assert!(!is_declared_type_range_bound(&f, "_2", 32, false));
    }

    /// The bound must be about `base` itself, not some other variable.
    #[test]
    fn a_bound_on_another_variable_is_not_inert_for_base() {
        let other = Formula::Var("_9".to_string(), Sort::Int);
        let f = Formula::Le(Box::new(other), Box::new(Formula::Int(U32_MAX)));
        assert!(!is_declared_type_range_bound(&f, "_2", 32, false));
    }
}
