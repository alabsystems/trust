//! THE ONE SEAM for "how many values can this local hold?" and "what is its value?".
//!
//! # The channel set
//!
//! A local receives a value through SEVERAL channels, and the class of bugs this
//! module exists to close is a scan that enumerates a PROPER SUBSET of them. The
//! complete set is `trust_types::LocalWrite`, produced by `Statement::local_write` and
//! `Terminator::local_write`. Those two classifiers live in `trust-types` rather than
//! here because `Statement` and `Terminator` are `#[non_exhaustive]`: only their own
//! crate can match them WITHOUT A WILDCARD, and only a wildcard-free match makes a new
//! MIR variant a COMPILE ERROR until it is classified. On top of that set there is
//! exactly one further channel, the one that is not a statement or a terminator at all:
//!
//!  * every PARAMETER (`1..=arg_count`) is defined at ENTRY, implicitly. No statement
//!    anywhere in the body carries that definition, so no block scan can see it.
//!  * everything else is one of the `LocalWrite` variants.
//!
//! The classifiers are checked against the model's OWN write-completeness taxonomy,
//! `trust_types::WriteEffect`: `LocalWrite::agrees_with` is asserted on every statement
//! and terminator [`for_each_local_write`] visits (debug builds — which is every test
//! run, over every corpus body) and is exercised variant-by-variant in
//! `trust_types::model_write_channel_tests`. Re-classifying a variant's `WriteEffect`
//! without re-classifying its channel therefore fails a test, and ADDING a variant
//! fails the build.
//!
//! `LocalWrite` is deliberately not `#[non_exhaustive]`, so every EXPORTED QUESTION
//! below — each written as a wildcard-free match over it — stops compiling when a
//! channel is added.
//!
//! # Why a subset is a false proof
//!
//! A predicate that scans a subset of the channels reads a local written through the
//! others as SINGLE-VALUED. Facts keyed on that reading are emitted against the
//! local's BARE name, `generate::safety` conjoins them into `vc.formula` BEFORE
//! `conjoin_preconditions_versioned_recorded` renames the whole formula, and the
//! rename binds the fact to whichever version is terminal in the block under proof —
//! including a version that never ran the write the scan did see. The fact is FALSE of
//! that value, the path condition goes UNSAT, and every obligation on the emptied path
//! is proved VACUOUSLY and kernel-certified. A RESOLVER is worse still: its answer is
//! INLINED into a formula, so version renaming cannot rebind a wrong one afterwards.
//!
//! THE BLOCK SCAN IS PRIVATE TO THIS MODULE. Callers ask one of the exported questions
//! below. Each question that walks the writes itself does so through an EXHAUSTIVE
//! match over [`LocalWrite`] — [`body_value_count`], [`body_never_explicitly_reseated`],
//! [`body_unique_value_def`], [`body_is_single_static_assignment`],
//! [`body_dest_fact_is_version_pinnable`], [`body_unique_defining_block`] — and the
//! remaining two ([`body_holds_one_value`], [`body_has_one_explicit_def`]) are
//! compositions of those. So a new channel forces
//! every question to state what it does with it, at compile time, with no site left to
//! inherit an unstated default.
//!
//! # One predicate cannot answer two questions
//!
//! [`body_is_single_static_assignment`] and [`body_dest_fact_is_version_pinnable`] are
//! deliberately SEPARATE and differ on exactly one shape — a `mut` parameter written by
//! one `Call` destination. They are the two halves of a gate that used to be one, and
//! the split is load-bearing IN BOTH DIRECTIONS:
//!
//!  * A fact keyed on a local's BARE NAME is a claim about every point in the function,
//!    so a parameter's entry definition refutes it. That is
//!    [`body_is_single_static_assignment`], and admitting the parameter there is a
//!    live kernel-certified false proof (`wc` below).
//!  * A fact PINNED to a post-call version token is a claim about one spelling that the
//!    entry value is never read under. That is
//!    [`body_dest_fact_is_version_pinnable`], and refusing the parameter there costs
//!    real proofs and buys nothing.
//!
//! The witness for the first half, refuted by the runtime oracle at 51,200 of 131,072
//! inputs and PROVED + kernel-certified before the parameter arm existed:
//!
//! ```ignore
//! pub fn wc(mut i: u8, j: u8, c: bool) -> u8 {
//!     if c { i = j.min(3); }
//!     i + 200                     // `i <= 3` was emitted as a GLOBAL fact on `i`
//! }
//! ```
//!
//! Asking the bare-name question at the version-pinned site (or the reverse) is the
//! defect, not the answer either one gives.
//!
//! # Absence of information is not a value
//!
//! Two of the six channels report that a write MAY have happened somewhere the seam
//! cannot see: [`LocalWrite::Unlocatable`] (no destination `Place` at all) and
//! [`LocalWrite::Escape`] (a mutable alias, through which a later store names a
//! DIFFERENT place). Neither is one value, and neither is zero values. A question that
//! grants a license ought therefore to DECLINE on them — answer "I do not know", not
//! "exactly one" — which is why [`body_value_count`] answers a
//! [`trust_types::ValueCount`] and not a `usize`: a `usize` licenses in one direction
//! or disqualifies in the other, and an unlocated write has to do both.
//!
//! [`LocalWrite::Unlocatable`] is handled that way everywhere. [`LocalWrite::Escape`]
//! IS NOT: [`body_value_count`] and [`body_unique_value_def`] both still admit it, and
//! in the resolver that is an OPEN, KERNEL-CERTIFIED FALSE PROOF, not a design choice.
//! Read the arm — it names the witness and the parked report — before treating this
//! module as sound about aliases.

use trust_types::{LocalWrite, Rvalue, Terminator, ValueCount, VerifiableBody, VerifiableFunction};

/// True iff `local` is a function PARAMETER (locals `1..=arg_count`) — the locals
/// that carry an implicit ENTRY definition. The return place (`_0`) is not one.
pub(crate) fn body_is_parameter(body: &VerifiableBody, local: usize) -> bool {
    local >= 1 && local <= body.arg_count
}

/// Visit EVERY channel by which a value can reach `local` inside `body.blocks`, with
/// the index in `body.blocks` of the block it is in.
///
/// The ENTRY definition is deliberately NOT visited: it is not in any block, and every
/// exported question below adds it explicitly via [`body_is_parameter`].
fn for_each_local_write<'a>(
    body: &'a VerifiableBody,
    local: usize,
    mut f: impl FnMut(usize, LocalWrite<'a>),
) {
    for (index, block) in body.blocks.iter().enumerate() {
        for stmt in &block.stmts {
            let write = stmt.local_write(local);
            debug_assert!(
                write.agrees_with(stmt.write_effect()),
                "statement channel classification disagrees with WriteEffect: {stmt:?}"
            );
            f(index, write);
            if stmt.escapes_local(local) {
                f(index, LocalWrite::Escape);
            }
        }
        let write = block.terminator.local_write(local);
        debug_assert!(
            write.agrees_with(block.terminator.write_effect()),
            "terminator channel classification disagrees with WriteEffect: {:?}",
            block.terminator
        );
        f(index, write);
    }
}

/// How many VALUES `local` can hold across the whole body: one per LOCATED write on
/// any channel that replaces the whole value, PLUS the implicit ENTRY definition a
/// parameter carries — and [`ValueCount::AtLeast`] when a write could not be located
/// at all.
///
/// `Exactly(1)` is the single-valued case UNIFORMLY — a parameter with no write at
/// all, or any other local with exactly one. `Exactly(0)` is a non-parameter that is
/// never written.
///
/// THE ENTRY DEFINITION IS COUNTED UNCONDITIONALLY. A liveness relaxation — "nothing
/// can read the incoming argument before the store, so the bare name means one value"
/// — was tried and REMOVED; it is a `body.blocks` analysis and both of the channels
/// that broke it are outside `body.blocks`:
///
///  * the UNWIND edge out of a `Call` whose destination is the parameter. The call did
///    not write the destination on that edge, so the parameter still holds its entry
///    value in the cleanup region. Pinned by
///    `a_call_dest_written_parameter_is_two_valued_because_of_the_unwind_edge`.
///  * the function's PRECONDITIONS. `vc.formula` carries them, and
///    `#[core::contracts::requires(k >= 10)]` is stated about the parameter's ENTRY
///    value. A post-definition fact renamed onto that same symbol contradicts the
///    precondition, the path goes UNSAT, and every obligation on it is proved
///    VACUOUSLY and kernel-certified. Pinned by
///    `a_stored_parameter_is_two_valued_even_when_no_block_reads_it_first`.
///
/// Two independent unsoundness channels through one precision recovery; the price of
/// counting the entry definition unconditionally is measured in
/// `tests/entry_def_structural.rs` (§ THE PRICE) and is paid.
///
/// WHAT IT COUNTS IS THE LOCATED WHOLE-VALUE CHANNELS. `WholeNamed`/`WholeOpaque`
/// REPLACE the local's value, and they are the only two that add to the total.
///
///  * `Partial` (a field or index store, a discriminant write, a `Deinit`, a `Drop`)
///    changes what the local holds without replacing it. It is NOT counted, and every
///    question below that cannot tolerate it refuses it for itself:
///    [`body_is_single_static_assignment`] and [`body_unique_defining_block`] refuse
///    it, and so does [`body_unique_value_def`]. Callers that adjudicate the partial
///    channel themselves compose with this count rather than duplicating it:
///    `lib.rs::array_local_index_naming_stable` decides its own projected stores (a
///    constant `Index` store keeps the array-theory naming, anything else bails) and
///    then asks [`body_has_one_explicit_def`] for the whole value. Folding `Partial`
///    in here double-counts exactly that store.
///  * `Unlocatable` is a write with NO destination `Place`. It is not one value and it
///    is not none: it is the absence of the information this function reports, so it
///    makes the count [`ValueCount::AtLeast`] and every affirmative question below
///    answers `false`. Counting it as a value instead is FAIL-OPEN, not fail-closed:
///    for a local with no whole-local write at all it would take the total from 0 to
///    1, and `Exactly(1)` is exactly the reading that licenses a global fact keyed on
///    the bare name — a license granted precisely where the seam admits it cannot see
///    the writes. `unlocatable_writes_fail_closed_for_every_local` pins all three
///    questions, not just the count.
///  * `Escape` — a `&mut local` handed out here — can be written through later at a
///    place this scan never names, so an escaped local can hold values this function
///    does not count. It is an OPEN RESIDUAL of THIS question, declared in the arm
///    rather than omitted: [`body_is_single_static_assignment`] and
///    [`body_unique_defining_block`] refuse it, but the count itself still admits it,
///    and so does [`body_unique_value_def`] — where admitting it is a live false
///    proof, named in that function's `Escape` arm.
///    Folding it in here is not a free tightening: every `for` loop's iterator local is
///    `&mut`-borrowed by the `Iterator::next` desugar, so counting the alias makes
///    every iterator local multi-valued at once and the loop-bound producers keyed on
///    this count stop firing across the whole corpus — turning `proved/` programs whose
///    runtime oracle never panics into refutations with counterexamples. That is a
///    REAL and substantial precision loss, and it is why the residual is still open.
///    Closing it needs the iterator tracers moved off the value question and onto an
///    ORIGIN question; that is a separate change, and it must be MEASURED when it is
///    made rather than quoted from here.
pub(crate) fn body_value_count(body: &VerifiableBody, local: usize) -> ValueCount {
    let mut n = ValueCount::ZERO.plus(usize::from(body_is_parameter(body, local)));
    for_each_local_write(body, local, |_, write| {
        n = match write {
            LocalWrite::Untouched => n,
            // Each of these REPLACES what `local` holds, so the bare name means one
            // more thing.
            LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => n.plus(1),
            // Refused by `body_is_single_static_assignment`,
            // `body_unique_defining_block` and `body_unique_value_def` for themselves,
            // and adjudicated by the callers that own the partial channel — see this
            // function's doc.
            LocalWrite::Partial => n,
            // OPEN RESIDUAL — see this function's doc. An alias is not itself a value,
            // and the write that arrives through it is invisible here.
            LocalWrite::Escape => n,
            // NOT a value: the absence of one. See this function's doc.
            LocalWrite::Unlocatable => n.plus_unlocatable(),
        };
    });
    n
}

/// True iff `local` PROVABLY holds ONE value everywhere its bare name can be read —
/// the [`body_value_count`] [`ValueCount::Exactly`]`(1)` case. This is the license a
/// GLOBAL fact keyed on the bare name needs, so an inexact count cannot grant it.
pub(crate) fn body_holds_one_value(body: &VerifiableBody, local: usize) -> bool {
    body_value_count(body, local).is_exactly(1)
}

/// True iff NO whole-local definition of `local` exists anywhere in the body: for a
/// parameter, the entry definition is the only one; for any other local, the slot is
/// never whole-written (it is projection-written, aliased, or never written).
///
/// Strictly stronger than [`body_holds_one_value`] for a parameter and strictly weaker for
/// any other local, so the two are NOT interchangeable. This is the question asked by
/// a caller that needs a fixed STORAGE SLOT (a closure-env pointer whose pointee can
/// be named definitionally), not a fixed VALUE — which is why a `Partial` write (into
/// the slot) and an `Escape` (an alias of it) do not disqualify, and an `Unlocatable`
/// write, which may have reseated it, does.
pub(crate) fn body_never_explicitly_reseated(body: &VerifiableBody, local: usize) -> bool {
    let mut reseated = false;
    for_each_local_write(body, local, |_, write| {
        reseated |= match write {
            LocalWrite::Untouched => false,
            LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => true,
            // A store into the slot, or an alias of it, keeps the slot itself.
            LocalWrite::Partial | LocalWrite::Escape => false,
            // Could have reseated it; the seam cannot tell.
            LocalWrite::Unlocatable => true,
        };
    });
    !reseated
}

/// True iff `local` holds ONE value AND that value is produced by an EXPLICIT
/// definition in `body.blocks`.
///
/// The question asked by a caller that goes on to INSPECT the defining statement —
/// "is this the `Vec::new()` that created the container", "is this the `len()` call
/// that produced the bound". A never-reassigned PARAMETER is single-valued but has no
/// such statement, so it answers `false` here and `true` to [`body_holds_one_value`].
pub(crate) fn body_has_one_explicit_def(body: &VerifiableBody, local: usize) -> bool {
    body_holds_one_value(body, local) && !body_never_explicitly_reseated(body, local)
}

/// The rvalue of `local`'s ONE value, when that value is produced by a whole-local
/// `Assign` and NOTHING ELSE touches the local.
///
/// `None` whenever the local can hold more than one value. That includes EVERY
/// PARAMETER with any write (whose `Assign` is its SECOND value — [`body_value_count`])
/// and every local reached by a channel this module cannot name EXCEPT ONE: a
/// `Call`/`TailCall` destination, a `SetDiscriminant`/`Deinit`/`Drop`, a projected
/// store, or an unlocatable pointer write all answer `None`; a MUTABLE ALIAS does not,
/// and that exception is a live defect rather than a rule — see the `Escape` arm.
/// This is the resolver channel, distinct from the counting channel: a caller that
/// INLINES the returned rvalue (a constant, a length, a referent place) bakes the value
/// into a formula, so version-renaming cannot rescue it afterwards.
///
/// A write THROUGH this local (`*local = v` — a `Deref`-first projection) changes the
/// POINTEE, not what `local` holds, so it does not count; see
/// `trust_types::LocalWrite::of_place`.
///
/// Live kernel-certified false proofs went through the missing channels, in both
/// directions:
///
///  * the ENTRY definition. `stable_min_arg_formula` resolves a modulo divisor / a
///    `min` argument through here and INLINES the result as a constant into a global
///    fact keyed on the parameter's bare name. `param_mod_divisor_guarded` /
///    `param_min_arg` are the rows.
///  * the `Call` DESTINATION. `pmod` — `let mut m = 4; if s { m = pick(c); } b[n % m]`
///    with `#[inline(never)] pick` — lowers at `-O` to `m = const 4` in bb0 and a
///    `Call` whose dest IS `m` in bb1, ONE `Assign` and one `Call` dest. An
///    `Assign`-only scan resolved `m` to `4`, `build_modulo_bound_facts` emitted
///    `n % m < 4`, and the out-of-bounds `b[n % 9]` was proved and kernel-certified.
///    `call_dest_and_assign_is_not_a_unique_value` and the end-to-end
///    `call_dest_reassigned_modulo_divisor_still_refutes` are the rows.
///
/// A THIRD ONE IS STILL OPEN: the MUTABLE ALIAS ([`LocalWrite::Escape`]). It is the
/// one channel this resolver does not refuse, and the arm below states the defect,
/// the witness and the reason the obvious tightening is not the fix, at the point
/// where the unsound answer is produced.
pub(crate) fn body_unique_value_def(body: &VerifiableBody, local: usize) -> Option<&Rvalue> {
    let mut found: Option<&Rvalue> = None;
    // The ENTRY definition is a value this resolver can never hand back.
    let mut ambiguous = body_is_parameter(body, local);
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(rvalue) => {
            if found.is_some() {
                ambiguous = true;
            } else {
                found = Some(rvalue);
            }
        }
        // ┌── KNOWN DEFECT — AN OPEN, KERNEL-CERTIFIED FALSE PROOF ────────────────┐
        //
        // THIS ARM IS UNSOUND AND IS NOT A DESIGN CHOICE. Do not read it as one.
        //
        // A `&mut local` handed out here can be stored through later at a place this
        // scan never names (`*p = v`, whose `place.local` is `p`, not `local`), so the
        // one `Assign` this resolver did see need not be the local's value at the use
        // — and this resolver hands it back anyway, INLINED into a formula, where
        // version renaming can no longer rebind it.
        //
        // THE LIVE WITNESS is `x3::pesc`, compiled WITHOUT `-O`:
        //
        // ```ignore
        // #[inline(never)] pub fn pick(c: bool) -> usize { if c { 4 } else { 9 } }
        // #[inline(never)] pub fn pesc(c: bool, n: usize, b: &[u8; 4]) -> u8 {
        //     let mut m = 4usize; let p = &mut m; *p = pick(c); b[n % m]
        // }
        // ```
        //
        // It lowers to ONE `Assign` `m = const 4`, an `Assign` `p = &mut m`, and a
        // store `(*p) = <call result>` whose place is `p`. This resolver answers `4`,
        // `build_modulo_bound_facts` inlines `n % m < 4`, and the out-of-bounds
        // `b[n % 9]` is PROVED and kernel-certified while the program panics at
        // runtime. AT `-O` the borrow is optimized away and the same source lowers to
        // the `Call`-destination shape the `WholeOpaque` arm above already refuses, so
        // the un-optimised lowering is the one that carries the channel.
        //
        // MOVING `Escape` INTO THE AMBIGUOUS ARM BELOW CLOSES THE FALSE PROOF AND IS
        // NOT THE FIX. The `Iterator::next` desugar `&mut`-borrows the iterator local
        // of EVERY Rust `for` loop, so the yield/origin tracers that resolve it
        // through this seam lose their answer at once and correct programs are refuted
        // with counterexamples — measured, on both the falsification corpus and this
        // crate's own precision controls. A real fix asks a DIFFERENT question (an
        // alias-aware ORIGIN for those tracers) instead of loosening this one.
        //
        // The witness, its runtime oracle, the mechanism, the affected rows by name,
        // and what a real fix needs are in the parked report `escape-residual.md`
        // (this change's review scratchpad).
        //
        // └────────────────────────────────────────────────────────────────────────┘
        LocalWrite::Escape => {}
        LocalWrite::WholeOpaque | LocalWrite::Partial | LocalWrite::Unlocatable => {
            ambiguous = true;
        }
    });
    if ambiguous { None } else { found }
}

/// The `Call` terminator that produces `local`'s ONE value, when that value comes from
/// a whole-local CALL DESTINATION and NOTHING ELSE touches the local.
///
/// The [`LocalWrite::WholeOpaque`] half of the resolver channel. [`body_unique_value_def`]
/// hands back an [`Rvalue`] and therefore refuses `WholeOpaque` — a call destination has
/// no `Rvalue` to name — so a caller that wants to INSPECT the producing call (which
/// callee, which arguments) had no seam question to ask and re-derived a block scan for
/// itself. `termination::resolve_saturating_add_increment` was exactly that scan, and it
/// was blind to the ENTRY definition: for a `mut` PARAMETER whose only body store is the
/// call, the entry value still reaches every use on a path that skips the call, and the
/// scan reported the call's value as the parameter's only one.
///
/// `None` whenever the local can hold more than one value, on ANY channel:
///
///  * a PARAMETER, always — its entry definition is not in `body.blocks` and this
///    resolver can never hand it back, so a parameter with a defining call holds TWO
///    values and a parameter without one has no call to return;
///  * a second `Call`/`TailCall` destination, or any [`LocalWrite::WholeNamed`] `Assign`
///    beside the call — two values, and the `Assign`'s is not the call's;
///  * [`LocalWrite::Partial`] (a projected store, `SetDiscriminant`, `Deinit`, `Drop`
///    glue) — the local's value after it is not the call's result;
///  * [`LocalWrite::Unlocatable`] — a write the seam cannot locate may have replaced it;
///  * [`LocalWrite::Escape`] — a `&mut local` handed out here can be stored through at a
///    place no scan keyed on `local` names. UNLIKE [`body_unique_value_def`], this
///    question REFUSES the alias channel. It is a new question with no `for`-loop
///    iterator tracers behind it, so the precision argument that keeps the residual open
///    there does not apply, and the scan this replaces already refused `&mut`/`&raw`
///    borrows of its temp by hand.
///
/// A `TailCall` writes only the return place `_0` and has no destination of its own, so
/// it can never be the answer; it is counted as a value and declined like any other
/// second definition.
pub(crate) fn body_unique_value_call(body: &VerifiableBody, local: usize) -> Option<&Terminator> {
    // The ENTRY definition is a value no call can be, so a parameter has none.
    let mut ambiguous = body_is_parameter(body, local);
    let mut at: Option<usize> = None;
    for_each_local_write(body, local, |index, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeOpaque => {
            if at.is_some() {
                ambiguous = true;
            } else {
                at = Some(index);
            }
        }
        // A named `Assign` is a SECOND value beside the call, and its value is not the
        // call's — either way this question has no single answer.
        LocalWrite::WholeNamed(_)
        | LocalWrite::Escape
        | LocalWrite::Partial
        | LocalWrite::Unlocatable => {
            ambiguous = true;
        }
    });
    if ambiguous {
        return None;
    }
    // `WholeOpaque` is reachable only from `Terminator::local_write`; no statement
    // produces it. The `Call` filter is what rejects the `TailCall` spelling.
    let terminator = &body.blocks.get(at?)?.terminator;
    matches!(terminator, Terminator::Call { .. }).then_some(terminator)
}

/// True iff `local` holds ONE value for the whole body ([`body_holds_one_value`]) and
/// that value is produced by a WHOLE-local write — no field/index store, no
/// discriminant write, no mutable alias, no unlocatable pointer write. Licenses
/// treating `Var(local)` as a GLOBAL invariant: the symbol has one meaning at every
/// program point.
///
/// SOUNDNESS (P0 false proof): before the parameter arm existed,
/// `fn f(g:&[u8;6], mut i:usize, c:bool)` whose body does `i = y*3+x` inside a
/// guarded loop scored one explicit def, PASSED, and licensed the flattened-index
/// fact `i <= 5` on the BARE parameter name — which version-renaming then bound to
/// the *entry* version read on the other branch, killing `g[i]` for every entry
/// `i >= 6`. Pinned by `param_reassigned_once_flat_index_still_refutes`.
///
/// The alias channel that used to be checked here by hand is now
/// [`LocalWrite::Escape`] (`trust_types::Statement::escapes_local`). Its own false
/// proof: `let mut i = a.min(3); let p = &mut i; *p = b; arr[i]` PROVED in-bounds in
/// both the default and the kernel-certified `-full` lane, because the store's place is
/// `*p` — `place.local == p`, not `i` — so no scan keyed on `i` saw the reassignment
/// and a stale `i <= 3` vacuously discharged the violated bounds VC.
pub(crate) fn body_is_single_static_assignment(body: &VerifiableBody, local: usize) -> bool {
    let mut whole = usize::from(body_is_parameter(body, local));
    let mut disqualified = false;
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => whole += 1,
        LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => disqualified = true,
    });
    !disqualified && whole == 1
}

/// True iff a fact about the value a `Call` terminator writes into `local` may be
/// PINNED to that call's post-call version token `{name}#s{block}_t`.
///
/// # This is a DIFFERENT QUESTION from [`body_is_single_static_assignment`], and the
/// # difference is the whole point of this function
///
/// `body_is_single_static_assignment` answers "may this local's BARE NAME carry a
/// function-wide invariant?". For a PARAMETER the answer is always NO — the entry
/// definition is a second value the bare name also denotes, on every path that skips
/// the body write — and that is exactly the false proof its parameter arm closes.
///
/// This function answers "is the post-call TOKEN a name of one value?", which is a
/// question about a SPELLING that does not exist at entry at all. The two answers
/// differ on precisely one shape, the `mut` parameter written by one call:
///
/// ```ignore
/// _3 = copy _1;                       // the argument temp rustc actually emits
/// _1 = step(move _3) -> bb1;          // dest IS the parameter
/// ```
///
/// The injected clause is threaded through `generate::block_defs`'
/// `version_terminator_dest_fact`, which rewrites EVERY occurrence of the dest's base
/// name to `{name}#s{block}_t`. Nothing reads the parameter's ENTRY value under that
/// spelling, so the fact cannot land on the path that skips the call — the skip path
/// reads the BARE name.
///
/// THE NAME-DISJOINTNESS IS STRUCTURAL, NOT MEASURED. Exactly two passes rewrite a
/// versioned token to the bare name — `discharge::normalize_ssa_version_tokens` and
/// `discharge::bare_ssa_guard_variant` — and both collapse `{name}#{tok}` to `{name}`
/// only when `discharge::local_versions_collapse_to_bare` licenses it. On its PARAMETER
/// arm that predicate requires `!local_has_call_dest_write(func, local)` — and a call whose dest
/// is this local IS a call-dest write. So for every shape admitted here through the
/// parameter arm the collapse is refused BY THIS PREDICATE'S OWN PRECONDITION, and the
/// post-call token stays a distinct SMT symbol from the bare entry read. Deleting the
/// parameter clause of `local_versions_collapse_to_bare` would make this unsound; that
/// pairing is ASSERTED, not left to a comment —
/// `param_entry_gate_tests::a_version_pinned_parameter_dest_can_never_collapse_to_the_bare_name`
/// fails there rather than as a false proof downstream.
///
/// # What it still refuses, and why each refusal is required
///
///  * MORE THAN ONE whole write. A second whole write means a second post-call (or
///    post-assign) version, and `version_terminator_dest_fact`'s rewrite is a BLANKET
///    base-name match: it would retime that other definition's reads onto THIS call's
///    token too. One whole write in `body.blocks` is what makes the blanket rewrite
///    equal to the targeted one.
///  * `Partial` — a field/index store, a discriminant write, a `Deinit`, a `Drop`.
///    The local changes at a point that mints no version token here, so the value the
///    token names is not the value at the use.
///  * `Escape` — a `&mut local` handed out anywhere. A store through the alias names a
///    different place, so it mints no token either and the pin is to a stale value.
///  * `Unlocatable` — a write the seam cannot locate at all. Absence of information is
///    not a value; it fails closed here as everywhere else in this module.
///
/// The one channel it ADMITS that `body_is_single_static_assignment` refuses is the
/// parameter's ENTRY definition, for the reason argued above. Every other channel is
/// refused identically, so this predicate is STRICTLY WEAKER than its sibling on
/// exactly one shape and identical on all the rest — which is the property that makes
/// splitting them a precision recovery rather than a hole.
///
/// The [`LocalWrite::WholeOpaque`] requirement is not redundant with the count: it is
/// what makes "the one whole write is a call destination" a fact rather than an
/// assumption about the caller. A caller asks this about the dest of a `Call` it is
/// looking at, so the one whole write it finds IS that call's — but stating it here
/// means a caller that asks about an `Assign`-written local gets `false`, instead of a
/// pin to a token that terminator never mints.
pub(crate) fn body_dest_fact_is_version_pinnable(body: &VerifiableBody, local: usize) -> bool {
    let mut opaque = 0usize;
    let mut named = 0usize;
    let mut disqualified = false;
    for_each_local_write(body, local, |_, write| match write {
        LocalWrite::Untouched => {}
        // The channel a `Call`/`TailCall` destination arrives on — the one that mints
        // the post-call token this pin names.
        LocalWrite::WholeOpaque => opaque += 1,
        // A named `Assign` is a second version of the local under a token this pin
        // does not name.
        LocalWrite::WholeNamed(_) => named += 1,
        LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => disqualified = true,
    });
    // The ENTRY definition is deliberately NOT charged here — see this function's doc.
    !disqualified && opaque == 1 && named == 0
}

/// The index in `body.blocks` of the ONE block that writes `local`, when the body
/// holds exactly one value of it and that value is not the parameter's entry value.
///
/// The question asked by a caller that resolves a definition ACROSS blocks on the
/// dominance argument "a local with a single static definition dominates all its uses,
/// because MIR never reads an uninitialized local". That argument needs the definition
/// to be unique on EVERY channel, and it is false of a parameter (initialized at ENTRY,
/// so a body definition of it need not run first) — both of which this answers.
///
/// `guards::latest_same_block_bool_definition` is the caller, and both halves are live
/// kernel-certified false proofs it carried:
///  * `p7` — `fn p7(a:&[u8;4], mut c: bool, i: usize, q: bool) { if q { c = i < 4; }
///    if c { a[i] } else { 0 } }` resolved the PARAMETER `c` to `i < 4` and proved
///    `a[i]` while `q=false, c=true, i>=4` indexes out of bounds.
///  * `p8` — `let c; if q { c = g(q); } else { c = i < 4; }` with `#[inline(never)] g`
///    lowers at `-O` to ONE `Assign` (`c = i < 4`) and one `Call` whose dest IS `c`.
///    An `Assign`-only uniqueness scan called `c` uniquely defined, inlined `i < 4` as
///    the SwitchInt edge fact, and proved `a[i]` while `q=true, i>=4` indexes out of
///    bounds.
///
/// THE PARTIAL AND ALIAS CHANNELS DISQUALIFY, they do not merely fail to count.
/// [`body_value_count`] scores neither, so `is_exactly(1)` above lets a body through
/// that has one whole write AND a field store, a `Drop`, or a `&mut` alias elsewhere —
/// and then there is no single block whose index answers "where the reaching
/// definition is", because the local changes at a point no index here names. Answering
/// with the whole write's block would assert a dominance that does not hold; answering
/// with the partial write's block is not a definition at all. Declining is the only
/// sound reading, and it is monotone (the caller loses a hypothesis).
/// `a_partially_written_local_has_no_unique_defining_block` is the row.
pub(crate) fn body_unique_defining_block(body: &VerifiableBody, local: usize) -> Option<usize> {
    if body_is_parameter(body, local) || !body_value_count(body, local).is_exactly(1) {
        return None;
    }
    let mut at: Option<usize> = None;
    let mut disqualified = false;
    for_each_local_write(body, local, |index, write| match write {
        LocalWrite::Untouched => {}
        LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => at = Some(index),
        LocalWrite::Partial | LocalWrite::Escape | LocalWrite::Unlocatable => disqualified = true,
    });
    if disqualified { None } else { at }
}

// ── the `VerifiableFunction` face ──────────────────────────────────────────
//
// Every question above is answered from `func.body` alone. These wrappers exist so
// the crate's call sites — which hold a `VerifiableFunction` — read naturally; the
// `body_*` forms are for the few callers (`typestate`) that hold only a body. There
// is ONE implementation of each question.

/// See [`body_is_parameter`].
pub fn is_parameter(func: &VerifiableFunction, local: usize) -> bool {
    body_is_parameter(&func.body, local)
}

/// See [`body_value_count`].
pub fn value_count(func: &VerifiableFunction, local: usize) -> ValueCount {
    body_value_count(&func.body, local)
}

/// See [`body_holds_one_value`].
pub fn holds_one_value(func: &VerifiableFunction, local: usize) -> bool {
    body_holds_one_value(&func.body, local)
}

/// See [`body_never_explicitly_reseated`].
pub fn never_explicitly_reseated(func: &VerifiableFunction, local: usize) -> bool {
    body_never_explicitly_reseated(&func.body, local)
}

/// See [`body_has_one_explicit_def`].
pub fn has_one_explicit_def(func: &VerifiableFunction, local: usize) -> bool {
    body_has_one_explicit_def(&func.body, local)
}

/// See [`body_unique_value_def`].
pub fn unique_value_def(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    body_unique_value_def(&func.body, local)
}

/// See [`body_unique_value_call`].
pub fn unique_value_call(func: &VerifiableFunction, local: usize) -> Option<&Terminator> {
    body_unique_value_call(&func.body, local)
}

/// See [`body_is_single_static_assignment`].
pub fn is_single_static_assignment(func: &VerifiableFunction, local: usize) -> bool {
    body_is_single_static_assignment(&func.body, local)
}

/// See [`body_dest_fact_is_version_pinnable`].
pub fn dest_fact_is_version_pinnable(func: &VerifiableFunction, local: usize) -> bool {
    body_dest_fact_is_version_pinnable(&func.body, local)
}

/// See [`body_unique_defining_block`].
pub fn unique_defining_block(func: &VerifiableFunction, local: usize) -> Option<usize> {
    body_unique_defining_block(&func.body, local)
}

#[cfg(test)]
#[path = "local_defs_tests.rs"]
mod local_defs_tests;
