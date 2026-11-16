//! Trust (2026-09-30): the two residuals of the fn-pointer `requires` fix,
//! L1 and L2 (docs/KNOWN_HAZARDS.md, the 2026-09-30 entry on "the fn-pointer
//! `requires` residuals"). Both are the premise the 2026-09-29 fix already
//! states — a function with a `requires` is verified UNDER it, so it may be
//! reached only where a call site charges the clause — failing on a route that
//! fix's gate (`function_has_unresolved_indirect_call`) did not look at.
//!
//! ## L1 — the callable inside a std closure the MIR inliner built
//!
//! Under an explicit `-Zmir-opt-level=2` (with `-Copt-level=3`) the inliner folds
//! `core::iter::once(y).map(div10).last()` into ONE call,
//! `<Once<u32> as Iterator>::fold::<Option<u32>, {closure@map_fold<u32, u32,
//! Option<u32>, fn(u32) -> u32 {div10}, …>}>`. `div10` is no longer a type argument
//! of any call in the body: it is a generic argument of core's `map_fold` closure,
//! and `callable_type_arg_is_unresolved_inner` took every sysroot closure as
//! resolved without asking what it was instantiated with. MEASURED on a stage 1 of
//! `3c29e31164` (default policy, strict and certify): the build is still refused,
//! but only by the unrelated `unsupported MIR Const::Closure` row that the
//! `requires`-free `add10` twin gets too, and with no `requires` note, so the day
//! that closure lowers it is a false accept. The same fold hides a FOREIGN item, a
//! fn pointer or a `dyn Fn` that the `-O0` spelling hands to `map` directly, where
//! the gate refuses it.
//!
//! The rule: a SYSROOT closure, coroutine-closure or coroutine handed to a call is
//! asked through what it can call — its parent's generic type arguments and its
//! captured upvars ([`sysroot_closure_callable_parts`]) — each exactly as a type
//! argument of the call itself would be, recursively (`copy_fold`'s closure wraps
//! `map_fold`'s). A LOCAL closure is unchanged: it is verified as its own body, so
//! the calls it makes are its own rows. Nothing that answered "unresolved" before
//! answers "resolved" now, and a sysroot closure over resolved callables (a
//! `requires`-free local item, a user closure, a std item that cannot panic) stays
//! resolved.
//!
//! What this does NOT give is `-O0` parity in either direction. It reaches only a
//! call that SURVIVES the inliner: at the same flags the inliner erased
//! `Some(y).map(add1)`, `let g = add1; g(y)` and `identity(add1)(y)` outright, and
//! a call that is gone is charged by nobody. Since 2026-09-30 (prepared, not built)
//! a verifying session's inliner keeps such a call (`requires_callee_inlining`;
//! docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-09-30 … — under an explicit
//! `-Zmir-opt-level=2` …"), and the direct-call lane charges it. And a parent's type
//! arguments are DATA as well as callables: an element type `fn(u32) -> u32` is
//! asked like a callable (`ty::FnPtr` answers "unresolved"), and so is a generic
//! helper such as `last::some::<T>` in a generic body. Usually the `-O0` spelling
//! hands the gate the same type (`copied::<'_, fn(u32) -> u32>` — measured
//! refused), but not always: `Vec<fn(u32) -> u32>`'s `into_iter().map(..).fold(..)`
//! names no fn-pointer type argument at `-O0` and its `map_fold` closure does. Both
//! are over-refusals, fail-closed.
//!
//! ## L2 — memory-safe never asked the indirect-call gate
//!
//! The gate is consulted inside `abort_on_full_verification_failure`: strict, the
//! default policy and certify. A body with no `unsafe` under
//! `-Ztrust-policy=memory-safe` is judged by
//! `abort_on_memory_safe_non_demotable_failure` instead, which reads ROWS, and an
//! unresolved indirect call has no row. MEASURED on a stage 1 of `3c29e31164`:
//! crate `c`, built on the default policy, `pub fn add1(x: u32) -> u32 requires x <
//! 100 { x + 1 }` (its overflow check elided on the strength of the `requires`), and
//! crate `ms2`, built `-Ztrust-policy=memory-safe`, `pub fn p(y: u32) -> u32 { let
//! fp: fn(u32) -> u32 = c::add1; fp(y) }`: exit 0 with no diagnostic, and a
//! verify-off `main` printed `p(u32::MAX) = 0`, where the verify-off build of the
//! same crates panics "attempt to add with overflow". Within ONE crate the build
//! is refused, but only by the `requires` function's own `assumption:requires`
//! row, and across crates that row lives in the callee's crate, built under
//! another policy.
//!
//! The rule: memory-safe refuses what the gate refuses on every other fail-closed
//! lane ([`abort_on_memory_safe_unresolved_indirect_call`]). That is PARITY, the
//! ground the 2026-09-29 close-out accepted P-REQ-1..2 on, and not a claim that
//! nothing narrower is sound. What is not sound is the natural narrowing — refuse
//! only a target that carries a `requires`:
//!  * a pointer whose target the body does not name — a parameter, a field, a
//!    `static`/`const` or promoted table, a call's return value — may be a
//!    `requires`-carrying function minted where no gate looks (a `const`
//!    initializer, a promoted, a body that reifies without calling, a verify-off
//!    crate); only the call site can refuse it;
//!  * a named FOREIGN target with no `requires` is code with no verdict here, and
//!    memory-safe refuses the DIRECT call to it (its absent-callee row; measured on
//!    the same stage 1), so admitting the pointer call launders that refusal;
//!  * a sysroot target that may panic (`fold(100, u32::div_euclid)`) has no row,
//!    and memory-safe admits a panic only as a compiler-MARKED row.
//! Some narrower rules would be sound — a reified sysroot item that
//! `sysroot_fn_item_cannot_panic` proves total (`u32::wrapping_add as fn(u32, u32)
//! -> u32`) calls no user code and cannot panic — but memory-safe would then admit
//! what the default lane refuses; recovering such a shape is work for both lanes.
//! It is the documented contract of `@trust-indirect-callee`
//! (`trust_types::TRUST_INDIRECT_CALLEE_PATH`: fail closed on it exactly as on a
//! callee whose body is absent), applied on the one lane that skipped it.
//!
//! ## L2 through a classifier skip (review of this change, 2026-09-30)
//!
//! The call above sits in `publish_body_verification_outcome`, which a body the
//! classifier SKIPS never reaches. Under memory-safe a no-`unsafe` body skipped as
//! `TreatedAsAssumption` (one safe `&raw const s.a` is `AddressOfField`; also a
//! pattern type, an escaped binder, a coroutine drop) or `UnreachableStart` is
//! admitted as ONE authenticated `assumption:<tag>` row — the premise being that
//! such a body can leave only its own panic-freedom undischarged. A skipped body
//! charges NOTHING, so the premise fails for a call it owes a `requires` and for an
//! unresolved callable. MEASURED (review, stage 1 of `3c29e31164`; again on
//! `fbc6068e3`): `let _q = &raw const s.a;` added to the L2 pointer call, to a
//! DIRECT `dep::add1(y)`, or to `v.iter().copied().map(dep::add1).last()` built exit
//! 0 under memory-safe, and `p(u32::MAX)` returned 0 for the first two; strict,
//! the default policy and certify refuse all three (the skip itself). The rule
//! ([`memory_safe_skip_withheld`]): the demotion is withheld, so the skip is refused
//! as on every other fail-closed lane, when the body makes a direct call whose
//! callee owes a caller precondition, local or foreign (read off the callee
//! operand's TYPE, so a call through a local holding the item counts), or when
//! the gate refuses it.
//!
//! The same skip laundered code with no verdict at all, `requires` or not — the
//! 2026-09-27 lowering-collapse launder (`native_lowering_collapse_uncharged_edges`)
//! one stage earlier. MEASURED on `fbc6068e3`, each with the field borrow: a
//! verify-off dependency's safe `deref_raw(q)` (`unsafe { *q }`) and `get()`
//! (`unreachable_unchecked`), and a VERIFIED dependency's `add1_wrapping(y)`, built
//! exit 0 under memory-safe; each without the borrow is refused. So the demotion is
//! also withheld on a masked fail-closed source, the collapse rule's own conjunct
//! (a call through a fn pointer is left to the gate, which resolves a local
//! reified constant). Not taken: the collapse rule's other conjunct, "every call
//! resolves to a local verified item", which refuses sysroot calls too. A skipped
//! body still stands for its sysroot callees' panics: with the borrow,
//! `std::process::exit(1)` behind a branch and `Vec::push` built exit 0 (each
//! refused without it), while `u32::checked_add` builds exit 0 either way; that
//! conjunct would refuse all three. docs/KNOWN_HAZARDS.md records it as OPEN.
//!
//! ## Cost (memory-safe)
//!
//! MEASURED on the same stage 1, each of these built exit 0 under memory-safe with
//! no row and is refused by the gate on the default policy; each is refused under
//! memory-safe after this change (predicted — no stage 1 with it was built here):
//! a fn-pointer parameter called (`call(f: fn(u32) -> u32, y: u32) -> u32 {
//! f(y) }`); a foreign item reified and called, with or without a `requires`; a
//! local closure coerced to a fn pointer and called; a sysroot item reified and
//! called; a sysroot item that may panic handed to generic code. A local
//! `requires`-free item reified and called, and every callable the gate resolves,
//! keep compiling. The skip path adds the same shapes in a body the classifier
//! skips, plus a direct call to a `requires`-carrying function there — which the
//! same body without the skip already fails on (`[precond] FAILED`) — and a masked
//! source there, which the body without the skip fails on too, with two
//! over-refusals the masked predicate carries: a `write!` into any sink (its
//! `write_fmt` arm) and a local type whose `Drop` this compilation did not prove
//! panic-free. No `tests/ui/trust` or run-make memory-safe fixture has a
//! classifier-skipped body (measured). Recovering the sysroot shapes needs an
//! authenticated memory-safe panic row for a sysroot callable that reaches no user
//! code; not done here.
//!
//! ## The ADT residual — an item owing a `requires` inside a type argument
//!
//! Trust (2026-09-30, prepared, not built). The gate asked each type argument of a
//! direct call as it stands — an item, a `&`/`&mut`/`Box` of one, a closure, a
//! `dyn`, a parameter — and an ADT answered "resolved" whatever it wrapped. At
//! `-Copt-level=3 -Zmir-opt-level=2` the inliner folds `once(y).map(add1)` into a
//! `Map` aggregate and leaves the call that consumes it, with `add1` in an ADT and in
//! no call: `.reduce(|a, b| a ^ b)` leaves `<Map<Once<u32>, fn(u32) -> u32 {add1}> as
//! Iterator>::reduce::<{closure@…}>`; `.max()` the same `Self` with core's `max_by`
//! closure over `<u32 as Ord>::cmp`, which L1 asks (a sysroot item that cannot panic,
//! so resolved — predicted); `.collect::<Vec<u32>>()` `SpecFromIterNested::<u32,
//! Map<…, fn(u32) -> u32 {add1}>>::from_iter`; a local generic consumer
//! `run::<Map<Once<u32>, fn(u32) -> u32 {add1}>>`. `add1` then runs inside the
//! callee, where no call charges its `requires`.
//!
//! MEASURED on a stage 1 of `fbc6068e3`. LIVE where the consumer is code nobody
//! verifies: with `#[trust::assume_total] #[inline(never)] fn run<I: Iterator<Item =
//! u32>>(it: I) -> Option<u32> { it.last() }`, `pub fn f(y: u32) -> Option<u32> {
//! run(core::iter::once(y).map(add1)) }` built exit 0 on strict, the default policy
//! and certify with no `[CALLABLE_TYPE_ARG]` line, and so did `dep::add1` from a
//! verified dependency (under memory-safe too, where the L2 gate answers the same
//! "resolved" — predicted: `fbc6068e3` has no L2); the certify library, built with
//! `-Coverflow-checks=on` and linked into a verify-off `main`, RETURNED `f(u32::MAX)
//! = Some(0)`, where its verify-off build panics "attempt to add with overflow". This
//! is not the declared `assume_total` route (docs/KNOWN_HAZARDS.md: an `assume_total`
//! body that calls `add1` itself): `run` names no `requires` item, and `run2(add1, y)`
//! into an `assume_total` `run2<F: Fn(u32) -> u32>` is refused by the gate at the same
//! flags; the `Map` alone let `f` through. MASKED where the consumer is std: each std
//! shape above was refused only by unrelated rows — the consuming call's panic-freedom
//! kept fatal as a generic absent callee (for `collect` also five `unsupported_mir`
//! rows), the native lowering failing on `max_by`'s capturing closure for `max` —
//! with no `requires` note, and the `requires`-free twins were refused by the same
//! rows. At `-O0` the `map(add1)` call survives and the gate refuses it.
//!
//! Rule (1) ([`ty_carries_requires_carrying_fn_item`]): after the question the gate
//! asks of a type argument as it stands, the argument — `Self` included — is
//! unresolved when it carries, ANYWHERE inside it, a function item that owes its
//! caller a `requires` ([`fn_item_owes_caller_precondition`], the predicate the L1/L2
//! note names items with: a local item as named and as resolved, a foreign one from
//! its crate's exported contract set, a sysroot item not asked). One `Ty::walk`, the
//! walk `ty_carries_masked_fail_closed_fn_value` makes, covers an ADT's type
//! arguments, a closure's parent arguments, signature and captures, and a sysroot
//! closure inside an ADT or the other way round. The gate's reified-constant
//! carve-out (`indirect_callee_is_a_reified_constant`, a direct call in all but
//! spelling) asks the reified item the same question: `let fp: fn(_) -> Option<u32> =
//! run; fp(core::iter::once(y).map(add1))` reifies `run::<Map<Once<u32>, fn(u32) -> u32
//! {add1}>>`, and with the `assume_total` `run` it built exit 0 (MEASURED). The note
//! ([`requires_carrying_fn_values`]) reads the same walk, so it names the item.
//!
//! One carve-out, a LOCAL closure's capture that is itself a function item (behind
//! `&`, `&mut` or `Box` at most): `let g = add1; let c = move |x: u32| if x < 100 {
//! g(x) } else { 0 }; c(y)` calls `<{closure} as Fn<(u32,)>>::call`, and the
//! closure's own body, verified as its own root, calls `g` — a call the direct-call
//! lane charges (MEASURED on `fbc6068e3`: the unguarded twin's closure is refused,
//! `[precond] FAILED`, counterexample `x = 100`; the guarded shape built exit 0 on
//! strict and the default policy). A captured item can leave the closure only through
//! that body: a call is charged there, a hand-over to generic code is gated there, a
//! return or a write through an argument is in the signature, which is walked, and
//! an item has no destructor. Every other capture IS walked, fail-closed: an ADT
//! capture brings its drop glue into whatever code drops the closure, and a
//! dependency's `Drop` over a generic callable would call the item there.
//!
//! Rule (1) matches an ITEM only, because a fn pointer's value is in no type: a
//! `fn(u32) -> u32` inside an ADT may be `add1` or anything else, and nothing asks
//! it there (the gate asks a pointer at the top level of a type argument or of a
//! sysroot closure's, L1, and where it is called). So `let fp: fn(u32) -> u32 = add1;
//! run(core::iter::once(y).map(fp))`, whose one call is `run::<Map<Once<u32>, fn(u32)
//! -> u32>>`, built exit 0 on the default policy and certify (MEASURED). Rule (2)
//! ([`body_mints_requires_carrying_value`], the cast rule) catches such a pointer where it is
//! MINTED, as `function_has_masked_fail_closed_dispatch` catches a reified dependency
//! function: a body with a cast whose SOURCE type carries an item owing a `requires`
//! — `add1 as fn(u32) -> u32`, `&add1` unsized to `&dyn Fn(u32) -> u32`, a `Map` over
//! it unsized to a `dyn Iterator` — is refused, since the value it makes no longer
//! names the item. That also refuses the verified caller that mints the pointer and
//! passes it BY VALUE to a helper which hands it on (`hand(add1, y)`). And rule (3):
//! the gate reads a call's item off the callee operand's TYPE, so a call through a
//! local holding the item (`let g = run; g(it)`, which `-Zmir-opt-level=0
//! -Zinline-mir=yes` leaves as `move _3(move _4)`) has its type arguments asked like
//! a constant's; before, only the lowering's `Call(indirect)` refused it (MEASURED).
//!
//! Where they reach: every lane that asks the gate — strict, the default policy and
//! certify (`abort_on_full_verification_failure`), memory-safe
//! ([`abort_on_memory_safe_unresolved_indirect_call`]) and its skip withholding
//! ([`memory_safe_skip_withheld`]), the writer-relative formatting bar. A body whose
//! native lowering FAILED is refused before the gate is consulted (the `max` shape),
//! so that error now carries the gate's notes ([`lowering_failure_gate_notes`]): the
//! verdict does not change, and the author is told what else refuses the body.
//!
//! Over-refusal (predicted): an owing item carried as DATA inside a type argument is
//! refused as a callable, as the gate already refuses it at the top level
//! (`size_of_val(&add1)`, MEASURED); `size_of_val(&Some(add1))` at `-O0` is refused
//! today by its generic-absent-callee row anyway, `requires` or not, and at
//! `-Zmir-opt-level=2` the call folds to a constant (both MEASURED). A pointer or a
//! `dyn` minted from an owing item is refused even where nothing calls it (a
//! comparison, a pointer returned to a verified caller — whose call through it the
//! gate refuses anyway). A LOCAL coroutine, async block or coroutine-closure gets no
//! capture carve-out, so one that captures `g = add1` and is handed to generic code
//! is refused, while a local closure's is not.
//!
//! Not reached, each MEASURED on `fbc6068e3` with the `assume_total` `run` at
//! `-Zmir-opt-level=2` unless noted:
//!  * a callable that comes from OUTSIDE the body inside an ADT: a fn-pointer
//!    parameter (`f(fp: fn(u32) -> u32, y)` handing `run(once(y).map(fp))`), a
//!    `&dyn Fn(u32) -> u32` parameter, a type parameter `F: Fn(u32) -> u32` — each
//!    built exit 0 on the default policy and certify, and each is refused at `-O0`,
//!    where `map` survives with the callable as its top-level type argument.
//!    `hand(fp, y)` in the fixture's `ptr_by_value_o3` is this shape; its caller,
//!    which mints the pointer, is refused by rule (2).
//!    With a std consumer the same hand-over is masked (`map(fp).reduce(..)`: refused
//!    only by the `reduce` row). Asking the other callable kinds inside an ADT would
//!    refuse fn-pointer DATA (`Vec<Handler>`, `size_of::<Option<fn()>>()`), which
//!    this change does not do;
//!  * a pointer to an owing item minted where no rule here looks — a `const`/`static`
//!    or promoted initializer, a verify-off crate — and handed in the same way. Since
//!    2026-10-03 (built and tested) the minting-site seam refuses it where it is
//!    minted for every LOCAL minting site (below, "The minting-site seam"); a verify-off
//!    crate's minting is still out of reach;
//!  * a RETURNED value: `pub fn g(y: u32) -> impl Iterator<Item = u32> {
//!    core::iter::once(y).map(add1) }` builds exit 0 at `-Zmir-opt-level=2` (it makes
//!    no call; refused at `-O0`), and `pub fn g() -> impl Fn(u32) -> u32 { add1 }`
//!    at every level. A verified consumer of the value is refused by rule (1) (its
//!    call's `Self` is the revealed type — predicted), but an unverified caller may
//!    call a PRIVATE `requires` item this way. Since 2026-10-03 (built and tested)
//!    the seam's R7 refuses a local opaque type whose hidden type carries the item;
//!  * under memory-safe on a stage 1 carrying L2 (not measurable on `fbc6068e3`,
//!    which has no L2): a consumer the classifier SKIPS (`let _q = &raw const s.a;
//!    it.last()`) in place of the `assume_total` one — predicted to let the shapes of
//!    the first bullet through with no declared premise, unless its skip is withheld;
//!  * a sysroot callable that may panic, or a foreign `requires`-free item, inside an
//!    ADT (these rules ask only for a `requires`); a call the inliner erases (L3).
//!
//! ## `#[trust::assume_total]` charged none of its calls (2026-09-30)
//!
//! `verification_decision` skips a body carrying `#[trust::assume_total]` as
//! `AssumedTotal`, a recorded assumption no policy refuses, unless the body can
//! perform an unsafe operation (D8-P0, `validity_transmute::assume_total_cannot_cover_body`).
//! A skipped body charges none of its calls. MEASURED on a stage 1 of `fbc6068e3`,
//! with `add1(x: u32) -> u32 requires x < 100 { x + 1 }` (its overflow check elided
//! under the clause) local or in a dependency verified on the default policy: an
//! `assume_total` body calling it directly, through `let g = add1`, as a reified
//! pointer or handed to `Option::map`; from a closure or a method that inherits the
//! attribute; or calling a fn-pointer or `&dyn Fn` PARAMETER that a verified caller
//! filled with `add1` — each built exit 0 under the default policy, strict and
//! certify (and, across crates, memory-safe) with only `Trust: ASSUMPTION
//! [assumed-total]`, while the same bodies without the attribute are refused on
//! those three policies. Linked into a verify-off `main`, the certify and default
//! builds of the direct, `map`, closure, pointer-parameter and `dyn Fn` shapes (and
//! of the cross-crate direct and pointer-parameter ones) RETURNED `p(u32::MAX) = 0`
//! (`Some(0)` through `map`), where the verify-off build panics. The parameter route
//! has no other gate: the body that reifies `add1` makes no call through it, and the
//! indirect-call gate is asked only at the call, which the skip removed.
//!
//! Totality is not a callee's precondition, as it is not validity. The attribute
//! assumes that THIS body does not panic and terminates; a callee's `requires` is
//! the premise the callee's own verification rests on — its body is verified with
//! the clause as an entry hypothesis and a check proved under it is elided — so a
//! call outside the clause is not a panic the attribute could assume away: it runs
//! the callee outside its verdict (a wrapped value; under an `unsafe` the callee
//! proved safe under the clause, undefined behaviour).
//!
//! The rule ([`assume_total_cannot_cover_calls`]) is D8-P0's for this obligation
//! family: such a body is verified exactly as if the attribute were absent when it
//! makes a direct call whose callee owes a caller precondition (the predicate
//! memory-safe's skip rule reads, [`direct_callees_owing_caller_precondition`]), or a
//! call the indirect-call gate refuses (`function_has_unresolved_indirect_call`) —
//! the latter because only that call site can refuse a `requires`-carrying function
//! another body turned into a value — or when it HOLDS such a callable
//! ([`held_uncharged_callables`]). The direct-call lane then charges the clause and
//! the gate asks the pointer, on every policy; strict, the default policy, certify
//! and memory-safe refuse what they refuse without the attribute, and advisory
//! reports it, with the warning [`warn_assume_total_does_not_cover_calls`] on every
//! policy. Whole-body for D8-P0's reason: keeping the skip for the panic rows while
//! charging the precondition rows would need a verification mode that classifies
//! every row as "assumed by the attribute" or "charged", and no such mode exists.
//! NOT taken: memory-safe's masked-source clause. A dependency function the body
//! calls may panic, which the attribute assumes away, and its validity rests on the
//! dependency-soundness premise docs/TCB.md names for a safe `assume_total` wrapper.
//!
//! What the body holds (review of this rule, 2026-09-30). The first two predicates
//! read calls, and the gate reads a call's TOP-LEVEL type arguments only. MEASURED on
//! the same stage 1, each built exit 0 under certify and the default policy with only
//! the `assumed-total` line, and RETURNED a wrong value (`[0]` for `p([u32::MAX])`)
//! linked into a verify-off `main`, and none makes a call the two predicates flag:
//! under `-Zinline-mir=yes` (or `-Copt-level=3 -Zmir-opt-level=2`),
//! `v.iter().copied().map(add1).collect()` — the inliner turns `map(add1)` into an
//! aggregate, and the one call left, `<Vec<u32> as SpecFromIterNested<u32, Map<…,
//! fn(u32) -> u32 {add1}>>>::from_iter`, names `add1` only inside an ADT type argument
//! (also `dep::add1`, and a fn-pointer parameter a verified caller filled); and, at
//! every opt-level, `add1` reified and handed to a verify-off dependency's
//! non-generic `apply(f: fn(u32) -> u32, y)`, or a fn-pointer parameter handed on the
//! same way, or `dep::Wrap(add1)` unsized to a `dyn` of a dependency trait whose
//! generic impl calls it. A body's TYPES show each: the `Map<…, fn {add1}>` local, the
//! reified pointer's local and the `add1` constant, the parameter, the `Wrap<fn
//! {add1}>` local. So the rule also asks the type of every local and constant
//! ([`uncharged_callable_component`], at any depth of generic arguments) for a
//! `requires`-carrying function item, a fn pointer, a `dyn Fn`, a callable type
//! parameter, or a foreign closure — asked only when the first two find nothing, so
//! it adds no refusal to a body they flag. Reconciled with main (2026-10-02): the
//! ADT-residual rules above (prepared, not built) make the indirect-call gate itself
//! refuse three of these — an owing ITEM anywhere inside a call's type argument (the
//! inlined `Map<…, fn {add1}>`, `dep::add1` too), and a cast whose source carries one
//! (`add1` reified for `apply`, `&Wrap(add1)` unsized to the `dyn`) — so for them the
//! gate clause answers first and names the item, and the held walk is what still
//! flags the fn-POINTER shapes no type names an item in (the parameter in the `Map`,
//! the parameter handed on). Verified, the inlined `collect` shapes are refused by
//! rows unrelated to `add1` too (its `NonNull` casts, `PtrOffset` and the uncounted
//! `collect` allocation), as the same body without the attribute is. The value
//! routes are refused by the dependency call's absent-callee row, as without the
//! attribute.
//!
//! What its CONSTANTS hold (second review, 2026-09-30). A type does not show a
//! function pointer stored in a FIELD. MEASURED on the same stage 1, each built exit 0
//! under certify and the default policy at `-O0`, `-Zinline-mir=yes` and `-Copt-level=3
//! -Zmir-opt-level=2` with only the `assumed-total` line, and RETURNED `[0]`:
//! `vo::run_h(&vo::H { f: add1 }, y)`, with a verify-off dependency's `pub struct H {
//! pub f: fn(u32) -> u32 }` and `run_h(h: &H, y) { (h.f)(y) }` — `&vo::H { f: add1 }`
//! is PROMOTED, so the reification is in `p::promoted[0]`, a body no pass verifies,
//! and `p` holds only a `&vo::H` constant — and the same `H` built in a local `const`
//! item (by reference or by value), an associated or an inline `const`, or a `static`;
//! the cross-crate `dep::add1` in the promoted; and a `static SD: &(dyn vo::Tr + Sync)
//! = &vo::Wrap(add1)` whose method the body calls. So the rule also reads the VALUE of
//! every constant operand ([`uncharged_callable_in_constant_value`]): it evaluates the
//! constant and follows its allocations' pointer provenance, asking each function
//! pointer's instance, each vtable's concrete type and each static's initializer, and
//! it fails closed where it cannot read. MEASURED: this walk, compiled VERBATIM into a
//! `rustc_private` driver on the installed trust toolchain (`321aaeda7`, the nearest
//! build that ships the compiler's crates; two `trust_mir_extract` helpers newer than
//! it stood in) and run at the end of `optimized_mir` — the query `TrustVerify` runs
//! in, as its last pass — names `add1` (or `dep::add1`) in every one of those bodies at
//! the three flag sets, and nothing in the `requires`-free twins (`inc` in the promoted
//! `H`, and in the `static`).
//!
//! What the impls of the types it names hold (third review, 2026-10-02). A dependency
//! generic over `T: vo::HasH` evaluates `T::H` itself, so a LOCAL impl `impl vo::HasH
//! for MyT { const H: vo::H = vo::H { f: add1 }; }` hands `add1` to
//! `vo::run_assoc::<MyT>(y)` with nothing in the `assume_total` body naming it (also
//! `const F: fn(u32) -> u32 = add1`). MEASURED OPEN at `-O0` by the review, with a
//! verify-off `vo`. No call need name `MyT` (fourth review, predicted by reading): an
//! unsizing coercion, `vo::run_dyn(&MyT, y)` reaching the dependency's blanket `impl<T:
//! HasH> Run for T` through `&dyn vo::Run`, or drop glue, `vo::Guard::<MyT>`'s `Drop`
//! reading `T::H`, reaches it as well. So the rule also evaluates, for every LOCAL type
//! the body names ANYWHERE — in a local's or a constant's type at any depth, through a
//! local ADT's fields, an opaque type's hidden type and a projection, and in a type a
//! constant's VALUE names (a vtable's concrete type, a reified instance) — the
//! associated constants of this crate's impls of FOREIGN traits whose trait reference
//! mentions it, and walks their values as a constant operand's; an impl's associated
//! types and its constants' values are keyed in turn, to a fixed point
//! ([`local_impl_associated_constants_held`]; prepared, not built). An impl with type
//! or const parameters answers "cannot read" (fail-closed). A local trait is not read:
//! only this crate's own code can name it, and that code is a verified body or an
//! `assume_total` one, each refused by a gate for a call through the constant's fn
//! pointer.
//!
//! NOT reached (residuals). Where the callable is minted decides who could refuse it:
//!  * in a VERIFIED body, as a value whose type does not show it — `add1` reified
//!    into a dependency struct's non-generic `fn` field by the caller and handed, by
//!    reference, through the `assume_total` body to the dependency's function that
//!    calls the field; `&dep::Wrap(add1)` unsized to `&dyn dep::Tr` in the caller,
//!    whose method the body calls; a type parameter `T: dep::Tr` the caller
//!    instantiates with `dep::Wrap<fn {add1}>`. Each built exit 0 and returned `[0]`
//!    at `-O0` on `fbc6068e3`, and the walk finds nothing in the `assume_total` body.
//!    Reconciled with main: the ADT-residual rules refuse each of the three in the
//!    verified CALLER (a cast whose source carries `add1`; an owing item inside a
//!    call's type argument) — predicted, those rules are prepared and not built —
//!    unless the reification is in the caller's PROMOTED (next bullet). Not refused
//!    there, and OPEN: the caller's `&MyT` unsized to `&dyn vo::Run` and handed
//!    through the body to `vo::run_dyn` (the cast's source carries no owing item, and
//!    the body names only `dyn vo::Run`, so the associated-constant walk never keys
//!    `MyT`);
//!  * in a body NO pass verifies — a `static`'s or `const`'s initializer, another
//!    body's promoted: `static HG: H = H { f: add1 }`, returned to the body by a
//!    verified `fn table() -> &'static H { &HG }` at `-O0` (inlined, `table` puts the
//!    static among the body's own constants, and the value walk reaches it: MEASURED
//!    with the driver at `-Zinline-mir=yes` and `-Copt-level=3 -Zmir-opt-level=2`); the
//!    caller's `call(&vo::H { f: add1 }, v)`, whose reification is `p::promoted[0]`.
//!    OPEN until 2026-10-03; the minting-site seam refuses both where they are minted
//!    — `HG`'s initializer, `p::promoted[0]` (MEASURED 2026-10-03);
//!  * through the trait impl of a type the body names, by a METHOD (measured
//!    OPEN at `-O0` by the third review): a verify-off DEFAULT method of the
//!    dependency's trait that returns or calls the function, or a verified impl
//!    method that returns it (`impl vo::HasG for MyT { fn g() -> fn(u32) -> u32 {
//!    add1 } }`, with `vo::run_g::<MyT>(y)`). A verified method that mints the
//!    pointer by a cast in its own body is refused there by the ADT-residual cast rule
//!    (MEASURED 2026-10-03); one that returns a pointer minted in a `static`, a `const`
//!    or a promoted, or returns the item through an opaque type (`fn g() -> impl
//!    Fn(u32) -> u32 { add1 }`, an RPITIT), was OPEN, and the minting-site seam
//!    (2026-10-03, MEASURED) refuses it where it is minted. A verify-off
//!    default method reaches only what the local impl supplies — an associated
//!    constant, a method's value, an impl method's own `requires` (refused at the impl,
//!    `trait_impl_requires`) — each minted in local code the seam or a gate reads;
//!  * the same associated-constant route through a type the body does not NAME: a
//!    type parameter of a GENERIC `assume_total` body that a verified caller
//!    instantiates with the local type (the body's calls name the parameter; the
//!    caller's call names `MyT`, an ADT with no owing item), or a value made for it
//!    in any other verified body — a caller (previous bullet) or a callee that
//!    returns it (`fn mk() -> &'static dyn vo::Run { &MyT }`, then `vo::run_dyn(mk(),
//!    y)` in the body, at `-O0`; also a `static` reached through a call's return
//!    value). OPEN until 2026-10-03: the minting-site seam refuses the local impl's
//!    `const H: vo::H = vo::H { f: add1 }` itself, wherever `MyT` later travels
//!    (MEASURED 2026-10-03; the two `dyn` shapes turned out refused already, by the
//!    spawn census's `UnmodeledThreadSpawnEffect` rows on `add1` and on the body that
//!    unsizes `&MyT`, on strict and certify). (A FOREIGN impl's constant can hold a local
//!    function only through the impl's type arguments, which the walk keys — by
//!    reading, not probed. A coroutine's saved locals are not keyed: a local
//!    coroutine is its own body, walked or verified there.)
//! Without the attribute each body is refused by the dependency call's absent-callee
//! row, which the skip removes by design (the dependency-soundness premise). The rule
//! that closes the minting routes is at the minting site, and since 2026-10-03 it is
//! built and tested: "The minting-site seam" below. Still not reached: a value
//! minted in a VERIFY-OFF crate, a value written at run time into a mutable static by
//! code no verdict covers, and a callable that reaches a body from OUTSIDE as a
//! parameter (refused where this compilation mints it, never at the hand-over). Nor
//! does the held-callable type walk open an ADT's FIELDS (only the associated-constant
//! walk's keying opens a LOCAL ADT's), nor does any walk follow a method.
//!
//! Cost (the same stage 1; each body WITHOUT the attribute, and with the attribute
//! plus an empty `unsafe {}` that routes it through D8-P0's verify-in-full, stands
//! in for the rule): a call whose clause the body proves still builds
//! (`if y < 100 { add1(y) } else { 0 }`, with the warning), but the body's other rows
//! are charged too — the same guarded call to a DEPENDENCY's function now meets the
//! absent-callee row the skip removed, and any panic the author assumed is charged.
//! A fn-pointer or `dyn Fn` parameter called in an `assume_total` body is refused
//! whatever its target, `requires`-free ones included, as the gate refuses it in any
//! verified body (the call site cannot see the target); so is every other callable
//! the gate refuses — a generic `F: Fn` parameter called, a sysroot item that may
//! panic handed to generic code (`fold(100, u32::div_euclid)`), a local closure
//! coerced to a fn pointer — each of which built exit 0 with the attribute. The
//! held-callable predicate adds: a fn pointer held as DATA anywhere in a local's or
//! constant's type (`Option<fn()>`, a `LazyLock<T>`, whose default `F` is `fn() -> T`)
//! loses the skip, and so may a body whose inlined sysroot code mints a fn pointer
//! under an explicit inliner flag, where the same body keeps it at `-O0` (as a
//! `requires` call the L3 rule keeps in an inlined helper does) — the common case is
//! formatting: `println!("{x}")`'s inlined `Argument::new_display` mints a `fn(&u32,
//! &mut Formatter) -> Result` local and its `unsafe fn(NonNull<()>, …)` transmute
//! (MEASURED with the driver on `assume_total_safe_body_keeps_its_skip.rs`'s
//! `print_total` at `-Zinline-mir=yes` and at `-Copt-level=3 -Zmir-opt-level=2`; at
//! `-O0` its walk is empty). The constant-value walk adds only its fail-closed arms: a
//! constant that does not evaluate in the body's typing environment (a generic one), a
//! pointer to an `extern` static, a static read from a `const fn`'s body; the
//! associated-constant walk adds a GENERIC local impl of a foreign trait with
//! associated constants, for a local type the body names anywhere, and turns an
//! associated constant of such an impl that does not evaluate — used or not — into a
//! build error (const-eval reports it); and its key walk's step budget makes a body
//! that names a polymorphically recursive local ADT (`struct Nested<T> { v: T, inner:
//! Option<Box<Nested<(T, T)>>> }`) lose the skip (fail-closed; the walk opens a new
//! type at every step) when the crate has a local impl of a foreign trait with
//! associated constants or types (an `impl Iterator` is one; without one the walk does
//! not run). Two over-refusals the review measured are gone (2026-10-02,
//! prepared, not built): a `PhantomData<fn() -> T>` marker (a `PhantomData` holds no
//! value, so only what its TYPE hands over is asked — an owing item, a callable type
//! parameter), and a dependency's `thread_local!` read (`dep::COUNTER.with(|c|
//! c.get())`) or static table of closures coerced to fn pointers (a coerced closure
//! captures nothing and carries no `requires`, so its parent's type arguments are
//! asked instead of the closure answering "uncharged"; a closure's generics parent is
//! its typeck root, so `thread_local!`'s accessor in a non-generic `static` has none).
//! A local `requires`-free item reified and called or handed on, a `requires`-free
//! item in the inlined `Map` or in a promoted, `const` or `static` value, and a local
//! closure handed to `map` keep the skip. The gate clause is not narrowed to the
//! callables that can carry a `requires`: a type parameter's instantiation is not
//! always gated at a caller — a generic impl's method reached through `dyn` is
//! instantiated by an unsizing coercion, which no gate reads — so trusting one would
//! rest on another lane's refusal of the `dyn` call. (A NAMED `requires`-free item —
//! `u32::div_euclid` — could be admitted soundly: its only
//! hazard is a panic; docs/DECISION_QUEUE.md, AT-REQ-1, records it.) No in-tree
//! `assume_total` body calls a `requires` function, makes a call the gate refuses or
//! holds a callable the walk flags (census: docs/KNOWN_HAZARDS.md, "FIX PREPARED
//! 2026-09-30 … `#[trust::assume_total]` charged none of its calls"; the held walk
//! MEASURED with the driver on every revision of every in-tree file that applies the
//! attribute: each attributed body's list is empty, except D8-P0's
//! `safe_extern_static`, whose pointer to an `extern` static D8-P0's own predicate,
//! asked first, already verifies).
//!
//! ## The minting-site seam (2026-10-03, built and tested)
//!
//! Every rule above reads a VERIFIED body. A `requires`-carrying function turned into a
//! value anywhere else was refused by nobody: a promoted (`&vo::H { f: add1 }` in any
//! owner — an `assume_total` body, a verified caller, a skipped or generic one), the
//! initializer of a `static`, a `const`, an associated constant (a generic impl's and a
//! trait default included), an inline or anonymous constant, a compile-time function,
//! and a value that leaves its body through an opaque return type (`fn g() -> impl
//! Fn(u32) -> u32 { add1 }`, `once(y).map(add1)` at `-Zmir-opt-level=2`, an RPITIT).
//! [`refuse_requires_carrying_values_minted_outside_verified_bodies`], called once per
//! crate from `trust_ensure_whole_crate_verification` at top level, reads each of those
//! bodies with the gate's own collector ([`collect_requires_carrying_values`]: R1 a call's
//! type argument — a generic `const fn` handed `add1` in an initializer — R2 a cast, R4
//! an unevaluated constant's arguments, R5 an evaluated constant's allocations, R6 an asm
//! `sym` operand, and a dropped place's type), asks every local opaque type's hidden type
//! (R7), and every `global_asm!` `sym` operand (R6), and refuses at the minting site: an
//! error on strict, the default policy, certify and memory-safe, a warning under advisory.
//! The indirect-call gate gains R4, R5, R6 and the drop rule for verified bodies
//! ([`body_mints_requires_carrying_value`]): at `-Zmir-opt-level=2` an inlined generic
//! `mk::<fn {add1}>` leaves only its promoted, `Unevaluated { def: mk, promoted: 0, args:
//! [fn {add1}] }`, where `-O0` refuses the call by rule (1). The local-closure carve-out
//! holds there too: a promoted a local closure owns is walked as the closure type its
//! arguments describe, and an inline `const`'s own type placeholder is not walked.
//!
//! Cost (docs/DECISION_QUEUE.md, AT-REQ-2): a static dispatch table of `requires`
//! handlers, a `const _: fn(u32) -> u32 = add1` signature check, an anonymous constant
//! that reifies one (its value cannot carry the pointer), a compile-time-only use in an
//! initializer (`size_of_val(&add1)`), an opaque return carrying the item even where only
//! verified callers exist, an async block or coroutine that captures one, a value of a
//! type carrying one that this body drops, and at `-Zmir-opt-level=2` an inlined generic
//! callee's promoted instantiated with one. Not reached: a verify-off crate's minting
//! (the dependency-soundness premise), a run-time write into a static, a direct call to a
//! `requires` function inside an initializer (CTFE runs the un-elided `mir_for_ctfe` of a
//! `const fn`), the local types of the bodies read (a promoted `&add1` mints nothing), and
//! Clean-origin preconditions (`def_owes_caller_precondition` does not read them; empty
//! today). R5 is a latent guard: no MIR the tree builds today holds a pointer-valued
//! constant (GVN does not propagate one), but the trust-ir flips — on by default under
//! `-Ztrust-verify=on` with `-Cdebuginfo=0` — re-derive bodies that could. No fixture
//! fails without R5, and none pins the gate's R6 or its drop rule (defense in depth: a
//! verify-off dependency's `Drop` that drop glue runs is also that call's absent-callee
//! row, and `assume_total`'s held walk reads the dropped local's type).

use super::{PreparedDiagnostic, PreparedDiagnosticChild, PreparedLocatedDiagnostic};

use rustc_middle::mir::visit::Visitor as _;

use super::*;

/// The types a SYSROOT closure, coroutine-closure or coroutine can hand to the code
/// it calls: its parent's generic TYPE arguments and its captured upvars. `None`
/// for a local one (verified as its own body, so the calls it makes are its own
/// rows), for a closure of a non-sysroot crate (refused whole by
/// `callable_type_arg_is_unresolved_inner` before this is asked), and for anything
/// that is not a closure or coroutine.
///
/// Only what the closure can CALL: not its signature part (a `fn` POINTER type that
/// describes the closure's own signature and is no value it holds), its kind, or a
/// coroutine's resume/yield/witness types. The parent's type arguments are taken
/// whole, so a data type among them (an iterator's element type) is asked too — the
/// fail-closed over-refusal the module doc records.
pub(super) fn sysroot_closure_callable_parts<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
) -> Option<Vec<Ty<'tcx>>> {
    let def_id = match *ty.kind() {
        ty::Closure(def_id, _) | ty::CoroutineClosure(def_id, _) | ty::Coroutine(def_id, _) => {
            def_id
        }
        _ => return None,
    };
    if def_id.is_local() || !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id) {
        return None;
    }
    closure_callable_parts(ty)
}

/// What a closure, coroutine-closure or coroutine of ANY crate can hand to the code it
/// calls — its parent's generic TYPE arguments and its captured upvars, the parts
/// [`sysroot_closure_callable_parts`] describes — or `None` for anything else. Which
/// crates' closures may be looked into is the caller's question.
fn closure_callable_parts<'tcx>(ty: Ty<'tcx>) -> Option<Vec<Ty<'tcx>>> {
    let (parent_args, upvars) = match *ty.kind() {
        ty::Closure(_, args) => {
            let args = args.as_closure();
            (
                args.parent_args().iter().filter_map(|arg| arg.as_type()).collect::<Vec<_>>(),
                args.upvar_tys(),
            )
        }
        ty::CoroutineClosure(_, args) => {
            let args = args.as_coroutine_closure();
            (
                args.parent_args().iter().filter_map(|arg| arg.as_type()).collect::<Vec<_>>(),
                args.upvar_tys(),
            )
        }
        ty::Coroutine(_, args) => {
            let args = args.as_coroutine();
            (
                args.parent_args().iter().filter_map(|arg| arg.as_type()).collect::<Vec<_>>(),
                args.upvar_tys(),
            )
        }
        _ => return None,
    };
    Some(parent_args.into_iter().chain(upvars.iter()).collect())
}

/// Trust (2026-09-30, residual L1): does the SYSROOT closure, coroutine-closure or
/// coroutine `ty`, handed to a direct call as a type argument, carry a callable
/// `callable_type_arg_is_unresolved_inner` answers "unresolved" for in what it was
/// instantiated with ([`sysroot_closure_callable_parts`])? `false` for a local
/// closure or coroutine and for a foreign non-sysroot coroutine, as before.
pub(super) fn sysroot_closure_carries_unresolved_callable<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    sysroot_closure_callable_parts(tcx, ty).is_some_and(|parts| {
        parts.into_iter().any(|part| callable_type_arg_is_unresolved_inner(tcx, typing_env, part))
    })
}

/// Does a call to the function item `def_id` at `args` owe its caller a
/// `requires`? A LOCAL item is asked as named and as resolved in this body
/// (`local_fn_item_owes_caller_precondition`). A FOREIGN item of a non-sysroot
/// crate is asked from the contract set its crate exported (`trust_contracts`,
/// served from rmeta), the set a DIRECT cross-crate call is charged from. A
/// sysroot item is not asked: the sysroot is built verify-off, so no check of its
/// was elided under a clause, and the gate judges it by its panics instead
/// (`foreign_fn_item_type_arg_is_accounted`).
fn fn_item_owes_caller_precondition<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if def_id.is_local() {
        local_fn_item_owes_caller_precondition(tcx, typing_env, def_id, args)
    } else {
        !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
            && trust_mir_extract::def_owes_caller_precondition(tcx, def_id)
    }
}

/// Trust (2026-09-30, review of residual L2): does a DIRECT call to `def_id` at
/// `args` owe its caller a `requires` — the `Precondition` row the direct-call lane
/// charges? A local item is asked as named and as resolved
/// (`local_fn_item_owes_caller_precondition`); any other item from the contract set
/// its crate exported, sysroot included: unlike [`fn_item_owes_caller_precondition`]
/// (which names an item for a note), this decides whether a body that charges no
/// call may be admitted, and the direct-call lane charges a sysroot callee's clause
/// too (none carries one today).
fn direct_callee_owes_caller_precondition<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: DefId,
    args: ty::GenericArgs<'tcx>,
) -> bool {
    if def_id.is_local() {
        local_fn_item_owes_caller_precondition(tcx, typing_env, def_id, args)
    } else {
        trust_mir_extract::def_owes_caller_precondition(tcx, def_id)
    }
}

/// Trust (2026-09-30, the ADT residual): the function item `ty` IS, when a call to
/// it owes its caller a `requires` ([`fn_item_owes_caller_precondition`]); `None`
/// for any other type — a fn POINTER included, whose value no type names.
fn owing_fn_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<DefId> {
    let ty::FnDef(def_id, args) = *ty.kind() else { return None };
    let owes = if args.has_escaping_bound_vars() {
        // Under a binder (a fn-pointer signature, a trait object's predicates) an
        // item's arguments may name a bound region, which instance resolution does
        // not take: ask the item as NAMED only, the contract set a direct call to it
        // is charged from.
        (def_id.is_local() || !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id))
            && trust_mir_extract::def_owes_caller_precondition(tcx, def_id)
    } else {
        fn_item_owes_caller_precondition(tcx, typing_env, def_id, args.skip_binder())
    };
    owes.then_some(def_id)
}

/// Push onto `owing` every function item owing a caller precondition that the
/// type `ty` carries ANYWHERE inside it ([`owing_fn_item`] over `Ty::walk`, the walk
/// `ty_carries_masked_fail_closed_fn_value` makes): the item itself, behind a
/// reference or a `Box`, in an ADT's type arguments (`Map<Once<u32>, fn(u32) -> u32
/// {add1}>`, the ADT residual), in a sysroot closure's parent arguments or captures
/// (L1), in a closure's signature. One exception, a LOCAL closure's capture that is
/// itself a function item (behind `&`, `&mut` or `Box` at most): only the closure's
/// own body, which is verified, can call it (see the module doc). Every other capture
/// of a local closure is walked. A fn POINTER is never matched.
fn collect_requires_carrying_callables<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    owing: &mut Vec<DefId>,
) {
    collect_requires_carrying_callables_in(tcx, typing_env, ty, owing, &mut FxHashSet::default());
}

/// [`collect_requires_carrying_callables`], with the types already walked in this
/// query. A local closure is walked through its parts, each in a walk of its own,
/// and nested local combinators share parts (a closure capturing a value of its
/// parent's type argument `F` has `F` among both), so without the shared set a
/// nest of depth `d` would be walked `2^d` times (review of the ADT residual).
fn collect_requires_carrying_callables_in<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    owing: &mut Vec<DefId>,
    visited: &mut FxHashSet<Ty<'tcx>>,
) {
    let mut walker = ty.walk();
    while let Some(arg) = walker.next() {
        let Some(t) = arg.as_type() else { continue };
        if !visited.insert(t) {
            walker.skip_current_subtree();
            continue;
        }
        match *t.kind() {
            ty::FnDef(..) => owing.extend(owing_fn_item(tcx, typing_env, t)),
            ty::Closure(def_id, args) if def_id.is_local() => {
                walker.skip_current_subtree();
                let args = args.as_closure();
                let parts = args
                    .parent_args()
                    .iter()
                    .filter_map(|arg| arg.as_type())
                    .chain([args.sig_as_fn_ptr_ty()])
                    .chain(args.upvar_tys().iter().filter(|upvar| {
                        !matches!(peel_fn_forwarding_layers(*upvar).kind(), ty::FnDef(..))
                    }));
                for part in parts {
                    collect_requires_carrying_callables_in(tcx, typing_env, part, owing, visited);
                }
            }
            _ => {}
        }
    }
}

/// Trust (2026-09-30, the ADT residual): does the type argument `ty` of a direct
/// call — `Self` included — carry a function item owing its caller a `requires`
/// anywhere inside it ([`collect_requires_carrying_callables`])? The indirect-call
/// gate asks it of every type argument after the question it asks of the argument
/// as it stands (`callable_type_arg_is_unresolved`), and of the item a reified-constant
/// pointer call names (`indirect_callee_is_a_reified_constant`); `true` makes the
/// argument, or the call, "unresolved". Under `TRUST_VANILLA_DEBUG=1` it names the
/// item, the pin that THIS rule refused.
pub(super) fn ty_carries_requires_carrying_fn_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> bool {
    let mut owing: Vec<DefId> = Vec::new();
    collect_requires_carrying_callables(tcx, typing_env, ty, &mut owing);
    let Some(&item) = owing.first() else { return false };
    if env_flag_enabled("TRUST_VANILLA_DEBUG") {
        eprintln!(
            "[CALLABLE_TYPE_ARG] `{}` owes its caller a `requires` and is carried inside a \
             type argument; not resolved",
            trust_mir_extract::safe_def_path_str(tcx, item),
        );
    }
    true
}

/// Trust (2026-10-03, the minting-site seam): HOW a body turns a function item that owes
/// its caller a `requires` into a value no call site charges
/// ([`collect_requires_carrying_values`]). Every rule walks a TYPE with
/// [`collect_requires_carrying_callables`], so the predicate (an item as named and as
/// resolved, a foreign one from its exported contract set, no sysroot item), the
/// item-only match and the local-closure capture carve-out are that walk's, unchanged.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MintedBy {
    /// R2 (2026-09-30): the SOURCE of a cast — `add1 as fn(u32) -> u32`, `&add1` or a
    /// `Map` over it unsized to a `dyn`, a reified `run::<Map<…, fn(u32) -> u32 {add1}>>`.
    /// Any cast kind and any operand, as the masked-source cast scan of
    /// `function_has_masked_fail_closed_dispatch_except` reads them.
    Cast,
    /// R1 (2026-09-30): a type argument of a call, `Self` included — `vo::mk_h(add1)`,
    /// `size_of_val(&add1)`. The item is read off the callee operand's TYPE, so a call
    /// through a local holding the item counts. The indirect-call gate asks this itself,
    /// call by call (`callable_type_arg_is_unresolved`).
    CallTypeArg,
    /// R4 (2026-10-03): the arguments of an UNEVALUATED constant — a generic `const`
    /// item, an associated constant, a promoted, an inlined callee's included
    /// (`Unevaluated { def: mk, promoted: 0, args: [fn(u32) -> u32 {add1}] }` once a
    /// generic `mk` is inlined at `-Zmir-opt-level=2`). Read from every constant operand
    /// and from the body's `required_consts`.
    GenericConstant,
    /// R5 (2026-10-03): an EVALUATED constant whose allocations, followed through their
    /// pointer provenance, hold a function pointer or a vtable made for such an item.
    FnPointerConstant,
    /// R6 (2026-10-03): an inline-asm or `global_asm!` `sym` operand.
    AsmSym,
    /// (2026-10-03) The type of a place a `Drop` terminator drops: its drop glue is code
    /// no call in this body names, and a dependency's `Drop` impl generic over a
    /// callable can conjure the item and call it.
    DropGlue,
    /// R7 (2026-10-03, the seam only): the hidden type of a local opaque type.
    OpaqueHiddenType,
}

impl MintedBy {
    /// How the item became a value, for a debug pin and a note: the text that follows
    /// "`<item>` owes its caller a `requires` and". `Cast`'s is the one the gate printed
    /// before this change, kept byte for byte (the ui fixtures match on it).
    fn describe(self) -> &'static str {
        match self {
            MintedBy::Cast => "is cast to a fn pointer or a `dyn`, which no longer names it",
            MintedBy::CallTypeArg => "is carried inside a call's type argument",
            MintedBy::GenericConstant => "is carried in a generic constant's arguments",
            MintedBy::FnPointerConstant => {
                "is a function pointer or a vtable in an evaluated constant's value"
            }
            MintedBy::AsmSym => "is named by an asm `sym` operand",
            MintedBy::DropGlue => "is in the type of a value this body drops",
            MintedBy::OpaqueHiddenType => "is in the hidden type of an opaque type",
        }
    }
}

/// Trust (2026-10-03): one value [`collect_requires_carrying_values`] found.
#[derive(Clone, Copy, Debug)]
struct MintedValue {
    /// The function item that owes its caller a `requires`. `None` for an evaluated
    /// constant whose allocations the walk could not all follow (R5's fail-closed
    /// answer: a dangling allocation or the step budget).
    item: Option<DefId>,
    span: rustc_span::Span,
    by: MintedBy,
}

/// The MIR walk behind [`collect_requires_carrying_values`].
struct MintingSites<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    body: &'a Body<'tcx>,
    out: &'a mut Vec<MintedValue>,
}

impl<'a, 'tcx> MintingSites<'a, 'tcx> {
    fn walk(&mut self, ty: Ty<'tcx>, span: rustc_span::Span, by: MintedBy) {
        let mut owing: Vec<DefId> = Vec::new();
        collect_requires_carrying_callables(self.tcx, self.typing_env, ty, &mut owing);
        self.out.extend(owing.into_iter().map(|item| MintedValue { item: Some(item), span, by }));
    }

    /// R4. The arguments of an unevaluated constant are walked as a type argument is,
    /// with two corrections (third critique of the seam's plan, 2026-10-03), each
    /// keeping what main accepts:
    ///  * a promoted of a LOCAL CLOSURE carries the closure's own arguments — `[parent..,
    ///    kind, signature, upvars]` — once the closure is inlined into its parent, so
    ///    they are walked as the closure TYPE they describe
    ///    ([`local_closure_owning_constant`]), and the local-closure capture carve-out
    ///    applies: `let g = add1; let c = move |x: u32| -> &'static u32 { if x < 100 &&
    ///    g(x) > k { &1 } else { &0 } }; c(y)` at `-Zmir-opt-level=2` is not refused by
    ///    this rule (no `[CALLABLE_TYPE_ARG]`; it builds on certify), as rule (1) does not
    ///    refuse it at `-O0` (no `[CALLABLE_TYPE_ARG]` there either). The BODY is not
    ///    accepted at `-O0`: on certify and the default policy it is refused, before this
    ///    rule as after it, by the native verifier's own rows — the closure aggregate whose
    ///    capture is the item is unsupported MIR (`AggregateKind::Closure`) — and by no
    ///    rule of the gate. The fixture's `capture_promoted_o3_certify` and
    ///    `capture_o0_certify` pin both halves; `capture_call_o0`
    ///    (`requires_callee_inside_adt_type_argument.rs`) is the capturing shape `-O0`
    ///    accepts, on the default policy. A coroutine's or coroutine-closure's arguments
    ///    are walked whole: no carve-out, as main has none for them;
    ///  * an INLINE `const { … }`'s last argument is its own type placeholder, the type of
    ///    the value the block makes: only the parent's arguments are walked. What the
    ///    block makes is read where it is made — its own `mir_for_ctfe`, which the seam
    ///    reads — and what the parent does with the value (a call, a cast, a hand-over) is
    ///    the parent's own rows: `if y < 100 { let g = const { add1 }; g(y) } else { 0 }`
    ///    stays accepted.
    fn unevaluated(
        &mut self,
        uv: rustc_middle::mir::UnevaluatedConst<'tcx>,
        span: rustc_span::Span,
    ) {
        let tcx = self.tcx;
        match tcx.def_kind(uv.def) {
            DefKind::AnonConst
                if tcx.anon_const_kind(uv.def)
                    == rustc_middle::ty::AnonConstKind::NonTypeSystemInline =>
            {
                let parent = uv.args.as_slice().split_last().map_or(&[][..], |(_, parent)| parent);
                for ty in parent.iter().filter_map(|arg| arg.as_type()) {
                    self.walk(ty, span, MintedBy::GenericConstant);
                }
            }
            DefKind::Closure => match local_closure_owning_constant(tcx, uv.def, uv.args) {
                Some(closure) => self.walk(closure, span, MintedBy::GenericConstant),
                None => {
                    for ty in uv.args.types() {
                        self.walk(ty, span, MintedBy::GenericConstant);
                    }
                }
            },
            _ => {
                for ty in uv.args.types() {
                    self.walk(ty, span, MintedBy::GenericConstant);
                }
            }
        }
    }

    /// R5. An evaluated constant is followed through its allocations' pointer provenance
    /// ([`walk_constant_allocations`], the held walk's traversal and step budget): each
    /// function pointer's instance is walked as the callable its TYPE is, each vtable
    /// through the concrete type it was made for, plain memory is followed. A `static`
    /// is NOT followed: its value is judged where it is made — the seam reads a local
    /// static's initializer, a foreign one is its own crate's — and reading through it
    /// would refuse, at every use, the address of a static whose initializer the seam
    /// already refuses (and fail closed on every `extern` static). A walk that cannot
    /// finish answers `item: None` (fail-closed).
    ///
    /// Inert on the MIR the tree builds today, by reading: MIR building names a function
    /// item as a zero-sized constant and a `static` by its address, and GVN does not
    /// propagate a pointer-valued constant (`gvn.rs`, "Check that we do not leak a
    /// pointer"). It guards the trust-ir flips (the codegen flip of `optimized_mir` and
    /// the CTFE flip of `mir_for_ctfe`, on by default under `-Ztrust-verify=on` with
    /// `-Cdebuginfo=0`), whose re-derived body could hold the reified pointer as a
    /// `Function` allocation instead of a cast. No fixture fails without it.
    fn evaluated(&mut self, value: rustc_middle::mir::ConstValue, span: rustc_span::Span) {
        use std::ops::ControlFlow;

        use rustc_middle::mir::interpret::GlobalAlloc;

        let Some(root) = constant_value_root(value) else { return };
        let (tcx, typing_env) = (self.tcx, self.typing_env);
        let mut named: Vec<Ty<'tcx>> = Vec::new();
        let walked = walk_constant_allocations(tcx, root, |global| {
            match global {
                GlobalAlloc::Function { instance } => named.push(instance.ty(tcx, typing_env)),
                GlobalAlloc::VTable(concrete, _) => named.push(concrete),
                GlobalAlloc::Memory(alloc) => return ControlFlow::Continue(Some(alloc)),
                GlobalAlloc::Static(_) | GlobalAlloc::TypeId { .. } => {}
            }
            ControlFlow::<(), _>::Continue(None)
        });
        for ty in named {
            self.walk(ty, span, MintedBy::FnPointerConstant);
        }
        if walked.is_err() {
            self.out.push(MintedValue { item: None, span, by: MintedBy::FnPointerConstant });
        }
    }
}

impl<'a, 'tcx> rustc_middle::mir::visit::Visitor<'tcx> for MintingSites<'a, 'tcx> {
    fn visit_statement(
        &mut self,
        statement: &Statement<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if let StatementKind::Assign(boxed) = &statement.kind
            && let Rvalue::Cast(_, operand, _) = &boxed.1
        {
            let source = operand.ty(&self.body.local_decls, self.tcx);
            self.walk(source, statement.source_info.span, MintedBy::Cast);
        }
        self.super_statement(statement, location);
    }

    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        let span = terminator.source_info.span;
        match &terminator.kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                if let ty::FnDef(_, args) = *func.ty(&self.body.local_decls, self.tcx).kind() {
                    for ty in args.skip_binder().types() {
                        self.walk(ty, span, MintedBy::CallTypeArg);
                    }
                }
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                for operand in operands.iter() {
                    if let rustc_middle::mir::InlineAsmOperand::SymFn { value } = operand {
                        self.walk(value.const_.ty(), value.span, MintedBy::AsmSym);
                    }
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let dropped = place.ty(&self.body.local_decls, self.tcx).ty;
                self.walk(dropped, span, MintedBy::DropGlue);
            }
            _ => {}
        }
        self.super_terminator(terminator, location);
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        _: rustc_middle::mir::Location,
    ) {
        match constant.const_ {
            Const::Unevaluated(uv, _) => self.unevaluated(uv, constant.span),
            Const::Val(value, _) => self.evaluated(value, constant.span),
            // A type-system constant: an integer, `bool`, `char` or a valtree of them.
            Const::Ty(..) => {}
        }
    }
}

/// Trust (2026-10-03, R4): the closure TYPE that the arguments of a constant owned by
/// the LOCAL closure `def` describe — a promoted of the closure, inlined into its parent
/// with the closure's own arguments — or `None` when `def` is not a plain local closure
/// (a coroutine, a coroutine-closure, a foreign closure: walked argument by argument), or
/// when the arguments are still the closure's identity PARAMETERS (the closure's own
/// body, where `ClosureArgs`' signature and upvar accessors would not hold, and the
/// parameters carry no item anyway).
fn local_closure_owning_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    args: ty::GenericArgs<'tcx>,
) -> Option<Ty<'tcx>> {
    let local = def.as_local()?;
    let Node::Expr(rustc_hir::Expr { kind: rustc_hir::ExprKind::Closure(closure), .. }) =
        tcx.hir_node_by_def_id(local)
    else {
        return None;
    };
    if !matches!(closure.kind, rustc_hir::ClosureKind::Closure) {
        return None;
    }
    // `ClosureArgsParts`: `[parent.., closure_kind, signature as a fn pointer, upvars]`.
    let [.., _, signature, upvars] = args.as_slice() else { return None };
    let concrete = signature.as_type().is_some_and(|t| matches!(t.kind(), ty::FnPtr(..)))
        && upvars.as_type().is_some_and(|t| matches!(t.kind(), ty::Tuple(..)));
    concrete.then(|| Ty::new_closure(tcx, def, args))
}

/// Trust (2026-10-03, the minting-site seam; generalizes the 2026-09-30 cast scan): push
/// onto `out` every function item owing its caller a `requires` that `body` turns into a
/// value no call site charges, and how ([`MintedBy`]): the source of a cast (R2), a call's
/// type argument (R1), an unevaluated constant's arguments (R4), an evaluated constant's
/// allocations (R5), an asm `sym` operand (R6), a dropped place's type. Unsorted and
/// possibly repeated. Asked of a VERIFIED body by the indirect-call gate
/// ([`body_mints_requires_carrying_value`]) and by the notes that name the item
/// ([`requires_carrying_fn_values`]), and of every body no pass verifies — a promoted, a
/// `const`/`static`/associated/inline/anonymous constant's initializer, a compile-time
/// function — by the seam ([`refuse_requires_carrying_values_minted_outside_verified_bodies`]).
///
/// NOT read, deliberately: the types of a body's LOCALS. A promoted `&add1` holds the
/// item in a local of type `&fn(u32) -> u32 {add1}` and turns it into nothing — what its
/// user does with the reference is the user's row (`dyn_o3`'s `&add1` unsized in the
/// parent is a cast there; `let _r = &add1;` is no value anyone can call through).
fn collect_requires_carrying_values<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    body: &Body<'tcx>,
    out: &mut Vec<MintedValue>,
) {
    MintingSites { tcx, typing_env, body, out }.visit_body(body);
}

/// Trust (2026-09-30, review of the ADT residual; widened 2026-10-03): does this body
/// MINT, from a function item owing its caller a `requires`, a value no call in it
/// charges ([`collect_requires_carrying_values`])? The indirect-call gate asks it after
/// every call has resolved, for the rules its own per-call loop does not ask: a CAST
/// (R2) — the value the cast makes names no item, so the item-only rule
/// ([`ty_carries_requires_carrying_fn_item`]) cannot see it again (`let fp: fn(u32) ->
/// u32 = add1; run(core::iter::once(y).map(fp))` leaves `run::<Map<Once<u32>, fn(u32) ->
/// u32>>` at `-Zmir-opt-level=2`, the same call a pointer PARAMETER makes), so it is
/// caught where it is MINTED, the ground `function_has_masked_fail_closed_dispatch`
/// catches a reified dependency function on; and since 2026-10-03 an unevaluated
/// constant's arguments (R4: an inlined generic callee's promoted, which at `-O0` is the
/// call rule (1) refuses), an evaluated constant's allocations (R5, a guard for the
/// trust-ir flips), an inline-asm `sym` operand (R6) and a dropped place's type. A
/// pointer minted in a promoted, a `const`/`static` initializer or an opaque return is
/// refused by the seam where it is minted
/// ([`refuse_requires_carrying_values_minted_outside_verified_bodies`]); one minted in a
/// verify-off crate, or handed in as a parameter, is not seen here (the module doc, "Not
/// reached"). Under `TRUST_VANILLA_DEBUG=1` it names the first item of each rule that
/// fired; the cast line is the one printed before 2026-10-03, byte for byte.
pub(super) fn body_mints_requires_carrying_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    let mut minted: Vec<MintedValue> = Vec::new();
    collect_requires_carrying_values(tcx, body.typing_env(tcx), body, &mut minted);
    // A call's type arguments are the gate's own question, asked call by call before this
    // (`callable_type_arg_is_unresolved`), with its own pins.
    minted.retain(|value| value.by != MintedBy::CallTypeArg);
    if minted.is_empty() {
        return false;
    }
    if env_flag_enabled("TRUST_VANILLA_DEBUG") {
        let mut printed: Vec<MintedBy> = Vec::new();
        for value in &minted {
            if printed.contains(&value.by) {
                continue;
            }
            printed.push(value.by);
            match value.item {
                Some(item) => eprintln!(
                    "[CALLABLE_TYPE_ARG] `{}` owes its caller a `requires` and {}; not resolved",
                    trust_mir_extract::safe_def_path_str(tcx, item),
                    value.by.describe(),
                ),
                None => eprintln!(
                    "[CALLABLE_TYPE_ARG] a constant whose allocations this compilation cannot \
                     follow; not resolved"
                ),
            }
        }
    }
    true
}

/// The function items owing a caller precondition that this body turns into a value no
/// call site charges ([`collect_requires_carrying_values`]: reified to a fn pointer,
/// unsized to a `dyn`, handed to a call inside a type argument, carried in a constant's
/// arguments or value, named by an asm `sym`, dropped), unsorted and possibly repeated
/// ([`requires_carrying_fn_values`] names them). A call's item is read off the callee
/// operand's TYPE, so a call through a local holding the item counts.
fn requires_carrying_fn_value_defs<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<DefId> {
    let mut minted: Vec<MintedValue> = Vec::new();
    collect_requires_carrying_values(tcx, body.typing_env(tcx), body, &mut minted);
    minted.into_iter().filter_map(|value| value.item).collect()
}

/// Trust (2026-09-29, widened 2026-09-30): the function items owing a caller
/// precondition that this body reifies to a fn pointer or hands to a call as a
/// callable type argument — LOCAL ones since 2026-09-29, and since 2026-09-30 a
/// FOREIGN one (L2), one inside a sysroot closure the MIR inliner built (L1) and one
/// anywhere inside a type argument (the ADT residual) — the shapes
/// `function_has_unresolved_indirect_call` refuses for them. For the
/// refusal's NOTE only: it names the function and the fix, and never decides a
/// verdict. Sorted and deduplicated by path so the note is deterministic.
pub(super) fn requires_carrying_fn_values<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<String> {
    let mut found: Vec<String> = requires_carrying_fn_value_defs(tcx, body)
        .into_iter()
        .map(|def_id| tcx.def_path_str(def_id))
        .collect();
    found.sort();
    found.dedup();
    found
}

/// The refusal note for one function [`requires_carrying_fn_values`] names. The
/// text predates L1/L2 (2026-09-29) and is kept byte for byte: the ui fixtures
/// match on its prefix.
pub(super) fn requires_value_note(callee: &str) -> String {
    format!(
        "`{callee}` carries a `requires` its callers owe, and this function reifies it \
         to a fn pointer or hands it to generic code as a value, where no call site \
         charges that precondition: its body is verified only UNDER the `requires`, so \
         such a call is not covered by its verdict. Options: call it directly — for \
         example through a closure, `|x| {callee}(x)`, where the precondition is \
         charged at the call and must be proved there; or remove the `requires` if \
         `{callee}` is total"
    )
}

/// Trust (2026-09-30, the ADT residual): the notes the indirect-call gate adds, for
/// a body whose native lowering FAILED. `abort_on_full_verification_failure` refuses
/// such a body on the failure and returns before it consults the gate, so a
/// callable the gate refuses there (the `.max()` shape of the module doc) was
/// refused with nothing naming it, and the gate's `TRUST_VANILLA_DEBUG` pin never
/// printed. Empty when the gate passes. Notes only: the body is refused either way.
pub(super) fn lowering_failure_gate_notes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<String> {
    if !function_has_unresolved_indirect_call(tcx, body) {
        return Vec::new();
    }
    let mut notes = vec![String::from(
        "the indirect-call gate refuses this function as well, whether or not the lowering \
         completes: it calls through a fn pointer or hands a function to generic code as a \
         value (`@trust-indirect-callee`)",
    )];
    notes.extend(requires_carrying_fn_values(tcx, body).iter().map(|c| requires_value_note(c)));
    // Trust (2026-10-03): and a std/core/alloc item the policy's rule does not account
    // for (`sysroot_callable_item`; empty on the default policy).
    notes.extend(
        sysroot_callable_item::unaccounted_sysroot_callable_items(tcx, body)
            .iter()
            .map(|item| sysroot_callable_item::unaccounted_sysroot_callable_note(item)),
    );
    notes
}

/// Trust (2026-09-30, residual L2): refuse, under `-Ztrust-policy=memory-safe`, a
/// body the indirect-call gate refuses on every other fail-closed lane
/// (`function_has_unresolved_indirect_call`) — parity; see the module doc for which
/// narrower rules are not sound here. Reached only for a body with no source or
/// inlined `unsafe` that the classifier did not skip: a body with `unsafe` is
/// judged by `abort_on_full_verification_failure`, which already asks the gate, and
/// a skipped one by [`memory_safe_skip_withheld`]. Refusal only, one error at most;
/// it never admits anything and touches no row.
pub(super) fn abort_on_memory_safe_unresolved_indirect_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) {
    if let Some(prepared) = prepare_memory_safe_unresolved_indirect_call(tcx, body, func_path) {
        prepared.emit(tcx);
    }
}

pub(super) fn prepare_memory_safe_unresolved_indirect_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func_path: &str,
) -> Option<PreparedLocatedDiagnostic> {
    if !function_has_unresolved_indirect_call(tcx, body) {
        return None;
    }
    let span = body.span;
    let mut diagnostic = PreparedDiagnostic {
        aborting: true,
        header: format!(
            "Trust memory-safe verification failed for `{func_path}`: a function called \
             through a fn pointer or handed to generic code as a value is not a body this \
             compilation verified"
        ),
        children: vec![PreparedDiagnosticChild::Note(
            "memory-safe refuses such a call exactly as it refuses a DIRECT call to a callee \
             with no verified body here: its target may be another crate's code, a std routine \
             whose panic no row records, or a function whose `requires` — and the runtime \
             checks its own verification elided under that `requires` — no call site charges. \
             Strict, the default policy and certify refuse the same call \
             (`@trust-indirect-callee`)".into(),
        )],
    };
    for callee in requires_carrying_fn_values(tcx, body) {
        diagnostic.children.push(PreparedDiagnosticChild::Note(requires_value_note(&callee)));
    }
    // Trust (2026-10-03): a std/core/alloc item handed over that memory-safe's rule
    // does not account for (`sysroot_callable_item`).
    for item in sysroot_callable_item::unaccounted_sysroot_callable_items(tcx, body) {
        diagnostic.children.push(PreparedDiagnosticChild::Note(
            sysroot_callable_item::unaccounted_sysroot_callable_note(&item),
        ));
    }
    diagnostic.children.push(PreparedDiagnosticChild::Note(
        "-Ztrust-policy=memory-safe conditionally admits only compiler-marked safe-code panic \
         or lowering assumptions in functions with neither source nor inlined unsafe; proofs \
         remain proofs, while UB, hardened, contract, functional, unmarked unknown, \
         runtime-checked, and other failed rows remain build errors".into(),
    ));
    Some(PreparedLocatedDiagnostic { span, diagnostic })
}

/// The callees of this body's DIRECT calls that owe their caller a precondition
/// ([`direct_callee_owes_caller_precondition`]), unsorted and possibly repeated —
/// the calls a body that is not verified leaves uncharged. The callee is read off
/// the call operand's TYPE, so a call through a local that holds the function item
/// counts as the call it is. Shared by the two skips that charge no call:
/// memory-safe's classifier-skip demotion ([`memory_safe_skip_withheld`]) and
/// `#[trust::assume_total]` ([`assume_total_cannot_cover_calls`]).
pub(super) fn direct_callees_owing_caller_precondition<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Vec<DefId> {
    let typing_env = body.typing_env(tcx);
    let mut owed: Vec<DefId> = Vec::new();
    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else { continue };
        if let TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } =
            &terminator.kind
            && let ty::FnDef(def_id, args) = *func.ty(&body.local_decls, tcx).kind()
            && direct_callee_owes_caller_precondition(tcx, typing_env, def_id, args.skip_binder())
        {
            owed.push(def_id);
        }
    }
    owed
}

/// `defs` as a deterministic, backquoted, comma-separated list of full paths. Full
/// paths (`with_no_trimmed_paths!`) because the caller builds the text before the
/// error it goes into is emitted.
fn quoted_paths(tcx: TyCtxt<'_>, defs: Vec<DefId>) -> String {
    let mut paths: Vec<String> = defs
        .into_iter()
        .map(|def_id| rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def_id)))
        .collect();
    paths.sort();
    paths.dedup();
    paths.iter().map(|path| format!("`{path}`")).collect::<Vec<_>>().join(", ")
}

/// Trust (2026-09-30, review of residual L2): why the memory-safe demotion of a
/// classifier skip must be WITHHELD for this body, or `None` when it may stand.
/// Asked in `run_pass`'s skip arm only for a `TreatedAsAssumption`/`UnreachableStart`
/// skip of a body with no source or inlined `unsafe` under memory-safe
/// (`memory_safe_demotion_applies`); a `Some` there makes the skip what it is on
/// every other fail-closed lane — refused — and the text is appended to that one
/// error's policy note.
///
/// The demotion's single assumption row stands for the body's own panic-freedom,
/// and a skipped body charges none of its calls. So it may not stand for:
///  * a DIRECT call whose callee owes a caller precondition
///    ([`direct_callee_owes_caller_precondition`]) — the callee's verified body,
///    and every check its verification elided, rests on each call being charged.
///    The callee is read off the call operand's TYPE, so a call through a local
///    that holds the function item counts as the call it is;
///  * anything the indirect-call gate refuses (`function_has_unresolved_indirect_call`),
///    the parity [`abort_on_memory_safe_unresolved_indirect_call`] gives a body
///    memory-safe verifies;
///  * a masked fail-closed source (`function_has_masked_fail_closed_dispatch`, with
///    a call through a fn pointer left to the gate): code no verdict here covers —
///    a dependency's function, verified or not, called or handed over; a std routine
///    at a dependency's type; foreign drop glue. The collapse rule
///    (`native_lowering_collapse_uncharged_edges`) refuses the same sources for the
///    sibling whole-body row, and memory-safe refuses a dependency call in a body it
///    verifies (the absent-callee row). The collapse rule's OTHER conjunct — every
///    call resolves to a local verified item — is not taken: it would also refuse a
///    skipped body's sysroot calls, which the memory-safe lane admits as a
///    capability gap today, including ones it admits unskipped (`checked_add`).
/// `UnreachableStart` bodies make no call, so they are never withheld.
pub(super) fn memory_safe_skip_withheld<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<String> {
    let owed = direct_callees_owing_caller_precondition(tcx, body);
    let unresolved_indirect = function_has_unresolved_indirect_call(tcx, body);
    // The collapse rule's masked conjunct, minus a call through a fn POINTER (every
    // such call is a masked source there; the gate above asks it precisely).
    let masked_source = function_has_masked_fail_closed_dispatch_except(tcx, body, |kind| {
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) = kind
        else {
            return false;
        };
        matches!(func.ty(&body.local_decls, tcx).kind(), ty::FnPtr(..))
    });
    if owed.is_empty() && !unresolved_indirect && !masked_source {
        return None;
    }
    let mut cannot_stand_for: Vec<String> = Vec::new();
    if !owed.is_empty() {
        cannot_stand_for.push(format!(
            "the call to {}, which carries a `requires` its callers owe (that function is \
             verified only under its `requires`, and a check its verification elided is not \
             in its code)",
            quoted_paths(tcx, owed),
        ));
    }
    if unresolved_indirect {
        let mut clause = String::from(
            "a call through a fn pointer or a function handed to generic code as a value, which \
             the indirect-call gate refuses on strict, the default policy and certify, and in a \
             body memory-safe verifies (`@trust-indirect-callee`)",
        );
        let valued = requires_carrying_fn_value_defs(tcx, body);
        if !valued.is_empty() {
            clause.push_str(&format!(
                " — here {}, which carries a `requires` its callers owe",
                quoted_paths(tcx, valued),
            ));
        }
        // Trust (2026-10-03): name a std/core/alloc item the gate refused under
        // memory-safe's rule (`sysroot_callable_item`).
        clause.push_str(&sysroot_callable_item::unaccounted_sysroot_callable_clause(tcx, body));
        cannot_stand_for.push(clause);
    }
    if masked_source {
        cannot_stand_for.push(String::from(
            "a masked fail-closed source — code no verdict in this compilation covers, such as a \
             dependency's function called, reified or handed over, a std routine run at a \
             dependency's type, or drop glue that runs a dependency's `Drop` \
             (`TRUST_MASK_TRACE=1` names it) — which memory-safe refuses in a body it verifies \
             (a dependency call's absent-callee row) and which an `assumption:native-lowering` \
             row may not stand for either (`native_lowering_collapse_uncharged_edges`)",
        ));
    }
    Some(format!(
        "; -Ztrust-policy=memory-safe did not admit this skip as an assumption: that assumption \
         would stand for the body's own panic-freedom only, and a skipped body charges none of \
         its calls, so it cannot stand for {}",
        cannot_stand_for.join(", nor for "),
    ))
}

/// Trust (2026-10-02, review of the `#[trust::assume_total]` rule): the component of
/// `ty`, at any depth, that code handed only the TYPE could still call, or `None`.
/// Asked where a type describes no value anyone holds: a `PhantomData`'s type
/// arguments. There a fn POINTER, a `dyn` or a closure is no value anyone can call —
/// `PhantomData<fn() -> T>` is the usual variance marker and was refused as a held fn
/// pointer. What a type alone does hand over is a value code can CONJURE from it: a
/// function item is a zero-sized type, so generic code given
/// `PhantomData<fn(u32) -> u32 {add1}>` can make the item (unsafely, e.g. by
/// `mem::zeroed`) and call it, and a type parameter or alias may be instantiated with
/// such an item. So, through `Ty::walk` (which also opens a closure's parts): a
/// function item that owes its caller a precondition, and a type parameter or alias
/// that may be called (`type_may_be_called_as_fn`), each fail-closed under escaping
/// bound variables — what [`uncharged_callable_component`] asks of those kinds
/// anywhere else. A closure's own body carries no `requires`, and a zero-sized
/// closure is made of what this walk opens.
fn conjurable_callable_component<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Option<Ty<'tcx>> {
    ty.walk().filter_map(|arg| arg.as_type()).find(|&t| match *t.kind() {
        ty::FnDef(def_id, args) => {
            t.has_escaping_bound_vars()
                || direct_callee_owes_caller_precondition(
                    tcx,
                    typing_env,
                    def_id,
                    args.skip_binder(),
                )
        }
        ty::Param(_) | ty::Alias(..) => {
            t.has_escaping_bound_vars() || type_may_be_called_as_fn(tcx, typing_env, t)
        }
        _ => false,
    })
}

/// Trust (2026-10-02, review of the `#[trust::assume_total]` rule): what a FOREIGN
/// closure that a constant's value holds behind a fn pointer can hand to the code it
/// calls — its parent's type arguments and its upvars ([`closure_callable_parts`]) —
/// asked as [`uncharged_callable_component`] asks them, or `None`. A closure behind a
/// fn pointer was coerced to one (`ClosureFnPointer`), so it captures nothing, and a
/// closure carries no `requires` of its own: the closure itself is not "uncharged",
/// as the type walk answers for a foreign closure it cannot see into. A closure's
/// generics parent is its TYPECK ROOT (`generics_of`; an inline `const { … }` block
/// is a typeck child), so the closures of `thread_local!`'s `LocalKey::new(const {
/// |init| … })` in a non-generic `static` have no parent arguments and no upvars, and
/// answer `None`. Measured shape (review): a dependency's `thread_local!` read,
/// `dep::COUNTER.with(|c| c.get())`, whose `LocalKey` holds such an accessor, and a
/// dependency's static table of coerced closures, each refused as holding a callable
/// before.
fn coerced_closure_component<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    closure: Ty<'tcx>,
    seen: &mut FxHashSet<Ty<'tcx>>,
) -> Option<Ty<'tcx>> {
    let Some(parts) = closure_callable_parts(closure) else {
        return uncharged_callable_component(tcx, typing_env, closure, seen);
    };
    parts.into_iter().find_map(|part| uncharged_callable_component(tcx, typing_env, part, seen))
}

/// Trust (2026-09-30, review of the `#[trust::assume_total]` rule): the first
/// component of `ty`, at any depth, that is a callable a value of `ty` carries to the
/// code it reaches with a `requires` that no call site in the body holding it charges;
/// `None` when there is none. Asked of every local's and constant's type of an
/// `assume_total` body ([`held_uncharged_callables`]).
///
/// A component answers "uncharged" when it is:
///  * a function item that owes its caller a precondition
///    ([`direct_callee_owes_caller_precondition`], asked as named and as resolved);
///  * a callable whose target the type does not name: a `fn` POINTER (its value may
///    be a `requires`-carrying function minted where no gate looks — the
///    pointer-parameter route), a `dyn` of an `Fn`-family trait, a type parameter or
///    alias that may be called (`type_may_be_called_as_fn`);
///  * a closure or coroutine-closure of a non-sysroot foreign crate, which the
///    indirect-call gate treats as unresolved too (verified by nobody here).
/// It is walked through what can CARRY such a callable: an ADT's, a function item's
/// and an alias's type arguments; tuple, array, slice, reference, raw-pointer and
/// pattern-type components; a `dyn`'s trait and projection arguments; a sysroot
/// closure's, and any foreign coroutine's, parent arguments and upvars. NOT walked: a
/// LOCAL closure or coroutine, which is verified as its own body (with the attribute,
/// when it inherits it), so what it captures is called or handed on under its own
/// verdict; a closure's SIGNATURE, a `fn` pointer type that describes it and is no
/// value it holds (so `Ty::walk`, which yields it, is not used); an ADT's FIELDS (the
/// residual the module doc records). A function item or an alias with escaping bound
/// variables, which `Instance::try_resolve` and the trait solver are not asked about,
/// answers "uncharged" (fail-closed). A `PhantomData` holds no value, so its type
/// arguments are asked only for what a TYPE alone can hand over
/// ([`conjurable_callable_component`]; review 2026-10-02: `PhantomData<fn() -> T>`,
/// the usual variance marker, answered "uncharged" as a fn pointer).
fn uncharged_callable_component<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    seen: &mut FxHashSet<Ty<'tcx>>,
) -> Option<Ty<'tcx>> {
    if !seen.insert(ty) {
        return None;
    }
    match *ty.kind() {
        ty::FnPtr(..) => Some(ty),
        ty::FnDef(def_id, args) => {
            if ty.has_escaping_bound_vars()
                || direct_callee_owes_caller_precondition(
                    tcx,
                    typing_env,
                    def_id,
                    args.skip_binder(),
                )
            {
                return Some(ty);
            }
            args.skip_binder()
                .types()
                .find_map(|arg| uncharged_callable_component(tcx, typing_env, arg, seen))
        }
        ty::Dynamic(predicates, ..) => {
            if predicates
                .principal_def_id()
                .is_some_and(|principal| trait_is_or_extends_fn_family(tcx, principal))
            {
                return Some(ty);
            }
            predicates.iter().find_map(|predicate| {
                let (args, term) = match predicate.skip_binder() {
                    ty::ExistentialPredicate::Trait(trait_ref) => (trait_ref.args, None),
                    ty::ExistentialPredicate::Projection(projection) => {
                        (projection.args, projection.term.as_type())
                    }
                    ty::ExistentialPredicate::AutoTrait(_) => return None,
                };
                args.types()
                    .chain(term)
                    .find_map(|arg| uncharged_callable_component(tcx, typing_env, arg, seen))
            })
        }
        ty::Closure(def_id, _) | ty::CoroutineClosure(def_id, _) | ty::Coroutine(def_id, _) => {
            if def_id.is_local() {
                return None;
            }
            if !matches!(ty.kind(), ty::Coroutine(..))
                && !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
            {
                return Some(ty);
            }
            closure_callable_parts(ty)?
                .into_iter()
                .find_map(|part| uncharged_callable_component(tcx, typing_env, part, seen))
        }
        ty::Param(_) | ty::Alias(..) => {
            if ty.has_escaping_bound_vars() || type_may_be_called_as_fn(tcx, typing_env, ty) {
                return Some(ty);
            }
            let ty::Alias(_, alias) = *ty.kind() else { return None };
            alias
                .args
                .types()
                .find_map(|arg| uncharged_callable_component(tcx, typing_env, arg, seen))
        }
        ty::Adt(adt, args) if adt.is_phantom_data() => {
            args.types().find_map(|arg| conjurable_callable_component(tcx, typing_env, arg))
        }
        ty::Adt(_, args) => {
            args.types().find_map(|arg| uncharged_callable_component(tcx, typing_env, arg, seen))
        }
        ty::Tuple(components) => components
            .iter()
            .find_map(|component| uncharged_callable_component(tcx, typing_env, component, seen)),
        ty::Ref(_, inner, _)
        | ty::RawPtr(inner, _)
        | ty::Slice(inner)
        | ty::Array(inner, _)
        | ty::Pat(inner, _) => uncharged_callable_component(tcx, typing_env, inner, seen),
        ty::UnsafeBinder(inner) => {
            uncharged_callable_component(tcx, typing_env, inner.skip_binder(), seen)
        }
        _ => None,
    }
}

/// A hard bound on the allocations ONE constant's value walk reads
/// ([`uncharged_callable_in_constant_value`]). Running out answers "cannot read"
/// (fail-closed), never "holds nothing".
const HELD_CONSTANT_VALUE_STEP_BUDGET: usize = 4096;

/// A hard bound on the distinct types [`local_impl_associated_constants_held`]'s key
/// walk opens, across all its rounds. Running out answers "cannot read" (fail-closed),
/// never "holds nothing" (fifth review, 2026-10-02: a polymorphically recursive local
/// ADT made the walk unbounded).
const ASSOCIATED_CONSTANT_KEY_WALK_STEP_BUDGET: usize = 4096;

/// Trust (2026-09-30, second review of the `#[trust::assume_total]` rule): what the
/// VALUE of one constant operand of an `assume_total` body carries that its TYPE does
/// not show — a function pointer stored in a field. `Some(note)` names the first
/// uncharged callable found ([`uncharged_callable_component`]), or says why the value
/// cannot be read here (fail-closed); `None` when it carries none.
///
/// MEASURED on a stage 1 of `fbc6068e3`: with a verify-off dependency's `pub struct H {
/// pub f: fn(u32) -> u32 }` and `run_h(h: &H, y) { (h.f)(y) }`, an `assume_total` body
/// `vo::run_h(&vo::H { f: add1 }, y)` built exit 0 under certify and the default policy
/// at `-O0`, `-Zinline-mir=yes` and `-Copt-level=3 -Zmir-opt-level=2`, and RETURNED a
/// wrong value; so did the same `H` as a local `const` item (by reference or by value),
/// an associated `const`, an inline `const`, a `static`, a dependency's `requires` item
/// in the struct, and a `static SD: &(dyn vo::Tr + Sync) = &vo::Wrap(add1)` handed to
/// the dependency. None of those bodies has a local or a constant whose TYPE names
/// `add1` or a callable: `&vo::H { f: add1 }` is PROMOTED — the reification moves into
/// `p::promoted[0]`, a body no pass of this compilation verifies, and `p` holds a
/// `&vo::H` constant — and a `const` or `static` initializer is not verified either.
/// The value names the function exactly: evaluation reifies `add1` into a
/// `GlobalAlloc::Function` whose instance is `add1`.
///
/// The walk evaluates the constant (a `Const::Unevaluated` — a promoted, a `const` item,
/// an associated or inline `const` — in the body's typing environment) and follows its
/// allocations through their pointer provenance, as the assumption-root census's
/// constant-memory walk (`census_user_axioms_in_constant_memory`) does: a function
/// pointer's instance is asked as the callable its TYPE is (`Instance::ty`, so a
/// `requires`-carrying item, a generic item instantiated with one and a foreign closure
/// answer as they do in a type, and a local closure or a `requires`-free item does not);
/// a vtable is asked through the concrete type it was made for (its methods and drop
/// glue are that type's); a `static` is read through its initializer; plain memory is
/// followed. It FAILS CLOSED — the note says the value cannot be read, and the body is
/// verified — on a constant that does not evaluate here (a generic one), an `extern`
/// static, a static whose initializer does not evaluate or that a const context's body
/// may not evaluate (rustc's own may-cycle condition, as the census's), a dangling
/// allocation, and the step budget. Not read: a type-system constant (`Const::Ty`: an
/// integer, `bool`, `char` or a valtree of them, which holds no pointer) and a constant
/// of a primitive type, `()` or `!` (so a `const { assert!(…) }` is not evaluated here
/// either). What is read of a `static` is its INITIALIZER: a value another
/// body writes into a mutable or interior-mutable static at run time is that body's
/// (the residual the module doc records).
///
/// (Fourth review, 2026-10-02) Every TYPE the value names — a function pointer's
/// instance type, a vtable's concrete type, a pointed-to `static`'s type — is pushed to
/// `reached`: a dependency handed `&dyn vo::Run` made for `MyT`, or the reified
/// `vo::run_assoc::<MyT>`, reaches `MyT`'s trait impls, which
/// [`local_impl_associated_constants_held`] then reads.
fn uncharged_callable_in_constant_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    static_eval_may_cycle: bool,
    constant: rustc_middle::mir::Const<'tcx>,
    span: rustc_span::Span,
    seen: &mut FxHashSet<Ty<'tcx>>,
    reached: &mut Vec<Ty<'tcx>>,
) -> Option<String> {
    use std::ops::ControlFlow::{Break, Continue};

    use rustc_middle::mir::Const;
    use rustc_middle::mir::interpret::GlobalAlloc;

    let holder = constant.ty();
    if holder.is_primitive() || holder.is_unit() || holder.is_never() {
        return None;
    }
    let unreadable_note = |why: &str| -> String {
        rustc_middle::ty::print::with_no_trimmed_paths!(format!(
            "a `{holder}` constant whose value this compilation cannot read here ({why})"
        ))
    };
    let value = match constant {
        Const::Ty(..) => return None,
        Const::Val(value, _) => value,
        Const::Unevaluated(..) => match constant.eval(tcx, typing_env, span) {
            Ok(value) => value,
            Err(_) => {
                return Some(unreadable_note(
                    "it does not evaluate in this body's typing environment",
                ));
            }
        },
    };
    let root = constant_value_root(value)?;
    // Trust (2026-10-03): the traversal is `walk_constant_allocations`, shared with the
    // minting-site rules' R5; what each allocation answers is this walk's own, unchanged.
    let found = walk_constant_allocations(tcx, root, |global| match global {
        GlobalAlloc::Function { instance, .. } => {
            let target = instance.ty(tcx, typing_env);
            reached.push(target);
            // Trust (2026-10-02, review): a FOREIGN closure behind a fn pointer was
            // coerced to one — the instance is the closure itself or its
            // `ClosureOnce` adapter shim — and is asked through what it can hand on
            // (`coerced_closure_component`), not answered "uncharged" as a type.
            let coerced_closure = match instance.def {
                ty::InstanceKind::Shim(ty::ShimKind::ClosureOnce { .. }) => {
                    Some(instance.args.type_at(0))
                }
                ty::InstanceKind::Item(def_id) if tcx.is_closure_like(def_id) => Some(target),
                _ => None,
            }
            .filter(
                |closure| matches!(*closure.kind(), ty::Closure(def_id, _) if !def_id.is_local()),
            );
            let found = match coerced_closure {
                Some(closure) => coerced_closure_component(tcx, typing_env, closure, seen),
                None => uncharged_callable_component(tcx, typing_env, target, seen),
            };
            match found {
                Some(component) => Break(rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "`{component}` (a function pointer in the value of a `{holder}` constant)"
                ))),
                None => Continue(None),
            }
        }
        GlobalAlloc::VTable(concrete, _) => {
            reached.push(concrete);
            match uncharged_callable_component(tcx, typing_env, concrete, seen) {
                Some(component) => Break(rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "`{component}` (in the `{concrete}` vtable in the value of a `{holder}` \
                         constant)"
                ))),
                None => Continue(None),
            }
        }
        GlobalAlloc::Static(def_id) => {
            if tcx.is_foreign_item(def_id) {
                return Break(unreadable_note("it points to an `extern` static"));
            }
            reached.push(tcx.type_of(def_id).instantiate_identity().skip_normalization());
            if static_eval_may_cycle {
                return Break(unreadable_note(
                    "it points to a static, which a const context's body may not evaluate",
                ));
            }
            match tcx.eval_static_initializer(def_id) {
                Ok(alloc) => Continue(Some(alloc)),
                Err(_) => Break(unreadable_note(
                    "it points to a static whose initializer does not evaluate",
                )),
            }
        }
        GlobalAlloc::Memory(alloc) => Continue(Some(alloc)),
        GlobalAlloc::TypeId { .. } => Continue(None),
    });
    match found {
        Ok(found) => found,
        Err(why) => Some(unreadable_note(why)),
    }
}

/// Trust (2026-10-03): the allocation a constant's VALUE starts from, or `None` for a
/// value with no pointer (an integer scalar, a zero-sized value). Shared by the held walk
/// ([`uncharged_callable_in_constant_value`]) and the minting-site rules' R5.
fn constant_value_root(
    value: rustc_middle::mir::ConstValue,
) -> Option<rustc_middle::mir::interpret::AllocId> {
    use rustc_middle::mir::ConstValue;
    use rustc_middle::mir::interpret::Scalar;

    match value {
        ConstValue::Scalar(Scalar::Ptr(ptr, _)) => Some(ptr.provenance.alloc_id()),
        ConstValue::Slice { alloc_id, .. } | ConstValue::Indirect { alloc_id, .. } => {
            Some(alloc_id)
        }
        ConstValue::Scalar(Scalar::Int { .. }) | ConstValue::ZeroSized => None,
    }
}

/// Trust (2026-10-03; extracted from the 2026-09-30 held walk, unchanged): follow the
/// allocations a constant's value reaches from `root` through their pointer provenance,
/// each allocation once, calling `visit` on each: `Break(b)` ends the walk with `b`,
/// `Continue(Some(contents))` follows the pointers `contents` holds, `Continue(None)`
/// follows nothing behind this allocation. `Err(why)` when the walk cannot finish — a
/// dangling allocation, or [`HELD_CONSTANT_VALUE_STEP_BUDGET`] allocations read — which
/// every caller answers fail-closed. Reads only the global allocation map: no evaluation,
/// so it is safe inside any query (a caller that evaluates a `static` does so in `visit`).
/// Shared by the held walk ([`uncharged_callable_in_constant_value`]) and the
/// minting-site rules' R5 ([`collect_requires_carrying_values`]).
fn walk_constant_allocations<'tcx, B>(
    tcx: TyCtxt<'tcx>,
    root: rustc_middle::mir::interpret::AllocId,
    mut visit: impl FnMut(
        rustc_middle::mir::interpret::GlobalAlloc<'tcx>,
    ) -> std::ops::ControlFlow<
        B,
        Option<rustc_middle::mir::interpret::ConstAllocation<'tcx>>,
    >,
) -> Result<Option<B>, &'static str> {
    use std::ops::ControlFlow;

    use rustc_middle::mir::interpret::AllocId;

    let mut visited: FxHashSet<AllocId> = FxHashSet::default();
    visited.insert(root);
    let mut todo = vec![root];
    let mut steps = 0usize;
    while let Some(id) = todo.pop() {
        steps += 1;
        if steps > HELD_CONSTANT_VALUE_STEP_BUDGET {
            return Err("the walk's step budget ran out");
        }
        let Some(global) = tcx.try_get_global_alloc(id) else {
            return Err("it points to an allocation this compilation does not have");
        };
        let contents = match visit(global) {
            ControlFlow::Break(found) => return Ok(Some(found)),
            ControlFlow::Continue(None) => continue,
            ControlFlow::Continue(Some(contents)) => contents,
        };
        for pointer in contents.inner().provenance().ptrs().values() {
            let next = pointer.alloc_id();
            if visited.insert(next) {
                todo.push(next);
            }
        }
    }
    Ok(None)
}

/// Trust (2026-09-30, review of the `#[trust::assume_total]` rule): the callables this
/// body HOLDS whose `requires` no call site in it charges, sorted and deduplicated;
/// empty when there is none. Three readings:
///  * the TYPE of every local — arguments, return place, temporaries, and the locals the
///    MIR inliner brought in — and of every constant operand (a callee with its type
///    arguments, a function item handed on, a promoted, a static's address), each hit
///    as "`component` (in `holder`)" ([`uncharged_callable_component`]);
///  * (second review, 2026-09-30) the VALUE of every constant operand, which can hold a
///    function pointer its type does not show — a `requires`-carrying function reified
///    into a struct field in a promoted, a `const` or a `static`
///    ([`uncharged_callable_in_constant_value`]);
///  * (third and fourth reviews, 2026-10-02) the VALUES of the associated constants
///    this crate's impls of FOREIGN traits give a local type the body names anywhere —
///    in a local's or a constant's type, or in what a constant's value names — which a
///    dependency generic over the trait evaluates itself
///    ([`local_impl_associated_constants_held`]).
/// A skipped body can call what it holds, or hand it to code that calls it, and nothing
/// charges that call. Types show what a value carries whatever calls survive: under
/// `-Zinline-mir=yes` the `map(add1)` call of `v.iter().copied().map(add1).collect()` is
/// inlined into an aggregate, and the one call left, `<Vec<u32> as
/// SpecFromIterNested<u32, Map<…, fn(u32) -> u32 {add1}>>>::from_iter`, names `add1`
/// only inside an ADT type argument — where the indirect-call gate does not look — while
/// the aggregate's local has that type.
///
/// One local is not asked: a fn-pointer local the indirect-call gate itself resolves
/// (`indirect_callee_is_a_reified_constant`: assigned once, from a LOCAL item that is
/// verified unconditionally, and never borrowed). Its target is named and owes
/// nothing, so `let fp: fn(u32) -> u32 = half; fp(y)` keeps the skip, as it does with
/// the gate.
fn held_uncharged_callables<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<String> {
    use rustc_middle::mir::visit::Visitor;
    use rustc_middle::mir::{ConstOperand, Location};

    struct Constants<'tcx>(Vec<(rustc_middle::mir::Const<'tcx>, rustc_span::Span)>);
    impl<'tcx> Visitor<'tcx> for Constants<'tcx> {
        fn visit_const_operand(&mut self, constant: &ConstOperand<'tcx>, _: Location) {
            self.0.push((constant.const_, constant.span));
        }
    }

    let typing_env = body.typing_env(tcx);
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    let mut holders: Vec<Ty<'tcx>> = Vec::new();
    // Every type the body names, for the associated-constant walk: its locals' and its
    // constants' types, and what its constants' values name.
    let mut reached: Vec<Ty<'tcx>> = body.local_decls.iter().map(|decl| decl.ty).collect();
    for (local, decl) in body.local_decls.iter_enumerated() {
        if matches!(decl.ty.kind(), ty::FnPtr(..))
            && indirect_callee_is_a_reified_constant(tcx, body, &Operand::Copy(Place::from(local)))
        {
            continue;
        }
        holders.push(decl.ty);
    }
    let mut constants = Constants(Vec::new());
    constants.visit_body(body);
    holders.extend(constants.0.iter().map(|&(constant, _)| constant.ty()));
    reached.extend(constants.0.iter().map(|&(constant, _)| constant.ty()));
    let mut held: Vec<String> = holders
        .into_iter()
        .filter_map(|holder| {
            let component = uncharged_callable_component(tcx, typing_env, holder, &mut seen)?;
            Some(rustc_middle::ty::print::with_no_trimmed_paths!(if component == holder {
                format!("`{component}`")
            } else {
                format!("`{component}` (in `{holder}`)")
            }))
        })
        .collect();
    // rustc's own condition for "evaluating a static here may cycle", as the census's
    // (`rustc_middle::mir::pretty::write_allocations`): an early-phase body that is
    // itself a const context.
    let static_eval_may_cycle = body.phase
        <= rustc_middle::mir::MirPhase::Runtime(rustc_middle::mir::RuntimePhase::PostCleanup)
        && body
            .source
            .def_id()
            .as_local()
            .is_some_and(|local| tcx.hir_body_const_context(local).is_some());
    held.extend(constants.0.into_iter().filter_map(|(constant, span)| {
        uncharged_callable_in_constant_value(
            tcx,
            typing_env,
            static_eval_may_cycle,
            constant,
            span,
            &mut seen,
            &mut reached,
        )
    }));
    held.extend(local_impl_associated_constants_held(
        tcx,
        typing_env,
        static_eval_may_cycle,
        reached,
        &mut seen,
    ));
    held.sort();
    held.dedup();
    held
}

/// Trust (2026-10-02, third and fourth reviews of the `#[trust::assume_total]` rule):
/// what the ASSOCIATED CONSTANTS of this crate's impls of FOREIGN traits hold, for the
/// LOCAL types the body names — notes in the form
/// [`uncharged_callable_in_constant_value`] gives, each naming the constant.
///
/// The third review's route: with a verify-off dependency's `pub trait HasH { const H:
/// H; }` and `run_assoc<T: HasH>(y) { (T::H.f)(y) }`, a local `impl vo::HasH for MyT {
/// const H: vo::H = vo::H { f: add1 }; }` and an `assume_total` body
/// `vo::run_assoc::<MyT>(y)` hand `add1` to code that calls it, and nothing in the body
/// names it: no local or constant of the body has it in its type or its value, since
/// the constant is evaluated inside `run_assoc` (also `const F: fn(u32) -> u32 =
/// add1`). The fourth review's: the dependency reaches the same constant without any
/// call naming `MyT` — through an unsizing coercion (`vo::run_dyn(&MyT, y)`, with the
/// dependency's blanket `impl<T: HasH> Run for T` reached through `&dyn vo::Run`) or
/// through drop glue (`let _g = vo::Guard::<MyT> { .. }`, whose `Drop` impl reads
/// `T::H`). Neither is a call, so this walk does not start from calls.
///
/// Code that is not this crate's can reach a local impl's associated constant only by
/// being instantiated with a type the impl's trait reference mentions, and only for a
/// FOREIGN trait (it cannot name a local one; this crate's own code that reads a
/// constant through a fn pointer is a verified body, refused by the indirect-call gate,
/// an `assume_total` one, refused by its gate clause, or a `#[trust::skip]` one, which
/// a fail-closed lane already reports as a coverage error). So the KEYS are collected
/// from every type in `roots` — the body's locals' and constants' types and what its
/// constants' values name — at any depth (`Ty::walk`), through a LOCAL ADT's fields,
/// an opaque type's hidden type and a normalizable projection: every local ADT, local
/// `extern` type and local `dyn` principal (`impl vo::HasH for dyn Local` is
/// orphan-legal). Every LOCAL impl of a foreign trait with associated constants or
/// types whose trait reference mentions a key (`impl Tr for MyT`, `for Box<MyT>`,
/// `impl Tr<MyT> for u32`) is read: each of the TRAIT's associated constants is
/// evaluated for the impl — the impl's own value or the trait's default — and walked
/// as a constant operand's value is; the impl's associated TYPES (`type A = MyU;`, which
/// the dependency reaches as `T::A`) and what the constants' values name are keyed in
/// turn, to a fixed point. An impl with type or const parameters is not instantiated
/// here and answers "cannot read" when its trait has associated constants
/// (fail-closed); one with lifetime parameters only is read with them erased.
///
/// Bounded (fifth review): the key walk opens at most
/// [`ASSOCIATED_CONSTANT_KEY_WALK_STEP_BUDGET`] distinct types over all its rounds; a
/// polymorphically recursive local ADT (`struct Nested<T> { v: T, inner:
/// Option<Box<Nested<(T, T)>>> }`), whose fields name a new type at every step, runs it
/// out, and the answer is "cannot read" — the body is verified, not skipped. The walk
/// does not run when this crate has no local impl of a foreign trait with associated
/// constants or types (nothing for a key to match).
///
/// Cost: evaluating an associated constant the program never uses can now fail the
/// build — const-eval reports its own error (a `panic!` in an unused impl's constant).
/// Narrow (only impls of foreign traits with associated constants, for a type an
/// `assume_total` body names), and fail-closed.
///
/// NOT reached (docs/KNOWN_HAZARDS.md, the entry's OPEN residual): the same route
/// through a METHOD (a verify-off default method, or a verified impl method, that
/// returns or calls the function); a type the body does not NAME — a type parameter of
/// a generic `assume_total` body that a verified caller instantiates with the local
/// type (the body names the parameter), or a value made in any other verified body — a
/// caller's `&MyT` unsized to `&dyn vo::Run`, or a callee's return (`fn mk() ->
/// &'static dyn vo::Run { &MyT }`, then `vo::run_dyn(mk(), y)` at `-O0`; a `static`
/// reached through a call's return value); and a coroutine's saved locals (a local coroutine is its own body, walked or verified
/// there).
fn local_impl_associated_constants_held<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    static_eval_may_cycle: bool,
    roots: Vec<Ty<'tcx>>,
    seen: &mut FxHashSet<Ty<'tcx>>,
) -> Vec<String> {
    use rustc_middle::mir::{Const, UnevaluatedConst};
    use rustc_middle::ty::print::PrintTraitRefExt as _;

    // The key a type is matched on, if it is one: a local ADT, a local `extern` type,
    // a `dyn` of a local trait.
    let key_of = |t: Ty<'tcx>| -> Option<DefId> {
        match *t.kind() {
            ty::Adt(adt, _) => Some(adt.did()),
            ty::Foreign(def_id) => Some(def_id),
            ty::Dynamic(predicates, ..) => predicates.principal_def_id(),
            _ => None,
        }
        .filter(|def_id| def_id.is_local())
    };
    // The local impls of foreign traits that have associated constants or types.
    let mut candidates: Vec<(DefId, Vec<DefId>)> = Vec::new();
    for (&trait_def_id, impls) in tcx.all_local_trait_impls(()) {
        if trait_def_id.is_local() {
            continue;
        }
        let items = tcx.associated_items(trait_def_id);
        let constants: Vec<DefId> = items
            .in_definition_order()
            .filter(|item| matches!(item.kind, ty::AssocKind::Const { .. }))
            .map(|item| item.def_id)
            .collect();
        let has_types =
            items.in_definition_order().any(|item| matches!(item.kind, ty::AssocKind::Type { .. }));
        if constants.is_empty() && !has_types {
            continue;
        }
        for impl_def_id in impls.iter().map(|local| local.to_def_id()) {
            if !matches!(tcx.impl_trait_header(impl_def_id).polarity, ty::ImplPolarity::Negative) {
                candidates.push((impl_def_id, constants.clone()));
            }
        }
    }

    // No local impl of a foreign trait with associated constants or types: nothing
    // for the keys to match, so no walk.
    if candidates.is_empty() {
        return Vec::new();
    }

    let mut keys: FxHashSet<DefId> = FxHashSet::default();
    let mut walked: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    let mut todo: Vec<Ty<'tcx>> = roots;
    // Whether the key walk ran out of steps (fifth review): a local ADT's fields are
    // instantiated with its arguments, so a polymorphically recursive type (`struct
    // Nested<T> { v: T, inner: Option<Box<Nested<(T, T)>>> }`) yields a new type at
    // every step and `walked` never repeats one. Shared by every `drain`, the
    // fixed-point rounds' included.
    let mut steps = 0usize;
    let mut drain = |todo: &mut Vec<Ty<'tcx>>, keys: &mut FxHashSet<DefId>| -> bool {
        while let Some(root) = todo.pop() {
            if !walked.insert(root) {
                continue;
            }
            steps += 1;
            if steps > ASSOCIATED_CONSTANT_KEY_WALK_STEP_BUDGET {
                todo.clear();
                return false;
            }
            for t in root.walk().filter_map(|arg| arg.as_type()) {
                if let Some(key) = key_of(t) {
                    keys.insert(key);
                }
                match *t.kind() {
                    ty::Adt(adt, args) if adt.did().is_local() => {
                        for field in adt.all_fields() {
                            todo.push(field.ty(tcx, args).skip_normalization());
                        }
                    }
                    ty::Alias(_, alias) => {
                        if let ty::AliasTyKind::Opaque { def_id } = alias.kind {
                            todo.push(
                                tcx.type_of(def_id)
                                    .instantiate(tcx, alias.args)
                                    .skip_normalization(),
                            );
                        } else if let Ok(normalized) = tcx
                            .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(t))
                            && normalized != t
                        {
                            todo.push(normalized);
                        }
                    }
                    _ => {}
                }
            }
        }
        true
    };
    // Running out answers "cannot read" (fail-closed: the body is verified), never
    // "holds nothing"; the keys collected so far are not a complete set to match on.
    let budget_ran_out = || {
        vec![
            "the associated constants of the types this body names, which this compilation \
             cannot read here (the walk's step budget ran out)"
                .to_string(),
        ]
    };
    if !drain(&mut todo, &mut keys) {
        return budget_ran_out();
    }

    let mut held: Vec<String> = Vec::new();
    let mut read = vec![false; candidates.len()];
    loop {
        let mut progressed = false;
        for (index, (impl_def_id, constants)) in candidates.iter().enumerate() {
            let impl_def_id = *impl_def_id;
            if read[index] {
                continue;
            }
            let header = tcx.impl_trait_header(impl_def_id);
            let declared = header.trait_ref.instantiate_identity().skip_normalization();
            let mentions_key = declared
                .args
                .types()
                .flat_map(|arg| arg.walk())
                .filter_map(|arg| arg.as_type())
                .any(|t| key_of(t).is_some_and(|key| keys.contains(&key)));
            if !mentions_key {
                continue;
            }
            read[index] = true;
            progressed = true;
            // What the dependency reaches as `T::A`: the impl's associated types.
            todo.extend(
                tcx.associated_items(impl_def_id)
                    .in_definition_order()
                    .filter(|item| matches!(item.kind, ty::AssocKind::Type { .. }))
                    .map(|item| {
                        tcx.type_of(item.def_id).instantiate_identity().skip_normalization()
                    }),
            );
            if constants.is_empty() {
                continue;
            }
            if tcx.generics_of(impl_def_id).requires_monomorphization(tcx) {
                held.push(rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                    "the associated constants of `impl {} for {}`, a generic impl whose values \
                     this compilation cannot read here",
                    declared.print_only_trait_path(),
                    declared.self_ty(),
                )));
                continue;
            }
            let impl_args =
                ty::GenericArgs::for_item(tcx, impl_def_id, |_, _| tcx.lifetimes.re_erased.into());
            let trait_ref = header.trait_ref.instantiate(tcx, impl_args).skip_normalization();
            for &constant_def_id in constants {
                if tcx.generics_of(constant_def_id).count() != trait_ref.args.len() {
                    held.push(rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                        "the generic associated constant `{}` of `impl {} for {}`, whose value \
                         this compilation cannot read here",
                        tcx.def_path_str(constant_def_id),
                        trait_ref.print_only_trait_path(),
                        trait_ref.self_ty(),
                    )));
                    continue;
                }
                let holder = tcx
                    .type_of(constant_def_id)
                    .instantiate(tcx, trait_ref.args)
                    .skip_normalization();
                todo.push(holder);
                let constant = Const::Unevaluated(
                    UnevaluatedConst::new(constant_def_id, trait_ref.args),
                    holder,
                );
                if let Some(note) = uncharged_callable_in_constant_value(
                    tcx,
                    typing_env,
                    static_eval_may_cycle,
                    constant,
                    tcx.def_span(impl_def_id),
                    seen,
                    &mut todo,
                ) {
                    held.push(rustc_middle::ty::print::with_no_trimmed_paths!(format!(
                        "{note}, the associated constant `{}` of a local type this body names",
                        tcx.def_path_str_with_args(constant_def_id, trait_ref.args),
                    )));
                }
            }
        }
        if !drain(&mut todo, &mut keys) {
            held.extend(budget_ran_out());
            return held;
        }
        if !progressed {
            break;
        }
    }
    held
}

/// Trust (2026-09-30): why `#[trust::assume_total]` may NOT skip this body — the
/// calls it makes, or the callables it holds, that the skip would leave charged to
/// nobody — or `None` when the skip may stand. Asked by `verification_decision` for
/// a body carrying the attribute after `validity_transmute::assume_total_cannot_cover_body`
/// answered `false` (no unsafe operation); a `Some` makes the body verified exactly
/// as if the attribute were absent, and [`warn_assume_total_does_not_cover_calls`]
/// says why, one note per returned clause.
///
/// The attribute assumes the body's TOTALITY (no panic, termination). It is not a
/// callee's precondition: a function with a `requires` is verified only UNDER it,
/// so the skip may not stand for (module doc, "`#[trust::assume_total]` charged none
/// of its calls"):
///  * a DIRECT call whose callee owes a caller precondition, local or foreign
///    ([`direct_callees_owing_caller_precondition`], the predicate memory-safe's skip
///    rule uses);
///  * anything the indirect-call gate refuses (`function_has_unresolved_indirect_call`):
///    a `requires`-carrying function reified or handed to generic code as a value, and
///    every call whose target this body does not name — a fn-pointer parameter, a
///    `dyn Fn`, a callable the gate cannot resolve — because only that call site can
///    refuse a `requires`-carrying function another body turned into a value;
///  * (asked only when neither of those holds) a callable the body HOLDS
///    ([`held_uncharged_callables`]): what the gate asks only at a call's top-level
///    type arguments and at a pointer call, the body's types show at every depth — a
///    `requires`-carrying item inside an ADT the MIR inliner built, reified and handed
///    to a non-generic function, unsized into a `dyn`, or dropped inside a value whose
///    glue calls it; a fn-pointer or `dyn Fn` value handed on rather than called — and
///    its constants' VALUES show where no type does: such an item reified into a
///    struct field in a promoted, a `const` or a `static`, or behind a vtable there,
///    or in an associated constant of a local impl for a local type the body names.
/// NOT a masked fail-closed source (memory-safe's third clause): a dependency's
/// function the body calls may panic, which is what the attribute assumes away, and
/// its validity rests on the dependency-soundness premise docs/TCB.md already names
/// for a safe `assume_total` wrapper.
///
/// Only LOCAL bodies are asked, as in `assume_total_cannot_cover_body`: a foreign
/// body in a declared bundling scope keeps its skip, which already refuses at the
/// reuse gate.
pub(super) fn assume_total_cannot_cover_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> Option<Vec<String>> {
    if !body.source.def_id().is_local() {
        return None;
    }
    let owed = direct_callees_owing_caller_precondition(tcx, body);
    let unresolved_indirect = function_has_unresolved_indirect_call(tcx, body);
    let mut uncovered: Vec<String> = Vec::new();
    if !owed.is_empty() {
        uncovered.push(format!(
            "this body makes the call to {}, which carries a `requires` its callers owe",
            quoted_paths(tcx, owed),
        ));
    }
    if unresolved_indirect {
        let mut clause = String::from(
            "this body makes a call through a fn pointer, a `dyn Fn` or a function handed to \
             generic code as a value, whose target may owe a `requires` that only this call site \
             can charge (the indirect-call gate, `@trust-indirect-callee`, refuses it on every \
             proof-claiming policy)",
        );
        let valued = requires_carrying_fn_value_defs(tcx, body);
        if !valued.is_empty() {
            clause.push_str(&format!(
                " — here {}, which carries a `requires` its callers owe",
                quoted_paths(tcx, valued),
            ));
        }
        // Trust (2026-10-03): name a std/core/alloc item the gate refused under the
        // `certify`/memory-safe rule (`sysroot_callable_item`).
        clause.push_str(&sysroot_callable_item::unaccounted_sysroot_callable_clause(tcx, body));
        uncovered.push(clause);
    }
    if uncovered.is_empty() {
        let held = held_uncharged_callables(tcx, body);
        if !held.is_empty() {
            uncovered.push(format!(
                "this body holds {}: each is, or may carry, a function owing a `requires` that no \
                 call site in this body charges, and code the body hands it to can call it",
                held.join(", "),
            ));
        }
    }
    (!uncovered.is_empty()).then_some(uncovered)
}

/// Tell the user why an `#[trust::assume_total]` body is verified anyway: it makes a
/// call, or holds a callable, that [`assume_total_cannot_cover_calls`] names (one
/// note per clause). Emitted from `verification_decision`, which can run more than
/// once per body; the diagnostic context deduplicates identical diagnostics. A
/// warning on every policy: the refusal, if any, is the verification's own (a
/// `[precond]` row, the indirect-call gate, a dependency call's absent-callee row),
/// and under `-Ztrust-policy=advisory`, which fails nothing, this and the
/// verification report are what report it. "Verified as if the attribute were
/// absent", not "verified in full": `verification_decision`'s later arms (a
/// contract-generated closure, an unreachable start, a classifier skip) still apply,
/// exactly as they would without the attribute.
pub(super) fn warn_assume_total_does_not_cover_calls(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    uncovered: &[String],
) {
    let path = rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def_id));
    let mut diag = tcx.dcx().struct_span_warn(
        tcx.def_span(def_id),
        format!(
            "Trust: `#[trust::assume_total]` on `{path}` does not cover the preconditions its \
             calls owe; the body is verified as if the attribute were absent"
        ),
    );
    diag.note(
        "`assume_total` assumes this body's TOTALITY (no panic, termination), never a callee's \
         precondition: a function with a `requires` is verified only UNDER it, and a check its \
         verification elided under the clause is not in its code, so a call outside the clause \
         does not panic — it runs that function outside its verdict (a wrong value, or undefined \
         behaviour where its `unsafe` was proved under the clause)",
    );
    for clause in uncovered {
        diag.note(clause.clone());
    }
    diag.help(
        "establish the precondition in verified code: this body is now verified as if the \
         attribute were absent, so a direct call whose `requires` it proves (for example under a \
         guard) is accepted; a `requires`-carrying function handed over as a value or through a \
         pointer is charged by no call site, so call it directly instead; or keep the attribute \
         on a body that neither calls nor holds such a function",
    );
    diag.emit();
}

/// Trust (2026-10-03, the minting-site seam): where
/// [`refuse_requires_carrying_values_minted_outside_verified_bodies`] found a value minted
/// — a body or a type no Trust verification pass reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum MintingHolder {
    /// The `mir_for_ctfe` of a `static`, a `const`, an associated, inline or anonymous
    /// constant, or a compile-time function or closure ([`reads_ctfe_body`]).
    Initializer(LocalDefId),
    /// A promoted constant of this owner (`promoted_mir`), whatever the owner is.
    Promoted(LocalDefId),
    /// The hidden type of this local opaque type.
    Opaque(LocalDefId),
    /// A `sym` operand of this `global_asm!` item.
    GlobalAsm(LocalDefId),
}

impl MintingHolder {
    fn def_id(self) -> LocalDefId {
        match self {
            MintingHolder::Initializer(def)
            | MintingHolder::Promoted(def)
            | MintingHolder::Opaque(def)
            | MintingHolder::GlobalAsm(def) => def,
        }
    }

    /// The holder as the error header names it.
    fn describe(self, tcx: TyCtxt<'_>) -> String {
        let path = |def: DefId| trust_mir_extract::safe_def_path_str(tcx, def);
        match self {
            MintingHolder::Initializer(local) => {
                let def = local.to_def_id();
                match tcx.def_kind(def) {
                    DefKind::Static { .. } => format!("`{}` (a `static` initializer)", path(def)),
                    DefKind::Const { .. } => format!("`{}` (a `const` initializer)", path(def)),
                    DefKind::AssocConst { .. } => {
                        format!("`{}` (an associated `const`)", path(def))
                    }
                    DefKind::AnonConst
                        if tcx.anon_const_kind(def)
                            == rustc_middle::ty::AnonConstKind::NonTypeSystemInline =>
                    {
                        format!("an inline `const` in `{}`", path(tcx.typeck_root_def_id(def)))
                    }
                    DefKind::AnonConst => {
                        format!("an anonymous constant in `{}`", path(tcx.parent(def)))
                    }
                    _ => format!("`{}` (a compile-time function)", path(def)),
                }
            }
            MintingHolder::Promoted(owner) => {
                format!("a promoted constant in `{}`", path(owner.to_def_id()))
            }
            MintingHolder::Opaque(opaque) => match tcx.local_opaque_ty_origin(opaque) {
                rustc_hir::OpaqueTyOrigin::FnReturn { parent, .. }
                | rustc_hir::OpaqueTyOrigin::AsyncFn { parent, .. } => {
                    format!("the opaque return type of `{}`", path(parent.to_def_id()))
                }
                rustc_hir::OpaqueTyOrigin::TyAlias { parent, .. } => {
                    format!("the opaque type `{}`", path(parent.to_def_id()))
                }
            },
            MintingHolder::GlobalAsm(_) => String::from("a `global_asm!` `sym` operand"),
        }
    }

    /// Why no call site is charged for what this holder makes: the note after the header.
    fn uncharged_because(self, item: &str) -> String {
        match self {
            MintingHolder::Initializer(_) | MintingHolder::Promoted(_) => format!(
                "a constant's initializer and a promoted are evaluated at compile time, and no \
                 Trust verification pass reads them; the value made here can reach code — \
                 verified or not, in this crate or another — that calls `{item}` through it with \
                 any argument, and no call site is charged its `requires`"
            ),
            MintingHolder::Opaque(_) => format!(
                "callers of this function see only the opaque type: code that calls the value \
                 it returns names no item it could be charged for, and code no verdict here \
                 covers — a dependency, a crate built with verification off — can call `{item}` \
                 through it with any argument"
            ),
            MintingHolder::GlobalAsm(_) => format!(
                "the assembly can call `{item}` with any argument, and no call site is charged \
                 its `requires`"
            ),
        }
    }
}

/// Trust (2026-10-03): whether the seam reads `local`'s `mir_for_ctfe`: the initializer of
/// a `static`, a `const`, an associated, inline or anonymous constant — not a trivial one,
/// whose body is `_0 = const <value>` and mints nothing (`mir_for_ctfe` debug-asserts
/// against it) — or the body of a compile-time function or closure (`ConstContext::Const`;
/// a `const fn` is verified as its own body, and `mir_for_ctfe` does not steal it). Never a
/// Clean-origin def (no HIR; its body is the kernel-gated emission, asked before
/// `hir_body_const_context` would answer for it) or a synthetic coroutine body (whose
/// `hir_body_const_context` panics; it is never a const context).
fn reads_ctfe_body(tcx: TyCtxt<'_>, local: LocalDefId) -> bool {
    match tcx.def_kind(local.to_def_id()) {
        DefKind::Const { .. }
        | DefKind::AssocConst { .. }
        | DefKind::AnonConst
        | DefKind::Static { .. } => !tcx.is_trivial_const(local),
        DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {
            !crate::clean_origin_mir::is_clean_origin(tcx, local)
                && matches!(
                    tcx.hir_body_const_context(local),
                    Some(rustc_hir::ConstContext::Const { .. })
                )
        }
        _ => false,
    }
}

/// Trust (2026-10-03, the minting-site seam): refuse a function item that owes its caller
/// a `requires` turned into a VALUE outside every verified body — where no Trust
/// verification pass, and so no indirect-call gate, ever looks — at the site that mints it
/// (docs/KNOWN_HAZARDS.md, the `#[trust::assume_total]` entry's residual (b) and the ADT
/// entry's "Not reached"; docs/DECISION_QUEUE.md, AT-REQ-2). Read, each with
/// [`collect_requires_carrying_values`] (R1 call type arguments, R2 casts, R4 unevaluated
/// constants' arguments, R5 evaluated constants' allocations, R6 asm `sym` operands,
/// dropped places) unless noted:
///  * (a) the `mir_for_ctfe` of every body [`reads_ctfe_body`] names — `static`, `const`,
///    associated (a generic impl's and a trait default included: the scan reads the
///    polymorphic MIR, so nothing is evaluated), inline and anonymous constants, and
///    compile-time functions and closures;
///  * (b) every promoted of every owner (`local_def_may_have_promoted_mir`): a verified
///    function's, an `assume_total`, `#[trust::skip]` or classifier-skipped one's, a
///    generic one's, a constant's;
///  * (c) R7: the hidden type of every local opaque type (`-> impl Fn(u32) -> u32 { add1
///    }`, an RPITIT in an impl or a trait default, an `async fn`'s or block's coroutine, a
///    TAIT/ATPIT), walked with [`collect_requires_carrying_callables`] — a returned item
///    leaves its body through the return place, with no call, cast or type argument;
///  * (d) R6: every `global_asm!` `sym` operand, typed from the item's `typeck` results
///    as the mono collector types it (`mir_keys` never holds a `global_asm!` body).
///
/// Policy: `fatal` (strict — the default policy —, certify, memory-safe) emits an error,
/// otherwise (advisory, which makes no proof claim) a warning; either way emit and
/// continue, no `abort_if_errors`, so every site is reported and the driver's error gate
/// fails the build. One diagnostic per (holder, item), at its first site, in a
/// deterministic order (`mir_keys` is an index set; MIR order; HIR item order). The seam
/// writes no proof-report or transport row: the refusal is the diagnostic alone.
///
/// Placement (the caller, `trust_ensure_whole_crate_verification`): top level, after the
/// eager verification walk, only with verification enabled on a front-end-clean crate.
/// Every demand here — `mir_for_ctfe`, `promoted_mir`, `type_of` of an opaque, `typeck` of
/// a `global_asm!` item — is made at a point no type-system query is active, as the
/// backing inventory makes the first two; NEVER call this from a query the type system can
/// reach (`mir_for_ctfe`, `promoted_mir`, `mir_promoted`, `optimized_mir`, `type_of`,
/// `layout_of`): E0391 (docs/KNOWN_HAZARDS.md). It demands no `optimized_mir`.
///
/// Not reached: a value minted in a VERIFY-OFF crate (its own constants, promoteds and
/// functions — the dependency-soundness premise); a value written at RUN TIME by code no
/// verdict covers into a mutable or interior-mutable static; a DIRECT call to a `requires`
/// function inside an initializer (charged to nobody, but not a value: CTFE runs a `const
/// fn`'s `mir_for_ctfe`, cloned before `TrustVerify` elides anything); the local TYPES of
/// the bodies read (a promoted `&add1` holds the item in a reference and mints nothing).
/// Under `TRUST_VANILLA_DEBUG=1` each refusal prints `[MINTED_VALUE] `<item>` owes its
/// caller a `requires` and becomes a value in <holder>; refused`.
pub(super) fn refuse_requires_carrying_values_minted_outside_verified_bodies<'tcx>(
    tcx: TyCtxt<'tcx>,
    fatal: bool,
) {
    let mut minted: Vec<(MintingHolder, MintedValue)> = Vec::new();
    let mut collect = |holder: MintingHolder, body: &Body<'tcx>| {
        let mut found: Vec<MintedValue> = Vec::new();
        collect_requires_carrying_values(tcx, body.typing_env(tcx), body, &mut found);
        minted.extend(found.into_iter().map(|value| (holder, value)));
    };
    // (a) and (b).
    for &local in tcx.mir_keys(()) {
        if reads_ctfe_body(tcx, local) {
            collect(MintingHolder::Initializer(local), tcx.mir_for_ctfe(local));
        }
        if local_def_may_have_promoted_mir(tcx, local.to_def_id()) {
            for promoted in tcx.promoted_mir(local.to_def_id()).iter() {
                collect(MintingHolder::Promoted(local), promoted);
            }
        }
    }
    let items = tcx.hir_crate_items(());
    // (c) R7: the hidden type of every local opaque type.
    for opaque in items.opaques() {
        let (parent, in_trait_or_impl) = match tcx.local_opaque_ty_origin(opaque) {
            rustc_hir::OpaqueTyOrigin::FnReturn { parent, in_trait_or_impl }
            | rustc_hir::OpaqueTyOrigin::AsyncFn { parent, in_trait_or_impl } => {
                (parent, in_trait_or_impl)
            }
            rustc_hir::OpaqueTyOrigin::TyAlias { parent, .. } => (parent, None),
        };
        // An RPITIT of a trait method with no default body has no hidden type, and asking
        // `type_of` for one is a `span_bug!` (`type_of_opaque`'s own guard).
        if in_trait_or_impl == Some(rustc_hir::RpitContext::Trait)
            && !tcx.defaultness(parent).has_value()
        {
            continue;
        }
        let hidden = tcx.erase_and_anonymize_regions(
            tcx.type_of(opaque).instantiate_identity().skip_normalization(),
        );
        if hidden.references_error() {
            continue;
        }
        let typing_env = ty::TypingEnv::post_analysis(tcx, opaque);
        let hidden = tcx
            .try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(hidden))
            .unwrap_or(hidden);
        let mut owing: Vec<DefId> = Vec::new();
        collect_requires_carrying_callables(tcx, typing_env, hidden, &mut owing);
        let span = tcx.def_span(opaque);
        minted.extend(owing.into_iter().map(|item| {
            (
                MintingHolder::Opaque(opaque),
                MintedValue { item: Some(item), span, by: MintedBy::OpaqueHiddenType },
            )
        }));
    }
    // (d) R6: `global_asm!` `sym` operands.
    for item in items.free_items() {
        let def_id = item.owner_id.def_id;
        if !matches!(tcx.def_kind(def_id.to_def_id()), DefKind::GlobalAsm) {
            continue;
        }
        let asm = match tcx.hir_expect_item(def_id).kind {
            rustc_hir::ItemKind::GlobalAsm { asm, .. } => asm,
            // A `clean { … }` island shares `DefKind::GlobalAsm` and names no operand (the
            // backing escape census's precedent: asking it for its assembly was an ICE).
            rustc_hir::ItemKind::CleanIsland { .. } => continue,
            ref kind => rustc_span::span_bug!(
                tcx.def_span(def_id),
                "a `DefKind::GlobalAsm` item is neither assembly nor a Clean island: {kind:?}"
            ),
        };
        if !asm
            .operands
            .iter()
            .any(|(operand, _)| matches!(operand, rustc_hir::InlineAsmOperand::SymFn { .. }))
        {
            continue;
        }
        let typeck = tcx.typeck(def_id);
        for (operand, operand_span) in asm.operands {
            let rustc_hir::InlineAsmOperand::SymFn { expr } = operand else { continue };
            let mut owing: Vec<DefId> = Vec::new();
            collect_requires_carrying_callables(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                typeck.expr_ty(expr),
                &mut owing,
            );
            minted.extend(owing.into_iter().map(|owed| {
                (
                    MintingHolder::GlobalAsm(def_id),
                    MintedValue { item: Some(owed), span: *operand_span, by: MintedBy::AsmSym },
                )
            }));
        }
    }
    let mut reported: FxHashSet<(MintingHolder, Option<DefId>)> = FxHashSet::default();
    for (holder, value) in minted {
        if reported.insert((holder, value.item)) {
            report_minted_value(tcx, fatal, holder, value);
        }
    }
}

/// One refusal of [`refuse_requires_carrying_values_minted_outside_verified_bodies`].
fn report_minted_value(tcx: TyCtxt<'_>, fatal: bool, holder: MintingHolder, value: MintedValue) {
    let holder_text = holder.describe(tcx);
    let item = value.item.map(|item| trust_mir_extract::safe_def_path_str(tcx, item));
    if env_flag_enabled("TRUST_VANILLA_DEBUG") {
        match &item {
            Some(item) => eprintln!(
                "[MINTED_VALUE] `{item}` owes its caller a `requires` and becomes a value in \
                 {holder_text}; refused"
            ),
            None => eprintln!(
                "[MINTED_VALUE] {holder_text} holds a constant whose allocations this \
                 compilation cannot follow; refused"
            ),
        }
    }
    let mut notes: Vec<(Option<rustc_span::Span>, String)> = Vec::new();
    if matches!(holder, MintingHolder::Initializer(_) | MintingHolder::Promoted(_)) {
        notes.push((
            Some(tcx.def_span(holder.def_id())),
            String::from("the value is made in the body of this item"),
        ));
    }
    let (header, help) = match &item {
        Some(item) => {
            notes.push((None, format!("`{item}` {}", value.by.describe())));
            notes.push((None, holder.uncharged_because(item)));
            notes.push((
                None,
                format!(
                    "a function with a `requires` is verified only UNDER it: where its crate is \
                     built with verification on, a check its verification proved under the \
                     clause is elided from its code, so a call outside the clause can return a \
                     wrong value instead of panicking; built with verification off it elides \
                     nothing, and the call is still outside `{item}`'s contract"
                ),
            ));
            (
                format!(
                    "Trust verification failed for {holder_text}: it turns `{item}`, which \
                     carries a `requires` its callers owe, into a value that no call site charges"
                ),
                format!(
                    "store or return a closure that establishes the precondition and calls \
                     `{item}` directly — `|x| if <precondition> {{ {item}(x) }} else {{ … }}` — \
                     so the call is charged, and must be proved, in a verified body; or remove \
                     the `requires` if `{item}` is total"
                ),
            )
        }
        None => (
            format!(
                "Trust verification failed for {holder_text}: it holds a constant whose \
                 allocations this compilation cannot follow, so whether it turns a function \
                 that carries a `requires` into a value that no call site charges cannot be \
                 decided"
            ),
            String::from(
                "the walk follows a constant's allocations through their pointer provenance up \
                 to a fixed step bound and fails closed past it; a smaller constant can be read",
            ),
        ),
    };
    if !fatal {
        notes.push((
            None,
            String::from(
                "advisory makes no proof claim; strict (the default policy), certify and \
                 memory-safe refuse this",
            ),
        ));
    }
    if fatal {
        emit_with_notes(tcx.dcx().struct_span_err(value.span, header), &notes, &help);
    } else {
        emit_with_notes(
            tcx.dcx().struct_span_warn(value.span, format!("Trust (advisory): {header}")),
            &notes,
            &help,
        );
    }
}

/// Add `notes` (a span note where a span is given) and `help` to `diag`, and emit it.
fn emit_with_notes(
    mut diag: rustc_errors::Diag<'_>,
    notes: &[(Option<rustc_span::Span>, String)],
    help: &str,
) {
    for (span, note) in notes {
        match span {
            Some(span) => {
                diag.span_note(*span, note.clone());
            }
            None => {
                diag.note(note.clone());
            }
        }
    }
    diag.help(help.to_string());
    let _ = diag.emit();
}
