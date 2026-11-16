//! Trust (2026-09-29): can a SYSROOT destructor, at a CONCRETE type, reach code
//! that is not the sysroot's own, or an indirect call whose target this
//! compilation cannot name?
//!
//! # The false proofs this closes
//!
//! Sysroot drop glue is credited as panic-free by BELIEF, not by a check: an
//! admitted sysroot destructor (`admit_foreign_destructor`, the X1 rule) and the
//! bridge's name-keyed std arms (`is_std_owning_or_scaffold`,
//! `is_audited_panic_free_std_drop`, …) both let the drop lower to
//! `Assert(true)`, and the destructor body's own panics are demanded of nobody.
//! That belief is the disclosed sysroot TCB — `core`/`alloc`/`std` are compiled
//! verify-off by bootstrap and trusted on every path. It is NOT a belief about
//! the code a sysroot destructor CALLS when that code is chosen by the value
//! being dropped. MEASURED on stage 1 of `fb9f57688a6` and of origin/main
//! `fbb9fa383d2` (m3's std): each built exit 0 under `-Ztrust-policy=certify`
//! with `functions_verified` 1 of 1, and a verify-off `main` handing it a
//! verify-off dependency's value panicked in the dependency (exit 101):
//!
//!  * `drop` of a `Waker` built on a dependency's `RawWakerVTable` — core's
//!    `<Waker as Drop>::drop` calls `(self.waker.vtable.drop)(data)`, a function
//!    pointer STORED IN THE VALUE (`LocalWaker` is the same);
//!  * `drop` of an `io::Error` made by `io::Error::other(dep::Bomb(7))`, at scope
//!    end or inside `io::Result` — `Repr`/`CustomOwner`/`Custom`'s destructors
//!    call `outer_drop`/`error_drop`, function pointers stored in the value, which
//!    drop a `Box<dyn Error>` whose vtable is the dependency's;
//!  * `drop` of an `Rc<dyn Any>`, an `Arc<dyn Error + Send + Sync>`, an
//!    `Rc<dyn Fn() -> u8>` or an `Rc<dep::Bomb>` — `Rc`/`Arc` are credited by
//!    NAME, and the bridge's descent to the owned value stops at the `NonNull`
//!    field (which drops nothing, so it carries a total-drop stamp), so the
//!    pointee is never visited;
//!  * `drop` of a `Box<u32, dep::DepAlloc>` / `Rc<u32, dep::DepAlloc>` — the
//!    destructor calls the dependency allocator's `deallocate`.
//!
//! # The rule
//!
//! A sysroot destructor is REACH-CLOSED when every body it can execute is a
//! sysroot body this compilation can see and every call in those bodies names
//! its callee. Decided on the concrete, monomorphic `rustc` type — never on a
//! trust-ir `Ty` spelling — starting at `<T as Drop>::drop` resolved at the
//! type's own arguments (`Instance::try_resolve`) and walking what the
//! monomorphization collector walks:
//!
//!  * every `Call`/`TailCall` in a walked body must be a `FnDef` that resolves
//!    to an `Item` of a sysroot crate (walked in turn), a compiler shim (walked),
//!    a sysroot foreign item (a linked symbol, a leaf), a tuple-struct
//!    constructor (a leaf), or an intrinsic (a leaf whose `fn`-item arguments are
//!    walked as callees);
//!  * every `Drop` in a walked body is walked as rustc's own drop glue for the
//!    dropped type (`drop_glue::<U>`, the collector's `visit_drop_use`);
//!    `needs_drop` false means there is no glue at all.
//!
//! Anything else OPENS it, fail-closed: a call through a function pointer
//! (`Waker`, `io::Error`'s `Custom`), a virtual call or the drop of a `dyn`
//! (`Rc<dyn Any>`), any body outside the sysroot — a dependency's or this
//! crate's own (`Rc<dep::Bomb>` reaches `Bomb::drop`) — a sysroot body whose MIR
//! is not available, an unresolvable or still-generic callee, an async-drop or
//! vtable shim, an inline-asm `sym fn`, and a walk that exceeds its budget. A
//! type OUTSIDE the sysroot with no destructor runs no code: its glue is a shim,
//! so `Rc<dep::Plain>` stays closed. That is why this is a reachability question
//! and not a field-type question (a rule on the type's fields alone would stop
//! crediting a sysroot owner of a dependency type whenever that type has no
//! destructor).
//!
//! Only the DESTRUCTOR is walked, not the whole glue: the glue is `Drop::drop`
//! followed by the fields' glue, and every field is its own node — asked on its
//! own by `record_body_drop_reach` and visited on its own by the bridge's
//! classifier. What a destructor drops through a POINTER (`Rc`'s `RcInner<T>`,
//! `Repr`'s `CustomOwner`) is not a field node, and it is inside the walk.
//!
//! # What it does NOT decide
//!
//! It never CREDITS anything: an open answer withdraws a credit, a closed one
//! leaves every other gate as it was. Code reached only through a GLOBAL — the
//! `#[global_allocator]` behind `__rust_dealloc` (its own published contract,
//! `contract:global-alloc-dealloc-panic-free`), a user `#[panic_handler]` or
//! panic hook (reached only once a panic has begun), link-time interposition of
//! a sysroot `extern` symbol — is not a value's code and stays under the
//! premises that already cover it. A sysroot body's own panics stay the sysroot
//! TCB.
//!
//! ONE indirect call is followed rather than opened: a `thread_local!` key's
//! accessor, called by `LocalKey::<T>::try_with` as `(self.inner)(None)`, when
//! the key is a CONSTANT (a `static` the sysroot itself declared, reached as
//! `KEY.with(..)`/`KEY.try_with(..)` in a walked body, directly or through
//! `LocalKey::with`'s `self`). The accessor is then read out of the constant's
//! memory and walked like any other callee — the R16 front-A machinery
//! (`callee_is_local_key_try_with`, `tls_local_key_accessor_instance`, and its
//! structural drift pin on `try_with`'s body, which must hold exactly that one
//! indirect call). This is what `std::thread::panicking()` does inside every
//! poisoning guard's destructor (`MutexGuard`, `RwLock*Guard`). Every other
//! function pointer opens the glue: this walk does not follow pointer provenance
//! in general, and the cost is recorded in `docs/DECISION_QUEUE.md`.
//!
//! Pinned by `tests/ui/trust/policy_b/sysroot_drop_reaches_dependency_code.rs`.
//!
//! # The second question: can a body reach the GLOBAL allocator? (2026-10-02)
//!
//! [`body_global_allocator_reach`] walks the same way from a whole verified body —
//! its calls and its drops, through sysroot bodies and this crate's own — and asks
//! whether anything reached calls one of `alloc`'s global-allocator shims
//! (`__rust_alloc`, `__rust_alloc_zeroed`, `__rust_realloc`, `__rust_dealloc`).
//! Which function stands behind those symbols is a LINK-TIME choice: std's default
//! handlers (`System`), or the `GlobalAlloc` impl of whatever `#[global_allocator]`
//! the final link registers. An rlib does not make that choice, so a "no" from this
//! walk is what lets such a body be credited without the
//! `contract:global-alloc-dealloc-panic-free` premise (`trust_verify.rs`,
//! `body_is_charged_global_alloc_contract`). Every way the walk cannot tell answers
//! "may reach" (fail-closed).
//!
//! MEASURED before it (stage 1 of origin/main `280ff7c48cd`, m3): a verified rlib
//! of `Box::new(7u8)` returned, `Box::into_raw(Box::new(..))`, `x.to_string()` and
//! `String::from("x")` + `mem::forget` built exit 0 under `-Ztrust-policy=certify`
//! with `functions_verified` 5 of 5 and no premise row, and a verify-off `main`
//! that registers a `#[global_allocator]` whose `alloc` panics — itself, or through
//! a sibling dependency the library never sees — panicked in that allocator inside
//! each of the four (exit 101).
//!
//! # The allocation-error handler, and the third question (2026-10-03)
//!
//! Both walks also stop at `__rust_alloc_error_handler`, the entry through which
//! `handle_alloc_error` runs whatever handles a FAILED allocation
//! ([`is_alloc_error_handler_entry`]). In a binary that links `std` that is
//! `rust_oom`, which calls the hook installed with `std::alloc::set_alloc_error_hook`
//! — and a hook may panic, catchably (`tests/ui/panics/alloc_error_hook-unwind.rs`).
//! A body can reach the handler without any shim, by allocating through a non-global
//! allocator (`Box::new_in(x, System)` calls `System`'s `malloc` directly).
//! [`body_allocation_failure_reach`] asks the narrower question the hook needs: can
//! an allocation FAIL here — an allocating shim (not `__rust_dealloc`: freeing cannot
//! fail) or the handler itself.
//!
//! # A call's reach (2026-10-10, CALL-REACH-1 phase 1)
//!
//! [`call_site_reach`] asks the destructor walk's question of a CALL: started at the
//! instance a verified body's sysroot call resolves to, can it execute a body that is
//! not the sysroot's? Two more bodies are leaves there ([`ReachMode::Call`]): an item
//! of a StableCrateId-allowlisted TCB crate, and a local item held to its own
//! verification at a monomorphic instance (the SP-2 premise). The type rule
//! `unverified_edges::holds_target` is its pre-filter, so only a call whose type
//! arguments the rule flags is walked. An open call is withdrawn from every bridge
//! credit (`trust_verify.rs`, `record_body_call_reach`). A call through a `fn`
//! pointer is a leaf of that walk (D2) except while the call hands the instance a
//! `fn` pointer type (D6, [`handed_fn_pointer_type`]) or a value that holds one in a
//! field and is not shown built in the calling body (D7,
//! [`handed_outside_fn_pointer_value`]), and except inside a `LocalKey` method (D8,
//! 2026-10-13): there the pointer is the key's accessor, `(*self).inner`
//! ([`calls_own_key_accessor`]), followed to the accessor read out of a CONSTANT key
//! and otherwise OPEN — a key the verified caller was handed, or a constant whose
//! accessor does not read back. A `LocalKey` method call skips the pre-filter (whose
//! type rule cannot see the key), and one a `LocalKey` body makes on its own `self`
//! is [`CallReach::CoveredByCaller`]. The module keeps its name:
//! it is cited by path across the compiler, the bridge and the docs, and the
//! destructor walk is still its first reader.

use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_middle::mir::{
    AggregateKind, Body, CastKind, Const, InlineAsmOperand, Local, NonDivergingIntrinsic, Operand,
    Place, ProjectionElem, Rvalue, Statement, StatementKind, TerminatorKind,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{self, Instance, InstanceKind, ShimKind, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Spanned;
use rustc_span::def_id::{DefId, DefPathHash, LOCAL_CRATE};

use super::foreign_destructor_admission::crate_is_sysroot_credited;
use super::unverified_edges::{self, EdgeRule};

/// Bodies one walk may visit before it answers OPEN. A backstop: the
/// destructor of an ordinary std owner (`Vec<u8>`, `HashMap<u8, u8>`,
/// `BTreeMap`, `Rc<u32>`) reaches tens of bodies.
const DROP_REACH_MAX_BODIES: usize = 2048;

/// The verdict of [`sysroot_destructor_reach`]: `Ok(())` = reach-closed,
/// `Err(why)` = open (the first reason the walk met, for the debug trace).
pub(super) type DropReach = Result<(), String>;

thread_local! {
    /// Memo of [`sysroot_destructor_reach`] per (compilation, type). The answer is a pure
    /// function of the concrete type in one compilation, so — unlike the
    /// per-bundle records — it is safe to share across nested bundles and is never
    /// cleared. Keyed by `type_id_hash`, a stable hash over `DefPathHash`es (which
    /// carry the defining crate's `StableCrateId`), so two same-named crates can
    /// never share an entry.
    static DROP_REACH_MEMO: std::cell::RefCell<FxHashMap<(u64, u128), DropReach>> =
        std::cell::RefCell::new(FxHashMap::default());
}

/// Does the ADT `ty` carry a destructor defined in the compiler's own sysroot
/// (`crate_is_sysroot_credited`)? Only such a destructor is ever credited by
/// belief — an admitted destructor, or a name the bridge's std arms know — so
/// only its reach is this module's question. A local or dependency destructor
/// is credited only by a proof this compilation ran (`structural_drop`'s
/// `drop_glue_discharges_panic_freedom`) or not at all.
pub(super) fn has_sysroot_destructor<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let ty::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    adt_def.destructor(tcx).is_some_and(|d| crate_is_sysroot_credited(tcx, d.did.krate))
}

/// Can the DESTRUCTOR of `ty` — its `<T as Drop>::drop` at this concrete
/// instantiation, and everything that body runs — reach code outside the
/// sysroot? See the module docs. `Ok(())` for a type with no destructor.
///
/// The destructor, not the whole drop glue: the glue is `Drop::drop` followed by
/// the FIELDS' glue, and every field is its own node for the bridge's
/// classifier, asked on its own (`record_body_drop_reach`). MEASURED: the first
/// build of this change walked the whole glue of every ADT, local ones included,
/// and withdrew the credit of a local type whose destructor this crate PROVED —
/// `drop_glue_proved_destructor_credits.rs` and
/// `drop_glue_proved_local_drop_tolerates_print.rs#ok` went red. A whole-glue
/// walk of a sysroot holder would do the same one level up (`Option<S>` for such
/// an `S`, whose proof the classifier checks at the `S` node). What a destructor
/// drops through a pointer (`Rc`'s `RcInner<T>`, `Repr`'s `CustomOwner`) is NOT
/// a field node, so it is inside this walk.
///
/// `ty` must be the concrete type the drop runs at; anything still generic
/// answers OPEN.
pub(super) fn sysroot_destructor_reach<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> DropReach {
    if ty.has_non_region_param() || ty.has_non_region_infer() || ty.has_non_region_placeholders() {
        return Err("the dropped type is not fully monomorphic".to_string());
    }
    let ty::Adt(adt_def, adt_args) = *ty.kind() else {
        return Ok(());
    };
    let Some(destructor) = adt_def.destructor(tcx) else {
        return Ok(());
    };
    let key = (
        tcx.stable_crate_id(rustc_span::def_id::LOCAL_CRATE).as_u64(),
        tcx.type_id_hash(ty).as_u128(),
    );
    if let Some(known) = DROP_REACH_MEMO.with(|memo| memo.borrow().get(&key).cloned()) {
        return known;
    }
    let verdict = match Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        destructor.did,
        adt_args,
    ) {
        Ok(Some(instance)) => walk(
            tcx,
            vec![(instance, None)],
            ReachMode::SysrootOnly,
            ty::TypingEnv::fully_monomorphized(),
            None,
        ),
        _ => Err(format!("the destructor of `{ty:?}` does not resolve")),
    };
    if super::env_flag_enabled("TRUST_DROP_GATE_DEBUG") {
        match &verdict {
            Ok(()) => eprintln!("[DROP_REACH] {ty:?}: closed"),
            Err(why) => eprintln!("[DROP_REACH] {ty:?}: OPEN — {why}"),
        }
    }
    DROP_REACH_MEMO.with(|memo| memo.borrow_mut().insert(key, verdict.clone()));
    verdict
}

/// The glue instance rustc emits for dropping a `ty` in place, or why it cannot
/// be named. `Ok(None)` = no glue (nothing to walk). `typing_env` is
/// `fully_monomorphized` for every walk but a CALL walk from a generic body
/// (`ReachMode::Call`), which passes that body's.
fn drop_glue_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mode: ReachMode,
) -> Result<Option<Instance<'tcx>>, String> {
    // Trust (2026-09-29): a coroutine's glue drops the locals its body holds across
    // an await, so it is that body's code; outside the sysroot it opens the glue
    // like any other such body. Decided BEFORE the resolve, which reads the
    // coroutine's `optimized_mir` (`resolve_instance`: `coroutine_drop_async()`);
    // when the coroutine encloses the body being verified that is a query cycle.
    // MEASURED on the first build of this module: an async fn `g2` calling `g`,
    // where `g` drops an `Rc` of `g2`'s future, failed E0391 ("cycle detected when
    // optimizing MIR for `g2::{closure#0}`" … "resolving instance
    // `drop_glue::<{async fn body of g2()}>`") under verification; origin/main
    // reports rustc's own E0733 there. `walk_body` routes a call to the
    // `drop_glue` lang item (`Rc::drop`'s `drop_in_place`) through this function
    // for the same reason.
    if let ty::Coroutine(def_id, _)
    | ty::CoroutineClosure(def_id, _)
    | ty::CoroutineWitness(def_id, _) = *ty.kind()
        && !crate_is_sysroot_credited(tcx, def_id.krate)
    {
        return Err(format!(
            "drops the coroutine `{}`, a body outside the sysroot",
            trust_mir_extract::safe_def_path_str(tcx, def_id)
        ));
    }
    if !ty.needs_drop(tcx, typing_env) {
        return Ok(None);
    }
    // Trust (IOERROR-PAYLOAD-1, 2026-10-27): except a `dyn core::error::Error` whose
    // every value is a sysroot type in this crate graph (`dyn_error_payload`), as
    // each walk asks it (`dyn_error_object_closed_for`).
    if matches!(ty.kind(), ty::Dynamic(..)) {
        if dyn_error_object_closed_for(tcx, ty, mode) {
            return Ok(None);
        }
        return Err(format!("drops a `{ty:?}`, whose destructor is chosen by its vtable"));
    }
    let Some(glue_def) = tcx.lang_items().get(LangItem::DropGlue) else {
        return Err("no `drop_glue` lang item".to_string());
    };
    match Instance::try_resolve(tcx, typing_env, glue_def, tcx.mk_args(&[ty.into()])) {
        Ok(Some(instance)) => Ok(Some(instance)),
        _ => Err(format!("the drop glue of `{ty:?}` does not resolve")),
    }
}

/// Trust (IOERROR-PAYLOAD-1, 2026-10-27): may a walk in `mode` take the drop of the
/// trait object `ty` as closed? Only a CALL walk, which holds a local body by
/// induction and grants a runtime-checked row, never a proof: the rule says the
/// payload runs sysroot code AND this crate's held bodies (`BufWriter<W>`'s
/// destructor flushes through a local `W::write`, `Splice<I>`'s pulls a local
/// closure through `I::next`). The destructor walk ([`ReachMode::SysrootOnly`])
/// credits what it closes as panic-free sysroot code and OPENS at every local
/// body, so it never takes the rule, and neither does the global-allocator walk.
fn dyn_error_object_closed_for<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, mode: ReachMode) -> bool {
    mode == ReachMode::Call && super::dyn_error_payload::dyn_is_closed_error_object(tcx, ty)
}

/// One reached instance, plus — for an inherent method of `LocalKey` — the
/// constant key its `&'static self` is known to be (see the module docs).
type Reached<'tcx> = (Instance<'tcx>, Option<Const<'tcx>>);

/// Trust (2026-10-10, CALL-REACH-1 phase 1): which bodies a reach walk treats as
/// leaves. The two modes differ ONLY in [`body_to_walk`]'s answer for an `Item`
/// outside the sysroot and for a still-generic shim; every other step is shared.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReachMode {
    /// The destructor walk's rule ([`sysroot_destructor_reach`], unchanged since
    /// 2026-09-29), also the global-allocator walk's for sysroot bodies: every
    /// `Item` outside the sysroot OPENS the walk, this crate's own included.
    SysrootOnly,
    /// A call's resolved instance ([`call_site_reach`], DECISION_QUEUE CALL-REACH-1):
    /// two more leaves, an item of a StableCrateId-allowlisted TCB crate and a
    /// LOCAL item held to its own verification at a monomorphic instance
    /// ([`call_walk_leaf`]); and a shim at a still-generic instance (a walk from a
    /// generic calling body) OPENS instead of building its MIR.
    ///
    /// Amended 2026-10-10 (D2, D3; measured on the first phase-1 build): the walk
    /// follows what the instance BUILDS, not what it is handed. A vtable or `fn`
    /// pointer a walked body builds is walked like a direct call
    /// ([`walk_built_dispatch`]); a virtual call, a `dyn` drop and a call through
    /// a `fn` pointer are leaves, because what they reach was built from a VALUE
    /// the instance was given, the value-level class the rung-1 dyn reliance, the
    /// writer-relative facts and the drop-reach walk judge where the value is made
    /// (design phase 2: closed-world indirect calls). And a cleanup block is not
    /// walked: it runs only while a panic unwinds, and every withdrawal of this
    /// walk is a panic-freedom row.
    ///
    /// Amended 2026-10-13 (D6, DECISION_QUEUE CALL-REACH-1-D6): D2's premise fails at
    /// the walk's ROOT, where "where the value was made" is the verified calling
    /// body, which judges no pointer it was itself handed. So while the root call
    /// hands the instance a `fn` pointer TYPE ([`handed_fn_pointer_type`]), a call
    /// through a pointer opens the walk instead of being a leaf.
    ///
    /// Amended 2026-10-13 (D7, DECISION_QUEUE CALL-REACH-1-D7): the same holds for a
    /// pointer in a FIELD of a value the root call hands the instance (a `Waker`'s
    /// vtable, a handed `fmt::Arguments`' formatters, a handed `LocalKey`'s accessor),
    /// unless the calling body is shown to have built that value itself
    /// ([`handed_outside_fn_pointer_value`]).
    Call,
}

/// Walk everything `roots` can execute (see the module docs), under `mode`'s
/// leaves, in `typing_env`.
fn walk<'tcx>(
    tcx: TyCtxt<'tcx>,
    roots: Vec<Reached<'tcx>>,
    mode: ReachMode,
    typing_env: ty::TypingEnv<'tcx>,
    handed_fn_pointer: Option<HandedFnPointer<'tcx>>,
) -> DropReach {
    let mut work: Vec<Reached<'tcx>> = roots;
    let mut visited: FxHashSet<Reached<'tcx>> = FxHashSet::default();
    while let Some(reached) = work.pop() {
        if !visited.insert(reached) {
            continue;
        }
        if visited.len() > DROP_REACH_MAX_BODIES {
            return Err(match mode {
                ReachMode::SysrootOnly => {
                    format!("the glue reaches more than {DROP_REACH_MAX_BODIES} bodies (budget)")
                }
                ReachMode::Call => {
                    format!("reaches more than {DROP_REACH_MAX_BODIES} bodies (budget)")
                }
            });
        }
        let Some(body) = body_to_walk(tcx, reached.0, mode)? else {
            continue;
        };
        walk_body(tcx, reached, body, &mut work, mode, typing_env, handed_fn_pointer)?;
    }
    Ok(())
}

/// The MIR a reached instance runs, `Ok(None)` for a leaf that runs no Rust body
/// of its own, or why the instance opens the glue. `mode` decides the two
/// call-walk leaves ([`ReachMode`]).
fn body_to_walk<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    mode: ReachMode,
) -> Result<Option<&'tcx Body<'tcx>>, String> {
    match instance.def {
        InstanceKind::Item(def_id) => {
            let path = || trust_mir_extract::safe_def_path_str(tcx, def_id);
            if !crate_is_sysroot_credited(tcx, def_id.krate) {
                if mode == ReachMode::Call && call_walk_leaf(tcx, def_id, instance.args) {
                    return Ok(None);
                }
                return Err(format!(
                    "reaches `{}`, a body outside the sysroot (crate `{}`)",
                    path(),
                    tcx.crate_name(def_id.krate)
                ));
            }
            // A sysroot `extern` declaration is a linked symbol (allocator shims,
            // libc); it has no Rust body here. What can stand behind one is a
            // global premise (see the module docs), not the dropped value's code.
            if tcx.is_foreign_item(def_id) {
                return Ok(None);
            }
            if matches!(tcx.def_kind(def_id), DefKind::Ctor(..)) {
                return Ok(None);
            }
            if !tcx.is_mir_available(def_id) {
                return Err(format!("reaches `{}`, whose MIR is not available", path()));
            }
            Ok(Some(tcx.optimized_mir(def_id)))
        }
        // An intrinsic runs no body; its `fn`-item arguments are walked at the
        // call site.
        InstanceKind::Intrinsic(_) | InstanceKind::LlvmIntrinsic(_) => Ok(None),
        // D2: a call walk's virtual call dispatches through a vtable the instance
        // was handed (one it built was walked at the unsizing, `walk_built_dispatch`).
        InstanceKind::Virtual(..) if mode == ReachMode::Call => Ok(None),
        InstanceKind::Virtual(def_id, _) => Err(format!(
            "makes a virtual call to `{}`",
            trust_mir_extract::safe_def_path_str(tcx, def_id)
        )),
        // Trust (2026-10-10, CALL-REACH-1 phase 1): a call walk from a GENERIC
        // calling body reaches instances at that body's type parameters. An `Item`'s
        // optimized MIR is the same at any instantiation and is walked as the MIR
        // inliner walks it, but a shim's MIR is BUILT for its instance, and the drop
        // and clone shim builders do not evaluate predicates in the caller's
        // param-env (rust-lang/rust#127030): such a shim opens the walk rather than
        // being built. Never reached by the destructor and allocator walks, whose
        // every instance is monomorphic.
        InstanceKind::Shim(shim)
            if mode == ReachMode::Call
                && (instance.args.has_non_region_param()
                    || instance.args.has_non_region_infer()
                    || instance.args.has_non_region_placeholders()) =>
        {
            Err(format!("reaches the `{shim:?}` shim at a still-generic instance"))
        }
        InstanceKind::Shim(shim) => match shim {
            ShimKind::DropGlue(_, None)
            | (ShimKind::FnPtrAsPtr(..) | ShimKind::FnPtrFromPtr(..)) => Ok(None),
            // D2, as for a virtual call: the vtable's drop entry is walked where the
            // instance builds it.
            ShimKind::DropGlue(_, Some(ty))
                if mode == ReachMode::Call && matches!(ty.kind(), ty::Dynamic(..)) =>
            {
                Ok(None)
            }
            // Trust (IOERROR-PAYLOAD-1, 2026-10-27): as in `drop_glue_instance`.
            ShimKind::DropGlue(_, Some(ty))
                if matches!(ty.kind(), ty::Dynamic(..))
                    && dyn_error_object_closed_for(tcx, ty, mode) =>
            {
                Ok(None)
            }
            ShimKind::DropGlue(_, Some(ty)) if matches!(ty.kind(), ty::Dynamic(..)) => {
                Err(format!("drops a `{ty:?}`, whose destructor is chosen by its vtable"))
            }
            ShimKind::VTable(..) if mode == ReachMode::Call => Ok(None),
            ShimKind::DropGlue(_, Some(_))
            | ShimKind::Reify(..)
            | ShimKind::FnPtr(..)
            | ShimKind::ClosureOnce { .. }
            | ShimKind::Clone(..)
            | ShimKind::ThreadLocal(..) => Ok(Some(tcx.mir_shims(shim))),
            ShimKind::VTable(..)
            | ShimKind::ConstructCoroutineInClosure { .. }
            | ShimKind::FutureDropPoll(..)
            | ShimKind::AsyncDropGlueCtor(..)
            | ShimKind::AsyncDropGlue(..) => Err(format!("reaches the `{shim:?}` shim")),
        },
    }
}

/// Instantiate a type read off `instance`'s MIR at the instance's arguments, in
/// `typing_env` (`fully_monomorphized` but for a call walk from a generic body).
fn mono<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    ty: Ty<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
) -> Result<Ty<'tcx>, String> {
    instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            typing_env,
            ty::EarlyBinder::bind(tcx, ty),
        )
        .map_err(|_| format!("a type in `{:?}` does not normalize", instance.def))
}

fn walk_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    (instance, key): Reached<'tcx>,
    body: &Body<'tcx>,
    work: &mut Vec<Reached<'tcx>>,
    mode: ReachMode,
    // `fully_monomorphized` for the destructor and allocator walks (what this
    // function always used), the calling body's for a call walk from a generic
    // body (`ReachMode::Call`).
    typing_env: ty::TypingEnv<'tcx>,
    // Trust (2026-10-13, CALL-REACH-1 D6, D7): a `fn` pointer type the CALL this
    // walk started from hands the instance (`handed_fn_pointer_type`), or a value
    // holding one that came from outside the verified calling body
    // (`handed_outside_fn_pointer_value`), or `None`. While it is `Some`, a call
    // through a pointer is not D2's leaf: it opens.
    handed_fn_pointer: Option<HandedFnPointer<'tcx>>,
) -> DropReach {
    // The one indirect call followed (module docs): `try_with`'s accessor call,
    // when this instance IS `LocalKey::<T>::try_with` at a known constant key.
    let tls_accessor = match (instance.def, key) {
        (InstanceKind::Item(def_id), Some(key))
            if super::callee_is_local_key_try_with(tcx, def_id, instance.args)
                && super::local_key_try_with_glue_drift_pin(
                    tcx,
                    typing_env,
                    def_id,
                    instance.args,
                ) =>
        {
            super::tls_local_key_accessor_instance(tcx, typing_env, key)
        }
        _ => None,
    };
    for block in body.basic_blocks.iter() {
        if mode == ReachMode::Call {
            // D3: a cleanup block runs only while a panic unwinds, after the
            // panic a withdrawal of this walk would name has already happened.
            if block.is_cleanup {
                continue;
            }
            for statement in &block.statements {
                walk_built_dispatch(tcx, instance, body, statement, work, typing_env)?;
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let callee_ty = mono(tcx, instance, func.ty(body, tcx), typing_env)?;
                if let (ty::FnPtr(..), Some(accessor)) = (callee_ty.kind(), tls_accessor) {
                    // The drift pin admitted exactly one indirect call in this
                    // body: this one. Its target is the key's accessor.
                    work.push((accessor, None));
                    continue;
                }
                let ty::FnDef(def_id, fn_args) = *callee_ty.kind() else {
                    // Trust (IOERROR-PAYLOAD-1, 2026-10-27): core's `Custom` and
                    // `CustomOwner` destructors call the drop functions alloc stored
                    // at construction; in a graph where only sysroot code fills them
                    // (`dyn_error_payload`) the call is the drop of a `Box<T>`, which
                    // the CALL walk follows (`dyn_error_object_closed_for`: never the
                    // destructor or global-allocator walk, which open here as before).
                    if mode == ReachMode::Call
                        && let InstanceKind::Item(method) = instance.def
                        && let Some(pointee) =
                            super::dyn_error_payload::io_error_drop_pointer_box_pointee(
                                tcx, method, callee_ty,
                            )
                    {
                        if let Some(glue) =
                            drop_glue_instance(tcx, Ty::new_box(tcx, pointee), typing_env, mode)?
                        {
                            work.push((glue, None));
                        }
                        continue;
                    }
                    if mode == ReachMode::Call && matches!(callee_ty.kind(), ty::FnPtr(..)) {
                        // D8 (DECISION_QUEUE CALL-REACH-1-D8): a `LocalKey` method's
                        // pointer call is its key's accessor, `(self.inner)(..)`
                        // (`try_with`; `initialize_with`, behind `set`). D2's "judged
                        // where the value was made" does not hold of the key: at an
                        // untraced key the maker is whoever handed the verified caller
                        // the `&'static LocalKey`, and at a constant one it is the
                        // crate that declared the key, a dependency's included. So the
                        // call is followed to the accessor read out of a CONSTANT key
                        // when the call is provably `self.inner`, and otherwise opens.
                        // (`try_with`'s pinned arm above has already taken its own.)
                        if let InstanceKind::Item(method) = instance.def
                            && def_is_local_key_inherent_method(tcx, method)
                        {
                            let accessor = key
                                .filter(|_| calls_own_key_accessor(body, func))
                                .and_then(|key| {
                                    super::tls_local_key_accessor_instance(tcx, typing_env, key)
                                });
                            match accessor {
                                Some(accessor) => {
                                    work.push((accessor, None));
                                    continue;
                                }
                                None => {
                                    return Err(format!(
                                        "calls the accessor of a `LocalKey` it could not read \
                                         out of a constant key (`{callee_ty:?}` in `{:?}`)",
                                        instance.def
                                    ));
                                }
                            }
                        }
                        // D6: unless the call hands the instance a `fn` pointer,
                        // which may be the very one called here.
                        if let Some(handed) = handed_fn_pointer {
                            return Err(handed_fn_pointer_reason(handed, callee_ty, instance));
                        }
                        // D2: a pointer this body was handed (one it built was
                        // walked at the reification, `walk_built_dispatch`).
                        continue;
                    }
                    return Err(match callee_ty.kind() {
                        ty::FnPtr(..) => format!(
                            "calls through a function pointer (`{callee_ty:?}`) in `{:?}`",
                            instance.def
                        ),
                        _ => format!("calls a `{callee_ty:?}` in `{:?}`", instance.def),
                    });
                };
                // Trust (2026-09-29): a call to the `drop_glue` lang item (what
                // `ptr::drop_in_place` calls) IS a drop of its type argument:
                // decided by `drop_glue_instance`, as a `Drop` terminator is, so the
                // `dyn` and coroutine arms apply before the resolve asks for a
                // coroutine's MIR. MEASURED: resolving it directly re-entered the
                // enclosing coroutine's `optimized_mir` (E0391) for `Rc::drop` at an
                // enclosing async fn's future.
                if tcx.is_lang_item(def_id, LangItem::DropGlue) {
                    if let Some(glue) =
                        drop_glue_instance(tcx, fn_args.skip_binder().type_at(0), typing_env, mode)?
                    {
                        work.push((glue, None));
                    }
                    continue;
                }
                let callee =
                    match Instance::try_resolve(tcx, typing_env, def_id, fn_args.skip_binder()) {
                        Ok(Some(callee)) => callee,
                        _ => {
                            return Err(format!(
                                "calls `{}`, which does not resolve",
                                trust_mir_extract::safe_def_path_str(tcx, def_id)
                            ));
                        }
                    };
                if let InstanceKind::Intrinsic(_) = callee.def {
                    // An intrinsic may call an item it is handed (`const_eval_select`
                    // runs its `fn`-item argument): walk those as callees. A
                    // function POINTER handed to one (`catch_unwind`) is an indirect
                    // call.
                    for arg in args.iter() {
                        let arg_ty = mono(tcx, instance, arg.node.ty(body, tcx), typing_env)?;
                        match *arg_ty.kind() {
                            ty::FnDef(arg_def, arg_args) => {
                                match Instance::try_resolve(
                                    tcx,
                                    typing_env,
                                    arg_def,
                                    arg_args.skip_binder(),
                                ) {
                                    Ok(Some(item)) => work.push((item, None)),
                                    _ => {
                                        return Err(format!(
                                            "hands `{}` to an intrinsic and it does not resolve",
                                            trust_mir_extract::safe_def_path_str(tcx, arg_def)
                                        ));
                                    }
                                }
                            }
                            // D2: as for a call through the pointer (and D6).
                            ty::FnPtr(..) if mode == ReachMode::Call => {
                                if let Some(handed) = handed_fn_pointer {
                                    return Err(handed_fn_pointer_reason(handed, arg_ty, instance));
                                }
                            }
                            ty::FnPtr(..) | ty::Closure(..) => {
                                return Err(format!(
                                    "hands a `{arg_ty:?}` to the intrinsic `{}`",
                                    trust_mir_extract::safe_def_path_str(tcx, def_id)
                                ));
                            }
                            _ => {}
                        }
                    }
                } else {
                    // A `LocalKey` method carries its constant key along, so the
                    // `try_with` it reaches can follow the accessor call.
                    let callee_key = match (callee.def, args.first()) {
                        (InstanceKind::Item(callee_def), Some(receiver))
                            if def_is_local_key_inherent_method(tcx, callee_def) =>
                        {
                            local_key_receiver(tcx, instance, body, &receiver.node, key)
                        }
                        _ => None,
                    };
                    work.push((callee, callee_key));
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let dropped = mono(tcx, instance, place.ty(body, tcx).ty, typing_env)?;
                if let Some(glue) = drop_glue_instance(tcx, dropped, typing_env, mode)? {
                    work.push((glue, None));
                }
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                if operands.iter().any(|op| matches!(op, InlineAsmOperand::SymFn { .. })) {
                    return Err(format!("names a `sym fn` in inline asm in `{:?}`", instance.def));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// Trust (2026-10-10, CALL-REACH-1 D2): what one statement of a body a CALL walk
/// reached BUILDS for later indirect dispatch, pushed as reached: the vtable of an
/// unsizing coercion to a trait object (its method entries and the concrete type's
/// drop glue, `glue::unsize_tails` as the instance-hypothesis glue reads them) and
/// the target of a `fn`-pointer reification (an item, or a non-capturing closure's
/// body). The dispatch through such a vtable or pointer is then a leaf of the walk
/// (`body_to_walk`, `walk_body`): what it can reach is what was built, and a
/// vtable or pointer the instance was HANDED was built where the value was made.
///
/// A coercion at a still-generic type (a walk from a generic calling body) opens:
/// its vtable is chosen by an instantiation this walk cannot see. A `dyn` -> `dyn`
/// upcast builds nothing new (`unsize_tails`). A vtable built in a CONSTANT (a
/// promoted `&T as &dyn _`) is not read here; sysroot code names a caller's type
/// only through its type parameters, and no std constant unsizes one.
fn walk_built_dispatch<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
    statement: &Statement<'tcx>,
    work: &mut Vec<Reached<'tcx>>,
    typing_env: ty::TypingEnv<'tcx>,
) -> DropReach {
    let StatementKind::Assign(assign) = &statement.kind else {
        return Ok(());
    };
    let Rvalue::Cast(CastKind::PointerCoercion(coercion, _), operand, target) = &assign.1 else {
        return Ok(());
    };
    let still_generic = |ty: Ty<'tcx>| {
        ty.has_non_region_param() || ty.has_non_region_infer() || ty.has_non_region_placeholders()
    };
    match coercion {
        PointerCoercion::Unsize => {
            let target = mono(tcx, instance, *target, typing_env)?;
            let builds_trait_object = target
                .walk()
                .filter_map(|arg| arg.as_type())
                .any(|ty| matches!(ty.kind(), ty::Dynamic(..)));
            if !builds_trait_object {
                return Ok(());
            }
            let source = mono(tcx, instance, operand.ty(body, tcx), typing_env)?;
            if still_generic(source) || still_generic(target) {
                return Err(format!(
                    "unsizes `{source}` to `{target}` at a still-generic type in `{:?}`",
                    instance.def
                ));
            }
            let mut tails = Vec::new();
            super::instance_hypothesis::glue::unsize_tails(tcx, source, target, 0, &mut tails)?;
            for (concrete, dyn_ty) in tails {
                if let ty::Dynamic(predicates, ..) = *dyn_ty.kind()
                    && let Some(principal) = predicates.principal()
                {
                    let trait_ref = tcx.instantiate_bound_regions_with_erased(
                        principal.with_self_ty(tcx, concrete),
                    );
                    for entry in tcx.vtable_entries(trait_ref) {
                        if let ty::VtblEntry::Method(method) = *entry {
                            work.push((method, None));
                        }
                    }
                }
                if let Some(glue) = drop_glue_instance(tcx, concrete, typing_env, ReachMode::Call)?
                {
                    work.push((glue, None));
                }
            }
        }
        PointerCoercion::ReifyFnPointer(_) => {
            let source = mono(tcx, instance, operand.ty(body, tcx), typing_env)?;
            let ty::FnDef(def_id, args) = *source.kind() else {
                return Err(format!("reifies a `{source:?}` in `{:?}`", instance.def));
            };
            match Instance::resolve_for_fn_ptr(tcx, typing_env, def_id, args.skip_binder()) {
                Some(target) => work.push((target, None)),
                None => {
                    return Err(format!(
                        "reifies `{}` to a `fn` pointer and it does not resolve",
                        trust_mir_extract::safe_def_path_str(tcx, def_id)
                    ));
                }
            }
        }
        PointerCoercion::ClosureFnPointer(_) => {
            let source = mono(tcx, instance, operand.ty(body, tcx), typing_env)?;
            let ty::Closure(def_id, args) = *source.kind() else {
                return Err(format!("reifies a `{source:?}` in `{:?}`", instance.def));
            };
            work.push((
                Instance::resolve_closure(tcx, def_id, args, ty::ClosureKind::FnOnce),
                None,
            ));
        }
        PointerCoercion::UnsafeFnPointer
        | PointerCoercion::MutToConstPointer
        | PointerCoercion::ArrayToPointer => {}
    }
    Ok(())
}

/// Is `def_id` an inherent method of std's `LocalKey` (its diagnostic item —
/// never a rendered path — in a crate resident in this compiler's own sysroot,
/// `super::adt_is_resident_std_local_key`)? Such a method's first argument is
/// the key.
fn def_is_local_key_inherent_method(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    if def_id.is_local() || tcx.trait_of_assoc(def_id).is_some() {
        return false;
    }
    let Some(impl_did) = tcx.impl_of_assoc(def_id) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
    matches!(self_ty.kind(), ty::Adt(adt, _)
        if super::adt_is_resident_std_local_key(tcx, adt.did()))
}

/// The constant key a `LocalKey` method is called on, traced from its receiver
/// operand in `body` (an instance of `instance`): a constant (promoted or not)
/// through the single-definition copy/reborrow chain R16 front A accepts, or
/// this body's OWN `self` parameter, which is `inherited` (the key the caller
/// bound). `None` whenever the chain is anything else — the accessor call then
/// opens the glue.
fn local_key_receiver<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    inherited: Option<Const<'tcx>>,
) -> Option<Const<'tcx>> {
    match local_key_receiver_source(tcx, instance, body, operand) {
        KeyReceiver::Constant(key) => Some(key),
        KeyReceiver::OwnSelf => inherited,
        KeyReceiver::Untraced => None,
    }
}

/// Where a `LocalKey` method's receiver comes from ([`local_key_receiver_source`]).
enum KeyReceiver<'tcx> {
    /// A constant key, read off the chain.
    Constant(Const<'tcx>),
    /// The calling body's own `self` parameter (`_1`): the key ITS caller bound.
    OwnSelf,
    /// Anything else: a key this trace cannot name.
    Untraced,
}

/// The source of a `LocalKey` method's receiver `operand` in `body` (an instance of
/// `instance`), along the chain [`local_key_receiver`] documents.
fn local_key_receiver_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> KeyReceiver<'tcx> {
    let mut operand = operand.clone();
    for _ in 0..4 {
        let place = match &operand {
            Operand::Constant(constant) => {
                return match instance.try_instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(tcx, constant.const_),
                ) {
                    Ok(key) => KeyReceiver::Constant(key),
                    Err(_) => KeyReceiver::Untraced,
                };
            }
            Operand::Copy(place) | Operand::Move(place) => *place,
            _ => return KeyReceiver::Untraced,
        };
        if !place.projection.is_empty() {
            return KeyReceiver::Untraced;
        }
        let Some((definitions, definition)) = single_definition(body, place.local) else {
            return KeyReceiver::Untraced;
        };
        if definitions == 0 {
            // Never written: a parameter. Only `self` (`_1`) carries the key.
            return if place.local == Local::from_u32(1) && body.arg_count >= 1 {
                KeyReceiver::OwnSelf
            } else {
                KeyReceiver::Untraced
            };
        }
        operand = match definition {
            Some(Rvalue::Use(inner, _)) => inner.clone(),
            // `_2 = &(*_5)`: a reborrow copies `_5` verbatim.
            Some(Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source))
                if source.projection.len() == 1
                    && matches!(source.projection[0], ProjectionElem::Deref) =>
            {
                Operand::Copy(Place::from(source.local))
            }
            _ => return KeyReceiver::Untraced,
        };
    }
    KeyReceiver::Untraced
}

/// Trust (2026-10-13, CALL-REACH-1-D8): is the callee operand `func` of a call in
/// `body` (a `LocalKey` method's) exactly the key's accessor, `(*_1).0` — the one
/// field `inner` of the `&'static self` the method was called on — read directly or
/// through one local with that single definition? `LocalKey<T>` has exactly that
/// one field (`tls_local_key_accessor_instance` checks it on the key's type).
fn calls_own_key_accessor<'tcx>(body: &Body<'tcx>, func: &Operand<'tcx>) -> bool {
    let is_self_inner = |place: &Place<'tcx>| {
        place.local == Local::from_u32(1)
            && body.arg_count >= 1
            && matches!(
                &place.projection[..],
                [ProjectionElem::Deref, ProjectionElem::Field(field, _)] if field.as_u32() == 0
            )
            && matches!(single_definition(body, Local::from_u32(1)), Some((0, _)))
    };
    let place = match func {
        Operand::Copy(place) | Operand::Move(place) => *place,
        _ => return false,
    };
    if is_self_inner(&place) {
        return true;
    }
    if !place.projection.is_empty() {
        return false;
    }
    match single_definition(body, place.local) {
        Some((1, Some(Rvalue::Use(Operand::Copy(source) | Operand::Move(source), _)))) => {
            is_self_inner(source)
        }
        _ => false,
    }
}

/// How many times `local` is written in `body`, and its one whole-place
/// assignment when that is the only write. `None` when the body holds a
/// terminator this trace does not model.
fn single_definition<'a, 'tcx>(
    body: &'a Body<'tcx>,
    local: Local,
) -> Option<(usize, Option<&'a Rvalue<'tcx>>)> {
    let mut definitions = 0usize;
    let mut definition = None;
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign) if assign.0.local == local => {
                    definitions += 1;
                    if assign.0.projection.is_empty() {
                        definition = Some(&assign.1);
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    definitions += 1;
                }
                _ => {}
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => {
                definitions += 1;
            }
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => return None,
            _ => {}
        }
    }
    Some((definitions, if definitions == 1 { definition } else { None }))
}

// ---------------------------------------------------------------------------
// Trust (2026-10-10, CALL-REACH-1 phase 1): the reach of a CALL — the same walk,
// started at the instance a verified body's call resolves to. Design:
// docs/design/2026-10-10-call-reach-1-instance-type-arguments.md §3.2-§3.3; ruling:
// docs/DECISION_QUEUE.md CALL-REACH-1. NOT YET BUILT OR MEASURED.
//
// An absent sysroot callee is credited by many lanes on one belief, "a sysroot
// callee runs only sysroot code": the bridge's name-keyed tables, its model arms,
// the C2 std-map stamp. That belief is about the sysroot's code, not about the code
// the instance's TYPE ARGUMENTS choose (an allocator's `allocate`, a hasher's
// `write`, a payload's `eq`, the items a destination drops). Each earlier fix asked
// one more position at one more credit site (FRONT B, SP-1, SP-2, the drop-reach
// fix); this asks the instance once, here, while it still exists, and the bridge
// withdraws every credit from a call it opens (`call_reach_open_callees`).

/// The verdict of [`call_site_reach`] for one call site.
#[derive(Clone, Debug)]
pub(super) enum CallReach {
    /// Not this rule's subject (see [`call_site_reach`], step 1): the call names no
    /// sysroot body to believe in.
    NotJudged,
    /// Held by the pre-filter, the ruled type rule for a call into the sysroot
    /// (`unverified_edges::holds_target` under `EdgeRule::AssumedTotal`).
    ClosedByPrefilter,
    /// Not held by the pre-filter, and the walk found every body the instance can
    /// execute to be a sysroot body or one of the two call-walk leaves.
    ClosedByWalk,
    /// Trust (2026-10-13, CALL-REACH-1-D8): a `LocalKey` method's body forwarding
    /// its own `self` to another `LocalKey` method. The call that reached this body
    /// was judged at its own site, with the key it bound, and its walk went through
    /// this call; nothing is withdrawn here.
    CoveredByCaller,
    /// The first reason the decision met; the bridge prints it in the call's
    /// fail-closed absent-callee row.
    Open(String),
    /// Trust (2026-10-13, CALL-REACH-1 D7): `Open`, from a calling body outside the
    /// sysroot whose call hands the instance a pointer it did not build (D6's type or
    /// D7's value). The bridge withdraws it even when the callee is BUNDLED
    /// (`CallReachWithdrawals::insert_withdrawing_bundled`): the bundled body lowers
    /// the pointer call as an unsupported construct, whose row the default policy
    /// accepts. Never minted for a bundled sysroot member's own calls, so `std::fmt`'s
    /// internal calls are not withdrawn (the poison-loop trigger, KNOWN_HAZARDS).
    OpenWithdrawingBundled(String),
}

thread_local! {
    /// Memo of the call walk per (compilation, resolved instance, generic calling
    /// body). A monomorphic instance's answer is a pure function of the instance in
    /// one compilation, so it is shared across bodies and nested bundles and never
    /// cleared, as `DROP_REACH_MEMO` is; an instance still generic at a calling
    /// body's type parameters is walked in THAT body's typing environment, so its
    /// key also names the body (by `DefPathHash`). Keyed by the instance's stable
    /// hash (`sysroot_panic_census::instance_cache_key`), never a rendered path. A
    /// walk seeded with a `LocalKey` receiver or an intrinsic's arguments depends on
    /// the call site and is not memoized.
    static CALL_REACH_MEMO: std::cell::RefCell<
        FxHashMap<(u64, String, Option<DefPathHash>, bool), DropReach>,
    > = std::cell::RefCell::new(FxHashMap::default());
}

/// Is the `Item` `def_id`, outside the sysroot, a LEAF of a call walk
/// ([`ReachMode::Call`]) at `args`? Two kinds, each a body something other than this
/// walk answers for:
///
///  * an item of a StableCrateId-allowlisted TCB crate (num-bigint, num-rational,
///    serde_json: `ty_convert::is_authenticated_bignum_crate` and its serde_json
///    twin, the disclosed TCB entries docs/TCB.md names), at type arguments that
///    reach no foreign user code (an allowlisted crate's generic at a dependency's
///    type runs that type's code, which no TCB entry covers);
///  * a LOCAL item this crate holds to its own verification
///    (`local_item_is_held_to_this_rule`: local, not a foreign item, with MIR, not
///    `#[trust::skip]`), at a MONOMORPHIC instance whose type arguments reach no
///    foreign user code. This is the SP-2 premise (`source_callback_is_verified`)
///    the masking walk also rests on: the body is verified as its own root or as a
///    member of the bundle that calls it, so its own calls and drops are charged
///    there. A local GENERIC instantiated at a type parameter or a dependency's type
///    is not held, as `EdgeRule::AssumedTotal` does not hold it: its verdict was
///    reached at its own parameters. For a closure-like body only the PARENT's type
///    arguments are its instantiation; its upvars are values its own body handles
///    (charged there), and the drop of a closure inside a walked body is a separate
///    drop edge of this walk. (`unverified_edges`' `local_instance_args_reach_foreign`
///    also asks the upvars, because a skipped `assume_total` body charges nothing.)
///
/// Trust: a concrete local GENERIC also needs the instance walk's settled no-edge
/// answer. Foundational type arguments alone do not hold a dispatch into a foreign
/// impl, and a provisional coinductive answer must not enter `CALL_REACH_MEMO`.
fn call_walk_leaf<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, args: ty::GenericArgs<'tcx>) -> bool {
    let instantiation_reaches_foreign = |instantiation: &[ty::GenericArg<'tcx>]| {
        let mut memo: FxHashMap<Ty<'tcx>, bool> = FxHashMap::default();
        instantiation.iter().any(|arg| {
            arg.has_non_region_param()
                || arg.has_non_region_infer()
                || arg.has_non_region_placeholders()
        }) || instantiation
            .iter()
            .filter_map(|arg| arg.as_type())
            .any(|t| super::ty_reaches_foreign_user_code(tcx, t, &mut memo))
    };
    if trust_mir_extract::is_authenticated_bignum_crate(tcx, def_id.krate)
        || trust_mir_extract::is_authenticated_serde_json_crate(tcx, def_id.krate)
    {
        return !instantiation_reaches_foreign(args.as_slice());
    }
    if !def_id.is_local() || !super::local_item_is_held_to_this_rule(tcx, def_id) {
        return false;
    }
    let closure_view = args.as_closure();
    let coroutine_closure_view = args.as_coroutine_closure();
    let coroutine_view = args.as_coroutine();
    let instantiation: &[ty::GenericArg<'tcx>] =
        if matches!(tcx.def_kind(def_id), DefKind::Closure | DefKind::SyntheticCoroutineBody) {
            match *tcx.type_of(def_id).instantiate_identity().skip_norm_wip().kind() {
                ty::Closure(..) => closure_view.parent_args(),
                ty::CoroutineClosure(..) => coroutine_closure_view.parent_args(),
                ty::Coroutine(..) => coroutine_view.parent_args(),
                // Not a shape this can split: not a leaf (fail-closed).
                _ => return false,
            }
        } else {
            args.as_slice()
        };
    // Trust (INSTANCE-WALK-1 call-walk leaf): foundational type arguments do
    // not determine which crate implements a generic body's dispatched calls.
    // `Lw<u32>::next` can call a dependency's `Act2 for u32`; its generic-root
    // verdict is conditional on that instance. Use the same instantiated-body
    // check as `unverified_edges::holds_target`, rather than hiding that edge at
    // this local leaf of a sysroot `Iterator::count` walk.
    !instantiation_reaches_foreign(instantiation)
        && unverified_edges::local_instance_has_settled_no_edge(tcx, def_id, args)
}

/// Trust (2026-10-10, CALL-REACH-1 phase 1): can the call `func(args)` in `body` — a
/// verified body, the root or a bundled member, in `typing_env` (the root's own
/// `post_analysis` environment, or `fully_monomorphized` for an instantiated member)
/// — execute a body that is not a sysroot body, this crate's own verified body, or
/// an allowlisted TCB crate's? The decision procedure of the design's §3.2, every
/// step fail-closed:
///
///  1. THE SUBJECT. A callee operand that is a constant `FnDef` of a
///     sysroot-resident crate (`crate_is_sysroot_credited`), whose instance resolves
///     in `typing_env` to something other than a virtual call. Anything else is
///     `NotJudged`: a dependency's callee is already a masked fail-closed call, a
///     local one is bundled or keeps its own row, a call through a pointer has no
///     `FnDef`, and a VIRTUAL call or one that does not resolve here (a trait method
///     dispatched on the calling body's own type parameter) runs no sysroot body the
///     credit could rest on: its target is chosen by a vtable or by a later
///     instantiation, and the lanes that credit those (rung 1 §(c)'s
///     `dyn_contract_total`, the rung-1/rung-2 generic-dispatch discharges, OD-1's
///     instance hypotheses) each enumerate or hypothesize the target themselves.
///     Leaving them unjudged keeps those lanes exactly as they were.
///  2. A monomorphic type argument that holds (or is not shown free of) a
///     coroutine of THIS crate OPENS before any query about the call: rustc answers
///     such a type's drop glue from the coroutine's own optimized MIR, which may be
///     on the query stack below this body's (E0391; the census's rule and its
///     helper, `sysroot_panic_census::holds_local_coroutine`).
///  3. THE PRE-FILTER. `unverified_edges::holds_target` under `AssumedTotal`: the
///     callee is the authentic sysroot (or a local body held by induction) and
///     neither the spelled nor the resolved instantiation reaches foreign user
///     code. `ClosedByPrefilter`, nothing walked. Every call whose generics carry
///     only sysroot and local types stops here.
///  4. THE WALK, from the resolved instance, in [`ReachMode::Call`]: the destructor
///     walk's rules plus the two leaves of [`call_walk_leaf`]. A `LocalKey` method's
///     constant receiver is carried in, so `try_with`'s accessor is followed as the
///     destructor walk follows it; an intrinsic's `fn`-item arguments are the roots
///     instead (an intrinsic runs no body of its own).
///
/// A census `Total` implies CLOSED (§3.2 step 3); that is applied where the census
/// verdicts are final, in `build_native_trust_ir_bundle_for_verifier_api`, which
/// takes every census-credited key out of the open set.
pub(super) fn call_site_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> CallReach {
    let Some((def_id, fn_args)) = func.const_fn_def() else {
        return CallReach::NotJudged;
    };
    if !crate_is_sysroot_credited(tcx, def_id.krate) {
        return CallReach::NotJudged;
    }
    let path = || trust_mir_extract::safe_def_path_str(tcx, def_id);
    if fn_args.has_non_region_infer() || fn_args.has_non_region_placeholders() {
        return CallReach::Open("is instantiated at an unresolved type".to_string());
    }
    // At a type parameter of the calling body the finder would read a rigid
    // projection as "may hold one", so a generic call is left to the walk's own
    // routing instead: a drop goes through `drop_glue_instance`, which asks a
    // coroutine before any resolve, and a shim at a still-generic instance opens
    // before it is built (`body_to_walk`). The census never asks a generic call
    // either (`sysroot_panic_census::not_applicable`).
    if !fn_args.has_non_region_param()
        && super::sysroot_panic_census::holds_local_coroutine(
            tcx,
            typing_env,
            fn_args,
            &mut FxHashSet::default(),
        )
    {
        return CallReach::Open(
            "is instantiated at a type that holds (or is not shown free of) a coroutine of \
             the crate being compiled, whose drop glue this walk does not ask for"
                .to_string(),
        );
    }
    // A call to the `drop_glue` lang item is a drop of its type argument, decided
    // as the walk decides a `Drop` (`drop_glue_instance`).
    let root = if tcx.is_lang_item(def_id, LangItem::DropGlue) {
        match drop_glue_instance(tcx, fn_args.type_at(0), typing_env, ReachMode::Call) {
            Ok(Some(glue)) => glue,
            Ok(None) => return CallReach::ClosedByWalk,
            Err(why) => return CallReach::Open(why),
        }
    } else {
        match Instance::try_resolve(tcx, typing_env, def_id, fn_args) {
            Ok(Some(instance)) if !matches!(instance.def, InstanceKind::Virtual(..)) => instance,
            _ => return CallReach::NotJudged,
        }
    };
    let generic = root.args.has_non_region_param();
    // Trust (2026-10-13, CALL-REACH-1-D8; DECISION_QUEUE CALL-REACH-1-D8): a
    // `LocalKey` method runs the accessor its key's `inner` field holds, and the
    // key is a VALUE, not a type argument: the pre-filter's type rule cannot see
    // it. The constant key the call is made on, traced in the calling body as the
    // global-allocator walk traces it (`root_edges`); `None` when it is not a
    // constant this trace reaches (a key the caller was handed) or the calling
    // body is generic.
    let local_key_root = matches!(root.def, InstanceKind::Item(root_def)
        if def_is_local_key_inherent_method(tcx, root_def));
    let receiver = if local_key_root {
        args.first().map(|receiver| {
            let caller = Instance::new_raw(
                body.source.def_id(),
                ty::GenericArgs::identity_for_item(tcx, body.source.def_id()),
            );
            local_key_receiver_source(tcx, caller, body, &receiver.node)
        })
    } else {
        None
    };
    // D8: a `LocalKey` method's body forwarding its OWN `self` to another
    // (`with` calling `self.try_with(f)`, `set` calling `self.initialize_with(..)`)
    // is a member a call into that method reached, and that call was judged at
    // ITS site, where the key it binds was traced (or not) and the walk went on
    // through this body and this very call. Judging it again here, with no key,
    // would open every bundled `LocalKey` method on its own forwarding call.
    if matches!(receiver, Some(KeyReceiver::OwnSelf))
        && def_is_local_key_inherent_method(tcx, body.source.def_id())
    {
        return CallReach::CoveredByCaller;
    }
    let traced_key = match receiver {
        Some(KeyReceiver::Constant(key)) if !generic => Some(key),
        _ => None,
    };
    // D8: the pre-filter's type rule cannot see the key, so a `LocalKey` method is
    // always walked: at a traced constant key the walk follows the accessor read
    // out of it (R16 front A), and at any other key the accessor call opens the
    // walk (`walk_body`).
    //
    // D7 (`handed_outside_fn_pointer_value`), asked BEFORE the pre-filter: the
    // pre-filter reads type arguments only, and a pointer in a field of a handed
    // value is chosen by no type argument. MEASURED on the first D7 build:
    // `std::fmt::format(a)` on a handed `fmt::Arguments` was `closed(prefilter)` and
    // still built exit 0 under the default policy. A receiver traced to a constant
    // key is not asked (the walk follows that key's accessor, D8); an untraced
    // `LocalKey` receiver is asked like any other value.
    let handed_outside_value =
        handed_outside_fn_pointer_value(tcx, body, typing_env, args, traced_key.is_some());
    if !local_key_root
        && handed_outside_value.is_none()
        && unverified_edges::holds_target(
            tcx,
            typing_env,
            EdgeRule::AssumedTotal,
            def_id,
            fn_args,
            false,
        )
    {
        return CallReach::ClosedByPrefilter;
    }
    if root.args.has_non_region_infer() || root.args.has_non_region_placeholders() {
        return CallReach::Open("is instantiated at an unresolved type".to_string());
    }
    // The roots of the walk, and whether they depend on this call site beyond its
    // instance (then the verdict is not memoized).
    let (roots, site_specific): (Vec<Reached<'tcx>>, bool) = match root.def {
        InstanceKind::Intrinsic(_) => {
            // An intrinsic runs no body; the items it is handed are what it calls
            // (`const_eval_select`), and a pointer or closure handed to it is an
            // indirect call (as in `walk_body`).
            let mut roots = Vec::new();
            for arg in args {
                let arg_ty = match tcx.try_normalize_erasing_regions(
                    typing_env,
                    ty::Unnormalized::new_wip(arg.node.ty(body, tcx)),
                ) {
                    Ok(arg_ty) => arg_ty,
                    Err(_) => {
                        return CallReach::Open(format!(
                            "hands the intrinsic `{}` an argument whose type does not normalize",
                            path()
                        ));
                    }
                };
                match *arg_ty.kind() {
                    ty::FnDef(arg_def, arg_args) => {
                        match Instance::try_resolve(
                            tcx,
                            typing_env,
                            arg_def,
                            arg_args.skip_binder(),
                        ) {
                            Ok(Some(item)) => roots.push((item, None)),
                            _ => {
                                return CallReach::Open(format!(
                                    "hands `{}` to an intrinsic and it does not resolve",
                                    trust_mir_extract::safe_def_path_str(tcx, arg_def)
                                ));
                            }
                        }
                    }
                    ty::FnPtr(..) | ty::Closure(..) => {
                        return CallReach::Open(format!(
                            "hands a `{arg_ty:?}` to the intrinsic `{}`",
                            path()
                        ));
                    }
                    _ => {}
                }
            }
            (roots, true)
        }
        InstanceKind::Item(_) if local_key_root && !generic => {
            // The constant key the call is made on (`traced_key` above).
            let site_specific = traced_key.is_some();
            (vec![(root, traced_key)], site_specific)
        }
        _ => (vec![(root, None)], false),
    };
    // D6: does this call hand the instance a `fn` pointer (see
    // `handed_fn_pointer_type`)? D7: or a value that holds one in a field and is not
    // shown built in the calling body (`handed_outside_fn_pointer_value`)? Then no
    // call through a pointer is a leaf of its walk.
    let handed_fn_pointer = handed_fn_pointer_type(tcx, body, typing_env, fn_args, root, args)
        .map(HandedFnPointer::Type)
        .or(handed_outside_value.map(HandedFnPointer::OutsideValue));
    let memo_key = (!site_specific).then(|| {
        (
            tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
            super::sysroot_panic_census::instance_cache_key(tcx, root),
            generic.then(|| tcx.def_path_hash(body.source.def_id())),
            handed_fn_pointer.is_some(),
        )
    });
    let known = memo_key
        .as_ref()
        .and_then(|key| CALL_REACH_MEMO.with(|memo| memo.borrow().get(key).cloned()));
    let verdict = match known {
        Some(verdict) => verdict,
        None => {
            let verdict = walk(tcx, roots, ReachMode::Call, typing_env, handed_fn_pointer);
            if let Some(key) = memo_key {
                CALL_REACH_MEMO.with(|memo| memo.borrow_mut().insert(key, verdict.clone()));
            }
            verdict
        }
    };
    match verdict {
        Ok(()) => CallReach::ClosedByWalk,
        Err(why)
            if handed_fn_pointer.is_some()
                && !crate_is_sysroot_credited(tcx, body.source.def_id().krate) =>
        {
            CallReach::OpenWithdrawingBundled(why)
        }
        Err(why) => CallReach::Open(why),
    }
}

/// Trust (2026-10-13, CALL-REACH-1 D6; DECISION_QUEUE CALL-REACH-1-D6): the first
/// `fn` pointer type the call `func(args)` HANDS the instance `root` — one written
/// anywhere in the generic arguments the call spells (`fn_args`) or resolves to
/// (`root.args`), or in the type of an argument it passes — or `None`.
///
/// D2 made a call through a `fn` pointer a leaf of the call walk on the premise that
/// a pointer the instance was handed "was built where the value was made", and is
/// judged there. At the walk's ROOT that premise names the verified CALLING body,
/// and nothing there judges a pointer that body was itself handed: `pub fn f(s: &mut
/// BTreeSet<u32>, it: Map<Copied<Iter<u32>>, fn(u32) -> u32>) { s.extend(it) }`
/// receives the pointer from a caller outside the crate, and `extend` runs it (the
/// `fn` pointer shim's call) — MEASURED on the stage 1 of main `825437bfeb`:
/// `closed(walk)`, then exit 0 under the default policy with one runtime-checked row
/// (`collect_extend_source_runs_unverified_code.rs#{btreeset,btreemap}_extend_fnptr`).
/// So while the call hands the instance a `fn` pointer type, a pointer call the walk
/// meets may be that value's, and it OPENS (`walk_body`). A pointer type the call
/// does not hand cannot carry a value the call handed, so std's own internal
/// pointers (the `fmt` builders D2 was measured on) keep D2's leaf.
///
/// The structural type walk (`Ty::walk`) reads generic arguments, references and
/// tuples, never an ADT's fields: a pointer stored in a sysroot ADT's FIELD of a
/// value the calling body was handed (a `Waker`'s `RawWakerVTable`) is not found
/// here; D7 asks it ([`handed_outside_fn_pointer_value`]). Fail-closed in the other
/// direction: a pointer the calling body reified from a verified local item is not
/// told apart from a handed one.
fn handed_fn_pointer_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    fn_args: ty::GenericArgs<'tcx>,
    root: Instance<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> Option<Ty<'tcx>> {
    // Trust (upstream 1.101): when the ROOT is itself a closure/coroutine
    // item, `root.args` carries the callee's own SIGNATURE as a `fn` pointer
    // type argument (now `Binder`-wrapped) — the same signature
    // `first_handed_fn_pointer` already holds names no pointer value when it
    // meets it inside a closure TYPE. Decompose a closure-like root's args
    // the same way (parent arguments + captures), or every closure root
    // "hands" itself its own signature and D6 opens on it — measured on
    // core's `DebugTuple::field::{closure#0}` (the `Result::and_then` closure
    // upstream moved from the generic `field_with` into the concrete
    // `field`), whose row then kept every derived-`Debug` root fail-closed.
    let root_spelled: Vec<Ty<'tcx>> = match tcx.def_kind(root.def_id()) {
        DefKind::Closure => {
            let closure = root.args.as_closure();
            closure
                .parent_args()
                .iter()
                .filter_map(|arg| arg.as_type())
                .chain(std::iter::once(closure.tupled_upvars_ty()))
                .collect()
        }
        DefKind::SyntheticCoroutineBody => {
            let coroutine = root.args.as_coroutine();
            coroutine
                .parent_args()
                .iter()
                .filter_map(|arg| arg.as_type())
                .chain(std::iter::once(coroutine.tupled_upvars_ty()))
                .collect()
        }
        _ => root.args.iter().filter_map(|arg| arg.as_type()).collect(),
    };
    let spelled = fn_args.iter().filter_map(|arg| arg.as_type()).chain(root_spelled);
    let passed = args.iter().flat_map(|arg| {
        let raw = arg.node.ty(body, tcx);
        // The raw type as well as the normalized one: a projection that does not
        // normalize here may still name a pointer in its own arguments.
        let normalized =
            tcx.try_normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(raw)).ok();
        std::iter::once(raw).chain(normalized)
    });
    spelled.chain(passed).find_map(first_handed_fn_pointer)
}

/// The first `fn` pointer type written in `ty`'s structure (D6). A closure-like
/// type's generic arguments carry its SIGNATURE as a `fn` pointer type
/// (`closure_sig_as_fn_ptr_ty`), which names no pointer value: only its parent's
/// arguments and its captures are searched, the captures because a closure the
/// sysroot built (`map_fold`'s) can hold the handed pointer and call it.
fn first_handed_fn_pointer<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let mut work = vec![ty];
    let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
    while let Some(ty) = work.pop() {
        if !seen.insert(ty) {
            continue;
        }
        let mut walker = ty.walk();
        while let Some(arg) = walker.next() {
            let Some(t) = arg.as_type() else { continue };
            let (parent, upvars) = match *t.kind() {
                ty::FnPtr(..) => return Some(t),
                ty::Closure(_, args) => {
                    let args = args.as_closure();
                    (
                        args.parent_args()
                            .iter()
                            .filter_map(|arg| arg.as_type())
                            .collect::<Vec<_>>(),
                        args.tupled_upvars_ty(),
                    )
                }
                ty::CoroutineClosure(_, args) => {
                    let args = args.as_coroutine_closure();
                    (
                        args.parent_args()
                            .iter()
                            .filter_map(|arg| arg.as_type())
                            .collect::<Vec<_>>(),
                        args.tupled_upvars_ty(),
                    )
                }
                ty::Coroutine(_, args) => {
                    let args = args.as_coroutine();
                    (
                        args.parent_args()
                            .iter()
                            .filter_map(|arg| arg.as_type())
                            .collect::<Vec<_>>(),
                        args.tupled_upvars_ty(),
                    )
                }
                _ => continue,
            };
            walker.skip_current_subtree();
            work.extend(parent);
            work.push(upvars);
        }
    }
    None
}

/// What the root call of a call walk hands its instance that turns D2's pointer-call
/// leaf off (D6, D7).
#[derive(Clone, Copy, Debug)]
enum HandedFnPointer<'tcx> {
    /// D6: a `fn` pointer TYPE written in the call's generic arguments or in the type
    /// of an argument it passes ([`handed_fn_pointer_type`]).
    Type(Ty<'tcx>),
    /// D7: an argument whose type holds a `fn` pointer in a FIELD (a `Waker`'s
    /// `RawWakerVTable`), and whose value is not shown built in the verified calling
    /// body ([`handed_outside_fn_pointer_value`]). The type is the argument's.
    OutsideValue(Ty<'tcx>),
}

/// The reason a call walk opens at a call through a `fn` pointer while its root call
/// hands the instance one (D6, [`handed_fn_pointer_type`]; D7,
/// [`handed_outside_fn_pointer_value`]).
fn handed_fn_pointer_reason<'tcx>(
    handed: HandedFnPointer<'tcx>,
    called: Ty<'tcx>,
    instance: Instance<'tcx>,
) -> String {
    match handed {
        HandedFnPointer::Type(handed) => format!(
            "calls through a function pointer (`{called:?}`) in `{:?}`, and the call hands it a \
             `{handed:?}`, whose target is chosen by a value this walk does not see built \
             (CALL-REACH-1 D6)",
            instance.def
        ),
        HandedFnPointer::OutsideValue(handed) => format!(
            "calls through a function pointer (`{called:?}`) in `{:?}`, and the call hands it a \
             `{handed:?}` that holds a function pointer in a field and was not built in the \
             verified calling body, so its target is chosen outside this walk \
             (CALL-REACH-1 D7)",
            instance.def
        ),
    }
}

/// Trust (2026-10-13, CALL-REACH-1 D7; DECISION_QUEUE CALL-REACH-1-D7): the type of
/// the first argument of `args` (the call's operands in the verified `body`) whose
/// type holds a `fn` pointer VALUE in its structure — a field of an ADT, at any depth,
/// through references, raw pointers, arrays, slices, tuples, closure captures and
/// `Box` — and whose value may have come from OUTSIDE `body` ([`OutsideValues`]); or
/// `None`.
///
/// D6 reads only `fn` pointer TYPES written in the call's instantiation and argument
/// types. A pointer stored in a sysroot ADT's field is not one: `pub fn f(w: &Waker) {
/// w.wake_by_ref() }` hands `wake_by_ref` the caller's caller's `RawWakerVTable`, and
/// `wake_by_ref` calls through it. MEASURED on the stage 1 of main `3ed8b09dad`:
/// `closed(walk)`, then exit 0 under the default policy with one runtime-checked row.
/// The same holds for a handed `fmt::Arguments` (`pub fn f(a: Arguments) -> String {
/// format(a) }`), whose `rt::Argument` formatters the caller chose. A purely
/// type-based rule cannot tell that `Arguments` from the one `format_args!` builds in
/// the body itself, whose formatter pointers are reified inside the `rt::Argument`
/// builder calls this rule judges at their own call sites; D7 tells them apart by the
/// VALUE's provenance inside the calling body, not by its type.
///
/// Asked only for a calling body outside the sysroot (the verified root, or a local
/// bundled member). A bundled SYSROOT member's parameters are values its bundled
/// caller passed, so the root call that passed them is where they are judged; asking
/// a member's own calls would withdraw `std::fmt`'s internal calls, the D2 trigger of
/// the poison-loop false proof (KNOWN_HAZARDS, "poison loop").
///
/// `receiver_traced`: the first argument is a `LocalKey` receiver the caller traced
/// to its constant key; the walk follows that key's accessor exactly (R16 front A),
/// so the argument is not asked. An untraced key is asked like any other value.
fn handed_outside_fn_pointer_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    receiver_traced: bool,
) -> Option<Ty<'tcx>> {
    if crate_is_sysroot_credited(tcx, body.source.def_id().krate) {
        return None;
    }
    let mut reach = FnPointerReach::new(tcx, typing_env);
    let candidates: Vec<(&Operand<'tcx>, Ty<'tcx>)> = args
        .iter()
        .skip(usize::from(receiver_traced))
        .filter_map(|arg| {
            let ty = reach.normalize(arg.node.ty(body, tcx));
            reach.holds_fn_pointer(ty).then_some((&arg.node, ty))
        })
        .collect();
    if candidates.is_empty() {
        return None;
    }
    let outside = OutsideValues::compute(tcx, body, &mut reach);
    candidates
        .into_iter()
        .find(|(operand, _)| outside.operand(tcx, body, operand, &mut reach))
        .map(|(_, ty)| ty)
}

/// Trust (2026-10-13, CALL-REACH-1 D7): does a type's VALUE hold a `fn` pointer, or
/// (for a carrier, [`FnPointerReach::carrier`]) a trait object a `fn` pointer value
/// can be recovered from? Read structurally: an ADT's fields at its instantiation,
/// references and raw pointers' pointees, arrays, slices, tuples, a closure's or
/// coroutine closure's captures. A `PhantomData<fn()>` holds none. Every type this
/// cannot read through answers yes (fail-closed): a type parameter, an alias that
/// does not normalize, a placeholder or inference variable, a coroutine (its saved
/// locals are not its type arguments), and a type past the budget.
struct FnPointerReach<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    memo: FxHashMap<(Ty<'tcx>, bool), bool>,
}

/// Types one [`FnPointerReach`] question may visit before it answers yes.
const FN_POINTER_REACH_MAX_TYPES: usize = 4096;

impl<'tcx> FnPointerReach<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Self {
        FnPointerReach { tcx, typing_env, memo: FxHashMap::default() }
    }

    /// `ty` normalized in the walk's typing environment, or `ty` itself when it does
    /// not normalize (the reach then reads its alias as "may hold one").
    fn normalize(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx
            .try_normalize_erasing_regions(self.typing_env, ty::Unnormalized::new_wip(ty))
            .unwrap_or(ty)
    }

    /// Does a value of `ty` hold a `fn` pointer (D7's question at the call)? A `dyn`
    /// does not count here: a virtual call is D2's other leaf, a separate class
    /// (SC-8's open-principal census refuses a handed principal).
    fn holds_fn_pointer(&mut self, ty: Ty<'tcx>) -> bool {
        self.reaches(ty, false)
    }

    /// Can a value of `ty` carry a `fn` pointer value into the calling body: one it
    /// holds, or one a `dyn` it holds can be downcast to (`<dyn Any>::downcast_ref`)?
    /// Only a carrier is ever marked outside ([`OutsideValues`]): a `&u32` read off a
    /// handed `&S` holds no pointer, so the `rt::Argument` built from it is not one.
    fn carrier(&mut self, ty: Ty<'tcx>) -> bool {
        self.reaches(ty, true)
    }

    fn reaches(&mut self, ty: Ty<'tcx>, count_dyn: bool) -> bool {
        if let Some(&known) = self.memo.get(&(ty, count_dyn)) {
            return known;
        }
        let mut work = vec![ty];
        let mut seen: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        let mut found = false;
        while let Some(t) = work.pop() {
            if !seen.insert(t) {
                continue;
            }
            if seen.len() > FN_POINTER_REACH_MAX_TYPES {
                found = true;
                break;
            }
            match *t.kind() {
                ty::FnPtr(..) => {
                    found = true;
                    break;
                }
                ty::Dynamic(..) => {
                    if count_dyn {
                        found = true;
                        break;
                    }
                }
                ty::Bool
                | ty::Char
                | ty::Int(_)
                | ty::Uint(_)
                | ty::Float(_)
                | ty::Str
                | ty::Never
                | ty::Foreign(_)
                | ty::FnDef(..) => {}
                ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => work.push(pointee),
                ty::Array(element, _) | ty::Slice(element) => work.push(element),
                // A pattern type (`usize is 0..=isize::MAX`, std's `Cap`) holds a
                // value of its base type.
                ty::Pat(base, _) => work.push(base),
                ty::Tuple(elements) => work.extend(elements.iter()),
                ty::Adt(adt, adt_args) => {
                    for field in adt.all_fields() {
                        let field_ty = field.ty(self.tcx, adt_args);
                        match self.tcx.try_normalize_erasing_regions(self.typing_env, field_ty) {
                            Ok(field_ty) => work.push(field_ty),
                            Err(_) => {
                                found = true;
                                break;
                            }
                        }
                    }
                    if found {
                        break;
                    }
                }
                ty::Closure(_, closure_args) => {
                    work.push(closure_args.as_closure().tupled_upvars_ty())
                }
                ty::CoroutineClosure(_, closure_args) => {
                    work.push(closure_args.as_coroutine_closure().tupled_upvars_ty())
                }
                // A type parameter, an unnormalized alias, a placeholder, an inference
                // variable, a coroutine and its witness, a pattern or unsafe-binder
                // type, an error: not read through (fail-closed).
                _ => {
                    found = true;
                    break;
                }
            }
        }
        self.memo.insert((ty, count_dyn), found);
        found
    }
}

/// Trust (2026-10-13, CALL-REACH-1 D7): which locals of a verified calling body may
/// hold a carrier value ([`FnPointerReach::carrier`]) that came from OUTSIDE the body.
/// A flow-insensitive may-analysis to a fixpoint; every source the body does not build
/// itself is outside:
///
///  * its parameters (a closure's environment and a coroutine's resume argument
///    included), a `Yield`'s resume place, a thread-local's address;
///  * a constant (a `static`'s address included) of carrier type: its pointers are
///    read off an allocation this walk does not read;
///  * a `fn` pointer the body reifies, or any cast or transmute that makes a carrier of
///    a non-carrier (a pointer cast to `*const Waker`), a raw-pointer aggregate
///    (`ptr::from_raw_parts` lowered), a union literal of carrier type, and a carrier
///    read through a union field;
///  * the result of every call EXCEPT a `format_args!` builder handed no outside value
///    ([`is_format_args_builder`]): a callee outside the sysroot, an indirect call or
///    an intrinsic, and any sysroot callee, which may return a value it was handed,
///    read through a pointer it was handed, or keep in a global.
///
/// A value read from an outside local (a field, a deref, a reborrow, a copy) is
/// outside. A write of an outside value through a pointer, and every call that may
/// write one through a pointer it is handed (one handed an outside value, one not a
/// sysroot body, one instantiated at a carrier type), make every EXPOSED carrier local
/// outside: one borrowed mutably, or shared with interior mutability. Inline assembly
/// makes every carrier outside.
struct OutsideValues {
    outside: Vec<bool>,
}

impl OutsideValues {
    fn compute<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        reach: &mut FnPointerReach<'tcx>,
    ) -> Self {
        let carrier: Vec<bool> = body
            .local_decls
            .iter()
            .map(|decl| {
                let ty = reach.normalize(decl.ty);
                reach.carrier(ty)
            })
            .collect();
        let mut exposed = vec![false; carrier.len()];
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(assign) = &statement.kind else { continue };
                let (place, mutable) = match &assign.1 {
                    Rvalue::Ref(_, kind, place) => (place, kind.mutability().is_mut()),
                    Rvalue::RawPtr(kind, place) => (place, kind.to_mutbl_lossy().is_mut()),
                    Rvalue::Reborrow(_, mutability, place) => (place, mutability.is_mut()),
                    _ => continue,
                };
                let local = place.local.as_usize();
                if !carrier[local] {
                    continue;
                }
                let interior_mutable = || {
                    let ty = reach.normalize(place.ty(body, tcx).ty);
                    !ty.is_freeze(tcx, reach.typing_env)
                };
                if mutable || interior_mutable() {
                    exposed[local] = true;
                }
            }
        }
        let mut this = OutsideValues { outside: vec![false; carrier.len()] };
        for local in body.args_iter() {
            this.outside[local.as_usize()] = carrier[local.as_usize()];
        }
        loop {
            let mut changed = false;
            let mut escape = false;
            let mut everything = false;
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    match &statement.kind {
                        StatementKind::Assign(assign) => {
                            if this.rvalue(tcx, body, &assign.1, reach) {
                                changed |= this.write(&assign.0, &carrier, &mut escape);
                            }
                        }
                        StatementKind::Intrinsic(intrinsic) => {
                            if let NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic
                                && this.operand(tcx, body, &copy.src, reach)
                            {
                                escape = true;
                                if let Some(dst) = copy.dst.place() {
                                    changed |= this.mark(dst.local, &carrier);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                match &block.terminator().kind {
                    TerminatorKind::Call { func, args, destination, .. } => {
                        let any_outside =
                            args.iter().any(|arg| this.operand(tcx, body, &arg.node, reach));
                        let callee = func.const_fn_def();
                        let built = !any_outside
                            && callee.is_some_and(|(def, _)| is_format_args_builder(tcx, def));
                        if !built {
                            changed |= this.write(destination, &carrier, &mut escape);
                        }
                        if any_outside || call_may_write_outside(tcx, callee, reach) {
                            escape = true;
                        }
                    }
                    TerminatorKind::TailCall { func, args, .. } => {
                        let any_outside =
                            args.iter().any(|arg| this.operand(tcx, body, &arg.node, reach));
                        if any_outside || call_may_write_outside(tcx, func.const_fn_def(), reach) {
                            escape = true;
                        }
                    }
                    TerminatorKind::Yield { resume_arg, .. } => {
                        changed |= this.write(resume_arg, &carrier, &mut escape);
                    }
                    TerminatorKind::InlineAsm { .. } => everything = true,
                    _ => {}
                }
            }
            if everything {
                for local in 0..carrier.len() {
                    if carrier[local] && !this.outside[local] {
                        this.outside[local] = true;
                        changed = true;
                    }
                }
            }
            if escape {
                for local in 0..carrier.len() {
                    if exposed[local] && !this.outside[local] {
                        this.outside[local] = true;
                        changed = true;
                    }
                }
            }
            if !changed {
                return this;
            }
        }
    }

    /// Mark `local` outside when it is a carrier; whether that changed anything.
    fn mark(&mut self, local: Local, carrier: &[bool]) -> bool {
        let local = local.as_usize();
        if carrier[local] && !self.outside[local] {
            self.outside[local] = true;
            return true;
        }
        false
    }

    /// An outside value is written to `place`: its base local holds it (or, through a
    /// deref, a pointer to memory that does, and the write may land in any exposed
    /// local).
    fn write(&mut self, place: &Place<'_>, carrier: &[bool], escape: &mut bool) -> bool {
        if place.projection.iter().any(|elem| matches!(elem, ProjectionElem::Deref)) {
            *escape = true;
        }
        self.mark(place.local, carrier)
    }

    /// Is the value read at `place` outside: its base local is, or the read goes
    /// through a UNION field into a carrier (a union reinterprets bytes, so the
    /// pointer read may be one no source above ever wrote)?
    fn place<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        place: &Place<'tcx>,
        reach: &mut FnPointerReach<'tcx>,
    ) -> bool {
        if self.outside[place.local.as_usize()] {
            return true;
        }
        let through_union = place.iter_projections().any(|(base, elem)| {
            matches!(elem, ProjectionElem::Field(..))
                && matches!(base.ty(body, tcx).ty.kind(), ty::Adt(adt, _) if adt.is_union())
        });
        through_union && {
            let ty = reach.normalize(place.ty(body, tcx).ty);
            reach.carrier(ty)
        }
    }

    fn operand<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        operand: &Operand<'tcx>,
        reach: &mut FnPointerReach<'tcx>,
    ) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.place(tcx, body, place, reach),
            Operand::Constant(constant) => {
                let ty = reach.normalize(constant.ty());
                reach.carrier(ty)
            }
            // A runtime-checks flag is a `bool`.
            Operand::RuntimeChecks(_) => false,
        }
    }

    fn rvalue<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        rvalue: &Rvalue<'tcx>,
        reach: &mut FnPointerReach<'tcx>,
    ) -> bool {
        match rvalue {
            Rvalue::Use(operand, _)
            | Rvalue::Repeat(operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::WrapUnsafeBinder(operand, _) => self.operand(tcx, body, operand, reach),
            Rvalue::BinaryOp(_, operands) => {
                self.operand(tcx, body, &operands.0, reach)
                    || self.operand(tcx, body, &operands.1, reach)
            }
            // A union literal is outside whenever it is a carrier: a pointer field may
            // later be read over the bytes another field was built from.
            Rvalue::Aggregate(kind, _) if matches!(**kind, AggregateKind::Adt(def, ..) if tcx.adt_def(def).is_union()) => {
                true
            }
            // Trust (2026-10-14, D7 review): a raw-pointer aggregate (the lowered
            // `aggregate_raw_ptr` intrinsic, `ptr::from_raw_parts`) makes a pointer to a
            // carrier from a data pointer that is not one, exactly as a pointer cast
            // does, so it is outside whatever its operands are. Not reachable at the
            // verified -O0 MIR today (the intrinsic is still a call there, and a call
            // result is outside); kept so a pass-order change fails closed.
            Rvalue::Aggregate(kind, _) if matches!(**kind, AggregateKind::RawPtr(..)) => true,
            Rvalue::Aggregate(_, operands) => {
                operands.iter().any(|operand| self.operand(tcx, body, operand, reach))
            }
            Rvalue::Ref(_, _, place)
            | Rvalue::RawPtr(_, place)
            | Rvalue::Reborrow(_, _, place)
            | Rvalue::CopyForDeref(place)
            | Rvalue::Discriminant(place) => self.place(tcx, body, place, reach),
            Rvalue::ThreadLocalRef(_) => true,
            Rvalue::Cast(kind, operand, target) => match kind {
                CastKind::PointerCoercion(
                    PointerCoercion::ReifyFnPointer(_) | PointerCoercion::ClosureFnPointer(_),
                    _,
                )
                | CastKind::Transmute => true,
                _ => {
                    let target = reach.normalize(*target);
                    let source = reach.normalize(operand.ty(body, tcx));
                    let made = reach.carrier(target) && !reach.carrier(source);
                    made || self.operand(tcx, body, operand, reach)
                }
            },
        }
    }
}

/// May a call write an outside carrier value through a pointer it is handed, even
/// when it is handed no outside value ([`OutsideValues`])? Yes unless it is a direct
/// call of a sysroot body (not an intrinsic) at an instantiation that holds no carrier
/// type: a non-sysroot callee may store what it reads from a global, and a sysroot
/// generic at a carrier type (`ptr::write::<Waker>`, `mem::transmute_copy`) may make
/// one of bytes.
fn call_may_write_outside<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: Option<(DefId, ty::GenericArgs<'tcx>)>,
    reach: &mut FnPointerReach<'tcx>,
) -> bool {
    let Some((def_id, fn_args)) = callee else {
        return true;
    };
    if !crate_is_sysroot_credited(tcx, def_id.krate) || tcx.intrinsic(def_id).is_some() {
        return true;
    }
    fn_args.iter().filter_map(|arg| arg.as_type()).any(|ty| {
        let ty = reach.normalize(ty);
        reach.carrier(ty)
    })
}

/// Trust (2026-10-13, CALL-REACH-1 D7; the audited builder list): is `def_id` an
/// inherent associated function of `core::fmt::Arguments` or `core::fmt::rt::Argument`
/// (their lang items `format_arguments` / `format_argument`, in a crate resident in
/// this compiler's own sysroot)? These are the constructors `format_args!` lowers to.
/// JUSTIFICATION: the only `fn` pointer an `rt::Argument` holds is the `formatter`
/// its `new_*` builder reifies from the trait method of the builder's own type
/// argument (`<T as Display>::fmt`, `argument_new!` in `library/core/src/fmt/rt.rs`),
/// inside the builder's body, which this call walk follows at that builder's own call
/// site (`walk_built_dispatch`); `from_usize` stores none. `Arguments::new` and
/// `from_str` store a template and an `&[Argument]` they are handed. So a value one of
/// them returns holds only pointers built under a judged call, or ones in its
/// arguments, and D7 counts it built in the body only when every argument is. Any
/// other inherent method returns no carrier (`as_str`, `estimated_capacity`). An
/// upstream change that adds a builder taking a pointer is caught by D6 (a `fn`
/// pointer type in the argument) or by this rule (a non-builder result is outside).
fn is_format_args_builder(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !crate_is_sysroot_credited(tcx, def_id.krate) || tcx.trait_of_assoc(def_id).is_some() {
        return false;
    }
    let Some(impl_did) = tcx.impl_of_assoc(def_id) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_did).instantiate_identity().skip_normalization();
    let ty::Adt(adt, _) = self_ty.kind() else {
        return false;
    };
    tcx.is_lang_item(adt.did(), LangItem::FormatArguments)
        || tcx.is_lang_item(adt.did(), LangItem::FormatArgument)
}

// ---------------------------------------------------------------------------
// Trust (2026-10-02): the GLOBAL allocator — a different question asked with the
// same walk.

/// Bodies one global-allocator walk may visit before it answers "may reach".
const ALLOCATOR_REACH_MAX_BODIES: usize = 4096;

/// Which allocator seam a global-allocator walk looks for.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum AllocatorSeam {
    /// Any of the four global-allocator shims, or the allocation-error handler:
    /// everything the final link's choice of allocator, or a runtime
    /// allocation-error hook, can stand behind ([`body_global_allocator_reach`]).
    Any,
    /// Only where an allocation can FAIL: the allocating shims (`alloc`,
    /// `alloc_zeroed`, `realloc`) and the allocation-error handler
    /// ([`body_allocation_failure_reach`]). `dealloc` cannot fail, so a body that
    /// only frees never runs the hook.
    AllocationFailure,
}

thread_local! {
    /// Memo of [`body_global_allocator_reach`] and [`body_allocation_failure_reach`]
    /// per (compilation, body, seam). The question is asked several times per
    /// verified body (the publication seam, the registry gate, the zero-obligation
    /// gate); the answer is a function of the body alone.
    static ALLOCATOR_REACH_MEMO: std::cell::RefCell<
        FxHashMap<(u64, rustc_span::def_id::DefId, Option<u32>, AllocatorSeam), DropReach>,
    > = std::cell::RefCell::new(FxHashMap::default());
}

/// Is `def_id` one of `alloc`'s global-allocator shims that `seam` asks about — a
/// foreign item carrying `#[rustc_allocator]`, `#[rustc_reallocator]` or
/// `#[rustc_allocator_zeroed]` (`__rust_alloc`, `__rust_realloc`,
/// `__rust_alloc_zeroed`), and for [`AllocatorSeam::Any`] also `#[rustc_deallocator]`
/// (`__rust_dealloc`)? Decided by the codegen attribute flags rustc lowers those
/// attributes to, never by a rendered name. Which function such a symbol runs is
/// decided by the FINAL LINK: the allocator shim rustc generates into an executable
/// (or a `staticlib`/`cdylib`/dylib) forwards it to std's default handlers
/// (`System`) or to a `#[global_allocator]`'s `GlobalAlloc` impl.
fn is_global_allocator_shim(
    tcx: TyCtxt<'_>,
    def_id: rustc_span::def_id::DefId,
    seam: AllocatorSeam,
) -> bool {
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
    let allocating = CodegenFnAttrFlags::ALLOCATOR
        | CodegenFnAttrFlags::REALLOCATOR
        | CodegenFnAttrFlags::ALLOCATOR_ZEROED;
    let flags = match seam {
        AllocatorSeam::Any => allocating | CodegenFnAttrFlags::DEALLOCATOR,
        AllocatorSeam::AllocationFailure => allocating,
    };
    tcx.is_foreign_item(def_id) && tcx.codegen_fn_attrs(def_id).flags.intersects(flags)
}

/// Trust (2026-10-03): is `def_id` the allocation-error handler entry —
/// `__rust_alloc_error_handler`, the foreign item through which
/// `alloc::alloc::handle_alloc_error` runs whatever handles allocation failure?
/// Recognized as a foreign item of a sysroot crate, flagged
/// `#[rustc_std_internal_symbol]`, whose name is the one the allocator shim is
/// generated under (`global_fn_name(ALLOC_ERROR_HANDLER)`). In a binary that links
/// `std`, the handler is std's `rust_oom`, which calls the hook a crate installed
/// with `std::alloc::set_alloc_error_hook` and aborts only if that hook returns: the
/// hook may PANIC, and the unwind is catchable (`tests/ui/panics/
/// alloc_error_hook-unwind.rs`). A body reaches it without any global-allocator
/// shim when it allocates through a non-global allocator (`Box::new_in(x, System)`
/// calls `System`'s `malloc` directly), so the shims alone do not answer the hook
/// question.
fn is_alloc_error_handler_entry(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    use rustc_ast::expand::allocator::{ALLOC_ERROR_HANDLER, global_fn_name};
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
    tcx.is_foreign_item(def_id)
        && crate_is_sysroot_credited(tcx, def_id.krate)
        && tcx
            .codegen_fn_attrs(def_id)
            .flags
            .contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL)
        && tcx.item_name(def_id).as_str() == global_fn_name(ALLOC_ERROR_HANDLER)
}

/// Can the body under verification reach the GLOBAL allocator, or the
/// allocation-error handler? `Ok(())` when no call it makes, no drop it runs, and no
/// body those reach — sysroot, this crate's own, or a dependency's with encoded MIR —
/// calls a global-allocator shim or reaches the allocation-error handler
/// ([`is_alloc_error_handler_entry`]); `Err(why)` when one does, or when the walk
/// cannot tell (a function pointer, a virtual call, a still-generic callee, a
/// dependency body without encoded MIR or linked dynamically or interposable, inline
/// assembly outside the sysroot, the budget): fail-closed, the caller treats both
/// alike. A sysroot panic entry is not entered ([`is_panic_entry`]).
///
/// The walk is [`walk_body`]'s, with two differences. A body outside the sysroot is
/// walked rather than opening the walk ([`allocator_walk_body`]): a local callee is
/// bundled into its caller's proof, so its allocation is the caller's. And the root
/// is the body as rustc optimized it, possibly generic, so its callees are resolved
/// in its own typing environment and must come out monomorphic.
pub(super) fn body_global_allocator_reach<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> DropReach {
    body_allocator_seam_reach(tcx, body, AllocatorSeam::Any)
}

/// Trust (2026-10-03): can the body under verification reach a point where an
/// allocation FAILS and the allocation-error handler runs — an allocating
/// global-allocator shim (`__rust_alloc`, `__rust_alloc_zeroed`, `__rust_realloc`),
/// or the handler itself? The same walk as [`body_global_allocator_reach`], with
/// `__rust_dealloc` left out: a body that only frees never fails an allocation. Asked
/// when a crate in the graph may install an allocation-error hook
/// (`trust_verify.rs`, `crate_graph_may_install_alloc_error_hook`).
pub(super) fn body_allocation_failure_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> DropReach {
    body_allocator_seam_reach(tcx, body, AllocatorSeam::AllocationFailure)
}

fn body_allocator_seam_reach<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    seam: AllocatorSeam,
) -> DropReach {
    let root = body.source.def_id();
    let key = (
        tcx.stable_crate_id(rustc_span::def_id::LOCAL_CRATE).as_u64(),
        root,
        body.source.promoted.map(|p| p.as_u32()),
        seam,
    );
    if let Some(known) = ALLOCATOR_REACH_MEMO.with(|memo| memo.borrow().get(&key).cloned()) {
        return known;
    }
    // No `alloc` in this compilation's graph (its `global_alloc_ty` lang item is
    // absent): no crate this code links declares the shims or `handle_alloc_error`,
    // so nothing it calls by name can reach one. What a caller hands in through a
    // pointer or a `dyn` is a call this compilation cannot name, which the
    // panic-freedom gates refuse.
    let verdict = if tcx.lang_items().get(LangItem::GlobalAlloc).is_none() {
        Ok(())
    } else {
        root_edges(tcx, body).and_then(|work| walk_to_global_allocator(tcx, work, root, seam))
    };
    if super::env_flag_enabled("TRUST_DROP_GATE_DEBUG") {
        let path = trust_mir_extract::safe_def_path_str(tcx, root);
        match &verdict {
            Ok(()) => eprintln!("[ALLOC_REACH {seam:?}] {path}: reaches no allocator seam"),
            Err(why) => eprintln!("[ALLOC_REACH {seam:?}] {path}: MAY ALLOCATE — {why}"),
        }
    }
    ALLOCATOR_REACH_MEMO.with(|memo| memo.borrow_mut().insert(key, verdict.clone()));
    verdict
}

/// Resolve a callee named in the root body, in the root's typing environment.
/// Only a monomorphic instance is walked.
fn resolve_root_callee<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    def_id: rustc_span::def_id::DefId,
    args: ty::GenericArgs<'tcx>,
) -> Result<Instance<'tcx>, String> {
    match Instance::try_resolve(tcx, typing_env, def_id, args) {
        Ok(Some(callee))
            if !(callee.args.has_non_region_param()
                || callee.args.has_non_region_infer()
                || callee.args.has_non_region_placeholders()) =>
        {
            Ok(callee)
        }
        Ok(Some(_)) => Err(format!(
            "calls `{}` at a still-generic argument",
            trust_mir_extract::safe_def_path_str(tcx, def_id)
        )),
        _ => Err(format!(
            "calls `{}`, which does not resolve",
            trust_mir_extract::safe_def_path_str(tcx, def_id)
        )),
    }
}

/// The root body's drop of `ty`: its glue, when it has one.
fn root_drop<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    work: &mut Vec<Reached<'tcx>>,
) -> DropReach {
    if !ty.needs_drop(tcx, typing_env) {
        return Ok(());
    }
    if ty.has_non_region_param() || ty.has_non_region_infer() || ty.has_non_region_placeholders() {
        return Err(format!("drops a `{ty:?}`, which is still generic"));
    }
    if let Some(glue) =
        drop_glue_instance(tcx, ty, ty::TypingEnv::fully_monomorphized(), ReachMode::SysrootOnly)?
    {
        work.push((glue, None));
    }
    Ok(())
}

/// The fn item type behind `func` when `func` is a fn pointer this body REIFIED
/// from a named item and never let anything reseat: a whole local, assigned exactly
/// once in the body, by a `ReifyFnPointer` cast of a constant fn item, never
/// borrowed or address-taken, and never a call's destination. The same shape
/// `indirect_callee_is_a_reified_constant` admits for the indirect-call gate (that
/// gate also asks who verifies the target, which this walk does not need: it walks
/// the target). `None` for anything else, which leaves the call unnamed.
fn reified_constant_target<'tcx>(body: &Body<'tcx>, func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    use rustc_middle::mir::CastKind;
    let (Operand::Copy(place) | Operand::Move(place)) = func else { return None };
    if !place.projection.is_empty() {
        return None;
    }
    let local = place.local;
    let mut target = None;
    let mut assignments = 0usize;
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else { continue };
            let (dest, rvalue) = &**assign;
            if let Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) = rvalue
                && borrowed.local == local
            {
                return None;
            }
            if dest.local != local {
                continue;
            }
            if !dest.projection.is_empty() {
                return None;
            }
            assignments += 1;
            target = match rvalue {
                Rvalue::Cast(
                    CastKind::PointerCoercion(
                        ty::adjustment::PointerCoercion::ReifyFnPointer(..),
                        _,
                    ),
                    Operand::Constant(constant),
                    _,
                ) if matches!(constant.const_.ty().kind(), ty::FnDef(..)) => {
                    Some(constant.const_.ty())
                }
                _ => None,
            };
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator().kind
            && destination.local == local
        {
            return None;
        }
    }
    if assignments == 1 { target } else { None }
}

/// What the root body calls and drops, as the walk's first work list.
fn root_edges<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Result<Vec<Reached<'tcx>>, String> {
    let root = body.source.def_id();
    let typing_env = ty::TypingEnv::post_analysis(tcx, root);
    let normalize =
        |ty: Ty<'tcx>| tcx.normalize_erasing_regions(typing_env, ty::Unnormalized::new_wip(ty));
    // The root at its own identity arguments: what `local_key_receiver` reads a
    // constant key through (a no-op instantiation).
    let root_instance = Instance::new_raw(root, ty::GenericArgs::identity_for_item(tcx, root));
    let mut work: Vec<Reached<'tcx>> = Vec::new();
    for block in body.basic_blocks.iter() {
        match &block.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let callee_ty = normalize(func.ty(body, tcx));
                // A fn pointer this body reified from a named item itself is a
                // call to that item.
                let named = match *callee_ty.kind() {
                    ty::FnPtr(..) => reified_constant_target(body, func).map(&normalize),
                    _ => Some(callee_ty),
                };
                let Some(&ty::FnDef(def_id, fn_args)) = named.as_ref().map(|ty| ty.kind()) else {
                    return Err(format!(
                        "calls a `{callee_ty:?}`, whose target this walk cannot name"
                    ));
                };
                if tcx.is_lang_item(def_id, LangItem::DropGlue) {
                    root_drop(tcx, typing_env, fn_args.skip_binder().type_at(0), &mut work)?;
                    continue;
                }
                let callee = resolve_root_callee(tcx, typing_env, def_id, fn_args.skip_binder())?;
                if let InstanceKind::Intrinsic(_) = callee.def {
                    for arg in args.iter() {
                        let arg_ty = normalize(arg.node.ty(body, tcx));
                        match *arg_ty.kind() {
                            ty::FnDef(arg_def, arg_args) => {
                                work.push((
                                    resolve_root_callee(
                                        tcx,
                                        typing_env,
                                        arg_def,
                                        arg_args.skip_binder(),
                                    )?,
                                    None,
                                ));
                            }
                            ty::FnPtr(..) | ty::Closure(..) => {
                                return Err(format!(
                                    "hands a `{arg_ty:?}` to the intrinsic `{}`",
                                    trust_mir_extract::safe_def_path_str(tcx, def_id)
                                ));
                            }
                            _ => {}
                        }
                    }
                    continue;
                }
                let callee_key = match (callee.def, args.first()) {
                    (InstanceKind::Item(callee_def), Some(receiver))
                        if def_is_local_key_inherent_method(tcx, callee_def) =>
                    {
                        local_key_receiver(tcx, root_instance, body, &receiver.node, None)
                    }
                    _ => None,
                };
                work.push((callee, callee_key));
            }
            TerminatorKind::Drop { place, .. } => {
                root_drop(tcx, typing_env, normalize(place.ty(body, tcx).ty), &mut work)?;
            }
            // The root is this crate's body: what an `asm!` template calls is not
            // visible, as for any body outside the sysroot (`allocator_walk_body`).
            TerminatorKind::InlineAsm { .. } => {
                return Err("holds inline assembly".to_string());
            }
            _ => {}
        }
    }
    Ok(work)
}

/// Does `def_id` BEGIN A PANIC — one of the sysroot's `fn` lang items that start
/// a panic (`panic`, `panic_fmt`, `panic_display`, `panic_bounds_check`, the
/// `panic_const_*` family, …, and std's `begin_panic`)? Such a call never returns.
/// If it is reachable the body is not panic-free whatever the panic machinery then
/// runs, and if it is not, nothing behind it runs; so the global-allocator walk
/// does not enter it. Identified by the compiler's lang-item table, never by a name
/// the crate chose.
fn is_panic_entry(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    crate_is_sysroot_credited(tcx, def_id.krate)
        && tcx.as_lang_item(def_id).is_some_and(|item| {
            matches!(item.target(), rustc_attr_ir::target::Target::Fn)
                && (item == LangItem::BeginPanic
                    || item == LangItem::ConstPanicFmt
                    || item.name().as_str().starts_with("panic"))
        })
}

/// A body outside the sysroot that holds inline assembly: the global-allocator
/// walk cannot see what an `asm!` template calls.
fn non_sysroot_body_holds_asm(body: &Body<'_>) -> bool {
    body.basic_blocks
        .iter()
        .any(|block| matches!(block.terminator().kind, TerminatorKind::InlineAsm { .. }))
}

/// The MIR a reached instance runs, for the global-allocator walk. Unlike the
/// destructor walk it also walks a body of THIS crate (a local callee is bundled
/// into its caller's proof, so its allocation is the caller's) and a dependency's
/// body whose encoded MIR is the code that runs (the P-MIR premise the bundling
/// lanes already rest on, `foreign_rederivation.rs`: MIR available, statically
/// linked, no interposable symbol). Everything else is [`body_to_walk`]'s answer.
fn allocator_walk_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    root: rustc_span::def_id::DefId,
) -> Result<Option<&'tcx Body<'tcx>>, String> {
    let InstanceKind::Item(def_id) = instance.def else {
        return body_to_walk(tcx, instance, ReachMode::SysrootOnly);
    };
    if is_panic_entry(tcx, def_id) {
        return Ok(None);
    }
    if crate_is_sysroot_credited(tcx, def_id.krate) {
        return body_to_walk(tcx, instance, ReachMode::SysrootOnly);
    }
    let path = || trust_mir_extract::safe_def_path_str(tcx, def_id);
    if tcx.is_foreign_item(def_id) {
        return Err(format!("calls `{}`, a foreign function outside the sysroot", path()));
    }
    if matches!(tcx.def_kind(def_id), DefKind::Ctor(..)) {
        return Ok(None);
    }
    let body = if let Some(local) = def_id.as_local() {
        // The body under verification calls itself: its calls are the root's,
        // already in the walk.
        if def_id == root {
            return Ok(None);
        }
        if super::optimized_mir_query_would_cycle(tcx, def_id) {
            // A member of a call cycle with a body on the stack: its elaborated-MIR
            // snapshot, the one the bundle reads for the same callee.
            match tcx.mir_for_trust_verification(local) {
                Some(body) => body,
                None => {
                    return Err(format!("calls `{}`, whose MIR is not readable here", path()));
                }
            }
        } else if tcx.is_mir_available(def_id) {
            tcx.optimized_mir(def_id)
        } else {
            return Err(format!("calls `{}`, whose MIR is not available", path()));
        }
    } else {
        if !tcx.is_mir_available(def_id) {
            return Err(format!("calls `{}`, a dependency body with no encoded MIR", path()));
        }
        if super::foreign_rederivation::crate_reaches_process_dynamically(tcx, def_id.krate) {
            return Err(format!("calls `{}`, in a dependency that may link dynamically", path()));
        }
        if tcx.codegen_fn_attrs(def_id).contains_extern_indicator() {
            return Err(format!("calls `{}`, an interposable symbol", path()));
        }
        tcx.optimized_mir(def_id)
    };
    if non_sysroot_body_holds_asm(body) {
        return Err(format!("calls `{}`, which holds inline assembly", path()));
    }
    Ok(Some(body))
}

fn walk_to_global_allocator<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut work: Vec<Reached<'tcx>>,
    root: rustc_span::def_id::DefId,
    seam: AllocatorSeam,
) -> DropReach {
    let mut visited: FxHashSet<Reached<'tcx>> = FxHashSet::default();
    while let Some(reached) = work.pop() {
        if !visited.insert(reached) {
            continue;
        }
        if visited.len() > ALLOCATOR_REACH_MAX_BODIES {
            return Err(format!("reaches more than {ALLOCATOR_REACH_MAX_BODIES} bodies (budget)"));
        }
        if let InstanceKind::Item(def_id) = reached.0.def {
            if is_global_allocator_shim(tcx, def_id, seam) {
                return Err(format!(
                    "calls the global allocator (`{}`)",
                    trust_mir_extract::safe_def_path_str(tcx, def_id)
                ));
            }
            if is_alloc_error_handler_entry(tcx, def_id) {
                return Err(format!(
                    "reaches the allocation-error handler (`{}`)",
                    trust_mir_extract::safe_def_path_str(tcx, def_id)
                ));
            }
        }
        let Some(body) = allocator_walk_body(tcx, reached.0, root)? else {
            continue;
        };
        walk_body(
            tcx,
            reached,
            body,
            &mut work,
            ReachMode::SysrootOnly,
            ty::TypingEnv::fully_monomorphized(),
            None,
        )?;
    }
    Ok(())
}
