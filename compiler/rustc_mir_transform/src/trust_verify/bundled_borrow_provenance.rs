//! Trust (D5-C, 2026-09-24): one borrow-provenance attestation per lowered
//! bundle function, keyed by the `def_path` the bridge reads, and recorded where
//! the body was admitted, including for members of the monomorphic FOREIGN drain
//! (the B-lane).
//!
//! ## The miss this closes
//!
//! ```text
//! pub fn rem_ref(x: &u32) -> u32 { x % 2 }
//! pub fn first_even(v: &[u32]) -> Option<u32> { v.iter().copied().find(|x| x % 2 == 0) }
//! ```
//!
//! `x % 2` on a `&u32` calls `<&u32 as Rem<u32>>::rem`, which the B-lane bundles
//! under its per-instance name. That body loads `*self` through its reference
//! parameter. The bridge stamps `ProofAnnotation::ValidBorrow` on such a load
//! only when `func.def_path` is in the compiler's borrow-provenance-clean set, and
//! trust-mc's direct-call summary models a `Load` only when it carries that stamp.
//!
//! The set was filled by re-walking `bundled_def_ids`, and the B-lane never puts
//! its members there (it records `bundled_mono_defs` instead). So a B-lane member
//! was never classified at all, and its load was never stamped. The summary then
//! declined (`unmodeled_instruction/Load`, measured with the call-summary census
//! on the snapshot's native-bundle dump) and the caller's aggregate panic-freedom
//! row read `runtime-checked` (`UnsupportedDirectCallSummary`). This was a
//! membership miss. It was also a key mismatch waiting to happen: the re-walk
//! would have rendered the generic `DefId` (`safe_def_path_str`), while the bridge
//! looks up the per-instance `bundled_name`. `ADMITTED_DESTRUCTOR_ADTS` learned the
//! same lesson ("deriving this by re-walking `bundled_def_ids` did NOT work").
//!
//! ## The key
//!
//! [`BorrowProvenanceLedger::record`] and
//! [`BorrowProvenanceLedger::record_mono_member`] are called with the `def_path` of
//! the `VerifiableFunction` that is pushed into the bundle, which is the string the
//! bridge's `clean.contains(&func.def_path)` reads. The verdict is computed on the
//! exact MIR body that `VerifiableFunction` was extracted from (for the B-lane, the
//! instantiated `mono_body`). No second rendering and no re-derived body is
//! involved. A `def_path` recorded more than once is clean only if EVERY body
//! recorded under it is clean (AND-composition), so a name collision can only
//! withhold the stamp.
//!
//! ## Soundness: this WIDENS acceptance, and the three conjuncts that bound it
//!
//! Before this, no B-lane member ever carried `ValidBorrow`. Now a B-lane member
//! carries it iff all of the following hold:
//!
//! 1. `trust_mir_extract::function_is_borrow_provenance_clean` on its instantiated
//!    body. This is the same classifier the root and the `DefId`-lane members
//!    already use: no deref of a raw pointer, no read through a union field, no
//!    unrecognized projection, and no cast to a reference other than a pointer
//!    coercion.
//! 2. [`mono_member_has_no_unsafe_reference_source`] on the same body. This is
//!    stricter than the local lane: no `Transmute` cast to ANY type, no
//!    `copy_nonoverlapping` statement, no inline asm, and every call a direct call
//!    of a constant `FnDef` naming a non-foreign item whose instantiated
//!    signature is `Safety::Safe`. That also refuses every target-feature fn,
//!    whose signature is `Unsafe`, and every call through a `fn` pointer.
//! 3. NO BODY THAT FAILS (1) OR (2), AND NO BODY THE LEDGER DID NOT ATTEST, REACHES
//!    THE MEMBER in the lowered module. Recorded by
//!    [`BorrowProvenanceLedger::record_mono_member`],
//!    [`BorrowProvenanceLedger::note_foreign_body`] and
//!    [`BorrowProvenanceLedger::note_local_body`], and applied to the final module
//!    by [`ReachScope::strip_unattested_reach`]. Until 2026-09-27 this was a
//!    bundle-wide screen: ANY failing foreign body withheld EVERY B-lane stamp.
//!    [`ReachScope`] says why that asked a coarser question than its own argument.
//!
//! Why (2): the classifier trusts a reference that arrives by call return. For a
//! LOCAL body, a reference obtained from an `unsafe fn` is paired with that call's
//! own unsafe-call row, which vcgen charges in this compilation. A foreign
//! member's calls are charged by nobody. Likewise a `Transmute` into a type that
//! merely CONTAINS a reference (`Option<&T>`) passes the classifier's `ty.is_ref()`
//! cast check. D8-P0's `[unsafe:validity-transmute]` row covers that for local
//! code, but it is minted only for bodies vcgen sees.
//!
//! Why (3), which was MEASURED as a false accept before it was added. (1) and (2)
//! judge one body, but a member's reference PARAMETER is produced by its caller.
//! Take a dependency `pass_transmuted(a)` that does
//! `load_ref(transmute::<usize, &u32>(a))`, where `load_ref(x: &u32) = *x`. It is
//! refused by (1), but it contains no `Load` of its own. `load_ref` passes (1) and
//! (2). With only a per-function stamp, `load_ref`'s load would be stamped, and
//! trust-mc's NESTED call summary (`translate_chc.rs`, "A call to a DIFFERENT
//! function whose body this module already holds") would summarize the whole
//! chain. The caller would then verify a load from address `a`. This was measured
//! on the snapshot's dump: with only `load_ref`'s `Load` stamped, `call-summary-
//! census` reports BOTH call sites `summarized`. A LOCAL fabricator does not need
//! (3): it is verified as its own root in the same compilation, where the
//! transmute row refuses it.
//!
//! Since D4-A (2026-09-24) that exact chain no longer reaches this ledger: a
//! non-sysroot foreign member whose source carries user `unsafe` is not bundled at
//! all (`foreign-member-user-unsafe-source`), so `pass_transmuted` is an absent
//! callee and the `xchain` revision is refused before (3) is asked. Measured
//! 2026-09-27 with `TRUST_BORROW_CLEAN_TRACE`: the `xchain` and `xtransmuted`
//! revisions record the root alone. So a bundled body that fails (1) or (2) is
//! today a SYSROOT body (the `RawVec`/`Vec` internals `collect` pulls in), or a
//! non-sysroot one that fails (2) through a `fn`-pointer or `dyn` call in safe
//! code. (3) stays, because it is what holds if either of those ever hands a
//! member a reference trust-mc composes; its reach-scoped form is pinned by the
//! unit tests, since no UI fixture can reach a B-lane fabricator any more.
//!
//! What is left, when all three hold, is where a dereferenced reference in a
//! stamped member can come from:
//!
//! * A PARAMETER. The member's callers are the root or a local member, both
//!   verified in this compilation, or a foreign body that itself passed (1) and
//!   (2). By induction over the bundle, the reference comes from one of the
//!   sources below, or from the root's own parameters. That last case is the
//!   "Parameter validity" premise already in `docs/TCB.md`.
//! * A BORROW of a place. The classifier checked every projection on the way to
//!   that place.
//! * A reference LOADED FROM MEMORY through such a reference. This is the
//!   type-system invariant the local lane already trusts.
//! * The return of a SAFE call to something outside the bundle. This is the
//!   callee's safe-API soundness contract. For the sysroot it is the same premise
//!   the `Box::new` root and D8 rest on. For a declared dependency it is the
//!   "dependency-soundness premise" of the TCB's Parameter-validity row. The
//!   premise is not new; it now also applies inside member bodies, and not only
//!   in the root.
//!
//! What the stamp suppresses is the load/store `MemoryAccessWithoutPreciseModel`
//! obligation, and nothing else. The loaded VALUE stays a fresh unconstrained
//! symbol in trust-mc (`translate_chc.rs`, the `ValidBorrow` load arms). Every
//! other obligation of the member body, including its `Assert`s
//! (`ensure_bundled_member_asserts_exactly_charged`), is unchanged. The
//! native gate still admits the stamp only on a `Load`/`Store` of a
//! source-generation-authorized bundle.

use rustc_middle::mir::{CastKind, NonDivergingIntrinsic};

use super::*;

/// Borrow-provenance verdicts for the functions of ONE native bundle, keyed by
/// the exact `VerifiableFunction::def_path` the bridge looks up.
#[derive(Default)]
pub(super) struct BorrowProvenanceLedger {
    by_def_path: FxHashMap<String, bool>,
    /// `def_path`s recorded by the B-lane. Their stamp additionally needs
    /// conjunct (3): see [`ReachScope`].
    mono_members: FxHashSet<String>,
    /// `def_path`s of LOCAL bodies (the root and local `DefId`-lane members),
    /// verified in this compilation. Conjunct (3) attests them as callers.
    local_bodies: FxHashSet<String>,
    /// The foreign-member-rule verdict of every FOREIGN body, AND-composed per
    /// `def_path` like `by_def_path`. Conjunct (3) attests a foreign caller only if
    /// every body recorded under its `def_path` passed.
    foreign_member_rule: FxHashMap<String, bool>,
}

impl BorrowProvenanceLedger {
    /// Record the verdict for one body lowered under `def_path` (the root, a
    /// `DefId`-lane member, or an unclassified body recorded `false`). `lane` is
    /// used only for the `TRUST_BORROW_CLEAN_TRACE` diagnostic, which reads no
    /// proof state and changes no verdict.
    pub(super) fn record(&mut self, def_path: &str, lane: &'static str, clean: bool) {
        if std::env::var_os("TRUST_BORROW_CLEAN_TRACE").is_some() {
            eprintln!("[BORROW_CLEAN] lane={lane} clean={clean} def_path={def_path}");
        }
        self.by_def_path
            .entry(def_path.to_owned())
            .and_modify(|known| *known &= clean)
            .or_insert(clean);
    }

    /// Record a B-lane member. `admits` is [`mono_member_admits_valid_borrow`] on
    /// its instantiated body. A member that fails it also seeds conjunct (3) for
    /// every B-lane member it reaches in the lowered module.
    pub(super) fn record_mono_member(&mut self, def_path: &str, admits: bool) {
        self.record(def_path, "mono-member", admits);
        self.mono_members.insert(def_path.to_owned());
        self.note_foreign_member_rule(def_path, admits);
    }

    /// A LOCAL body (the root, or a local `DefId`-lane member). It is verified as
    /// its own root in this compilation, so it never seeds scoped conjunct 3.
    pub(super) fn note_local_body(&mut self, def_path: &str) {
        self.local_bodies.insert(def_path.to_owned());
    }

    fn note_foreign_member_rule(&mut self, def_path: &str, admits: bool) {
        self.foreign_member_rule
            .entry(def_path.to_owned())
            .and_modify(|known| *known &= admits)
            .or_insert(admits);
    }

    /// Conjunct (3) for a FOREIGN body that is not a B-lane member (a foreign
    /// `DefId`-lane member, or the unclassified comparator sub-lane). It does not
    /// change that body's own stamp; it only decides whether that body may call a
    /// stamped B-lane member.
    pub(super) fn note_foreign_body(&mut self, def_path: &str, admits: bool) {
        self.note_foreign_member_rule(def_path, admits);
        if !admits && std::env::var_os("TRUST_BORROW_CLEAN_TRACE").is_some() {
            eprintln!("[BORROW_CLEAN] foreign body fails the member rule: {def_path}");
        }
    }
}

impl BorrowProvenanceLedger {
    /// The set handed to the bridge — every `def_path` whose EVERY recorded body is
    /// clean under (1) and (2); a path recorded unclean anywhere is absent
    /// (fail-closed) — plus the [`ReachScope`] that applies conjunct (3) to the
    /// lowered module.
    // The results are sets, so the maps' iteration order cannot reach them.
    #[allow(rustc::potential_query_instability)]
    pub(super) fn into_clean_set_and_reach_scope(self) -> (FxHashSet<String>, ReachScope) {
        let Self { by_def_path, mono_members, local_bodies, foreign_member_rule } = self;
        let clean =
            by_def_path.into_iter().filter(|(_, clean)| *clean).map(|(path, _)| path).collect();
        // Positively attested only. A `def_path` the ledger never recorded, or
        // recorded failing the member rule anywhere, is NOT attested and seeds.
        let mut attested_callers: FxHashSet<String> = foreign_member_rule
            .iter()
            .filter(|(_, admits)| **admits)
            .map(|(path, _)| path.clone())
            .collect();
        for path in local_bodies {
            if foreign_member_rule.get(&path) != Some(&false) {
                attested_callers.insert(path);
            }
        }
        (clean, ReachScope { mono_members, attested_callers })
    }
}

/// Conjunct (3), asked on the LOWERED module instead of on the bundle
/// (2026-09-27; it replaced the bundle-wide screen after an adversarial review).
///
/// ## Why the bundle-wide form is coarser than its own argument
///
/// Conjunct 3 exists for ONE channel: "a member's reference PARAMETER is
/// produced by its caller" (`xchain`: `pass_transmuted` fabricates, `load_ref`
/// loads). trust-mc composes bodies only along the module's own function
/// references, so a fabricating body can put a reference into a member's
/// parameter, as trust-mc sees it, only if the member is reachable from that
/// body. The bundle-wide form also withholds every stamp when the unclean body
/// cannot reach the member at all. Measured on the idiomatic sample's `i04`
/// (`v.iter().copied().filter(|x| x % 2 == 0).collect()`): `collect` pulls
/// `RawVec`/`Vec` allocation bodies into the bundle, they fail the member rule,
/// and `<&u32 as Rem<u32>>::rem`, reached only through the local closure, loses
/// its stamp. `rem`'s summary then declines (`unmodeled_instruction/Load`), and
/// `evens` stays runtime-checked.
///
/// ## The rule
///
/// SEEDS are the module functions whose `def_path` is NOT positively attested:
/// every body except the local ones and the foreign ones that passed the member
/// rule wherever they were recorded. A body the ledger never saw is a seed. The
/// TAINT is everything a seed reaches through any function reference: `Call`,
/// `Invoke`, `SeqMap`'s element function, a `FnDef` constant, or any future
/// instruction whose `Debug` spelling names a `FuncId`. One `CallIndirect` in the
/// tainted region taints every member. A B-lane member in the taint has every
/// `ValidBorrow` removed, which is exactly its unstamped lowering (the stamp is the
/// only thing the clean set controls). Anything unexpected in the module's shape
/// strips every member, which is the bundle-wide behaviour.
///
/// ## The cross-repo coupling this rests on (adversarial review, 2026-09-27)
///
/// The taint must contain every edge along which trust-mc COMPOSES bodies. Today
/// that is `Inst::Call` alone: the nested call summary resolves its callee by
/// `function_by_id`, while `CallIndirect`, `Invoke`, `SeqMap` and a by-name
/// `SymbolAddr` slot are not composed (fresh symbols or declines in
/// `translate_chc.rs`). The taint follows `Call`, `Invoke`, `SeqMap`, `FnDef`
/// constants and any `FuncId(n)` in an instruction's `Debug` text, and treats
/// `CallIndirect` as reaching everything, so it is a superset. If trust-mc starts
/// composing through a new edge that names no `FuncId` (a by-name slot), this
/// pass must learn it FIRST. Two further invariants, both held by construction
/// and neither re-checked here: the bridge lowers `current` in order
/// (`FuncId::new(index)`, then `add_function`), and every LOCAL member's unsafe
/// operations are charged in its own verification (the premise the local lane
/// already stands on).
///
/// ## What a stamped member's reference can still come from
///
/// The sources the ledger's module doc lists, each carried by a premise that the
/// ROOT lane already stands on: a borrow (checked), a load through a valid
/// reference (the type invariant), the return of a safe call (the safe-API
/// contract; the root lane stamps a load of such a return today), or a parameter
/// whose every caller in the module is attested. A body that is not in the module
/// is not composed by trust-mc at all. Its call sites lower through the
/// absent-callee arm (a may-panic `Assert(false)` unless the compiler classified
/// the callee total) or through a std-anchored modeled edge (the `collect` closure
/// arm, the total-iterator arms), which is the sysroot premise.
pub(super) struct ReachScope {
    mono_members: FxHashSet<String>,
    attested_callers: FxHashSet<String>,
}

impl ReachScope {
    /// Strip `ValidBorrow` from every B-lane member of `module` reachable from an
    /// unattested body. `def_paths[i]` must be the `def_path` of the function
    /// `module` lowered at index `i` (`FuncId == index`), which is what the bundle
    /// builder keeps in `current`. Returns how many member functions lost a stamp.
    ///
    /// Trust (C1, 2026-11-06): it also withdraws every source reference claim
    /// (`trust_ir_bridge::LoweredSourceReferenceSites`) of each member it
    /// withholds, `sites` being the side table of the lowering that produced
    /// `module`. Conjunct (3) says such a member's reference parameter may come
    /// from an unattested body, so neither its loads nor its parameters may be
    /// claimed initialized. There is no variant without the table: a strip that
    /// left the claims in place would be the unsound one.
    pub(super) fn strip_unattested_reach(
        &self,
        module: &mut trust_ir::Module,
        def_paths: &[&str],
        sites: &mut trust_ir_bridge::LoweredSourceReferenceSites,
    ) -> usize {
        let is_member =
            |index: usize| def_paths.get(index).is_some_and(|p| self.mono_members.contains(*p));
        let shape_is_exact = module.functions.len() == def_paths.len()
            && module.functions.iter().enumerate().all(|(index, f)| f.id.index() as usize == index);
        let reached = if shape_is_exact {
            reachable_from_unattested(module, def_paths, &self.attested_callers)
        } else {
            None
        };
        let mut stripped = 0;
        for index in 0..module.functions.len() {
            let tainted = match &reached {
                Some(reached) => reached[index],
                // Shape mismatch or an indirect call in the taint: every member.
                None => true,
            };
            if tainted && is_member(index) {
                sites.withdraw_function(index);
                let mut removed_any = false;
                for block in &mut module.functions[index].blocks {
                    for node in &mut block.body {
                        let before = node.proofs.len();
                        node.proofs.retain(|proof| {
                            !matches!(proof, trust_ir::ProofAnnotation::ValidBorrow)
                        });
                        removed_any |= node.proofs.len() != before;
                    }
                }
                if removed_any {
                    stripped += 1;
                }
                if std::env::var_os("TRUST_BORROW_CLEAN_TRACE").is_some() {
                    eprintln!(
                        "[BORROW_CLEAN] scoped conjunct 3 withholds: {}",
                        def_paths.get(index).copied().unwrap_or("<unmapped>")
                    );
                }
            }
        }
        stripped
    }
}

/// `Some(reached)` with `reached[i]` = function `i` is reachable from a seed
/// (itself included), or `None` when the taint contains a `CallIndirect` or a
/// reference to a function outside the module, which reaches everything.
fn reachable_from_unattested(
    module: &trust_ir::Module,
    def_paths: &[&str],
    attested_callers: &FxHashSet<String>,
) -> Option<Vec<bool>> {
    let count = module.functions.len();
    let mut reached = vec![false; count];
    let mut stack = Vec::new();
    // A `def_path` that names more than one module function cannot say WHICH body
    // the ledger attested, so none of them is attested (adversarial review C2).
    let mut occurrences: FxHashMap<&str, usize> = FxHashMap::default();
    for def_path in def_paths {
        *occurrences.entry(*def_path).or_insert(0) += 1;
    }
    for (index, def_path) in def_paths.iter().enumerate() {
        if !attested_callers.contains(*def_path) || occurrences[def_path] > 1 {
            reached[index] = true;
            stack.push(index);
        }
    }
    while let Some(index) = stack.pop() {
        for block in &module.functions[index].blocks {
            for node in &block.body {
                if matches!(node.inst, trust_ir::Inst::CallIndirect { .. }) {
                    return None;
                }
                for target in referenced_functions(&node.inst) {
                    if target >= count {
                        return None;
                    }
                    if !reached[target] {
                        reached[target] = true;
                        stack.push(target);
                    }
                }
            }
        }
    }
    Some(reached)
}

/// Every function index `inst` names. The explicit arms are the variants that
/// carry a `FuncId` today; the `Debug` scan is the backstop for a variant or a
/// nested constant (`Constant::FnDef`) added later, and relies on
/// `FuncId`'s pinned `Debug` form `FuncId(<n>)` (trust-ir `value.rs` tests it).
/// Over-reporting only strips more stamps.
fn referenced_functions(inst: &trust_ir::Inst) -> Vec<usize> {
    let mut targets = Vec::new();
    match inst {
        trust_ir::Inst::Call { callee, .. } | trust_ir::Inst::Invoke { callee, .. } => {
            targets.push(callee.index() as usize)
        }
        trust_ir::Inst::SeqMap { fwd, .. } => targets.push(fwd.index() as usize),
        _ => {}
    }
    let spelled = format!("{inst:?}");
    let mut rest = spelled.as_str();
    while let Some(at) = rest.find("FuncId(") {
        rest = &rest[at + "FuncId(".len()..];
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        if let Ok(index) = digits.parse::<usize>() {
            targets.push(index);
        }
    }
    targets
}

/// Conjuncts (1) and (2) for one foreign body: may the bridge stamp `ValidBorrow`
/// inside a B-lane member whose instantiated body is `mono_body`, as far as that
/// body alone can tell? Conjunct (3) is the ledger's.
pub(super) fn mono_member_admits_valid_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    mono_body: &Body<'tcx>,
) -> bool {
    trust_mir_extract::function_is_borrow_provenance_clean(tcx, mono_body)
        && mono_member_has_no_unsafe_reference_source(tcx, mono_body)
}

/// The foreign-member conjunct: `body` contains no operation whose validity
/// obligation would be the member's own (uncharged) unsafe code. It rounds toward
/// NO: anything it does not recognize as a safe direct call is refused.
fn mono_member_has_no_unsafe_reference_source<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign)
                    if matches!(assign.1, Rvalue::Cast(CastKind::Transmute, ..)) =>
                {
                    return false;
                }
                StatementKind::Intrinsic(intrinsic)
                    if matches!(**intrinsic, NonDivergingIntrinsic::CopyNonOverlapping(_)) =>
                {
                    return false;
                }
                _ => {}
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => {
                if !callee_is_safe_non_foreign_fn_item(tcx, func) {
                    return false;
                }
            }
            TerminatorKind::InlineAsm { .. } => return false,
            _ => {}
        }
    }
    true
}

/// A direct call of a constant `FnDef` operand naming a non-foreign item whose
/// instantiated signature is `Safety::Safe`. A call through a `fn` pointer (or
/// any operand that is not a constant `FnDef`) answers `false`.
fn callee_is_safe_non_foreign_fn_item<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Some((def_id, args)) = func.const_fn_def() else {
        return false;
    };
    !tcx.is_foreign_item(def_id)
        && tcx.fn_sig(def_id).instantiate(tcx, args).skip_binder().safety().is_safe()
}

#[cfg(test)]
mod tests;
