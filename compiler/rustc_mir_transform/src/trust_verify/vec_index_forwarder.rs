//! Trust (VEC-AS-SLICE, 2026-09-25): std's `Vec` SCALAR index forwards its
//! member bounds `Assert` to the caller-side owned-`Vec` index row.
//!
//! ## The over-refusal this closes
//!
//! `v[i]` on a `Vec<T>` is the call `<Vec<T> as Index<usize>>::index(&v, i)`
//! (`index_mut` for a write). Its body is one forward — `Index::index(&**self,
//! index)`, whose `<[T] as Index>::index` is `#[inline(always)]` — so the bundled
//! body `F` calls `<usize as SliceIndex<[T]>>::index(index, slice)` (`M`), and `M`
//! carries the bounds `Assert(index < slice.len())`. The bridge admits `M` into its
//! derived-requires lane (`index < slice__slice_len`), but `M`'s ONLY call site sits
//! in `F`, a FOREIGN member with no own root run, so
//! `ensure_bundled_member_asserts_exactly_charged` refused every bundle that
//! indexed a `Vec`: "refused Assert-bearing transitive member … the site(s) in
//! `<alloc::vec::Vec<T> as Index<usize>>::index` are not owned". Even `if i <
//! v.len() { v[i] }` was refused (measured on `0.10.0+g3b30328c0`).
//!
//! ## Where the demand already lives
//!
//! The caller's OWN vcgen already charges `v[i]` at the call: the `#7c` owned-`Vec`
//! scalar-index producer (`trust_vcgen`'s `slice_method_panic_body`, `RangeIndex`
//! arm) emits `SliceBoundsCheck` with the violation `i >= coll_len(v)` over the
//! container's abstract length — the symbol `v.len()`, `v.is_empty()` and the
//! resize-stability gates tie — or, when that length is not recoverable, the
//! never-provable `UnsupportedMir { container-index-unstable-len }` row. That row
//! is the demand; what was missing is the COMPOSITION claim that it is where
//! `M`'s `Assert`, reached through `F`, is demanded.
//!
//! ## The rule
//!
//! A call site of `M` inside a bundled member `F` is OWNED BY FORWARDING when:
//!
//! 1. `F` is std's `<Vec<T, A> as Index<usize>>::index` or `<Vec<T, A> as
//!    IndexMut<usize>>::index_mut` — decided on the RESOLVED instance: the impl
//!    method's trait is the `Index`/`IndexMut` LANG ITEM, the impl's self type is
//!    an ADT carrying the `Vec` DIAGNOSTIC ITEM, both defs are artifact-resident
//!    sysroot defs (`def_is_in_real_sysroot_crate`), and the index type argument is
//!    exactly `usize`. Never a rendered name. Composed fail-closed across admitting
//!    paths.
//! 2. `F`'s extracted body has exactly two formals and exactly one call site to
//!    `M`, whose FIRST argument is `F`'s index formal `_2`, unmodified — the index
//!    `M` bounds-checks is the index the caller passed.
//! 3. `M`'s derived charge is exactly the single bounds requires
//!    `m0 < m1__slice_len` over its two formals: the `Assert` compares the forwarded
//!    index against the length of the forwarded slice.
//! 4. EVERY call site of `F` in the bundle is charged: a ROOT site by the owned-
//!    `Vec` index row regenerated from the root's own MIR
//!    (`trust_vcgen::owned_vec_scalar_index_row`) and matched, as a multiset, by
//!    kind, location, function and recorded obligation body in the root's public
//!    inventory; a site in another bundled member by that member's own accepted
//!    root run, exactly as `member_assert_ownership` credits a direct charge (the
//!    root records its `F` charges for that purpose, `SliceBoundsCheck` rows only —
//!    a never-provable row could only poison the owner's evidence).
//!
//! ## The premise (docs/TCB.md, "A `Vec` scalar index forwards …")
//!
//! `F` passes `M` the slice `&**self`, and `Vec`'s `Deref` builds it as
//! `from_raw_parts(self.as_ptr(), self.len)`, so its length IS `self.len()` — the
//! quantity the `#7c` row's `coll_len` is tied to. std is built verify-off, so this
//! is a modeled fact about the sealed sysroot, recorded as such; rule 2 pins the
//! index half structurally, and rule 1 pins which body the fact is about.
//!
//! ## What stays refused, on purpose
//!
//! * A range index (`&v[a..b]` — `I = Range<usize>`): a different `M`, with
//!   different panic paths.
//! * A `VecDeque`/`String`/user-type index: not rule 1.
//! * A root site whose `#7c` row is absent or does not match: rule 4, atomic.
//! * A site in a local owner whose own row did not PROVE (or was the never-provable
//!   backstop): the owner records no charge, so the site is unowned.

use super::*;

/// Which of std's two `Vec` scalar-index forwarders a bundled member is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum VecIndexForwarderKind {
    Index,
    IndexMut,
}

/// What the admitting paths said about a member, composed fail-closed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum VecIndexForwarderEvidence {
    /// No admitting path asked (every non-B-lane member).
    #[default]
    NotRecorded,
    /// A path resolved it and it is not a forwarder.
    NotAForwarder,
    Forwarder(VecIndexForwarderKind),
    /// Two admitting paths disagreed. Never credits anything.
    Conflicting,
}

impl VecIndexForwarderEvidence {
    fn compose(&mut self, new: Self) {
        *self = match (*self, new) {
            (Self::NotRecorded, new) => new,
            (known, Self::NotRecorded) => known,
            (known, new) if known == new => known,
            _ => Self::Conflicting,
        };
    }

    pub(super) fn is_forwarder(self) -> bool {
        matches!(self, Self::Forwarder(_))
    }
}

/// Rule 1: is this RESOLVED instance std's `Vec` scalar-index forwarder?
pub(super) fn vec_usize_index_forwarder<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Option<VecIndexForwarderKind> {
    let ty::InstanceKind::Item(def_id) = instance.def else {
        return None;
    };
    if def_id.is_local()
        || !matches!(tcx.def_kind(def_id), DefKind::AssocFn)
        || !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, def_id)
    {
        return None;
    }
    let impl_did = tcx.trait_impl_of_assoc(def_id)?;
    let trait_ref =
        tcx.impl_trait_ref(impl_did).instantiate(tcx, instance.args).skip_normalization();
    // `Index`/`IndexMut` each declare exactly one method (`index`/`index_mut`), so an
    // associated FUNCTION of an impl of the lang-item trait is that method.
    let kind = if tcx.is_lang_item(trait_ref.def_id, rustc_attr_ir::lang_items::LangItem::Index) {
        VecIndexForwarderKind::Index
    } else if tcx.is_lang_item(trait_ref.def_id, rustc_attr_ir::lang_items::LangItem::IndexMut) {
        VecIndexForwarderKind::IndexMut
    } else {
        return None;
    };
    let ty::Adt(adt_def, _) = trait_ref.self_ty().kind() else {
        return None;
    };
    let adt_did = adt_def.did();
    if adt_did.is_local()
        || !tcx.is_diagnostic_item(sym::Vec, adt_did)
        || !trust_mir_extract::def_is_in_real_sysroot_crate(tcx, adt_did)
    {
        return None;
    }
    // `Index<Idx>`: the single generic argument after `Self` is the index type.
    let mut index_args = trait_ref.args.types().skip(1);
    let (Some(index_ty), None) = (index_args.next(), index_args.next()) else {
        return None;
    };
    (index_ty == tcx.types.usize).then_some(kind)
}

/// Record rule 1's answer for an admitted B-lane member. The caller records the
/// member first (`record_bundled_member_source_identity`).
pub(super) fn record_vec_index_forwarder<'tcx>(
    tcx: TyCtxt<'tcx>,
    ledger: &mut BundledMemberSourceIdentityLedger,
    member: &trust_types::VerifiableFunction,
    instance: ty::Instance<'tcx>,
) -> Result<(), String> {
    let key = bundled_member_source_identity_key(member)?;
    let Some(provenance) = ledger.get_mut(&key) else {
        return Err(format!(
            "Vec index-forwarder evidence for `{}` was recorded before the member",
            member.def_path
        ));
    };
    provenance.vec_index_forwarder.compose(match vec_usize_index_forwarder(tcx, instance) {
        Some(kind) => VecIndexForwarderEvidence::Forwarder(kind),
        None => VecIndexForwarderEvidence::NotAForwarder,
    });
    Ok(())
}

/// Test-only: attach forwarder evidence without a `TyCtxt`.
#[cfg(test)]
pub(super) fn attach_vec_index_forwarder_for_test(
    ledger: &mut BundledMemberSourceIdentityLedger,
    member: &trust_types::VerifiableFunction,
    kind: VecIndexForwarderKind,
) {
    let key = bundled_member_source_identity_key(member).expect("synthetic member serializes");
    ledger
        .get_mut(&key)
        .expect("member recorded first")
        .vec_index_forwarder
        .compose(VecIndexForwarderEvidence::Forwarder(kind));
}

/// Rule 3, over `M`'s derived admission.
pub(super) fn requires_is_forwarded_bounds(param_names: &[String], requires: &[Formula]) -> bool {
    let ([index, slice], [Formula::Lt(lhs, rhs)]) = (param_names, requires) else {
        return false;
    };
    let len_name = format!("{slice}__slice_len");
    matches!(lhs.as_ref(), Formula::Var(name, _) if name == index)
        && matches!(rhs.as_ref(), Formula::Var(name, _) if *name == len_name)
}

/// Rule 2, over `F`'s extracted body and its call sites to `M`.
pub(super) fn forwarder_body_forwards_index(
    forwarder: &trust_types::VerifiableFunction,
    member: &trust_types::VerifiableFunction,
    member_identity: trust_types::CalleeIdentity,
) -> Result<(), &'static str> {
    if forwarder.body.arg_count != 2 {
        return Err("the forwarder does not have exactly the (receiver, index) formals");
    }
    let sites = forwarder
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            trust_types::Terminator::Call { func, callee_identity, args, .. }
            | trust_types::Terminator::TailCall { func, callee_identity, args, .. }
                if member.name == func.as_str()
                    || member.def_path == func.as_str()
                    || *callee_identity == Some(member_identity) =>
            {
                Some(args)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [args] = sites.as_slice() else {
        return Err("the forwarder does not call the member exactly once");
    };
    let forwards_index = matches!(
        args.first(),
        Some(trust_types::Operand::Copy(place) | trust_types::Operand::Move(place))
            if place.local == 2 && place.projections.is_empty()
    );
    if !forwards_index || args.len() != 2 {
        return Err("the forwarder does not pass its own index formal as the member's index");
    }
    Ok(())
}

/// Rule 4 for every forwarder in the bundle: which are fully charged (with the
/// reason for each that is not), and what THIS root charged at its own direct
/// calls to one (published as own-root evidence, `SliceBoundsCheck` rows only).
pub(super) struct ForwarderCharges {
    pub(super) verdicts: FxHashMap<BundledMemberSourceIdentityKey, Result<(), String>>,
    pub(super) own_charges: Vec<member_assert_ownership::OwnRootMemberAssertCharge>,
}

pub(super) fn charge_vec_index_forwarders(
    root: &trust_types::VerifiableFunction,
    members: &[trust_types::VerifiableFunction],
    member_identities: &BundledMemberSourceIdentityLedger,
    all_vcs: &[VerificationCondition],
) -> Result<ForwarderCharges, String> {
    let mut verdicts = FxHashMap::default();
    let mut own_charges = Vec::new();
    let names = |candidate: &trust_types::VerifiableFunction, callee: &str| {
        candidate.name == callee || candidate.def_path == callee
    };
    // Rows are consumed across ALL forwarders, so one row can never stand in for two
    // call sites, even of two different forwarders.
    let mut consumed = vec![false; all_vcs.len()];
    // Trust (2026-10-02, census-vcgen-hang): ONE VC-gen memo scope for every row this
    // gate regenerates. Each replay asks the root's whole-function statement-version
    // oracle, which is memoized only inside a scope; unscoped, every root site rebuilt
    // it, O(sites x body) — on aterm-census `run_lock_order_census` (1114 blocks, 24
    // sites) minutes past the function's budget, inside bundle construction. The
    // scope changes no row (`trust_vcgen::row_replay_scope`: memos live, work meter
    // off, as for an unscoped replay); the only function asked about is `root`,
    // borrowed for the whole call.
    let _replay = trust_vcgen::row_replay_scope();
    for forwarder in members.iter().skip(1) {
        let key = bundled_member_source_identity_key(forwarder)?;
        let Some(provenance) = member_identities.get(&key) else {
            continue;
        };
        if !provenance.vec_index_forwarder.is_forwarder() {
            continue;
        }
        let verdict =
            (|| -> Result<Option<member_assert_ownership::OwnRootMemberAssertCharge>, String> {
                let Some(identity) = provenance.identity else {
                    return Err("it has no unique compiler-authenticated identity".into());
                };
                let mut sites = Vec::new();
                let mut rows = Vec::new();
                let mut all_bounds = true;
                for block in &root.body.blocks {
                    let (func, callee_identity, span) = match &block.terminator {
                        trust_types::Terminator::Call { func, callee_identity, span, .. }
                        | trust_types::Terminator::TailCall {
                            func, callee_identity, span, ..
                        } => (func.as_str(), *callee_identity, span),
                        _ => continue,
                    };
                    if !names(forwarder, func) && callee_identity != Some(identity) {
                        continue;
                    }
                    if callee_identity != Some(identity) {
                        return Err("a root call carries no, or a different, compiler-authenticated identity".into());
                    }
                    if members.iter().skip(1).filter(|candidate| names(candidate, func)).count()
                        != 1
                    {
                        return Err(
                            "a root call's callee key does not bind exactly one bundled body"
                                .into(),
                        );
                    }
                    // Trust (2026-10-02, census-vcgen-hang): the replay is this gate's
                    // costly step, so it stops at the function's deadline. The forwarder
                    // is then refused (its sites stay unowned: fail-closed), and the
                    // bundle being built is discarded anyway by the deadline check
                    // `build_full_verification_input` runs after construction, against
                    // the same deadline the compiler installs ambiently for the function:
                    // this decides when the work stops, not what is published.
                    if trust_types::verify_budget::current_deadline()
                        .is_some_and(|at| std::time::Instant::now() >= at)
                    {
                        return Err(format!(
                            "{NATIVE_BUNDLE_DEADLINE_DECLINE} while the root's owned-Vec index rows were regenerated"
                        ));
                    }
                    let Some((kind, body)) =
                        trust_vcgen::owned_vec_scalar_index_row(root, block.id)
                    else {
                        return Err(format!(
                            "the root's own vcgen emits no owned-Vec index row at {}:{}:{}",
                            span.file, span.line_start, span.col_start
                        ));
                    };
                    let found = all_vcs.iter().enumerate().position(|(index, vc)| {
                        !consumed[index]
                            && (vc.function.as_str() == root.def_path
                                || vc.function.as_str() == root.name)
                            && vc.location == *span
                            && vc.kind == kind
                            && vc.obligation.as_ref().is_some_and(|record| record.body == body)
                    });
                    let Some(index) = found else {
                        return Err(format!(
                            "no row in the root's inventory exactly matches the regenerated owned-Vec index row at {}:{}:{}",
                            span.file, span.line_start, span.col_start
                        ));
                    };
                    consumed[index] = true;
                    all_bounds &= matches!(kind, VcKind::SliceBoundsCheck);
                    sites.push(span.clone());
                    rows.push(all_vcs[index].clone());
                }
                let nested = member_assert_ownership::nested_member_call_ownership(
                    members,
                    forwarder,
                    &key,
                    identity,
                    member_identities,
                    None,
                )?;
                if let Some(reason) = nested.unowned {
                    return Err(reason);
                }
                if sites.is_empty() && nested.sites == 0 {
                    return Err("no call site reaches it".into());
                }
                Ok((!sites.is_empty() && all_bounds).then(|| {
                    member_assert_ownership::OwnRootMemberAssertCharge::new(
                        key.clone(),
                        identity,
                        sites,
                        rows,
                    )
                }))
            })();
        match verdict {
            Ok(charge) => {
                own_charges.extend(charge);
                verdicts.insert(key, Ok(()));
            }
            Err(reason) => {
                verdicts.insert(key, Err(reason));
            }
        }
    }
    Ok(ForwarderCharges { verdicts, own_charges })
}

/// What `member_assert_ownership` needs to credit a site of `M` inside a forwarder.
pub(super) struct ForwardedBoundsCredit<'a> {
    /// Rule 3 held for `M`.
    pub(super) member_is_forwarded_bounds: bool,
    pub(super) forwarders: &'a FxHashMap<BundledMemberSourceIdentityKey, Result<(), String>>,
}

impl ForwardedBoundsCredit<'_> {
    /// `None` when the caller is not a forwarder at all (the ordinary ownership rules
    /// apply); `Some(Ok)` when its sites are owned by forwarding; `Some(Err)` with the
    /// reason when it is a forwarder whose sites are not.
    pub(super) fn judge(
        &self,
        caller: &trust_types::VerifiableFunction,
        caller_key: &BundledMemberSourceIdentityKey,
        caller_is_forwarder: bool,
        member: &trust_types::VerifiableFunction,
        member_identity: trust_types::CalleeIdentity,
    ) -> Option<Result<(), String>> {
        if !caller_is_forwarder {
            return None;
        }
        if !self.member_is_forwarded_bounds {
            return Some(Err(
                "it is a Vec index forwarder, but the member's derived charge is not the single forwarded bounds requires".into(),
            ));
        }
        if let Err(reason) = forwarder_body_forwards_index(caller, member, member_identity) {
            return Some(Err(reason.into()));
        }
        Some(match self.forwarders.get(caller_key) {
            Some(Ok(())) => Ok(()),
            Some(Err(reason)) => Err(format!(
                "it is a Vec index forwarder whose own call sites are not all charged: {reason}"
            )),
            None => Err("it is a Vec index forwarder that was not judged in this bundle".into()),
        })
    }
}
