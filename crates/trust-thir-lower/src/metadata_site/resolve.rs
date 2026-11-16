//! Metadata validation before the existing pure SiteTy reconstruction path.

use rustc_hir::def::{CtorKind, DefKind};
use rustc_middle::ty::{
    self, ExistentialPredicateStableCmpExt, FallibleTypeFolder, TyCtxt, TypeFoldable,
    TypeSuperFoldable, TypeVisitableExt,
};
use rustc_span::def_id::DefId;

use super::{Decoded, InstanceKind, RecoveredSite, Result, SiteError};
use crate::{
    SiteArg, SiteClosureKind, SiteConst, SiteExistentialPredicate, SiteTerm, SiteTy, SiteValTree,
};

pub(super) fn recover<'tcx>(
    tcx: TyCtxt<'tcx>,
    suffix: &str,
    decoded: Decoded,
) -> Result<RecoveredSite<'tcx>> {
    if decoded.kind != InstanceKind::Item {
        return Err(SiteError("legacy site reify runtime adapter is unsupported"));
    }
    if !function_kind(tcx.def_kind(decoded.definition)) {
        return Err(SiteError("legacy site root is not a function Item"));
    }
    arguments(tcx, decoded.definition, &decoded.args, 0)?;
    // This helper only interns the explicitly preserved types/values/erased
    // regions. It reads no MIR body or MIR inventory despite its module name.
    let args = crate::to_mir::rebuild_site_args(tcx, &decoded.args)
        .ok_or(SiteError("legacy site Rustc argument reconstruction"))?;
    if args.has_non_region_param() || args.has_infer() || args.has_escaping_bound_vars() {
        return Err(SiteError("legacy site arguments are not concrete"));
    }
    let instance = ty::Instance::try_resolve(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        decoded.definition,
        args,
    )
    .map_err(|_| SiteError("legacy site Rustc instance resolution failed"))?
    .ok_or(SiteError("legacy site Rustc instance is unresolved"))?;
    if !matches!(instance.def, ty::InstanceKind::Item(_)) {
        return Err(SiteError("legacy site resolved runtime adapter is unsupported"));
    }
    if super::canonical_suffix(tcx, instance)? != suffix {
        return Err(SiteError("legacy site resolved instance does not canonically re-encode"));
    }
    Ok(RecoveredSite { instance, args: decoded.args })
}

fn function_kind(kind: DefKind) -> bool {
    matches!(kind, DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(_, CtorKind::Fn))
}

fn rust_type<'tcx>(tcx: TyCtxt<'tcx>, ty: &SiteTy) -> Result<ty::Ty<'tcx>> {
    crate::to_mir::rebuild_site_args(tcx, &[SiteArg::Ty(ty.clone())])
        .and_then(|args| args[0].as_type())
        .ok_or(SiteError("legacy site Rustc type reconstruction"))
}

/// `offset=1` is the EXISTENTIAL vocabulary: Rust explicitly omits Self.
/// No synthetic Self type is supplied to fill that position.
fn arguments(tcx: TyCtxt<'_>, owner: DefId, args: &[SiteArg], offset: usize) -> Result<()> {
    let generics = tcx.generics_of(owner);
    if args.len().checked_add(offset) != Some(generics.count()) {
        return Err(SiteError("legacy site positional generic arity"));
    }
    for (index, arg) in args.iter().enumerate() {
        match (&generics.param_at(index + offset, tcx).kind, arg) {
            (ty::GenericParamDefKind::Lifetime, SiteArg::ErasedRegion) => {}
            (ty::GenericParamDefKind::Type { .. }, SiteArg::Ty(ty)) => site_type(tcx, ty)?,
            (ty::GenericParamDefKind::Const { .. }, SiteArg::Const(value)) => konst(tcx, value)?,
            _ => return Err(SiteError("legacy site positional generic kind")),
        }
    }
    let rebuilt = crate::to_mir::rebuild_site_args(tcx, args)
        .ok_or(SiteError("legacy site nominal argument reconstruction"))?;
    for (index, arg) in args.iter().enumerate() {
        if let SiteArg::Const(SiteConst::Value(ty, _)) = arg {
            let binder = tcx.type_of(generics.param_at(index + offset, tcx).def_id);
            let expected = if offset == 0 {
                binder.instantiate(tcx, rebuilt).skip_normalization()
            } else {
                binder
                    .instantiate_identity()
                    .skip_normalization()
                    .try_fold_with(&mut WithoutSelf { tcx, args: rebuilt })?
            };
            if tcx.erase_and_anonymize_regions(expected) != rust_type(tcx, ty)? {
                return Err(SiteError("legacy site const argument declared type"));
            }
        }
    }
    Ok(())
}

fn site_type(tcx: TyCtxt<'_>, ty: &SiteTy) -> Result<()> {
    match ty {
        SiteTy::Bool
        | SiteTy::Char
        | SiteTy::Str
        | SiteTy::Never
        | SiteTy::Int(_)
        | SiteTy::Uint(_)
        | SiteTy::Float(_) => {}
        SiteTy::Foreign(owner) => {
            if tcx.def_kind(*owner) != DefKind::ForeignTy {
                return Err(SiteError("legacy site foreign definition kind"));
            }
        }
        SiteTy::Adt(owner, args) => {
            if !matches!(tcx.def_kind(*owner), DefKind::Struct | DefKind::Enum | DefKind::Union) {
                return Err(SiteError("legacy site ADT definition kind"));
            }
            arguments(tcx, *owner, args, 0)?;
        }
        SiteTy::FnDef(owner, args) => {
            if !function_kind(tcx.def_kind(*owner)) {
                return Err(SiteError("legacy site function definition kind"));
            }
            arguments(tcx, *owner, args, 0)?;
        }
        SiteTy::Tuple(types) | SiteTy::FnPtr { inputs_and_output: types, .. } => {
            for ty in types {
                site_type(tcx, ty)?;
            }
        }
        SiteTy::Array(ty, count) => {
            let bits = tcx.data_layout.pointer_size().bits();
            if bits < 64 && *count >> bits != 0 {
                return Err(SiteError("legacy site array length target width"));
            }
            site_type(tcx, ty)?;
        }
        SiteTy::Ref(ty, _) | SiteTy::RawPtr(ty, _) | SiteTy::Slice(ty) => site_type(tcx, ty)?,
        SiteTy::ClosureLike(kind, owner, args) => closure(tcx, *kind, *owner, args)?,
        SiteTy::Dynamic(predicates) => {
            if predicates.is_empty() {
                return Err(SiteError("legacy site empty dynamic predicates"));
            }
            let mut rebuilt = Vec::with_capacity(predicates.len());
            let mut principals = 0;
            for predicate in predicates {
                let value = match predicate {
                    SiteExistentialPredicate::Trait(owner, args) => {
                        if tcx.def_kind(*owner) != DefKind::Trait || tcx.trait_is_auto(*owner) {
                            return Err(SiteError("legacy site principal trait definition kind"));
                        }
                        principals += 1;
                        if principals > 1 {
                            return Err(SiteError("legacy site multiple dynamic principal traits"));
                        }
                        arguments(tcx, *owner, args, 1)?;
                        ty::ExistentialPredicate::Trait(ty::ExistentialTraitRef::new_from_args(
                            tcx,
                            *owner,
                            rebuild(tcx, args)?,
                        ))
                    }
                    SiteExistentialPredicate::AutoTrait(owner) => {
                        if tcx.def_kind(*owner) != DefKind::Trait || !tcx.trait_is_auto(*owner) {
                            return Err(SiteError("legacy site auto trait definition kind"));
                        }
                        ty::ExistentialPredicate::AutoTrait(*owner)
                    }
                    SiteExistentialPredicate::Projection(owner, args, term) => {
                        if !matches!(tcx.def_kind(*owner), DefKind::AssocTy | DefKind::AssocConst)
                            || tcx.trait_of_assoc(*owner).is_none()
                        {
                            return Err(SiteError(
                                "legacy site projection is not a trait associated item",
                            ));
                        }
                        arguments(tcx, *owner, args, 1)?;
                        match (tcx.def_kind(*owner), &**term) {
                            (DefKind::AssocTy, SiteTerm::Ty(value)) => site_type(tcx, value)?,
                            (DefKind::AssocConst, SiteTerm::Const(value)) => {
                                konst(tcx, value)?;
                                let expected = tcx
                                    .type_of(*owner)
                                    .instantiate_identity()
                                    .skip_normalization()
                                    .try_fold_with(&mut WithoutSelf {
                                        tcx,
                                        args: rebuild(tcx, args)?,
                                    })?;
                                let SiteConst::Value(actual, _) = value;
                                if rust_type(tcx, actual)?
                                    != tcx.erase_and_anonymize_regions(expected)
                                {
                                    return Err(SiteError(
                                        "legacy site associated const term declared type",
                                    ));
                                }
                            }
                            _ => return Err(SiteError("legacy site projection term kind")),
                        }
                        let term: ty::Term<'_> = match &**term {
                            SiteTerm::Ty(value) => rust_type(tcx, value)?.into(),
                            SiteTerm::Const(value) => rebuild_const(tcx, value)?.into(),
                        };
                        ty::ExistentialPredicate::Projection(
                            ty::ExistentialProjection::new_from_args(
                                tcx,
                                *owner,
                                rebuild(tcx, args)?,
                                term,
                            ),
                        )
                    }
                };
                rebuilt.push(value);
            }
            // The existing interner ASSERTS canonical order. Check attacker
            // input before that call, without sorting away wire information.
            if rebuilt.windows(2).any(|pair| {
                pair[0].stable_cmp(tcx, &pair[1]) == std::cmp::Ordering::Greater
                    || pair[0] == pair[1]
            }) {
                return Err(SiteError("legacy site dynamic predicate order or duplicate"));
            }
            dynamic_projection_population(tcx, &rebuilt)?;
        }
    }
    Ok(())
}

/// Rustc's dynamic-type constructor asserts the associated projection census.
/// Read the real trait metadata, including distinct supertrait instantiations,
/// before calling that constructor. Metadata identity parameters are used only
/// to enumerate declarations; none becomes a reconstructed runtime argument.
fn dynamic_projection_population<'tcx>(
    tcx: TyCtxt<'tcx>,
    predicates: &[ty::ExistentialPredicate<'tcx>],
) -> Result<()> {
    let identity = |owner| {
        let hash = tcx.def_path_hash(owner);
        (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
    };
    let mut expected = Vec::new();
    let mut allowed = Vec::new();
    if let Some(principal) = predicates.iter().find_map(|p| match p {
        ty::ExistentialPredicate::Trait(trait_ref) => Some(*trait_ref),
        _ => None,
    }) {
        for (count, parent) in ty::elaborate::supertraits(
            tcx,
            ty::Binder::dummy(ty::TraitRef::identity(tcx, principal.def_id)),
        )
        .enumerate()
        {
            if count >= super::MAX_NODES {
                return Err(SiteError("legacy site supertrait metadata budget"));
            }
            // This is the same metadata declaration walk as the census, but
            // bind its original positions to the actual existential arguments.
            // Self is absent from the wire. Never fill it with a dummy type:
            // WithoutSelf refuses a declaration argument that depends on it.
            let parent = tcx.instantiate_bound_regions_with_erased(parent);
            let prefix = tcx
                .mk_args(&parent.args.as_slice()[1..])
                .try_fold_with(&mut WithoutSelf { tcx, args: principal.args })?;
            if prefix.has_non_region_param()
                || prefix.has_infer()
                || prefix.has_escaping_bound_vars()
            {
                return Err(SiteError(
                    "legacy site supertrait arguments are not concrete without Self",
                ));
            }
            for item in tcx.associated_items(parent.def_id).in_definition_order() {
                if item.can_have_equality_constraint(tcx) && !item.is_impl_trait_in_trait() {
                    if allowed.len() >= super::MAX_NODES {
                        return Err(SiteError(
                            "legacy site associated declaration metadata budget",
                        ));
                    }
                    let row = (identity(item.def_id), prefix);
                    allowed.push(row);
                    if !tcx.generics_require_sized_self(item.def_id) {
                        expected.push(row);
                    }
                }
            }
        }
    }
    let matches = |row: &(super::StableDef, ty::GenericArgs<'tcx>),
                   projection: &ty::ExistentialProjection<'tcx>| {
        row.0 == identity(projection.def_id)
            && projection.args.len() >= row.1.len()
            && projection.args.as_slice()[..row.1.len()] == row.1.as_slice()[..]
    };
    let mut claimed = vec![false; expected.len()];
    let mut bindings = std::collections::HashSet::new();
    for predicate in predicates {
        if let ty::ExistentialPredicate::Projection(projection) = predicate {
            // The raw provided projection is not normalized or repaired. Both
            // definition and every typed trait argument must match the loaded
            // declaration after positional substitution from the principal.
            if !allowed.iter().any(|row| matches(row, projection)) {
                return Err(SiteError("legacy site dynamic projection trait arguments mismatch"));
            }
            if !bindings.insert((projection.def_id, projection.args)) {
                return Err(SiteError("legacy site duplicate dynamic projection binding"));
            }
            if !tcx.generics_require_sized_self(projection.def_id) {
                let Some(index) = expected.iter().enumerate().find_map(|(index, row)| {
                    (!claimed[index] && matches(row, projection)).then_some(index)
                }) else {
                    return Err(SiteError("legacy site dynamic required projection population"));
                };
                claimed[index] = true;
            }
        }
    }
    if claimed.iter().any(|claimed| !claimed) {
        return Err(SiteError("legacy site dynamic required projection population"));
    }
    Ok(())
}

fn rebuild<'tcx>(tcx: TyCtxt<'tcx>, args: &[SiteArg]) -> Result<ty::GenericArgs<'tcx>> {
    crate::to_mir::rebuild_site_args(tcx, args)
        .ok_or(SiteError("legacy site positional reconstruction"))
}

fn rebuild_const<'tcx>(tcx: TyCtxt<'tcx>, value: &SiteConst) -> Result<ty::Const<'tcx>> {
    rebuild(tcx, &[SiteArg::Const(value.clone())])?
        .get(0)
        .and_then(|value| value.as_const())
        .ok_or(SiteError("legacy site const reconstruction"))
}

fn closure(tcx: TyCtxt<'_>, kind: SiteClosureKind, owner: DefId, args: &[SiteArg]) -> Result<()> {
    if !matches!(tcx.def_kind(owner), DefKind::Closure | DefKind::SyntheticCoroutineBody) {
        return Err(SiteError("legacy site closure definition kind"));
    }
    let actual = tcx.type_of(owner).instantiate_identity().skip_normalization();
    let matches = matches!(
        (kind, actual.kind()),
        (SiteClosureKind::Closure, ty::Closure(..))
            | (SiteClosureKind::CoroutineClosure, ty::CoroutineClosure(..))
            | (SiteClosureKind::Coroutine, ty::Coroutine(..))
            | (SiteClosureKind::CoroutineWitness, ty::Coroutine(..))
    );
    if !matches {
        return Err(SiteError("legacy site closure family metadata mismatch"));
    }
    arguments(tcx, owner, args, 0)?;
    let parent = tcx.generics_of(owner).parent_count;
    let synthetic = &args[parent..];
    let is_kind = |arg: &SiteArg| {
        matches!(arg, SiteArg::Ty(SiteTy::Int(ty::IntTy::I8 | ty::IntTy::I16 | ty::IntTy::I32)))
    };
    let tuple = |arg: &SiteArg| matches!(arg, SiteArg::Ty(SiteTy::Tuple(_)));
    match kind {
        SiteClosureKind::Closure => {
            if synthetic.len() != 3 || !is_kind(&synthetic[0]) || !tuple(&synthetic[2]) {
                return Err(SiteError("legacy site ordinary closure synthetic arguments"));
            }
            let SiteArg::Ty(SiteTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted }) =
                &synthetic[1]
            else {
                return Err(SiteError("legacy site ordinary closure signature kind"));
            };
            if abi != "rust-call"
                || !safe
                || *c_variadic
                || splatted.is_some()
                || inputs_and_output.len() != 2
                || !matches!(inputs_and_output[0], SiteTy::Tuple(_))
            {
                return Err(SiteError("legacy site ordinary closure tupled signature"));
            }
        }
        SiteClosureKind::CoroutineClosure => {
            if synthetic.len() != 4
                || !is_kind(&synthetic[0])
                || !tuple(&synthetic[2])
                || !matches!(synthetic[1], SiteArg::Ty(SiteTy::FnPtr { .. }))
                || !matches!(synthetic[3], SiteArg::Ty(SiteTy::FnPtr { .. }))
            {
                return Err(SiteError("legacy site coroutine closure synthetic arguments"));
            }
        }
        SiteClosureKind::Coroutine | SiteClosureKind::CoroutineWitness => {
            if synthetic.len() != 5
                || !(is_kind(&synthetic[0])
                    || matches!(&synthetic[0], SiteArg::Ty(SiteTy::Tuple(types)) if types.is_empty()))
                || !tuple(&synthetic[4])
            {
                return Err(SiteError("legacy site coroutine synthetic arguments"));
            }
        }
    }
    // Synthetic signature/capture/coroutine slots are facts of this owner,
    // not free parameters an attacker may select while retaining its hash.
    let declared = tcx.type_of(owner).instantiate(tcx, rebuild(tcx, args)?).skip_normalization();
    let declared_args = match declared.kind() {
        ty::Closure(_, args) | ty::CoroutineClosure(_, args) | ty::Coroutine(_, args) => *args,
        _ => return Err(SiteError("legacy site closure metadata type disappeared")),
    };
    if crate::encode_site_args(tcx, declared_args).as_deref() != Some(args) {
        return Err(SiteError("legacy site closure synthetic signature/capture metadata mismatch"));
    }
    Ok(())
}

fn konst(tcx: TyCtxt<'_>, value: &SiteConst) -> Result<()> {
    let SiteConst::Value(ty, tree) = value;
    site_type(tcx, ty)?;
    if let SiteValTree::Branch(values) = tree {
        for value in values {
            konst(tcx, value)?;
        }
    }
    value_tree(tcx, rust_type(tcx, ty)?, tree)
}

fn value_tree<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>, tree: &SiteValTree) -> Result<()> {
    let scalar = |bytes: u64| -> Result<u128> {
        let SiteValTree::Leaf(bits, actual) = tree else {
            return Err(SiteError("legacy site scalar valtree shape"));
        };
        if *actual != bytes {
            return Err(SiteError("legacy site scalar type width"));
        }
        Ok(*bits)
    };
    let branches = || -> Result<&[SiteConst]> {
        let SiteValTree::Branch(values) = tree else {
            return Err(SiteError("legacy site aggregate valtree shape"));
        };
        Ok(values)
    };
    let child = |value: &SiteConst, expected: ty::Ty<'tcx>| -> Result<()> {
        let SiteConst::Value(actual, _) = value;
        if rust_type(tcx, actual)? != tcx.erase_and_anonymize_regions(expected) {
            return Err(SiteError("legacy site valtree child type"));
        }
        Ok(())
    };
    match ty.kind() {
        ty::Bool => {
            if scalar(1)? > 1 {
                return Err(SiteError("legacy site invalid boolean constant"));
            }
        }
        ty::Char => {
            if char::from_u32(
                u32::try_from(scalar(4)?)
                    .map_err(|_| SiteError("legacy site invalid char constant"))?,
            )
            .is_none()
            {
                return Err(SiteError("legacy site invalid char constant"));
            }
        }
        ty::Int(kind) => {
            scalar(match kind {
                ty::IntTy::Isize => tcx.data_layout.pointer_size().bytes(),
                ty::IntTy::I8 => 1,
                ty::IntTy::I16 => 2,
                ty::IntTy::I32 => 4,
                ty::IntTy::I64 => 8,
                ty::IntTy::I128 => 16,
            })?;
        }
        ty::Uint(kind) => {
            scalar(match kind {
                ty::UintTy::Usize => tcx.data_layout.pointer_size().bytes(),
                ty::UintTy::U8 => 1,
                ty::UintTy::U16 => 2,
                ty::UintTy::U32 => 4,
                ty::UintTy::U64 => 8,
                ty::UintTy::U128 => 16,
            })?;
        }
        ty::Float(kind) => {
            scalar(match kind {
                ty::FloatTy::F16 => 2,
                ty::FloatTy::F32 => 4,
                ty::FloatTy::F64 => 8,
                ty::FloatTy::F128 => 16,
            })?;
        }
        ty::RawPtr(pointee, _) => {
            if matches!(pointee.kind(), ty::Str | ty::Slice(_) | ty::Dynamic(..)) {
                return Err(SiteError("legacy site wide raw pointer constant adapter unsupported"));
            }
            scalar(tcx.data_layout.pointer_size().bytes())?;
        }
        ty::Ref(_, pointee, _) => value_tree(tcx, *pointee, tree)?,
        ty::FnDef(..) => {
            if !branches()?.is_empty() {
                return Err(SiteError("legacy site function-item constant is not ZST"));
            }
        }
        ty::Str => {
            let mut bytes = Vec::new();
            for value in branches()? {
                child(value, tcx.types.u8)?;
                let SiteConst::Value(_, SiteValTree::Leaf(bits, 1)) = value else {
                    return Err(SiteError("legacy site str byte"));
                };
                bytes.push(*bits as u8);
            }
            std::str::from_utf8(&bytes).map_err(|_| SiteError("legacy site str constant UTF-8"))?;
        }
        ty::Slice(elem) | ty::Array(elem, _) => {
            let values = branches()?;
            if let ty::Array(_, count) = ty.kind() {
                let expected = count
                    .try_to_target_usize(tcx)
                    .ok_or(SiteError("legacy site array constant length is not a value"))?;
                if u64::try_from(values.len()).ok() != Some(expected) {
                    return Err(SiteError("legacy site array valtree length"));
                }
            }
            for value in values {
                child(value, *elem)?;
            }
        }
        ty::Tuple(types) => {
            let values = branches()?;
            if types.len() != values.len() {
                return Err(SiteError("legacy site tuple valtree length"));
            }
            for (value, expected) in values.iter().zip(types.iter()) {
                child(value, expected)?;
            }
        }
        ty::Adt(adt, args) => {
            if adt.is_union() {
                return Err(SiteError("legacy site union const adapter unsupported"));
            }
            let values = branches()?;
            let (variant, fields) = if adt.is_enum() {
                let Some((tag, fields)) = values.split_first() else {
                    return Err(SiteError("legacy site enum valtree missing variant"));
                };
                child(tag, tcx.types.u32)?;
                let SiteConst::Value(_, SiteValTree::Leaf(tag, 4)) = tag else {
                    return Err(SiteError("legacy site enum valtree variant"));
                };
                (
                    usize::try_from(*tag)
                        .map_err(|_| SiteError("legacy site enum variant overflow"))?,
                    fields,
                )
            } else {
                (0, values)
            };
            let variant = adt
                .variants()
                .iter()
                .nth(variant)
                .ok_or(SiteError("legacy site enum variant absent"))?;
            if variant.fields.len() != fields.len() {
                return Err(SiteError("legacy site ADT valtree field population"));
            }
            for (value, field) in fields.iter().zip(variant.fields.iter()) {
                child(value, field.ty(tcx, *args).skip_normalization())?;
            }
        }
        _ => {
            return Err(SiteError(
                "legacy site const type has no supported valtree runtime adapter",
            ));
        }
    }
    Ok(())
}

/// Existential arguments omit Self. Substitute each present position at its
/// original index and refuse an actual dependency on missing Self. Unlike an
/// ordinary substitution this never manufactures a dummy type at index zero.
struct WithoutSelf<'tcx> {
    tcx: TyCtxt<'tcx>,
    args: ty::GenericArgs<'tcx>,
}

impl<'tcx> FallibleTypeFolder<TyCtxt<'tcx>> for WithoutSelf<'tcx> {
    type Error = SiteError;
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn try_fold_ty(&mut self, value: ty::Ty<'tcx>) -> Result<ty::Ty<'tcx>> {
        if let ty::Param(param) = value.kind() {
            let index = param
                .index
                .checked_sub(1)
                .ok_or(SiteError("legacy site existential constant depends on absent Self"))?;
            return self
                .args
                .get(index as usize)
                .and_then(|arg| arg.as_type())
                .ok_or(SiteError("legacy site existential type substitution kind"));
        }
        value.try_super_fold_with(self)
    }
    fn try_fold_const(&mut self, value: ty::Const<'tcx>) -> Result<ty::Const<'tcx>> {
        if let ty::ConstKind::Param(param) = value.kind() {
            let index = param
                .index
                .checked_sub(1)
                .ok_or(SiteError("legacy site existential const index"))?;
            return self
                .args
                .get(index as usize)
                .and_then(|arg| arg.as_const())
                .ok_or(SiteError("legacy site existential const substitution kind"));
        }
        value.try_super_fold_with(self)
    }
    fn try_fold_region(&mut self, _: ty::Region<'tcx>) -> Result<ty::Region<'tcx>> {
        Ok(self.tcx.lifetimes.re_erased)
    }
}
