//! The Rust host half of stable template keys. It never reads MIR or layout.

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_hir::def::{CtorKind, DefKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, DefPathHash, LOCAL_CRATE};

use super::{HoleKey, KeyArg, KeyConst, KeyConstItem, KeyError, KeyTy, Result, StableDef, MAX_DEPTH, MAX_BYTES, MAX_NODES};

pub fn stable_def(tcx: TyCtxt<'_>, def: DefId) -> StableDef {
    let hash = tcx.def_path_hash(def);
    (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
}

pub fn definition(tcx: TyCtxt<'_>, key: StableDef) -> Result<DefId> {
    // The external lookup assumes its StableCrateId has been loaded. Check
    // that premise before handing an untrusted metadata key to the lookup.
    if !std::iter::once(LOCAL_CRATE)
        .chain(tcx.crates(()).iter().copied())
        .any(|c| tcx.stable_crate_id(c).as_u64() == key.0)
    {
        return Err(KeyError("template key names an unloaded crate"));
    }
    let def = tcx
        .def_path_hash_to_def_id(DefPathHash(Fingerprint::new(key.0, key.1)))
        .ok_or(KeyError("template key definition is absent"))?;
    let hash = tcx.def_path_hash(def);
    if key != (hash.stable_crate_id().as_u64(), hash.local_hash().as_u64())
        || key.0 != tcx.stable_crate_id(def.krate).as_u64()
    {
        return Err(KeyError("template key differs from actual Rust definition"));
    }
    Ok(def)
}

pub fn key_of_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Result<KeyTy> {
    type_key(tcx, tcx.erase_and_anonymize_regions(ty), 0, &mut SourceBudget::new(13))
}

pub fn key_of_call<'tcx>(
    tcx: TyCtxt<'tcx>, item: DefId, args: ty::GenericArgs<'tcx>,
) -> Result<HoleKey> {
    Ok(HoleKey::Callee { item: stable_def(tcx, item), args: args_key(tcx, tcx.erase_and_anonymize_regions(args), 0, &mut SourceBudget::new(29))? })
}

pub fn key_of_associated_const<'tcx>(
    tcx: TyCtxt<'tcx>, item: DefId, args: ty::GenericArgs<'tcx>,
) -> Result<HoleKey> {
    if tcx.def_kind(item) != DefKind::AssocConst { return Err(KeyError("template const hole is not associated")); }
    Ok(HoleKey::Const(KeyConstItem::Assoc {
        item: stable_def(tcx, item), args: args_key(tcx, tcx.erase_and_anonymize_regions(args), 0, &mut SourceBudget::new(29))?,
    }))
}

fn depth(depth: usize) -> Result<()> {
    if depth > MAX_DEPTH { Err(KeyError("template Rust term depth budget")) } else { Ok(()) }
}

// Charge the expanded tree before allocating it. Rustc's interned DAG may
// share a child exponentially often, so checking only the final byte codec is
// too late. These charges match the canonical wire grammar, including arg tags.
struct SourceBudget { bytes: usize, nodes: usize, reserved: usize }
impl SourceBudget {
    fn new(bytes: usize) -> Self { Self { bytes, nodes: 0, reserved: 0 } }
    fn bytes(&mut self, bytes: usize) -> Result<()> {
        self.bytes = self.bytes.checked_add(bytes).ok_or(KeyError("template Rust byte budget"))?;
        if self.bytes > MAX_BYTES { return Err(KeyError("template Rust byte budget")); }
        Ok(())
    }
    fn node(&mut self, n: usize) -> Result<()> {
        depth(n)?;
        self.nodes += 1;
        if self.nodes > MAX_NODES { return Err(KeyError("template Rust node budget")); }
        self.bytes(1)
    }
    fn list(&mut self, len: usize) -> Result<()> {
        self.reserved = self.reserved.checked_add(len).ok_or(KeyError("template Rust allocation budget"))?;
        if self.reserved > MAX_NODES { return Err(KeyError("template Rust allocation budget")); }
        self.bytes(4)
    }
}

fn args_key<'tcx>(tcx: TyCtxt<'tcx>, args: ty::GenericArgs<'tcx>, n: usize, budget: &mut SourceBudget) -> Result<Vec<KeyArg>> {
    depth(n)?;
    budget.list(args.len())?;
    args.iter().map(|arg| { budget.node(n)?; Ok(match arg.kind() {
        ty::GenericArgKind::Lifetime(_) => KeyArg::ErasedRegion,
        ty::GenericArgKind::Type(t) => KeyArg::Type(type_key(tcx, t, n + 1, budget)?),
        ty::GenericArgKind::Const(c) => KeyArg::Const(const_key(tcx, c, n + 1, budget)?),
    }) }).collect()
}

fn const_key<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Const<'tcx>, n: usize, budget: &mut SourceBudget) -> Result<KeyConst> {
    budget.node(n)?;
    match value.kind() {
        ty::ConstKind::Param(p) => { budget.bytes(4)?; Ok(KeyConst::Param(p.index)) },
        ty::ConstKind::Value(v) => {
            budget.bytes(17)?;
            let ty::ValTreeKind::Leaf(bits) = &*v.valtree else {
                return Err(KeyError("template key non-scalar const value"));
            };
            let ty = Box::new(type_key(tcx, v.ty, n + 1, budget)?);
            let bytes = u8::try_from(bits.size().bytes()).map_err(|_| KeyError("template key const width"))?;
            let bits = bits.to_bits(bits.size());
            super::scalar(bits, bytes, &ty)?;
            Ok(KeyConst::Value { bits, bytes, ty })
        }
        ty::ConstKind::Alias(..) => Err(KeyError("template key unevaluated const argument")),
        ty::ConstKind::Expr(..) => Err(KeyError("template key generic const expression")),
        ty::ConstKind::Infer(..) => Err(KeyError("template key inferred const")),
        ty::ConstKind::Bound(..) => Err(KeyError("template key bound const")),
        ty::ConstKind::Placeholder(..) => Err(KeyError("template key placeholder const")),
        ty::ConstKind::Error(..) => Err(KeyError("template key error const")),
    }
}

/// Exhaustive: a new rustc type kind must be represented or refused by name.
fn type_key<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>, n: usize, budget: &mut SourceBudget) -> Result<KeyTy> {
    budget.node(n)?;
    budget.bytes(match t.kind() {
        ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Ref(..) | ty::RawPtr(..) => 1,
        ty::Param(_) => 4,
        ty::Adt(..) | ty::FnDef(..) | ty::Closure(..) | ty::Foreign(..) => 16,
        ty::Alias(..) => 17,
        _ => 0,
    })?;
    Ok(match t.kind() {
        ty::Bool => KeyTy::Bool,
        ty::Char => KeyTy::Char,
        ty::Int(i) => KeyTy::Int(match i {
            ty::IntTy::Isize => 0, ty::IntTy::I8 => 8, ty::IntTy::I16 => 16,
            ty::IntTy::I32 => 32, ty::IntTy::I64 => 64, ty::IntTy::I128 => 128,
        }),
        ty::Uint(i) => KeyTy::Uint(match i {
            ty::UintTy::Usize => 0, ty::UintTy::U8 => 8, ty::UintTy::U16 => 16,
            ty::UintTy::U32 => 32, ty::UintTy::U64 => 64, ty::UintTy::U128 => 128,
        }),
        ty::Float(i) => KeyTy::Float(match i {
            ty::FloatTy::F16 => 16, ty::FloatTy::F32 => 32,
            ty::FloatTy::F64 => 64, ty::FloatTy::F128 => 128,
        }),
        ty::Str => KeyTy::Str,
        ty::Never => KeyTy::Never,
        ty::Param(p) => KeyTy::Param(p.index),
        ty::Adt(adt, args) => KeyTy::Adt(stable_def(tcx, adt.did()), args_key(tcx, *args, n + 1, budget)?),
        ty::Ref(_, pointee, mutability) => KeyTy::Ref {
            mutable: mutability.is_mut(), pointee: Box::new(type_key(tcx, *pointee, n + 1, budget)?),
        },
        ty::RawPtr(pointee, mutability) => KeyTy::RawPtr {
            mutable: mutability.is_mut(), pointee: Box::new(type_key(tcx, *pointee, n + 1, budget)?),
        },
        ty::Slice(t) => KeyTy::Slice(Box::new(type_key(tcx, *t, n + 1, budget)?)),
        ty::Array(t, c) => KeyTy::Array(Box::new(type_key(tcx, *t, n + 1, budget)?), const_key(tcx, *c, n + 1, budget)?),
        ty::Tuple(ts) => {
            budget.list(ts.len())?;
            KeyTy::Tuple(ts.iter().map(|t| type_key(tcx, t, n + 1, budget)).collect::<Result<_>>()?)
        },
        ty::FnDef(item, args) => {
            if !args.bound_vars().is_empty() { return Err(KeyError("template key bound function-item arguments")); }
            KeyTy::FnDef(stable_def(tcx, *item), args_key(tcx, args.skip_binder(), n + 1, budget)?)
        }
        ty::FnPtr(types, header) => {
            if !types.bound_vars().is_empty() { return Err(KeyError("template key bound function-pointer signature")); }
            let types = types.skip_binder();
            budget.list(types.inputs_and_output.len())?;
            budget.bytes(header.abi().as_str().len() + 4 + usize::from(header.fn_sig_kind.splatted().is_some()))?;
            KeyTy::FnPtr {
                inputs_and_output: types.inputs_and_output.iter()
                    .map(|t| type_key(tcx, t, n + 1, budget)).collect::<Result<_>>()?,
                abi: header.abi().as_str().to_string(), safe: header.safety().is_safe(),
                c_variadic: header.c_variadic(), splatted: header.fn_sig_kind.splatted(),
            }
        }
        ty::Closure(item, args) => KeyTy::Closure(stable_def(tcx, *item), args_key(tcx, *args, n + 1, budget)?),
        ty::Alias(rigid, alias) => match alias.kind {
            ty::AliasTyKind::Projection { def_id } => KeyTy::Projection {
                item: stable_def(tcx, def_id.into()), args: args_key(tcx, alias.args, n + 1, budget)?,
                rigid: matches!(rigid, ty::IsRigid::Yes),
            },
            ty::AliasTyKind::Inherent { .. } => return Err(KeyError("template key inherent alias")),
            ty::AliasTyKind::Opaque { .. } => return Err(KeyError("template key opaque alias")),
            ty::AliasTyKind::Free { .. } => return Err(KeyError("template key free alias")),
        },
        ty::Foreign(item) => KeyTy::Foreign(stable_def(tcx, *item)),
        ty::Dynamic(..) => return Err(KeyError("template key dynamic trait object")),
        ty::Coroutine(..) => return Err(KeyError("template key coroutine type")),
        ty::CoroutineClosure(..) => return Err(KeyError("template key coroutine-closure type")),
        ty::CoroutineWitness(..) => return Err(KeyError("template key coroutine witness")),
        ty::Pat(..) => return Err(KeyError("template key pattern type")),
        ty::UnsafeBinder(..) => return Err(KeyError("template key unsafe binder")),
        ty::Bound(..) => return Err(KeyError("template key bound type")),
        ty::Placeholder(..) => return Err(KeyError("template key placeholder type")),
        ty::Infer(..) => return Err(KeyError("template key inferred type")),
        ty::Error(..) => return Err(KeyError("template key error type")),
    })
}

fn param<'tcx>(tcx: TyCtxt<'tcx>, owner: DefId, index: u32) -> Result<&'tcx ty::GenericParamDef> {
    let generics = tcx.generics_of(owner);
    if index as usize >= generics.count() { return Err(KeyError("template key parameter index")); }
    Ok(generics.param_at(index as usize, tcx))
}

pub fn ty_of_key<'tcx>(tcx: TyCtxt<'tcx>, key: &KeyTy, owner: DefId) -> Result<ty::Ty<'tcx>> {
    // Encoding checks the same depth/size/scalar constraints for typed callers
    // and decoded metadata alike, before any rustc constructor is reached.
    super::encode_type(key)?;
    rebuild_type(tcx, key, owner, 0)
}

pub fn call_of_key<'tcx>(
    tcx: TyCtxt<'tcx>, key: &HoleKey, owner: DefId,
) -> Result<(DefId, ty::GenericArgs<'tcx>)> {
    let HoleKey::Callee { item, args } = key else { return Err(KeyError("template key is not a callee")); };
    super::encode(key)?;
    let item = definition(tcx, *item)?;
    if !matches!(tcx.def_kind(item), DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(_, CtorKind::Fn)) {
        return Err(KeyError("template callee key is not a function"));
    }
    Ok((item, rebuild_args(tcx, item, args, owner, 0)?))
}

/// Rebuild every original generic position and declared const-argument type
/// before answering an associated-constant key.
pub fn associated_const_of_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    key: &HoleKey,
    owner: DefId,
) -> Result<(DefId, ty::GenericArgs<'tcx>)> {
    super::encode(key)?;
    let HoleKey::Const(KeyConstItem::Assoc { item, args }) = key else {
        return Err(KeyError("template key is not an associated constant"));
    };
    let item = definition(tcx, *item)?;
    if tcx.def_kind(item) != DefKind::AssocConst {
        return Err(KeyError("template constant key definition is not an associated constant"));
    }
    Ok((item, rebuild_args(tcx, item, args, owner, 0)?))
}

pub fn checked_call_key<'tcx>(
    tcx: TyCtxt<'tcx>, item: DefId, args: ty::GenericArgs<'tcx>, owner: DefId,
) -> Result<HoleKey> {
    let key = key_of_call(tcx, item, args)?;
    let (decoded, rebuilt) = call_of_key(tcx, &key, owner)?;
    if decoded != item || tcx.erase_and_anonymize_regions(rebuilt) != tcx.erase_and_anonymize_regions(args) {
        return Err(KeyError("template callee key does not round-trip"));
    }
    Ok(key)
}

pub fn checked_type_key<'tcx>(tcx: TyCtxt<'tcx>, t: ty::Ty<'tcx>, owner: DefId) -> Result<KeyTy> {
    let key = key_of_ty(tcx, t)?;
    if ty_of_key(tcx, &key, owner)? != tcx.erase_and_anonymize_regions(t) {
        return Err(KeyError("template type key does not round-trip"));
    }
    Ok(key)
}

fn rebuild_args<'tcx>(
    tcx: TyCtxt<'tcx>, item: DefId, keys: &[KeyArg], owner: DefId, n: usize,
) -> Result<ty::GenericArgs<'tcx>> {
    depth(n)?;
    let generics = tcx.generics_of(item);
    if keys.len() != generics.count() { return Err(KeyError("template key generic arity")); }
    let mut args = Vec::with_capacity(keys.len());
    for (i, key) in keys.iter().enumerate() {
        let kind = &generics.param_at(i, tcx).kind;
        let arg: ty::GenericArg<'tcx> = match (kind, key) {
            (ty::GenericParamDefKind::Lifetime, KeyArg::ErasedRegion) => tcx.lifetimes.re_erased.into(),
            (ty::GenericParamDefKind::Type { .. }, KeyArg::Type(t)) => rebuild_type(tcx, t, owner, n + 1)?.into(),
            (ty::GenericParamDefKind::Const { .. }, KeyArg::Const(c)) => rebuild_const(tcx, c, owner, n + 1)?.into(),
            _ => return Err(KeyError("template key generic argument kind")),
        };
        args.push(arg);
    }
    let args = tcx.mk_args(&args);
    for (i, key) in keys.iter().enumerate() {
        if let KeyArg::Const(c) = key {
            let expected = tcx.type_of(generics.param_at(i, tcx).def_id).instantiate(tcx, args).skip_normalization();
            let actual = const_type(tcx, c, owner, n + 1)?;
            if tcx.erase_and_anonymize_regions(expected) != tcx.erase_and_anonymize_regions(actual) {
                return Err(KeyError("template key const argument type"));
            }
        }
    }
    Ok(args)
}

fn const_type<'tcx>(tcx: TyCtxt<'tcx>, key: &KeyConst, owner: DefId, n: usize) -> Result<ty::Ty<'tcx>> {
    depth(n)?;
    match key {
        KeyConst::Value { ty, .. } => rebuild_type(tcx, ty, owner, n + 1),
        KeyConst::Param(p) => {
            let def = param(tcx, owner, *p)?;
            if !matches!(def.kind, ty::GenericParamDefKind::Const { .. }) {
                return Err(KeyError("template key parameter is not a const"));
            }
            Ok(tcx.type_of(def.def_id).instantiate_identity().skip_normalization())
        }
    }
}

fn rebuild_const<'tcx>(tcx: TyCtxt<'tcx>, key: &KeyConst, owner: DefId, n: usize) -> Result<ty::Const<'tcx>> {
    depth(n)?;
    Ok(match key {
        KeyConst::Param(p) => {
            let def = param(tcx, owner, *p)?;
            if !matches!(def.kind, ty::GenericParamDefKind::Const { .. }) {
                return Err(KeyError("template key parameter is not a const"));
            }
            ty::Const::new_param(tcx, ty::ParamConst { index: *p, name: def.name })
        }
        KeyConst::Value { bits, bytes, ty } => {
            super::scalar(*bits, *bytes, ty)?;
            if matches!(**ty, KeyTy::Int(0) | KeyTy::Uint(0))
                && u64::from(*bytes) != tcx.data_layout.pointer_size().bytes()
            { return Err(KeyError("template key target-sized const width")); }
            let ty = rebuild_type(tcx, ty, owner, n + 1)?;
            let bits = rustc_middle::ty::ScalarInt::try_from_uint(*bits, rustc_abi::Size::from_bytes(*bytes))
                .ok_or(KeyError("template key scalar reconstruction"))?;
            ty::Const::new_value(tcx, ty::ValTree::from_scalar_int(tcx, bits), ty)
        }
    })
}

fn rebuild_type<'tcx>(tcx: TyCtxt<'tcx>, key: &KeyTy, owner: DefId, n: usize) -> Result<ty::Ty<'tcx>> {
    depth(n)?;
    Ok(match key {
        KeyTy::Bool => tcx.types.bool, KeyTy::Char => tcx.types.char,
        KeyTy::Str => tcx.types.str_, KeyTy::Never => tcx.types.never,
        KeyTy::Int(i) => ty::Ty::new_int(tcx, match i {
            0 => ty::IntTy::Isize, 8 => ty::IntTy::I8, 16 => ty::IntTy::I16,
            32 => ty::IntTy::I32, 64 => ty::IntTy::I64, 128 => ty::IntTy::I128,
            _ => return Err(KeyError("template key signed integer width")),
        }),
        KeyTy::Uint(i) => ty::Ty::new_uint(tcx, match i {
            0 => ty::UintTy::Usize, 8 => ty::UintTy::U8, 16 => ty::UintTy::U16,
            32 => ty::UintTy::U32, 64 => ty::UintTy::U64, 128 => ty::UintTy::U128,
            _ => return Err(KeyError("template key unsigned integer width")),
        }),
        KeyTy::Float(i) => ty::Ty::new_float(tcx, match i {
            16 => ty::FloatTy::F16, 32 => ty::FloatTy::F32, 64 => ty::FloatTy::F64,
            128 => ty::FloatTy::F128, _ => return Err(KeyError("template key floating-point width")),
        }),
        KeyTy::Param(index) => {
            let def = param(tcx, owner, *index)?;
            if !matches!(def.kind, ty::GenericParamDefKind::Type { .. }) {
                return Err(KeyError("template key parameter is not a type"));
            }
            ty::Ty::new_param(tcx, *index, def.name)
        }
        KeyTy::Adt(item, keys) => {
            let item = definition(tcx, *item)?;
            if !matches!(tcx.def_kind(item), DefKind::Struct | DefKind::Enum | DefKind::Union) {
                return Err(KeyError("template key nominal definition is not an ADT"));
            }
            ty::Ty::new_adt(tcx, tcx.adt_def(item), rebuild_args(tcx, item, keys, owner, n + 1)?)
        }
        KeyTy::FnDef(item, keys) => {
            let item = definition(tcx, *item)?;
            if !matches!(tcx.def_kind(item), DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(_, CtorKind::Fn)) {
                return Err(KeyError("template key function-item definition kind"));
            }
            ty::Ty::new_fn_def(tcx, item, ty::Binder::dummy(rebuild_args(tcx, item, keys, owner, n + 1)?))
        }
        KeyTy::Closure(item, keys) => {
            let item = definition(tcx, *item)?;
            if tcx.def_kind(item) != DefKind::Closure
                || !matches!(tcx.type_of(item).instantiate_identity().skip_normalization().kind(), ty::Closure(..))
            { return Err(KeyError("template key ordinary closure definition kind")); }
            let args = rebuild_args(tcx, item, keys, owner, n + 1)?;
            let parent = tcx.generics_of(item).parent_count;
            if args.len() != parent + 3 { return Err(KeyError("template key closure synthetic arity")); }
            let kind = args[parent].as_type().ok_or(KeyError("template key closure kind slot"))?;
            if !matches!(kind.kind(), ty::Int(ty::IntTy::I8 | ty::IntTy::I16 | ty::IntTy::I32)) {
                return Err(KeyError("template key closure kind"));
            }
            let sig = args[parent + 1].as_type().ok_or(KeyError("template key closure signature slot"))?;
            let ty::FnPtr(types, header) = sig.kind() else { return Err(KeyError("template key closure signature type")); };
            let types = types.skip_binder();
            if header.abi() != rustc_abi::ExternAbi::RustCall || !header.safety().is_safe()
                || header.c_variadic() || header.fn_sig_kind.splatted().is_some()
                || types.inputs_and_output.len() != 2 || !matches!(types.inputs_and_output[0].kind(), ty::Tuple(_))
            { return Err(KeyError("template key closure tupled signature")); }
            let captures = args[parent + 2].as_type().ok_or(KeyError("template key closure capture slot"))?;
            if !matches!(captures.kind(), ty::Tuple(_)) { return Err(KeyError("template key closure capture tuple")); }
            ty::Ty::new_closure(tcx, item, args)
        }
        KeyTy::Ref { mutable, pointee } => ty::Ty::new_ref(tcx, tcx.lifetimes.re_erased,
            rebuild_type(tcx, pointee, owner, n + 1)?, if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not }),
        KeyTy::RawPtr { mutable, pointee } => ty::Ty::new_ptr(tcx,
            rebuild_type(tcx, pointee, owner, n + 1)?, if *mutable { ty::Mutability::Mut } else { ty::Mutability::Not }),
        KeyTy::Slice(t) => ty::Ty::new_slice(tcx, rebuild_type(tcx, t, owner, n + 1)?),
        KeyTy::Array(t, c) => {
            if const_type(tcx, c, owner, n + 1)? != tcx.types.usize {
                return Err(KeyError("template key array length is not usize"));
            }
            ty::Ty::new_array_with_const_len(tcx,
                rebuild_type(tcx, t, owner, n + 1)?, rebuild_const(tcx, c, owner, n + 1)?)
        },
        KeyTy::Tuple(ts) => ty::Ty::new_tup(tcx,
            &ts.iter().map(|t| rebuild_type(tcx, t, owner, n + 1)).collect::<Result<Vec<_>>>()?),
        KeyTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted } => {
            let parsed_abi: rustc_abi::ExternAbi = abi.parse().map_err(|_| KeyError("template key function ABI"))?;
            if parsed_abi.as_str() != abi {
                return Err(KeyError("template key noncanonical ABI name"));
            }
            let count = inputs_and_output.len().checked_sub(1).ok_or(KeyError("template key missing function output"))?;
            let kind = ty::FnSigKind::new(parsed_abi, if *safe { rustc_hir::Safety::Safe } else { rustc_hir::Safety::Unsafe },
                *c_variadic, *splatted, count).map_err(|_| KeyError("template key function header"))?;
            let tys = inputs_and_output.iter().map(|t| rebuild_type(tcx, t, owner, n + 1)).collect::<Result<Vec<_>>>()?;
            ty::Ty::new_fn_ptr(tcx, ty::Binder::dummy(ty::FnSig { inputs_and_output: tcx.mk_type_list(&tys), fn_sig_kind: kind }))
        }
        KeyTy::Projection { item, args, rigid } => {
            let item = definition(tcx, *item)?;
            if tcx.def_kind(item) != DefKind::AssocTy || tcx.trait_of_assoc(item).is_none() {
                return Err(KeyError("template key projection definition kind"));
            }
            let alias = ty::AliasTy::new_from_args(tcx, ty::AliasTyKind::Projection { def_id: item },
                rebuild_args(tcx, item, args, owner, n + 1)?);
            ty::Ty::new_alias(tcx, if *rigid { ty::IsRigid::Yes } else { ty::IsRigid::No }, alias)
        }
        KeyTy::Foreign(item) => {
            let item = definition(tcx, *item)?;
            if tcx.def_kind(item) != DefKind::ForeignTy { return Err(KeyError("template key foreign definition kind")); }
            ty::Ty::new_foreign(tcx, item)
        }
    })
}
