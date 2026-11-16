//! Read-only recovery of the complete version-1 legacy concrete-callee key.
//!
//! The wire is the unchanged `lineage::ConcreteCalleeKey::symbol_suffix`, not
//! a display name or a signature. Parsing grants no admission or codegen
//! authority. Rustc metadata must independently identify every nominal owner;
//! a real resolved Item must re-encode to the complete original suffix.
//! Regions are reconstructed only where the legacy format explicitly erased
//! them. No MIR body, inventory, native symbol, or invented value is an input.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};

use crate::{
    SiteArg, SiteClosureKind, SiteConst, SiteExistentialPredicate, SiteTerm, SiteTy, SiteValTree,
};

mod resolve;

const MAX_BYTES: usize = 1 << 20;
const MAX_NODES: usize = 1 << 16;
const MAX_DEPTH: usize = 128;
type StableDef = (u64, u64);
type Result<T> = std::result::Result<T, SiteError>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SiteError(pub &'static str);

impl std::fmt::Display for SiteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for SiteError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InstanceKind {
    Item,
    ReifyShim,
}

struct Decoded {
    definition: DefId,
    kind: InstanceKind,
    args: Vec<SiteArg>,
}

/// Actual Rustc identity and original positional reconstruction data only.
/// This is deliberately not an admission token, backend handle or proof grade.
pub struct RecoveredSite<'tcx> {
    instance: ty::Instance<'tcx>,
    args: Vec<SiteArg>,
}

impl<'tcx> RecoveredSite<'tcx> {
    pub fn instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }
    pub fn site_args(&self) -> &[SiteArg] {
        &self.args
    }
}

/// Recover a plain Item through loaded Rust metadata and exact re-encoding.
/// Runtime callable/borrow/capture/drop adapters are not supplied by recovery.
pub fn recover<'tcx>(tcx: TyCtxt<'tcx>, suffix: &str) -> Result<RecoveredSite<'tcx>> {
    recover_with_definition(tcx, suffix, |identity| {
        crate::template_key::rustc::definition(tcx, identity)
            .map_err(|_| SiteError("legacy site definition absent from loaded Rust metadata"))
    })
}

/// Recovery with a caller's identity lookup, still without an admission token.
/// The sealed upstream importer uses its own independently checked Rustc lookup
/// here, so every nominal identity in the complete key crosses that boundary.
pub fn recover_with_definition<'tcx>(
    tcx: TyCtxt<'tcx>,
    suffix: &str,
    mut definition: impl FnMut(StableDef) -> Result<DefId>,
) -> Result<RecoveredSite<'tcx>> {
    let decoded = decode(suffix, &mut definition)?;
    resolve::recover(tcx, suffix, decoded)
}

/// Spell a real Item using the existing canonical encoder, without admission.
/// Useful when comparing a retained site against independently obtained Rustc
/// identity; no signature or display path substitutes for generic arguments.
pub fn canonical_suffix<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> Result<String> {
    let ty::InstanceKind::Item(definition) = instance.def else {
        return Err(SiteError("legacy site runtime adapter is not a plain Item"));
    };
    let args = crate::encode_site_args(tcx, instance.args)
        .ok_or(SiteError("resolved legacy site arguments are not encodable"))?;
    Ok(crate::lineage::ConcreteCalleeKey::from_site_args(
        tcx,
        definition,
        crate::lineage::ConcreteInstanceKind::Item,
        &args,
    )
    .symbol_suffix())
}

fn decode(
    suffix: &str,
    definition: &mut impl FnMut(StableDef) -> Result<DefId>,
) -> Result<Decoded> {
    if suffix.len() < 52 || suffix.len() % 2 != 0 || suffix.len() > MAX_BYTES * 2 {
        return Err(SiteError("legacy site byte budget or hex length"));
    }
    fn nibble(byte: u8) -> Result<u8> {
        match byte {
            b'0'..=b'9' => Ok(byte - b'0'),
            b'a'..=b'f' => Ok(byte - b'a' + 10),
            _ => Err(SiteError("legacy site noncanonical hex")),
        }
    }
    let mut bytes = Vec::with_capacity(suffix.len() / 2);
    for pair in suffix.as_bytes().chunks_exact(2) {
        bytes.push((nibble(pair[0])? << 4) | nibble(pair[1])?);
    }
    let mut reader = Reader { bytes: &bytes, cursor: 0, nodes: 0, reserved: 0, definition };
    if reader.byte()? != 1 {
        return Err(SiteError("legacy site version"));
    }
    let definition = reader.definition()?;
    let kind = match reader.byte()? {
        0 => InstanceKind::Item,
        1 => InstanceKind::ReifyShim,
        _ => return Err(SiteError("legacy site instance kind")),
    };
    let args = reader.args(0, false)?;
    if reader.cursor != bytes.len() {
        return Err(SiteError("legacy site trailing bytes"));
    }
    Ok(Decoded { definition, kind, args })
}

struct Reader<'a, F> {
    bytes: &'a [u8],
    cursor: usize,
    nodes: usize,
    reserved: usize,
    definition: &'a mut F,
}

impl<F: FnMut(StableDef) -> Result<DefId>> Reader<'_, F> {
    fn take(&mut self, count: usize) -> Result<&[u8]> {
        let end = self.cursor.checked_add(count).ok_or(SiteError("legacy site offset overflow"))?;
        let bytes = self.bytes.get(self.cursor..end).ok_or(SiteError("legacy site truncated"))?;
        self.cursor = end;
        Ok(bytes)
    }
    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }
    fn u64(&mut self) -> Result<u64> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn bool(&mut self) -> Result<bool> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(SiteError("legacy site boolean")),
        }
    }
    fn node(&mut self, depth: usize) -> Result<()> {
        if depth > MAX_DEPTH {
            return Err(SiteError("legacy site depth budget"));
        }
        self.nodes += 1;
        if self.nodes > MAX_NODES {
            return Err(SiteError("legacy site node budget"));
        }
        Ok(())
    }
    fn count(&mut self) -> Result<usize> {
        let count =
            usize::try_from(self.u64()?).map_err(|_| SiteError("legacy site count overflow"))?;
        self.reserved =
            self.reserved.checked_add(count).ok_or(SiteError("legacy site allocation overflow"))?;
        if self.reserved > MAX_NODES || count > self.bytes.len() - self.cursor {
            return Err(SiteError("legacy site allocation budget"));
        }
        Ok(count)
    }
    fn string(&mut self) -> Result<String> {
        let len =
            usize::try_from(self.u64()?).map_err(|_| SiteError("legacy site string overflow"))?;
        let text =
            std::str::from_utf8(self.take(len)?).map_err(|_| SiteError("legacy site UTF-8"))?;
        Ok(text.to_owned())
    }
    fn definition(&mut self) -> Result<DefId> {
        let stable = (self.u64()?, self.u64()?);
        (self.definition)(stable)
    }
    fn args(&mut self, depth: usize, marked: bool) -> Result<Vec<SiteArg>> {
        self.node(depth)?;
        let count = self.count()?;
        let mut args = Vec::with_capacity(count);
        for _ in 0..count {
            self.node(depth + 1)?;
            let tag = self.byte()?;
            args.push(if marked {
                match tag {
                    12 => SiteArg::ErasedRegion,
                    13 => SiteArg::Const(self.konst(depth + 2)?),
                    tag => SiteArg::Ty(self.ty_tag(depth + 2, tag)?),
                }
            } else {
                match tag {
                    0 => SiteArg::ErasedRegion,
                    1 => SiteArg::Ty(self.ty(depth + 2)?),
                    2 => SiteArg::Const(self.konst(depth + 2)?),
                    _ => return Err(SiteError("legacy site generic argument kind")),
                }
            });
        }
        Ok(args)
    }
    fn konst(&mut self, depth: usize) -> Result<SiteConst> {
        self.node(depth)?;
        Ok(SiteConst::Value(self.ty(depth + 1)?, self.tree(depth + 1)?))
    }
    fn tree(&mut self, depth: usize) -> Result<SiteValTree> {
        self.node(depth)?;
        match self.byte()? {
            0 => {
                let bits = u128::from_be_bytes(self.take(16)?.try_into().unwrap());
                let size = self.u64()?;
                if !(1..=16).contains(&size) || (size < 16 && bits >> (size * 8) != 0) {
                    return Err(SiteError("legacy site scalar bits/width"));
                }
                Ok(SiteValTree::Leaf(bits, size))
            }
            1 => {
                let count = self.count()?;
                let mut values = Vec::with_capacity(count);
                for _ in 0..count {
                    values.push(self.konst(depth + 1)?);
                }
                Ok(SiteValTree::Branch(values))
            }
            _ => Err(SiteError("legacy site valtree kind")),
        }
    }
    fn ty(&mut self, depth: usize) -> Result<SiteTy> {
        let tag = self.byte()?;
        self.ty_tag(depth, tag)
    }
    fn ty_tag(&mut self, depth: usize, tag: u8) -> Result<SiteTy> {
        self.node(depth)?;
        Ok(match tag {
            0 => SiteTy::Bool,
            1 => SiteTy::Char,
            2 => SiteTy::Str,
            18 => SiteTy::Never,
            3 => SiteTy::Int(match self.string()?.as_str() {
                "isize" => ty::IntTy::Isize,
                "i8" => ty::IntTy::I8,
                "i16" => ty::IntTy::I16,
                "i32" => ty::IntTy::I32,
                "i64" => ty::IntTy::I64,
                "i128" => ty::IntTy::I128,
                _ => return Err(SiteError("legacy site signed integer spelling")),
            }),
            4 => SiteTy::Uint(match self.string()?.as_str() {
                "usize" => ty::UintTy::Usize,
                "u8" => ty::UintTy::U8,
                "u16" => ty::UintTy::U16,
                "u32" => ty::UintTy::U32,
                "u64" => ty::UintTy::U64,
                "u128" => ty::UintTy::U128,
                _ => return Err(SiteError("legacy site unsigned integer spelling")),
            }),
            5 => SiteTy::Float(match self.string()?.as_str() {
                "f16" => ty::FloatTy::F16,
                "f32" => ty::FloatTy::F32,
                "f64" => ty::FloatTy::F64,
                "f128" => ty::FloatTy::F128,
                _ => return Err(SiteError("legacy site float spelling")),
            }),
            6 => SiteTy::Adt(self.definition()?, self.args(depth + 1, true)?),
            7 => {
                let count = self.count()?;
                let mut values = Vec::with_capacity(count);
                for _ in 0..count {
                    values.push(self.ty(depth + 1)?);
                }
                SiteTy::Tuple(values)
            }
            8 => SiteTy::Array(Box::new(self.ty(depth + 1)?), self.u64()?),
            9 => SiteTy::Slice(Box::new(self.ty(depth + 1)?)),
            10 | 11 => {
                let mutable = if self.bool()? { ty::Mutability::Mut } else { ty::Mutability::Not };
                let pointee = Box::new(self.ty(depth + 1)?);
                if tag == 10 {
                    SiteTy::Ref(pointee, mutable)
                } else {
                    SiteTy::RawPtr(pointee, mutable)
                }
            }
            14 => SiteTy::FnDef(self.definition()?, self.args(depth + 1, true)?),
            15 => {
                let abi = self.string()?;
                let parsed: rustc_abi::ExternAbi =
                    abi.parse().map_err(|_| SiteError("legacy site function ABI"))?;
                if parsed.as_str() != abi {
                    return Err(SiteError("legacy site noncanonical ABI"));
                }
                let safe = self.bool()?;
                let c_variadic = self.bool()?;
                let splatted = if self.bool()? { Some(self.byte()?) } else { None };
                let count = self.count()?;
                let arity =
                    count.checked_sub(1).ok_or(SiteError("legacy site missing function result"))?;
                ty::FnSigKind::new(
                    parsed,
                    if safe { rustc_hir::Safety::Safe } else { rustc_hir::Safety::Unsafe },
                    c_variadic,
                    splatted,
                    arity,
                )
                .map_err(|_| SiteError("legacy site function header"))?;
                let mut inputs_and_output = Vec::with_capacity(count);
                for _ in 0..count {
                    inputs_and_output.push(self.ty(depth + 1)?);
                }
                SiteTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted }
            }
            16 => {
                let kind = match self.byte()? {
                    0 => SiteClosureKind::Closure,
                    1 => SiteClosureKind::CoroutineClosure,
                    2 => SiteClosureKind::Coroutine,
                    3 => SiteClosureKind::CoroutineWitness,
                    _ => return Err(SiteError("legacy site closure kind")),
                };
                SiteTy::ClosureLike(kind, self.definition()?, self.args(depth + 1, true)?)
            }
            17 => {
                let count = self.count()?;
                let mut predicates = Vec::with_capacity(count);
                for _ in 0..count {
                    self.node(depth + 1)?;
                    predicates.push(match self.byte()? {
                        0 => SiteExistentialPredicate::Trait(
                            self.definition()?,
                            self.args(depth + 2, false)?,
                        ),
                        1 => {
                            let owner = self.definition()?;
                            let args = self.args(depth + 2, false)?;
                            let term = match self.byte()? {
                                0 => SiteTerm::Ty(self.ty(depth + 2)?),
                                1 => SiteTerm::Const(self.konst(depth + 2)?),
                                _ => return Err(SiteError("legacy site existential term")),
                            };
                            SiteExistentialPredicate::Projection(owner, args, Box::new(term))
                        }
                        2 => SiteExistentialPredicate::AutoTrait(self.definition()?),
                        _ => return Err(SiteError("legacy site existential predicate")),
                    });
                }
                SiteTy::Dynamic(predicates)
            }
            19 => SiteTy::Foreign(self.definition()?),
            _ => return Err(SiteError("legacy site type discriminator")),
        })
    }
}

#[cfg(test)]
mod tests;
