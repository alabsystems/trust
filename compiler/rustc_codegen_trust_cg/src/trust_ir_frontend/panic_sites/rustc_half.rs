//! Trust (PKG-CP, R-8 item P): the rustc half of the panic-site pass — what rustc says a failed
//! check calls and where it reports itself. Everything here is read from rustc, never assumed:
//!
//! * the ENTRY is the kind's `core` lang item (`panic_const_add_overflow`, `panic_bounds_check`,
//!   ...), named by `tcx.symbol_name`, and admitted only when its `FnAbi` is what the sited
//!   lowering passes: the Rust ABI, not variadic, not unwinding, one 64-bit integer register per
//!   kind operand and then the pointer `#[track_caller]` appends, returning `!`;
//! * the LOCATION is the `core::panic::Location` rustc's own const-eval builds for the check's
//!   span (`TyCtxt::span_as_caller_location`, the query LLVM's backend uses for the same MIR
//!   `Assert`), read back byte for byte from its interned allocation, with each pointer as a
//!   `SymbolAddr` to the allocation it points to. Both allocations are named as rustc's LLVM
//!   backend names a constant allocation, `alloc_<stable hash>`.
//!
//! The span is the producer's stamp (file, line, 0-based char column) resolved back to a
//! position by `trust_thir_lower::to_mir::rustc_span_of` and checked to round-trip. The
//! producer stamps `span.source_callsite()`, while rustc reports
//! `span.ctxt().outer_expn().expansion_cause()`, and the two can differ (an `include!`
//! expansion is where `expansion_cause` stops). So no stamp is trusted on its own: the
//! ORACLE ([`Resolver::matches_rustc_mir`]) requires each sited check of a body to match a
//! distinct `Assert` terminator of rustc's own MIR for that instance, by lang item and by the
//! location record rustc computes from the MIR span, which is what LLVM's backend passes.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use rustc_abi::{BackendRepr, CanonAbi, Primitive, Size};
use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::stable_hash::{
    FromStableHash, StableHash, StableHasher, StableHasherHash,
};
use rustc_hir::def::DefKind;
use rustc_middle::mir::{self, ConstValue};
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar, alloc_range};
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use rustc_target::callconv::PassMode;
use trust_ir::value::SourceSpan;
use trust_ir::{AssertKind, AssertOverflowOp, Constant, Module};

use super::{DataImage, LocationRecord, Resolver, SitingReport};

/// Fold and site the checks of `m_cg` with what `tcx` says (see the parent module).
pub(crate) fn site_codegen_module(tcx: TyCtxt<'_>, m_cg: &mut Module) -> SitingReport {
    let mut resolver = RustcResolver {
        tcx,
        entries: BTreeMap::new(),
        owners: None,
        names: BTreeMap::new(),
    };
    super::site(m_cg, &mut resolver)
}

struct RustcResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    entries: BTreeMap<&'static str, Result<String, String>>,
    /// Each known body symbol and its instance.
    owners: Option<BTreeMap<String, ty::Instance<'tcx>>>,
    names: BTreeMap<AllocId, String>,
}

/// The lang item a failed check of `kind` calls (MIR `AssertKind::panic_function`).
fn lang_item(kind: &AssertKind) -> Option<LangItem> {
    Some(match kind {
        AssertKind::Overflow(op) => match op {
            AssertOverflowOp::Add => LangItem::PanicAddOverflow,
            AssertOverflowOp::Sub => LangItem::PanicSubOverflow,
            AssertOverflowOp::Mul => LangItem::PanicMulOverflow,
            AssertOverflowOp::Div => LangItem::PanicDivOverflow,
            AssertOverflowOp::Rem => LangItem::PanicRemOverflow,
            AssertOverflowOp::Shl => LangItem::PanicShlOverflow,
            AssertOverflowOp::Shr => LangItem::PanicShrOverflow,
            AssertOverflowOp::Neg => LangItem::PanicNegOverflow,
        },
        AssertKind::DivByZero => LangItem::PanicDivZero,
        AssertKind::RemByZero => LangItem::PanicRemZero,
        AssertKind::BoundsCheck { .. } => LangItem::PanicBoundsCheck,
        AssertKind::MisalignedPtr { .. } => LangItem::PanicMisalignedPointerDereference,
        AssertKind::NullPtr => LangItem::PanicNullPointerDereference,
        AssertKind::Unspecified => return None,
    })
}

/// The lang item a MIR `Assert` calls when it fails, as LLVM's backend lowers it
/// (`rustc_codegen_ssa` `codegen_assert_terminator`); `None` for a kind no trust-ir check has.
fn mir_lang_item<O>(msg: &mir::AssertKind<O>) -> Option<LangItem> {
    use rustc_middle::mir::BinOp;
    Some(match msg {
        mir::AssertKind::BoundsCheck { .. } => LangItem::PanicBoundsCheck,
        mir::AssertKind::MisalignedPointerDereference { .. } => {
            LangItem::PanicMisalignedPointerDereference
        }
        mir::AssertKind::Overflow(
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr,
            ..,
        )
        | mir::AssertKind::OverflowNeg(_)
        | mir::AssertKind::DivisionByZero(_)
        | mir::AssertKind::RemainderByZero(_)
        | mir::AssertKind::NullPointerDereference => msg.panic_function(),
        _ => return None,
    })
}

/// The name rustc's LLVM backend gives a constant allocation (`rustc_codegen_llvm`
/// `scalar_to_backend`): `alloc_` and the allocation's 128-bit stable hash.
struct AllocHash(u128);

impl FromStableHash for AllocHash {
    type Hash = StableHasherHash;

    fn from(StableHasherHash([low, high]): Self::Hash) -> Self {
        AllocHash(u128::from(low) | (u128::from(high) << 64))
    }
}

impl<'tcx> RustcResolver<'tcx> {
    fn owners(&mut self) -> &BTreeMap<String, ty::Instance<'tcx>> {
        let tcx = self.tcx;
        self.owners.get_or_insert_with(|| {
            let mut owners = BTreeMap::new();
            for cgu in tcx.collect_and_partition_mono_items(()).codegen_units {
                for item in cgu.items().keys() {
                    if let MonoItem::Fn(instance) = *item {
                        owners.insert(tcx.symbol_name(instance).name.to_string(), instance);
                    }
                }
            }
            // A local non-generic body the inventory does not name (inventory residue).
            for owner in tcx.hir_body_owners() {
                if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
                    || tcx.generics_of(owner).requires_monomorphization(tcx)
                {
                    continue;
                }
                let instance = ty::Instance::mono(tcx, owner.to_def_id());
                owners.entry(tcx.symbol_name(instance).name.to_string()).or_insert(instance);
            }
            owners
        })
    }

    fn alloc_name(&mut self, id: AllocId) -> Result<String, String> {
        if let Some(name) = self.names.get(&id) {
            return Ok(name.clone());
        }
        let tcx = self.tcx;
        let GlobalAlloc::Memory(alloc) = tcx.global_alloc(id) else {
            return Err(format!("{id:?} is not a memory allocation"));
        };
        let hash: AllocHash = tcx.with_stable_hashing_context(|mut hcx| {
            let mut hasher = StableHasher::new();
            alloc.inner().stable_hash(&mut hcx, &mut hasher);
            hasher.finish()
        });
        let name = format!("alloc_{:032x}", hash.0);
        self.names.insert(id, name.clone());
        Ok(name)
    }

    /// The allocation `id` as a flat image, and the allocations its pointers name.
    fn image(&mut self, id: AllocId) -> Result<(DataImage, Vec<AllocId>), String> {
        let tcx = self.tcx;
        if !tcx.data_layout.endian.eq(&rustc_abi::Endian::Little) {
            return Err("the target is not little-endian".into());
        }
        let GlobalAlloc::Memory(alloc) = tcx.global_alloc(id) else {
            return Err(format!("{id:?} is not a memory allocation"));
        };
        let inner = alloc.inner();
        if inner.mutability.is_mut() {
            return Err(format!("{id:?} is mutable"));
        }
        inner
            .init_mask()
            .is_range_initialized(alloc_range(Size::ZERO, inner.size()))
            .map_err(|range| format!("{id:?} has uninitialized bytes at {range:?}"))?;
        let ptrs = inner.provenance().ptrs();
        if inner.provenance().provenances().count() != ptrs.len() {
            return Err(format!("{id:?} carries a partial pointer"));
        }
        let pointer = tcx.data_layout.pointer_size().bytes_usize();
        let size = inner.size().bytes_usize();
        let bytes = inner.inspect_with_uninit_and_ptr_outside_interpreter(0..size);
        let mut elements = Vec::with_capacity(size);
        let mut pointees = Vec::new();
        let mut at = 0;
        while at < size {
            if let Some(prov) = ptrs.get(&Size::from_bytes(at)) {
                let word = bytes
                    .get(at..at + pointer)
                    .ok_or_else(|| format!("{id:?} has a pointer past its end"))?;
                let mut addend = [0u8; 8];
                addend[..pointer].copy_from_slice(word);
                let addend = i64::from_le_bytes(addend);
                let pointee = prov.alloc_id();
                elements.push(Constant::SymbolAddr { symbol: self.alloc_name(pointee)?, addend });
                pointees.push(pointee);
                at += pointer;
            } else {
                elements.push(Constant::Int(i128::from(bytes[at])));
                at += 1;
            }
        }
        let align = u32::try_from(inner.align.bytes())
            .map_err(|_| format!("{id:?} has an alignment beyond u32"))?;
        Ok((DataImage { symbol: self.alloc_name(id)?, align, elements }, pointees))
    }
}

impl<'tcx> Resolver for RustcResolver<'tcx> {
    fn entry(&mut self, kind: &AssertKind) -> Result<String, String> {
        let Some(item) = lang_item(kind) else {
            return Err(format!("the `{}` kind names no Rust panic", kind.keyword()));
        };
        let rustc_name = item.name();
        let Some(name) = kind.rust_panic_lang_item().filter(|n| *n == rustc_name.as_str()) else {
            return Err(format!(
                "trust-ir names `{:?}` for this kind, rustc `{rustc_name}`",
                kind.rust_panic_lang_item()
            ));
        };
        if let Some(answer) = self.entries.get(name) {
            return answer.clone();
        }
        let tcx = self.tcx;
        let operands = kind.operand_count();
        let answer = (|| {
            let def_id = tcx
                .lang_items()
                .get(item)
                .ok_or_else(|| format!("the lang item `{name}` is missing"))?;
            if tcx.generics_of(def_id).requires_monomorphization(tcx) {
                return Err(format!("`{name}` is generic"));
            }
            let instance = ty::Instance::mono(tcx, def_id);
            if !instance.def.requires_caller_location(tcx) {
                return Err(format!("`{name}` does not take a caller location"));
            }
            let typing_env = ty::TypingEnv::fully_monomorphized();
            let sig = instance.ty(tcx, typing_env).fn_sig(tcx).skip_binder();
            if sig.inputs().len() != operands
                || sig.inputs().iter().any(|input| *input != tcx.types.usize)
                || !sig.output().is_never()
            {
                return Err(format!(
                    "`{name}` is not `fn({}) -> !`",
                    vec!["usize"; operands].join(", ")
                ));
            }
            let fn_abi = tcx
                .fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))
                .map_err(|error| format!("rustc's FnAbi for `{name}` failed: {error:?}"))?;
            if fn_abi.conv != CanonAbi::Rust || fn_abi.c_variadic || fn_abi.can_unwind {
                return Err(format!(
                    "`{name}` is not a non-variadic, non-unwinding Rust-ABI function (an \
                     unwinding panic entry is not lowered faithfully on this lane)"
                ));
            }
            if fn_abi.args.len() != operands + 1 {
                return Err(format!(
                    "`{name}`'s FnAbi passes {} argument(s), not its {operands} operand(s) and \
                     the caller location",
                    fn_abi.args.len()
                ));
            }
            for (index, arg) in fn_abi.args.iter().enumerate() {
                let scalar = match (&arg.mode, arg.layout.backend_repr) {
                    (PassMode::Direct(_), BackendRepr::Scalar(scalar)) => scalar.primitive(),
                    _ => return Err(format!("`{name}`'s argument {index} is not a direct scalar")),
                };
                let ok = if index < operands {
                    matches!(scalar, Primitive::Int(rustc_abi::Integer::I64, false))
                } else {
                    matches!(scalar, Primitive::Pointer(_))
                        && arg.layout.size == tcx.data_layout.pointer_size()
                };
                if !ok {
                    return Err(format!("`{name}`'s argument {index} is `{scalar:?}`"));
                }
            }
            if !matches!(fn_abi.ret.mode, PassMode::Ignore) {
                return Err(format!("`{name}` returns a value"));
            }
            Ok(tcx.symbol_name(instance).name.to_string())
        })();
        self.entries.insert(name, answer.clone());
        answer
    }

    fn location(&mut self, files: &[String], span: SourceSpan) -> Result<LocationRecord, String> {
        let tcx = self.tcx;
        let position = trust_thir_lower::to_mir::rustc_span_of(tcx, files, span).ok_or_else(|| {
            format!(
                "the stamp {}:{}:{} names no position in a file this session loaded",
                files.get(span.file as usize).map_or("<no file>", String::as_str),
                span.line,
                span.col
            )
        })?;
        let back = tcx.sess.source_map().lookup_char_pos(position.lo());
        if back.line != span.line as usize || back.col.0 != span.col as usize {
            return Err(format!(
                "the stamp {}:{} resolves to {}:{}",
                span.line, span.col, back.line, back.col.0
            ));
        }
        self.record_of(position)
    }

    fn reports_own_location(&mut self, symbol: &str) -> Result<(), String> {
        let tcx = self.tcx;
        match self.owners().get(symbol) {
            None => Err(format!("`{symbol}` is not a rustc instance of this compilation")),
            Some(instance) if instance.def.requires_caller_location(tcx) => Err(format!(
                "`{symbol}` is `#[track_caller]`: its checks report its caller's location, a \
                 run-time value"
            )),
            Some(_) => Ok(()),
        }
    }

    fn matches_rustc_mir(
        &mut self,
        symbol: &str,
        checks: &[(AssertKind, LocationRecord)],
    ) -> Result<(), String> {
        let tcx = self.tcx;
        let Some(instance) = self.owners().get(symbol).copied() else {
            return Err(format!("`{symbol}` is not a rustc instance of this compilation"));
        };
        let ty::InstanceKind::Item(def_id) = instance.def else {
            return Err(format!("`{symbol}` is a `{:?}` shim, not an item body", instance.def));
        };
        if !tcx.is_mir_available(def_id) {
            return Err(format!("rustc has no MIR for `{symbol}`"));
        }
        let body = tcx.instance_mir(instance.def);
        // Every MIR `Assert` LLVM would lower as its own: (lang item, location record).
        let mut unmatched: Vec<(rustc_span::Symbol, LocationRecord)> = Vec::new();
        for block in body.basic_blocks.iter() {
            let terminator = block.terminator();
            let mir::TerminatorKind::Assert { msg, .. } = &terminator.kind else { continue };
            // A check inlined from another body reports through that body's callsite chain.
            if terminator.source_info.scope.inlined_instance(&body.source_scopes).is_some() {
                continue;
            }
            let Some(item) = mir_lang_item(msg) else { continue };
            unmatched.push((item.name(), self.record_of(terminator.source_info.span)?));
        }
        for (kind, record) in checks {
            let Some(name) = kind.rust_panic_lang_item() else {
                return Err(format!("the `{}` kind names no Rust panic", kind.keyword()));
            };
            let Some(at) = unmatched.iter().position(|(n, r)| n.as_str() == name && r == record) else {
                return Err(format!(
                    "rustc's MIR for `{symbol}` has no unmatched `Assert` calling `{name}` at the \
                     location the producer stamped ({} MIR `Assert`(s) left)",
                    unmatched.len()
                ));
            };
            unmatched.swap_remove(at);
        }
        Ok(())
    }
}

impl<'tcx> RustcResolver<'tcx> {
    /// rustc's `core::panic::Location` record for `position`, imaged with the file name it
    /// points to.
    fn record_of(&mut self, position: Span) -> Result<LocationRecord, String> {
        let tcx = self.tcx;
        let ConstValue::Scalar(Scalar::Ptr(pointer, _)) = tcx.span_as_caller_location(position)
        else {
            return Err("rustc's caller location is not a pointer".into());
        };
        let (prov, offset) = pointer.into_raw_parts();
        if offset != Size::ZERO {
            return Err("rustc's caller location points into its allocation".into());
        }
        let (record, pointees) = self.image(prov.alloc_id())?;
        let [file_id] = pointees.as_slice() else {
            return Err(format!(
                "rustc's location record holds {} pointer(s), not one",
                pointees.len()
            ));
        };
        let (file, file_pointees) = self.image(*file_id)?;
        if !file_pointees.is_empty() {
            return Err("the location's file name holds a pointer".into());
        }
        if record.symbol == file.symbol {
            return Err("the location record and its file name share a name".into());
        }
        Ok(LocationRecord { record, file })
    }
}
