// trust_vcgen/ffi_pointer_contract.rs: documented return contracts of pointer-returning
// libc symbols, and the structural facts a body derives from them.
//
// THE PROBLEM (G1, 2026-10-27). An FFI call's result is a free variable: `ffi_vcgen`'s
// summaries have no assumption channel, and the separation engine names an untracked
// pointer `_N.*` with an unconstrained `ptr_`, `align_`, `heap` and `writable_`. So
// every dereference of `__error()` (errno save/restore in a signal handler) and of a
// null-checked `getpwuid()` result FAILED its `[unsafe:sep:deref]` rows, and rustc's
// own `CheckNull`/`CheckAlignment` asserts in front of the dereference were
// `UnmodeledSafetyAssert` (per-statement lane) and an unprovable hardened twin.
//
// WHAT THIS MODULE ADMITS, AND WHY EACH FACT IS TRUE:
//
// * [`POINTER_RETURN_CONTRACTS`] — one row per C symbol, each the documented guarantee
//   of that symbol (the citation is in the row and in docs/TCB.md). A row applies only
//   to a FOREIGN call (`is_foreign`, the compiler's `tcx.is_foreign_item`) whose
//   compiler-resolved `extern`-block leaf (`CalleeKey::foreign_block_leaf`) AND link
//   symbol (`CalleeKey::upstream_foreign_link_symbol`, `tcx.symbol_name`) are the
//   symbol, declared by an UPSTREAM crate named `libc` (see
//   [`CONTRACT_DECLARING_CRATE`]), with the documented arity, on a target the row holds
//   for ([`ContractPlatform`]), AND whose declared return type is the documented pointer
//   type: `*mut i32` for the errno slots, and for `getpwuid` a pointer to a STRUCT
//   whose field list — names, order and types, as the extractor presents the
//   declaring crate's Rust declaration — is Darwin's `struct passwd` exactly
//   ([`DARWIN_PASSWD`]; REVIEW-A4C4-MINORS-1). A Rust fn that merely shares the name is
//   not foreign; the program's own declaration, a `#[link_name]`-renamed one, a
//   declaration with another arity, and one whose pointee is another type (for
//   `getpwuid`: a `passwd` with a field added, dropped, renamed, reordered or retyped,
//   or a union) are refused. What the field list cannot show — a `repr` attribute that
//   changes the declared struct's size, alignment or member placement — is read off
//   rustc's computed layout of the declaration, which the COMPILER hands over for the
//   call's block (`VcgenContext::with_compiler_foreign_return_pointee_layouts`; the
//   verifying extractor never fills `Ty::Adt::layout`): it must be the C layout
//   exactly, and with no layout the row lends nothing (fix-forward, 2026-11-07).
// * A same-crate WRAPPER whose body returns such a call's result unchanged
//   ([`compute_return_ffi_pointer_summaries`]) lends the contract to its callers, only
//   for a contract valid for the thread's lifetime, and only at a call whose identity
//   reaches the summarized body (`call_reaches_summarized_body`).
// * A CONTRACT-ROOTED local is assigned exactly once in the body, as the whole
//   destination of such a call, and is never borrowed: every read of it reads the call
//   result.
// * Dominance facts over a contract-rooted local `L`, on normal (non-unwind) edges:
//   - non-null where the contract says so, or in a block dominated by the false edge
//     of `switchInt(L.is_null())` (the core `is_null`, authenticated as the real
//     sysroot), or by the success edge of an earlier rustc `CheckNull` assert on `L`;
//   - aligned to `K` in a block dominated by the success edge of a rustc
//     `CheckAlignment` assert on `L` with constant `K` — that assert was inserted for a
//     dereference of `L` itself, so `K` is `align_of` of `L`'s own pointee — or to the
//     contract's guaranteed alignment;
//   - valid (allocated, of the declared pointee type, at offset 0) where the contract's
//     validity window holds: for the thread's lifetime, or (`getpwuid`) until any call
//     other than the core `is_null` lies on a path from the call to the use.
//
// Every recognizer fails closed: an unrecognized shape, a second write, a borrow, an
// unknown terminator, or a missing compiler identity yields no fact, and the row keeps
// its existing (failing / unknown) obligation.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    AdtKind, AdtLayoutInfo, AssertMessage, BasicBlock, BinOp, ConstValue, Operand, Place,
    Projection, Rvalue, Statement, Terminator, Ty, UnOp, VerifiableFunction,
};

/// The documented pointee of a contract's returned pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractPointee {
    /// C `int`: a 4-byte, 4-aligned signed integer on every target Trust supports.
    CInt,
    /// A C struct with this EXACT member list ([`CStructLayout`]), which has at least
    /// one pointer member, so its alignment is at least the target's pointer width.
    CStruct(&'static CStructLayout),
}

/// The type of one C struct member, as the extractor presents the declaring crate's
/// Rust spelling of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CMember {
    /// `char *`, declared `*mut c_char`; `c_char` is `i8` on every Darwin target.
    MutCharPtr,
    /// A fixed-width integer (`uid_t`/`gid_t` = `u32`; LP64 `time_t` = `long` = `i64`).
    Int { width: u32, signed: bool },
}

impl CMember {
    fn matches(self, ty: &Ty) -> bool {
        match self {
            CMember::MutCharPtr => matches!(
                ty,
                Ty::RawPtr { mutable: true, pointee }
                    if matches!(**pointee, Ty::Int { width: 8, signed: true })
            ),
            CMember::Int { width, signed } => {
                matches!(ty, Ty::Int { width: w, signed: s } if *w == width && *s == signed)
            }
        }
    }
}

/// The exact shape of a documented C struct.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct CStructLayout {
    /// The struct tag; matched against the declared ADT's last path segment.
    pub(crate) name: &'static str,
    /// Every member, in declaration order: name and type.
    pub(crate) fields: &'static [(&'static str, CMember)],
    /// The C layout (bytes): size, alignment, and each member's offset in declaration
    /// order. rustc's computed layout of the declaration must equal it
    /// ([`PointerReturnContract::pointee_matches`]).
    pub(crate) size: u64,
    pub(crate) align: u64,
    pub(crate) offsets: &'static [u64],
}

/// Darwin's `struct passwd` (`<pwd.h>`, macOS SDK; libc 0.2.191
/// `src/unix/bsd/mod.rs`, whose `pw_fields` member is compiled out for
/// `target_vendor = "apple"`), on an LP64 Darwin target:
///
/// ```c
/// struct passwd {
///     char *pw_name; char *pw_passwd; uid_t pw_uid; gid_t pw_gid;
///     __darwin_time_t pw_change; char *pw_class; char *pw_gecos; char *pw_dir;
///     char *pw_shell; __darwin_time_t pw_expire;
/// };
/// ```
///
/// 72 bytes, 8-aligned, no padding. A 32-bit Darwin target (`time_t` is a 32-bit
/// `long` there) does not match, and gets no contract.
pub(crate) const DARWIN_PASSWD: CStructLayout = CStructLayout {
    name: "passwd",
    fields: &[
        ("pw_name", CMember::MutCharPtr),
        ("pw_passwd", CMember::MutCharPtr),
        ("pw_uid", CMember::Int { width: 32, signed: false }),
        ("pw_gid", CMember::Int { width: 32, signed: false }),
        ("pw_change", CMember::Int { width: 64, signed: true }),
        ("pw_class", CMember::MutCharPtr),
        ("pw_gecos", CMember::MutCharPtr),
        ("pw_dir", CMember::MutCharPtr),
        ("pw_shell", CMember::MutCharPtr),
        ("pw_expire", CMember::Int { width: 64, signed: true }),
    ],
    size: 72,
    align: 8,
    offsets: &[0, 8, 16, 20, 24, 32, 40, 48, 56, 64],
};

/// How long the returned pointer stays valid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractValidity {
    /// For the calling thread's lifetime (errno).
    ThreadLifetime,
    /// Until the next call that may reach the same storage. Modeled as: until ANY call
    /// other than the core `is_null` (see [`PointerFacts::valid_at`]).
    UntilNextCall,
}

/// The targets on which a contract row is the C library's documented behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractPlatform {
    /// Every target that links a C library defining the symbol: the row is the C
    /// standard's (or the symbol's own ABI document's) guarantee.
    Any,
    /// Only a Darwin target (`target.is_like_darwin`: macOS, iOS, tvOS, watchOS,
    /// visionOS), whose libSystem (Libinfo) behavior the row states. The compiler
    /// supplies the target bit ([`crate::VcgenContext::with_target_is_darwin`]); a
    /// missing context answers "not Darwin", which admits no such row.
    Darwin,
}

/// The documented return guarantee of one pointer-returning C symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PointerReturnContract {
    /// The C symbol: the LINK symbol the call must resolve to
    /// (`CalleeKey::upstream_foreign_link_symbol`), and the declaration's Rust name.
    pub(crate) symbol: &'static str,
    /// The documented number of parameters; a declaration with another arity is not
    /// this symbol's documented prototype and gets no contract.
    pub(crate) arity: usize,
    /// The targets on which the row holds.
    pub(crate) platform: ContractPlatform,
    /// Whether the documented result may be a null pointer.
    pub(crate) may_be_null: bool,
    /// The documented pointee type.
    pub(crate) pointee: ContractPointee,
    /// Whether the caller may write through the result.
    pub(crate) writable: bool,
    /// How long the result stays valid.
    pub(crate) validity: ContractValidity,
    /// The documented clause the row rests on (docs/TCB.md carries the same text).
    pub(crate) citation: &'static str,
}

/// The contracts. ONE ROW PER SYMBOL, each the symbol's documented guarantee; docs/TCB.md
/// "libc/Darwin pointer return-contract summaries" lists the same rows.
pub(crate) const POINTER_RETURN_CONTRACTS: &[PointerReturnContract] = &[
    PointerReturnContract {
        symbol: "__error",
        arity: 0,
        platform: ContractPlatform::Any,
        may_be_null: false,
        pointee: ContractPointee::CInt,
        writable: true,
        validity: ContractValidity::ThreadLifetime,
        citation: "Darwin/FreeBSD <sys/errno.h>: `#define errno (*__error())`; ISO C11 7.5p2: \
                   errno expands to a modifiable lvalue of type int with thread local \
                   storage duration",
    },
    PointerReturnContract {
        symbol: "__errno_location",
        arity: 0,
        platform: ContractPlatform::Any,
        may_be_null: false,
        pointee: ContractPointee::CInt,
        writable: true,
        validity: ContractValidity::ThreadLifetime,
        citation: "LSB Core `__errno_location`: returns the address of the errno variable \
                   for the current thread; glibc/musl <errno.h>: `#define errno \
                   (*__errno_location())`; ISO C11 7.5p2",
    },
    PointerReturnContract {
        symbol: "getpwuid",
        arity: 1,
        // POSIX lets a getpw* call from ANY thread overwrite the result, and glibc and
        // musl keep it in one process-wide static buffer (glibc may also reallocate
        // the string buffer it points into), so on those targets another thread's call
        // races with this thread's read and the until-next-call window below is not a
        // per-thread fact. Darwin's Libinfo keeps each thread's result in
        // thread-specific data (`LI_set_thread_item`), released only by that thread's
        // next lookup of the same kind: there the window is per thread.
        platform: ContractPlatform::Darwin,
        may_be_null: true,
        pointee: ContractPointee::CStruct(&DARWIN_PASSWD),
        writable: false,
        validity: ContractValidity::UntilNextCall,
        citation: "POSIX.1-2024 getpwuid: returns a pointer to a struct passwd, or a null \
                   pointer; the application shall not modify the structure; the pointer \
                   might be invalidated by a subsequent getpwent(), getpwnam() or \
                   getpwuid(). Darwin Libinfo (getpwuid -> LI_set_thread_item): the \
                   result is held per thread until that thread's next such lookup",
    },
];

impl PointerReturnContract {
    /// Whether `pointee` is the documented pointee type of this contract.
    ///
    /// For a [`ContractPointee::CStruct`], the declared ADT must be a `struct`
    /// (`adt_kind`, from rustc's `AdtDef`; an unknown kind is refused) named by the
    /// layout's tag, with EXACTLY the layout's members — the same count, and each member
    /// the same name and type, in declaration order — AND rustc's computed layout of it
    /// must be exactly the C size, alignment and member offsets (REVIEW-A4C4-MINORS-1).
    /// The C library hands back a pointer to ITS object; a declaration that is larger,
    /// or places a member elsewhere, would let a read through the result leave that
    /// object, so anything but the exact shape lends no contract.
    ///
    /// THE LAYOUT IS REQUIRED, not checked when present (fix-forward, 2026-11-07). The
    /// member list cannot show a `repr`: Darwin's ten members under `#[repr(C,
    /// align(16))]` are 80 bytes, and a whole-struct read `*pw` leaves the 72-byte C
    /// object. The first cut checked `Ty::Adt::layout` only when it was `Some`, and the
    /// verifying extractor never fills it (only `faithful_scalars()` extraction does,
    /// and the verifier pipeline stays on the legacy entry), so on every compile the
    /// check was skipped. `compiler_layout` is rustc's `layout_of` of the call's pointee,
    /// handed over by the compiler for the call's block
    /// (`VcgenContext::with_compiler_foreign_return_pointee_layouts`). At least one of
    /// the two must be present, and every one present must be exactly the C layout.
    fn pointee_matches(&self, pointee: &Ty, compiler_layout: Option<&AdtLayoutInfo>) -> bool {
        match self.pointee {
            ContractPointee::CInt => matches!(pointee, Ty::Int { width: 32, signed: true }),
            ContractPointee::CStruct(c) => match pointee {
                Ty::Adt { name: adt, fields, variants, layout, adt_kind, .. } => {
                    let is_c_layout = |l: &AdtLayoutInfo| {
                        l.size == c.size
                            && l.align == c.align
                            && l.field_offsets.as_slice() == c.offsets
                    };
                    let layouts = [layout.as_deref(), compiler_layout];
                    variants.is_empty()
                        && *adt_kind == Some(AdtKind::Struct)
                        && adt_leaf(adt) == c.name
                        && fields.len() == c.fields.len()
                        && fields
                            .iter()
                            .zip(c.fields)
                            .all(|((name, ty), (want, member))| name == want && member.matches(ty))
                        && layouts.iter().any(Option::is_some)
                        && layouts.into_iter().flatten().all(is_c_layout)
                }
                _ => false,
            },
        }
    }

    /// The alignment, in bytes, every result is guaranteed to have (a null result is
    /// aligned to everything). `word_bytes` is the target's pointer width when the
    /// caller knows it — the width of the `usize` a rustc `CheckAlignment` assert casts
    /// the address to — and `None` otherwise.
    ///
    /// * `CInt`: 4. The contract matched only a declared `*mut i32`, and a 32-bit C
    ///   `int` is 4-aligned on every target Trust supports.
    /// * `CStruct`: the pointer width. A C struct is aligned to at least each member's
    ///   alignment, the struct has a pointer member, and on every target Trust supports
    ///   a data pointer's alignment is its width. Without the width: 1 (no claim).
    pub(crate) fn guaranteed_align(&self, word_bytes: Option<i128>) -> i128 {
        match self.pointee {
            ContractPointee::CInt => 4,
            ContractPointee::CStruct(_) => word_bytes.unwrap_or(1),
        }
    }
}

/// The last path segment of an ADT name, generic arguments removed.
fn adt_leaf(name: &str) -> &str {
    let base = name.split('<').next().unwrap_or(name);
    base.rsplit("::").next().unwrap_or(base)
}

fn contract_named(symbol: &str) -> Option<&'static PointerReturnContract> {
    POINTER_RETURN_CONTRACTS.iter().find(|c| c.symbol == symbol)
}

/// The pointee of `func`'s whole local `local`, when it is a raw pointer.
fn raw_pointee(func: &VerifiableFunction, local: usize) -> Option<&Ty> {
    match crate::local_ty_ref(func, local)? {
        Ty::RawPtr { pointee, .. } => Some(pointee),
        _ => None,
    }
}

/// The crate NAME whose `extern` declarations of the contract symbols are believed.
///
/// A crate name is not an identity — a path or git dependency, a `[patch]`, or the
/// crate under verification itself can be called `libc`, and the crates.io `libc`
/// shares its name with the sysroot's copy (so `krate_name_is_ambiguous` is true for
/// the very declarations this module exists for). What makes a declaration lend a
/// contract is therefore checked on the declaration itself, in
/// [`direct_call_contract`]:
///
/// * its LINK symbol (`CalleeKey::upstream_foreign_link_symbol`, from
///   `tcx.symbol_name`) is the contract's C symbol, so a `#[link_name = "malloc"] fn
///   __error()` is refused whatever crate wrote it;
/// * it is declared by an UPSTREAM crate (that field is `None` for a local
///   declaration), so the program under verification never lends itself a contract;
/// * its arity and its return type are the symbol's documented prototype.
///
/// This name check is defense in depth on top of those: it keeps the believed
/// declarations to the one crate docs/TCB.md names. The residual premise — that the
/// C symbol resolves to the platform C library's definition and is not interposed by
/// a `#[no_mangle]`/`#[export_name]`/`#[linkage]` definition elsewhere in the final
/// link — is recorded in docs/TCB.md ("libc/Darwin pointer return-contract
/// summaries").
const CONTRACT_DECLARING_CRATE: &str = "libc";

/// Whether the current function's compilation targets Darwin (see
/// [`ContractPlatform::Darwin`]). Missing or foreign context: `false`.
fn platform_admits(func: &VerifiableFunction, platform: ContractPlatform) -> bool {
    match platform {
        ContractPlatform::Any => true,
        ContractPlatform::Darwin => crate::target_is_darwin_for(&func.def_path),
    }
}

/// The contract of a DIRECT foreign call terminator: `is_foreign`, a compiler-resolved
/// `extern`-block leaf naming a contract symbol, declared by an upstream crate named
/// `libc` ([`CONTRACT_DECLARING_CRATE`]) whose declaration links to exactly that C
/// symbol (`CalleeKey::upstream_foreign_link_symbol`), with the documented arity, on a
/// target the row holds for, into a whole-local destination of the documented pointer
/// type (for a struct pointee, with rustc's layout of it for `block`'s call: see
/// [`PointerReturnContract::pointee_matches`]). Anything else is `None`.
pub(crate) fn direct_call_contract(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<&'static PointerReturnContract> {
    let term = &block.terminator;
    let Terminator::Call { is_foreign: true, callee_key: Some(key), dest, args, .. } = term else {
        return None;
    };
    if key.krate_name != CONTRACT_DECLARING_CRATE {
        return None;
    }
    let contract = contract_named(key.foreign_block_leaf.as_deref()?)?;
    // The declaration's Rust name is the symbol AND so is the symbol it links to.
    if key.upstream_foreign_link_symbol.as_deref() != Some(contract.symbol)
        || args.len() != contract.arity
        || !platform_admits(func, contract.platform)
        || !dest.projections.is_empty()
    {
        return None;
    }
    let compiler_layout =
        crate::compiler_foreign_return_pointee_layout_for(&func.def_path, block.id);
    contract
        .pointee_matches(raw_pointee(func, dest.local)?, compiler_layout.as_ref())
        .then_some(contract)
}

/// The contract a call reaches: a direct foreign call ([`direct_call_contract`]) or a
/// same-crate wrapper recorded by [`compute_return_ffi_pointer_summaries`] whose body
/// the call's identity reaches. A wrapper lends only a thread-lifetime contract.
pub(crate) fn call_contract(
    func: &VerifiableFunction,
    block: &BasicBlock,
) -> Option<&'static PointerReturnContract> {
    if let Some(contract) = direct_call_contract(func, block) {
        return Some(contract);
    }
    let term = &block.terminator;
    let Terminator::Call { is_foreign: false, func: callee, dest, .. } = term else {
        return None;
    };
    if !dest.projections.is_empty() {
        return None;
    }
    let pointee = raw_pointee(func, dest.local)?;
    let symbol = crate::callee_ffi_pointer_return_symbol(callee)?;
    if !crate::call_reaches_summarized_body(term) {
        return None;
    }
    let contract = contract_named(&symbol)?;
    // A wrapper lends only a thread-lifetime contract, and every such contract's
    // pointee is a C `int`: no struct layout is asked for here.
    (contract.validity == ContractValidity::ThreadLifetime
        && contract.pointee_matches(pointee, None))
    .then_some(contract)
}

/// The wrapper summaries: each function whose return place `_0` (a raw pointer) is
/// written exactly once, as the whole destination of a direct contract call with a
/// thread-lifetime contract, and is mentioned by no other statement or terminator.
/// Keyed by def path; the value is the contract's symbol.
///
/// SOUND: such a body returns, on every path that returns, exactly the foreign call's
/// result — no statement can change `_0` after the call, and no borrow of `_0` exists.
#[must_use]
pub fn compute_return_ffi_pointer_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, String> {
    let mut out = FxHashMap::default();
    for func in funcs {
        if let Some(symbol) = wrapper_contract_symbol(func) {
            out.insert(func.def_path.clone(), symbol.to_string());
        }
    }
    out
}

fn wrapper_contract_symbol(func: &VerifiableFunction) -> Option<&'static str> {
    // PERF-COMPILER-VCGEN-587: a wrapper requires a bare-dest Call to `_0` and no TailCall;
    // reject functions without a bare-dest Call or with a TailCall via cached terminator presence.
    if {
        let tp = crate::generate::terminator_presence_for(func);
        !tp.has_bare_dest_call || tp.has_tail_call
    } {
        return None;
    }
    raw_pointee(func, 0)?;
    let mut found: Option<&'static PointerReturnContract> = None;
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Call { dest, .. } if dest.local == 0 => {
                let contract = direct_call_contract(func, block)?;
                if found.is_some() || contract.validity != ContractValidity::ThreadLifetime {
                    return None;
                }
                found = Some(contract);
            }
            Terminator::Return | Terminator::Goto(_) | Terminator::Unreachable => {}
            Terminator::TailCall { .. } => return None,
            other => {
                if crate::sep_engine::terminator_mentions_local(other, 0)
                    || !crate::sep_engine::for_each_terminator_successor(other, |_| {})
                {
                    return None;
                }
            }
        }
    }
    let contract = found?;
    if func
        .body
        .blocks
        .iter()
        .any(|block| block.stmts.iter().any(|stmt| crate::sep_engine::stmt_mentions_local(stmt, 0)))
    {
        return None;
    }
    Some(contract.symbol)
}

/// A contract-rooted local: the call block, its normal successor and the contract.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ContractRoot {
    pub(crate) contract: &'static PointerReturnContract,
    /// The block whose `Call` terminator writes the local.
    pub(crate) call_block: usize,
    /// The call's normal return target (whose only predecessor is `call_block`).
    pub(crate) target: usize,
}

/// Remove locals from `candidates` whose own storage is written or borrowed anywhere in
/// `func`, other than as the whole destination of a `Call` terminator; clear `candidates`
/// when the body has an inline-asm/opaque terminator or a terminator whose successors
/// cannot be read (either may write any local).
///
/// A `Call` destination is NOT removed here: each caller checks call destinations itself.
fn remove_written_or_borrowed<V>(
    func: &VerifiableFunction,
    candidates: &mut FxHashMap<usize, V>,
) {
    if candidates.is_empty() {
        return;
    }
    let remove_own_storage = |place: &Place, map: &mut FxHashMap<usize, V>| {
        if !matches!(place.projections.first(), Some(Projection::Deref)) {
            map.remove(&place.local);
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    remove_own_storage(place, candidates);
                    match rvalue {
                        Rvalue::Ref { place: p, .. } | Rvalue::AddressOf(_, p) => {
                            remove_own_storage(p, candidates);
                        }
                        Rvalue::Use(_)
                        | Rvalue::BinaryOp(..)
                        | Rvalue::CheckedBinaryOp(..)
                        | Rvalue::UncheckedBinaryOp(..)
                        | Rvalue::UnaryOp(..)
                        | Rvalue::Cast(..)
                        | Rvalue::Aggregate(..)
                        | Rvalue::Discriminant(_)
                        | Rvalue::Len(_)
                        | Rvalue::Repeat(..)
                        | Rvalue::CopyForDeref(_) => {}
                        // An rvalue this module does not read may borrow: refuse every
                        // local it mentions.
                        _ => {
                            candidates
                                .retain(|&k, _| !crate::sep_engine::stmt_mentions_local(stmt, k));
                        }
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                // `SetDiscriminant`/`Deinit`/`Retag`/`PlaceMention` of the local, an
                // intrinsic or unsupported statement reading it, or a statement this
                // module does not know: refuse the locals it mentions.
                other => {
                    candidates.retain(|&k, _| !crate::sep_engine::stmt_mentions_local(other, k));
                }
            }
            if candidates.is_empty() {
                return;
            }
        }
        match &block.terminator {
            Terminator::Drop { place, .. } => remove_own_storage(place, candidates),
            Terminator::Opaque { .. } => {
                candidates.clear();
                return;
            }
            term if !crate::sep_engine::for_each_terminator_successor(term, |_| {}) => {
                candidates.clear();
                return;
            }
            _ => {}
        }
        if candidates.is_empty() {
            return;
        }
    }
}

/// Every local assigned exactly once, as the whole destination of a contract call with
/// a normal return target, and otherwise never written or borrowed. An argument or the
/// return place is never one.
fn contract_rooted_locals(func: &VerifiableFunction) -> FxHashMap<usize, ContractRoot> {
    // PERF-COMPILER-VCGEN-587: skip the block scan when the body has no bare-dest Call.
    if !crate::generate::terminator_presence_for(func).has_bare_dest_call {
        return FxHashMap::default();
    }
    let mut candidates: FxHashMap<usize, ContractRoot> = FxHashMap::default();
    let mut refused: FxHashSet<usize> = FxHashSet::default();
    for block in &func.body.blocks {
        let Terminator::Call { dest, target: Some(target), .. } = &block.terminator else {
            continue;
        };
        if dest.local == 0 || dest.local <= func.body.arg_count || !dest.projections.is_empty() {
            continue;
        }
        let Some(contract) = call_contract(func, block) else { continue };
        if candidates
            .insert(dest.local, ContractRoot { contract, call_block: block.id.0, target: target.0 })
            .is_some()
        {
            refused.insert(dest.local);
        }
    }
    candidates.retain(|local, _| !refused.contains(local));
    if candidates.is_empty() {
        return candidates;
    }
    for block in &func.body.blocks {
        let Terminator::Call { dest, .. } = &block.terminator else { continue };
        if !matches!(dest.projections.first(), Some(Projection::Deref))
            && candidates.get(&dest.local).is_some_and(|root| root.call_block != block.id.0)
        {
            refused.insert(dest.local);
        }
    }
    candidates.retain(|local, _| !refused.contains(local));
    remove_written_or_borrowed(func, &mut candidates);
    candidates
}

fn own_storage_is(place: &Place, local: usize) -> bool {
    place.local == local && !matches!(place.projections.first(), Some(Projection::Deref))
}

/// Whether `local`'s own storage may be reached through a pointer somewhere in `func`:
/// a `&`/`&raw` of it, or an unsupported rvalue or a statement this module does not read
/// that mentions it. A write through such a pointer would not name `local`, so a
/// definition read off the statement list could be stale.
fn may_be_borrowed(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().flat_map(|block| &block.stmts).any(|stmt| match stmt {
        Statement::Assign {
            rvalue: Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place),
            ..
        } => own_storage_is(place, local),
        Statement::Assign {
            rvalue: Rvalue::Unsupported { .. } | Rvalue::PtrOffset { .. }, ..
        }
        | Statement::Intrinsic { .. }
        | Statement::CopyNonOverlapping { .. }
        | Statement::Unsupported { .. } => crate::sep_engine::stmt_mentions_local(stmt, local),
        _ => false,
    })
}

/// The definition of `local` that is CURRENT just before statement `limit` of `block`:
/// the last statement before `limit` that may write `local`, when it is a whole-local
/// `Assign` — its index and rvalue. `None` when `local` is not assigned in
/// `block.stmts[..limit]`, when that last touch is a partial write, a storage marker or
/// a statement this module does not read, or when `local` may be borrowed
/// ([`may_be_borrowed`]). A use at `limit` therefore reads exactly the returned rvalue's
/// value: it is what the statement at `limit` (or, with `limit == stmts.len()`, the
/// terminator) sees, even where an optimization reused the local for another value
/// later in the block.
fn def_before<'a>(
    func: &VerifiableFunction,
    block: &'a BasicBlock,
    local: usize,
    limit: usize,
) -> Option<(usize, &'a Rvalue)> {
    for (index, stmt) in block.stmts.get(..limit)?.iter().enumerate().rev() {
        match stmt {
            Statement::Assign { place, rvalue, .. } if place.local == local => {
                return (place.projections.is_empty() && !may_be_borrowed(func, local))
                    .then_some((index, rvalue));
            }
            // Writes another local (memory through a pointer cannot be `local`: it is
            // not borrowed) and at most READS `local`.
            Statement::Assign { .. }
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            Statement::StorageLive(l) | Statement::StorageDead(l) if *l != local => {}
            other if !crate::sep_engine::stmt_mentions_local(other, local) => {}
            _ => return None,
        }
    }
    None
}

fn whole_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(Place { local, projections })
        | Operand::Move(Place { local, projections })
            if projections.is_empty() =>
        {
            Some(*local)
        }
        _ => None,
    }
}

fn const_int(op: &Operand) -> Option<i128> {
    match op {
        Operand::Constant(ConstValue::Uint(v, _)) => i128::try_from(*v).ok(),
        Operand::Constant(ConstValue::Int(v)) => Some(*v),
        _ => None,
    }
}

/// An operand's integer value just before statement `limit`: a constant, or a local
/// whose current same-block definition ([`def_before`]) is a constant or
/// `Sub(const, const)`.
fn int_value(
    func: &VerifiableFunction,
    block: &BasicBlock,
    op: &Operand,
    limit: usize,
) -> Option<i128> {
    if let Some(v) = const_int(op) {
        return Some(v);
    }
    match def_before(func, block, whole_local(op)?, limit)?.1 {
        Rvalue::Use(inner) => const_int(inner),
        Rvalue::BinaryOp(BinOp::Sub, a, b) => const_int(a)?.checked_sub(const_int(b)?),
        _ => None,
    }
}

/// The pointer local an address word read at statement `limit` of `block` is computed
/// from: `a = (p as *const ()) as uN` or `a = p as uN`, `p` a whole raw-pointer local,
/// each the CURRENT definition at its use ([`def_before`]). Returns the pointer local and
/// the address word's width in bytes.
fn address_source(
    func: &VerifiableFunction,
    block: &BasicBlock,
    op: &Operand,
    limit: usize,
) -> Option<(usize, i128)> {
    let (at, Rvalue::Cast(inner, Ty::Int { width, signed: false })) =
        def_before(func, block, whole_local(op)?, limit)?
    else {
        return None;
    };
    let word_bytes = i128::from(*width) / 8;
    let mut p = whole_local(inner)?;
    if let Some((_, Rvalue::Cast(src, Ty::RawPtr { .. }))) = def_before(func, block, p, at) {
        p = whole_local(src)?;
    }
    raw_pointee(func, p)?;
    Some((p, word_bytes))
}

/// A rustc runtime pointer check this module can read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PtrAssert {
    /// `CheckNull`: the assert passes only when `local` is non-null.
    NonNull { local: usize },
    /// `CheckAlignment`: the assert passes only when `local` is `align`-aligned.
    Aligned { local: usize, align: i128, word_bytes: i128 },
}

/// Parse `block`'s terminator as rustc's `CheckNull` or `CheckAlignment` assert, in the
/// exact shapes those passes emit (`check_null.rs`, `check_alignment.rs`):
///
/// * null: `c = !(e & n)`, `e = (addr == 0)`, `n = (size != 0)` with a NON-ZERO constant
///   size (a zero-sized pointee admits null, so its assert proves nothing) or the
///   constant `true`; expected `true`.
/// * alignment: `c = (m == 0)`, `m = addr & k`, `k = K - 1`; expected `true`.
///
/// `addr` must be the pointer local itself cast to an unsigned word. Each link of the
/// chain is the definition CURRENT at its use ([`def_before`]): a local the block
/// reassigns later, a borrowed local or a partial write breaks the chain. Anything else
/// is `None`.
pub(crate) fn parse_ptr_assert(func: &VerifiableFunction, block: &BasicBlock) -> Option<PtrAssert> {
    let Terminator::Assert { cond, expected: true, msg, .. } = &block.terminator else {
        return None;
    };
    let end = block.stmts.len();
    if end == 0 {
        return None;
    }
    let c = whole_local(cond)?;
    match msg {
        AssertMessage::NullPointerDereference => {
            let (at_c, Rvalue::UnaryOp(UnOp::Not, inner)) = def_before(func, block, c, end)? else {
                return None;
            };
            let (at_and, Rvalue::BinaryOp(BinOp::BitAnd, x, y)) =
                def_before(func, block, whole_local(inner)?, at_c)?
            else {
                return None;
            };
            let is_null_test = |op: &Operand| -> Option<usize> {
                let (at_eq, Rvalue::BinaryOp(BinOp::Eq, l, r)) =
                    def_before(func, block, whole_local(op)?, at_and)?
                else {
                    return None;
                };
                let addr = if const_int(r) == Some(0) {
                    l
                } else if const_int(l) == Some(0) {
                    r
                } else {
                    return None;
                };
                address_source(func, block, addr, at_eq).map(|(p, _)| p)
            };
            let nonzero_size = |op: &Operand| -> bool {
                if matches!(op, Operand::Constant(ConstValue::Bool(true))) {
                    return true;
                }
                let Some(n) = whole_local(op) else { return false };
                match def_before(func, block, n, at_and).map(|(_, rv)| rv) {
                    Some(Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))) => true,
                    Some(Rvalue::BinaryOp(BinOp::Ne, a, b)) => {
                        (const_int(b) == Some(0) && const_int(a).is_some_and(|s| s != 0))
                            || (const_int(a) == Some(0) && const_int(b).is_some_and(|s| s != 0))
                    }
                    _ => false,
                }
            };
            let local = match (is_null_test(x), is_null_test(y)) {
                (Some(p), None) if nonzero_size(y) => p,
                (None, Some(p)) if nonzero_size(x) => p,
                _ => return None,
            };
            Some(PtrAssert::NonNull { local })
        }
        AssertMessage::MisalignedPointerDereference => {
            let (at_c, Rvalue::BinaryOp(BinOp::Eq, l, r)) = def_before(func, block, c, end)? else {
                return None;
            };
            let masked = if const_int(r) == Some(0) {
                l
            } else if const_int(l) == Some(0) {
                r
            } else {
                return None;
            };
            let (at_and, Rvalue::BinaryOp(BinOp::BitAnd, x, y)) =
                def_before(func, block, whole_local(masked)?, at_c)?
            else {
                return None;
            };
            let (addr, mask) = match (
                address_source(func, block, x, at_and),
                address_source(func, block, y, at_and),
            ) {
                (Some(a), None) => (a, int_value(func, block, y, at_and)?),
                (None, Some(a)) => (a, int_value(func, block, x, at_and)?),
                _ => return None,
            };
            let align = mask.checked_add(1)?;
            // A power of two, as `align_of` always is: then `addr & (K - 1) == 0` is
            // exactly `addr % K == 0`.
            if align <= 0 || align & (align - 1) != 0 {
                return None;
            }
            Some(PtrAssert::Aligned { local: addr.0, align, word_bytes: addr.1 })
        }
        _ => None,
    }
}

/// Whether `term` is a call of the real core `<*const T>::is_null` / `<*mut T>::is_null`
/// (compiler-authenticated as the real sysroot `core`, not a crate that names itself
/// `core`). Returns the whole-local argument and the whole-local destination.
fn is_core_is_null_call(term: &Terminator) -> Option<(usize, usize)> {
    let Terminator::Call {
        func: callee, args, dest, callee_key: Some(key), is_foreign: false, ..
    } = term
    else {
        return None;
    };
    if !key.krate_is_real_sysroot
        || key.krate_name_is_ambiguous
        || key.krate_name != "core"
        || !dest.projections.is_empty()
        || args.len() != 1
    {
        return None;
    }
    // `core::ptr::mut_ptr::<impl *mut T>::is_null`, optionally followed by one
    // turbofish group (the extractor's `::<__trust_args@…>` stamp).
    let rest = callee
        .strip_prefix("core::ptr::mut_ptr::<impl *mut ")
        .or_else(|| callee.strip_prefix("core::ptr::const_ptr::<impl *const "))?;
    let at = rest.find(">::is_null")?;
    let tail = &rest[at + ">::is_null".len()..];
    if !(tail.is_empty() || (tail.starts_with("::<") && tail.ends_with('>'))) {
        return None;
    }
    Some((whole_local(&args[0])?, dest.local))
}

/// Locals written exactly once, by the whole destination of a call with a normal return
/// target, and otherwise never written or borrowed; mapped to that call's block.
fn single_call_defined_locals(func: &VerifiableFunction) -> FxHashMap<usize, usize> {
    let mut defs: FxHashMap<usize, usize> = FxHashMap::default();
    let mut refused: FxHashSet<usize> = FxHashSet::default();
    for block in &func.body.blocks {
        if let Terminator::Call { dest, target, .. } = &block.terminator
            && !matches!(dest.projections.first(), Some(Projection::Deref))
        {
            if !dest.projections.is_empty()
                || target.is_none()
                || defs.insert(dest.local, block.id.0).is_some()
            {
                refused.insert(dest.local);
            }
        }
    }
    defs.retain(|l, _| !refused.contains(l) && *l != 0 && *l > func.body.arg_count);
    remove_written_or_borrowed(func, &mut defs);
    defs
}

/// The structural pointer facts of one body (see the module comment).
///
/// WHY A FACT ABOUT A CONTRACT-ROOTED `L` AT ITS ENTRY BLOCK `E` HOLDS AT A USE BLOCK `U`
/// THAT `E` DOMINATES. `L` is written only by the call in block `C`, whose return target
/// `T` has `C` as its only predecessor, and `E` is required to be dominated by `T` and
/// distinct from `C` (so `C` strictly dominates `E`). On any path to `U`, take the last
/// execution of `C`: it is followed by `T`, and from `T` the path reaches `U` without
/// re-executing `C`. If that suffix skipped `E`, prefixing it with a path to `C` that
/// avoids `E` (one exists: `C` strictly dominates `E`, so `E` does not dominate `C`)
/// would reach `U` without `E`, contradicting `E dom U`. So the last `E` before `U`
/// follows the last `C`, and `L` holds the same value at `E` and at `U`.
#[derive(Debug, Clone)]
pub(crate) struct PointerFacts {
    roots: FxHashMap<usize, ContractRoot>,
    /// Block -> its dominators (normal edges).
    dom: FxHashMap<usize, FxHashSet<usize>>,
    /// `(entry, local)`: entering block `entry` implies `local != 0`, because the
    /// program tested it (the false edge of a core `is_null`).
    nonnull_entries: Vec<(usize, usize)>,
    /// `(entry, local)`: entering block `entry` implies `local != 0`, because a rustc
    /// `CheckNull` assert on it passed. Used only to discharge LATER asserts, never a
    /// dereference's own rows (see [`PointerFacts::tested_nonnull_at`]).
    asserted_nonnull_entries: Vec<(usize, usize)>,
    /// `(entry, local, K)`: entering block `entry` implies `local % K == 0`.
    aligned_entries: Vec<(usize, usize, i128)>,
    /// Normal-edge successors and predecessors.
    succs: FxHashMap<usize, Vec<usize>>,
    preds: FxHashMap<usize, Vec<usize>>,
    /// Blocks whose terminator runs no foreign or user code: `Goto`, `SwitchInt`,
    /// `Assert`, or a call of the core `is_null`.
    call_free: FxHashSet<usize>,
}

impl PointerFacts {
    /// The facts of `func`, or `None` when it has no contract-rooted local (the common
    /// case: nothing below is computed) or its CFG cannot be read.
    pub(crate) fn for_function(func: &VerifiableFunction) -> Option<Self> {
        let mut roots = contract_rooted_locals(func);
        if roots.is_empty() {
            return None;
        }
        let blocks = &func.body.blocks;
        if blocks.iter().enumerate().any(|(i, b)| b.id.0 != i) {
            return None;
        }
        let mut succs: FxHashMap<usize, Vec<usize>> =
            FxHashMap::with_capacity_and_hasher(blocks.len(), Default::default());
        let mut preds: FxHashMap<usize, Vec<usize>> =
            FxHashMap::with_capacity_and_hasher(blocks.len(), Default::default());
        for block in blocks {
            let s = crate::sep_engine::terminator_successors(&block.terminator)?;
            for &t in &s {
                preds.entry(t).or_default().push(block.id.0);
            }
            succs.insert(block.id.0, s);
        }
        // The entry block (index 0) is also entered from outside the body, an edge
        // `preds` does not list: it is never anyone's sole-predecessor successor.
        let sole_pred =
            |to: usize, from: usize| to != 0 && preds.get(&to).is_some_and(|p| p == &[from]);
        // A root whose return target can be entered from elsewhere is no root.
        roots.retain(|_, root| sole_pred(root.target, root.call_block));
        if roots.is_empty() {
            return None;
        }
        let dom = crate::sep_engine::block_dominators(blocks);
        if dom.is_empty() {
            return None;
        }
        let dominated_by =
            |block: usize, by: usize| dom.get(&block).is_some_and(|d| d.contains(&by));
        // An entry fact about `local` is kept only where `local` is the current call
        // result: the entry is dominated by the call's target and is not the call block.
        let entry_ok = |entry: usize, local: usize| {
            roots
                .get(&local)
                .is_some_and(|root| entry != root.call_block && dominated_by(entry, root.target))
        };

        let mut nonnull_entries = Vec::new();
        let mut asserted_nonnull_entries = Vec::new();
        let mut aligned_entries = Vec::new();
        let mut bool_defs: Option<FxHashMap<usize, usize>> = None;
        for block in blocks {
            let here = block.id.0;
            if let Terminator::Assert { target, .. } = &block.terminator
                && sole_pred(target.0, here)
            {
                match parse_ptr_assert(func, block) {
                    Some(PtrAssert::NonNull { local }) if entry_ok(target.0, local) => {
                        asserted_nonnull_entries.push((target.0, local));
                    }
                    Some(PtrAssert::Aligned { local, align, .. }) if entry_ok(target.0, local) => {
                        aligned_entries.push((target.0, local, align));
                    }
                    _ => {}
                }
            }
            // `switchInt(r) [0 -> F]` where `r = L.is_null()` was computed in a block
            // `B` that dominates this switch and is itself dominated by `L`'s call
            // target (so `r` describes the current `L`): `F` sees `L != 0`.
            if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator
                && let [(0, false_target)] = targets.as_slice()
                && false_target.0 != otherwise.0
                && sole_pred(false_target.0, here)
                && let Some(r) = whole_local(discr)
                && let Some(&def_block) =
                    bool_defs.get_or_insert_with(|| single_call_defined_locals(func)).get(&r)
                && let Some((ptr, dest)) = is_core_is_null_call(&blocks[def_block].terminator)
                && dest == r
                && entry_ok(def_block, ptr)
                && dominated_by(here, def_block)
                && entry_ok(false_target.0, ptr)
            {
                nonnull_entries.push((false_target.0, ptr));
            }
        }
        let mut call_free = FxHashSet::default();
        if roots.values().any(|root| root.contract.validity == ContractValidity::UntilNextCall) {
            call_free.reserve(blocks.len());
            for b in blocks {
                if matches!(
                    b.terminator,
                    Terminator::Goto(_) | Terminator::SwitchInt { .. } | Terminator::Assert { .. }
                ) || is_core_is_null_call(&b.terminator).is_some()
                {
                    call_free.insert(b.id.0);
                }
            }
        }
        Some(PointerFacts {
            roots,
            dom,
            nonnull_entries,
            asserted_nonnull_entries,
            aligned_entries,
            succs,
            preds,
            call_free,
        })
    }

    fn dominated_by(&self, block: usize, by: usize) -> bool {
        self.dom.get(&block).is_some_and(|d| d.contains(&by))
    }

    /// The root of `local` when `block` sees `local` as the current call result (it is
    /// dominated by the call's return target).
    fn live_root(&self, block: usize, local: usize) -> Option<&ContractRoot> {
        self.roots.get(&local).filter(|root| self.dominated_by(block, root.target))
    }

    /// The contract of `local` as seen from `block`.
    pub(crate) fn contract_at(
        &self,
        block: usize,
        local: usize,
    ) -> Option<&'static PointerReturnContract> {
        self.live_root(block, local).map(|root| root.contract)
    }

    /// Is `local` non-null on entry to `block` by the contract or by a dominating
    /// `is_null` test the program made? This is what a DEREFERENCE's null and
    /// allocation rows may use. A passed rustc `CheckNull` assert is deliberately not
    /// enough there: a dereference of a nullable result that only rustc's runtime
    /// check guards (`*libc::getpwuid(uid)` with no test) keeps its REFUTED null row,
    /// so the missing test is reported as the failure it is, not as an unproved assert.
    pub(crate) fn tested_nonnull_at(&self, block: usize, local: usize) -> bool {
        let Some(root) = self.live_root(block, local) else { return false };
        !root.contract.may_be_null
            || self
                .nonnull_entries
                .iter()
                .any(|&(entry, l)| l == local && self.dominated_by(block, entry))
    }

    /// Is `local` non-null on entry to `block` by [`Self::tested_nonnull_at`] or by a
    /// dominating passed rustc `CheckNull` assert on it? What a LATER pointer assert on
    /// the same local may use: the program cannot reach it with `local == 0`.
    pub(crate) fn nonnull_at(&self, block: usize, local: usize) -> bool {
        self.tested_nonnull_at(block, local)
            || (self.live_root(block, local).is_some()
                && self
                    .asserted_nonnull_entries
                    .iter()
                    .any(|&(entry, l)| l == local && self.dominated_by(block, entry)))
    }

    /// The largest alignment a dominating passed `CheckAlignment` assert gives `local`
    /// on entry to `block`.
    pub(crate) fn asserted_align_at(&self, block: usize, local: usize) -> Option<i128> {
        self.live_root(block, local)?;
        self.aligned_entries
            .iter()
            .filter(|&&(entry, l, _)| l == local && self.dominated_by(block, entry))
            .map(|&(_, _, k)| k)
            .max()
    }

    /// The largest alignment `local` is known to have on entry to `block`: a dominating
    /// passed `CheckAlignment` assert on it, or the contract's guarantee.
    pub(crate) fn known_align_at(
        &self,
        block: usize,
        local: usize,
        word_bytes: Option<i128>,
    ) -> Option<i128> {
        let root = self.live_root(block, local)?;
        let asserted = self.asserted_align_at(block, local).unwrap_or(0);
        Some(asserted.max(root.contract.guaranteed_align(word_bytes)))
    }

    /// Is `local`'s object valid (allocated, of the documented type) on entry to
    /// `block`? A thread-lifetime contract: whenever `block` sees the current call
    /// result. An until-next-call contract: additionally, every block on a path from the
    /// call's target to `block` (excluding `block` itself unless it lies on a cycle
    /// through the window) ends in a terminator that runs no foreign or user code.
    pub(crate) fn valid_at(&self, block: usize, local: usize) -> bool {
        let Some(root) = self.live_root(block, local) else { return false };
        match root.contract.validity {
            ContractValidity::ThreadLifetime => true,
            ContractValidity::UntilNextCall => {
                let from = self.reach_forward(root.target);
                if !from.contains(&block) || from.iter().all(|b| self.call_free.contains(b)) {
                    return true;
                }
                let to = self.reach_backward_strict(block);
                from.intersection(&to).all(|b| self.call_free.contains(b))
            }
        }
    }

    fn reach_forward(&self, start: usize) -> FxHashSet<usize> {
        let mut seen = FxHashSet::with_capacity_and_hasher(self.succs.len(), Default::default());
        let mut stack = vec![start];
        while let Some(b) = stack.pop() {
            if seen.insert(b) {
                stack.extend(self.succs.get(&b).into_iter().flatten().copied());
            }
        }
        seen
    }

    /// Blocks that reach `target` by at least one edge.
    fn reach_backward_strict(&self, target: usize) -> FxHashSet<usize> {
        let mut seen = FxHashSet::with_capacity_and_hasher(self.preds.len(), Default::default());
        let mut stack: Vec<usize> = self.preds.get(&target).cloned().unwrap_or_default();
        while let Some(b) = stack.pop() {
            if seen.insert(b) {
                stack.extend(self.preds.get(&b).into_iter().flatten().copied());
            }
        }
        seen
    }

    /// Can `block`'s rustc pointer assert not fail, by the contract and the dominance
    /// facts? Only for an assert on a contract-rooted local:
    /// * `CheckNull` — the local is non-null on entry to the assert's block;
    /// * `CheckAlignment` with constant `K` — `K` is at most the local's known alignment
    ///   on entry to the assert's block (a dominating EARLIER assert, or the contract).
    pub(crate) fn discharges_assert(&self, func: &VerifiableFunction, block: &BasicBlock) -> bool {
        match parse_ptr_assert(func, block) {
            Some(PtrAssert::NonNull { local }) => self.nonnull_at(block.id.0, local),
            Some(PtrAssert::Aligned { local, align, word_bytes }) => {
                self.known_align_at(block.id.0, local, Some(word_bytes)).is_some_and(|k| align <= k)
            }
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    //! REVIEW-A4C4-MINORS-1: `getpwuid`'s pointee is Darwin's `struct passwd` EXACTLY.
    //! Before, any variant-less ADT whose leaf name was `passwd` and that had one
    //! raw-pointer field lent the contract, so a `libc`-named dependency declaring
    //! `struct passwd { pw_name: *mut c_char, tail: [u64; 1024] }` had the
    //! allocation-validity and alignment rows of `(*pw).tail[1000]` dropped, though the
    //! object the C library returns is 72 bytes.

    use trust_types::AdtLayoutInfo;

    use super::*;

    fn char_ptr(mutable: bool, signed: bool) -> Ty {
        Ty::RawPtr { mutable, pointee: Box::new(Ty::Int { width: 8, signed }) }
    }

    fn int(width: u32, signed: bool) -> Ty {
        Ty::Int { width, signed }
    }

    /// libc 0.2.191's Darwin `struct passwd`, spelled as the real-MIR extractor spells it
    /// in `tests/fixtures/ffi_pointer_contract/passwd_*_mir.json` (aarch64-apple-darwin).
    fn darwin_fields() -> Vec<(String, Ty)> {
        [
            ("pw_name", char_ptr(true, true)),
            ("pw_passwd", char_ptr(true, true)),
            ("pw_uid", int(32, false)),
            ("pw_gid", int(32, false)),
            ("pw_change", int(64, true)),
            ("pw_class", char_ptr(true, true)),
            ("pw_gecos", char_ptr(true, true)),
            ("pw_dir", char_ptr(true, true)),
            ("pw_shell", char_ptr(true, true)),
            ("pw_expire", int(64, true)),
        ]
        .into_iter()
        .map(|(name, ty)| (name.to_string(), ty))
        .collect()
    }

    fn darwin_layout() -> AdtLayoutInfo {
        AdtLayoutInfo {
            size: 72,
            align: 8,
            field_offsets: vec![0, 8, 16, 20, 24, 32, 40, 48, 56, 64],
            repr: "c".to_string(),
        }
    }

    fn adt(
        name: &str,
        fields: Vec<(String, Ty)>,
        kind: Option<AdtKind>,
        rustc_layout: Option<AdtLayoutInfo>,
    ) -> Ty {
        let mut ty = Ty::adt(name, fields);
        if let Ty::Adt { adt_kind, layout, .. } = &mut ty {
            *adt_kind = kind;
            *layout = rustc_layout.map(Box::new);
        }
        ty
    }

    fn passwd(fields: Vec<(String, Ty)>) -> Ty {
        adt("libc::unix::bsd::passwd", fields, Some(AdtKind::Struct), None)
    }

    fn getpwuid() -> &'static PointerReturnContract {
        contract_named("getpwuid").expect("the getpwuid row exists")
    }

    /// rustc's layout as the compiler hands it over for the call's block: the C one.
    fn rustc() -> Option<&'static AdtLayoutInfo> {
        static LAYOUT: std::sync::OnceLock<AdtLayoutInfo> = std::sync::OnceLock::new();
        Some(LAYOUT.get_or_init(darwin_layout))
    }

    /// The real declaration lends the contract with rustc's layout of it, from the
    /// compiler (the verifying lane) or in the model (the faithful extractor), or both.
    #[test]
    fn darwin_passwd_is_getpwuid_pointee() {
        assert!(getpwuid().pointee_matches(&passwd(darwin_fields()), rustc()));
        let modeled = adt(
            "libc::unix::bsd::passwd",
            darwin_fields(),
            Some(AdtKind::Struct),
            Some(darwin_layout()),
        );
        assert!(getpwuid().pointee_matches(&modeled, None));
        assert!(getpwuid().pointee_matches(&modeled, rustc()));
        // Only the last path segment is matched: the module path is libc's internal
        // organisation, and the member list is what is checked.
        assert!(getpwuid().pointee_matches(
            &adt("libc::unix::bsd::apple::passwd", darwin_fields(), Some(AdtKind::Struct), None),
            rustc(),
        ));
    }

    /// REVIEW-A4C4-MINORS-1 fix-forward (2026-11-07): with NO layout the exact member list
    /// lends nothing. The member list cannot show a `repr`, and the verifying extractor
    /// never fills `Ty::Adt::layout`, so before this the size, alignment and offset
    /// conjunct was skipped on every compile (`layout.is_none_or(..)`): Darwin's ten
    /// members under `#[repr(C, align(16))]` (80 bytes) lent the contract.
    #[test]
    fn darwin_members_without_a_layout_are_refused() {
        assert!(!getpwuid().pointee_matches(&passwd(darwin_fields()), None));
    }

    /// The review's trigger: one pointer field and an 8 KiB tail. Refused, even with the
    /// C layout handed over (the member list refuses it).
    #[test]
    fn oversized_passwd_is_refused() {
        let fields = vec![
            ("pw_name".to_string(), char_ptr(true, true)),
            ("tail".to_string(), Ty::Array { elem: Box::new(int(64, false)), len: 1024 }),
        ];
        assert!(!getpwuid().pointee_matches(&passwd(fields), rustc()));
        // The exact members followed by the same tail: still refused.
        let mut appended = darwin_fields();
        appended
            .push(("tail".to_string(), Ty::Array { elem: Box::new(int(64, false)), len: 1024 }));
        assert!(!getpwuid().pointee_matches(&passwd(appended), rustc()));
    }

    /// Each single-member edit of the exact list is refused: rename, drop, swap, retype.
    /// The C layout is handed over, so the member list is what refuses each.
    #[test]
    fn every_edit_of_the_member_list_is_refused() {
        let n = darwin_fields().len();
        for i in 0..n {
            let mut renamed = darwin_fields();
            renamed[i].0.push('x');
            assert!(!getpwuid().pointee_matches(&passwd(renamed), rustc()), "member {i} renamed");

            let mut dropped = darwin_fields();
            dropped.remove(i);
            assert!(!getpwuid().pointee_matches(&passwd(dropped), rustc()), "member {i} dropped");

            if i + 1 < n {
                let mut swapped = darwin_fields();
                swapped.swap(i, i + 1);
                assert!(
                    !getpwuid().pointee_matches(&passwd(swapped), rustc()),
                    "members {i},{} swapped",
                    i + 1
                );
            }
        }
        let retypes: [(usize, Ty); 6] = [
            // `uid_t` as `i32` (the nto/qnx spelling).
            (2, int(32, true)),
            // `gid_t` as `u16`.
            (3, int(16, false)),
            // A 32-bit `time_t` (32-bit Darwin's `long`): no contract there.
            (4, int(32, true)),
            // `*const c_char`.
            (7, char_ptr(false, true)),
            // An unsigned `c_char`.
            (7, char_ptr(true, false)),
            // A pointer member as an integer of the same width.
            (8, int(64, false)),
        ];
        for (i, ty) in retypes {
            let mut retyped = darwin_fields();
            retyped[i].1 = ty.clone();
            assert!(
                !getpwuid().pointee_matches(&passwd(retyped), rustc()),
                "member {i} retyped as {ty:?}"
            );
        }
    }

    /// The exact member list in the wrong kind of ADT or under another tag (with the C
    /// layout handed over), or with a rustc layout that is not the C one — a `repr(C,
    /// align(16))` declaration is 80 bytes and 16-aligned; a reordering `repr(Rust)` moves
    /// members — from either channel: refused.
    #[test]
    fn wrong_kind_tag_or_layout_is_refused() {
        for kind in [None, Some(AdtKind::Union), Some(AdtKind::Enum)] {
            assert!(
                !getpwuid()
                    .pointee_matches(&adt("libc::passwd", darwin_fields(), kind, None), rustc()),
                "kind {kind:?}"
            );
        }
        assert!(!getpwuid().pointee_matches(
            &adt("libc::passwd_ex", darwin_fields(), Some(AdtKind::Struct), None),
            rustc(),
        ));
        let mut over_aligned = darwin_layout();
        over_aligned.size = 80;
        over_aligned.align = 16;
        let mut moved = darwin_layout();
        moved.field_offsets.swap(2, 3);
        for wrong in [over_aligned, moved] {
            let modeled = |layout: Option<AdtLayoutInfo>| {
                adt("libc::passwd", darwin_fields(), Some(AdtKind::Struct), layout)
            };
            // The live channel: the compiler's layout of the declaration.
            assert!(!getpwuid().pointee_matches(&modeled(None), Some(&wrong)), "{wrong:?}");
            // The model's (faithful extraction), alone or beside a right compiler one.
            assert!(!getpwuid().pointee_matches(&modeled(Some(wrong.clone())), None));
            assert!(!getpwuid().pointee_matches(&modeled(Some(wrong.clone())), rustc()));
            // A right model layout does not excuse a wrong compiler one.
            assert!(!getpwuid().pointee_matches(&modeled(Some(darwin_layout())), Some(&wrong)));
        }
        assert!(!getpwuid().pointee_matches(&int(32, true), rustc()));
    }

    /// The errno rows are unchanged: a declared `*mut i32` and nothing else.
    #[test]
    fn errno_pointee_is_unchanged() {
        let errno = contract_named("__error").expect("the __error row exists");
        assert!(errno.pointee_matches(&int(32, true), None));
        assert!(!errno.pointee_matches(&int(64, false), None));
        assert!(!errno.pointee_matches(&passwd(darwin_fields()), rustc()));
    }
}
