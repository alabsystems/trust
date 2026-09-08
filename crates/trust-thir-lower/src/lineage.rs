//! Trust (L1, artifact-lineage attestation): the per-body lineage digest.
//!
//! Before this module existed, THREE objects claimed to be "the body the flip compiled":
//! the per-body mini-module `flip_registry::record_green` stores, the row for that body in
//! the assembled crate artifact (`crate_module`), and the MIR re-derived at the flip
//! (`trust_ir_flip`). Nothing connected them — the A1 double-build pin and the A6 flip
//! event concerned DIFFERENT objects. This module mints ONE digest at the `mir_built`
//! hook, over the intact per-body mini-module PLUS its callee-identity ledger, and every
//! downstream carrier (registry entry, flip event log line, coverage row) states exactly
//! that value. "Which row of the artifact is the body the flip selected?" therefore
//! becomes a question with a mechanical answer — digest equality — instead of no answer
//! at all. Read "What this establishes, and what it does not" below before quoting that
//! anywhere: this is the plumbing that makes the correspondence STATEABLE, not a proof
//! that the assembled row is semantically the body that was proved.
//!
//! # What the digest binds
//!
//! * The body's stable DEFINITION IDENTITY (`DefPathHash`: `StableCrateId` +
//!   crate-local path hash). **v2, and it is the fix for a MEASURED collision — see
//!   "Why identity is in the framing" below.**
//! * The mini-module content, via [`Module::stable_digest`] — trust-ir's whole-module
//!   G19 build-determinism fingerprint (domain `trust_ir.module.v2`, cross-process
//!   determinism contract + conformance test `build_determinism.rs`). REUSED, not
//!   reimplemented: this module adds framing around that digest, never a second
//!   module hash.
//! * The callee-identity ledger (`Lowered::callees`), canonically framed below. The
//!   ledger is a REAL input to the flip (`to_mir::lower_ir_to_mir` spells every
//!   `TerminatorKind::Call` func operand from it), so two identical modules with
//!   different ledgers are different compile inputs and MUST digest differently.
//!
//! # Why identity is in the framing (v1 -> v2)
//!
//! v1 digested CONTENT alone, on the reasoning that a mini-module already names its body:
//! its single function is named `tcx.def_path_str(def)`, and that name is inside
//! `stable_digest`. `def_path_str` is a DISPLAY path and is **not injective over
//! `DefId`s**, and the producer says so at the naming site (`lib.rs`: *"The name is only a
//! label on this single-function module; nothing matches on it"*) — true before this
//! module existed, false the moment the name became part of an identity.
//!
//! MEASURED, at `10f221fbe5` over 200 `tests/ui` crates (1,000 coverage rows): 28 lineage
//! digests were each claimed by more than one coverage row, 148 rows in total, and in **6
//! of those collisions more than one of the colliding rows was SPLICED** — that is, one
//! digest addressed six DIFFERENT functions of the shipped artifact. In
//! `tests/ui/array-slice-vec/subslice-patterns-const-eval.rs` the digest
//! `sha256:daf66c5a…` is carried by the rows that became `func_id` 5, 9, 13, 31, 35 and 39,
//! all named `main::CONST_EVAL::{constant#0}::{const-init}` in the assembled module. The
//! mechanism is macro expansion: `compare_evaluation!` declares `const CONST_EVAL: $t = $e`
//! in several invocations, so six distinct `DefId`s share one `def_path_str`, one lowered
//! body, and — because every instruction's span points into the macro DEFINITION — one span
//! set. Nothing left in v1's framing could tell them apart.
//!
//! That is precisely the failure this module exists to prevent: "which row of the artifact
//! is the body the flip selected?" had six answers, and the flip event carries no `func_id`
//! with which to choose. No flip event in that sample carried a colliding digest (0 of 48
//! flipped bodies), so no shipped body was mis-attributed — but the colliding class is
//! `BodyKind::ConstInit`, which `flip_registry::record_green` explicitly admits for the CTFE
//! seam, so the gap was reachable, not merely present.
//!
//! Binding rustc's `DefPathHash` closes it by construction: two definitions are two
//! definitions whatever they lower to. Unlike a raw `(CrateNum, DefIndex)`, this is
//! rustc's collision-checked identity across compiler sessions and crate-graph loading
//! orders, so clean-build reproducibility does not depend on incidental index allocation.
//!
//! The two byte-strings are joined under the domain-separated
//! [`trust_ir::ProofDigest::sha256_domain`] hasher with this module's own domain, so a
//! lineage digest can never be confused with a bare module digest.
//!
//! Raw `DefId`/`CrateNum` indices still enter the framing because the flip consumes them,
//! but they are never used as a callee identity. Concrete callees carry a
//! [`ConcreteCalleeKey`] made from collision-checked [`DefinitionIdentity`] values and a
//! typed, region-erased encoding of their normalized generic arguments. This distinction
//! is load-bearing: raw indices are session-local reconstruction data; the concrete key is
//! the cross-body declaration/interning identity.
//!
//! # Where the value surfaces
//!
//! | carrier | field | minted at |
//! |---|---|---|
//! | flip registry entry | [`crate::flip_registry::GreenBody::lineage`] | `record_green` |
//! | flip event (`info!` "compiled from trust-ir") | `lineage` | logged at `try_flip` / `try_flip_ctfe`, after re-derivation |
//! | published coverage row | `lineage` (+ `func_id`, the row's index into the assembled `module.functions`) | `crate_module::record`, before assembly |
//!
//! The coverage sidecar is not a loose companion: `artifact_publication` commits the
//! binary module, the canonical text, and `coverage.json` as ONE set behind a single
//! commit marker, so a consumer that sees the marker sees a row set that belongs to that
//! binary.
//!
//! # Fail-closed
//!
//! No digest, no green: `flip_registry::green_body` — the sole constructor of a registry
//! entry — refuses when this computation refuses (e.g. a mini-module that does not carry
//! exactly one function), so a flip event can never fire without a lineage digest to log. And the flip RE-DERIVES the digest from the payload it took and
//! declines on any mismatch ([`crate::flip::derive_flip_body`]), so the value the event
//! publishes always describes the bytes that event is about.
//!
//! # What this establishes, and what it does not
//!
//! ESTABLISHED: the object the flip compiled and the object the artifact row was built
//! from are the same PRE-ASSEMBLY value, and that value is named by a digest that is
//! reproducible across processes (trust-ir's G19 contract) and that changes if either the
//! module content or the callee ledger changes.
//!
//! NOT ESTABLISHED (do not read the digest as more than it is):
//!
//! * **The canonical-remapping certificate.** Assembly sorts bodies, assigns fresh dense
//!   `FuncId`s, re-interns type/enum/struct tables and rewrites callees. The row's
//!   `func_id` ADDRESSES the resulting function, and the row's `lineage` NAMES the input
//!   it came from — but nothing here proves the assembled function still means what the
//!   pre-assembly mini-module meant. That proof does not exist. The digest is what makes
//!   it stateable (both sides now name one object); it does not discharge it.
//! * **Tamper evidence.** The registry is in-process Session state and the flip event is
//!   a `tracing` line. This is a lineage record for a cooperating toolchain, not a signed
//!   attestation against an adversary who controls the compiler.
//! * **Anything about the emitted machine code.** The digest binds trust-ir to trust-ir.
//!   The MIR→codegen leg below it is the differential gate's business, not this module's.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com> | Copyright 2026 | License: MIT OR Apache-2.0

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use trust_ir::{Module, ProofDigest};

use crate::{CalleeRef, SiteArg, SiteConst, SiteTy, SiteValTree};

/// Domain tag for the lineage digest. Versioned: any change to the framing below MUST
/// bump the suffix so old and new digests can never collide silently. `v3` adds the
/// stable concrete-callee key and replaces DefIndex-derived callee ids with body-local
/// interned ids.
pub const BODY_LINEAGE_DOMAIN: &str = "trust_thir_lower.body_lineage.v3";

/// Collision-checked, cross-session identity of the definition whose body is
/// being attested. The components are exactly rustc's `DefPathHash` halves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefinitionIdentity {
    stable_crate_id: u64,
    local_hash: u64,
}

impl DefinitionIdentity {
    /// Obtain rustc's stable identity for `def`; do not substitute a display
    /// path or raw `DefId`, both of which are non-injective across the scope the
    /// lineage digest claims to cover.
    pub(crate) fn from_def_id(tcx: TyCtxt<'_>, def: DefId) -> Self {
        let hash = tcx.def_path_hash(def);
        Self {
            stable_crate_id: hash.stable_crate_id().as_u64(),
            local_hash: hash.local_hash().as_u64(),
        }
    }

    pub(crate) fn symbol_suffix(self) -> String {
        format!("{:016x}{:016x}", self.stable_crate_id, self.local_hash)
    }

    #[cfg(test)]
    pub(crate) const fn test_only(stable_crate_id: u64, local_hash: u64) -> Self {
        Self { stable_crate_id, local_hash }
    }
}

/// The rustc instance category whose semantics a concrete callee key denotes.
///
/// `Item` and `ReifyShim` are deliberately distinct even when they forward to the same
/// definition and carry equal args: taking the address of a reify shim is a different
/// codegen object from calling the item directly. Every unsupported `InstanceKind` stays
/// outside this enum and therefore cannot accidentally acquire a concrete key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConcreteInstanceKind {
    Item,
    ReifyShim,
}

/// Stable, typed generic-argument identity for one concrete rustc instance.
///
/// This intentionally does not reuse [`SiteArg`]. `SiteArg` is reconstruction data and
/// therefore contains raw `DefId`s for ADTs; an inter-body declaration key must instead
/// use collision-checked definition identities. Regions are absent/erased by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteInstanceArg {
    ErasedRegion,
    Ty(ConcreteInstanceTy),
    Const(ConcreteInstanceConst),
}

/// Trust (wave-DY): the stable-identity mirror of `SiteExistentialPredicate`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteExistentialPredicate {
    Trait(DefinitionIdentity, Vec<ConcreteInstanceArg>),
    Projection(DefinitionIdentity, Vec<ConcreteInstanceArg>, Box<ConcreteTerm>),
    AutoTrait(DefinitionIdentity),
}

/// Trust (wave-DY): the stable-identity mirror of `SiteTerm`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteTerm {
    Ty(ConcreteInstanceTy),
    Const(ConcreteInstanceConst),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteInstanceConst {
    Value(ConcreteInstanceTy, ConcreteInstanceValTree),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteInstanceValTree {
    Leaf(u128, u64),
    Branch(Vec<ConcreteInstanceConst>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteInstanceTy {
    Bool,
    Char,
    Str,
    Int(rustc_middle::ty::IntTy),
    Uint(rustc_middle::ty::UintTy),
    Float(rustc_middle::ty::FloatTy),
    /// Trust (wave-AA): args are POSITIONAL and kind-tagged, mirroring `SiteTy::Adt` — a
    /// `Vec<ConcreteInstanceTy>` could not record that arg *k* was a lifetime or a const, and
    /// two instances differing only there must not digest equal.
    Adt(DefinitionIdentity, Vec<ConcreteInstanceArg>),
    Tuple(Vec<ConcreteInstanceTy>),
    Array(Box<ConcreteInstanceTy>, u64),
    Slice(Box<ConcreteInstanceTy>),
    Ref(Box<ConcreteInstanceTy>, rustc_middle::ty::Mutability),
    /// Trust (wave-RP): the raw-pointer counterpart of [`ConcreteInstanceTy::Ref`]. A distinct
    /// variant, never folded into `Ref`: `*const T` and `&T` are different types and two
    /// instances differing only in that must not digest equal.
    RawPtr(Box<ConcreteInstanceTy>, rustc_middle::ty::Mutability),
    /// Trust (wave-FD): a fn ITEM — `DefinitionIdentity` + positional args, the `Adt` shape.
    FnDef(DefinitionIdentity, Vec<ConcreteInstanceArg>),
    /// Trust (wave-FP): a fn POINTER — binder-erased signature plus the header's observable
    /// facts (see `SiteTy::FnPtr`). The header is part of the identity: two fn pointers that
    /// differ only in ABI or safety are different types and must not digest equal.
    /// Trust (wave-CL): a closure-family type — kind + identity + positional args.
    ClosureLike(crate::SiteClosureKind, DefinitionIdentity, Vec<ConcreteInstanceArg>),
    /// Trust (wave-DY): a trait object as its predicate list, region erased.
    Dynamic(Vec<ConcreteExistentialPredicate>),
    FnPtr {
        inputs_and_output: Vec<ConcreteInstanceTy>,
        abi: String,
        safe: bool,
        c_variadic: bool,
        splatted: Option<u8>,
    },
}

/// Collision-checked identity of one concrete callee instance.
///
/// Signatures and display names are facts checked against this key, never constituents of
/// it. In particular, `pick::<1>` and `pick::<2>` remain different keys even when their
/// lowered `FuncTy`s are byte-identical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConcreteCalleeKey {
    definition: DefinitionIdentity,
    kind: ConcreteInstanceKind,
    args: Vec<ConcreteInstanceArg>,
}

impl ConcreteCalleeKey {
    /// Convert the already-normalized, region-erased reconstruction encoding into a stable
    /// declaration key. The caller must pass args from the resolved rustc `Instance`, not
    /// the raw MIR site spelling.
    pub(crate) fn from_site_args(
        tcx: TyCtxt<'_>,
        def: DefId,
        kind: ConcreteInstanceKind,
        args: &[SiteArg],
    ) -> Self {
        Self {
            definition: DefinitionIdentity::from_def_id(tcx, def),
            kind,
            args: args.iter().map(|arg| stable_arg(tcx, arg)).collect(),
        }
    }

    /// An injective, canonical symbol suffix. This is the full typed key encoded as hex,
    /// not a display path, `Debug` rendering, raw `DefId`, or truncated hash. Distinct keys
    /// therefore cannot silently retain one display name when assembly must emit both.
    pub(crate) fn symbol_suffix(&self) -> String {
        let mut bytes = Vec::new();
        encode_concrete_callee_key(&mut bytes, self);
        let mut out = String::with_capacity(bytes.len() * 2);
        const HEX: &[u8; 16] = b"0123456789abcdef";
        for byte in bytes {
            out.push(HEX[(byte >> 4) as usize] as char);
            out.push(HEX[(byte & 0x0f) as usize] as char);
        }
        out
    }

    pub(crate) fn has_generic_args(&self) -> bool {
        !self.args.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn test_only(
        definition: DefinitionIdentity,
        kind: ConcreteInstanceKind,
        args: Vec<ConcreteInstanceArg>,
    ) -> Self {
        Self {
            definition,
            kind,
            args,
        }
    }
}

fn stable_arg(tcx: TyCtxt<'_>, arg: &SiteArg) -> ConcreteInstanceArg {
    match arg {
        SiteArg::ErasedRegion => ConcreteInstanceArg::ErasedRegion,
        SiteArg::Ty(ty) => ConcreteInstanceArg::Ty(stable_ty(tcx, ty)),
        SiteArg::Const(c) => ConcreteInstanceArg::Const(stable_const(tcx, c)),
    }
}

fn stable_const(tcx: TyCtxt<'_>, c: &SiteConst) -> ConcreteInstanceConst {
    let SiteConst::Value(ty, value) = c;
    ConcreteInstanceConst::Value(stable_ty(tcx, ty), stable_valtree(tcx, value))
}

fn stable_valtree(tcx: TyCtxt<'_>, value: &SiteValTree) -> ConcreteInstanceValTree {
    match value {
        SiteValTree::Leaf(bits, size) => ConcreteInstanceValTree::Leaf(*bits, *size),
        SiteValTree::Branch(values) => ConcreteInstanceValTree::Branch(
            values
                .iter()
                .map(|value| stable_const(tcx, value))
                .collect(),
        ),
    }
}

fn stable_ty(tcx: TyCtxt<'_>, ty: &SiteTy) -> ConcreteInstanceTy {
    match ty {
        SiteTy::Bool => ConcreteInstanceTy::Bool,
        SiteTy::Char => ConcreteInstanceTy::Char,
        SiteTy::Str => ConcreteInstanceTy::Str,
        SiteTy::Int(value) => ConcreteInstanceTy::Int(*value),
        SiteTy::Uint(value) => ConcreteInstanceTy::Uint(*value),
        SiteTy::Float(value) => ConcreteInstanceTy::Float(*value),
        SiteTy::Adt(def, args) => ConcreteInstanceTy::Adt(
            DefinitionIdentity::from_def_id(tcx, *def),
            args.iter().map(|arg| stable_arg(tcx, arg)).collect(),
        ),
        SiteTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted } => {
            ConcreteInstanceTy::FnPtr {
                inputs_and_output: inputs_and_output
                    .iter()
                    .map(|t| stable_ty(tcx, t))
                    .collect(),
                abi: abi.clone(),
                safe: *safe,
                c_variadic: *c_variadic,
                splatted: *splatted,
            }
        }
        SiteTy::Dynamic(preds) => ConcreteInstanceTy::Dynamic(
            preds
                .iter()
                .map(|p| match p {
                    crate::SiteExistentialPredicate::Trait(did, args) => {
                        ConcreteExistentialPredicate::Trait(
                            DefinitionIdentity::from_def_id(tcx, *did),
                            args.iter().map(|a| stable_arg(tcx, a)).collect(),
                        )
                    }
                    crate::SiteExistentialPredicate::Projection(did, args, term) => {
                        ConcreteExistentialPredicate::Projection(
                            DefinitionIdentity::from_def_id(tcx, *did),
                            args.iter().map(|a| stable_arg(tcx, a)).collect(),
                            Box::new(match &**term {
                                crate::SiteTerm::Ty(t) => ConcreteTerm::Ty(stable_ty(tcx, t)),
                                crate::SiteTerm::Const(c) => {
                                    ConcreteTerm::Const(stable_const(tcx, c))
                                }
                            }),
                        )
                    }
                    crate::SiteExistentialPredicate::AutoTrait(did) => {
                        ConcreteExistentialPredicate::AutoTrait(DefinitionIdentity::from_def_id(
                            tcx, *did,
                        ))
                    }
                })
                .collect(),
        ),
        SiteTy::ClosureLike(kind, def, args) => ConcreteInstanceTy::ClosureLike(
            *kind,
            DefinitionIdentity::from_def_id(tcx, *def),
            args.iter().map(|arg| stable_arg(tcx, arg)).collect(),
        ),
        SiteTy::FnDef(def, args) => ConcreteInstanceTy::FnDef(
            DefinitionIdentity::from_def_id(tcx, *def),
            args.iter().map(|arg| stable_arg(tcx, arg)).collect(),
        ),
        SiteTy::Tuple(values) => {
            ConcreteInstanceTy::Tuple(values.iter().map(|value| stable_ty(tcx, value)).collect())
        }
        SiteTy::Array(elem, len) => ConcreteInstanceTy::Array(Box::new(stable_ty(tcx, elem)), *len),
        SiteTy::Slice(elem) => ConcreteInstanceTy::Slice(Box::new(stable_ty(tcx, elem))),
        SiteTy::Ref(pointee, mutability) => {
            ConcreteInstanceTy::Ref(Box::new(stable_ty(tcx, pointee)), *mutability)
        }
        SiteTy::RawPtr(pointee, mutability) => {
            ConcreteInstanceTy::RawPtr(Box::new(stable_ty(tcx, pointee)), *mutability)
        }
    }
}

/// Compute the lineage digest of one body: its definition identity, its per-body
/// mini-module, and its callee ledger.
///
/// MUST be called on the INTACT hook-time `Lowered` (before `crate_module::record`
/// removes `functions[0]` for assembly) — the whole point is that `record_green`,
/// `crate_module::record`, and therefore the flip event and the coverage row, all
/// digest the SAME object.
///
/// `definition` is the body's own stable `DefPathHash` identity, and it is the FIRST
/// thing framed: content alone does not identify a body (measured — see the module docs),
/// so a digest that omitted it could name several functions of one artifact at once.
///
/// Fails closed (`Err`) when the module does not carry exactly one function: a
/// body-less or multi-function module is not a per-body lowering, and attesting it
/// would name the wrong object.
pub fn body_lineage_digest(
    definition: DefinitionIdentity,
    module: &Module,
    callees: &[CalleeRef],
) -> Result<ProofDigest, String> {
    if module.functions.len() != 1 {
        return Err(format!(
            "per-body lineage digest requires exactly one function in the mini-module, found {}",
            module.functions.len()
        ));
    }
    let module_digest = module.stable_digest();
    let mut bytes = Vec::with_capacity(16 + 32 + 8 + callees.len() * 64);
    encode_u64(&mut bytes, definition.stable_crate_id);
    encode_u64(&mut bytes, definition.local_hash);
    bytes.extend_from_slice(&module_digest.bytes);
    encode_u64(&mut bytes, callees.len() as u64);
    for callee in callees {
        encode_callee(&mut bytes, callee);
    }
    Ok(ProofDigest::sha256_domain(BODY_LINEAGE_DOMAIN, &bytes))
}

fn encode_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_be_bytes());
}

fn encode_u64(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_be_bytes());
}

/// Length-prefixed UTF-8 — unambiguous concatenation (no delimiter injection).
fn encode_str(out: &mut Vec<u8>, s: &str) {
    encode_u64(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

fn encode_bool(out: &mut Vec<u8>, b: bool) {
    out.push(u8::from(b));
}

fn encode_def_id(out: &mut Vec<u8>, def_id: DefId) {
    encode_u32(out, def_id.krate.as_u32());
    encode_u32(out, def_id.index.as_u32());
}

fn encode_definition_identity(out: &mut Vec<u8>, identity: DefinitionIdentity) {
    encode_u64(out, identity.stable_crate_id);
    encode_u64(out, identity.local_hash);
}

fn encode_concrete_callee_key(out: &mut Vec<u8>, key: &ConcreteCalleeKey) {
    // Version byte for the standalone/injective symbol encoding. The enclosing lineage
    // domain is independently versioned.
    out.push(1);
    encode_definition_identity(out, key.definition);
    out.push(match key.kind {
        ConcreteInstanceKind::Item => 0,
        ConcreteInstanceKind::ReifyShim => 1,
    });
    encode_u64(out, key.args.len() as u64);
    for arg in &key.args {
        encode_concrete_arg(out, arg);
    }
}

fn encode_concrete_arg(out: &mut Vec<u8>, arg: &ConcreteInstanceArg) {
    match arg {
        ConcreteInstanceArg::ErasedRegion => out.push(0),
        ConcreteInstanceArg::Ty(ty) => {
            out.push(1);
            encode_concrete_ty(out, ty);
        }
        ConcreteInstanceArg::Const(value) => {
            out.push(2);
            encode_concrete_const(out, value);
        }
    }
}

fn encode_concrete_const(out: &mut Vec<u8>, value: &ConcreteInstanceConst) {
    let ConcreteInstanceConst::Value(ty, tree) = value;
    encode_concrete_ty(out, ty);
    encode_concrete_valtree(out, tree);
}

fn encode_concrete_valtree(out: &mut Vec<u8>, tree: &ConcreteInstanceValTree) {
    match tree {
        ConcreteInstanceValTree::Leaf(bits, size) => {
            out.push(0);
            out.extend_from_slice(&bits.to_be_bytes());
            encode_u64(out, *size);
        }
        ConcreteInstanceValTree::Branch(values) => {
            out.push(1);
            encode_u64(out, values.len() as u64);
            for value in values {
                encode_concrete_const(out, value);
            }
        }
    }
}

fn encode_concrete_ty(out: &mut Vec<u8>, ty: &ConcreteInstanceTy) {
    match ty {
        ConcreteInstanceTy::Bool => out.push(0),
        ConcreteInstanceTy::Char => out.push(1),
        ConcreteInstanceTy::Str => out.push(2),
        ConcreteInstanceTy::Int(value) => {
            out.push(3);
            encode_str(out, value.name_str());
        }
        ConcreteInstanceTy::Uint(value) => {
            out.push(4);
            encode_str(out, value.name_str());
        }
        ConcreteInstanceTy::Float(value) => {
            out.push(5);
            encode_str(out, value.name_str());
        }
        // Trust (wave-AA): the arg stream is SELF-DISCRIMINATING and byte-compatible. A TYPE
        // arg emits its own `encode_concrete_ty` bytes, whose first byte is a type tag in
        // 0..=11 — so an ADT whose args are all types encodes BYTE-IDENTICALLY to before this
        // wave and its lineage digest does not move (the wave-CRT discipline, which link 2c's
        // pinned digests depend on). A lifetime emits the reserved tag 12 and a const the
        // reserved tag 13, neither of which any `encode_concrete_ty` can produce.
        ConcreteInstanceTy::Adt(definition, args) => {
            out.push(6);
            encode_definition_identity(out, *definition);
            encode_u64(out, args.len() as u64);
            for arg in args {
                match arg {
                    ConcreteInstanceArg::Ty(ty) => encode_concrete_ty(out, ty),
                    ConcreteInstanceArg::ErasedRegion => out.push(12),
                    ConcreteInstanceArg::Const(value) => {
                        out.push(13);
                        encode_concrete_const(out, value);
                    }
                }
            }
        }
        ConcreteInstanceTy::Tuple(values) => {
            out.push(7);
            encode_u64(out, values.len() as u64);
            for value in values {
                encode_concrete_ty(out, value);
            }
        }
        ConcreteInstanceTy::Array(elem, len) => {
            out.push(8);
            encode_concrete_ty(out, elem);
            encode_u64(out, *len);
        }
        ConcreteInstanceTy::Slice(elem) => {
            out.push(9);
            encode_concrete_ty(out, elem);
        }
        ConcreteInstanceTy::Ref(pointee, mutability) => {
            out.push(10);
            out.push(match mutability {
                rustc_middle::ty::Mutability::Not => 0,
                rustc_middle::ty::Mutability::Mut => 1,
            });
            encode_concrete_ty(out, pointee);
        }
        // Trust (wave-RP): tag 11, APPENDED on the wave-CRT discipline — tags 0..=10 keep
        // their meaning, so a body whose instance args contain no raw pointer encodes
        // BYTE-IDENTICALLY to before this wave and its lineage digest does not move. A
        // distinct tag from `Ref`'s 10 is what keeps `*const T` and `&T` from digesting equal.
        // Trust (wave-FD): tag 14. Tags 12 and 13 are PERMANENTLY RESERVED as the ADT/FnDef
        // arg-stream markers for a lifetime and a const (see the Adt arm) — a type tag may
        // never take either, or an arg that is itself a fn item would be indistinguishable
        // from a region marker.
        // Trust (wave-FP): tag 15. Every header fact is framed — two fn pointers differing
        // only in ABI or safety are different types and must not share a lineage.
        ConcreteInstanceTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted } => {
            out.push(15);
            encode_str(out, abi);
            out.push(u8::from(*safe));
            out.push(u8::from(*c_variadic));
            match splatted {
                None => out.push(0),
                Some(i) => {
                    out.push(1);
                    out.push(*i);
                }
            }
            encode_u64(out, inputs_and_output.len() as u64);
            for t in inputs_and_output {
                encode_concrete_ty(out, t);
            }
        }
        // Trust (wave-DY): tag 17. Every predicate is framed with its own discriminator, and
        // the LIST ORDER is preserved — rustc keeps an object's predicates in a canonical
        // order, so two objects that differ only in that order are different types.
        ConcreteInstanceTy::Dynamic(preds) => {
            out.push(17);
            encode_u64(out, preds.len() as u64);
            for p in preds {
                match p {
                    ConcreteExistentialPredicate::Trait(definition, args) => {
                        out.push(0);
                        encode_definition_identity(out, *definition);
                        encode_u64(out, args.len() as u64);
                        for a in args {
                            encode_concrete_arg(out, a);
                        }
                    }
                    ConcreteExistentialPredicate::Projection(definition, args, term) => {
                        out.push(1);
                        encode_definition_identity(out, *definition);
                        encode_u64(out, args.len() as u64);
                        for a in args {
                            encode_concrete_arg(out, a);
                        }
                        match &**term {
                            ConcreteTerm::Ty(t) => {
                                out.push(0);
                                encode_concrete_ty(out, t);
                            }
                            ConcreteTerm::Const(c) => {
                                out.push(1);
                                encode_concrete_const(out, c);
                            }
                        }
                    }
                    ConcreteExistentialPredicate::AutoTrait(definition) => {
                        out.push(2);
                        encode_definition_identity(out, *definition);
                    }
                }
            }
        }
        // Trust (wave-CL): tag 16 plus a KIND byte — a closure and a coroutine sharing a
        // DefId (they cannot, but the encoding does not rely on that) stay distinguishable.
        ConcreteInstanceTy::ClosureLike(kind, definition, args) => {
            out.push(16);
            out.push(match kind {
                crate::SiteClosureKind::Closure => 0,
                crate::SiteClosureKind::CoroutineClosure => 1,
                crate::SiteClosureKind::Coroutine => 2,
                crate::SiteClosureKind::CoroutineWitness => 3,
            });
            encode_definition_identity(out, *definition);
            encode_u64(out, args.len() as u64);
            for arg in args {
                match arg {
                    ConcreteInstanceArg::Ty(ty) => encode_concrete_ty(out, ty),
                    ConcreteInstanceArg::ErasedRegion => out.push(12),
                    ConcreteInstanceArg::Const(value) => {
                        out.push(13);
                        encode_concrete_const(out, value);
                    }
                }
            }
        }
        ConcreteInstanceTy::FnDef(definition, args) => {
            out.push(14);
            encode_definition_identity(out, *definition);
            encode_u64(out, args.len() as u64);
            for arg in args {
                match arg {
                    ConcreteInstanceArg::Ty(ty) => encode_concrete_ty(out, ty),
                    ConcreteInstanceArg::ErasedRegion => out.push(12),
                    ConcreteInstanceArg::Const(value) => {
                        out.push(13);
                        encode_concrete_const(out, value);
                    }
                }
            }
        }
        ConcreteInstanceTy::RawPtr(pointee, mutability) => {
            out.push(11);
            out.push(match mutability {
                rustc_middle::ty::Mutability::Not => 0,
                rustc_middle::ty::Mutability::Mut => 1,
            });
            encode_concrete_ty(out, pointee);
        }
    }
}

/// Every field of [`CalleeRef`] enters the framing — the ledger decides how the shim
/// spells calls at flip time, so omitting a field would let two different compile
/// inputs share a digest. Field order is struct declaration order; bind by full
/// destructure so a future field cannot silently escape the digest.
fn encode_callee(out: &mut Vec<u8>, callee: &CalleeRef) {
    let CalleeRef {
        func_id,
        is_local,
        def_index,
        def_id,
        definition,
        concrete_key,
        def_path,
        force_havoc,
        site_def_id,
        site_args,
        ret_ty,
        ret_ty_conflict,
        is_rust_abi,
    } = callee;
    encode_u32(out, func_id.index());
    encode_bool(out, *is_local);
    encode_u32(out, *def_index);
    encode_def_id(out, *def_id);
    encode_definition_identity(out, *definition);
    match concrete_key {
        None => out.push(0),
        Some(key) => {
            out.push(1);
            encode_concrete_callee_key(out, key);
        }
    }
    encode_str(out, def_path);
    encode_bool(out, *force_havoc);
    encode_def_id(out, *site_def_id);
    match site_args {
        None => out.push(0),
        Some(args) => {
            out.push(1);
            encode_u64(out, args.len() as u64);
            for arg in args {
                encode_site_arg(out, arg);
            }
        }
    }
    // Trust (#178): the agreed call-result type and its poison flag DO enter the digest — they
    // pick the bodyless declaration's signature at crate assembly, so two inputs that differ only
    // here produce different modules. `{:?}` is sufficient framing: `Ty` is a closed enum whose
    // Debug is injective for the table-free fragment this field is restricted to, and the length
    // prefix in `encode_str` keeps it unambiguous against the neighbouring fields.
    match ret_ty {
        None => out.push(0),
        Some(t) => {
            out.push(1);
            encode_str(out, &format!("{t:?}"));
        }
    }
    encode_bool(out, *ret_ty_conflict);
    // Trust (#180): picks the declaration's `calling_conv`, so it changes the emitted module.
    encode_bool(out, *is_rust_abi);
}

fn encode_site_arg(out: &mut Vec<u8>, arg: &SiteArg) {
    match arg {
        SiteArg::ErasedRegion => out.push(0),
        SiteArg::Ty(t) => {
            out.push(1);
            encode_site_ty(out, t);
        }
        // Trust (#197 follow-up): a CONST arg. It MUST be framed — two sites that differ only in
        // a const arg (`Bar::<2, _>` vs `Bar::<3, _>`) are different callee identities, and a
        // digest that dropped the const would give them one lineage.
        SiteArg::Const(c) => {
            out.push(2);
            encode_site_const(out, c);
        }
    }
}

/// Same discriminant-tagged framing as [`encode_site_ty`], and bounded the same way: the encoder
/// (`crate::encode_site_const`) is depth-capped and only admits `ConstKind::Value`, so the tree
/// here is finite. The leaf carries the WIDTH alongside the bits because they are jointly the
/// value's identity — `1u8` and `1u64` are different consts.
fn encode_site_const(out: &mut Vec<u8>, c: &SiteConst) {
    let SiteConst::Value(ty, vt) = c;
    encode_site_ty(out, ty);
    encode_site_valtree(out, vt);
}

fn encode_site_valtree(out: &mut Vec<u8>, vt: &SiteValTree) {
    match vt {
        SiteValTree::Leaf(bits, size_bytes) => {
            out.push(0);
            out.extend_from_slice(&bits.to_le_bytes());
            out.extend_from_slice(&size_bytes.to_le_bytes());
        }
        SiteValTree::Branch(elems) => {
            out.push(1);
            out.extend_from_slice(&(elems.len() as u64).to_le_bytes());
            for e in elems {
                encode_site_const(out, e);
            }
        }
    }
}

/// Discriminant-tagged recursive framing. `SiteTy` is the finite region/const-free
/// fragment (`encode_ty` fails closed on anything else), so recursion is bounded by
/// the encoded type's own structure.
fn encode_site_ty(out: &mut Vec<u8>, t: &SiteTy) {
    match t {
        SiteTy::Bool => out.push(0),
        SiteTy::Char => out.push(1),
        SiteTy::Str => out.push(2),
        SiteTy::Int(i) => {
            out.push(3);
            encode_str(out, i.name_str());
        }
        SiteTy::Uint(u) => {
            out.push(4);
            encode_str(out, u.name_str());
        }
        SiteTy::Float(f) => {
            out.push(5);
            encode_str(out, f.name_str());
        }
        // Trust (wave-AA): same self-discriminating arg stream as the concrete encoder — a
        // type arg keeps its own tag (0..=11, so all-type ADTs stay byte-identical), a
        // lifetime is the reserved 12, a const the reserved 13.
        SiteTy::Adt(did, args) => {
            out.push(6);
            encode_def_id(out, *did);
            encode_u64(out, args.len() as u64);
            for a in args {
                match a {
                    SiteArg::Ty(t) => encode_site_ty(out, t),
                    SiteArg::ErasedRegion => out.push(12),
                    SiteArg::Const(c) => {
                        out.push(13);
                        encode_site_const(out, c);
                    }
                }
            }
        }
        SiteTy::Tuple(ts) => {
            out.push(7);
            encode_u64(out, ts.len() as u64);
            for a in ts {
                encode_site_ty(out, a);
            }
        }
        SiteTy::Array(elem, len) => {
            out.push(8);
            encode_site_ty(out, elem);
            encode_u64(out, *len);
        }
        SiteTy::Slice(elem) => {
            out.push(9);
            encode_site_ty(out, elem);
        }
        // Trust (wave-CRT): a reference. Tag 10 is APPENDED, never inserted: tags 0..=9 keep
        // their meaning, so every body whose site args contain no reference encodes
        // BYTE-IDENTICALLY to before this wave and its lineage digest does not move. That is
        // load-bearing — link 2c pins those digests, and a renumbering would churn every one of
        // them for a change that does not affect them.
        //
        // The REGION is absent by construction (`SiteTy::Ref` does not carry one), so the digest
        // is region-blind here exactly as the comparator is.
        SiteTy::Ref(pointee, mutbl) => {
            out.push(10);
            out.push(match mutbl {
                rustc_middle::ty::Mutability::Not => 0,
                rustc_middle::ty::Mutability::Mut => 1,
            });
            encode_site_ty(out, pointee);
        }
        // Trust (wave-RP): tag 11, appended on the same discipline. Unlike `Ref` this encoding
        // is EXACT rather than region-blind — a raw pointer carries no region at all.
        // Trust (wave-FD): tag 14; 12/13 stay reserved as the arg-stream markers.
        // Trust (wave-FP): tag 15, same framing as the concrete encoder.
        SiteTy::FnPtr { inputs_and_output, abi, safe, c_variadic, splatted } => {
            out.push(15);
            encode_str(out, abi);
            out.push(u8::from(*safe));
            out.push(u8::from(*c_variadic));
            match splatted {
                None => out.push(0),
                Some(i) => {
                    out.push(1);
                    out.push(*i);
                }
            }
            encode_u64(out, inputs_and_output.len() as u64);
            for t in inputs_and_output {
                encode_site_ty(out, t);
            }
        }
        // Trust (wave-DY): tag 17, same framing as the concrete encoder.
        SiteTy::Dynamic(preds) => {
            out.push(17);
            encode_u64(out, preds.len() as u64);
            for p in preds {
                match p {
                    crate::SiteExistentialPredicate::Trait(did, args) => {
                        out.push(0);
                        encode_def_id(out, *did);
                        encode_u64(out, args.len() as u64);
                        for a in args {
                            encode_site_arg(out, a);
                        }
                    }
                    crate::SiteExistentialPredicate::Projection(did, args, term) => {
                        out.push(1);
                        encode_def_id(out, *did);
                        encode_u64(out, args.len() as u64);
                        for a in args {
                            encode_site_arg(out, a);
                        }
                        match &**term {
                            crate::SiteTerm::Ty(t) => {
                                out.push(0);
                                encode_site_ty(out, t);
                            }
                            crate::SiteTerm::Const(c) => {
                                out.push(1);
                                encode_site_const(out, c);
                            }
                        }
                    }
                    crate::SiteExistentialPredicate::AutoTrait(did) => {
                        out.push(2);
                        encode_def_id(out, *did);
                    }
                }
            }
        }
        // Trust (wave-CL): tag 16 + kind byte, same framing as the concrete encoder.
        SiteTy::ClosureLike(kind, did, args) => {
            out.push(16);
            out.push(match kind {
                crate::SiteClosureKind::Closure => 0,
                crate::SiteClosureKind::CoroutineClosure => 1,
                crate::SiteClosureKind::Coroutine => 2,
                crate::SiteClosureKind::CoroutineWitness => 3,
            });
            encode_def_id(out, *did);
            encode_u64(out, args.len() as u64);
            for a in args {
                match a {
                    SiteArg::Ty(t) => encode_site_ty(out, t),
                    SiteArg::ErasedRegion => out.push(12),
                    SiteArg::Const(c) => {
                        out.push(13);
                        encode_site_const(out, c);
                    }
                }
            }
        }
        SiteTy::FnDef(did, args) => {
            out.push(14);
            encode_def_id(out, *did);
            encode_u64(out, args.len() as u64);
            for a in args {
                match a {
                    SiteArg::Ty(t) => encode_site_ty(out, t),
                    SiteArg::ErasedRegion => out.push(12),
                    SiteArg::Const(c) => {
                        out.push(13);
                        encode_site_const(out, c);
                    }
                }
            }
        }
        SiteTy::RawPtr(pointee, mutbl) => {
            out.push(11);
            out.push(match mutbl {
                rustc_middle::ty::Mutability::Not => 0,
                rustc_middle::ty::Mutability::Mut => 1,
            });
            encode_site_ty(out, pointee);
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_span::def_id::{CrateNum, DefId, DefIndex};
    use trust_ir::{BlockId, FuncId, FuncTy, Function, Module};

    use super::{
        ConcreteCalleeKey, ConcreteInstanceArg, ConcreteInstanceConst, ConcreteInstanceKind,
        ConcreteInstanceTy, ConcreteInstanceValTree, DefinitionIdentity, body_lineage_digest,
    };
    use crate::CalleeRef;

    fn probe_module(fn_name: &str) -> Module {
        let mut module = Module::new("lineage_probe");
        let ty = module.add_func_type(FuncTy {
            params: Vec::new(),
            returns: Vec::new(),
            is_vararg: false,
        });
        module.add_function(Function::new(FuncId::new(0), fn_name, ty, BlockId::new(0)));
        module
    }

    /// Stable definition identity under test. Production obtains these halves from
    /// `TyCtxt::def_path_hash`; unit fixtures supply collision-free synthetic values.
    fn probe_definition(local_hash: u64) -> DefinitionIdentity {
        DefinitionIdentity::test_only(0xC0DE, local_hash)
    }

    fn probe_callee(force_havoc: bool) -> CalleeRef {
        let def_id = DefId {
            krate: CrateNum::from_u32(0),
            index: DefIndex::from_u32(7),
        };
        let definition = probe_definition(7);
        CalleeRef {
            func_id: FuncId::new(1),
            is_local: true,
            def_index: 7,
            def_id,
            definition,
            concrete_key: Some(ConcreteCalleeKey::test_only(
                definition,
                ConcreteInstanceKind::Item,
                Vec::new(),
            )),
            def_path: "lineage_probe::callee".to_string(),
            force_havoc,
            site_def_id: def_id,
            site_args: Some(Vec::new()),
            // Trust (#178): the UNKNOWN spelling, byte-identical to what
            // `admit_callee` writes (see the `self.callees.push` site in `lib.rs`)
            // — a callee no site has bound a result from. This probe is about the
            // lineage digest, so it must use the producer's own default rather
            // than invent a return type the digest would then depend on.
            ret_ty: None,
            ret_ty_conflict: false,
            // Trust (#180): `is_local: true` above, so the producer's own rule
            // (`is_rust_abi: !def_id.is_local() && ..`, `lib.rs`) writes `false`
            // here too — the probe must not invent an ABI the digest depends on.
            is_rust_abi: false,
        }
    }

    fn const_u32_key(value: u128) -> ConcreteCalleeKey {
        ConcreteCalleeKey::test_only(
            probe_definition(11),
            ConcreteInstanceKind::Item,
            vec![ConcreteInstanceArg::Const(ConcreteInstanceConst::Value(
                ConcreteInstanceTy::Uint(rustc_middle::ty::UintTy::U32),
                ConcreteInstanceValTree::Leaf(value, 4),
            ))],
        )
    }

    /// `pick::<1>` and `pick::<2>` have identical function types but are different semantic
    /// instances. Their canonical declaration identity must bind the typed const payload.
    #[test]
    fn test_concrete_key_distinguishes_same_signature_const_instances() {
        let one = const_u32_key(1);
        let two = const_u32_key(2);
        assert_ne!(one, two);
        assert_ne!(one.symbol_suffix(), two.symbol_suffix());
        assert_eq!(one.symbol_suffix(), const_u32_key(1).symbol_suffix());
    }

    /// A reify shim is a different codegen object from the underlying item even with the same
    /// definition and normalized args; the instance-kind discriminator is part of the key.
    #[test]
    fn test_concrete_key_distinguishes_item_from_reify_shim() {
        let definition = probe_definition(12);
        let item = ConcreteCalleeKey::test_only(definition, ConcreteInstanceKind::Item, Vec::new());
        let shim =
            ConcreteCalleeKey::test_only(definition, ConcreteInstanceKind::ReifyShim, Vec::new());
        assert_ne!(item, shim);
        assert_ne!(item.symbol_suffix(), shim.symbol_suffix());
    }

    /// Determinism at this seam: the same body (module + ledger), digested twice from
    /// independently constructed values, produces the same digest. (Cross-process
    /// determinism of the inner module digest is trust-ir's G19 conformance test;
    /// this pins the framing added here.)
    #[test]
    fn test_lineage_digest_same_body_twice_returns_same_digest() {
        let a = body_lineage_digest(
            probe_definition(3),
            &probe_module("probe"),
            &[probe_callee(false)],
        )
        .expect("single-function module must digest");
        let b = body_lineage_digest(
            probe_definition(3),
            &probe_module("probe"),
            &[probe_callee(false)],
        )
        .expect("single-function module must digest");
        assert_eq!(a, b, "identical (module, ledger) inputs must produce identical digests");
    }

    /// A perturbed BODY must change the digest (the module content is bound).
    #[test]
    fn test_lineage_digest_perturbed_body_returns_different_digest() {
        let base =
            body_lineage_digest(probe_definition(3), &probe_module("probe"), &[]).expect("digest");
        let perturbed =
            body_lineage_digest(probe_definition(3), &probe_module("probe_perturbed"), &[])
                .expect("digest");
        assert_ne!(base, perturbed, "a perturbed body must not share the original's digest");
    }

    /// A perturbed LEDGER must change the digest even when the module is untouched —
    /// the ledger is a real flip input, not metadata.
    #[test]
    fn test_lineage_digest_perturbed_ledger_returns_different_digest() {
        let module = probe_module("probe");
        let base = body_lineage_digest(probe_definition(3), &module, &[probe_callee(false)])
            .expect("digest");
        let havoced = body_lineage_digest(probe_definition(3), &module, &[probe_callee(true)])
            .expect("digest");
        assert_ne!(base, havoced, "the callee ledger must be bound by the digest");
        let empty = body_lineage_digest(probe_definition(3), &module, &[]).expect("digest");
        assert_ne!(base, empty, "dropping a ledger row must change the digest");
    }

    /// Fail-closed: a module that is not a single-body lowering refuses to digest.
    #[test]
    fn test_lineage_digest_bodyless_module_fails_closed() {
        let module = Module::new("no_bodies");
        let error = body_lineage_digest(probe_definition(3), &module, &[])
            .expect_err("a function-less module must not receive a lineage digest");
        assert!(error.contains("exactly one function"), "refusal must state the invariant");
    }

    /// **THE MEASURED COLLISION, PINNED.** Two DISTINCT definitions whose lowered bodies
    /// are byte-identical must not share a digest.
    ///
    /// This is a regression test for an observed defect, not a hypothetical. At
    /// `10f221fbe5`, over 200 `tests/ui` crates, 28 lineage digests were each claimed by
    /// more than one coverage row and 6 of those collisions had more than one SPLICED row —
    /// one digest addressing six different functions of the shipped artifact
    /// (`tests/ui/array-slice-vec/subslice-patterns-const-eval.rs`, `func_id` 5/9/13/31/35/39,
    /// all named `main::CONST_EVAL::{constant#0}::{const-init}`). The producer names a
    /// mini-module's function with `tcx.def_path_str`, which macro expansion makes
    /// non-injective, and every instruction's span points into the macro DEFINITION, so the
    /// two bodies were equal in every byte v1 hashed.
    ///
    /// The fixture reproduces exactly that shape: same module, same ledger, different
    /// stable definition identity. Under v1 this assertion FAILS.
    #[test]
    fn test_lineage_digest_distinguishes_two_definitions_with_identical_bodies() {
        let module = probe_module("main::CONST_EVAL::{constant#0}");
        let first = body_lineage_digest(probe_definition(30), &module, &[]).expect("digest");
        let second = body_lineage_digest(probe_definition(36), &module, &[]).expect("digest");
        assert_ne!(
            first, second,
            "two DEFINITIONS that lower to identical content must not share a lineage digest: \
             the flip event carries only the digest, so a shared one names several functions \
             of the artifact at once and the attestation cannot say which body shipped"
        );
        // ...and the digest must still be a pure function of its inputs: the SAME definition
        // digests the same twice, so the assertion above is about identity, not about noise.
        assert_eq!(
            first,
            body_lineage_digest(probe_definition(30), &module, &[]).expect("digest"),
            "the same definition must digest identically — otherwise the check above proves \
             nothing"
        );
    }

    /// The stable-crate half of the identity is bound too. A local path hash is only
    /// unique within a crate, so a framing that hashed it alone would let two crates collide.
    #[test]
    fn test_lineage_digest_binds_the_crate_as_well_as_the_index() {
        let module = probe_module("probe");
        let local =
            body_lineage_digest(DefinitionIdentity::test_only(1, 7), &module, &[]).expect("digest");
        let foreign =
            body_lineage_digest(DefinitionIdentity::test_only(2, 7), &module, &[]).expect("digest");
        assert_ne!(local, foreign, "the same index in a different crate is a different body");
    }
}
