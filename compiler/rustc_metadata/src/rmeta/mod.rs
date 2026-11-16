use std::marker::PhantomData;
use std::mem::size_of;
use std::num::NonZero;
use std::rc::Rc;

use decoder::LazyDecoder;
// Trust (D21): `ProcMacroClients` is in-process declarations or an isolated dylib.
pub(crate) use decoder::{
    CrateMetadata, CrateNumMap, MetadataBlob, ProcMacroClients, TargetModifiers,
};
use def_path_hash_map::DefPathHashMapRef;
use encoder::EncodeContext;
pub use encoder::{EncodedMetadata, encode_metadata, rendered_const};
pub(crate) use parameterized::ParameterizedOverTcx;
use rustc_abi::{FieldIdx, ReprOptions, VariantIdx};
use rustc_ast as ast;
use rustc_attr_ir::lang_items::LangItem;
use rustc_attr_ir::{
    Attribute, ConstStability, DefaultBodyStability, Deprecation, Stability, StrippedCfgItem,
};
use rustc_crate_store::{CrateDepKind, ForeignModule, LinkagePreference, NativeLib};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::svh::Svh;
use rustc_hir as hir;
use rustc_hir::PreciseCapturingArgKind;
use rustc_hir::def::{CtorKind, DefKind, MacroKinds};
use rustc_hir::def_id::{
    CRATE_DEF_INDEX, CrateNum, DefId, DefIdMap, DefIndex, DefPathHash, LOCAL_CRATE, LocalDefId,
    StableCrateId,
};
use rustc_hir::definitions::DefKey;
use rustc_index::bit_set::DenseBitSet;
use rustc_index::{Idx, IndexVec};
use rustc_macros::{
    BlobDecodable, Decodable, Encodable, LazyDecodable, MetadataEncodable, TyDecodable, TyEncodable,
};
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrs;
use rustc_middle::middle::debugger_visualizer::DebuggerVisualizerFile;
use rustc_middle::middle::deduced_param_attrs::DeducedParamAttrs;
use rustc_middle::middle::exported_symbols::{ExportedSymbol, SymbolExportInfo};
use rustc_middle::middle::lib_features::FeatureStability;
use rustc_middle::middle::resolve::{AmbigModChild, DocLinkResMap, ModChild};
use rustc_middle::middle::resolve_bound_vars::ObjectLifetimeDefault;
// Trust: cross-crate PROOF-position citation, increment 2 (TRANSPORT).
use rustc_middle::middle::trust_clean_proof::TrustCleanProofManifest;
use rustc_middle::middle::trust_ir_entry::{TrustIrCrateHeader, TrustIrEntryBlob};
use rustc_middle::mir;
use rustc_middle::mir::ConstValue;
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_middle::util::Providers;
use rustc_serialize::opaque::FileEncoder;
use rustc_session::config::mitigation_coverage::DeniedPartialMitigation;
use rustc_session::config::{SymbolManglingVersion, TargetModifier};
use rustc_span::edition::Edition;
use rustc_span::hygiene::{DecodedSyntaxContext, ExpnIndex, MacroKind, SyntaxContextKey};
use rustc_span::{self, ExpnData, ExpnHash, ExpnId, Ident, Span, Symbol};
use rustc_target::spec::{PanicStrategy, TargetTuple};
use table::TableBuilder;

use crate::eii::EiiMapEncodedKeyValue;
use crate::rmeta::parameterized::EncodeFrom;
use crate::rmeta::remapped_def_id::RemappedRawDefId;

mod decoder;
mod def_path_hash_map;
mod encoder;
mod parameterized;
mod table;
// Trust: the golden TyEncodable MIR wire layout, pinned to METADATA_VERSION.
#[cfg(test)]
mod tests;

pub(crate) fn rustc_version(cfg_version: &'static str) -> String {
    format!("rustc {cfg_version}")
}

/// Metadata encoding version.
/// N.B., increment this if you change the format of metadata such that
/// the rustc version can't be found to compare with `rustc_version()`.
// Trust: (I7) — bumped 11 -> 12: +`trust_clean_verdict_digest` table,
// +`trust_clean_island_sources`/`trust_clean_origin_exports` CrateRoot fields.
//
// Trust: bumped 12 -> 13 — f24fdb2fdb added `Statement::trust_modular_arith` to
// the MIR statement encoding WITHOUT bumping this constant. MIR bodies ride
// rmeta (`optimized_mir`/`mir_for_ctfe` tables), so that changed the wire format
// while the header still said 12: a driver at f24fdb2fdb+ decoding a
// pre-f24fdb2fdb v12 sysroot ICEs mid-stream ("invalid enum variant tag while
// decoding `StmtDebugInfo`, expected 0..2, actual 15" — the missing trailing
// bool misaligns the next statement's tag) instead of refusing with E0514.
// This bump restores the refusal. NOTE FOR THE NEXT ENCODING CHANGE: any field
// or variant added to a `TyEncodable` MIR type changes this format, even when
// no rmeta TABLE changes — bump here in the SAME commit, and see
// `seal_driver.sh sysrootcheck`'s decode probe, which catches the skew class
// this comment exists to prevent.
//
// Trust: the source-side guard for that rule is `rmeta/tests.rs`
// (`./x.py test compiler/rustc_metadata`): it pins the encoded layout of a MIR
// corpus and the variant count of every TyEncodable MIR enum to the version
// below, and fails with "bump METADATA_VERSION" when they move without it.
//
// Trust: bumped 13 -> 14 — cross-crate PROOF-position citation increment 2 adds
// the `trust_clean_proof_manifest` CrateRoot field. An `Option<LazyValue<_>>`
// changes the format for EVERY crate, including the ones that write `None`, so
// a stage that was not rebuilt must refuse with E0514 rather than decode a
// shifted root. That refusal is the designed behaviour of this bump: rebuild
// the sysroot in the same step as this change.
//
// Trust: bumped 14 -> 15 — D4 increment A adds the defaulted
// `trust_no_user_unsafe_source` table, which changes the `LazyTables` layout for
// EVERY crate. Same discipline as above: rebuild the sysroot in the same step.
//
// Trust: bumped 15 -> 16 — CB3 adds the defaulted `trust_clean_island_item` table
// (the per-def `clean { … }` island marker the certified-monitor dependency check
// reads), which changes the `LazyTables` layout for EVERY crate. Same discipline:
// rebuild the sysroot in the same step, and `mir_layout.golden` is re-recorded
// under 16 (its MIR layout lines are unchanged — only a table moved).
//
// Trust: bumped 16 -> 17 — adds the `trust_references_alloc_error_hook` CrateRoot
// field (a crate may install an allocation-error hook), which shifts the root for
// EVERY crate. Same discipline: rebuild the sysroot in the same step, and
// `mir_layout.golden` is re-recorded under 17 (its MIR layout lines are unchanged —
// only the root grew a field).
//
// Trust: bumped 17 -> 18 — step 2 increment 6 (6.2) adds the optional `trust_ir_entry`
// table (opaque per-definition trust-ir entry bytes) and the `trust_ir_header` CrateRoot
// field (`Option<LazyValue<TrustIrCrateHeader>>`), which change the `LazyTables` layout and
// the root for EVERY crate, including one compiled without the producer (an empty table, a
// `None` header). Same discipline: rebuild the sysroot in the same step, and
// `mir_layout.golden` is re-recorded under 18 (its MIR layout lines are unchanged).
//
// Trust: bumped 18 -> 19 — TINV step 2 appends `TrustObligationKind::TypeInvariant`, a
// TyEncodable MIR enum (`mir_layout.golden` records its variant count, 21 -> 22). Appended
// last, so no existing discriminant moves, but a crate carrying the new tag must be refused
// (E0514) by an older driver rather than ICE mid-decode. Same discipline: rebuild the sysroot
// in the same step, and `mir_layout.golden` is re-recorded under 19.
//
// Trust: bumped 19 -> 20 — T6 adds the `trust_proof_session_mir` CrateRoot field
// (`trust_crate_mir_is_proof_session_pipeline`: was this crate's MIR built by the
// proof-session `-O0` MIR pipeline?), which shifts the root for EVERY crate. Same
// discipline: rebuild the sysroot in the same step, and `mir_layout.golden` is
// re-recorded under 20 (its MIR layout lines are unchanged — only the root grew a
// field).
//
// Trust: bumped 20 -> 21 — the 1.101 toolchain port: upstream changed a
// TyEncodable MIR wire layout (`Statement`'s encoded shape moved), so
// `mir_layout.golden` is re-recorded under 21 in the same commit.
//
// Trust: bumped 21 -> 22 — the 3e92e1a2 toolchain port: upstream changed the
// metadata format in the same window (their own 11 -> 12 bump), so
// `mir_layout.golden` is re-recorded under 22 in the same commit.
// Trust: 22 -> 23 adds the per-ADT ODT transport table (TG10).
const METADATA_VERSION: u8 = 23;

/// Metadata header which includes `METADATA_VERSION`.
///
/// This header is followed by the `CrateRoot` and `CrateRootUnhashed` positions
/// which represent the hashed and unhashed metadata contents respectively, the
/// crate hash (SVH), and the rustc version string. See the offset constants
/// below for the exact layout.
pub const METADATA_HEADER: &[u8] = &[b'r', b'u', b's', b't', 0, 0, 0, METADATA_VERSION];

/// Fixed-size fields encoded immediately after `METADATA_HEADER`, in order:
/// `CrateRoot` position (u64), `CrateRootUnhashed` position (u64), crate hash
/// (`Fingerprint`/SVH), then the variable-length rustc version string.
const ROOT_POS_OFFSET: usize = METADATA_HEADER.len();
const ROOT_POS_LEN: usize = size_of::<u64>();
const UNHASHED_POS_OFFSET: usize = ROOT_POS_OFFSET + ROOT_POS_LEN;
const UNHASHED_POS_LEN: usize = size_of::<u64>();
const CRATE_HASH_OFFSET: usize = UNHASHED_POS_OFFSET + UNHASHED_POS_LEN;
const CRATE_HASH_LEN: usize = size_of::<Fingerprint>();
const VERSION_OFFSET: usize = CRATE_HASH_OFFSET + CRATE_HASH_LEN;

/// A value of type T referred to by its absolute position
/// in the metadata, and which can be decoded lazily.
///
/// Metadata is effective a tree, encoded in post-order,
/// and with the root's position written next to the header.
/// That means every single `LazyValue` points to some previous
/// location in the metadata and is part of a larger node.
///
/// The first `LazyValue` in a node is encoded as the backwards
/// distance from the position where the containing node
/// starts and where the `LazyValue` points to, while the rest
/// use the forward distance from the previous `LazyValue`.
/// Distances start at 1, as 0-byte nodes are invalid.
/// Also invalid are nodes being referred in a different
/// order than they were encoded in.
#[must_use]
struct LazyValue<T> {
    position: NonZero<usize>,
    _marker: PhantomData<fn() -> T>,
}

impl<T> LazyValue<T> {
    fn from_position(position: NonZero<usize>) -> LazyValue<T> {
        LazyValue { position, _marker: PhantomData }
    }
}

/// A list of lazily-decoded values.
///
/// Unlike `LazyValue<Vec<T>>`, the length is encoded next to the
/// position, not at the position, which means that the length
/// doesn't need to be known before encoding all the elements.
///
/// If the length is 0, no position is encoded, but otherwise,
/// the encoding is that of `LazyArray`, with the distinction that
/// the minimal distance the length of the sequence, i.e.
/// it's assumed there's no 0-byte element in the sequence.
struct LazyArray<T> {
    position: NonZero<usize>,
    num_elems: usize,
    _marker: PhantomData<fn() -> T>,
}

impl<T> Default for LazyArray<T> {
    fn default() -> LazyArray<T> {
        LazyArray::from_position_and_num_elems(NonZero::new(1).unwrap(), 0)
    }
}

impl<T> LazyArray<T> {
    fn from_position_and_num_elems(position: NonZero<usize>, num_elems: usize) -> LazyArray<T> {
        LazyArray { position, num_elems, _marker: PhantomData }
    }
}

/// A list of lazily-decoded values, with the added capability of random access.
///
/// Random-access table (i.e. offering constant-time `get`/`set`), similar to
/// `LazyArray<T>`, but without requiring encoding or decoding all the values
/// eagerly and in-order.
///
/// `IdxEncode` - is a type of index that is used to write to the table,
/// `IdxDecode` - is a type of index that is used to read from the table.
struct LazyTable<IdxEncode, IdxDecode, T> {
    position: NonZero<usize>,
    /// The encoded size of the elements of a table is selected at runtime to drop
    /// trailing zeroes. The low bit selects sparse encoding; the remaining bits
    /// store the number of bytes used for each table element.
    width_and_sparse: usize,
    /// How many elements are in the table.
    len: usize,
    _marker: PhantomData<fn(IdxEncode, IdxDecode) -> T>,
}

impl<Ie, Id, T> LazyTable<Ie, Id, T> {
    fn from_position_and_encoded_size(
        position: NonZero<usize>,
        width_and_sparse: usize,
        len: usize,
    ) -> LazyTable<Ie, Id, T> {
        LazyTable { position, width_and_sparse, len, _marker: PhantomData }
    }
}

impl<T> Copy for LazyValue<T> {}
impl<T> Clone for LazyValue<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for LazyArray<T> {}
impl<T> Clone for LazyArray<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Ie, Id, T> Copy for LazyTable<Ie, Id, T> {}
impl<Ie, Id, T> Clone for LazyTable<Ie, Id, T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Encoding / decoding state for `Lazy`s (`LazyValue`, `LazyArray`, and `LazyTable`).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum LazyState {
    /// Outside of a metadata node.
    NoNode,

    /// Inside a metadata node, and before any `Lazy`s.
    /// The position is that of the node itself.
    NodeStart(NonZero<usize>),

    /// Inside a metadata node, with a previous `Lazy`s.
    /// The position is where that previous `Lazy` would start.
    Previous(NonZero<usize>),
}

type SyntaxContextTable =
    LazyTable<RemappedSyntaxContext, DecodedSyntaxContext, Option<LazyValue<SyntaxContextKey>>>;
type ExpnDataTable = LazyTable<RemappedLocalExpnIndex, ExpnIndex, Option<LazyValue<ExpnData>>>;
type ExpnHashTable = LazyTable<RemappedLocalExpnIndex, ExpnIndex, Option<LazyValue<ExpnHash>>>;

#[derive(MetadataEncodable, LazyDecodable)]
pub(crate) struct ProcMacroData {
    proc_macro_decls_static: LazyValue<LocalDefId>,
    stability: Option<Stability>,
    macros: LazyArray<(LocalDefId, LazyValue<ProcMacroKind>)>,
    proc_macro_quoted_spans: LazyTable<usize, usize, Option<LazyValue<Span>>>,
}

#[derive(MetadataEncodable, LazyDecodable)]
pub enum ProcMacroKind {
    CustomDerive { trait_name: String, attributes: Vec<String> },
    Attr { name: String },
    Bang { name: String },
}

/// Serialized crate metadata.
///
/// This contains just enough information to determine if we should load the `CrateRoot` or not.
/// Prefer [`CrateRoot`] whenever possible to avoid ICEs when using `omit-git-hash` locally.
/// See #76720 for more details.
///
/// If you do modify this struct, also bump the [`METADATA_VERSION`] constant.
#[derive(MetadataEncodable, BlobDecodable)]
pub(crate) struct CrateHeader {
    pub(crate) triple: TargetTuple,
    pub(crate) name: Symbol,
    /// Whether this is the header for a proc-macro crate.
    ///
    /// This is separate from [`ProcMacroData`] to avoid having to update [`METADATA_VERSION`] every
    /// time ProcMacroData changes.
    pub(crate) is_proc_macro_crate: bool,
    /// Whether this crate metadata section is just a stub.
    /// Stubs do not contain the full metadata (it will be typically stored
    /// in a separate rmeta file).
    ///
    /// This is used inside rlibs and dylibs when using `-Cembed-metadata=no`.
    pub(crate) is_stub: bool,
}

/// Serialized `.rmeta` data for a crate.
///
/// When compiling a proc-macro crate, we encode many of
/// the `LazyArray<T>` fields as `Lazy::empty()`. This serves two purposes:
///
/// 1. We avoid performing unnecessary work. Proc-macro crates can only
/// export proc-macros functions, which are compiled into a shared library.
/// As a result, a large amount of the information we normally store
/// (e.g. optimized MIR) is unneeded by downstream crates.
/// 2. We avoid serializing invalid `CrateNum`s. When we deserialize
/// a proc-macro crate, we don't load any of its dependencies (since we
/// just need to invoke a native function from the shared library).
/// This means that any foreign `CrateNum`s that we serialize cannot be
/// deserialized, since we will not know how to map them into the current
/// compilation session. If we were to serialize a proc-macro crate like
/// a normal crate, much of what we serialized would be unusable in addition
/// to being unused.
#[derive(MetadataEncodable, LazyDecodable)]
pub(crate) struct CrateRoot {
    /// A header used to detect if this is the right crate to load.
    header: CrateHeader,

    stable_crate_id: StableCrateId,
    required_panic_strategy: Option<PanicStrategy>,
    panic_in_drop_strategy: PanicStrategy,
    edition: Edition,
    has_global_allocator: bool,
    has_alloc_error_handler: bool,
    has_panic_handler: bool,
    has_default_lib_allocator: bool,
    externally_implementable_items: LazyArray<EiiMapEncodedKeyValue>,

    crate_deps: LazyArray<CrateDep>,
    dylib_dependency_formats: LazyArray<Option<LinkagePreference>>,
    lib_features: LazyArray<(Symbol, FeatureStability)>,
    stability_implications: LazyArray<(Symbol, Symbol)>,
    lang_items: LazyArray<(LocalDefId, LangItem)>,
    lang_items_missing: LazyArray<LangItem>,
    stripped_cfg_items: LazyArray<StrippedCfgItem<LocalDefId>>,
    diagnostic_items: LazyArray<(Symbol, LocalDefId)>,
    canonical_symbols: LazyArray<(Symbol, LocalDefId)>,
    fake_doc_items: LazyArray<LocalDefId>,
    native_libraries: LazyArray<NativeLib>,
    foreign_modules: LazyArray<ForeignModule>,
    traits: LazyArray<LocalDefId>,
    impls: LazyArray<TraitImpls>,
    incoherent_impls: LazyArray<IncoherentImpls>,
    // Trust: step 2 increment 6 (6.2) — the trust-ir entries' crate header. `None` when the
    // direct producer did not run. Declared HERE, between the two fields whose lazies are
    // written before (`incoherent_impls`) and after (`interpret_alloc_index`) it, because
    // `emit_lazy_distance` requires the root's lazy positions to follow field order and the
    // header is written in the `trust-ir` section, right after `mir`.
    trust_ir_header: Option<LazyValue<TrustIrCrateHeader>>,
    interpret_alloc_index: LazyArray<u64>,
    proc_macro_data: Option<ProcMacroData>,

    tables: LazyTables,
    debugger_visualizers: LazyArray<DebuggerVisualizerFile>,

    exportable_items: LazyArray<LocalDefId>,
    stable_order_of_exportable_impls: LazyArray<(LocalDefId, usize)>,
    // Trust: (I7) — Clean-origin cross-crate transport, root halves. The island
    // sources are declaration TRANSPORT (the importer re-elaborates them under
    // its OWN kernel; text is never authority). The export list is the digest
    // table's second, independent encoding: an importer refuses a listed def
    // without a decodable digest row, so row-absence cannot demote a
    // Clean-origin def to ordinary Rust (I7 risk R1). Both empty for every
    // crate without Clean-origin defs.
    trust_clean_island_sources: LazyArray<String>,
    // Trust: `LocalDefId`, not bare `DefIndex`: 1.101's metadata encoder
    // panics on a bare DefIndex (it cannot know the index is local); the
    // wire bytes are the same u32 the 1.99 encoder wrote.
    trust_clean_origin_exports: LazyArray<LocalDefId>,
    // Trust: cross-crate PROOF-position citation, increment 2 (TRANSPORT). The
    // manifest for the island sources above: which Clean kernel produced them,
    // and the digest over the exact bytes published. `Some` for every crate
    // that HAS islands — deliberately weaker than the export list's condition,
    // because a pure spec crate mints nothing callable and must still be
    // citable — and `None` for every crate that has none. Authority-free in
    // the same way the sources are: the consumer compares the version and
    // recomputes the digest, then re-elaborates and kernel-checks every byte.
    trust_clean_proof_manifest: Option<LazyValue<TrustCleanProofManifest>>,
    exported_non_generic_symbols: LazyArray<(ExportedSymbol<'static>, SymbolExportInfo)>,
    exported_generic_symbols: LazyArray<(ExportedSymbol<'static>, SymbolExportInfo)>,

    syntax_contexts: SyntaxContextTable,
    expn_data: ExpnDataTable,
    expn_hashes: ExpnHashTable,

    def_path_hash_map: LazyValue<DefPathHashMapRef<'static>>,

    source_map: LazyTable<u32, u32, Option<LazyValue<rustc_span::SourceFile>>>,
    target_modifiers: LazyArray<TargetModifier>,
    denied_partial_mitigations: LazyArray<DeniedPartialMitigation>,

    compiler_builtins: bool,
    needs_allocator: bool,
    needs_panic_runtime: bool,
    no_builtins: bool,
    panic_runtime: bool,
    profiler_runtime: bool,
    symbol_mangling_version: SymbolManglingVersion,

    specialization_enabled_in: bool,
    // Trust (2026-10-03): `true` iff some body of this crate names a function
    // called `set_alloc_error_hook` (`trust_crate_references_alloc_error_hook`): a
    // downstream compilation ORs it over its graph, because an installed
    // allocation-error hook may panic and so makes allocation failure a panic path.
    trust_references_alloc_error_hook: bool,
    // Trust (T6, 2026-10-09): `true` iff this crate's MIR was built by the
    // proof-session `-O0` MIR pipeline (`trust_crate_mir_is_proof_session_pipeline`):
    // a verified dependent re-derives this crate's encoded MIR only then.
    trust_proof_session_mir: bool,
}

/// A separate struct for extra metadata that must be encoded *after*
/// the main crate hash is finalized.
#[derive(MetadataEncodable, LazyDecodable)]
pub(crate) struct CrateRootUnhashed {
    extra_filename: String,

    /// The `-C extra-filename` of each dependency, indexed by the `CrateNum` they had in *this*
    /// crate's encoding. The `LOCAL_CRATE` slot is unused filler so that dependency `CrateNum`s
    /// can index this directly; this crate's own value is `extra_filename` above.
    dep_extra_filenames: IndexVec<CrateNum, String>,
}

rustc_index::newtype_index! {
    #[max = 0x1FFF_FFFF] // `u32::MAX` >> 3, as `SyntaxContext` should be fit in 29 bits (see `span_encoding`).
    #[default]
    pub(super) struct RemappedSyntaxContext {}
}

rustc_index::newtype_index! {
    #[default]
    pub(super) struct RemappedLocalExpnIndex {}
}

#[derive(Default)]
pub(crate) struct LocalDefsRemapping {
    /// See `Definitions::first_non_det_index`, it is just cached version of it.
    pub first_non_det_index: u32,

    /// The map where for each non-det local def id the remapped def index
    /// is stored. It can be accessed by
    /// `remapping[id.local_def_index - first_non_det_index]`, the caller should
    /// ensure that `id.local_def_index >= first_non_det_index`.
    pub remapping: Vec<DefIndex>,

    /// The ordered list of NON-remapped non-det local def ids. This
    /// list is used when we need to iterate over all local defs in a
    /// stable order.
    pub sorted_non_det_ids: Rc<[LocalDefId]>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct RemappedLocalDefId {
    pub index: DefIndex,
}

impl Idx for RemappedLocalDefId {
    #[inline]
    fn new(idx: usize) -> Self {
        RemappedLocalDefId { index: DefIndex::from_usize(idx) }
    }

    #[inline]
    fn index(self) -> usize {
        self.index.as_usize()
    }
}

impl LocalDefsRemapping {
    /// This method should be used whenever the `LocalDefId` is encoded, as it remaps
    /// it's `local_def_index` for deterministic metadata encoding, this
    /// remapping needs to be applied to all `LocalDefId`s during metadata encoding.
    /// Note that when implementing custom structs that represent `LocalDefId` the
    /// remapping should also be applied (see `RawDefId`).
    #[inline]
    fn map_local_def_id(&self, local_def_id: LocalDefId) -> RemappedLocalDefId {
        RemappedLocalDefId { index: self.map_index(local_def_id.local_def_index) }
    }

    /// Remaps `DefId` only if it local for deterministic metadata encoding. External
    /// def ids are not needed to be remapped as they are already deterministic.
    /// Whenever a `DefId` is encoded this method should be called.
    /// Note that when implementing custom structs that represent `DefId` the
    /// remapping should also be applied (see `RawDefId`).
    #[inline]
    fn map_def_id(&self, def_id: DefId) -> DefId {
        if def_id.is_local() {
            DefId { krate: LOCAL_CRATE, index: self.map_index(def_id.index) }
        } else {
            def_id
        }
    }

    /// Shared part of `map_local_def_id` and `map_def_id` which remaps a def index.
    /// Given only def index we do not know whether it belongs to local or external
    /// def id, so this method should not be called on `DefIndex`es whose origin is unknown.
    /// Prefer to use above-mentioned methods instead or use it when it is clear that
    /// `DefIndex` is local.
    #[inline]
    fn map_index(&self, def_index: DefIndex) -> DefIndex {
        let index = def_index.as_u32();

        if index < self.first_non_det_index {
            def_index
        } else {
            let shifted_idx = index - self.first_non_det_index;
            self.remapping[shifted_idx as usize]
        }
    }

    fn iter_sorted_local_ids(&self) -> impl Iterator<Item = LocalDefId> + use<> {
        let first_non_det_index = self.first_non_det_index;
        let non_det_part = Rc::clone(&self.sorted_non_det_ids);

        gen move {
            for i in 0..first_non_det_index {
                yield LocalDefId { local_def_index: DefIndex::from_u32(i) }
            }

            let len = non_det_part.len();
            for i in 0..len {
                yield non_det_part[i]
            }
        }
    }

    fn new(tcx: TyCtxt<'_>) -> LocalDefsRemapping {
        let defs = tcx.definitions();

        let mut non_det_ids = vec![];
        let start = defs.first_non_det_index().as_usize();
        let num_defs = defs.num_definitions();

        for idx in start..num_defs {
            let def_id_level = |mut id| {
                let mut level = 0;
                while let Some(parent) = tcx.opt_local_parent(id) {
                    level += 1;
                    id = parent;
                }

                level
            };

            let def_id = LocalDefId { local_def_index: idx.into() };
            non_det_ids.push((
                def_id,
                def_id_level(def_id),
                defs.def_path_hash(def_id).local_hash(),
            ));
        }

        // Sort by level first in order to satisfy the invariant that child def id
        // always has a higher def index than its parent (see `def_id_partial_cmp`),
        // in context of one level sort by stable hash. Ids from higher level will
        // get higher remapped def index.
        non_det_ids.sort_by_key(|(_, level, hash)| (*level, *hash));

        let mut remapping = vec![CRATE_DEF_INDEX; non_det_ids.len()];
        for (idx, (id, ..)) in non_det_ids.into_iter().enumerate() {
            remapping[id.local_def_index.as_usize() - start] = DefIndex::from_usize(start + idx);
        }

        let mut sorted_non_det_ids = (start..num_defs)
            .into_iter()
            .map(|idx| LocalDefId { local_def_index: DefIndex::from(idx) })
            .collect::<Vec<_>>();

        sorted_non_det_ids.sort_by_key(|id| remapping[id.local_def_index.as_usize() - start]);

        let sorted_non_det_ids = Rc::from(sorted_non_det_ids);
        LocalDefsRemapping { first_non_det_index: start as u32, remapping, sorted_non_det_ids }
    }
}

pub(crate) mod remapped_def_id {
    use super::*;

    /// On-disk representation of `DefId`.
    /// This creates a type-safe way to enforce that we remap the CrateNum between the on-disk
    /// representation and the compilation session.
    #[derive(Copy, Clone, Hash, PartialEq, Eq, Encodable, BlobDecodable)]
    pub(crate) struct RemappedRawDefId {
        krate: u32,
        index: u32,
    }

    impl RemappedRawDefId {
        pub(crate) fn new_unchecked(krate: u32, index: u32) -> RemappedRawDefId {
            RemappedRawDefId { krate, index }
        }

        pub(crate) fn create(def_id: DefId, remapping: &LocalDefsRemapping) -> RemappedRawDefId {
            let def_id = remapping.map_def_id(def_id);
            RemappedRawDefId { krate: def_id.krate.as_u32(), index: def_id.index.as_u32() }
        }

        /// This exists so that `provide_one!` is happy
        pub(crate) fn decode(self, meta: (&CrateMetadata, TyCtxt<'_>)) -> DefId {
            let krate = CrateNum::from_u32(self.krate);
            let krate = meta.0.map_encoded_cnum_to_current(krate);
            DefId { krate, index: DefIndex::from_u32(self.index) }
        }

        pub(crate) fn decompose(&self) -> (u32, u32) {
            (self.krate, self.index)
        }
    }
}

/// A dependency record, as stored in the hashed [`CrateRoot`].
///
/// Note the absence of the dependency's `-C extra-filename`: it lives in
/// [`CrateRootUnhashed::dep_extra_filenames`] instead, deliberately outside the hash.
#[derive(Encodable, BlobDecodable)]
pub(crate) struct CrateDep {
    pub name: Symbol,
    pub hash: Svh,
    pub host_hash: Option<Svh>,
    pub kind: CrateDepKind,
    pub is_private: bool,
}

#[derive(MetadataEncodable, LazyDecodable)]
pub(crate) struct TraitImpls {
    trait_id: RemappedRawDefId,
    impls: LazyArray<(LocalDefId, Option<SimplifiedType>)>,
}

#[derive(MetadataEncodable, LazyDecodable)]
pub(crate) struct IncoherentImpls {
    self_ty: LazyValue<SimplifiedType>,
    impls: LazyArray<LocalDefId>,
}

/// Define `LazyTables` and `TableBuilders` at the same time.
macro_rules! define_tables {
    (
        - defaulted: $($name1:ident: Table<$T1:ty>,)+
        - optional: $($name2:ident: Table<$T2:ty>,)+
    ) => {
        #[derive(MetadataEncodable, LazyDecodable)]
        pub(crate) struct LazyTables {
            $($name1: LazyTable<RemappedLocalDefId, DefIndex, $T1>,)+
            $($name2: LazyTable<RemappedLocalDefId, DefIndex, Option<$T2>>,)+
        }

        #[derive(Default)]
        struct TableBuilders {
            $($name1: TableBuilder<RemappedLocalDefId, DefIndex, $T1>,)+
            $($name2: TableBuilder<RemappedLocalDefId, DefIndex, Option<$T2>>,)+
        }

        impl TableBuilders {
            fn encode(&self, buf: &mut FileEncoder<'_>) -> LazyTables {
                LazyTables {
                    $($name1: self.$name1.encode(buf),)+
                    $($name2: self.$name2.encode(buf),)+
                }
            }
        }

        impl<'a, 'tcx, 'b> TableWriter<'a, 'tcx, 'b> {
            $(
                /// Records a value into the corresponding `TableBuilders` field, encoding it in
                /// the process when necessary
                fn $name1<T>(&mut self, i: LocalDefId, v: T)
                where
                    $T1: EncodeFrom<'tcx, T>
                {
                    let encoded = <$T1 as EncodeFrom<'tcx, T>>::encode_from(self.encoder, v);
                    let idx = self.encoder.local_defs_remapping.map_local_def_id(i);
                    self.encoder.tables.$name1.set(idx, encoded);
                }
            )+
            $(
                /// Records a value into the corresponding `TableBuilders` field, encoding it in
                /// the process when necessary
                fn $name2<T>(&mut self, i: LocalDefId, v: T)
                where
                    $T2: EncodeFrom<'tcx, T>
                {
                    let encoded = <$T2 as EncodeFrom<'tcx, T>>::encode_from(self.encoder, v);
                    let idx = self.encoder.local_defs_remapping.map_local_def_id(i);
                    self.encoder.tables.$name2.set(idx, Some(encoded));
                }
            )+
        }
    }
}

/// Helper struct for writing values into [`TableBuilders`].
#[must_use]
struct TableWriter<'a, 'tcx, 'b> {
    encoder: &'b mut EncodeContext<'a, 'tcx>,
}

define_tables! {
// If the compiler complains about `EncodeFrom` or `ParameterizedOverTcx` bounds when calling a
// function generated in this macro, add them to parameterized.rs
- defaulted:
    intrinsic: Table<Option<LazyValue<ty::IntrinsicDef>>>,
    is_macro_rules: Table<bool>,
    type_alias_is_checked: Table<bool>,
    attr_flags: Table<AttrFlags>,
    // The u64 is the crate-local part of the DefPathHash. All hashes in this crate have the same
    // StableCrateId, so we omit encoding those into the table.
    //
    // Note also that this table is fully populated (no gaps) as every DefIndex should have a
    // corresponding DefPathHash.
    def_path_hashes: Table<u64>,
    explicit_item_bounds: Table<LazyArray<(ty::Clause<'static>, Span)>>,
    explicit_item_self_bounds: Table<LazyArray<(ty::Clause<'static>, Span)>>,
    inferred_outlives_of: Table<LazyArray<(ty::Clause<'static>, Span)>>,
    explicit_super_clauses_of: Table<LazyArray<(ty::Clause<'static>, Span)>>,
    explicit_implied_clauses_of: Table<LazyArray<(ty::Clause<'static>, Span)>>,
    explicit_implied_const_bounds: Table<LazyArray<(ty::PolyTraitRef<'static>, Span)>>,
    inherent_impls: Table<LazyArray<LocalDefId>>,
    // Reexported names are not associated with individual `DefId`s,
    // e.g. a glob import can introduce a lot of names, all with the same `DefId`.
    // That's why the encoded list needs to contain `ModChild` structures describing all the names
    // individually instead of `DefId`s.
    module_children_reexports: Table<LazyArray<ModChild>>,
    ambig_module_children: Table<LazyArray<AmbigModChild>>,
    cross_crate_inlinable: Table<bool>,
    asyncness: Table<ty::Asyncness>,
    constness: Table<hir::Constness>,
    safety: Table<hir::Safety>,
    defaultness: Table<hir::Defaultness>,
    // Trust: D4 increment A (2026-09-24) — `true` ONLY for a def whose encoding
    // compiler established that its source contains NO user `unsafe`
    // (`trust_def_has_user_unsafe_source` == false). Stored NEGATED on purpose: a
    // defaulted table answers `false` for every missing row, and a missing row must
    // read as "not known safe", so the extern provider's `!row` fails closed.
    trust_no_user_unsafe_source: Table<bool>,
    // Trust: CB3 (2026-09-28) — `true` ONLY for a `DefKind::GlobalAsm` def whose
    // encoding compiler saw a `clean { … }` / `clean mod` island in its HIR
    // (`trust_def_is_clean_island`). An island shares `DefKind::GlobalAsm` but emits no
    // machine code; this row is how a dependent tells it from a real `global_asm!`
    // without HIR. Defaulted `false` is the fail-closed reading: a missing row keeps a
    // `DefKind::GlobalAsm` def classified as real assembly.
    trust_clean_island_item: Table<bool>,
    impl_is_fully_generic_for_reflection: Table<bool>,

- optional:
    opt_rpitit_info: Table<LazyValue<ty::ImplTraitInTraitData>>,
    attributes: Table<LazyArray<Attribute>>,
    // For non-reexported names in a module every name is associated with a separate `DefId`,
    // so we can take their names, visibilities etc from other encoded tables.
    module_children_non_reexports: Table<LazyArray<LocalDefId>>,
    associated_item_or_field_def_ids: Table<LazyArray<LocalDefId>>,
    def_kind: Table<DefKind>,
    visibility: Table<LazyValue<ty::Visibility<LocalDefId>>>,
    def_span: Table<LazyValue<Span>>,
    def_ident_span: Table<LazyValue<Span>>,
    lookup_stability: Table<LazyValue<Stability>>,
    lookup_const_stability: Table<LazyValue<ConstStability>>,
    lookup_default_body_stability: Table<LazyValue<DefaultBodyStability>>,
    lookup_deprecation_entry: Table<LazyValue<Deprecation>>,
    explicit_clauses_of: Table<LazyValue<ty::GenericClauses<'static>>>,
    generics_of: Table<LazyValue<ty::Generics>>,
    type_of: Table<LazyValue<ty::EarlyBinder<'static, Ty<'static>>>>,
    variances_of: Table<LazyArray<ty::Variance>>,
    fn_sig: Table<LazyValue<ty::EarlyBinder<'static, ty::PolyFnSig<'static>>>>,
    codegen_fn_attrs: Table<LazyValue<CodegenFnAttrs>>,
    impl_trait_header: Table<LazyValue<ty::ImplTraitHeader<'static>>>,
    const_param_default: Table<LazyValue<ty::EarlyBinder<'static, rustc_middle::ty::Const<'static>>>>,
    object_lifetime_default: Table<LazyValue<ObjectLifetimeDefault>>,
    optimized_mir: Table<LazyValue<mir::Body<'static>>>,
    mir_for_ctfe: Table<LazyValue<mir::Body<'static>>>,
    trivial_const: Table<LazyValue<(ConstValue, Ty<'static>)>>,
    closure_saved_names_of_captured_variables: Table<LazyValue<IndexVec<FieldIdx, Symbol>>>,
    mir_coroutine_witnesses: Table<LazyValue<mir::CoroutineLayout<'static>>>,
    promoted_mir: Table<LazyValue<IndexVec<mir::Promoted, mir::Body<'static>>>>,
    trust_contracts: Table<LazyValue<mir::trust_contract::TrustContractBundle<'static>>>,
    // Trust: (I7) — opaque `VerdictDigest::encode` bytes, one row per Clean-origin
    // def. Opaque ON PURPOSE: rmeta never names the Clean closure's types, and
    // versioning lives in ONE place — the digest's own magic+format — so a format
    // skew surfaces as the digest decoder's fail-closed refusal at the importer,
    // never as an rmeta shape error.
    trust_clean_verdict_digest: Table<LazyValue<Vec<u8>>>,
    // Trust: D-2 C1/C2 data, not a serialized kernel authority token.
    trust_odt_entry: Table<LazyValue<Vec<u8>>>,
    // Trust: step 2 increment 6 (6.2) — one OPAQUE trust-ir entry per definition the direct
    // producer encoded (`trust_thir_lower::rmeta_entry`), the precedent above: rmeta never
    // names a trust-ir type, and the entry's own magic, schema and trust-ir wire version are
    // the only versioning, so a skew is the entry decoder's refusal, never an rmeta shape error.
    trust_ir_entry: Table<LazyValue<TrustIrEntryBlob>>,
    thir_abstract_const: Table<LazyValue<ty::EarlyBinder<'static, ty::Const<'static>>>>,
    impl_parent: Table<RemappedRawDefId>,
    const_conditions: Table<LazyValue<ty::ConstConditions<'static>>>,
    // FIXME(eddyb) perhaps compute this on the fly if cheap enough?
    coerce_unsized_info: Table<LazyValue<ty::adjustment::CoerceUnsizedInfo>>,
    mir_const_qualif: Table<LazyValue<mir::ConstQualifs>>,
    rendered_const: Table<LazyValue<String>>,
    rendered_precise_capturing_args: Table<LazyArray<PreciseCapturingArgKind<Symbol, Symbol>>>,
    fn_arg_idents: Table<LazyArray<Option<Ident>>>,
    coroutine_kind: Table<hir::CoroutineKind>,
    coroutine_for_closure: Table<RemappedRawDefId>,
    adt_destructor: Table<LazyValue<ty::Destructor>>,
    adt_async_destructor: Table<LazyValue<ty::AsyncDestructor>>,
    coroutine_by_move_body_def_id: Table<RemappedRawDefId>,
    eval_static_initializer: Table<LazyValue<mir::interpret::ConstAllocation<'static>>>,
    trait_def: Table<LazyValue<ty::TraitDef>>,
    expn_that_defined: Table<LazyValue<ExpnId>>,
    default_fields: Table<LazyValue<DefId>>,
    params_in_repr: Table<LazyValue<DenseBitSet<u32>>>,
    repr_options: Table<LazyValue<ReprOptions>>,
    // `def_keys` and `def_path_hashes` represent a lazy version of a
    // `DefPathTable`. This allows us to avoid deserializing an entire
    // `DefPathTable` up front, since we may only ever use a few
    // definitions from any given crate.
    def_keys: Table<LazyValue<DefKey>>,
    variant_data: Table<LazyValue<VariantData>>,
    assoc_container: Table<LazyValue<ty::AssocContainer>>,
    macro_definition: Table<LazyValue<ast::DelimArgs>>,
    deduced_param_attrs: Table<LazyArray<DeducedParamAttrs>>,
    collect_return_position_impl_trait_in_trait_tys: Table<LazyValue<DefIdMap<ty::EarlyBinder<'static, Ty<'static>>>>>,
    doc_link_resolutions: Table<LazyValue<DocLinkResMap>>,
    doc_link_traits_in_scope: Table<LazyArray<DefId>>,
    assumed_wf_types_for_rpitit: Table<LazyArray<(Ty<'static>, Span)>>,
    opaque_ty_origin: Table<LazyValue<hir::OpaqueTyOrigin<DefId>>>,
    anon_const_kind: Table<LazyValue<ty::AnonConstKind>>,
    const_of_item: Table<LazyValue<Option<ty::EarlyBinder<'static, ty::Const<'static>>>>>,
    associated_types_for_impl_traits_in_trait_or_impl: Table<LazyValue<DefIdMap<Vec<DefId>>>>,
    args_known_to_outlive_alias_params: Table<LazyValue<Vec<(usize, DenseBitSet<u32>)>>>,
    mut_restriction: Table<LazyValue<ty::RestrictionKind>>,
}

#[derive(TyEncodable, TyDecodable)]
struct VariantData {
    idx: VariantIdx,
    discr: ty::VariantDiscr,
    /// If this is unit or tuple-variant/struct, then this is the index of the ctor id.
    ctor: Option<(CtorKind, LocalDefId)>,
    is_non_exhaustive: bool,
}

bitflags::bitflags! {
    #[derive(Default)]
    pub struct AttrFlags: u8 {
        const IS_DOC_HIDDEN = 1 << 0;
    }
}

/// A span tag byte encodes a bunch of data, so that we can cut out a few extra bytes from span
/// encodings (which are very common, for example, libcore has ~650,000 unique spans and over 1.1
/// million references to prior-written spans).
///
/// The byte format is split into several parts:
///
/// [ a a a a a c d d ]
///
/// `a` bits represent the span length. We have 5 bits, so we can store lengths up to 30 inline, with
/// an all-1s pattern representing that the length is stored separately.
///
/// `c` represents whether the span context is zero (and then it is not stored as a separate varint)
/// for direct span encodings, and whether the offset is absolute or relative otherwise (zero for
/// absolute).
///
/// d bits represent the kind of span we are storing (local, foreign, partial, indirect).
#[derive(Encodable, Decodable, Copy, Clone)]
struct SpanTag(u8);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum SpanKind {
    Local = 0b00,
    Foreign = 0b01,
    Partial = 0b10,
    // Indicates the actual span contents are elsewhere.
    // If this is the kind, then the span context bit represents whether it is a relative or
    // absolute offset.
    Indirect = 0b11,
}

impl SpanTag {
    fn new(kind: SpanKind, context: rustc_span::SyntaxContext, length: usize) -> SpanTag {
        let mut data = 0u8;
        data |= kind as u8;
        if context.is_root() {
            data |= 0b100;
        }
        let all_1s_len = (0xffu8 << 3) >> 3;
        // strictly less than - all 1s pattern is a sentinel for storage being out of band.
        if length < all_1s_len as usize {
            data |= (length as u8) << 3;
        } else {
            data |= all_1s_len << 3;
        }

        SpanTag(data)
    }

    fn indirect(relative: bool, length_bytes: u8) -> SpanTag {
        let mut tag = SpanTag(SpanKind::Indirect as u8);
        if relative {
            tag.0 |= 0b100;
        }
        assert!(length_bytes <= 8);
        tag.0 |= length_bytes << 3;
        tag
    }

    fn kind(self) -> SpanKind {
        let masked = self.0 & 0b11;
        match masked {
            0b00 => SpanKind::Local,
            0b01 => SpanKind::Foreign,
            0b10 => SpanKind::Partial,
            0b11 => SpanKind::Indirect,
            _ => unreachable!(),
        }
    }

    fn is_relative_offset(self) -> bool {
        debug_assert_eq!(self.kind(), SpanKind::Indirect);
        self.0 & 0b100 != 0
    }

    fn context(self) -> Option<rustc_span::SyntaxContext> {
        if self.0 & 0b100 != 0 { Some(rustc_span::SyntaxContext::root()) } else { None }
    }

    fn length(self) -> Option<rustc_span::BytePos> {
        let all_1s_len = (0xffu8 << 3) >> 3;
        let len = self.0 >> 3;
        if len != all_1s_len { Some(rustc_span::BytePos(u32::from(len))) } else { None }
    }
}

// Tags for encoding Symbol's
const SYMBOL_STR: u8 = 0;
const SYMBOL_OFFSET: u8 = 1;
const SYMBOL_PREDEFINED: u8 = 2;

pub fn provide(providers: &mut Providers) {
    encoder::provide(&mut providers.queries);
    decoder::provide(providers);
}
