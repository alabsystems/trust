use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use rustc_attr_ir::{AttributeKind, EncodeCrossCrate, find_attr};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::{FxHashSet, FxIndexMap, FxIndexSet};
use rustc_data_structures::memmap::{Mmap, MmapMut};
use rustc_data_structures::owned_slice::slice_owned;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_data_structures::sync::{par_for_each_in, par_join};
use rustc_data_structures::temp_dir::MaybeTempDir;
use rustc_data_structures::thousands::usize_with_underscores;
use rustc_hir as hir;
use rustc_hir::def_id::{CRATE_DEF_ID, LOCAL_CRATE, LocalDefId, LocalDefIdSet};
use rustc_hir::definitions::DefPathData;
use rustc_hir_pretty::id_to_string;
use rustc_index::IndexVec;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::hir::map::compute_hir_hash;
use rustc_middle::middle::dependency_format::Linkage;
// Trust: cross-crate PROOF-position citation, increment 2 (TRANSPORT).
use rustc_middle::middle::trust_clean_proof::TrustCleanProofManifest;
use rustc_middle::middle::trust_ir_entry::{
    TrustIrCrateHeader, TrustIrEntryBlob, TrustIrLocalEntries, TrustIrUnencoded,
};
use rustc_middle::mir::interpret;
use rustc_middle::mir::trust_contract::TrustContractBundle;
use rustc_middle::query::Providers;
use rustc_middle::traits::specialization_graph;
use rustc_middle::ty::AssocContainer;
use rustc_middle::ty::codec::TyEncoder;
use rustc_middle::ty::fast_reject::{self, TreatParams};
use rustc_serialize::opaque::FileEncoder;
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_session::config::mitigation_coverage::DeniedPartialMitigation;
use rustc_session::config::{OptLevel, OutputType, TargetModifier};
use rustc_span::def_id::CRATE_MOD_ID;
// Trust: LINUX-SELF-HOST-1 — the encoder no longer takes the session-wide hygiene remapping;
// see `syntax_context_indices`.
use rustc_span::hygiene::HygieneEncodeContext;
use rustc_span::{
    ByteSymbol, ExternalSource, FileName, LocalExpnId, SourceFile, SpanData, SpanEncoder,
    StableSourceFileId, Symbol, SyntaxContext, bug, span_bug,
};
use rustc_structures::CrateType;
use tracing::{debug, instrument, trace};
use twox_hash::XxHash3_128;

use crate::diagnostics::{FailCreateFileEncoder, FailWriteFile};
use crate::eii::EiiMapEncodedKeyValue;
use crate::rmeta::remapped_def_id::RemappedRawDefId;
use crate::rmeta::*;

pub(super) struct EncodeContext<'a, 'tcx> {
    opaque: FileEncoder<'a>,
    metadata_hasher: Arc<Mutex<XxHash3_128>>,
    tcx: TyCtxt<'tcx>,
    feat: &'tcx rustc_feature::Features,
    pub(super) tables: TableBuilders,

    lazy_state: LazyState,
    span_shorthands: FxHashMap<Span, usize>,
    type_shorthands: FxHashMap<Ty<'tcx>, usize>,
    predicate_shorthands: FxHashMap<ty::PredicateKind<'tcx>, usize>,

    interpret_allocs: FxIndexSet<interpret::AllocId>,

    // This is used to speed up Span encoding.
    // The `usize` is an index into the `MonotonicVec`
    // that stores the `SourceFile`
    source_file_cache: (Arc<SourceFile>, usize),
    // The indices (into the `SourceMap`'s `MonotonicVec`)
    // of all of the `SourceFiles` that we need to serialize.
    // When we serialize a `Span`, we insert the index of its
    // `SourceFile` into the `FxIndexSet`.
    // The order inside the `FxIndexSet` is used as on-disk
    // order of `SourceFiles`, and encoded inside `Span`s.
    required_source_files: Option<FxIndexSet<usize>>,
    is_proc_macro: bool,
    hygiene_ctxt: Rc<RefCell<HygieneEncodeContext>>,
    // Used for both `Symbol`s and `ByteSymbol`s.
    symbol_index_table: FxHashMap<u32, usize>,
    // Trust: step 2 increment 6 (6.2) — under `-Zmeta-stats` only, the encoded size of each
    // definition's `optimized_mir` row and of its trust-ir entry, for the per-definition
    // comparison R-8 asks for (design §6.3). Empty otherwise.
    trust_ir_mir_bytes: Vec<(LocalDefId, usize)>,
    trust_ir_entry_bytes: Vec<(LocalDefId, usize)>,
    // Trust (6.5.4): the S complement; R per-definition statistics keep their denominator.
    trust_ir_template_defs: FxHashSet<LocalDefId>,
    // Trust: step 2 increment 6 (6.2) — under `-Zmeta-stats` only, the header's unencoded
    // rows counted by reason class (the text before the reason's first `(`). `None` when the
    // producer did not run.
    trust_ir_unencoded_classes: Option<Vec<(String, usize)>>,
    // Trust: step 2 increment 6 (6.5.1) — under `-Zmeta-stats` only, the rows the producer
    // routed to its level-S template builder (`TrustIrLocalEntries::templates`): how many carry
    // an entry, and the others counted by reason class. `None` when the producer did not run.
    trust_ir_template_classes: Option<(usize, Vec<(String, usize)>)>,
    pub(super) local_defs_remapping: LocalDefsRemapping,
    // Trust: LINUX-SELF-HOST-1 — the number written for a `SyntaxContext` (and, below, for a
    // local `ExpnId`) is the order in which this encoder first writes it, the root first at 0,
    // exactly as `required_source_files` numbers local `SourceFile`s. It used to be a rank over
    // every context the session held after `commit_end_of_determinism`, taken when
    // `encode_crate_root` started, with the raw session index for anything allocated later.
    // The session allocates a foreign context whenever it first decodes a span that carries
    // it, so that rank moved with work that encodes nothing: a typeck root replayed from a
    // `.twit` store decodes fewer core contexts, and `-Zthreads` > 1 runs `prefetch_mir`
    // before the snapshot instead of inside `encode_mir`. With `-Zmetadata-crate-hash` the
    // crate hash is a hash of these bytes, so every dependent moved too. The encode order is
    // the byte order, which byte-identical output already needs to be deterministic.
    syntax_context_indices: FxIndexSet<SyntaxContext>,
    local_expn_indices: FxIndexSet<LocalExpnId>,
}

/// If the current crate is a proc-macro, returns early with `LazyArray::default()`.
/// This is useful for skipping the encoding of things that aren't needed
/// for proc-macro crates.
macro_rules! empty_proc_macro {
    ($self:ident) => {
        if $self.is_proc_macro {
            return LazyArray::default();
        }
    };
}

macro_rules! encoder_methods {
    ($($name:ident($ty:ty);)*) => {
        $(fn $name(&mut self, value: $ty) {
            self.opaque.$name(value)
        })*
    }
}

impl<'a, 'tcx> Encoder for EncodeContext<'a, 'tcx> {
    const DETERMINISTIC_HASH_MAP_ENCODE: bool = true;

    encoder_methods! {
        emit_usize(usize);
        emit_u128(u128);
        emit_u64(u64);
        emit_u32(u32);
        emit_u16(u16);
        emit_u8(u8);

        emit_isize(isize);
        emit_i128(i128);
        emit_i64(i64);
        emit_i32(i32);
        emit_i16(i16);

        emit_raw_bytes(&[u8]);
    }
}

impl<'a, 'tcx, T> Encodable<EncodeContext<'a, 'tcx>> for LazyValue<T> {
    fn encode(&self, e: &mut EncodeContext<'a, 'tcx>) {
        e.emit_lazy_distance(self.position);
    }
}

impl<'a, 'tcx, T> Encodable<EncodeContext<'a, 'tcx>> for LazyArray<T> {
    fn encode(&self, e: &mut EncodeContext<'a, 'tcx>) {
        e.emit_usize(self.num_elems);
        if self.num_elems > 0 {
            e.emit_lazy_distance(self.position)
        }
    }
}

impl<'a, 'tcx, Ie, Id, T> Encodable<EncodeContext<'a, 'tcx>> for LazyTable<Ie, Id, T> {
    fn encode(&self, e: &mut EncodeContext<'a, 'tcx>) {
        e.emit_usize(self.width_and_sparse);
        e.emit_usize(self.len);
        e.emit_lazy_distance(self.position);
    }
}

impl<'a, 'tcx> Encodable<EncodeContext<'a, 'tcx>> for ExpnIndex {
    fn encode(&self, s: &mut EncodeContext<'a, 'tcx>) {
        s.emit_u32(self.as_u32());
    }
}

impl<'a, 'tcx> SpanEncoder for EncodeContext<'a, 'tcx> {
    fn def_path_hasher(&self) -> impl Fn(DefId) -> DefPathHash {
        self.tcx.prelocked_def_path_hasher()
    }

    fn encode_crate_num(&mut self, crate_num: CrateNum) {
        if crate_num != LOCAL_CRATE && self.is_proc_macro {
            panic!("Attempted to encode non-local CrateNum {crate_num:?} for proc-macro crate");
        }
        self.emit_u32(crate_num.as_u32());
    }

    /// This function panics as we need to remap only local def indices, however
    /// we can not determine if the def index is local given only def index.
    /// In metadata `LocalDefId` is used instead of `DefIndex` as with this wrapper
    /// around def index we certainly know that it came from local crate.
    fn encode_def_index(&mut self, _: DefIndex) {
        panic!("use LocalDefId or DefId or encode DefIndex manually")
    }

    fn encode_def_id(&mut self, def_id: DefId) {
        let def_id = self.local_defs_remapping.map_def_id(def_id);

        def_id.krate.encode(self);
        self.emit_u32(def_id.index.as_u32());
    }

    fn encode_syntax_context(&mut self, syntax_context: SyntaxContext) {
        self.hygiene_ctxt.borrow_mut().enqueue_syntax_context_for_encoding(syntax_context);
        // Trust: LINUX-SELF-HOST-1 — first-encounter number; see `syntax_context_indices`.
        let (index, _) = self.syntax_context_indices.insert_full(syntax_context);
        self.emit_u32(RemappedSyntaxContext::from_usize(index).as_u32());
    }

    fn encode_expn_id(&mut self, expn_id: ExpnId) {
        if expn_id.krate == LOCAL_CRATE {
            // We will only write details for local expansions. Non-local expansions will fetch
            // data from the corresponding crate's metadata.
            // FIXME(#43047) FIXME(#74731) We may eventually want to avoid relying on external
            // metadata from proc-macro crates.
            self.hygiene_ctxt.borrow_mut().schedule_expn_data_for_encoding(expn_id);
        }
        expn_id.krate.encode(self);

        let raw_expn_index = match expn_id.as_local() {
            // Trust: LINUX-SELF-HOST-1 — first-encounter number; see `syntax_context_indices`.
            // A foreign `ExpnId` already carries its owning crate's encoded index.
            Some(local_expn) => {
                let (index, _) = self.local_expn_indices.insert_full(local_expn);
                RemappedLocalExpnIndex::from_usize(index).as_u32()
            }
            None => expn_id.local_id.as_u32(),
        };

        raw_expn_index.encode(self);
    }

    fn encode_span(&mut self, span: Span) {
        match self.span_shorthands.entry(span) {
            Entry::Occupied(o) => {
                // If an offset is smaller than the absolute position, we encode with the offset.
                // This saves space since smaller numbers encode in less bits.
                let last_location = *o.get();
                // This cannot underflow. Metadata is written with increasing position(), so any
                // previously saved offset must be smaller than the current position.
                let offset = self.opaque.position() - last_location;
                if offset < last_location {
                    let needed = bytes_needed(offset);
                    SpanTag::indirect(true, needed as u8).encode(self);
                    self.opaque.write_with(|dest| {
                        *dest = offset.to_le_bytes();
                        needed
                    });
                } else {
                    let needed = bytes_needed(last_location);
                    SpanTag::indirect(false, needed as u8).encode(self);
                    self.opaque.write_with(|dest| {
                        *dest = last_location.to_le_bytes();
                        needed
                    });
                }
            }
            Entry::Vacant(v) => {
                let position = self.opaque.position();
                v.insert(position);
                // Data is encoded with a SpanTag prefix (see below).
                span.data().encode(self);
            }
        }
    }

    fn encode_symbol(&mut self, sym: Symbol) {
        self.encode_symbol_or_byte_symbol(sym.as_u32(), |this| this.emit_str(sym.as_str()));
    }

    fn encode_byte_symbol(&mut self, byte_sym: ByteSymbol) {
        self.encode_symbol_or_byte_symbol(byte_sym.as_u32(), |this| {
            this.emit_byte_str(byte_sym.as_byte_str())
        });
    }

    /// We override `encode` function for `LocalDefId` as its default
    /// encoding logic is `self.encode_def_id(def_id.to_def_id())`
    /// meaning that the crate num will also be encoded, however as in metadata we use
    /// `LocalDefId` as a wrapper around def index we want to encode
    /// def index only, so we override the encode implementation.
    fn encode_local_def_id(&mut self, def_id: LocalDefId) {
        self.emit_u32(self.local_defs_remapping.map_local_def_id(def_id).index.as_u32());
    }

    /// We override encoding logic for `DefKey` during metadata encoding,
    /// as `DefKey` has a field `parent` of type `Option<DefIndex>` whose encoding will
    /// cause panic. So we remap it to `LocalDefId` as def keys during metadata encoding are all local.
    fn encode_def_key(
        &mut self,
        parent: Option<DefIndex>,
        disambiguated_data: impl Encodable<Self>,
    ) {
        parent.as_ref().map(|p| LocalDefId { local_def_index: *p }).encode(self);
        disambiguated_data.encode(self);
    }
}

fn bytes_needed(n: usize) -> usize {
    (usize::BITS - n.leading_zeros()).div_ceil(u8::BITS) as usize
}

impl<'a, 'tcx> Encodable<EncodeContext<'a, 'tcx>> for SpanData {
    fn encode(&self, s: &mut EncodeContext<'a, 'tcx>) {
        // Don't serialize any `SyntaxContext`s from a proc-macro crate,
        // since we don't load proc-macro dependencies during serialization.
        // This means that any hygiene information from macros used *within*
        // a proc-macro crate (e.g. invoking a macro that expands to a proc-macro
        // definition) will be lost.
        //
        // This can show up in two ways:
        //
        // 1. Any hygiene information associated with identifier of
        // a proc macro (e.g. `#[proc_macro] pub fn $name`) will be lost.
        // Since proc-macros can only be invoked from a different crate,
        // real code should never need to care about this.
        //
        // 2. Using `Span::def_site` or `Span::mixed_site` will not
        // include any hygiene information associated with the definition
        // site. This means that a proc-macro cannot emit a `$crate`
        // identifier which resolves to one of its dependencies,
        // which also should never come up in practice.
        //
        // Additionally, this affects `Span::parent`, and any other
        // span inspection APIs that would otherwise allow traversing
        // the `SyntaxContexts` associated with a span.
        //
        // None of these user-visible effects should result in any
        // cross-crate inconsistencies (getting one behavior in the same
        // crate, and a different behavior in another crate) due to the
        // limited surface that proc-macros can expose.
        //
        // IMPORTANT: If this is ever changed, be sure to update
        // `rustc_span::hygiene::raw_encode_expn_id` to handle
        // encoding `ExpnData` for proc-macro crates.
        let ctxt = if s.is_proc_macro { SyntaxContext::root() } else { self.ctxt };

        if self.is_dummy() {
            let tag = SpanTag::new(SpanKind::Partial, ctxt, 0);
            tag.encode(s);
            if tag.context().is_none() {
                ctxt.encode(s);
            }
            return;
        }

        // The Span infrastructure should make sure that this invariant holds:
        debug_assert!(self.lo <= self.hi);

        if !s.source_file_cache.0.contains(self.lo) {
            let source_map = s.tcx.sess.source_map();
            let source_file_index = source_map.lookup_source_file_idx(self.lo);
            s.source_file_cache =
                (Arc::clone(&source_map.files()[source_file_index]), source_file_index);
        }
        let (ref source_file, source_file_index) = s.source_file_cache;
        debug_assert!(source_file.contains(self.lo));

        if !source_file.contains(self.hi) {
            // Unfortunately, macro expansion still sometimes generates Spans
            // that malformed in this way.
            let tag = SpanTag::new(SpanKind::Partial, ctxt, 0);
            tag.encode(s);
            if tag.context().is_none() {
                ctxt.encode(s);
            }
            return;
        }

        // There are two possible cases here:
        // 1. This span comes from a 'foreign' crate - e.g. some crate upstream of the
        // crate we are writing metadata for. When the metadata for *this* crate gets
        // deserialized, the deserializer will need to know which crate it originally came
        // from. We use `TAG_VALID_SPAN_FOREIGN` to indicate that a `CrateNum` should
        // be deserialized after the rest of the span data, which tells the deserializer
        // which crate contains the source map information.
        // 2. This span comes from our own crate. No special handling is needed - we just
        // write `TAG_VALID_SPAN_LOCAL` to let the deserializer know that it should use
        // our own source map information.
        //
        // If we're a proc-macro crate, we always treat this as a local `Span`.
        // In `encode_source_map`, we serialize foreign `SourceFile`s into our metadata
        // if we're a proc-macro crate.
        // This allows us to avoid loading the dependencies of proc-macro crates: all of
        // the information we need to decode `Span`s is stored in the proc-macro crate.
        let (kind, metadata_index) = if source_file.is_imported() && !s.is_proc_macro {
            // To simplify deserialization, we 'rebase' this span onto the crate it originally came
            // from (the crate that 'owns' the file it references. These rebased 'lo' and 'hi'
            // values are relative to the source map information for the 'foreign' crate whose
            // CrateNum we write into the metadata. This allows `imported_source_files` to binary
            // search through the 'foreign' crate's source map information, using the
            // deserialized 'lo' and 'hi' values directly.
            //
            // All of this logic ensures that the final result of deserialization is a 'normal'
            // Span that can be used without any additional trouble.
            let metadata_index = {
                // Introduce a new scope so that we drop the 'read()' temporary
                match &*source_file.external_src.read() {
                    ExternalSource::Foreign { metadata_index, .. } => *metadata_index,
                    src => panic!("Unexpected external source {src:?}"),
                }
            };

            (SpanKind::Foreign, metadata_index)
        } else {
            // Record the fact that we need to encode the data for this `SourceFile`
            let source_files =
                s.required_source_files.as_mut().expect("Already encoded SourceMap!");
            let (metadata_index, _) = source_files.insert_full(source_file_index);
            let metadata_index: u32 =
                metadata_index.try_into().expect("cannot export more than U32_MAX files");

            (SpanKind::Local, metadata_index)
        };

        // Encode the start position relative to the file start, so we profit more from the
        // variable-length integer encoding.
        let lo = self.lo - source_file.start_pos;

        // Encode length which is usually less than span.hi and profits more
        // from the variable-length integer encoding that we use.
        let len = self.hi - self.lo;

        let tag = SpanTag::new(kind, ctxt, len.0 as usize);
        tag.encode(s);
        if tag.context().is_none() {
            ctxt.encode(s);
        }
        lo.encode(s);
        if tag.length().is_none() {
            len.encode(s);
        }

        // Encode the index of the `SourceFile` for the span, in order to make decoding faster.
        metadata_index.encode(s);

        if kind == SpanKind::Foreign {
            // This needs to be two lines to avoid holding the `s.source_file_cache`
            // while calling `cnum.encode(s)`
            let cnum = s.source_file_cache.0.cnum;
            cnum.encode(s);
        }
    }
}

impl<'a, 'tcx> Encodable<EncodeContext<'a, 'tcx>> for [u8] {
    fn encode(&self, e: &mut EncodeContext<'a, 'tcx>) {
        Encoder::emit_usize(e, self.len());
        e.emit_raw_bytes(self);
    }
}

impl<'a, 'tcx> TyEncoder<'tcx> for EncodeContext<'a, 'tcx> {
    const CLEAR_CROSS_CRATE: bool = true;

    fn position(&self) -> usize {
        self.opaque.position()
    }

    fn type_shorthands(&mut self) -> &mut FxHashMap<Ty<'tcx>, usize> {
        &mut self.type_shorthands
    }

    fn predicate_shorthands(&mut self) -> &mut FxHashMap<ty::PredicateKind<'tcx>, usize> {
        &mut self.predicate_shorthands
    }

    fn encode_alloc_id(&mut self, alloc_id: &rustc_middle::mir::interpret::AllocId) {
        let (index, _) = self.interpret_allocs.insert_full(*alloc_id);

        index.encode(self);
    }
}

impl<'a, 'tcx> EncodeContext<'a, 'tcx> {
    fn emit_lazy_distance(&mut self, position: NonZero<usize>) {
        let pos = position.get();
        let distance = match self.lazy_state {
            LazyState::NoNode => bug!("emit_lazy_distance: outside of a metadata node"),
            LazyState::NodeStart(start) => {
                let start = start.get();
                assert!(pos <= start);
                start - pos
            }
            LazyState::Previous(last_pos) => {
                assert!(
                    last_pos <= position,
                    "make sure that the calls to `lazy*` \
                     are in the same order as the metadata fields",
                );
                position.get() - last_pos.get()
            }
        };
        self.lazy_state = LazyState::Previous(NonZero::new(pos).unwrap());
        self.emit_usize(distance);
    }

    pub(super) fn lazy<T: ParameterizedOverTcx, B: Borrow<T::Value<'tcx>>>(
        &mut self,
        value: B,
    ) -> LazyValue<T>
    where
        T::Value<'tcx>: Encodable<EncodeContext<'a, 'tcx>>,
    {
        let pos = NonZero::new(self.position()).unwrap();

        assert_eq!(self.lazy_state, LazyState::NoNode);
        self.lazy_state = LazyState::NodeStart(pos);
        value.borrow().encode(self);
        self.lazy_state = LazyState::NoNode;

        assert!(pos.get() <= self.position());

        LazyValue::from_position(pos)
    }

    pub(super) fn lazy_array<
        T: ParameterizedOverTcx,
        I: IntoIterator<Item = B>,
        B: Borrow<T::Value<'tcx>>,
    >(
        &mut self,
        values: I,
    ) -> LazyArray<T>
    where
        T::Value<'tcx>: Encodable<EncodeContext<'a, 'tcx>>,
    {
        let pos = NonZero::new(self.position()).unwrap();

        assert_eq!(self.lazy_state, LazyState::NoNode);
        self.lazy_state = LazyState::NodeStart(pos);
        let len = values.into_iter().map(|value| value.borrow().encode(self)).count();
        self.lazy_state = LazyState::NoNode;

        assert!(pos.get() <= self.position());

        LazyArray::from_position_and_num_elems(pos, len)
    }

    fn encode_symbol_or_byte_symbol(
        &mut self,
        index: u32,
        emit_str_or_byte_str: impl Fn(&mut Self),
    ) {
        // if symbol/byte symbol is predefined, emit tag and symbol index
        if Symbol::is_predefined(index) {
            self.opaque.emit_u8(SYMBOL_PREDEFINED);
            self.opaque.emit_u32(index);
        } else {
            // otherwise write it as string or as offset to it
            match self.symbol_index_table.entry(index) {
                Entry::Vacant(o) => {
                    self.opaque.emit_u8(SYMBOL_STR);
                    let pos = self.opaque.position();
                    o.insert(pos);
                    emit_str_or_byte_str(self);
                }
                Entry::Occupied(o) => {
                    let x = *o.get();
                    self.emit_u8(SYMBOL_OFFSET);
                    self.emit_usize(x);
                }
            }
        }
    }

    fn encode_def_path_table(&mut self) {
        let defs = self.tcx.definitions();
        if self.is_proc_macro {
            for def_id in std::iter::once(CRATE_DEF_ID)
                .chain(self.tcx.resolutions(()).proc_macros.iter().copied())
            {
                let def_key = defs.def_key(def_id);
                let def_path_hash = defs.def_path_hash(def_id);

                self.table_writer().def_keys(def_id, def_key);
                self.table_writer().def_path_hashes(def_id, def_path_hash.local_hash().as_u64());
            }
        } else {
            for def_id in self.local_defs_remapping.iter_sorted_local_ids() {
                let def_key = defs.def_key(def_id);
                let hash = defs.def_path_hash(def_id).local_hash().as_u64();

                self.table_writer().def_keys(def_id, def_key);
                self.table_writer().def_path_hashes(def_id, hash);
            }
        }
    }

    fn encode_def_path_hash_map(&mut self) -> LazyValue<DefPathHashMapRef<'static>> {
        self.lazy(DefPathHashMapRef::BorrowedFromTcx(self.tcx.def_path_hash_to_def_index_map()))
    }

    fn encode_source_map(
        &mut self,
    ) -> LazyTable<u32, u32, Option<LazyValue<rustc_span::SourceFile>>> {
        let source_map = self.tcx.sess.source_map();
        let all_source_files = source_map.files();

        // By replacing the `Option` with `None`, we ensure that we can't
        // accidentally serialize any more `Span`s after the source map encoding
        // is done.
        let required_source_files = self.required_source_files.take().unwrap();

        let mut adapted = TableBuilder::default();

        let local_crate_stable_id = self.tcx.stable_crate_id(LOCAL_CRATE);

        // Trust (DC-18a): `-Ztrust-path-free` judges each name exactly as it is written.
        let path_free = self.tcx.sess.opts.unstable_opts.trust_path_free;

        // Only serialize `SourceFile`s that were used during the encoding of a `Span`.
        //
        // The order in which we encode source files is important here: the on-disk format for
        // `Span` contains the index of the corresponding `SourceFile`.
        for (on_disk_index, &source_file_index) in required_source_files.iter().enumerate() {
            let source_file = &all_source_files[source_file_index];
            // Don't serialize imported `SourceFile`s, unless we're in a proc-macro crate.
            assert!(!source_file.is_imported() || self.is_proc_macro);

            // At export time we expand all source file paths to absolute paths because
            // downstream compilation sessions can have a different compiler working
            // directory, so relative paths from this or any other upstream crate
            // won't be valid anymore.
            //
            // At this point we also erase the actual on-disk path and only keep
            // the remapped version -- as is necessary for reproducible builds.
            let mut adapted_source_file = (**source_file).clone();

            match source_file.name {
                FileName::Real(ref original_file_name) => {
                    let mut adapted_file_name = original_file_name.clone();
                    adapted_file_name.update_for_crate_metadata();
                    adapted_source_file.name = FileName::Real(adapted_file_name);
                }
                _ => {
                    // expanded code, not from a file
                }
            };

            // Trust: DC-18a.
            if path_free {
                crate::trust_path_free::judge_file_name(
                    self.tcx,
                    source_file,
                    &adapted_source_file.name,
                );
            }

            // We're serializing this `SourceFile` into our crate metadata,
            // so mark it as coming from this crate.
            // This also ensures that we don't try to deserialize the
            // `CrateNum` for a proc-macro dependency - since proc macro
            // dependencies aren't loaded when we deserialize a proc-macro,
            // trying to remap the `CrateNum` would fail.
            if self.is_proc_macro {
                adapted_source_file.cnum = LOCAL_CRATE;
            }

            // Update the `StableSourceFileId` to make sure it incorporates the
            // id of the current crate. This way it will be unique within the
            // crate graph during downstream compilation sessions.
            adapted_source_file.stable_id = StableSourceFileId::from_filename_for_export(
                &adapted_source_file.name,
                local_crate_stable_id,
            );

            let on_disk_index: u32 =
                on_disk_index.try_into().expect("cannot export more than U32_MAX files");
            adapted.set_some(on_disk_index, self.lazy(adapted_source_file));
        }

        // Trust (DC-18a): a local file no span in this metadata names is still written by
        // name elsewhere (a Trust-IR entry's file table), so every local name is judged.
        // `encode_and_write_metadata` reports the refusals and writes no output.
        if path_free {
            for (index, source_file) in all_source_files.iter().enumerate() {
                if source_file.is_imported() || required_source_files.contains(&index) {
                    continue;
                }
                let mut exported = source_file.name.clone();
                if let FileName::Real(real) = &mut exported {
                    real.update_for_crate_metadata();
                }
                crate::trust_path_free::judge_file_name(self.tcx, source_file, &exported);
            }
        }

        adapted.encode(&mut self.opaque)
    }

    fn encode_crate_root(&mut self) -> (LazyValue<CrateRoot>, LazyValue<CrateRootUnhashed>) {
        let tcx = self.tcx;

        // We set it here as we need it only for metadata encoding,
        // while `with_encode_metadata_header` is used in some other places too.
        self.local_defs_remapping = LocalDefsRemapping::new(tcx);
        // Trust: LINUX-SELF-HOST-1 — no hygiene snapshot here: `SyntaxContext`s and local
        // `ExpnId`s are numbered as they are written (`syntax_context_indices`).

        let mut stats: Vec<(&'static str, usize)> = Vec::with_capacity(32);

        macro_rules! stat {
            ($label:literal, $f:expr) => {{
                let orig_pos = self.position();
                let res = $f();
                stats.push(($label, self.position() - orig_pos));
                res
            }};
        }

        // We have already encoded some things. Get their combined size from the current position.
        stats.push(("preamble", self.position()));

        let externally_implementable_items = stat!("externally-implementable-items", || self
            .encode_externally_implementable_items());

        let (crate_deps, dylib_dependency_formats) =
            stat!("dep", || (self.encode_crate_deps(), self.encode_dylib_dependency_formats()));

        let lib_features = stat!("lib-features", || self.encode_lib_features());

        let stability_implications =
            stat!("stability-implications", || self.encode_stability_implications());

        let (lang_items, lang_items_missing) = stat!("lang-items", || {
            (self.encode_lang_items(), self.encode_lang_items_missing())
        });

        let stripped_cfg_items = stat!("stripped-cfg-items", || self.encode_stripped_cfg_items());

        let diagnostic_items = stat!("diagnostic-items", || self.encode_diagnostic_items());

        let canonical_symbols = stat!("canonical-symbols", || self.encode_canonical_symbols());

        let fake_doc_items = stat!("fake-doc-items", || self.encode_fake_doc_items());

        let native_libraries = stat!("native-libs", || self.encode_native_libraries());

        let foreign_modules = stat!("foreign-modules", || self.encode_foreign_modules());

        _ = stat!("def-path-table", || self.encode_def_path_table());

        // Encode the def IDs of traits, for rustdoc and diagnostics.
        let traits = stat!("traits", || self.encode_traits());

        // Encode the def IDs of impls, for coherence checking.
        let impls = stat!("impls", || self.encode_impls());

        let incoherent_impls = stat!("incoherent-impls", || self.encode_incoherent_impls());

        _ = stat!("mir", || self.encode_mir());

        // Trust: step 2 increment 6 (6.2) — trust-ir entries in their own section, so
        // `-Zmeta-stats` reports them beside `mir` (the per-definition comparison of §6.3).
        // Only when the producer runs: a crate built without it reads no trust-ir query here
        // (no dependency edge for the metadata dep node, so incremental reuse is unchanged)
        // and its `-Zmeta-stats` gains no row, exactly as before this table existed.
        let trust_ir_header = if self.tcx.sess.trust_ir_lower_enabled() {
            stat!("trust-ir", || self.encode_trust_ir_entries())
        } else {
            None
        };

        _ = stat!("def-ids", || self.encode_def_ids());

        let interpret_alloc_index = stat!("interpret-alloc-index", || {
            let mut interpret_alloc_index = Vec::new();
            let mut n = 0;
            trace!("beginning to encode alloc ids");
            loop {
                let new_n = self.interpret_allocs.len();
                // if we have found new ids, serialize those, too
                if n == new_n {
                    // otherwise, abort
                    break;
                }
                trace!("encoding {} further alloc ids", new_n - n);
                for idx in n..new_n {
                    let id = self.interpret_allocs[idx];
                    let pos = self.position() as u64;
                    interpret_alloc_index.push(pos);
                    interpret::specialized_encode_alloc_id(self, tcx, id);
                }
                n = new_n;
            }
            self.lazy_array(interpret_alloc_index)
        });

        // Encode the proc macro data. This affects `tables`, so we need to do this before we
        // encode the tables. This overwrites def_keys, so it must happen after
        // encode_def_path_table.
        let proc_macro_data = stat!("proc-macro-data", || self.encode_proc_macros());

        let tables = stat!("tables", || self.tables.encode(&mut self.opaque));

        let debugger_visualizers =
            stat!("debugger-visualizers", || self.encode_debugger_visualizers());

        let exportable_items = stat!("exportable-items", || self.encode_exportable_items());

        let stable_order_of_exportable_impls =
            stat!("exportable-items", || self.encode_stable_order_of_exportable_impls());

        // Trust: (I7) — Clean-origin cross-crate transport, root halves; and, since
        // cross-crate PROOF-position citation increment 2, the proof transport manifest.
        //
        // THE TWO HALVES HAVE DIFFERENT CONDITIONS, ON PURPOSE.
        //
        // * The CALL lane's export list stays gated on the MINT REGISTRY, exactly as
        //   before. It is the digest table's second, independent encoding (I7 risk R1);
        //   gating it on anything else could drop a listed def and demote a Clean-origin
        //   def to ordinary Rust.
        // * The island SOURCES and the manifest are now encoded whenever this crate HAS
        //   islands. Until increment 2 they rode the registry's condition too, so a crate
        //   whose islands are proof-only transported NOTHING — and a pure spec crate, the
        //   flagship shape for a workspace's one spec crate, mints nothing by
        //   construction (`trust_clean_mint` grants for `def` only, and only for the
        //   emittable shapes). That made cross-crate CITATION unreachable by transport
        //   rather than by decision. The bytes are transport, never authority: the
        //   consumer re-elaborates and kernel-checks all of them under its OWN kernel.
        //
        // The old comment here claimed the trust queries "re-run the Clean kernel", and
        // that is no longer true of either query invoked below: `trust_clean_island_
        // sources` is `clean_origin_mir::collect_island_sources`, a HIR walk over
        // `free_items()` with no session and no kernel, and `trust_clean_proof_manifest`
        // hashes the strings that walk returns. A crate with no islands therefore pays
        // one walk of an inventory this phase has already computed, and writes the same
        // empty arrays it wrote before.
        // THE `lazy*` CALL ORDER IS LOAD-BEARING, and it is not the order the
        // decision is made in. `emit_lazy_distance` asserts that the positions the
        // `CrateRoot` fields carry are non-decreasing in FIELD-DECLARATION order —
        // here `trust_clean_island_sources`, then `trust_clean_origin_exports`, then
        // `trust_clean_proof_manifest`. MEASURED 2026-09-19 on a stage1 built from
        // the first draft of this hunk, which lazied exports → manifest → sources:
        // EVERY crate with a `clean { … }` island ICEd with
        //     make sure that the calls to `lazy*` are in the same order as the
        //     metadata fields
        // at rmeta/mod.rs's `CrateRoot::encode`. So both trust queries are asked
        // FIRST, the pair rule is decided on their values, and only then are the
        // three fields written in their declared order.
        let (trust_clean_island_sources, trust_clean_origin_exports, trust_clean_proof_manifest) =
            stat!("trust-clean-origin", || {
                let sources = tcx.trust_clean_island_sources(LOCAL_CRATE);
                // The manifest is computed by the same local provider that produced
                // the sources, in `rustc_mir_transform`, so the digest is taken over
                // the very vector encoded below and the two cannot drift apart. A
                // crate with islands whose manifest could not be minted is a compiler
                // defect the provider has already reported as fatal; encoding the
                // sources without it would publish bytes no consumer can identify, so
                // the unreachable arm writes NEITHER of the two transported halves.
                let manifest = if sources.is_empty() {
                    None
                } else {
                    tcx.trust_clean_proof_manifest(LOCAL_CRATE)
                };
                let sources: &[String] = if manifest.is_some() { sources } else { &[] };

                // 1. `trust_clean_island_sources`.
                let encoded_sources = if sources.is_empty() {
                    LazyArray::default()
                } else {
                    self.lazy_array(sources.iter())
                };
                // 2. `trust_clean_origin_exports`. Unconditional on the PROOF lane:
                //    the CALL lane's export list is the digest table's second,
                //    independent encoding, and dropping it to punish a defect in the
                //    proof half would demote a Clean-origin def to ordinary Rust. Its
                //    own readmission fails closed if it ever looks for the island
                //    text of a listed def and finds none.
                let encoded_exports = if tcx.resolutions(()).clean_origin_defs.is_empty() {
                    LazyArray::default()
                } else {
                    let exports = tcx.trust_clean_origin_exports(LOCAL_CRATE);
                    // Trust: as `LocalDefId` (see the CrateRoot field): these are
                    // this crate's own defs by construction.
                    self.lazy_array(
                        exports
                            .iter()
                            .map(|&local_def_index| LocalDefId { local_def_index }),
                    )
                };
                // 3. `trust_clean_proof_manifest`.
                let encoded_manifest = manifest.map(|manifest| {
                    self.lazy::<TrustCleanProofManifest, &TrustCleanProofManifest>(manifest)
                });
                (encoded_sources, encoded_exports, encoded_manifest)
            });

        // Encode exported symbols info. This is prefetched in `encode_metadata`.
        let (exported_non_generic_symbols, exported_generic_symbols) =
            stat!("exported-symbols", || {
                (
                    self.encode_exported_symbols(tcx.exported_non_generic_symbols(LOCAL_CRATE)),
                    self.encode_exported_symbols(tcx.exported_generic_symbols(LOCAL_CRATE)),
                )
            });

        // Encode the hygiene data.
        // IMPORTANT: this *must* be the last thing that we encode (other than `SourceMap`). The
        // process of encoding other items (e.g. `optimized_mir`) may cause us to load data from
        // the incremental cache. If this causes us to deserialize a `Span`, then we may load
        // additional `SyntaxContext`s into the global `HygieneData`. Therefore, we need to encode
        // the hygiene data last to ensure that we encode any `SyntaxContext`s that might be used.
        let (syntax_contexts, expn_data, expn_hashes) = stat!("hygiene", || self.encode_hygiene());

        let def_path_hash_map = stat!("def-path-hash-map", || self.encode_def_path_hash_map());

        // Encode source_map. This needs to be done last, because encoding `Span`s tells us which
        // `SourceFiles` we actually need to encode.
        let source_map = stat!("source-map", || self.encode_source_map());
        let target_modifiers = stat!("target-modifiers", || self.encode_target_modifiers());
        let denied_partial_mitigations = stat!("denied-partial-mitigations", || self
            .encode_enabled_denied_partial_mitigations());

        let root = stat!("crate-root", || {
            let attrs = tcx.hir_krate_attrs();
            self.lazy(CrateRoot {
                header: CrateHeader {
                    name: tcx.crate_name(LOCAL_CRATE),
                    triple: tcx.sess.opts.target_triple.clone(),
                    is_proc_macro_crate: proc_macro_data.is_some(),
                    is_stub: false,
                },

                stable_crate_id: tcx.stable_crate_id(LOCAL_CRATE),
                required_panic_strategy: tcx.required_panic_strategy(LOCAL_CRATE),
                panic_in_drop_strategy: tcx.sess.opts.unstable_opts.panic_in_drop,
                edition: tcx.sess.edition(),
                has_global_allocator: tcx.has_global_allocator(LOCAL_CRATE),
                has_alloc_error_handler: tcx.has_alloc_error_handler(LOCAL_CRATE),
                has_panic_handler: tcx.has_panic_handler(LOCAL_CRATE),
                has_default_lib_allocator: find_attr!(attrs, DefaultLibAllocator),
                externally_implementable_items,
                proc_macro_data,
                debugger_visualizers,
                compiler_builtins: find_attr!(attrs, CompilerBuiltins),
                needs_allocator: find_attr!(attrs, NeedsAllocator),
                needs_panic_runtime: find_attr!(attrs, NeedsPanicRuntime),
                no_builtins: find_attr!(attrs, NoBuiltins),
                panic_runtime: find_attr!(attrs, PanicRuntime),
                profiler_runtime: find_attr!(attrs, ProfilerRuntime),
                symbol_mangling_version: tcx.sess.opts.get_symbol_mangling_version(),

                crate_deps,
                dylib_dependency_formats,
                lib_features,
                stability_implications,
                lang_items,
                diagnostic_items,
                canonical_symbols,
                fake_doc_items,
                lang_items_missing,
                stripped_cfg_items,
                native_libraries,
                foreign_modules,
                source_map,
                target_modifiers,
                denied_partial_mitigations,
                traits,
                impls,
                incoherent_impls,
                // Trust: step 2 increment 6 (6.2).
                trust_ir_header,
                exportable_items,
                stable_order_of_exportable_impls,
                // Trust: (I7)
                trust_clean_island_sources,
                trust_clean_origin_exports,
                // Trust: cross-crate PROOF-position citation, increment 2.
                trust_clean_proof_manifest,
                exported_non_generic_symbols,
                exported_generic_symbols,
                interpret_alloc_index,
                tables,
                syntax_contexts,
                expn_data,
                expn_hashes,
                def_path_hash_map,
                specialization_enabled_in: tcx.specialization_enabled_in(LOCAL_CRATE),
                // Trust (2026-10-03): see the field.
                trust_references_alloc_error_hook: tcx
                    .trust_crate_references_alloc_error_hook(LOCAL_CRATE),
                // Trust (T6): see the field.
                trust_proof_session_mir: tcx.trust_crate_mir_is_proof_session_pipeline(LOCAL_CRATE),
            })
        });

        // By default the crate hash (SVH) is derived from the encoded metadata bytes. With
        // `-Z metadata-crate-hash=no` we instead store the legacy HIR-based hash, which the
        // `crate_hash` query computes directly without consulting `local_crate_hash`.
        let hash = if tcx.sess.opts.unstable_opts.metadata_crate_hash {
            self.opaque.flush();
            Svh::new(Fingerprint::from_le_bytes(
                self.metadata_hasher.lock().unwrap().finish_128().to_le_bytes(),
            ))
        } else {
            tcx.crate_hash(LOCAL_CRATE)
        };
        tcx.untracked().local_crate_hash.set(hash).expect("local_crate_hash set twice");

        let unhashed = stat!("final", || {
            // Indexed by dependency `CrateNum`, matching the numbering `encode_crate_deps` uses.
            // Slot 0 (`LOCAL_CRATE`) is filler; this crate's own value is `extra_filename`.
            let mut dep_extra_filenames = IndexVec::from_elem_n(String::new(), 1);
            if !self.is_proc_macro {
                for &cnum in tcx.crates(()).iter() {
                    let idx = dep_extra_filenames.push(tcx.extra_filename(cnum).to_owned());
                    assert_eq!(idx, cnum, "dep_extra_filenames must be indexed by CrateNum");
                }
            }

            self.lazy(CrateRootUnhashed {
                extra_filename: tcx.sess.opts.cg.extra_filename.clone(),
                dep_extra_filenames,
            })
        });

        let total_bytes = self.position();

        let computed_total_bytes: usize = stats.iter().map(|(_, size)| size).sum();
        assert_eq!(total_bytes, computed_total_bytes);

        if tcx.sess.opts.unstable_opts.meta_stats {
            use std::fmt::Write;

            self.opaque.flush();

            // Rewind and re-read all the metadata to count the zero bytes we wrote.
            let pos_before_rewind = self.opaque.file().stream_position().unwrap();
            let mut zero_bytes = 0;
            self.opaque.file().rewind().unwrap();
            let file = std::io::BufReader::new(self.opaque.file());
            for e in file.bytes() {
                if e.unwrap() == 0 {
                    zero_bytes += 1;
                }
            }
            assert_eq!(self.opaque.file().stream_position().unwrap(), pos_before_rewind);

            stats.sort_by_key(|&(_, usize)| usize);
            stats.reverse(); // bigger items first

            let prefix = "meta-stats";
            let perc = |bytes| (bytes * 100) as f64 / total_bytes as f64;

            let section_w = 23;
            let size_w = 10;
            let banner_w = 64;

            // We write all the text into a string and print it with a single
            // `eprint!`. This is an attempt to minimize interleaved text if multiple
            // rustc processes are printing macro-stats at the same time (e.g. with
            // `RUSTFLAGS='-Zmeta-stats' cargo build`). It still doesn't guarantee
            // non-interleaving, though.
            let mut s = String::new();
            _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
            _ = writeln!(s, "{prefix} METADATA STATS: {}", tcx.crate_name(LOCAL_CRATE));
            _ = writeln!(s, "{prefix} {:<section_w$}{:>size_w$}", "Section", "Size");
            _ = writeln!(s, "{prefix} {}", "-".repeat(banner_w));
            for (label, size) in stats {
                _ = writeln!(
                    s,
                    "{prefix} {:<section_w$}{:>size_w$} ({:4.1}%)",
                    label,
                    usize_with_underscores(size),
                    perc(size)
                );
            }
            _ = writeln!(s, "{prefix} {}", "-".repeat(banner_w));
            _ = writeln!(
                s,
                "{prefix} {:<section_w$}{:>size_w$} (of which {:.1}% are zero bytes)",
                "Total",
                usize_with_underscores(total_bytes),
                perc(zero_bytes)
            );
            _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
            // Trust: step 2 increment 6 (6.2) — the per-definition comparison (design §6.3):
            // each definition that carries a trust-ir entry, against its own `optimized_mir`
            // row (the MIR row alone: promoted MIR and the allocations a body references are
            // encoded elsewhere). Printed only when the crate carries entries.
            if self
                .trust_ir_entry_bytes
                .iter()
                .any(|(d, _)| !self.trust_ir_template_defs.contains(d))
            {
                let mir: FxHashMap<LocalDefId, usize> =
                    self.trust_ir_mir_bytes.iter().copied().collect();
                let mut pairs: Vec<(usize, usize)> = self
                    .trust_ir_entry_bytes
                    .iter()
                    .filter(|(def, _)| !self.trust_ir_template_defs.contains(def))
                    .filter_map(|(def, entry)| mir.get(def).map(|m| (*entry, *m)))
                    .collect();
                let entry_total: usize = pairs.iter().map(|(e, _)| e).sum();
                let mir_total: usize = pairs.iter().map(|(_, m)| m).sum();
                let not_larger = pairs.iter().filter(|(e, m)| e <= m).count();
                pairs.sort_by(|(e1, m1), (e2, m2)| (e1 * m2).cmp(&(e2 * m1)));
                let median = pairs
                    .get(pairs.len() / 2)
                    .map(|(e, m)| *e as f64 / (*m).max(1) as f64)
                    .unwrap_or(0.0);
                _ = writeln!(
                    s,
                    "{prefix} trust-ir per definition: {} with both rows; entry <= optimized_mir \
                     for {not_larger}; entry {} vs optimized_mir {} bytes; median entry/mir {median:.2}",
                    pairs.len(),
                    usize_with_underscores(entry_total),
                    usize_with_underscores(mir_total),
                );
                _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
            }
            // Trust (6.5.4): disclose the complete S row population independently of R.
            if !self.trust_ir_template_defs.is_empty() {
                let mir: FxHashMap<LocalDefId, usize> =
                    self.trust_ir_mir_bytes.iter().copied().collect();
                let mut pairs: Vec<(usize, usize)> = self
                    .trust_ir_entry_bytes
                    .iter()
                    .filter(|(def, _)| self.trust_ir_template_defs.contains(def))
                    .filter_map(|(def, entry)| mir.get(def).map(|m| (*entry, *m)))
                    .collect();
                let entry_total: usize = pairs.iter().map(|(e, _)| e).sum();
                let mir_total: usize = pairs.iter().map(|(_, m)| m).sum();
                let not_larger = pairs.iter().filter(|(e, m)| e <= m).count();
                pairs.sort_by(|(e1, m1), (e2, m2)| (e1 * m2).cmp(&(e2 * m1)));
                let median = pairs
                    .get(pairs.len() / 2)
                    .map(|(e, m)| *e as f64 / (*m).max(1) as f64)
                    .unwrap_or(0.0);
                _ = writeln!(
                    s,
                    "{prefix} trust-ir templates per definition: {} with both rows; template <= \
                     optimized_mir for {not_larger}; template {} vs optimized_mir {} bytes; \
                     median template/mir {median:.2}",
                    pairs.len(),
                    usize_with_underscores(entry_total),
                    usize_with_underscores(mir_total),
                );
                _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
            }
            if let Some(classes) = &self.trust_ir_unencoded_classes {
                let total: usize = classes.iter().map(|(_, n)| n).sum();
                let listed: Vec<String> = classes.iter().map(|(c, n)| format!("{c}={n}")).collect();
                _ = writeln!(
                    s,
                    "{prefix} trust-ir entries: {} encoded; {total} unencoded: {}",
                    self.trust_ir_entry_bytes.len(),
                    listed.join(" ")
                );
                _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
            }
            // Trust: step 2 increment 6 (6.5.1) — the routed (level-S) rows on a line of their own.
            // The total line counts all emitted R/S bytes; only refused routed rows remain
            // in its legacy template-pending aggregate. The S line records their real classes.
            if let Some((encoded, classes)) = &self.trust_ir_template_classes {
                let total: usize = classes.iter().map(|(_, n)| n).sum();
                let listed: Vec<String> = classes.iter().map(|(c, n)| format!("{c}={n}")).collect();
                _ = writeln!(
                    s,
                    "{prefix} trust-ir templates: {encoded} encoded; {total} unencoded: {}",
                    listed.join(" ")
                );
                _ = writeln!(s, "{prefix} {}", "=".repeat(banner_w));
            }
            eprint!("{s}");
        }

        (root, unhashed)
    }
}

struct AnalyzeAttrState {
    is_exported: bool,
    is_doc_hidden: bool,
}

/// Returns whether an attribute needs to be recorded in metadata, that is, if it's usable and
/// useful in downstream crates. Local-only attributes are an obvious example, but some
/// rustdoc-specific attributes can equally be of use while documenting the current crate only.
///
/// Removing these superfluous attributes speeds up compilation by making the metadata smaller.
///
/// Note: the `is_exported` parameter is used to cache whether the given `DefId` has a public
/// visibility: this is a piece of data that can be computed once per defid, and not once per
/// attribute. Some attributes would only be usable downstream if they are public.
#[inline]
fn analyze_attr(attr: &rustc_attr_ir::Attribute, state: &mut AnalyzeAttrState) -> bool {
    match attr {
        Attribute::Parsed(AttributeKind::DocComment { .. }) => {
            // We keep all doc comments reachable to rustdoc because they might be "imported" into
            // downstream crates if they use `#[doc(inline)]` to copy an item's documentation into
            // their own.
            state.is_exported
        }
        Attribute::Parsed(AttributeKind::Doc(d)) => {
            if d.hidden.is_some() {
                state.is_doc_hidden = true;
            }
            true
        }
        Attribute::Parsed(p) => p.encode_cross_crate() == EncodeCrossCrate::Yes,
        Attribute::Tool(_) | Attribute::DeriveHelper(_) => true,
    }
}

#[inline]
fn should_encode_span(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::ConstParam
        | DefKind::LifetimeParam
        | DefKind::Fn
        | DefKind::Const
        | DefKind::Static { .. }
        | DefKind::Ctor(..)
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::Macro(_)
        | DefKind::ExternCrate
        | DefKind::Use
        | DefKind::AnonConst
        | DefKind::OpaqueTy
        | DefKind::Field
        | DefKind::Impl { .. }
        | DefKind::Closure
        | DefKind::SyntheticCoroutineBody => true,
        DefKind::ForeignMod | DefKind::GlobalAsm | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_attrs(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::Fn
        | DefKind::Const
        | DefKind::Static { nested: false, .. }
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::Macro(_)
        | DefKind::Field
        | DefKind::ConstParam
        | DefKind::Impl { .. } => true,
        // Encoding attrs for `Use` items allows `#[doc(hidden)]` on re-exports
        // to be read cross-crate, which is needed for diagnostic path selection
        // in `visible_parent_map`. See #153477.
        DefKind::Use => true,
        // Tools may want to be able to detect their tool lints on
        // closures from upstream crates, too. This is used by
        // https://github.com/model-checking/kani and is not a performance
        // or maintenance issue for us.
        DefKind::Closure => true,
        DefKind::SyntheticCoroutineBody => false,
        DefKind::TyParam
        | DefKind::Ctor(..)
        | DefKind::ExternCrate
        | DefKind::ForeignMod
        | DefKind::AnonConst
        | DefKind::OpaqueTy
        | DefKind::LifetimeParam
        | DefKind::Static { nested: true, .. }
        | DefKind::GlobalAsm
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_expn_that_defined(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::Impl { .. } => true,
        DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::Fn
        | DefKind::Const
        | DefKind::ConstParam
        | DefKind::Static { .. }
        | DefKind::Ctor(..)
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::Macro(_)
        | DefKind::ExternCrate
        | DefKind::Use
        | DefKind::ForeignMod
        | DefKind::AnonConst
        | DefKind::OpaqueTy
        | DefKind::Field
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::Closure
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_visibility(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Mod
        | DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::Fn
        | DefKind::Const
        | DefKind::Static { nested: false, .. }
        | DefKind::Ctor(..)
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::Macro(..)
        | DefKind::Field => true,
        DefKind::Use
        | DefKind::ForeignMod
        | DefKind::TyParam
        | DefKind::ConstParam
        | DefKind::LifetimeParam
        | DefKind::AnonConst
        | DefKind::Static { nested: true, .. }
        | DefKind::OpaqueTy
        | DefKind::GlobalAsm
        | DefKind::Impl { .. }
        | DefKind::Closure
        | DefKind::ExternCrate
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_stability(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Mod
        | DefKind::Ctor(..)
        | DefKind::Variant
        | DefKind::Field
        | DefKind::Struct
        | DefKind::AssocTy
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::TyParam
        | DefKind::ConstParam
        | DefKind::Static { .. }
        | DefKind::Const
        | DefKind::Fn
        | DefKind::ForeignMod
        | DefKind::TyAlias
        | DefKind::OpaqueTy
        | DefKind::Enum
        | DefKind::Union
        | DefKind::Impl { .. }
        | DefKind::Trait
        | DefKind::TraitAlias
        | DefKind::Macro(..)
        | DefKind::ForeignTy => true,
        DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::AnonConst
        | DefKind::GlobalAsm
        | DefKind::Closure
        | DefKind::ExternCrate
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

/// Whether we should encode MIR. Return a pair, resp. for CTFE and for LLVM.
///
/// Computing, optimizing and encoding the MIR is a relatively expensive operation.
/// We want to avoid this work when not required. Therefore:
/// - we only compute `mir_for_ctfe` on items with const-eval semantics;
/// - we skip `optimized_mir` for check runs.
/// - we only encode `optimized_mir` that could be generated in other crates, that is, a code that
///   is either generic or has inline hint, and is reachable from the other crates (contained
///   in reachable set).
///
/// Note: Reachable set describes definitions that might be generated or referenced from other
/// crates and it can be used to limit optimized MIR that needs to be encoded. On the other hand,
/// the reachable set doesn't have much to say about which definitions might be evaluated at compile
/// time in other crates, so it cannot be used to omit CTFE MIR. For example, `f` below is
/// unreachable and yet it can be evaluated in other crates:
///
/// ```
/// const fn f() -> usize { 0 }
/// pub struct S { pub a: [usize; f()] }
/// ```
fn should_encode_mir(
    tcx: TyCtxt<'_>,
    reachable_set: &LocalDefIdSet,
    clean_origin_defs: &[(LocalDefId, Symbol, Span)],
    def_id: LocalDefId,
) -> (bool, bool) {
    // Trust: (I7) — a Clean-origin def's gated body ALWAYS travels, on both rows.
    //
    // WHY (measured 2026-08-19; this corrects the I7 plan's original claim): it is NOT
    // that `reachable_set` cannot contain a Clean-origin def. In the target configuration
    // it DOES: the mint plants the def into its enclosing module's resolutions with
    // `Visibility::Public` (rustc_resolve/src/build_reduced_graph.rs), the resolver's
    // effective-visibilities pass iterates module RESOLUTIONS, not AST/HIR items
    // (rustc_resolve/src/effective_visibilities.rs:125-148), privacy clones and only
    // extends that table (rustc_privacy/src/lib.rs:1787), and `reachable_set` seeds its
    // worklist from it — for library crate types `propagate_node` then inserts every
    // worklist item unconditionally, and `Node::Synthetic` (what `feed_hir` produces) is a
    // handled no-recurse arm, not a `bug!` (rustc_passes/src/reachable.rs:481-486,
    // :196-202, :299-306). So for a def in a `pub mod` of an rlib the stock
    // `reachable_set.contains` conjunct is TRUE.
    //
    // The conjuncts that actually decide the stock `opt` answer are the OTHER two, and
    // they vary with build mode:
    //   * `should_codegen()` is false for check-mode rmeta (pipelined `cargo check`), so
    //     downstream consumers of that rmeta would find no opt row at all;
    //   * at `OptLevel::No` a monomorphic def neither requires monomorphization nor is
    //     `cross_crate_inlinable` (cross_crate_inline.rs returns false at O0), while at
    //     O1+ the one-statement projection body can already be inlinable — i.e. whether
    //     the body travels would flip with the optimization level; and in a PRIVATE
    //     module the def genuinely is absent from `reachable_set`.
    //
    // None of those knobs may decide whether a Clean-origin body crosses the crate
    // boundary. The gated body is the ONLY body such a def has (there is no HIR to
    // re-derive one from), the importer re-gates whatever it decodes under its own
    // kernel, and a row whose presence varies with -O level, crate type, or module
    // visibility is a lane where a downstream crate sometimes links an upstream symbol
    // its own readmission never saw. Both rows therefore encode unconditionally: the
    // ctfe row because the def is fed `Constness::Const { always: false }` (callable in
    // const position), the opt row for every other consumer — and both extern decode
    // surfaces are gated by the import wave for the same reason (I7 risk R8).
    //
    // Registry lookup, never a HIR-derived filter: a Clean-origin def is exactly the
    // thing HIR inventories cannot see.
    if !clean_origin_defs.is_empty()
        && clean_origin_defs.iter().any(|&(clean_def, _, _)| clean_def == def_id)
    {
        return (true, true);
    }
    match tcx.def_kind(def_id) {
        // instance_mir uses mir_for_ctfe rather than optimized_mir for constructors
        DefKind::Ctor(_, _) => (true, false),
        // Constants
        DefKind::AnonConst | DefKind::AssocConst | DefKind::Const => (true, false),
        // Coroutines require optimized MIR to compute layout.
        DefKind::Closure if tcx.is_coroutine(def_id.to_def_id()) => (false, true),
        DefKind::SyntheticCoroutineBody => (false, true),
        // Full-fledged functions + closures
        DefKind::AssocFn | DefKind::Fn | DefKind::Closure => {
            let opt = tcx.sess.opts.unstable_opts.always_encode_mir
                || (tcx.sess.opts.output_types.should_codegen()
                    && reachable_set.contains(&def_id)
                    && (tcx.generics_of(def_id).requires_monomorphization(tcx)
                        || tcx.cross_crate_inlinable(def_id)));
            // Comptime fns do not have optimized MIR at all.
            let opt =
                opt && !matches!(tcx.constness(def_id), hir::Constness::Const { always: true });
            // The function has a `const` modifier or is in a `const trait`.
            let is_const_fn = tcx.is_const_fn(def_id.to_def_id());
            (is_const_fn, opt)
        }
        // The others don't have MIR.
        _ => (false, false),
    }
}

#[inline]
fn should_encode_variances<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::OpaqueTy
        | DefKind::Fn
        | DefKind::Ctor(..)
        | DefKind::AssocFn => true,
        DefKind::AssocTy => {
            // Only encode variances for RPITITs (for traits)
            matches!(tcx.opt_rpitit_info(def_id), Some(ty::ImplTraitInTraitData::Trait { .. }))
        }
        DefKind::Mod
        | DefKind::Variant
        | DefKind::Field
        | DefKind::AssocConst
        | DefKind::TyParam
        | DefKind::ConstParam
        | DefKind::Static { .. }
        | DefKind::Const
        | DefKind::ForeignMod
        | DefKind::TyAlias
        | DefKind::Impl { .. }
        | DefKind::Trait
        | DefKind::TraitAlias
        | DefKind::Macro(..)
        | DefKind::ForeignTy
        | DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::AnonConst
        | DefKind::GlobalAsm
        | DefKind::Closure
        | DefKind::ExternCrate
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_generics(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Trait
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::TraitAlias
        | DefKind::AssocTy
        | DefKind::Fn
        | DefKind::Const
        | DefKind::Static { .. }
        | DefKind::Ctor(..)
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::AnonConst
        | DefKind::OpaqueTy
        | DefKind::Impl { .. }
        | DefKind::Field
        | DefKind::TyParam
        | DefKind::Closure
        | DefKind::SyntheticCoroutineBody => true,
        DefKind::Mod
        | DefKind::ForeignMod
        | DefKind::ConstParam
        | DefKind::Macro(..)
        | DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::ExternCrate
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_type(tcx: TyCtxt<'_>, def_id: LocalDefId, def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Ctor(..)
        | DefKind::Field
        | DefKind::Fn
        | DefKind::Const
        | DefKind::Static { nested: false, .. }
        | DefKind::TyAlias
        | DefKind::ForeignTy
        | DefKind::Impl { .. }
        | DefKind::AssocFn
        | DefKind::AssocConst
        | DefKind::Closure
        | DefKind::ConstParam
        | DefKind::AnonConst
        | DefKind::SyntheticCoroutineBody => true,

        DefKind::OpaqueTy => {
            let origin = tcx.local_opaque_ty_origin(def_id);
            if let hir::OpaqueTyOrigin::FnReturn { parent, .. }
            | hir::OpaqueTyOrigin::AsyncFn { parent, .. } = origin
                && let hir::Node::TraitItem(trait_item) = tcx.hir_node_by_def_id(parent)
                && let (_, hir::TraitFn::Required(..)) = trait_item.expect_fn()
            {
                false
            } else {
                true
            }
        }

        DefKind::AssocTy => {
            let assoc_item = tcx.associated_item(def_id);
            match assoc_item.container {
                ty::AssocContainer::InherentImpl | ty::AssocContainer::TraitImpl(_) => true,
                ty::AssocContainer::Trait => assoc_item.defaultness(tcx).has_value(),
            }
        }
        DefKind::TyParam => {
            let hir::Node::GenericParam(param) = tcx.hir_node_by_def_id(def_id) else { bug!() };
            let hir::GenericParamKind::Type { default, .. } = param.kind else { bug!() };
            default.is_some()
        }

        DefKind::Trait
        | DefKind::TraitAlias
        | DefKind::Mod
        | DefKind::ForeignMod
        | DefKind::Macro(..)
        | DefKind::Static { nested: true, .. }
        | DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::ExternCrate
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_fn_sig(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(_, CtorKind::Fn) => true,

        DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Field
        | DefKind::Const
        | DefKind::Static { .. }
        | DefKind::Ctor(..)
        | DefKind::TyAlias
        | DefKind::OpaqueTy
        | DefKind::ForeignTy
        | DefKind::Impl { .. }
        | DefKind::AssocConst
        | DefKind::Closure
        | DefKind::ConstParam
        | DefKind::AnonConst
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::Trait
        | DefKind::TraitAlias
        | DefKind::Mod
        | DefKind::ForeignMod
        | DefKind::Macro(..)
        | DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::ExternCrate
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_constness(def_kind: DefKind) -> bool {
    match def_kind {
        DefKind::Fn
        | DefKind::AssocFn
        | DefKind::Closure
        | DefKind::Ctor(_, CtorKind::Fn)
        | DefKind::Impl { of_trait: false } => true,

        DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Field
        | DefKind::Const
        | DefKind::AssocConst
        | DefKind::AnonConst
        | DefKind::Static { .. }
        | DefKind::TyAlias
        | DefKind::OpaqueTy
        | DefKind::Impl { .. }
        | DefKind::ForeignTy
        | DefKind::ConstParam
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::Trait
        | DefKind::TraitAlias
        | DefKind::Mod
        | DefKind::ForeignMod
        | DefKind::Macro(..)
        | DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::ExternCrate
        | DefKind::Ctor(_, CtorKind::Const)
        | DefKind::Variant
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

#[inline]
fn should_encode_const(def_kind: DefKind) -> bool {
    match def_kind {
        // FIXME(mgca): should we remove Const and AssocConst here?
        DefKind::Const | DefKind::AssocConst | DefKind::AnonConst => true,

        DefKind::Struct
        | DefKind::Union
        | DefKind::Enum
        | DefKind::Variant
        | DefKind::Ctor(..)
        | DefKind::Field
        | DefKind::Fn
        | DefKind::Static { .. }
        | DefKind::TyAlias
        | DefKind::OpaqueTy
        | DefKind::ForeignTy
        | DefKind::Impl { .. }
        | DefKind::AssocFn
        | DefKind::Closure
        | DefKind::ConstParam
        | DefKind::AssocTy
        | DefKind::TyParam
        | DefKind::Trait
        | DefKind::TraitAlias
        | DefKind::Mod
        | DefKind::ForeignMod
        | DefKind::Macro(..)
        | DefKind::Use
        | DefKind::LifetimeParam
        | DefKind::GlobalAsm
        | DefKind::ExternCrate
        | DefKind::SyntheticCoroutineBody
        | DefKind::TestBinderConstraints => false,
    }
}

impl<'a, 'tcx> EncodeContext<'a, 'tcx> {
    fn encode_attrs(&mut self, def_id: LocalDefId) {
        let tcx = self.tcx;
        let mut state = AnalyzeAttrState {
            is_exported: tcx.effective_visibilities(()).is_exported(def_id),
            is_doc_hidden: false,
        };
        let attr_iter = tcx
            .hir_attrs(tcx.local_def_id_to_hir_id(def_id))
            .iter()
            .filter(|attr| analyze_attr(*attr, &mut state));

        self.table_writer().attributes(def_id, attr_iter);

        let mut attr_flags = AttrFlags::empty();
        if state.is_doc_hidden {
            attr_flags |= AttrFlags::IS_DOC_HIDDEN;
        }

        self.table_writer().attr_flags(def_id, attr_flags);
    }

    /// Helper struct simplifying writing to tables in the `tables` field.
    ///
    /// Writing to a field of `tables` should be as simple as
    /// `self.table_writer().field(index, tcx.get_field_value(index))`, even for complex structs
    /// that require encoding as `LazyValue`/`LazyArray` first.
    fn table_writer(&mut self) -> super::TableWriter<'a, 'tcx, '_> {
        super::TableWriter { encoder: self }
    }

    fn encode_def_ids(&mut self) {
        self.encode_info_for_mod(CRATE_DEF_ID);

        // Proc-macro crates only export proc-macro items, which are looked
        // up using `proc_macro_data`
        if self.is_proc_macro {
            return;
        }

        let tcx = self.tcx;
        for local_id in self.local_defs_remapping.iter_sorted_local_ids() {
            let def_id = local_id.to_def_id();
            let def_kind = tcx.def_kind(local_id);
            self.table_writer().def_kind(local_id, def_kind);
            // Trust: CB3 (2026-09-28) — a `clean { … }` island shares
            // `DefKind::GlobalAsm`; mark it, per def, so a dependent's
            // `DefKind::GlobalAsm` policies can admit the island without
            // admitting a real `global_asm!` in the same crate. Written only
            // for an island, so every other row reads back `false`.
            if def_kind == DefKind::GlobalAsm && tcx.trust_def_is_clean_island(def_id) {
                self.table_writer().trust_clean_island_item(local_id, true);
            }

            // The `DefCollector` will sometimes create unnecessary `DefId`s
            // for trivial const arguments which are directly lowered to
            // `ConstArgKind::Path`. We never actually access this `DefId`
            // anywhere so we don't need to encode it for other crates.
            // FIXME(mgca): This probably isn't true, they probably are accessed, but, test case?
            if def_kind == DefKind::AnonConst
                && matches!(
                    tcx.hir_node_by_def_id(local_id),
                    hir::Node::ConstArg(_)
                        | hir::Node::Infer(hir::InferArg { kind: hir::InferArgKind::Const, .. })
                )
            {
                continue;
            }

            // Trust: pre-filter on the cheap HIR check so the `trust_contracts`
            // query (dep node, arena-allocated empty bundle, unconditional
            // disk-cache row) only executes for defs that actually carry
            // contract clauses — not for every local def in the crate.
            if TrustContractBundle::def_may_have_contracts(tcx, local_id) {
                let trust_contracts = self.tcx.trust_contracts(def_id);
                if !trust_contracts.is_empty() {
                    self.table_writer().trust_contracts(local_id, trust_contracts);
                }
            }

            if def_kind == DefKind::Field
                && let hir::Node::Field(field) = tcx.hir_node_by_def_id(local_id)
                && let Some(anon) = field.default
            {
                self.table_writer().default_fields(local_id, anon.def_id.to_def_id());
            }

            if should_encode_span(def_kind) {
                let def_span = tcx.def_span(local_id);
                self.table_writer().def_span(local_id, def_span);
            }
            if should_encode_attrs(def_kind) {
                self.encode_attrs(local_id);
            }
            if should_encode_expn_that_defined(def_kind) {
                self.table_writer().expn_that_defined(local_id, tcx.expn_that_defined(def_id));
            }
            if should_encode_span(def_kind)
                && let Some(ident_span) = tcx.def_ident_span(def_id)
            {
                self.table_writer().def_ident_span(local_id, ident_span);
            }
            if def_kind.has_codegen_attrs() {
                self.table_writer().codegen_fn_attrs(local_id, tcx.codegen_fn_attrs(def_id));
            }
            if should_encode_visibility(def_kind) {
                let vis = tcx.local_visibility(local_id).map_id(|mod_id| mod_id.to_local_def_id());
                self.table_writer().visibility(local_id, vis);
            }
            if should_encode_stability(def_kind) {
                self.encode_stability(local_id);
                self.encode_const_stability(local_id);
                self.encode_default_body_stability(local_id);
                self.encode_deprecation(local_id);
            }
            if should_encode_variances(tcx, def_id, def_kind) {
                let v = tcx.variances_of(def_id);
                self.table_writer().variances_of(local_id, v);
            }
            if should_encode_fn_sig(def_kind) {
                self.table_writer().fn_sig(local_id, tcx.fn_sig(def_id));
            }
            if should_encode_generics(def_kind) {
                let g = tcx.generics_of(def_id);
                self.table_writer().generics_of(local_id, g);
                self.table_writer().explicit_clauses_of(local_id, tcx.explicit_clauses_of(def_id));
                let inferred_outlives = tcx.inferred_outlives_of(def_id);
                self.table_writer().inferred_outlives_of(local_id, inferred_outlives);

                for param in &g.own_params {
                    if let ty::GenericParamDefKind::Const { has_default: true, .. } = param.kind {
                        let default = tcx.const_param_default(param.def_id);
                        self.table_writer()
                            .const_param_default(param.def_id.expect_local(), default);
                    }
                }
            }
            if tcx.is_conditionally_const(def_id) {
                self.table_writer().const_conditions(local_id, tcx.const_conditions(def_id));
            }
            if should_encode_type(tcx, local_id, def_kind) {
                self.table_writer().type_of(local_id, tcx.type_of(def_id));
            }
            if should_encode_constness(def_kind) {
                let constness = tcx.constness(def_id);
                self.table_writer().constness(local_id, constness);
            }
            if let DefKind::Fn | DefKind::AssocFn = def_kind {
                let asyncness = tcx.asyncness(def_id);
                self.table_writer().asyncness(local_id, asyncness);
                self.table_writer().fn_arg_idents(local_id, tcx.fn_arg_idents(def_id));
            }
            self.table_writer().intrinsic(local_id, tcx.intrinsic(def_id));
            if let DefKind::TyParam | DefKind::Trait = def_kind {
                let default = tcx.object_lifetime_default(def_id);
                self.table_writer().object_lifetime_default(local_id, default);
            }
            if let DefKind::Trait = def_kind {
                self.table_writer().trait_def(local_id, tcx.trait_def(def_id));
                self.table_writer().explicit_super_clauses_of(
                    local_id,
                    tcx.explicit_super_clauses_of(def_id).skip_binder(),
                );
                self.table_writer().explicit_implied_clauses_of(
                    local_id,
                    tcx.explicit_implied_clauses_of(def_id).skip_binder(),
                );
                let module_children = tcx.module_children_local(local_id);
                self.table_writer().module_children_non_reexports(
                    local_id,
                    module_children.iter().map(|child| child.res.def_id().expect_local()),
                );
                if tcx.is_const_trait(def_id) {
                    self.table_writer().explicit_implied_const_bounds(
                        local_id,
                        tcx.explicit_implied_const_bounds(def_id).skip_binder(),
                    );
                }
            }
            if let DefKind::TraitAlias = def_kind {
                self.table_writer().trait_def(local_id, tcx.trait_def(def_id));
                self.table_writer().explicit_super_clauses_of(
                    local_id,
                    tcx.explicit_super_clauses_of(def_id).skip_binder(),
                );
                self.table_writer().explicit_implied_clauses_of(
                    local_id,
                    tcx.explicit_implied_clauses_of(def_id).skip_binder(),
                );
            }
            if let DefKind::Trait | DefKind::Impl { .. } = def_kind {
                let associated_item_def_ids = tcx.associated_item_def_ids(def_id);
                self.table_writer().associated_item_or_field_def_ids(
                    local_id,
                    associated_item_def_ids.iter().map(|&def_id| def_id.expect_local()),
                );
                for &def_id in associated_item_def_ids {
                    self.encode_info_for_assoc_item(def_id.expect_local());
                }
            }
            if let DefKind::Closure | DefKind::SyntheticCoroutineBody = def_kind
                && let Some(coroutine_kind) = tcx.coroutine_kind(def_id)
            {
                self.table_writer().coroutine_kind(local_id, coroutine_kind);
            }
            if def_kind == DefKind::Closure
                && tcx.type_of(def_id).skip_binder().is_coroutine_closure()
            {
                let coroutine_for_closure = tcx.coroutine_for_closure(def_id);
                let remapped_id =
                    RemappedRawDefId::create(coroutine_for_closure, &self.local_defs_remapping);

                self.table_writer().coroutine_for_closure(local_id, remapped_id);

                // If this async closure has a by-move body, record it too.
                if tcx.needs_coroutine_by_move_body_def_id(coroutine_for_closure) {
                    let id = tcx.coroutine_by_move_body_def_id(coroutine_for_closure);
                    let id = RemappedRawDefId::create(id, &self.local_defs_remapping);

                    self.table_writer()
                        .coroutine_by_move_body_def_id(coroutine_for_closure.expect_local(), id);
                }
            }
            if let DefKind::Static { .. } = def_kind {
                if !tcx.is_foreign_item(def_id) {
                    match tcx.eval_static_initializer(def_id) {
                        Ok(data) => {
                            self.table_writer().eval_static_initializer(local_id, data);
                        }
                        Err(err) => match err {
                            interpret::ErrorHandled::Reported(_, _) => {
                                tcx.dcx().delayed_bug(format!(
                                    "eval_static_initializer returned an error in metadata emission"
                                ));
                            }
                            interpret::ErrorHandled::TooGeneric(span) => {
                                span_bug!(span, "generic static???");
                            }
                        },
                    };
                }
            }
            if let DefKind::Enum | DefKind::Struct | DefKind::Union = def_kind {
                self.encode_info_for_adt(local_id);
            }
            if let DefKind::Mod = def_kind {
                self.encode_info_for_mod(local_id);
            }
            if let DefKind::Macro(_) = def_kind {
                self.encode_info_for_macro(local_id);
            }
            if let DefKind::TyAlias = def_kind {
                self.table_writer()
                    .type_alias_is_checked(local_id, tcx.type_alias_is_checked(def_id));

                if tcx.type_alias_is_checked(def_id) {
                    self.table_writer().args_known_to_outlive_alias_params(
                        local_id,
                        tcx.args_known_to_outlive_alias_params(def_id),
                    );
                }
            }
            if let DefKind::OpaqueTy = def_kind {
                self.encode_explicit_item_bounds(local_id);
                self.encode_explicit_item_self_bounds(local_id);
                self.table_writer().opaque_ty_origin(local_id, tcx.opaque_ty_origin(def_id));
                self.encode_precise_capturing_args(local_id);
                if tcx.is_conditionally_const(def_id) {
                    self.table_writer().explicit_implied_const_bounds(
                        local_id,
                        tcx.explicit_implied_const_bounds(def_id).skip_binder(),
                    );
                }
                self.table_writer().args_known_to_outlive_alias_params(
                    local_id,
                    tcx.args_known_to_outlive_alias_params(def_id),
                );
            }
            if let DefKind::AssocTy = def_kind {
                let assoc_item = tcx.associated_item(def_id);
                match assoc_item.container {
                    ty::AssocContainer::Trait => {
                        self.table_writer().args_known_to_outlive_alias_params(
                            local_id,
                            tcx.args_known_to_outlive_alias_params(def_id),
                        );
                    }
                    ty::AssocContainer::InherentImpl => {
                        self.table_writer().args_known_to_outlive_alias_params(
                            local_id,
                            tcx.args_known_to_outlive_alias_params(def_id),
                        );
                    }
                    ty::AssocContainer::TraitImpl(_) => {}
                }
            }
            if let DefKind::AnonConst = def_kind {
                self.table_writer().anon_const_kind(local_id, tcx.anon_const_kind(def_id));
            }
            if let DefKind::Const | DefKind::AssocConst = def_kind {
                self.table_writer().const_of_item(local_id, tcx.const_of_item(def_id));
            }
            if tcx.impl_method_has_trait_impl_trait_tys(def_id)
                && let Ok(table) = tcx.collect_return_position_impl_trait_in_trait_tys(def_id)
            {
                self.table_writer()
                    .collect_return_position_impl_trait_in_trait_tys(local_id, table);
            }
            if let DefKind::Impl { .. } | DefKind::Trait = def_kind {
                let table = tcx.associated_types_for_impl_traits_in_trait_or_impl(def_id);
                self.table_writer()
                    .associated_types_for_impl_traits_in_trait_or_impl(local_id, table);
            }
        }

        for (def_id, impls) in &tcx.crate_inherent_impls(()).0.inherent_impls {
            self.table_writer()
                .inherent_impls(*def_id, impls.iter().map(|def_id| def_id.expect_local()));
        }

        for (def_id, res_map) in &tcx.resolutions(()).doc_link_resolutions {
            self.table_writer().doc_link_resolutions(def_id.to_local_def_id(), res_map);
        }

        for (def_id, traits) in &tcx.resolutions(()).doc_link_traits_in_scope {
            self.table_writer().doc_link_traits_in_scope(def_id.to_local_def_id(), traits);
        }

        // Trust: (I7) — one verdict-digest row per Clean-origin def. The registry (fed by
        // rustc_resolve's mint, the ONE site that can create a Clean-origin `DefId`) is
        // iterated directly rather than filtered from a HIR-derived inventory — a
        // Clean-origin def is exactly the thing HIR walks cannot see, so a predicate over
        // `iter_local_def_id` filtered on HIR would be vacuously false while looking like a
        // working filter.
        //
        // The digest provider FATALS on any refusal instead of returning `None` for a
        // registry def: row-absence is how importers recognise ordinary Rust, so encoding
        // nothing here would fail OPEN (I7 risk R1). The `bug!` below is the belt on that
        // contract, and the root `trust_clean_origin_exports` list is the second,
        // independent encoding the importer cross-checks rows against.
        let clean_origin_defs = &tcx.resolutions(()).clean_origin_defs;
        let mut trust_digest_rows = 0usize;
        for &(clean_def, name, _) in clean_origin_defs.iter() {
            let def_id = clean_def.to_def_id();
            let Some(digest) = tcx.trust_clean_verdict_digest(def_id) else {
                bug!(
                    "Clean-origin def `{name}` ({def_id:?}) is in the mint registry but its \
                     verdict-digest provider returned None; the provider's contract is to \
                     fatal on refusal, so this is a compiler defect"
                );
            };
            self.table_writer().trust_clean_verdict_digest(clean_def, digest);
            trust_digest_rows += 1;
        }
        assert_eq!(
            trust_digest_rows,
            clean_origin_defs.len(),
            "every Clean-origin def must have exactly one verdict-digest row (I7 risk R1)"
        );
    }

    fn encode_externally_implementable_items(&mut self) -> LazyArray<EiiMapEncodedKeyValue> {
        empty_proc_macro!(self);
        let externally_implementable_items = self.tcx.externally_implementable_items(LOCAL_CRATE);

        self.lazy_array(externally_implementable_items.iter().map(
            |(foreign_item, (decl, impls))| {
                (
                    *foreign_item,
                    (decl.clone(), impls.iter().map(|(impl_did, i)| (*impl_did, *i)).collect()),
                )
            },
        ))
    }

    #[instrument(level = "trace", skip(self))]
    fn encode_info_for_adt(&mut self, local_def_id: LocalDefId) {
        let def_id = local_def_id.to_def_id();
        let tcx = self.tcx;
        let adt_def = tcx.adt_def(def_id);
        // Trust: every generated C2 face is kernel-checked before its entry is
        // published. Unsupported ADTs publish refusal data, so ordinary Rust
        // remains admissible without a value-face or a proof claim.
        if let Some(entry) = tcx.trust_odt_entry(def_id) {
            self.table_writer().trust_odt_entry(local_def_id, entry);
        }
        self.table_writer().repr_options(local_def_id, adt_def.repr());

        let params_in_repr = tcx.params_in_repr(def_id);
        self.table_writer().params_in_repr(local_def_id, params_in_repr);

        if adt_def.is_enum() {
            let module_children = tcx.module_children_local(local_def_id);
            self.table_writer().module_children_non_reexports(
                local_def_id,
                module_children.iter().map(|child| child.res.def_id().expect_local()),
            );
        } else {
            // For non-enum, there is only one variant, and its def_id is the adt's.
            debug_assert_eq!(adt_def.variants().len(), 1);
            debug_assert_eq!(adt_def.non_enum_variant().def_id, def_id);
            // Therefore, the loop over variants will encode its fields as the adt's children.
        }

        for (idx, variant) in adt_def.variants().iter_enumerated() {
            let variant_id = variant.def_id.expect_local();

            let data = VariantData {
                discr: variant.discr,
                idx,
                ctor: variant.ctor.map(|(kind, def_id)| (kind, def_id.expect_local())),
                is_non_exhaustive: variant.is_field_list_non_exhaustive(),
            };
            self.table_writer().variant_data(variant_id, data);

            self.table_writer().associated_item_or_field_def_ids(
                variant_id,
                variant.fields.iter().map(|f| f.did.expect_local()),
            );

            for field in &variant.fields {
                let field_id = field.did.expect_local();
                self.table_writer().safety(field_id, field.safety);
                self.table_writer().mut_restriction(field_id, field.mut_restriction);
            }

            if let Some((CtorKind::Fn, ctor_def_id)) = variant.ctor {
                let fn_sig = tcx.fn_sig(ctor_def_id);
                // FIXME only encode signature for ctor_def_id
                self.table_writer().fn_sig(variant_id, fn_sig);
            }
        }

        if let Some(destructor) = tcx.adt_destructor(local_def_id) {
            self.table_writer().adt_destructor(local_def_id, destructor);
        }

        if let Some(destructor) = tcx.adt_async_destructor(local_def_id) {
            self.table_writer().adt_async_destructor(local_def_id, destructor);
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_info_for_mod(&mut self, local_def_id: LocalDefId) {
        let tcx = self.tcx;

        // If we are encoding a proc-macro crates, `encode_info_for_mod` will
        // only ever get called for the crate root. We still want to encode
        // the crate root for consistency with other crates (some of the resolver
        // code uses it). However, we skip encoding anything relating to child
        // items - we encode information about proc-macros later on.
        if self.is_proc_macro {
            // Encode this here because we don't do it in encode_def_ids.
            self.table_writer()
                .expn_that_defined(local_def_id, tcx.expn_that_defined(local_def_id));
        } else {
            let module_children = tcx.module_children_local(local_def_id);

            self.table_writer().module_children_non_reexports(
                local_def_id,
                module_children
                    .iter()
                    .filter(|child| child.reexport_chain.is_empty())
                    .map(|child| child.res.def_id().expect_local()),
            );

            self.table_writer().module_children_reexports(
                local_def_id,
                module_children.iter().filter(|child| !child.reexport_chain.is_empty()),
            );

            let ambig_module_children = tcx
                .resolutions(())
                .ambig_module_children
                .get(&local_def_id)
                .map_or_default(|v| &v[..]);
            self.table_writer().ambig_module_children(local_def_id, ambig_module_children);
        }
    }

    fn encode_explicit_item_bounds(&mut self, def_id: LocalDefId) {
        debug!("EncodeContext::encode_explicit_item_bounds({:?})", def_id);
        let bounds = self.tcx.explicit_item_bounds(def_id).skip_binder();
        self.table_writer().explicit_item_bounds(def_id, bounds);
    }

    fn encode_explicit_item_self_bounds(&mut self, def_id: LocalDefId) {
        debug!("EncodeContext::encode_explicit_item_self_bounds({:?})", def_id);
        let bounds = self.tcx.explicit_item_self_bounds(def_id).skip_binder();
        self.table_writer().explicit_item_self_bounds(def_id, bounds);
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_info_for_assoc_item(&mut self, def_id: LocalDefId) {
        let tcx = self.tcx;
        let item = tcx.associated_item(def_id);

        if matches!(item.container, AssocContainer::Trait | AssocContainer::TraitImpl(_)) {
            self.table_writer().defaultness(def_id, item.defaultness(tcx));
        }

        self.table_writer().assoc_container(def_id, item.container);

        if let AssocContainer::Trait = item.container
            && item.is_type()
        {
            self.encode_explicit_item_bounds(def_id);
            self.encode_explicit_item_self_bounds(def_id);
            if tcx.is_conditionally_const(def_id) {
                self.table_writer().explicit_implied_const_bounds(
                    def_id,
                    tcx.explicit_implied_const_bounds(def_id).skip_binder(),
                );
            }
        }
        if let ty::AssocKind::Type { data: ty::AssocTypeData::Rpitit(rpitit_info) } = item.kind {
            self.table_writer().opt_rpitit_info(def_id, rpitit_info);
            if matches!(rpitit_info, ty::ImplTraitInTraitData::Trait { .. }) {
                self.table_writer()
                    .assumed_wf_types_for_rpitit(def_id, tcx.assumed_wf_types_for_rpitit(def_id));
                self.encode_precise_capturing_args(def_id);
            }
        }
    }

    fn encode_precise_capturing_args(&mut self, def_id: LocalDefId) {
        let Some(precise_capturing_args) = self.tcx.rendered_precise_capturing_args(def_id) else {
            return;
        };

        self.table_writer().rendered_precise_capturing_args(def_id, precise_capturing_args);
    }

    fn encode_mir(&mut self) {
        if self.is_proc_macro {
            return;
        }

        let tcx = self.tcx;
        let reachable_set = tcx.reachable_set(());
        let clean_origin_defs = &tcx.resolutions(()).clean_origin_defs[..];

        let keys_and_jobs = tcx.mir_keys(()).iter().filter_map(|&def_id| {
            let (encode_const, encode_opt) =
                should_encode_mir(tcx, reachable_set, clean_origin_defs, def_id);
            if encode_const || encode_opt { Some((def_id, encode_const, encode_opt)) } else { None }
        });
        for (def_id, encode_const, encode_opt) in keys_and_jobs {
            debug_assert!(encode_const || encode_opt);

            debug!("EntryBuilder::encode_mir({:?})", def_id);
            if encode_opt {
                // Trust: step 2 increment 6 (6.2) — see `trust_ir_mir_bytes`.
                let trust_mir_start = self.position();
                self.table_writer().optimized_mir(def_id, tcx.optimized_mir(def_id));
                if tcx.sess.opts.unstable_opts.meta_stats {
                    self.trust_ir_mir_bytes.push((def_id, self.position() - trust_mir_start));
                }
                // Trust: PKG-C5d — the same body's `mentioned_items`, spans dropped and
                // nothing filtered, so `trust_mentioned_items` reads back exactly that
                // field (see the table's comment in `rmeta/mod.rs`).
                if let Some(items) = &tcx.optimized_mir(def_id).mentioned_items {
                    self.table_writer().trust_mentioned_items(
                        def_id,
                        items.iter().map(|item| item.node).collect::<Vec<_>>(),
                    );
                }

                self.table_writer()
                    .cross_crate_inlinable(def_id, tcx.cross_crate_inlinable(def_id));
                // Trust: D4 increment A (2026-09-24) — the user-`unsafe` SOURCE fact
                // travels beside every encoded body, computed by the only compiler that
                // has this body's HIR. Recorded (negated) only when the source is known
                // free of user `unsafe`; every other def, and every def a non-Trust or
                // older producer encoded, reads back as "has unsafe" downstream.
                if !self.tcx.trust_def_has_user_unsafe_source(def_id.to_def_id()) {
                    self.table_writer().trust_no_user_unsafe_source(def_id, true);
                }

                self.table_writer().closure_saved_names_of_captured_variables(
                    def_id,
                    tcx.closure_saved_names_of_captured_variables(def_id),
                );

                if tcx.is_coroutine(def_id.to_def_id())
                    && let Some(witnesses) = tcx.mir_coroutine_witnesses(def_id)
                {
                    self.table_writer().mir_coroutine_witnesses(def_id, witnesses);
                }
            }
            let mut is_trivial = false;
            if encode_const {
                if let Some((val, ty)) = tcx.trivial_const(def_id) {
                    is_trivial = true;
                    self.table_writer().trivial_const(def_id, (val, ty));
                } else {
                    is_trivial = false;
                    self.table_writer().mir_for_ctfe(def_id, tcx.mir_for_ctfe(def_id));
                }

                // FIXME(generic_const_exprs): this feels wrong to have in `encode_mir`
                let abstract_const = tcx.thir_abstract_const(def_id);
                if let Ok(Some(abstract_const)) = abstract_const {
                    self.table_writer().thir_abstract_const(def_id, abstract_const);
                }

                if should_encode_const(tcx.def_kind(def_id)) {
                    let qualifs = tcx.mir_const_qualif(def_id);
                    self.table_writer().mir_const_qualif(def_id, qualifs);
                    let body = tcx.hir_maybe_body_owned_by(def_id);
                    if let Some(body) = body {
                        let const_data = rendered_const(tcx, &body, def_id);
                        self.table_writer().rendered_const(def_id, const_data);
                    }
                }
            }
            if !is_trivial {
                self.table_writer().promoted_mir(def_id, tcx.promoted_mir(def_id));
            }

            if tcx.is_coroutine(def_id.to_def_id())
                && let Some(witnesses) = tcx.mir_coroutine_witnesses(def_id)
            {
                self.table_writer().mir_coroutine_witnesses(def_id, witnesses);
            }
        }

        // Encode all the deduced parameter attributes for everything that has MIR, even for items
        // that can't be inlined. But don't if we aren't optimizing in non-incremental mode, to
        // save the query traffic.
        if tcx.sess.opts.output_types.should_codegen()
            && tcx.sess.opts.optimize != OptLevel::No
            && tcx.sess.opts.incremental.is_none()
        {
            for &local_def_id in tcx.mir_keys(()) {
                if let DefKind::AssocFn | DefKind::Fn = tcx.def_kind(local_def_id) {
                    self.table_writer().deduced_param_attrs(
                        local_def_id,
                        tcx.deduced_param_attrs(local_def_id.to_def_id()),
                    );
                }
            }
        }
    }

    // Trust: one opaque entry per retained producer definition, independent of
    // optimized-MIR export. Preserve the legacy optimized-MIR refusal inventory
    // as well, so widening transport never erases a previous denominator. Nothing when the producer did not run: no row, no header.
    // Called only when `Session::trust_ir_lower_enabled` (see the call site). A proc-macro
    // crate built with the producer writes its header too (its crate-wide refusal, no row), so
    // the header a consumer reads is the one the local `trust_ir_crate_header` reports and a
    // header-less crate means only "built without the producer" (review 2026-10-05).
    fn encode_trust_ir_entries(&mut self) -> Option<LazyValue<TrustIrCrateHeader>> {
        if !self.tcx.sess.trust_ir_lower_enabled() {
            return None;
        }
        let tcx = self.tcx;
        let local = tcx.trust_ir_local_entries(());
        if !local.producer_ran {
            return None;
        }
        let (header, rows) = trust_ir_rows(tcx, local);
        let meta_stats = tcx.sess.opts.unstable_opts.meta_stats;
        if meta_stats {
            fn count(classes: &mut Vec<(String, usize)>, class: &str) {
                match classes.iter_mut().find(|(c, _)| *c == class) {
                    Some((_, n)) => *n += 1,
                    None => classes.push((class.to_string(), 1)),
                }
            }
            let class_of =
                |reason: &str| reason.split('(').next().unwrap_or(reason).trim().to_string();
            let mut classes: Vec<(String, usize)> = Vec::new();
            // Trust: step 2 increment 6 (6.5.1) — a row routed to the template builder is
            // counted here as `template-pending`, as it was before that builder existed, and by
            // its own class on the templates line.
            let mut template_classes: Vec<(String, usize)> = Vec::new();
            if let Some(reason) = &header.crate_refusal {
                count(&mut classes, &class_of(reason));
            }
            for row in &header.unencoded {
                if local.templates.contains(&row.def_index) {
                    count(&mut classes, "template-pending");
                    count(&mut template_classes, &class_of(&row.reason));
                } else {
                    count(&mut classes, &class_of(&row.reason));
                }
            }
            classes.sort();
            template_classes.sort();
            self.trust_ir_unencoded_classes = Some(classes);
            let encoded_templates = rows
                .iter()
                .filter(|(def_id, _)| local.templates.contains(&def_id.local_def_index.as_u32()))
                .count();
            self.trust_ir_template_classes = Some((encoded_templates, template_classes));
        }
        for (def_id, blob) in rows {
            let start = self.position();
            self.table_writer().trust_ir_entry(def_id, blob);
            if meta_stats {
                // Trust (6.5.4): total encoded rows still include both R and S.
                if local.templates.contains(&def_id.local_def_index.as_u32()) {
                    self.trust_ir_template_defs.insert(def_id);
                }
                self.trust_ir_entry_bytes.push((def_id, self.position() - start));
            }
        }
        Some(self.lazy(header))
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_stability(&mut self, def_id: LocalDefId) {
        // The query lookup can take a measurable amount of time in crates with many items. Check if
        // the stability attributes are even enabled before using their queries.
        if self.feat.staged_api() || self.tcx.sess.opts.unstable_opts.force_unstable_if_unmarked {
            if let Some(stab) = self.tcx.lookup_stability(def_id) {
                self.table_writer().lookup_stability(def_id, stab);
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_const_stability(&mut self, def_id: LocalDefId) {
        // The query lookup can take a measurable amount of time in crates with many items. Check if
        // the stability attributes are even enabled before using their queries.
        if self.feat.staged_api() || self.tcx.sess.opts.unstable_opts.force_unstable_if_unmarked {
            if let Some(stab) = self.tcx.lookup_const_stability(def_id) {
                self.table_writer().lookup_const_stability(def_id, stab);
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_default_body_stability(&mut self, def_id: LocalDefId) {
        // The query lookup can take a measurable amount of time in crates with many items. Check if
        // the stability attributes are even enabled before using their queries.
        if self.feat.staged_api() || self.tcx.sess.opts.unstable_opts.force_unstable_if_unmarked {
            if let Some(stab) = self.tcx.lookup_default_body_stability(def_id) {
                self.table_writer().lookup_default_body_stability(def_id, stab);
            }
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_deprecation(&mut self, def_id: LocalDefId) {
        if let Some(depr) = self.tcx.lookup_deprecation(def_id.to_def_id()) {
            self.table_writer().lookup_deprecation_entry(def_id, depr);
        }
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_info_for_macro(&mut self, def_id: LocalDefId) {
        let tcx = self.tcx;

        let (_, macro_def, _) = tcx.hir_expect_item(def_id).expect_macro();
        self.table_writer().is_macro_rules(def_id, macro_def.macro_rules);
        self.table_writer().macro_definition(def_id, &*macro_def.body);
    }

    fn encode_native_libraries(&mut self) -> LazyArray<NativeLib> {
        empty_proc_macro!(self);
        let used_libraries = self.tcx.native_libraries(LOCAL_CRATE);
        // Trust (DC-18a): a native library's name is written as given.
        if self.tcx.sess.opts.unstable_opts.trust_path_free {
            for lib in used_libraries {
                crate::trust_path_free::judge_native_library(self.tcx, lib);
            }
        }
        self.lazy_array(used_libraries.iter())
    }

    fn encode_foreign_modules(&mut self) -> LazyArray<ForeignModule> {
        empty_proc_macro!(self);
        let foreign_modules = self.tcx.foreign_modules(LOCAL_CRATE);
        self.lazy_array(foreign_modules.iter().map(|(_, m)| m).cloned())
    }

    fn encode_hygiene(&mut self) -> (SyntaxContextTable, ExpnDataTable, ExpnHashTable) {
        let mut syntax_contexts: TableBuilder<_, _, _> = Default::default();
        let mut expn_data_table: TableBuilder<_, _, _> = Default::default();
        let mut expn_hash_table: TableBuilder<_, _, _> = Default::default();

        HygieneEncodeContext::encode(
            &Rc::clone(&self.hygiene_ctxt),
            &mut (&mut *self, &mut syntax_contexts, &mut expn_data_table, &mut expn_hash_table),
            |(this, syntax_contexts, _, _), ctxt, ctxt_data| {
                // Trust: LINUX-SELF-HOST-1 — the number `encode_syntax_context` wrote for this
                // context; it numbered the context in the same call that enqueued it.
                let index = this
                    .syntax_context_indices
                    .get_index_of(&ctxt)
                    .expect("an enqueued SyntaxContext has an encoding number");
                syntax_contexts
                    .set_some(RemappedSyntaxContext::from_usize(index), this.lazy(ctxt_data));
            },
            |(this, _, expn_data_table, expn_hash_table), expn_id, expn_data, hash| {
                if let Some(expn_id) = expn_id.as_local() {
                    // Trust: LINUX-SELF-HOST-1 — as above, from `encode_expn_id`.
                    let index = this
                        .local_expn_indices
                        .get_index_of(&expn_id)
                        .expect("a scheduled local ExpnId has an encoding number");
                    let expn_index = RemappedLocalExpnIndex::from_usize(index);

                    expn_data_table.set_some(expn_index, this.lazy(expn_data.expect("local expn")));
                    expn_hash_table.set_some(expn_index, this.lazy(hash));
                }
            },
        );

        (
            syntax_contexts.encode(&mut self.opaque),
            expn_data_table.encode(&mut self.opaque),
            expn_hash_table.encode(&mut self.opaque),
        )
    }

    fn encode_proc_macros(&mut self) -> Option<ProcMacroData> {
        let is_proc_macro = self.tcx.crate_types().contains(&CrateType::ProcMacro);
        if is_proc_macro {
            let tcx = self.tcx;
            let proc_macro_decls_static = tcx.proc_macro_decls_static(()).unwrap();
            let proc_macro_decls_static = self.lazy(proc_macro_decls_static);

            let stability = tcx.lookup_stability(CRATE_DEF_ID);

            self.table_writer().def_kind(CRATE_DEF_ID, DefKind::Mod);
            self.table_writer().def_span(CRATE_DEF_ID, tcx.def_span(CRATE_DEF_ID.to_def_id()));
            self.encode_attrs(CRATE_DEF_ID);
            let vis = tcx.local_visibility(CRATE_DEF_ID).map_id(|mod_id| mod_id.to_local_def_id());
            self.table_writer().visibility(CRATE_DEF_ID, vis);
            if let Some(stability) = stability {
                self.table_writer().lookup_stability(CRATE_DEF_ID, stability);
            }
            self.encode_deprecation(CRATE_DEF_ID);
            if let Some(res_map) = tcx.resolutions(()).doc_link_resolutions.get(&CRATE_MOD_ID) {
                self.table_writer().doc_link_resolutions(CRATE_DEF_ID, res_map);
            }
            if let Some(traits) = tcx.resolutions(()).doc_link_traits_in_scope.get(&CRATE_MOD_ID) {
                self.table_writer().doc_link_traits_in_scope(CRATE_DEF_ID, traits);
            }

            let mut macros = vec![];

            // Normally, this information is encoded when we walk the items
            // defined in this crate. However, we skip doing that for proc-macro crates,
            // so we manually encode just the information that we need
            for &proc_macro in &tcx.resolutions(()).proc_macros {
                let id = proc_macro;
                let proc_macro = tcx.local_def_id_to_hir_id(proc_macro);
                let mut name = tcx.hir_name(proc_macro);
                let span = tcx.hir_span(proc_macro);
                // Proc-macros may have attributes like `#[allow_internal_unstable]`,
                // so downstream crates need access to them.
                let attrs = tcx.hir_attrs(proc_macro);
                let (macro_kind, kind) = if find_attr!(attrs, ProcMacro) {
                    (MacroKind::Bang, ProcMacroKind::Bang { name: name.as_str().to_owned() })
                } else if find_attr!(attrs, ProcMacroAttribute) {
                    (MacroKind::Attr, ProcMacroKind::Attr { name: name.as_str().to_owned() })
                } else if let Some((trait_name, helper_attrs)) = find_attr!(attrs,
                    ProcMacroDerive { trait_name, helper_attrs } => (trait_name, helper_attrs))
                {
                    name = *trait_name;
                    (
                        MacroKind::Derive,
                        ProcMacroKind::CustomDerive {
                            trait_name: name.as_str().to_owned(),
                            attributes: helper_attrs
                                .iter()
                                .map(|attr| attr.as_str().to_owned())
                                .collect(),
                        },
                    )
                } else {
                    bug!("Unknown proc-macro type for item {:?}", id);
                };

                macros.push((id, self.lazy(kind)));

                let mut def_key = tcx.hir_def_key(id);
                def_key.disambiguated_data.data = DefPathData::MacroNs(name);

                self.table_writer().def_kind(id, DefKind::Macro(macro_kind.into()));

                self.encode_attrs(id);
                self.table_writer().def_keys(id, def_key);
                self.table_writer().def_ident_span(id, span);
                self.table_writer().def_span(id, span);
                self.table_writer().visibility(id, ty::Visibility::Public);
                if let Some(stability) = stability {
                    self.table_writer().lookup_stability(id, stability);
                }
            }

            let macros = self.lazy_array(macros);

            let mut proc_macro_quoted_spans = TableBuilder::default();
            for (i, span) in tcx.sess.proc_macro_quoted_spans() {
                proc_macro_quoted_spans.set_some(i, self.lazy(span));
            }

            let proc_macro_quoted_spans = proc_macro_quoted_spans.encode(&mut self.opaque);

            Some(ProcMacroData {
                proc_macro_decls_static,
                stability,
                macros,
                proc_macro_quoted_spans,
            })
        } else {
            None
        }
    }

    fn encode_debugger_visualizers(&mut self) -> LazyArray<DebuggerVisualizerFile> {
        empty_proc_macro!(self);
        self.lazy_array(
            self.tcx
                .debugger_visualizers(LOCAL_CRATE)
                .iter()
                // Erase the path since it may contain privacy sensitive data
                // that we don't want to end up in crate metadata.
                // The path is only needed for the local crate because of
                // `--emit dep-info`.
                .map(DebuggerVisualizerFile::path_erased),
        )
    }

    fn encode_crate_deps(&mut self) -> LazyArray<CrateDep> {
        empty_proc_macro!(self);

        let deps = self
            .tcx
            .crates(())
            .iter()
            .map(|&cnum| {
                let dep = CrateDep {
                    name: self.tcx.crate_name(cnum),
                    hash: self.tcx.crate_hash(cnum),
                    host_hash: self.tcx.crate_host_hash(cnum),
                    kind: self.tcx.crate_dep_kind(cnum),
                    is_private: self.tcx.is_private_dep(cnum),
                };
                (cnum, dep)
            })
            .collect::<Vec<_>>();

        {
            // Sanity-check the crate numbers
            let mut expected_cnum = 1;
            for &(n, _) in &deps {
                assert_eq!(n, CrateNum::new(expected_cnum));
                expected_cnum += 1;
            }
        }

        // We're just going to write a list of crate 'name-hash-version's, with
        // the assumption that they are numbered 1 to n.
        // FIXME (#2166): This is not nearly enough to support correct versioning
        // but is enough to get transitive crate dependencies working.
        self.lazy_array(deps.iter().map(|(_, dep)| dep))
    }

    fn encode_target_modifiers(&mut self) -> LazyArray<TargetModifier> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        self.lazy_array(tcx.sess.opts.gather_target_modifiers())
    }

    fn encode_enabled_denied_partial_mitigations(&mut self) -> LazyArray<DeniedPartialMitigation> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        self.lazy_array(tcx.sess.gather_enabled_denied_partial_mitigations())
    }

    fn encode_lib_features(&mut self) -> LazyArray<(Symbol, FeatureStability)> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        let lib_features = tcx.lib_features(LOCAL_CRATE);
        self.lazy_array(lib_features.to_sorted_vec())
    }

    fn encode_stability_implications(&mut self) -> LazyArray<(Symbol, Symbol)> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        let implications = tcx.stability_implications(LOCAL_CRATE);
        let sorted = implications.to_sorted_stable_ord();
        self.lazy_array(sorted.into_iter().map(|(k, v)| (*k, *v)))
    }

    fn encode_canonical_symbols(&mut self) -> LazyArray<(Symbol, LocalDefId)> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        let canonical_symbols = &tcx.canonical_symbols(LOCAL_CRATE);
        self.lazy_array(canonical_symbols.iter().map(|cs| (cs.symbol, cs.def_id.expect_local())))
    }

    fn encode_diagnostic_items(&mut self) -> LazyArray<(Symbol, LocalDefId)> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        let diagnostic_items = &tcx.diagnostic_items(LOCAL_CRATE).name_to_id;
        self.lazy_array(
            diagnostic_items.iter().map(|(&name, def_id)| (name, def_id.expect_local())),
        )
    }

    fn encode_fake_doc_items(&mut self) -> LazyArray<LocalDefId> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        let fake_doc_items = &tcx.fake_doc_items(LOCAL_CRATE);
        self.lazy_array(fake_doc_items.iter().map(|cs| cs.expect_local()))
    }

    fn encode_lang_items(&mut self) -> LazyArray<(LocalDefId, LangItem)> {
        empty_proc_macro!(self);
        let lang_items = self.tcx.lang_items().iter();
        self.lazy_array(
            lang_items
                .filter_map(|(lang_item, def_id)| def_id.as_local().map(|id| (id, lang_item))),
        )
    }

    fn encode_lang_items_missing(&mut self) -> LazyArray<LangItem> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        self.lazy_array(&tcx.lang_items().missing)
    }

    fn encode_stripped_cfg_items(&mut self) -> LazyArray<StrippedCfgItem<LocalDefId>> {
        self.lazy_array(
            self.tcx
                .stripped_cfg_items(LOCAL_CRATE)
                .into_iter()
                .map(|item| item.clone().map_scope_id(|def_id| def_id.expect_local())),
        )
    }

    fn encode_traits(&mut self) -> LazyArray<LocalDefId> {
        empty_proc_macro!(self);
        self.lazy_array(self.tcx.traits(LOCAL_CRATE).iter().map(|def_id| def_id.expect_local()))
    }

    /// Encodes an index, mapping each trait to its (local) implementations.
    #[instrument(level = "debug", skip(self))]
    fn encode_impls(&mut self) -> LazyArray<TraitImpls> {
        empty_proc_macro!(self);
        let tcx = self.tcx;
        let mut trait_impls: FxIndexMap<DefId, Vec<(LocalDefId, Option<SimplifiedType>)>> =
            FxIndexMap::default();

        for id in tcx.hir_free_items() {
            let DefKind::Impl { of_trait } = tcx.def_kind(id.owner_id) else {
                continue;
            };
            let local_id = id.owner_id.def_id;

            if of_trait {
                let header = tcx.impl_trait_header(local_id);
                self.table_writer().impl_trait_header(local_id, header);

                let impl_is_fully_generic_for_reflection =
                    tcx.impl_is_fully_generic_for_reflection(local_id);

                self.table_writer().impl_is_fully_generic_for_reflection(
                    local_id,
                    impl_is_fully_generic_for_reflection,
                );
                self.table_writer().defaultness(local_id, tcx.defaultness(local_id));

                let trait_ref = header.trait_ref.instantiate_identity().skip_norm_wip();
                let simplified_self_ty = fast_reject::simplify_type(
                    tcx,
                    trait_ref.self_ty(),
                    TreatParams::InstantiateWithInfer,
                );
                trait_impls
                    .entry(trait_ref.def_id)
                    .or_default()
                    .push((local_id, simplified_self_ty));

                let trait_def = tcx.trait_def(trait_ref.def_id);
                if let Ok(mut an) = trait_def.ancestors(tcx, local_id.to_def_id())
                    && let Some(specialization_graph::Node::Impl(parent)) = an.nth(1)
                {
                    let parent = RemappedRawDefId::create(parent, &self.local_defs_remapping);
                    self.table_writer().impl_parent(local_id, parent);
                }

                // if this is an impl of `CoerceUnsized`, create its
                // "unsized info", else just store None
                if tcx.is_lang_item(trait_ref.def_id, LangItem::CoerceUnsized) {
                    let coerce_unsized_info = tcx.coerce_unsized_info(local_id).unwrap();
                    self.table_writer().coerce_unsized_info(local_id, coerce_unsized_info);
                }
            }
        }

        let trait_impls: Vec<_> = trait_impls
            .into_iter()
            .map(|(trait_def_id, impls)| TraitImpls {
                trait_id: RemappedRawDefId::create(trait_def_id, &self.local_defs_remapping),
                impls: self.lazy_array(&impls),
            })
            .collect();

        self.lazy_array(&trait_impls)
    }

    #[instrument(level = "debug", skip(self))]
    fn encode_incoherent_impls(&mut self) -> LazyArray<IncoherentImpls> {
        empty_proc_macro!(self);
        let tcx = self.tcx;

        let all_impls: Vec<_> = tcx
            .crate_inherent_impls(())
            .0
            .incoherent_impls
            .iter()
            .map(|(&simp, impls)| IncoherentImpls {
                self_ty: self.lazy(simp),
                impls: self.lazy_array(impls.iter().map(|def_id| *def_id)),
            })
            .collect();

        self.lazy_array(&all_impls)
    }

    fn encode_exportable_items(&mut self) -> LazyArray<LocalDefId> {
        empty_proc_macro!(self);
        self.lazy_array(
            self.tcx.exportable_items(LOCAL_CRATE).iter().map(|def_id| def_id.expect_local()),
        )
    }

    fn encode_stable_order_of_exportable_impls(&mut self) -> LazyArray<(LocalDefId, usize)> {
        empty_proc_macro!(self);
        let stable_order_of_exportable_impls =
            self.tcx.stable_order_of_exportable_impls(LOCAL_CRATE);
        self.lazy_array(
            stable_order_of_exportable_impls
                .iter()
                .map(|(def_id, idx)| (def_id.expect_local(), *idx)),
        )
    }

    // Encodes all symbols exported from this crate into the metadata.
    //
    // This pass is seeded off the reachability list calculated in the
    // middle::reachable module but filters out items that either don't have a
    // symbol associated with them (they weren't translated) or if they're an FFI
    // definition (as that's not defined in this crate).
    fn encode_exported_symbols(
        &mut self,
        exported_symbols: &[(ExportedSymbol<'tcx>, SymbolExportInfo)],
    ) -> LazyArray<(ExportedSymbol<'static>, SymbolExportInfo)> {
        empty_proc_macro!(self);

        self.lazy_array(exported_symbols.iter().cloned())
    }

    fn encode_dylib_dependency_formats(&mut self) -> LazyArray<Option<LinkagePreference>> {
        empty_proc_macro!(self);
        let formats = self.tcx.dependency_formats(());
        if let Some(arr) = formats.get(&CrateType::Dylib) {
            return self.lazy_array(arr.iter().skip(1 /* skip LOCAL_CRATE */).map(
                |slot| match *slot {
                    Linkage::NotLinked | Linkage::IncludedFromDylib => None,

                    Linkage::Dynamic => Some(LinkagePreference::RequireDynamic),
                    Linkage::Static => Some(LinkagePreference::RequireStatic),
                },
            ));
        }
        LazyArray::default()
    }
}

/// Used to prefetch queries which will be needed later by metadata encoding.
/// Only a subset of the queries are actually prefetched to keep this code smaller.
fn prefetch_mir(tcx: TyCtxt<'_>) {
    if !tcx.sess.opts.output_types.should_codegen() {
        // We won't emit MIR, so don't prefetch it.
        return;
    }

    let reachable_set = tcx.reachable_set(());
    let clean_origin_defs = &tcx.resolutions(()).clean_origin_defs[..];
    par_for_each_in(tcx.mir_keys(()).as_slice(), |&def_id| {
        if tcx.is_trivial_const(def_id) {
            return;
        }
        let (encode_const, encode_opt) =
            should_encode_mir(tcx, reachable_set, clean_origin_defs, def_id);

        if encode_const {
            tcx.ensure_done().mir_for_ctfe(def_id);
        }
        if encode_opt {
            tcx.ensure_done().optimized_mir(def_id);
        }
        if encode_opt || encode_const {
            tcx.ensure_done().promoted_mir(def_id);
        }
    })
}

// NOTE(eddyb) The following comment was preserved for posterity, even
// though it's no longer relevant as EBML (which uses nested & tagged
// "documents") was replaced with a scheme that can't go out of bounds.
//
// And here we run into yet another obscure archive bug: in which metadata
// loaded from archives may have trailing garbage bytes. Awhile back one of
// our tests was failing sporadically on the macOS 64-bit builders (both nopt
// and opt) by having ebml generate an out-of-bounds panic when looking at
// metadata.
//
// Upon investigation it turned out that the metadata file inside of an rlib
// (and ar archive) was being corrupted. Some compilations would generate a
// metadata file which would end in a few extra bytes, while other
// compilations would not have these extra bytes appended to the end. These
// extra bytes were interpreted by ebml as an extra tag, so they ended up
// being interpreted causing the out-of-bounds.
//
// The root cause of why these extra bytes were appearing was never
// discovered, and in the meantime the solution we're employing is to insert
// the length of the metadata to the start of the metadata. Later on this
// will allow us to slice the metadata to the precise length that we just
// generated regardless of trailing bytes that end up in it.

pub struct EncodedMetadata {
    // The declaration order matters because `full_metadata` should be dropped
    // before `_temp_dir`.
    full_metadata: Option<Mmap>,
    // This is an optional stub metadata containing only the crate header.
    // The header should be very small, so we load it directly into memory.
    stub_metadata: Option<Vec<u8>>,
    // The path containing the metadata, to record as work product.
    path: Option<Box<Path>>,
    // We need to carry MaybeTempDir to avoid deleting the temporary
    // directory while accessing the Mmap.
    _temp_dir: Option<MaybeTempDir>,
}

impl EncodedMetadata {
    /// Trust: the no-metadata form (same state `from_path` yields for a
    /// zero-length file). Used by the `--emit=trust-ir`-only lane, which
    /// otherwise encoded a multi-MB rmeta only to discard it (no metadata
    /// output requested, no codegen, no link).
    #[inline]
    pub fn empty() -> Self {
        Self { full_metadata: None, stub_metadata: None, path: None, _temp_dir: None }
    }

    #[inline]
    pub fn from_path(
        path: PathBuf,
        stub_path: Option<PathBuf>,
        temp_dir: Option<MaybeTempDir>,
    ) -> std::io::Result<Self> {
        let file = std::fs::File::open(&path)?;
        let file_metadata = file.metadata()?;
        if file_metadata.len() == 0 {
            return Ok(Self {
                full_metadata: None,
                stub_metadata: None,
                path: None,
                _temp_dir: None,
            });
        }
        let full_mmap = unsafe { Some(Mmap::map(file)?) };

        let stub =
            if let Some(stub_path) = stub_path { Some(std::fs::read(stub_path)?) } else { None };

        Ok(Self {
            full_metadata: full_mmap,
            stub_metadata: stub,
            path: Some(path.into()),
            _temp_dir: temp_dir,
        })
    }

    #[inline]
    pub fn full(&self) -> &[u8] {
        &self.full_metadata.as_deref().unwrap_or_default()
    }

    #[inline]
    pub fn stub_or_full(&self) -> &[u8] {
        self.stub_metadata.as_deref().unwrap_or(self.full())
    }

    #[inline]
    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }
}

impl<S: Encoder> Encodable<S> for EncodedMetadata {
    fn encode(&self, s: &mut S) {
        self.stub_metadata.encode(s);

        let slice = self.full();
        slice.encode(s)
    }
}

impl<D: Decoder> Decodable<D> for EncodedMetadata {
    fn decode(d: &mut D) -> Self {
        let stub = <Option<Vec<u8>>>::decode(d);

        let len = d.read_usize();
        let full_metadata = if len > 0 {
            let mut mmap = MmapMut::map_anon(len).unwrap();
            mmap.copy_from_slice(d.read_raw_bytes(len));
            Some(mmap.make_read_only().unwrap())
        } else {
            None
        };

        Self { full_metadata, stub_metadata: stub, path: None, _temp_dir: None }
    }
}

#[instrument(level = "trace", skip(tcx))]
pub fn encode_metadata(tcx: TyCtxt<'_>, path: &Path, ref_path: Option<&Path>) {
    // Since encoding metadata is not in a query, and nothing is cached,
    // there's no need to do dep-graph tracking for any of it.
    tcx.dep_graph.assert_ignored();

    let _prof_timer = tcx.prof.verbose_generic_activity("generate_crate_metadata");

    let dep_node = tcx.metadata_dep_node();

    // If the metadata dep-node is green, try to reuse the saved work product.
    if tcx.dep_graph.is_fully_enabled()
        && let incr_comp_session = tcx.incr_comp_session.unwrap()
        && let Some(old_incr_comp_session_dir) = &incr_comp_session.old_session_directory
        && let work_product_id =
            WorkProductId::from_cgu_name(WorkProduct::METADATA_WORKPRODUCT_CGU_NAME)
        && let Some(work_product) = tcx.dep_graph.previous_work_product(&work_product_id)
        && tcx.dep_graph.try_mark_green(tcx, &dep_node).is_some()
    {
        let saved_path = &work_product.saved_files[OutputType::Metadata.extension()];
        let source_file_in_incr_dir = &old_incr_comp_session_dir.join(saved_path);
        debug!("copying preexisting metadata from {source_file_in_incr_dir:?} to {path:?}");
        match rustc_fs_util::link_or_copy(&source_file_in_incr_dir, path) {
            Ok(_) => {}
            Err(err) => tcx.dcx().emit_fatal(FailCreateFileEncoder { err }),
        };

        // Read the SVH from the old metadata header.
        let file = std::fs::File::open(&source_file_in_incr_dir).unwrap();
        let mmap = unsafe { Mmap::map(file) }.unwrap();
        let owned = slice_owned(mmap, Deref::deref);
        let blob = MetadataBlob::new(owned);
        let hash = blob.expect("file already created").get_crate_hash();
        tcx.untracked().local_crate_hash.set(hash).expect("local_crate_hash set twice");

        // Generate the metadata stub manually, as that is a small file compared to full metadata.
        if let Some(ref_path) = ref_path {
            let _prof_timer = tcx.prof.verbose_generic_activity("generate_crate_metadata_stub");

            with_encode_metadata_header(tcx, ref_path, |ecx| {
                let header: LazyValue<CrateHeader> = ecx.lazy(CrateHeader {
                    name: tcx.crate_name(LOCAL_CRATE),
                    triple: tcx.sess.opts.target_triple.clone(),
                    is_proc_macro_crate: false,
                    is_stub: true,
                });
                (header.position.get(), 0)
            })
        }

        return;
    };

    if tcx.sess.opts.jobs.frontend.is_some() {
        // Prefetch some queries used by metadata encoding.
        // This is not necessary for correctness, but is only done for performance reasons.
        // It can be removed if it turns out to cause trouble or be detrimental to performance.
        par_join(
            || prefetch_mir(tcx),
            || {
                let _ = tcx.exported_non_generic_symbols(LOCAL_CRATE);
                let _ = tcx.exported_generic_symbols(LOCAL_CRATE);
            },
        );
    }

    // Perform metadata encoding inside a task, so the dep-graph can check if any encoded
    // information changes, and maybe reuse the work product.
    tcx.dep_graph.with_task(
        dep_node,
        tcx,
        || {
            with_encode_metadata_header(tcx, path, |ecx| {
                // Encode all the entries and extra information in the crate,
                // culminating in the `CrateRoot` which points to all of it.
                let (root, unhashed) = ecx.encode_crate_root();

                // Flush buffer to ensure backing file has the correct size.
                ecx.opaque.flush();
                // Record metadata size for self-profiling
                tcx.prof.artifact_size(
                    "crate_metadata",
                    "crate_metadata",
                    ecx.opaque.file().metadata().unwrap().len(),
                );

                (root.position.get(), unhashed.position.get())
            })
        },
        None,
    );

    // Generate the metadata stub manually, as that is a small file compared to full metadata.
    if let Some(ref_path) = ref_path {
        let _prof_timer = tcx.prof.verbose_generic_activity("generate_crate_metadata_stub");

        with_encode_metadata_header(tcx, ref_path, |ecx| {
            let header: LazyValue<CrateHeader> = ecx.lazy(CrateHeader {
                name: tcx.crate_name(LOCAL_CRATE),
                triple: tcx.sess.opts.target_triple.clone(),
                is_proc_macro_crate: false,
                is_stub: true,
            });
            (header.position.get(), 0)
        })
    }
}

fn with_encode_metadata_header(
    tcx: TyCtxt<'_>,
    path: &Path,
    f: impl FnOnce(&mut EncodeContext<'_, '_>) -> (usize, usize),
) {
    // By default the crate hash (SVH) is computed from the bytes of the encoded metadata,
    // Under `-Z metadata-crate-hash=no` the SVH comes from the legacy `crate_hash` query instead and
    // this hasher is never consulted, so we skip seeding it and feeding metadata bytes into it.
    let metadata_crate_hash = tcx.sess.opts.unstable_opts.metadata_crate_hash;
    // The SVH is an XXH3-128 digest of the encoded metadata bytes. XXH3 is a fast, non-cryptographic
    // hash; that is sufficient here because the SVH is only a change detector, is never keyed
    // secretly (it must be reproducible), and compiling a crate already runs its build scripts and
    // proc-macros, so the crate author is trusted regardless.
    let metadata_hasher = Arc::new(Mutex::new(XxHash3_128::new()));
    if metadata_crate_hash {
        // Fold in inputs that are not part of the encoded metadata bytes, reduced to a single
        // fingerprint via the stable hasher and then mixed into the byte digest.
        let hir_body_hash = compute_hir_hash(tcx);
        let supplement: Fingerprint = tcx.with_stable_hashing_context(|mut hcx| {
            let mut hasher = StableHasher::new();
            // Add dep_tracking_hash to ensure the SVH changes when any tracked flag changes.
            tcx.sess.opts.dep_tracking_hash(true).stable_hash(&mut hcx, &mut hasher);
            // Add HIR hash for untracked elements, e.g. DefKind::GlobalAsm.
            hir_body_hash.stable_hash(&mut hcx, &mut hasher);
            hasher.finish()
        });
        metadata_hasher.lock().unwrap().write(&supplement.to_le_bytes());
    }

    // Feed every flushed byte into `metadata_hasher` so the SVH covers the entire encoded metadata.
    let mut flush_strategy = {
        let metadata_hasher = Arc::clone(&metadata_hasher);
        move |bytes: &[u8]| metadata_hasher.lock().unwrap().write(bytes)
    };

    let mut encoder = if metadata_crate_hash {
        FileEncoder::with_flush_strategy(path, &mut flush_strategy)
    } else {
        FileEncoder::new(path)
    }
    .unwrap_or_else(|err| tcx.dcx().emit_fatal(FailCreateFileEncoder { err }));
    encoder.emit_raw_bytes(METADATA_HEADER);

    // Will be filled with the root position after encoding everything.
    encoder.emit_raw_bytes(&0u64.to_le_bytes());

    // Same with unhashed_position.
    encoder.emit_raw_bytes(&0u64.to_le_bytes());

    // Same with crate_hash.
    encoder.emit_raw_bytes(&Fingerprint::ZERO.to_le_bytes());

    let source_map_files = tcx.sess.source_map().files();
    let source_file_cache = (Arc::clone(&source_map_files[0]), 0);
    let required_source_files = Some(FxIndexSet::default());
    drop(source_map_files);

    let mut ecx = EncodeContext {
        opaque: encoder,
        metadata_hasher: Arc::clone(&metadata_hasher),
        tcx,
        feat: tcx.features(),
        tables: Default::default(),
        lazy_state: LazyState::NoNode,
        span_shorthands: Default::default(),
        type_shorthands: Default::default(),
        predicate_shorthands: Default::default(),
        source_file_cache,
        interpret_allocs: Default::default(),
        required_source_files,
        is_proc_macro: tcx.crate_types().contains(&CrateType::ProcMacro),
        hygiene_ctxt: Default::default(),
        symbol_index_table: Default::default(),
        trust_ir_mir_bytes: Vec::new(),
        trust_ir_entry_bytes: Vec::new(),
        trust_ir_template_defs: FxHashSet::default(),
        trust_ir_unencoded_classes: None,
        trust_ir_template_classes: None,
        local_defs_remapping: Default::default(),
        // Trust: LINUX-SELF-HOST-1 — the roots keep number 0, which both decoders
        // (`decode_syntax_context`, `decode_expn_id`) read as the root.
        syntax_context_indices: FxIndexSet::from_iter([SyntaxContext::root()]),
        local_expn_indices: FxIndexSet::from_iter([LocalExpnId::ROOT]),
    };

    // Encode the rustc version string in a predictable location.
    rustc_version(tcx.sess.cfg_version).encode(&mut ecx);

    let (root_position, unhashed_position) = f(&mut ecx);

    // Make sure we report any errors from writing to the file.
    // If we forget this, compilation can succeed with an incomplete rmeta file,
    // causing an ICE when the rmeta file is read by another compilation.
    if let Err((path, err)) = ecx.opaque.finish() {
        tcx.dcx().emit_fatal(FailWriteFile { path: &path, err });
    }

    let mut file = ecx.opaque.file();
    // We will return to this position after writing the root position and crate hash.
    let pos_before_seek = file.stream_position().unwrap();

    if let Err(err) = encode_root_position(file, root_position) {
        tcx.dcx().emit_fatal(FailWriteFile { path: ecx.opaque.path(), err });
    }

    if let Err(err) = encode_unhashed_position(file, unhashed_position) {
        tcx.dcx().emit_fatal(FailWriteFile { path: ecx.opaque.path(), err });
    }

    let hash = tcx
        .untracked()
        .local_crate_hash
        .get()
        .copied()
        .expect("local_crate_hash set during encoding");
    if let Err(err) = encode_crate_hash(file, hash) {
        tcx.dcx().emit_fatal(FailWriteFile { path: ecx.opaque.path(), err });
    }

    if let Err(err) = file.seek(SeekFrom::Start(pos_before_seek)) {
        tcx.dcx().emit_fatal(FailWriteFile { path: ecx.opaque.path(), err });
    }
}

fn encode_root_position(mut file: &File, pos: usize) -> Result<(), std::io::Error> {
    file.seek(SeekFrom::Start(ROOT_POS_OFFSET as u64))?;
    file.write_all(&pos.to_le_bytes())?;
    Ok(())
}

fn encode_unhashed_position(mut file: &File, pos: usize) -> Result<(), std::io::Error> {
    file.seek(SeekFrom::Start(UNHASHED_POS_OFFSET as u64))?;
    file.write_all(&pos.to_le_bytes())?;
    Ok(())
}

fn encode_crate_hash(mut file: &File, hash: Svh) -> Result<(), std::io::Error> {
    file.seek(SeekFrom::Start(CRATE_HASH_OFFSET as u64))?;
    file.write_all(&hash.as_fingerprint().to_le_bytes())?;
    Ok(())
}

// Trust: step 2 increment 6 (6.2) — the local crate's trust-ir header and entry rows, over
// the complete retained producer inventory plus the legacy optimized-MIR refusal
// inventory. A non-inline Rust body needs its entry even though Rust exports no
// optimized MIR for it. Transport expands; all producer validation/refusals remain.
// One function serves the encoder and local header provider, so they cannot differ.
fn trust_ir_rows<'a>(
    tcx: TyCtxt<'_>,
    local: &'a TrustIrLocalEntries,
) -> (TrustIrCrateHeader, Vec<(LocalDefId, &'a TrustIrEntryBlob)>) {
    let mut header = TrustIrCrateHeader {
        trust_ir_version: local.trust_ir_version,
        entry_schema: local.entry_schema,
        encoded: 0,
        unencoded: Vec::new(),
        crate_refusal: local.crate_refusal.clone(),
    };
    let mut rows = Vec::new();
    if header.crate_refusal.is_some() {
        return (header, rows);
    }
    let reachable_set = tcx.reachable_set(());
    let clean_origin_defs = &tcx.resolutions(()).clean_origin_defs[..];
    let mut definitions: std::collections::BTreeSet<u32> = tcx.mir_keys(())
        .iter()
        .copied()
        .filter(|&def| should_encode_mir(tcx, reachable_set, clean_origin_defs, def).1)
        .map(|def| def.local_def_index.as_u32())
        .collect();
    definitions.extend(local.entries.keys().copied());
    for def_index in definitions {
        let def_id = LocalDefId {
            local_def_index: rustc_hir::def_id::DefIndex::from_u32(def_index),
        };
        match local.entries.get(&def_index) {
            Some(Ok(blob)) => rows.push((def_id, blob)),
            Some(Err(reason)) => {
                header.unencoded.push(TrustIrUnencoded { def_index, reason: reason.clone() })
            }
            None => header.unencoded.push(TrustIrUnencoded {
                def_index,
                reason: rustc_middle::middle::trust_ir_entry::UNRECORDED_REASON.to_string(),
            }),
        }
    }
    header.encoded = rows.len() as u32;
    header.unencoded.sort();
    rows.sort_by_key(|(def_id, _)| def_id.local_def_index);
    (header, rows)
}

pub(crate) fn provide(providers: &mut Providers) {
    *providers = Providers {
        // Trust: step 2 increment 6 (6.2) — see `trust_ir_rows`.
        trust_ir_crate_header: |tcx, _: rustc_middle::query::LocalCrate| {
            if !tcx.sess.trust_ir_lower_enabled() {
                return None;
            }
            let local = tcx.trust_ir_local_entries(());
            local.producer_ran.then(|| trust_ir_rows(tcx, local).0)
        },
        doc_link_resolutions: |tcx, def_id| {
            tcx.resolutions(())
                .doc_link_resolutions
                .get(&def_id)
                .unwrap_or_else(|| span_bug!(tcx.def_span(def_id), "no resolutions for a doc link"))
        },
        doc_link_traits_in_scope: |tcx, def_id| {
            tcx.resolutions(()).doc_link_traits_in_scope.get(&def_id).unwrap_or_else(|| {
                span_bug!(tcx.def_span(def_id), "no traits in scope for a doc link")
            })
        },

        ..*providers
    }
}

/// Build a textual representation of an unevaluated constant expression.
///
/// If the const expression is too complex, an underscore `_` is returned.
/// For const arguments, it's `{ _ }` to be precise.
/// This means that the output is not necessarily valid Rust code.
///
/// Currently, only
///
/// * literals (optionally with a leading `-`)
/// * unit `()`
/// * blocks (`{ … }`) around simple expressions and
/// * paths without arguments
///
/// are considered simple enough. Simple blocks are included since they are
/// necessary to disambiguate unit from the unit type.
/// This list might get extended in the future.
///
/// Without this censoring, in a lot of cases the output would get too large
/// and verbose. Consider `match` expressions, blocks and deeply nested ADTs.
/// Further, private and `doc(hidden)` fields of structs would get leaked
/// since HIR datatypes like the `body` parameter do not contain enough
/// semantic information for this function to be able to hide them –
/// at least not without significant performance overhead.
///
/// Whenever possible, prefer to evaluate the constant first and try to
/// use a different method for pretty-printing. Ideally this function
/// should only ever be used as a fallback.
pub fn rendered_const<'tcx>(tcx: TyCtxt<'tcx>, body: &hir::Body<'_>, def_id: LocalDefId) -> String {
    let value = body.value;

    #[derive(PartialEq, Eq)]
    enum Classification {
        Literal,
        Simple,
        Complex,
    }

    use Classification::*;

    fn classify(expr: &hir::Expr<'_>) -> Classification {
        match &expr.kind {
            hir::ExprKind::Unary(hir::UnOp::Neg, expr) => {
                if matches!(expr.kind, hir::ExprKind::Lit(_)) { Literal } else { Complex }
            }
            hir::ExprKind::Lit(_) => Literal,
            hir::ExprKind::Tup([]) => Simple,
            hir::ExprKind::Block(hir::Block { stmts: [], expr: Some(expr), .. }, _) => {
                if classify(expr) == Complex { Complex } else { Simple }
            }
            // Paths with a self-type or arguments are too “complex” following our measure since
            // they may leak private fields of structs (with feature `adt_const_params`).
            // Consider: `<Self as Trait<{ Struct { private: () } }>>::CONSTANT`.
            // Paths without arguments are definitely harmless though.
            hir::ExprKind::Path(hir::QPath::Resolved(_, hir::Path { segments, .. })) => {
                if segments.iter().all(|segment| segment.args.is_none()) { Simple } else { Complex }
            }
            // FIXME: Claiming that those kinds of QPaths are simple is probably not true if the Ty
            //        contains const arguments. Is there a *concise* way to check for this?
            hir::ExprKind::Path(hir::QPath::TypeRelative(..)) => Simple,
            _ => Complex,
        }
    }

    match classify(value) {
        // For non-macro literals, we avoid invoking the pretty-printer and use the source snippet
        // instead to preserve certain stylistic choices the user likely made for the sake of
        // legibility, like:
        //
        // * hexadecimal notation
        // * underscores
        // * character escapes
        //
        // FIXME: This passes through `-/*spacer*/0` verbatim.
        Literal
            if !value.span.from_expansion()
                && let Ok(snippet) = tcx.sess.source_map().span_to_snippet(value.span) =>
        {
            snippet
        }

        // Otherwise we prefer pretty-printing to get rid of extraneous whitespace, comments and
        // other formatting artifacts.
        Literal | Simple => id_to_string(&tcx, body.id().hir_id),

        // FIXME: Omit the curly braces if the enclosing expression is an array literal
        //        with a repeated element (an `ExprKind::Repeat`) as in such case it
        //        would not actually need any disambiguation.
        Complex => {
            if tcx.def_kind(def_id) == DefKind::AnonConst {
                "{ _ }".to_owned()
            } else {
                "_".to_owned()
            }
        }
    }
}
