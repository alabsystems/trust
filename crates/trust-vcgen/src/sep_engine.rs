// trust_vcgen/sep_engine.rs: Minimal separation logic provenance engine
//
// Combines the symbolic heap (separation_logic.rs) with provenance tracking
// (memory_provenance.rs) into a unified engine for unsafe Rust verification.
// Interprets MIR statements to update heap state and generates VCs for
// 8 unsafe patterns: raw deref read, raw deref write, alloc, dealloc,
// ptr::copy, transmute, offset, and realloc.
//
// Part of #436: Separation logic provenance engine for unsafe Rust verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    BlockId, Formula, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator,
    Ty, VcKind, VerifiableFunction, VerificationCondition,
};

#[cfg(test)]
use crate::separation_logic::SepFormula;
use crate::separation_logic::{PointerPermission, ProvenanceId, SymbolicHeap, SymbolicPointer};

fn generated_sep_var(name: impl AsRef<str>, sort: Sort) -> Formula {
    Formula::Var(crate::separation_logic::generated_symbol(name.as_ref()), sort)
}

// ────────────────────────────────────────────────────────────────────────────
// Step 1: SepEngine struct
// ────────────────────────────────────────────────────────────────────────────

/// Minimal separation logic provenance engine for unsafe Rust verification.
///
/// Combines a [`SymbolicHeap`] (heap cells and provenance tracking) with a
/// forward MIR interpreter that detects 8 unsafe patterns and generates
/// verification conditions. The engine tracks heap state across statements
/// and computes frame conditions for modular reasoning.
///
/// # Design
///
/// The engine walks MIR blocks forward, interpreting each statement and
/// terminator. When it detects an unsafe pattern (raw pointer deref, alloc,
/// dealloc, transmute, etc.), it:
///
/// 1. Snapshots the current heap state (pre-state)
/// 2. Updates the heap according to the operation's semantics
/// 3. Computes the frame (cells unchanged between pre and post)
/// 4. Generates VCs asserting the operation's safety preconditions
///
/// # References
///
/// - Reynolds (2002): Separation logic, a logic for shared mutable data
/// - O'Hearn, Pym (1999): The logic of bunched implications
#[derive(Debug, Clone)]
pub(crate) struct SepEngine {
    /// The symbolic heap tracking cells and pointers.
    heap: SymbolicHeap,
    /// Map from MIR local index to the pointer name used in the heap.
    local_to_ptr: FxHashMap<usize, String>,
    /// Local types used to distinguish raw-pointer derefs from safe ref derefs.
    local_tys: Vec<Ty>,
    /// Local NAMES, so operands resolve to the same SMT variable the rest of the
    /// pipeline uses (`place_to_var_name`): a named local `len` must be `len`,
    /// not `_1`, or guards/defs over `len` won't connect to this VC's operand.
    local_names: Vec<Option<String>>,
    /// VCs accumulated during interpretation.
    vcs: Vec<VerificationCondition>,
    /// Function name for VC attribution.
    func_name: String,
    /// Provenance ids of allocations classified as externally-mutable
    /// (memory-mapped files/shared objects). Uses of these require the captured
    /// length to be re-validated against the live size — see
    /// [`is_external_map_call`] and [`SepEngine::interpret_external_map`].
    external_allocs: Vec<ProvenanceId>,
    /// Statically-known byte sizes for allocations whose size is in the type
    /// (e.g. a `&[u8; N]` fixed array). When a raw slice is built from such a
    /// pointer, the bounds obligation uses the CONCRETE size, so a guard like
    /// `len <= N` discharges it. See [`SepEngine::interpret_address_of`].
    concrete_sizes: FxHashMap<ProvenanceId, i128>,
    /// Symbolic (non-constant) allocation sizes bound to a provenance: e.g. a
    /// memory map's size is its `len` ARGUMENT (`mmap(.., len, ..)` returns a
    /// region of exactly `len` bytes). Lets the backing-invariant ESTABLISH
    /// obligation at `Self { ptr: mmap_result, len }` discharge (`len < len` is
    /// UNSAT) instead of comparing against an unconstrained `size_var`.
    symbolic_sizes: FxHashMap<ProvenanceId, Formula>,
    /// Each tracked pointer's byte OFFSET from its allocation base (0 at the
    /// base, accumulated through `ptr.add`/`offset`). The slice/copy bounds
    /// obligation is `offset + count > size`, NOT `count > size` — so an offset
    /// pointer cannot be unsoundly discharged by a count-only guard, and a
    /// correctly bounded `offset + count <= size` discharges it.
    pointer_offsets: FxHashMap<String, Formula>,
    /// Locals whose value is a known integer constant (`let cap = 64`). Used to
    /// resolve a `Layout::from_size_align(cap, _)` size argument to a literal so
    /// the resulting heap allocation carries a CONCRETE size.
    const_locals: FxHashMap<usize, i128>,
    /// Locals holding a `Layout` whose byte size is statically known, threaded
    /// from `Layout::from_size_align[_unchecked](size, _)` through `unwrap`/
    /// `expect`/moves to the `alloc(layout)` call site. At the allocation this
    /// becomes the provenance's [`concrete_sizes`] entry — turning a guarded
    /// `from_raw_parts(p, len)` over a `Layout`-sized buffer from caught into
    /// PROVABLE (the static-size analog of the dynamic mmap `self.len` class).
    layout_sizes: FxHashMap<usize, i128>,
    /// Declared "backing-length" type invariants for a struct: each
    /// `(ptr_field_index, len_field_index)` asserts that the raw-pointer field
    /// `ptr_field` is valid for `len_field` bytes (e.g. aterm's
    /// `MmapMut { ptr, len }`). This is the relational invariant that lets a
    /// `from_raw_parts(self.ptr.add(start), len)` over a struct field be PROVED.
    /// The invariant is sound only if it is ESTABLISHED at construction — so at
    /// every `Self { ptr, len }` aggregate the engine emits an obligation that
    /// the pointer's allocation is at least `len` bytes (see the Aggregate arm).
    field_backing: Vec<(usize, usize)>,
    /// Locals that hold a load of a struct field `(*base).field` — `local ->
    /// (base_local, field_index)`. Used by the backing-invariant ASSUME: a
    /// `from_raw_parts` over a pointer that traces to a backing pointer field
    /// gets its allocation size modeled as the sibling length field.
    field_loads: FxHashMap<usize, (usize, usize)>,
    /// The named formula for the local that loaded a given `(base, field)` — so
    /// the ASSUME can use the SAME variable the guard/length sees for
    /// `self.len`, letting `start + len <= self.len` discharge the obligation.
    field_load_var: FxHashMap<(usize, usize), Formula>,
    /// When set, a memory-map call also emits a `VcKind::Temporal` carrying the
    /// sound mmap-truncation `StateMachine`, so `ty` model-checks the temporal
    /// hazard (CATCHES it unless a single-writer invariant holds). Batteries-on
    /// by default (`check_sep_unsafe_blocked` enables it unconditionally; it is
    /// an L2-domain VC, kept only at `-Z trust-verify-level=2`); the always-on
    /// `ExternallyMutableAllocationBounds` already catches it via the bounds
    /// path at L0/L1.
    emit_temporal_mmap: bool,
    /// Whether a single-writer invariant is declared for the mapped region (the
    /// backing file is not concurrently truncatable — `map_mut`'s documented
    /// `unsafe` contract). When set, the temporal model disables the `Truncate`
    /// env action, so `ty` PROVES the temporal property instead of catching it.
    temporal_single_writer: bool,
    /// Whether this function's backing struct has an INTERPROCEDURALLY CERTIFIED
    /// backing invariant: every constructor of the struct (across the analyzed
    /// crate) was shown to ESTABLISH `alloc_size >= self.len`, and no field-write
    /// breaks it (see [`crate::backing_cert`]). Only then may the use-site ASSUME
    /// bound the opaque `backing_alloc_size_*` symbol below `self.len` and so
    /// discharge a guarded access — soundly, because the establish licenses it.
    /// OFF by default ⇒ the ASSUME stays fail-closed (CAUGHT, never falsely
    /// proved), which is the sound per-function default.
    backing_certified: bool,
    /// Locals defined by an `AddressOf` whose ONLY use is the operand of a
    /// `PtrMetadata` read — the compiler's `<[T]>::len()` lowering on a `&[T]`/
    /// `&mut [T]`. Such a `&raw const/mut` never dereferences (it only reads the
    /// fat pointer's length metadata word), so it carries NO source-liveness
    /// obligation; emitting one false-refutes safe guarded `&mut [T]` indexing.
    /// Populated by [`metadata_only_addr_of_locals`]; consulted in
    /// [`SepEngine::interpret_address_of`]. Empty ⇒ every addr_of is flagged.
    metadata_only_addr_of: FxHashSet<usize>,
    /// Locals defined by an `AddressOf` of a whole, untracked stack local whose
    /// raw pointer is CONFINED to the defining block and consumed only as a
    /// by-value argument of that block's own `Call` terminator — the
    /// `&mut out`-parameter FFI shape (`waitpid(pid, &mut status, 0)`). Source
    /// liveness holds structurally at every in-frame use of such a pointer, so
    /// the conservative `[unsafe:sep:addr_of]` source-liveness VC is discharged.
    /// Populated by [`call_arg_confined_addr_of_locals`]; consulted in
    /// [`SepEngine::interpret_address_of`]. Empty ⇒ every addr_of is flagged.
    call_arg_confined_addr_of: FxHashSet<usize>,
    /// Provenances produced by an INFALLIBLE, type-aligned box allocator
    /// (`box_new_uninit` / `Box::new`): the global allocator aborts on OOM (never
    /// returns null to safe code) and returns memory aligned to the `Layout`'s
    /// alignment, which equals the boxed type's alignment. A raw deref/write of
    /// such a pointer (before any free) is therefore non-null, points to a valid
    /// allocation, is aligned, and is writable — the [`box_alloc_postcondition`]
    /// facts the deref/write handlers conjoin onto the violation so the solver
    /// discharges null/alloc-validity/alignment/write-permission. SOUND only for
    /// these infallible allocators (a fallible `alloc::alloc` CAN return null, so
    /// it is deliberately NOT recorded here — its null check stays fail-closed).
    box_good_provs: FxHashSet<ProvenanceId>,
    /// Whether the block currently being interpreted is reachable from the entry
    /// (`bb0`) via the IR's normal terminator successors. CLEANUP (unwind) blocks are
    /// NOT reachable this way — rustc's unwind successor edges are dropped at
    /// extraction (`Terminator::Call`/`Drop` keep only `target`; `Resume` is the
    /// unwind sink). A `Drop` in such an unreachable block is unwind cleanup, so it
    /// must NOT free a provenance for the (path-insensitive) normal-path heap analysis
    /// — else a freshly-allocated box, freed by its lower-block-index cleanup `Drop`,
    /// spuriously reports use-after-free at its normal-path initialization write. Set
    /// per block by the driver; consulted in [`SepEngine::interpret_drop`].
    current_block_reachable: bool,
    /// Provenances of stack locals taken by `&x` / `&raw x` that are STACK-GOOD:
    /// the backing local has NO `StorageDead` anywhere in the body AND the
    /// function has NO back-edge (the whole-program gate computed by
    /// [`SepEngine::with_stack_good_gate`]). For such a provenance, a raw deref AT
    /// OFFSET 0 is non-null, in-bounds, points to live memory, and is aligned to
    /// the local's type — the facts [`SepEngine::discharge_stack_good`] conjoins
    /// onto the deref violations so the solver discharges null / in-bounds /
    /// alignment (allocation-validity is dropped, exactly as in box-good).
    ///
    /// SOUND only under the whole-program gate: it never relies on a `StorageDead`
    /// being VISITED before the deref, so it is immune to the index-ordered,
    /// path-insensitive block walk (a loop-carried back-edge `StorageDead` would be
    /// visited late). Any local with a `StorageDead`, or any function with a loop,
    /// falls through to the fail-closed deref VCs.
    stack_good_provs: FxHashSet<ProvenanceId>,
    /// Backing MIR local for each stack-good provenance, so the deref can recover
    /// the local's concrete byte size (in-bounds) and alignment.
    stack_good_local: FxHashMap<ProvenanceId, usize>,
    /// Locals with a `StorageDead` ANYWHERE in the body. A `&x` of such a local is
    /// NOT stack-good (its storage may end before a later deref). Precomputed by
    /// [`SepEngine::with_stack_good_gate`].
    locals_with_storage_dead: FxHashSet<usize>,
    /// Whether the body has a back-edge (a terminator successor with id `<=` the
    /// current block's id — a sound over-approximation of "has a loop"). When true,
    /// NO provenance is stack-good. Precomputed by `with_stack_good_gate`.
    stack_good_has_back_edge: bool,
}

impl SepEngine {
    /// Create a new engine for a given function.
    #[must_use]
    pub(crate) fn new(func_name: &str) -> Self {
        Self {
            heap: SymbolicHeap::new(&crate::separation_logic::generated_symbol("heap")),
            local_to_ptr: FxHashMap::default(),
            local_tys: Vec::new(),
            local_names: Vec::new(),
            vcs: Vec::new(),
            func_name: func_name.to_string(),
            external_allocs: Vec::new(),
            concrete_sizes: FxHashMap::default(),
            symbolic_sizes: FxHashMap::default(),
            pointer_offsets: FxHashMap::default(),
            const_locals: FxHashMap::default(),
            layout_sizes: FxHashMap::default(),
            field_backing: Vec::new(),
            field_loads: FxHashMap::default(),
            field_load_var: FxHashMap::default(),
            emit_temporal_mmap: false,
            temporal_single_writer: false,
            backing_certified: false,
            metadata_only_addr_of: FxHashSet::default(),
            call_arg_confined_addr_of: FxHashSet::default(),
            box_good_provs: FxHashSet::default(),
            current_block_reachable: true,
            stack_good_provs: FxHashSet::default(),
            stack_good_local: FxHashMap::default(),
            locals_with_storage_dead: FxHashSet::default(),
            stack_good_has_back_edge: false,
        }
    }

    /// Precompute the whole-program STACK-GOOD gate from the function body: the set
    /// of locals that have a `StorageDead` anywhere, and whether the body has a
    /// back-edge (loop). A `&x` provenance is recorded stack-good (in
    /// [`SepEngine::interpret_ref`] / [`SepEngine::interpret_address_of`]) ONLY when
    /// the backing local is NOT in `locals_with_storage_dead` AND there is NO
    /// back-edge — a conservative, walk-order-independent liveness/aliasing gate.
    #[must_use]
    pub(crate) fn with_stack_good_gate(mut self, blocks: &[trust_types::BasicBlock]) -> Self {
        let mut storage_dead = FxHashSet::default();
        let mut has_back_edge = false;
        for block in blocks {
            for stmt in &block.stmts {
                if let Statement::StorageDead(local) = stmt {
                    storage_dead.insert(*local);
                }
            }
            // A successor with id <= this block's id is a back-edge (loop). An
            // unreadable (#[non_exhaustive]) terminator is treated as a back-edge —
            // fail closed (no stack-good discharge anywhere in the function).
            match terminator_successors(&block.terminator) {
                Some(succs) if succs.iter().all(|&s| s > block.id.0) => {}
                _ => has_back_edge = true,
            }
        }
        self.locals_with_storage_dead = storage_dead;
        self.stack_good_has_back_edge = has_back_edge;
        self
    }

    /// Declare the set of `AddressOf` destination locals that are pure fat-pointer
    /// metadata reads (consumed only by `PtrMetadata`). See
    /// [`SepEngine::metadata_only_addr_of`] and [`metadata_only_addr_of_locals`].
    #[must_use]
    pub(crate) fn with_metadata_only_addr_of(mut self, locals: FxHashSet<usize>) -> Self {
        self.metadata_only_addr_of = locals;
        self
    }

    /// Declare the set of `AddressOf` destination locals whose raw pointer is
    /// call-arg-confined to its defining block (the `&mut out`-parameter FFI
    /// shape). See [`SepEngine::call_arg_confined_addr_of`] and
    /// [`call_arg_confined_addr_of_locals`].
    #[must_use]
    pub(crate) fn with_call_arg_confined_addr_of(mut self, locals: FxHashSet<usize>) -> Self {
        self.call_arg_confined_addr_of = locals;
        self
    }

    /// Enable emitting the `ty` mmap-truncation temporal obligation at map sites.
    /// `single_writer` declares the no-concurrent-truncation invariant, flipping
    /// the model from caught (truncatable) to provable.
    #[must_use]
    pub(crate) fn with_temporal_mmap(mut self, on: bool, single_writer: bool) -> Self {
        self.emit_temporal_mmap = on;
        self.temporal_single_writer = single_writer;
        self
    }

    /// Declare backing-length invariants `(ptr_field, len_field)` for the struct
    /// whose methods/constructors this function manipulates. See
    /// [`SepEngine::field_backing`].
    #[must_use]
    pub(crate) fn with_field_backing(mut self, backing: Vec<(usize, usize)>) -> Self {
        self.field_backing = backing;
        self
    }

    /// Mark this function's backing struct invariant as interprocedurally
    /// CERTIFIED (see [`SepEngine::backing_certified`]). When set, the backing
    /// ASSUME may license `alloc_size >= self.len`, so a guarded use discharges.
    #[must_use]
    pub(crate) fn with_backing_certified(mut self, certified: bool) -> Self {
        self.backing_certified = certified;
        self
    }

    /// The opaque backing-allocation-size symbol for a backing pointer field,
    /// plus — only when the struct's invariant is interprocedurally CERTIFIED —
    /// the assumption `alloc_size >= self.<len_field>` that a verified establish
    /// licenses. Both the `from_raw_parts` copy-bounds ASSUME and the `.add`
    /// offset ASSUME bound against this SAME opaque symbol, so that without a
    /// certificate every backing obligation is fail-closed (CAUGHT) against an
    /// unknown size — a per-function analysis cannot know the real allocation
    /// size. With a certificate, the returned assumption (conjoined into the
    /// violation formula) lets a guard `offset + len <= self.len` discharge it.
    fn backing_alloc_size(
        &self,
        base: usize,
        ptr_field: usize,
        len_field: usize,
    ) -> (Formula, Option<Formula>) {
        let size = generated_sep_var(format!("backing_alloc_size_{base}_{ptr_field}"), Sort::Int);
        let assumption = if self.backing_certified {
            self.field_load_var
                .get(&(base, len_field))
                .cloned()
                .map(|self_len| Formula::Ge(Box::new(size.clone()), Box::new(self_len)))
        } else {
            None
        };
        (size, assumption)
    }

    /// Resolve an operand to a known integer constant: a literal `Constant`, or
    /// an unprojected local previously assigned an integer constant
    /// (`const_locals`). `None` when the value is not statically known.
    fn operand_const_int(&self, op: &Operand) -> Option<i128> {
        match op {
            Operand::Constant(trust_types::ConstValue::Int(n)) => Some(*n),
            Operand::Constant(trust_types::ConstValue::Uint(n, _)) => i128::try_from(*n).ok(),
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                self.const_locals.get(&p.local).copied()
            }
            _ => None,
        }
    }

    /// The byte offset-from-base of a pointer operand (0 when untracked / at the
    /// base). Used to make slice/copy bounds obligations offset-aware.
    fn operand_offset(&self, op: &Operand) -> Formula {
        operand_local(op)
            .and_then(|local| self.local_to_ptr.get(&local))
            .and_then(|name| self.pointer_offsets.get(name))
            .cloned()
            .unwrap_or(Formula::Int(0))
    }

    #[must_use]
    pub(crate) fn with_local_tys(mut self, local_tys: Vec<Ty>) -> Self {
        self.local_tys = local_tys;
        self
    }

    #[must_use]
    pub(crate) fn with_local_names(mut self, local_names: Vec<Option<String>>) -> Self {
        self.local_names = local_names;
        self
    }

    /// The backing-allocation size of a pointer operand, when the pointer traces
    /// to a tracked concrete allocation: the CONCRETE byte size if known (a fixed
    /// array), else the allocation's symbolic `size_var`. `None` when the pointer
    /// is untracked/unknown (then callers keep the symbolic fail-closed form).
    fn operand_alloc_size(&self, op: &Operand) -> Option<Formula> {
        let local = operand_local(op)?;
        let ptr_name = self.local_to_ptr.get(&local)?;
        let prov = self.heap.pointer(ptr_name).map(|p| p.provenance)?;
        if !prov.is_concrete() {
            return None;
        }
        Some(match self.concrete_sizes.get(&prov) {
            Some(&n) => Formula::Int(n),
            None => match self.symbolic_sizes.get(&prov) {
                Some(f) => f.clone(),
                None => Formula::Var(prov.size_var(), Sort::Int),
            },
        })
    }

    /// Byte stride of one element behind a pointer LOCAL: `size_of(pointee)`.
    /// `None` when the pointee type/size is not modeled.
    fn local_pointee_stride(&self, local: usize) -> Option<i128> {
        self.local_tys.get(local).and_then(|t| t.pointee_ty()).and_then(ty_byte_size)
    }

    /// The element length of a slice/array RECEIVER operand: the concrete array
    /// length when it is in the type (`[T; N]`, possibly behind references), else
    /// a symbolic per-local length variable for a dynamically-sized slice (so a
    /// `i < slice.len()` guard can still discharge the obligation). Used for the
    /// `get_unchecked` bounds obligation.
    fn operand_container_len(&self, op: &Operand) -> Formula {
        if let Some(local) = operand_local(op) {
            let mut ty = self.local_tys.get(local);
            while let Some(Ty::Ref { inner, .. }) = ty {
                ty = Some(inner.as_ref());
            }
            if let Some(Ty::Array { len, .. }) = ty {
                return Formula::Int(i128::from(*len));
            }
            // Dynamic slice: bound by the slice's ELEMENT length. Emit the SAME
            // `{name}__slice_len` symbol that `slice_len_formula` (and hence
            // `s.len()` / `Rvalue::Len`) produces for this receiver, so a dominating
            // `if i < s.len()` guard DISCHARGES the obligation: `_N = Len(s)` is
            // lowered to the fact `_N == s__slice_len`, so the guard `i < _N`
            // becomes `i < s__slice_len`, a direct contradiction with the violation
            // `i >= s__slice_len`. The old `container_len_{local}` symbol was
            // name-disjoint from the guard and could NEVER be discharged (a
            // false-reject of guarded code). Mirrors `container_byte_len`'s slice
            // arm exactly. SOUNDNESS: the symbol is unconstrained absent a guard, so
            // an UNGUARDED `get_unchecked(i)` still yields SAT `i >= len` and fails
            // closed — this only lets a REAL `i < s.len()` guard connect.
            let name = self
                .local_names
                .get(local)
                .and_then(Clone::clone)
                .unwrap_or_else(|| format!("_{local}"));
            return Formula::Var(format!("{name}__slice_len"), Sort::Int);
        }
        generated_sep_var("container_len_unknown", Sort::Int)
    }

    /// Byte length (`size_of_val`) of a slice/array CONTAINER receiver `local`:
    /// `elem_stride * element_count`. Uses the SAME `container_len_{local}` element-count
    /// variable [`operand_container_len`] emits (so a `src.len()` guard connects) and the
    /// concrete `[T; N]` length when present. `None` when the receiver is not a slice/array
    /// or its element size is unmodeled (caller must then fail closed, leaving the
    /// provenance size symbolic — NEVER assume stride 1).
    ///
    /// SOUNDNESS: this is EXACTLY the byte count `<container>.as_ptr()` is valid for AT
    /// OFFSET 0 — the base of the container's backing allocation, guaranteed to hold at
    /// least `size_of_val(X)` bytes (it IS `X`). So binding it as the provenance's
    /// allocation size under-approximates (or equals) the true allocation — never
    /// over-states reachable bytes — hence usable as a sound `size` lower bound.
    fn container_byte_len(&self, local: usize) -> Option<Formula> {
        let mut ty = self.local_tys.get(local)?;
        while let Ty::Ref { inner, .. } = ty {
            ty = inner.as_ref();
        }
        let (elem, count) = match ty {
            Ty::Array { elem, len } => (elem.as_ref(), Formula::Int(i128::from(*len))),
            Ty::Slice { elem } => {
                // Use the SAME `{name}__slice_len` variable `slice_len_formula` (and hence
                // `X.len()` / `Rvalue::Len`) produces for this receiver, so the byte-length
                // binding UNIFIES with the caller's length relation. `local_names` mirrors
                // `place_to_var_name`'s source-name-or-`_{local}` convention.
                let name = self
                    .local_names
                    .get(local)
                    .and_then(Clone::clone)
                    .unwrap_or_else(|| format!("_{local}"));
                (elem.as_ref(), Formula::Var(format!("{name}__slice_len"), Sort::Int))
            }
            _ => return None,
        };
        let stride = ty_byte_size(elem)?;
        Some(scale_to_bytes(stride, count))
    }

    /// Byte stride of one element behind a pointer OPERAND. SOUNDNESS-CRITICAL:
    /// callers that turn an ELEMENT count/offset into a byte extent MUST scale by
    /// this, and MUST fail closed (fall back to the symbolic obligation) when it
    /// is `None` — NEVER assume a stride of 1. `from_raw_parts(p, len)` /
    /// `ptr::copy(.., n)` / `p.add(n)` count `len`/`n` in ELEMENTS of the pointee
    /// (`p.add(n)` advances `n * size_of(T)` bytes), while the backing allocation
    /// size is in BYTES. Comparing an element count directly against a byte size
    /// under-checks by `size_of(T)` — e.g. `from_raw_parts::<u32>(p, 64)` over a
    /// 64-BYTE buffer reads 256 bytes but would compare `64 > 64` (false) and be
    /// unsoundly proved safe. Assuming stride 1 for an unknown pointee would
    /// re-open exactly that hole, so unknown ⇒ fail closed.
    fn operand_pointee_stride(&self, op: &Operand) -> Option<i128> {
        operand_local(op).and_then(|l| self.local_pointee_stride(l))
    }

    /// Resolve a `Copy`/`Move` operand of an unprojected local to the SAME SMT
    /// variable name the rest of the pipeline uses (`place_to_var_name`): the
    /// local's declared name if any, else `_N`. This is what lets a guard/def
    /// over `len` connect to an obligation that reads `len`. Falls back to the
    /// generic operand formula for anything else.
    fn operand_named_formula(&self, op: &Operand) -> Formula {
        if let Operand::Copy(p) | Operand::Move(p) = op
            && p.projections.is_empty()
        {
            let name = self
                .local_names
                .get(p.local)
                .and_then(Clone::clone)
                .unwrap_or_else(|| format!("_{}", p.local));
            return Formula::Var(name, Sort::Int);
        }
        operand_to_formula_simple(op)
    }

    /// Number of accumulated VCs.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn vc_count(&self) -> usize {
        self.vcs.len()
    }

    /// Number of accumulated VCs so far (used to attribute VCs to the block
    /// being interpreted, for guard application).
    #[must_use]
    pub(crate) fn vc_len(&self) -> usize {
        self.vcs.len()
    }

    /// Consume the engine and return accumulated VCs.
    #[must_use]
    pub(crate) fn into_vcs(self) -> Vec<VerificationCondition> {
        self.vcs
    }

    // ────────────────────────────────────────────────────────────────────
    // Step 3: MIR statement interpreter for 8 unsafe patterns
    // ────────────────────────────────────────────────────────────────────

    /// Interpret a MIR statement, updating heap state and emitting VCs.
    pub(crate) fn interpret_statement(&mut self, stmt: &Statement, span: &SourceSpan) {
        if let Statement::Assign { place, rvalue, span: stmt_span } = stmt {
            let sp = if stmt_span.line_start > 0 { stmt_span } else { span };
            self.interpret_assign(place, rvalue, sp);
        }
    }

    /// Interpret a MIR terminator, updating heap state and emitting VCs.
    pub(crate) fn interpret_terminator(&mut self, term: &Terminator) {
        match term {
            // Pattern 3: Allocation via alloc::alloc, Box::new, Vec::with_capacity, etc.
            Terminator::Call { func: callee, args, dest, span, .. } => {
                self.interpret_call(callee, args, dest, span);
            }
            // Pattern 4: Deallocation via Drop
            Terminator::Drop { place, span, .. } => {
                self.interpret_drop(place, span);
            }
            _ => {}
        }
    }

    /// Interpret an assignment statement.
    fn interpret_assign(&mut self, place: &Place, rvalue: &Rvalue, span: &SourceSpan) {
        // Soundness: any write to a local INVALIDATES a previously-tracked
        // integer constant / Layout size for it. Only a fresh constant or layout
        // assignment (in the arms below) re-establishes it. Without this, a local
        // reassigned across paths could keep a STALE, too-large size and then
        // unsoundly discharge a guarded slice. Clearing first, re-inserting only
        // on a known-constant write, keeps the recorded size a sound bound.
        if place.projections.is_empty() {
            self.const_locals.remove(&place.local);
            self.layout_sizes.remove(&place.local);
            // Soundness (backing-invariant ASSUME): a write to a local also
            // INVALIDATES any previously-recorded backing field-load tag for it.
            // A field load `_x = (*self).ptr` tags `_x` as the backing pointer
            // field so a later `from_raw_parts(_x, self.len)` may ASSUME the
            // allocation is `self.len` bytes. If `_x` is then reassigned to an
            // UNRELATED pointer (`_x = move _other`, `_other` into a different
            // allocation), the tag must die — otherwise the assume sizes the new
            // allocation by `self.len`, emitting `0 + len > len` (UNSAT) and
            // FALSELY discharging a genuine out-of-bounds slice. The arms below
            // (field load, copy-propagation, pointer cast, `.add` offset)
            // re-establish the tag on writes that legitimately carry it.
            self.field_loads.remove(&place.local);
            // SAME hazard for the provenance map: a reassignment to an
            // untracked pointer must drop the stale allocation binding.
            self.local_to_ptr.remove(&place.local);
        }
        match rvalue {
            // Pattern 1: Raw pointer deref read — `_x = *ptr`
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                if self.place_has_raw_deref(src) =>
            {
                self.interpret_raw_deref_read(src, span);
            }
            Rvalue::CopyForDeref(src) if self.place_has_raw_deref(src) => {
                self.interpret_raw_deref_read(src, span);
            }

            // Pattern 8: Pointer offset via BinaryOp::Add/Sub on pointer locals
            Rvalue::BinaryOp(trust_types::BinOp::Add | trust_types::BinOp::Sub, lhs_op, rhs_op) => {
                // Check if LHS is a tracked pointer (pointer arithmetic)
                if let Operand::Copy(lhs_place) | Operand::Move(lhs_place) = lhs_op
                    && self.local_to_ptr.contains_key(&lhs_place.local)
                {
                    self.interpret_ptr_offset(place, lhs_place, rhs_op, span);
                }
            }

            // Pattern 7: Transmute / pointer cast.
            Rvalue::Cast(operand, _) => {
                // Transmute VCs are generated by the separation_logic::transmute_vc
                // path. Here we only thread heap tracking: a pointer cast
                // (e.g. `&raw const arr as *const u8`, a `PtrToPtr` cast) preserves
                // provenance, so propagate the source pointer's tracking to the
                // destination. This is what lets a later `from_raw_parts` recover
                // the original allocation's size. The guard `local_to_ptr` already
                // restricts this to pointer sources (an int->ptr cast's source is
                // not a tracked pointer).
                if let Operand::Copy(src) | Operand::Move(src) = operand {
                    if let Some(ptr_name) = self.local_to_ptr.get(&src.local).cloned() {
                        self.local_to_ptr.insert(place.local, ptr_name);
                    }
                    // Carry a backing field-load tag through a pointer cast
                    // (`self.ptr as *const u8` is `_2 = _3 as *const u8`), so the
                    // backing-invariant assume still recognizes the slice pointer.
                    if let Some(&bf) = self.field_loads.get(&src.local) {
                        self.field_loads.insert(place.local, bf);
                    }
                }
            }

            // Pattern 6: AddressOf (&raw const / &raw mut)
            Rvalue::AddressOf(mutable, src_place) => {
                self.interpret_address_of(place, src_place, *mutable, span);
            }

            // Pattern 2: Raw pointer deref write — `*ptr = val`
            // This is captured when the destination place has a Deref projection
            _ if self.place_has_raw_deref(place) => {
                self.interpret_raw_deref_write(place, rvalue, span);
            }

            // Struct construction `Self { ptr, len, .. }`: ESTABLISH each declared
            // backing-length invariant. For `(ptr_field, len_field)`, the
            // pointer's allocation must be at least `len_field` bytes — otherwise
            // a later `from_raw_parts` over that field (which ASSUMES the
            // invariant) would be unsound. Emitting it here is what makes the
            // assume sound: every constructor must prove it.
            Rvalue::Aggregate(trust_types::AggregateKind::Adt { .. }, operands)
                if !self.field_backing.is_empty() =>
            {
                let backings = self.field_backing.clone();
                for (ptr_field, len_field) in backings {
                    let (Some(ptr_op), Some(len_op)) =
                        (operands.get(ptr_field), operands.get(len_field))
                    else {
                        continue;
                    };
                    // Size of the pointer field's allocation (symbolic when the
                    // pointer is not a tracked concrete allocation — then the
                    // obligation stays fail-closed, which is sound).
                    let size = self.operand_alloc_size(ptr_op).unwrap_or_else(|| {
                        generated_sep_var(format!("backing_ptr_size_{}", place.local), Sort::Int)
                    });
                    let len = self.operand_named_formula(len_op);
                    // Violation (prove UNSAT): the allocation is SMALLER than the
                    // length the struct will claim — `size < len`.
                    self.vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe:sep:backing] field #{ptr_field} must be valid for \
                                 field #{len_field} bytes at construction in {}",
                                self.func_name
                            ),
                        },
                        function: self.func_name.clone().into(),
                        location: span.clone(),
                        formula: Formula::Lt(Box::new(size), Box::new(len)),
                        contract_metadata: None,
                    });
                }
            }

            // Ref creation: track derived pointers
            Rvalue::Ref { mutable, place: src_place } => {
                self.interpret_ref(place, src_place, *mutable);
            }

            // Copy/Move: propagate pointer tracking, integer-constant values, and
            // a threaded `Layout` size, so an allocation built from a moved
            // `Layout` (and a guard over a moved `cap`) still connect.
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                if let Some(ptr_name) = self.local_to_ptr.get(&src.local).cloned() {
                    self.local_to_ptr.insert(place.local, ptr_name);
                }
                if place.projections.is_empty() {
                    if let Some(&n) = self.const_locals.get(&src.local) {
                        self.const_locals.insert(place.local, n);
                    }
                    if let Some(&n) = self.layout_sizes.get(&src.local) {
                        self.layout_sizes.insert(place.local, n);
                    }
                    // Field load `_x = (*base).field`: remember which struct field
                    // this local holds (for the backing-invariant ASSUME), and the
                    // SAME variable name the guard/length will see for that field.
                    if let Some(bf) = field_access(src) {
                        self.field_loads.insert(place.local, bf);
                        let named = self.operand_named_formula(&Operand::Copy(place.clone()));
                        self.field_load_var.entry(bf).or_insert(named);
                    } else if let Some(&bf) = self.field_loads.get(&src.local) {
                        // Propagate a field-load tag through a plain copy `_y = _x`.
                        self.field_loads.insert(place.local, bf);
                    }
                }
            }

            // Track integer-constant locals (`let cap = 64`) so a later
            // `Layout::from_size_align(cap, _)` resolves to a concrete size.
            Rvalue::Use(Operand::Constant(cv)) if place.projections.is_empty() => {
                let n = match cv {
                    trust_types::ConstValue::Int(n) => Some(*n),
                    trust_types::ConstValue::Uint(n, _) => i128::try_from(*n).ok(),
                    _ => None,
                };
                if let Some(n) = n {
                    self.const_locals.insert(place.local, n);
                }
            }

            _ => {}
        }
    }

    fn place_has_raw_deref(&self, place: &Place) -> bool {
        let Some(mut ty) = self.local_tys.get(place.local).cloned() else {
            return place.projections.iter().any(|proj| matches!(proj, Projection::Deref));
        };

        for proj in &place.projections {
            match proj {
                Projection::Deref => match ty {
                    Ty::RawPtr { .. } => return true,
                    Ty::Ref { inner, .. } => ty = *inner,
                    _ => return false,
                },
                _ => {
                    let Some(next_ty) = crate::project_ty(ty, proj) else {
                        return false;
                    };
                    ty = next_ty;
                }
            }
        }

        false
    }

    /// Pattern 1: Raw pointer dereference read.
    ///
    /// Generates VCs for: null check, allocation validity, provenance bounds.
    fn interpret_raw_deref_read(&mut self, src: &Place, span: &SourceSpan) {
        let ptr_name = self
            .local_to_ptr
            .get(&src.local)
            .cloned()
            .unwrap_or_else(|| format!("_{}.*", src.local));

        // Generate heap-aware read VCs
        let read_vcs = self.heap.read_vc(&ptr_name, &self.func_name, span);
        let mut vcs = if read_vcs.is_empty() {
            // Pointer not tracked in heap; fall back to deref VCs
            crate::separation_logic::deref_vc(&self.func_name, &ptr_name, span)
        } else {
            read_vcs
        };
        self.discharge_box_good(&ptr_name, &mut vcs);
        self.discharge_stack_good(&ptr_name, src.local, &mut vcs);
        self.vcs.extend(vcs);
    }

    /// Pattern 2: Raw pointer dereference write.
    ///
    /// Generates VCs for: all read checks + write permission + post-write consistency.
    fn interpret_raw_deref_write(&mut self, dest: &Place, rvalue: &Rvalue, span: &SourceSpan) {
        let ptr_name = self
            .local_to_ptr
            .get(&dest.local)
            .cloned()
            .unwrap_or_else(|| format!("_{}.*", dest.local));

        let value_formula = rvalue_to_formula(rvalue);

        // Generate heap-aware write VCs
        let write_vcs = self.heap.write_vc(&ptr_name, &value_formula, &self.func_name, span);
        if write_vcs.is_empty() {
            // Pointer not tracked; fall back to raw_write_vc
            let mut vcs = crate::separation_logic::raw_write_vc(
                &self.func_name,
                &ptr_name,
                &value_formula,
                span,
            );
            self.discharge_box_good(&ptr_name, &mut vcs);
            self.discharge_stack_good(&ptr_name, dest.local, &mut vcs);
            self.vcs.extend(vcs);
        } else {
            let mut write_vcs = write_vcs;
            self.discharge_box_good(&ptr_name, &mut write_vcs);
            self.discharge_stack_good(&ptr_name, dest.local, &mut write_vcs);
            self.vcs.extend(write_vcs);

            // Update heap cell if pointer is tracked
            if let Some(ptr) = self.heap.pointer(&ptr_name) {
                let addr = ptr.addr.clone();
                let prov = ptr.provenance;
                self.heap.write_cell(&format!("cell_{ptr_name}"), addr, value_formula, prov);
            }
        }
    }

    /// If `ptr_name`'s provenance is an INFALLIBLE box allocator
    /// (`box_new_uninit`/`Box::new`) and the allocation has NOT been freed, conjoin
    /// the SINGLE relevant allocator-postcondition fact onto each matching violation,
    /// so the solver finds the same-term contradiction directly.
    ///
    /// Per-VC (NOT one combined `A`) ON PURPOSE: conjoining a multi-conjunct fact set
    /// onto a violation whose contradiction is on a DISJOINT variable (e.g. the
    /// post-write `w != w`) stops the solver short-circuiting — it instead tries to
    /// satisfy the unrelated array/nonlinear conjuncts and DEGRADES (ay LRA "Sat but
    /// unsupported" / array model-validation), spuriously failing an otherwise-clean
    /// VC. Targeting one fact per violation keeps each query a direct contradiction.
    ///
    /// SOUNDNESS: each fact is a genuine allocator guarantee; `fact ∧ violation` UNSAT
    /// = `fact ⟹ ¬violation` (non-vacuous — arithmetic/array atoms, preserved by the
    /// vacuity gate). Only the null / allocation-validity / write-permission violations
    /// are discharged. The post-write VC is left untouched (it is the self-discharging
    /// read-over-write reflexive tautology). The ALIGNMENT VC is left untouched (it
    /// needs the CONCRETE pointee alignment — a symbolic-divisor `ptr % align` fact is
    /// nonlinear and would poison the query; it stays soundly caught). Use-after-free /
    /// permission / bounds VCs are likewise left caught.
    fn discharge_box_good(&self, ptr_name: &str, vcs: &mut Vec<VerificationCondition>) {
        let is_box_good = self
            .heap
            .pointer(ptr_name)
            .map(|p| {
                self.box_good_provs.contains(&p.provenance) && !self.heap.is_freed(p.provenance)
            })
            .unwrap_or(false);
        if !is_box_good {
            return;
        }
        // DROP the allocation-validity check: the box allocation is valid by the
        // infallible allocator's contract (the heap cell is genuinely allocated), so —
        // like the size check — it is moot. We drop rather than discharge it because
        // its violation is an array `Select(heap, ptr) == -1` and trust-mc does NOT
        // congruence-close array reads, so conjoining `Select != -1` would NOT prove
        // (it surfaces a spurious counterexample). Sound: an infallible box allocator
        // never returns a pointer into unallocated memory.
        vcs.retain(|vc| {
            !matches!(&vc.kind, VcKind::Assertion { message } if message.contains("allocation validity"))
        });
        for vc in vcs.iter_mut() {
            let VcKind::Assertion { message } = &vc.kind else {
                continue;
            };
            let fact = if message.contains("null check") {
                // ptr != 0 — the allocator aborts on OOM, never returns null.
                Some(box_alloc_nonnull_fact(ptr_name))
            } else if message.contains("write permission") {
                // writable — freshly allocated memory is exclusively owned.
                Some(generated_sep_var(format!("writable_{ptr_name}"), Sort::Bool))
            } else {
                None
            };
            if let Some(fact) = fact {
                let violation = std::mem::replace(&mut vc.formula, Formula::Bool(true));
                vc.formula = Formula::And(vec![fact, violation]);
            }
        }
    }

    /// Record provenance `prov` (a `&local`/`&raw local` of `backing_local`) as
    /// STACK-GOOD when the whole-program gate permits: the backing local never has
    /// its storage ended AND the function has no back-edge. See
    /// [`SepEngine::stack_good_provs`].
    fn record_stack_good(&mut self, prov: ProvenanceId, backing_local: usize) {
        if self.stack_good_has_back_edge || self.locals_with_storage_dead.contains(&backing_local) {
            return;
        }
        self.stack_good_provs.insert(prov);
        self.stack_good_local.insert(prov, backing_local);
    }

    /// If `ptr_name`'s provenance is STACK-GOOD (a `&local` under the whole-program
    /// gate) AND the deref is at OFFSET 0, conjoin the genuine facts that the
    /// address is non-null, in-bounds, and (when the backing alignment meets the
    /// deref's requirement) aligned onto the matching deref violations, and DROP the
    /// allocation-validity VC (the live local is genuinely allocated; its
    /// `Select(heap,ptr) == -1` array violation is not congruence-closed — the same
    /// reason as [`SepEngine::discharge_box_good`]).
    ///
    /// `deref_local` is the pointer local being dereferenced; its pointee type gives
    /// the REQUIRED alignment, and alignment is discharged only when the backing
    /// local's alignment is `>=` that requirement (both powers of two) — so a
    /// re-cast under-aligned `&x as *const u8 as *const u32` deref stays CAUGHT.
    ///
    /// SOUNDNESS: every conjoined fact is a genuine property of a `&` of a LIVE
    /// local AT OFFSET 0 — a reference is non-null, its address equals the
    /// allocation base within a `size`-byte allocation, and is aligned to the
    /// local's type. The OFFSET-0 gate is essential: an offset pointer (`p.add(i)`)
    /// must NOT receive `ptr == base`, or an out-of-bounds deref would be FALSELY
    /// proved — so it falls through to the fail-closed VCs.
    fn discharge_stack_good(
        &self,
        ptr_name: &str,
        deref_local: usize,
        vcs: &mut Vec<VerificationCondition>,
    ) {
        let Some(prov) = self.heap.pointer(ptr_name).map(|p| p.provenance) else {
            return;
        };
        if !self.stack_good_provs.contains(&prov) || self.heap.is_freed(prov) {
            return;
        }
        // OFFSET-0 ONLY. An offset pointer's address is not the allocation base, so
        // conjoining `ptr == base` there would false-prove an out-of-bounds deref.
        // `None` means no offset was ever accumulated for this pointer (a direct
        // `&x`); any `.add`/`.offset` sets a non-zero offset and disqualifies it.
        if !matches!(self.pointer_offsets.get(ptr_name), None | Some(Formula::Int(0))) {
            return;
        }
        let Some(&backing_local) = self.stack_good_local.get(&prov) else {
            return;
        };
        let Some(size_k) = self.concrete_sizes.get(&prov).copied() else {
            return;
        };
        let backing_align = self.local_tys.get(backing_local).and_then(ty_byte_align);
        let required_align =
            self.local_tys.get(deref_local).and_then(|t| t.pointee_ty()).and_then(ty_byte_align);

        let ptr = generated_sep_var(format!("ptr_{ptr_name}"), Sort::Int);
        let base = Formula::Var(prov.base_var(), Sort::Int);
        let size = Formula::Var(prov.size_var(), Sort::Int);

        // DROP allocation-validity (the live local is allocated; its array-`Select`
        // violation is not congruence-closed — same as box-good).
        vcs.retain(|vc| {
            !matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("allocation validity"))
        });
        for vc in vcs.iter_mut() {
            let VcKind::Assertion { message } = &vc.kind else {
                continue;
            };
            let fact = if message.contains("null check") {
                // A reference / address-of a live local is non-null.
                Some(box_alloc_nonnull_fact(ptr_name))
            } else if message.contains("out-of-bounds") || message.contains("out of bounds") {
                // At offset 0: addr == base, and the allocation is exactly `size_k`
                // bytes — so `base <= addr < base + size_k` holds, refuting the
                // `Not(in_bounds)` violation.
                Some(Formula::And(vec![
                    Formula::Eq(Box::new(ptr.clone()), Box::new(base.clone())),
                    Formula::Eq(Box::new(size.clone()), Box::new(Formula::Int(size_k))),
                ]))
            } else if message.contains("alignment") {
                // Discharge alignment only when the backing local's alignment meets
                // the deref's requirement (both powers of two): the address of a
                // K-aligned local is `required`-aligned when K >= required. Constrain
                // the symbolic `align_` divisor to `required` and assert the address
                // is `required`-aligned, refuting `ptr % align != 0`.
                match (backing_align, required_align) {
                    (Some(k), Some(req)) if req > 0 && k >= req => Some(Formula::And(vec![
                        Formula::Eq(
                            Box::new(generated_sep_var(format!("align_{ptr_name}"), Sort::Int)),
                            Box::new(Formula::Int(req)),
                        ),
                        Formula::Eq(
                            Box::new(Formula::Rem(
                                Box::new(ptr.clone()),
                                Box::new(Formula::Int(req)),
                            )),
                            Box::new(Formula::Int(0)),
                        ),
                    ])),
                    _ => None,
                }
            } else {
                None
            };
            if let Some(fact) = fact {
                let violation = std::mem::replace(&mut vc.formula, Formula::Bool(true));
                vc.formula = Formula::And(vec![fact, violation]);
            }
        }
    }

    /// Pattern 3: Allocation (alloc::alloc, Box::new, Vec::with_capacity, etc.).
    fn interpret_call(&mut self, callee: &str, args: &[Operand], dest: &Place, span: &SourceSpan) {
        let lower = callee.to_lowercase();

        if is_external_map_call(&lower) {
            // Memory map of an externally-mutable region (file/shared object).
            self.interpret_external_map(args, dest, span, callee);
        } else if is_container_as_ptr_call(&lower) {
            // `<[T]>::as_ptr` / `as_mut_ptr` / array `as_ptr`: the returned raw
            // pointer aliases the receiver's buffer, so it has the SAME
            // provenance (and offset). Propagate tracking — otherwise a pointer
            // derived as `buf.as_ptr() as *const T` loses the backing size and a
            // later `from_raw_parts` falls to the symbolic fail-closed path.
            if let Some(recv) = args.first().and_then(operand_local)
                && let Some(ptr_name) = self.local_to_ptr.get(&recv).cloned()
            {
                self.local_to_ptr.insert(dest.local, ptr_name.clone());
                // SOUND provenance-size fact for an OFFSET-0 container `as_ptr()`:
                // `X.as_ptr()` returns a pointer to the BASE of `X`'s backing allocation,
                // whose byte size is exactly `size_of_val(X) = elem_stride * len(X)`. Bind
                // that as the provenance's symbolic allocation size so a
                // `from_raw_parts(p, n)` byte-bounds obligation discharges against `X`'s
                // length instead of the unconstrained `prov.size_var()` fail-closed form.
                // GUARDS: offset-0 receiver only (`byte_length(X)` is the base allocation;
                // an offset pointer reaches fewer bytes — the false-PROVE hazard);
                // `container_byte_len` fails closed on a non-container or unmodeled element
                // size (never stride 1); do NOT clobber a known concrete/symbolic size.
                if matches!(self.pointer_offsets.get(&ptr_name), None | Some(Formula::Int(0)))
                    && let Some(prov) = self.heap.pointer(&ptr_name).map(|p| p.provenance)
                    && prov.is_concrete()
                    && !self.concrete_sizes.contains_key(&prov)
                    && !self.symbolic_sizes.contains_key(&prov)
                    && let Some(byte_len) = self.container_byte_len(recv)
                {
                    self.symbolic_sizes.insert(prov, byte_len);
                }
            }
        } else if is_ptr_cast_call(&lower) {
            // `<*mut T>::cast::<U>()` / `cast_mut` / `cast_const`: a pointee-type
            // cast that PRESERVES the address and provenance, exactly like an `as`
            // pointer cast — only the pointee type changes. The real aterm
            // `map_mut` stores `mmap(...).cast::<u8>()`, so without propagating
            // tracking here the backing pointer's allocation size is LOST at
            // construction and the struct fails to certify (its establish becomes
            // a non-trivial `Lt(symbolic, len)`). Carry the provenance and the
            // backing field-load tag (and thus the byte offset, keyed by the same
            // pointer name) from the receiver — mirrors the `Rvalue::Cast` arm.
            if let Some(recv) = args.first().and_then(operand_local) {
                if let Some(ptr_name) = self.local_to_ptr.get(&recv).cloned() {
                    self.local_to_ptr.insert(dest.local, ptr_name);
                }
                if let Some(&bf) = self.field_loads.get(&recv) {
                    self.field_loads.insert(dest.local, bf);
                }
            }
        } else if is_layout_size_call(&lower) {
            // `Layout::from_size_align[_unchecked](size, align)`: when `size`
            // resolves to a literal, record the layout's concrete byte size so
            // the allocation built from it carries that size.
            if let Some(size_op) = args.first()
                && let Some(n) = self.operand_const_int(size_op)
            {
                self.layout_sizes.insert(dest.local, n);
            }
        } else if is_layout_passthrough_call(&lower) {
            // `Result/Option::unwrap`/`expect` over a tracked `Layout`: thread
            // its size through (no-op for any unwrap whose source is untracked).
            if let Some(src) = args.first().and_then(operand_local)
                && let Some(&n) = self.layout_sizes.get(&src)
            {
                self.layout_sizes.insert(dest.local, n);
            }
            // `Option::unwrap_unchecked` / `Result::unwrap_unchecked` is UB if the
            // receiver is `None`/`Err` — UNLIKE the safe panicking `unwrap`/`expect`,
            // which this arm also matches (for the Layout-threading above) but must
            // NOT flag. "the receiver is `Some`/`Ok`" is an enum-discriminant fact
            // the arithmetic deref/transmute machinery cannot express, so emit a
            // fail-closed Unknown obligation that NAMES the required invariant — a
            // visible proof gap, never a silent pass. Scoped strictly to the
            // `_unchecked` spelling so ordinary `unwrap`/`expect` stay obligation-free.
            if lower.contains("unwrap_unchecked") {
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:unwrap_unchecked] the receiver must be `Some`/`Ok` \
                             before `unwrap_unchecked` in {}",
                            self.func_name,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    // Fail-closed: an unconstrained predicate the solver cannot
                    // prove false, so the obligation stays caught until justified.
                    formula: generated_sep_var(
                        format!("unsafe_unwrap_unchecked_unjustified_{}", dest.local),
                        Sort::Bool,
                    ),
                    contract_metadata: None,
                });
            }
        } else if is_alloc_call(&lower) {
            // Fresh allocation: assign provenance and track pointer
            let prov = self.heap.allocate(&format!("alloc_{}", dest.local));
            let ptr_name = format!("alloc_{}", dest.local);
            self.local_to_ptr.insert(dest.local, ptr_name.clone());

            // An infallible, type-aligned box allocator (`box_new_uninit`/`Box::new`)
            // never returns null and returns aligned memory; record its provenance so
            // a later deref/write of the boxed pointer discharges null/alloc/align/
            // write-permission via the allocator postcondition (see the deref/write
            // handlers + `box_alloc_postcondition`).
            let box_good = is_known_good_box_alloc(&lower);
            if box_good {
                self.box_good_provs.insert(prov);
            }

            // If the allocation was sized by a tracked `Layout` (a constant
            // size), record that CONCRETE size for the provenance — so a guarded
            // `from_raw_parts(p, len)` with `len <= size` PROVES (the static
            // analog of the dynamic mmap `self.len` size class).
            if let Some(layout_op) = args.first()
                && let Some(local) = operand_local(layout_op)
                && let Some(&n) = self.layout_sizes.get(&local)
            {
                self.concrete_sizes.insert(prov, n);
            }

            // VC: allocation may fail (null check on result). For a fallible
            // allocator this is a real fail-closed obligation; for an infallible box
            // allocator the result is non-null by the allocator's abort-on-OOM
            // contract, so conjoin that genuine fact onto the violation, making
            // `ptr != 0 ∧ ptr == 0` UNSAT (proved, non-vacuously — arithmetic atoms).
            let null_violation = Formula::Eq(
                Box::new(generated_sep_var(format!("ptr_{ptr_name}"), Sort::Int)),
                Box::new(Formula::Int(0)),
            );
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:alloc] allocation result null check for {} in {}",
                        callee, self.func_name,
                    ),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                formula: if box_good {
                    Formula::And(vec![box_alloc_nonnull_fact(&ptr_name), null_violation])
                } else {
                    null_violation
                },
                contract_metadata: None,
            });

            // VC: allocation size must be positive. SKIP for an infallible box
            // allocator: its size is the boxed type's compile-time layout size (the
            // allocation already succeeded), so the `size_var` is unconstrained here and
            // `size <= 0` would false-FAIL. A fallible raw alloc keeps the check (its
            // runtime size genuinely must be positive).
            if !box_good {
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:alloc] allocation size check for {} ({})",
                            callee, prov,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    formula: Formula::Le(
                        Box::new(Formula::Var(prov.size_var(), Sort::Int)),
                        Box::new(Formula::Int(0)),
                    ),
                    contract_metadata: None,
                });
            }
        } else if is_dealloc_call(&lower) {
            // Deallocation via explicit dealloc call
            self.interpret_dealloc_call(dest, span, callee);
        } else if is_realloc_call(&lower) {
            // Pattern 8 variant: realloc
            self.interpret_realloc(dest, span, callee);
        } else if is_ptr_offset_call(&lower) {
            // `ptr.add(n)` / `ptr.offset(n)` lower to a CALL (not a BinaryOp), so
            // route it through the offset interpreter to keep the result pointer's
            // provenance and accumulate its byte offset — otherwise a later
            // `from_raw_parts` over the offset pointer loses its tracked size.
            if let (Some(src_op), Some(off_op)) = (args.first(), args.get(1))
                && let Some(src_local) = operand_local(src_op)
            {
                self.interpret_ptr_offset(dest, &Place::local(src_local), off_op, span);
            }
        } else if is_nonzero_new_unchecked_call(&lower) {
            // `NonZero*::new_unchecked(x)` / `NonNull::new_unchecked(p)`: it is UB
            // for the argument to be zero (the niche the `NonZero`/`NonNull`
            // invariant forbids). This precondition IS arithmetic, so MODEL it: the
            // violation is `arg == 0`, dischargeable by a dominating `if x != 0`
            // guard (which the guard-resolution pass conjoins). Unguarded ⇒ the
            // `arg == 0` literal stays SAT ⇒ CAUGHT. The argument is read with the
            // same SMT name the guard sees (`operand_named_formula`) so they connect.
            if let Some(arg) = args.first() {
                let value = self.operand_named_formula(arg);
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:new_unchecked] argument must be non-zero \
                             (the `NonZero`/`NonNull` invariant) in {}",
                            self.func_name,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    // Violation (prove UNSAT): the argument is zero.
                    formula: Formula::Eq(Box::new(value), Box::new(Formula::Int(0))),
                    contract_metadata: None,
                });
            }
        } else if lower.contains("from_u32_unchecked") {
            // `char::from_u32_unchecked(x)`: UB unless `x` is a Unicode scalar value
            // — i.e. `x <= 0x10FFFF` AND `x` is NOT a surrogate (`0xD800..=0xDFFF`).
            // Both halves are arithmetic, so MODEL the disjoint violation. A guard
            // proving the scalar-value range (e.g. `if x < 0xD800`) discharges its
            // conjunct; unguarded ⇒ CAUGHT. Argument read with the guard-visible name.
            if let Some(arg) = args.first() {
                let value = self.operand_named_formula(arg);
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:from_u32_unchecked] argument must be a Unicode \
                             scalar value (<= 0x10FFFF and not a surrogate) in {}",
                            self.func_name,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    // Violation (prove UNSAT): out of range OR in the surrogate gap.
                    formula: Formula::Or(vec![
                        Formula::Gt(Box::new(value.clone()), Box::new(Formula::Int(0x10FFFF))),
                        Formula::And(vec![
                            Formula::Ge(Box::new(value.clone()), Box::new(Formula::Int(0xD800))),
                            Formula::Le(Box::new(value), Box::new(Formula::Int(0xDFFF))),
                        ]),
                    ]),
                    contract_metadata: None,
                });
            }
        } else if lower.contains("set_len") {
            // `Vec::set_len(new_len)` (also `String`/`VecDeque`): the caller asserts
            // `new_len <= capacity` AND that the first `new_len` elements are
            // initialized. MODEL the tractable `new_len <= capacity` half: violation
            // `new_len > capacity_{recv}`, dischargeable by an `if new_len <= cap`
            // guard whose `cap` matches the receiver's symbolic capacity var. The
            // "elements initialized" half is a heap-shape fact the engine cannot
            // express, so it stays folded into the fail-closed capacity var (unguarded
            // ⇒ CAUGHT). `new_len` read with the guard-visible name; receiver keyed by
            // its local so a per-receiver capacity guard connects.
            if let (Some(recv), Some(len_op)) = (args.first().and_then(operand_local), args.get(1))
            {
                let new_len = self.operand_named_formula(len_op);
                let capacity = generated_sep_var(format!("capacity_{recv}"), Sort::Int);
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:set_len] new length must not exceed capacity \
                             (and elements must be initialized) in {}",
                            self.func_name,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    // Violation (prove UNSAT): the new length exceeds capacity.
                    formula: Formula::Gt(Box::new(new_len), Box::new(capacity)),
                    contract_metadata: None,
                });
            }
        } else if let Some((tag, condition)) = unsafe_assertion_op(&lower) {
            // UB-class ops whose safety condition is NOT arithmetic (valid UTF-8,
            // full initialization). The deref/transmute machinery cannot express
            // these, so emit a fail-closed obligation that NAMES the exact
            // required invariant (the agentic-feedback value) — always caught
            // regardless of a `// SAFETY:` comment, dischargeable by `#[trust::skip]`
            // or a future explicit justification. Closes the gap where these
            // slipped through with no specific obligation.
            // The STD `vec!`-machinery `box_assume_init_into_vec_unsafe` is generated
            // ONLY by the `vec!` macro AFTER writing every element into the box, so its
            // `assume_init` is always preceded by a full initialization — it is std's
            // own verified code (a user cannot call this `#[doc(hidden)]` unstable
            // internal directly). Discharge it (like `box_new_uninit`'s postcondition).
            // A user `MaybeUninit::assume_init` is NOT this call, so it stays fail-closed.
            let unjustified =
                generated_sep_var(format!("unsafe_{tag}_unjustified_{}", dest.local), Sort::Bool);
            let formula =
                if tag == "assume_init" && lower.contains("box_assume_init_into_vec_unsafe") {
                    // justified ∧ unjustified ⇒ UNSAT (proved). Sound by the std `vec!`
                    // contract (full write precedes); references the real obligation var, so
                    // it is not vacuous (the `Var` atom is opaque to the vacuity gate).
                    Formula::And(vec![Formula::Not(Box::new(unjustified.clone())), unjustified])
                } else {
                    // Fail-closed: an unconstrained predicate the solver cannot prove
                    // false, so the obligation stays caught until justified.
                    unjustified
                };
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!("[unsafe:sep:{tag}] {condition} in {}", self.func_name),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        } else if is_raw_read_write_call(&lower) {
            // `core::ptr::read(p)` / `write(p, v)` (incl. volatile/unaligned):
            // accessing one element at `p` is UB if it lies outside `p`'s backing
            // allocation. The deref happens INSIDE the std fn, so the Deref-place
            // handling never sees it — this closes that gap. Obligation:
            // `offset + size_of(T) > alloc_size` (concrete when tracked; symbolic
            // fail-closed otherwise, so it is always caught).
            if let Some(ptr_op) = args.first() {
                match (self.operand_alloc_size(ptr_op), self.operand_pointee_stride(ptr_op)) {
                    (Some(size), Some(stride)) => {
                        let offset = self.operand_offset(ptr_op);
                        let extent = Formula::Add(Box::new(offset), Box::new(Formula::Int(stride)));
                        self.vcs.push(VerificationCondition {
                            kind: VcKind::CopyBoundsViolation {
                                callee: callee.to_string(),
                                direction: "src".to_string(),
                                detail: format!(
                                    "raw read/write may access past the backing allocation in {}",
                                    self.func_name
                                ),
                            },
                            function: self.func_name.clone().into(),
                            location: span.clone(),
                            formula: Formula::Gt(Box::new(extent), Box::new(size)),
                            contract_metadata: None,
                        });
                    }
                    _ => {
                        // Untracked pointer: fail-closed symbolic obligation.
                        let vcs = crate::separation_logic::unsafe_fn_call_sep_vc(
                            &self.func_name,
                            callee,
                            span,
                        );
                        self.vcs.extend(vcs);
                    }
                }
            }
        } else if is_unchecked_index_call(&lower) {
            // `slice.get_unchecked(i)` / `get_unchecked_mut(i)`: the language
            // inserts NO bounds check (it is UB if `i >= len`), so Trust emits the
            // obligation that the index is in bounds. Fail-closed by default; a
            // guard `if i < len { ... }` discharges it. Closes an unsafe-op
            // coverage gap — previously this UB-class op produced no obligation.
            if let (Some(recv), Some(idx_op)) = (args.first(), args.get(1)) {
                let len = self.operand_container_len(recv);
                let index = self.operand_named_formula(idx_op);
                self.vcs.push(VerificationCondition {
                    kind: VcKind::IndexOutOfBounds,
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    // Violation (prove UNSAT): index past the container length.
                    formula: Formula::Ge(Box::new(index), Box::new(len)),
                    contract_metadata: None,
                });
            }
        } else if lower.contains("ptr::copy") || lower.contains("ptr::copy_nonoverlapping") {
            // Pattern 5: ptr::copy / ptr::copy_nonoverlapping
            self.interpret_ptr_copy(args, dest, span, callee);
        } else if lower.contains("from_raw_parts")
            && args
                .first()
                .zip(args.get(1))
                .is_some_and(|(p, l)| self.try_backing_from_raw_parts(p, l, callee, span))
        {
            // Handled by the backing-invariant ASSUME (size modeled as the
            // sibling length field) — see try_backing_from_raw_parts.
        } else if lower.contains("from_raw_parts") {
            // slice::from_raw_parts(ptr, len): the slice must not claim more than
            // its backing allocation holds.
            //
            // When the pointer argument (args[0]) traces to an allocation this
            // engine tracks, anchor the obligation to that allocation's REAL
            // size variable (`prov.size_var()`) and the REAL `len` operand
            // (args[1]) — so a surrounding guard like `if start + len <= cap`
            // can discharge it (this is the wiring the guard-resolution pass
            // needs). Otherwise fall back to the shared builder's symbolic
            // fail-closed obligation.
            let from_args = (|| {
                let ptr_op = args.first()?;
                let len_op = args.get(1)?;
                let ptr_local = operand_local(ptr_op)?;
                let ptr_name = self.local_to_ptr.get(&ptr_local)?;
                let prov = self.heap.pointer(ptr_name).map(|p| p.provenance)?;
                if !prov.is_concrete() {
                    return None;
                }
                // SOUNDNESS: `len` is in ELEMENTS but `size` is in BYTES, so the
                // obligation must compare `stride * len` (bytes) against `size`.
                // An unknown stride must fail closed (`?` → symbolic fallback),
                // never assume 1 — see `operand_pointee_stride`.
                let stride = self.operand_pointee_stride(ptr_op)?;
                let len = scale_to_bytes(stride, self.operand_named_formula(len_op));
                // Prefer the CONCRETE size when the allocation's size is in the
                // type (a fixed array): then `len > N` is dischargeable by a
                // `len <= N` guard. Else prefer a recorded SYMBOLIC size (e.g. the
                // offset-0 `X.as_ptr()` byte-length bound `elem_stride * len(X)`), so a
                // `from_raw_parts(X.as_ptr(), n)` whose `n` relates to `len(X)` discharges.
                // Otherwise the unconstrained symbolic size variable (fail-closed). Same
                // resolution order as `operand_alloc_size`.
                let size = match self.concrete_sizes.get(&prov) {
                    Some(&n) => Formula::Int(n),
                    None => match self.symbolic_sizes.get(&prov) {
                        Some(f) => f.clone(),
                        None => Formula::Var(prov.size_var(), Sort::Int),
                    },
                };
                // Offset-aware: the slice spans `[ptr+offset, ptr+offset+len)`,
                // so the in-bounds condition is `offset + len <= size`. Using
                // `offset + len` (not just `len`) keeps an offset pointer from
                // being unsoundly discharged by a `len`-only guard. `offset` is
                // already in BYTES (scaled at the `.add` in interpret_ptr_offset),
                // matching the byte-scaled `len` and byte `size`.
                let offset = self.operand_offset(ptr_op);
                let extent = Formula::Add(Box::new(offset), Box::new(len));
                // Violation (prove UNSAT): offset + len > backing allocation size.
                self.vcs.push(VerificationCondition {
                    kind: VcKind::CopyBoundsViolation {
                        callee: callee.to_string(),
                        direction: "src".to_string(),
                        detail: format!(
                            "slice length may exceed the backing allocation in {}",
                            self.func_name
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    formula: Formula::Gt(Box::new(extent), Box::new(size)),
                    contract_metadata: None,
                });
                Some(())
            })();
            if from_args.is_none() {
                // Untracked pointer: keep the symbolic fail-closed obligation.
                let vcs =
                    crate::separation_logic::unsafe_fn_call_sep_vc(&self.func_name, callee, span);
                self.vcs.extend(vcs);
            }
        } else if lower.contains("mem::transmute") {
            // Pattern 7: transmute via call
            let vcs = crate::separation_logic::transmute_vc(&self.func_name, "Src", "Dst", span);
            self.vcs.extend(vcs);
        }
    }

    /// Backing-invariant ASSUME for `from_raw_parts(ptr, len)`: when the pointer
    /// traces to a backing pointer field `self.<ptr_field>` (possibly via
    /// `.add(start)`), model its allocation size as the sibling length field
    /// `self.<len_field>` — the relational invariant established at construction.
    /// Emits `offset + stride*len > self.len_field`; a guard `start + len <=
    /// self.len` then discharges it (and `as_slice`, whose `len` argument IS
    /// `self.len`, discharges trivially since `self.len > self.len` is UNSAT).
    /// Returns `true` iff it applied. SOUND because every constructor must prove
    /// the establish obligation (see the `Aggregate` arm); this is its dual.
    fn try_backing_from_raw_parts(
        &mut self,
        ptr_op: &Operand,
        len_op: &Operand,
        callee: &str,
        span: &SourceSpan,
    ) -> bool {
        if self.field_backing.is_empty() {
            return false;
        }
        let Some(ptr_local) = operand_local(ptr_op) else { return false };
        let Some(&(base, ptr_field)) = self.field_loads.get(&ptr_local) else { return false };
        let Some((_, len_field)) =
            self.field_backing.iter().copied().find(|(pf, _)| *pf == ptr_field)
        else {
            return false;
        };
        // SOUNDNESS: the backing pointer field's REAL allocation size is UNKNOWN
        // to this (strictly per-function) analysis. Modeling it as the `self.len`
        // field would make `as_slice` (`from_raw_parts(self.ptr, self.len)`) emit
        // `len > len` (UNSAT) and FALSELY discharge — nothing in a single function
        // verifies the cross-function invariant `alloc_size >= self.len` (the
        // ESTABLISH obligation lives in the constructor, a different function).
        // So bound against a DISTINCT opaque allocation-size symbol. The
        // assumption `alloc_size >= self.len` is supplied ONLY when the struct's
        // invariant is interprocedurally CERTIFIED (every constructor establishes
        // it — see `backing_alloc_size` / `crate::backing_cert`); otherwise the
        // obligation is fail-closed (CAUGHT). It still NAMES the invariant for
        // actionable guidance.
        let (size, assumption) = self.backing_alloc_size(base, ptr_field, len_field);
        // Unknown pointee stride must fail closed, never assume 1.
        let Some(stride) = self.operand_pointee_stride(ptr_op) else { return false };
        let len = scale_to_bytes(stride, self.operand_named_formula(len_op));
        let offset = self.operand_offset(ptr_op);
        let extent = Formula::Add(Box::new(offset), Box::new(len));
        // Violation (prove UNSAT): offset + len > the backing allocation size. A
        // certificate conjoins `alloc_size >= self.len`, so a guarded access
        // (`offset + len <= self.len`) discharges it; without one it stays open.
        let violation = Formula::Gt(Box::new(extent), Box::new(size));
        let formula = match assumption {
            Some(a) => Formula::And(vec![a, violation]),
            None => violation,
        };
        self.vcs.push(VerificationCondition {
            kind: VcKind::CopyBoundsViolation {
                callee: callee.to_string(),
                direction: "src".to_string(),
                detail: format!(
                    "slice length may exceed the backing field (invariant `field #{ptr_field} \
                     valid for field #{len_field} bytes`) in {}",
                    self.func_name
                ),
            },
            function: self.func_name.clone().into(),
            location: span.clone(),
            formula,
            contract_metadata: None,
        });
        true
    }

    /// A memory-mapping call (`mmap`, `MmapMut::map_mut`, …) over an
    /// externally-mutable region. The mapped length is the *current* size of an
    /// external object (typically a file) that another process can shrink. The
    /// captured length is therefore not a stable bound: a later access must
    /// re-validate it against the live size, or a truncation leaves the mapping
    /// pointing past the file's end → SIGBUS / out-of-bounds read.
    ///
    /// In addition to the usual fresh-allocation bookkeeping (provenance +
    /// null-on-failure), this records the provenance as externally-mutable and
    /// emits an [`VcKind::ExternallyMutableAllocationBounds`] obligation.
    fn interpret_external_map(
        &mut self,
        args: &[Operand],
        dest: &Place,
        span: &SourceSpan,
        callee: &str,
    ) {
        let prov = self.heap.allocate(&format!("map_{}", dest.local));
        let ptr_name = format!("map_{}", dest.local);
        self.local_to_ptr.insert(dest.local, ptr_name.clone());
        self.external_allocs.push(prov);

        // Bind the mapping's allocation size to its `len` argument. `libc::mmap`
        // is `mmap(addr, len, prot, flags, fd, offset)`, so `len` is args[1]; a
        // `memmap2`-style `map_mut(file)` carries no explicit len here and is
        // left symbolic. Binding `size(map) == len` lets a struct that stores
        // this pointer with that same `len` PROVE its backing-length invariant
        // at construction (`len < len` is UNSAT).
        // SOUNDNESS: bind the size to `len` ONLY for the verified `libc::mmap(addr,
        // len, prot, flags, fd, offset)` free-fn shape — 6 args, byte-len at
        // args[1]. A `memmap2`-style METHOD `MmapMut::map_mut(self, ..)` has the
        // receiver at args[0] and NO byte-len at args[1]; binding there would bind
        // the size to an unrelated operand and FALSELY discharge a construction
        // establish as `n < n` (UNSAT). Anything else leaves the size symbolic.
        if args.len() >= 6 {
            self.symbolic_sizes.insert(prov, self.operand_named_formula(&args[1]));
        }

        // VC: the map call may fail (null/err result).
        self.vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[unsafe:sep:map] map result validity check for {} in {}",
                    callee, self.func_name,
                ),
            },
            function: self.func_name.clone().into(),
            location: span.clone(),
            formula: Formula::Eq(
                Box::new(generated_sep_var(format!("ptr_{ptr_name}"), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        });

        // Obligation: the length captured at map time must not exceed the live
        // backing size at use. Violation (must be proven UNSAT):
        //   mapped_len > live_size.
        //
        // The mapped length reuses this allocation's tracked size variable
        // (`prov.size_var()`) — the same one interpret_ptr_offset reasons about
        // for offsets into this provenance — so downstream obligations over the
        // mapping share the variable instead of an isolated free var. The live
        // size is the external quantity that a truncation can shrink below it.
        let mapped_len = Formula::Var(prov.size_var(), Sort::Int);
        let live_size = generated_sep_var(format!("{ptr_name}_live_size"), Sort::Int);
        self.vcs.push(VerificationCondition {
            kind: VcKind::ExternallyMutableAllocationBounds {
                allocation_kind: "mmap_file".into(),
                live_size: format!("{ptr_name}_live_size"),
                detail: format!(
                    "memory map from `{callee}` in {}: re-validate the mapped length against the \
                     live backing size before each access (a concurrent truncation makes the \
                     captured length unsound ⇒ SIGBUS / out-of-bounds read)",
                    self.func_name,
                ),
            },
            function: self.func_name.clone().into(),
            location: span.clone(),
            formula: Formula::Gt(Box::new(mapped_len), Box::new(live_size)),
            contract_metadata: None,
        });

        // Opt-in: also model the temporal hazard for `ty`. The `Truncate` env
        // action makes an access-while-stale reachable unless a single-writer
        // invariant holds, so `ty` CATCHES it with the
        // `Mapped → truncate → stale_access` trace. Re-validation is deliberately
        // NOT modeled as a fix (TOCTOU).
        //
        // SOUNDNESS: `#[trust::single_writer]` is DECLARED, never verified — the
        // compiler sets it from a bare `item_has_trust_attr` presence test. It is
        // therefore passed as `SingleWriterEvidence::Declared`, which does NOT
        // disable `Truncate`. Previously this site forwarded the raw bool, so the
        // attribute deleted the bad state from the model outright and a complete
        // exploration of the reduced model was graded `AssuranceLevel::Sound` —
        // an unverified caller promise laundered into a proof. The declaration is
        // a real obligation ON THE CALLER (it is exactly what `map_mut`'s
        // `unsafe` contract asks for); it is not a discharged one. When a checked
        // single-writer proof exists it should pass `Verified` here, and that is
        // the ONLY thing that may re-enable the reduction.
        if self.emit_temporal_mmap {
            let single_writer_evidence = if self.temporal_single_writer {
                trust_types::SingleWriterEvidence::Declared
            } else {
                trust_types::SingleWriterEvidence::None
            };
            self.vcs.push(VerificationCondition {
                kind: VcKind::Temporal {
                    property: "AG !bad".into(),
                    machine: Some(trust_types::StateMachineMetadata::mmap_temporal_model(
                        single_writer_evidence,
                    )),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                // Non-constant placeholder: the real verdict is ty's model-check of
                // the carried machine, not this formula. A constant (`Bool(true)`)
                // would be discharged by the constant-folder backend before ty is
                // consulted, so use a fresh symbolic var the folder returns Unknown
                // for — routing the VC to ty (the only backend that claims the
                // L2-domain Temporal kind).
                formula: generated_sep_var(
                    format!("mmap_temporal_safe_{}", dest.local),
                    Sort::Bool,
                ),
                contract_metadata: None,
            });
        }
    }

    /// Pattern 4: Deallocation via Drop terminator.
    fn interpret_drop(&mut self, place: &Place, span: &SourceSpan) {
        // A `Drop` in a CLEANUP (unwind) block — unreachable from `bb0` via the IR's
        // normal `target` edges — is unwind cleanup, not a normal-path free. Skipping
        // it for the path-insensitive heap analysis is SOUND (the unwind path is the
        // function already panicking; its frees don't precede a normal-path access) and
        // fixes the spurious use-after-free at a box's initialization write (the box's
        // lower-block-index cleanup `Drop` would otherwise free it first). A genuine
        // normal-path drop is in a REACHABLE block, so it still frees and a real
        // use-after-free / double-free is still caught.
        if !self.current_block_reachable {
            return;
        }
        if let Some(ptr_name) = self.local_to_ptr.get(&place.local).cloned()
            && let Some(ptr) = self.heap.pointer(&ptr_name)
        {
            let prov = ptr.provenance;

            // VC: double-free check
            if self.heap.is_freed(prov) {
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:free] double-free of `{ptr_name}` ({prov}) in {}",
                            self.func_name,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    formula: Formula::Bool(true), // definite violation
                    contract_metadata: None,
                });
            }

            self.heap.free(prov);
        }
    }

    /// Deallocation via explicit dealloc::dealloc call.
    fn interpret_dealloc_call(&mut self, dest: &Place, span: &SourceSpan, callee: &str) {
        if let Some(ptr_name) = self.local_to_ptr.get(&dest.local).cloned()
            && let Some(ptr) = self.heap.pointer(&ptr_name)
        {
            let prov = ptr.provenance;
            if self.heap.is_freed(prov) {
                self.vcs.push(VerificationCondition {
                    kind: VcKind::Assertion {
                        message: format!(
                            "[unsafe:sep:free] double-free via `{callee}` of `{ptr_name}` in {}",
                            self.func_name,
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                });
            }
            self.heap.free(prov);
        }
    }

    /// Pattern 5: ptr::copy / ptr::copy_nonoverlapping.
    ///
    /// VCs: source readable, destination writable, non-overlapping if nonoverlapping variant.
    fn interpret_ptr_copy(
        &mut self,
        args: &[Operand],
        _dest: &Place,
        span: &SourceSpan,
        callee: &str,
    ) {
        let src_name = "copy_src";
        let dst_name = "copy_dst";

        // When the real call arguments are available and the src/dst pointers
        // trace to tracked allocations, emit the bounds obligation against the
        // REAL count operand and the allocation's (concrete-when-known) size:
        // `count > size` — dischargeable by a `count <= size` guard, exactly like
        // the from_raw_parts case. `copy[_nonoverlapping](src, dst, count)`.
        let any_tracked = args.first().and_then(|op| self.operand_alloc_size(op)).is_some()
            || args.get(1).and_then(|op| self.operand_alloc_size(op)).is_some();
        // SOUNDNESS: `count` is in ELEMENTS, allocation sizes in BYTES — scale by
        // the pointee stride (same for src and dst). An unknown stride fails the
        // `if let` and drops to the symbolic fail-closed obligations below, rather
        // than under-checking by assuming stride 1.
        let stride = args
            .first()
            .and_then(|op| self.operand_pointee_stride(op))
            .or_else(|| args.get(1).and_then(|op| self.operand_pointee_stride(op)));
        if let (true, Some(stride), Some(src_op), Some(dst_op), Some(cnt_op)) =
            (any_tracked, stride, args.first(), args.get(1), args.get(2))
        {
            let count = scale_to_bytes(stride, self.operand_named_formula(cnt_op));
            for (side, op) in [("src", src_op), ("dst", dst_op)] {
                // SOUND: emit a bounds obligation for EVERY side. A tracked side
                // gets the dischargeable `count > size`; an untracked side keeps
                // a fail-closed symbolic obligation (`count > <side>_size` over a
                // free var) so its bounds are never silently dropped.
                let size = self
                    .operand_alloc_size(op)
                    .unwrap_or_else(|| generated_sep_var(format!("copy_{side}_size"), Sort::Int));
                // Offset-aware: the copy touches `[ptr+offset, ptr+offset+count)`.
                let offset = self.operand_offset(op);
                let extent = Formula::Add(Box::new(offset), Box::new(count.clone()));
                self.vcs.push(VerificationCondition {
                    kind: VcKind::CopyBoundsViolation {
                        callee: callee.to_string(),
                        direction: side.to_string(),
                        detail: format!(
                            "copy count may exceed the {side} allocation in {}",
                            self.func_name
                        ),
                    },
                    function: self.func_name.clone().into(),
                    location: span.clone(),
                    // Violation (prove UNSAT): offset + count > backing size.
                    formula: Formula::Gt(Box::new(extent), Box::new(size)),
                    contract_metadata: None,
                });
            }
            {
                // Non-overlapping check (for the _nonoverlapping variant) still
                // applies; emit it with the real count, then return.
                if callee.to_lowercase().contains("nonoverlapping") {
                    let src_ptr = generated_sep_var(format!("ptr_{src_name}"), Sort::Int);
                    let dst_ptr = generated_sep_var(format!("ptr_{dst_name}"), Sort::Int);
                    self.vcs.push(VerificationCondition {
                        kind: VcKind::Assertion {
                            message: format!(
                                "[unsafe:sep:copy] overlap check for {} in {}",
                                callee, self.func_name,
                            ),
                        },
                        function: self.func_name.clone().into(),
                        location: span.clone(),
                        formula: Formula::And(vec![
                            Formula::Lt(
                                Box::new(src_ptr.clone()),
                                Box::new(Formula::Add(
                                    Box::new(dst_ptr.clone()),
                                    Box::new(count.clone()),
                                )),
                            ),
                            Formula::Lt(
                                Box::new(dst_ptr),
                                Box::new(Formula::Add(Box::new(src_ptr), Box::new(count))),
                            ),
                        ]),
                        contract_metadata: None,
                    });
                }
                return;
            }
        }

        // Source must be readable
        let read_vcs = crate::separation_logic::deref_vc(&self.func_name, src_name, span);
        self.vcs.extend(read_vcs);

        // Destination must be writable
        let value = generated_sep_var("copy_value", Sort::Int);
        let write_vcs =
            crate::separation_logic::raw_write_vc(&self.func_name, dst_name, &value, span);
        self.vcs.extend(write_vcs);

        // Allocation-bounds check (applies to BOTH `ptr::copy` and the
        // `_nonoverlapping` variant): copying `count` elements must stay within
        // the source allocation (read) and the destination allocation (write).
        // The language inserts no bounds check here, so we make it an obligation.
        // Violation (must be proven UNSAT):
        //   src_ptr + count > src_base + src_size   (read past source), or
        //   dst_ptr + count > dst_base + dst_size   (write past destination).
        //
        // Like the existing deref/transmute sep VCs, these use symbolic vars for
        // the copy operands and so are FAIL-CLOSED markers: they correctly flag
        // "this raw count is unproven" and stay SAT until a downstream points-to
        // fact ties `*_base`/`*_size` to a concrete tracked allocation. They are
        // not (yet) solver-discharged bounds on their own.
        let count = generated_sep_var("copy_count", Sort::Int);
        for (side, name) in [("src", src_name), ("dst", dst_name)] {
            let ptr = generated_sep_var(format!("ptr_{name}"), Sort::Int);
            let base = generated_sep_var(format!("{name}_base"), Sort::Int);
            let size = generated_sep_var(format!("{name}_size"), Sort::Int);
            self.vcs.push(VerificationCondition {
                kind: VcKind::CopyBoundsViolation {
                    callee: callee.to_string(),
                    direction: side.to_string(),
                    detail: format!(
                        "copy of `copy_count` elements may exceed the {side} allocation in {}",
                        self.func_name,
                    ),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                // ptr + count > base + size
                formula: Formula::Gt(
                    Box::new(Formula::Add(Box::new(ptr), Box::new(count.clone()))),
                    Box::new(Formula::Add(Box::new(base), Box::new(size))),
                ),
                contract_metadata: None,
            });
        }

        // Non-overlapping check for copy_nonoverlapping
        if callee.to_lowercase().contains("nonoverlapping") {
            let src_ptr = generated_sep_var(format!("ptr_{src_name}"), Sort::Int);
            let dst_ptr = generated_sep_var(format!("ptr_{dst_name}"), Sort::Int);
            let count = generated_sep_var("copy_count", Sort::Int);

            // Overlap: src < dst + count AND dst < src + count
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:copy] overlap check for {} in {}",
                        callee, self.func_name,
                    ),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                formula: Formula::And(vec![
                    Formula::Lt(
                        Box::new(src_ptr.clone()),
                        Box::new(Formula::Add(Box::new(dst_ptr.clone()), Box::new(count.clone()))),
                    ),
                    Formula::Lt(
                        Box::new(dst_ptr),
                        Box::new(Formula::Add(Box::new(src_ptr), Box::new(count))),
                    ),
                ]),
                contract_metadata: None,
            });
        }
    }

    /// Pattern 6: AddressOf (&raw const / &raw mut).
    fn interpret_address_of(
        &mut self,
        dest: &Place,
        src_place: &Place,
        mutable: bool,
        span: &SourceSpan,
    ) {
        let ptr_name = format!("raw_{}", dest.local);
        let permission =
            if mutable { PointerPermission::ReadWrite } else { PointerPermission::ReadOnly };

        // If source is tracked, derive provenance; otherwise create fresh.
        let prov = if let Some(src_name) = self.local_to_ptr.get(&src_place.local) {
            self.heap.pointer(src_name).map(|p| p.provenance).unwrap_or(ProvenanceId::UNKNOWN)
        } else if let Some(size) = self.local_tys.get(src_place.local).and_then(ty_byte_size) {
            // Taking a raw pointer to a value whose size is in the type (e.g. a
            // fixed array `[u8; N]`): record a CONCRETE allocation so a later
            // `from_raw_parts` bounds obligation can be discharged by a guard.
            let p = self.heap.allocate(&format!("sized_{}", src_place.local));
            self.concrete_sizes.insert(p, size);
            self.record_stack_good(p, src_place.local);
            p
        } else {
            ProvenanceId::UNKNOWN
        };

        let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
        self.heap.track_pointer(ptr);
        // A raw pointer taken directly at a value is at offset 0 of its allocation.
        self.pointer_offsets.insert(ptr_name.clone(), Formula::Int(0));
        self.local_to_ptr.insert(dest.local, ptr_name);

        // A pure metadata read (`_p = &raw const/mut *slice; _ = PtrMetadata(_p)`,
        // the `<[T]>::len()` lowering) never dereferences `_p` — it only reads the
        // fat pointer's length word, which is part of the pointer VALUE, not the
        // pointee allocation. So no source-liveness obligation is owed. Skipping it
        // is SOUND (the local was disqualified if it appears in any deref/store/
        // call/return position) and necessary: emitting it false-refutes the
        // ubiquitous guarded `&mut [T]` index `if i < dst.len() { dst[i] = .. }`.
        if self.metadata_only_addr_of.contains(&dest.local) {
            return;
        }

        // The `&mut out`-parameter FFI shape (`waitpid(pid, &mut status, 0)`):
        // the raw pointer of a whole, UNTRACKED stack local is confined to its
        // defining block and consumed only as a by-value argument of that
        // block's own call terminator, with no `StorageDead` of the source in
        // between — so the source's storage is provably live at every in-frame
        // use of the pointer and the conservative source-liveness VC below is
        // structurally discharged (see `call_arg_confined_addr_of_locals` for
        // the fail-closed confinement conditions). The untracked-source guard
        // keeps this away from the inherited-provenance hazard documented
        // above: a `&raw` of a TRACKED/DERIVED pointer keeps its obligation.
        if self.call_arg_confined_addr_of.contains(&dest.local)
            && ((src_place.projections.is_empty()
                && !self.local_to_ptr.contains_key(&src_place.local))
                // The single-level REBORROW shape the recognizer admits
                // (`_r = &mut local; _p = &raw mut (*_r)` — the `poll(&mut
                // pfd, ..)` lowering; see `call_arg_confined_addr_of_locals`):
                // membership already encodes the recognizer's whole-body
                // confinement walk + the UNDERLYING local's StorageDead scan.
                // `_r` being pointer-tracked is inherent to the shape (it IS a
                // reference to live in-frame storage), not the
                // inherited-provenance hazard documented below — that hazard
                // is `&raw` OF a pointer variable (whose own storage can end),
                // whereas here the liveness subject is the reborrowed-to
                // stack local the recognizer scanned.
                || src_place.projections.as_slice() == [Projection::Deref])
        {
            return;
        }

        // SOUNDNESS: do NOT suppress the source-liveness VC merely because the
        // provenance is stack-good. The stack-good gate is recorded for the
        // backing local of a `&value` (it certifies that backing local never has
        // its storage ended), but a `&raw const/mut` of a TRACKED/DERIVED pointer
        // (the `local_to_ptr` branch above) inherits that same provenance from a
        // TRANSITIVE original — so the source here is the inner pointer, whose own
        // storage CAN end (`StorageDead`) independently of the original stack slot.
        // Suppressing on inherited stack-goodness would discharge the source-
        // liveness obligation for a dangling raw pointer (`q = &raw const p` where
        // `p` later `StorageDead`s): a false-prove of safety for a use of a dead
        // pointer. The source-liveness obligation is conservative (`Bool(true)`,
        // always CAUGHT) and cheap; emit it unconditionally for every non-metadata
        // addr_of, exactly as the engine did before the raw-pointer feature.
        // (The legitimate concrete-allocation tracking above — `sized_N` /
        // `concrete_sizes` for a later `from_raw_parts` bounds discharge — is
        // preserved; only the over-broad VC suppression is removed.)

        // VC: source liveness
        let vcs = crate::separation_logic::address_of_sep_vc(
            &self.func_name,
            &format!("_{}", src_place.local),
            mutable,
            span,
        );
        self.vcs.extend(vcs);
    }

    /// Pattern 8: Pointer offset (ptr.add, ptr.offset, ptr + n).
    fn interpret_ptr_offset(
        &mut self,
        dest: &Place,
        src_place: &Place,
        offset_op: &Operand,
        span: &SourceSpan,
    ) {
        let src_name = self
            .local_to_ptr
            .get(&src_place.local)
            .cloned()
            .unwrap_or_else(|| format!("_{}", src_place.local));

        let dest_name = format!("offset_{}", dest.local);

        // Accumulate the BYTE offset from the allocation base: dest_offset =
        // src_offset + stride * this_offset. `.add(n)` on `*const T` advances
        // `n * size_of(T)` bytes, so the element count must be scaled by the
        // pointee stride to compose with the byte allocation size downstream.
        // Use the PIPELINE variable name for the offset operand
        // (operand_named_formula) so a guard/def over `start` connects to the
        // obligation's offset — same reason the len operand is named. An UNKNOWN
        // stride yields a fail-closed poison offset (a fresh var no guard can
        // discharge), never an under-counted element offset.
        let src_stride = self.local_pointee_stride(src_place.local);
        let src_offset = self.pointer_offsets.get(&src_name).cloned().unwrap_or(Formula::Int(0));
        let this_offset = match src_stride {
            Some(stride) => scale_to_bytes(stride, self.operand_named_formula(offset_op)),
            None => generated_sep_var(format!("offset_unknown_stride_{}", dest.local), Sort::Int),
        };
        self.pointer_offsets
            .insert(dest_name.clone(), Formula::Add(Box::new(src_offset), Box::new(this_offset)));

        self.local_to_ptr.insert(dest.local, dest_name.clone());

        // Carry a backing field-load tag through `self.ptr.add(start)` so the
        // backing-invariant assume still recognizes the offset pointer.
        if let Some(&bf) = self.field_loads.get(&src_place.local) {
            self.field_loads.insert(dest.local, bf);
        }

        // Derive provenance from source
        let prov =
            self.heap.pointer(&src_name).map(|p| p.provenance).unwrap_or(ProvenanceId::UNKNOWN);

        let permission = self
            .heap
            .pointer(&src_name)
            .map(|p| p.permission)
            .unwrap_or(PointerPermission::ReadWrite);

        // Byte address: the element offset advances `stride` bytes per element.
        let offset_formula = match src_stride {
            Some(stride) => scale_to_bytes(stride, operand_to_formula_simple(offset_op)),
            None => operand_to_formula_simple(offset_op),
        };
        let src_addr = generated_sep_var(format!("ptr_{src_name}"), Sort::Int);
        let dest_addr = Formula::Add(Box::new(src_addr.clone()), Box::new(offset_formula));

        let ptr = SymbolicPointer {
            addr: dest_addr,
            provenance: prov,
            name: dest_name.clone(),
            permission,
        };
        self.heap.track_pointer(ptr);

        // VC: result must remain within allocation bounds.
        // If the base traces to a backing pointer field, bound the accumulated
        // byte offset against the OPAQUE backing allocation size (NOT `self.len`
        // directly — that would unsoundly assume `self.len <= alloc_size` with no
        // verified establish). `ptr.add(offset)` is valid when `offset <=
        // alloc_size` (one-past-the-end is permitted for `add`; the deref bound is
        // the copy-bounds VC). When the invariant is CERTIFIED the conjoined
        // `alloc_size >= self.len` lets a `start + len <= self.len` guard
        // discharge it; otherwise it stays fail-closed (CAUGHT).
        let backing_info =
            self.field_loads.get(&src_place.local).copied().and_then(|(base_struct, ptr_field)| {
                self.field_backing
                    .iter()
                    .copied()
                    .find(|(pf, _)| *pf == ptr_field)
                    .map(|(_, len_field)| (base_struct, ptr_field, len_field))
            });
        if let Some((base_struct, ptr_field, len_field)) = backing_info {
            let (size, assumption) = self.backing_alloc_size(base_struct, ptr_field, len_field);
            let offset = self.pointer_offsets.get(&dest_name).cloned().unwrap_or(Formula::Int(0));
            // Violation (prove UNSAT): offset past the backing allocation size.
            let violation = Formula::Gt(Box::new(offset), Box::new(size));
            let formula = match assumption {
                Some(a) => Formula::And(vec![a, violation]),
                None => violation,
            };
            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:offset] pointer offset out of bounds for `{src_name}` in {}",
                        self.func_name,
                    ),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                formula,
                contract_metadata: None,
            });
        } else if prov.is_concrete() {
            let base = Formula::Var(prov.base_var(), Sort::Int);
            let size = Formula::Var(prov.size_var(), Sort::Int);
            let dest_addr_var = generated_sep_var(format!("ptr_{dest_name}"), Sort::Int);

            self.vcs.push(VerificationCondition {
                kind: VcKind::Assertion {
                    message: format!(
                        "[unsafe:sep:offset] pointer offset out of bounds for `{src_name}` in {}",
                        self.func_name,
                    ),
                },
                function: self.func_name.clone().into(),
                location: span.clone(),
                formula: Formula::Or(vec![
                    // dest < base
                    Formula::Lt(Box::new(dest_addr_var.clone()), Box::new(base.clone())),
                    // dest >= base + size
                    Formula::Not(Box::new(Formula::Lt(
                        Box::new(dest_addr_var),
                        Box::new(Formula::Add(Box::new(base), Box::new(size))),
                    ))),
                ]),
                contract_metadata: None,
            });
        }
    }

    /// Realloc: free old allocation, create new one.
    fn interpret_realloc(&mut self, dest: &Place, span: &SourceSpan, callee: &str) {
        // Free old allocation if tracked
        if let Some(ptr_name) = self.local_to_ptr.get(&dest.local).cloned()
            && let Some(ptr) = self.heap.pointer(&ptr_name)
        {
            let prov = ptr.provenance;
            self.heap.free(prov);
        }

        // Allocate new region
        let prov = self.heap.allocate(&format!("realloc_{}", dest.local));
        let ptr_name = format!("realloc_{}", dest.local);
        self.local_to_ptr.insert(dest.local, ptr_name.clone());

        // VC: realloc result null check
        self.vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[unsafe:sep:realloc] result null check for {} in {}",
                    callee, self.func_name,
                ),
            },
            function: self.func_name.clone().into(),
            location: span.clone(),
            formula: Formula::Eq(
                Box::new(generated_sep_var(format!("ptr_{ptr_name}"), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        });

        // VC: new size must be positive
        self.vcs.push(VerificationCondition {
            kind: VcKind::Assertion {
                message: format!(
                    "[unsafe:sep:realloc] new allocation size check for {} ({})",
                    callee, prov,
                ),
            },
            function: self.func_name.clone().into(),
            location: span.clone(),
            formula: Formula::Le(
                Box::new(Formula::Var(prov.size_var(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
            contract_metadata: None,
        });
    }

    /// Interpret a Ref rvalue (borrow creation).
    fn interpret_ref(&mut self, dest: &Place, src_place: &Place, mutable: bool) {
        let permission =
            if mutable { PointerPermission::ReadWrite } else { PointerPermission::ReadOnly };

        let ptr_name = format!("ref_{}", dest.local);
        let prov = if let Some(src_name) = self.local_to_ptr.get(&src_place.local) {
            self.heap.pointer(src_name).map(|ptr| ptr.provenance).unwrap_or(ProvenanceId::UNKNOWN)
        } else if src_place.projections.is_empty()
            && let Some(size) = self.local_tys.get(src_place.local).and_then(ty_byte_size)
        {
            // A reference to a WHOLE value whose size is in the type (e.g.
            // `&buf` for `buf: [u8; N]`): record a CONCRETE allocation at offset
            // 0, so a pointer later derived from it (`as_ptr`, casts) carries the
            // backing size and a `from_raw_parts` bound can be discharged. The
            // `projections.is_empty()` guard keeps this SOUND: a reference to a
            // SUBSLICE/field (`&buf[k..]`) has a nonzero offset we do not model
            // here, so it stays UNKNOWN (fail-closed) rather than recording the
            // whole-array size at offset 0 (which would under-count).
            let p = self.heap.allocate(&format!("sized_ref_{}", src_place.local));
            self.concrete_sizes.insert(p, size);
            self.record_stack_good(p, src_place.local);
            p
        } else {
            ProvenanceId::UNKNOWN
        };

        let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
        self.heap.track_pointer(ptr);
        self.local_to_ptr.insert(dest.local, ptr_name);
    }

    // ────────────────────────────────────────────────────────────────────
    // Step 4: Frame computation from heap diff
    // ────────────────────────────────────────────────────────────────────

    /// Compute the frame between two heap snapshots.
    ///
    /// The frame is the separating conjunction of cells that exist in
    /// `before` but are unchanged in the current heap. This enables the
    /// frame rule: `{P} C {Q}` implies `{P * R} C {Q * R}` when R is
    /// the frame.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn compute_frame(before: &SymbolicHeap, after: &SymbolicHeap) -> SepFormula {
        let before_formula = before.to_sep_formula();
        let after_formula = after.to_sep_formula();

        // If both are emp, frame is emp
        if before_formula.is_emp() && after_formula.is_emp() {
            return SepFormula::Emp;
        }

        // If before is emp, there is no frame (everything is new)
        if before_formula.is_emp() {
            return SepFormula::Emp;
        }

        // If after is emp, everything was freed; frame is emp
        if after_formula.is_emp() {
            return SepFormula::Emp;
        }

        // Conservative: the frame is the before state minus modified cells.
        // In a more precise implementation, we would track which cells changed.
        // For now, return the before state as a conservative over-approximation
        // of the frame (the caller verifies disjointness separately).
        before_formula
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Step 2: SepFormula::PointsToMulti extension
// ────────────────────────────────────────────────────────────────────────────

/// Create a multi-cell PointsTo formula for a contiguous allocation.
///
/// `points_to_multi(base, values)` produces:
///   `base |-> values[0] * (base+1) |-> values[1] * ... * (base+n-1) |-> values[n-1]`
///
/// This is the natural extension for modeling arrays, slices, and
/// multi-byte allocations in separation logic.
#[cfg(test)]
#[must_use]
pub(crate) fn points_to_multi(base: &Formula, values: &[Formula]) -> SepFormula {
    if values.is_empty() {
        return SepFormula::Emp;
    }

    let cells: Vec<SepFormula> = values
        .iter()
        .enumerate()
        .map(|(i, val)| {
            let addr = if i == 0 {
                base.clone()
            } else {
                Formula::Add(Box::new(base.clone()), Box::new(Formula::Int(i as i128)))
            };
            SepFormula::points_to(addr, val.clone())
        })
        .collect();

    SepFormula::star_many(cells)
}

// ────────────────────────────────────────────────────────────────────────────
// Step 5: Integration — check_sep_unsafe for generate_vcs
// ────────────────────────────────────────────────────────────────────────────

/// Generate separation-logic-based VCs for unsafe operations in a function.
///
/// Walks MIR forward through all blocks, interpreting statements and
/// terminators with the [`SepEngine`]. Returns VCs for detected unsafe
/// patterns: raw deref read/write, alloc, dealloc, ptr::copy, transmute,
/// address_of, and pointer offset.
///
/// Test-facing convenience wrapper around the production blocked-VC entry point.
#[must_use]
#[cfg(test)]
pub(crate) fn check_sep_unsafe(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    check_sep_unsafe_blocked(func).into_iter().map(|(vc, _)| vc).collect()
}

/// Detect a backing-length invariant `(ptr_field, len_field)` from a function's
/// local types: a struct (possibly behind references) with EXACTLY one raw-
/// pointer field and EXACTLY one unsigned-integer field has the unambiguous
/// buffer+length shape (e.g. `MmapMut { ptr: *mut u8, len: usize }`). The struct
/// surfaces in any function that touches it — as the `&self` receiver of a
/// method, or as the constructed value in `Self { .. }`. Conservative by design:
/// only the unambiguous shape, so the (sound, establish-backed) obligations are
/// never emitted for a struct whose pointer and length are unrelated.
#[cfg(test)]
fn detect_field_backing(func: &VerifiableFunction) -> Vec<(usize, usize)> {
    detect_backing_struct(func).map(|(_, pf, lf)| vec![(pf, lf)]).unwrap_or_default()
}

/// The first unambiguous backing struct among a function's local types, as
/// `(struct_name, ptr_field, len_field)`. Same shape rule as
/// [`detect_field_backing`] (exactly one raw-pointer field and one unsigned-int
/// field), but also surfaces the struct NAME so the use site can look up whether
/// that struct's backing invariant is interprocedurally certified
/// ([`crate::is_backing_struct_certified`]).
/// Every backing-shaped struct this function mentions, as `(name, ptr, len)`.
///
/// SOUNDNESS: [`detect_backing_struct`] returns only the FIRST match, which is
/// fine for a single-struct analysis but wrong for the interprocedural
/// certification scan. There, a function is only examined for struct `S` when
/// detection returns `S` — so a decoy local of the same shape appearing earlier
/// in `locals` makes the function be skipped for `S` entirely, taking its
/// backing-field mutation check with it. The mutator becomes invisible and `S`
/// certifies, which publishes the use-site ASSUME `alloc_size >= self.len`.
///
/// Callers deciding whether a function is RELEVANT to a named struct must use
/// this; only callers that genuinely want "the one struct this function is
/// about" may use the singular form.
pub(crate) fn detect_backing_structs(func: &VerifiableFunction) -> Vec<(String, usize, usize)> {
    let mut found: Vec<(String, usize, usize)> = Vec::new();
    for local in &func.body.locals {
        let mut ty = &local.ty;
        while let Ty::Ref { inner, .. } = ty {
            ty = inner;
        }
        if let Ty::Adt { name, fields, .. } = ty {
            let ptrs: Vec<usize> = fields
                .iter()
                .enumerate()
                .filter(|(_, (_, t))| matches!(t, Ty::RawPtr { .. }))
                .map(|(i, _)| i)
                .collect();
            let lens: Vec<usize> = fields
                .iter()
                .enumerate()
                .filter(|(_, (_, t))| matches!(t, Ty::Int { signed: false, .. }))
                .map(|(i, _)| i)
                .collect();
            if ptrs.len() == 1 && lens.len() == 1 && !found.iter().any(|(n, _, _)| n == name) {
                found.push((name.clone(), ptrs[0], lens[0]));
            }
        }
    }
    found
}

pub(crate) fn detect_backing_struct(func: &VerifiableFunction) -> Option<(String, usize, usize)> {
    for local in &func.body.locals {
        let mut ty = &local.ty;
        while let Ty::Ref { inner, .. } = ty {
            ty = inner;
        }
        if let Ty::Adt { name, fields, .. } = ty {
            let ptrs: Vec<usize> = fields
                .iter()
                .enumerate()
                .filter(|(_, (_, t))| matches!(t, Ty::RawPtr { .. }))
                .map(|(i, _)| i)
                .collect();
            let lens: Vec<usize> = fields
                .iter()
                .enumerate()
                .filter(|(_, (_, t))| matches!(t, Ty::Int { signed: false, .. }))
                .map(|(i, _)| i)
                .collect();
            if ptrs.len() == 1 && lens.len() == 1 {
                return Some((name.clone(), ptrs[0], lens[0]));
            }
        }
    }
    None
}

/// Run the separation engine on `func` with the `(ptr_field, len_field)` backing
/// pair FORCED on (bypassing the opt-in gate), and return the ESTABLISH-obligation
/// violation formulas emitted at struct constructions (`[unsafe:sep:backing] …
/// at construction`). Each is the form `Lt(alloc_size, len)`; the constructor
/// establishes the invariant iff that is UNSAT. Used by interprocedural backing
/// certification ([`crate::backing_cert`]) to decide whether a constructor proves
/// `alloc_size >= self.len` from its local facts alone.
pub(crate) fn establish_formulas(
    func: &VerifiableFunction,
    ptr_field: usize,
    len_field: usize,
) -> Vec<Formula> {
    let mut engine = SepEngine::new(&func.name)
        .with_local_tys(func.body.locals.iter().map(|local| local.ty.clone()).collect())
        .with_local_names(func.body.locals.iter().map(|local| local.name.clone()).collect())
        .with_field_backing(vec![(ptr_field, len_field)]);

    // Mirror check_sep_unsafe_blocked's ref-arg pointer initialization so a
    // pointer constructed from an argument is tracked when the establish VC is
    // formed.
    for local in &func.body.locals {
        if local.index > 0
            && local.index <= func.body.arg_count
            && let trust_types::Ty::Ref { mutable, .. } = &local.ty
        {
            let ptr_name = format!("arg_{}", local.index);
            let prov = engine.heap.allocate(&ptr_name);
            let permission =
                if *mutable { PointerPermission::ReadWrite } else { PointerPermission::ReadOnly };
            let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
            engine.heap.track_pointer(ptr);
            engine.local_to_ptr.insert(local.index, ptr_name);
        }
    }

    let reachable = reachable_block_ids(&func.body.blocks);
    let default_span = SourceSpan::default();
    for block in &func.body.blocks {
        // Cleanup (unwind) blocks are unreachable via the IR's normal `target` edges;
        // their `Drop`s are unwind cleanup and must not free for the normal-path heap
        // analysis (see `interpret_drop`).
        engine.current_block_reachable = reachable.contains(&block.id.0);
        for stmt in &block.stmts {
            let span = match stmt {
                Statement::Assign { span, .. } => span,
                _ => &default_span,
            };
            engine.interpret_statement(stmt, span);
        }
        engine.interpret_terminator(&block.terminator);
    }

    engine
        .into_vcs()
        .into_iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::Assertion { message }
                if message.contains("[unsafe:sep:backing]")
                    && message.contains("at construction") =>
            {
                Some(vc.formula)
            }
            _ => None,
        })
        .collect()
}

/// Block ids reachable from the entry (`bb0`) via the IR's terminator successors.
/// CLEANUP (unwind) blocks are NOT reachable: rustc's unwind successor edges are
/// dropped at extraction (`Terminator::Call`/`Drop` keep only their normal `target`;
/// `Resume` is the unwind sink, with no successor). So the complement of this set is
/// exactly the cleanup/dead blocks, whose `Drop`s the heap analysis must not treat as
/// normal-path frees (see [`SepEngine::interpret_drop`]).
fn reachable_block_ids(blocks: &[trust_types::BasicBlock]) -> FxHashSet<usize> {
    // CONSERVATIVE: `Terminator` is `#[non_exhaustive]`, so a future variant has
    // successors we cannot read. Rather than UNDER-approximate reachability (which
    // could wrongly mark a normal block as cleanup and skip a genuine `Drop` free →
    // miss a use-after-free → false PROVE of unsafe code), treat EVERY block as
    // reachable when any terminator is unknown. Known terminators give precise
    // reachability, so cleanup blocks are identified exactly.
    if blocks.iter().any(|b| terminator_successors(&b.terminator).is_none()) {
        return blocks.iter().map(|b| b.id.0).collect();
    }
    let mut reachable = FxHashSet::default();
    let mut stack = vec![0usize]; // entry block `bb0`
    while let Some(id) = stack.pop() {
        if !reachable.insert(id) {
            continue;
        }
        if let Some(block) = blocks.iter().find(|b| b.id.0 == id) {
            for succ in terminator_successors(&block.terminator).into_iter().flatten() {
                if !reachable.contains(&succ) {
                    stack.push(succ);
                }
            }
        }
    }
    reachable
}

/// The normal control-flow successors of a terminator (the unwind/cleanup edges were
/// dropped at extraction, so this yields only normal-path successors). `None` for a
/// future `#[non_exhaustive]` variant whose successors are unreadable.
fn terminator_successors(term: &Terminator) -> Option<Vec<usize>> {
    Some(match term {
        Terminator::Goto(b) => vec![b.0],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            targets.iter().map(|(_, b)| b.0).chain(std::iter::once(otherwise.0)).collect()
        }
        Terminator::Call { target: Some(b), .. } => vec![b.0],
        Terminator::Assert { target, .. } => vec![target.0],
        Terminator::Drop { target, .. } => vec![target.0],
        Terminator::Opaque { targets, .. } => targets.iter().map(|b| b.0).collect(),
        Terminator::Call { target: None, .. }
        | Terminator::Return
        | Terminator::Unreachable
        | Terminator::Resume => Vec::new(),
        _ => return None,
    })
}

/// Run the production separation pass and pair each VC with the `BlockId` it was
/// generated in, so callers can conjoin that block's path guards (e.g. a
/// `len <= N` branch condition) — letting a guarded `from_raw_parts` discharge.
pub(crate) fn check_sep_unsafe_blocked(
    func: &VerifiableFunction,
) -> Vec<(VerificationCondition, BlockId)> {
    // Quick check: skip functions with no unsafe-looking patterns
    if !has_unsafe_patterns(func) {
        return Vec::new();
    }

    let mut engine = SepEngine::new(&func.name)
        .with_local_tys(func.body.locals.iter().map(|local| local.ty.clone()).collect())
        .with_local_names(func.body.locals.iter().map(|local| local.name.clone()).collect())
        .with_metadata_only_addr_of(metadata_only_addr_of_locals(func))
        .with_call_arg_confined_addr_of(call_arg_confined_addr_of_locals(func))
        .with_stack_good_gate(&func.body.blocks);

    // Opt-in relational backing-length invariants. OFF by default (so there is
    // zero behavior change for existing code); the `#[trust::backing]` attribute
    // enables proving buffer+length structs (e.g. aterm's `MmapMut { ptr, len }`).
    // Detection is conservative — only an unambiguous (one raw-pointer field, one
    // unsigned-int field) struct — and the obligations stay sound because the
    // construction ESTABLISH obligation must discharge whatever a method ASSUMES.
    // Source-driven `#[trust::backing]` (via the compiler-set hint) is the only
    // authority for relational backing invariants. The former ambient override
    // could silently assert an invariant that was absent from source and change
    // Catch to Prove outside rustc's dependency graph.
    // Trust: removed `TRUST_BACKING_INVARIANTS` env read; sole surface is the
    // `#[trust::backing]` attribute (via the owner-checked VC-gen context).
    if crate::backing_hint_for(&func.def_path) {
        if let Some((struct_name, pf, lf)) = detect_backing_struct(func) {
            engine = engine.with_field_backing(vec![(pf, lf)]);
            // If a whole-crate pre-pass certified this struct's backing invariant
            // (every constructor establishes `alloc_size >= self.len`), the
            // use-site ASSUME may license that fact and so discharge a guarded
            // access — soundly. Uncertified ⇒ fail-closed (CAUGHT).
            if crate::is_backing_struct_certified(&struct_name) {
                engine = engine.with_backing_certified(true);
            }
        }
    }
    // Emit the mmap-truncation temporal model by DEFAULT (batteries-on, no env
    // flag — see docs/DESIGN_PHILOSOPHY.md). It is an L2-domain VC, so
    // `filter_vcs_by_level` keeps it only at `-Z trust-verify-level=2` (where
    // `ty` CATCHES the truncation hazard, or PROVES it under a single-writer
    // invariant) and drops it at L0/L1 — where the always-on
    // `ExternallyMutableAllocationBounds` already catches the hazard. It is only
    // materialized at an actual map call site (`interpret_external_map`), so
    // non-mmap functions are unaffected. `single_writer` comes from the
    // `#[trust::single_writer]` attribute (compiler-set hint) as the sole
    // authority; an ambient testing override is not a proof assumption.
    // Trust: removed `TRUST_TEMPORAL_SINGLE_WRITER` env read; sole surface is the
    // `#[trust::single_writer]` attribute (via the owner-checked VC-gen context).
    let single_writer = crate::single_writer_hint_for(&func.def_path);
    engine = engine.with_temporal_mmap(true, single_writer);

    // Initialize pointer tracking for ref-typed arguments
    for local in &func.body.locals {
        if local.index > 0
            && local.index <= func.body.arg_count
            && let trust_types::Ty::Ref { mutable, .. } = &local.ty
        {
            let ptr_name = format!("arg_{}", local.index);
            let prov = engine.heap.allocate(&ptr_name);
            let permission =
                if *mutable { PointerPermission::ReadWrite } else { PointerPermission::ReadOnly };
            let ptr = SymbolicPointer::new(&ptr_name, prov, permission);
            engine.heap.track_pointer(ptr);
            engine.local_to_ptr.insert(local.index, ptr_name);
        }
    }

    // Forward walk through blocks, recording which block each VC came from.
    let reachable = reachable_block_ids(&func.body.blocks);
    let default_span = SourceSpan::default();
    let mut vc_blocks: Vec<BlockId> = Vec::new();
    for block in &func.body.blocks {
        // Cleanup (unwind) blocks are unreachable via normal `target` edges; their
        // `Drop`s are unwind cleanup and must not free (see `interpret_drop`).
        engine.current_block_reachable = reachable.contains(&block.id.0);
        let before = engine.vc_len();
        for stmt in &block.stmts {
            let span = match stmt {
                Statement::Assign { span, .. } => span,
                _ => &default_span,
            };
            engine.interpret_statement(stmt, span);
        }
        engine.interpret_terminator(&block.terminator);
        for _ in before..engine.vc_len() {
            vc_blocks.push(block.id);
        }
    }

    engine
        .into_vcs()
        .into_iter()
        .zip(vc_blocks)
        // TRUSTED-STD-SPAN gate. Every VC this engine emits is an
        // `[unsafe:sep:*]` unsafe-operation obligation whose `location` is the
        // operation's OWN source span. When that span resolves to the sysroot
        // standard library (`core`/`alloc`/`std`, i.e. the `library/` tree), the
        // unsafe op is std-internal — e.g. the `vec!` macro's inlined
        // `RawVec`/`Box::new_uninit`/`assume_init`, whose span is
        // `alloc/src/macros.rs` even though the macro was expanded into a user
        // function's MIR. Std is already the trusted TCB the verifier hard-skips
        // for `core`/`alloc`/`std` ("all proofs are conditional on its
        // correctness", `trust_proof_cert`), so charging its macro-internal
        // unsafe to the user is inconsistent. Discharge (drop) it here.
        //
        // SOUNDNESS: gated STRICTLY on the std-span check ([`is_trusted_std_span`],
        // fail-closed) — never on obligation kind. A user-written `unsafe` block
        // (its span in ny-cert / any first-party crate) is NOT a std span, so its
        // obligation is preserved untouched. Only unsafe-operation VCs pass
        // through this driver, so slice-bounds / arithmetic / absent-callee
        // obligations (emitted elsewhere) are unaffected.
        .filter(|(vc, _)| !is_trusted_std_span(&vc.location))
        .collect()
}

// ────────────────────────────────────────────────────────────────────────────
// Helpers
// ────────────────────────────────────────────────────────────────────────────

/// Locals defined by `AddressOf` (`&raw const/mut`) whose ONLY use across the
/// function is the whole-value operand of a `PtrMetadata` read.
///
/// This is the compiler's `<[T]>::len()` lowering: `_p = &raw const *slice_ref;
/// _len = PtrMetadata(_p)` (it lowers to a raw `&raw const` notably on a
/// `&mut [T]`, where the length is re-read at each index/guard). Taking the
/// address purely to read the fat pointer's LENGTH metadata never dereferences
/// the pointee — the metadata word is part of the pointer value itself — so such
/// a pointer carries no source-liveness obligation. The sep engine's blanket
/// `[unsafe:sep:addr_of]` source-liveness VC therefore false-refutes the safe,
/// ubiquitous guarded `&mut [T]` index `if i < dst.len() { dst[i] = .. }`; this
/// set lets [`SepEngine::interpret_address_of`] skip it.
///
/// SOUNDNESS: a local is INCLUDED only if every other appearance (a deref or
/// index THROUGH it, a store of it, a call argument, a return, a reassignment) is
/// absent — any such appearance disqualifies it and the normal obligation stands.
/// So the skip can only ever drop an obligation for a provably-non-dereferencing
/// metadata read, never for a pointer that is actually used.
fn metadata_only_addr_of_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    // Push every local an operand READS (its base local, plus any Index locals in
    // its projections).
    fn operand_reads(op: &Operand, out: &mut Vec<usize>) {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            out.push(p.local);
            for proj in &p.projections {
                if let Projection::Index(i) = proj {
                    out.push(*i);
                }
            }
        }
    }
    // Index locals inside a place's projections are reads, regardless of whether
    // the place is read or written.
    fn place_index_reads(place: &Place, out: &mut Vec<usize>) {
        for proj in &place.projections {
            if let Projection::Index(i) = proj {
                out.push(*i);
            }
        }
    }

    // Candidates: locals assigned by a whole-value `AddressOf`.
    let mut candidates: FxHashSet<usize> = FxHashSet::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue: Rvalue::AddressOf(_, _), .. } = stmt
                && place.projections.is_empty()
            {
                candidates.insert(place.local);
            }
        }
    }
    if candidates.is_empty() {
        return candidates;
    }

    let mut disqualified: FxHashSet<usize> = FxHashSet::default();
    // A candidate qualifies only if it is ACTUALLY consumed by ≥1 PtrMetadata read.
    // An AddressOf whose result is never read is a dead/dangling raw pointer, not a
    // metadata read — it keeps the conservative source-liveness obligation.
    let mut consumed_by_metadata: FxHashSet<usize> = FxHashSet::default();
    let disq = |reads: &[usize], disqualified: &mut FxHashSet<usize>| {
        for &l in reads {
            if candidates.contains(&l) {
                disqualified.insert(l);
            }
        }
    };

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                // A non-Assign statement that mentions a candidate place (Drop-like
                // markers, Deinit, Retag, PlaceMention) is a use we don't model —
                // disqualify conservatively.
                match stmt {
                    Statement::SetDiscriminant { place, .. }
                    | Statement::Deinit { place }
                    | Statement::Retag { place }
                    | Statement::PlaceMention(place) => {
                        if candidates.contains(&place.local) {
                            disqualified.insert(place.local);
                        }
                        let mut reads = Vec::new();
                        place_index_reads(place, &mut reads);
                        disq(&reads, &mut disqualified);
                    }
                    Statement::Intrinsic { args, .. } => {
                        let mut reads = Vec::new();
                        for op in args {
                            operand_reads(op, &mut reads);
                        }
                        disq(&reads, &mut disqualified);
                    }
                    Statement::Unsupported { operands, .. } => {
                        let mut reads = Vec::new();
                        for op in operands {
                            operand_reads(op, &mut reads);
                        }
                        disq(&reads, &mut disqualified);
                    }
                    _ => {}
                }
                continue;
            };

            let mut reads = Vec::new();
            // A write THROUGH a candidate (`*p = ..`, `p[i] = ..`) dereferences it.
            if place.local != 0
                && candidates.contains(&place.local)
                && !place.projections.is_empty()
            {
                disqualified.insert(place.local);
            }
            // Reassigning a candidate to a non-AddressOf value muddies the
            // single-pointer "only use" invariant — drop it.
            if place.projections.is_empty()
                && candidates.contains(&place.local)
                && !matches!(rvalue, Rvalue::AddressOf(_, _))
            {
                disqualified.insert(place.local);
            }
            place_index_reads(place, &mut reads);

            match rvalue {
                // The one ALLOWED use: PtrMetadata over the whole candidate pointer.
                // A projected operand (not expected for a pointer) is a real read.
                Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, op) => {
                    if let Operand::Copy(p) | Operand::Move(p) = op {
                        if p.projections.is_empty() {
                            if candidates.contains(&p.local) {
                                consumed_by_metadata.insert(p.local);
                            }
                        } else {
                            operand_reads(op, &mut reads);
                        }
                    }
                }
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Repeat(op, _) => operand_reads(op, &mut reads),
                Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                    operand_reads(a, &mut reads);
                    operand_reads(b, &mut reads);
                }
                Rvalue::Ref { place: p, .. }
                | Rvalue::AddressOf(_, p)
                | Rvalue::Discriminant(p)
                | Rvalue::Len(p)
                | Rvalue::CopyForDeref(p) => {
                    reads.push(p.local);
                    place_index_reads(p, &mut reads);
                }
                Rvalue::Aggregate(_, ops) => {
                    for op in ops {
                        operand_reads(op, &mut reads);
                    }
                }
                Rvalue::Unsupported { operands, .. } => {
                    for op in operands {
                        operand_reads(op, &mut reads);
                    }
                }
                // Trust: Rvalue is #[non_exhaustive]. An unknown future variant may
                // read a candidate pointer in some position we cannot inspect, so
                // fail closed: disqualify every candidate it could touch.
                _ => disqualified.extend(candidates.iter().copied()),
            }
            disq(&reads, &mut disqualified);
        }

        // Terminator reads / reassignments.
        let mut reads = Vec::new();
        match &block.terminator {
            Terminator::Call { args, dest, .. } => {
                for op in args {
                    operand_reads(op, &mut reads);
                }
                if candidates.contains(&dest.local) {
                    disqualified.insert(dest.local);
                }
                place_index_reads(dest, &mut reads);
            }
            Terminator::SwitchInt { discr, .. } => operand_reads(discr, &mut reads),
            Terminator::Assert { cond, .. } => operand_reads(cond, &mut reads),
            Terminator::Drop { place, .. } => {
                if candidates.contains(&place.local) {
                    disqualified.insert(place.local);
                }
                place_index_reads(place, &mut reads);
            }
            _ => {}
        }
        disq(&reads, &mut disqualified);
    }

    candidates.retain(|l| !disqualified.contains(l) && consumed_by_metadata.contains(l));
    candidates
}

/// Whether `stmt` mentions (reads, writes, or storage-marks) any local in `set`,
/// treating unknown `#[non_exhaustive]` payloads as a mention (fail closed).
/// Storage markers of a SET member count as a mention here; the caller decides
/// whether they are benign for its analysis.
fn stmt_mentions_any(stmt: &Statement, set: &FxHashSet<usize>) -> bool {
    let place_mentions = |p: &Place| {
        set.contains(&p.local)
            || p.projections
                .iter()
                .any(|proj| matches!(proj, Projection::Index(i) if set.contains(i)))
    };
    let op_mentions =
        |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if place_mentions(p));
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            place_mentions(place)
                || match rvalue {
                    Rvalue::Use(op)
                    | Rvalue::UnaryOp(_, op)
                    | Rvalue::Cast(op, _)
                    | Rvalue::Repeat(op, _) => op_mentions(op),
                    Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                        op_mentions(a) || op_mentions(b)
                    }
                    Rvalue::Ref { place: p, .. }
                    | Rvalue::AddressOf(_, p)
                    | Rvalue::Discriminant(p)
                    | Rvalue::Len(p)
                    | Rvalue::CopyForDeref(p) => place_mentions(p),
                    Rvalue::Aggregate(_, ops) => ops.iter().any(op_mentions),
                    Rvalue::Unsupported { operands, .. } => operands.iter().any(op_mentions),
                    // #[non_exhaustive]: an unknown rvalue may touch anything.
                    _ => true,
                }
        }
        Statement::StorageLive(l) | Statement::StorageDead(l) => set.contains(l),
        Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place }
        | Statement::PlaceMention(place) => place_mentions(place),
        Statement::Intrinsic { args, .. } => args.iter().any(op_mentions),
        Statement::Unsupported { operands, .. } => operands.iter().any(op_mentions),
        Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => false,
        // #[non_exhaustive]: an unknown statement may touch anything.
        _ => true,
    }
}

/// Whether `term` mentions any local in `set`; unknown/opaque terminators count
/// as a mention (fail closed).
fn terminator_mentions_any(term: &Terminator, set: &FxHashSet<usize>) -> bool {
    let place_mentions = |p: &Place| {
        set.contains(&p.local)
            || p.projections
                .iter()
                .any(|proj| matches!(proj, Projection::Index(i) if set.contains(i)))
    };
    let op_mentions =
        |op: &Operand| matches!(op, Operand::Copy(p) | Operand::Move(p) if place_mentions(p));
    match term {
        Terminator::Call { args, dest, .. } => args.iter().any(op_mentions) || place_mentions(dest),
        Terminator::SwitchInt { discr, .. } => op_mentions(discr),
        Terminator::Assert { cond, .. } => op_mentions(cond),
        Terminator::Drop { place, .. } => place_mentions(place),
        Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable | Terminator::Resume => {
            false
        }
        // Opaque (inline asm, …) and unknown #[non_exhaustive] variants may
        // consume anything: fail closed.
        _ => true,
    }
}

/// Locals defined by an `AddressOf` of a WHOLE stack local whose raw pointer is
/// CONFINED to the defining block and consumed only as a bare by-value argument
/// of that block's own `Call` terminator — the `&mut out`-parameter FFI shape:
/// `let mut status = 0; waitpid(pid, &mut status, 0)` lowers to
/// `_p = &raw mut _status; waitpid(.., move _p, ..)`.
///
/// For such a pointer the blanket `[unsafe:sep:addr_of]` source-liveness VC is
/// discharged STRUCTURALLY: the pointer cannot outlive the block (its only
/// consumers are that block's call arguments; it never escapes into another
/// block, place projection, store, return slot, or the call destination), and
/// the source local's storage cannot end before the call (no `StorageDead(src)`
/// between the `AddressOf` and the terminator — a local's storage ends only at
/// its `StorageDead`). So the source is live at every in-frame use. Retention
/// of the pointer by the CALLEE past the call is the FFI summary's contract
/// surface, not this VC's: the liveness claim here covers exactly the in-frame
/// uses the confinement proves.
///
/// SOUNDNESS (fail-closed): a candidate is kept only if EVERY appearance of the
/// pointer — and of every same-block pure `Use`/`Cast` copy of it (the `&mut`
/// → `*mut` coercion chain) — across the WHOLE body is one of: the defining
/// assign, a recognized chain link, a benign storage marker of the pointer
/// temp itself, or a bare by-value argument of the defining block's call
/// terminator. Any other mention (via the fail-closed
/// [`stmt_mentions_any`]/[`terminator_mentions_any`] walks, which treat unknown
/// `#[non_exhaustive]` payloads as mentions) disqualifies it and the
/// conservative VC stands.
fn call_arg_confined_addr_of_locals(func: &VerifiableFunction) -> FxHashSet<usize> {
    let mut confined: FxHashSet<usize> = FxHashSet::default();

    for (bidx, block) in func.body.blocks.iter().enumerate() {
        // Only a block ending in a call can consume the pointer.
        let Terminator::Call { args: call_args, dest: call_dest, .. } = &block.terminator else {
            continue;
        };

        'candidates: for (sidx, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place, rvalue: Rvalue::AddressOf(_, src), .. } = stmt else {
                continue;
            };
            if !place.projections.is_empty() || place.local == 0 || place.local == src.local {
                continue;
            }
            // Effective source + the ref link (if any). Two admitted shapes:
            //   DIRECT:   `_p = &raw mut _status`            (src whole local)
            //   REBORROW: `_r = &mut _status; _p = &raw mut (*_r)` — a
            //   `&mut local` call argument reborrowed to a raw pointer (the
            //   `poll(&mut pfd, ..)` lowering). Admitted iff `_r` is defined
            //   EARLIER IN THIS BLOCK as a whole-place `Ref` of a whole
            //   untracked local; `_r` then JOINS THE CHAIN, so any mention of
            //   it other than the defining Ref, the AddressOf itself, and
            //   benign storage markers disqualifies the candidate via the
            //   existing fail-closed walks. The liveness subject (StorageDead
            //   scan below) is the UNDERLYING local in both shapes. Deeper
            //   projections/reborrow chains stay rejected (fail-closed).
            let (src_local, ref_link) = if src.projections.is_empty() {
                (src.local, None)
            } else if src.projections.as_slice() == [Projection::Deref] {
                let mut underlying = None;
                for (eidx, earlier) in block.stmts.iter().enumerate().take(sidx) {
                    if let Statement::Assign {
                        place: r, rvalue: Rvalue::Ref { place: u, .. }, ..
                    } = earlier
                        && r.projections.is_empty()
                        && r.local == src.local
                        && u.projections.is_empty()
                    {
                        // Last same-block whole-place Ref definition wins —
                        // matching the value the AddressOf actually reads.
                        underlying = Some((u.local, eidx));
                    }
                }
                match underlying {
                    Some((u, eidx)) if u != place.local && u != src.local => {
                        (u, Some((src.local, eidx)))
                    }
                    _ => continue,
                }
            } else {
                continue;
            };

            // Build the same-block coercion chain and verify no StorageDead of
            // the source (and no unrecognized mention of a chain member)
            // between the AddressOf and the call terminator.
            let mut chain: FxHashSet<usize> = FxHashSet::default();
            chain.insert(place.local);
            let mut reborrow_def_stmt = None;
            if let Some((r, eidx)) = ref_link {
                chain.insert(r);
                reborrow_def_stmt = Some(eidx);
            }
            let mut chain_stmts: FxHashSet<usize> = FxHashSet::default();
            chain_stmts.insert(sidx);
            // The reborrow's defining `Ref` is a recognized chain statement:
            // without this the whole-body escape scan would see it as an
            // unrecognized mention of the ref link and disqualify the shape.
            if let Some(eidx) = reborrow_def_stmt {
                chain_stmts.insert(eidx);
            }
            for (j, later) in block.stmts.iter().enumerate().skip(sidx + 1) {
                match later {
                    // The source's storage ends before the call: keep the VC.
                    Statement::StorageDead(l) | Statement::StorageLive(l) if *l == src_local => {
                        continue 'candidates;
                    }
                    // Benign storage markers of the pointer temps themselves.
                    Statement::StorageDead(l) | Statement::StorageLive(l) if chain.contains(l) => {
                        chain_stmts.insert(j);
                    }
                    // A pure whole-value copy/cast of a chain member (the
                    // `&mut` → `*mut` coercion): extend the chain.
                    Statement::Assign {
                        place: q,
                        rvalue: Rvalue::Use(op) | Rvalue::Cast(op, _),
                        ..
                    } if q.projections.is_empty()
                        && q.local != src_local
                        && !chain.contains(&q.local)
                        && matches!(
                            op,
                            Operand::Copy(p2) | Operand::Move(p2)
                                if p2.projections.is_empty() && chain.contains(&p2.local)
                        ) =>
                    {
                        chain.insert(q.local);
                        chain_stmts.insert(j);
                    }
                    other => {
                        // Any other mention of a chain member: keep the VC.
                        if stmt_mentions_any(other, &chain) {
                            continue 'candidates;
                        }
                    }
                }
            }

            // The call terminator: every chain appearance must be a bare
            // by-value argument; the destination must not touch the chain; and
            // the pointer must actually be consumed (a dead pointer keeps the
            // conservative VC).
            let mut consumed = false;
            for arg in call_args {
                if let Operand::Copy(p) | Operand::Move(p) = arg {
                    if chain.contains(&p.local) {
                        if p.projections.is_empty() {
                            consumed = true;
                        } else {
                            continue 'candidates;
                        }
                    }
                    if p.projections
                        .iter()
                        .any(|proj| matches!(proj, Projection::Index(i) if chain.contains(i)))
                    {
                        continue 'candidates;
                    }
                }
            }
            if !consumed
                || chain.contains(&call_dest.local)
                || call_dest
                    .projections
                    .iter()
                    .any(|proj| matches!(proj, Projection::Index(i) if chain.contains(i)))
            {
                continue;
            }

            // Whole-body escape scan: no chain member may appear anywhere else.
            for (b2, other_block) in func.body.blocks.iter().enumerate() {
                for (s2, other_stmt) in other_block.stmts.iter().enumerate() {
                    if b2 == bidx && chain_stmts.contains(&s2) {
                        continue;
                    }
                    // Storage markers of the pointer temps in OTHER blocks are
                    // benign (rustc places `StorageDead(_p)` in the call's
                    // successor block); they neither read nor deref.
                    if let Statement::StorageDead(l) | Statement::StorageLive(l) = other_stmt
                        && chain.contains(l)
                    {
                        continue;
                    }
                    if stmt_mentions_any(other_stmt, &chain) {
                        continue 'candidates;
                    }
                }
                if b2 != bidx && terminator_mentions_any(&other_block.terminator, &chain) {
                    continue 'candidates;
                }
            }

            confined.insert(place.local);
        }
    }

    confined
}

/// Check if a function contains patterns that warrant sep-logic analysis.
fn has_unsafe_patterns(func: &VerifiableFunction) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                // Deref on source or destination
                if crate::place_has_raw_deref(func, place) {
                    return true;
                }
                match rvalue {
                    Rvalue::Use(operand) if crate::operand_has_raw_deref(func, operand) => {
                        return true;
                    }
                    Rvalue::CopyForDeref(place) if crate::place_has_raw_deref(func, place) => {
                        return true;
                    }
                    Rvalue::AddressOf(_, _) => return true,
                    _ => {}
                }
            }
        }
        // Check for unsafe calls
        if let Terminator::Call { func: callee, .. } = &block.terminator {
            let lower = callee.to_lowercase();
            if is_alloc_call(&lower)
                || is_dealloc_call(&lower)
                || is_realloc_call(&lower)
                || is_external_map_call(&lower)
                || is_ptr_offset_call(&lower)
                || lower.contains("ptr::copy")
                || lower.contains("from_raw_parts")
                || lower.contains("mem::transmute")
                || is_unchecked_index_call(&lower)
                || is_raw_read_write_call(&lower)
                || unsafe_assertion_op(&lower).is_some()
                || is_unsafe_arith_op(&lower)
                || is_unwrap_unchecked_call(&lower)
            {
                return true;
            }
        }
    }
    false
}

/// True when an unsafe operation's OWN source span resolves to the sysroot
/// standard library — the `core`/`alloc`/`std` (and the rest of the `library/`)
/// tree that the verifier already treats as trusted TCB and hard-skips (see
/// `trust_proof_cert`'s std hard-skip: "all proofs are conditional on its
/// correctness"). Such an unsafe op is std-internal — e.g. the `vec!` macro's
/// inlined `RawVec` / `Box::new_uninit` / `assume_init`, whose span is
/// `alloc/src/macros.rs` even after the macro is expanded into a user function's
/// MIR — NOT user unsafe. So it must not be charged as a user-facing obligation.
///
/// SOUNDNESS / fail-closed: returns `true` ONLY for a span we can positively
/// identify as sysroot std. An empty file, binary provenance, or ANY first-party
/// / user path (a genuine `unsafe` block in ny-cert, etc.) returns `false`, so
/// that obligation is preserved. This never inspects obligation kind — only the
/// span.
pub(crate) fn is_trusted_std_span(span: &SourceSpan) -> bool {
    is_trusted_std_file(&span.file)
}

/// Span-file predicate for [`is_trusted_std_span`] (split out for direct unit
/// testing). Recognizes the two shapes a sysroot std source path takes in a
/// [`SourceSpan::file`]:
///   1. A `library/` path *segment* — the in-tree tree (`library/alloc/src/…`),
///      an absolute checkout (`/…/rust/library/core/src/…`), or a remapped
///      virtual path (`/rustc/<hash>/library/std/src/…`). This covers every
///      sysroot crate.
///   2. A path-prefix-remapped bare crate root that stripped the `library/`
///      prefix, e.g. the observed `alloc/src/macros.rs`, `core/src/…`,
///      `std/src/…`. Matched only as a leading `<std-crate>/src/` so no
///      first-party path (never rooted at a std crate name) can collide.
///
/// Fail-closed: an empty path or `binary:` provenance is NOT std here.
fn is_trusted_std_file(file: &str) -> bool {
    // No usable source location ⇒ cannot prove std ⇒ keep the obligation.
    if file.is_empty() || file.starts_with("binary:") {
        return false;
    }

    // Normalize separators so path-segment matching is platform-independent.
    let norm = file.replace('\\', "/");

    // The sysroot crates whose sources this gate may trust. A crate whose name
    // is not on this list is somebody else's code, wherever it happens to sit.
    const STD_CRATES: [&str; 9] = [
        "core",
        "alloc",
        "std",
        "proc_macro",
        "test",
        "panic_abort",
        "panic_unwind",
        "std_detect",
        "unwind",
    ];
    let is_std_crate_root = |rest: &str| {
        STD_CRATES
            .iter()
            .any(|krate| rest.strip_prefix(krate).is_some_and(|tail| tail.starts_with("/src/")))
    };

    // (1) The sysroot standard-library source tree: a `library/` segment
    // IMMEDIATELY followed by a known std crate and its `src/`.
    //
    // SOUNDNESS: this used to accept ANY path containing a `library/` segment.
    // That is a text test on a user-controlled value — `SourceSpan.file` is the
    // unremapped local path (`prefer_local_unconditionally`, see
    // trust-mir-extract's `convert_span`). Trusting a span here DELETES every
    // `[unsafe:sep:*]` obligation for it, and the compiler's fail-closed
    // unsafe-call net deliberately yields to this engine (`call_has_unsafe_model`
    // => `continue`), so nothing else re-covers those operations. A crate laid
    // out under `library/` is not exotic — `first-party/trust-mc` declares
    // `members = ["library/trust-mc", ...]` and that tree contains real `unsafe`
    // — so in-tree code was silently having its memory-safety obligations
    // dropped by a path substring.
    //
    // Residual, deliberately accepted and recorded rather than papered over: a
    // non-sysroot crate literally laid out as `library/core/src/...` still
    // matches. Closing that needs rustc-authenticated provenance
    // (`SourceFile::cnum` / `SourceFile::is_imported()`) carried into
    // `SourceSpan`, which is a schema change across trust-types and
    // trust-mir-extract. Narrowing to the known crate names removes every
    // trigger reachable by accident.
    if let Some(rest) =
        norm.strip_prefix("library/").or_else(|| norm.split_once("/library/").map(|(_, a)| a))
    {
        if is_std_crate_root(rest) {
            return true;
        }
    }

    // (2) Remapped bare crate root (`library/` prefix stripped). Only the known
    // sysroot crate roots, matched as a LEADING `<crate>/src/` segment.
    is_std_crate_root(&norm)
}

/// Check if a callee is an allocation function.
fn is_alloc_call(lower: &str) -> bool {
    lower.contains("alloc::alloc")
        || lower.contains("box::new")
        || lower.contains("vec::with_capacity")
        || lower.contains("vec::new")
        || lower.contains("alloc::alloc_zeroed")
        // The free fn `box_new_uninit` that `Box::<T>::new`/`new_uninit` INLINE to in
        // optimized MIR (`contains("box::new")` MISSES it: `box_new_uninit` has no
        // `box::new` substring). Recognizing it here tracks its provenance so a deref/
        // write of the boxed pointer resolves to the allocation (and, via
        // `is_known_good_box_alloc`, gets the infallible-allocator postcondition).
        || is_known_good_box_alloc(lower)
}

/// An INFALLIBLE, type-aligned box allocator: `box_new_uninit` (the free fn
/// `Box::new`/`Box::new_uninit` inline to) or `Box::new` itself. The global
/// allocator aborts on OOM — it never returns null to safe code — and returns
/// memory aligned to the `Layout`'s alignment (= the boxed type's alignment). So
/// a raw deref/write of the returned pointer is non-null, valid, aligned, and
/// writable (the [`box_alloc_postcondition`] facts). DELIBERATELY EXCLUDES the
/// fallible raw `alloc::alloc`/`alloc_zeroed` (which CAN return null — assuming
/// non-null there would false-PROVE a real null-deref) and `Vec` constructors
/// (a `Vec::new` pointer is a dangling-but-non-null sentinel into ZERO capacity,
/// not a deref-safe region). Anchored to a recognizable std box-allocator token.
fn is_known_good_box_alloc(lower: &str) -> bool {
    // `box_new_uninit` is a distinctive std-internal name (no user fn shares it);
    // require a std/alloc/core (`boxed`) origin so a same-named user item cannot
    // qualify. `Box::<T>::new` lowers with the `boxed::box` path segment.
    //
    // STRIP generic args before matching: the monomorphized METHOD form
    // `box::<[formula; 2]>::new_uninit` (the `Box::<T>::new_uninit` the `vec!` of a
    // LARGE element emits — NOT inlined to the generic-free `box_new_uninit`) has its
    // `box::new` segment SPLIT by the `<…>`, so the raw substring match misses it (the
    // `vec!` of a SMALL element inlines to `box_new_uninit`, which matched — hence the
    // discrepancy). Normalize like `total_no_panic_call_summary`. The cascading
    // false-FAILs this once exposed are now co-fixed: the `[unsafe:sep:alloc]` size
    // check is SKIPPED for an infallible box alloc (the box is type-sized), and the
    // use-after-free is fixed at the root (cleanup-block `Drop`s no longer free — see
    // `interpret_drop` + `reachable_block_ids`).
    let std_origin = lower.contains("boxed")
        || lower.starts_with("std::")
        || lower.starts_with("alloc::")
        || lower.starts_with("core::");
    if !std_origin {
        return false;
    }
    let mut without_generics = String::with_capacity(lower.len());
    let mut depth = 0usize;
    for c in lower.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => without_generics.push(c),
            _ => {}
        }
    }
    let normalized =
        without_generics.split("::").filter(|seg| !seg.is_empty()).collect::<Vec<_>>().join("::");
    // INFALLIBLE box allocators: the free `box_new_uninit`, `Box::new`, and
    // `Box::new_uninit` (`box::new` is a substring of the normalized `box::new_uninit`).
    // `Box::new_uninit` returns UNINITIALIZED memory, but the POINTER is still non-null
    // + aligned + a valid allocation (the only facts the box-good postcondition
    // asserts; initialization is the separate `assume_init` obligation).
    normalized.contains("box_new_uninit") || normalized.contains("box::new")
}

/// The non-null half of [`box_alloc_postcondition`] — an infallible box
/// allocator's result pointer is non-zero. Same SMT name (`ptr_{name}`) the
/// `[unsafe:sep:alloc]`/`deref_vc` null checks use, so conjoining it onto the
/// `ptr == 0` violation yields the UNSAT `ptr != 0 ∧ ptr == 0`.
fn box_alloc_nonnull_fact(ptr_name: &str) -> Formula {
    Formula::Not(Box::new(Formula::Eq(
        Box::new(generated_sep_var(format!("ptr_{ptr_name}"), Sort::Int)),
        Box::new(Formula::Int(0)),
    )))
}

// The individual allocator-postcondition facts are conjoined per-VC by
// `discharge_box_good` (one fact per matching violation) — see its doc-comment for
// why a single combined postcondition poisons the solver. The alignment guarantee
// (`ptr % align == 0`) is deliberately omitted: `align` is a symbolic divisor (the
// pointee alignment is not recoverable from the IR for an Adt pointee), so the
// nonlinear `ptr % align` would degrade the query; alignment stays soundly caught
// until the concrete pointee alignment is available from tcx layout.

/// Check if a callee is a container-to-raw-pointer accessor (`as_ptr` /
/// `as_mut_ptr` on a slice, array, `Vec`, etc.). The result aliases the
/// receiver's buffer, so provenance/offset propagate through it.
fn is_container_as_ptr_call(lower: &str) -> bool {
    lower.contains("::as_ptr") || lower.contains("::as_mut_ptr")
}

/// Whether the separation engine MODELS this call (lowercased name) — i.e. some
/// `interpret_call` arm handles it (emitting an obligation and/or tracking
/// provenance), so it is NOT silently ignored. Used by the compiler's
/// authoritative unsafe-call completeness check to avoid double-flagging a call
/// Trust already covers. Mirrors the `interpret_call` dispatch + the call arm of
/// `has_unsafe_patterns`.
pub(crate) fn call_is_modeled(lower: &str) -> bool {
    is_external_map_call(lower)
        || is_container_as_ptr_call(lower)
        || is_ptr_cast_call(lower)
        || is_layout_size_call(lower)
        || is_layout_passthrough_call(lower)
        || is_alloc_call(lower)
        || is_dealloc_call(lower)
        || is_realloc_call(lower)
        || is_ptr_offset_call(lower)
        || is_unchecked_index_call(lower)
        || is_raw_read_write_call(lower)
        || unsafe_assertion_op(lower).is_some()
        || is_unsafe_arith_op(lower)
        || is_unwrap_unchecked_call(lower)
        || lower.contains("ptr::copy")
        || lower.contains("from_raw_parts")
        || lower.contains("mem::transmute")
        // `core::fmt::Arguments::*` constructors (`new_v1`/`new_const`/`new_v1_formatted`) are
        // `unsafe fn`s by SIGNATURE but compiler-GENERATED by `format_args!`, which upholds their
        // only safety precondition (`pieces.len() == args.len() + 1`). They construct a value with
        // no UB and no panic, so the hardened unsafe-call boundary treats them as covered. (Actual
        // formatting — and any user `Display`/`Debug` panic — happens later in `write_fmt`.)
        || lower.contains("fmt::arguments::")
        // `from_raw_fd` (`FromRawFd::from_raw_fd` and the inherent forms on
        // `OwnedFd`/`File`/sockets): wraps an integer fd into an owning type —
        // NO memory access, no panic. Its safety precondition (fd validity +
        // sole ownership) is a resource-typestate property outside this
        // memory-safety layer's scope, mirroring the `fmt::arguments::`
        // precedent above. A non-std user fn that happens to be named
        // `from_raw_fd` is still verified independently in its own body, so
        // covering the CALL cannot false-prove any memory operation.
        || lower.contains("from_raw_fd")
        // Native-TLS lazy-init `get_or_init` — the compiler-generated, doc(hidden)
        // `thread_local!` machinery. Same compiler-generated-unsafe tier as the
        // `fmt::arguments::` precedent above (see the helper for the full argument).
        || is_native_tls_lazy_init_call(lower)
}

/// The `thread_local!`-expanded native-TLS lazy-init call
/// `std::thread::local_impl::LazyStorage::<T, {()|!}>::get_or_init::<fn() -> T {…_init_fn}>`
/// (std `sys/thread_local/native/mod.rs`; body in `native/lazy.rs`). Trust treats it
/// as COVERED for the hardened unsafe-call completeness boundary — the exact tier of
/// the `fmt::arguments::` compiler-generated-unsafe entry in `call_is_modeled`:
///
///  * It is an `unsafe fn` by SIGNATURE, whose sole safety precondition is "`self`
///    (the TLS `Storage`) stays valid until the thread's TLS destructor runs". That
///    precondition is upheld BY CONSTRUCTION by the `thread_local!` expansion, which
///    only ever calls it on the `#[thread_local] static __RUST_STD_INTERNAL_VAL`
///    that lives for the whole thread — never on a caller-supplied pointer.
///  * Its body is pure `Cell`/`UnsafeCell`/`ptr`/`MaybeUninit` state-machine work:
///    NO user-reachable UB from a safe context and NO user-reachable panic (its one
///    `unreachable!()` is the dead recursive-`State::Destroyed` arm; the driven init
///    fn `__rust_std_internal_init_fn` is a SEPARATE proof unit carrying its OWN
///    obligations — see the mirror `is_trusted_panic_free_absent_callee` discharge).
///  * `std::thread::local_impl` is `#[doc(hidden)]` and namable ONLY by the
///    `thread_local!` expansion, so NO user-authored `get_or_init` call can ride
///    this — a same-named user/`OnceLock`/`OnceCell` `get_or_init` lacks the
///    `thread::local_impl::lazystorage` module anchor and stays fail-closed.
///
/// So claiming coverage suppresses ONLY the always-refuting `[unsafe:unmodeled-call]`
/// finding on `ARENA::{constant#0}::{closure#0,1}`; it introduces no model of the
/// call's effects (this predicate is consumed only by the compiler's completeness
/// cross-check, not by `interpret_call`). Matched on the LOWERCASED def-path the
/// completeness check passes (`call_has_unsafe_model` lowercases first), and via
/// `contains` because the init-fn turbofish `::<fn() -> T {…}>` carries a `->` that
/// no bracket-balanced normalization survives — the `LazyStorage::…::get_or_init`
/// head is stable, so the anchored substrings are exact.
fn is_native_tls_lazy_init_call(lower: &str) -> bool {
    let hit = lower.contains("thread::local_impl::lazystorage") && lower.contains("::get_or_init");
    if hit && std::env::var_os("TRUST_TLS_DISCHARGE_DEBUG").is_some() {
        eprintln!(
            "TRUST_TLS_DISCHARGE_DEBUG: call_is_modeled covers native-TLS lazy-init \
             unsafe call `{lower}` — [unsafe:unmodeled-call] completeness finding \
             suppressed (compiler-generated, doc(hidden); driven init fn carries its own)"
        );
    }
    hit
}

/// Check if a callee is a raw-pointer pointee-cast METHOD (`<*mut T>::cast`,
/// `<*const T>::cast`, `cast_mut`, `cast_const`). These change only the pointee
/// type while PRESERVING the address and provenance, so tracking must survive
/// them exactly as it does an `as` pointer cast. Scoped to the raw-pointer
/// inherent-impl paths (`const_ptr`/`mut_ptr`) so it never matches unrelated
/// `cast`-named methods (e.g. enum `downcast`, `NonNull` is handled separately).
fn is_ptr_cast_call(lower: &str) -> bool {
    (lower.contains("const_ptr") || lower.contains("mut_ptr")) && lower.contains("::cast")
}

/// Check if a callee is unchecked indexing (`<[T]>::get_unchecked`,
/// `get_unchecked_mut`) — UB if the index is out of bounds, with no
/// language-inserted check, so Trust must emit the bounds obligation itself.
fn is_unchecked_index_call(lower: &str) -> bool {
    lower.contains("::get_unchecked")
}

/// UB-class ops whose safety condition is a non-arithmetic type invariant.
/// Returns `(tag, human-readable required-invariant)` for the obligation message.
fn unsafe_assertion_op(lower: &str) -> Option<(&'static str, &'static str)> {
    if lower.contains("from_utf8_unchecked") {
        Some(("from_utf8_unchecked", "the input bytes must be valid UTF-8 (the `str` invariant)"))
    } else if lower.contains("assume_init") {
        Some(("assume_init", "the value must be fully initialized before `assume_init`"))
    } else if lower.contains("from_bytes_with_nul_unchecked") {
        // `CStr::from_bytes_with_nul_unchecked`: UB unless the bytes are
        // nul-terminated with no interior nul. A buffer-shape invariant the
        // arithmetic machinery cannot express ⇒ fail-closed Unknown.
        Some((
            "from_bytes_with_nul_unchecked",
            "the input bytes must be nul-terminated with no interior nul (the `CStr` invariant)",
        ))
    } else {
        None
    }
}

/// `NonZero*::new_unchecked` / `NonNull::new_unchecked` — UB if the argument is
/// zero (resp. null), an ARITHMETIC precondition the engine models directly.
/// Scoped to the `new_unchecked` spelling; `unreachable_unchecked` and the other
/// `_unchecked` ops do not contain it.
fn is_nonzero_new_unchecked_call(lower: &str) -> bool {
    lower.contains("new_unchecked")
}

/// UB-class ops whose safety precondition is ARITHMETIC, so the engine emits a
/// real (guard-dischargeable) obligation rather than a fail-closed Unknown:
/// `NonZero*/NonNull::new_unchecked` (arg ≠ 0), `char::from_u32_unchecked`
/// (Unicode scalar value), `Vec::set_len` (new_len ≤ capacity). Mirrors the
/// dispatch arms in `interpret_call`; used by `has_unsafe_patterns` /
/// `call_is_modeled` so a function whose ONLY unsafe op is one of these is still
/// analyzed (not skipped) and is not double-flagged by the compiler's
/// completeness check.
fn is_unsafe_arith_op(lower: &str) -> bool {
    is_nonzero_new_unchecked_call(lower)
        || lower.contains("from_u32_unchecked")
        || lower.contains("set_len")
}

/// `Option/Result::unwrap_unchecked` — UB if the receiver is `None`/`Err`. A
/// non-arithmetic discriminant fact ⇒ fail-closed Unknown, emitted from the
/// `is_layout_passthrough_call` arm (which also threads tracked `Layout` sizes).
/// Recognized here so `has_unsafe_patterns` / `call_is_modeled` see it as covered.
fn is_unwrap_unchecked_call(lower: &str) -> bool {
    lower.contains("unwrap_unchecked")
}

/// Check if a callee is a raw single-element memory access via a CALL —
/// `ptr::read`, `ptr::read_volatile`, `ptr::read_unaligned`, and the `write`
/// equivalents. The dereference is hidden inside the std function (not a MIR
/// `Deref` place), so it needs its own bounds obligation. `write_bytes` (a
/// `count`-sized memset) and `copy` are handled by their own paths, not here.
fn is_raw_read_write_call(lower: &str) -> bool {
    (lower.contains("ptr::read") || lower.contains("ptr::write"))
        && !lower.contains("write_bytes")
        && !lower.contains("read_volatile_from")
}

/// Check if a callee constructs a `Layout` from an explicit byte size
/// (`Layout::from_size_align` / `…_unchecked`). The first argument is the size,
/// which — when constant — bounds any allocation made from the layout.
fn is_layout_size_call(lower: &str) -> bool {
    lower.contains("layout::from_size_align")
}

/// Check if a callee is a transparent unwrap of a `Result`/`Option`
/// (`unwrap`/`expect`/`unwrap_unchecked`). Used only to thread a tracked
/// `Layout` size through `from_size_align(...).unwrap()`; a no-op for any
/// unwrap whose argument carries no tracked size.
fn is_layout_passthrough_call(lower: &str) -> bool {
    lower.contains("::unwrap") || lower.contains("::expect") || lower.contains("unwrap_unchecked")
}

/// Check if a callee is a deallocation function.
fn is_dealloc_call(lower: &str) -> bool {
    lower.contains("alloc::dealloc") || lower.contains("drop_in_place")
}

/// Check if a callee is a reallocation function.
fn is_realloc_call(lower: &str) -> bool {
    lower.contains("alloc::realloc")
}

/// Check if a callee is a pointer-offset method (`<*const/mut T>::add`,
/// `::offset`, `::wrapping_add`, `::wrapping_offset`). These lower to a CALL,
/// not a `BinaryOp`, so the engine must route them to the offset interpreter to
/// preserve provenance and accumulate the byte offset. `::sub`/`::wrapping_sub`
/// are intentionally excluded (their operand would need negating).
fn is_ptr_offset_call(lower: &str) -> bool {
    (lower.contains("const_ptr") || lower.contains("mut_ptr"))
        && (lower.contains("::add")
            || lower.contains("::offset")
            || lower.contains("::wrapping_add")
            || lower.contains("::wrapping_offset"))
}

/// Check if a callee maps an *externally-mutable* region — an `mmap`/`memmap`
/// of a file or shared object whose size another process (or thread) can change
/// after the map is created. Name-based, like the other classifiers above. The
/// hazard: the length captured at map time is not a stable bound (truncation ⇒
/// the mapping outlives the bytes ⇒ SIGBUS / out-of-bounds read).
fn is_external_map_call(lower: &str) -> bool {
    // Unambiguous memory-map markers. These substrings already cover the real
    // call shapes — `libc::mmap`, `memmap2::MmapMut::map_mut`,
    // `aterm_scrollback::mmap::MmapMut::map_mut` all contain `mmap`/`memmap`.
    if lower.contains("mmap") || lower.contains("memmap") {
        return true;
    }
    // A bare `map_mut`/`map_shared`/`map_anon` token is NOT treated as a memory
    // map on its own: it collides with unrelated container/arena methods (e.g.
    // `evmap::ReadHandle::map_mut`), which would be wrongly flagged. It only
    // counts when an mmap-family qualifier is also present on the path — and in
    // that case the `mmap`/`memmap` check above already returned, so there is
    // intentionally no standalone `map_mut` arm here.
    false
}

/// Convert an rvalue to a formula (simplified).
fn rvalue_to_formula(rvalue: &Rvalue) -> Formula {
    match rvalue {
        Rvalue::Use(op) => operand_to_formula_simple(op),
        _ => generated_sep_var("rval", Sort::Int),
    }
}

/// Statically-known byte size of a type, when it is in the type itself
/// (sized integers, bools, and fixed arrays/tuples of those). Returns `None`
/// for types whose size is not a compile-time constant we model here.
pub(crate) fn ty_byte_size(ty: &Ty) -> Option<i128> {
    match ty {
        Ty::Bool => Some(1),
        Ty::Int { width, .. } | Ty::Float { width } | Ty::Bv(width) => Some(i128::from(*width) / 8),
        Ty::Array { elem, len } => ty_byte_size(elem).map(|e| e * i128::from(*len)),
        Ty::Tuple(elems) => elems.iter().map(ty_byte_size).sum::<Option<i128>>(),
        _ => None,
    }
}

/// Statically-known byte ALIGNMENT of a type, for the scalar types we model
/// (alignment equals size for a primitive scalar — a power of two). Composite
/// types are intentionally not modeled here, so their alignment stays fail-closed
/// (returns `None`). Used by [`SepEngine::discharge_stack_good`] to discharge a
/// stack-good deref's alignment only when the backing alignment meets the
/// requirement.
pub(crate) fn ty_byte_align(ty: &Ty) -> Option<i128> {
    match ty {
        Ty::Bool => Some(1),
        Ty::Int { width, .. } | Ty::Float { width } | Ty::Bv(width) => Some(i128::from(*width) / 8),
        _ => None,
    }
}

/// If `place` is a struct field access `(*base).field` or `base.field`, return
/// `(base_local, field_index)`. Used to tag locals that hold a field value for
/// the backing-length invariant assume.
fn field_access(place: &Place) -> Option<(usize, usize)> {
    match place.projections.as_slice() {
        [Projection::Field(i)] => Some((place.local, *i)),
        [Projection::Deref, Projection::Field(i)] => Some((place.local, *i)),
        _ => None,
    }
}

/// The MIR local an operand reads from, if it is a `Copy`/`Move` of a place.
fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
        _ => None,
    }
}

/// Scale an ELEMENT-count/offset formula to BYTES by a known element stride.
/// Identity when the stride is 1, so byte-wide (`u8`) obligations stay textually
/// `len > N` and existing proofs are unaffected; for wider pointees it becomes
/// `stride * len > N`. See [`SepEngine::operand_pointee_stride`] for why this is
/// soundness-critical.
fn scale_to_bytes(stride: i128, elems: Formula) -> Formula {
    if stride == 1 { elems } else { Formula::Mul(Box::new(Formula::Int(stride)), Box::new(elems)) }
}

/// Simplified operand-to-formula for the engine (no function context needed).
fn operand_to_formula_simple(op: &Operand) -> Formula {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            Formula::Var(format!("_{}", place.local), Sort::Int)
        }
        Operand::Constant(cv) => match cv {
            trust_types::ConstValue::Bool(b) => Formula::Bool(*b),
            trust_types::ConstValue::Int(n) => Formula::Int(*n),
            trust_types::ConstValue::Uint(n, _) => match i128::try_from(*n) {
                Ok(n) => Formula::Int(n),
                Err(_) => Formula::UInt(*n),
            },
            trust_types::ConstValue::Float(f) => {
                generated_sep_var(format!("float_{f}"), Sort::BitVec(64))
            }
            trust_types::ConstValue::Unit => Formula::Int(0),
            trust_types::ConstValue::CallableItem { def_path, kind, def_path_hash } => {
                Formula::var_owned(
                    trust_types::ConstValue::callable_smt_var_name(def_path, *kind, *def_path_hash),
                    Sort::Int,
                )
            }
            // opaque, injectively-named term for a `&str` literal.
            trust_types::ConstValue::Str { bytes } => {
                Formula::Var(trust_types::ConstValue::str_smt_var_name(bytes), Sort::Int)
            }
            _ => Formula::Var("__unknown_const".into(), Sort::Int),
        },
        Operand::Symbolic(formula) => formula.clone(),
        _ => Formula::Var("__unknown_operand".into(), Sort::Int),
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, ProofLevel, Rvalue,
        SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn empty_span() -> SourceSpan {
        SourceSpan::default()
    }

    fn formula_contains_var(formula: &Formula, name: &str) -> bool {
        matches!(formula, Formula::Var(var, _) if var == name)
            || formula.children().into_iter().any(|child| formula_contains_var(child, name))
    }

    fn make_func(
        name: &str,
        locals: Vec<LocalDecl>,
        arg_count: usize,
        blocks: Vec<BasicBlock>,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: empty_span(),
            body: VerifiableBody { return_ty: Ty::Unit, locals, arg_count, blocks },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    // ── SepEngine basic tests ─────────────────────────────────────────

    #[test]
    fn test_sep_engine_new() {
        let engine = SepEngine::new("test_fn");
        assert_eq!(engine.vc_count(), 0);
        assert_eq!(engine.func_name, "test_fn");
    }

    #[test]
    fn test_sep_engine_into_vcs_empty() {
        let engine = SepEngine::new("test_fn");
        let vcs = engine.into_vcs();
        assert!(vcs.is_empty());
    }

    // ── Pattern 1: Raw pointer deref read ─────────────────────────────

    #[test]
    fn test_raw_deref_read_generates_vcs() {
        let func = make_func(
            "deref_read",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Deref],
                    })),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // Should produce deref VCs (null, alloc, align)
        assert!(vcs.len() >= 3, "raw deref read should produce at least 3 VCs, got {}", vcs.len());
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null check")
        )));
    }

    // ── REFUTATION: tracked-source addr_of inherits a stack-good prov ──
    //
    // `q = &raw const p` where `p = &raw const x`. The source `p` is itself a
    // tracked pointer, so `interpret_address_of` takes the TRACKED-SOURCE branch
    // (1782-1783) and reuses x's stack-good provenance P for q. The new guard then
    // suppresses the source-liveness VC for `_2` (the pointer `p`) — even though
    // `p` has a StorageDead (it dangles). The discharge is licensed by x's
    // stack-goodness, NOT by p's liveness: a false-prove.
    #[test]
    fn refute_tracked_source_inherits_stack_good_prov() {
        // _0: (); _1: i32 x; _2: *const i32 p; _3: *const *const i32 q
        let func = make_func(
            "addr_of_of_ptr",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::i32()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr {
                        mutable: false,
                        pointee: Box::new(Ty::RawPtr {
                            mutable: false,
                            pointee: Box::new(Ty::i32()),
                        }),
                    },
                    name: Some("q".into()),
                },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    // _2 = &raw const _1   (x is sized i32, no StorageDead -> stack-good prov P)
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(1)),
                        span: empty_span(),
                    },
                    // _3 = &raw const _2   (TRACKED-SOURCE: src _2 is a tracked ptr)
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::AddressOf(false, Place::local(2)),
                        span: empty_span(),
                    },
                    // StorageDead(_2): the pointer `p` dangles; `q` now points to dead storage.
                    Statement::StorageDead(2),
                ],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // The source-liveness VC for the SECOND addr_of is about `_2` (the pointer
        // p). p has a StorageDead, so this obligation MUST survive (stay CAUGHT).
        let p_liveness = vcs.iter().any(|vc| {
            matches!(
                &vc.kind,
                VcKind::Assertion { message }
                    if message.contains("addr_of") && message.contains("`_2`")
            )
        });
        assert!(
            p_liveness,
            "SOUNDNESS: source-liveness VC for `_2` (a StorageDead pointer) must be \
             emitted; design suppressed it via x's inherited stack-good prov. VCs: {:?}",
            vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }

    // ── call-arg-confined addr_of: the `&mut out`-param FFI shape ──────

    /// `waitpid(pid, &mut status, 0)`: `_3 = &raw mut _2` is confined to its
    /// defining block and consumed only by that block's call terminator, with
    /// no `StorageDead(_2)` before the call — the source-liveness VC is
    /// structurally discharged (pty_fd_seam regression).
    #[test]
    fn call_arg_confined_addr_of_discharges_liveness_vc() {
        let func =
            confined_addr_of_func(/* dead_before_call = */ false, /* escapes = */ false);
        let vcs = check_sep_unsafe(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message }
                    if message.contains("addr_of") && message.contains("`_2`")
            )),
            "confined same-block call-arg addr_of must not flag source liveness. VCs: {:?}",
            vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }

    /// Fail-closed controls: a `StorageDead(src)` BETWEEN the `AddressOf` and
    /// the call, or the pointer ESCAPING into a later block, keeps the VC.
    #[test]
    fn call_arg_confined_addr_of_fails_closed_on_dead_source_or_escape() {
        for (dead, escapes) in [(true, false), (false, true)] {
            let func = confined_addr_of_func(dead, escapes);
            let vcs = check_sep_unsafe(&func);
            assert!(
                vcs.iter().any(|vc| matches!(
                    &vc.kind,
                    VcKind::Assertion { message }
                        if message.contains("addr_of") && message.contains("`_2`")
                )),
                "dead={dead} escapes={escapes}: source-liveness VC must survive. VCs: {:?}",
                vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
            );
        }
    }

    /// `_0: i32 ret; _1: i32 pid (arg); _2: i32 status; _3: *mut i32; _4: i32
    /// call dest` — block 0 takes `&raw mut _2` and calls `waitpid` with it;
    /// block 1 releases storage and returns.
    fn confined_addr_of_func(dead_before_call: bool, escapes: bool) -> VerifiableFunction {
        let mut b0_stmts = vec![
            Statement::StorageLive(3),
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::AddressOf(true, Place::local(2)),
                span: empty_span(),
            },
        ];
        if dead_before_call {
            b0_stmts.push(Statement::StorageDead(2));
        }
        let mut b1_stmts = vec![Statement::StorageDead(3), Statement::StorageDead(2)];
        if escapes {
            // The raw pointer leaks into the successor block: NOT confined.
            b1_stmts.insert(
                0,
                Statement::Assign {
                    place: Place::local(5),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                    span: empty_span(),
                },
            );
        }
        make_func(
            "confined_addr_of",
            vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("pid".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("status".into()) },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) },
                    name: None,
                },
                LocalDecl { index: 4, ty: Ty::i32(), name: None },
                LocalDecl {
                    index: 5,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::i32()) },
                    name: None,
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: b0_stmts,
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "waitpid".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Move(Place::local(3)),
                            Operand::Constant(ConstValue::Int(0)),
                        ],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                        is_foreign: true,
                        is_unsafe_sig: true,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: b1_stmts, terminator: Terminator::Return },
            ],
        )
    }

    // ── Pattern 2: Raw pointer deref write ────────────────────────────

    #[test]
    fn test_raw_deref_write_generates_vcs() {
        let func = make_func(
            "deref_write",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                    rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(42, 32))),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // Should produce deref VCs (null, alloc, align) + write permission = 4 VCs.
        // The former 5th VC -- the post-write read-over-write consistency obligation
        // `Select(Store(h, p, v), p) == v` -- was a content-free array-theory tautology
        // and was deliberately dropped (vc_gen.rs raw_write_vc), so it is no longer emitted.
        assert!(vcs.len() >= 4, "raw deref write should produce at least 4 VCs, got {}", vcs.len());
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("write permission")
        )));
    }

    // ── Pattern 3: Allocation ─────────────────────────────────────────

    #[test]
    fn test_alloc_generates_vcs() {
        let func = make_func(
            "alloc_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.len() >= 2,
            "alloc should produce at least 2 VCs (null + size), got {}",
            vcs.len()
        );
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null check")
        )));
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("size check")
        )));
    }

    // ── Pattern 4: Deallocation (Drop) ────────────────────────────────

    #[test]
    fn test_double_free_generates_vc() {
        let func = make_func(
            "double_free",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(2),
                        span: empty_span(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(3),
                        span: empty_span(),
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("double-free")
            )),
            "double drop should produce a double-free VC"
        );
    }

    // ── Pattern 5: ptr::copy_nonoverlapping ───────────────────────────

    #[test]
    fn test_ptr_copy_nonoverlapping_generates_overlap_vc() {
        let func = make_func(
            "copy_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("dst".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::copy_nonoverlapping".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("overlap")
            )),
            "copy_nonoverlapping should produce an overlap check VC"
        );
    }

    /// Trust: `copy_nonoverlapping` must now also prove the count stays within
    /// BOTH the source and destination allocations — not just non-overlap.
    /// (Closes the audited gap: previously only an overlap VC was emitted, so a
    /// count larger than the destination allocation went unflagged.)
    #[test]
    fn test_ptr_copy_generates_allocation_bounds_vcs() {
        let func = make_func(
            "copy_bounds_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("dst".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::copy_nonoverlapping".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let dst = vcs.iter().find(|vc| {
            matches!(&vc.kind, VcKind::CopyBoundsViolation { direction, .. } if direction == "dst")
        });
        let src = vcs.iter().find(|vc| {
            matches!(&vc.kind, VcKind::CopyBoundsViolation { direction, .. } if direction == "src")
        });
        assert!(dst.is_some(), "copy must emit a destination-bounds obligation");
        assert!(src.is_some(), "copy must emit a source-bounds obligation");
        // The obligation must be non-trivial: it relates the copy count to the
        // allocation size (`ptr + count > base + size`), not a constant.
        let dst = dst.unwrap();
        let copy_count = crate::separation_logic::generated_symbol("copy_count");
        let copy_dst_size = crate::separation_logic::generated_symbol("copy_dst_size");
        assert!(
            formula_contains_var(&dst.formula, &copy_count)
                && formula_contains_var(&dst.formula, &copy_dst_size),
            "dst bounds obligation must relate copy_count to the destination size, got {:?}",
            dst.formula
        );
        assert_eq!(dst.kind.proof_level(), ProofLevel::L0Safety);
    }

    /// Trust: a memory map of an externally-mutable region (mmap of a file)
    /// emits an `ExternallyMutableAllocationBounds` obligation — the captured
    /// mapped length is not a stable bound (a concurrent truncation ⇒ SIGBUS).
    #[test]
    fn test_mmap_call_generates_external_mutable_bounds_vc() {
        let func = make_func(
            "mmap_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("map".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "aterm_scrollback::mmap::MmapMut::map_mut".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let ext = vcs.iter().find(|vc| {
            matches!(&vc.kind, VcKind::ExternallyMutableAllocationBounds { allocation_kind, .. }
                if allocation_kind == "mmap_file")
        });
        assert!(
            ext.is_some(),
            "an mmap of an externally-mutable region must emit an ExternallyMutableAllocationBounds obligation"
        );
        let ext = ext.unwrap();
        // The violation is `mapped_len > live_size`: a Gt whose right side is the
        // external live-size var, and whose left side is the allocation's tracked
        // size var (shared with offset/deref obligations over this provenance).
        assert!(
            matches!(&ext.formula, Formula::Gt(_, _)),
            "external-mutable obligation must be a `mapped_len > live_size` comparison, got {:?}",
            ext.formula
        );
        assert!(
            formula_contains_var(
                &ext.formula,
                &crate::separation_logic::generated_symbol("map_1_live_size"),
            ),
            "the obligation must reference the live backing size, got {:?}",
            ext.formula
        );
        assert_eq!(ext.kind.proof_level(), ProofLevel::L0Safety);
    }

    /// Trust: a *non-mmap* `.map_mut()` (e.g. a container/arena method) must NOT
    /// be misclassified as an externally-mutable memory map — the classifier
    /// requires an mmap-family qualifier, so bare `map_mut` does not match.
    #[test]
    fn test_unrelated_map_mut_is_not_external_mutable() {
        let func = make_func(
            "arena_map_mut_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("slot".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "my_arena::Slot::map_mut".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            !vcs.iter()
                .any(|vc| matches!(&vc.kind, VcKind::ExternallyMutableAllocationBounds { .. })),
            "a non-mmap `.map_mut()` must not be flagged as an externally-mutable map"
        );
    }

    /// Trust: a *normal* heap allocation must NOT be flagged as
    /// externally-mutable — the new obligation is precise, not a flood.
    #[test]
    fn test_plain_alloc_has_no_external_mutable_bounds_vc() {
        let func = make_func(
            "alloc_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("p".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "alloc::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            !vcs.iter()
                .any(|vc| matches!(&vc.kind, VcKind::ExternallyMutableAllocationBounds { .. })),
            "a plain alloc must not be flagged as externally-mutable"
        );
    }

    /// Trust: `slice::from_raw_parts` now emits a real bounds obligation
    /// (`len > alloc_size`), replacing the vacuous `len < 0` check that could
    /// never catch anything for `usize` lengths.
    #[test]
    fn test_from_raw_parts_emits_real_bounds_obligation() {
        let vcs = crate::separation_logic::unsafe_fn_call_sep_vc(
            "build_slice",
            "core::slice::from_raw_parts",
            &empty_span(),
        );
        let bounds = vcs.iter().find(|vc| {
            matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
        });
        assert!(
            bounds.is_some(),
            "from_raw_parts must emit a CopyBoundsViolation obligation, got kinds {:?}",
            vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
        );
        let bounds = bounds.unwrap();
        // Must relate len to the allocation size, and must NOT be the old
        // vacuous `len < 0` form.
        let fallback_len =
            crate::separation_logic::generated_symbol("len_core_slice_from_raw_parts");
        let fallback_size =
            crate::separation_logic::generated_symbol("alloc_size_core_slice_from_raw_parts");
        assert!(
            formula_contains_var(&bounds.formula, &fallback_len)
                && formula_contains_var(&bounds.formula, &fallback_size),
            "obligation must relate len to alloc_size, got {:?}",
            bounds.formula
        );
        assert!(
            !matches!(&bounds.formula, Formula::Lt(_, b) if matches!(**b, Formula::Int(0))),
            "must not be the vacuous len < 0 obligation"
        );
    }

    /// Trust: `slice::from_raw_parts` routed through the ENGINE (not just the
    /// standalone helper) must emit the CopyBoundsViolation — this is what fires
    /// in a real compile via interpret_call.
    #[test]
    fn test_from_raw_parts_via_engine_emits_bounds_vc() {
        let func = make_func(
            "make_slice",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("s".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::slice::from_raw_parts".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))),
            "from_raw_parts via the engine must emit a CopyBoundsViolation, got {:?}",
            vcs.iter().map(|vc| vc.kind.description()).collect::<Vec<_>>()
        );
    }

    /// Trust: when from_raw_parts' pointer traces to a tracked allocation, the
    /// bounds obligation is anchored to the REAL `len` operand and the
    /// allocation's provenance size variable — not isolated symbolic vars — so a
    /// surrounding guard can discharge it.
    #[test]
    fn test_from_raw_parts_wires_real_len_and_provenance() {
        let func = make_func(
            "slice_from_alloc",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                // `p` is a real raw pointer (alloc returns `*mut u8`); a bare-int
                // pointer fixture would be unrealistic and dodge the stride path.
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("len".into()) },
            ],
            0,
            vec![
                // _1 = alloc(...)  -> _1 gets tracked provenance
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "alloc::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                // _0 = from_raw_parts(move _1, copy _2)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
            })
            .expect("from_raw_parts must emit a CopyBoundsViolation");
        // The obligation references the REAL len operand by the PIPELINE name
        // (`len`, the local's declared name — matching place_to_var_name so guards
        // and defs over `len` connect), not a synthetic placeholder.
        assert!(
            formula_contains_var(&bounds.formula, "len"),
            "obligation must use the real `len` operand by name, got {:?}",
            bounds.formula
        );
        assert!(
            !formula_contains_var(
                &bounds.formula,
                &crate::separation_logic::generated_symbol("len_core_slice_from_raw_parts"),
            ),
            "obligation must NOT fall back to the synthetic len var, got {:?}",
            bounds.formula
        );
        assert!(
            matches!(&bounds.formula, Formula::Gt(_, _)),
            "obligation must be `len > size`, got {:?}",
            bounds.formula
        );
    }

    /// Trust: copy_nonoverlapping into a FIXED-SIZE array destination emits its
    /// destination-bounds obligation against the CONCRETE array size and the
    /// REAL count operand (`count > 64`), so a `count <= 64` guard discharges it
    /// — the same provable chain as from_raw_parts, extended to the other HIGH-2
    /// pattern (raw bulk copy).
    #[test]
    fn test_copy_nonoverlapping_into_fixed_array_uses_concrete_size() {
        let func = make_func(
            "copy_into_array",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("dst".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("src".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("count".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(true, Place::local(1)),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::copy_nonoverlapping".to_string(),
                        // (src, dst, count)
                        args: vec![
                            Operand::Copy(Place::local(3)),
                            Operand::Move(Place::local(2)),
                            Operand::Copy(Place::local(4)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let dst = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { direction, .. }
                if direction == "dst")
            })
            .expect("copy must emit a destination-bounds obligation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        assert!(
            contains_int(&dst.formula, 64) && formula_contains_var(&dst.formula, "count"),
            "dst obligation must be `count > 64` (concrete size + named count), got {:?}",
            dst.formula
        );
    }

    /// Trust (regression lock): a `from_raw_parts` over `buf.add(start)` — where
    /// `.add` is a CALL (`std::ptr::const_ptr::add`) — must carry the OFFSET-AWARE
    /// concrete obligation `start + 64-size`, i.e. `Gt(Add(start, len), 64)`, not
    /// the symbolic fallback. This protects the ptr::add-call routing + offset
    /// tracking + concrete-size + pipeline-naming chain that makes guarded offset
    /// slices prove. (See examples/unsafe-coverage/offset_slice_soundness.rs.)
    #[test]
    fn test_from_raw_parts_over_offset_array_is_offset_aware_concrete() {
        let func = make_func(
            "slice_offset_array",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("base".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("start".into()),
                },
                LocalDecl {
                    index: 5,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            0,
            vec![
                // _2 = &raw const buf
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(1)),
                        span: empty_span(),
                    }],
                    // _3 = const_ptr::add(move _2, copy start)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::const_ptr::<impl *const u8>::add".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Copy(Place::local(4))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                // _0 = from_raw_parts(copy _3, copy len)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(5))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
            })
            .expect("from_raw_parts must emit a CopyBoundsViolation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        // Offset-aware concrete obligation: references the real `start` offset,
        // the real `len`, AND the concrete size 64 — NOT the symbolic fallback.
        assert!(
            formula_contains_var(&bounds.formula, "start")
                && formula_contains_var(&bounds.formula, "len")
                && contains_int(&bounds.formula, 64),
            "obligation must be offset-aware concrete (start + len > 64), got {:?}",
            bounds.formula
        );
        assert!(
            !formula_contains_var(
                &bounds.formula,
                &crate::separation_logic::generated_symbol("alloc_size_core_slice_from_raw_parts",),
            ),
            "obligation must NOT be the symbolic fallback, got {:?}",
            bounds.formula
        );
    }

    /// Trust: a `from_raw_parts(p, len)` over a pointer from
    /// `alloc(Layout::from_size_align(64, 1).unwrap())` uses the CONCRETE layout
    /// size 64 in its bounds obligation — threading the size through the
    /// `const cap` local, the layout constructor, and the `unwrap`. This is the
    /// static-size analog of the dynamic mmap `self.len` class: a guard
    /// `len <= 64` discharges `len > 64`. Without this link the obligation would
    /// use the unbindable symbolic `prov_N_size` and never prove.
    /// SKEPTIC PROBE (local_to_ptr residual): a concrete 64-byte alloc is
    /// tracked to `_1`, copied into `_2`, then `_2` is REASSIGNED to an
    /// untracked pointer `_6`. A later `from_raw_parts(_2, len)` must NOT be
    /// sized by the stale 64-byte allocation. If `local_to_ptr[_2]` survives
    /// the reassignment, the concrete path fires and the obligation carries
    /// `64` (unsound: it describes the wrong, now-unrelated pointer). Correct
    /// behavior is the symbolic fail-closed fallback (no concrete 64).
    #[test]
    fn test_skeptic_stale_local_to_ptr_after_reassignment() {
        let func = make_func(
            "slice_from_reassigned_ptr",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p1".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p2".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("cap".into()),
                },
                LocalDecl { index: 5, ty: Ty::Unit, name: Some("layout".into()) },
                LocalDecl {
                    index: 6,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("other".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(
                            64, 64,
                        ))),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::alloc::layout::Layout::from_size_align_unchecked".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(4)),
                            Operand::Constant(trust_types::ConstValue::Uint(1, 64)),
                        ],
                        dest: Place::local(5),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "alloc::alloc::alloc".to_string(),
                        args: vec![Operand::Move(Place::local(5))],
                        dest: Place::local(1),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        // _2 = copy _1   => local_to_ptr[_2] = alloc (concrete 64)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: empty_span(),
                        },
                        // _2 = move _6   (p2 = other; UNTRACKED, different alloc)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Move(Place::local(6))),
                            span: empty_span(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Copy(Place::local(2)), Operand::Copy(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(3)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs.iter().find(|vc| {
            matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
            if callee.contains("from_raw_parts"))
        });
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        if let Some(vc) = bounds {
            assert!(
                !contains_int(&vc.formula, 64),
                "STALE local_to_ptr SURVIVED: from_raw_parts over a reassigned \
                 pointer was sized by the old 64-byte allocation. formula = {:?}",
                vc.formula
            );
        }
    }

    #[test]
    fn test_from_raw_parts_over_layout_alloc_uses_concrete_size() {
        let func = make_func(
            "slice_from_layout_alloc",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("cap".into()),
                },
                LocalDecl { index: 4, ty: Ty::Unit, name: Some("layout_res".into()) },
                LocalDecl { index: 5, ty: Ty::Unit, name: Some("layout".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    // let cap = 64;
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(trust_types::ConstValue::Uint(
                            64, 64,
                        ))),
                        span: empty_span(),
                    }],
                    // _4 = Layout::from_size_align(copy cap, const 1)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::alloc::layout::Layout::from_size_align".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(3)),
                            Operand::Constant(trust_types::ConstValue::Uint(1, 64)),
                        ],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    // _5 = Result::unwrap(move _4)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::result::Result::<T, E>::unwrap".to_string(),
                        args: vec![Operand::Move(Place::local(4))],
                        dest: Place::local(5),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    // _1 = alloc::alloc(move _5)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "alloc::alloc::alloc".to_string(),
                        args: vec![Operand::Move(Place::local(5))],
                        dest: Place::local(1),
                        target: Some(BlockId(3)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![],
                    // _0 = from_raw_parts(copy _1, copy len)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(4)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
            })
            .expect("from_raw_parts must emit a CopyBoundsViolation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        fn mentions_size_var(f: &Formula) -> bool {
            matches!(f, Formula::Var(v, _) if v.contains("_size"))
                || f.children().into_iter().any(mentions_size_var)
        }
        assert!(
            contains_int(&bounds.formula, 64) && formula_contains_var(&bounds.formula, "len"),
            "obligation must use the concrete layout size 64 and the real `len`, got {:?}",
            bounds.formula
        );
        assert!(
            !mentions_size_var(&bounds.formula),
            "obligation must NOT fall back to the unbindable symbolic size var, got {:?}",
            bounds.formula
        );
    }

    /// Trust (regression lock): copy_nonoverlapping into `buf.add(off)` carries
    /// the OFFSET-AWARE concrete dst obligation `Gt(Add(off, count), 64)` — real
    /// offset, real count, concrete size — not the symbolic fallback. Parallel to
    /// the from_raw_parts offset lock, protecting the copy side of the chain.
    #[test]
    fn test_copy_into_offset_array_is_offset_aware_concrete() {
        let func = make_func(
            "copy_offset_array",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("base".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("dst".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("off".into()),
                },
                LocalDecl {
                    index: 5,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("src".into()),
                },
                LocalDecl {
                    index: 6,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("count".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(true, Place::local(1)),
                        span: empty_span(),
                    }],
                    // _3 = mut_ptr::add(move _2, copy off)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::mut_ptr::<impl *mut u8>::add".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Copy(Place::local(4))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    // copy_nonoverlapping(src, dst=_3, count)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::copy_nonoverlapping".to_string(),
                        args: vec![
                            Operand::Copy(Place::local(5)),
                            Operand::Move(Place::local(3)),
                            Operand::Copy(Place::local(6)),
                        ],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let dst = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { direction, .. }
                if direction == "dst")
            })
            .expect("copy must emit a destination-bounds obligation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        assert!(
            formula_contains_var(&dst.formula, "off")
                && formula_contains_var(&dst.formula, "count")
                && contains_int(&dst.formula, 64),
            "dst obligation must be offset-aware concrete (off + count > 64), got {:?}",
            dst.formula
        );
    }

    /// Trust (SOUNDNESS regression lock): from_raw_parts::<u32> over a `[u8; 64]`
    /// must scale the ELEMENT count by the pointee stride (4) before comparing to
    /// the BYTE allocation size: the obligation is `4 * len > 64` (len > 16), NOT
    /// `len > 64`. Without scaling, a `len <= 64` guard would falsely discharge a
    /// 256-byte read from a 64-byte buffer (a 192-byte OOB read) — the critical
    /// unsound false-discharge an adversarial audit found and this fix closes.
    #[test]
    fn test_from_raw_parts_wider_pointee_scales_to_bytes() {
        let func = make_func(
            "slice_u32_over_u8_array",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                // *const u32 over the [u8;64] buffer — stride 4.
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(1)),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Copy(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
            })
            .expect("from_raw_parts must emit a CopyBoundsViolation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        fn contains_mul(f: &Formula) -> bool {
            matches!(f, Formula::Mul(_, _)) || f.children().into_iter().any(contains_mul)
        }
        // Must scale by stride 4 (a Mul by 4) and still bound by the 64-byte size.
        assert!(
            contains_mul(&bounds.formula)
                && contains_int(&bounds.formula, 4)
                && contains_int(&bounds.formula, 64)
                && formula_contains_var(&bounds.formula, "len"),
            "obligation must be `4 * len > 64` (stride-scaled), got {:?}",
            bounds.formula
        );
        // SOUNDNESS: it must NOT be the unscaled `len > 64`, which a `len <= 64`
        // guard would falsely discharge.
        let unscaled = Formula::Gt(
            Box::new(Formula::Add(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(64)),
        );
        assert_ne!(
            bounds.formula, unscaled,
            "obligation must NOT be the unsound unscaled `len > 64`"
        );
    }

    /// Trust: provenance survives the real `buf.as_ptr() as *const u32` chain
    /// (`&buf` → unsize `&[u8]` → `as_ptr` CALL → `PtrToPtr` cast), so the
    /// `from_raw_parts` obligation reaches the CONCRETE stride-scaled form
    /// (`4 * len > 64`) instead of the symbolic fail-closed fallback. This closes
    /// the provenance-through-cast-chain completeness gap an end-to-end run
    /// surfaced — and proves it via the concrete path, not the symbolic one.
    #[test]
    fn test_provenance_survives_as_ptr_cast_chain() {
        let func = make_func(
            "slice_via_as_ptr_chain",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("p3".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p4".into()),
                },
                LocalDecl {
                    index: 5,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                    },
                    name: Some("s5".into()),
                },
                LocalDecl {
                    index: 6,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 64 }),
                    },
                    name: Some("r6".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // _6 = &_1
                        Statement::Assign {
                            place: Place::local(6),
                            rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                            span: empty_span(),
                        },
                        // _5 = move _6 as &[u8] (Unsize)
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::Cast(Operand::Move(Place::local(6)), Ty::Unit),
                            span: empty_span(),
                        },
                    ],
                    // _4 = <[u8]>::as_ptr(move _5)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::<impl [u8]>::as_ptr".to_string(),
                        args: vec![Operand::Move(Place::local(5))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        // _3 = move _4 as *const u32 (PtrToPtr)
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Cast(Operand::Move(Place::local(4)), Ty::Unit),
                            span: empty_span(),
                        },
                    ],
                    // _0 = from_raw_parts(copy _3, copy len)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
            })
            .expect("from_raw_parts must emit a CopyBoundsViolation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        fn contains_mul(f: &Formula) -> bool {
            matches!(f, Formula::Mul(_, _)) || f.children().into_iter().any(contains_mul)
        }
        fn mentions_alloc_fallback(f: &Formula) -> bool {
            matches!(f, Formula::Var(v, _) if v.contains("alloc_size") || v.contains("_size"))
                || f.children().into_iter().any(mentions_alloc_fallback)
        }
        // Concrete stride path reached through the whole cast chain.
        assert!(
            contains_mul(&bounds.formula)
                && contains_int(&bounds.formula, 4)
                && contains_int(&bounds.formula, 64)
                && formula_contains_var(&bounds.formula, "len"),
            "provenance must survive the as_ptr/cast chain to the concrete `4 * len > 64`, got {:?}",
            bounds.formula
        );
        assert!(
            !mentions_alloc_fallback(&bounds.formula),
            "must NOT be the symbolic fail-closed fallback, got {:?}",
            bounds.formula
        );
    }

    /// Trust (relational invariant, establish side): constructing a struct that
    /// declares a backing-length invariant `(ptr_field=0, len_field=1)` emits an
    /// obligation that the pointer field's allocation is at least the length
    /// field — `size < len` (violation form). This is the SOUND foundation that
    /// lets a later `from_raw_parts(self.ptr.add(..), ..)` ASSUME the invariant:
    /// every constructor must establish it. Here a 32-byte allocation backing a
    /// claimed len of 64 yields `32 < 64`, which is correctly NOT dischargeable.
    #[test]
    fn test_backing_invariant_establish_obligation_at_construction() {
        use trust_types::AggregateKind;
        let func = make_func(
            "construct_s",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 32 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(true, Place::local(1)),
                        span: empty_span(),
                    },
                    // _0 = S { ptr: move _2, len: const 64 }
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt { name: "S".into(), variant: 0, active_field: None, args: None },
                            vec![
                                Operand::Move(Place::local(2)),
                                Operand::Constant(trust_types::ConstValue::Uint(64, 64)),
                            ],
                        ),
                        span: empty_span(),
                    },
                ],
                terminator: Terminator::Return,
            }],
        );

        // Drive the engine directly with the backing descriptor (0 -> 1).
        let mut engine = SepEngine::new(&func.name)
            .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect())
            .with_local_names(func.body.locals.iter().map(|l| l.name.clone()).collect())
            .with_field_backing(vec![(0, 1)]);
        let span = empty_span();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                engine.interpret_statement(stmt, &span);
            }
            engine.interpret_terminator(&block.terminator);
        }
        let vcs = engine.into_vcs();
        let est = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:backing]"))
            })
            .expect("construction must emit a backing-invariant establish obligation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        assert!(
            matches!(&est.formula, Formula::Lt(_, _)),
            "establish obligation must be `size < len`, got {:?}",
            est.formula
        );
        assert!(
            contains_int(&est.formula, 32) && contains_int(&est.formula, 64),
            "establish obligation must relate alloc size 32 to claimed len 64, got {:?}",
            est.formula
        );
    }

    /// Trust: the backing-invariant auto-detector picks the unambiguous
    /// buffer+length shape (one raw-pointer field, one unsigned-int field) and
    /// declines ambiguous structs — so opt-in detection stays conservative.
    #[test]
    fn test_detect_field_backing_conservative() {
        let mmap = make_func(
            "as_slice",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Adt { adt_kind: None, layout: None, 
                            variants: Vec::new(),
                            name: "MmapMut".into(),
                            fields: vec![
                                (
                                    "ptr".into(),
                                    Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                                ),
                                ("len".into(), Ty::Int { width: 64, signed: false }),
                            ],
                            disc_index_safe: false,
                            faithful_enum_repr: None, enum_layout: None, }),
                    },
                    name: Some("self".into()),
                },
            ],
            1,
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        );
        assert_eq!(detect_field_backing(&mmap), vec![(0, 1)]);

        // Two pointer fields ⇒ ambiguous ⇒ no backing.
        let ambiguous = make_func(
            "x",
            vec![LocalDecl {
                index: 0,
                ty: Ty::Adt { adt_kind: None, layout: None, 
                    variants: Vec::new(),
                    name: "X".into(),
                    fields: vec![
                        ("a".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                        ("b".into(), Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) }),
                        ("n".into(), Ty::Int { width: 64, signed: false }),
                    ],
                    disc_index_safe: false,
                    faithful_enum_repr: None, enum_layout: None, },
                name: None,
            }],
            0,
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
        );
        assert!(detect_field_backing(&ambiguous).is_empty());
    }

    /// Trust (relational invariant, end-to-end establish): an `mmap`-backed
    /// struct `Self { ptr: mmap(.., len, ..), len }` PROVES its backing-invariant
    /// establish obligation — `size(mmap) == len`, so the obligation is
    /// `len < len` (UNSAT). This is the link that lets aterm's `map_mut`
    /// construction discharge, completing the proof chain with the assume side.
    #[test]
    fn test_mmap_backed_struct_establish_obligation_discharges() {
        use trust_types::AggregateKind;
        let func = make_func(
            "map_mut",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("mapped".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    // _2 = libc::mmap(null, len, prot, flags, fd, off)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: true,
                        func: "libc::mmap".to_string(),
                        args: vec![
                            Operand::Constant(trust_types::ConstValue::Int(0)),
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(trust_types::ConstValue::Int(3)),
                            Operand::Constant(trust_types::ConstValue::Int(1)),
                            Operand::Constant(trust_types::ConstValue::Int(7)),
                            Operand::Constant(trust_types::ConstValue::Int(0)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    // _0 = S { ptr: move _2, len: copy _1 }
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt { name: "S".into(), variant: 0, active_field: None, args: None },
                            vec![Operand::Move(Place::local(2)), Operand::Copy(Place::local(1))],
                        ),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
        );

        let mut engine = SepEngine::new(&func.name)
            .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect())
            .with_local_names(func.body.locals.iter().map(|l| l.name.clone()).collect())
            .with_field_backing(vec![(0, 1)]);
        let span = empty_span();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                engine.interpret_statement(stmt, &span);
            }
            engine.interpret_terminator(&block.terminator);
        }
        let vcs = engine.into_vcs();
        let est = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:backing]"))
            })
            .expect("construction must emit a backing-invariant establish obligation");
        // `size(mmap) == len` and claimed `len` are the same variable, so the
        // obligation is `len < len` — UNSAT, i.e. PROVABLE.
        assert_eq!(
            est.formula,
            Formula::Lt(
                Box::new(Formula::Var("len".into(), Sort::Int)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            ),
            "mmap-backed establish obligation must be `len < len` (provable), got {:?}",
            est.formula
        );
    }

    /// Trust: an mmap call emits a `VcKind::Temporal` carrying the sound
    /// mmap-truncation state machine when the temporal model is enabled, so `ty`
    /// can model-check the hazard end-to-end.
    #[test]
    fn test_mmap_emits_temporal_obligation_when_enabled() {
        let func = make_func(
            "open_map",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: true,
                        func: "libc::mmap".to_string(),
                        args: vec![
                            Operand::Constant(trust_types::ConstValue::Int(0)),
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(trust_types::ConstValue::Int(3)),
                            Operand::Constant(trust_types::ConstValue::Int(1)),
                            Operand::Constant(trust_types::ConstValue::Int(7)),
                            Operand::Constant(trust_types::ConstValue::Int(0)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let mut engine = SepEngine::new(&func.name)
            .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect())
            .with_local_names(func.body.locals.iter().map(|l| l.name.clone()).collect())
            .with_temporal_mmap(true, false);
        let span = empty_span();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                engine.interpret_statement(stmt, &span);
            }
            engine.interpret_terminator(&block.terminator);
        }
        let vcs = engine.into_vcs();
        let temporal = vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::Temporal { machine: Some(_), .. }))
            .expect("mmap must emit a temporal obligation with a state machine when enabled");
        let VcKind::Temporal { property, machine: Some(md) } = &temporal.kind else {
            unreachable!()
        };
        assert_eq!(property, "AG !bad");
        assert!(
            md.states.iter().any(|s| s == "BadAccess"),
            "the mmap model must include the stale-access bad state (default = truncatable)"
        );
    }

    /// Trust (relational invariant, ASSUME side): `as_slice(&self)` doing
    /// `from_raw_parts(self.ptr, self.len)` over a struct with backing `(0, 1)`
    /// models the pointer field's allocation size as the sibling length field —
    /// so the obligation is `self.len > self.len` (UNSAT ⇒ provable), the dual of
    /// the construction-establish obligation. The size and the length must be the
    /// SKEPTIC REPRO: reassign the ptr local from an UNRELATED, untracked
    /// pointer between the field-load and `from_raw_parts`. The stale
    /// `field_loads[_2] = (self, ptr_field)` tag must NOT survive to model the
    /// new allocation's size as `self.len`. If it does, genuinely-unsafe OOB
    /// code is falsely discharged (`0 + len > len` UNSAT).
    #[test]
    fn test_skeptic_stale_field_load_tag_after_reassignment() {
        let func = make_func(
            "as_slice_reassigned",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Unit) },
                    name: Some("self".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                // _4 = an UNRELATED raw pointer into a DIFFERENT allocation.
                LocalDecl {
                    index: 4,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("other".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // _2 = (*self).0   (ptr field)  => field_loads[_2] = (1,0)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(0)],
                            })),
                            span: empty_span(),
                        },
                        // _3 = (*self).1   (len field)
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(1)],
                            })),
                            span: empty_span(),
                        },
                        // _2 = move _4   (p = other_ptr; UNTRACKED, different alloc)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Move(Place::local(4))),
                            span: empty_span(),
                        },
                    ],
                    // _0 = from_raw_parts(move _2, move _3)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let mut engine = SepEngine::new(&func.name)
            .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect())
            .with_local_names(func.body.locals.iter().map(|l| l.name.clone()).collect())
            .with_field_backing(vec![(0, 1)]);
        let span = empty_span();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                engine.interpret_statement(stmt, &span);
            }
            engine.interpret_terminator(&block.terminator);
        }
        let vcs = engine.into_vcs();
        // Find the backing-assume obligation, if it (unsoundly) fired.
        let backing = vcs.iter().find(|vc| {
            matches!(&vc.kind, VcKind::CopyBoundsViolation { detail, .. }
            if detail.contains("backing field"))
        });
        if let Some(vc) = backing {
            // If the stale tag survived, the formula is `Gt(Add(0, len), len)`
            // i.e. `0 + len > len` (UNSAT = falsely discharged for OOB code).
            if let Formula::Gt(extent, size) = &vc.formula {
                let stale = matches!(&**size, Formula::Var(v, _) if v == "len")
                    && formula_contains_var(extent, "len");
                assert!(
                    !stale,
                    "STALE TAG SURVIVED: backing assume modeled the reassigned \
                     pointer's size as self.len. formula = {:?}",
                    vc.formula
                );
            }
        }
    }

    /// The backing ASSUME for `from_raw_parts(self.ptr, self.len)` must bound the
    /// extent against a DISTINCT opaque allocation-size symbol — never against
    /// `self.len` itself. Binding to `self.len` would yield `len > len` (UNSAT)
    /// and discharge `as_slice` for free with no verified establish (the old
    /// unsoundness). The obligation is fail-closed (CAUGHT) until interprocedural
    /// struct-invariant threading supplies `alloc_size >= self.len`.
    #[test]
    fn test_backing_invariant_assume_is_fail_closed_for_as_slice() {
        let func = make_func(
            "as_slice",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::Unit) },
                    name: Some("self".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // _2 = (*self).0   (ptr field)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(0)],
                            })),
                            span: empty_span(),
                        },
                        // _3 = (*self).1   (len field)
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(1)],
                            })),
                            span: empty_span(),
                        },
                    ],
                    // _0 = from_raw_parts(move _2, move _3)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let mut engine = SepEngine::new(&func.name)
            .with_local_tys(func.body.locals.iter().map(|l| l.ty.clone()).collect())
            .with_local_names(func.body.locals.iter().map(|l| l.name.clone()).collect())
            .with_field_backing(vec![(0, 1)]);
        let span = empty_span();
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                engine.interpret_statement(stmt, &span);
            }
            engine.interpret_terminator(&block.terminator);
        }
        let vcs = engine.into_vcs();
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { detail, .. }
                if detail.contains("backing field"))
            })
            .expect("from_raw_parts over a backing field must use the assume obligation");
        // The obligation must be `Gt(extent, size)` where the extent uses the
        // `len` field but the SIZE is a DISTINCT opaque allocation-size symbol,
        // NOT `len`. That makes the VC fail-closed (`(0+len) > alloc_size` is not
        // identically false), so it cannot discharge without a verified establish.
        let Formula::Gt(extent, size) = &bounds.formula else {
            panic!("expected `extent > size`, got {:?}", bounds.formula)
        };
        assert_eq!(
            **size,
            generated_sep_var("backing_alloc_size_1_0", Sort::Int),
            "size must be a DISTINCT opaque allocation-size symbol, got {size:?}"
        );
        assert_ne!(
            **size,
            Formula::Var("len".into(), Sort::Int),
            "regression: binding size to `self.len` reintroduces the free discharge"
        );
        assert!(
            formula_contains_var(extent, "len"),
            "extent must still use the `len` field, got {extent:?}"
        );
    }

    /// Trust (SOUNDNESS lock): `get_unchecked(i)` indexes by ELEMENT, so its
    /// bound is the element COUNT, not the byte size. Over a `[u32; 8]` the
    /// obligation must be `i >= 8` (count), NOT `i >= 32` (bytes) — the latter
    /// would unsoundly permit `i` in `8..32`, a 96-byte out-of-bounds read. This
    /// is the same element-vs-byte trap that bit `from_raw_parts`.
    #[test]
    fn test_get_unchecked_bounds_by_element_count_not_bytes() {
        let func = make_func(
            "uc32",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Array { elem: Box::new(Ty::u32()), len: 8 }),
                    },
                    name: Some("arr".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::<impl [u32]>::get_unchecked".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let bounds = check_sep_unsafe(&func)
            .into_iter()
            .find(|vc| matches!(&vc.kind, VcKind::IndexOutOfBounds))
            .expect("get_unchecked must emit IndexOutOfBounds");
        assert_eq!(
            bounds.formula,
            Formula::Ge(
                Box::new(Formula::Var("i".into(), Sort::Int)),
                Box::new(Formula::Int(8)), // element COUNT — NOT 32 bytes
            ),
            "get_unchecked over [u32;8] must bound by element count 8, not byte size, got {:?}",
            bounds.formula
        );
    }

    /// Trust (SOUNDNESS lock): `ptr::read::<u32>(p)` over a 2-BYTE allocation must
    /// be CAUGHT — it reads `size_of::<u32>() == 4` bytes, so the obligation is
    /// `0 + 4 > 2` (a 2-byte OOB read), which is SAT (not provable). Verifies the
    /// raw-access obligation uses the pointee BYTE size, not an element count.
    #[test]
    fn test_ptr_read_wider_type_over_small_alloc_is_caught() {
        let func = make_func(
            "rd_u32",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 2 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p8".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("p32".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::AddressOf(false, Place::local(1)),
                            span: empty_span(),
                        },
                        // _3 = _2 as *const u32 (PtrToPtr) — provenance propagates
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Cast(Operand::Move(Place::local(2)), Ty::Unit),
                            span: empty_span(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::ptr::read".to_string(),
                        args: vec![Operand::Copy(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let bounds = check_sep_unsafe(&func)
            .into_iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { detail, .. }
                if detail.contains("raw read/write"))
            })
            .expect("ptr::read must emit a raw read/write bounds obligation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        // `0 + 4 > 2`: the u32 read (4 bytes) vs the 2-byte allocation.
        assert!(
            contains_int(&bounds.formula, 4) && contains_int(&bounds.formula, 2),
            "ptr::read::<u32> over [u8;2] must bound 4 bytes against 2, got {:?}",
            bounds.formula
        );
    }

    /// Trust (unsafe-op completeness): `str::from_utf8_unchecked` emits a
    /// fail-closed obligation that NAMES the required invariant (valid UTF-8), so
    /// the UB-class op is always caught — previously it had no specific
    /// obligation. (`MaybeUninit::assume_init` is handled the same way.)
    #[test]
    fn test_from_utf8_unchecked_is_caught_with_named_invariant() {
        let func = make_func(
            "u8u",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                    },
                    name: Some("bytes".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::str::from_utf8_unchecked".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:from_utf8_unchecked]")
                    && message.contains("valid UTF-8"))),
            "from_utf8_unchecked must emit a fail-closed obligation naming the UTF-8 invariant"
        );
    }

    /// Trust (unsafe-op completeness): `ptr::read(p)` over a pointer to a fixed
    /// `[u8; 32]` (offset 0) emits a bounds obligation `0 + 1 > 32` — i.e. the
    /// single-byte read must lie within the 32-byte allocation. The deref is
    /// hidden inside `ptr::read`, so the `Deref`-place path misses it; this closes
    /// the gap. (`0 + 1 > 32` is UNSAT ⇒ a read at offset 0 of a 32-byte alloc is
    /// proved in-bounds.)
    #[test]
    fn test_ptr_read_emits_bounds_obligation() {
        let func = make_func(
            "rd",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 32 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(1)),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::ptr::read".to_string(),
                        args: vec![Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { detail, .. }
                if detail.contains("raw read/write"))
            })
            .expect("ptr::read must emit a raw read/write bounds obligation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        assert!(
            matches!(&bounds.formula, Formula::Gt(_, _)) && contains_int(&bounds.formula, 32),
            "obligation must bound the access against the 32-byte allocation, got {:?}",
            bounds.formula
        );
    }

    /// Trust (unsafe-op completeness): `slice.get_unchecked(i)` over a `[u8; 8]`
    /// emits an `IndexOutOfBounds` obligation `i >= 8` — the bounds check the
    /// language omits for the unchecked accessor. Fail-closed by default; a
    /// `i < 8` guard discharges it. Previously this UB-class op was uncaught.
    #[test]
    fn test_get_unchecked_emits_bounds_obligation() {
        let func = make_func(
            "uc",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Array { elem: Box::new(Ty::u8()), len: 8 }),
                    },
                    name: Some("arr".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("i".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::<impl [u8]>::get_unchecked".to_string(),
                        args: vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| matches!(&vc.kind, VcKind::IndexOutOfBounds))
            .expect("get_unchecked must emit an IndexOutOfBounds obligation");
        assert_eq!(
            bounds.formula,
            Formula::Ge(Box::new(Formula::Var("i".into(), Sort::Int)), Box::new(Formula::Int(8)),),
            "obligation must be `i >= 8` (the array length), got {:?}",
            bounds.formula
        );
    }

    // ── Unsafe-op completeness: NonZero/NonNull::new_unchecked, char::from_u32_unchecked,
    //    Vec::set_len, Option/Result::unwrap_unchecked (the extended allowlist) ──

    /// Build a single-block function whose sole terminator is `callee(args)`.
    fn one_call_func(
        name: &str,
        locals: Vec<LocalDecl>,
        callee: &str,
        args: Vec<Operand>,
    ) -> VerifiableFunction {
        make_func(
            name,
            locals,
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: callee.to_string(),
                        args,
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        )
    }

    /// FIRE-ON-BUG: an UNGUARDED `NonZeroU32::new_unchecked(x)` emits a modeled
    /// `x == 0` obligation (the niche the `NonZero` invariant forbids). The
    /// violation references the argument `x` by its guard-visible name so a
    /// dominating `if x != 0` can discharge it.
    #[test]
    fn test_new_unchecked_unguarded_emits_nonzero_obligation() {
        let func = one_call_func(
            "nz",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("x".into()),
                },
            ],
            "core::num::NonZeroU32::new_unchecked",
            vec![Operand::Copy(Place::local(1))],
        );
        let vcs = check_sep_unsafe(&func);
        let vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:new_unchecked]"))
            })
            .expect("new_unchecked must emit a non-zero obligation");
        assert_eq!(
            vc.formula,
            Formula::Eq(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0)),),
            "obligation must be the modeled `x == 0`, got {:?}",
            vc.formula
        );
    }

    /// NO FALSE POSITIVE: a GUARDED `if x != 0 { NonZeroU32::new_unchecked(x) }`
    /// must PROVE. The dominating `x != 0` guard, conjoined by the guard-resolution
    /// pass, makes the `x == 0` violation UNSAT (`x != 0 AND x == 0`). We assert the
    /// guard threaded the SAME `x` into the obligation so the conjunction is
    /// contradictory.
    #[test]
    fn test_new_unchecked_guarded_by_nonzero_proves() {
        // bb0: switch on x { 0 => bb2 (no-op), otherwise => bb1 (the call) }
        // bb1 is reached only when x != 0.
        let func = make_func(
            "nz_guarded",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("x".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        exhaustive_enum_unreachable: false,
                        discr: Operand::Copy(Place::local(1)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        span: empty_span(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::num::NonZeroU32::new_unchecked".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let vcs = crate::generate_vcs(&func);
        let vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:new_unchecked]"))
            })
            .expect("guarded new_unchecked must still produce the obligation");
        // The dominating `x != 0` guard must be conjoined with the `x == 0`
        // violation, yielding a self-contradictory (UNSAT ⇒ PROVED) conjunction.
        assert!(
            matches!(&vc.formula, Formula::And(_) | Formula::Or(_)),
            "guard must be conjoined onto the obligation, got {:?}",
            vc.formula
        );
        // Both the guard (`x != 0`) and the violation (`x == 0`) must be present
        // over the SAME `x`, so the conjunction is contradictory (PROVED). The
        // guard contributes a negated/`!=` form and the violation an `Eq`.
        fn has_x_eq_zero(f: &Formula) -> bool {
            matches!(f, Formula::Eq(a, b)
                if matches!(a.as_ref(), Formula::Var(n, _) if n == "x")
                    && matches!(b.as_ref(), Formula::Int(0)))
                || f.children().into_iter().any(has_x_eq_zero)
        }
        fn has_x_neq_zero(f: &Formula) -> bool {
            matches!(f, Formula::Not(inner)
                if matches!(inner.as_ref(), Formula::Eq(a, b)
                    if matches!(a.as_ref(), Formula::Var(n, _) if n == "x")
                        && matches!(b.as_ref(), Formula::Int(0))))
                || f.children().into_iter().any(has_x_neq_zero)
        }
        assert!(
            has_x_eq_zero(&vc.formula),
            "violation `x == 0` must survive in the guarded formula: {:?}",
            vc.formula
        );
        assert!(
            has_x_neq_zero(&vc.formula),
            "dominating guard `x != 0` must be conjoined over the same `x`: {:?}",
            vc.formula
        );
    }

    /// FIRE-ON-BUG: `char::from_u32_unchecked(x)` emits the modeled Unicode
    /// scalar-value obligation: a disjunction of the out-of-range half
    /// (`x > 0x10FFFF`) and the surrogate gap (`0xD800 <= x <= 0xDFFF`).
    #[test]
    fn test_from_u32_unchecked_emits_scalar_value_obligation() {
        let func = one_call_func(
            "ch",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 32, signed: false },
                    name: Some("x".into()),
                },
            ],
            "core::char::from_u32_unchecked",
            vec![Operand::Copy(Place::local(1))],
        );
        let vcs = check_sep_unsafe(&func);
        let vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:from_u32_unchecked]"))
            })
            .expect("from_u32_unchecked must emit a scalar-value obligation");
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        assert!(
            matches!(&vc.formula, Formula::Or(_))
                && contains_int(&vc.formula, 0x10FFFF)
                && contains_int(&vc.formula, 0xD800)
                && contains_int(&vc.formula, 0xDFFF),
            "obligation must encode the scalar-value range + surrogate gap, got {:?}",
            vc.formula
        );
    }

    /// FIRE-ON-BUG: `Vec::set_len(new_len)` emits the modeled `new_len > capacity`
    /// obligation (the tractable `new_len <= capacity` half).
    #[test]
    fn test_set_len_emits_capacity_obligation() {
        let func = one_call_func(
            "sl",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }),
                    },
                    name: Some("v".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("new_len".into()),
                },
            ],
            "alloc::vec::Vec::<u8>::set_len",
            vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
        );
        let vcs = check_sep_unsafe(&func);
        let vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:set_len]"))
            })
            .expect("set_len must emit a capacity obligation");
        assert_eq!(
            vc.formula,
            Formula::Gt(
                Box::new(Formula::Var("new_len".into(), Sort::Int)),
                Box::new(generated_sep_var("capacity_1", Sort::Int)),
            ),
            "obligation must be `new_len > capacity_<recv>`, got {:?}",
            vc.formula
        );
    }

    /// FIRE-ON-BUG: `Option::unwrap_unchecked()` emits a fail-closed Unknown
    /// obligation naming the `Some`/`Ok` precondition (a non-arithmetic
    /// discriminant fact). Distinct from the safe panicking `unwrap`/`expect`,
    /// which must NOT be flagged (covered below).
    #[test]
    fn test_unwrap_unchecked_emits_failclosed_obligation() {
        let func = one_call_func(
            "uu",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("opt".into()) },
            ],
            "core::option::Option::<u32>::unwrap_unchecked",
            vec![Operand::Copy(Place::local(1))],
        );
        let vcs = check_sep_unsafe(&func);
        let vc = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:unwrap_unchecked]"))
            })
            .expect("unwrap_unchecked must emit a fail-closed obligation");
        assert!(
            matches!(&vc.formula, Formula::Var(name, Sort::Bool)
                if name.contains("unwrap_unchecked_unjustified")),
            "obligation must be the fail-closed Unknown var, got {:?}",
            vc.formula
        );
    }

    /// NO FALSE POSITIVE: the SAFE panicking `Option::unwrap()` (and `expect`) must
    /// NOT be treated as an unsafe op — they panic, they do not invoke UB. No
    /// `[unsafe:sep:*]` obligation may be emitted for a function whose only call is
    /// a plain `unwrap`.
    #[test]
    fn test_safe_unwrap_emits_no_unsafe_obligation() {
        let func = one_call_func(
            "su",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("opt".into()) },
            ],
            "core::option::Option::<u32>::unwrap",
            vec![Operand::Copy(Place::local(1))],
        );
        let vcs = check_sep_unsafe(&func);
        assert!(
            !vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
                if message.contains("[unsafe:sep:"))),
            "safe `unwrap` must not produce any unsafe obligation, got {:#?}",
            vcs.iter().map(|v| format!("{:?}", v.kind)).collect::<Vec<_>>()
        );
    }

    /// REGRESSION: extending the allowlist must NOT change the existing
    /// `from_utf8_unchecked` / `assume_init` fail-closed obligations.
    #[test]
    fn test_existing_failclosed_ops_unchanged() {
        for (callee, tag, needle) in [
            ("core::str::from_utf8_unchecked", "from_utf8_unchecked", "valid UTF-8"),
            ("core::mem::MaybeUninit::<u32>::assume_init", "assume_init", "fully initialized"),
        ] {
            let func = one_call_func(
                "fc",
                vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                ],
                callee,
                vec![Operand::Copy(Place::local(1))],
            );
            let vcs = check_sep_unsafe(&func);
            assert!(
                vcs.iter().any(|vc| matches!(&vc.kind, VcKind::Assertion { message }
                    if message.contains(&format!("[unsafe:sep:{tag}]"))
                        && message.contains(needle))),
                "{callee} must still emit its fail-closed obligation naming `{needle}`"
            );
        }
    }

    /// Trust: from_raw_parts over a pointer to a FIXED-SIZE array uses the
    /// CONCRETE array byte-size in its bounds obligation (`len > 64`), so a
    /// `len <= 64` guard can discharge it — turning the HIGH-2 class from
    /// always-caught to provable when the size is in the type.
    #[test]
    fn test_from_raw_parts_over_fixed_array_uses_concrete_size() {
        let func = make_func(
            "slice_from_array",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(1)),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Copy(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        let bounds = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind, VcKind::CopyBoundsViolation { callee, .. }
                if callee.contains("from_raw_parts"))
            })
            .expect("from_raw_parts must emit a CopyBoundsViolation");
        // The obligation must compare against the CONCRETE size 64, so a
        // `len <= 64` guard makes it UNSAT (provable).
        fn contains_int(f: &Formula, n: i128) -> bool {
            matches!(f, Formula::Int(v) if *v == n)
                || f.children().into_iter().any(|c| contains_int(c, n))
        }
        assert!(
            contains_int(&bounds.formula, 64),
            "obligation must use the concrete array size 64, got {:?}",
            bounds.formula
        );
        assert!(
            matches!(&bounds.formula, Formula::Gt(_, _)),
            "obligation must be `len > 64`, got {:?}",
            bounds.formula
        );
    }

    // ── Pattern 6: AddressOf ──────────────────────────────────────────

    #[test]
    fn test_address_of_generates_vc() {
        let func = make_func(
            "addr_of_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::AddressOf(true, Place::local(1)),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("&raw mut")
            )),
            "AddressOf should produce a source liveness VC"
        );
    }

    // ── Pattern 7: Transmute ──────────────────────────────────────────

    #[test]
    fn test_transmute_call_generates_vcs() {
        let func = make_func(
            "transmute_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::mem::transmute".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert_eq!(vcs.len(), 3, "transmute should produce 3 VCs (layout, validity, align)");
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("layout")
        )));
    }

    // ── points_to_multi tests ─────────────────────────────────────────

    #[test]
    fn test_points_to_multi_empty() {
        let base = Formula::Var("base".into(), Sort::Int);
        let result = points_to_multi(&base, &[]);
        assert!(result.is_emp());
    }

    #[test]
    fn test_points_to_multi_single() {
        let base = Formula::Var("base".into(), Sort::Int);
        let result = points_to_multi(&base, &[Formula::Int(42)]);
        assert_eq!(result.cell_count(), 1);
    }

    #[test]
    fn test_points_to_multi_multiple() {
        let base = Formula::Var("base".into(), Sort::Int);
        let values = vec![Formula::Int(1), Formula::Int(2), Formula::Int(3)];
        let result = points_to_multi(&base, &values);
        assert_eq!(result.cell_count(), 3);
    }

    // ── Frame computation tests ───────────────────────────────────────

    #[test]
    fn test_compute_frame_both_empty() {
        let before = SymbolicHeap::new("h1");
        let after = SymbolicHeap::new("h2");
        let frame = SepEngine::compute_frame(&before, &after);
        assert!(frame.is_emp());
    }

    #[test]
    fn test_compute_frame_before_empty() {
        let before = SymbolicHeap::new("h1");
        let mut after = SymbolicHeap::new("h2");
        let prov = after.allocate("p");
        after.write_cell("cell", Formula::Int(0), Formula::Int(42), prov);

        let frame = SepEngine::compute_frame(&before, &after);
        assert!(frame.is_emp(), "no cells before means no frame");
    }

    #[test]
    fn test_compute_frame_with_cells() {
        let mut before = SymbolicHeap::new("h1");
        let prov = before.allocate("p");
        before.write_cell("cell_a", Formula::Int(0), Formula::Int(1), prov);

        let mut after = SymbolicHeap::new("h2");
        let prov2 = after.allocate("q");
        after.write_cell("cell_b", Formula::Int(1), Formula::Int(2), prov2);

        let frame = SepEngine::compute_frame(&before, &after);
        // Conservative: frame is the before state
        assert_eq!(frame.cell_count(), 1);
    }

    // ── Integration: safe function produces no VCs ────────────────────

    #[test]
    fn test_safe_function_no_sep_vcs() {
        let func = make_func(
            "safe_add",
            vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
            ],
            2,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        trust_types::BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.is_empty(), "safe function should produce no sep VCs");
    }

    // ── All sep engine VCs are L0Safety ───────────────────────────────

    #[test]
    fn test_all_sep_engine_vcs_are_l0_safety() {
        let func = make_func(
            "mixed_unsafe",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        for vc in &vcs {
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L0Safety,
                "all sep engine VCs should be L0Safety"
            );
        }
    }

    /// Trust: lock in that the NEW unsafe VC kinds (CopyBoundsViolation,
    /// ExternallyMutableAllocationBounds) are present and classified L0Safety —
    /// the generic invariant test above only drives a raw deref, so it never
    /// constructs these kinds.
    #[test]
    fn test_new_unsafe_vc_kinds_are_l0_safety() {
        let func = make_func(
            "copy_and_map",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("dst".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("map".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::copy_nonoverlapping".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "memmap2::MmapMut::map_mut".to_string(),
                        args: vec![],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        for vc in &vcs {
            // The mmap-truncation `Temporal` VC is now emitted by default and is
            // legitimately L2-domain (`ty` checks it at `-Z trust-verify-level=2`);
            // it is filtered out at L0. Every OTHER sep VC — including the new
            // safety kinds this test guards — must be L0Safety.
            if matches!(&vc.kind, VcKind::Temporal { .. }) {
                continue;
            }
            assert_eq!(
                vc.kind.proof_level(),
                ProofLevel::L0Safety,
                "all non-temporal sep engine VCs (incl. the new kinds) should be L0Safety, got {:?}",
                vc.kind
            );
        }
        assert!(
            vcs.iter().any(|vc| matches!(&vc.kind, VcKind::CopyBoundsViolation { .. })),
            "the new CopyBoundsViolation kind must be exercised here"
        );
        assert!(
            vcs.iter()
                .any(|vc| matches!(&vc.kind, VcKind::ExternallyMutableAllocationBounds { .. })),
            "the new ExternallyMutableAllocationBounds kind must be exercised here"
        );
    }

    #[test]
    fn test_sep_engine_preserves_symbolic_write_formula() {
        let symbolic_name = "trust_symbolic.formula";
        let symbolic = Formula::Var(symbolic_name.to_string(), Sort::Int);
        let func = make_func(
            "symbolic_raw_write",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                    rvalue: Rvalue::Use(Operand::Symbolic(symbolic)),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        // The symbolic write value was only ever embedded in the post-write
        // read-over-write consistency VC (`Select(Store(h, p, v), p) == v`), which was
        // deliberately dropped as a content-free array-theory tautology. So the symbolic
        // formula is no longer carried in any emitted VC.
        assert!(
            !vcs.iter().any(|vc| formula_contains_var(&vc.formula, symbolic_name)),
            "symbolic value is only carried by the dropped consistency VC, so no VC should reference it"
        );
        // The symbolic operand must still be recognized as `Operand::Symbolic` and not fall
        // through to the catch-all `__unknown_operand` degradation -- the remaining deref /
        // write-permission VCs are emitted normally rather than poisoned by an unknown value.
        assert!(!vcs.is_empty(), "symbolic raw write must still emit deref + write-permission VCs");
        assert!(
            !vcs.iter().any(|vc| formula_contains_var(&vc.formula, "__unknown_operand")),
            "symbolic write operand must not degrade to __unknown_operand"
        );
    }

    // ── Ref argument tracking ─────────────────────────────────────────

    #[test]
    fn test_ref_arg_tracked_and_readable() {
        // fn f(x: &u32) -> u32 { *x }
        let func = make_func(
            "read_ref",
            vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                    name: Some("x".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            1,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                    span: empty_span(),
                }],
                terminator: Terminator::Return,
            }],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(vcs.is_empty(), "safe reference deref should not enter sep analysis");
    }

    // ── Use-after-free detection ──────────────────────────────────────

    #[test]
    fn test_use_after_free_detected() {
        // alloc, free, then read through the pointer
        let func = make_func(
            "use_after_free",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::alloc::alloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Drop {
                        unwind: UnwindEdge::Unreachable,
                        place: Place::local(1),
                        target: BlockId(2),
                        span: empty_span(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref],
                        })),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("use-after-free")
            )),
            "reading freed pointer should produce use-after-free VC"
        );
    }

    // ── Realloc ───────────────────────────────────────────────────────

    #[test]
    fn test_realloc_generates_vcs() {
        let func = make_func(
            "realloc_test",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("ptr".into()) },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::alloc::realloc".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.iter().any(|vc| matches!(
                &vc.kind,
                VcKind::Assertion { message } if message.contains("realloc")
            )),
            "realloc should produce VCs"
        );
    }

    #[test]
    fn probe_negative_offset_from_raw_parts() {
        // [u8;64] buf; base=&raw const buf; p = base.offset(-100); from_raw_parts(p, len)
        // offset accumulates to -100. Question: is there ANY lower-bound check on
        // the from_raw_parts obligation (offset>=0 / dest>=base)?
        let func = make_func(
            "neg_off",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Array { elem: Box::new(Ty::u8()), len: 64 },
                    name: Some("buf".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("base".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 4,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            0,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::AddressOf(false, Place::local(1)),
                        span: empty_span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "std::ptr::const_ptr::<impl *const u8>::offset".to_string(),
                        args: vec![
                            Operand::Move(Place::local(2)),
                            Operand::Constant(trust_types::ConstValue::Int(-100)),
                        ],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(4))],
                        dest: Place::local(0),
                        target: Some(BlockId(2)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
        );
        let vcs = check_sep_unsafe(&func);
        for vc in &vcs {
            match &vc.kind {
                VcKind::CopyBoundsViolation { callee, .. } if callee.contains("from_raw_parts") => {
                    eprintln!("PROBE_NEG from_raw_parts obligation: {:?}", vc.formula)
                }
                VcKind::Assertion { message } if message.contains("offset") => {
                    eprintln!("PROBE_NEG offset assertion: {:?}", vc.formula)
                }
                _ => {}
            }
        }
        eprintln!("PROBE_NEG total vcs = {}", vcs.len());
    }

    /// INDEPENDENT VERIFIER PROBE: regression guard for the cross-crate /
    /// field-by-field discharge that USED to be unsound.
    /// `as_slice(&self) -> &[u8] { from_raw_parts(self.ptr, self.len) }` over a
    /// `Buf { ptr: *mut u8, len: usize }` whose CONSTRUCTOR is not in this
    /// function (another crate, or field-by-field `s.ptr=p; s.len=n;`). The whole
    /// per-function pipeline (`check_sep_unsafe`) runs with backing enabled.
    /// Previously the only backing VC was the ASSUME `Gt(self.len, self.len)`
    /// (trivially UNSAT ⇒ discharged) with NO establish obligation, so a
    /// `self.len` larger than the real allocation was proved safe for free. The
    /// fix bounds against a DISTINCT opaque allocation-size symbol, so the VC is
    /// fail-closed (CAUGHT) until a verified establish supplies the invariant.
    /// This test pins that fail-closed shape so the free discharge cannot return.
    #[test]
    fn verifier_probe_as_slice_backing_assume_is_fail_closed() {
        // No explicit summary context: this probe asserts the UNCERTIFIED
        // (fail-closed) shape.
        let buf_ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Buf".into(),
            fields: vec![
                ("ptr".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                ("len".into(), Ty::Int { width: 64, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        let func = make_func(
            "as_slice",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(buf_ty) },
                    name: Some("self".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // _2 = (*self).0   (ptr field)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(0)],
                            })),
                            span: empty_span(),
                        },
                        // _3 = (*self).1   (len field)
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(1)],
                            })),
                            span: empty_span(),
                        },
                    ],
                    // _0 = from_raw_parts(move _2, move _3)
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        );

        // Full per-function pipeline entry point.
        let context = crate::VcgenContext::for_function(func.def_path.clone()).with_backing(true);
        let vcs = crate::with_vcgen_context(&context, || check_sep_unsafe(&func));
        for vc in &vcs {
            eprintln!("PROBE VC kind={:?} formula={:?}", vc.kind, vc.formula);
        }
        // 1) NO establish obligation is present (the constructor was never seen).
        let establish = vcs.iter().any(|vc| {
            matches!(&vc.kind,
            VcKind::Assertion { message } if message.contains("[unsafe:sep:backing]"))
        });
        assert!(!establish, "EXPECTED: no establish obligation in an as_slice-only fn");

        // 2) The backing ASSUME fired, and its RHS is a DISTINCT opaque
        //    allocation-size symbol — NOT `self.len`. This is the soundness fix:
        //    bounding against `self.len` would make the VC `(0+len) > len`
        //    (trivially UNSAT) and FALSELY discharge `as_slice` without any
        //    verified establish. Against an opaque size the VC is fail-closed:
        //    it is NOT trivially UNSAT and can only discharge once a verified
        //    establish supplies `alloc_size >= self.len` (interprocedural
        //    struct-invariant threading, not yet built).
        let backing = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind,
            VcKind::CopyBoundsViolation { detail, .. } if detail.contains("backing field"))
            })
            .expect("EXPECTED: backing-invariant ASSUME fires for as_slice");
        let Formula::Gt(extent, size) = &backing.formula else {
            panic!("expected Gt(extent,size), got {:?}", backing.formula)
        };
        // The RHS is the opaque per-(base,field) allocation-size symbol, so the
        // violation `(0 + len) > backing_alloc_size_1_0` is NOT identically false.
        assert_eq!(
            **size,
            generated_sep_var("backing_alloc_size_1_0", Sort::Int),
            "backing size must be a DISTINCT opaque symbol, never `self.len`"
        );
        assert_ne!(
            **size,
            Formula::Var("len".into(), Sort::Int),
            "regression: binding to `self.len` reintroduces the `len > len` free discharge"
        );
        assert_eq!(
            **extent,
            Formula::Add(
                Box::new(Formula::Int(0)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            ),
            "extent is `0 + len`; with an opaque size the VC is fail-closed (CAUGHT)"
        );
        eprintln!(
            "VERIFIER PROBE: backing VC = `(0+len) > backing_alloc_size_1_0` \
                   (fail-closed, NOT trivially UNSAT) => sound CATCH, no free discharge"
        );
    }

    /// `Buf { ptr: *mut u8, len: u64 }` with `as_slice(&self) -> &[u8] {
    /// from_raw_parts(self.ptr, self.len) }` — the use-site fixture shared by the
    /// certified/uncertified consumer tests below.
    fn as_slice_buf_fixture() -> VerifiableFunction {
        let buf_ty = Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Buf".into(),
            fields: vec![
                ("ptr".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                ("len".into(), Ty::Int { width: 64, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, };
        make_func(
            "as_slice",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(buf_ty) },
                    name: Some("self".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
            ],
            1,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(0)],
                            })),
                            span: empty_span(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(1)],
                            })),
                            span: empty_span(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".to_string(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: empty_span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        )
    }

    #[test]
    fn certified_backing_licenses_as_slice_discharge() {
        // Consumer side of interprocedural certification: given a CERTIFICATE for
        // the backing struct, the ASSUME for `from_raw_parts(self.ptr, self.len)`
        // conjoins the licensed `backing_alloc_size_1_0 >= self.len`, so the VC
        // becomes `And([Ge(size, len), Gt(0+len, size)])` — UNSAT (discharged),
        // establish-backed. (The producer side — that certification is granted
        // iff every constructor establishes — is covered in `backing_cert`.)
        let func = as_slice_buf_fixture();
        let context = crate::VcgenContext::for_function(func.def_path.clone())
            .with_backing(true)
            .with_callee_summaries(
                crate::CalleeSummaryContext::default()
                    .with_certified_backing_structs(std::iter::once("Buf".to_string()).collect()),
            );
        let vcs = crate::with_vcgen_context(&context, || check_sep_unsafe(&func));
        let backing = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind,
                VcKind::CopyBoundsViolation { detail, .. } if detail.contains("backing field"))
            })
            .expect("backing ASSUME must fire");
        let Formula::And(conj) = &backing.formula else {
            panic!("certified backing VC must be a conjunction, got {:?}", backing.formula)
        };
        let has_assumption = conj.iter().any(|f| {
            matches!(f,
            Formula::Ge(s, l)
                if **s == generated_sep_var("backing_alloc_size_1_0", Sort::Int)
                    && **l == Formula::Var("len".into(), Sort::Int))
        });
        assert!(
            has_assumption,
            "certified VC must conjoin `backing_alloc_size_1_0 >= len`, got {:?}",
            backing.formula
        );
        assert!(
            conj.iter().any(|f| matches!(f, Formula::Gt(_, _))),
            "the violation `Gt(extent, size)` must remain in the conjunction"
        );
    }

    #[test]
    fn uncertified_backing_stays_fail_closed_for_as_slice() {
        // Control: the SAME fixture without a certificate must keep the bare,
        // fail-closed `Gt(extent, size)` against the opaque size — no assumption.
        let func = as_slice_buf_fixture();
        let context = crate::VcgenContext::for_function(func.def_path.clone()).with_backing(true);
        let vcs = crate::with_vcgen_context(&context, || check_sep_unsafe(&func));
        let backing = vcs
            .iter()
            .find(|vc| {
                matches!(&vc.kind,
                VcKind::CopyBoundsViolation { detail, .. } if detail.contains("backing field"))
            })
            .expect("backing ASSUME must fire");
        assert!(
            matches!(&backing.formula, Formula::Gt(_, _)),
            "uncertified backing VC must be a bare `Gt(extent, size)` (fail-closed), got {:?}",
            backing.formula
        );
    }

    #[test]
    fn call_is_modeled_recognizes_handled_calls_and_rejects_others() {
        // Calls the separation engine MODELS (an obligation or tracking) — used by
        // the compiler's authoritative unsafe-call completeness check to avoid
        // double-flagging a covered call.
        for modeled in [
            "core::slice::from_raw_parts",
            "std::ptr::copy_nonoverlapping",
            "std::ptr::mut_ptr::<impl *mut t>::add",
            "std::ptr::mut_ptr::<impl *mut t>::cast",
            "core::ptr::read",
            "libc::mmap",
            "core::slice::<impl [t]>::get_unchecked",
            "core::mem::transmute",
            "core::mem::maybeuninit::<t>::assume_init",
            // Native-TLS lazy-init `get_or_init` (LOWERCASED, as `call_has_unsafe_model`
            // passes it) — the compiler-generated `thread_local!` machinery, covered.
            "std::thread::local_impl::lazystorage::<std::cell::refcell<rational::arena>, ()>::get_or_init::<fn() -> std::cell::refcell<rational::arena> {rational::arena::__rust_std_internal_init_fn}>",
        ] {
            assert!(call_is_modeled(modeled), "should be modeled: {modeled}");
        }
        // Arbitrary unsafe fn the engine does NOT model — must be rejected, so the
        // compiler's check emits a fail-closed obligation for it. The `OnceLock`/
        // `OnceCell` `get_or_init` siblings lack the `thread::local_impl::lazystorage`
        // module anchor, so they stay fail-closed (soundness boundary).
        for unmodeled in [
            "mycrate::frobnicate_raw",
            "core::num::<impl u64>::wrapping_add",
            "mycrate::do_thing",
            "std::sync::oncelock::<u32>::get_or_init::<{closure@x.rs}>",
        ] {
            assert!(!call_is_modeled(unmodeled), "should NOT be modeled: {unmodeled}");
        }
    }

    // ── TRUSTED-STD-SPAN gate ─────────────────────────────────────────
    //
    // An unsafe operation whose OWN span is in the sysroot standard library
    // (`alloc/src/macros.rs` etc. — the `vec!` macro's inlined RawVec /
    // Box::new_uninit / assume_init) is std-internal TCB, already trusted, so it
    // must NOT be charged to the user function it expanded into. A user `unsafe`
    // op (span in a first-party crate) MUST still be charged (fail-closed).

    fn span_in(file: &str) -> SourceSpan {
        SourceSpan { file: file.to_string(), line_start: 1, col_start: 1, line_end: 1, col_end: 20 }
    }

    /// A minimal function containing exactly one unsafe raw-pointer deref read,
    /// with the deref statement's source span set to `file`.
    fn deref_read_func_with_span(file: &str) -> VerifiableFunction {
        make_func(
            "deref_read",
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("val".into()) },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u32()) },
                    name: Some("ptr".into()),
                },
            ],
            0,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 2,
                        projections: vec![Projection::Deref],
                    })),
                    span: span_in(file),
                }],
                terminator: Terminator::Return,
            }],
        )
    }

    #[test]
    fn test_is_trusted_std_file_std_paths() {
        // The sysroot `library/` tree — in-tree, absolute, and remapped virtual
        // forms — plus the remapped bare crate roots (`library/` prefix stripped).
        for std_file in [
            "library/alloc/src/macros.rs",
            "library/core/src/slice/mod.rs",
            "library/std/src/io/mod.rs",
            "/host/dev/rust/library/alloc/src/macros.rs",
            "/rustc/e8be5c8/library/core/src/ptr/mod.rs",
            "alloc/src/macros.rs",
            "core/src/ptr/mod.rs",
            "std/src/vec/mod.rs",
        ] {
            assert!(is_trusted_std_file(std_file), "should be trusted std: {std_file}");
        }
    }

    #[test]
    fn test_is_trusted_std_file_user_paths() {
        // First-party / user paths, an empty span, and binary provenance are NOT
        // std — fail-closed keeps their obligations.
        for user_file in [
            "crates/ny-cert/src/candidates.rs",
            "/host/dev/ny/crates/ny-cert/src/lib.rs",
            "src/main.rs",
            "my_core_lib/src/thing.rs", // superstring of a std crate name, not a segment
            "",
            "binary:0x1000",
        ] {
            assert!(!is_trusted_std_file(user_file), "should NOT be trusted std: {user_file}");
        }
    }

    /// SOUNDNESS REGRESSION: a `library/` path segment is NOT by itself evidence
    /// of sysroot std.
    ///
    /// Trusting a span deletes every `[unsafe:sep:*]` obligation for it, and
    /// nothing else re-covers those operations — the compiler's unsafe-call net
    /// yields to this engine. The gate previously accepted any path containing a
    /// `library/` segment, so a crate laid out that way had its memory-safety
    /// obligations silently dropped. `first-party/trust-mc` declares
    /// `members = ["library/trust-mc", ...]` and that tree contains real
    /// `unsafe`, so this was reachable in-tree rather than hypothetical.
    #[test]
    fn library_segment_alone_is_not_trusted_std() {
        for user_file in [
            // The in-tree layout that made this reachable.
            "first-party/trust-mc/library/trust-mc/src/futures.rs",
            "library/trust-mc/src/futures.rs",
            // A workspace that simply uses `library/` as a directory name.
            "library/mycrate/src/raw.rs",
            "/home/dev/proj/library/thing/src/lib.rs",
            "library",
            "library/",
            // A std crate NAME without the `src/` segment is not a crate root.
            "library/core/lib.rs",
            "core/lib.rs",
            // Superstrings of std crate names must not match as segments.
            "library/coreutils/src/main.rs",
            "testing/src/lib.rs",
        ] {
            assert!(
                !is_trusted_std_file(user_file),
                "a `library/` segment alone must not confer std trust: {user_file}"
            );
        }
    }

    /// The legitimate sysroot layouts must keep working — this gate exists so
    /// std's own `unsafe` is not re-verified, and over-tightening it would flood
    /// every build with std obligations.
    #[test]
    fn sysroot_std_layouts_remain_trusted() {
        for std_file in [
            "library/core/src/ptr/mod.rs",
            "library/std/src/vec/mod.rs",
            "/home/dev/checkout/library/alloc/src/boxed.rs",
            "/rustc/abcdef0123/library/core/src/slice/mod.rs",
            // Remapped bare crate roots (the `library/` prefix stripped).
            "core/src/ptr/mod.rs",
            "test/src/lib.rs",
        ] {
            assert!(is_trusted_std_file(std_file), "should remain trusted std: {std_file}");
        }
    }

    #[test]
    fn test_std_span_unsafe_op_not_charged() {
        // The exact task shape: the `vec!`-macro unsafe charged with a std span.
        let func = deref_read_func_with_span("alloc/src/macros.rs");
        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.is_empty(),
            "unsafe op with a std-library span must be trusted (0 obligations), got {}: {:?}",
            vcs.len(),
            vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_user_span_unsafe_op_still_charged() {
        // The SAME unsafe op with a first-party span MUST still be charged.
        let func = deref_read_func_with_span("crates/ny-cert/src/candidates.rs");
        let vcs = check_sep_unsafe(&func);
        assert!(
            vcs.len() >= 3,
            "unsafe op with a user span must still be charged (>=3 deref VCs), got {}",
            vcs.len()
        );
        assert!(vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::Assertion { message } if message.contains("null check")
        )));
    }
}
