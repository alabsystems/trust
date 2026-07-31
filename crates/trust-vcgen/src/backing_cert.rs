// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Interprocedural backing-invariant certification.
//!
//! A `#[trust::backing]` struct `S { ptr, len }` declares the relational
//! invariant `R(s) := "s.ptr is valid for s.len elements"`. A use-site ASSUME —
//! `from_raw_parts(self.ptr.add(start), len)` over the field, in
//! [`crate::sep_engine`] — is only SOUND to discharge if `R` is a genuine TYPE
//! invariant: *every* value of `S` satisfies it. That holds iff every
//! constructor of `S` ESTABLISHES `R` and no field-write breaks it.
//!
//! A strictly per-function analysis cannot know this — the establish obligation
//! lives in the *constructor*, a different function (often a different crate).
//! Without the cross-function link, modeling `s.ptr`'s allocation size as
//! `s.len` makes `as_slice` reduce to `len > len` (UNSAT) and discharge for
//! free — UNSOUND (an oversized or field-by-field-built `S` is "proved" safe).
//! That false discharge is exactly what the 2026-06 soundness audit found; the
//! use site now stays fail-closed (CAUGHT) unless this module issues a
//! certificate.
//!
//! This pass examines a whole set of functions (the crate), and certifies a
//! backing struct `S` iff:
//!   1. at least one constructor of `S` is present in the set, AND
//!   2. every constructor ESTABLISHES `R` (its `Lt(alloc_size, len)` obligation
//!      is trivially UNSAT from the constructor's local facts — e.g. an
//!      `mmap(len)`-built struct gives `len < len`), AND
//!   3. no function writes a backing field of `S` outside construction (a write
//!      could break `R` after it was established).
//!
//! **SOUNDNESS CONTRACT.** The caller MUST pass the COMPLETE set of bodies
//! that can construct or mutate `S`. For a struct with PRIVATE backing fields
//! this is exactly the bodies of `S`'s defining crate — Rust forbids external
//! code from constructing or mutating private fields — so a whole-crate analysis
//! is complete. The `#[trust::backing]` attribute is the developer's declaration
//! that the fields are sealed; Trust then VERIFIES that every in-crate
//! constructor establishes `R`. If the set is incomplete (an unseen constructor
//! could violate `R`), the certificate is NOT sound to rely on — this function
//! starts from `all_establish = true` / `broken_by_mutation = false` and only
//! WEAKENS them from evidence it sees, so an omitted body pushes TOWARD
//! certification, never away from it. "Every body" is wider than the crate's
//! `fn` items: a `const`/`static` initializer (`const B: S = S { ptr, len }`),
//! a tuple-ctor shim used as a function value, a closure, a `promoted_mir`
//! fragment (promotion moves a `&S { .. }` aggregate out of its parent body),
//! and a `#[rustc_comptime]` fn are all constructor-capable. The compiler
//! integration (`trust_init_backing_certificates` in `rustc_mir_transform`)
//! therefore inventories every `mir_keys` body owner — recovering already-stolen
//! const-context bodies through `mir_for_ctfe` — and withholds the certificate
//! entirely (fail closed) if any body cannot be inventoried, and only certifies
//! private-field structs.

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{AggregateKind, Formula, Projection, Rvalue, Statement, VerifiableFunction};

use crate::sep_engine::{detect_backing_struct, detect_backing_structs, establish_formulas};

/// Certify the backing invariants provable from `functions`, returning the set
/// of struct names whose invariant is established by every constructor and
/// broken by none. A name in the result authorizes the use-site ASSUME (in
/// `sep_engine`) to license `alloc_size >= self.len` and so discharge a guarded
/// access. See the module docs for the soundness contract on `functions`.
#[must_use]
pub fn certify_backing_invariants(functions: &[VerifiableFunction]) -> FxHashSet<String> {
    // Universe of backing structs referenced anywhere, as name -> (ptr, len).
    let mut shapes: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    for func in functions {
        if let Some((name, pf, lf)) = detect_backing_struct(func) {
            shapes.entry(name).or_insert((pf, lf));
        }
    }

    let mut certified = FxHashSet::default();
    for (name, (pf, lf)) in shapes {
        let mut saw_constructor = false;
        let mut all_establish = true;
        let mut broken_by_mutation = false;

        for func in functions {
            // Only functions that touch THIS struct shape/name are relevant.
            //
            // SOUNDNESS: this must consider EVERY backing-shaped struct the
            // function mentions, not just the first one. `detect_backing_struct`
            // returns the first matching local, so a decoy of the same shape
            // (one raw pointer, one unsigned integer) appearing earlier in
            // `locals` used to make this `continue` — skipping the function for
            // `name` entirely, and taking its `writes_backing_field` check with
            // it. A mutator of `name` sitting in a function that also mentions
            // another backing struct was therefore invisible, `name` certified,
            // and the use-site ASSUME `alloc_size >= self.len` was published on
            // a struct whose length could be changed after construction.
            if !detect_backing_structs(func).iter().any(|(n, _, _)| *n == name) {
                continue;
            }

            if constructs_struct(func) {
                let establishes = establish_formulas(func, pf, lf);
                // A constructor with no establish obligation isn't really
                // constructing the backing struct here (e.g. it only forwards a
                // reference); ignore it. One that emits obligations must have
                // them ALL trivially UNSAT to count as establishing.
                if !establishes.is_empty() {
                    saw_constructor = true;
                    // Canonicalize variable names through the constructor's
                    // copy-chains first: PRE-optimization MIR copies a param like
                    // `len` into distinct temporaries (`_5`, `_6`), so the raw
                    // establish is `Lt(_5, _6)` even though both ARE `len`. Without
                    // this, a genuinely-establishing constructor reads as
                    // non-establishing and the struct fails to certify (sound but
                    // useless). The canonicalizer makes `_5`/`_6` resolve to `len`.
                    let canon = build_copy_canon(func);
                    if !establishes.iter().all(|f| lt_is_unsat_modulo_copies(f, func, &canon)) {
                        all_establish = false;
                    }
                }
            }

            if writes_backing_field(func, pf, lf) {
                broken_by_mutation = true;
            }
        }

        if saw_constructor && all_establish && !broken_by_mutation {
            certified.insert(name);
        }
    }
    certified
}

/// Whether `func` contains a struct-construction aggregate (`S { .. }`).
fn constructs_struct(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().flat_map(|b| b.stmts.iter()).any(|stmt| {
        matches!(
            stmt,
            Statement::Assign { rvalue: Rvalue::Aggregate(AggregateKind::Adt { .. }, _), .. }
        )
    })
}

/// Whether `func` can MUTATE a backing field outside whole-struct construction —
/// either by storing to it (`(*x).len = …`) or by letting a `&mut` to it escape
/// (`&mut self.len`). Either denies certification, since a post-construction
/// mutation could break the established invariant.
///
/// A field LOAD (`_t = (*x).len`) and a shared borrow (`&self.len`) also put the
/// field projection on the rvalue, and are deliberately NOT flagged: neither can
/// mutate.
fn writes_backing_field(func: &VerifiableFunction, ptr_field: usize, len_field: usize) -> bool {
    let touches_backing = |place: &trust_types::Place| {
        place
            .projections
            .iter()
            .any(|proj| matches!(proj, Projection::Field(i) if *i == ptr_field || *i == len_field))
    };
    func.body.blocks.iter().flat_map(|b| b.stmts.iter()).any(|stmt| {
        let Statement::Assign { place, rvalue, .. } = stmt else { return false };
        if touches_backing(place) {
            return true;
        }
        // SOUNDNESS: a direct store is not the only way a backing field is
        // mutated. Handing out `&mut self.len` lowers to
        // `_0 = &mut ((*_1).1)` — an `Rvalue::Ref` whose Field projection sits on
        // the SOURCE place — so a destination-only scan never sees it, the struct
        // still certifies, and callers can then set `len` to anything while the
        // published ASSUME still claims `alloc_size >= self.len`. That ASSUME is
        // what makes an out-of-bounds obligation come back PROVED, so an escape
        // must deny certification exactly as a store does.
        //
        // Shared borrows are fine and deliberately not flagged: `&self.len`
        // cannot mutate. Only `&mut` / `&raw mut` escapes count.
        match rvalue {
            Rvalue::Ref { mutable: true, place } => touches_backing(place),
            Rvalue::AddressOf(true, place) => touches_backing(place),
            _ => false,
        }
    })
}

/// Whether a backing ESTABLISH obligation `Lt(alloc_size, len)` is trivially
/// UNSAT (the constructor establishes `alloc_size >= len`), provable WITHOUT a
/// solver: identical operands (`x < x`) or two constants with `a >= b`. Anything
/// else is treated conservatively as NOT established at this layer.
fn lt_is_unsat(f: &Formula) -> bool {
    let Formula::Lt(a, b) = f else { return false };
    if a == b {
        return true; // x < x is false
    }
    if let (Formula::Int(x), Formula::Int(y)) = (a.as_ref(), b.as_ref()) {
        return x >= y; // constant `x < y` is false exactly when x >= y
    }
    false
}

/// Like [`lt_is_unsat`], but two variables that resolve to the SAME local through
/// the constructor's copy-chains (`copy`) count as identical — so a pre-opt
/// `Lt(_5, _6)` where both temps copy the same `len` param is recognized as
/// `len < len` (UNSAT). Conservative: anything not provably equal is NOT
/// established.
fn lt_is_unsat_modulo_copies(
    f: &Formula,
    func: &VerifiableFunction,
    copy: &FxHashMap<usize, usize>,
) -> bool {
    if lt_is_unsat(f) {
        return true;
    }
    let Formula::Lt(a, b) = f else { return false };
    if let (Formula::Var(an, _), Formula::Var(bn, _)) = (a.as_ref(), b.as_ref()) {
        return canon_var_name(an, func, copy) == canon_var_name(bn, func, copy);
    }
    false
}

/// Build the constructor's copy-canonicalization map `dst_local -> src_local` for
/// `dst = Use(Copy|Move(src))` (both unprojected), gated on `dst` being assigned
/// at most once (SSA-stable) so a reassigned local never aliases unsoundly.
fn build_copy_canon(func: &VerifiableFunction) -> FxHashMap<usize, usize> {
    let mut assign_count: FxHashMap<usize, usize> = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.projections.is_empty()
            {
                *assign_count.entry(place.local).or_insert(0) += 1;
            }
        }
        if let trust_types::Terminator::Call { dest, .. } = &block.terminator
            && dest.projections.is_empty()
        {
            *assign_count.entry(dest.local).or_insert(0) += 1;
        }
    }
    let mut canon = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = stmt else { continue };
            let (trust_types::Operand::Copy(src) | trust_types::Operand::Move(src)) = op else {
                continue;
            };
            if place.projections.is_empty()
                && src.projections.is_empty()
                && assign_count.get(&place.local).copied().unwrap_or(0) <= 1
            {
                canon.insert(place.local, src.local);
            }
        }
    }
    canon
}

/// Resolve a formula variable name (`_N`, or a named local's name) to the
/// canonical name of the local it copy-chains to.
fn canon_var_name(name: &str, func: &VerifiableFunction, copy: &FxHashMap<usize, usize>) -> String {
    let Some(mut local) = var_name_to_local(name, func) else {
        return name.to_string();
    };
    // Follow the copy chain to its root (bounded by the map size; no cycles since
    // each entry is `dst -> src` with dst single-assigned).
    let mut seen = 0;
    while let Some(&src) = copy.get(&local) {
        if src == local || seen > func.body.locals.len() {
            break;
        }
        local = src;
        seen += 1;
    }
    func.body.locals.get(local).and_then(|l| l.name.clone()).unwrap_or_else(|| format!("_{local}"))
}

/// The local a formula variable names: `_N` -> N, else the index of the local
/// whose name matches (mirrors `operand_named_formula`'s naming).
fn var_name_to_local(name: &str, func: &VerifiableFunction) -> Option<usize> {
    if let Some(rest) = name.strip_prefix('_')
        && let Ok(n) = rest.parse::<usize>()
    {
        return Some(n);
    }
    func.body.locals.iter().position(|l| l.name.as_deref() == Some(name))
}

#[cfg(test)]
mod tests {
    use trust_types::UnwindEdge;
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
        VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn buf_ty() -> Ty {
        Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "Buf".into(),
            fields: vec![
                ("ptr".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                ("len".into(), Ty::Int { width: 64, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, }
    }

    fn func(
        name: &str,
        arg_count: usize,
        locals: Vec<LocalDecl>,
        blocks: Vec<BasicBlock>,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.into(),
            def_path: name.into(),
            span: span(),
            body: VerifiableBody { return_ty: Ty::Unit, locals, blocks, arg_count },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
        }
    }

    /// A constructor `Buf { ptr: mmap(len), len }` that ESTABLISHES the invariant
    /// (the alloc size IS `len`, so the establish obligation is `len < len`).
    fn establishing_ctor() -> VerifiableFunction {
        func(
            "Buf::map",
            1,
            vec![
                LocalDecl { index: 0, ty: buf_ty(), name: Some("ret".into()) },
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
            vec![
                // _2 = mmap(0, len, 0, 0, 0, 0)  -> alloc size bound to `len`
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: true,
                        func: "libc::mmap".into(),
                        args: vec![
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Move(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: span(),
                        atomic: None,
                    },
                },
                // _0 = Buf { ptr: move _2, len: move _1 }
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Buf".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(1))],
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
        )
    }

    /// `as_slice(&self) -> &[u8] { from_raw_parts(self.ptr, self.len) }` — a USE
    /// site, not a constructor.
    fn as_slice() -> VerifiableFunction {
        func(
            "Buf::as_slice",
            1,
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(buf_ty()) },
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
                            span: span(),
                        },
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(Operand::Copy(Place {
                                local: 1,
                                projections: vec![Projection::Deref, Projection::Field(1)],
                            })),
                            span: span(),
                        },
                    ],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::slice::from_raw_parts".into(),
                        args: vec![Operand::Move(Place::local(2)), Operand::Move(Place::local(3))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: span(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
        )
    }

    #[test]
    fn certifies_when_every_constructor_establishes() {
        // Whole "crate": one establishing constructor + one use site.
        let certified = certify_backing_invariants(&[establishing_ctor(), as_slice()]);
        assert!(
            certified.contains("Buf"),
            "Buf must be certified: its sole constructor establishes R"
        );
    }

    /// A constructor that copies the `len` param into DISTINCT temporaries before
    /// the mmap call and the aggregate — exactly what pre-optimization MIR does.
    /// The raw establish is `Lt(_4, _5)` (both copies of `len`); certification
    /// must canonicalize them through the copy-chain to recognize `len < len`
    /// (UNSAT) and certify. Without `build_copy_canon`/`lt_is_unsat_modulo_copies`
    /// this constructor reads as non-establishing and Buf fails to certify.
    fn establishing_ctor_with_copy_temps() -> VerifiableFunction {
        func(
            "Buf::map_copies",
            1,
            vec![
                LocalDecl { index: 0, ty: buf_ty(), name: Some("ret".into()) },
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
                LocalDecl { index: 3, ty: Ty::Int { width: 64, signed: false }, name: None },
                LocalDecl { index: 4, ty: Ty::Int { width: 64, signed: false }, name: None },
            ],
            vec![
                // _3 = copy len; _2 = mmap(0, move _3, 0, 0, 0, 0)
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                        span: span(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: true,
                        func: "libc::mmap".into(),
                        args: vec![
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Move(Place::local(3)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: span(),
                        atomic: None,
                    },
                },
                // _4 = copy len; _0 = Buf { ptr: move _2, len: move _4 }
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: span(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Aggregate(
                                AggregateKind::Adt {
                                    name: "Buf".into(),
                                    variant: 0,
                                    active_field: None,
                                    args: None,
                                },
                                vec![
                                    Operand::Move(Place::local(2)),
                                    Operand::Move(Place::local(4)),
                                ],
                            ),
                            span: span(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
        )
    }

    /// A constructor that casts the mmap result via the `.cast::<u8>()` METHOD
    /// (not an `as` cast) before storing it — exactly aterm's real `map_mut`
    /// (`mmap(...).cast::<u8>()`). The pointee-cast method must propagate
    /// provenance like an `as` cast, else the backing allocation size is lost and
    /// the establish becomes non-trivial. Without `is_ptr_cast_call` handling
    /// this constructor reads as non-establishing and Buf fails to certify.
    fn establishing_ctor_with_ptr_cast() -> VerifiableFunction {
        func(
            "Buf::map_cast",
            1,
            vec![
                LocalDecl { index: 0, ty: buf_ty(), name: Some("ret".into()) },
                LocalDecl {
                    index: 1,
                    ty: Ty::Int { width: 64, signed: false },
                    name: Some("len".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::Unit) },
                    name: Some("raw".into()),
                },
                LocalDecl {
                    index: 3,
                    ty: Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) },
                    name: Some("p".into()),
                },
            ],
            vec![
                // _2 = mmap(0, len, 0, 0, 0, 0)   (returns *mut c_void-ish)
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: true,
                        func: "libc::mmap".into(),
                        args: vec![
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Move(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                            Operand::Constant(ConstValue::Int(0)),
                        ],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: span(),
                        atomic: None,
                    },
                },
                // _3 = _2.cast::<u8>()   (pointee-cast METHOD, preserves provenance)
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "core::ptr::mut_ptr::<impl *mut T>::cast".into(),
                        args: vec![Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(2)),
                        span: span(),
                        atomic: None,
                    },
                },
                // _0 = Buf { ptr: move _3, len: move _1 }
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Aggregate(
                            AggregateKind::Adt {
                                name: "Buf".into(),
                                variant: 0,
                                active_field: None,
                                args: None,
                            },
                            vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(1))],
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
        )
    }

    #[test]
    fn certifies_through_ptr_cast_method() {
        let certified =
            certify_backing_invariants(&[establishing_ctor_with_ptr_cast(), as_slice()]);
        assert!(
            certified.contains("Buf"),
            "constructor stores `mmap(...).cast::<u8>()`; the pointee-cast method must \
             propagate provenance so the establish stays `len < len` and Buf certifies"
        );
    }

    #[test]
    fn certifies_through_copy_temporaries() {
        let certified =
            certify_backing_invariants(&[establishing_ctor_with_copy_temps(), as_slice()]);
        assert!(
            certified.contains("Buf"),
            "constructor copies `len` into temps before mmap+aggregate; canonicalization \
             through the copy-chain must still recognize `len < len` and certify Buf"
        );
    }

    #[test]
    fn not_certified_without_a_seen_constructor() {
        // Only the use site is present — no constructor seen, so the invariant
        // cannot be vouched for. MUST stay uncertified (fail-closed at use site).
        let certified = certify_backing_invariants(&[as_slice()]);
        assert!(!certified.contains("Buf"), "no constructor seen ⇒ must NOT certify");
    }

    #[test]
    fn not_certified_when_a_constructor_does_not_establish() {
        // A constructor `Buf { ptr: untracked, len }` whose pointer has no tracked
        // allocation size ⇒ establish obligation is `Lt(symbolic_size, len)`,
        // NOT trivially UNSAT ⇒ does not establish ⇒ deny.
        let bad = func(
            "Buf::from_raw",
            2,
            vec![
                LocalDecl { index: 0, ty: buf_ty(), name: Some("ret".into()) },
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
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Aggregate(
                        AggregateKind::Adt { name: "Buf".into(), variant: 0, active_field: None, args: None },
                        vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
        );
        let certified = certify_backing_invariants(&[bad, as_slice()]);
        assert!(!certified.contains("Buf"), "a non-establishing constructor ⇒ must NOT certify");
    }

    #[test]
    fn not_certified_when_a_backing_field_is_mutated() {
        // A method that writes `(*self).len = 0` could break R post-construction.
        let mutator = func(
            "Buf::clear_len",
            1,
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(buf_ty()) },
                    name: Some("self".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(1)],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
        );
        let certified = certify_backing_invariants(&[establishing_ctor(), mutator, as_slice()]);
        assert!(!certified.contains("Buf"), "a backing-field write ⇒ must NOT certify");
    }

    /// SOUNDNESS REGRESSION: handing out `&mut self.len` must deny certification
    /// exactly as a direct store does.
    ///
    /// `fn len_mut(&mut self) -> &mut usize { &mut self.len }` lowers to
    /// `_0 = &mut ((*_1).1)` — an `Rvalue::Ref` whose `Field` projection sits on
    /// the SOURCE place. The mutation scan looked only at destination places, so
    /// this was invisible: the struct certified, and the certificate licenses the
    /// use-site ASSUME `alloc_size >= self.len`. A caller could then set `len` to
    /// anything while that ASSUME stood, which turns a CAUGHT out-of-bounds
    /// obligation into PROVED.
    #[test]
    fn not_certified_when_a_backing_field_escapes_by_mut_reference() {
        let escaper = func(
            "Buf::len_mut",
            1,
            vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Ref {
                        mutable: true,
                        inner: Box::new(Ty::Int { width: 64, signed: false }),
                    },
                    name: None,
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(buf_ty()) },
                    name: Some("self".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Ref {
                        mutable: true,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(1)],
                        },
                    },
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
        );
        let certified = certify_backing_invariants(&[establishing_ctor(), escaper, as_slice()]);
        assert!(
            !certified.contains("Buf"),
            "a `&mut` escape of a backing field ⇒ must NOT certify"
        );
    }

    /// SOUNDNESS REGRESSION: a decoy struct must not hide a real mutator.
    ///
    /// The relevance test used `detect_backing_struct`, which returns the FIRST
    /// backing-shaped local. A mutator of `Buf` that also mentions another
    /// backing-shaped struct EARLIER in its locals resolved to that other struct,
    /// hit the `continue`, and was never scanned for `Buf` — so
    /// `broken_by_mutation` stayed false, `Buf` certified, and the use-site
    /// ASSUME `alloc_size >= self.len` was published on a struct whose length a
    /// caller could change after construction.
    #[test]
    fn a_decoy_backing_struct_cannot_hide_a_mutator() {
        let other_ty = || Ty::Adt {
            adt_kind: None,
            layout: None,
            variants: Vec::new(),
            name: "Other".into(),
            fields: vec![
                ("p".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                ("n".into(), Ty::Int { width: 64, signed: false }),
            ],
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
        };
        // Mutates `Buf::len`, but `Other` occupies an earlier local.
        let hidden_mutator = func(
            "evil",
            2,
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(other_ty()) },
                    name: Some("decoy".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: true, inner: Box::new(buf_ty()) },
                    name: Some("buf".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place {
                        local: 2,
                        projections: vec![Projection::Deref, Projection::Field(1)],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(9999))),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
        );
        let certified =
            certify_backing_invariants(&[establishing_ctor(), hidden_mutator, as_slice()]);
        assert!(
            !certified.contains("Buf"),
            "a decoy backing struct in an earlier local must not hide a mutator of Buf"
        );
    }

    /// The counterpart: a SHARED borrow of a backing field cannot mutate, so it
    /// must not deny certification. Without this, the fix above would be an
    /// over-tightening that silently disables the whole backing lane for any
    /// struct with a `fn len(&self) -> &usize`.
    #[test]
    fn shared_borrow_of_a_backing_field_still_certifies() {
        let reader = func(
            "Buf::len_ref",
            1,
            vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Int { width: 64, signed: false }),
                    },
                    name: None,
                },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: false, inner: Box::new(buf_ty()) },
                    name: Some("self".into()),
                },
            ],
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Ref {
                        mutable: false,
                        place: Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(1)],
                        },
                    },
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
        );
        let certified = certify_backing_invariants(&[establishing_ctor(), reader, as_slice()]);
        assert!(
            certified.contains("Buf"),
            "a shared borrow cannot mutate, so it must not deny certification"
        );
    }

    #[test]
    fn lt_is_unsat_recognizes_trivial_cases() {
        let v = Formula::Var("len".into(), trust_types::Sort::Int);
        assert!(lt_is_unsat(&Formula::Lt(Box::new(v.clone()), Box::new(v))), "x < x is UNSAT");
        assert!(
            lt_is_unsat(&Formula::Lt(Box::new(Formula::Int(64)), Box::new(Formula::Int(32)))),
            "64 < 32 is UNSAT"
        );
        assert!(
            !lt_is_unsat(&Formula::Lt(Box::new(Formula::Int(32)), Box::new(Formula::Int(64)))),
            "32 < 64 is SAT"
        );
        let a = Formula::Var("a".into(), trust_types::Sort::Int);
        let b = Formula::Var("b".into(), trust_types::Sort::Int);
        assert!(
            !lt_is_unsat(&Formula::Lt(Box::new(a), Box::new(b))),
            "a < b unknown ⇒ not established"
        );
    }
}
