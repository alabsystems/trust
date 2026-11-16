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
//!
//! A complete body set is necessary, not sufficient. This pass recognizes a
//! constructor as a struct literal and a mutator as a store to (or `&mut` of) a
//! backing field, in a body that has a local of the struct's type. In-crate code
//! can reach the same bytes without either — a raw pointer cast, a transmute, a
//! union, a foreign or unsafe callee, a generic body instantiated with the struct —
//! and each of those certified the struct until 2026-09-30. The compiler's escape
//! census (`backing_escape_census` in `rustc_mir_transform`'s `trust_verify.rs`)
//! scans the same inventory on its rustc MIR and removes such a struct from this
//! pass's result; see docs/TCB.md, "A `#[trust::backing]` certificate".

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{AggregateKind, Formula, Projection, Rvalue, Statement, VerifiableFunction};

use crate::sep_engine::{detect_backing_struct, establish_formulas, mentions_backing_struct};

/// Certify the backing invariants provable from `functions`, returning the set
/// of struct names whose invariant is established by every constructor and
/// broken by none. A name in the result authorizes the use-site ASSUME (in
/// `sep_engine`) to license `alloc_size >= self.len` and so discharge a guarded
/// access. See the module docs for the soundness contract on `functions`.
#[must_use]
pub fn certify_backing_invariants(functions: &[VerifiableFunction]) -> FxHashSet<String> {
    // Universe of backing structs referenced anywhere, as name -> (ptr, len).
    // `detect_backing_struct` only inspects `func.body.locals`, which tail-call
    // expansion does not modify, so we can check whether any backing struct
    // exists before expanding tail calls.
    let mut shapes: std::collections::BTreeMap<String, (usize, usize)> =
        std::collections::BTreeMap::new();
    for func in functions {
        if let Some((name, pf, lf)) = detect_backing_struct(func) {
            shapes.entry(name).or_insert((pf, lf));
        }
    }
    if shapes.is_empty() || !functions.iter().any(constructs_struct) {
        return FxHashSet::default();
    }

    // Constructor/mutator certification is authority-bearing.  Present every
    // TailCall through the canonical call-plus-return projection so the
    // separation engine and write-set scanners cannot silently skip it.
    let expanded_functions: Vec<std::borrow::Cow<'_, VerifiableFunction>> =
        functions.iter().map(VerifiableFunction::with_tail_calls_expanded).collect();

    let mut certified = FxHashSet::default();
    for (name, (pf, lf)) in shapes {
        let mut saw_constructor = false;
        let mut all_establish = true;
        let mut broken_by_mutation = false;

        for func in &expanded_functions {
            if broken_by_mutation || !all_establish {
                break;
            }
            let func: &VerifiableFunction = func;
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
            if !mentions_backing_struct(func, &name) {
                continue;
            }

            if constructs_struct(func) {
                let establishes = establish_formulas(func, &name, pf, lf);
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
                    let mut canon: Option<FxHashMap<usize, usize>> = None;
                    if !establishes.iter().all(|f| {
                        lt_is_unsat(f) || {
                            let canon = canon.get_or_insert_with(|| build_copy_canon(func));
                            lt_is_unsat_modulo_copies(f, func, canon)
                        }
                    }) {
                        all_establish = false;
                    }
                }
            }

            if writes_backing_field(func, pf, lf) {
                broken_by_mutation = true;
            }
        }

        // TINV step 4c (2026-10-05): the KEYED scan, over EVERY function with no
        // relevance gate. `writes_backing_field` above keys on a bare field index in
        // relevant bodies only; `place_write` names the ADT each written field belongs
        // to, so it also sees a store through `&mut Wrap`, a `*mut Buf` parameter, a
        // Box-elaborated raw temp, a call destination, and a `&raw const` of the field
        // (minus the extractor's fake-metadata borrow). The result is the UNION: this
        // only adds denials. Unresolved and unlocatable writes and call arguments stay
        // the rustc census's to deny.
        if saw_constructor
            && all_establish
            && !broken_by_mutation
            && expanded_functions
                .iter()
                .any(|func| crate::place_write::writes_fields_of_expanded(func, &name, &[pf, lf]))
        {
            broken_by_mutation = true;
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
        // cannot mutate. This asks what `self` POINTS TO, so its channels are the
        // write-channel rule's (`generate::borrow_write_target`) — except `&raw const`,
        // which is DELEGATED, not dropped: a `&raw const` of a backing field used as a
        // pointer (a valid `*const -> *mut` cast root, defined to write through under
        // Tree Borrows when derived from `&mut self`) is denied by the ADT-keyed scan
        // this one is unioned with over every function (`place_write::writes_fields_of`,
        // TINV step 4c), which exempts the extractor's fake-metadata borrow (one
        // `PtrMetadata` use). Counting it here as well would deny that borrow too.
        // Pinned by `not_certified_when_a_backing_field_escapes_by_raw_const_pointer`
        // and `a_raw_const_borrow_of_len_denies_unless_it_is_fake_metadata`.
        crate::generate::borrow_write_target(func, rvalue).is_some_and(|place| {
            touches_backing(place) && !matches!(rvalue, Rvalue::AddressOf(false, _))
        })
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
        let Some(la) = canon_var_local(func, an, copy) else { return false };
        let Some(lb) = canon_var_local(func, bn, copy) else { return false };
        if la == lb {
            return true;
        }
        return match (
            func.body.locals.get(la).and_then(|l| l.name.as_deref()),
            func.body.locals.get(lb).and_then(|l| l.name.as_deref()),
        ) {
            (Some(na), Some(nb)) => na == nb,
            (None, None) => false,
            (Some(n), None) => {
                n.strip_prefix('_').and_then(|r| r.parse::<usize>().ok()) == Some(lb)
            }
            (None, Some(n)) => {
                n.strip_prefix('_').and_then(|r| r.parse::<usize>().ok()) == Some(la)
            }
        };
    }
    false
}

/// Build the constructor's copy-canonicalization map `dst_local -> src_local` for
/// `dst = Use(Copy|Move(src))` (both unprojected), gated on `dst` holding AT MOST
/// ONE VALUE so a reassigned local never aliases unsoundly. `local_defs::value_count`
/// and not a block tally: a PARAMETER is defined at ENTRY, so `mut d` copied over once
/// would otherwise canonicalize the parameter's name to `src` on the edge that still
/// holds the incoming argument.
fn build_copy_canon(func: &VerifiableFunction) -> FxHashMap<usize, usize> {
    let mut canon = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue: Rvalue::Use(op), .. } = stmt else { continue };
            let (trust_types::Operand::Copy(src) | trust_types::Operand::Move(src)) = op else {
                continue;
            };
            // PERF-COMPILER-VCGEN-587: parameters already have an entry value (1) plus
            // this `Statement::Assign` (≥ 2), so `value_count(func, place.local).is_at_most(1)`
            // is always false for parameters.
            if place.projections.is_empty()
                && src.projections.is_empty()
                && !crate::local_defs::is_parameter(func, place.local)
                && crate::local_defs::value_count(func, place.local).is_at_most(1)
            {
                canon.insert(place.local, src.local);
            }
        }
    }
    canon
}

/// Resolve a formula variable name (`_N`, or a named local's name) to the
/// canonical local index it copy-chains to.
fn canon_var_local(
    func: &VerifiableFunction,
    name: &str,
    copy: &FxHashMap<usize, usize>,
) -> Option<usize> {
    let mut local = var_name_to_local(name, func)?;
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
    Some(local)
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
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, SourceSpan, Terminator, Ty,
        UnwindEdge, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn span() -> SourceSpan {
        SourceSpan::default()
    }

    fn buf_ty() -> Ty {
        Ty::Adt {
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "Buf".into(),
            fields: vec![
                ("ptr".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                ("len".into(), Ty::Int { width: 64, signed: false }),
            ]
            .into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        }
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
            body: VerifiableBody {
                return_ty: Ty::Unit,
                locals,
                blocks,
                arg_count,
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("libc::mmap"),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::slice::raw::from_raw_parts",
                        ),
                        is_foreign: false,
                        func: "core::slice::raw::from_raw_parts".into(),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("libc::mmap"),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("libc::mmap"),
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
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(
                            "core::ptr::mut_ptr::<impl *mut T>::cast",
                        ),
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
                        AggregateKind::Adt {
                            name: "Buf".into(),
                            variant: 0,
                            active_field: None,
                            args: None,
                        },
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
            variants: Vec::new().into(),
            name: "Other".into(),
            fields: vec![
                ("p".into(), Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u8()) }),
                ("n".into(), Ty::Int { width: 64, signed: false }),
            ]
            .into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            arbitrary_precision: None,
            validity_wrapper: None,
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

    /// Trust (2026-09-30): the same escape through `&raw const` —
    /// `_0 = &raw const ((*_1).1)` with `self: &mut Buf`. A `*const` is a valid
    /// `*const -> *mut` cast root (`trust_types::Statement::escapes_local` says so for
    /// the local-keyed question), and a write through a raw pointer derived from a
    /// `&mut` is not UB under Tree Borrows (raw pointers are not retagged), so a
    /// caller holding it can set `len` exactly as through `&mut self.len`. The scan
    /// listed `&mut` / `&raw mut` only.
    #[test]
    fn not_certified_when_a_backing_field_escapes_by_raw_const_pointer() {
        let escaper = func(
            "Buf::len_ptr",
            1,
            vec![
                LocalDecl {
                    index: 0,
                    ty: Ty::RawPtr {
                        mutable: false,
                        pointee: Box::new(Ty::Int { width: 64, signed: false }),
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
                    rvalue: Rvalue::AddressOf(
                        false,
                        Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(1)],
                        },
                    ),
                    span: span(),
                }],
                terminator: Terminator::Return,
            }],
        );
        let certified = certify_backing_invariants(&[establishing_ctor(), escaper, as_slice()]);
        assert!(
            !certified.contains("Buf"),
            "a `&raw const` escape of a backing field ⇒ must NOT certify"
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

    // ---- TINV step 4c: the keyed scan (`place_write`) only adds denials ----------

    fn wrap_ty() -> Ty {
        Ty::Adt {
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "Wrap".into(),
            fields: vec![("b".into(), buf_ty())].into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        }
    }

    fn one_stmt_fn(
        name: &str,
        param: Ty,
        extra: Vec<Ty>,
        stmts: Vec<Statement>,
    ) -> VerifiableFunction {
        let mut locals = vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl { index: 1, ty: param, name: Some("p".into()) },
        ];
        for (i, ty) in extra.into_iter().enumerate() {
            locals.push(LocalDecl { index: 2 + i, ty, name: None });
        }
        func(
            name,
            1,
            locals,
            vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
        )
    }

    fn store_zero(place: Place) -> Statement {
        Statement::Assign {
            place,
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
            span: span(),
        }
    }

    fn certifies_with(extra: VerifiableFunction) -> bool {
        certify_backing_invariants(&[establishing_ctor(), extra, as_slice()]).contains("Buf")
    }

    /// The relevance gate skipped a body holding only `&mut Wrap`, so the index scan
    /// never saw `(*w).b.len = 0`.
    #[test]
    fn not_certified_when_a_wrapper_writes_the_backing_field() {
        let wrapper = one_stmt_fn(
            "Wrap::clear",
            Ty::Ref { mutable: true, inner: Box::new(wrap_ty()) },
            vec![],
            vec![store_zero(Place {
                local: 1,
                projections: vec![Projection::Deref, Projection::Field(0), Projection::Field(1)],
            })],
        );
        assert!(!certifies_with(wrapper));
    }

    /// The relevance gate peels only references, so a `*mut Buf` parameter was skipped.
    #[test]
    fn not_certified_through_a_raw_ptr_param() {
        let raw = one_stmt_fn(
            "clear_raw",
            Ty::RawPtr { mutable: true, pointee: Box::new(buf_ty()) },
            vec![],
            vec![store_zero(Place {
                local: 1,
                projections: vec![Projection::Deref, Projection::Field(1)],
            })],
        );
        assert!(!certifies_with(raw));
    }

    /// A `&raw const` of the length field that is then used as a pointer is a write
    /// channel; the extractor's fake-metadata borrow (one `PtrMetadata` use) is not.
    #[test]
    fn a_raw_const_borrow_of_len_denies_unless_it_is_fake_metadata() {
        let raw_u64 =
            Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Int { width: 64, signed: false }) };
        let borrow = |extra_use: bool| {
            let mut stmts = vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::AddressOf(
                        false,
                        Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(1)],
                        },
                    ),
                    span: span(),
                },
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::UnaryOp(
                        trust_types::UnOp::PtrMetadata,
                        Operand::Copy(Place::local(2)),
                    ),
                    span: span(),
                },
            ];
            if extra_use {
                stmts.push(Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(2))),
                    span: span(),
                });
            }
            one_stmt_fn(
                "Buf::peek",
                Ty::Ref { mutable: false, inner: Box::new(buf_ty()) },
                vec![raw_u64.clone(), Ty::Unit, raw_u64.clone()],
                stmts,
            )
        };
        assert!(certifies_with(borrow(false)), "a fake-metadata borrow must not deny");
        assert!(!certifies_with(borrow(true)), "an escaping `&raw const` of len must deny");
        // INT-RAWCONST-HAVOC-1 (2026-10-06), restated at the wave-19 merge (2026-10-09):
        // the index scan DELEGATES `&raw const` to the keyed `place_write` classifier it
        // is unioned with (main's H2 design, above), so the pin is on the union. Through
        // a `&mut Buf` receiver, too, an escaping `&raw const (*p).len` denies
        // certification.
        let mut through_mut = borrow(true);
        through_mut.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(buf_ty()) };
        assert!(!certifies_with(through_mut), "an escaping `&raw const` of len through `&mut Buf`");
    }

    /// A call's destination is a write the `Assign`-only scan never saw.
    #[test]
    fn not_certified_when_a_backing_field_is_a_call_destination() {
        let mut caller = one_stmt_fn(
            "Buf::reset",
            Ty::Ref { mutable: true, inner: Box::new(buf_ty()) },
            vec![],
            vec![],
        );
        caller.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Call {
                    func: "big".into(),
                    args: vec![],
                    dest: Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(1)],
                    },
                    target: Some(BlockId(1)),
                    span: span(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Unreachable,
                    callee_identity: None,
                    callee_key: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ];
        assert!(!certifies_with(caller));
    }

    /// The same write to a same-index field of ANOTHER struct does not deny.
    #[test]
    fn a_same_index_write_to_another_adt_does_not_deny() {
        let other = Ty::Adt {
            adt_kind: None,
            layout: None,
            variants: Vec::new().into(),
            name: "Other".into(),
            fields: vec![
                ("a".into(), Ty::Int { width: 64, signed: false }),
                ("b".into(), Ty::Int { width: 64, signed: false }),
            ]
            .into(),
            disc_index_safe: false,
            faithful_enum_repr: None,
            enum_layout: None,
            arbitrary_precision: None,
            validity_wrapper: None,
        };
        let unrelated = one_stmt_fn(
            "Other::clear",
            Ty::Ref { mutable: true, inner: Box::new(other) },
            vec![],
            vec![store_zero(Place {
                local: 1,
                projections: vec![Projection::Deref, Projection::Field(1)],
            })],
        );
        assert!(certifies_with(unrelated));
    }
}
