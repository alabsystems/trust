// trust_vcgen/rusthorn_encoding.rs: RustHorn borrow encoding for trust_wp CHC verification
//
// Implements the RustHorn encoding (Matsushita et al., ESOP 2020) that translates
// Rust ownership and borrowing semantics into Constrained Horn Clause (CHC) constraints
// for trust-wp-based deductive verification.
//
// Key idea: Mutable references become prophecy variables. For `&'a mut T`:
//   - `*v` (current_var): the value at borrow creation
//   - `^v` (prophecy_var): the value returned when the borrow expires
//
// This lets us reason about `&mut` code in pure first-order logic without
// separation logic, making it amenable to CHC solvers like Spacer/trust_wp.
//
// Part of Epic #552, implements #589.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BorrowEncoding, Formula, ProphecyVar, Rvalue, Sort, SortFromTy, Statement, Terminator,
    VerifiableFunction,
};

use crate::chc::{ChcClause, ChcError, ChcPredicate, ChcSystem, ClauseRole};

// ---------------------------------------------------------------------------
// MIR scanning: extract borrow operations from the function body
// ---------------------------------------------------------------------------

/// Scan a function's MIR body and produce a RustHorn borrow encoding.
///
/// Walks all statements looking for `Rvalue::Ref` (borrow creation) and
/// assignment-to-deref patterns (borrow expiry / mutation through borrow).
/// Produces prophecy variables and the constraints needed for CHC encoding.
#[must_use]
pub fn encode_borrows(func: &VerifiableFunction) -> BorrowEncoding {
    let mut encoding = BorrowEncoding::default();
    // `(destination local, prophecy index)`. The index is the borrow EVENT's
    // identity: two sequential borrows of the same source place must not share
    // one prophecy pair merely because their source names are equal.
    let mut active_borrows: Vec<(usize, usize)> = Vec::new();

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            // Borrow creation: `_dst = &[mut] _src`
            if let Statement::Assign {
                place, rvalue: Rvalue::Ref { mutable, place: src }, ..
            } = stmt
            {
                let place_name = local_name(func, src.local);
                let sort = local_sort(func, src.local);
                let mut prophecy = if *mutable {
                    ProphecyVar::mutable_borrow(&place_name, sort)
                } else {
                    ProphecyVar::shared_borrow(&place_name, sort)
                };

                // The legacy spelling (`x__curr`, `x__final`) is already unique
                // for the first borrow of a collision-safe place. A later
                // borrow event for that place needs its own reserved verifier
                // symbols, or predicate signatures contain duplicate parameters
                // and expiry of either borrow constrains both prophecies.
                if encoding.prophecies.iter().any(|prior| prior.place == place_name) {
                    let event = encoding.prophecies.len();
                    let stem =
                        crate::generated_formula_symbol("rusthorn", &format!("borrow_{event}"));
                    prophecy.current_var = format!("{stem}__curr");
                    prophecy.prophecy_var = format!("{stem}__final");
                }

                // Shared borrows have identity constraint: ^v = *v. Add it
                // only after assigning this event's unique logical names.
                if !*mutable {
                    encoding.creation_constraints.push(prophecy.identity_constraint());
                }
                // Overwriting a reference destination ends its previous borrow
                // event. This scan cannot attach the old expiry equality to
                // this exact program point, so dropping that equality is safer
                // than resolving the old prophecy at some later Drop.
                active_borrows.retain(|(dst_local, _)| place.local != *dst_local);
                let prophecy_index = encoding.prophecies.len();
                encoding.prophecies.push(prophecy);
                active_borrows.push((place.local, prophecy_index));
            }
        }

        // Check terminators for drops that expire borrows
        if let Terminator::Drop { place, .. } = &block.terminator {
            // When a reference is dropped, the borrow expires.
            // Find prophecies associated with this local and generate
            // expiry constraints.
            for (dst_local, prophecy_index) in &active_borrows {
                if place.local == *dst_local {
                    let prophecy = &encoding.prophecies[*prophecy_index];
                    if !prophecy.mutable {
                        continue;
                    }
                    // At borrow expiry, the prophecy variable equals
                    // the current value of the source place.
                    let current_val = Formula::Var(prophecy.place.clone(), prophecy.sort.clone());
                    encoding.expiry_constraints.push(prophecy.resolve(current_val));
                }
            }
            // A later borrow assigned to the same destination is a distinct
            // event. Do not let this expired event be resolved again by a
            // later Drop terminator.
            active_borrows.retain(|(dst_local, _)| place.local != *dst_local);
        }
    }

    // Deliberately do not synthesize aliasing assumptions here. This MIR scan
    // has no path-sensitive region/liveness model, so two borrow EVENTS of one
    // place may be sequential. Encoding their exclusivity as `!(true && true)`
    // adds `false` to every CHC premise and can vacuously prove any query.
    // Actual overlap is an ownership-admission concern; omitting an unproven
    // assumption here is the conservative (proof-losing, never proof-gaining)
    // behavior.

    encoding
}

/// Augment a CHC system with RustHorn borrow encoding.
///
/// For each predicate in the system, extends its parameter list with the
/// prophecy variables from the borrow encoding. Entry clauses get creation
/// constraints, exit clauses get expiry constraints, and all clauses get any
/// explicitly supplied aliasing constraints. The MIR scanner itself does not
/// invent path-insensitive aliasing assumptions.
#[must_use]
pub fn augment_chc_with_borrows(system: &ChcSystem, encoding: &BorrowEncoding) -> ChcSystem {
    if encoding.is_empty() {
        return system.clone();
    }

    let prophecy_params = encoding.predicate_params();

    // Extend predicate signatures with prophecy variables
    let predicates: Vec<ChcPredicate> = system
        .predicates
        .iter()
        .map(|pred| {
            let mut params = pred.params.clone();
            params.extend(prophecy_params.clone());
            ChcPredicate { name: pred.name.clone(), params }
        })
        .collect();

    // Augment clause constraints with borrow encoding
    let clauses: Vec<ChcClause> = system
        .clauses
        .iter()
        .zip(system.roles.iter())
        .map(|(clause, role)| {
            let mut extra_constraints = Vec::new();

            // All clauses get aliasing constraints
            let aliasing = encoding.aliasing_formula();
            if aliasing != Formula::Bool(true) {
                extra_constraints.push(aliasing);
            }

            match role {
                ClauseRole::Entry => {
                    // Entry clauses: add creation constraints (prophecy introduction)
                    let creation = encoding.creation_formula();
                    if creation != Formula::Bool(true) {
                        extra_constraints.push(creation);
                    }
                }
                ClauseRole::Exit => {
                    // Exit clauses: add expiry constraints (prophecy resolution)
                    let expiry = encoding.expiry_formula();
                    if expiry != Formula::Bool(true) {
                        extra_constraints.push(expiry);
                    }
                }
                ClauseRole::Inductive => {
                    // Inductive clauses: prophecy variables flow through unchanged
                    // (they are parameters of the predicate, not modified by the body)
                }
                ClauseRole::Safety => {
                    // Safety query clauses are not a rusthorn/prophecy construct
                    // (they encode a loop-carried bounds/overflow obligation); no
                    // prophecy creation/expiry applies.
                }
            }

            // Extend head/body atoms with prophecy arguments
            let head = clause.head.as_ref().map(|atom| {
                let mut args = atom.args.clone();
                for p in &encoding.prophecies {
                    args.push(Formula::Var(p.current_var.clone(), p.sort.clone()));
                    args.push(Formula::Var(p.prophecy_var.clone(), p.sort.clone()));
                }
                crate::chc::ChcAtom { predicate: atom.predicate.clone(), args }
            });

            let body_atoms: Vec<crate::chc::ChcAtom> = clause
                .body_atoms
                .iter()
                .map(|atom| {
                    let mut args = atom.args.clone();
                    for p in &encoding.prophecies {
                        args.push(Formula::Var(p.current_var.clone(), p.sort.clone()));
                        args.push(Formula::Var(p.prophecy_var.clone(), p.sort.clone()));
                    }
                    crate::chc::ChcAtom { predicate: atom.predicate.clone(), args }
                })
                .collect();

            let constraint = if extra_constraints.is_empty() {
                clause.constraint.clone()
            } else {
                extra_constraints.insert(0, clause.constraint.clone());
                Formula::And(extra_constraints)
            };

            ChcClause {
                head,
                body_atoms,
                constraint,
                label: format!("{} [rusthorn]", clause.label),
            }
        })
        .collect();

    ChcSystem {
        predicates,
        clauses,
        roles: system.roles.clone(),
        function_name: system.function_name.clone(),
    }
}

/// Build a CHC system with RustHorn encoding for a function.
///
/// Convenience function that runs the standard CHC encoding (from `chc.rs`)
/// and then augments it with prophecy variables from borrow analysis.
///
/// Returns `Ok(None)` if the function has no loops (CHC encoding requires loops).
/// Any CHC encoding failure is returned explicitly so unsupported loop MIR
/// cannot be mistaken for an obligation-free function.
pub fn encode_function_with_borrows(
    func: &VerifiableFunction,
) -> Result<Option<(ChcSystem, BorrowEncoding)>, ChcError> {
    let system = match crate::chc::encode_function_loops(func) {
        Ok(system) => system,
        Err(ChcError::NoLoops { .. }) => return Ok(None),
        Err(err) => return Err(err),
    };
    let encoding = encode_borrows(func);
    let augmented = augment_chc_with_borrows(&system, &encoding);
    Ok(Some((augmented, encoding)))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Get the collision-safe formula name for a local variable.
fn local_name(func: &VerifiableFunction, local: usize) -> String {
    crate::place_to_var_name(func, &trust_types::Place::local(local))
}

/// Get the SMT sort for a local variable.
fn local_sort(func: &VerifiableFunction, local: usize) -> Sort {
    // LocalDecl.index is the Trust IR identity; vector position is not. Public
    // standalone callers may provide sparse/reordered tables, while duplicate
    // indices are ambiguous and therefore receive only the conservative legacy
    // fallback (the checked CHC entry point rejects malformed Trust IR first).
    let mut matches = func.body.locals.iter().filter(|decl| decl.index == local);
    match (matches.next(), matches.next()) {
        (Some(decl), None) => Sort::from_ty(&decl.ty),
        _ => Sort::Int,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, Sort,
        SourceSpan, Statement, Terminator, Ty, VerifiableBody,
    };

    use super::*;

    /// Build a function with a mutable borrow:
    /// ```
    /// fn inc(x: &mut u32) { *x += 1; }
    /// ```
    /// Simplified MIR:
    ///   _0: ()           (return)
    ///   _1: &mut u32     (arg: x)
    ///   _2: u32          (temporary)
    fn mutable_borrow_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "inc".to_string(),
            def_path: "test::inc".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl {
                        index: 1,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                        name: Some("x".into()),
                    },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("val".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        // val = &mut x (reborrow for the read-modify-write)
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with a shared borrow:
    /// ```
    /// fn read(x: &u32) -> u32 { *x }
    /// ```
    fn shared_borrow_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "read".to_string(),
            def_path: "test::read".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) },
                        name: Some("r".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 1,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Two distinct, shadowed source locals in a reordered declaration table.
    /// Formula identity must come from `LocalDecl.index`, not vector position
    /// or the non-unique source/debug name.
    fn shadowed_reordered_borrows_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "shadowed_reordered".to_string(),
            def_path: "test::shadowed_reordered".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 2, ty: Ty::u64(), name: Some("x".into()) },
                    LocalDecl { index: 1, ty: Ty::u8(), name: Some("x".into()) },
                    LocalDecl {
                        index: 4,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u64()) },
                        name: Some("r64".into()),
                    },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u8()) },
                        name: Some("r8".into()),
                    },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(2) },
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Borrow `x`, end that event, then borrow `x` again. A function-wide
    /// same-place test must not misclassify these events as overlapping.
    fn sequential_mutable_reborrows_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "sequential_reborrows".to_string(),
            def_path: "test::sequential_reborrows".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                        name: Some("first".into()),
                    },
                    LocalDecl {
                        index: 3,
                        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
                        name: Some("second".into()),
                    },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Drop {
                            unwind: trust_types::UnwindEdge::Unreachable,
                            place: Place::local(2),
                            target: BlockId(1),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Drop {
                            unwind: trust_types::UnwindEdge::Unreachable,
                            place: Place::local(3),
                            target: BlockId(2),
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a function with no borrows.
    fn no_borrow_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "test::add".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::u32(), name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::u32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    /// Build a loop whose body contains unsupported MIR. RustHorn must
    /// propagate the CHC failure instead of returning None as if no loop existed.
    fn loop_with_unsupported_update() -> VerifiableFunction {
        VerifiableFunction {
            name: "unsupported_loop".to_string(),
            def_path: "test::unsupported_loop".to_string(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                    LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".into()) },
                    LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock {
                        id: BlockId(1),
                        stmts: vec![Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Lt,
                                Operand::Copy(Place::local(2)),
                                Operand::Copy(Place::local(1)),
                            ),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::SwitchInt {
                            discr: Operand::Copy(Place::local(3)),
                            targets: vec![(1, BlockId(2))],
                            otherwise: BlockId(3),
                            exhaustive_enum_unreachable: false,
                            span: SourceSpan::default(),
                        },
                    },
                    BasicBlock {
                        id: BlockId(2),
                        stmts: vec![Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Unsupported {
                                kind: "Rvalue::ThreadLocalRef".into(),
                                detail: "thread-local address semantics are not modeled".into(),
                                operands: vec![],
                            },
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn loop_with_u8_wrapping_contract() -> VerifiableFunction {
        let mut func = loop_with_unsupported_update();
        func.name = "rusthorn_u8_wrapping_contract".to_string();
        func.def_path = "test::rusthorn_u8_wrapping_contract".to_string();
        func.body.locals[1].ty = Ty::u8();
        func.body.locals[2].ty = Ty::u8();
        func.preconditions = vec![Formula::Eq(
            Box::new(Formula::Add(
                Box::new(Formula::Var("n".into(), Sort::Int)),
                Box::new(Formula::Int(1)),
            )),
            Box::new(Formula::Int(0)),
        )];
        func
    }

    // -- ProphecyVar unit tests --

    #[test]
    fn test_prophecy_var_mutable_borrow() {
        let p = ProphecyVar::mutable_borrow("x", Sort::Int);
        assert_eq!(p.place, "x");
        assert_eq!(p.current_var, "x__curr");
        assert_eq!(p.prophecy_var, "x__final");
        assert!(p.mutable);
    }

    #[test]
    fn test_prophecy_var_shared_borrow() {
        let p = ProphecyVar::shared_borrow("y", Sort::BitVec(32));
        assert_eq!(p.place, "y");
        assert_eq!(p.current_var, "y__curr");
        assert_eq!(p.prophecy_var, "y__final");
        assert!(!p.mutable);
        assert_eq!(p.sort, Sort::BitVec(32));
    }

    #[test]
    fn test_prophecy_identity_constraint() {
        let p = ProphecyVar::shared_borrow("x", Sort::Int);
        let constraint = p.identity_constraint();
        assert!(matches!(&constraint, Formula::Eq(lhs, rhs)
            if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "x__curr")
            && matches!(rhs.as_ref(), Formula::Var(name, _) if name == "x__final")
        ));
    }

    #[test]
    fn test_prophecy_resolve() {
        let p = ProphecyVar::mutable_borrow("x", Sort::Int);
        let final_val = Formula::Add(
            Box::new(Formula::Var("x__curr".into(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );
        let resolved = p.resolve(final_val.clone());
        assert!(matches!(&resolved, Formula::Eq(lhs, rhs)
            if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "x__final")
            && **rhs == final_val
        ));
    }

    // -- BorrowEncoding unit tests --

    #[test]
    fn test_borrow_encoding_empty() {
        let enc = BorrowEncoding::default();
        assert!(enc.is_empty());
        assert_eq!(enc.prophecy_count(), 0);
        assert!(enc.predicate_params().is_empty());
        assert_eq!(enc.creation_formula(), Formula::Bool(true));
        assert_eq!(enc.expiry_formula(), Formula::Bool(true));
        assert_eq!(enc.aliasing_formula(), Formula::Bool(true));
        assert_eq!(enc.full_constraint(), Formula::Bool(true));
    }

    #[test]
    fn test_borrow_encoding_predicate_params() {
        let mut enc = BorrowEncoding::default();
        enc.prophecies.push(ProphecyVar::mutable_borrow("x", Sort::Int));
        enc.prophecies.push(ProphecyVar::shared_borrow("y", Sort::BitVec(32)));

        let params = enc.predicate_params();
        assert_eq!(params.len(), 4); // 2 vars per prophecy
        assert_eq!(params[0], ("x__curr".into(), Sort::Int));
        assert_eq!(params[1], ("x__final".into(), Sort::Int));
        assert_eq!(params[2], ("y__curr".into(), Sort::BitVec(32)));
        assert_eq!(params[3], ("y__final".into(), Sort::BitVec(32)));
    }

    #[test]
    fn test_borrow_encoding_creation_formula_single() {
        let mut enc = BorrowEncoding::default();
        enc.creation_constraints.push(Formula::Bool(false));
        assert_eq!(enc.creation_formula(), Formula::Bool(false));
    }

    #[test]
    fn test_borrow_encoding_creation_formula_multiple() {
        let mut enc = BorrowEncoding::default();
        enc.creation_constraints.push(Formula::Bool(true));
        enc.creation_constraints.push(Formula::Bool(false));
        assert!(matches!(enc.creation_formula(), Formula::And(terms) if terms.len() == 2));
    }

    #[test]
    fn test_borrow_encoding_full_constraint() {
        let mut enc = BorrowEncoding::default();
        enc.creation_constraints.push(Formula::Var("c".into(), Sort::Bool));
        enc.expiry_constraints.push(Formula::Var("e".into(), Sort::Bool));
        let full = enc.full_constraint();
        assert!(matches!(&full, Formula::And(terms) if terms.len() == 2));
    }

    // -- encode_borrows integration tests --

    #[test]
    fn test_encode_borrows_mutable() {
        let func = mutable_borrow_function();
        let encoding = encode_borrows(&func);

        assert_eq!(encoding.prophecy_count(), 1);
        assert!(encoding.prophecies[0].mutable);
        assert_eq!(encoding.prophecies[0].place, "x");
        assert_eq!(encoding.prophecies[0].current_var, "x__curr");
        assert_eq!(encoding.prophecies[0].prophecy_var, "x__final");
    }

    #[test]
    fn test_encode_borrows_shared() {
        let func = shared_borrow_function();
        let encoding = encode_borrows(&func);

        assert_eq!(encoding.prophecy_count(), 1);
        assert!(!encoding.prophecies[0].mutable);
        assert_eq!(encoding.prophecies[0].place, "x");
        // Shared borrows produce identity constraint
        assert_eq!(encoding.creation_constraints.len(), 1);
    }

    #[test]
    fn test_encode_borrows_none() {
        let func = no_borrow_function();
        let encoding = encode_borrows(&func);

        assert!(encoding.is_empty());
        assert_eq!(encoding.creation_constraints.len(), 0);
        assert_eq!(encoding.expiry_constraints.len(), 0);
    }

    #[test]
    fn test_encode_borrows_shared_identity_constraint() {
        let func = shared_borrow_function();
        let encoding = encode_borrows(&func);

        // The shared borrow should produce an identity constraint: x__curr == x__final
        assert_eq!(encoding.creation_constraints.len(), 1);
        assert!(matches!(
            &encoding.creation_constraints[0],
            Formula::Eq(lhs, rhs)
                if matches!(lhs.as_ref(), Formula::Var(name, _) if name == "x__curr")
                && matches!(rhs.as_ref(), Formula::Var(name, _) if name == "x__final")
        ));
    }

    #[test]
    fn test_encode_borrows_uses_explicit_indices_and_collision_safe_names() {
        let func = shadowed_reordered_borrows_function();
        let encoding = encode_borrows(&func);

        assert_eq!(encoding.prophecy_count(), 2);
        // Both source locals were named `x`; distinct MIR identities must stay
        // distinct in every formula produced by the RustHorn lane.
        assert_eq!(encoding.prophecies[0].place, "_1");
        assert_eq!(encoding.prophecies[1].place, "_2");
        // The declaration vector is deliberately reordered. Sort lookup must
        // use LocalDecl.index rather than the vector slot.
        assert_eq!(encoding.prophecies[0].sort, Sort::BitVec(8));
        assert_eq!(encoding.prophecies[1].sort, Sort::BitVec(64));
        assert_eq!(encoding.prophecies[0].current_var, "_1__curr");
        assert_eq!(encoding.prophecies[1].current_var, "_2__curr");
    }

    #[test]
    fn test_sequential_same_place_borrows_get_unique_events_without_false_assumptions() {
        let func = sequential_mutable_reborrows_function();
        let encoding = encode_borrows(&func);

        assert_eq!(encoding.prophecy_count(), 2);
        assert_eq!(encoding.prophecies[0].place, "x");
        assert_eq!(encoding.prophecies[1].place, "x");
        assert_ne!(encoding.prophecies[0].current_var, encoding.prophecies[1].current_var);
        assert_ne!(encoding.prophecies[0].prophecy_var, encoding.prophecies[1].prophecy_var);

        let parameters = encoding.predicate_params();
        let parameter_names: Vec<&str> = parameters.iter().map(|(name, _)| name.as_str()).collect();
        let unique_names: std::collections::BTreeSet<&str> =
            parameter_names.iter().copied().collect();
        assert_eq!(parameter_names.len(), unique_names.len());

        // This scan cannot infer region overlap. In particular, it must not
        // turn two sequential borrow events into the always-false premise that
        // previously made every CHC query vacuously safe.
        assert!(encoding.aliasing_constraints.is_empty());
        assert_eq!(encoding.aliasing_formula(), Formula::Bool(true));

        // Each Drop resolves exactly its event's distinct prophecy.
        assert_eq!(encoding.expiry_constraints.len(), 2);
        for (constraint, prophecy) in
            encoding.expiry_constraints.iter().zip(encoding.prophecies.iter())
        {
            assert!(matches!(
                constraint,
                Formula::Eq(lhs, rhs)
                    if matches!(lhs.as_ref(), Formula::Var(name, sort)
                        if name == &prophecy.prophecy_var && sort == &prophecy.sort)
                    && matches!(rhs.as_ref(), Formula::Var(name, sort)
                        if name == "x" && sort == &prophecy.sort)
            ));
        }
    }

    #[test]
    fn test_encode_function_with_borrows_no_loops_returns_none() {
        let func = no_borrow_function();
        let result = encode_function_with_borrows(&func).expect("no loops is not an error");
        assert!(result.is_none());
    }

    #[test]
    fn test_encode_function_with_borrows_unsupported_loop_fails_closed() {
        let func = loop_with_unsupported_update();
        let err = encode_function_with_borrows(&func)
            .expect_err("unsupported loop MIR must not be conflated with no loops");
        assert!(matches!(
            err,
            ChcError::UnsupportedMir { kind, .. } if kind == "Rvalue::ThreadLocalRef"
        ));
    }

    #[test]
    fn test_encode_function_with_borrows_rejects_u8_wrapping_contract_arithmetic() {
        let func = loop_with_u8_wrapping_contract();
        let err = encode_function_with_borrows(&func)
            .expect_err("RustHorn must expose fixed-width contract lowering gaps");
        assert!(matches!(
            err,
            ChcError::UnsupportedContractArithmetic {
                function,
                contract_kind: "precondition",
                contract_index: 0,
            } if function == "test::rusthorn_u8_wrapping_contract"
        ));
    }

    // -- augment_chc_with_borrows tests --

    #[test]
    fn test_augment_chc_empty_encoding_is_noop() {
        // Build a minimal CHC system
        let pred = ChcPredicate { name: "inv".to_string(), params: vec![("i".into(), Sort::Int)] };
        let clause = ChcClause {
            head: Some(pred.apply_unprimed()),
            body_atoms: vec![],
            constraint: Formula::Bool(true),
            label: "entry".to_string(),
        };
        let system = ChcSystem {
            predicates: vec![pred],
            clauses: vec![clause],
            roles: vec![ClauseRole::Entry],
            function_name: "test".to_string(),
        };

        let encoding = BorrowEncoding::default();
        let augmented = augment_chc_with_borrows(&system, &encoding);

        // Should be unchanged
        assert_eq!(augmented.predicates[0].params.len(), 1);
        assert_eq!(augmented.clauses[0].constraint, Formula::Bool(true));
    }

    #[test]
    fn test_augment_chc_adds_prophecy_params() {
        let pred = ChcPredicate { name: "inv".to_string(), params: vec![("i".into(), Sort::Int)] };
        let clause = ChcClause {
            head: Some(pred.apply_unprimed()),
            body_atoms: vec![],
            constraint: Formula::Bool(true),
            label: "entry".to_string(),
        };
        let system = ChcSystem {
            predicates: vec![pred],
            clauses: vec![clause],
            roles: vec![ClauseRole::Entry],
            function_name: "test".to_string(),
        };

        let mut encoding = BorrowEncoding::default();
        encoding.prophecies.push(ProphecyVar::mutable_borrow("x", Sort::Int));

        let augmented = augment_chc_with_borrows(&system, &encoding);

        // Predicate should have 3 params: i, x__curr, x__final
        assert_eq!(augmented.predicates[0].params.len(), 3);
        assert_eq!(augmented.predicates[0].params[1].0, "x__curr");
        assert_eq!(augmented.predicates[0].params[2].0, "x__final");
    }

    #[test]
    fn test_augment_chc_entry_gets_creation_constraints() {
        let pred = ChcPredicate { name: "inv".to_string(), params: vec![("i".into(), Sort::Int)] };
        let clause = ChcClause {
            head: Some(pred.apply_unprimed()),
            body_atoms: vec![],
            constraint: Formula::Var("pre".into(), Sort::Bool),
            label: "entry".to_string(),
        };
        let system = ChcSystem {
            predicates: vec![pred],
            clauses: vec![clause],
            roles: vec![ClauseRole::Entry],
            function_name: "test".to_string(),
        };

        let mut encoding = BorrowEncoding::default();
        encoding.prophecies.push(ProphecyVar::shared_borrow("x", Sort::Int));
        encoding.creation_constraints.push(encoding.prophecies[0].identity_constraint());

        let augmented = augment_chc_with_borrows(&system, &encoding);

        // Entry clause should have And([original_constraint, creation_constraint])
        assert!(
            matches!(&augmented.clauses[0].constraint, Formula::And(terms) if terms.len() == 2)
        );
    }

    #[test]
    fn test_augment_chc_exit_gets_expiry_constraints() {
        let pred = ChcPredicate { name: "inv".to_string(), params: vec![("i".into(), Sort::Int)] };
        let exit_clause = ChcClause {
            head: None,
            body_atoms: vec![pred.apply_unprimed()],
            constraint: Formula::Var("exit_cond".into(), Sort::Bool),
            label: "exit".to_string(),
        };
        let system = ChcSystem {
            predicates: vec![pred],
            clauses: vec![exit_clause],
            roles: vec![ClauseRole::Exit],
            function_name: "test".to_string(),
        };

        let mut encoding = BorrowEncoding::default();
        encoding.prophecies.push(ProphecyVar::mutable_borrow("x", Sort::Int));
        encoding.expiry_constraints.push(Formula::Eq(
            Box::new(Formula::Var("x__final".into(), Sort::Int)),
            Box::new(Formula::Var("x".into(), Sort::Int)),
        ));

        let augmented = augment_chc_with_borrows(&system, &encoding);

        // Exit clause should have And([original_constraint, expiry_constraint])
        assert!(
            matches!(&augmented.clauses[0].constraint, Formula::And(terms) if terms.len() == 2)
        );
    }

    #[test]
    fn test_augment_chc_labels_annotated() {
        let pred = ChcPredicate { name: "inv".to_string(), params: vec![("i".into(), Sort::Int)] };
        let clause = ChcClause {
            head: Some(pred.apply_unprimed()),
            body_atoms: vec![],
            constraint: Formula::Bool(true),
            label: "entry_bb1".to_string(),
        };
        let system = ChcSystem {
            predicates: vec![pred],
            clauses: vec![clause],
            roles: vec![ClauseRole::Entry],
            function_name: "test".to_string(),
        };

        let mut encoding = BorrowEncoding::default();
        encoding.prophecies.push(ProphecyVar::mutable_borrow("x", Sort::Int));

        let augmented = augment_chc_with_borrows(&system, &encoding);
        assert!(augmented.clauses[0].label.contains("[rusthorn]"));
    }

    #[test]
    fn test_borrow_encoding_serialization_roundtrip() {
        let mut encoding = BorrowEncoding::default();
        encoding.prophecies.push(ProphecyVar::mutable_borrow("x", Sort::Int));
        encoding.prophecies.push(ProphecyVar::shared_borrow("y", Sort::BitVec(32)));
        encoding.creation_constraints.push(encoding.prophecies[1].identity_constraint());

        let json = serde_json::to_string(&encoding).expect("serialize");
        let round: BorrowEncoding = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.prophecy_count(), 2);
        assert_eq!(round.creation_constraints.len(), 1);
        assert!(round.prophecies[0].mutable);
        assert!(!round.prophecies[1].mutable);
    }
}
