use std::sync::Arc;

use rustc_ast::node_id::NodeMap;
use thin_vec::thin_vec;

use crate::LoweringContext;

#[derive(Clone, Copy)]
struct AstContractClause {
    span: rustc_span::Span,
    origin: rustc_hir::ContractClauseOrigin,
    citation: Option<rustc_ast::TrustCitation>,
    /// Trust: the native payload's token-rendered spelling — the faithful
    /// text authority when `span` went through macro expansion. `None` for
    /// attribute-origin clauses.
    payload: Option<rustc_span::Symbol>,
    /// Exact AST identity for typed attributes. Opaque attribute and native
    /// verifier-language clauses deliberately have no Rust expression.
    predicate_node_id: Option<rustc_ast::NodeId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OrderedContractClause<T> {
    ordinal: u32,
    kind: rustc_ast::FnContractClauseKind,
    value: T,
}

#[derive(Debug, PartialEq, Eq)]
enum ContractClauseOrderError {
    TooManyClauses,
    AmbiguousLegacyTypedLane(rustc_ast::FnContractClauseKind),
    InvalidLane {
        kind: rustc_ast::FnContractClauseKind,
        lane: rustc_ast::FnContractClauseLane,
    },
    DuplicateFunctionDecreases {
        stored: usize,
    },
    NonDenseOrdinal {
        position: usize,
        ordinal: u32,
    },
    NonDenseLaneIndex {
        kind: rustc_ast::FnContractClauseKind,
        lane: rustc_ast::FnContractClauseLane,
        expected: usize,
        lane_index: u32,
    },
    MissingLaneValue {
        kind: rustc_ast::FnContractClauseKind,
        lane: rustc_ast::FnContractClauseLane,
        lane_index: usize,
    },
    UnmarkedLaneValue {
        kind: rustc_ast::FnContractClauseKind,
        lane: rustc_ast::FnContractClauseLane,
        marked: usize,
        stored: usize,
    },
}

fn contract_clause_lane_slot(
    kind: rustc_ast::FnContractClauseKind,
    lane: rustc_ast::FnContractClauseLane,
) -> Option<usize> {
    use rustc_ast::FnContractClauseKind::{Decreases, Ensures, Requires};
    use rustc_ast::FnContractClauseLane::{Native, Opaque, Typed};
    match (kind, lane) {
        (Requires, Typed) => Some(0),
        (Requires, Opaque) => Some(1),
        (Requires, Native) => Some(2),
        (Ensures, Typed) => Some(3),
        (Ensures, Opaque) => Some(4),
        (Ensures, Native) => Some(5),
        (Decreases, Native) => Some(6),
        (Decreases, Typed | Opaque) => None,
    }
}

fn contract_clause_slot_identity(
    slot: usize,
) -> (rustc_ast::FnContractClauseKind, rustc_ast::FnContractClauseLane) {
    use rustc_ast::FnContractClauseKind::{Decreases, Ensures, Requires};
    use rustc_ast::FnContractClauseLane::{Native, Opaque, Typed};
    match slot {
        0 => (Requires, Typed),
        1 => (Requires, Opaque),
        2 => (Requires, Native),
        3 => (Ensures, Typed),
        4 => (Ensures, Opaque),
        5 => (Ensures, Native),
        6 => (Decreases, Native),
        _ => unreachable!("contract lane slots are fixed at seven"),
    }
}

/// Resolve the parser-authored marker stream against the seven physical AST
/// lanes. No source-position fallback is permitted: equal macro spans cannot
/// recover authored identity, and guessing would silently mis-index evidence.
fn restore_contract_clause_authored_order<T: Copy>(
    markers: &[rustc_ast::FnContractClauseMarker],
    lanes: [&[T]; 7],
) -> Result<Vec<OrderedContractClause<T>>, ContractClauseOrderError> {
    let mut consumed = [0usize; 7];
    let mut ordered = Vec::with_capacity(markers.len());
    for (position, marker) in markers.iter().copied().enumerate() {
        let expected_ordinal =
            u32::try_from(position).map_err(|_| ContractClauseOrderError::TooManyClauses)?;
        if marker.ordinal != expected_ordinal {
            return Err(ContractClauseOrderError::NonDenseOrdinal {
                position,
                ordinal: marker.ordinal,
            });
        }

        let slot = contract_clause_lane_slot(marker.kind, marker.lane).ok_or(
            ContractClauseOrderError::InvalidLane { kind: marker.kind, lane: marker.lane },
        )?;
        let lane_index = usize::try_from(marker.lane_index)
            .map_err(|_| ContractClauseOrderError::TooManyClauses)?;
        if lane_index != consumed[slot] {
            return Err(ContractClauseOrderError::NonDenseLaneIndex {
                kind: marker.kind,
                lane: marker.lane,
                expected: consumed[slot],
                lane_index: marker.lane_index,
            });
        }
        let Some(value) = lanes[slot].get(lane_index).copied() else {
            return Err(ContractClauseOrderError::MissingLaneValue {
                kind: marker.kind,
                lane: marker.lane,
                lane_index,
            });
        };
        consumed[slot] += 1;
        ordered.push(OrderedContractClause { ordinal: marker.ordinal, kind: marker.kind, value });
    }

    for (slot, (&marked, lane)) in consumed.iter().zip(lanes).enumerate() {
        if marked != lane.len() {
            let (kind, lane_kind) = contract_clause_slot_identity(slot);
            return Err(ContractClauseOrderError::UnmarkedLaneValue {
                kind,
                lane: lane_kind,
                marked,
                stored: lane.len(),
            });
        }
    }
    Ok(ordered)
}

fn typed_contract_clause_lane(
    kind: rustc_ast::FnContractClauseKind,
    clauses: &thin_vec::ThinVec<Box<rustc_ast::Expr>>,
    legacy_clause: Option<&rustc_ast::Expr>,
) -> Result<Vec<AstContractClause>, ContractClauseOrderError> {
    if !clauses.is_empty() && legacy_clause.is_some() {
        return Err(ContractClauseOrderError::AmbiguousLegacyTypedLane(kind));
    }
    Ok(if clauses.is_empty() {
        legacy_clause
            .into_iter()
            .map(|clause| AstContractClause {
                span: clause.span,
                origin: rustc_hir::ContractClauseOrigin::Attribute,
                citation: None,
                payload: None,
                predicate_node_id: Some(clause.id),
            })
            .collect()
    } else {
        clauses
            .iter()
            .map(|clause| AstContractClause {
                span: clause.span,
                origin: rustc_hir::ContractClauseOrigin::Attribute,
                citation: None,
                payload: None,
                predicate_node_id: Some(clause.id),
            })
            .collect()
    })
}

fn ordered_ast_contract_clauses(
    contract: &rustc_ast::FnContract,
) -> Result<Vec<OrderedContractClause<AstContractClause>>, ContractClauseOrderError> {
    use rustc_ast::FnContractClauseKind::{Ensures, Requires};

    let requires_typed = typed_contract_clause_lane(
        Requires,
        &contract.requires_clauses,
        contract.requires.as_deref(),
    )?;
    let requires_opaque = contract
        .trust_opaque_requires
        .iter()
        .copied()
        .map(|span| AstContractClause {
            span,
            origin: rustc_hir::ContractClauseOrigin::Attribute,
            citation: None,
            payload: None,
            predicate_node_id: None,
        })
        .collect::<Vec<_>>();
    let requires_native = contract
        .trust_native_requires
        .iter()
        .map(|clause| AstContractClause {
            span: clause.predicate,
            origin: rustc_hir::ContractClauseOrigin::Native,
            citation: clause.citation,
            payload: Some(clause.payload),
            predicate_node_id: None,
        })
        .collect::<Vec<_>>();
    let ensures_typed = typed_contract_clause_lane(
        Ensures,
        &contract.ensures_clauses,
        contract.ensures.as_deref(),
    )?;
    let ensures_opaque = contract
        .trust_opaque_ensures
        .iter()
        .copied()
        .map(|span| AstContractClause {
            span,
            origin: rustc_hir::ContractClauseOrigin::Attribute,
            citation: None,
            payload: None,
            predicate_node_id: None,
        })
        .collect::<Vec<_>>();
    let ensures_native = contract
        .trust_native_ensures
        .iter()
        .map(|clause| AstContractClause {
            span: clause.predicate,
            origin: rustc_hir::ContractClauseOrigin::Native,
            citation: clause.citation,
            payload: Some(clause.payload),
            predicate_node_id: None,
        })
        .collect::<Vec<_>>();
    let decreases_native = contract
        .trust_native_decreases
        .iter()
        .map(|clause| AstContractClause {
            span: clause.predicate,
            origin: rustc_hir::ContractClauseOrigin::Native,
            citation: clause.citation,
            payload: Some(clause.payload),
            predicate_node_id: None,
        })
        .collect::<Vec<_>>();
    if decreases_native.len() > 1 {
        return Err(ContractClauseOrderError::DuplicateFunctionDecreases {
            stored: decreases_native.len(),
        });
    }

    restore_contract_clause_authored_order(
        &contract.clause_order,
        [
            &requires_typed,
            &requires_opaque,
            &requires_native,
            &ensures_typed,
            &ensures_opaque,
            &ensures_native,
            &decreases_native,
        ],
    )
}

fn contract_diagnostic_span(contract: &rustc_ast::FnContract) -> rustc_span::Span {
    contract
        .requires_clauses
        .first()
        .map(|clause| clause.span)
        .or_else(|| contract.requires.as_ref().map(|clause| clause.span))
        .or_else(|| contract.trust_opaque_requires.first().copied())
        .or_else(|| contract.trust_native_requires.first().map(|clause| clause.predicate))
        .or_else(|| contract.ensures_clauses.first().map(|clause| clause.span))
        .or_else(|| contract.ensures.as_ref().map(|clause| clause.span))
        .or_else(|| contract.trust_opaque_ensures.first().copied())
        .or_else(|| contract.trust_native_ensures.first().map(|clause| clause.predicate))
        .or_else(|| contract.trust_native_decreases.first().map(|clause| clause.predicate))
        .unwrap_or(rustc_span::DUMMY_SP)
}

impl<'hir> LoweringContext<'_, 'hir> {
    pub(super) fn lower_hir_contract(
        &mut self,
        contract: Option<&rustc_ast::FnContract>,
        loop_clauses: Vec<rustc_hir::LoopClause>,
        predicate_hir_ids: NodeMap<rustc_hir::HirId>,
    ) -> Option<&'hir rustc_hir::FnContract<'hir>> {
        if contract.is_none() && !predicate_hir_ids.is_empty() {
            self.dcx().span_delayed_bug(
                rustc_span::DUMMY_SP,
                format!(
                    "body without a function contract collected {} typed contract predicate \
                     identities",
                    predicate_hir_ids.len(),
                ),
            );
            return None;
        }

        let (requires, ensures, decreases) = match contract {
            Some(contract) => match ordered_ast_contract_clauses(contract) {
                Ok(ordered) => {
                    let mut requires = Vec::new();
                    let mut ensures = Vec::new();
                    let mut decreases = Vec::new();
                    for clause in ordered {
                        match clause.kind {
                            rustc_ast::FnContractClauseKind::Requires => requires.push(clause),
                            rustc_ast::FnContractClauseKind::Ensures => ensures.push(clause),
                            rustc_ast::FnContractClauseKind::Decreases => decreases.push(clause),
                        }
                    }

                    let typed_clause_count = requires
                        .iter()
                        .chain(&ensures)
                        .chain(&decreases)
                        .filter(|clause| clause.value.predicate_node_id.is_some())
                        .count();
                    if typed_clause_count != predicate_hir_ids.len() {
                        if self.dcx().has_errors().is_none() {
                            self.dcx().span_delayed_bug(
                                contract_diagnostic_span(contract),
                                format!(
                                    "function contract lowered {actual} distinct typed predicate \
                                     identities for {typed_clause_count} authored typed clauses",
                                    actual = predicate_hir_ids.len(),
                                ),
                            );
                        }
                        return None;
                    }

                    (
                        self.lower_contract_clauses(requires, &predicate_hir_ids)?,
                        self.lower_contract_clauses(ensures, &predicate_hir_ids)?,
                        self.lower_contract_clauses(decreases, &predicate_hir_ids)?,
                    )
                }
                Err(error) => {
                    self.dcx().span_delayed_bug(
                        contract_diagnostic_span(contract),
                        format!(
                            "function contract has an inconsistent parser-authored clause order: \
                             {error:?}"
                        ),
                    );
                    (
                        &[] as &[rustc_hir::ContractClause],
                        &[] as &[rustc_hir::ContractClause],
                        &[] as &[rustc_hir::ContractClause],
                    )
                }
            },
            None => (
                &[] as &[rustc_hir::ContractClause],
                &[] as &[rustc_hir::ContractClause],
                &[] as &[rustc_hir::ContractClause],
            ),
        };

        if requires.is_empty()
            && ensures.is_empty()
            && decreases.is_empty()
            && loop_clauses.is_empty()
        {
            None
        } else {
            let loop_clauses = self.arena.alloc_from_iter(loop_clauses);
            Some(self.arena.alloc(rustc_hir::FnContract {
                requires,
                ensures,
                decreases,
                loop_clauses,
            }))
        }
    }

    /// Lower already validated function clauses into their kind-specific HIR
    /// arrays while retaining each function-wide authored ordinal and exact
    /// typed-expression identity.
    fn lower_contract_clauses(
        &mut self,
        clauses: Vec<OrderedContractClause<AstContractClause>>,
        predicate_hir_ids: &NodeMap<rustc_hir::HirId>,
    ) -> Option<&'hir [rustc_hir::ContractClause]> {
        let mut lowered = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let predicate_hir_id = match clause.value.predicate_node_id {
                Some(node_id) => match predicate_hir_ids.get(&node_id).copied() {
                    Some(hir_id) => Some(hir_id),
                    None => {
                        if self.dcx().has_errors().is_none() {
                            self.dcx().span_delayed_bug(
                                clause.value.span,
                                format!(
                                    "typed function-contract clause {} has no exact lowered HIR \
                                     predicate identity",
                                    clause.ordinal,
                                ),
                            );
                        }
                        return None;
                    }
                },
                None => None,
            };
            lowered.push(rustc_hir::ContractClause {
                span: self.lower_span(clause.value.span),
                origin: clause.value.origin,
                citation: clause.value.citation.map(|citation| self.lower_trust_citation(citation)),
                payload: clause.value.payload,
                ordinal: clause.ordinal,
                predicate_hir_id,
            });
        }
        Some(self.arena.alloc_from_iter(lowered))
    }

    fn record_contract_predicate_hir_id(
        &mut self,
        node_id: rustc_ast::NodeId,
        hir_id: rustc_hir::HirId,
        span: rustc_span::Span,
    ) {
        if let Some(previous) = self.trust_contract_clause_exprs.insert(node_id, hir_id) {
            self.dcx().span_delayed_bug(
                span,
                format!(
                    "typed function-contract AST predicate {node_id:?} was lowered more than \
                     once ({previous:?}, then {hir_id:?})"
                ),
            );
        }
    }

    pub(super) fn lower_trust_citation(
        &self,
        citation: rustc_ast::TrustCitation,
    ) -> rustc_hir::TrustCitation {
        rustc_hir::TrustCitation { name: citation.name, span: self.lower_span(citation.span) }
    }

    /// Lowered runtime contract checks are guarded with the `contract_checks` compiler flag,
    /// i.e. the flag turns into a boolean guard in the lowered HIR. The reason
    /// for not eliminating the contract code entirely when the `contract_checks`
    /// flag is disabled is so that contracts can be type checked, even when
    /// they are disabled, which avoids them becoming stale (i.e. out of sync
    /// with the codebase) over time.
    ///
    /// tRustc verification must preserve the first-class contract through a
    /// typed query before this runtime-check lowering erases verifier structure.
    ///
    /// The optimiser should be able to eliminate all contract code guarded
    /// by `if false`, leaving the original body intact when runtime contract
    /// checks are disabled.
    pub(super) fn lower_contract(
        &mut self,
        body: impl FnOnce(&mut Self) -> rustc_hir::Expr<'hir>,
        contract: &rustc_ast::FnContract,
    ) -> rustc_hir::Expr<'hir> {
        // The order in which things are lowered is important! I.e to
        // refer to variables in contract_decls from postcond/precond,
        // we must lower it first!
        let contract_decls = self.lower_decls(contract);

        // Trust: opaque trust-spec clauses (`trust_opaque_requires` /
        // `trust_opaque_ensures`) are deliberately ABSENT here — they are spec
        // vocabulary, not Rust, so they get no runtime-check lowering (and
        // thus never touch `contract_check_requires` /
        // `contract_build_check_ensures` typing). Their spans still reach the
        // verifier via `lower_hir_contract`.
        let has_requires = !contract.requires_clauses.is_empty() || contract.requires.is_some();

        // Trust: EVERY ensures clause is lowered — each `|ret| …` closure was
        // assigned a DefId during def collection, so each must become a real
        // HIR owner (an unlowered clause would be a phantom owner that ICEs at
        // crate-metadata encoding: `No HirId for DefId(..::{closure#N})`).
        // Multiple clauses compose as chained pass-through checks (see
        // `wrap_body_with_contract_checks`), replacing the former hard error
        // "a function may have at most one `#[ensures]` contract clause" —
        // which was a drop-in divergence: plain rustc (via the trust-spec
        // passthrough macro) accepts any number of `#[trust::ensures]` attrs.
        let ensures_exprs: Vec<&rustc_ast::Expr> = contract
            .ensures_clauses
            .iter()
            .map(|e| &**e)
            .chain(contract.ensures.as_deref())
            .collect();

        match (!has_requires, !ensures_exprs.is_empty()) {
            (_, true) => {
                // Lower the fn contract, which turns:
                //
                // { body }
                //
                // into (one checker binding PER ensures clause; declarations
                // and precondition checks ride the FIRST binding's init):
                //
                // let __ensures_checker = if contract_checks {
                //     CONTRACT_DECLARATIONS;
                //     contract_check_requires(PRECOND);
                //     Some(|ret_val| POSTCOND_1)
                // } else {
                //     None
                // };
                // let __ensures_checker1 = if contract_checks {
                //     Some(|ret_val| POSTCOND_2)
                // } else {
                //     None
                // };
                // {
                //     let ret = { body };
                //
                //     if contract_checks {
                //         contract_check_ensures(__ensures_checker1,
                //             contract_check_ensures(__ensures_checker, ret))
                //     } else {
                //         ret
                //     }
                // }
                let preconds = if has_requires { self.lower_preconds(contract) } else { &[][..] };

                let mut checker_inits = Vec::with_capacity(ensures_exprs.len());
                for (i, ens) in ensures_exprs.iter().enumerate() {
                    let postcond_checker = self.lower_postcond_checker(ens);
                    let contract_check = if i == 0 {
                        self.lower_contract_check_with_postcond(
                            contract_decls,
                            preconds,
                            postcond_checker,
                        )
                    } else {
                        self.lower_contract_check_with_postcond(&[], &[], postcond_checker)
                    };
                    checker_inits.push((contract_check, postcond_checker.span));
                }

                let wrapped_body = self.wrap_body_with_contract_checks(body, &checker_inits);
                self.expr_block(wrapped_body)
            }
            (false, false) => {
                // Lower the fn contract, which turns:
                //
                // { body }
                //
                // into:
                //
                // {
                //      if contracts_checks {
                //          CONTRACT_DECLARATIONS;
                //          contract_requires(PRECOND);
                //      }
                //      body
                // }
                let preconds = self.lower_preconds(contract);
                let precond_check =
                    self.lower_contract_check_just_precond(contract_decls, preconds);

                let body = self.arena.alloc(body(self));

                // Flatten the body into precond check, then body.
                let wrapped_body = self.block_all(
                    body.span,
                    self.arena.alloc_from_iter([precond_check].into_iter()),
                    Some(body),
                );
                self.expr_block(wrapped_body)
            }
            (true, false) => body(self),
        }
    }

    fn lower_decls(&mut self, contract: &rustc_ast::FnContract) -> &'hir [rustc_hir::Stmt<'hir>] {
        let (decls, decls_tail) = self.lower_stmts(&contract.declarations);

        if let Some(e) = decls_tail {
            // include the tail expression in the declaration statements
            let tail = self.stmt_expr(e.span, *e);
            self.arena.alloc_from_iter(decls.into_iter().map(|d| *d).chain([tail].into_iter()))
        } else {
            decls
        }
    }

    /// Lower the precondition check intrinsic.
    fn lower_preconds(
        &mut self,
        contract: &rustc_ast::FnContract,
    ) -> &'hir [rustc_hir::Stmt<'hir>] {
        if contract.requires_clauses.is_empty() {
            self.arena.alloc_from_iter(contract.requires.iter().map(|req| self.lower_precond(req)))
        } else {
            self.arena.alloc_from_iter(
                contract.requires_clauses.iter().map(|req| self.lower_precond(req)),
            )
        }
    }

    fn lower_precond(&mut self, req: &rustc_ast::Expr) -> rustc_hir::Stmt<'hir> {
        let lowered_req = self.lower_expr_mut(req);
        self.record_contract_predicate_hir_id(req.id, lowered_req.hir_id, req.span);
        let req_span = self.mark_span_with_reason(
            rustc_span::DesugaringKind::Contract,
            lowered_req.span,
            Some(Arc::clone(&self.allow_contracts)),
        );

        let check_ident: rustc_span::Ident =
            rustc_span::Ident::from_str_and_span("__requires_checker", req_span);
        let (checker_pat, check_hir_id) =
            self.pat_ident_binding_mode_mut(req_span, check_ident, rustc_hir::BindingMode::NONE);
        let checker_decl = self.stmt_let_pat(
            None,
            req_span,
            Some(self.arena.alloc(lowered_req)),
            self.arena.alloc(checker_pat),
            rustc_hir::LocalSource::Contract,
        );

        let req_checker = self.expr_ident(req_span, check_ident, check_hir_id);
        let precond = self.expr_call_lang_item_fn_mut(
            req_span,
            rustc_hir::LangItem::ContractCheckRequires,
            &*arena_vec![self; *req_checker],
        );
        let precond = self.arena.alloc(precond);
        let precond_block = self.block_all(req_span, arena_vec![self; checker_decl], Some(precond));
        let precond_block = self.expr_block(precond_block);
        self.stmt_expr(req.span, precond_block)
    }

    fn lower_postcond_checker(&mut self, ens: &rustc_ast::Expr) -> &'hir rustc_hir::Expr<'hir> {
        let ens_span = self.lower_span(ens.span);
        let ens_span = self.mark_span_with_reason(
            rustc_span::DesugaringKind::Contract,
            ens_span,
            Some(Arc::clone(&self.allow_contracts)),
        );
        let lowered_ens = self.lower_expr_mut(ens);
        self.record_contract_predicate_hir_id(ens.id, lowered_ens.hir_id, ens.span);
        self.expr_call_lang_item_fn(
            ens_span,
            rustc_hir::LangItem::ContractBuildCheckEnsures,
            &*arena_vec![self; lowered_ens],
        )
    }

    fn lower_contract_check_just_precond(
        &mut self,
        contract_decls: &'hir [rustc_hir::Stmt<'hir>],
        preconds: &'hir [rustc_hir::Stmt<'hir>],
    ) -> rustc_hir::Stmt<'hir> {
        let stmts = self.arena.alloc_from_iter(
            contract_decls.into_iter().map(|d| *d).chain(preconds.into_iter().map(|p| *p)),
        );

        let span = preconds.first().map(|precond| precond.span).unwrap_or_else(|| {
            contract_decls.last().map(|decl| decl.span).unwrap_or(rustc_span::DUMMY_SP)
        });
        let then_block_stmts = self.block_all(span, stmts, None);
        let then_block = self.arena.alloc(self.expr_block(&then_block_stmts));

        let precond_check = rustc_hir::ExprKind::If(
            self.arena.alloc(self.expr_bool_literal(span, self.tcx.sess.contract_checks())),
            then_block,
            None,
        );

        let precond_check = self.expr(span, precond_check);
        self.stmt_expr(span, precond_check)
    }

    fn lower_contract_check_with_postcond(
        &mut self,
        contract_decls: &'hir [rustc_hir::Stmt<'hir>],
        preconds: &'hir [rustc_hir::Stmt<'hir>],
        postcond_checker: &'hir rustc_hir::Expr<'hir>,
    ) -> &'hir rustc_hir::Expr<'hir> {
        let stmts = self.arena.alloc_from_iter(
            contract_decls.into_iter().map(|d| *d).chain(preconds.into_iter().map(|p| *p)),
        );
        let span = preconds.first().map(|precond| precond.span).unwrap_or(postcond_checker.span);

        let postcond_checker = self.arena.alloc(self.expr_enum_variant_lang_item(
            postcond_checker.span,
            rustc_hir::lang_items::LangItem::OptionSome,
            &*arena_vec![self; *postcond_checker],
        ));
        let then_block_stmts = self.block_all(span, stmts, Some(postcond_checker));
        let then_block = self.arena.alloc(self.expr_block(&then_block_stmts));

        let none_expr = self.arena.alloc(self.expr_enum_variant_lang_item(
            postcond_checker.span,
            rustc_hir::lang_items::LangItem::OptionNone,
            Default::default(),
        ));
        let else_block = self.block_expr(none_expr);
        let else_block = self.arena.alloc(self.expr_block(else_block));

        let contract_check = rustc_hir::ExprKind::If(
            self.arena.alloc(self.expr_bool_literal(span, self.tcx.sess.contract_checks())),
            then_block,
            Some(else_block),
        );
        self.arena.alloc(self.expr(span, contract_check))
    }

    // Trust: N-clause generalization of the former single-checker
    // `wrap_body_with_contract_check` — one `let __ensures_checkerN` binding
    // per ensures clause, all installed for `return`-interception, with the
    // checks chained in attribute order at every return point.
    fn wrap_body_with_contract_checks(
        &mut self,
        body: impl FnOnce(&mut Self) -> rustc_hir::Expr<'hir>,
        checker_inits: &[(&'hir rustc_hir::Expr<'hir>, rustc_span::Span)],
    ) -> &'hir rustc_hir::Block<'hir> {
        let mut bindings = Vec::with_capacity(checker_inits.len());
        let mut postcond_decls = Vec::with_capacity(checker_inits.len());
        for (i, &(contract_check, postcond_span)) in checker_inits.iter().enumerate() {
            // Distinct binder names purely for HIR readability — resolution
            // goes through the HirId, not the name.
            let name =
                if i == 0 { "__ensures_checker".into() } else { format!("__ensures_checker{i}") };
            let check_ident: rustc_span::Ident =
                rustc_span::Ident::from_str_and_span(&name, postcond_span);
            let (checker_pat, check_hir_id) = self.pat_ident_binding_mode_mut(
                postcond_span,
                check_ident,
                rustc_hir::BindingMode::NONE,
            );
            postcond_decls.push(self.stmt_let_pat(
                None,
                postcond_span,
                Some(contract_check),
                self.arena.alloc(checker_pat),
                rustc_hir::LocalSource::Contract,
            ));
            bindings.push((postcond_span, check_ident, check_hir_id));
        }

        // Install contract_ensures so we will intercept `return` statements,
        // then lower the body.
        self.contract_ensures = bindings;
        let body = self.arena.alloc(body(self));

        // Finally, inject the chained ensures checks on the implicit return
        // of the body.
        let body = self.inject_all_ensures_checks(body);

        // Flatten the body into precond, then postconds, then wrapped body.
        let wrapped_body =
            self.block_all(body.span, self.arena.alloc_from_iter(postcond_decls), Some(body));
        wrapped_body
    }

    /// Create an `ExprKind::Ret` that is optionally wrapped by calls to check
    /// the contract ensures clauses, if any exist.
    pub(super) fn checked_return(
        &mut self,
        opt_expr: Option<&'hir rustc_hir::Expr<'hir>>,
    ) -> rustc_hir::ExprKind<'hir> {
        let checked_ret = match self.contract_ensures.first() {
            Some(&(check_span, _, _)) => {
                let expr = opt_expr.unwrap_or_else(|| self.expr_unit(check_span));
                Some(self.inject_all_ensures_checks(expr))
            }
            None => opt_expr,
        };
        rustc_hir::ExprKind::Ret(checked_ret)
    }

    // Trust: chain one check per `#[ensures]` clause, in attribute order —
    // `contract_check_ensures(checker, ret)` asserts the checker's
    // postcondition and passes `ret` through, so N clauses compose as nested
    // pass-through calls (clause 1 innermost, i.e. checked first).
    fn inject_all_ensures_checks(
        &mut self,
        mut expr: &'hir rustc_hir::Expr<'hir>,
    ) -> &'hir rustc_hir::Expr<'hir> {
        for (span, ident, hir_id) in self.contract_ensures.clone() {
            expr = self.inject_ensures_check(expr, span, ident, hir_id);
        }
        expr
    }

    /// Wraps an expression with a call to the ensures check before it gets returned.
    pub(super) fn inject_ensures_check(
        &mut self,
        expr: &'hir rustc_hir::Expr<'hir>,
        span: rustc_span::Span,
        cond_ident: rustc_span::Ident,
        cond_hir_id: rustc_hir::HirId,
    ) -> &'hir rustc_hir::Expr<'hir> {
        // {
        //     let ret = { body };
        //
        //     if contract_checks {
        //         contract_check_ensures(__postcond, ret)
        //     } else {
        //         ret
        //     }
        // }
        let ret_ident: rustc_span::Ident = rustc_span::Ident::from_str_and_span("__ret", span);

        // Set up the return `let` statement.
        let (ret_pat, ret_hir_id) =
            self.pat_ident_binding_mode_mut(span, ret_ident, rustc_hir::BindingMode::NONE);

        let ret_stmt = self.stmt_let_pat(
            None,
            span,
            Some(expr),
            self.arena.alloc(ret_pat),
            rustc_hir::LocalSource::Contract,
        );

        let ret = self.expr_ident(span, ret_ident, ret_hir_id);

        let cond_fn = self.expr_ident(span, cond_ident, cond_hir_id);
        let contract_check = self.expr_call_lang_item_fn_mut(
            span,
            rustc_hir::LangItem::ContractCheckEnsures,
            arena_vec![self; *cond_fn, *ret],
        );
        let contract_check = self.arena.alloc(contract_check);
        let call_expr = self.block_expr_block(contract_check);

        // same ident can't be used in 2 places, so we create a new one for the
        // else branch
        let ret = self.expr_ident(span, ret_ident, ret_hir_id);
        let ret_block = self.block_expr_block(ret);

        let contracts_enabled: rustc_hir::Expr<'_> =
            self.expr_bool_literal(span, self.tcx.sess.contract_checks());
        let contract_check = self.arena.alloc(self.expr(
            span,
            rustc_hir::ExprKind::If(
                self.arena.alloc(contracts_enabled),
                call_expr,
                Some(ret_block),
            ),
        ));

        let attrs: rustc_ast::AttrVec = thin_vec![self.unreachable_code_attr(span)];
        self.lower_attrs(contract_check.hir_id, &attrs, span, rustc_hir::Target::Expression);

        let ret_block = self.block_all(span, arena_vec![self; ret_stmt], Some(contract_check));
        self.arena.alloc(self.expr_block(self.arena.alloc(ret_block)))
    }
}

// Trust: the clause-ordering cases are Trust's, and they need the private
// helpers above; the file keeps them so the module tree, not an integration
// test, is what grants that access.
#[cfg(test)]
mod tests;
