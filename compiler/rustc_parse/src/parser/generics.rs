use rustc_ast::tokenstream::Spacing;
use rustc_ast::{
    self as ast, AttrVec, DUMMY_NODE_ID, GenericBounds, GenericParam, GenericParamKind, TyKind,
    WhereClause, WherePredicate, token,
};
use rustc_ast_pretty::pprust;
use rustc_errors::{Applicability, Diag, PResult};
use rustc_span::{Ident, Span, Symbol, kw, sym};
use thin_vec::ThinVec;

use super::{ForceCollect, Parser, Trailing, UsePreAttrPos};
use crate::diagnostics::{
    self, MultipleWhereClauses, UnexpectedDefaultValueForLifetimeInGenericParameters,
    UnexpectedSelfInGenericParameters, WhereClauseBeforeTupleStructBody,
    WhereClauseBeforeTupleStructBodySugg,
};
use crate::exp;

enum PredicateKindOrStructBody {
    PredicateKind(ast::WherePredicateKind),
    StructBody(ThinVec<ast::FieldDef>),
}

impl<'a> Parser<'a> {
    /// Parses bounds of a lifetime parameter `BOUND + BOUND + BOUND`, possibly with trailing `+`.
    ///
    /// ```text
    /// BOUND = LT_BOUND (e.g., `'a`)
    /// ```
    pub(crate) fn parse_lt_param_bounds(&mut self) -> GenericBounds {
        let mut lifetimes = ThinVec::new();
        while self.check_lifetime() {
            lifetimes.push(ast::GenericBound::Outlives(self.expect_lifetime()));

            if !self.eat_plus() {
                break;
            }
        }
        lifetimes
    }

    /// Matches `typaram = IDENT (`?` unbound)? optbounds ( EQ ty )?`.
    fn parse_ty_param(&mut self, preceding_attrs: AttrVec) -> PResult<'a, GenericParam> {
        let ident = self.parse_ident()?;

        // We might have a typo'd `Const` that was parsed as a type parameter.
        if self.may_recover()
            && ident.name.as_str().to_ascii_lowercase() == kw::Const.as_str()
            && self.check_ident()
        // `Const` followed by IDENT
        {
            return self.recover_const_param_with_mistyped_const(preceding_attrs, ident);
        }

        // Parse optional colon and param bounds.
        let mut colon_span = None;
        let bounds = if self.eat(exp!(Colon)) {
            colon_span = Some(self.prev_token.span);
            // recover from `impl Trait` in type param bound
            if self.token.is_keyword(kw::Impl) {
                let impl_span = self.token.span;
                let snapshot = self.create_snapshot_for_diagnostic();
                match self.parse_ty() {
                    Ok(p) => {
                        if let TyKind::ImplTrait(_, bounds) = &p.kind {
                            let span = impl_span.to(self.token.span.shrink_to_lo());
                            let mut err = self.dcx().struct_span_err(
                                span,
                                "expected trait bound, found `impl Trait` type",
                            );
                            err.span_label(span, "not a trait");
                            if let [bound, ..] = &bounds[..] {
                                err.span_suggestion_verbose(
                                    impl_span.until(bound.span()),
                                    "use the trait bounds directly",
                                    String::new(),
                                    Applicability::MachineApplicable,
                                );
                            }
                            return Err(err);
                        }
                    }
                    Err(err) => {
                        err.cancel();
                    }
                }
                self.restore_snapshot(snapshot);
            }
            self.parse_generic_bounds()?
        } else {
            ThinVec::new()
        };

        let default = if self.eat(exp!(Eq)) { Some(self.parse_ty()?) } else { None };
        Ok(GenericParam {
            ident,
            id: ast::DUMMY_NODE_ID,
            attrs: preceding_attrs,
            bounds,
            kind: GenericParamKind::Type { default },
            is_placeholder: false,
            colon_span,
        })
    }

    pub(crate) fn parse_const_param(
        &mut self,
        preceding_attrs: AttrVec,
    ) -> PResult<'a, GenericParam> {
        let const_span = self.token.span;

        self.expect_keyword(exp!(Const))?;
        let ident = self.parse_ident()?;
        if let Err(mut err) = self.expect(exp!(Colon)) {
            return if self.token.kind == token::Comma || self.token.kind == token::Gt {
                // Recover parse from `<const N>` where the type is missing.
                let span = const_span.to(ident.span);
                err.span_suggestion_verbose(
                    ident.span.shrink_to_hi(),
                    "you likely meant to write the type of the const parameter here",
                    ": /* Type */".to_string(),
                    Applicability::HasPlaceholders,
                );
                let kind = TyKind::Err(err.emit_err());
                let ty = self.mk_ty(span, kind);
                Ok(GenericParam {
                    ident,
                    id: ast::DUMMY_NODE_ID,
                    attrs: preceding_attrs,
                    bounds: ThinVec::new(),
                    kind: GenericParamKind::Const { ty, span, default: None },
                    is_placeholder: false,
                    colon_span: None,
                })
            } else {
                Err(err)
            };
        }
        let ty = self.parse_ty()?;

        // Parse optional const generics default value.
        let default = if self.eat(exp!(Eq)) { Some(self.parse_const_arg()?) } else { None };
        let span = if let Some(ref default) = default {
            const_span.to(default.value.span)
        } else {
            const_span.to(ty.span)
        };

        Ok(GenericParam {
            ident,
            id: ast::DUMMY_NODE_ID,
            attrs: preceding_attrs,
            bounds: ThinVec::new(),
            kind: GenericParamKind::Const { ty, span, default },
            is_placeholder: false,
            colon_span: None,
        })
    }

    pub(crate) fn recover_const_param_with_mistyped_const(
        &mut self,
        preceding_attrs: AttrVec,
        mistyped_const_ident: Ident,
    ) -> PResult<'a, GenericParam> {
        let ident = self.parse_ident()?;
        self.expect(exp!(Colon))?;
        let ty = self.parse_ty()?;

        // Parse optional const generics default value.
        let default = if self.eat(exp!(Eq)) { Some(self.parse_const_arg()?) } else { None };
        let span = if let Some(ref default) = default {
            mistyped_const_ident.span.to(default.value.span)
        } else {
            mistyped_const_ident.span.to(ty.span)
        };

        self.dcx()
            .struct_span_err(
                mistyped_const_ident.span,
                format!("`const` keyword was mistyped as `{}`", mistyped_const_ident.as_str()),
            )
            .with_span_suggestion_verbose(
                mistyped_const_ident.span,
                "use the `const` keyword",
                kw::Const,
                Applicability::MachineApplicable,
            )
            .emit();

        Ok(GenericParam {
            ident,
            id: ast::DUMMY_NODE_ID,
            attrs: preceding_attrs,
            bounds: ThinVec::new(),
            kind: GenericParamKind::Const { ty, span, default },
            is_placeholder: false,
            colon_span: None,
        })
    }

    /// Parse a (possibly empty) list of generic (lifetime, type, const) parameters.
    ///
    /// ```ebnf
    /// GenericParams = (GenericParam ("," GenericParam)* ","?)?
    /// ```
    pub(super) fn parse_generic_params(&mut self) -> PResult<'a, ThinVec<ast::GenericParam>> {
        let mut params = ThinVec::new();
        let mut done = false;
        let prev = self.parsing_generics;
        self.parsing_generics = true;
        while !done {
            let attrs = self.parse_outer_attributes()?;
            let param = match self.collect_tokens(None, attrs, ForceCollect::No, |this, attrs| {
                if this.eat_keyword_noexpect(kw::SelfUpper) {
                    // `Self` as a generic param is invalid. Here we emit the diagnostic and continue parsing
                    // as if `Self` never existed.
                    this.dcx()
                        .emit_err(UnexpectedSelfInGenericParameters { span: this.prev_token.span });

                    // Eat a trailing comma, if it exists.
                    let _ = this.eat(exp!(Comma));
                }

                let param = if this.check_lifetime() {
                    let lifetime = this.expect_lifetime();
                    // Parse lifetime parameter.
                    let (colon_span, bounds) = if this.eat(exp!(Colon)) {
                        (Some(this.prev_token.span), this.parse_lt_param_bounds())
                    } else {
                        (None, ThinVec::new())
                    };

                    if this.check_noexpect(&token::Eq) && this.look_ahead(1, |t| t.is_lifetime()) {
                        let lo = this.token.span;
                        // Parse `= 'lifetime`.
                        this.bump(); // `=`
                        this.bump(); // `'lifetime`
                        let span = lo.to(this.prev_token.span);
                        this.dcx().emit_err(UnexpectedDefaultValueForLifetimeInGenericParameters {
                            span,
                        });
                    }

                    Some(ast::GenericParam {
                        ident: lifetime.ident,
                        id: lifetime.id,
                        attrs,
                        bounds,
                        kind: ast::GenericParamKind::Lifetime,
                        is_placeholder: false,
                        colon_span,
                    })
                } else if this.check_keyword(exp!(Const)) {
                    // Parse const parameter.
                    Some(this.parse_const_param(attrs)?)
                } else if this.check_ident() {
                    // Parse type parameter.
                    Some(this.parse_ty_param(attrs)?)
                } else if this.token.can_begin_type() {
                    // Trying to write an associated type bound? (#26271)
                    let snapshot = this.create_snapshot_for_diagnostic();
                    let lo = this.token.span;
                    match this.parse_ty_where_predicate_kind() {
                        Ok(_) => {
                            this.dcx().emit_err(diagnostics::BadAssocTypeBounds {
                                span: lo.to(this.prev_token.span),
                            });
                            // FIXME - try to continue parsing other generics?
                        }
                        Err(err) => {
                            err.cancel();
                            // FIXME - maybe we should overwrite 'self' outside of `collect_tokens`?
                            this.restore_snapshot(snapshot);
                        }
                    }
                    return Ok((None, Trailing::No, UsePreAttrPos::No));
                } else {
                    // Check for trailing attributes and stop parsing.
                    if !attrs.is_empty() {
                        if !params.is_empty() {
                            this.dcx()
                                .emit_err(diagnostics::AttrAfterGeneric { span: attrs[0].span });
                        } else {
                            this.dcx()
                                .emit_err(diagnostics::AttrWithoutGenerics { span: attrs[0].span });
                        }
                    }
                    return Ok((None, Trailing::No, UsePreAttrPos::No));
                };

                if !this.eat(exp!(Comma)) {
                    done = true;
                }
                // We just ate the comma, so no need to capture the trailing token.
                Ok((param, Trailing::No, UsePreAttrPos::No))
            }) {
                Ok(param) => param,
                Err(err) => {
                    self.parsing_generics = prev;
                    return Err(err);
                }
            };

            if let Some(param) = param {
                params.push(param);
            } else {
                break;
            }
        }
        self.parsing_generics = prev;
        Ok(params)
    }

    /// Parses a set of optional generic type parameter declarations. Where
    /// clauses are not parsed here, and must be added later via
    /// `parse_where_clause()`.
    ///
    /// matches generics = ( ) | ( < > ) | ( < typaramseq ( , )? > ) | ( < lifetimes ( , )? > )
    ///                  | ( < lifetimes , typaramseq ( , )? > )
    /// where   typaramseq = ( typaram ) | ( typaram , typaramseq )
    pub(super) fn parse_generics(&mut self) -> PResult<'a, ast::Generics> {
        // invalid path separator `::` in function definition
        // for example `fn invalid_path_separator::<T>() {}`
        if self.eat_noexpect(&token::PathSep) {
            self.dcx()
                .emit_err(diagnostics::InvalidPathSepInFnDefinition { span: self.prev_token.span });
        }

        let span_lo = self.token.span;
        let (params, span) = if self.eat_lt() {
            let params = self.parse_generic_params()?;
            self.expect_gt_or_maybe_suggest_closing_generics(&params)?;
            (params, span_lo.to(self.prev_token.span))
        } else {
            (ThinVec::new(), self.prev_token.span.shrink_to_hi())
        };
        Ok(ast::Generics {
            params,
            where_clause: WhereClause {
                has_where_token: false,
                predicates: ThinVec::new(),
                span: self.prev_token.span.shrink_to_hi(),
            },
            span,
        })
    }

    /// Parses an experimental fn contract
    /// (`contract_requires(WWW) contract_ensures(ZZZ)`, repeated in any order)
    ///
    /// Trust: additionally accepts the Trust-origin clause keywords
    /// (`trust_contract_requires` / `trust_contract_ensures`) injected when a
    /// trust-spec attribute (`#[trust::requires]` / `#[trust::ensures]`) is
    /// expanded. An ATTRIBUTE-origin payload joins the upstream typed lane only
    /// when it is plain, typeable Rust; a payload written in spec vocabulary
    /// (`result`, compatibility `old()`/bounded quantifiers, `==>`) — or one that does not
    /// parse as a Rust expression — is recorded as an OPAQUE clause (span
    /// only) so it never reaches name resolution or typeck. The verifier's
    /// `trust_contracts` query recovers opaque predicates from source text.
    /// Native signature clauses are always kept in their own span-only lane,
    /// preserving their distinct bare-`result` semantics through lowering.
    pub(super) fn parse_contract(&mut self) -> PResult<'a, Option<Box<ast::FnContract>>> {
        let mut declarations = ThinVec::new();
        let mut requires = ThinVec::new();
        let mut ensures = ThinVec::new();
        let mut trust_opaque_requires = ThinVec::new();
        let mut trust_opaque_ensures = ThinVec::new();
        let mut trust_native_requires = ThinVec::new();
        let mut trust_native_ensures = ThinVec::new();
        let mut trust_native_decreases = ThinVec::new();
        let mut clause_order = ThinVec::new();
        let mut saw_native_decreases = false;

        loop {
            if self.token.is_keyword(kw::ContractRequires) {
                let (mut clause_declarations, clause_requires) = self.parse_contract_requires()?;
                declarations.append(&mut clause_declarations);
                let lane_index = requires.len();
                requires.push(clause_requires);
                record_fn_contract_clause(
                    &mut clause_order,
                    ast::FnContractClauseKind::Requires,
                    ast::FnContractClauseLane::Typed,
                    lane_index,
                );
            } else if self.token.is_keyword(kw::ContractEnsures) {
                let clause_ensures = self.parse_contract_ensures()?;
                let lane_index = ensures.len();
                ensures.push(clause_ensures);
                record_fn_contract_clause(
                    &mut clause_order,
                    ast::FnContractClauseKind::Ensures,
                    ast::FnContractClauseLane::Typed,
                    lane_index,
                );
            } else if self.token.is_keyword(kw::TrustContractRequires) {
                // Trust-origin precondition clause.
                self.bump();
                self.psess.gated_spans.gate(sym::contracts_internals, self.prev_token.span);
                match self.parse_trust_contract_clause(TrustContractClauseKind::Requires)? {
                    TrustContractClause::Typed {
                        declarations: mut clause_declarations,
                        clause,
                    } => {
                        declarations.append(&mut clause_declarations);
                        let lane_index = requires.len();
                        requires.push(clause);
                        record_fn_contract_clause(
                            &mut clause_order,
                            ast::FnContractClauseKind::Requires,
                            ast::FnContractClauseLane::Typed,
                            lane_index,
                        );
                    }
                    TrustContractClause::Opaque(span) => {
                        let lane_index = trust_opaque_requires.len();
                        trust_opaque_requires.push(span);
                        record_fn_contract_clause(
                            &mut clause_order,
                            ast::FnContractClauseKind::Requires,
                            ast::FnContractClauseLane::Opaque,
                            lane_index,
                        );
                    }
                    // Trust (E9): a cited attribute clause IS a native
                    // verifier-language clause; storing it in the native lane
                    // is what makes the two surfaces one representation.
                    TrustContractClause::Native(clause) => {
                        let lane_index = trust_native_requires.len();
                        trust_native_requires.push(clause);
                        record_fn_contract_clause(
                            &mut clause_order,
                            ast::FnContractClauseKind::Requires,
                            ast::FnContractClauseLane::Native,
                            lane_index,
                        );
                    }
                }
            } else if self.token.is_keyword(kw::TrustContractEnsures) {
                // Trust-origin postcondition clause.
                self.bump();
                self.psess.gated_spans.gate(sym::contracts_internals, self.prev_token.span);
                match self.parse_trust_contract_clause(TrustContractClauseKind::Ensures)? {
                    TrustContractClause::Typed { clause, .. } => {
                        let lane_index = ensures.len();
                        ensures.push(clause);
                        record_fn_contract_clause(
                            &mut clause_order,
                            ast::FnContractClauseKind::Ensures,
                            ast::FnContractClauseLane::Typed,
                            lane_index,
                        );
                    }
                    TrustContractClause::Opaque(span) => {
                        let lane_index = trust_opaque_ensures.len();
                        trust_opaque_ensures.push(span);
                        record_fn_contract_clause(
                            &mut clause_order,
                            ast::FnContractClauseKind::Ensures,
                            ast::FnContractClauseLane::Opaque,
                            lane_index,
                        );
                    }
                    // Trust (E9): see the requires arm — a cited attribute
                    // clause joins the native lane, so `#[trust::ensures(P by
                    // T)]` and `fn f(..) ensures P by T` are the same clause
                    // from here on (same `result` binding, same native snippet
                    // syntax, same E9 discharge).
                    TrustContractClause::Native(clause) => {
                        let lane_index = trust_native_ensures.len();
                        trust_native_ensures.push(clause);
                        record_fn_contract_clause(
                            &mut clause_order,
                            ast::FnContractClauseKind::Ensures,
                            ast::FnContractClauseLane::Native,
                            lane_index,
                        );
                    }
                }
            } else if self.token.is_non_raw_ident_where(|id| id.name == sym::requires) {
                // Trust: FIRST-CLASS signature clause (two-language design
                // D0/D1, R3): `fn f(..) requires P .. { .. }`. This grammar
                // position is rejected by vanilla Rust, so the contextual
                // ident cannot collide with any valid program — drop-in
                // invariant 1 holds by construction. No feature gate: this IS
                // the Trust surface (verification by default).
                self.bump();
                let clause = self.parse_trust_native_clause(TrustNativeClauseContext::Signature)?;
                let lane_index = trust_native_requires.len();
                trust_native_requires.push(clause);
                record_fn_contract_clause(
                    &mut clause_order,
                    ast::FnContractClauseKind::Requires,
                    ast::FnContractClauseLane::Native,
                    lane_index,
                );
            } else if self.token.is_non_raw_ident_where(|id| id.name == sym::ensures) {
                // Trust: first-class `ensures` clause (see above).
                self.bump();
                let clause = self.parse_trust_native_clause(TrustNativeClauseContext::Signature)?;
                let lane_index = trust_native_ensures.len();
                trust_native_ensures.push(clause);
                record_fn_contract_clause(
                    &mut clause_order,
                    ast::FnContractClauseKind::Ensures,
                    ast::FnContractClauseLane::Native,
                    lane_index,
                );
            } else if self.token.is_non_raw_ident_where(|id| id.name == sym::decreases) {
                // Trust: one first-class function-recursion termination
                // measure (ratified E5). Unlike loop `decreases`, this clause
                // belongs to the function signature and therefore joins the
                // function-wide authored-order stream.
                let keyword_span = self.token.span;
                if saw_native_decreases {
                    return Err(self.dcx().struct_span_err(
                        keyword_span,
                        "duplicate `decreases` clause on this function",
                    ));
                }
                saw_native_decreases = true;
                self.bump();
                let clause = self.parse_trust_native_clause(TrustNativeClauseContext::Signature)?;
                let lane_index = trust_native_decreases.len();
                trust_native_decreases.push(clause);
                record_fn_contract_clause(
                    &mut clause_order,
                    ast::FnContractClauseKind::Decreases,
                    ast::FnContractClauseLane::Native,
                    lane_index,
                );
            } else {
                break;
            }
        }

        if requires.is_empty()
            && ensures.is_empty()
            && trust_opaque_requires.is_empty()
            && trust_opaque_ensures.is_empty()
            && trust_native_requires.is_empty()
            && trust_native_ensures.is_empty()
            && trust_native_decreases.is_empty()
        {
            Ok(None)
        } else {
            Ok(Some(Box::new(ast::FnContract {
                declarations,
                // The clause vectors are the canonical AST storage for parsed contracts.
                // Keeping duplicate expressions in the legacy single-clause fields creates
                // duplicate closure DefIds that never get lowered into HIR owners.
                requires: None,
                ensures: None,
                requires_clauses: requires,
                ensures_clauses: ensures,
                trust_opaque_requires,
                trust_opaque_ensures,
                trust_native_requires,
                trust_native_ensures,
                trust_native_decreases,
                clause_order,
            })))
        }
    }

    fn parse_contract_requires(
        &mut self,
    ) -> PResult<'a, (ThinVec<rustc_ast::Stmt>, Box<rustc_ast::Expr>)> {
        let _ = self.eat_keyword_noexpect(exp!(ContractRequires).kw);
        self.psess.gated_spans.gate(sym::contracts_internals, self.prev_token.span);
        self.parse_contract_requires_payload()
    }

    /// Parses a requires-clause payload (a block whose trailing expression is
    /// the precondition): shared by upstream clauses and the Trust typed lane.
    fn parse_contract_requires_payload(
        &mut self,
    ) -> PResult<'a, (ThinVec<rustc_ast::Stmt>, Box<rustc_ast::Expr>)> {
        let mut decls_and_precond = self.parse_block()?;

        let precond = match decls_and_precond.stmts.pop() {
            Some(precond) => match precond.kind {
                rustc_ast::StmtKind::Expr(expr) => expr,
                // Insert dummy node that will be rejected by typechecker to
                // avoid reinventing an error
                _ => self.mk_unit_expr(decls_and_precond.span),
            },
            None => self.mk_unit_expr(decls_and_precond.span),
        };
        // Trust: pin the synthesized closure to `-> bool` so a non-bool
        // precondition is an E0308 mismatch at the contract expression
        // (upstream's diagnostic), not an E0271 bound failure at the
        // `contract_check_requires` call.
        let bool_ty = self.mk_ty(
            precond.span,
            TyKind::Path(None, ast::Path::from_ident(Ident::new(sym::bool, precond.span))),
        );
        let precond = self.mk_closure_expr(precond.span, ast::FnRetTy::Ty(bool_ty), precond);
        let decls = decls_and_precond.stmts;
        Ok((decls, precond))
    }

    fn parse_contract_ensures(&mut self) -> PResult<'a, Box<rustc_ast::Expr>> {
        let _ = self.eat_keyword_noexpect(exp!(ContractEnsures).kw);
        self.psess.gated_spans.gate(sym::contracts_internals, self.prev_token.span);
        self.parse_expr()
    }

    /// Trust: parses one Trust-origin clause payload (the brace-delimited
    /// group injected by `ExpandTrustRequires` / `ExpandTrustEnsures`; the
    /// clause keyword has already been eaten and gated).
    ///
    /// The payload joins the typed lane — byte-identical treatment to an
    /// upstream `core::contracts` clause — only when ALL of these hold:
    ///   * its tokens contain no spec-only vocabulary (`result`, compatibility
    ///     `old`/bounded quantifiers, or a `==>` implication),
    ///   * it parses as the expected Rust payload with nothing left over,
    ///   * for an ensures clause, it is a `|ret| ...` closure (upstream's
    ///     surface — a bare bool expression cannot satisfy the
    ///     `contract_build_check_ensures` closure bound).
    /// Anything else becomes an OPAQUE clause: only the payload span is kept,
    /// so the spec text is never name-resolved or type-checked, and the
    /// `trust_contracts` query recovers it from the source map (fail-closed:
    /// an unparseable predicate can only fail to prove, never falsely prove).
    ///
    /// Trust (E9, ONE CITATION REPRESENTATION / TWO SURFACES): a payload that
    /// carries a `by <thm>` citation is not an opaque span — a citation IS the
    /// declaration that this clause is a verifier-language proof obligation
    /// discharged by the Clean kernel. Such a payload is therefore handed to
    /// the SAME [`Self::parse_trust_native_clause`] the first-class signature
    /// surface uses and joins the SAME native lane, so `#[trust::ensures(P by
    /// T)]` and `fn f(..) ensures P by T` produce byte-identical AST from that
    /// point on and share one discharge path. Attribute payloads WITHOUT a
    /// citation are untouched (typed/opaque exactly as before).
    fn parse_trust_contract_clause(
        &mut self,
        kind: TrustContractClauseKind,
    ) -> PResult<'a, TrustContractClause> {
        // Only our expanders emit the Trust clause keywords, and they always
        // wrap the payload in a brace group. Accept a hand-written (already
        // feature-gated) non-brace payload through the upstream typed parse so
        // the grammar stays total.
        if self.token.kind.open_delim() != Some(token::Delimiter::Brace) {
            return match kind {
                TrustContractClauseKind::Requires => {
                    let (declarations, clause) = self.parse_contract_requires_payload()?;
                    Ok(TrustContractClause::Typed { declarations, clause })
                }
                TrustContractClauseKind::Ensures => Ok(TrustContractClause::Typed {
                    declarations: ThinVec::new(),
                    clause: self.parse_expr()?,
                }),
            };
        }

        // Capture the whole payload group without committing to a Rust parse.
        let tree = self.parse_token_tree();
        let rustc_ast::tokenstream::TokenTree::Delimited(dspan, _, _, ref inner) = tree else {
            unreachable!("parse_token_tree at an open delimiter returns TokenTree::Delimited");
        };
        // The span the verifier will read back through the source map: the
        // user-written payload tokens themselves (falling back to the whole
        // group for an empty payload).
        let payload_span = match (inner.iter().next(), inner.iter().last()) {
            (Some(first), Some(last)) => first.span().to(last.span()),
            _ => dspan.entire(),
        };

        // Trust (E9): an authored `by <thm>` citation routes the clause onto
        // the native verifier-language lane. The pre-filter is deliberately
        // narrow — a depth-zero `by` token in the payload — so a payload that
        // cannot carry a citation reaches EXACTLY the pre-existing code below.
        if trust_attribute_payload_has_depth_zero_by(inner) {
            let mut citation_parser = Parser::new(self.psess, inner.clone(), None);
            // Errors here are citation errors (a bare `by`, a malformed dotted
            // path, an empty predicate before one): they are AUTHORED errors
            // and must surface, never be cancelled into a silently uncited
            // opaque clause (a dropped citation would leave a clause looking
            // checked while nothing checked it).
            let clause = citation_parser
                .parse_trust_native_clause(TrustNativeClauseContext::AttributePayload)?;
            if clause.citation.is_some() {
                if citation_parser.token != token::Eof {
                    return Err(self.dcx().struct_span_err(
                        citation_parser.token.span,
                        "expected the end of the contract clause after its `by` citation",
                    ));
                }
                return Ok(TrustContractClause::Native(clause));
            }
            // The `by` was ordinary predicate vocabulary: fall through to the
            // unchanged typed/opaque decision below.
        }

        if trust_spec_payload_is_opaque(inner) {
            return Ok(TrustContractClause::Opaque(payload_span));
        }

        // Speculative typed parse over the captured group. A failure is not an
        // error — the clause simply stays opaque.
        let stream = rustc_ast::tokenstream::TokenStream::new(vec![tree.clone()]);
        let mut payload_parser = Parser::new(self.psess, stream, None);
        let typed = match kind {
            TrustContractClauseKind::Requires => {
                payload_parser.parse_contract_requires_payload().map(|(declarations, clause)| {
                    Some(TrustContractClause::Typed { declarations, clause })
                })
            }
            TrustContractClauseKind::Ensures => payload_parser.parse_expr().map(|clause| {
                trust_ensures_payload_is_closure(&clause)
                    .then(|| TrustContractClause::Typed { declarations: ThinVec::new(), clause })
            }),
        };
        match typed {
            Ok(Some(typed)) if payload_parser.token == token::Eof => Ok(typed),
            Ok(_) => Ok(TrustContractClause::Opaque(payload_span)),
            Err(err) => {
                err.cancel();
                Ok(TrustContractClause::Opaque(payload_span))
            }
        }
    }

    /// Trust: parses one FIRST-CLASS clause payload (two-language design
    /// D0/D1, R3): the bare predicate tokens after a contextual
    /// `requires`/`ensures`/`decreases` in the signature-clause position, ending at the
    /// next clause keyword, `where`, the body `{`, `;`, or EOF.
    ///
    /// Native clauses are ALWAYS verifier-language, span-only predicates.
    /// This origin is preserved separately through AST and HIR. In particular,
    /// it lets the `trust_contracts` query interpret native
    /// `ensures result ...` directly while continuing to require the upstream
    /// `|ret| ...` closure shape for attribute-origin ensures. Native clauses
    /// never reach Rust name resolution, typeck, or the inherited exec-projection
    /// lowering; their runtime story is certified monitors (design §1.1).
    /// The cooked lexer represents immediately trailing prime marks as
    /// `SingleQuote` punctuation, so this span walk can carry `x'` without
    /// teaching ordinary Rust identifier parsing about primed names.
    fn parse_trust_native_clause(
        &mut self,
        context: TrustNativeClauseContext,
    ) -> PResult<'a, ast::TrustNativeClause> {
        let payload_lo = self.token.span;

        // Lookahead walk over a snapshot to find the clause terminator. The
        // walked tokens are never parsed as Rust, so verifier vocabulary can
        // never leak into name resolution or type checking.
        let mut probe = self.create_snapshot_for_diagnostic();
        let mut depth = 0usize;
        let mut payload_hi = payload_lo;
        let mut payload_token_count = 0usize;
        // Token-rendered payload spelling. The span walk below is diagnostic
        // information only: macro expansion (notably a proc macro stamping
        // every emitted token with one call-site span) makes
        // `payload_lo.to(payload_hi)` unable to recover the authored text, so
        // the exact consumed tokens are rendered here as the faithful
        // spelling authority carried through AST and HIR.
        let mut payload_text = String::new();
        // A depth-0 `{` normally terminates the clause (it is the fn body) —
        // EXCEPT when a block-introducing keyword (`match`/`if`/`else`/…) is
        // pending, in which case the brace belongs to that spec expression
        // (`ensures match result { .. }`, the design's §12.1 shape) and is
        // walked as a nested group. Cases the heuristic cannot see stay
        // fail-closed: a misjudged boundary surfaces as a loud parse error on
        // the "body", never as silent acceptance.
        let mut pending_block_kw = false;
        let mut saw_payload_token = false;
        loop {
            let tok = &probe.token;
            let is_next_clause = Self::trust_native_clause_keyword(tok, context);
            // `by` is contextual too: it begins a citation only when a valid
            // (or boundary-malformed) dotted path consumes the entire suffix.
            // An ordinary depth-zero identifier named `by` inside a predicate
            // must remain verifier vocabulary.
            let starts_citation = depth == 0
                && tok.is_non_raw_ident_where(|id| id.name == sym::by)
                && probe.trust_native_citation_suffix_starts_here(context);
            if depth == 0
                && (matches!(tok.kind, token::TokenKind::Semi | token::TokenKind::Eof)
                    || (context == TrustNativeClauseContext::Signature
                        && tok.is_keyword(kw::Where))
                    || is_next_clause
                    || starts_citation)
            {
                break;
            }
            if tok.kind.open_delim() == Some(token::Delimiter::Brace) && depth == 0 {
                // In a self-delimiting attribute payload there is no function
                // body, so a depth-zero brace group always belongs to the
                // predicate.
                if pending_block_kw || context == TrustNativeClauseContext::AttributePayload {
                    pending_block_kw = false;
                    depth += 1;
                } else {
                    break;
                }
            } else if tok.kind.open_delim().is_some() {
                depth += 1;
            } else if tok.kind.close_delim().is_some() {
                if depth == 0 {
                    // A stray closer belongs to the surrounding item; stop.
                    break;
                }
                depth -= 1;
            }
            if depth == 0
                && (tok.is_keyword(kw::Match)
                    || tok.is_keyword(kw::If)
                    || tok.is_keyword(kw::Else)
                    || tok.is_keyword(kw::Loop)
                    || tok.is_keyword(kw::While)
                    || tok.is_keyword(kw::Unsafe))
            {
                pending_block_kw = true;
            }
            match tok.kind {
                // Transparent macro-fragment boundaries render no text; keep
                // their neighbors separated so two distinct tokens can never
                // glue into one different (but valid) verifier name.
                token::TokenKind::OpenInvisible(_) | token::TokenKind::CloseInvisible(_) => {
                    if !payload_text.is_empty() && !payload_text.ends_with(' ') {
                        payload_text.push(' ');
                    }
                }
                _ => {
                    payload_text.push_str(&pprust::token_to_string(tok));
                    // Preserve authored adjacency: post-state primes (`x'`)
                    // and glued operators are only spellable joint, while
                    // `Alone` restores the separating whitespace.
                    if probe.token_spacing == Spacing::Alone {
                        payload_text.push(' ');
                    }
                }
            }
            payload_hi = tok.span;
            saw_payload_token = true;
            payload_token_count += 1;
            probe.bump();
        }

        if !saw_payload_token {
            // Empty payload (`fn f() requires { .. }` parses `{` as the
            // terminator): an authored clause with no predicate is an error,
            // not a silent skip (design §1.2-6).
            return Err(self.dcx().struct_span_err(payload_lo, TRUST_EMPTY_CLAUSE_PAYLOAD_MSG));
        }

        // Consume exactly the payload walked by the lookahead. The query owns
        // semantic parsing of this verifier-language clause.
        // Consume by token count, never by span equality. Macro expansion and
        // proc-macro output may legitimately assign the same call-site span to
        // every token in a clause; using the probe terminator's span as a
        // cursor then consumed zero tokens and left verifier vocabulary in the
        // Rust parser. The snapshot walked exactly this many tokens, so replay
        // that count on the real parser regardless of span identity.
        for _ in 0..payload_token_count {
            debug_assert!(!matches!(self.token.kind, token::TokenKind::Eof));
            self.bump();
        }
        let predicate = payload_lo.to(payload_hi);

        // Trust: optional `by <thm>` citation suffix (E9). The citation is a
        // dotted name path (Clean names use `.` segments); span-only — the
        // kernel owns resolution and statement unification. A bare `by` is an
        // authored error (design §1.2-6).
        let citation = if self.token.is_non_raw_ident_where(|id| id.name == sym::by) {
            let by_span = self.token.span;
            self.bump();
            // Trust (ruling R1): a LEADING `::` is the same spelling mistake as
            // an interior one, so it gets the same named refusal rather than
            // the generic "expected a theorem name" — the widened suffix probe
            // claims it, and a refusal that changes wording with the position
            // of the separator teaches the rule twice.
            if self.token.kind == token::PathSep {
                return Err(self
                    .dcx()
                    .struct_span_err(
                        by_span.to(self.token.span),
                        "a contract clause citation is spelled with `.`, not `::`",
                    )
                    .with_note(
                        "a citation names a CLEAN declaration, and a Clean name has no leading \
                         separator: write `by <theorem>`, or `by <crate>.<theorem>` for a \
                         dependency's (ruling R1, 2026-09-19)",
                    )
                    .with_span_suggestion(
                        self.token.span,
                        "options: remove the leading separator",
                        "",
                        Applicability::MachineApplicable,
                    ));
            }
            let Some(first_segment) = Self::trust_native_citation_segment(&self.token) else {
                return Err(self.dcx().struct_span_err(
                    by_span,
                    "expected a theorem name after `by` in the contract clause citation",
                ));
            };
            let cite_lo = self.token.span;
            let mut cite_hi = self.token.span;
            let mut canonical_name = first_segment.name.as_str().to_owned();
            self.bump();
            // Dotted segments: `by Crate.module.theorem`. A doubled/tripled
            // dot lexes as one `..`/`...` token; claim it here and fail closed
            // (design §1.2-6) instead of silently swallowing the malformed
            // citation into the span-only predicate payload.
            while matches!(self.token.kind, token::Dot | token::DotDot | token::DotDotDot) {
                if self.token.kind != token::Dot {
                    return Err(self.dcx().struct_span_err(
                        cite_lo.to(self.token.span),
                        "expected a name segment after `.` in the contract clause citation",
                    ));
                }
                self.bump();
                let Some(segment) = Self::trust_native_citation_segment(&self.token) else {
                    return Err(self.dcx().struct_span_err(
                        cite_lo.to(self.prev_token.span),
                        "expected a name segment after `.` in the contract clause citation",
                    ));
                };
                canonical_name.push('.');
                canonical_name.push_str(segment.name.as_str());
                cite_hi = self.token.span;
                self.bump();
            }
            // Trust (cross-crate proof citation, ruling R1 — decided
            // 2026-09-19): the citation grammar takes the DOTTED Clean
            // spelling, and that includes the crate-qualified form for a
            // dependency's theorem (`by <crate>.<theorem>`). The Rust path
            // separator is refused here, by name, instead of falling into the
            // generic "expected `.` or the end of the citation" below: `::`
            // is what a Rust programmer reaches for first, and the reason it
            // is not accepted is a decision about the surface rather than a
            // parse accident. The probe
            // (`trust_native_citation_suffix_starts_here`) claims `::` for
            // exactly this diagnostic.
            if self.token.kind == token::PathSep {
                let sep_span = self.token.span;
                return Err(self
                    .dcx()
                    .struct_span_err(
                        cite_lo.to(sep_span),
                        "a contract clause citation is spelled with `.`, not `::`",
                    )
                    .with_note(
                        "a citation names a CLEAN declaration, and Clean name segments are \
                         separated by `.`. That is also how a dependency's theorem is cited: \
                         `by <crate>.<theorem>`, the dependency's crate name, a `.`, then the \
                         declaration's own Clean name",
                    )
                    .with_note(
                        "both spellings are not accepted, because one theorem with two \
                         spellings is two names for one obligation in every diagnostic, \
                         ledger and published row that mentions it (ruling R1, 2026-09-19)",
                    )
                    .with_span_suggestion(
                        sep_span,
                        "options: write the Clean segment separator",
                        ".",
                        Applicability::MachineApplicable,
                    ));
            }
            if !Self::trust_native_clause_terminator(&self.token, context) {
                return Err(self.dcx().struct_span_err(
                    self.token.span,
                    "expected `.` or the end of the contract clause citation",
                ));
            }
            Some(ast::TrustCitation {
                name: Symbol::intern(&canonical_name),
                span: cite_lo.to(cite_hi),
            })
        } else {
            None
        };

        Ok(ast::TrustNativeClause {
            predicate,
            payload: Symbol::intern(payload_text.trim_ascii()),
            citation,
        })
    }

    /// Whether the current contextual `by` consumes a complete citation
    /// suffix. Boundary-malformed suffixes (bare `by`, or a trailing dot) are
    /// also claimed here so the real parser emits a focused authored error.
    fn trust_native_citation_suffix_starts_here(&self, context: TrustNativeClauseContext) -> bool {
        debug_assert!(self.token.is_non_raw_ident_where(|id| id.name == sym::by));
        let mut probe = self.create_snapshot_for_diagnostic();
        probe.bump();

        // A final identifier named `by` is valid predicate vocabulary (for
        // example `ensures by == by`). Do not steal it as a bare citation;
        // an actually malformed trailing `... by` remains in the predicate
        // and fails closed during semantic elaboration.
        if Self::trust_native_clause_terminator(&probe.token, context) {
            return false;
        }

        // `by` is also ordinary verifier vocabulary. In
        // `ensures foo(by) == by by Clean.Lemmas.bound`, the first depth-zero
        // `by` belongs to the predicate and the immediately following one is
        // the citation marker. Without this look-through, the first candidate
        // sees the all-identifier suffix `by Clean...`, claims it as one
        // malformed citation path, and rejects a valid clause. Prefer the later
        // marker when its own remaining suffix is path-shaped through the
        // clause boundary. This check is intentionally raw (it does not recurse
        // through the same ambiguity rule), so a run of contextual `by` tokens
        // consistently selects the last one with a citation-shaped suffix.
        if probe.token.is_non_raw_ident_where(|id| id.name == sym::by) {
            let mut later = probe.create_snapshot_for_diagnostic();
            later.bump();
            let mut later_saw_path_token = false;
            loop {
                if Self::trust_native_clause_terminator(&later.token, context) {
                    if later_saw_path_token {
                        return false;
                    }
                    break;
                }
                if later.token.ident().is_some()
                    || matches!(
                        later.token.kind,
                        // Trust (ruling R1): `::` is claimed as path-shaped so
                        // a misspelled citation reaches the citation parser's
                        // named refusal. Before this it was left in the
                        // predicate payload, and MEASURED (2026-09-19, pack
                        // `ddafc55ba72`) that is worse than a late refusal:
                        // under `-Ztrust-verify=off` the clause compiles with
                        // NO diagnostic at all and the citation the author
                        // wrote is silently dropped; under `=on` it
                        // fail-closes as an "unsupported contract predicate
                        // expression", naming the whole clause and never the
                        // spelling.
                        token::Dot | token::DotDot | token::DotDotDot | token::PathSep
                    )
                {
                    later_saw_path_token = true;
                    later.bump();
                } else {
                    break;
                }
            }
        }

        // Recognize a whole path-shaped suffix before validating it. This
        // deliberately includes raw/reserved identifiers and malformed dot
        // sequences so the real parser emits a hard citation diagnostic. Any
        // operator, delimiter, or other predicate token makes `by` ordinary
        // verifier vocabulary instead.
        let mut saw_path_token = false;
        loop {
            if Self::trust_native_clause_terminator(&probe.token, context) {
                return saw_path_token;
            }
            if probe.token.ident().is_some()
                || matches!(
                    probe.token.kind,
                    // Trust (ruling R1): see the sibling loop above — `::` is
                    // path-shaped here so that `by krate::thm` is claimed and
                    // refused by name.
                    token::Dot | token::DotDot | token::DotDotDot | token::PathSep
                )
            {
                saw_path_token = true;
                probe.bump();
            } else {
                return false;
            }
        }
    }

    fn trust_native_citation_segment(tok: &token::Token) -> Option<Ident> {
        match tok.ident() {
            Some((id, token::IdentKind::Normal)) if !id.is_reserved() => Some(id),
            _ => None,
        }
    }

    fn trust_native_clause_keyword(tok: &token::Token, context: TrustNativeClauseContext) -> bool {
        match context {
            TrustNativeClauseContext::Signature => {
                tok.is_non_raw_ident_where(|id| {
                    matches!(id.name, sym::requires | sym::ensures | sym::decreases)
                }) || tok.is_keyword(kw::ContractRequires)
                    || tok.is_keyword(kw::ContractEnsures)
                    || tok.is_keyword(kw::TrustContractRequires)
                    || tok.is_keyword(kw::TrustContractEnsures)
            }
            TrustNativeClauseContext::Loop => {
                tok.is_non_raw_ident_where(|id| matches!(id.name, sym::invariant | sym::decreases))
            }
            // One attribute carries exactly one clause; `requires`/`ensures`/
            // `decreases`/`invariant` inside its payload are ordinary verifier
            // vocabulary, not a following clause.
            TrustNativeClauseContext::AttributePayload => false,
        }
    }

    fn trust_native_clause_terminator(
        tok: &token::Token,
        context: TrustNativeClauseContext,
    ) -> bool {
        matches!(tok.kind, token::TokenKind::Semi | token::TokenKind::Eof)
            // An attribute payload has no function body, so a depth-zero `{`
            // is part of the predicate (`ensures match result { .. } by T`)
            // rather than the boundary.
            || (context != TrustNativeClauseContext::AttributePayload
                && tok.kind.open_delim() == Some(token::Delimiter::Brace))
            || tok.kind.close_delim().is_some()
            || (context == TrustNativeClauseContext::Signature && tok.is_keyword(kw::Where))
            || Self::trust_native_clause_keyword(tok, context)
    }

    /// Trust: parses FIRST-CLASS loop clauses (two-language design E4/E5):
    /// `while cond invariant P invariant Q decreases e { .. }` — contextual
    /// `invariant`/`decreases` idents between the loop header and its block, a
    /// grammar position vanilla Rust rejects (so `None` for all vanilla
    /// programs, drop-in invariant 1 by construction). Payloads are
    /// verifier-language, span-only — the same walk and fail-closed rules as
    /// signature clauses ([`Self::parse_trust_native_clause`]).
    pub(super) fn parse_trust_loop_contract(
        &mut self,
    ) -> PResult<'a, Option<Box<ast::LoopContract>>> {
        let mut clauses = ThinVec::new();
        let mut saw_decreases = false;
        loop {
            if self.token.is_non_raw_ident_where(|id| id.name == sym::invariant) {
                let keyword_span = self.token.span;
                self.bump();
                let clause = self.parse_trust_native_clause(TrustNativeClauseContext::Loop)?;
                clauses.push(ast::LoopClause {
                    kind: ast::LoopClauseKind::Invariant,
                    keyword_span,
                    clause,
                });
            } else if self.token.is_non_raw_ident_where(|id| id.name == sym::decreases) {
                let keyword_span = self.token.span;
                if saw_decreases {
                    // One termination measure per loop (E5: "one termination
                    // surface"); a duplicate is an authored-spec error.
                    return Err(self.dcx().struct_span_err(
                        keyword_span,
                        "duplicate `decreases` clause on this loop",
                    ));
                }
                saw_decreases = true;
                self.bump();
                let clause = self.parse_trust_native_clause(TrustNativeClauseContext::Loop)?;
                clauses.push(ast::LoopClause {
                    kind: ast::LoopClauseKind::Decreases,
                    keyword_span,
                    clause,
                });
            } else {
                break;
            }
        }
        if clauses.is_empty() {
            Ok(None)
        } else {
            Ok(Some(Box::new(ast::LoopContract { clauses })))
        }
    }

    /// Parses an optional where-clause.
    ///
    /// ```ignore (only-for-syntax-highlight)
    /// where T : Trait<U, V> + 'b, 'a : 'b
    /// ```
    pub(super) fn parse_where_clause(&mut self) -> PResult<'a, WhereClause> {
        self.parse_where_clause_common(None).map(|(clause, _)| clause)
    }

    pub(super) fn parse_struct_where_clause(
        &mut self,
        struct_name: Ident,
        body_insertion_point: Span,
    ) -> PResult<'a, (WhereClause, Option<ThinVec<ast::FieldDef>>)> {
        self.parse_where_clause_common(Some((struct_name, body_insertion_point)))
    }

    fn parse_where_clause_common(
        &mut self,
        struct_: Option<(Ident, Span)>,
    ) -> PResult<'a, (WhereClause, Option<ThinVec<ast::FieldDef>>)> {
        if !self.eat_keyword(exp!(Where)) {
            return Ok((
                WhereClause {
                    has_where_token: false,
                    predicates: ThinVec::new(),
                    span: self.prev_token.span.shrink_to_hi(),
                },
                None,
            ));
        }

        if self.eat_noexpect(&token::Colon) {
            let colon_span = self.prev_token.span;
            self.dcx()
                .struct_span_err(colon_span, "unexpected colon after `where`")
                .with_span_suggestion_short(
                    colon_span,
                    "remove the colon",
                    "",
                    Applicability::MachineApplicable,
                )
                .emit();
        }

        let where_lo = self.prev_token.span;

        // We are considering adding generics to the `where` keyword as an alternative higher-rank
        // parameter syntax (as in `where<'a>` or `where<T>`. To avoid that being a breaking
        // change we parse those generics now, but report an error.
        if self.choose_generics_over_qpath(0) {
            let generics = self.parse_generics()?;
            self.dcx().emit_err(diagnostics::WhereOnGenerics { span: generics.span });
        }

        let (predicates, tuple_struct_body) =
            self.parse_where_clause_predicates(struct_, where_lo)?;
        let where_clause = WhereClause {
            has_where_token: true,
            predicates,
            span: where_lo.to(self.prev_token.span),
        };
        Ok((where_clause, tuple_struct_body))
    }

    pub(super) fn parse_where_clause_predicates(
        &mut self,
        struct_: Option<(Ident, Span)>,
        where_lo: Span,
    ) -> PResult<'a, (ThinVec<WherePredicate>, Option<ThinVec<ast::FieldDef>>)> {
        let mut predicates = ThinVec::new();
        let mut tuple_struct_body = None;

        loop {
            let where_sp = where_lo.to(self.prev_token.span);
            let attrs = self.parse_outer_attributes()?;
            let pred_lo = self.token.span;
            let predicate = self.collect_tokens(None, attrs, ForceCollect::No, |this, attrs| {
                for attr in &attrs {
                    self.psess.gated_spans.gate(sym::where_clause_attrs, attr.span);
                }
                let kind = if this.check_lifetime() && this.look_ahead(1, |t| !t.is_like_plus()) {
                    let lifetime = this.expect_lifetime();
                    // Bounds starting with a colon are mandatory, but possibly empty.
                    this.expect(exp!(Colon))?;
                    let bounds = this.parse_lt_param_bounds();
                    Some(ast::WherePredicateKind::RegionPredicate(ast::WhereRegionPredicate {
                        lifetime,
                        bounds,
                    }))
                } else if this.check_type() {
                    match this.parse_ty_where_predicate_kind_or_recover_tuple_struct_body(
                        struct_, pred_lo, where_sp,
                    )? {
                        PredicateKindOrStructBody::PredicateKind(kind) => Some(kind),
                        PredicateKindOrStructBody::StructBody(body) => {
                            tuple_struct_body = Some(body);
                            None
                        }
                    }
                } else {
                    if let [.., last] = &attrs[..] {
                        if last.is_doc_comment() {
                            this.dcx().emit_err(diagnostics::DocCommentDoesNotDocumentAnything {
                                span: last.span,
                                missing_comma: None,
                            });
                        } else {
                            this.dcx().emit_err(diagnostics::AttrWithoutWherePredicates {
                                span: last.span,
                            });
                        }
                    }
                    None
                };
                let predicate = kind.map(|kind| ast::WherePredicate {
                    attrs,
                    kind,
                    id: DUMMY_NODE_ID,
                    span: pred_lo.to(this.prev_token.span),
                    is_placeholder: false,
                });
                Ok((predicate, Trailing::No, UsePreAttrPos::No))
            })?;
            match predicate {
                Some(predicate) => predicates.push(predicate),
                None => break,
            }

            let prev_token = self.prev_token.span;
            let ate_comma = self.eat(exp!(Comma));

            if self.eat_keyword_noexpect(kw::Where) {
                self.dcx().emit_err(MultipleWhereClauses {
                    span: self.token.span,
                    previous: pred_lo,
                    between: prev_token.shrink_to_hi().to(self.prev_token.span),
                });
            } else if !ate_comma {
                break;
            }
        }

        Ok((predicates, tuple_struct_body))
    }

    fn parse_ty_where_predicate_kind_or_recover_tuple_struct_body(
        &mut self,
        struct_: Option<(Ident, Span)>,
        pred_lo: Span,
        where_sp: Span,
    ) -> PResult<'a, PredicateKindOrStructBody> {
        let mut snapshot = None;

        if let Some(struct_) = struct_
            && self.may_recover()
            && self.token == token::OpenParen
        {
            snapshot = Some((struct_, self.create_snapshot_for_diagnostic()));
        };

        match self.parse_ty_where_predicate_kind() {
            Ok(pred) => Ok(PredicateKindOrStructBody::PredicateKind(
                ast::WherePredicateKind::BoundPredicate(pred),
            )),
            Err(type_err) => {
                let Some(((struct_name, body_insertion_point), mut snapshot)) = snapshot else {
                    return Err(type_err);
                };

                // Check if we might have encountered an out of place tuple struct body.
                match snapshot.parse_tuple_struct_body() {
                    // Since we don't know the exact reason why we failed to parse the
                    // predicate (we might have stumbled upon something bogus like `(T): ?`),
                    // employ a simple heuristic to weed out some pathological cases:
                    // Look for a semicolon (strong indicator) or anything that might mark
                    // the end of the item (weak indicator) following the body.
                    Ok(body)
                        if matches!(snapshot.token.kind, token::Semi | token::Eof)
                            || snapshot.token.can_begin_item() =>
                    {
                        type_err.cancel();

                        let body_sp = pred_lo.to(snapshot.prev_token.span);
                        let map = self.psess.source_map();

                        self.dcx().emit_err(WhereClauseBeforeTupleStructBody {
                            span: where_sp,
                            name: struct_name.span,
                            body: body_sp,
                            sugg: map.span_to_snippet(body_sp).ok().map(|body| {
                                WhereClauseBeforeTupleStructBodySugg {
                                    left: body_insertion_point.shrink_to_hi(),
                                    snippet: body,
                                    right: map.end_point(where_sp).to(body_sp),
                                }
                            }),
                        });

                        self.restore_snapshot(snapshot);
                        Ok(PredicateKindOrStructBody::StructBody(body))
                    }
                    Ok(_) => Err(type_err),
                    Err(body_err) => {
                        body_err.cancel();
                        Err(type_err)
                    }
                }
            }
        }
    }

    pub(crate) fn parse_ty_where_predicate_kind(
        &mut self,
    ) -> PResult<'a, ast::WhereBoundPredicate> {
        // Parse optional `for<'a, 'b>`.
        // This `for` is parsed greedily and applies to the whole predicate,
        // the bounded type can have its own `for` applying only to it.
        // Examples:
        // * `for<'a> Trait1<'a>: Trait2<'a /* ok */>`
        // * `(for<'a> Trait1<'a>): Trait2<'a /* not ok */>`
        // * `for<'a> for<'b> Trait1<'a, 'b>: Trait2<'a /* ok */, 'b /* not ok */>`
        let (bound_vars, _) = self.parse_higher_ranked_binder()?;

        let ty = self.parse_ty_for_where_clause()?;

        if self.eat(exp!(Colon)) {
            // The bounds may be empty; we intentionally accept predicates like  `Ty:`.
            let bounds = self.parse_generic_bounds()?;

            return Ok(ast::WhereBoundPredicate {
                bound_generic_params: bound_vars,
                bounded_ty: ty,
                bounds,
            });
        }

        // NOTE: If we ever end up impl'ing and stabilizing equality predicates (#20041),
        //       we need to pick between `=` and `==`, both is not an option!
        if self.eat(exp!(Eq)) || self.eat(exp!(EqEq)) {
            let lhs_ty = ty;
            let rhs_ty = self.parse_ty()?;

            // NOTE: If we ever end up impl'ing equality predicates,
            //       we ought to track the binder in the AST node!
            let _ = bound_vars;

            let mut diag = self.dcx().struct_span_err(
                lhs_ty.span.to(rhs_ty.span),
                "general type equality constraints are not supported",
            );
            diag.note(
                "see issue #20041 <https://github.com/rust-lang/rust/issues/20041> \
                 for more information",
            );
            diag.span(lhs_ty.span.to(rhs_ty.span));
            diag.span_label(lhs_ty.span.to(rhs_ty.span), "not supported");

            suggest_replacing_equality_pred_with_assoc_item_constraint(&mut diag, *lhs_ty, *rhs_ty);

            return Err(diag);
        }

        self.maybe_recover_bounds_doubled_colon(&ty)?;
        self.unexpected_any()
    }

    pub(super) fn choose_generics_over_qpath(&self, start: usize) -> bool {
        // There's an ambiguity between generic parameters and qualified paths in impls.
        // If we see `<` it may start both, so we have to inspect some following tokens.
        // The following combinations can only start generics,
        // but not qualified paths (with one exception):
        //     `<` `>` - empty generic parameters
        //     `<` `#` - generic parameters with attributes
        //     `<` (LIFETIME|IDENT) `>` - single generic parameter
        //     `<` (LIFETIME|IDENT) `,` - first generic parameter in a list
        //     `<` (LIFETIME|IDENT) `:` - generic parameter with bounds
        //     `<` (LIFETIME|IDENT) `=` - generic parameter with a default
        //     `<` const                - generic const parameter
        //     `<` IDENT `?`            - RECOVERY for `impl<T ?Bound` missing a `:`, meant to
        //                                avoid the `T?` to `Option<T>` recovery for types.
        // The only truly ambiguous case is
        //     `<` IDENT `>` `::` IDENT ...
        // we disambiguate it in favor of generics (`impl<T> ::absolute::Path<T> { ... }`)
        // because this is what almost always expected in practice, qualified paths in impls
        // (`impl <Type>::AssocTy { ... }`) aren't even allowed by type checker at the moment.
        self.look_ahead(start, |t| t == &token::Lt)
            && (self.look_ahead(start + 1, |t| t == &token::Pound || t == &token::Gt)
                || self.look_ahead(start + 1, |t| t.is_lifetime() || t.is_ident())
                    && self.look_ahead(start + 2, |t| {
                        matches!(t.kind, token::Gt | token::Comma | token::Colon | token::Eq)
                        // Recovery-only branch -- this could be removed,
                        // since it only affects diagnostics currently.
                            || t.kind == token::Question
                    })
                || self.is_keyword_ahead(start + 1, &[kw::Const]))
    }
}

fn suggest_replacing_equality_pred_with_assoc_item_constraint(
    diag: &mut Diag<'_>,
    lhs_ty: ast::Ty,
    rhs_ty: ast::Ty,
) {
    let TyKind::Path(qself, ast::Path { segments, .. }) = lhs_ty.kind else { return };

    let mut parts = Vec::new();
    let applicability = match qself {
        // We have something like `Ty::Item<i32> = Rhs`.
        None if let [self_ty_seg, assoc_item_seg] = &segments[..]
            && self_ty_seg.ident.name != kw::PathRoot =>
        {
            parts.push((
                self_ty_seg.span().between(assoc_item_seg.span()),
                ": /* Trait */</* ... */".into(),
            ));
            Applicability::HasPlaceholders
        }
        Some(qself) if let [assoc_item_seg] = &segments[qself.position..] => {
            parts.push((lhs_ty.span.until(qself.ty.span), String::new()));

            // We have something like `<Option<usize> as self::Trait<i32>>::Item = Rhs`.
            if let trait_segs @ [.., final_trait_seg] = &segments[..qself.position] {
                parts.push((qself.ty.span.between(trait_segs[0].span()), ": ".into()));
                let (span, snippet) = match &final_trait_seg.args {
                    Some(args) => {
                        let ast::GenericArgs::AngleBracketed(args) = args else { return };
                        let Some(args) = args.args.last() else { return };
                        (args.span(), ", ")
                    }
                    None => (final_trait_seg.span(), "<"),
                };
                parts.push((span.between(assoc_item_seg.span()), snippet.into()));
                Applicability::MaybeIncorrect
            }
            // We have something like `<[u8]>::Item == Rhs`.
            else {
                parts.push((
                    qself.ty.span.between(assoc_item_seg.span()),
                    ": /* Trait */</* ... */".into(),
                ));
                Applicability::HasPlaceholders
            }
        }
        _ => return,
    };

    parts.push((lhs_ty.span.between(rhs_ty.span), " = ".into()));
    parts.push((rhs_ty.span.shrink_to_hi(), ">".into()));

    diag.multipart_suggestion(
        "replace it with an associated item constraint if possible",
        parts,
        applicability,
    );
}

/// Append one independently checkable marker to the function-wide authored
/// clause stream. Source spans are deliberately absent from this identity:
/// distinct proc-macro outputs can carry exactly equal spans.
fn record_fn_contract_clause(
    clause_order: &mut ThinVec<ast::FnContractClauseMarker>,
    kind: ast::FnContractClauseKind,
    lane: ast::FnContractClauseLane,
    lane_index: usize,
) {
    let ordinal = u32::try_from(clause_order.len())
        .expect("a function cannot contain more than u32::MAX contract clauses");
    let lane_index = u32::try_from(lane_index)
        .expect("a function cannot contain more than u32::MAX clauses in one contract lane");
    clause_order.push(ast::FnContractClauseMarker { ordinal, kind, lane, lane_index });
}

/// Trust: which clause a Trust-origin trust-spec contract payload belongs to.
#[derive(Copy, Clone)]
enum TrustContractClauseKind {
    Requires,
    Ensures,
}

/// Grammar boundary for span-only native predicates. Signature and loop
/// clauses have distinct contextual keywords: `requires`/`ensures`/`decreases`
/// terminate function clauses, while `invariant`/`decreases` terminate loop
/// clauses. An identifier named `invariant` remains ordinary verifier
/// vocabulary in a function predicate, and `requires`/`ensures` remain
/// ordinary vocabulary in a loop predicate. Sharing one terminator set would
/// truncate valid authored predicates.
#[derive(Copy, Clone, PartialEq, Eq)]
enum TrustNativeClauseContext {
    Signature,
    Loop,
    /// Trust (E9): the brace-delimited payload of one `#[trust::requires]` /
    /// `#[trust::ensures]` attribute. The group is self-delimiting, so the only
    /// boundary is its end: there is no function body to stop at (a depth-zero
    /// `{` belongs to the predicate here) and no sibling clause keyword to
    /// watch for (one attribute carries exactly one clause).
    AttributePayload,
}

/// Trust: how one Trust-origin trust-spec contract clause is carried after
/// parsing.
enum TrustContractClause {
    /// Plain, typeable Rust — joins the upstream typed lane (name-resolved,
    /// type-checked, runtime-check lowered) exactly like a `core::contracts`
    /// clause.
    Typed { declarations: ThinVec<rustc_ast::Stmt>, clause: Box<rustc_ast::Expr> },
    /// Spec vocabulary (or otherwise inadmissible to the typed lane): only the
    /// payload span survives. The verifier's `trust_contracts` query recovers
    /// the predicate text through the source map; the program's types and
    /// runtime behavior are untouched.
    Opaque(Span),
    /// Trust (E9): the payload carried a `by <thm>` citation, so it is a
    /// verifier-language clause with a kernel-discharge obligation — exactly
    /// what the first-class signature surface produces. It joins the NATIVE
    /// lane so both surfaces share one representation and one discharge path.
    Native(rustc_ast::TrustNativeClause),
}

/// Trust (E9): whether a `#[trust::requires]` / `#[trust::ensures]` payload can
/// possibly carry a `by <thm>` citation.
///
/// A citation marker is always a DEPTH-ZERO token of the payload, so only the
/// stream's own top-level tokens are inspected — a `by` nested inside a call or
/// a bracket is predicate vocabulary and can never open a citation. This is a
/// pre-filter, not the decision: a payload that passes it is handed to
/// [`Parser::parse_trust_native_clause`], which applies the one canonical
/// citation grammar (shared with the first-class signature surface) and decides
/// whether this `by` actually starts a citation. A payload that fails it takes
/// the pre-existing typed/opaque path with no behavior change whatsoever.
fn trust_attribute_payload_has_depth_zero_by(stream: &rustc_ast::tokenstream::TokenStream) -> bool {
    use rustc_ast::tokenstream::TokenTree;

    stream.iter().any(|tt| match tt {
        TokenTree::Token(tok, _) => tok.is_non_raw_ident_where(|id| id.name == sym::by),
        TokenTree::Delimited(..) => false,
    })
}

/// Trust: whether a trust-spec clause payload must stay OPAQUE — i.e. it uses
/// spec-only vocabulary that is not Rust and must never reach name resolution
/// or typeck. Detected purely at the token level (before any speculative
/// parse, so recovery diagnostics can never leak):
///   * the reserved spec atoms `result`, `old`, `forall`, `exists`;
///   * the spec implication `==>` (an `==` token followed by a `>` token —
///     that sequence is never valid Rust, so no typeable payload is lost).
/// The check is deliberately conservative: a payload that merely MENTIONS a
/// reserved name (e.g. a user item named `old`) is routed to the opaque,
/// fail-closed lane rather than guessed at.
fn trust_spec_payload_is_opaque(stream: &rustc_ast::tokenstream::TokenStream) -> bool {
    use rustc_ast::tokenstream::TokenTree;

    let mut prev_was_eqeq = false;
    for tt in stream.iter() {
        match tt {
            TokenTree::Token(tok, _) => {
                if prev_was_eqeq && tok.kind == token::Gt {
                    return true;
                }
                prev_was_eqeq = tok.kind == token::EqEq;
                if let Some((ident, _)) = tok.ident()
                    && matches!(ident.name, sym::result | sym::old | sym::forall | sym::exists)
                {
                    return true;
                }
            }
            TokenTree::Delimited(.., inner) => {
                prev_was_eqeq = false;
                if trust_spec_payload_is_opaque(inner) {
                    return true;
                }
            }
        }
    }
    false
}

/// Trust: whether a Trust-origin ensures payload is (syntactically) the
/// `|ret| ...` closure upstream's typed lane expects, looking through
/// parentheses and the single-tail-expression block the expander's brace
/// wrapping produces. Anything else cannot satisfy the
/// `contract_build_check_ensures` closure bound and stays opaque.
fn trust_ensures_payload_is_closure(expr: &rustc_ast::Expr) -> bool {
    let mut expr = expr;
    loop {
        match &expr.kind {
            ast::ExprKind::Closure(..) => return true,
            ast::ExprKind::Paren(inner) => expr = inner,
            ast::ExprKind::Block(block, None) => {
                let [stmt] = &block.stmts[..] else {
                    return false;
                };
                let ast::StmtKind::Expr(inner) = &stmt.kind else {
                    return false;
                };
                expr = inner;
            }
            _ => return false,
        }
    }
}

/// Trust: the single spelling of "you wrote a clause keyword and no predicate".
///
/// Both the native clause position and the attribute compat surface refuse an
/// empty payload, and they must refuse it with the same words: the attribute
/// spellings are a compat surface over the native grammar, not a second lane,
/// so two texts for one rule would be two rules to a reader.
const TRUST_EMPTY_CLAUSE_PAYLOAD_MSG: &str =
    "expected a predicate expression after the contract clause keyword";

/// Trust: turn one recognized `#[trust::loop_invariant(P)]` /
/// `#[trust::decreases(e)]` attribute into the SAME [`ast::LoopClause`] the
/// native `loop`/`while` clause position produces.
///
/// This is the whole of the attribute surface's meaning, and it is deliberately
/// a thin wrapper rather than a second implementation. The payload is captured
/// by [`Parser::parse_trust_native_clause`] — the identical routine the native
/// grammar uses — so the attribute and the native clause cannot disagree about
/// what the predicate IS. That matters concretely, not decoratively: that
/// routine is where invisible macro-fragment boundaries are rendered as
/// separators so two tokens can never glue into a different valid verifier
/// name, where authored adjacency is preserved so `x'` survives, and where the
/// optional `by <thm>` citation is canonicalized. A `TokenStream::to_string()`
/// or a meta-item parse would silently differ on every one of those.
///
/// The `predicate` span it returns is exactly the payload tokens INSIDE the
/// parentheses, which is what `trust_contract_query` reads back through the
/// source map whenever the span is not from expansion; the surrounding
/// `#[trust::…(` and `)]` are never part of it.
///
/// Fail-closed in three ways, each of which would otherwise be a dropped
/// clause: an empty payload is an error raised below, at the attribute's own
/// span; a payload the clause walk does not consume to the end leaves a
/// non-`Eof` token and [`crate::parse_in`] raises `unexpected()`; and a
/// `Delimiter` other than parentheses never reaches here (the caller rejects
/// it).
pub fn parse_trust_loop_clause_attr<'a>(
    psess: &'a rustc_session::parse::ParseSess,
    kind: ast::LoopClauseKind,
    keyword_span: Span,
    args: &ast::DelimArgs,
) -> PResult<'a, ast::LoopClause> {
    // Trust: `#[trust::loop_invariant()]` — the payload token stream is EMPTY,
    // so the parser `parse_in` builds below opens on `Eof` and
    // `parse_trust_native_clause`'s `payload_lo = self.token.span` is the
    // synthesized end-of-stream span, which renders at the crate root (1:1).
    // The refusal is correct; the position was not, and a diagnostic that
    // points at a file rather than at the attribute cannot be acted on
    // (DESIGN_PHILOSOPHY principle 10 / v7-D3: a refusal must carry the fix).
    //
    // The empty case is decided HERE, where the attribute's own span is in
    // hand, so it lands on the same span as the sibling refusals raised by the
    // caller in `rustc_expand` (`needs a parenthesized predicate`, `takes its
    // predicate in parentheses`). The native clause position is untouched:
    // there `payload_lo` is a real authored token span and already correct.
    // The message is shared with that arm so the two spellings of one rule
    // cannot drift apart.
    if args.tokens.is_empty() {
        return Err(psess.dcx().struct_span_err(keyword_span, TRUST_EMPTY_CLAUSE_PAYLOAD_MSG));
    }
    let clause = crate::parse_in(psess, args.tokens.clone(), "loop clause attribute", |p| {
        p.parse_trust_native_clause(TrustNativeClauseContext::Loop)
    })?;
    Ok(ast::LoopClause { kind, keyword_span, clause })
}
