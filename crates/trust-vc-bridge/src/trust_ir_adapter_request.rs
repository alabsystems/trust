use std::collections::BTreeMap;

use trust_vc_trust_engine::{
    TrustArithOp, TrustCompareOp, TrustContractFrame, TrustExpr, TrustFunctionSignature,
    TrustLogicOp, TrustNativeContext, TrustOldValue, TrustProofLineage, TrustProofPolicy,
    TrustSort, TrustSourceSpan, TrustTrustIrAdapterRequest, TrustTrustIrObligation,
    TrustTrustIrObligationKind, TrustTrustIrProofUnit, TrustVariable,
};
use trust_verifier_api::{
    BundleSubject, MetadataEntry, ObligationKind, SourceLocation,
    TRUST_SPEC_PREDICATE_SCHEMA_VERSION, TrustContract, TrustContractBundle, TrustObligation,
    TrustSpecBinaryOp, TrustSpecBvBinaryOp, TrustSpecExpr, TrustSpecExprKind, TrustSpecPredicate,
    TrustSpecSort, TrustSpecUnaryOp, TrustSpecVariable, TrustSpecVariableOrigin,
};

/// Build the trust-vc-native Tmir adapter request consumed by `trust-vc-trust-runner`.
///
/// This is the Trust-side producer for the trust_vc `TrustTrustIrAdapterRequest`
/// boundary. It consumes the typed `TrustContractBundle` shape emitted by the
/// compiler/Tmir pipeline, preserves requires/ensures `result` and `old(...)`
/// bindings as a native trust_vc contract frame, and forwards typed CFG
/// translation-validation VCs as trust_vc Tmir obligations.
pub fn trust_vc_trust_ir_adapter_request_from_bundle(
    bundle: &TrustContractBundle,
) -> Result<TrustTrustIrAdapterRequest, TrustVcTmirAdapterEmissionError> {
    let mut emitter = AdapterEmitter::new(bundle);
    emitter.emit()
}

/// Failure while emitting trust-vc's native Tmir adapter request from Trust data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TrustVcTmirAdapterEmissionError {
    EmptyBundle { bundle_id: String },
    MissingContract { obligation_id: String, contract_id: String },
    UnsupportedObligationKind { obligation_id: String, kind: ObligationKind },
    UnsupportedContractPredicate { obligation_id: String, contract_id: String, reason: String },
    InvalidTypedPredicate { obligation_id: String, reason: String },
    MissingTypedCfgPredicate { obligation_id: String },
    MissingNativeOwnershipContext { obligation_id: String, kind: ObligationKind },
    UnsupportedSpecExpression { obligation_id: String, reason: String },
    InvalidIntegerLiteral { obligation_id: String, value: String },
    SortConflict { name: String, first: TrustSort, second: TrustSort },
}

impl std::fmt::Display for TrustVcTmirAdapterEmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyBundle { bundle_id } => {
                write!(f, "bundle `{bundle_id}` has no trust_vc Tmir obligations")
            }
            Self::MissingContract { obligation_id, contract_id } => write!(
                f,
                "obligation `{obligation_id}` references missing contract `{contract_id}`"
            ),
            Self::UnsupportedObligationKind { obligation_id, kind } => {
                write!(f, "obligation `{obligation_id}` has unsupported trust_vc kind {kind:?}")
            }
            Self::UnsupportedContractPredicate { obligation_id, contract_id, reason } => write!(
                f,
                "obligation `{obligation_id}` contract `{contract_id}` is not a typed Trust predicate: {reason}"
            ),
            Self::InvalidTypedPredicate { obligation_id, reason } => {
                write!(f, "obligation `{obligation_id}` has invalid typed predicate: {reason}")
            }
            Self::MissingTypedCfgPredicate { obligation_id } => write!(
                f,
                "trust_vc native obligation `{obligation_id}` is missing trust.vc.formula.payload typed predicate"
            ),
            Self::MissingNativeOwnershipContext { obligation_id, kind } => write!(
                f,
                "trust_vc native obligation `{obligation_id}` ({kind:?}) requires typed ownership, borrow, lifetime, alias, or provenance context"
            ),
            Self::UnsupportedSpecExpression { obligation_id, reason } => {
                write!(f, "obligation `{obligation_id}` uses unsupported spec expression: {reason}")
            }
            Self::InvalidIntegerLiteral { obligation_id, value } => {
                write!(f, "obligation `{obligation_id}` has non-i128 integer literal `{value}`")
            }
            Self::SortConflict { name, first, second } => {
                write!(
                    f,
                    "variable `{name}` has conflicting trust_vc sorts {first:?} and {second:?}"
                )
            }
        }
    }
}

impl std::error::Error for TrustVcTmirAdapterEmissionError {}

struct AdapterEmitter<'a> {
    bundle: &'a TrustContractBundle,
    variables: BTreeMap<String, TrustSort>,
    result_sort: Option<TrustSort>,
    old_values: BTreeMap<String, TrustOldValue>,
}

impl<'a> AdapterEmitter<'a> {
    fn new(bundle: &'a TrustContractBundle) -> Self {
        Self { bundle, variables: BTreeMap::new(), result_sort: None, old_values: BTreeMap::new() }
    }

    fn emit(&mut self) -> Result<TrustTrustIrAdapterRequest, TrustVcTmirAdapterEmissionError> {
        let mut obligations = Vec::new();
        for obligation in &self.bundle.obligations {
            match trust_ir_obligation_kind(obligation) {
                Some(TrustTrustIrObligationKind::Requires)
                | Some(TrustTrustIrObligationKind::Ensures) => {
                    obligations.push(self.emit_contract_obligation(obligation)?);
                }
                Some(
                    TrustTrustIrObligationKind::TranslationValidation
                    | TrustTrustIrObligationKind::MemoryNoAlias
                    | TrustTrustIrObligationKind::BorrowProvenance,
                ) => {
                    obligations.push(self.emit_typed_vc_obligation(obligation)?);
                }
                None => {}
                Some(kind) => {
                    return Err(TrustVcTmirAdapterEmissionError::UnsupportedObligationKind {
                        obligation_id: obligation.obligation_id.clone(),
                        kind: public_kind_for_error(kind),
                    });
                }
            }
        }

        if obligations.is_empty() {
            return Err(TrustVcTmirAdapterEmissionError::EmptyBundle {
                bundle_id: self.bundle.bundle_id.clone(),
            });
        }

        let mut request = TrustTrustIrAdapterRequest::new(self.bundle.bundle_id.clone())
            .with_proof_policy(TrustProofPolicy::EvidenceOnly)
            .insert_metadata("trust.producer", "Trust")
            .insert_metadata("trust.pipeline", "compiler-trust-contract-bundle+trust_ir")
            .insert_metadata("trust.verifier_api.schema_version", &self.bundle.schema_version);

        for entry in &self.bundle.metadata {
            request = request.insert_metadata(entry.key.clone(), entry.value.clone());
        }

        let unit = TrustTrustIrProofUnit::new(self.unit_id(), self.native_context())
            .with_display_name(self.display_name())
            .with_obligations(obligations);
        Ok(request.with_unit(unit))
    }

    fn emit_contract_obligation(
        &mut self,
        obligation: &TrustObligation,
    ) -> Result<TrustTrustIrObligation, TrustVcTmirAdapterEmissionError> {
        let contract = self.contract_for(obligation)?;
        let predicate = typed_predicate_from_contract(obligation, contract)?;
        let expr = self.lower_predicate(obligation, &predicate)?;
        let kind = trust_ir_obligation_kind(obligation).expect("contract kind was pre-filtered");
        let rule = match kind {
            TrustTrustIrObligationKind::Requires => "requires-clause",
            TrustTrustIrObligationKind::Ensures => "ensures-clause",
            _ => "contract-clause",
        };

        Ok(self.finish_obligation(
            obligation,
            kind,
            expr,
            TrustProofLineage::trust_types_contract("Trust trust-mir-extract", rule)
                .with_input_digest(predicate_digest(&predicate)),
        ))
    }

    fn emit_typed_vc_obligation(
        &mut self,
        obligation: &TrustObligation,
    ) -> Result<TrustTrustIrObligation, TrustVcTmirAdapterEmissionError> {
        let predicate = typed_cfg_predicate_from_metadata(obligation)?;
        let expr = self.lower_predicate(obligation, &predicate)?;
        let kind = trust_ir_obligation_kind(obligation).expect("VC kind was pre-filtered");
        if matches!(
            kind,
            TrustTrustIrObligationKind::MemoryNoAlias
                | TrustTrustIrObligationKind::BorrowProvenance
        ) {
            return Err(TrustVcTmirAdapterEmissionError::MissingNativeOwnershipContext {
                obligation_id: obligation.obligation_id.clone(),
                kind: obligation.kind.clone(),
            });
        }
        let rule = match kind {
            TrustTrustIrObligationKind::TranslationValidation => "typed-cfg-proof",
            TrustTrustIrObligationKind::MemoryNoAlias => "typed-memory-no-alias",
            TrustTrustIrObligationKind::BorrowProvenance => "typed-borrow-provenance",
            _ => "typed-vc-proof",
        };
        Ok(self.finish_obligation(
            obligation,
            kind,
            expr,
            TrustProofLineage::trust_ir_lowering("Trust trust-mir-extract", rule)
                .with_input_digest(predicate_digest(&predicate)),
        ))
    }

    fn finish_obligation(
        &self,
        obligation: &TrustObligation,
        kind: TrustTrustIrObligationKind,
        expr: TrustExpr,
        lineage: TrustProofLineage,
    ) -> TrustTrustIrObligation {
        let mut emitted =
            TrustTrustIrObligation::expr(obligation.obligation_id.clone(), kind, expr, lineage);
        if let Some(span) = source_span(&obligation.source) {
            emitted = emitted.with_span(span);
        }
        emitted
    }

    fn lower_predicate(
        &mut self,
        obligation: &TrustObligation,
        predicate: &TrustSpecPredicate,
    ) -> Result<TrustExpr, TrustVcTmirAdapterEmissionError> {
        predicate.validate().map_err(|reason| {
            TrustVcTmirAdapterEmissionError::InvalidTypedPredicate {
                obligation_id: obligation.obligation_id.clone(),
                reason,
            }
        })?;
        if !predicate.has_current_schema() || predicate.root_sort != TrustSpecSort::Bool {
            return Err(TrustVcTmirAdapterEmissionError::InvalidTypedPredicate {
                obligation_id: obligation.obligation_id.clone(),
                reason: format!(
                    "expected schema {TRUST_SPEC_PREDICATE_SCHEMA_VERSION} rooted at bool"
                ),
            });
        }

        for variable in &predicate.variables {
            self.record_spec_variable(&obligation.obligation_id, variable)?;
        }

        let mut lowering = ExprLowering {
            obligation_id: &obligation.obligation_id,
            variables: &mut self.variables,
            result_sort: &mut self.result_sort,
            old_values: &mut self.old_values,
        };
        lowering.lower(&predicate.root)
    }

    fn record_spec_variable(
        &mut self,
        obligation_id: &str,
        variable: &TrustSpecVariable,
    ) -> Result<(), TrustVcTmirAdapterEmissionError> {
        if matches!(variable.origin, TrustSpecVariableOrigin::Quantified) {
            return Ok(());
        }
        let sort = spec_sort(variable.sort).ok_or_else(|| {
            TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                obligation_id: obligation_id.to_string(),
                reason: "array and float sorts are outside the trust_vc direct scalar adapter fragment"
                    .to_string(),
            }
        })?;
        record_variable_sort(&mut self.variables, variable.name.clone(), sort)
    }

    fn contract_for(
        &self,
        obligation: &TrustObligation,
    ) -> Result<&TrustContract, TrustVcTmirAdapterEmissionError> {
        let contract_id = obligation.contract_id.as_ref().ok_or_else(|| {
            TrustVcTmirAdapterEmissionError::UnsupportedContractPredicate {
                obligation_id: obligation.obligation_id.clone(),
                contract_id: "<none>".to_string(),
                reason: "contract obligations must reference a compiler contract".to_string(),
            }
        })?;
        self.bundle
            .contracts
            .iter()
            .find(|contract| &contract.contract_id == contract_id)
            .ok_or_else(|| TrustVcTmirAdapterEmissionError::MissingContract {
                obligation_id: obligation.obligation_id.clone(),
                contract_id: contract_id.clone(),
            })
    }

    fn native_context(&self) -> TrustNativeContext {
        let params = self
            .variables
            .iter()
            .map(|(name, sort)| TrustVariable::new(name.clone(), sort.clone()))
            .collect::<Vec<_>>();
        let return_sort = self.result_sort.clone().unwrap_or(TrustSort::Bool);
        let signature = TrustFunctionSignature::new(self.unit_id(), params, return_sort.clone());

        let mut frame = TrustContractFrame::new();
        if self.result_sort.is_some() {
            frame = frame.with_return_value(TrustVariable::new("result", return_sort));
        }
        for old_value in self.old_values.values() {
            frame = frame.with_old_value(old_value.clone());
        }

        TrustNativeContext::new(signature).with_contract_frame(frame)
    }

    fn unit_id(&self) -> String {
        match &self.bundle.subject {
            BundleSubject::Function { path, .. } => path.clone(),
            BundleSubject::Crate { name } => name.clone(),
            BundleSubject::Artifact { name, .. } => name.clone(),
            _ => self.bundle.bundle_id.clone(),
        }
    }

    fn display_name(&self) -> String {
        match &self.bundle.subject {
            BundleSubject::Function { crate_name, path } => {
                format!("{path} ({crate_name})")
            }
            BundleSubject::Crate { name } => name.clone(),
            BundleSubject::Artifact { name, kind } => format!("{name} ({kind})"),
            _ => self.bundle.bundle_id.clone(),
        }
    }
}

struct ExprLowering<'a> {
    obligation_id: &'a str,
    variables: &'a mut BTreeMap<String, TrustSort>,
    result_sort: &'a mut Option<TrustSort>,
    old_values: &'a mut BTreeMap<String, TrustOldValue>,
}

impl ExprLowering<'_> {
    fn lower(
        &mut self,
        expr: &TrustSpecExpr,
    ) -> Result<TrustExpr, TrustVcTmirAdapterEmissionError> {
        match &expr.kind {
            TrustSpecExprKind::BoolLiteral { value } => Ok(TrustExpr::bool_literal(*value)),
            TrustSpecExprKind::IntLiteral { value } => {
                let value = value.parse::<i128>().map_err(|_| {
                    TrustVcTmirAdapterEmissionError::InvalidIntegerLiteral {
                        obligation_id: self.obligation_id.to_string(),
                        value: value.clone(),
                    }
                })?;
                Ok(TrustExpr::int_literal(value, self.spec_sort(expr.sort)?))
            }
            TrustSpecExprKind::BitVecLiteral { value, width } => {
                let value = value.parse::<i128>().map_err(|_| {
                    TrustVcTmirAdapterEmissionError::InvalidIntegerLiteral {
                        obligation_id: self.obligation_id.to_string(),
                        value: value.clone(),
                    }
                })?;
                Ok(TrustExpr::int_literal(
                    value,
                    TrustSort::BitVector { width: *width, signed: false },
                ))
            }
            TrustSpecExprKind::Variable { name } => {
                let sort = self.spec_sort(expr.sort)?;
                record_variable_sort(self.variables, name.clone(), sort.clone())?;
                Ok(TrustExpr::variable(name.clone(), sort))
            }
            TrustSpecExprKind::Result => {
                let sort = self.spec_sort(expr.sort)?;
                record_optional_sort("result", self.result_sort, sort.clone())?;
                Ok(TrustExpr::variable("result", sort))
            }
            TrustSpecExprKind::Unary { op, expr } => match op {
                TrustSpecUnaryOp::Not => Ok(TrustExpr::not(self.lower(expr)?)),
                TrustSpecUnaryOp::Neg => Ok(TrustExpr::arith(
                    TrustArithOp::Sub,
                    TrustExpr::int_literal(0, self.spec_sort(expr.sort)?),
                    self.lower(expr)?,
                    self.spec_sort(expr.sort)?,
                )),
                _ => Err(TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                    obligation_id: self.obligation_id.to_string(),
                    reason: "non-exhaustive TrustSpecUnaryOp is not mapped into trust_vc TrustExpr"
                        .to_string(),
                }),
            },
            TrustSpecExprKind::Binary { op, lhs, rhs } => self.lower_binary(*op, lhs, rhs, expr.sort),
            TrustSpecExprKind::BvBinary { op, lhs, rhs, width } => {
                self.lower_bv_binary(*op, lhs, rhs, *width)
            }
            TrustSpecExprKind::Old { expr: old_expr } => self.lower_old(old_expr),
            TrustSpecExprKind::Field { .. }
            | TrustSpecExprKind::Index { .. }
            | TrustSpecExprKind::Quantifier { .. } => {
                Err(TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                    obligation_id: self.obligation_id.to_string(),
                    reason: "field, index, and quantifier nodes are not yet mapped into trust_vc TrustExpr".to_string(),
                })
            }
            _ => Err(TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                obligation_id: self.obligation_id.to_string(),
                reason: "non-exhaustive TrustSpecExpr node is not mapped into trust_vc TrustExpr"
                    .to_string(),
            }),
        }
    }

    fn lower_binary(
        &mut self,
        op: TrustSpecBinaryOp,
        lhs: &TrustSpecExpr,
        rhs: &TrustSpecExpr,
        sort: TrustSpecSort,
    ) -> Result<TrustExpr, TrustVcTmirAdapterEmissionError> {
        let left = self.lower(lhs)?;
        let right = self.lower(rhs)?;
        Ok(match op {
            TrustSpecBinaryOp::Add => {
                TrustExpr::arith(TrustArithOp::Add, left, right, self.spec_sort(sort)?)
            }
            TrustSpecBinaryOp::Sub => {
                TrustExpr::arith(TrustArithOp::Sub, left, right, self.spec_sort(sort)?)
            }
            TrustSpecBinaryOp::Mul => {
                TrustExpr::arith(TrustArithOp::Mul, left, right, self.spec_sort(sort)?)
            }
            TrustSpecBinaryOp::Div => {
                TrustExpr::arith(TrustArithOp::Div, left, right, self.spec_sort(sort)?)
            }
            TrustSpecBinaryOp::Mod => {
                TrustExpr::arith(TrustArithOp::Rem, left, right, self.spec_sort(sort)?)
            }
            TrustSpecBinaryOp::Eq => TrustExpr::compare(TrustCompareOp::Eq, left, right),
            TrustSpecBinaryOp::Ne => TrustExpr::compare(TrustCompareOp::Ne, left, right),
            TrustSpecBinaryOp::Lt => TrustExpr::compare(TrustCompareOp::Lt, left, right),
            TrustSpecBinaryOp::Le => TrustExpr::compare(TrustCompareOp::Le, left, right),
            TrustSpecBinaryOp::Gt => TrustExpr::compare(TrustCompareOp::Gt, left, right),
            TrustSpecBinaryOp::Ge => TrustExpr::compare(TrustCompareOp::Ge, left, right),
            TrustSpecBinaryOp::And => TrustExpr::logic(TrustLogicOp::And, left, right),
            TrustSpecBinaryOp::Or => TrustExpr::logic(TrustLogicOp::Or, left, right),
            TrustSpecBinaryOp::Implies => TrustExpr::implies(left, right),
            _ => {
                return Err(TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                    obligation_id: self.obligation_id.to_string(),
                    reason:
                        "non-exhaustive TrustSpecBinaryOp is not mapped into trust_vc TrustExpr"
                            .to_string(),
                });
            }
        })
    }

    fn lower_bv_binary(
        &mut self,
        op: TrustSpecBvBinaryOp,
        lhs: &TrustSpecExpr,
        rhs: &TrustSpecExpr,
        width: u32,
    ) -> Result<TrustExpr, TrustVcTmirAdapterEmissionError> {
        let left = self.lower(lhs)?;
        let right = self.lower(rhs)?;
        let sort = TrustSort::BitVector { width, signed: false };
        Ok(match op {
            TrustSpecBvBinaryOp::Add => TrustExpr::arith(TrustArithOp::Add, left, right, sort),
            TrustSpecBvBinaryOp::Sub => TrustExpr::arith(TrustArithOp::Sub, left, right, sort),
            TrustSpecBvBinaryOp::Mul => TrustExpr::arith(TrustArithOp::Mul, left, right, sort),
            TrustSpecBvBinaryOp::Udiv => TrustExpr::arith(TrustArithOp::Div, left, right, sort),
            TrustSpecBvBinaryOp::Urem => TrustExpr::arith(TrustArithOp::Rem, left, right, sort),
            TrustSpecBvBinaryOp::Ult => TrustExpr::compare(TrustCompareOp::Lt, left, right),
            TrustSpecBvBinaryOp::Ule => TrustExpr::compare(TrustCompareOp::Le, left, right),
            TrustSpecBvBinaryOp::Ugt => TrustExpr::compare(TrustCompareOp::Gt, left, right),
            TrustSpecBvBinaryOp::Uge => TrustExpr::compare(TrustCompareOp::Ge, left, right),
            _ => {
                return Err(TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                    obligation_id: self.obligation_id.to_string(),
                    reason: "bitwise, shift, signed comparison, and bitvector-unary nodes are not mapped into trust_vc TrustExpr"
                        .to_string(),
                });
            }
        })
    }

    fn lower_old(
        &mut self,
        expr: &TrustSpecExpr,
    ) -> Result<TrustExpr, TrustVcTmirAdapterEmissionError> {
        let source = old_source_label(self.obligation_id, expr)?;
        let snapshot = old_snapshot_name(&source);
        let sort = self.spec_sort(expr.sort)?;
        let snapshot_var = TrustVariable::new(snapshot.clone(), sort.clone());
        self.old_values
            .entry(source.clone())
            .or_insert_with(|| TrustOldValue::new(source.clone(), snapshot_var));
        Ok(TrustExpr::old(source, snapshot, sort))
    }

    fn spec_sort(&self, sort: TrustSpecSort) -> Result<TrustSort, TrustVcTmirAdapterEmissionError> {
        spec_sort(sort).ok_or_else(|| TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
            obligation_id: self.obligation_id.to_string(),
            reason: "array and float sorts are outside the trust_vc direct scalar adapter fragment"
                .to_string(),
        })
    }
}

fn typed_predicate_from_contract(
    obligation: &TrustObligation,
    contract: &TrustContract,
) -> Result<TrustSpecPredicate, TrustVcTmirAdapterEmissionError> {
    match TrustSpecPredicate::from_contract_predicate(&contract.predicate) {
        Ok(Some(predicate)) => Ok(predicate),
        Ok(None) => Err(TrustVcTmirAdapterEmissionError::UnsupportedContractPredicate {
            obligation_id: obligation.obligation_id.clone(),
            contract_id: contract.contract_id.clone(),
            reason: "expected Tmir trust.spec-predicate.v1 payload".to_string(),
        }),
        Err(error) => Err(TrustVcTmirAdapterEmissionError::InvalidTypedPredicate {
            obligation_id: obligation.obligation_id.clone(),
            reason: error.to_string(),
        }),
    }
}

fn typed_cfg_predicate_from_metadata(
    obligation: &TrustObligation,
) -> Result<TrustSpecPredicate, TrustVcTmirAdapterEmissionError> {
    let payload =
        metadata_value(&obligation.metadata, "trust.vc.formula.payload").ok_or_else(|| {
            TrustVcTmirAdapterEmissionError::MissingTypedCfgPredicate {
                obligation_id: obligation.obligation_id.clone(),
            }
        })?;
    // Trust (R1 corpus): depth-tolerant parse — dense loop-unrolled functions
    // emit legitimately >128-deep predicate trees; see `trust_types::json_depth`.
    trust_types::json_depth::from_str_deep(payload).map_err(|error| {
        TrustVcTmirAdapterEmissionError::InvalidTypedPredicate {
            obligation_id: obligation.obligation_id.clone(),
            reason: error.to_string(),
        }
    })
}

/// Decode and lower the exact public typed CFG predicate carried by one
/// verifier obligation.
///
/// The direct MIR-memory lane uses this same lowering as the native TrustIR
/// request emitter so its private proof-unit predicate cannot drift onto a
/// merely same-ID proposition.  The returned expression is the public
/// bad-state formula; callers that verify an assertion must apply the exact
/// negation normalization used by the MIR-memory producer.
pub(crate) fn lowered_typed_cfg_predicate_from_metadata(
    obligation: &TrustObligation,
) -> Result<TrustExpr, TrustVcTmirAdapterEmissionError> {
    let predicate = typed_cfg_predicate_from_metadata(obligation)?;
    predicate.validate().map_err(|reason| {
        TrustVcTmirAdapterEmissionError::InvalidTypedPredicate {
            obligation_id: obligation.obligation_id.clone(),
            reason,
        }
    })?;
    if !predicate.has_current_schema() || predicate.root_sort != TrustSpecSort::Bool {
        return Err(TrustVcTmirAdapterEmissionError::InvalidTypedPredicate {
            obligation_id: obligation.obligation_id.clone(),
            reason: format!("expected schema {TRUST_SPEC_PREDICATE_SCHEMA_VERSION} rooted at bool"),
        });
    }

    let mut variables = BTreeMap::new();
    for variable in &predicate.variables {
        if !matches!(variable.origin, TrustSpecVariableOrigin::Quantified) {
            let sort = spec_sort(variable.sort).ok_or_else(|| {
                TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
                    obligation_id: obligation.obligation_id.clone(),
                    reason: "array and float sorts are outside the trust_vc direct scalar adapter fragment"
                        .to_string(),
                }
            })?;
            record_variable_sort(&mut variables, variable.name.clone(), sort)?;
        }
    }
    let mut result_sort = None;
    let mut old_values = BTreeMap::new();
    ExprLowering {
        obligation_id: &obligation.obligation_id,
        variables: &mut variables,
        result_sort: &mut result_sort,
        old_values: &mut old_values,
    }
    .lower(&predicate.root)
}

fn trust_ir_obligation_kind(obligation: &TrustObligation) -> Option<TrustTrustIrObligationKind> {
    match &obligation.kind {
        ObligationKind::Precondition => Some(TrustTrustIrObligationKind::Requires),
        ObligationKind::Postcondition => Some(TrustTrustIrObligationKind::Ensures),
        ObligationKind::Custom { namespace, name }
            if namespace == "trust.vc" && name == "translation_validation" =>
        {
            Some(TrustTrustIrObligationKind::TranslationValidation)
        }
        ObligationKind::MemorySafety => Some(TrustTrustIrObligationKind::MemoryNoAlias),
        ObligationKind::BoundsCheck => Some(TrustTrustIrObligationKind::MemoryNoAlias),
        ObligationKind::Ownership => Some(TrustTrustIrObligationKind::BorrowProvenance),
        _ => None,
    }
}

fn public_kind_for_error(kind: TrustTrustIrObligationKind) -> ObligationKind {
    match kind {
        TrustTrustIrObligationKind::Requires => ObligationKind::Precondition,
        TrustTrustIrObligationKind::Ensures => ObligationKind::Postcondition,
        TrustTrustIrObligationKind::TranslationValidation => ObligationKind::Custom {
            namespace: "trust.vc".to_string(),
            name: "translation_validation".to_string(),
        },
        TrustTrustIrObligationKind::LoopInvariant => ObligationKind::LoopInvariant,
        TrustTrustIrObligationKind::MemoryNoAlias => ObligationKind::MemorySafety,
        TrustTrustIrObligationKind::BorrowProvenance => ObligationKind::Ownership,
        TrustTrustIrObligationKind::PanicFreedom => ObligationKind::ArithmeticSafety,
        TrustTrustIrObligationKind::TypeInvariant => ObligationKind::Invariant,
        _ => ObligationKind::Custom {
            namespace: "trust_vc.trust_ir".to_string(),
            name: "unknown".to_string(),
        },
    }
}

fn source_span(location: &SourceLocation) -> Option<TrustSourceSpan> {
    Some(TrustSourceSpan::new(
        location.file.as_ref()?.clone(),
        location.line?,
        location.column?,
        location.end_line.or(location.line)?,
        location.end_column.or(location.column)?,
    ))
}

fn spec_sort(sort: TrustSpecSort) -> Option<TrustSort> {
    match sort {
        TrustSpecSort::Bool => Some(TrustSort::Bool),
        TrustSpecSort::Int => Some(TrustSort::MathInt),
        TrustSpecSort::BitVec { width } => Some(TrustSort::BitVector { width, signed: false }),
        TrustSpecSort::Array { .. } => None,
        // Fail-closed: this adapter has no IEEE-754 sort, and mapping floats
        // onto any scalar TrustSort would give the terms wrong semantics.
        TrustSpecSort::Float { .. } => None,
    }
}

fn record_variable_sort(
    variables: &mut BTreeMap<String, TrustSort>,
    name: String,
    sort: TrustSort,
) -> Result<(), TrustVcTmirAdapterEmissionError> {
    if name == "result" {
        return Ok(());
    }
    match variables.insert(name.clone(), sort.clone()) {
        Some(existing) if existing != sort => Err(TrustVcTmirAdapterEmissionError::SortConflict {
            name,
            first: existing,
            second: sort,
        }),
        _ => Ok(()),
    }
}

fn record_optional_sort(
    name: &str,
    slot: &mut Option<TrustSort>,
    sort: TrustSort,
) -> Result<(), TrustVcTmirAdapterEmissionError> {
    match slot {
        Some(existing) if existing != &sort => Err(TrustVcTmirAdapterEmissionError::SortConflict {
            name: name.to_string(),
            first: existing.clone(),
            second: sort,
        }),
        Some(_) => Ok(()),
        None => {
            *slot = Some(sort);
            Ok(())
        }
    }
}

fn old_source_label(
    obligation_id: &str,
    expr: &TrustSpecExpr,
) -> Result<String, TrustVcTmirAdapterEmissionError> {
    match &expr.kind {
        TrustSpecExprKind::Variable { name } => Ok(name.clone()),
        TrustSpecExprKind::Result => Ok("result".to_string()),
        _ => Err(TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression {
            obligation_id: obligation_id.to_string(),
            reason: "old(...) emission currently supports local variables and result only"
                .to_string(),
        }),
    }
}

fn old_snapshot_name(source: &str) -> String {
    format!(
        "old_{}",
        source
            .chars()
            .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
            .collect::<String>()
    )
}

fn metadata_value<'a>(metadata: &'a [MetadataEntry], key: &str) -> Option<&'a str> {
    metadata.iter().find(|entry| entry.key == key).map(|entry| entry.value.as_str())
}

fn predicate_digest(predicate: &TrustSpecPredicate) -> String {
    let payload = serde_json::to_vec(predicate).expect("TrustSpecPredicate serializes");
    format!("sha256:{}", trust_types::stable_sha256_hex(&payload))
}

trait WithObligations {
    fn with_obligations(self, obligations: Vec<TrustTrustIrObligation>) -> Self;
}

impl WithObligations for TrustTrustIrProofUnit {
    fn with_obligations(mut self, obligations: Vec<TrustTrustIrObligation>) -> Self {
        for obligation in obligations {
            self = self.with_obligation(obligation);
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use trust_vc_trust_engine::{
        TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION, TrustOutcome, TrustProofEvidenceProfile,
        TrustVcTrustEngine,
    };
    use trust_verifier_api::{
        ContractKind, ContractPredicate, ProofStrength, TrustSpecBinaryOp, TrustSpecExpr,
        TrustSpecScalarSort, TrustSpecVariableOrigin,
    };

    use super::*;

    const TRUST_VC_CONTRACT_CFG_GOLDEN: &str = include_str!(
        "../fixtures/trust_ir_adapter/trust_increment_contract_cfg_trust_ir_adapter_golden.json"
    );

    fn int_var(name: &str) -> TrustSpecExpr {
        TrustSpecExpr::variable(name, TrustSpecSort::Int)
    }

    fn bool_var(name: &str) -> TrustSpecExpr {
        TrustSpecExpr::variable(name, TrustSpecSort::Bool)
    }

    fn local_int(name: &str, index: usize) -> TrustSpecVariable {
        TrustSpecVariable {
            name: name.to_string(),
            sort: TrustSpecSort::Int,
            origin: TrustSpecVariableOrigin::Local { index },
        }
    }

    fn local_bool(name: &str, index: usize) -> TrustSpecVariable {
        TrustSpecVariable {
            name: name.to_string(),
            sort: TrustSpecSort::Bool,
            origin: TrustSpecVariableOrigin::Local { index },
        }
    }

    fn source(line: u32, column: u32, end_column: u32) -> SourceLocation {
        SourceLocation {
            file: Some("crates/trust-vc-bridge/fixtures/trust_vc_increment.rs".to_string()),
            line: Some(line),
            column: Some(column),
            end_line: Some(line),
            end_column: Some(end_column),
        }
    }

    fn typed_vc_metadata(predicate: &TrustSpecPredicate) -> Vec<MetadataEntry> {
        vec![
            MetadataEntry {
                key: "trust.vc.formula.schema".to_string(),
                value: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: "trust.vc.formula.payload".to_string(),
                value: serde_json::to_string(predicate).expect("predicate serializes"),
            },
        ]
    }

    fn typed_contract(
        contract_id: &str,
        kind: ContractKind,
        predicate: TrustSpecPredicate,
        source: SourceLocation,
    ) -> TrustContract {
        TrustContract {
            contract_id: contract_id.to_string(),
            kind,
            predicate: predicate.into_contract_predicate().expect("predicate serializes"),
            source,
            metadata: vec![MetadataEntry {
                key: "trust.contract.lowering".to_string(),
                value: "spec_expr".to_string(),
            }],
        }
    }

    fn obligation(
        obligation_id: &str,
        kind: ObligationKind,
        contract_id: Option<&str>,
        source: SourceLocation,
    ) -> TrustObligation {
        TrustObligation {
            obligation_id: obligation_id.to_string(),
            kind,
            contract_id: contract_id.map(str::to_string),
            proof_item_id: None,
            source,
            description: format!("prove {obligation_id}"),
            required_strength: Some(ProofStrength::deductive()),
            summary_facts: Vec::new(),
            metadata: Vec::new(),
        }
    }

    fn trust_vc_contract_cfg_bundle() -> TrustContractBundle {
        let requires = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Ge,
                int_var("x"),
                TrustSpecExpr::int_literal("0"),
            ),
            vec![local_int("x", 1)],
        );
        let ensures = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::And,
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Eq,
                    TrustSpecExpr::old(int_var("x")),
                    TrustSpecExpr::old(int_var("x")),
                ),
                TrustSpecExpr::binary(
                    TrustSpecBinaryOp::Eq,
                    TrustSpecExpr::result(TrustSpecSort::Int),
                    TrustSpecExpr::result(TrustSpecSort::Int),
                ),
            ),
            vec![local_int("x", 1)],
        );
        let cfg = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                bool_var("cfg_edge_entry_return"),
                bool_var("cfg_edge_entry_return"),
            ),
            vec![local_bool("cfg_edge_entry_return", 99)],
        );

        let mut cfg_obligation = obligation(
            "trust_ir.cfg.entry_to_return",
            ObligationKind::Custom {
                namespace: "trust.vc".to_string(),
                name: "translation_validation".to_string(),
            },
            None,
            SourceLocation {
                file: Some("trust_ir:trust_vc_fixture::increment_checked".to_string()),
                line: Some(1),
                column: Some(1),
                end_line: Some(1),
                end_column: Some(8),
            },
        );
        cfg_obligation.metadata = vec![
            MetadataEntry {
                key: "trust.vc.kind".to_string(),
                value: "translation_validation".to_string(),
            },
            MetadataEntry {
                key: "trust.trust_ir.cfg.edge".to_string(),
                value: "bb0->bb1".to_string(),
            },
            MetadataEntry {
                key: "trust.vc.formula.schema".to_string(),
                value: TRUST_SPEC_PREDICATE_SCHEMA_VERSION.to_string(),
            },
            MetadataEntry {
                key: "trust.vc.formula.payload".to_string(),
                value: serde_json::to_string(&cfg).expect("cfg predicate serializes"),
            },
        ];

        let mut bundle = TrustContractBundle::empty(
            "Trust::compiler::trust_vc_trust_ir_adapter::increment_old_result_cfg",
            BundleSubject::Function {
                crate_name: "trust_vc_fixture".to_string(),
                path: "trust_vc_fixture::increment_checked".to_string(),
            },
        );
        bundle.metadata = vec![
            MetadataEntry {
                key: "trust.fixture.path".to_string(),
                value: "crates/trust-vc-bridge/fixtures/trust_ir_adapter/trust_increment_contract_cfg_trust_ir_adapter_golden.json".to_string(),
            },
            MetadataEntry {
                key: "trust.issue.refs".to_string(),
                value: "#2789,#2790".to_string(),
            },
            MetadataEntry {
                key: "trust.vc.snapshot".to_string(),
                value: "e2832d239d80d0b600e6e259d44d5ff173b79fec".to_string(),
            },
        ];
        bundle.contracts = vec![
            typed_contract(
                "contract.requires.x_nonnegative",
                ContractKind::Requires,
                requires,
                source(3, 5, 21),
            ),
            typed_contract(
                "contract.ensures.old_result_reflexive",
                ContractKind::Ensures,
                ensures,
                source(4, 5, 29),
            ),
        ];
        bundle.obligations = vec![
            obligation(
                "requires.x_nonnegative",
                ObligationKind::Precondition,
                Some("contract.requires.x_nonnegative"),
                source(3, 5, 21),
            ),
            obligation(
                "ensures.old_result_reflexive",
                ObligationKind::Postcondition,
                Some("contract.ensures.old_result_reflexive"),
                source(4, 5, 29),
            ),
            cfg_obligation,
        ];
        bundle
    }

    #[test]
    fn emits_native_trust_vc_trust_ir_adapter_request_golden_from_compiler_bundle() {
        let bundle = trust_vc_contract_cfg_bundle();
        let request = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
            .expect("compiler bundle emits trust_vc adapter request");
        let generated = serde_json::to_value(&request).expect("request serializes");
        let golden: serde_json::Value =
            serde_json::from_str(TRUST_VC_CONTRACT_CFG_GOLDEN).expect("golden decodes");

        assert_eq!(
            generated,
            golden,
            "generated trust_vc adapter request:\n{}",
            serde_json::to_string_pretty(&generated).expect("generated JSON formats")
        );

        assert_eq!(request.schema_version(), TRUST_TRUST_IR_ADAPTER_SCHEMA_VERSION);
        let unit = &request.units()[0];
        let frame = unit.native_context().contract_frame().expect("contract frame emitted");
        assert_eq!(frame.return_value().expect("result binding").name(), "result");
        assert_eq!(frame.old_values()[0].source(), "x");
        assert_eq!(frame.old_values()[0].snapshot().name(), "old_x");
        assert_eq!(unit.obligations().len(), 3);

        let engine = TrustVcTrustEngine::new();
        engine
            .validate_trust_ir_adapter_request(&request)
            .expect("generated request matches trust_vc runner input contract");
        let report = engine
            .verify_trust_ir_adapter_request(&request)
            .expect("generated request verifies through trust_vc adapter");
        assert!(matches!(report.units()[0].outcome(), TrustOutcome::Verified));
        let evidence = report.units()[0].proof_evidence();
        assert_eq!(evidence[1].evidence_profile(), TrustProofEvidenceProfile::TypedContractFrame);
        assert_eq!(
            evidence[2].evidence_profile(),
            TrustProofEvidenceProfile::TypedTranslationValidation
        );
    }

    #[test]
    fn trust_vc_trust_ir_adapter_request_rejects_string_backed_contracts() {
        let mut bundle = trust_vc_contract_cfg_bundle();
        bundle.contracts[0].predicate = ContractPredicate::TrustExpr { text: "x >= 0".to_string() };

        let err = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
            .expect_err("string-backed contracts are not native trust_vc adapter evidence");

        assert!(matches!(
            err,
            TrustVcTmirAdapterEmissionError::UnsupportedContractPredicate { .. }
        ));
    }

    #[test]
    fn trust_vc_trust_ir_adapter_request_rejects_duplicate_typed_variables() {
        let mut bundle = trust_vc_contract_cfg_bundle();
        let cfg = bundle
            .obligations
            .iter_mut()
            .find(|obligation| obligation.obligation_id == "trust_ir.cfg.entry_to_return")
            .expect("CFG fixture obligation exists");
        let payload = cfg
            .metadata
            .iter_mut()
            .find(|entry| entry.key == "trust.vc.formula.payload")
            .expect("CFG fixture carries typed payload");
        let mut predicate: TrustSpecPredicate =
            serde_json::from_str(&payload.value).expect("fixture predicate parses");
        predicate.variables.push(predicate.variables[0].clone());
        payload.value = serde_json::to_string(&predicate).expect("mutated predicate serializes");

        let error = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
            .expect_err("duplicate typed declarations must fail closed");
        assert!(
            matches!(error, TrustVcTmirAdapterEmissionError::InvalidTypedPredicate { .. }),
            "unexpected error: {error}"
        );
        assert!(error.to_string().contains("duplicate variables"), "unexpected error: {error}");
    }

    #[test]
    fn memory_and_borrow_obligations_require_native_ownership_context() {
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(TrustSpecBinaryOp::Eq, bool_var("p"), bool_var("p")),
            vec![local_bool("p", 1)],
        );
        for (kind, obligation_id) in [
            (ObligationKind::MemorySafety, "memory.no_alias"),
            (ObligationKind::BoundsCheck, "bounds.check"),
            (ObligationKind::Ownership, "borrow.provenance"),
        ] {
            let mut native_obligation = obligation(obligation_id, kind, None, source(8, 5, 20));
            native_obligation.metadata = typed_vc_metadata(&predicate);
            let mut bundle = TrustContractBundle::empty(
                "Trust::compiler::trust_vc_trust_ir_adapter::memory_ownership",
                BundleSubject::Function {
                    crate_name: "demo".to_string(),
                    path: "demo::memory".to_string(),
                },
            );
            bundle.obligations = vec![native_obligation];

            let err = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
                .expect_err("context-free memory/ownership predicates are not proof evidence");

            assert!(matches!(
                err,
                TrustVcTmirAdapterEmissionError::MissingNativeOwnershipContext { .. }
            ));
            assert!(err.to_string().contains("requires typed ownership"));
        }
    }

    #[test]
    fn trust_vc_owned_memory_obligations_without_typed_predicate_fail_closed() {
        for (kind, obligation_id) in [
            (ObligationKind::MemorySafety, "memory.no_payload"),
            (ObligationKind::BoundsCheck, "bounds.no_payload"),
        ] {
            let mut bundle = TrustContractBundle::empty(
                "Trust::compiler::trust_vc_trust_ir_adapter::missing_memory_payload",
                BundleSubject::Function {
                    crate_name: "demo".to_string(),
                    path: "demo::memory".to_string(),
                },
            );
            bundle.obligations = vec![obligation(obligation_id, kind, None, source(8, 5, 20))];

            let err = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
                .expect_err("trust-vc-owned memory obligation must not be silently dropped");

            assert!(matches!(
                err,
                TrustVcTmirAdapterEmissionError::MissingTypedCfgPredicate { .. }
            ));
            assert!(err.to_string().contains(obligation_id));
        }
    }

    #[test]
    fn trust_vc_owned_bounds_check_in_mixed_bundle_must_not_disappear() {
        let mut bundle = trust_vc_contract_cfg_bundle();
        bundle.obligations.push(obligation(
            "bounds.no_payload",
            ObligationKind::BoundsCheck,
            None,
            source(8, 5, 20),
        ));

        let err = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
            .expect_err("trust-vc-owned bounds obligation must block mixed adapter emission");

        assert!(matches!(err, TrustVcTmirAdapterEmissionError::MissingTypedCfgPredicate { .. }));
        assert!(err.to_string().contains("bounds.no_payload"));
    }

    #[test]
    fn trust_vc_direct_scalar_adapter_rejects_public_array_select() {
        let array_sort = TrustSpecSort::Array { element: TrustSpecScalarSort::Int };
        let predicate = TrustSpecPredicate::new(
            TrustSpecExpr::binary(
                TrustSpecBinaryOp::Eq,
                TrustSpecExpr::index(
                    TrustSpecExpr::variable("xs", array_sort),
                    TrustSpecExpr::int_literal("0"),
                    TrustSpecSort::Int,
                ),
                TrustSpecExpr::int_literal("0"),
            ),
            vec![TrustSpecVariable {
                name: "xs".to_string(),
                sort: array_sort,
                origin: TrustSpecVariableOrigin::Local { index: 0 },
            }],
        );
        predicate.validate().expect("bounded public Select predicate validates");
        let contract_id = "contract.requires.array-select";
        let mut bundle = TrustContractBundle::empty(
            "Trust::compiler::trust_vc_trust_ir_adapter::array_select_rejected",
            BundleSubject::Function {
                crate_name: "demo".to_string(),
                path: "demo::array_select".to_string(),
            },
        );
        bundle.contracts =
            vec![typed_contract(contract_id, ContractKind::Requires, predicate, source(3, 5, 21))];
        bundle.obligations = vec![obligation(
            "requires.array-select",
            ObligationKind::Precondition,
            Some(contract_id),
            source(3, 5, 21),
        )];

        let error = trust_vc_trust_ir_adapter_request_from_bundle(&bundle)
            .expect_err("trust_vc direct scalar adapter must reject arrays");
        assert!(matches!(error, TrustVcTmirAdapterEmissionError::UnsupportedSpecExpression { .. }));
        assert!(error.to_string().contains("array sorts are outside"), "{error}");
    }
}
