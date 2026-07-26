//! TrustIr layout-sensitive cast evidence adapters.
//!
//! These helpers consume TrustIr's typed layout evidence surface and provide a
//! stable fail-closed bridge for Trust proof/report gates.

use trust_ir::Module;
use trust_ir::inst::Inst;

use crate::lower::BridgeError;

/// TrustIr commit that introduced typed layout evidence for MIR casts.
pub const TRUST_IR_LAYOUT_EVIDENCE_COMMIT: &str = "44a43e8a7ffe7c476ea83ec21352e098daf2dda3";
/// Target-validation stage used when typed layout evidence is missing.
pub const TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_STAGE: &str = "trust-ir-bridge::target-validation";
/// Target-validation feature used when typed layout evidence is missing.
pub const TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE: &str =
    "trust_ir-layout-sensitive-cast-evidence-missing";

/// One layout-sensitive TrustIr cast that lacks typed layout evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustIrLayoutSensitiveCastBlocker {
    pub function: String,
    pub block: usize,
    pub statement_index: usize,
    pub op: String,
    pub src: String,
    pub dst: String,
    pub reason: String,
}

impl TrustIrLayoutSensitiveCastBlocker {
    #[must_use]
    pub fn reason_summary(&self) -> String {
        format!(
            "layout-sensitive TrustIr cast {} from {} to {} lacks typed layout evidence: {}",
            self.op, self.src, self.dst, self.reason
        )
    }

    #[must_use]
    pub fn diagnostics(&self) -> Vec<String> {
        vec![
            format!("blocker-code={TRUST_IR_LAYOUT_EVIDENCE_BLOCKER_FEATURE}"),
            format!("trust_ir-layout-evidence-commit={TRUST_IR_LAYOUT_EVIDENCE_COMMIT}"),
            format!("function={}", self.function),
            format!("block={}", self.block),
            format!("statement_index={}", self.statement_index),
            format!("cast_op={}", self.op),
            format!("src_ty={}", self.src),
            format!("dst_ty={}", self.dst),
            format!("layout-evidence-error={}", self.reason),
            "required-evidence=typed-layout-cast-evidence".to_string(),
            "fail-closed=true".to_string(),
            "proof-grade=false".to_string(),
        ]
    }
}

/// Collect layout-sensitive casts rejected by TrustIr typed layout evidence.
#[must_use]
pub fn collect_layout_sensitive_cast_blockers(
    module: &Module,
) -> Vec<TrustIrLayoutSensitiveCastBlocker> {
    let mut blockers = Vec::new();

    for function in &module.functions {
        for block in &function.blocks {
            for (statement_index, node) in block.body.iter().enumerate() {
                let Inst::Cast { op, src_ty, dst_ty, .. } = &node.inst else {
                    continue;
                };
                if !op.is_layout_sensitive() {
                    continue;
                }
                if let Err(reason) = module.layout_sensitive_cast_evidence(*op, src_ty, dst_ty) {
                    blockers.push(TrustIrLayoutSensitiveCastBlocker {
                        function: function.name.clone(),
                        block: block.id.as_usize(),
                        statement_index,
                        op: op.to_string(),
                        src: src_ty.to_string(),
                        dst: dst_ty.to_string(),
                        reason: reason.to_string(),
                    });
                }
            }
        }
    }

    blockers
}

/// Reject a TrustIr module when any layout-sensitive cast lacks typed evidence.
pub fn ensure_layout_sensitive_cast_evidence(module: &Module) -> Result<(), BridgeError> {
    let blockers = collect_layout_sensitive_cast_blockers(module);
    if blockers.is_empty() {
        return Ok(());
    }

    let details = blockers
        .iter()
        .map(TrustIrLayoutSensitiveCastBlocker::reason_summary)
        .collect::<Vec<_>>()
        .join("; ");
    Err(BridgeError::UnsupportedOp(format!(
        "typed layout evidence from TrustIr {TRUST_IR_LAYOUT_EVIDENCE_COMMIT} is required before layout-sensitive casts can contribute to proof-grade acceptance: {details}"
    )))
}
