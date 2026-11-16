//! Actual sequential-runtime consumer of the native comparison. A failed
//! comparison retains its observations and any unretired operation owner.
use super::comparison::{self, ComparedNode};
use super::context::NodeContext;
use crate::compiler::native_job::{NativeOperationGraph, NativeRetainedGraph};
use crate::util::CargoResult;
use anyhow::Context as _;
use trust_resource_controller::native_job::Kind;

pub(super) struct Attempt {
    comparison: Option<ComparedNode>,
    continuation: Option<NativeRetainedGraph>,
    operation: Option<NativeOperationGraph>,
    failure: Option<anyhow::Error>,
}
impl Attempt {
    pub(super) fn run(
        context: &NodeContext<'_>,
        continuation: Option<NativeRetainedGraph>,
    ) -> Self {
        let mut attempt = Self {
            comparison: None,
            continuation: None,
            operation: None,
            failure: None,
        };
        let result = (|| -> CargoResult<()> {
            let Kind::Compare {
                baseline,
                candidate,
                selection,
            } = &context.plan().nodes[context.node().0 as usize].kind
            else {
                anyhow::bail!("native comparison received another node role")
            };
            let original = continuation
                .context("native comparison lacks its actual original runtime/GNU continuation")?;
            attempt.operation = Some(original.resume_operation()?);
            // This call obtains its own actual SAME-bank preparation before
            // the first retained-input read. The returned owner is not a grade.
            attempt.comparison = Some(comparison::compare(
                context, baseline, candidate, selection,
            )?);
            let preparation = context.prepare()?;
            attempt
                .comparison
                .as_ref()
                .expect("comparison owner retained before validation")
                .require_complete(context, &preparation)?;
            Ok(())
        })();
        if let Err(error) = result {
            attempt.reporting_failed(error);
        }
        if let Some(operation) = attempt.operation.take() {
            match operation.try_suspend() {
                Ok(original) => attempt.continuation = Some(original),
                Err((error, original)) => {
                    attempt.operation = Some(original);
                    attempt.reporting_failed(error);
                }
            }
        }
        attempt
    }
    pub(super) fn reporting_failed(&mut self, error: anyhow::Error) {
        self.failure = Some(match self.failure.take() {
            Some(original) => error.context(format!("native comparison also failed: {original:#}")),
            None => error,
        });
    }
    pub(super) fn failure(&self) -> Option<String> {
        self.failure.as_ref().map(|error| format!("{error:#}"))
    }
    pub(super) fn retired(&self) -> bool {
        self.continuation.is_some() && self.operation.is_none()
    }
    pub(super) fn comparison(&self) -> Option<&ComparedNode> {
        self.comparison.as_ref()
    }
    pub(super) fn take_continuation(&mut self) -> Option<NativeRetainedGraph> {
        self.continuation.take()
    }
}
