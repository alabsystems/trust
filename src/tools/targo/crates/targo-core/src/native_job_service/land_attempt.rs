//! Retain the genuine repository/source preparation on an actual Land node.
//! Prepared input custody never stands in for admitted Agh/Git publication.
use super::comparison::{self, PreparedLand};
use super::context::NodeContext;
use crate::compiler::native_job::{NativeOperationGraph, NativeRetainedGraph};
use crate::util::CargoResult;
use anyhow::Context as _;
use trust_resource_controller::native_job::Kind;

pub(super) struct Attempt {
    prepared: Option<PreparedLand>,
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
            prepared: None,
            continuation: None,
            operation: None,
            failure: None,
        };
        let result = (|| -> CargoResult<()> {
            let Kind::Land {
                source,
                comparison,
                selection,
            } = &context.plan().nodes[context.node().0 as usize].kind
            else {
                anyhow::bail!("native Land received another node role")
            };
            let original =
                continuation.context("native Land lacks its actual runtime/GNU continuation")?;
            attempt.operation = Some(original.resume_operation()?);
            attempt.prepared = Some(comparison::prepare_land(
                context,
                *source,
                *comparison,
                selection,
            )?);
            let preparation = context.prepare()?;
            attempt
                .prepared
                .as_ref()
                .expect("native Land preparation retained before qualification")
                .require_publication(context, &preparation)?;
            anyhow::bail!(
                "native Land still requires the actual admitted Agh and separate Git execution owners"
            )
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
            Some(original) => error.context(format!("native Land also failed: {original:#}")),
            None => error,
        });
    }
    pub(super) fn failure(&self) -> String {
        self.failure
            .as_ref()
            .map(|error| format!("{error:#}"))
            .unwrap_or_else(|| "native Land has no actual publication owner".into())
    }
    pub(super) fn retired(&self) -> bool {
        self.continuation.is_some() && self.operation.is_none()
    }
    pub(super) fn take_continuation(&mut self) -> Option<NativeRetainedGraph> {
        self.continuation.take()
    }
}
