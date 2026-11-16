//! Workload-only known refusal from the SAME retained native member owner.
//! A decoded status or io::ErrorKind cannot construct this observation.
use super::*;

impl MetadataMember {
    /// Revalidate actual host pin, the retained bound Refused frame, absence
    /// of Started/completion, and physical event/output EOF. This proves no
    /// executed target, successful output, accounting or permission to retry.
    /// Old metadata/resolver purposes retain their existing API/behavior.
    pub fn workload_refusal(&mut self, deadline: Instant) -> io::Result<Option<&StatusFrame>> {
        let result = observe(&self.streams, &self.request, self.refusal_finalized, || {
            self.pin.validate(deadline)
        });
        if result.is_err() {
            // A later failed recheck cannot be retried into a positive fact.
            self.refusal_finalized = false;
        }
        result
    }
}

fn observe<'a>(
    streams: &'a MetadataStreams,
    request: &NativeQueryRequest,
    finalized: bool,
    original_pin: impl FnOnce() -> io::Result<()>,
) -> io::Result<Option<&'a StatusFrame>> {
    require_workload_observer(request)?;
    if streams.failed {
        return Err(invalid("earlier protocol/capture failure vetoes workload refusal"));
    }
    if !finalized {
        return Ok(None);
    }
    let Some(frame) = streams.state.refused_frame.as_ref() else { return Ok(None) };
    let Status::Refused { reason } = &frame.status else {
        return Err(invalid("retained workload refusal has another status"));
    };
    if frame.root_attempt != request.member().binding.root_attempt
        || frame.member_attempt != request.member().member_attempt
        || streams.state.refused.as_ref() != Some(reason)
        || streams.state.started.is_some()
        || streams.state.completed.is_some()
        || streams.state.workload.is_some()
        || streams.state.paired.is_some()
        || streams.state.contained.is_some()
        || streams.state.linker_completed.is_some()
        || streams.state.accounting.is_some()
        || streams.output.observer_failed
    {
        return Err(invalid("workload refusal contradicts its original lifecycle/capture"));
    }
    if !streams.output.eof.iter().all(|eof| *eof) || !streams.events.at_eof()? {
        return Ok(None);
    }
    original_pin()?;
    Ok(Some(frame))
}

#[cfg(test)]
mod tests;
