//! Original diagnostic visibility while output waits for final publication.
//! This monotonic session ledger records ONLY errors the original publisher
//! prepared. It is not a verdict, proof, row grade or late selection result.

use super::*;

#[derive(Default)]
struct PlannedOriginalErrors {
    count: u64,
    poisoned: bool,
}

/// Captured at the original publisher entry, before any source/private helper
/// can demand another body. Never compare this old global DCX count at late
/// emission: only the eager original semantic effects consume this baseline.
#[derive(Clone, Copy)]
pub(in crate::trust_verify) struct OriginalErrorBaseline {
    actual: usize,
    planned: Option<u64>,
}

impl PlannedOriginalErrors {
    fn record(&mut self) {
        match self.count.checked_add(1) {
            Some(count) => self.count = count,
            None => self.poisoned = true,
        }
    }

    fn unchanged(&self, original: u64) -> bool {
        !self.poisoned && self.count == original
    }
}

pub(in crate::trust_verify) fn baseline(tcx: TyCtxt<'_>) -> OriginalErrorBaseline {
    let actual = tcx.dcx().err_count();
    // The ordinary pin-off path acquires no pending reporting cell.
    let planned = trust_certify::calculus_row::base::has_production_pin().then(|| {
        tcx.sess.with_trust_compiler_state::<PlannedOriginalErrors, _>(|state| state.count)
    });
    OriginalErrorBaseline { actual, planned }
}

pub(in crate::trust_verify) fn unchanged(
    tcx: TyCtxt<'_>,
    baseline: &OriginalErrorBaseline,
) -> bool {
    tcx.dcx().err_count() == baseline.actual
        && baseline.planned.is_none_or(|original| {
            tcx.sess.with_trust_compiler_state::<PlannedOriginalErrors, _>(|state| {
                state.unchanged(original)
            })
        })
}

/// Called once when a compact sink receives an ORIGINAL aborting diagnostic,
/// at the point the immediate publisher would have emitted it. Do not call
/// this for a hypothetical checked plan or a final re-emission. Keeping the
/// count monotonic avoids treating a later selected report as an eager fact.
pub(super) fn record_original_abort(sess: &Session) {
    sess.with_trust_compiler_state::<PlannedOriginalErrors, _>(PlannedOriginalErrors::record);
}

#[cfg(test)]
mod tests;
