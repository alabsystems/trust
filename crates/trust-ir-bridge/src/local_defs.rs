//! Bridge queries over the shared local-definition interpretation.
//!
//! `trust-types` owns the write-channel reducer, body walk and shared-cell
//! escape classification. The bridge and vcgen ask the same value question.

use trust_types::local_defs::{self, LocalDefinitionSummary};
use trust_types::{Rvalue, Terminator, ValueCount, VerifiableFunction};

pub(crate) fn is_parameter_of(arg_count: usize, local: usize) -> bool {
    local_defs::is_parameter(arg_count, local)
}

pub(crate) fn summarize(
    func: &VerifiableFunction,
    local: usize,
) -> LocalDefinitionSummary<'_, usize> {
    let mut summary = LocalDefinitionSummary::for_local(func.body.arg_count, local);
    local_defs::visit_local_writes(
        &func.body,
        local,
        |statement| local_defs::statement_escapes_local(&func.body, statement, local),
        |block, _, write| summary.observe(block, write),
    );
    summary
}

pub(crate) fn value_count(func: &VerifiableFunction, local: usize) -> ValueCount {
    summarize(func, local).value_count()
}

pub(crate) fn holds_one_value(func: &VerifiableFunction, local: usize) -> bool {
    value_count(func, local).is_exactly(1)
}

pub(crate) fn has_one_stable_value(func: &VerifiableFunction, local: usize) -> bool {
    summarize(func, local).has_one_stable_value()
}

pub(crate) fn has_at_most_one_stable_value(func: &VerifiableFunction, local: usize) -> bool {
    summarize(func, local).has_at_most_one_stable_value()
}

/// Only a sole whole-value assignment may be inlined. Parameter entry values,
/// partial writes, aliases and unlocatable writes all prevent this answer.
pub(crate) fn unique_value_def(func: &VerifiableFunction, local: usize) -> Option<&Rvalue> {
    summarize(func, local).unique_value_def().map(|(_, value)| value)
}

/// A sole opaque write must still be an actual Call, not a TailCall.
pub(crate) fn unique_value_call(func: &VerifiableFunction, local: usize) -> Option<&Terminator> {
    let block = summarize(func, local).unique_value_call_index(&func.body)?;
    Some(&func.body.blocks[block].terminator)
}
