//! Shared interpretation of the existing local-write channels.
//!
//! The count includes a parameter's entry value and located whole writes. Partial
//! writes and escapes do not add a located value; an unlocatable write makes the
//! count inexact. A unique-value answer is stricter: partial writes, escapes and
//! unlocatable writes invalidate it. These are distinct questions, not interchangeable
//! licenses for a fact about a local's value.
//!
//! Callers retain their traversal/caching strategy. Shared-reference escapes
//! are classified from the same body/type model on both compiler paths.
//! This module supplies the same allocation-free decision logic to a full scan
//! and to an indexed scan, using `LocalWrite` rather than another intermediate IR.

use crate::{LocalWrite, Rvalue, Statement, Terminator, ValueCount, VerifiableBody};

/// The return slot is not a parameter; locals `1..=arg_count` have an entry value.
#[inline]
pub const fn is_parameter(arg_count: usize, local: usize) -> bool {
    local >= 1 && local <= arg_count
}

/// Whether an alias can invalidate this local's unique value. Shared borrows
/// qualify only for own storage covering interior-mutable bytes.
pub fn statement_escapes_local(body: &VerifiableBody, statement: &Statement, local: usize) -> bool {
    statement.escapes_local(local)
        || crate::interior_mutability::shared_borrow_of_local_covers_cell(body, statement, local)
}

/// The SLOT rule's escape classifier ([`source_slot_is_stable`]): a write-capable alias
/// of storage rooted at the local (`&mut`, `&raw` of any place under it), and NOT a
/// shared borrow of its `UnsafeCell` bytes. That omission is the slot rule's contract,
/// not an oversight: a caller claiming a value is frozen screens the precise shared-cell
/// places itself (or holds a compiler `Freeze` license and says so), which keeps a
/// frozen sibling field usable. [`statement_escapes_local`] is the cell-aware twin. An
/// indexed re-implementation of the slot rule asks this, by name, so the classifier is
/// stated once. Trust: 2026-11-07 (VCGEN-CENSUS-SITE-REDS-1).
#[inline]
pub fn statement_escapes_local_slot(statement: &Statement, local: usize) -> bool {
    statement.escapes_local(local)
}

/// The narrower storage question: can an alias change what this local holds?
/// Borrowing through a pointer reaches its pointee, not the pointer slot.
/// Callers may use this only for a query whose proof obligation excludes pointee
/// mutation (for example, whether the pointer itself can be reseated).
pub fn statement_escapes_local_storage(
    body: &VerifiableBody,
    statement: &Statement,
    local: usize,
) -> bool {
    statement.escapes_local_storage(local)
        || crate::interior_mutability::shared_borrow_of_local_covers_cell(body, statement, local)
}

/// Visit all explicit writes in body order, with their source locations.
///
/// `None` is the terminator; `Some(i)` is statement `i`. The caller's escape
/// classifier runs in addition to the model-owned local-write classifier, so an
/// alias is reported even when the statement does not itself replace the value.
pub fn visit_local_writes<'a>(
    body: &'a VerifiableBody,
    local: usize,
    mut escapes: impl FnMut(&Statement) -> bool,
    mut visit: impl FnMut(usize, Option<usize>, LocalWrite<'a>),
) {
    for (block_index, block) in body.blocks.iter().enumerate() {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            let write = statement.local_write(local);
            debug_assert!(
                write.agrees_with(statement.write_effect()),
                "statement channel classification disagrees with WriteEffect: {statement:?}"
            );
            visit(block_index, Some(statement_index), write);
            if escapes(statement) {
                visit(block_index, Some(statement_index), LocalWrite::Escape);
            }
        }
        let write = block.terminator.local_write(local);
        debug_assert!(
            write.agrees_with(block.terminator.write_effect()),
            "terminator channel classification disagrees with WriteEffect: {:?}",
            block.terminator
        );
        visit(block_index, None, write);
    }
}

/// Stable storage reachable from a local, excluding only the shared-cell
/// channel. Callers claiming a value is frozen must also screen the precise
/// shared-cell places; this separate query keeps unaffected sibling fields usable.
pub fn source_slot_is_stable(body: &VerifiableBody, local: usize) -> bool {
    source_is_stable(body, local, false, false)
}

/// [`source_slot_is_stable`] with ONE narrowing: a terminator `Drop` of the WHOLE
/// local is the end of its value, not a write. Every other channel is judged exactly
/// as [`source_slot_is_stable`] judges it, over the same walk and the same cell-blind
/// escape classifier, so a caller must screen the shared-cell places as that query's
/// callers do (or hold a compiler `Freeze` license for the value, and say so).
///
/// Why the narrowing holds: `Drop(x)` ends `x`'s value and leaves `x` uninitialised;
/// MIR reads a dropped place only after a re-initialisation, which is a second whole
/// write this question still refuses. So every read the body can make of the local
/// while its value is live sees its one value. It is the wrong answer for a fact asked
/// about the bare name at an arbitrary point (a consumed value cannot license a later
/// fact), which is why [`source_slot_is_stable`] counts the drop. Trust: 2026-11-07
/// (VCGEN-CENSUS-SITE-REDS-1): stated here, beside the rule it narrows, rather than
/// restated in a verifier crate.
pub fn source_slot_is_stable_modulo_whole_drops(body: &VerifiableBody, local: usize) -> bool {
    source_is_stable(body, local, false, true)
}

/// Stable storage reachable from a local, including shared interior-mutability
/// channels. Unlike a whole-pointer-value query, a store through that pointer
/// invalidates this answer even though it does not reseat the pointer.
pub fn source_value_is_stable(body: &VerifiableBody, local: usize) -> bool {
    source_is_stable(body, local, true, false)
}

/// [`source_value_is_stable`] (the cell-aware escape classifier,
/// [`statement_escapes_local`]) with the whole-drop narrowing of
/// [`source_slot_is_stable_modulo_whole_drops`], for a caller that matches only places
/// the body reads while the local's value is live.
pub fn source_value_is_stable_modulo_whole_drops(body: &VerifiableBody, local: usize) -> bool {
    source_is_stable(body, local, true, true)
}

fn source_is_stable(
    body: &VerifiableBody,
    local: usize,
    include_shared_cells: bool,
    whole_drop_ends_value: bool,
) -> bool {
    let mut summary = LocalDefinitionSummary::for_local(body.arg_count, local);
    let mut projected_store = false;
    visit_local_writes(
        body,
        local,
        |statement| {
            if include_shared_cells {
                statement_escapes_local(body, statement, local)
            } else {
                statement_escapes_local_slot(statement, local)
            }
        },
        |block, statement, write| {
            if whole_drop_ends_value
                && statement.is_none()
                && matches!(&body.blocks[block].terminator, Terminator::Drop { place, .. }
                    if place.local == local && place.projections.is_empty())
            {
                return;
            }
            summary.observe((), write);
            // LocalWrite describes the local's own value. This stronger query
            // also tracks writes through a pointer rooted there. Ordinary partial
            // writes, deinit/drop and unlocatable channels are handled above.
            projected_store |= match statement {
                Some(index) => matches!(&body.blocks[block].stmts[index],
                    Statement::Assign { place, .. }
                    if place.local == local && !place.projections.is_empty()),
                None => matches!(&body.blocks[block].terminator,
                    Terminator::Call { dest, .. }
                    if dest.local == local && !dest.projections.is_empty()),
            };
        },
    );
    !projected_store && summary.has_at_most_one_stable_value()
}

/// Counts located values and tracks a sole whole-value definition.
///
/// `Location` is retained unchanged for callers that cache a statement or need
/// the producing call's block. It has no role in deciding uniqueness. An escaped
/// initializer is deliberately not a unique value: a later store through that
/// alias can make the initializer historical. Origin-only queries have a
/// different contract and do not use this summary.
pub struct LocalDefinitionSummary<'a, Location> {
    count: ValueCount,
    sole: Option<(Location, LocalWrite<'a>)>,
    ambiguous: bool,
}

impl<'a, Location: Copy> LocalDefinitionSummary<'a, Location> {
    #[inline]
    pub fn for_local(arg_count: usize, local: usize) -> Self {
        let parameter = is_parameter(arg_count, local);
        Self { count: ValueCount::ZERO.plus(usize::from(parameter)), sole: None, ambiguous: false }
    }

    /// Add one already-classified channel. A new channel must define both its
    /// counting and unique-value behavior here, through this exhaustive match.
    #[inline]
    pub fn observe(&mut self, location: Location, write: LocalWrite<'a>) {
        match write {
            LocalWrite::Untouched => {}
            LocalWrite::WholeNamed(_) | LocalWrite::WholeOpaque => {
                self.count = self.count.plus(1);
                if self.sole.is_some() {
                    self.ambiguous = true;
                } else {
                    self.sole = Some((location, write));
                }
            }
            LocalWrite::Partial | LocalWrite::Escape => self.ambiguous = true,
            LocalWrite::Unlocatable => {
                self.count = self.count.plus_unlocatable();
                self.ambiguous = true;
            }
        }
    }

    #[inline]
    pub fn value_count(&self) -> ValueCount {
        self.count
    }

    /// One complete value and no partial, escaped or unlocatable write. A
    /// parameter's entry value counts; a parameter followed by a store has two.
    #[inline]
    pub fn has_one_stable_value(&self) -> bool {
        !self.ambiguous && self.count.is_exactly(1)
    }

    /// The same stability condition allowing zero definitions. This is the
    /// at-most-one question, not permission to read an uninitialized local.
    #[inline]
    pub fn has_at_most_one_stable_value(&self) -> bool {
        !self.ambiguous && self.count.is_at_most(1)
    }

    #[inline]
    pub fn unique_value_def(&self) -> Option<(Location, &'a Rvalue)> {
        if self.ambiguous || !self.count.is_exactly(1) {
            return None;
        }
        match self.sole {
            Some((location, LocalWrite::WholeNamed(value))) => Some((location, value)),
            _ => None,
        }
    }

    /// A sole opaque whole write. The caller must still check that its actual
    /// terminator is a `Call`: a `TailCall` has no returnable destination.
    #[inline]
    pub fn unique_opaque_write(&self) -> Option<Location> {
        if self.ambiguous || !self.count.is_exactly(1) {
            return None;
        }
        match self.sole {
            Some((location, LocalWrite::WholeOpaque)) => Some(location),
            _ => None,
        }
    }
}

impl LocalDefinitionSummary<'_, usize> {
    /// Resolve the sole opaque whole write to an actual call block. Tail calls
    /// contribute a value but have no destination-producing call to return.
    #[inline]
    pub fn unique_value_call_index(&self, body: &VerifiableBody) -> Option<usize> {
        let index = self.unique_opaque_write()?;
        matches!(body.blocks.get(index)?.terminator, Terminator::Call { .. }).then_some(index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConstValue, Operand};

    fn value() -> Rvalue {
        Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))
    }

    #[test]
    fn entry_and_historical_writes_are_distinct_values() {
        let value = value();
        let mut parameter = LocalDefinitionSummary::for_local(1, 1);
        assert!(parameter.has_one_stable_value());
        assert!(parameter.unique_value_def().is_none());
        parameter.observe(0, LocalWrite::WholeNamed(&value));
        assert!(parameter.value_count().is_exactly(2));
        assert!(!parameter.has_at_most_one_stable_value());
        assert!(parameter.unique_value_def().is_none());
        let mut local = LocalDefinitionSummary::for_local(1, 2);
        local.observe(0, LocalWrite::WholeNamed(&value));
        assert_eq!(local.unique_value_def().map(|(at, _)| at), Some(0));
        local.observe(1, LocalWrite::WholeNamed(&value));
        assert!(local.value_count().is_exactly(2));
        assert!(local.unique_value_def().is_none());
    }

    #[test]
    fn non_value_channels_cannot_license_a_unique_value() {
        let value = value();
        for invalidation in [LocalWrite::Partial, LocalWrite::Escape, LocalWrite::Unlocatable] {
            let mut summary = LocalDefinitionSummary::for_local(0, 1);
            summary.observe(0, LocalWrite::WholeNamed(&value));
            summary.observe(1, invalidation);
            assert!(summary.unique_value_def().is_none());
            assert!(summary.unique_opaque_write().is_none());
            assert_eq!(
                summary.value_count().is_exactly(1),
                !matches!(invalidation, LocalWrite::Unlocatable)
            );
        }
    }

    #[test]
    fn named_and_opaque_definitions_do_not_substitute_for_each_other() {
        let value = value();
        let mut summary = LocalDefinitionSummary::for_local(0, 1);
        summary.observe(7, LocalWrite::WholeOpaque);
        assert_eq!(summary.unique_opaque_write(), Some(7));
        assert!(summary.unique_value_def().is_none());
        summary.observe(8, LocalWrite::WholeNamed(&value));
        assert!(summary.unique_value_def().is_none());
        assert!(summary.unique_opaque_write().is_none());
    }
}
