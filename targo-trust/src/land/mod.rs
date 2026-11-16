//! `targo trust land --check`: the validation rows of the landing gate's row
//! table, selected by a change and run (docs/PLAN.md PKG-LIVE-4;
//! docs/design/2026-11-12-live-edit-loop.md step 4 and section 5).
//!
//! The table is `gates/land.toml` ([`table`]). The verb reads it as
//! `scripts/lib/land_select.py` reads it, selects the rows a change selects as
//! `land_select.validation_test_modules` selects them ([`select`]), runs each
//! selected row's command ([`run`]) and prints one verdict per row ([`cli`]).
//!
//! This is the validation rows only, and it is not the landing gate. The
//! Python gate (`scripts/land_gate.py`) still selects and runs the validation
//! leg itself, and no gate calls this verb. The landing, `targo trust land`
//! without `--check`, is not implemented here. Two readers of one table stay
//! until the Python reader is deleted;
//! `targo-trust/tests/fixtures/land_select_cases.json` is asserted by this
//! module's tests and by `scripts/tests/land_gate_test.py`, and is what holds
//! the two to the same answers.
//!
//! A verdict here is a command's exit status. It is a gate input, never a
//! proof, and it grants nothing by itself.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

mod cli;
mod run;
mod select;
mod table;

#[cfg(test)]
mod tests;

pub(crate) use cli::{USAGE_LINE, run_subcommand};

/// The verb, after `targo trust`: `main.rs` dispatches on it.
pub(crate) const SUBCOMMAND: &str = "land";

/// A selected row FAILed.
pub(crate) const EXIT_FAIL: u8 = 1;
/// A usage error, a table that does not load, or a tree that breaks the
/// table's `covered` rule.
pub(crate) const EXIT_USAGE: u8 = 2;
/// COULD NOT RUN: the change could not be read, or a selected row was not
/// judged.
pub(crate) const EXIT_COULD_NOT_RUN: u8 = 3;
