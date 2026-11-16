//! Rows a corpus file states about itself, in `//@ <name>: <value>` lines.
//!
//! The open-dispatch ladder (`tests/open-dispatch-ladder/`) keeps each row's
//! disposition in the file it is about, so a row and its program cannot part.
//! A table group names the dialect its files are written in (`headers`), and
//! this module reads it:
//!
//! | header | `trust-ladder` | `trust-ladder-xcrate` |
//! |---|---|---|
//! | the pin | `trust-ladder` | `trust-ladder-xcrate` |
//! | a text the output must hold | `trust-ladder-row` | `trust-ladder-row` |
//! | `trust-ladder-crate-type` | `bin`; a library without it | `lib`; a binary without it |
//! | the dependency | none | `trust-ladder-xcrate-dep`, `libt` without it |
//! | a dependency to re-derive | none | `trust-ladder-xcrate-declare` |
//!
//! A library is compiled with `--crate-type=lib`, a binary with no crate type.
//! `trust-ladder-xcrate-declare: <crate>` adds
//! `-Ztrust-bundle-foreign-crate=<crate>` after the dependency's arguments. A
//! dependency's own file may carry `trust-ladder-dep-flags`, a
//! space-separated list added to the group's `dependency_args`.
//!
//! A header is a line that starts with `//@ <name>:`; its value is the rest of
//! the line after any spaces. The first line of a name is the one that counts,
//! and one with no value says nothing, as `scripts/open_dispatch_ladder.sh`
//! reads them.

use serde::Deserialize;

use super::Pin;

/// A header dialect a table group may name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
pub(crate) enum Dialect {
    /// One file is one row.
    #[serde(rename = "trust-ladder")]
    Ladder,
    /// A row built against a dependency crate.
    #[serde(rename = "trust-ladder-xcrate")]
    LadderXcrate,
}

impl Dialect {
    /// The header that carries the row's pin.
    pub(crate) fn pin_header(self) -> &'static str {
        match self {
            Self::Ladder => "trust-ladder",
            Self::LadderXcrate => "trust-ladder-xcrate",
        }
    }
}

const ROW: &str = "trust-ladder-row";
const CRATE_TYPE: &str = "trust-ladder-crate-type";
const DEPENDENCY: &str = "trust-ladder-xcrate-dep";
const DECLARE: &str = "trust-ladder-xcrate-declare";
const DEPENDENCY_FLAGS: &str = "trust-ladder-dep-flags";

/// The dependency of a cross-crate row that names none.
const DEFAULT_DEPENDENCY: &str = "libt";

/// What one file says of its own row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) pin: Pin,
    /// A text the compile's output must hold for the row to be as pinned.
    pub(crate) log_contains: Option<String>,
    /// The arguments the headers add after the group's.
    pub(crate) args: Vec<String>,
    /// The crate the row is built against, and the arguments that follow the
    /// dependency's own (`--extern`, `-L`).
    pub(crate) dependency: Option<(String, Vec<String>)>,
}

/// The value of the first `//@ <name>:` line of `text`; `None` when there is
/// no such line or it has no value.
fn header<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    text.split('\n')
        .find_map(|line| line.strip_prefix("//@ ")?.strip_prefix(name)?.strip_prefix(':'))
        .map(|value| value.trim_start_matches(' '))
        .filter(|value| !value.is_empty())
}

/// The row `text` (a corpus file's contents) states in `dialect`.
pub(crate) fn row(dialect: Dialect, text: &str) -> Result<Row, String> {
    let pin_header = dialect.pin_header();
    let pin = match header(text, pin_header) {
        Some("verifies") => Pin::Verifies,
        Some("refuses") => Pin::Refuses,
        Some("conditional") => Pin::Conditional,
        Some(other) => {
            return Err(format!(
                "`//@ {pin_header}: {other}` is not `verifies`, `refuses` or `conditional`"
            ));
        }
        None => return Err(format!("it has no `//@ {pin_header}:` line, so it states no row")),
    };
    let library = match (header(text, CRATE_TYPE), dialect) {
        (Some("lib"), _) | (None, Dialect::Ladder) => true,
        (Some("bin"), _) | (None, Dialect::LadderXcrate) => false,
        (Some(other), _) => {
            return Err(format!("`//@ {CRATE_TYPE}: {other}` is neither `bin` nor `lib`"));
        }
    };
    let args = if library { vec!["--crate-type=lib".to_owned()] } else { Vec::new() };
    let dependency = match dialect {
        Dialect::Ladder => {
            for name in [DEPENDENCY, DECLARE] {
                if header(text, name).is_some() {
                    return Err(format!(
                        "`//@ {name}:` belongs to a `{}` row, and this is a `{pin_header}` row",
                        Dialect::LadderXcrate.pin_header()
                    ));
                }
            }
            None
        }
        Dialect::LadderXcrate => {
            let name = header(text, DEPENDENCY).unwrap_or(DEFAULT_DEPENDENCY).to_owned();
            let declared = header(text, DECLARE)
                .map(|declared| format!("-Ztrust-bundle-foreign-crate={declared}"));
            Some((name, declared.into_iter().collect()))
        }
    };
    Ok(Row { pin, log_contains: header(text, ROW).map(str::to_owned), args, dependency })
}

/// The arguments a dependency's own file adds to its build.
pub(crate) fn dependency_flags(text: &str) -> Vec<String> {
    header(text, DEPENDENCY_FLAGS)
        .map(|flags| flags.split_whitespace().map(str::to_owned).collect())
        .unwrap_or_default()
}
