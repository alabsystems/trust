//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//! **I8 negative — Clean syntax error inside the `.clean` file.**
//! The unit is loaded as a REAL `SourceFile` and parsed by the real Clean
//! parser at load time, so the diagnostic's primary span must land inside
//! `clean_unit_syntax_error_helper.clean` at the offending line/column — the
//! entire point of giving the unit its own `SourceFile` — with the v7/D3
//! note (syntax error, not a failed proof) and options (fix the syntax; or
//! inline the declarations as `clean { … }`).
//!
//! The error is in a non-`.rs` file, so this test matches on
//! `error-pattern` rather than a tilde annotation; the `.stderr` blessed on
//! first run must show the `--> …clean_unit_syntax_error_helper.clean:…`
//! span to count as green.

clean mod clean_unit_syntax_error_helper;

fn main() {}
//~? ERROR Clean unit `clean_unit_syntax_error_helper.clean` failed to parse
