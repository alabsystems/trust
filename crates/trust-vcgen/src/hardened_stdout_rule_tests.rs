// Tests for the hardened `stdout` rule's exact-callee exclusions
// (`hardened::CALL_RULE_EXACT_CALLEE_EXCLUSIONS`, `hardened::call_rule_matches`):
// `std::process::Command::stdout::<S>` for std's own writeless `Into<Stdio>`
// sources `S` is not a `process_semantics` boundary, every real writer keeps its
// row (a dependency's conversion run inside `Command::stdout::<dep::X>`
// included), and no other decision of the rule table moves.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::tests::{call_block, return_block, test_function};
use super::*;

/// Trust (2026-10-25, hardened `stdout` false match). The `stdout` needle
/// compares identifier tokens, so it minted a `process_semantics` mandate on
/// `std::process::Command::stdout`, which wires a CHILD's stdout
/// (claude-code-alab: two of its three rows). The callee spellings are the ones
/// the compiler renders, measured on Trust 15698 (`hardened boundary
/// (process_semantics): <callee>`) and in the ui fixtures
/// `hardened_command_stdio_not_process_semantics.rs` and
/// `hardened_command_stdio_dep_conversion_keeps_row.rs`.
fn process_semantics_rows(callee: &str) -> usize {
    let func = test_function(vec![call_block(0, callee), return_block(1)]);
    generate_hardened_vcs_for_profile(&func)
        .iter()
        .filter(|vc| {
            matches!(
                &vc.kind,
                VcKind::HardenedBoundary { category: HardenedVcCategory::ProcessSemantics, .. }
            )
        })
        .count()
}

/// Every rendered `Command::stdout::<S>` the exclusion list names, measured.
const EXCLUDED_COMMAND_STDOUT: [&str; 10] = [
    "std::process::Command::stdout::<std::process::Stdio>",
    "std::process::Command::stdout::<std::fs::File>",
    "std::process::Command::stdout::<std::io::stdio::Stdout>",
    "std::process::Command::stdout::<std::io::stdio::Stderr>",
    "std::process::Command::stdout::<std::process::ChildStdin>",
    "std::process::Command::stdout::<std::process::ChildStdout>",
    "std::process::Command::stdout::<std::process::ChildStderr>",
    "std::process::Command::stdout::<std::os::fd::owned::OwnedFd>",
    "std::process::Command::stdout::<std::io::pipe::PipeReader>",
    "std::process::Command::stdout::<std::io::pipe::PipeWriter>",
];

#[test]
fn command_stdio_configuration_is_not_a_process_semantics_boundary() {
    // NEGATIVE: the child-stdio configurer fed one of std's own writeless
    // `Into<Stdio>` sources, by its exact rendered callee.
    for callee in EXCLUDED_COMMAND_STDOUT {
        assert_eq!(process_semantics_rows(callee), 0, "{callee}");
    }
    // never matched (no needle) and still not
    for callee in [
        "std::process::Command::stderr::<std::process::Stdio>",
        "std::process::Command::stdin::<std::process::Stdio>",
    ] {
        assert_eq!(process_semantics_rows(callee), 0, "{callee}");
    }
}

#[test]
fn a_conversion_the_call_runs_from_outside_std_keeps_the_mandate() {
    // Trust (2026-10-26, adversarial review of the first version, which
    // compared def-path segments with generic arguments STRIPPED and so
    // withheld every one of these rows). `Command::stdout<T: Into<Stdio>>` runs
    // `cfg.into()`: for `T` outside std's own sources that is a dependency's
    // `From`/`Into` impl, which may print. Measured on a verify-off dependency:
    // each of the first four writes fd 1 and panics on a closed pipe (exit 101).
    // Spellings as the compiler renders them (Trust 15698).
    for callee in [
        "std::process::Command::stdout::<fake::Loud>",
        "std::process::Command::stdout::<alloc::boxed::Box<fake::Loud>>",
        "std::process::Command::stdout::<&fake::Loud>",
        "std::process::Command::stdout::<fake::Direct>",
        // a caller's type parameter: any `Into<Stdio>` at all
        "std::process::Command::stdout::<T>",
        // the extractor's argument fingerprint hides the argument
        "std::process::Command::stdout::<__trust_args@1840eba8da696d9097e38d892c407cb3>",
        concat!(
            "std::process::Command::stdout::<std::process::Stdio>",
            "::<__trust_args@1840eba8da696d9097e38d892c407cb3>"
        ),
        // no argument rendered: the argument is unknown
        "std::process::Command::stdout",
        // a std type wrapping an outside type is not a std source
        "std::process::Command::stdout::<alloc::boxed::Box<std::process::Stdio>>",
    ] {
        assert_eq!(process_semantics_rows(callee), 1, "{callee}");
    }
}

#[test]
fn only_the_real_std_item_is_excluded() {
    // Trust (2026-10-26, adversarial review finding 2). The first version's
    // segment compare dropped every segment starting with `<`, so a qualified
    // prefix compared equal to the std path (measured: a fn-local
    // `mod process { struct Command; impl Command { fn stdout(..) } }` inside a
    // trait-impl method named `std` lost its call-site row). Whole-string
    // equality is anchored at the root; each of these keeps its row.
    for callee in [
        "<qpath_body::Foo as qpath_body::T>::std::process::Command::stdout",
        "<qpath_body::Foo as qpath_body::T>::std::process::Command::stdout::<std::process::Stdio>",
        // a crate impersonating `std` (`--extern std=` or `--crate-name std`),
        // rendered under the unauthenticated-crate stamp
        "__trust_crate@fc768d65f114d01a::std::process::Command::stdout::<std::process::Stdio>",
        "__trust_crate@1973d11b2baa21fa::std::process::Command::stdout::<std::process::Stdio>",
        // a path that merely contains the spelling, rooted elsewhere
        "depa::std::process::Command::stdout::<std::process::Stdio>",
        // `extern crate fake as std;` renders the real crate name
        "fake::process::Command::stdout",
        // the per-platform impls are not listed (never in a verified crate's
        // calls; if inlining ever exposed one, its conversion would be unseen)
        "std::sys::process::unix::common::Command::stdout",
        "std::sys::process::windows::Command::stdout",
        // surrounding whitespace is not normalized away
        " std::process::Command::stdout::<std::process::Stdio>",
        "std::process::Command::stdout::<std::process::Stdio> ",
    ] {
        assert_eq!(process_semantics_rows(callee), 1, "{callee}");
    }
}

#[test]
fn process_stdout_writers_keep_their_process_semantics_mandate() {
    // POSITIVE CONTROLS: this process's stdout acquisition and the print
    // backend, in the rendered (`stdio`) and re-exported spellings.
    for callee in
        ["std::io::stdio::stdout", "std::io::stdout", "std::io::stdio::_print", "std::io::_print"]
    {
        assert_eq!(process_semantics_rows(callee), 1, "{callee}");
    }
    // FAIL-CLOSED, unchanged: a `stdout` the list does not name still mints. A
    // dependency's or the crate's own `…::stdout` (these two really write fd
    // 1); a std generic whose fn-item argument is `std::io::stdout` (calling
    // it); and a listed configurer whose generic argument names another
    // `stdout` item.
    for callee in [
        "anstream::stdout",
        "termcolor::StandardStream::stdout",
        "my_tool::stdout",
        "core::ops::FnOnce::call_once::<fn() -> std::io::Stdout {std::io::stdout}, ()>",
        "std::process::Command::stdout::<my_tool::stdout::Sink>",
    ] {
        assert_eq!(process_semantics_rows(callee), 1, "{callee}");
    }
    // UNCHANGED NON-ROWS: the rule never had a stderr needle, so `eprint!`'s
    // backend and `io::stderr` carry no `process_semantics` row before or
    // after this change (pinned so a widening is a visible decision).
    for callee in ["std::io::stdio::stderr", "std::io::stdio::_eprint", "std::io::_eprint"] {
        assert_eq!(process_semantics_rows(callee), 0, "{callee}");
    }
}

#[test]
fn every_exclusion_is_an_authenticated_std_callee_with_a_std_argument() {
    // STRUCTURE of the list, so a later entry cannot widen it silently: each
    // excluded callee is this test's measured spelling, rooted at an
    // authenticated sysroot crate, is `Command::stdout` applied to exactly one
    // std-rooted, non-generic argument type, and names the needle only once.
    let mut listed: Vec<&str> = CALL_RULE_EXACT_CALLEE_EXCLUSIONS
        .iter()
        .flat_map(|(needle, callees)| {
            assert_eq!(*needle, "stdout", "only the `stdout` rule has exclusions");
            callees.iter().copied()
        })
        .collect();
    let mut measured = EXCLUDED_COMMAND_STDOUT.to_vec();
    listed.sort_unstable();
    measured.sort_unstable();
    assert_eq!(listed, measured, "the exclusion list moved without its measured spellings");
    for callee in listed {
        assert!(trust_types::path_root_is_authenticated_sysroot_crate(callee), "{callee}");
        let argument = callee
            .strip_prefix("std::process::Command::stdout::<")
            .and_then(|rest| rest.strip_suffix('>'))
            .unwrap_or_else(|| panic!("not `Command::stdout::<S>`: {callee}"));
        assert!(argument.starts_with("std::"), "{callee}");
        assert!(!argument.contains(['<', '>', '&', ' ', '(', '[']), "{callee}");
        assert_eq!(
            callee
                .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
                .filter(|token| *token == "stdout")
                .count(),
            1,
            "{callee}"
        );
    }
}

#[test]
fn the_exclusions_change_no_decision_but_their_own_entries() {
    // The token rule's verdict, recomputed here, agrees with the new matcher
    // on every callee except a listed child-stdio configurer. A regression
    // that widened the exclusion (a prefix, segment or substring compare, or
    // dropping the generic argument) would flip one of the agreeing rows.
    let token_rule = |callee: &str| {
        CALL_RULES
            .iter()
            .filter(|rule| call_matches(callee, rule.needle))
            .map(|rule| rule.needle)
            .collect::<Vec<_>>()
    };
    let new_rule = |callee: &str| {
        CALL_RULES
            .iter()
            .filter(|rule| call_rule_matches(callee, rule))
            .map(|rule| rule.needle)
            .collect::<Vec<_>>()
    };
    for callee in [
        "std::io::stdio::stdout",
        "std::io::stdio::_print",
        "std::process::Command::stdout",
        "std::process::Command::stdout::<fake::Loud>",
        "std::process::Command::stdout::<T>",
        "<a::Foo as a::T>::std::process::Command::stdout::<std::process::Stdio>",
        "std::process::Command::stdout_capture",
        "std::process::Command::stdouts",
        "std::process::CommandExt::stdout",
        "std::process::Command::stdout::inner",
        "std::process::stdout",
        "std::sys::process::unix::common::Command::stdout",
        "core::result::Result::<std::process::Output, std::io::Error>::unwrap",
        "std::fs::metadata::<&std::path::Path>",
        "alloc::string::String::from_utf8_lossy",
    ] {
        assert_eq!(new_rule(callee), token_rule(callee), "{callee}");
    }
    for callee in EXCLUDED_COMMAND_STDOUT {
        assert_eq!(token_rule(callee), ["stdout"], "the token rule matched {callee}");
        assert!(new_rule(callee).is_empty(), "{callee}");
    }
}
