//! Trust (FFI-SCALAR-LIBC-1, 2026-11-01): the integer-argument libc call summaries
//! (`getpid`, `getpgrp`, `geteuid`, `getsid`, `tcgetpgrp`, `raise`, `__error`;
//! `trust_vcgen::ffi_summary::scalar_libc_summaries`) end to end through the
//! generation entry the compiler calls, on REAL extracted MIR (`-Ztrust-dump=mir:<dir>`,
//! the stage 1 of the combined G1+G3 landing tree 87c5b81eef, aarch64-apple-darwin,
//! the sysroot `libc` via `rustc_private`). Fixtures under
//! `tests/fixtures/ffi_scalar_libc/<fn>_mir.json`; the sources are
//! `scalar.rs.txt` and `fakelibc.rs.txt` beside them (the second compiled
//! `--crate-name libc -C metadata=fake`, so its key's crate NAME is `libc` too).
//!
//! BEFORE (the same compiler's strict gate over the same source): every one of these
//! functions failed the strict lane on exactly one row, the FFI lane's
//! `unmodeled FFI call: no summary` (`hardened_ffi_boundary`, UNKNOWN).
//!
//! Each positive (a call to the upstream `libc` crate's own declaration of the symbol,
//! at its arity) generates no FFI row. The negative controls keep it: the program's own
//! declaration of `getpid`, an upstream crate named `libc` declaring
//! `#[link_name = "getppid"] fn getpid()`, and the same crate declaring
//! `#[link_name = "getsid"] fn session_of(pid)`.

use trust_types::{VcKind, VerifiableFunction, VerificationCondition};

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/ffi_scalar_libc/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("{path} must deserialize: {e}"))
}

/// Every row `name` generates (solver-bound and generation-discharged), hardened
/// profile on, as `targo trust check` runs it, on a Darwin target as dumped.
fn rows(name: &str) -> Vec<VerificationCondition> {
    let func = load(name);
    let context =
        trust_vcgen::VcgenContext::for_function(func.def_path.clone()).with_target_is_darwin(true);
    let (solver_vcs, discharged) =
        trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context(
            &func,
            &trust_vcgen::SummaryDatabase::default(),
            true,
            &context,
        );
    solver_vcs.into_iter().chain(discharged.into_iter().map(|(vc, _)| vc)).collect()
}

/// The FFI lane's rows: the `FfiBoundaryViolation` kind, or the hardened
/// `FfiBoundary` category.
fn ffi_rows(rows: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    rows.iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::FfiBoundaryViolation { .. })
                || format!("{:?}", vc.kind).contains("FfiBoundary")
        })
        .collect()
}

/// The fixture's one call is the extractor's own key for it (a guard on the fixture:
/// a re-dump that lost a field would make a negative pass for the wrong reason).
fn the_call(func: &VerifiableFunction) -> (bool, trust_types::CalleeKey, usize) {
    let calls: Vec<_> = func
        .body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            trust_types::Terminator::Call { is_foreign, callee_key, args, .. } => {
                Some((*is_foreign, callee_key.clone(), args.len()))
            }
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{}: exactly one call", func.name);
    let (is_foreign, key, arity) = calls.into_iter().next().unwrap();
    (is_foreign, key.expect("the call is keyed"), arity)
}

#[test]
fn upstream_libc_scalar_calls_generate_no_ffi_row() {
    for (name, symbol, arity) in [
        ("pid", "getpid", 0),
        ("pgrp", "getpgrp", 0),
        ("euid", "geteuid", 0),
        ("sid", "getsid", 1),
        ("fg", "tcgetpgrp", 1),
        ("raise_it", "raise", 1),
        ("errno_slot", "__error", 0),
    ] {
        let func = load(name);
        let (is_foreign, key, args) = the_call(&func);
        assert!(is_foreign, "{name}");
        assert_eq!(key.krate_name, "libc", "{name}");
        assert_eq!(key.foreign_block_leaf.as_deref(), Some(symbol), "{name}");
        assert_eq!(key.upstream_foreign_link_symbol.as_deref(), Some(symbol), "{name}");
        assert_eq!(args, arity, "{name}");
        let rows = rows(name);
        let ffi = ffi_rows(&rows);
        assert!(ffi.is_empty(), "{name}: the `{symbol}` call must mint no FFI row; got {ffi:#?}");
    }
}

#[test]
fn own_and_misdeclared_libc_calls_keep_the_unmodeled_ffi_row() {
    for (name, why) in [
        ("own_pid", "the program's own `extern` declaration of `getpid` (no upstream link symbol)"),
        ("fake_pid", "an upstream crate named `libc` linking `getppid` under the name `getpid`"),
        ("fake_sid", "an upstream crate named `libc` linking `getsid` under the name `session_of`"),
    ] {
        let func = load(name);
        let (is_foreign, key, _) = the_call(&func);
        assert!(is_foreign, "{name}");
        // The fixture really is the shape the control names.
        match name {
            "own_pid" => assert_eq!(key.upstream_foreign_link_symbol, None),
            "fake_pid" => {
                assert_eq!(key.krate_name, "libc");
                assert_eq!(key.foreign_block_leaf.as_deref(), Some("getpid"));
                assert_eq!(key.upstream_foreign_link_symbol.as_deref(), Some("getppid"));
            }
            _ => {
                assert_eq!(key.krate_name, "libc");
                assert_eq!(key.foreign_block_leaf.as_deref(), Some("session_of"));
                assert_eq!(key.upstream_foreign_link_symbol.as_deref(), Some("getsid"));
            }
        }
        let rows = rows(name);
        // The row is the no-summary fail-close. Its violation is `true`, conjoined with
        // the interval environment where the body has bounded locals (`fake_sid`'s
        // parameter), which keeps it satisfiable.
        let unmodeled = ffi_rows(&rows).into_iter().any(|vc| {
            matches!(&vc.kind, VcKind::FfiBoundaryViolation { desc, .. }
                if desc.contains("unmodeled FFI call: no summary"))
        });
        assert!(unmodeled, "{name} ({why}): must keep the fail-closed FFI row; got {rows:#?}");
    }
}
