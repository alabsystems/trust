//! Trust (G1, 2026-10-27): the documented return contracts of pointer-returning libc
//! symbols (`__error`, `__errno_location`, `getpwuid`;
//! `trust_vcgen::ffi_pointer_contract`) end to end through the generation entry the
//! compiler calls, on REAL extracted MIR (`-Ztrust-dump=mir:<dir>`, stage 1 of main
//! 723f9ec299, aarch64-apple-darwin, libc 0.2.191). Fixtures under
//! `tests/fixtures/ffi_pointer_contract/<fn>_mir.json`; the source of each function is
//! quoted at its test.
//!
//! BEFORE (the same compiler's strict gate over the same sources): every deref of the
//! errno slot and of a null-checked `getpwuid` result FAILED its `[unsafe:sep:deref]`
//! null / allocation / alignment rows (and `[unsafe:sep:write]` write permission), and
//! each rustc `CheckNull` / `CheckAlignment` assert in front of it was an
//! `UnmodeledSafetyAssert` UNKNOWN plus an unprovable hardened panic-boundary twin.
//!
//! Each positive test has its negative controls: the same shape without the fact the
//! discharge needs (no null check, a call inside the validity window, a write, a
//! mis-declared pointee, an offset pointer, a wrapper that may return null, a
//! reassigned local, a wrapper summary without the identity gate) keeps its rows.

use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/ffi_pointer_contract/{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("{path} must deserialize: {e}"))
}

/// The identity every call of `g1repro::errno_slot` in the fixtures carries (the
/// wrapper's `DefId` in the dumped crate).
const ERRNO_SLOT_CRATE: u64 = 1_543_344_083_766_507_038;
const ERRNO_SLOT_INDEX: u32 = 4;

/// The summary context the compiler would install: the wrapper summaries computed
/// over `bodies`, and (when `with_identity`) the identity map saying which calls reach
/// `g1repro::errno_slot`.
fn summaries(bodies: &[&str], with_identity: bool) -> trust_vcgen::CalleeSummaryContext {
    let funcs: Vec<VerifiableFunction> = bodies.iter().map(|n| load(n)).collect();
    let wrappers = trust_vcgen::compute_return_ffi_pointer_summaries(&funcs);
    let mut context =
        trust_vcgen::CalleeSummaryContext::default().with_return_ffi_pointer_contracts(wrappers);
    if with_identity {
        let ids = funcs
            .iter()
            .map(|f| {
                (
                    f.def_path.clone(),
                    trust_vcgen::SummaryBodyIdentity::Item {
                        stable_crate_id: ERRNO_SLOT_CRATE,
                        def_index: ERRNO_SLOT_INDEX,
                    },
                )
            })
            .collect();
        context = context.with_summary_body_identities(ids);
    }
    context
}

/// One generated row: a short rendering of its kind and text, and the verdict the
/// deterministic in-process ay gives it (or the generation's own preclassification).
#[derive(Debug, Clone)]
struct Row {
    text: String,
    verdict: &'static str,
    /// The row's violation formula is the literal `false`: in-process ay "proves" it,
    /// but the compiler path gives it no proof authority (trust-certify declines a bare
    /// `false` as a producer placeholder), so it is UNKNOWN there.
    bare_false: bool,
}

fn verdict_tag(result: &VerificationResult) -> &'static str {
    match result {
        VerificationResult::Proved { .. } => "PROVED",
        VerificationResult::Failed { .. } => "FAILED",
        _ => "UNKNOWN",
    }
}

fn row_text(vc: &VerificationCondition) -> String {
    match &vc.kind {
        VcKind::Assertion { message } => message.clone(),
        VcKind::UnsupportedMir { kind, detail } => format!("unsupported {kind}: {detail}"),
        other => format!("{other:?}"),
    }
}

/// Every row of `name` through the compiler's entry (hardened profile on, as
/// `targo trust check` runs it), each solved. The fixtures were dumped for
/// aarch64-apple-darwin, so the context declares a Darwin target as the compiler does
/// there (`with_target_is_darwin`); [`rows_on`] chooses.
fn rows(name: &str, context: Option<trust_vcgen::CalleeSummaryContext>) -> Vec<Row> {
    rows_of(load(name), context)
}

/// [`rows`] for a body built in the test (Darwin target).
fn rows_of(
    func: VerifiableFunction,
    context: Option<trust_vcgen::CalleeSummaryContext>,
) -> Vec<Row> {
    rows_on(func, context, true)
}

/// [`rows_of`] with the target's Darwin bit chosen by the test.
fn rows_on(
    func: VerifiableFunction,
    context: Option<trust_vcgen::CalleeSummaryContext>,
    darwin: bool,
) -> Vec<Row> {
    rows_with_passwd_layout(func, context, darwin, Some(darwin_passwd_layout()))
}

/// What rustc's `layout_of` computes for the fixtures' `struct passwd` (libc 0.2.191,
/// aarch64-apple-darwin: `#[repr(C)]`, ten members): 72 bytes, 8-aligned, no padding.
fn darwin_passwd_layout() -> trust_types::AdtLayoutInfo {
    trust_types::AdtLayoutInfo {
        size: 72,
        align: 8,
        field_offsets: vec![0, 8, 16, 20, 24, 32, 40, 48, 56, 64],
        repr: "c".to_string(),
    }
}

/// The compiler's foreign-call pointee layouts for `func`
/// (`VcgenContext::with_compiler_foreign_return_pointee_layouts`, which
/// `rustc_mir_transform::trust_verify` fills from `layout_of`): `layout` for the block of
/// each foreign call whose destination points to a `passwd`. The real-MIR fixtures do not
/// carry the compiler's side channel, so the test hands over what the compiler computed
/// for the declaration they were dumped from; `None` hands over nothing.
fn passwd_layouts(
    func: &VerifiableFunction,
    layout: Option<trust_types::AdtLayoutInfo>,
) -> trust_types::fx::FxHashMap<trust_types::BlockId, trust_types::AdtLayoutInfo> {
    let Some(layout) = layout else { return Default::default() };
    func.body
        .blocks
        .iter()
        .filter(|block| {
            matches!(&block.terminator, trust_types::Terminator::Call { is_foreign: true, dest, .. }
                if func.body.locals.iter().any(|decl| decl.index == dest.local
                    && matches!(&decl.ty, trust_types::Ty::RawPtr { pointee, .. }
                        if matches!(pointee.as_ref(), trust_types::Ty::Adt { name, .. }
                            if name.rsplit("::").next() == Some("passwd")))))
        })
        .map(|block| (block.id, layout.clone()))
        .collect()
}

/// [`rows_on`] with the compiler's `passwd` layout chosen by the test.
fn rows_with_passwd_layout(
    func: VerifiableFunction,
    context: Option<trust_vcgen::CalleeSummaryContext>,
    darwin: bool,
    layout: Option<trust_types::AdtLayoutInfo>,
) -> Vec<Row> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let layouts = passwd_layouts(&func, layout);
            let mut vcgen_context = trust_vcgen::VcgenContext::for_function(func.def_path.clone())
                .with_target_is_darwin(darwin)
                .with_compiler_foreign_return_pointee_layouts(layouts);
            if let Some(summaries) = context {
                vcgen_context = vcgen_context.with_callee_summaries(summaries);
            }
            let (solver_vcs, discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context(
                    &func,
                    &trust_vcgen::SummaryDatabase::default(),
                    true,
                    &vcgen_context,
                );
            let router = trust_router::Router::deterministic_in_process_ay(
                30_000,
                trust_types::determinism::EffortScale::BUILTIN,
            );
            let mut out: Vec<Row> = discharged
                .iter()
                .map(|(vc, result)| Row {
                    text: row_text(vc),
                    verdict: verdict_tag(result),
                    bare_false: vc.formula == trust_types::Formula::Bool(false),
                })
                .collect();
            for (vc, result) in router.verify_all(&solver_vcs) {
                if std::env::var_os("G1_DUMP_UNPROVED").is_some()
                    && !matches!(result, VerificationResult::Proved { .. })
                {
                    eprintln!("UNPROVED {} :: {:?} :: {:?}", row_text(&vc), vc.formula, result);
                }
                out.push(Row {
                    text: row_text(&vc),
                    verdict: verdict_tag(&result),
                    bare_false: vc.formula == trust_types::Formula::Bool(false),
                });
            }
            out
        })
        .expect("spawn generation thread")
        .join()
        .expect("generation thread must not panic")
}

/// The rows whose text contains `needle`.
fn matching<'a>(rows: &'a [Row], needle: &str) -> Vec<&'a Row> {
    rows.iter().filter(|r| r.text.contains(needle)).collect()
}

const SEP_NULL: &str = "[unsafe:sep:deref] null check";
const SEP_ALLOC: &str = "[unsafe:sep:deref] allocation validity";
/// Dropped, like the allocation row, where the facts establish the alignment
/// (`sep_engine::discharge_ffi_contract`): a positive test asserts it is absent, and the
/// negative controls that it is still there and unproved.
const SEP_ALIGN: &str = "[unsafe:sep:deref] alignment check";
const SEP_WRITE: &str = "[unsafe:sep:write] write permission";
const ASSERT_NULL: &str = "UnmodeledSafetyAssert(NullPointerDereference)";
const ASSERT_ALIGN: &str = "UnmodeledSafetyAssert(MisalignedPointerDereference)";
const TWIN_NULL: &str = "mir_assert::NullPointerDereference";
const TWIN_ALIGN: &str = "mir_assert::MisalignedPointerDereference";

/// Every row naming one of `needles` is PROVED, and at least one such row exists
/// unless `may_be_absent`.
fn assert_all_proved(name: &str, rows: &[Row], needle: &str) {
    let hits = matching(rows, needle);
    assert!(!hits.is_empty(), "{name}: expected a `{needle}` row to exist; rows: {rows:#?}");
    assert!(
        hits.iter().all(|r| r.verdict == "PROVED"),
        "{name}: every `{needle}` row must prove; got {hits:#?}"
    );
    assert!(
        hits.iter().all(|r| !r.bare_false),
        "{name}: a `{needle}` row is the literal `false`, which proves here but carries no \
         proof authority on the compiler path; got {hits:#?}"
    );
}

fn assert_none(name: &str, rows: &[Row], needle: &str) {
    let hits = matching(rows, needle);
    assert!(hits.is_empty(), "{name}: expected no `{needle}` row; got {hits:#?}");
}

fn assert_some_unproved(name: &str, rows: &[Row], needle: &str) {
    let hits = matching(rows, needle);
    assert!(
        hits.iter().any(|r| r.verdict != "PROVED"),
        "{name}: a `{needle}` row must exist and stay unproved; got {hits:#?} of {rows:#?}"
    );
}

// ── errno ───────────────────────────────────────────────────────────────────────

/// ```text
/// pub fn errno_direct() -> c_int { unsafe { *libc::__error() } }
/// ```
/// A direct foreign call: no summary needed.
#[test]
fn errno_direct_deref_proves() {
    let r = rows("errno_direct", None);
    assert_all_proved("errno_direct", &r, SEP_NULL);
    assert_none("errno_direct", &r, SEP_ALIGN);
    assert_none("errno_direct", &r, SEP_ALLOC);
    for needle in [ASSERT_NULL, ASSERT_ALIGN, TWIN_NULL, TWIN_ALIGN] {
        assert_none("errno_direct", &r, needle);
    }
}

/// ```text
/// fn errno_slot() -> *mut c_int { unsafe { libc::__error() } }
/// pub fn set_errno(value: c_int) { unsafe { *errno_slot() = value } }
/// ```
/// Through a same-crate wrapper: the contract travels only with the wrapper summary AND
/// the identity gate.
#[test]
fn set_errno_through_the_wrapper_proves() {
    let r = rows("set_errno", Some(summaries(&["errno_slot"], true)));
    assert_all_proved("set_errno", &r, SEP_NULL);
    assert_none("set_errno", &r, SEP_ALIGN);
    assert_all_proved("set_errno", &r, SEP_WRITE);
    assert_none("set_errno", &r, SEP_ALLOC);
    for needle in [ASSERT_NULL, ASSERT_ALIGN, TWIN_NULL, TWIN_ALIGN] {
        assert_none("set_errno", &r, needle);
    }
}

/// Negative controls for the wrapper: no summary at all, and a summary without the
/// identity map that says the call reaches the summarized body.
#[test]
fn set_errno_without_the_summary_or_its_identity_keeps_its_rows() {
    for (label, context) in [
        ("no summary", None),
        ("summary without identity", Some(summaries(&["errno_slot"], false))),
    ] {
        let r = rows("set_errno", context);
        let name = format!("set_errno ({label})");
        assert_some_unproved(&name, &r, SEP_NULL);
        assert_some_unproved(&name, &r, SEP_ALLOC);
        assert_some_unproved(&name, &r, SEP_WRITE);
        assert_some_unproved(&name, &r, ASSERT_NULL);
        assert_some_unproved(&name, &r, ASSERT_ALIGN);
    }
}

/// ```text
/// pub extern "C" fn errno_save_restore(sig: c_int) {
///     let slot = errno_slot();
///     let saved = unsafe { *slot };
///     let _ = sig;
///     unsafe { *slot = saved };
/// }
/// ```
/// The signal-handler errno save/restore (agy `on_signal`).
#[test]
fn errno_save_restore_in_a_signal_handler_proves() {
    let r = rows("errno_save_restore", Some(summaries(&["errno_slot"], true)));
    assert_all_proved("errno_save_restore", &r, SEP_NULL);
    assert_none("errno_save_restore", &r, SEP_ALIGN);
    assert_all_proved("errno_save_restore", &r, SEP_WRITE);
    assert_none("errno_save_restore", &r, SEP_ALLOC);
    for needle in [ASSERT_NULL, ASSERT_ALIGN, TWIN_NULL, TWIN_ALIGN] {
        assert_none("errno_save_restore", &r, needle);
    }
}

/// ```text
/// mod fake { unsafe extern "C" { #[link_name = "__error"] pub fn __error() -> *mut u64; } }
/// pub fn errno_wrong_type() -> u64 { unsafe { *fake::__error() } }
/// ```
/// The right symbol behind a declaration with another pointee: no contract. The
/// declaration's crate is re-labelled `libc` so the pointee check alone is what refuses.
#[test]
fn a_misdeclared_errno_keeps_its_rows() {
    let r = rows_of(with_errno_declared_by(load("errno_wrong_type"), "libc"), None);
    assert_some_unproved("errno_wrong_type", &r, SEP_NULL);
    assert_some_unproved("errno_wrong_type", &r, SEP_ALLOC);
    assert_some_unproved("errno_wrong_type", &r, ASSERT_NULL);
}

/// `func` with every call of an `extern`-block `__error` re-labelled as declared by
/// the crate `krate`.
fn with_errno_declared_by(mut func: VerifiableFunction, krate: &str) -> VerifiableFunction {
    let mut relabelled = 0;
    for block in &mut func.body.blocks {
        if let trust_types::Terminator::Call { callee_key: Some(key), .. } = &mut block.terminator
            && key.foreign_block_leaf.as_deref() == Some("__error")
        {
            key.krate_name = krate.to_string();
            relabelled += 1;
        }
    }
    assert!(relabelled > 0, "{}: no `__error` call to relabel", func.name);
    func
}

/// A correctly typed `__error` declared by a crate with another name lends nothing:
/// only declarations of the crate named `libc` are believed (defense in depth on top of
/// the link-symbol and upstream checks below). Positive control:
/// `errno_direct_deref_proves` (the same body, declared by `libc`).
#[test]
fn an_errno_declared_outside_the_libc_crate_keeps_its_rows() {
    let r = rows_of(with_errno_declared_by(load("errno_direct"), "g1repro"), None);
    assert_some_unproved("errno_direct", &r, SEP_NULL);
    assert_some_unproved("errno_direct", &r, SEP_ALLOC);
    assert_some_unproved("errno_direct", &r, SEP_ALIGN);
    assert_some_unproved("errno_direct", &r, ASSERT_NULL);
}

/// `func` with every `extern`-block `__error` call's key edited by `edit`.
fn with_errno_key(
    mut func: VerifiableFunction,
    edit: impl Fn(&mut trust_types::CalleeKey, &mut Vec<trust_types::Operand>),
) -> VerifiableFunction {
    let mut edited = 0;
    for block in &mut func.body.blocks {
        if let trust_types::Terminator::Call { callee_key: Some(key), args, .. } =
            &mut block.terminator
            && key.foreign_block_leaf.as_deref() == Some("__error")
        {
            edit(key, args);
            edited += 1;
        }
    }
    assert!(edited > 0, "{}: no `__error` call to edit", func.name);
    func
}

/// G1 review finding 1 (2026-10-27): the CRATE NAME is not an identity. The reviewer's
/// counterexample compiled the program's own `extern "C" { fn __error() -> *mut c_int; }`
/// with `--crate-name libc`, and its rows were discharged exactly like the real libc's.
/// Here the local declaration is modelled as the extractor now mints it: crate name
/// `libc`, leaf `__error`, but NO `upstream_foreign_link_symbol` (a local declaration
/// never carries one). The rows stay. Positive control: `errno_direct_deref_proves`.
#[test]
fn an_errno_the_local_crate_named_libc_declares_keeps_its_rows() {
    let local = with_errno_key(load("errno_direct"), |key, _| {
        assert_eq!(key.upstream_foreign_link_symbol.as_deref(), Some("__error"));
        key.upstream_foreign_link_symbol = None;
    });
    let r = rows_of(local, None);
    assert_some_unproved("errno_direct (local libc)", &r, SEP_NULL);
    assert_some_unproved("errno_direct (local libc)", &r, SEP_ALLOC);
    assert_some_unproved("errno_direct (local libc)", &r, ASSERT_NULL);
}

/// G1 review finding 1: a `libc`-named upstream crate whose `__error` declaration links
/// to ANOTHER symbol (`#[link_name = "malloc"] fn __error() -> *mut c_int`) lends
/// nothing: the contract is the C symbol's, and the link symbol is not `__error`.
#[test]
fn an_errno_renamed_by_link_name_keeps_its_rows() {
    let renamed = with_errno_key(load("errno_direct"), |key, _| {
        key.upstream_foreign_link_symbol = Some("malloc".to_string());
    });
    let r = rows_of(renamed, None);
    assert_some_unproved("errno_direct (link_name malloc)", &r, SEP_NULL);
    assert_some_unproved("errno_direct (link_name malloc)", &r, SEP_ALLOC);
    assert_some_unproved("errno_direct (link_name malloc)", &r, ASSERT_NULL);
}

/// G1 review finding 1: a declaration with another arity is not `__error`'s documented
/// prototype (`int *__error(void)`), and lends nothing.
#[test]
fn an_errno_declared_with_another_arity_keeps_its_rows() {
    let wrong_arity = with_errno_key(load("errno_direct"), |_, args| {
        args.push(trust_types::Operand::Constant(trust_types::ConstValue::Int(0)));
    });
    let r = rows_of(wrong_arity, None);
    assert_some_unproved("errno_direct (arity 1)", &r, SEP_NULL);
    assert_some_unproved("errno_direct (arity 1)", &r, SEP_ALLOC);
}

/// ```text
/// pub fn errno_offset() -> c_int { unsafe { *libc::__error().add(1) } }
/// ```
/// The deref is of an offset pointer, not of the contract-rooted local.
#[test]
fn an_offset_from_errno_keeps_its_rows() {
    let r = rows("errno_offset", None);
    assert_some_unproved("errno_offset", &r, SEP_ALLOC);
}

/// ```text
/// fn maybe_slot(real: bool) -> *mut c_int {
///     if real { unsafe { libc::__error() } } else { std::ptr::null_mut() }
/// }
/// pub fn errno_maybe(real: bool) -> c_int { unsafe { *maybe_slot(real) } }
/// ```
/// A wrapper that may return null lends nothing.
#[test]
fn a_wrapper_that_may_return_null_lends_nothing() {
    let funcs = vec![load("maybe_slot"), load("errno_slot")];
    let wrappers = trust_vcgen::compute_return_ffi_pointer_summaries(&funcs);
    assert_eq!(
        wrappers.get("g1repro::errno_slot").map(String::as_str),
        Some("__error"),
        "the positive control: `errno_slot` is a wrapper of `__error`"
    );
    assert!(
        !wrappers.contains_key("g1repro::maybe_slot"),
        "`maybe_slot` may return null and must not be summarized: {wrappers:?}"
    );
    let r = rows("errno_maybe", Some(summaries(&["maybe_slot"], true)));
    assert_some_unproved("errno_maybe", &r, SEP_NULL);
    assert_some_unproved("errno_maybe", &r, ASSERT_NULL);
}

/// ```text
/// pub fn errno_reassigned(other: *mut c_int) -> c_int {
///     let mut p = errno_slot();
///     if other.is_null() { p = other; }
///     unsafe { *p }
/// }
/// ```
/// A second assignment: the local is no longer the call result on every path.
#[test]
fn a_reassigned_errno_pointer_keeps_its_rows() {
    let r = rows("errno_reassigned", Some(summaries(&["errno_slot"], true)));
    assert_some_unproved("errno_reassigned", &r, SEP_NULL);
    assert_some_unproved("errno_reassigned", &r, ASSERT_NULL);
}

/// `errno_direct`'s `CheckNull` block (bb2) rewritten so that the assert tests ANOTHER
/// pointer: `_7 = _13 as *const ()` (a fresh, unconstrained `_13`), and, after
/// `_10 = _8 == 0` has read it, the address word `_8` is REUSED for `_1 as u64`. At the
/// terminator the last definition of `_8` names the contract-rooted `_1`, but `_10`
/// read the earlier one. The assert parser must follow the definition CURRENT at each
/// use, so this assert is not discharged by `_1`'s contract.
fn errno_direct_with_a_stale_address_word() -> VerifiableFunction {
    use trust_types::{Operand, Place, Rvalue, Statement, Ty};
    let mut func = load("errno_direct");
    let raw_i32 =
        Ty::RawPtr { mutable: true, pointee: Box::new(Ty::Int { width: 32, signed: true }) };
    func.body.locals.push(trust_types::LocalDecl { index: 13, ty: raw_i32, name: None });
    let block = &mut func.body.blocks[2];
    assert!(
        matches!(
            block.terminator,
            trust_types::Terminator::Assert {
                msg: trust_types::AssertMessage::NullPointerDereference,
                ..
            }
        ),
        "fixture drift: bb2 of errno_direct must end in the CheckNull assert"
    );
    let unit_ptr = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::Unit) };
    let u64_ty = Ty::Int { width: 64, signed: false };
    let whole = |local: usize| Place { local, projections: vec![] };
    let at_eq = block
        .stmts
        .iter()
        .position(|s| matches!(s, Statement::Assign { place, .. } if place.local == 10))
        .expect("fixture drift: `_10 = _8 == 0` in bb2");
    match &mut block.stmts[0] {
        Statement::Assign { place, rvalue, .. } if place.local == 7 => {
            *rvalue = Rvalue::Cast(Operand::Copy(whole(13)), unit_ptr);
        }
        other => panic!("fixture drift: bb2 must start with `_7 = _1 as *const ()`, got {other:?}"),
    }
    block.stmts.insert(
        at_eq + 1,
        Statement::Assign {
            place: whole(8),
            rvalue: Rvalue::Cast(Operand::Copy(whole(1)), u64_ty),
            span: trust_types::SourceSpan::default(),
        },
    );
    func
}

#[test]
fn a_null_assert_on_another_pointer_is_not_discharged_by_a_reused_address_word() {
    // Positive control: the unmodified body discharges its null assert.
    let r = rows("errno_direct", None);
    assert_none("errno_direct", &r, ASSERT_NULL);
    assert_none("errno_direct", &r, TWIN_NULL);
    // The assert really tests `_13`: it is not discharged.
    let r = rows_of(errno_direct_with_a_stale_address_word(), None);
    assert_some_unproved("errno_direct (stale address word)", &r, ASSERT_NULL);
    assert_some_unproved("errno_direct (stale address word)", &r, TWIN_NULL);
}

// ── getpwuid ────────────────────────────────────────────────────────────────────

/// ```text
/// pub fn passwd_dir_len() -> usize {
///     unsafe {
///         let pw = libc::getpwuid(libc::getuid());
///         if pw.is_null() || (*pw).pw_dir.is_null() { return 0; }
///         std::ffi::CStr::from_ptr((*pw).pw_dir).to_bytes().len()
///     }
/// }
/// ```
/// The agy `passwd_home` shape: null-checked, read before any other call.
#[test]
fn getpwuid_with_the_null_check_proves() {
    let r = rows("passwd_dir_len", None);
    assert_all_proved("passwd_dir_len", &r, SEP_NULL);
    assert_none("passwd_dir_len", &r, SEP_ALIGN);
    assert_none("passwd_dir_len", &r, SEP_ALLOC);
    for needle in [ASSERT_NULL, ASSERT_ALIGN, TWIN_NULL, TWIN_ALIGN] {
        assert_none("passwd_dir_len", &r, needle);
    }
}

/// G1 review finding 2 (2026-10-27): `getpwuid`'s result is per thread only on Darwin
/// (Libinfo); glibc and musl keep it in one process-wide buffer that another thread's
/// `getpw*` call overwrites. Off Darwin — and with no compiler context at all, which
/// declares no target — the same body keeps its rows. Positive control:
/// `getpwuid_with_the_null_check_proves` (the same body on Darwin).
#[test]
fn getpwuid_off_darwin_keeps_its_rows() {
    let r = rows_on(load("passwd_dir_len"), None, false);
    assert_some_unproved("passwd_dir_len (not Darwin)", &r, SEP_ALLOC);
    assert_some_unproved("passwd_dir_len (not Darwin)", &r, ASSERT_NULL);
}

/// The errno contract is the C standard's, on every target: off Darwin it still holds.
#[test]
fn errno_off_darwin_still_proves() {
    let r = rows_on(load("errno_direct"), None, false);
    assert_all_proved("errno_direct (not Darwin)", &r, SEP_NULL);
    assert_none("errno_direct (not Darwin)", &r, SEP_ALLOC);
}

/// ```text
/// pub fn passwd_unchecked() -> usize {
///     unsafe {
///         let pw = libc::getpwuid(libc::getuid());
///         std::ffi::CStr::from_ptr((*pw).pw_dir).to_bytes().len()
///     }
/// }
/// ```
/// No null check: getpwuid may return null, so the null rows stay. (The alignment
/// assert still discharges: a null result is aligned to everything.)
#[test]
fn getpwuid_without_the_null_check_fails() {
    let r = rows("passwd_unchecked", None);
    assert_some_unproved("passwd_unchecked", &r, SEP_NULL);
    assert_some_unproved("passwd_unchecked", &r, SEP_ALLOC);
    assert_some_unproved("passwd_unchecked", &r, ASSERT_NULL);
    assert!(
        matching(&r, SEP_NULL).iter().any(|row| row.verdict == "FAILED"),
        "the null deref must be REFUTED, not merely unknown: {r:#?}"
    );
}

/// ```text
/// let pw = libc::getpwuid(libc::getuid());
/// if pw.is_null() { return 0; }
/// let _ = libc::getpwnam(c"root".as_ptr());
/// usize::from((*pw).pw_dir.is_null())
/// ```
/// A call inside the validity window: the allocation row stays; null and alignment
/// (properties of the unchanged pointer VALUE) still discharge.
#[test]
fn getpwuid_read_after_another_call_keeps_its_allocation_row() {
    let r = rows("passwd_stale", None);
    assert_some_unproved("passwd_stale", &r, SEP_ALLOC);
    assert_all_proved("passwd_stale", &r, SEP_NULL);
    assert_none("passwd_stale", &r, ASSERT_NULL);
}

/// ```text
/// let pw = libc::getpwuid(libc::getuid());
/// if pw.is_null() { return; }
/// (*pw).pw_uid = 0;
/// ```
/// POSIX: the application shall not modify the structure.
#[test]
fn a_write_through_getpwuid_keeps_its_write_row() {
    let r = rows("passwd_write", None);
    assert_some_unproved("passwd_write", &r, SEP_WRITE);
    assert_all_proved("passwd_write", &r, SEP_NULL);
}

/// `func` with the member list of the `struct passwd` its `pw` local (`_1`) points to
/// edited by `edit`.
fn with_passwd_members(
    mut func: VerifiableFunction,
    edit: impl Fn(&mut Vec<(String, trust_types::Ty)>),
) -> VerifiableFunction {
    let mut edited = 0;
    for decl in &mut func.body.locals {
        if let trust_types::Ty::RawPtr { pointee, .. } = &mut decl.ty
            && let trust_types::Ty::Adt { name, fields, .. } = pointee.as_mut()
            && name.rsplit("::").next() == Some("passwd")
        {
            edit(fields.make_mut());
            edited += 1;
        }
    }
    assert_eq!(edited, 1, "{}: expected exactly one `*mut passwd` local", func.name);
    func
}

/// REVIEW-A4C4-MINORS-1: `getpwuid`'s contract is for Darwin's `struct passwd` EXACTLY
/// (72 bytes). The same body, its `passwd` declared by the crate named `libc` with a
/// member list that is not Darwin's, keeps its allocation-validity and alignment rows
/// (before, any `passwd` with one raw-pointer member lent the contract, so a
/// `{ pw_name, tail: [u64; 1024] }` declaration had `(*pw).tail[1000]`'s rows dropped).
/// Each edit keeps member 7 (`pw_dir`, the member the body reads) where it is. Positive
/// control: `getpwuid_with_the_null_check_proves` (the same body, unedited).
#[test]
fn getpwuid_with_a_passwd_that_is_not_darwins_keeps_its_rows() {
    let tail = || {
        (
            "tail".to_string(),
            trust_types::Ty::Array {
                elem: Box::new(trust_types::Ty::Int { width: 64, signed: false }),
                len: 1024,
            },
        )
    };
    let edits: [(&str, Box<dyn Fn(&mut Vec<(String, trust_types::Ty)>)>); 3] = [
        ("an oversized tail appended", Box::new(move |m| m.push(tail()))),
        ("pw_dir renamed", Box::new(|m| m[7].0 = "pw_home".to_string())),
        (
            "pw_uid retyped as i32",
            Box::new(|m| m[2].1 = trust_types::Ty::Int { width: 32, signed: true }),
        ),
    ];
    for (what, edit) in edits {
        let r = rows_of(with_passwd_members(load("passwd_dir_len"), edit), None);
        let name = format!("passwd_dir_len ({what})");
        assert_some_unproved(&name, &r, SEP_ALLOC);
        assert_some_unproved(&name, &r, ASSERT_NULL);
    }
}

/// REVIEW-A4C4-MINORS-1 fix-forward (2026-11-07): the member list cannot show a `repr`,
/// so rustc's computed layout of the declaration must be the C one, and the verifying
/// extractor never fills `Ty::Adt::layout` (every fixture here has `layout: null`): the
/// compiler hands it over for the call's block. Without it, or with the layout of
/// Darwin's ten members under `#[repr(C, align(16))]` (80 bytes, 16-aligned), or of a
/// reordering `repr(Rust)` (`pw_uid`/`pw_gid` moved), the null-checked body keeps its
/// allocation row and its null assert. Before, the first cut skipped the layout
/// conjunct whenever the model had none, so each of these lent the contract. Positive
/// control: `getpwuid_with_the_null_check_proves` (the same body, the C layout).
#[test]
fn getpwuid_without_the_c_layout_keeps_its_rows() {
    let over_aligned = trust_types::AdtLayoutInfo { size: 80, align: 16, ..darwin_passwd_layout() };
    let mut reordered = darwin_passwd_layout();
    reordered.field_offsets = vec![0, 8, 64, 68, 16, 24, 32, 40, 48, 56];
    reordered.repr = "rust".to_string();
    for (what, layout) in [
        ("no layout", None),
        ("repr(C, align(16))", Some(over_aligned)),
        ("repr(Rust)", Some(reordered)),
    ] {
        let r = rows_with_passwd_layout(load("passwd_dir_len"), None, true, layout);
        let name = format!("passwd_dir_len ({what})");
        assert_some_unproved(&name, &r, SEP_ALLOC);
        assert_some_unproved(&name, &r, ASSERT_NULL);
    }
}

// ── FnPtrToPtr: an opaque code address ───────────────────────────────────────────

/// `_2 = _1 as *const u8` for `_1: extern "C" fn(i32)` (MIR `CastKind::FnPtrToPtr`,
/// the `on_signal as *const ()` half of the `sighandler_t` idiom), optionally followed
/// by `_3 = *_2`. Built by hand because the extractor spells the cast `Rvalue::Cast`
/// only on this branch.
fn fn_ptr_cast_body(deref: bool) -> VerifiableFunction {
    use trust_types::{
        BasicBlock, BlockId, FnSig, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody,
    };
    let fn_ptr =
        Ty::FnPtr { sig: Box::new(FnSig { params: vec![Ty::i32()], ret: Box::new(Ty::Unit) }) };
    let code_ptr = Ty::RawPtr { mutable: false, pointee: Box::new(Ty::u8()) };
    let mut stmts = vec![Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), code_ptr.clone()),
        span: SourceSpan::default(),
    }];
    if deref {
        stmts.push(Statement::Assign {
            place: Place::local(3),
            rvalue: Rvalue::Use(Operand::Copy(Place {
                local: 2,
                projections: vec![Projection::Deref],
            })),
            span: SourceSpan::default(),
        });
    }
    let name = if deref { "fn_ptr_code_address_deref" } else { "fn_ptr_code_address" };
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("g1repro::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: fn_ptr, name: Some("handler".into()) },
                LocalDecl { index: 2, ty: code_ptr, name: Some("addr".into()) },
                LocalDecl { index: 3, ty: Ty::u8(), name: Some("byte".into()) },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// The cast lowers: no unsupported / opaque row for it, and nothing unproved at all
/// when the address is only computed (positive control for the deref test below).
#[test]
fn a_fn_pointer_cast_to_a_thin_pointer_lowers() {
    let r = rows_of(fn_ptr_cast_body(false), None);
    assert_none("fn_ptr_code_address", &r, "FnPtrToPtr");
    assert_none("fn_ptr_code_address", &r, "unsupported");
    assert!(
        r.iter().all(|row| row.verdict == "PROVED"),
        "computing a code address owes nothing; rows: {r:#?}"
    );
}

/// A read through the code address keeps its separation rows unproved: the cast is a
/// fresh value with no allocation, so nothing discharges null / allocation validity.
#[test]
fn a_deref_of_a_fn_pointer_code_address_refuses() {
    let r = rows_of(fn_ptr_cast_body(true), None);
    assert_none("fn_ptr_code_address_deref", &r, "FnPtrToPtr");
    assert_some_unproved("fn_ptr_code_address_deref", &r, SEP_NULL);
    assert_some_unproved("fn_ptr_code_address_deref", &r, SEP_ALLOC);
}

// ── addr_of source liveness over a straight run ──────────────────────────────────

const ADDR_OF_SET: &str = "[unsafe:sep:addr_of] &raw const on `_2`";

/// ```text
/// pub fn unblock(sig: c_int) {
///     let mut set_of: libc::sigset_t = unsafe { std::mem::zeroed() };
///     unsafe {
///         libc::sigemptyset(&raw mut set_of);
///         libc::sigaddset(&raw mut set_of, sig);
///         libc::pthread_sigmask(libc::SIG_UNBLOCK, &raw const set_of, std::ptr::null_mut());
///     }
/// }
/// ```
/// The agy `die_by` shape: `_8 = &raw const _2` is taken in bb3, bb3 calls
/// `null_mut()`, and bb4 (whose only predecessor is bb3) passes `_8` to
/// `pthread_sigmask`.
///
/// The fixture was dumped at `-Copt-level=0`, where rustc's `RemoveStorageMarkers` has
/// deleted every `StorageLive`/`StorageDead` before `TrustVerify` sees the body. This
/// helper puts `_2`'s markers back where an optimized build keeps them (`StorageLive(_2)`
/// first in bb0, `StorageDead(_2)` first in the return block, after the last use), so the
/// straight run has the scope evidence it requires.
fn unblock_with_source_markers() -> VerifiableFunction {
    let mut func = load("unblock");
    func.body.blocks[0].stmts.insert(0, trust_types::Statement::StorageLive(2));
    let ret = func
        .body
        .blocks
        .iter_mut()
        .find(|b| matches!(b.terminator, trust_types::Terminator::Return))
        .expect("unblock returns");
    ret.stmts.insert(0, trust_types::Statement::StorageDead(2));
    func
}

/// With `_2`'s storage markers visible and its scope ending after the last use, the
/// `&raw const` source-liveness row is discharged by the straight-run confinement, like
/// the two `&raw mut` rows consumed by their own block's call already were.
#[test]
fn an_address_taken_one_call_before_its_use_discharges_liveness() {
    let r = rows_of(unblock_with_source_markers(), None);
    assert_none("unblock", &r, ADDR_OF_SET);
    assert_none("unblock", &r, "[unsafe:sep:addr_of] &raw mut on `_2`");
}

/// Negative control: the body exactly as dumped at `-Copt-level=0` has no storage
/// markers, so a scope end between the address-of and its use could not be seen; the
/// straight run does not extend and the cross-block row stays.
#[test]
fn an_address_whose_source_has_no_storage_markers_keeps_its_liveness_row() {
    let r = rows("unblock", None);
    assert_some_unproved("unblock", &r, ADDR_OF_SET);
}

/// Negative control: the marked body with `StorageDead(_2)` also placed at the start of
/// bb4, before the call that uses the pointer, keeps the row.
#[test]
fn an_address_used_after_its_source_dies_keeps_its_liveness_row() {
    let mut func = unblock_with_source_markers();
    let using = func
        .body
        .blocks
        .iter_mut()
        .find(|b| {
            matches!(&b.terminator, trust_types::Terminator::Call { func, .. }
                if func.ends_with("pthread_sigmask"))
        })
        .expect("unblock calls pthread_sigmask");
    using.stmts.insert(0, trust_types::Statement::StorageDead(2));
    let r = rows_of(func, None);
    assert_some_unproved("unblock", &r, ADDR_OF_SET);
}

/// The marked `unblock` body with `_10 = <op>` (a fresh `u32` local) appended to bb3,
/// after `_8 = &raw const _2` and before bb3's `null_mut()` call, whose successor bb4
/// passes `_8` to `pthread_sigmask`.
fn unblock_with_source_read_after_address(op: trust_types::Operand) -> VerifiableFunction {
    let u32_ty = trust_types::Ty::Int { width: 32, signed: false };
    unblock_with_stmt_after_address(trust_types::Rvalue::Use(op), u32_ty)
}

/// The marked `unblock` body with `_10 = <rvalue>` (a fresh local of type `ty`)
/// appended to bb3, where [`unblock_with_source_read_after_address`] puts it.
fn unblock_with_stmt_after_address(
    rvalue: trust_types::Rvalue,
    ty: trust_types::Ty,
) -> VerifiableFunction {
    let mut func = unblock_with_source_markers();
    func.body.locals.push(trust_types::LocalDecl { index: 10, ty, name: None });
    let addr_block = func
        .body
        .blocks
        .iter_mut()
        .find(|b| {
            b.stmts.iter().any(|s| {
                matches!(s, trust_types::Statement::Assign {
                    place, rvalue: trust_types::Rvalue::AddressOf(false, src), ..
                } if place.local == 8 && src.local == 2)
            })
        })
        .expect("unblock takes `_8 = &raw const _2`");
    addr_block.stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place::local(10),
        rvalue,
        span: trust_types::SourceSpan::default(),
    });
    func
}

/// G1 review finding 3 (2026-10-27): a MOVE out of the source between the `&raw` and a
/// use in a later run block ends it, like a `StorageDead` (the reviewer's `let p = &raw
/// const s; drop(s); take_ptr(p)`, whose `-O1` MIR is `_5 = move _2; drop(move _5) ->
/// bb1; bb1: take_ptr(p)`). The row stays.
#[test]
fn an_address_used_after_its_source_is_moved_out_keeps_its_liveness_row() {
    let moved = unblock_with_source_read_after_address(trust_types::Operand::Move(
        trust_types::Place::local(2),
    ));
    let r = rows_of(moved, None);
    assert_some_unproved("unblock (source moved out)", &r, ADDR_OF_SET);
}

/// Positive control for the move test: a COPY of the source leaves it holding its
/// value, and the row is discharged as without the statement.
#[test]
fn an_address_used_after_its_source_is_copied_discharges_liveness() {
    let copied = unblock_with_source_read_after_address(trust_types::Operand::Copy(
        trust_types::Place::local(2),
    ));
    let r = rows_of(copied, None);
    assert_none("unblock (source copied)", &r, ADDR_OF_SET);
}

/// G1 review finding 3: a run CALL that moves the source (here bb3's own call) kills
/// it for the use in bb4.
#[test]
fn an_address_used_after_a_call_moves_its_source_keeps_its_liveness_row() {
    let mut func = unblock_with_source_markers();
    let caller = func
        .body
        .blocks
        .iter_mut()
        .find(|b| {
            matches!(&b.terminator, trust_types::Terminator::Call { func, .. }
                if func.starts_with("core::ptr::null_mut"))
        })
        .expect("unblock calls null_mut");
    let trust_types::Terminator::Call { args, .. } = &mut caller.terminator else { unreachable!() };
    args.push(trust_types::Operand::Move(trust_types::Place::local(2)));
    let r = rows_of(func, None);
    assert_some_unproved("unblock (call moves the source)", &r, ADDR_OF_SET);
}

/// The type of `_2` in the `unblock` fixture (its `sigset_t`).
fn unblock_source_ty() -> trust_types::Ty {
    let func = load("unblock");
    func.body.locals.iter().find(|d| d.index == 2).expect("unblock has `_2`").ty.clone()
}

/// G1 review (defense in depth): a NEW `&mut` alias of the source made on the run
/// counts as an end of the source, because a later call could move it out or drop it
/// in place through the alias without naming the source again. The row stays.
#[test]
fn an_address_used_after_a_mutable_alias_of_its_source_keeps_its_liveness_row() {
    let ty = trust_types::Ty::Ref { mutable: true, inner: Box::new(unblock_source_ty()) };
    let aliased = unblock_with_stmt_after_address(
        trust_types::Rvalue::Ref { mutable: true, place: trust_types::Place::local(2) },
        ty,
    );
    let r = rows_of(aliased, None);
    assert_some_unproved("unblock (source &mut-aliased)", &r, ADDR_OF_SET);
}

/// Same for a new raw alias (`&raw mut _2`).
#[test]
fn an_address_used_after_a_raw_alias_of_its_source_keeps_its_liveness_row() {
    let ty = trust_types::Ty::RawPtr { mutable: true, pointee: Box::new(unblock_source_ty()) };
    let aliased = unblock_with_stmt_after_address(
        trust_types::Rvalue::AddressOf(true, trust_types::Place::local(2)),
        ty,
    );
    let r = rows_of(aliased, None);
    assert_some_unproved("unblock (source raw-aliased)", &r, ADDR_OF_SET);
}

/// Positive control for the two alias tests: a SHARED borrow of the source cannot
/// de-initialize it, and the row is discharged as without the statement.
#[test]
fn an_address_used_after_a_shared_borrow_of_its_source_discharges_liveness() {
    let ty = trust_types::Ty::Ref { mutable: false, inner: Box::new(unblock_source_ty()) };
    let borrowed = unblock_with_stmt_after_address(
        trust_types::Rvalue::Ref { mutable: false, place: trust_types::Place::local(2) },
        ty,
    );
    let r = rows_of(borrowed, None);
    assert_none("unblock (source shared-borrowed)", &r, ADDR_OF_SET);
}
