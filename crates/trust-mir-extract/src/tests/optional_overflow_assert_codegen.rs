// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Trust (OVF-ASSERT-XCRATE-1, 2026-10-06): an optional overflow assert is erased
//! only where THIS session codegens the body.
//!
//! OVF-ASSERT-ERASED-1 extracted every optional overflow assert of a checks-off
//! session as `Goto`, keyed on the EXTRACTING session. A bundled foreign body is
//! codegened by another crate: a checks-on dependency keeps the check, so the
//! erased model proved panic-freedom for code that panics. These controls pin the
//! three modes on real compiler MIR, under overflow checks OFF and ON.
//!
//! `foreign_inlinable_body_keeps_its_panic_edge_with_checks_off` FAILS on the tree
//! before this change: there `core::num::<impl i32>::abs`'s `OverflowNeg` assert,
//! extracted in a checks-off session, became a `Goto` (no panic edge, and the
//! interval lane read `x != MIN` off nothing).

use rustc_span::def_id::DefId;
use trust_types::{BlockId, Operand, Terminator};

use super::*;
use crate::convert::{
    OPTIONAL_OVERFLOW_ASSERT_CODEGEN_SESSION_UNKNOWN, OptionalOverflowAssertBodySession,
    OptionalOverflowAssertCodegen,
};

const FIXTURE_PATH: &str = "optional_overflow_assert_codegen_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![feature(rustc_attrs)]
#![allow(internal_features)]

#[rustc_inherit_overflow_checks]
pub fn inherited_add(x: i32) -> i32 { x + 1 }

pub fn calls_abs(x: i32) -> i32 { x.abs() }

pub fn calls_exit(code: i32) -> ! { std::process::exit(code) }

pub fn calls_generic(o: Option<i32>) -> i32 { o.unwrap_or(0) }
"#;

struct FixtureFileLoader;

impl rustc_span::source_map::FileLoader for FixtureFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        path == Path::new(FIXTURE_PATH)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if self.file_exists(path) {
            Ok(FIXTURE_SOURCE.into())
        } else {
            Err(io::Error::other("unexpected optional-overflow-assert fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary reads are unsupported in the optional-overflow fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

/// How one extracted optional overflow assert came out.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Shape {
    /// Erased: a `Goto` to the assert's success target.
    Goto(usize),
    /// Kept, with the condition rustc wrote.
    Assert { target: usize },
    /// Kept, with the condition replaced by the codegen-session sentinel.
    AssertUnknownSession { target: usize },
    /// Anything else, rendered for the failure message.
    Other(#[allow(dead_code)] String),
}

fn shape(terminator: &Terminator) -> Shape {
    match terminator {
        Terminator::Goto(BlockId(target)) => Shape::Goto(*target),
        Terminator::Assert { cond: Operand::Unsupported { kind, .. }, target, .. }
            if kind == OPTIONAL_OVERFLOW_ASSERT_CODEGEN_SESSION_UNKNOWN =>
        {
            Shape::AssertUnknownSession { target: target.0 }
        }
        Terminator::Assert { cond: Operand::Copy(_) | Operand::Move(_), target, .. } => {
            Shape::Assert { target: target.0 }
        }
        other => Shape::Other(format!("{other:?}")),
    }
}

/// One optional overflow assert of a fixture body, under every mode.
#[derive(Clone, Debug)]
struct AssertRow {
    /// The assert's success target in rustc's MIR.
    target: usize,
    /// `convert_basic_block` under each explicit mode.
    this_session: Shape,
    foreign_keep: Shape,
    foreign_unknown: Shape,
    /// The `ForeignKeep` and `ForeignUnknown` terminators, serialized, with the
    /// condition removed: everything but the condition must agree.
    keep_without_cond: serde_json::Value,
    unknown_without_cond: serde_json::Value,
    /// What the production extraction (`extract_function`) produced.
    extracted: Shape,
    /// The body's classification.
    session: OptionalOverflowAssertBodySession,
    /// The classification of the same body for a CODEGEN extraction.
    codegen_session: OptionalOverflowAssertBodySession,
}

#[derive(Default)]
struct Observed {
    /// Keyed by `inherited_add` (local) and `abs` (core's, reached from `calls_abs`).
    asserts: BTreeMap<&'static str, AssertRow>,
    /// Classification of callee items that need no MIR here.
    callee_sessions: BTreeMap<&'static str, OptionalOverflowAssertBodySession>,
    overflow_checks: Option<bool>,
}

struct Callbacks {
    observed: Observed,
}

fn without_cond(terminator: &Terminator) -> serde_json::Value {
    let mut value = serde_json::to_value(terminator).expect("serializable terminator");
    if let Some(fields) = value.get_mut("Assert").and_then(serde_json::Value::as_object_mut) {
        fields.remove("cond");
    }
    value
}

fn optional_overflow_assert_row<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> AssertRow {
    let mut rows = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let mir::TerminatorKind::Assert { msg, target, .. } = &data.terminator().kind else {
            continue;
        };
        if !msg.is_optional_overflow_check() {
            continue;
        }
        let convert = |mode| {
            crate::convert::convert_basic_block(
                tcx,
                bb,
                data,
                Some(body),
                Some(body.typing_env(tcx)),
                Some(body.source.def_id()),
                mode,
            )
            .terminator
        };
        let keep = convert(OptionalOverflowAssertCodegen::ForeignKeep);
        let unknown = convert(OptionalOverflowAssertCodegen::ForeignUnknown);
        let extracted = extract_function(tcx, body)
            .body
            .blocks
            .iter()
            .find(|block| block.id == BlockId(bb.as_usize()))
            .map(|block| shape(&block.terminator))
            .unwrap_or_else(|| Shape::Other(format!("bb{} missing", bb.as_usize())));
        rows.push(AssertRow {
            target: target.as_usize(),
            this_session: shape(&convert(OptionalOverflowAssertCodegen::ThisSession)),
            foreign_keep: shape(&keep),
            foreign_unknown: shape(&unknown),
            keep_without_cond: without_cond(&keep),
            unknown_without_cond: without_cond(&unknown),
            extracted,
            session: OptionalOverflowAssertBodySession::of(tcx, body, false),
            codegen_session: OptionalOverflowAssertBodySession::of(tcx, body, true),
        });
    }
    assert_eq!(
        rows.len(),
        1,
        "`{}` must hold exactly one optional overflow assert",
        tcx.def_path_str(body.source.def_id())
    );
    rows.pop().expect("one row")
}

/// The callee `DefId` of the first direct call in `body`.
fn first_callee<'tcx>(body: &mir::Body<'tcx>) -> DefId {
    body.basic_blocks
        .iter()
        .find_map(|data| match &data.terminator().kind {
            mir::TerminatorKind::Call { func, .. } => func.const_fn_def().map(|(def, _)| def),
            _ => None,
        })
        .expect("the fixture body keeps its call (`-Zinline-mir=no`)")
}

impl rustc_driver::Callbacks for Callbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        self.observed.overflow_checks = Some(tcx.sess.overflow_checks());
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let body = tcx.optimized_mir(did);
            match tcx.item_name(did).as_str() {
                "inherited_add" => {
                    self.observed
                        .asserts
                        .insert("inherited_add", optional_overflow_assert_row(tcx, body));
                }
                "calls_abs" => {
                    let abs = first_callee(body);
                    assert!(!abs.is_local(), "`abs` is core's");
                    assert_eq!(tcx.item_name(abs).as_str(), "abs");
                    self.observed
                        .asserts
                        .insert("abs", optional_overflow_assert_row(tcx, tcx.optimized_mir(abs)));
                }
                "calls_exit" => {
                    let exit = first_callee(body);
                    assert!(!exit.is_local(), "`exit` is std's");
                    self.observed.callee_sessions.insert(
                        "exit",
                        OptionalOverflowAssertBodySession::of_instance(
                            tcx,
                            ty::InstanceKind::Item(exit),
                            false,
                        ),
                    );
                }
                "calls_generic" => {
                    let unwrap_or = first_callee(body);
                    assert!(!unwrap_or.is_local(), "`Option::unwrap_or` is core's");
                    self.observed.callee_sessions.insert(
                        "unwrap_or",
                        OptionalOverflowAssertBodySession::of_instance(
                            tcx,
                            ty::InstanceKind::Item(unwrap_or),
                            false,
                        ),
                    );
                }
                _ => {}
            }
        }
        Compilation::Stop
    }
}

fn observe(overflow_checks: &str) -> Observed {
    let mut callbacks = Callbacks { observed: Observed::default() };
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "trust_mir_extract_optional_overflow_assert".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        // Keep each call a call, so `abs` is a separate (foreign) body and the
        // local assert is the local body's own.
        "-Zinline-mir=no".into(),
        format!("-Coverflow-checks={overflow_checks}"),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile the optional-overflow-assert fixture");
    let observed = callbacks.observed;
    assert_eq!(observed.overflow_checks, Some(overflow_checks == "on"), "the flag took effect");
    for key in ["inherited_add", "abs"] {
        assert!(observed.asserts.contains_key(key), "fixture row `{key}` was not observed");
    }
    for key in ["exit", "unwrap_or"] {
        assert!(observed.callee_sessions.contains_key(key), "callee `{key}` was not observed");
    }
    observed
}

fn checks_off() -> &'static Observed {
    static OBSERVED: std::sync::OnceLock<Observed> = std::sync::OnceLock::new();
    OBSERVED.get_or_init(|| observe("off"))
}

fn checks_on() -> &'static Observed {
    static OBSERVED: std::sync::OnceLock<Observed> = std::sync::OnceLock::new();
    OBSERVED.get_or_init(|| observe("on"))
}

/// The pure decision, every input. Only a dependency-exported body whose
/// inherited-checks attribute is provably absent, at an assert its own MIR builder
/// wrote, keeps the assert as a check.
#[test]
fn the_assert_mode_truth_table() {
    use OptionalOverflowAssertBodySession as S;
    use OptionalOverflowAssertCodegen as C;
    for inlined in [false, true] {
        assert_eq!(S::ThisSession.assert_codegen(inlined), C::ThisSession);
        assert_eq!(S::Undetermined.assert_codegen(inlined), C::ForeignUnknown);
        assert_eq!(
            S::DependencyExported { inherit_overflow_checks_provably_absent: false }
                .assert_codegen(inlined),
            C::ForeignUnknown,
            "an inherited-checks body carries its asserts whatever its crate's setting"
        );
    }
    let absent = S::DependencyExported { inherit_overflow_checks_provably_absent: true };
    assert_eq!(absent.assert_codegen(false), C::ForeignKeep);
    assert_eq!(
        absent.assert_codegen(true),
        C::ForeignUnknown,
        "a MIR-inlined assert says nothing about the body's own crate"
    );
}

/// The classification of real items: local bodies and codegen extractions are this
/// session's; a foreign inlinable or generic body is undetermined; a foreign
/// exported body is the dependency's, and the inherited-checks attribute cannot be
/// read across crates, so it never reaches `ForeignKeep`.
#[test]
fn body_sessions_follow_who_codegens_the_body() {
    for observed in [checks_off(), checks_on()] {
        let local = &observed.asserts["inherited_add"];
        assert_eq!(local.session, OptionalOverflowAssertBodySession::ThisSession);
        assert_eq!(local.codegen_session, OptionalOverflowAssertBodySession::ThisSession);
        let abs = &observed.asserts["abs"];
        assert_eq!(abs.session, OptionalOverflowAssertBodySession::Undetermined, "{abs:?}");
        assert_eq!(abs.codegen_session, OptionalOverflowAssertBodySession::ThisSession);
        assert_eq!(
            observed.callee_sessions["exit"],
            OptionalOverflowAssertBodySession::DependencyExported {
                inherit_overflow_checks_provably_absent: false
            }
        );
        assert_eq!(
            observed.callee_sessions["unwrap_or"],
            OptionalOverflowAssertBodySession::Undetermined
        );
    }
}

/// With checks OFF the mode decides; with checks ON it is never consulted and the
/// assert is kept as rustc wrote it.
#[test]
fn convert_honors_the_mode_only_with_checks_off() {
    for key in ["inherited_add", "abs"] {
        let off = &checks_off().asserts[key];
        let target = off.target;
        assert_eq!(off.this_session, Shape::Goto(target), "{key}: {off:?}");
        assert_eq!(off.foreign_keep, Shape::Assert { target }, "{key}: {off:?}");
        assert_eq!(off.foreign_unknown, Shape::AssertUnknownSession { target }, "{key}: {off:?}");
        assert_eq!(
            off.keep_without_cond, off.unknown_without_cond,
            "{key}: the unknown-session assert keeps the message, the success target and \
             the unwind edge; only the condition goes"
        );

        let on = &checks_on().asserts[key];
        for mode in [&on.this_session, &on.foreign_keep, &on.foreign_unknown] {
            assert_eq!(*mode, Shape::Assert { target: on.target }, "{key}: {on:?}");
        }
    }
}

/// THE FIX. A foreign body that another crate may codegen keeps its panic edge in
/// a checks-off session, and nothing is read off its success edge.
#[test]
fn foreign_inlinable_body_keeps_its_panic_edge_with_checks_off() {
    let abs = &checks_off().asserts["abs"];
    assert_eq!(
        abs.extracted,
        Shape::AssertUnknownSession { target: abs.target },
        "core's `abs` is codegened by whichever crate references it, under that crate's \
         overflow checks: {abs:?}"
    );
}

/// What OVF-ASSERT-ERASED-1 established stays: this session's own body is extracted
/// as the `Goto` its codegen emits, and a checks-on session keeps every assert.
#[test]
fn local_body_and_checks_on_sessions_are_unchanged() {
    let local = &checks_off().asserts["inherited_add"];
    assert_eq!(local.extracted, Shape::Goto(local.target), "{local:?}");
    for key in ["inherited_add", "abs"] {
        let on = &checks_on().asserts[key];
        assert_eq!(on.extracted, Shape::Assert { target: on.target }, "{key}: {on:?}");
    }
}
