// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Real-MIR call shape and name preservation, plus a positively triggered
//! pointer-assert postpass. Generic drop/contains are preservation controls:
//! their current printed turbofish names do not trigger the legacy rewrites.
//! These tests do not establish callee execution, a Clean helper, or a proof verdict.

use super::*;

const FIXTURE_PATH: &str = "faithful_call_shape_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]

pub struct Dropped(pub u32);
impl Drop for Dropped {
    fn drop(&mut self) { self.0 = 0; }
}
pub fn explicit_drop(value: Dropped) { std::mem::drop(value); }

pub fn constant_range(value: u32) -> bool {
    const RANGE: &std::ops::Range<u32> = &(2..9);
    RANGE.contains(&value)
}

pub struct Reader(pub u32);
pub trait Read { fn read(&self) -> u32; }
impl Read for Reader {
    #[inline(never)]
    fn read(&self) -> u32 { self.0 }
}
pub fn local_trait(value: &Reader) -> u32 { <Reader as Read>::read(value) }

#[inline(never)]
pub fn identity<T>(value: T) -> T { value }
pub fn generic_calls(small: u8, large: u16) -> (u8, u16) {
    (identity::<u8>(small), identity::<u16>(large))
}

pub fn primitive(value: u32, addend: u32) -> u32 { value.wrapping_add(addend) }
pub fn ref_read(value: &u64) -> u64 { unsafe { *(value as *const u64) } }
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
            Err(io::Error::other("unexpected faithful call-shape fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in call-shape fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

struct ExpectedCall {
    block: usize,
    name: String,
    identity: trust_types::CalleeIdentity,
    key: trust_types::CalleeKey,
    // None marks a compiler constant. Its value conversion is a separate
    // concern; this test does not claim that opaque constants are faithful.
    args: Vec<Option<Operand>>,
    destination: Place,
    target: Option<BlockId>,
    unwind: trust_types::UnwindEdge,
}

struct Modes {
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
    calls: Vec<ExpectedCall>,
    asserts: Vec<ExpectedAssert>,
    mir_local_count: usize,
}

struct ExpectedAssert {
    block: usize,
    condition: Operand,
    expected: bool,
    message: trust_types::AssertMessage,
    target: BlockId,
    unwind: trust_types::UnwindEdge,
}

#[derive(Default)]
struct ShapeCallbacks {
    functions: BTreeMap<String, Modes>,
}

fn plain_place(place: mir::Place<'_>) -> Place {
    assert!(place.projection.is_empty(), "fixture call places must be whole locals");
    Place::local(place.local.as_usize())
}

fn expected_operand(operand: &mir::Operand<'_>) -> Option<Operand> {
    match operand {
        mir::Operand::Copy(place) => Some(Operand::Copy(plain_place(*place))),
        mir::Operand::Move(place) => Some(Operand::Move(plain_place(*place))),
        mir::Operand::Constant(_) => None,
        other => panic!("unexpected call-shape fixture operand: {other:?}"),
    }
}

fn unwind_edge(unwind: mir::UnwindAction) -> trust_types::UnwindEdge {
    match unwind {
        mir::UnwindAction::Continue => trust_types::UnwindEdge::Continue,
        mir::UnwindAction::Unreachable => trust_types::UnwindEdge::Unreachable,
        mir::UnwindAction::Terminate(_) => trust_types::UnwindEdge::Terminate,
        mir::UnwindAction::Cleanup(block) => {
            trust_types::UnwindEdge::Cleanup(BlockId(block.as_usize()))
        }
    }
}

impl rustc_driver::Callbacks for ShapeCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
                continue;
            }
            let name = tcx.item_name(did).to_string();
            let leaf = match name.as_str() {
                "explicit_drop" => "drop",
                "constant_range" => "contains",
                "local_trait" => "read",
                "generic_calls" => "identity",
                "primitive" => "wrapping_add",
                "ref_read" => "",
                _ => continue,
            };
            let body = tcx.optimized_mir(did);
            let calls = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    let mir::TerminatorKind::Call {
                        func, args, destination, target, unwind, ..
                    } = &data.terminator().kind
                    else {
                        return None;
                    };
                    let (callee, generic_args) = func.const_fn_def()?;
                    if tcx.item_name(callee).as_str() != leaf {
                        return None;
                    }
                    let direct = crate::convert::direct_call_def_path(
                        tcx,
                        callee,
                        generic_args,
                        crate::safe_def_path_str_with_args(tcx, callee, generic_args),
                    );
                    let expected_name = if name == "local_trait" {
                        let instance = ty::Instance::try_resolve(
                            tcx,
                            body.typing_env(tcx),
                            callee,
                            generic_args,
                        )
                        .expect("local trait resolution succeeds")
                        .expect("local trait has one concrete implementation");
                        assert!(instance.def_id().is_local());
                        assert_ne!(instance.def_id(), callee);
                        assert!(!tcx.generics_of(instance.def_id()).requires_monomorphization(tcx));
                        // The trait item and resolved implementation have
                        // different compiler IDs but can print identically.
                        // Check the resolved spelling without claiming that
                        // this fixture necessarily exercises a text rename.
                        crate::safe_def_path_str(tcx, instance.def_id())
                    } else if name == "primitive" {
                        assert!(!callee.is_local());
                        let marked = format!(
                            "{}{}",
                            trust_types::TRUST_RUSTC_TOTAL_PRIMITIVE_METHOD_PATH_PREFIX,
                            direct
                        );
                        assert!(
                            trust_types::RustcTotalPrimitiveMethod::classify(&marked).is_some()
                        );
                        marked
                    } else {
                        direct
                    };
                    Some(ExpectedCall {
                        block: block.as_usize(),
                        name: expected_name,
                        identity: crate::convert::callee_identity_for(tcx, callee, generic_args)
                            .expect("concrete callee has compiler identity"),
                        key: crate::convert::callee_key_for(tcx, callee),
                        args: args.iter().map(|arg| expected_operand(&arg.node)).collect(),
                        destination: plain_place(*destination),
                        target: target.map(|block| BlockId(block.as_usize())),
                        unwind: unwind_edge(*unwind),
                    })
                })
                .collect::<Vec<_>>();
            let expected_calls = match name.as_str() {
                "generic_calls" => 2,
                "ref_read" => 0,
                _ => 1,
            };
            assert_eq!(calls.len(), expected_calls);
            let asserts = if name == "ref_read" {
                body.basic_blocks
                    .iter_enumerated()
                    .filter_map(|(block, data)| {
                        let mir::TerminatorKind::Assert {
                            cond, expected, msg, target, unwind, ..
                        } = &data.terminator().kind
                        else {
                            return None;
                        };
                        let message = match &**msg {
                            mir::AssertKind::MisalignedPointerDereference { .. } => {
                                trust_types::AssertMessage::MisalignedPointerDereference
                            }
                            mir::AssertKind::NullPointerDereference => {
                                trust_types::AssertMessage::NullPointerDereference
                            }
                            other => panic!("unexpected reference-read assertion: {other:?}"),
                        };
                        Some(ExpectedAssert {
                            block: block.as_usize(),
                            condition: expected_operand(cond)
                                .expect("pointer check uses a local condition"),
                            expected: *expected,
                            message,
                            target: BlockId(target.as_usize()),
                            unwind: unwind_edge(*unwind),
                        })
                    })
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };
            if name == "ref_read" {
                assert!(
                    !asserts.is_empty(),
                    "compiler must emit real pointer assertions for this fixture"
                );
            }

            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            let restored = extract_function(tcx, body);
            assert_eq!(logical.content_hash(), restored.content_hash());
            assert_eq!(
                serde_json::to_vec(&logical).expect("logical serialization"),
                serde_json::to_vec(&restored).expect("restored serialization")
            );
            assert!(
                self.functions
                    .insert(
                        name,
                        Modes {
                            logical,
                            faithful,
                            calls,
                            asserts,
                            mir_local_count: body.local_decls.len()
                        }
                    )
                    .is_none()
            );
        }
        Compilation::Stop
    }
}

fn extract_modes() -> BTreeMap<String, Modes> {
    let mut callbacks = ShapeCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "faithful_call_shape_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
        "-Zinline-mir=no".into(),
        "-Cdebug-assertions=yes".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile faithful call-shape fixture");
    assert_eq!(
        callbacks.functions.keys().map(String::as_str).collect::<Vec<_>>(),
        [
            "constant_range",
            "explicit_drop",
            "generic_calls",
            "local_trait",
            "primitive",
            "ref_read"
        ]
    );
    callbacks.functions
}

fn call_at(function: &VerifiableFunction, block: usize) -> &Terminator {
    &function
        .body
        .blocks
        .iter()
        .find(|entry| entry.id == BlockId(block))
        .expect("same MIR block")
        .terminator
}

fn assert_preserved(modes: &Modes, call: &ExpectedCall) {
    let Terminator::Call { func, args, dest, target, unwind, callee_identity, callee_key, .. } =
        call_at(&modes.faithful, call.block)
    else {
        panic!("actual MIR call {} must retain its Call terminator", call.name);
    };
    assert_eq!(func, &call.name);
    assert_eq!(*callee_identity, Some(call.identity));
    assert_eq!(callee_key.as_ref(), Some(&call.key));
    assert_eq!(dest, &call.destination);
    assert_eq!(target, &call.target);
    assert_eq!(unwind, &call.unwind);
    assert_eq!(args.len(), call.args.len());
    for (actual, expected) in args.iter().zip(&call.args) {
        if let Some(expected) = expected {
            assert_eq!(
                serde_json::to_vec(actual).expect("actual operand"),
                serde_json::to_vec(expected).expect("compiler operand")
            );
        } else {
            assert!(matches!(actual, Operand::Constant(_)), "compiler constant stays an operand");
        }
    }
    assert_eq!(modes.faithful.body.locals.len(), modes.mir_local_count);
}

#[test]
fn faithful_generic_mem_drop_preserves_the_existing_real_call_in_both_modes() {
    let functions = extract_modes();
    let modes = &functions["explicit_drop"];
    let call = &modes.calls[0];
    assert_preserved(modes, call);
    assert_eq!(
        serde_json::to_vec(call_at(&modes.logical, call.block)).expect("logical call"),
        serde_json::to_vec(call_at(&modes.faithful, call.block)).expect("faithful call")
    );
    assert_eq!(modes.logical.body.locals.len(), modes.mir_local_count);
}

#[test]
fn faithful_generic_range_contains_preserves_the_existing_real_call_in_both_modes() {
    let functions = extract_modes();
    let modes = &functions["constant_range"];
    let call = &modes.calls[0];
    assert_preserved(modes, call);
    assert_eq!(
        serde_json::to_vec(call_at(&modes.logical, call.block)).expect("logical call"),
        serde_json::to_vec(call_at(&modes.faithful, call.block)).expect("faithful call")
    );
    assert_eq!(modes.logical.body.locals.len(), modes.mir_local_count);
}

#[test]
fn faithful_local_trait_keeps_compiler_devirtualization_and_generic_calls_distinct() {
    let functions = extract_modes();
    for name in ["local_trait", "generic_calls"] {
        let modes = &functions[name];
        for call in &modes.calls {
            assert_preserved(modes, call);
            assert_eq!(
                serde_json::to_vec(call_at(&modes.logical, call.block)).expect("logical call"),
                serde_json::to_vec(call_at(&modes.faithful, call.block)).expect("faithful call")
            );
        }
    }
    let calls = &functions["generic_calls"].calls;
    assert_ne!(calls[0].name, calls[1].name);
    assert_ne!(calls[0].identity, calls[1].identity);
}

#[test]
fn faithful_primitive_keeps_authenticated_operation_marker() {
    let functions = extract_modes();
    let modes = &functions["primitive"];
    let call = &modes.calls[0];
    assert_preserved(modes, call);
    assert_eq!(
        serde_json::to_vec(call_at(&modes.logical, call.block)).expect("logical call"),
        serde_json::to_vec(call_at(&modes.faithful, call.block)).expect("faithful call")
    );
}

#[test]
fn faithful_reference_read_retains_pointer_assertions_that_logical_mode_discharges() {
    let functions = extract_modes();
    let modes = &functions["ref_read"];
    assert!(!modes.asserts.is_empty(), "must exercise a real compiler-generated check");
    assert_eq!(modes.faithful.body.locals.len(), modes.mir_local_count);
    for check in &modes.asserts {
        let logical = call_at(&modes.logical, check.block);
        assert!(
            matches!(logical, Terminator::Goto(target) if *target == check.target),
            "positive control must discharge the compiler pointer assert, got {logical:?}"
        );
        let Terminator::Assert { cond, expected, msg, target, unwind, .. } =
            call_at(&modes.faithful, check.block)
        else {
            panic!("faithful mode must retain the actual compiler pointer assertion");
        };
        assert_eq!(
            serde_json::to_vec(cond).expect("condition"),
            serde_json::to_vec(&check.condition).expect("compiler condition")
        );
        assert_eq!(*expected, check.expected);
        assert_eq!(
            serde_json::to_vec(msg).expect("message"),
            serde_json::to_vec(&check.message).expect("compiler message kind")
        );
        assert_eq!(*target, check.target);
        assert_eq!(*unwind, check.unwind);
    }
}
