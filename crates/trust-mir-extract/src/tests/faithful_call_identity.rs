// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Real compiler calls must not become logical total-havoc sentinels in the
//! faithful extraction lane. This std-backed fixture is not the Clean helper
//! and does not establish Clone/Debug body correctness or a proof verdict.

use super::*;

const FIXTURE_PATH: &str = "faithful_call_identity_fixture.rs";
const FIXTURE_SOURCE: &str = r#"
#![allow(dead_code)]
#![feature(fmt_helpers_for_derive, pointer_is_aligned_to)]

pub fn standard_clone(value: &u64) -> u64 {
    <u64 as std::clone::Clone>::clone(value)
}

pub mod lookalike {
    pub trait Clone { fn clone(&self) -> u64; }
    impl Clone for u64 {
        #[inline(never)]
        fn clone(&self) -> u64 { self.wrapping_add(1) }
    }
}

pub fn lookalike_clone(value: &u64) -> u64 {
    <u64 as lookalike::Clone>::clone(value)
}

#[derive(Debug)]
pub struct DebugPair { pub first: u64, pub second: bool }

#[derive(Debug)]
pub struct DebugTuple(pub u64, pub bool);

#[derive(Debug)]
pub struct DebugMany { pub a: u64, pub b: u64, pub c: u64, pub d: u64, pub e: u64, pub f: bool }

#[derive(Debug)]
pub struct DebugTupleMany(pub u64, pub u64, pub u64, pub u64, pub u64, pub bool);

pub fn malformed_fixed(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct_field2_finish("Bad first", &1u64, &2u64)
}

pub fn malformed_nary(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct_fields_finish("Bad first", &[&1u64, &2u64])
}

pub fn unknown_fixed(f: &mut std::fmt::Formatter<'_>, names: &str) -> std::fmt::Result {
    f.debug_struct_field2_finish(names, &1u64, &2u64)
}

pub fn unknown_nary(f: &mut std::fmt::Formatter<'_>, names: &str) -> std::fmt::Result {
    f.debug_struct_fields_finish(names, &[&1u64, &2u64])
}

pub fn constant_local_names(f: &mut std::fmt::Formatter<'_>, first: u64, second: u64) -> std::fmt::Result {
    let names = "Good first second";
    f.debug_struct_fields_finish(names, &[&first, &second])
}

pub fn promoted_values(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let names = "Good first second";
    f.debug_struct_fields_finish(names, &[&1u64, &2u64])
}

pub fn reborrowed_names(f: &mut std::fmt::Formatter<'_>, first: u64, second: u64) -> std::fmt::Result {
    let names = "Good first second";
    let forwarded = &*names;
    f.debug_struct_fields_finish(forwarded, &[&first, &second])
}

pub fn reborrowed_mutated_names(f: &mut std::fmt::Formatter<'_>, first: u64, second: u64) -> std::fmt::Result {
    let mut names = "Good first second";
    let slot = &mut names;
    *slot = "Bad first";
    let forwarded = &*names;
    f.debug_struct_fields_finish(forwarded, &[&first, &second])
}

pub fn reborrowed_parameter_names(f: &mut std::fmt::Formatter<'_>, names: &str, first: u64, second: u64) -> std::fmt::Result {
    let forwarded = &*names;
    f.debug_struct_fields_finish(forwarded, &[&first, &second])
}

pub fn aliased_names(f: &mut std::fmt::Formatter<'_>, replacement: &str) -> std::fmt::Result {
    let mut names = "Good first second";
    let address = &raw mut names;
    unsafe { *address = replacement; }
    f.debug_struct_field2_finish(names, &1u64, &2u64)
}

pub fn safe_alias_names(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut names = "Good first second";
    let slot = &mut names;
    *slot = "Bad first";
    f.debug_struct_field2_finish(names, &1u64, &2u64)
}

#[inline(never)]
fn another_name() -> &'static str { "Bad first" }

pub fn mixed_names(f: &mut std::fmt::Formatter<'_>, good: bool) -> std::fmt::Result {
    let names;
    if good { names = "Good first second"; } else { names = another_name(); }
    f.debug_struct_field2_finish(names, &1u64, &2u64)
}

pub fn conditional_name_parameter(
    f: &mut std::fmt::Formatter<'_>, mut names: &str, good: bool,
) -> std::fmt::Result {
    if good { names = "Good first second"; }
    f.debug_struct_field2_finish(names, &1u64, &2u64)
}

pub fn conditional_value_parameter(
    f: &mut std::fmt::Formatter<'_>, mut value: &dyn std::fmt::Debug, good: bool,
) -> std::fmt::Result {
    if good { value = &1u64; }
    f.debug_struct_field2_finish("Good first second", value, &2u64)
}

pub fn conditional_array_parameter(
    f: &mut std::fmt::Formatter<'_>, mut values: [&dyn std::fmt::Debug; 2], good: bool,
) -> std::fmt::Result {
    if good { values = [&1u64, &2u64]; }
    f.debug_struct_fields_finish("Good first second", &values)
}

pub fn alignment_literal(p: *const u8) -> bool { p.is_aligned_to(8) }

pub fn alignment_local(p: *const u8) -> bool {
    let alignment = 8;
    p.is_aligned_to(alignment)
}

pub fn alignment_alias(p: *const u8) -> bool {
    let mut alignment = 8;
    let slot = &mut alignment;
    *slot = 3;
    p.is_aligned_to(alignment)
}

pub fn alignment_parameter(p: *const u8, mut alignment: usize, reset: bool) -> bool {
    if reset { alignment = 8; }
    p.is_aligned_to(alignment)
}

pub struct ForgedField;
#[automatically_derived]
impl std::fmt::Debug for ForgedField {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { panic!("forged field") }
}

pub fn forged_field(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct_field2_finish("Bad first second", &ForgedField, &2u64)
}

pub fn overwritten_value_array(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut values: [&dyn std::fmt::Debug; 2] = [&1u64, &2u64];
    values[0] = &ForgedField;
    f.debug_struct_fields_finish("Bad first second", &values)
}

pub fn overwritten_value_slot(f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut value: &dyn std::fmt::Debug = &1u64;
    let address = &raw mut value;
    unsafe { *address = &ForgedField; }
    f.debug_struct_field2_finish("Bad first second", value, &2u64)
}
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
            Err(io::Error::other("unexpected faithful call fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are not supported in call fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Case {
    StandardClone,
    LookalikeClone,
    DebugFinisher { nary: bool, total: bool },
}

impl Case {
    fn is_debug(self) -> bool {
        matches!(self, Self::DebugFinisher { .. })
    }

    fn logical_total(self) -> bool {
        self == Self::StandardClone || matches!(self, Self::DebugFinisher { total: true, .. })
    }
}

struct CallRecord {
    case: Case,
    logical: VerifiableFunction,
    faithful: VerifiableFunction,
    block: usize,
    expected_name: String,
    expected_identity: trust_types::CalleeIdentity,
    expected_key: trust_types::CalleeKey,
    expected_args: Option<Vec<Operand>>,
    destination: Place,
    target: Option<BlockId>,
    unwind: trust_types::UnwindEdge,
}

#[derive(Default)]
struct CallCallbacks {
    records: BTreeMap<String, CallRecord>,
    alignment_constants: BTreeMap<String, Option<u128>>,
}

fn plain_place(place: mir::Place<'_>) -> Place {
    assert!(place.projection.is_empty(), "fixture call operands/destination stay whole-local");
    Place::local(place.local.as_usize())
}

fn clone_argument(operand: &mir::Operand<'_>) -> Operand {
    match operand {
        mir::Operand::Copy(place) => Operand::Copy(plain_place(*place)),
        mir::Operand::Move(place) => Operand::Move(plain_place(*place)),
        _ => panic!("Clone fixture must call with an actual local reference, not a constant"),
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

impl rustc_driver::Callbacks for CallCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.file_loader = Some(Box::new(FixtureFileLoader));
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.sess.dcx().abort_if_errors();
        for owner in tcx.hir_body_owners() {
            let did = owner.to_def_id();
            if !matches!(
                tcx.def_kind(did),
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            ) {
                continue;
            }
            let Some(name) = tcx.opt_item_name(did) else { continue };
            if matches!(
                name.as_str(),
                "alignment_literal" | "alignment_local" | "alignment_alias" | "alignment_parameter"
            ) {
                let body = tcx.optimized_mir(did);
                let mut observed = Vec::new();
                for data in body.basic_blocks.iter() {
                    let mir::TerminatorKind::Call { func, args, .. } = &data.terminator().kind
                    else {
                        continue;
                    };
                    let Some((callee, _)) = func.const_fn_def() else { continue };
                    if tcx.item_name(callee).as_str() != "is_aligned_to" {
                        continue;
                    }
                    observed.push(
                        crate::immutable_operand_const(body, &args[1].node)
                            .and_then(|constant| constant.try_to_scalar_int())
                            .map(|value| value.to_uint(value.size())),
                    );
                }
                assert_eq!(observed.len(), 1, "alignment fixture retains its actual call");
                assert!(self.alignment_constants.insert(name.to_string(), observed[0]).is_none());
                continue;
            }
            let (record_name, case) = match name.as_str() {
                "standard_clone" => (name.to_string(), Case::StandardClone),
                "lookalike_clone" => (name.to_string(), Case::LookalikeClone),
                "fmt" => {
                    let impl_id = tcx.trait_impl_of_assoc(did).expect("Debug impl");
                    // These derive fixtures have nominal struct self types;
                    // inspecting the outer ADT does not normalize projections.
                    let self_ty = tcx.type_of(impl_id).instantiate_identity().skip_normalization();
                    let ty::Adt(adt, _) = self_ty.kind() else { continue };
                    let receiver = tcx.item_name(adt.did()).to_string();
                    if receiver == "ForgedField" {
                        assert!(tcx.is_automatically_derived(impl_id));
                        assert!(!tcx.is_builtin_derived(impl_id), "an attribute is not provenance");
                        continue;
                    }
                    let nary = match receiver.as_str() {
                        "DebugPair" | "DebugTuple" => false,
                        "DebugMany" | "DebugTupleMany" => true,
                        // ForgedField's panicking body is a field-totality negative,
                        // not itself one of the finisher call fixtures.
                        _ => continue,
                    };
                    assert!(tcx.is_builtin_derived(impl_id), "actual builtin derive provenance");
                    (receiver, Case::DebugFinisher { nary, total: true })
                }
                "constant_local_names" | "reborrowed_names" => {
                    (name.to_string(), Case::DebugFinisher { nary: true, total: true })
                }
                "malformed_nary"
                | "unknown_nary"
                | "overwritten_value_array"
                | "conditional_array_parameter"
                | "promoted_values"
                | "reborrowed_mutated_names"
                | "reborrowed_parameter_names" => {
                    (name.to_string(), Case::DebugFinisher { nary: true, total: false })
                }
                "malformed_fixed"
                | "unknown_fixed"
                | "aliased_names"
                | "mixed_names"
                | "forged_field"
                | "overwritten_value_slot"
                | "safe_alias_names"
                | "conditional_name_parameter"
                | "conditional_value_parameter" => {
                    (name.to_string(), Case::DebugFinisher { nary: false, total: false })
                }
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
                    let (callee, generic_args) =
                        func.const_fn_def().expect("selected call has a compiler FnDef");
                    let leaf = tcx.item_name(callee);
                    let selected = match case {
                        Case::StandardClone | Case::LookalikeClone => leaf.as_str() == "clone",
                        Case::DebugFinisher { nary, .. } => {
                            leaf.as_str()
                                == if nary {
                                    "debug_struct_fields_finish"
                                } else {
                                    "debug_struct_field2_finish"
                                }
                        }
                    };
                    selected.then_some((
                        block,
                        args,
                        destination,
                        target,
                        unwind,
                        callee,
                        generic_args,
                    ))
                })
                .collect::<Vec<_>>();
            assert_eq!(calls.len(), 1, "the real selected MIR call must survive without inlining");
            let (block, args, destination, target, unwind, callee, generic_args) = calls[0];
            if !case.is_debug() {
                let method = tcx.associated_item(callee).trait_item_def_id().unwrap_or(callee);
                let is_real_clone = tcx.trait_of_assoc(method) == tcx.lang_items().clone_trait();
                assert!(tcx.lang_items().clone_trait().is_some());
                assert_eq!(
                    is_real_clone,
                    case == Case::StandardClone,
                    "primitive receiver alone cannot authenticate a lookalike Clone trait"
                );
            } else {
                assert!(!callee.is_local(), "derived finisher is a real core Formatter method");
                let path = crate::safe_def_path_str(tcx, callee);
                assert!(
                    path.starts_with("core::fmt::Formatter")
                        || path.starts_with("std::fmt::Formatter")
                );
            }

            if case.is_debug() {
                let valid_names = !matches!(
                    record_name.as_str(),
                    "malformed_fixed"
                        | "malformed_nary"
                        | "unknown_fixed"
                        | "unknown_nary"
                        | "aliased_names"
                        | "mixed_names"
                        | "safe_alias_names"
                        | "conditional_name_parameter"
                        | "reborrowed_mutated_names"
                        | "reborrowed_parameter_names"
                );
                let fields = if matches!(record_name.as_str(), "DebugMany" | "DebugTupleMany") {
                    6
                } else {
                    2
                };
                assert_eq!(
                    crate::debug_finisher_names_have_fields(tcx, body, &args[1].node, fields),
                    valid_names,
                    "shared extractor/P-SPLIT name guard for {record_name}",
                );
            }

            let expected_identity = crate::convert::callee_identity_for(tcx, callee, generic_args)
                .expect("fully concrete fixture callee has identity");
            let expected_key = crate::convert::callee_key_for(tcx, callee);
            let expected_name = if case == Case::LookalikeClone {
                // Independently resolve this concrete local impl. Do not call
                // the name/sentinel selector under test to build its oracle.
                let instance = ty::Instance::try_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    callee,
                    generic_args,
                )
                .expect("lookalike resolution succeeds")
                .expect("concrete local impl");
                let resolved = instance.def_id();
                assert!(resolved.is_local() && tcx.is_mir_available(resolved));
                assert!(!tcx.generics_of(resolved).requires_monomorphization(tcx));
                crate::safe_def_path_str(tcx, resolved)
            } else {
                // Both standard callees are nonlocal, so local-impl
                // devirtualization is inapplicable. Derive the exact ordinary
                // spelling directly from the compiler FnDef and substitutions.
                assert!(!callee.is_local());
                crate::convert::direct_call_def_path(
                    tcx,
                    callee,
                    generic_args,
                    crate::safe_def_path_str_with_args(tcx, callee, generic_args),
                )
            };
            let logical = extract_function(tcx, body);
            let faithful = extract_function_faithful(tcx, body);
            let restored = extract_function(tcx, body);
            assert_eq!(logical.content_hash(), restored.content_hash());
            assert_eq!(
                serde_json::to_vec(&logical).expect("logical serialization"),
                serde_json::to_vec(&restored).expect("restored serialization")
            );
            let record = CallRecord {
                case,
                logical,
                faithful,
                block: block.as_usize(),
                expected_name,
                expected_identity,
                expected_key,
                expected_args: (!case.is_debug())
                    .then(|| args.iter().map(|arg| clone_argument(&arg.node)).collect()),
                destination: plain_place(*destination),
                target: target.map(|block| BlockId(block.as_usize())),
                unwind: unwind_edge(*unwind),
            };
            assert!(self.records.insert(record_name, record).is_none());
        }
        Compilation::Stop
    }
}

fn extract_calls() -> BTreeMap<String, CallRecord> {
    let mut callbacks = CallCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name".into(),
        "faithful_call_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        "-Zmir-opt-level=0".into(),
        "-Zinline-mir=no".into(),
        "-Zno-codegen".into(),
        "-Zcodegen-backend=dummy".into(),
        "--sysroot".into(),
        compiler_sysroot(),
    ];
    let result = rustc_driver::catch_fatal_errors(|| -> rustc_interface::interface::Result<()> {
        rustc_driver::run_compiler(&args, &mut callbacks);
        Ok(())
    });
    assert!(result.is_ok(), "failed to compile faithful call-identity fixture");
    assert_eq!(
        callbacks.records.keys().map(String::as_str).collect::<Vec<_>>(),
        [
            "DebugMany",
            "DebugPair",
            "DebugTuple",
            "DebugTupleMany",
            "aliased_names",
            "conditional_array_parameter",
            "conditional_name_parameter",
            "conditional_value_parameter",
            "constant_local_names",
            "forged_field",
            "lookalike_clone",
            "malformed_fixed",
            "malformed_nary",
            "mixed_names",
            "overwritten_value_array",
            "overwritten_value_slot",
            "promoted_values",
            "reborrowed_mutated_names",
            "reborrowed_names",
            "reborrowed_parameter_names",
            "safe_alias_names",
            "standard_clone",
            "unknown_fixed",
            "unknown_nary",
        ]
    );
    assert_eq!(
        callbacks.alignment_constants,
        BTreeMap::from([
            ("alignment_alias".to_string(), None),
            ("alignment_literal".to_string(), Some(8)),
            ("alignment_local".to_string(), Some(8)),
            ("alignment_parameter".to_string(), None),
        ])
    );
    callbacks.records
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

fn assert_preserved(record: &CallRecord) {
    let faithful = call_at(&record.faithful, record.block);
    let Terminator::Call { func, args, dest, target, unwind, callee_identity, callee_key, .. } =
        faithful
    else {
        panic!("actual call must remain a Call, not a value approximation");
    };
    assert_eq!(func, &record.expected_name);
    assert_ne!(func, crate::convert::TRUST_TOTAL_CLONE_SENTINEL);
    assert_eq!(*callee_identity, Some(record.expected_identity));
    assert_eq!(callee_key.as_ref(), Some(&record.expected_key));
    assert_eq!(dest, &record.destination);
    assert_eq!(target, &record.target);
    assert_eq!(unwind, &record.unwind);
    if let Some(expected) = &record.expected_args {
        assert_eq!(
            serde_json::to_vec(args).expect("args"),
            serde_json::to_vec(expected).expect("MIR args")
        );
    }

    let mut logical = call_at(&record.logical, record.block).clone();
    let Terminator::Call { func: logical_name, .. } = &mut logical else { panic!("logical call") };
    if !record.case.logical_total() {
        assert_eq!(
            logical_name.as_str(),
            func.as_str(),
            "unsupported calls retain their real identity in both extraction modes"
        );
    } else {
        assert_eq!(
            logical_name.as_str(),
            crate::convert::TRUST_TOTAL_CLONE_SENTINEL,
            "positive control must exercise a real logical sentinel rewrite"
        );
    }
    *logical_name = func.clone();
    // Exact comparison covers arguments (including the debug finisher's
    // constants), destination, normal/unwind edges, span and all authority fields.
    assert_eq!(
        serde_json::to_vec(&logical).expect("logical call"),
        serde_json::to_vec(faithful).expect("faithful call")
    );
}

#[test]
fn faithful_std_clone_retains_actual_call_and_compiler_identity() {
    let records = extract_calls();
    assert_preserved(&records["standard_clone"]);
}

#[test]
fn faithful_user_clone_lookalike_remains_an_ordinary_call_in_both_modes() {
    let records = extract_calls();
    assert_preserved(&records["lookalike_clone"]);
}

#[test]
fn faithful_derived_debug_retains_actual_finisher_call() {
    let records = extract_calls();
    for name in ["DebugPair", "DebugTuple", "DebugMany", "DebugTupleMany"] {
        assert_preserved(&records[name]);
    }
}

#[test]
fn malformed_or_unknown_debug_names_keep_the_real_call_in_both_modes() {
    let records = extract_calls();
    for name in ["malformed_fixed", "malformed_nary", "unknown_fixed", "unknown_nary"] {
        assert_preserved(&records[name]);
    }
}

#[test]
fn copied_constant_debug_names_remain_supported_but_aliases_and_mixed_defs_do_not() {
    let records = extract_calls();
    for name in [
        "constant_local_names",
        "reborrowed_names",
        "reborrowed_mutated_names",
        "reborrowed_parameter_names",
        "aliased_names",
        "mixed_names",
        "safe_alias_names",
    ] {
        assert_preserved(&records[name]);
    }
}

#[test]
fn promoted_debug_value_arrays_keep_the_real_call() {
    // A promoted array has no recoverable pre-erasure operands in this body.
    // Constant names alone must not authorize its value slice.
    assert_preserved(&extract_calls()["promoted_values"]);
}

#[test]
fn forged_automatically_derived_field_keeps_the_real_debug_call() {
    let records = extract_calls();
    assert_preserved(&records["forged_field"]);
}

#[test]
fn overwritten_debug_field_slots_and_array_elements_keep_the_real_call() {
    let records = extract_calls();
    for name in ["overwritten_value_array", "overwritten_value_slot"] {
        assert_preserved(&records[name]);
    }
}

#[test]
fn conditional_assignments_do_not_replace_unknown_incoming_parameters() {
    let records = extract_calls();
    for name in
        ["conditional_name_parameter", "conditional_value_parameter", "conditional_array_parameter"]
    {
        assert_preserved(&records[name]);
    }
}
