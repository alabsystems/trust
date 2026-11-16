// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Real Rust through the compiler-owned extractor and then the public trust-ir
//! bridge, for three producer lowering gaps that dropped whole std bodies from
//! a MIR-encoded sysroot (crystal D3, 2026-09-25) — and that any Trust program
//! containing the same construct hits the same way:
//!
//! * T2 — a DIRECT call with no return target to a local `-> !` function
//!   (`std::thread::ThreadId::new`'s `#[cold] fn exhausted() -> !`) lowers as
//!   `call; unreachable`;
//! * T3 — `ShlUnchecked`/`ShrUnchecked` (`core::ptr::align_offset::<u8>`) lower
//!   as the shift behind its asserted amount-range precondition;
//! * T4 — a transmute INTO a pattern type (`I32NotAllOnes::new`, the
//!   `ValidRawFd` of `FileDesc::from_raw_fd`) lowers as the identity behind its
//!   asserted valid range.
//!
//! Each row checks the EXTRACTED shape against the MIR it came from, lowers it,
//! requires `validate_module` to accept the result, prints the emitted IR, and
//! EXECUTES it on the reference interpreter: the value on the defined domain
//! and a failed `assert` (the charged UB precondition) outside it. A module that
//! merely comes back `Ok` is not the claim.
//!
//! T1 (`transmute::<bool, AtomicBool>`, `Once`'s queue `wait`) is NOT fixed on
//! this branch: the admission it extends — the "destination has no validity
//! invariant" transmute leg — exists only on the crystal lane. The last row pins
//! that refusal so the day it closes here, this file says so.

#![feature(rustc_private)]
// Trust (CUSTODY-EMBEDDED-TEST-LOAN-1): these tests run the compiler in process;
// their binary captures its scheduler at native entry (tests/support/native_test_entry.rs).
#![cfg_attr(
    any(target_os = "linux", target_os = "macos"),
    feature(test, custom_test_frameworks, exitcode_exit_method)
)]
#![cfg_attr(any(target_os = "linux", target_os = "macos"), test_runner(native_test_entry::main))]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use rustc_driver::Compilation;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use trust_ir::inst::{BinOp as IrBinOp, ICmpOp, Inst};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty as IrTy;
use trust_ir::{Constant, Module};
use trust_ir_bridge::{BridgeError, OwnedSequenceAccess};
use trust_types::{
    BinOp, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, VerifiableFunction,
};

const FIXTURE_PATH: &str = "producer_lowering_gaps_fixture.rs";
/// `trust_types::TRUST_TRANSMUTE_INTO_VALID_RANGE_KIND`, spelled out: the sentinel's
/// kind is a cross-crate contract between the extractor and the bridge, so the
/// tests pin its exact spelling rather than re-reading the constant (and so they
/// also compile, and fail meaningfully, against a tree that predates it).
const VALID_RANGE_SENTINEL: &str = "CastKind::Transmute(valid-range)";

const FIXTURE_SOURCE: &str = r#"
#![feature(
    core_intrinsics,
    pattern_types,
    pattern_type_macro,
    const_trait_impl,
    pattern_type_range_trait,
    temporary_niche_types
)]
#![allow(internal_features, dead_code)]

use std::pat::pattern_type;

// T2 — the shape of `std::thread::ThreadId::new`: a local cold `-> !` helper
// called on the exhaustion path, with no return target.
#[cold]
#[inline(never)]
fn exhausted() -> ! {
    panic!("failed to generate unique thread ID: bitspace exhausted")
}

pub fn next_id(last: u64) -> u64 {
    if last == u64::MAX {
        exhausted()
    }
    last + 1
}

// T3 — `unchecked_shl`/`unchecked_shr`, which `LowerIntrinsics` turns into MIR
// `ShlUnchecked`/`ShrUnchecked` (`core::ptr::align_offset::<u8>` does exactly
// this).
pub unsafe fn shl_u8(x: u8, n: u32) -> u8 {
    unsafe { core::intrinsics::unchecked_shl(x, n) }
}

pub unsafe fn shr_i32(x: i32, n: u32) -> i32 {
    unsafe { core::intrinsics::unchecked_shr(x, n) }
}

// T4 — a transmute INTO a pattern type over the source's own integer type,
// written directly, and reached through the real std constructor.
pub unsafe fn not_all_ones(fd: i32) -> pattern_type!(i32 is ..-1 | 0..) {
    unsafe { core::mem::transmute(fd) }
}

pub unsafe fn non_zero(v: u32) -> pattern_type!(u32 is 1..) {
    unsafe { core::mem::transmute(v) }
}

pub fn valid_raw_fd(fd: i32) -> Option<core::num::niche_types::I32NotAllOnes> {
    core::num::niche_types::I32NotAllOnes::new(fd)
}

// T1 (pinned, not fixed here) — `AtomicBool::new` is exactly this transmute.
pub fn atomic_bool(b: bool) -> core::sync::atomic::AtomicBool {
    unsafe { core::mem::transmute(b) }
}

// T5 — std's OWN `Vec` bodies, which the logical lane cannot lower because it
// spells `Vec<T>` as `Seq<T>`: `Vec::new` ends in the struct constructor
// `Vec { buf, len }`, `push_mut` borrows `(*self).buf` and stores `(*self).len`.
pub fn empty_u64() -> Vec<u64> {
    Vec::new()
}

pub fn push_u8(v: &mut Vec<u8>) -> &mut u8 {
    v.push_mut(1)
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
            Err(io::Error::other("unexpected producer lowering gap fixture path"))
        }
    }

    fn read_binary_file(&self, _path: &Path) -> io::Result<Arc<[u8]>> {
        Err(io::Error::other("binary source reads are unsupported for this fixture"))
    }

    fn current_directory(&self) -> io::Result<PathBuf> {
        std::env::current_dir()
    }
}

// The same explicit sysroot overrides as `compiler_atomic_bridge.rs` (an
// integration target cannot call the library's private cfg(test) helper), and
// the same refusal of a proven driver version mismatch.
fn compiler_sysroot() -> String {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();
    // Bootstrap exports RUSTC_SYSROOT (and a tool build SYSROOT) for the compiler
    // BUILD, i.e. `stage0-sysroot` while this stage 1 test embeds a newer rustc_driver, and
    // the version check below cannot tell them apart (both print `1.99.0-dev`). So the
    // ambient values come LAST, after the local stage sysroots, as in the library's own
    // `compiler_sysroot`; TRUST_TEST_SYSROOT and TEST_SYSROOT stay explicit overrides.
    let env_sysroot = |key: &str| std::env::var_os(key).map(PathBuf::from);
    let mut candidates = ["TRUST_TEST_SYSROOT", "TEST_SYSROOT"]
        .into_iter()
        .filter_map(env_sysroot)
        .collect::<Vec<_>>();
    for host in
        ["host", "aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"]
    {
        for stage in ["stage2", "stage1"] {
            candidates.push(root.join("build").join(host).join(stage));
        }
    }
    candidates.extend(["RUSTC_SYSROOT", "SYSROOT"].into_iter().filter_map(env_sysroot));
    for candidate in candidates {
        let compiler = candidate.join("bin/trustc");
        if !compiler.is_file() {
            continue;
        }
        let has_std = candidate.join("lib/rustlib").read_dir().is_ok_and(|entries| {
            entries.flatten().any(|entry| {
                let names = entry
                    .path()
                    .join("lib")
                    .read_dir()
                    .map(|files| {
                        files
                            .flatten()
                            .map(|file| file.file_name().to_string_lossy().into_owned())
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                ["libcore-", "libstd-"].iter().all(|prefix| {
                    names.iter().any(|name| name.starts_with(prefix) && name.ends_with(".rmeta"))
                })
            })
        });
        if !has_std {
            continue;
        }
        if let Some(version) = rustc_interface::util::rustc_version_str() {
            let output = std::process::Command::new(compiler)
                .arg("--version")
                .output()
                .expect("query selected compiler identity");
            if !output.status.success()
                || !String::from_utf8_lossy(&output.stdout).contains(version.trim())
            {
                continue;
            }
        }
        return candidate
            .canonicalize()
            .expect("canonical compiler sysroot")
            .to_string_lossy()
            .into_owned();
    }
    panic!(
        "set TRUST_TEST_SYSROOT to the Trust sysroot matching this embedded rustc_driver (bin/trustc and host core/std metadata required)"
    );
}

/// One extracted body, with the MIR facts the rows check the extraction against.
struct Extracted {
    function: VerifiableFunction,
    /// Every MIR binop spelling in the body (`ShlUnchecked`, …).
    mir_binops: Vec<String>,
    /// Every MIR transmute destination in the body, `Debug`-printed.
    mir_transmute_targets: Vec<String>,
}

#[derive(Default)]
struct GapCallbacks {
    bodies: BTreeMap<String, Extracted>,
}

fn record<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Extracted {
    let mut mir_binops = Vec::new();
    let mut mir_transmute_targets = Vec::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let mir::StatementKind::Assign(assign) = &statement.kind else { continue };
            let (_, rvalue) = &**assign;
            match rvalue {
                mir::Rvalue::BinaryOp(op, _) => mir_binops.push(format!("{op:?}")),
                mir::Rvalue::Cast(mir::CastKind::Transmute, _, ty) => {
                    mir_transmute_targets.push(format!("{ty:?}"))
                }
                _ => {}
            }
        }
    }
    Extracted {
        function: trust_mir_extract::extract_function(tcx, body),
        mir_binops,
        mir_transmute_targets,
    }
}

impl rustc_driver::Callbacks for GapCallbacks {
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
            let body = tcx.optimized_mir(did);
            if name == "valid_raw_fd" {
                // The REAL std constructor: the body D3 dropped reaches its transmute
                // here. Its MIR is cross-crate available because it is `#[inline]`.
                let callee = body
                    .basic_blocks
                    .iter()
                    .find_map(|data| match &data.terminator().kind {
                        mir::TerminatorKind::Call { func, .. } => func.const_fn_def(),
                        _ => None,
                    })
                    .map(|(callee, _)| callee)
                    .expect("valid_raw_fd calls I32NotAllOnes::new");
                assert_eq!(tcx.item_name(callee).as_str(), "new");
                assert!(!callee.is_local(), "the constructor is core's, not the fixture's");
                self.bodies
                    .insert("I32NotAllOnes::new".into(), record(tcx, tcx.optimized_mir(callee)));
            }
            if let Some(key) = match name.as_str() {
                "empty_u64" => Some("Vec::<u64>::new"),
                "push_u8" => Some("Vec::<u8>::push_mut"),
                _ => None,
            } {
                // T5: the REAL std callee, monomorphized exactly as the bundle
                // does (`instance_mir` instantiated under a fully monomorphic
                // typing env), so `Vec<u64>` reaches the extractor concrete.
                let (callee, args) = body
                    .basic_blocks
                    .iter()
                    .find_map(|data| match &data.terminator().kind {
                        mir::TerminatorKind::Call { func, .. } => func.const_fn_def(),
                        _ => None,
                    })
                    .expect("the T5 fixture calls its std Vec method");
                assert!(!callee.is_local(), "`{key}` is alloc's, not the fixture's");
                let typing_env = ty::TypingEnv::fully_monomorphized();
                let instance = ty::Instance::try_resolve(tcx, typing_env, callee, args)
                    .ok()
                    .flatten()
                    .expect("the std Vec callee resolves");
                let mono = instance.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    typing_env,
                    ty::EarlyBinder::bind(tcx, tcx.instance_mir(instance.def).clone()),
                );
                self.bodies.insert(key.into(), record(tcx, &mono));
            }
            self.bodies.insert(name, record(tcx, body));
        }
        Compilation::Stop
    }
}

fn extract_fixture(mir_opt_level: u8) -> BTreeMap<String, Extracted> {
    let mut callbacks = GapCallbacks::default();
    let args = vec![
        "rustc".into(),
        FIXTURE_PATH.into(),
        "--crate-name=producer_lowering_gaps_fixture".into(),
        "--crate-type=lib".into(),
        "--edition=2021".into(),
        format!("-Zmir-opt-level={mir_opt_level}"),
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
    assert!(result.is_ok(), "the producer lowering gap fixture must compile");
    callbacks.bodies
}

fn validated(result: Result<Module, trust_ir_bridge::BridgeError>, what: &str) -> Module {
    let module = result.unwrap_or_else(|error| panic!("{what} must lower, got: {error}"));
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "{what} lowered to an invalid module: {errors:?}\n{module}");
    println!("==== {what}\n{module}");
    module
}

fn single_assign(function: &VerifiableFunction, want: impl Fn(&Rvalue) -> bool) -> &Rvalue {
    let rvalues: Vec<&Rvalue> = function
        .body
        .blocks
        .iter()
        .flat_map(|block| &block.stmts)
        .filter_map(|statement| match statement {
            Statement::Assign { rvalue, .. } if want(rvalue) => Some(rvalue),
            _ => None,
        })
        .collect();
    match rvalues.as_slice() {
        [one] => one,
        other => panic!("`{}`: expected exactly one matching rvalue, got {other:?}", function.name),
    }
}

fn run(
    module: &Module,
    function: &str,
    args: Vec<InterpretValue>,
) -> Result<i128, InterpretErrorCode> {
    let id = module
        .functions
        .iter()
        .find(|f| f.name.ends_with(function))
        .unwrap_or_else(|| panic!("`{function}` is a module function"))
        .id;
    match Interpreter::with_module(module).execute_func(id, args) {
        Ok(outcome) => {
            let value = &outcome.returns[0];
            let bits = value.as_int().unwrap_or_else(|| panic!("integer result, got {value:?}"));
            Ok(if matches!(value.ty, IrTy::I8 | IrTy::I16 | IrTy::I32 | IrTy::I64 | IrTy::I128) {
                bits.as_signed()
            } else {
                i128::try_from(bits.as_unsigned()).expect("fixture results fit i128")
            })
        }
        Err(error) => Err(error.code),
    }
}

fn int(ty: IrTy, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("in-range interpreter integer")
}

/// T2. The extractor keeps the target-less call as a `Call` (rustc's never-type
/// fact), and the bridge ends its block `call @exhausted()` followed by the
/// never-continues tail `const false; assume; unreachable`.
#[test]
fn a_direct_call_to_a_local_never_returning_fn_lowers_as_call_then_unreachable() {
    for level in [0, 3] {
        let bodies = extract_fixture(level);
        let caller = &bodies["next_id"].function;
        let callee = &bodies["exhausted"].function;
        let call = caller
            .body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator {
                Terminator::Call { func, target: None, dest, .. }
                    if func.ends_with("exhausted") =>
                {
                    Some(dest)
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("O{level}: a target-less call of `exhausted`: {caller:#?}"));
        assert!(call.projections.is_empty());
        assert_eq!(
            caller.body.locals[call.local].ty,
            Ty::Never,
            "O{level}: the call's destination is the `!`-typed local"
        );
        let module = validated(
            trust_ir_bridge::lower_to_trust_ir_functions("gaps", &[caller.clone(), callee.clone()]),
            &format!("next_id + exhausted at mir-opt-level={level}"),
        );
        let callee_id = module
            .functions
            .iter()
            .find(|f| f.name.ends_with("exhausted"))
            .expect("the bundled callee")
            .id;
        let caller_fn =
            module.functions.iter().find(|f| f.name.ends_with("next_id")).expect("the caller");
        // The call is followed by the never-continues tail: `%c = const false;
        // assume %c; unreachable` (the `!` result type modelled as "control does
        // not continue", then the point's charge).
        assert!(
            caller_fn.blocks.iter().any(|block| {
                let insts = block.body.iter().map(|node| &node.inst).collect::<Vec<_>>();
                match insts.as_slice() {
                    [
                        ..,
                        Inst::Call { callee, .. },
                        Inst::Const { value: Constant::Bool(false), .. },
                        Inst::Assume { cond },
                        Inst::Unreachable,
                    ] => {
                        *callee == callee_id
                            && block.body[block.body.len() - 3].results.as_slice() == [*cond]
                    }
                    _ => false,
                }
            }),
            "O{level}: some block ends `call @exhausted(); const false; assume; unreachable`"
        );
    }
}

/// T3. `ShlUnchecked`/`ShrUnchecked` are extracted as `UncheckedBinaryOp(Shl|Shr)`
/// and lowered as the shift behind `assert(amount < BITS)`, evaluated at the
/// amount's own `u32` type.
#[test]
fn unchecked_shifts_lower_behind_their_amount_range_precondition() {
    for level in [0, 3] {
        let bodies = extract_fixture(level);
        for (name, op, value_ty, ir_op) in [
            ("shl_u8", BinOp::Shl, IrTy::U8, IrBinOp::Shl),
            ("shr_i32", BinOp::Shr, IrTy::I32, IrBinOp::AShr),
        ] {
            let extracted = &bodies[name];
            let mir_op = if op == BinOp::Shl { "ShlUnchecked" } else { "ShrUnchecked" };
            assert!(
                extracted.mir_binops.iter().any(|b| b == mir_op),
                "O{level} `{name}`: the MIR really carries `{mir_op}`: {:?}",
                extracted.mir_binops
            );
            let rvalue = single_assign(&extracted.function, |r| {
                matches!(r, Rvalue::UncheckedBinaryOp(..) | Rvalue::Unsupported { .. })
            });
            assert!(
                matches!(rvalue, Rvalue::UncheckedBinaryOp(o, _, _) if *o == op),
                "O{level} `{name}`: extracted as UncheckedBinaryOp({op:?}), got {rvalue:?}"
            );
            let module = validated(
                trust_ir_bridge::lower_to_trust_ir(&extracted.function),
                &format!("{name} at mir-opt-level={level}"),
            );
            let insts: Vec<&Inst> =
                module.functions[0].blocks.iter().flat_map(|b| &b.body).map(|n| &n.inst).collect();
            let guard = insts
                .iter()
                .position(|i| matches!(i, Inst::ICmp { op: ICmpOp::Ult, ty: IrTy::U32, .. }))
                .unwrap_or_else(|| {
                    panic!("`{name}`: `icmp ult` at the u32 amount type: {insts:?}")
                });
            let assert = insts
                .iter()
                .position(|i| matches!(i, Inst::Assert { .. }))
                .unwrap_or_else(|| panic!("`{name}`: the precondition assert: {insts:?}"));
            let shift = insts
                .iter()
                .position(
                    |i| matches!(i, Inst::BinOp { op, ty, .. } if *op == ir_op && *ty == value_ty),
                )
                .unwrap_or_else(|| panic!("`{name}`: the {ir_op:?} at {value_ty}: {insts:?}"));
            assert!(guard < assert && assert < shift, "`{name}`: guard, assert, shift: {insts:?}");
        }
        let shl =
            validated(trust_ir_bridge::lower_to_trust_ir(&bodies["shl_u8"].function), "shl_u8");
        assert_eq!(run(&shl, "shl_u8", vec![int(IrTy::U8, 3), int(IrTy::U32, 6)]), Ok(0xC0));
        for amount in [8, 32, 256] {
            assert_eq!(
                run(&shl, "shl_u8", vec![int(IrTy::U8, 1), int(IrTy::U32, amount)]),
                Err(InterpretErrorCode::Panic),
                "`unchecked_shl(1u8, {amount})` is UB and must fail its precondition"
            );
        }
        let shr =
            validated(trust_ir_bridge::lower_to_trust_ir(&bodies["shr_i32"].function), "shr_i32");
        assert_eq!(run(&shr, "shr_i32", vec![int(IrTy::I32, -64), int(IrTy::U32, 4)]), Ok(-4));
        assert_eq!(
            run(&shr, "shr_i32", vec![int(IrTy::I32, -64), int(IrTy::U32, 32)]),
            Err(InterpretErrorCode::Panic)
        );
    }
}

/// T4. A transmute into a pattern type is extracted as the valid-range sentinel,
/// its range read off rustc's layout, and lowered as the identity behind the
/// asserted range — for the fixture's own pattern types AND for core's real
/// `I32NotAllOnes::new` (the `ValidRawFd` behind `FileDesc::from_raw_fd`).
#[test]
fn a_transmute_into_a_pattern_type_lowers_as_the_identity_behind_its_valid_range() {
    for level in [0, 3] {
        let bodies = extract_fixture(level);
        for (name, start, end) in [
            ("not_all_ones", ConstValue::Int(0), ConstValue::Int(-2)),
            ("non_zero", ConstValue::Uint(1, 32), ConstValue::Uint(u128::from(u32::MAX), 32)),
            ("I32NotAllOnes::new", ConstValue::Int(0), ConstValue::Int(-2)),
        ] {
            let extracted = &bodies[name];
            assert!(
                extracted.mir_transmute_targets.iter().any(|t| t.contains("pattern_type!")),
                "O{level} `{name}`: the MIR really transmutes into a pattern type: {:?}",
                extracted.mir_transmute_targets
            );
            // The transmute's rvalue, in either spelling: the sentinel (fixed) or the
            // historical `CastKind::Transmute` refusal (the pre-fix tree).
            let rvalue = single_assign(&extracted.function, |r| {
                matches!(r, Rvalue::Unsupported { kind, .. }
                    if kind == VALID_RANGE_SENTINEL
                        || kind == "CastKind::Transmute")
            });
            let Rvalue::Unsupported { kind, operands, .. } = rvalue else { unreachable!() };
            assert_eq!(
                kind, VALID_RANGE_SENTINEL,
                "O{level} `{name}`: the valid-range sentinel, not the historical refusal"
            );
            assert!(
                matches!(
                    operands.as_slice(),
                    [Operand::Copy(_) | Operand::Move(_), Operand::Constant(s), Operand::Constant(e)]
                        // `ConstValue` has no `PartialEq`; its `Debug` spelling is exact.
                        if format!("{s:?}") == format!("{start:?}")
                            && format!("{e:?}") == format!("{end:?}")
                ),
                "O{level} `{name}`: [value, {start:?}, {end:?}] from the layout, got {operands:?}"
            );
        }
        let wrap = validated(
            trust_ir_bridge::lower_to_trust_ir(&bodies["not_all_ones"].function),
            "not_all_ones",
        );
        for fd in [0, 3, i128::from(i32::MAX), -2, i128::from(i32::MIN)] {
            assert_eq!(run(&wrap, "not_all_ones", vec![int(IrTy::I32, fd)]), Ok(fd));
        }
        assert_eq!(
            run(&wrap, "not_all_ones", vec![int(IrTy::I32, -1)]),
            Err(InterpretErrorCode::Panic),
            "-1 is outside `..-1 | 0..` and the transmute of it is UB"
        );
        let nz =
            validated(trust_ir_bridge::lower_to_trust_ir(&bodies["non_zero"].function), "non_zero");
        assert_eq!(run(&nz, "non_zero", vec![int(IrTy::U32, 7)]), Ok(7));
        assert_eq!(run(&nz, "non_zero", vec![int(IrTy::U32, 0)]), Err(InterpretErrorCode::Panic));
        // The real std constructor lowers too (its `if let` guard dominates the
        // assert, so every path that reaches the transmute satisfies it).
        validated(
            trust_ir_bridge::lower_to_trust_ir(&bodies["I32NotAllOnes::new"].function),
            "core::num::niche_types::I32NotAllOnes::new",
        );
    }
}

/// T1, PINNED OPEN on this branch. `transmute::<bool, AtomicBool>` is still the
/// historical refusal here, because the admission T1 extends (the crystal lane's
/// "destination has no validity invariant" leg, whose source conjunct lacks a
/// `bool` arm) does not exist on this branch. When it lands, this row must be
/// rewritten into the fix's regression test — never deleted.
#[test]
fn bool_into_atomic_bool_transmute_is_still_refused_on_this_branch() {
    let bodies = extract_fixture(0);
    let rvalue = single_assign(&bodies["atomic_bool"].function, |r| {
        matches!(r, Rvalue::Unsupported { .. } | Rvalue::Cast(..))
    });
    assert!(
        matches!(rvalue, Rvalue::Unsupported { kind, .. } if kind == "CastKind::Transmute"),
        "T1 is open here: expected the historical transmute refusal, got {rvalue:?}"
    );
}

/// T5 — std's own `Vec` bodies on the logical lane. Measured 2026-10-12
/// (`TRUST_SURVIVOR_TRACE=1`, nn-glm5 and tla-backend): 25 of 49 survivor-retry
/// roots lost a bundle member to "Enum aggregate on non-ADT type Seq" (the
/// `Vec { buf, len }` constructor of `Vec::new` and friends) and 2 to "Field
/// projection .N on non-aggregate type Seq" (`push_mut`, `reserve`, ...). The
/// refusal is right — `Seq` carries no `buf`/`len` — but neither message named
/// the shape or the reason. Both now refuse with the TYPED owned-sequence gap,
/// and must stay refusals: a body that lowered here would have to invent a
/// model of the Vec's representation.
#[test]
fn std_vec_internal_bodies_refuse_with_the_typed_owned_sequence_gap() {
    for level in [0, 3] {
        let bodies = extract_fixture(level);
        for (name, want) in [
            ("Vec::<u64>::new", OwnedSequenceAccess::Construct { operands: 2 }),
            ("Vec::<u8>::push_mut", OwnedSequenceAccess::Field { index: 0 }),
        ] {
            let function = &bodies[name].function;
            // `Vec::new` returns the Seq; `push_mut` reaches it through `&mut self`.
            assert!(
                function
                    .body
                    .locals
                    .iter()
                    .any(|local| format!("{:?}", local.ty).contains("Seq {")),
                "O{level} `{name}`: the logical lane spells its Vec as Seq: {:?}",
                function.body.locals
            );
            let error = trust_ir_bridge::lower_to_trust_ir(function)
                .expect_err("a std Vec-internal body must not lower on the logical lane");
            let BridgeError::OwnedSequenceInternals { access, seq_ty } = &error else {
                panic!("O{level} `{name}`: expected the typed owned-sequence gap, got {error}");
            };
            assert_eq!(*access, want, "O{level} `{name}`: {error}");
            assert!(seq_ty.starts_with("Seq {"), "O{level} `{name}`: {seq_ty}");
        }
    }
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "support/native_test_entry.rs"]
mod native_test_entry;
