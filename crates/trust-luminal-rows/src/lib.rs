// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 OR the MIT license
//
//! trust-luminal-rows: what the Luminal-row tests share.
//!
//! Each Luminal capability row this crate meets
//! (`tests/luminal-domination/capabilities.json`, docs/PLAN.md section 4) is
//! one integration-test target with its own `main`. A target builds a trust-ir
//! module through trust-ir's public builder, validates it, runs every case in
//! the reference interpreter against a hand-written loop, and then sends every
//! run to SemR's executable oracle (`semr_eval`, built from trust-ir's
//! `lean/semr` at Trust's `first-party/trust-ir` pin) on the module's binary
//! image. Only when every check has passed and SemR has returned the
//! interpreter's verdict on every run does the target print
//!
//! ```text
//! LUMINAL-ROW <id> PASS
//! ```
//!
//! as its last line ([`Row::finish`]); `scripts/luminal_domination.py --run`
//! counts a row as met only on that line and exit status 0. A failed check
//! panics, so the process exits non-zero before the line.
//!
//! SemR is required, never optional, for the line: when no `lake` exists and
//! `TRUST_IR_REQUIRE_LEAN` is not `1`, the SemR half is skipped with a
//! `SKIPPED:` line and the row is NOT met by that run (exit 0, no pass line).
//! With `TRUST_IR_REQUIRE_LEAN=1` (the rows' exits set it) a missing `lake` is
//! a failure. The Lake is the one trust-ir's own SemR tests use:
//! `TRUST_IR_SEMR_LAKE`, `TRUST_IR_LAKE`, `$HOME/.elan/bin/lake`, then `PATH`.
//!
//! What a pass establishes: the interpreter and SemR agree with each other and
//! with the hand loop on the finite runs the target names. It is sampled
//! evidence, not a proof over every shape or value.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::{
    ArrayValue, BodyGate, FuncId, Function, Inst, InterpretErrorCode, InterpretValue,
    InterpretValueKind, Interpreter, Module, Ty, ValueId,
};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

/// `tensor<elem, rank>`.
#[must_use]
pub fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

/// What emits a case's body from the function's parameters; the returned
/// value is the function's one result.
pub type Emit = Box<dyn Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId>;

/// One function `fn {name}(params..) -> result`, one entry block whose body
/// [`Emit`] writes, then the return of the value it gives.
pub struct Case {
    pub name: String,
    pub params: Vec<Ty>,
    pub result: Ty,
    pub body: Emit,
}

/// A [`Case`].
pub fn case(
    name: impl Into<String>,
    params: Vec<Ty>,
    result: Ty,
    body: impl Fn(&mut FunctionBuilder<'_>, &[ValueId]) -> ValueId + 'static,
) -> Case {
    Case { name: name.into(), params, result, body: Box::new(body) }
}

/// The module holding `cases`, each body gated (the cases are executable
/// fixtures, never a proof-carrying body).
///
/// # Panics
///
/// When the builder refuses the module, or two cases share a name.
#[must_use]
pub fn module_of(name: &str, cases: &[Case]) -> Module {
    let mut mb = ModuleBuilder::new(name);
    for (i, c) in cases.iter().enumerate() {
        assert!(
            cases[..i].iter().all(|earlier| earlier.name != c.name),
            "two cases named {}",
            c.name
        );
        let ft = mb.add_func_type(c.params.clone(), vec![c.result.clone()]);
        let mut fb = mb.function(c.name.as_str(), ft);
        let entry = fb.create_block();
        let params: Vec<ValueId> =
            c.params.iter().map(|ty| fb.add_block_param(entry, ty.clone())).collect();
        fb.switch_to_block(entry);
        let out = (c.body)(&mut fb, &params);
        fb.ret(vec![out]);
        fb.set_body_gate(BodyGate::Gated {
            authority: "luminal-row-fixture".into(),
            evidence: None,
        });
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: a Luminal-row fixture")
}

/// Asserts that the module validates with no error, and names the module in
/// the failure.
///
/// # Panics
///
/// When the validator reports anything.
pub fn assert_validates(m: &Module) {
    let errors = validate_module(m);
    assert!(errors.is_empty(), "module {} must validate, got {errors:#?}", m.name);
}

/// The function `name` of `m`.
///
/// # Panics
///
/// When there is none.
#[must_use]
pub fn function<'m>(m: &'m Module, name: &str) -> &'m Function {
    m.functions.iter().find(|f| f.name == name).unwrap_or_else(|| panic!("no function {name}"))
}

/// Every instruction of `name`'s body, block by block, the return included.
#[must_use]
pub fn instructions<'m>(m: &'m Module, name: &str) -> Vec<&'m Inst> {
    function(m, name)
        .blocks
        .iter()
        .flat_map(|block| block.body.iter().map(|node| &node.inst))
        .collect()
}

/// An integer scalar of type `ty` holding `value` (reduced to the type's
/// width as the interpreter's constructor reduces it).
///
/// # Panics
///
/// When `ty` is not an integer type.
#[must_use]
pub fn int(ty: &Ty, value: i128) -> InterpretValue {
    InterpretValue::int(ty.clone(), value).expect("an integer value")
}

/// A tensor of `elem` with extents `dims` and the row-major `values`.
///
/// # Panics
///
/// When the element count is not the product of `dims`.
#[must_use]
pub fn tensor_value(elem: &Ty, dims: &[u64], values: &[i128]) -> InterpretValue {
    assert_eq!(values.len(), count(dims), "{dims:?} holds {} elements", count(dims));
    InterpretValue {
        ty: tensor(elem.clone(), dims.len() as u32),
        kind: InterpretValueKind::Tensor {
            dims: dims.to_vec(),
            elems: ArrayValue::from_vec(values.iter().map(|&x| int(elem, x)).collect()),
        },
    }
}

// ───────────────────────────── index space ─────────────────────────────

/// The number of elements of a tensor of extents `dims`.
#[must_use]
pub fn count(dims: &[u64]) -> usize {
    dims.iter().map(|&d| usize::try_from(d).expect("a test extent fits usize")).product()
}

/// Every coordinate of extents `dims`, in row-major order (the last axis
/// fastest); one empty coordinate for rank 0, none when an extent is 0.
#[must_use]
pub fn coordinates(dims: &[u64]) -> Vec<Vec<u64>> {
    let mut out = Vec::with_capacity(count(dims));
    for flat in 0..count(dims) {
        let mut rest = flat as u64;
        let mut coord = vec![0u64; dims.len()];
        for (slot, &extent) in coord.iter_mut().zip(dims).rev() {
            *slot = rest % extent;
            rest /= extent;
        }
        out.push(coord);
    }
    out
}

/// The row-major offset of `coord` in extents `dims`.
///
/// # Panics
///
/// When the ranks differ or a coordinate is outside its axis: the hand loops
/// read only in range.
#[must_use]
pub fn offset(dims: &[u64], coord: &[u64]) -> usize {
    assert_eq!(dims.len(), coord.len(), "one coordinate per axis");
    let mut at = 0usize;
    for (&extent, &c) in dims.iter().zip(coord) {
        assert!(c < extent, "the hand loop reads in range: {c} in {extent}");
        at = at * extent as usize + c as usize;
    }
    at
}

// ───────────────────────────── verdicts ─────────────────────────────

/// SemR's spelling of an integer type (`intTyOfCode` in trust-ir's
/// `lean/semr/SemRRuntimeMain.lean`).
///
/// # Panics
///
/// When `ty` is not an integer type.
#[must_use]
pub fn semr_int_code(ty: &Ty) -> u32 {
    match ty {
        Ty::I8 => 0,
        Ty::I16 => 1,
        Ty::I32 => 2,
        Ty::I64 => 3,
        Ty::I128 => 4,
        Ty::Isize => 5,
        Ty::U8 => 6,
        Ty::U16 => 7,
        Ty::U32 => 8,
        Ty::U64 => 9,
        Ty::U128 => 10,
        Ty::Usize => 11,
        other => panic!("not an integer element type: {other}"),
    }
}

/// One engine's verdict on one run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// One returned integer tensor: its element type's SemR code, extents
    /// and row-major residues (each the element's bits, unsigned).
    Tensor { elem: u32, dims: Vec<u64>, residues: Vec<u128> },
    /// Undefined behaviour, by its normative message.
    Ub(String),
    /// Anything else, verbatim.
    Other(String),
}

/// A returned tensor as a [`Verdict::Tensor`], with its element type and its
/// elements as the integers they denote (signed types two's complement).
///
/// # Panics
///
/// When `v` is not an integer tensor whose elements share one width.
#[must_use]
pub fn decode(v: &InterpretValue) -> (Ty, Vec<u64>, Vec<i128>) {
    let (Ty::Tensor(elem, _), InterpretValueKind::Tensor { dims, elems }) = (&v.ty, &v.kind) else {
        panic!("a tensor value, got {v:?}")
    };
    let values = elems
        .iter()
        .map(|e| {
            let i = e.as_int().expect("a tensor element is an integer");
            if i.signed {
                i.as_signed()
            } else {
                i128::try_from(i.as_unsigned()).expect("a test element fits i128")
            }
        })
        .collect();
    ((**elem).clone(), dims.clone(), values)
}

fn tensor_verdict(v: &InterpretValue) -> Verdict {
    let (Ty::Tensor(elem, _), InterpretValueKind::Tensor { dims, elems }) = (&v.ty, &v.kind) else {
        return Verdict::Other(format!("not a tensor: {v:?}"));
    };
    Verdict::Tensor {
        elem: semr_int_code(elem),
        dims: dims.clone(),
        residues: elems
            .iter()
            .map(|e| e.as_int().expect("a tensor element is an integer").raw)
            .collect(),
    }
}

/// An argument as `semr_eval` reads it: a tensor as `t<element code>:<element
/// source bits>:<extents>:<residues>` (an empty tensor states its type's
/// reference width), an integer as `i<code>:<bits>:<raw>`, a Bool as `b0` or
/// `b1` (trust-ir's `lean_exec_differential` spelling).
fn semr_arg(v: &InterpretValue) -> String {
    match &v.kind {
        InterpretValueKind::Int(i) => format!("i{}:{}:{}", semr_int_code(&v.ty), i.bits, i.raw),
        InterpretValueKind::Bool(b) => if *b { "b1" } else { "b0" }.to_string(),
        InterpretValueKind::Tensor { dims, elems } => {
            let Ty::Tensor(elem, _) = &v.ty else {
                panic!("a tensor value has a tensor type, got {v:?}")
            };
            let ints: Vec<_> =
                elems.iter().map(|e| e.as_int().expect("a tensor element is an integer")).collect();
            let bits = ints.first().map_or_else(
                || elem.bit_width_with(64).expect("an integer element has a width"),
                |i| i.bits,
            );
            assert!(
                ints.iter().all(|i| i.bits == bits),
                "a tensor's elements share one width: {v:?}"
            );
            let dims: Vec<String> = dims.iter().map(u64::to_string).collect();
            let residues: Vec<String> = ints.iter().map(|i| i.raw.to_string()).collect();
            format!("t{}:{bits}:{}:{}", semr_int_code(elem), dims.join(","), residues.join(","))
        }
        other => panic!("no SemR spelling for {other:?}"),
    }
}

fn semr_verdict(line: &str) -> Verdict {
    use serde_json::Value;
    let other = || Verdict::Other(line.to_string());
    let Ok(j) = serde_json::from_str::<Value>(line) else {
        return other();
    };
    if let Some(message) = j.get("ub").and_then(Value::as_str) {
        return Verdict::Ub(message.to_string());
    }
    let Some([returned]) = j.get("ok").and_then(Value::as_array).map(Vec::as_slice) else {
        return other();
    };
    let Some(t) = returned.get("tensor") else {
        return other();
    };
    let dims = t["dims"]
        .as_array()
        .and_then(|ds| ds.iter().map(Value::as_u64).collect::<Option<Vec<u64>>>());
    let residues = t["elems"].as_array().and_then(|xs| {
        xs.iter()
            .map(|x| x.as_str().and_then(|s| s.parse::<u128>().ok()))
            .collect::<Option<Vec<u128>>>()
    });
    match (t["elem"].as_u64().and_then(|e| u32::try_from(e).ok()), dims, residues) {
        (Some(elem), Some(dims), Some(residues)) => Verdict::Tensor { elem, dims, residues },
        _ => other(),
    }
}

// ───────────────────────────── the differential ─────────────────────────────

/// The runs of one module: each run's interpreter verdict, kept for SemR.
pub struct Differential<'m> {
    module: &'m Module,
    runs: Vec<(String, Vec<InterpretValue>, Verdict)>,
}

impl<'m> Differential<'m> {
    /// No runs yet. The module must validate.
    ///
    /// # Panics
    ///
    /// When it does not.
    #[must_use]
    pub fn new(module: &'m Module) -> Self {
        assert_validates(module);
        Differential { module, runs: Vec::new() }
    }

    /// The module the runs are of.
    #[must_use]
    pub fn module(&self) -> &'m Module {
        self.module
    }

    /// Run `name` on `args` in the reference interpreter, which must return
    /// one integer tensor of the function's declared result type; record the
    /// run for SemR and return the tensor's element type, extents and
    /// elements (each the integer it denotes).
    ///
    /// # Panics
    ///
    /// On any interpreter error, or a result that is not one tensor of the
    /// declared type.
    pub fn computes(&mut self, name: &str, args: Vec<InterpretValue>) -> (Ty, Vec<u64>, Vec<i128>) {
        let f = function(self.module, name);
        let outcome = Interpreter::with_module(self.module)
            .execute_func(f.id, args.clone())
            .unwrap_or_else(|e| panic!("{name}: {e:?}"));
        let [result] = outcome.returns.as_slice() else {
            panic!("{name}: one return, got {:?}", outcome.returns);
        };
        let declared = &self
            .module
            .func_type(f.ty)
            .unwrap_or_else(|| panic!("{name}: its function type is in the module"))
            .returns;
        assert_eq!(
            std::slice::from_ref(&result.ty),
            declared.as_slice(),
            "{name}: the result has the declared type"
        );
        let decoded = decode(result);
        self.runs.push((name.to_string(), args, tensor_verdict(result)));
        decoded
    }

    /// Run `name` on `args` in the reference interpreter, which must stop
    /// with undefined behaviour whose normative message is `message`; record
    /// the run for SemR, which must give the same message byte for byte.
    ///
    /// # Panics
    ///
    /// When the interpreter returns, or stops otherwise.
    pub fn ub(&mut self, name: &str, args: Vec<InterpretValue>, message: &str) {
        let f = function(self.module, name);
        let error =
            Interpreter::with_module(self.module).execute_func(f.id, args.clone()).expect_err(name);
        assert_eq!(
            (error.code, error.message.as_str()),
            (InterpretErrorCode::UndefinedBehavior, message),
            "{name}: undefined behaviour by its normative message"
        );
        self.runs.push((name.to_string(), args, Verdict::Ub(message.to_string())));
    }

    /// Every recorded run sent to SemR's `semr_eval` on the module's binary
    /// image, in one invocation; each verdict must equal the interpreter's.
    /// `scratch` is a directory the caller owns (an integration test's
    /// `CARGO_TARGET_TMPDIR`). `Err` when SemR was not run (no `lake` and
    /// Lean not required), which leaves the row unmet.
    ///
    /// # Panics
    ///
    /// On any disagreement, a failed SemR build or run, no recorded run, or
    /// a missing `lake` under `TRUST_IR_REQUIRE_LEAN=1`.
    pub fn semr(self, scratch: &Path) -> Result<Agreement, Skipped> {
        assert!(!self.runs.is_empty(), "a row sends at least one run to SemR");
        let exe = semr_eval()?;
        let blob =
            trust_ir::binary::serialize_module(self.module).expect("the module has a wire image");
        let dir = Scratch::new(scratch, &self.module.name);
        let blob_path = dir.path("module.tmbc");
        let runs_path = dir.path("runs.txt");
        std::fs::write(&blob_path, &blob).expect("write the SemR blob");
        let mut lines = String::new();
        for (name, args, _) in &self.runs {
            let func: FuncId = function(self.module, name).id;
            lines.push_str(&format!("{SEMR_FUEL} {SEMR_CALL_DEPTH} {}", func.index()));
            for arg in args {
                lines.push(' ');
                lines.push_str(&semr_arg(arg));
            }
            lines.push('\n');
        }
        std::fs::write(&runs_path, lines.as_bytes()).expect("write the SemR runs");
        let out = Command::new(&exe)
            .arg(&blob_path)
            .arg(&runs_path)
            .output()
            .unwrap_or_else(|e| panic!("cannot run {}: {e}", exe.display()));
        drop(dir);
        assert!(
            out.status.success(),
            "semr_eval exited with {}:\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
        let text = String::from_utf8_lossy(&out.stdout);
        let verdicts: Vec<Verdict> = text.lines().map(semr_verdict).collect();
        assert_eq!(verdicts.len(), self.runs.len(), "one SemR verdict per run:\n{text}");
        let mut agreement = Agreement::default();
        for ((name, args, want), got) in self.runs.iter().zip(&verdicts) {
            assert_eq!(got, want, "SemR on {name} {args:?}");
            agreement.runs += 1;
            if matches!(want, Verdict::Ub(_)) {
                agreement.ub += 1;
            }
        }
        Ok(agreement)
    }
}

/// How many runs SemR agreed on, of them how many undefined behaviour.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Agreement {
    pub runs: usize,
    pub ub: usize,
}

/// Why SemR did not run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Skipped(pub String);

// ───────────────────────────── the row ─────────────────────────────

/// One ledger row's run: its checks in order, then [`Row::finish`].
pub struct Row {
    id: &'static str,
    checks: usize,
}

impl Row {
    /// The row `id` (its ledger id, e.g. `logical-ir-shapes/gather`).
    #[must_use]
    pub fn new(id: &'static str) -> Self {
        println!("luminal row {id}");
        Row { id, checks: 0 }
    }

    /// Run one named check; a failure panics, which ends the process before
    /// the pass line.
    pub fn check(&mut self, name: &str, f: impl FnOnce()) {
        f();
        self.checks += 1;
        println!("  check {name}: ok");
    }

    /// The row's last line: the pass line when SemR agreed on every run,
    /// else a `SKIPPED:` line that says the row is not met by this run.
    ///
    /// # Panics
    ///
    /// When no check ran.
    pub fn finish(self, semr: Result<Agreement, Skipped>) {
        assert!(self.checks > 0, "a row runs at least one check");
        match semr {
            Ok(a) => {
                println!(
                    "  SemR's semr_eval agreed with the reference interpreter on {} runs of the \
                     module's binary image ({} undefined behaviour by the byte-identical \
                     normative message, {} tensors)",
                    a.runs,
                    a.ub,
                    a.runs - a.ub
                );
                println!("LUMINAL-ROW {} PASS", self.id);
            }
            Err(Skipped(why)) => {
                println!("SKIPPED: {why}; row {} is not met by this run", self.id);
            }
        }
        std::io::stdout().flush().expect("flush stdout");
    }
}

// ───────────────────────────── SemR ─────────────────────────────

/// Fuel and call depth for each SemR run (trust-ir's differential's).
const SEMR_FUEL: u64 = 10_000;
const SEMR_CALL_DEPTH: u64 = 64;

/// trust-ir's SemR package at Trust's `first-party/trust-ir` pin.
fn semr_package() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../first-party/trust-ir/lean/semr")
}

/// The Lake that builds SemR: `TRUST_IR_SEMR_LAKE`, `TRUST_IR_LAKE`, elan's
/// shim, then `PATH` (the order of trust-ir's SemR tests).
fn lake() -> Option<PathBuf> {
    if let Some(explicit) = std::env::var_os("TRUST_IR_SEMR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(explicit) = std::env::var_os("TRUST_IR_LAKE") {
        return Some(explicit.into());
    }
    if let Some(home) = std::env::var_os("HOME") {
        let shim = Path::new(&home).join(".elan/bin/lake");
        if shim.is_file() {
            return Some(shim);
        }
    }
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|directory| directory.join("lake"))
        .find(|candidate| candidate.is_file())
}

/// Build `semr_eval` with the package's pinned Lean and return its path, or
/// `Err` when no Lake exists and Lean is not required.
fn semr_eval() -> Result<PathBuf, Skipped> {
    let Some(lake) = lake() else {
        assert_ne!(
            std::env::var("TRUST_IR_REQUIRE_LEAN").as_deref(),
            Ok("1"),
            "TRUST_IR_REQUIRE_LEAN=1 but no lake builds first-party/trust-ir/lean/semr"
        );
        return Err(Skipped(
            "the SemR half needs lake (TRUST_IR_SEMR_LAKE, TRUST_IR_LAKE, \
             $HOME/.elan/bin/lake, PATH); the interpreter half ran"
                .to_string(),
        ));
    };
    let package = semr_package();
    assert!(
        package.join("lakefile.lean").is_file(),
        "no SemR package at {}: is first-party/trust-ir checked out?",
        package.display()
    );
    let mut command = Command::new(&lake);
    command.current_dir(&package).env_remove("SDKROOT");
    if let Some(bin) = lake.parent() {
        let mut path = bin.as_os_str().to_os_string();
        path.push(":");
        path.push(std::env::var_os("PATH").unwrap_or_default());
        command.env("PATH", path);
    }
    let out = command
        .args(["build", "semr_eval"])
        .output()
        .unwrap_or_else(|e| panic!("run {} build semr_eval: {e}", lake.display()));
    assert!(
        out.status.success(),
        "`lake build semr_eval` failed in {}:\n{}{}",
        package.display(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let exe = package.join(".lake/build/bin/semr_eval");
    assert!(exe.is_file(), "lake reported success but {} is missing", exe.display());
    Ok(exe)
}

/// A scratch directory unique to this process and call under the caller's
/// directory, removed when the guard drops, on a panic too.
struct Scratch(PathBuf);

impl Scratch {
    fn new(root: &Path, label: &str) -> Self {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let call = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = root.join(format!("luminal-row-semr-{label}-{}-{call}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap_or_else(|e| panic!("scratch {}: {e}", dir.display()));
        Scratch(dir)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
