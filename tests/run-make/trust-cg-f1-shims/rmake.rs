//! Trust (step 2 increment 4d, sub-step 4d.0a; docs/design/2026-10-08-step2-inc4d-shims-plan.md
//! §1(a), docs/design/2026-09-29-step2-inc4-drops.md §5 and §7.4): THE OTHER SHIMS, PINNED AS
//! MEASURED. One subject crate per shim class (the F1 refusal census prints at most three
//! samples per class), each compiled five ways:
//!
//! * PART A — probe channel C (`-Ztrust-instance-flip-probe=*`): every `kind=shim-<k>` row is
//!   `route=mir result=residue` with no `glue=` column (no source-first producer exists for a
//!   shim; the probe runs no MIR-derived producer for it). 4d.1 adds a `shim=` column.
//! * PART A′ — trust-cg's MIR frontend (`-Ztrust-cg-frontend=mir`, the default and the shipped
//!   path), the R-8 baseline and the evidence of the R-2 residual that frontend carries: it takes
//!   every inventory item, shims included, through `tcx.instance_mir` with no `InstanceKind`
//!   filter. MEASURED on these subjects: no subject compiles there and no object is written, so no
//!   shim symbol is defined; the frontend stops, fail-closed, at the first item it cannot extract
//!   or admit, which is sometimes the shim itself (refused by that frontend's ABI admission,
//!   e.g. `TRACK_CALLER` for the reified `#[track_caller]` item) and otherwise a caller. Which
//!   item is first follows the codegen unit's item order, so only the outcome is pinned; the
//!   control (`control.rs`) ships and defines its symbol, so the outcome check is not vacuous.
//! * PART B — F1 (`-Ztrust-cg-frontend=trust-ir`) under the default strict output gate: the shim
//!   is refused `[synthesized-instance]` naming `Shim(<Kind>(..))`, and each caller's class and
//!   detail are pinned as measured. The instance lane's own reason is not in the census (its
//!   refusal is `ProducerDeclined`), so PART B′ pins the producer's per-body tags for the callers
//!   from the trust-ir coverage artifact.
//! * PART C — F1 with verification off under `-Ztrust-cg-output-gate=allow-unknown` (really
//!   allow-unknown only with verification off). The shim lines are unchanged; what changes is
//!   that a GENERIC caller is refused by D17's rule (a generic instance is admitted only under the
//!   strict gate) instead of by the instance lane, and the inactive glue lane leaves a coroutine's
//!   glue a plain `Shim(DropGlue(..))`.
//!
//! * PART D — F1's compiler lane (`-Ztrust-cg-f1-backend=compiler`, step 5.4.2's
//!   `select_for_codegen_module`) under the strict gate: every subject is refused there exactly
//!   as on the LIR lane (the same `refused N of M`, classes and printed samples), except the
//!   coroutine's glue, which that lane does not license (`[unlicensed-body]`, INC5.4-GLUE, owner
//!   ruling D31(a)); `thread_local` fatals on its static first there too. No rlib is written.
//!
//! What flips each pin: 4d.1 (the `shim=` column of Part A), 4d.3 (Part B's `Shim(Clone(()))`,
//! then each kind as its row of plan §6 lands; Part D with it, as the lane licenses each).
//!
//! Measured first on a stage 1 of main `7400e00495` (2026-10-08); every expectation below is that
//! measurement, except the earlier source refusals explicitly pinned in `clone_unit` and
//! `clone_closure`. Part D was added at the landing, 2026-10-14, after 5.4.2 merged (main
//! `2e45dc94e1`), measured on a stage 1 of main `277e263c33` and run on the landing's merge. A
//! subject that stops producing its shim is changed, never the assertion.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use std::collections::BTreeMap;
use std::path::Path;

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{File, Object, ObjectSymbol};
use run_make_support::{rfs, rust_lib_name, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

// ── PART A: probe channel C ──────────────────────────────────────────────────────────────────

/// One `TRUST-WALLA-PROBE C sym=` row. `def` is everything after ` def=` (the def path and the
/// args); `columns` the optional columns between the result and it.
#[derive(Debug)]
struct Row {
    sym: String,
    kind: String,
    local: String,
    route: String,
    result: String,
    columns: String,
    def: String,
}

fn channel_c(input: &str) -> Vec<Row> {
    let stderr = rustc()
        .input(input)
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Cpanic=abort")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .out_dir(format!("probe-{}", stem(input)))
        .run()
        .stderr_utf8();
    assert!(stderr.contains("TRUST-WALLA-PROBE C summary"), "channel C ran:\n{stderr}");
    stderr
        .lines()
        .filter_map(|line| line.strip_prefix("TRUST-WALLA-PROBE C sym="))
        .map(|rest| {
            let field = |text: &str, key: &str| -> (String, String) {
                let at =
                    text.find(&format!(" {key}=")).unwrap_or_else(|| panic!("`{key}`: {text}"));
                (text[..at].to_string(), text[at + key.len() + 2..].to_string())
            };
            let (sym, rest) = field(rest, "kind");
            let (kind, rest) = field(&rest, "local");
            let (local, rest) = field(&rest, "route");
            let (route, rest) = field(&rest, "result");
            let (head, def) = field(&rest, "def");
            // The result runs to the first optional column (a result can contain spaces).
            let cut = ["drops=", "glue=", "shim=", "rmeta="]
                .iter()
                .filter_map(|key| head.find(&format!(" {key}")))
                .min()
                .unwrap_or(head.len());
            Row {
                sym,
                kind,
                local,
                route,
                result: head[..cut].to_string(),
                columns: head[cut..].trim().to_string(),
                def,
            }
        })
        .collect()
}

fn stem(input: &str) -> &str {
    input.strip_suffix(".rs").expect("a .rs subject")
}

/// The subject's shim rows, each checked to be residue on the MIR route with no glue or shim
/// column unless it is drop glue.
fn shim_rows(rows: &[Row]) -> Vec<&Row> {
    let shims: Vec<&Row> = rows.iter().filter(|r| r.kind.starts_with("shim-")).collect();
    for row in &shims {
        assert_eq!((row.route.as_str(), row.result.as_str()), ("mir", "residue"), "{row:?}");
        assert!(!row.columns.contains("shim="), "no shim column before 4d.1: {row:?}");
        if row.kind != "shim-drop-glue" {
            assert!(row.columns.is_empty(), "a non-glue shim has no column: {row:?}");
        }
    }
    shims
}

/// The one shim row of `kind` whose `def` text starts with `def` and contains `args`.
fn shim<'a>(rows: &[&'a Row], kind: &str, def: &str, args: &str) -> &'a Row {
    let found: Vec<&&Row> = rows
        .iter()
        .filter(|r| r.kind == kind && r.def.starts_with(def) && r.def.contains(args))
        .collect();
    assert_eq!(found.len(), 1, "one `{kind}` row `{def}` `{args}`: {rows:#?}");
    *found[0]
}

// ── PARTS A′, B, C: trust-cg ─────────────────────────────────────────────────────────────────

/// `tests/run-make/trust-cg-f1-drop-glue`'s `f1()` flags; the MIR frontend takes
/// `-Ztrust-cg-frontend=mir` in place of `trust-ir` and drops `-Ztrust-ir-lower`.
fn trust_cg(input: &str, out: &str, frontend: &str, extra: &[&str]) -> run_make_support::Rustc {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input(input)
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-verify=off");
    if frontend == "trust-ir" {
        cmd.arg("-Ztrust-ir-lower");
    }
    cmd.arg(format!("-Ztrust-cg-frontend={frontend}"))
        .args(extra)
        .out_dir(out)
        .env_remove(TRUST_NO_VERIFY_ENV);
    cmd
}

/// The F1 refusal census of a refused compile: `refused N of M`, each class's count, and every
/// printed sample with its class.
#[derive(Debug)]
struct Census {
    refused: (usize, usize),
    classes: BTreeMap<String, usize>,
    samples: Vec<(String, String)>,
}

fn census(stderr: &str) -> Census {
    let head = stderr
        .split("-Ztrust-cg-frontend=trust-ir refused ")
        .nth(1)
        .unwrap_or_else(|| panic!("no refusal census:\n{stderr}"));
    let mut numbers = head.split_whitespace();
    let refused: usize = numbers.next().and_then(|n| n.parse().ok()).expect("refused");
    assert_eq!(numbers.next(), Some("of"));
    let reachable: usize = numbers.next().and_then(|n| n.parse().ok()).expect("reachable");
    let mut classes = BTreeMap::new();
    let mut samples = Vec::new();
    let mut class = String::new();
    for line in stderr.lines().map(str::trim) {
        if let (Some(open), true) = (line.find("%)  ["), line.ends_with(']')) {
            let count = line.split_whitespace().next().and_then(|n| n.parse().ok()).expect("count");
            class = line[open + 5..line.len() - 1].to_string();
            classes.insert(class.clone(), count);
        } else if let Some(sample) = line.strip_prefix("e.g. ") {
            samples.push((class.clone(), sample.to_string()));
        }
    }
    assert_eq!(classes.values().sum::<usize>(), refused, "{stderr}");
    Census { refused: (refused, reachable), classes, samples }
}

impl Census {
    fn classes(&self) -> Vec<(&str, usize)> {
        self.classes.iter().map(|(class, n)| (class.as_str(), *n)).collect()
    }

    /// The one sample whose leading symbol satisfies `pick`, as (class, text).
    fn sample(&self, what: &str, pick: impl Fn(&str) -> bool) -> (&str, &str) {
        let found: Vec<&(String, String)> = self
            .samples
            .iter()
            .filter(|(_, text)| text.split('`').nth(1).is_some_and(&pick))
            .collect();
        assert_eq!(found.len(), 1, "one sample for {what}: {:#?}", self.samples);
        (found[0].0.as_str(), found[0].1.as_str())
    }

    /// Every printed sample of `class`.
    fn of(&self, class: &str) -> Vec<&str> {
        self.samples.iter().filter(|(c, _)| c == class).map(|(_, t)| t.as_str()).collect()
    }
}

/// Symbol predicates (v0 mangling; no crate hash, which moves with the compiler).
fn item(name: &str) -> impl Fn(&str) -> bool + '_ {
    move |sym| sym.starts_with("_RNvCs") && sym.ends_with(&format!("{}{name}", name.len()))
}
fn generic(name: &str) -> impl Fn(&str) -> bool + '_ {
    move |sym| sym.starts_with("_RINvCs") && sym.contains(&format!("{}{name}", name.len()))
}
fn closure_in(name: &str) -> impl Fn(&str) -> bool + '_ {
    move |sym| sym.starts_with("_RNCNvCs") && sym.contains(&format!("{}{name}0", name.len()))
}
fn exactly(symbol: &str) -> impl Fn(&str) -> bool + '_ {
    move |sym| sym == symbol
}

/// The sample's refusal is the producer's coverage refusal. Since fe91162869
/// `ProducerDeclined` carries the first unsupported tag, so the census line
/// ends `ProducerDeclined("<tag>")`, not the bare variant name this pin was
/// written against (the ends-with-bare-name form is unsatisfiable on main
/// too; the tag is the producer's diagnosis and stays unpinned here).
fn producer_declined(text: &str) -> bool {
    text.contains(": ProducerDeclined(\"") && text.ends_with("\")")
}
const HANDOFF_ABSENT: &str = "` = DefIndex(";
/// A local closure instance. Since 2dc38fb191 (the exact typed FnOnce source handoff) a local
/// closure is routed to that checked source route before the instance lane's item-kind check,
/// which admits only a concrete CAPTURING by-value FnOnce; every `Fn` closure here is refused there
/// (before: "is a Closure; the instance lane splices only fn and associated-fn items").
const A_CLOSURE: &str = "only a capturing FnOnce value has the typed source environment convention";
/// The same route refuses a coroutine body before any environment check.
const A_COROUTINE: &str = "requires a concrete non-coroutine source closure";
const REIFY_ONLY: &str = "no call site binds the result (a reify-only edge)";
const D17_GENERIC: &str =
    "is a generic instance body; owner ruling D17 admits one only under the STRICT";
/// An upstream item. Since a4e15ca586 (the sealed level-R upstream importer) the assembler sends
/// every one through `upstream_entry::admit`: under the strict gate core's items are
/// `[upstream-body]` with the importer's `absent` refusal (core has no Trust-IR producer), and
/// under `allow-unknown` the importer's D17/D39 strict condition refuses first, `[upstream-entry]`
/// (before: `[upstream-body]` on both lanes, "... is an upstream body ... = <name>").
const UPSTREAM_STRICT: (&str, &str) =
    ("upstream-body", "absent: upstream crate was compiled without the Trust-IR producer");
const UPSTREAM_RELAXED: (&str, &str) =
    ("upstream-entry", "strict: D17/D39 admits upstream bodies only under the strict output gate");

/// F1's compiler lane (step 5.4.2): `-Ztrust-cg-f1-backend=compiler`.
const COMPILER_LANE: &str = "-Ztrust-cg-f1-backend=compiler";

/// Part B (strict) and Part C (allow-unknown) of one subject, with Part D checked: on F1's
/// compiler lane the strict compile refuses the same functions with the same classes and the
/// same printed samples ([`same_on_the_compiler_lane`]).
fn f1_both(input: &str) -> (Census, Census) {
    let (strict, relaxed, compiler) = f1_all(input);
    same_on_the_compiler_lane(input, &strict, &compiler);
    (strict, relaxed)
}

/// Part B, Part C and Part D's census of one subject: strict, allow-unknown, and strict on F1's
/// compiler lane.
fn f1_all(input: &str) -> (Census, Census, Census) {
    let s = stem(input);
    let strict = trust_cg(input, &format!("f1-strict-{s}"), "trust-ir", &[]).run_fail();
    let relaxed = trust_cg(
        input,
        &format!("f1-allow-{s}"),
        "trust-ir",
        &["-Ztrust-cg-output-gate=allow-unknown"],
    )
    .run_fail();
    let compiler =
        trust_cg(input, &format!("f1-compiler-{s}"), "trust-ir", &[COMPILER_LANE]).run_fail();
    for out in [&strict, &relaxed, &compiler] {
        out.assert_not_ice();
    }
    let compiler = compiler.stderr_utf8();
    assert!(!Path::new(&format!("f1-compiler-{s}")).join(rust_lib_name(s)).exists(), "{s}");
    (census(&strict.stderr_utf8()), census(&relaxed.stderr_utf8()), census(&compiler))
}

/// PART D: the compiler lane selects through `select_for_codegen_module` and refuses exactly
/// what F1's LIR lane refuses: the same `refused N of M`, the same classes and counts, and the
/// same printed samples (class and text).
fn same_on_the_compiler_lane(input: &str, lir: &Census, compiler: &Census) {
    assert_eq!(compiler.refused, lir.refused, "{input}: the same functions are refused");
    assert_eq!(compiler.classes(), lir.classes(), "{input}: the same classes");
    let sorted = |census: &Census| {
        let mut samples = census.samples.clone();
        samples.sort();
        samples
    };
    assert_eq!(sorted(compiler), sorted(lir), "{input}: the same printed samples");
}

/// The shim's own refusal in a census: `[synthesized-instance]`, naming its kind.
fn shim_refused(census: &Census, row: &Row, needle: &str) {
    let (class, text) = census.sample("the shim", exactly(&row.sym));
    assert_eq!(class, "synthesized-instance", "{text}");
    assert!(text.contains(needle), "the shim's refusal names `{needle}`: {text}");
}

// ── PART A′: trust-cg's MIR frontend ─────────────────────────────────────────────────────────

/// The symbols the rlib's one object defines.
fn defined_symbols(rlib: &str) -> Vec<String> {
    let data = rfs::read(rlib);
    let archive = ArchiveFile::parse(&*data).expect("rlib is an archive");
    let mut objects = Vec::new();
    for member in archive.members() {
        let member = member.expect("archive member");
        if member.name().ends_with(b".o") {
            objects.push(member.data(&*data).expect("member data").to_vec());
        }
    }
    assert_eq!(objects.len(), 1, "one codegen unit, one object");
    let object = File::parse(&*objects[0]).expect("the trust-cg object");
    object
        .symbols()
        .filter(|symbol| symbol.is_definition())
        .filter_map(|symbol| symbol.name().ok().map(str::to_string))
        .collect()
}

/// Part A′ for a subject: refused fail-closed, no object written, so no shim symbol defined.
fn mir_frontend_refuses(input: &str) {
    let s = stem(input);
    let out = format!("mir-{s}");
    let refused = trust_cg(input, &out, "mir", &[]).run_fail();
    refused.assert_not_ice();
    let stderr = refused.stderr_utf8();
    assert!(
        stderr.contains("trust-cg cannot faithfully materialize rustc's reachable mono-item graph"),
        "{s}: the MIR frontend refuses the unit:\n{stderr}"
    );
    assert!(!Path::new(&out).join(rust_lib_name(s)).exists(), "{s}: no rlib is written");
}

// ── PART B′: the producer's own tags for the callers ─────────────────────────────────────────

/// The analysis-time producer's coverage rows (`--emit=trust-ir`), by def path: (lowered,
/// symbolic, splice refusal, unsupported tags).
fn coverage(input: &str) -> BTreeMap<String, (bool, bool, String, Vec<String>)> {
    let s = stem(input);
    let out = format!("cov-{s}");
    rustc()
        .input(input)
        .crate_type("lib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("--emit=trust-ir,metadata")
        .out_dir(&out)
        .run();
    let text = rfs::read_to_string(format!("{out}/{s}.trust-ir.coverage.json"));
    let json: serde_json::Value = serde_json::from_str(&text).expect("coverage JSON");
    let mut rows = BTreeMap::new();
    for body in json["bodies"].as_array().expect("bodies") {
        let tags = body["unsupported"]
            .as_array()
            .map(|tags| tags.iter().filter_map(|t| t[0].as_str().map(str::to_string)).collect())
            .unwrap_or_default();
        rows.insert(
            body["def_path"].as_str().expect("def_path").to_string(),
            (
                body["lowered"].as_bool().unwrap_or(false),
                body["symbolic"].as_bool().unwrap_or(false),
                body["splice_refusal"].as_str().unwrap_or("").to_string(),
                tags,
            ),
        );
    }
    rows
}

fn main() {
    // ── Part A′'s control: the MIR frontend ships a shim-free body and its symbol is defined ──
    trust_cg("control.rs", "mir-control", "mir", &[]).run();
    let control = defined_symbols(&format!("mir-control/{}", rust_lib_name("control")));
    assert!(control.iter().any(|s| s.ends_with("ctl")), "the control's symbol: {control:?}");
    for subject in [
        "clone_unit.rs",
        "clone_tuple.rs",
        "clone_closure.rs",
        "clone_fn_def.rs",
        "closure_once.rs",
        "dyn_fn.rs",
        "fn_ptr_item.rs",
        "fn_ptr_ptr.rs",
        "reify_track_caller.rs",
        "reify_virtual.rs",
        "fn_ptr_addr.rs",
        "ctor_value.rs",
        "coroutine.rs",
        "thread_local.rs",
        "drop_glue_none.rs",
    ] {
        mir_frontend_refuses(subject);
    }

    clone_unit();
    clone_tuple();
    clone_closure();
    clone_fn_def();
    closure_once();
    dyn_fn();
    fn_ptr_item();
    fn_ptr_ptr();
    reify_track_caller();
    reify_virtual();
    fn_ptr_addr();
    ctor_value();
    coroutine();
    thread_local();
    drop_glue_none();
}

/// `Shim(Clone(()))`, the 4d.3 plumbing subject (flips at 4d.3).
fn clone_unit() {
    let rows = channel_c("clone_unit.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let unit = shim(&shims, "shim-clone", "std::clone::Clone::clone", "args=[()]");
    let (strict, relaxed) = f1_both("clone_unit.rs");
    assert_eq!(strict.refused, (3, 3));
    assert_eq!(
        strict.classes(),
        [("producer-declined", 2), ("synthesized-instance", 1)]
    );
    shim_refused(&strict, unit, "Shim(Clone(");
    let (class, text) = strict.sample("dup::<()>", generic("dup"));
    assert_eq!(class, "producer-declined");
    assert!(text.contains("instance producer refused") && producer_declined(text));
    let (class, text) = strict.sample("run", item("run"));
    assert_eq!(class, "producer-declined");
    assert!(text.contains(HANDOFF_ABSENT), "{text}");
    // Allow-unknown: the shim line is the same; the generic caller falls to D17's rule.
    assert_eq!(relaxed.refused, (3, 3));
    assert_eq!(
        relaxed.classes(),
        [("instance-assembly", 1), ("producer-declined", 1), ("synthesized-instance", 1)]
    );
    shim_refused(&relaxed, unit, "Shim(Clone(");
    let (_, text) = relaxed.sample("dup::<()>", generic("dup"));
    assert!(text.contains(D17_GENERIC), "{text}");
    let (class, text) = relaxed.sample("run", item("run"));
    assert_eq!(class, "producer-declined");
    assert!(text.contains(HANDOFF_ABSENT), "{text}");
    // The stable-address fence refuses `&u` before callee assembly: this unit
    // local has no admitted slot, and a fresh snapshot would lose place identity.
    // Keep the exact source diagnosis beside the unchanged shim/D17 refusals.
    let cov = coverage("clone_unit.rs");
    assert_eq!(cov.len(), 2, "both source functions remain in the producer census");
    assert_eq!(cov["dup"].2, "Splice(symbolic body)");
    assert!(cov["dup"].1);
    assert!(!cov["run"].0 && !cov["run"].1);
    assert_eq!(cov["run"].2, "");
    assert_eq!(
        cov["run"].3,
        ["Borrow(shared local lacks stable storage)", "Call(unsupported arg)"]
    );
}

/// `Shim(Clone(<tuple>))` at `(u64,)` (the first E5 candidate), `(u64, u64)`, `(u64, L)` and
/// `(i32, i32)` reified. Four shims: the census prints three samples per class, so this subject
/// pins counts.
fn clone_tuple() {
    let rows = channel_c("clone_tuple.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 4, "{shims:#?}");
    for args in ["args=[(u64,)]", "args=[(u64, u64)]", "args=[(u64, L)]", "args=[(i32, i32)]"] {
        shim(&shims, "shim-clone", "std::clone::Clone::clone", args);
    }
    let (strict, relaxed) = f1_both("clone_tuple.rs");
    assert_eq!(strict.refused, (12, 12));
    // The derived `<L as Clone>::clone` calls core's `<u64 as Clone>::clone`, an upstream item:
    // the caller's row carries the importer's refusal of that callee (`UPSTREAM_STRICT` /
    // `UPSTREAM_RELAXED`; before a4e15ca586 both were `[instance-assembly]`, "is an upstream
    // body ... (increment 6)").
    let l_clone = |sym: &str| {
        sym.starts_with("_RNvXCs")
            && sym.contains("_11clone_tupleNtB2_1L")
            && sym.ends_with("5cloneB2_")
    };
    assert_eq!(
        strict.classes(),
        [
            ("instance-assembly", 3),
            ("producer-declined", 4),
            ("synthesized-instance", 4),
            ("upstream-body", 1)
        ]
    );
    let (class, text) = strict.sample("<L as Clone>::clone", l_clone);
    assert_eq!((class, text.contains(UPSTREAM_STRICT.1)), (UPSTREAM_STRICT.0, true), "{text}");
    for census in [&strict, &relaxed] {
        let shown = census.of("synthesized-instance");
        assert_eq!(shown.len(), 3, "three of four samples: {shown:#?}");
        assert!(shown.iter().all(|t| t.contains("= Shim(Clone(")), "{shown:#?}");
    }
    assert_eq!(
        relaxed.classes(),
        [
            ("instance-assembly", 6),
            ("producer-declined", 1),
            ("synthesized-instance", 4),
            ("upstream-entry", 1)
        ]
    );
    let (class, text) = relaxed.sample("<L as Clone>::clone", l_clone);
    assert_eq!((class, text.contains(UPSTREAM_RELAXED.1)), (UPSTREAM_RELAXED.0, true), "{text}");
    let (class, text) = relaxed.sample("as_value", item("as_value"));
    assert_eq!(class, "producer-declined");
    assert!(text.contains(HANDOFF_ABSENT), "{text}");
    // The reified value use is the producer's `Reify(instance shim)`.
    let cov = coverage("clone_tuple.rs");
    assert_eq!(cov["as_value"].3, ["Reify(instance shim)"]);
    assert!(!cov["as_value"].0);
}

/// `Shim(Clone(<closure>))` over a one-capture closure (the second E5 candidate).
fn clone_closure() {
    let rows = channel_c("clone_closure.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let clone = shim(&shims, "shim-clone", "std::clone::Clone::clone", "::run::{closure#0})");
    assert!(clone.def.contains("args=[Closure(DefId("), "{clone:?}");
    let (strict, relaxed) = f1_both("clone_closure.rs");
    // Since cbe8659343 (one typed environment slot for an admitted Fn/FnMut closure, "independent
    // copied closures") the producer lowers `run`'s call `d()` of the CLONED capturing closure, so
    // `run` is no longer producer-declined: it reaches assembly and is refused through its callee
    // `dup::<closure>` (before: `[producer-declined]`, `Call(closure env unsupported)`).
    assert_eq!(strict.refused, (4, 4));
    assert_eq!(
        strict.classes(),
        [("instance-assembly", 2), ("producer-declined", 1), ("synthesized-instance", 1)]
    );
    shim_refused(&strict, clone, "Shim(Clone(");
    let (class, text) = strict.sample("the closure", closure_in("run"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains(A_CLOSURE), "{text}");
    let (class, text) = strict.sample("dup::<closure>", generic("dup"));
    assert_eq!(class, "producer-declined");
    assert!(producer_declined(text), "{text}");
    let (class, text) = strict.sample("run", item("run"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains("'s callee `") && producer_declined(text), "{text}");
    assert_eq!(relaxed.refused, (4, 4));
    assert_eq!(relaxed.classes(), [("instance-assembly", 3), ("synthesized-instance", 1)]);
    shim_refused(&relaxed, clone, "Shim(Clone(");
    let (class, text) = relaxed.sample("dup::<closure>", generic("dup"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains(D17_GENERIC), "{text}");
    let (class, text) = relaxed.sample("the closure", closure_in("run"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains(A_CLOSURE), "{text}");
    let (class, text) = relaxed.sample("run", item("run"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains("'s callee `") && text.contains(D17_GENERIC), "{text}");
    // `run`, the generic function and the closure all lower; only `dup` is a symbolic splice.
    let cov = coverage("clone_closure.rs");
    assert_eq!(cov.len(), 3, "the caller, generic function and closure remain in the census");
    assert!(cov["dup"].0 && cov["dup"].1);
    assert_eq!(cov["dup"].2, "Splice(symbolic body)");
    assert!(cov["run"].0 && !cov["run"].1);
    assert_eq!(cov["run"].2, "");
    assert!(cov["run"].3.is_empty());
    assert!(cov["run::{closure#0}"].0 && !cov["run::{closure#0}"].1);
    assert_eq!(cov["run::{closure#0}"].2, "");
    assert!(cov["run::{closure#0}"].3.is_empty());
}

/// `Shim(Clone(<fn item>))`: its callers touch a fn-item value, which the producer spells
/// symbolically (INC4D-FNDEF).
fn clone_fn_def() {
    let rows = channel_c("clone_fn_def.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let clone = shim(&shims, "shim-clone", "std::clone::Clone::clone", "args=[FnDef(DefId(");
    // 1.101 spelling: the FnDef arg's empty late-bound region list renders as
    // `Binder { value: [], bound_vars: [] }`, not the bare `[]`.
    assert!(clone.def.contains("::inc), Binder { value: [], bound_vars: [] })]"), "{clone:?}");
    let (strict, relaxed) = f1_both("clone_fn_def.rs");
    assert_eq!(strict.refused, (3, 4), "`inc` completes");
    assert_eq!(strict.classes(), [("producer-declined", 2), ("synthesized-instance", 1)]);
    shim_refused(&strict, clone, "Shim(Clone(");
    let is_w_clone = |sym: &str| sym.starts_with("_RNvXCs") && sym.contains("1WNv");
    let (class, text) = strict.sample("<W<inc> as Clone>::clone", is_w_clone);
    assert_eq!(class, "producer-declined");
    assert!(producer_declined(text), "{text}");
    let (class, text) = strict.sample("run", item("run"));
    assert_eq!(class, "producer-declined");
    assert!(text.contains(HANDOFF_ABSENT), "{text}");
    assert_eq!(
        relaxed.classes(),
        [("instance-assembly", 1), ("producer-declined", 1), ("synthesized-instance", 1)]
    );
    assert!(relaxed.sample("<W<inc> as Clone>::clone", is_w_clone).1.contains(D17_GENERIC));
    // The producer: both callers are symbolic (a fn item is `Ty::Unit` + `param_opaque`).
    let cov = coverage("clone_fn_def.rs");
    assert!(cov["run"].1 && !cov["run"].0, "{:?}", cov["run"]);
    let w_clone = &cov["<W<F> as std::clone::Clone>::clone"];
    assert!(w_clone.1, "{w_clone:?}");
    assert_eq!(w_clone.2, "Splice(symbolic body)");
}

/// `Shim(ClosureOnce { .. })`: an `Fn` closure called through `FnOnce::call_once`.
fn closure_once() {
    let rows = channel_c("closure_once.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let call_once = "std::ops::FnOnce::call_once";
    let once = shim(&shims, "shim-closure-once", call_once, "::run::{closure#0})");
    let (strict, relaxed) = f1_both("closure_once.rs");
    assert_eq!(strict.refused, (4, 4));
    assert_eq!(
        strict.classes(),
        [("instance-assembly", 2), ("producer-declined", 1), ("synthesized-instance", 1)]
    );
    shim_refused(&strict, once, "Shim(ClosureOnce { call_once:");
    assert!(strict.sample("the closure", closure_in("run")).1.contains(A_CLOSURE));
    let (class, text) = strict.sample("apply::<closure>", generic("apply"));
    assert_eq!(class, "producer-declined");
    assert!(producer_declined(text), "{text}");
    let (class, text) = strict.sample("run", item("run"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains("'s callee `") && producer_declined(text), "{text}");
    assert_eq!(relaxed.classes(), [("instance-assembly", 3), ("synthesized-instance", 1)]);
    shim_refused(&relaxed, once, "Shim(ClosureOnce { call_once:");
    assert!(relaxed.sample("apply::<closure>", generic("apply")).1.contains(D17_GENERIC));
}

/// `Shim(VTable(..))` and `Shim(ClosureOnce { .. })`: a `dyn Fn` vtable's `call_once` slot.
fn dyn_fn() {
    let rows = channel_c("dyn_fn.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 2, "{shims:#?}");
    let call_once = "std::ops::FnOnce::call_once";
    let vtable = shim(&shims, "shim-vtable", call_once, "::go::{closure#0})");
    let once = shim(&shims, "shim-closure-once", call_once, "::go::{closure#0})");
    let (strict, relaxed) = f1_both("dyn_fn.rs");
    for census in [&strict, &relaxed] {
        assert_eq!(census.refused, (5, 5));
        assert_eq!(
            census.classes(),
            [("instance-assembly", 1), ("producer-declined", 2), ("synthesized-instance", 2)]
        );
        shim_refused(census, vtable, "Shim(VTable(");
        shim_refused(census, once, "Shim(ClosureOnce { call_once:");
        assert!(census.sample("the closure", closure_in("go")).1.contains(A_CLOSURE));
        for caller in ["go", "run"] {
            let (class, text) = census.sample(caller, item(caller));
            assert_eq!(class, "producer-declined");
            assert!(text.contains(HANDOFF_ABSENT), "{text}");
        }
    }
    // The producer: the dyn call is `Call(dyn dispatch)`.
    let cov = coverage("dyn_fn.rs");
    assert_eq!(cov["run"].3, ["Call(dyn dispatch)"]);
}

/// `Shim(FnPtr(.., <fn item>))`: a fn item called through `Fn::call` (INC4D-FNDEF, rust-call).
fn fn_ptr_item() {
    let rows = channel_c("fn_ptr_item.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let call = shim(&shims, "shim-fn-ptr", "std::ops::Fn::call", "args=[FnDef(DefId(");
    assert!(call.def.contains("::inc), Binder { value: [], bound_vars: [] }), (u64,)]"), "{call:?}");
    let (strict, relaxed) = f1_both("fn_ptr_item.rs");
    assert_eq!(strict.refused, (3, 4), "`inc` completes");
    assert_eq!(strict.classes(), [("producer-declined", 2), ("synthesized-instance", 1)]);
    shim_refused(&strict, call, "Shim(FnPtr(");
    let (class, text) = strict.sample("twice::<inc>", generic("twice"));
    assert_eq!(class, "producer-declined");
    assert!(producer_declined(text), "{text}");
    assert!(strict.sample("run", item("run")).1.contains(HANDOFF_ABSENT));
    assert_eq!(
        relaxed.classes(),
        [("instance-assembly", 1), ("producer-declined", 1), ("synthesized-instance", 1)]
    );
    assert!(relaxed.sample("twice::<inc>", generic("twice")).1.contains(D17_GENERIC));
    // The producer: `run` passes the fn item as a zero-sized callable stand-in.
    let cov = coverage("fn_ptr_item.rs");
    assert_eq!(cov["run"].2, "Splice(zst callable stand-in argument)");
    // Since 51558bd9ff (EXACT-THIR-ABI-1) `twice`'s `f(..)` reaches `Fn::call`, a source
    // `extern "rust-call"` declaration with no IR convention until a real tuple adapter exists,
    // so `twice` is a symbolic body the producer refuses at that callee, and a refused row carries
    // no splice refusal (before: lowered, `Splice(symbolic body)`). A rust-call callee given a
    // plain-Rust convention without that adapter would lower `twice` again and fail here.
    assert!(!cov["twice"].0 && cov["twice"].1, "{:?}", cov["twice"]);
    assert_eq!(cov["twice"].2, "");
    assert_eq!(
        cov["twice"].3,
        ["Callee(foreign-ABI repr(Rust) struct by value)", "Callee(unsupported source ABI)"]
    );
}

/// `Shim(FnPtr(.., <fn pointer>))`: a fn pointer called through `Fn::call`.
fn fn_ptr_ptr() {
    let rows = channel_c("fn_ptr_ptr.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let call = shim(
        &shims,
        "shim-fn-ptr",
        "std::ops::Fn::call",
        "args=[Binder { value: fn(u64) -> u64, bound_vars: [] }, (u64,)]",
    );
    let (strict, relaxed) = f1_both("fn_ptr_ptr.rs");
    assert_eq!(strict.refused, (3, 4), "`inc` completes");
    assert_eq!(
        strict.classes(),
        [("instance-assembly", 1), ("producer-declined", 1), ("synthesized-instance", 1)]
    );
    shim_refused(&strict, call, "Shim(FnPtr(");
    assert!(producer_declined(strict.sample("twice::<fn>", generic("twice")).1));
    let (class, text) = strict.sample("run", item("run"));
    assert_eq!(class, "instance-assembly");
    assert!(text.contains("UnsignableCallee(") && text.contains(REIFY_ONLY), "{text}");
    assert_eq!(relaxed.classes(), [("instance-assembly", 2), ("synthesized-instance", 1)]);
    assert!(relaxed.sample("twice::<fn>", generic("twice")).1.contains(D17_GENERIC));
}

/// `Shim(Reify(..))` of a `#[track_caller]` item (INC4D-REIFY-TC).
fn reify_track_caller() {
    let rows = channel_c("reify_track_caller.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let reify = shim(&shims, "shim-reify", "tc ", "args=[]");
    assert_eq!(reify.local, "true", "the shim of a local item is local");
    let (strict, relaxed) = f1_both("reify_track_caller.rs");
    for census in [&strict, &relaxed] {
        assert_eq!(census.refused, (3, 3));
        assert_eq!(
            census.classes(),
            [("instance-assembly", 1), ("synthesized-instance", 1), ("unsupported-abi", 1)]
        );
        shim_refused(census, reify, "Shim(Reify(");
        let (class, text) = census.sample("tc", item("tc"));
        assert_eq!(class, "unsupported-abi");
        assert!(text.contains("unsupported codegen attribute flags TRACK_CALLER"), "{text}");
        let (class, text) = census.sample("run", item("run"));
        assert_eq!(class, "instance-assembly");
        assert!(text.contains("UnsignableCallee(") && text.contains(REIFY_ONLY), "{text}");
    }
}

/// `Shim(Reify(..))` over a `Virtual`: `<dyn T as T>::get` reified.
fn reify_virtual() {
    let rows = channel_c("reify_virtual.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let reify = shim(&shims, "shim-reify", "T::get ", "args=[dyn [Binder { value: Trait(T)");
    let (strict, relaxed) = f1_both("reify_virtual.rs");
    for census in [&strict, &relaxed] {
        assert_eq!(census.refused, (2, 3), "`<S as T>::get` completes");
        assert_eq!(census.classes(), [("producer-declined", 1), ("synthesized-instance", 1)]);
        shim_refused(census, reify, "Shim(Reify(");
        assert!(census.sample("run", item("run")).1.contains(HANDOFF_ABSENT));
    }
    // The producer refuses `run` at its fn-pointer type before the reify of a virtual.
    let cov = coverage("reify_virtual.rs");
    assert!(!cov["run"].0);
    assert!(cov["run"].3.iter().any(|t| t == "Reify(unsupported fn-ptr ty)"), "{:?}", cov["run"]);
}

/// `Shim(FnPtrAsPtr(..))` (1.101 spelling; `FnPtrAddr` before) through core's `fn_addr_eq`,
/// whose local copy is an upstream item.
fn fn_ptr_addr() {
    let rows = channel_c("fn_ptr_addr.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let addr = shim(
        &shims,
        "shim-fn-ptr-addr",
        // 1.101: upstream renamed `std::marker::FnPtr::addr` to `std::ops::FnPtr::as_ptr`.
        "std::ops::FnPtr::as_ptr",
        "args=[Binder { value: fn(), bound_vars: [] }]",
    );
    let eq = rows.iter().filter(|r| r.def.starts_with("std::ptr::fn_addr_eq ")).collect::<Vec<_>>();
    assert_eq!(eq.len(), 1, "a local copy of `fn_addr_eq`: {rows:#?}");
    assert_eq!((eq[0].kind.as_str(), eq[0].local.as_str()), ("item", "false"));
    let (strict, relaxed) = f1_both("fn_ptr_addr.rs");
    for (census, (upstream, reason)) in [(&strict, UPSTREAM_STRICT), (&relaxed, UPSTREAM_RELAXED)] {
        // 1.101: core's `fn_addr_eq` now reaches `FnPtr::addr` (the method, an
        // upstream body) and `NonZero::new_unchecked`'s precondition check
        // beside the `FnPtr::as_ptr` shim (`Shim(FnPtrAsPtr(..))`, renamed from
        // `FnPtrAddr`), so the graph and the upstream class both grow by
        // two; `a` and `b` still complete.
        assert_eq!(census.refused, (5, 7), "`a` and `b` complete");
        assert_eq!(
            census.classes(),
            [("instance-assembly", 1), ("synthesized-instance", 1), (upstream, 3)]
        );
        shim_refused(census, addr, "Shim(FnPtrAsPtr(");
        let (class, text) = census.sample("fn_addr_eq", exactly(&eq[0].sym));
        assert_eq!(class, upstream);
        assert!(text.ends_with(reason), "{text}");
        let (class, text) = census.sample("same", item("same"));
        assert_eq!(class, "instance-assembly");
        assert!(text.contains("UnsignableCallee(") && text.contains(REIFY_ONLY), "{text}");
    }
}

/// Constructors as codegen items: `[not-a-local-item]` on F1, `NoSourceBody("ctor")` in channel
/// C, and `Shim(FnPtr(.., <constructor>))` for `Option::map(Wrapper::Fd)` (INC4D-CTOR).
fn ctor_value() {
    let rows = channel_c("ctor_value.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let call = shim(&shims, "shim-fn-ptr", "std::ops::FnOnce::call_once", "args=[FnDef(DefId(");
    assert!(
        call.def
            .contains("::Wrapper::Fd::{constructor#0}), Binder { value: [], bound_vars: [] }), (i32,)]"),
        "{call:?}"
    );
    for ctor in ["Wrapper::Fd ", "Wrapper::Pipe ", "Tagged "] {
        let row = rows.iter().find(|r| r.def.starts_with(ctor)).expect(ctor);
        assert_eq!(
            (row.route.as_str(), row.result.as_str()),
            ("pre-route", "refused(NoSourceBody(\"ctor\"))"),
            "{row:?}"
        );
    }
    let (strict, relaxed) = f1_both("ctor_value.rs");
    for (census, (upstream, _)) in [(&strict, UPSTREAM_STRICT), (&relaxed, UPSTREAM_RELAXED)] {
        assert_eq!(census.refused, (7, 7));
        assert_eq!(
            census.classes(),
            [
                ("instance-assembly", 1),
                ("not-a-local-item", 3),
                ("producer-declined", 1),
                ("synthesized-instance", 1),
                (upstream, 1),
            ]
        );
        shim_refused(census, call, "Shim(FnPtr(");
        for ctor in ["Tagged", "Wrapper::Fd", "Wrapper::Pipe"] {
            let needle = format!("constructor shim `{ctor}` has no source body");
            assert!(census.of("not-a-local-item").iter().any(|t| t.contains(&needle)), "{ctor}");
        }
        assert!(census.sample("wrap_fd", item("wrap_fd")).1.contains(HANDOFF_ABSENT));
        let (class, text) = census.sample("ctor_values", item("ctor_values"));
        assert_eq!(class, "instance-assembly");
        assert!(text.contains("UnsignableCallee(") && text.contains(REIFY_ONLY), "{text}");
    }
}

/// An `async fn`'s future dropped: coroutine glue, refused by shape on the glue lane.
fn coroutine() {
    let rows = channel_c("coroutine.rs");
    let shims = shim_rows(&rows);
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let glue = shim(&shims, "shim-drop-glue", "std::ptr::drop_glue", "args=[Coroutine(DefId(");
    assert_eq!(glue.columns, "glue=refused-shape", "{glue:?}");
    let (strict, relaxed, compiler) = f1_all("coroutine.rs");
    for (census, (upstream, _)) in [(&strict, UPSTREAM_STRICT), (&relaxed, UPSTREAM_RELAXED)] {
        assert_eq!(census.refused, (5, 5));
        assert_eq!(
            census.classes(),
            [
                ("instance-assembly", 1),
                ("producer-declined", 2),
                ("synthesized-instance", 1),
                (upstream, 1),
            ]
        );
        for caller in ["f", "make_and_drop"] {
            assert!(census.sample(caller, item(caller)).1.contains(HANDOFF_ABSENT));
        }
        assert!(census.sample("the coroutine body", closure_in("f")).1.contains(A_COROUTINE));
    }
    // Strict: the glue lane refuses the coroutine's glue by shape. Allow-unknown: the lane is
    // inactive and the glue item is a plain synthesized instance.
    let (class, text) = strict.sample("the glue", exactly(&glue.sym));
    assert_eq!(class, "synthesized-instance");
    assert!(text.contains("coroutine glue (`coroutine_drop`)"), "{text}");
    shim_refused(&relaxed, glue, "Shim(DropGlue(");
    // Part D: the compiler lane licenses no glue (INC5.4-GLUE, owner ruling D31(a)), so the
    // coroutine's glue is `[unlicensed-body]` there; every other refusal and sample is the LIR
    // lane's.
    assert_eq!(compiler.refused, strict.refused);
    assert_eq!(
        compiler.classes(),
        [
            ("instance-assembly", 1),
            ("producer-declined", 2),
            ("unlicensed-body", 1),
            ("upstream-body", 1),
        ]
    );
    let (class, text) = compiler.sample("the glue", exactly(&glue.sym));
    assert_eq!(class, "unlicensed-body");
    assert!(
        text.contains("the compiler lane licenses exactly the direct and instance lanes"),
        "{text}"
    );
    let others = |census: &Census| {
        let mut samples: Vec<(String, String)> = census
            .samples
            .iter()
            .filter(|(_, text)| text.split('`').nth(1) != Some(glue.sym.as_str()))
            .cloned()
            .collect();
        samples.sort();
        samples
    };
    assert_eq!(others(&compiler), others(&strict), "the other samples are the LIR lane's");
}

/// A `thread_local!` read: no `Shim(ThreadLocal(..))` on this target, and F1 fatals on the
/// `#[thread_local]` static before any function is lowered.
fn thread_local() {
    let rows = channel_c("thread_local.rs");
    let shims = shim_rows(&rows);
    assert!(rows.iter().all(|r| r.kind != "shim-thread-local"), "{rows:#?}");
    // The one shim is std's own initializer closure's `FnOnce::call_once`.
    assert_eq!(shims.len(), 1, "{shims:#?}");
    let init = "::K::{constant#0}::{closure#1})";
    shim(&shims, "shim-closure-once", "std::ops::FnOnce::call_once", init);
    for extra in [&[][..], &["-Ztrust-cg-output-gate=allow-unknown"][..], &[COMPILER_LANE][..]] {
        let refused = trust_cg("thread_local.rs", "f1-tls", "trust-ir", extra).run_fail();
        let stderr = refused.stderr_utf8();
        assert!(stderr.contains("is #[thread_local]; TLS data is not"), "{stderr}");
        assert!(!stderr.contains("REFUSAL CENSUS"), "the static fatals first:\n{stderr}");
    }
}

/// `drop_in_place::<u64>` reified: an upstream `Item` in this tree, and no
/// `Shim(DropGlue(_, None))` row (that glue is collected only when it is not a direct call).
fn drop_glue_none() {
    let rows = channel_c("drop_glue_none.rs");
    assert!(shim_rows(&rows).is_empty(), "no shim at all: {rows:#?}");
    let place: Vec<&Row> =
        rows.iter().filter(|r| r.def.starts_with("std::ptr::drop_in_place ")).collect();
    assert_eq!(place.len(), 1, "{rows:#?}");
    assert!(place[0].def.ends_with("args=[u64]"), "{:?}", place[0]);
    let (strict, relaxed) = f1_both("drop_glue_none.rs");
    for (census, (upstream, reason)) in [(&strict, UPSTREAM_STRICT), (&relaxed, UPSTREAM_RELAXED)] {
        assert_eq!(census.refused, (2, 2));
        assert_eq!(census.classes(), [("producer-declined", 1), (upstream, 1)]);
        let (class, text) = census.sample("drop_in_place::<u64>", exactly(&place[0].sym));
        assert_eq!(class, upstream);
        assert!(text.ends_with(reason), "{text}");
        assert!(census.sample("get", item("get")).1.contains(HANDOFF_ABSENT));
    }
}
