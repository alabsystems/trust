//! The step-2 scoreboard: how much of the real codegen inventory the source-first
//! instance-keyed producer covers (docs/plans/2026-09-29-trust-ir-sole-compile-path.md, step 2,
//! increment 1).
//!
//! `-Ztrust-instance-flip-probe=*` prints one `TRUST-WALLA-PROBE C` row per `MonoItem::Fn` the
//! collector handed codegen, routed through the instance-keyed producer's measurement entry
//! (`trust_ir_of_instance_with_facts`; step 2 increment 4d.0a deleted the `pub` wrappers
//! `trust_ir_of_instance` / `trust_ir_of_instance_explained`, which nothing called). The subject crate
//! mixes the population the plan has to retire: local generic instances (`ident::<u64>`,
//! `ident::<u8>`, `G::<u32>::tag`), a trait method, a closure, drop glue for a `Vec`, and std
//! bodies.
//!
//! Run 1 is the default lifecycle: THIR is stolen by `check_unsafety` long before codegen, so
//! every local instance answers `ThirStolen` — the lifecycle wall, pinned as a number
//! (`thir_ok=0`). Run 2 keeps THIR alive with `-Zno-steal-thir`: the same local generic
//! instances now lower from THIR. Run 3 selects the trust-ir codegen frontend without that
//! flag: since step 2 increment 2 it keeps THIR alive by itself, so it must match run 2. In both
//! runs drop glue and std bodies are `route=mir result=residue`: nothing source-first produces
//! them yet.
//!
//! `result=ok` is COVERAGE ONLY IF CRATE ASSEMBLY TOOK THE BODY (2026-10-01). Before, it meant
//! "the instance lane produced a Module", and that counted the generic instances below (and, on
//! real crates, bodies refused at assembly or spliced with a loop erased) as coverage. The
//! probe reads the analysis-time crate module, which holds identity bodies only, so
//! `ident::<u64>`, `ident::<u8>` and `G::<u32>::tag` read `assembly-refused(generic-instance)`
//! — also since step 2 increment 3, whose codegen-time assembler appends generic instance bodies
//! to a private copy of that module (pinned by `trust-cg-f1-generic-instance`, disclosed by its
//! coverage artifact; the probe cannot see that copy). The non-generic closure and trait method
//! stay `ok`. Measured on this subject before increment 3's rows were added: main f5dd1d805a
//! reported `thir_ok=5`; the same compiler with this rule reported `thir_ok=2 assembly_refused=3`.
//!
//! Step 2 increment 3 made the instance module SELF-CONTAINED (the body plus one signed
//! declaration per callee edge), so a body that calls reports `functions=1+n` — `calls_ident`
//! (non-generic, spliced) prints `ok(input=Thir,functions=2)`, where it used to print
//! `functions=1` with a call to a `FuncId(1)` the module did not define — and a body still
//! carrying a finalizer-only pending-const SENTINEL is refused (`with_const::<u8>` reads a local
//! `const`; it used to print `ok`).
//!
//! Step 2 increment 4b (the producer emits drops) adds a DROP COLUMN to every local item row,
//! read from the effect-conservation gate's verdict against rustc's drop elaboration
//! (`drop_oracle.rs`): `placed` (the producer's drops equal rustc's), `elided`, `mismatch`,
//! `none`, `unchecked`; the summary counts them. `roots` owns a `Vec` and only borrows it: its
//! drop is placed (`drops=placed`), while its row stays `refused(LaneRefused("symbolic"))` — the
//! instance lane's verdict, which 4b does not change (the instance lane plans no drops; its
//! frozen gate still refuses every drop-bearing instance). No row may read `mismatch`.
//!
//! Step 2 increment 4c (drop glue as trust-ir) adds a GLUE COLUMN to every drop-glue row: the
//! drop-glue oracle's verdict on the synthesized glue against rustc's own drop shim
//! (`drop_glue_oracle.rs`). This subject's glue (`Vec<u64>`, `RawVec<u64>`) needs `alloc`'s
//! destructors, so it reads `refused-upstream-body`; the corpus that agrees is
//! `tests/run-make/trust-cg-f1-drop-glue`.
//!
//! Run 4 (S3) compiles a second subject whose only point is CONSTRUCTORS reaching codegen as
//! `InstanceKind::Item`: an enum-variant ctor passed to `Option::map` (`.map(Wrapper::Fd)`) and
//! an enum-variant and a tuple-struct ctor used as values. A ctor has no HIR body, and channel C
//! used to route a local one to THIR, where `tcx.thir_body` ICEd ("(ctor ..) has no associated
//! body") — measured 2026-10-01 on aterm-uds (`ChildStdio::Fd`, `BootClock`) under
//! `-Zno-steal-thir`. The routing rule now refuses it by name before any query
//! (`InstanceRefusal::NoSourceBody("ctor")`): with THIR kept alive and in the default lifecycle,
//! the compile exits 0 and each ctor row reads
//! `route=pre-route result=refused(NoSourceBody("ctor"))`. A separate subject, so the exact
//! coverage counts of runs 1-3 do not move.
//@ ignore-cross-compile

use run_make_support::{rfs, rustc};

const SUBJECT: &str = r#"#![crate_type = "lib"]

#[inline(never)]
pub fn ident<T>(x: T) -> T {
    x
}

pub struct G<T>(pub T);

impl<T> G<T> {
    #[inline(never)]
    pub fn tag(&self) -> u32 {
        7
    }
}

pub trait Tr {
    fn get(&self) -> u64;
}

pub struct K(pub u64);

impl Tr for K {
    fn get(&self) -> u64 {
        self.0
    }
}

pub fn calls_ident(n: u64) -> u64 {
    ident::<u64>(n)
}

const KC: u64 = 5;

#[inline(never)]
pub fn with_const<T>(x: u64) -> u64 {
    x ^ KC
}

pub fn roots(n: u64) -> u64 {
    let a = ident::<u64>(n) ^ with_const::<u8>(n);
    let b = ident::<u8>(3) as u64;
    let c = G(1u32).tag() as u64;
    let v: Vec<u64> = vec![a, b, c];
    let add = |x: u64| x + 1;
    let k = K(n);
    let d: &dyn Tr = &k;
    add(v.len() as u64) + d.get()
}
"#;

/// Trust (S3): constructors as codegen items. See the module docs, run 4.
const CTOR_SUBJECT: &str = r#"#![crate_type = "lib"]

pub enum Wrapper {
    Fd(i32),
    Pipe(i32, i32),
    Closed,
}

pub struct Tagged(pub u64);

// An enum-variant ctor passed as a function: `Option::map` calls it through the `FnOnce` shim
// of its fn-item type, so codegen collects the ctor itself as an `InstanceKind::Item`.
pub fn wrap_fd(v: Option<i32>) -> Option<Wrapper> {
    v.map(Wrapper::Fd)
}

// Constructors used as VALUES: coerced to fn pointers and called through them.
pub fn ctor_values(a: i32, b: i32, n: u64) -> u64 {
    let pipe: fn(i32, i32) -> Wrapper = Wrapper::Pipe;
    let tag: fn(u64) -> Tagged = Tagged;
    let w = pipe(a, b);
    let t = tag(n);
    match w {
        Wrapper::Pipe(x, _) => t.0 + x as u64,
        _ => t.0,
    }
}
"#;

fn probe(extra: &[&str]) -> String {
    probe_file("subject.rs", extra)
}

fn probe_file(file: &str, extra: &[&str]) -> String {
    let out = rustc()
        .input(file)
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .args(extra)
        .run();
    out.stderr_utf8()
}

fn c_rows(stderr: &str) -> Vec<&str> {
    stderr.lines().filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym=")).collect()
}

fn summary_field(stderr: &str, field: &str) -> usize {
    let line = stderr
        .lines()
        .find(|l| l.starts_with("TRUST-WALLA-PROBE C summary"))
        .unwrap_or_else(|| panic!("channel C printed no summary:\n{stderr}"));
    line.split_whitespace()
        .find_map(|kv| kv.strip_prefix(&format!("{field}=")))
        .and_then(|v| v.parse().ok())
        .unwrap_or_else(|| panic!("summary has no `{field}`: {line}"))
}

fn rows_for<'a>(rows: &[&'a str], def: &str) -> Vec<&'a str> {
    rows.iter().copied().filter(|r| r.contains(&format!(" def={def} "))).collect()
}

/// Trust (S3): every constructor row is refused by the routing rule, by name, and the compile
/// that printed them exited 0 (`probe_file` runs it with `.run()`). `ctor_subject.rs` has
/// exactly three ctors that reach codegen.
fn assert_ctor_rows_refused(stderr: &str) {
    assert!(!stderr.contains("internal compiler error"), "no ICE:\n{stderr}");
    assert!(!stderr.contains("has no associated body"), "no `thir_body` on a ctor:\n{stderr}");
    assert_eq!(summary_field(stderr, "panics"), 0, "no probe row may panic:\n{stderr}");
    let rows = c_rows(stderr);
    for def in ["Wrapper::Fd", "Wrapper::Pipe", "Tagged"] {
        let row = rows_for(&rows, def);
        assert_eq!(row.len(), 1, "one codegen instance of the ctor `{def}`:\n{stderr}");
        assert!(
            row[0].contains(
                "kind=item local=true route=pre-route result=refused(NoSourceBody(\"ctor\"))"
            ),
            "a local ctor has no source body and never reaches the THIR route: {}",
            row[0]
        );
    }
    assert!(
        stderr.lines().any(|l| l == "TRUST-WALLA-PROBE C class NoSourceBody(\"ctor\")=3"),
        "the class table counts the three ctors:\n{stderr}"
    );
}

fn main() {
    rfs::write("subject.rs", SUBJECT);
    seam_one_working_copy();

    // ── Run 1: the default lifecycle ───────────────────────────────────────
    let stolen = probe(&[]);
    let rows = c_rows(&stolen);
    assert!(!rows.is_empty(), "channel C must print one row per mono fn item:\n{stolen}");
    assert_eq!(
        summary_field(&stolen, "fn_items"),
        rows.len(),
        "the summary must count exactly the rows printed"
    );
    assert_eq!(summary_field(&stolen, "panics"), 0, "no probe row may panic:\n{stolen}");
    let ident = rows_for(&rows, "ident");
    assert_eq!(ident.len(), 2, "ident::<u64> and ident::<u8> are two instances: {ident:#?}");
    for row in &ident {
        assert!(
            row.contains("route=thir result=refused(ThirStolen)"),
            "a local instance at codegen time finds THIR stolen: {row}"
        );
    }
    assert_eq!(summary_field(&stolen, "thir_ok"), 0, "the lifecycle wall, as a number");

    // ── Run 2: THIR kept alive ─────────────────────────────────────────────
    let kept = probe(&["-Zno-steal-thir"]);
    let rows = c_rows(&kept);
    assert_eq!(summary_field(&kept, "panics"), 0, "no probe row may panic:\n{kept}");
    let ident = rows_for(&rows, "ident");
    assert_eq!(ident.len(), 2, "{ident:#?}");
    for row in &ident {
        assert!(
            row.contains("route=thir result=assembly-refused(generic-instance)"),
            "a local generic instance lowers source-first, but no assembled body holds it — \
             it is not coverage until instance-keyed assembly lands: {row}"
        );
    }
    let tag = rows_for(&rows, "G::<T>::tag");
    assert_eq!(tag.len(), 1, "{tag:#?}");
    assert!(tag[0].contains("route=thir result=assembly-refused(generic-instance)"), "{}", tag[0]);
    for def in ["<K as Tr>::get", "roots::{closure#0}"] {
        let row = rows_for(&rows, def);
        assert_eq!(row.len(), 1, "{def}: {row:#?}");
        assert!(
            row[0].contains("route=thir result=ok(input=Thir,functions=1)"),
            "a non-generic local body that crate assembly spliced is coverage: {}",
            row[0]
        );
    }
    assert!(
        rows.iter().any(|r| r.contains("kind=shim-drop-glue") && r.contains("route=mir result=residue")),
        "drop glue has no source-first producer yet and must be reported as residue:\n{kept}"
    );
    assert_eq!(
        summary_field(&kept, "thir_ok"),
        3,
        "exactly the closure, `K::get` and `calls_ident`:\n{kept}"
    );
    assert_eq!(summary_field(&kept, "assembly_refused"), 3, "ident x2 and tag:\n{kept}");
    assert_eq!(summary_field(&kept, "erased"), 0, "nothing here is lowered by erasure:\n{kept}");
    assert_self_contained_rows(&rows);
    assert!(summary_field(&kept, "residue") > 0, "std bodies and shims are residue:\n{kept}");
    assert_drop_column(&rows, &kept);

    // ── Run 3: the trust-ir codegen frontend keeps THIR alive by itself ───
    // (step 2 increment 2): selecting `-Ztrust-cg-frontend=trust-ir` must give the same
    // source-first coverage as `-Zno-steal-thir`, without that flag.
    let frontend = probe(&["-Ztrust-cg-frontend=trust-ir"]);
    assert_eq!(summary_field(&frontend, "panics"), 0, "no probe row may panic:\n{frontend}");
    for field in ["thir_ok", "assembly_refused"] {
        assert_eq!(
            summary_field(&frontend, field),
            summary_field(&kept, field),
            "the trust-ir frontend must retain THIR exactly as -Zno-steal-thir does:\n{frontend}"
        );
    }
    let rows = c_rows(&frontend);
    assert!(
        !rows.iter().any(|r| r.contains("refused(ThirStolen)")),
        "no instance may find THIR stolen when the trust-ir frontend is selected:\n{frontend}"
    );
    assert_self_contained_rows(&rows);
    assert_drop_column(&rows, &frontend);

    // ── Run 4 (S3): constructors never reach `thir_body` ───────────────────
    // With THIR kept alive (the measured ICE) and in the default lifecycle: the THIR route asks
    // `thir_body` BEFORE its stolen check (`instance_admission::admit_instance_body`), so a ctor
    // reached the ICE in both, not only where THIR survives.
    rfs::write("ctor_subject.rs", CTOR_SUBJECT);
    let lifecycles: [&[&str]; 2] = [&["-Zno-steal-thir"], &[]];
    for extra in lifecycles {
        assert_ctor_rows_refused(&probe_file("ctor_subject.rs", extra));
    }
}

/// Step 2 increment 4b: the drop column. `roots` owns a `Vec` the producer now drops, equal to
/// rustc's elaboration; nothing else here owns a value that needs dropping; nothing mismatches.
fn assert_drop_column(rows: &[&str], stderr: &str) {
    let roots = rows_for(rows, "roots");
    assert_eq!(roots.len(), 1, "{roots:#?}");
    assert!(roots[0].contains(" drops=placed "), "`roots` drops its `Vec`: {}", roots[0]);
    for def in ["calls_ident", "<K as Tr>::get", "roots::{closure#0}"] {
        let row = rows_for(rows, def);
        assert!(row[0].contains(" drops=none "), "{def}: {}", row[0]);
    }
    assert_eq!(summary_field(stderr, "drops_mismatch"), 0, "{stderr}");
    assert_eq!(summary_field(stderr, "drops_elided"), 0, "{stderr}");
    assert_eq!(summary_field(stderr, "drops_placed"), 1, "{stderr}");
    assert_glue_column(rows, stderr);
}

/// Step 2 increment 4c: the glue column. Every drop-glue row carries the drop-glue oracle's
/// verdict (`drop_glue_oracle`); the subject's only glue is `Vec<u64>`'s and its `RawVec`'s,
/// whose destructors are `alloc`'s, so each reads `refused-upstream-body` (increment 6), and
/// nothing the oracle compares differs.
fn assert_glue_column(rows: &[&str], stderr: &str) {
    let glue: Vec<&&str> = rows.iter().filter(|r| r.contains(" kind=shim-drop-glue ")).collect();
    assert!(!glue.is_empty(), "{stderr}");
    for row in &glue {
        assert!(row.contains(" glue=refused-upstream-body "), "an `alloc` destructor: {row}");
    }
    for field in ["glue_match", "glue_differs", "glue_misses", "glue_extras", "glue_oracle_failed"] {
        assert_eq!(summary_field(stderr, field), 0, "`{field}`: {stderr}");
    }
    assert_eq!(summary_field(stderr, "glue_refused"), glue.len(), "{stderr}");
}

/// Step 2 increment 3: a body that calls carries its callee's declaration, and a body that
/// still holds a pending-const sentinel is refused before assembly is asked.
fn assert_self_contained_rows(rows: &[&str]) {
    let calls = rows_for(rows, "calls_ident");
    assert_eq!(calls.len(), 1, "{calls:#?}");
    assert!(
        calls[0].contains("route=thir result=ok(input=Thir,functions=2)"),
        "a body with one callee is the body plus that callee's declaration: {}",
        calls[0]
    );
    let with_const = rows_for(rows, "with_const");
    assert_eq!(with_const.len(), 1, "{with_const:#?}");
    assert!(
        with_const[0].contains("route=thir result=refused(PendingConsts)"),
        "a finalizer-only const sentinel is refused, never emitted: {}",
        with_const[0]
    );
}

/// Trust (R8-SEAM, `docs/DECISION_QUEUE.md`, taken 2026-10-05): the crate-seam differential computes
/// from ONE working copy of the assembled module what it computed from whole-module copies. The
/// TEST-ONLY `-Ztrust-ir-seam-reference=<report>` option runs the pre-R8-SEAM seam over the
/// pre-R8-SEAM differential (`crates/trust-thir-lower/src/crate_module/seam_reference.rs` and
/// `.../differential/compare_entries_reference.rs`, verbatim) beside the live one at
/// crate finalization and fails finalization on any difference in the verdicts or the UC probe's
/// traced outcomes; `tests/run-make/trust-ir-seam-one-working-copy` pins that each lane is reached.
fn seam_cross_check(file: &str, edition: &str, tag: &str) {
    let report = format!("seam-reference-{tag}.txt");
    let out = rustc()
        .input(file)
        .crate_type("lib")
        .edition(edition)
        .arg("-Copt-level=0")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("--emit=metadata")
        .out_dir(format!("seam-out-{tag}"))
        .arg(format!("-Ztrust-ir-seam-reference={report}"))
        .run();
    let stderr = out.stderr_utf8();
    assert!(!stderr.contains("seam cross-check"), "{tag}: the seams differ:\n{stderr}");
    let text = rfs::read_to_string(&report);
    for line in ["differences 0", "restored true"] {
        assert!(text.lines().any(|l| l == line), "{tag}: the report lacks `{line}`:\n{text}");
    }
    assert!(!text.lines().any(|l| l == "verdicts 0"), "{tag}: no deferred body was compared:\n{text}");
}

fn seam_one_working_copy() {
    rfs::write("subject.rs", SUBJECT);
    rfs::write("ctor_subject.rs", CTOR_SUBJECT);
    seam_cross_check("subject.rs", "2021", "census");
    seam_cross_check("ctor_subject.rs", "2021", "census-ctor");
}

/// The R8-SEAM cross-check on this fixture's subjects, under libtest as well as compiletest (the
/// frozen-file waiver cites it).
#[test]
fn the_seam_on_the_census_subjects_is_the_reference_seam() {
    seam_one_working_copy();
}
