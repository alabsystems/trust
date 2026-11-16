//! Step 2 increment 6: the LEVEL-S TEMPLATE LANE, judged and recorded, and since the bounded
//! 6.5.4 producer milestone (687eab86c1) WRITTEN for the templates that pass every gate
//! (`docs/design/2026-10-08-step2-inc6-step5-level-s-producer-plan.md` §1 "run-make";
//! `docs/decisions/2026-11-05-level-s-producer-freeze-extension.md`;
//! `crates/trust-thir-lower/src/template_lowering.rs`).
//!
//! A dependency with `pub` generics is built with the direct producer on, with the TEST-ONLY
//! switch `-Ztrust-ir-lower-templates` off (the default) and on; a user instantiates every
//! subject and probe channel C reads each one's `rmeta=absent(<class>)` from the dependency's
//! trust-ir header. Pins:
//!
//!  * (A) LEVEL R DOES NOT MOVE: across the two builds every `TRIRENTR` entry blob, the
//!    `<crate>.effect-conservation.json` sidecar, every object file in the rlib, the level-R
//!    `trust-ir per definition:` line and every other `-Zmeta-stats` section's byte count but
//!    `tables` are identical. What differs is the trust-ir HEADER, by design — it records each
//!    generic definition's template class — and, from 687eab86c1, the written level-S rows: the
//!    `trust-ir` section's bytes, the `tables` section (one entry-table row per written
//!    template), the total and the percentages, the `trust-ir templates:` line, the new
//!    `trust-ir templates per definition:` line, and the `trust-ir entries:` line, which counts
//!    every emitted R and S row (each written template moves from its `template-pending`
//!    aggregate to `encoded`);
//!  * (A') NOTHING REACHES STRICT OR THE SCORECARD: the same A/B under `-Ztrust-ir-lower=strict`
//!    with `RUSTC_LOG=rustc_mir_build::builder=info` gives identical diagnostics, exit status and
//!    `trust-ir-lower: effect conservation` events (a leaked template verdict would add one
//!    event per template body);
//!  * (B) EACH SUBJECT'S CLASS with the switch on, through channel C and the templates line —
//!    measured at landing and pinned below;
//!  * (C) NO ICE IN A SILENT SESSION: the switch-on build under `TRUST_VANILLA_ANNOUNCED=1`;
//!  * (D) THE DEFAULT: with the switch off every routed definition reads
//!    `template-pending(capture off)`.
//!
//! With the switch off no template is written (`0 encoded`). With it on, the five templates
//! that pass every gate are written as authenticated level-S (`TRIRTMPL`) metadata, and the
//! level-R reader a consumer runs refuses them by magic (`entry-refused(magic)`): no consumer
//! admits an S row yet.
//@ ignore-cross-compile

use std::collections::BTreeMap;

use run_make_support::{rfs, rustc};

const DEP: &str = r#"#![crate_type = "lib"]

pub trait Tag {
    fn tag() -> u64;
}

pub trait Foo {
    fn n(&self) -> usize {
        0
    }
}

pub struct Wrapper<T>(pub T);

#[inline]
pub fn mix(x: u32) -> u32 {
    x ^ 0x5a5a_5a5a
}

#[inline]
pub fn twice(x: u32) -> u32 {
    mix(mix(x))
}

#[inline(never)]
pub fn ident<T>(x: T) -> T {
    x
}

#[inline(never)]
pub fn phantom<T>(x: u64) -> u64 {
    x ^ 0x5a
}

#[inline(never)]
pub fn raw_arr<T, const N: usize>(p: *const [T; N]) -> *const [T; N] {
    p
}

#[inline(never)]
pub fn bump<T>(x: u64) -> u64 {
    x + 1
}

#[inline(never)]
pub fn pick<T: Tag>(x: u64) -> u64 {
    x ^ T::tag()
}

#[inline(never)]
pub fn fwd<T: ?Sized>(x: &T) -> &T {
    x
}

#[inline(never)]
pub fn mut_slice<T>(x: &mut [T]) -> &mut [T] {
    x
}

#[inline(never)]
pub fn wrap<T>(x: T) -> Wrapper<T> {
    Wrapper(x)
}

pub async fn later<T>(x: T) -> T {
    x
}

#[inline(never)]
#[track_caller]
pub fn located<T>(x: T) -> T {
    x
}

pub fn make_closure() -> impl Fn(u64) -> u64 {
    |x| x ^ 1
}

#[inline(never)]
pub fn cst<const N: usize>(x: usize) -> usize {
    x ^ N
}

#[inline(never)]
pub fn opt_ref<T>(o: Option<&T>) -> bool {
    match o {
        Some(_) => true,
        None => false,
    }
}
"#;

const USER: &str = r#"#![crate_type = "lib"]

use std::future::Future;

pub struct Local;

impl dep::Tag for Local {
    fn tag() -> u64 {
        7
    }
}

impl dep::Foo for Local {}

pub fn use_all(x: u64) -> u64 {
    let mut a = [1u8; 4];
    let p = dep::raw_arr::<u8, 4>(&a as *const [u8; 4]);
    let s_len = dep::mut_slice::<u8>(&mut a[..]).len() as u64;
    let w = dep::wrap::<u64>(x);
    let f = dep::make_closure();
    let mut fut = std::pin::pin!(dep::later::<u64>(x));
    let waker = std::task::Waker::noop();
    let _ = fut.as_mut().poll(&mut std::task::Context::from_waker(waker));
    dep::ident::<u64>(x)
        ^ dep::twice(x as u32) as u64
        ^ dep::phantom::<u8>(x)
        ^ dep::bump::<u8>(x)
        ^ dep::pick::<Local>(x)
        ^ dep::fwd::<str>("ab").len() as u64
        ^ dep::Foo::n(&Local) as u64
        ^ s_len
        ^ w.0
        ^ f(x)
        ^ dep::located::<u64>(x)
        ^ dep::cst::<3>(x as usize) as u64
        ^ dep::opt_ref::<u8>(Some(&a[0])) as u64
        ^ (p as usize as u64)
}
"#;

struct Build {
    /// stdout + stderr.
    out: String,
    stderr: String,
    success: bool,
}

/// Build `dep.rs` into `out` with the direct producer on, the switch `templates`, and `extra`.
fn dep(out: &str, templates: bool, extra: &[&str], env: &[(&str, &str)]) -> Build {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    cmd.input("dep.rs")
        .crate_name("dep")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=off")
        .arg("--emit=metadata,link")
        .arg("-Zmeta-stats")
        .out_dir(out);
    if !extra.iter().any(|a| a.starts_with("-Ztrust-ir-lower=")) {
        cmd.arg("-Ztrust-ir-lower");
    }
    for a in extra {
        cmd.arg(a);
    }
    if templates {
        cmd.arg("-Ztrust-ir-lower-templates=yes");
    }
    for (k, v) in env {
        cmd.env(k, v);
    }
    let run = cmd.run_unchecked();
    let stderr = run.stderr_utf8();
    Build { out: format!("{}{}", run.stdout_utf8(), stderr), stderr, success: run.status().success() }
}

fn user(dep_out: &str, out: &str) -> String {
    let run = rustc()
        .input("user.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .extern_("dep", format!("{dep_out}/libdep.rlib"))
        .out_dir(out)
        .run();
    run.stderr_utf8()
}

/// The channel-C rows naming `def` (`def=<path> `), in order.
fn rows<'a>(stderr: &'a str, def: &str) -> Vec<&'a str> {
    stderr
        .lines()
        .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym=") && l.contains(&format!(" def={def} ")))
        .collect()
}

/// The `rmeta=` column of the one channel-C row of `def` that is not drop glue.
fn rmeta_of(stderr: &str, def: &str) -> String {
    let rows: Vec<&str> =
        rows(stderr, def).into_iter().filter(|r| !r.contains(" kind=drop-glue")).collect();
    assert_eq!(rows.len(), 1, "one channel-C row for `{def}`:\n{}", channel_c(stderr));
    let at = rows[0].find(" rmeta=").expect("an rmeta column") + " rmeta=".len();
    rows[0][at..].split_whitespace().next().unwrap().to_string()
}

fn channel_c(stderr: &str) -> String {
    stderr.lines().filter(|l| l.starts_with("TRUST-WALLA-PROBE C")).collect::<Vec<_>>().join("\n")
}

/// Every trust-ir entry blob in an rmeta file (the framing `trust-ir-rmeta-entry-roundtrip`
/// reads: schema-5 magic/version/content digest and length-framed payload).
fn entries(rmeta: &[u8]) -> Vec<Vec<u8>> {
    let u64_at = |at: usize| u64::from_le_bytes(rmeta[at..at + 8].try_into().unwrap()) as usize;
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(found) = rmeta[at..].windows(8).position(|w| w == b"TRIRENTR") {
        let start = at + found;
        // Trust: entry schema 5 frames the complete owner/mode/module/evidence payload.
        assert_eq!(u32::from_le_bytes(rmeta[start + 8..start + 12].try_into().unwrap()), 5);
        let p = start + 56 + u64_at(start + 48);
        out.push(rmeta[start..p].to_vec());
        at = p;
    }
    out
}

/// The members of an `ar` archive (BSD `#1/<len>` and GNU short names), name -> bytes.
fn ar_members(archive: &[u8]) -> BTreeMap<String, Vec<u8>> {
    assert!(archive.starts_with(b"!<arch>\n"), "an ar archive");
    let mut out = BTreeMap::new();
    let mut at = 8;
    while at + 60 <= archive.len() {
        let header = &archive[at..at + 60];
        let raw_name = String::from_utf8_lossy(&header[..16]).trim_end().to_string();
        let size: usize = String::from_utf8_lossy(&header[48..58]).trim().parse().unwrap();
        let mut data = &archive[at + 60..at + 60 + size];
        let name = if let Some(len) = raw_name.strip_prefix("#1/") {
            let len: usize = len.parse().unwrap();
            let name = String::from_utf8_lossy(&data[..len]).trim_end_matches('\0').to_string();
            data = &data[len..];
            name
        } else {
            raw_name.trim_end_matches('/').to_string()
        };
        out.insert(name, data.to_vec());
        at += 60 + size + (size % 2);
    }
    out
}

/// The `-Zmeta-stats` section rows `label -> bytes` (`meta-stats <label> <bytes> (<pct>%)`).
fn section_bytes(stats: &str) -> BTreeMap<String, String> {
    stats
        .lines()
        .filter_map(|l| {
            let mut words = l.split_whitespace();
            (words.next()? == "meta-stats").then_some(())?;
            let label = words.next()?.to_string();
            let bytes = words.next()?;
            let pct = words.next()?;
            (bytes.chars().all(|c| c.is_ascii_digit() || c == '_') && pct.starts_with('('))
                .then(|| (label, bytes.to_string()))
        })
        .collect()
}

fn line<'a>(stats: &'a str, prefix: &str) -> &'a str {
    stats
        .lines()
        .find(|l| l.starts_with(prefix))
        .unwrap_or_else(|| panic!("no `{prefix}` line:\n{stats}"))
}

fn conservation_events(stderr: &str) -> Vec<&str> {
    stderr.lines().filter(|l| l.contains("trust-ir-lower: effect conservation")).collect()
}

/// The template builder's row per definition, from its `trust-ir-lower: template row` info
/// events (`RUSTC_LOG=trust_thir_lower::rmeta_entry=info`): `def_path -> reason`. Both events this
/// recipe reads are `info!`: a stage built with `rust.debug-logging = false` compiles `debug!` out
/// (see trust-thir-unsafe-await-census), and this recipe read no row on one (2026-10-17).
fn template_rows(stderr: &str) -> BTreeMap<String, String> {
    let field = |l: &str, name: &str| -> Option<String> {
        let at = l.find(&format!("{name}="))? + name.len() + 1;
        let rest = &l[at..];
        // The reason is the last field and may hold spaces; the path holds none.
        let value = if name == "reason" {
            rest.trim_end().to_string()
        } else {
            rest.split_whitespace().next()?.to_string()
        };
        Some(value.trim_end_matches(',').to_string())
    };
    stderr
        .lines()
        .filter(|l| l.contains("trust-ir-lower: template row"))
        .filter_map(|l| Some((field(l, "def_path")?, field(l, "reason")?)))
        .collect()
}

fn sidecar(dir: &str) -> Vec<u8> {
    let path = format!("{dir}/dep.effect-conservation.json");
    rfs::read(&path)
}

fn main() {
    rfs::write("dep.rs", DEP);
    rfs::write("user.rs", USER);

    // ── (A) Level R does not move ─────────────────────────────────────────────
    let off = dep("dep-off", false, &["-Ztrust-dump=ir:dump-off"], &[]);
    let on = dep("dep-on", true, &["-Ztrust-dump=ir:dump-on"], &[]);
    assert!(off.success, "the default build succeeds:\n{}", off.out);
    assert!(on.success, "the switch-on build succeeds:\n{}", on.out);
    assert!(!on.out.contains("internal compiler error"), "no ICE:\n{}", on.out);
    let (entries_off, entries_on) =
        (entries(&rfs::read("dep-off/libdep.rmeta")), entries(&rfs::read("dep-on/libdep.rmeta")));
    assert_eq!(entries_off.len(), 2, "`mix` and `twice` carry level-R entries");
    assert_eq!(entries_off, entries_on, "every TRIRENTR entry blob is byte-identical");
    assert_eq!(sidecar("dump-off"), sidecar("dump-on"), "the effect-conservation sidecar");
    let (rlib_off, rlib_on) =
        (ar_members(&rfs::read("dep-off/libdep.rlib")), ar_members(&rfs::read("dep-on/libdep.rlib")));
    let objects = |m: &BTreeMap<String, Vec<u8>>| -> BTreeMap<String, Vec<u8>> {
        m.iter().filter(|(n, _)| n.ends_with(".o")).map(|(n, b)| (n.clone(), b.clone())).collect()
    };
    assert!(!objects(&rlib_off).is_empty(), "the rlib carries object files: {:?}", rlib_off.keys());
    assert_eq!(objects(&rlib_off), objects(&rlib_on), "every object file in the rlib");
    let prefix = "meta-stats trust-ir per definition:";
    assert_eq!(line(&off.out, prefix), line(&on.out, prefix), "the level-R line `{prefix}`");
    // From 687eab86c1 the S rows have their own per-definition line; the R one keeps its
    // population. With the switch off there is no S row and so no S line.
    assert!(
        !off.out.contains("meta-stats trust-ir templates per definition:"),
        "no S row is written with the switch off:\n{}",
        off.out
    );
    assert!(
        line(&on.out, "meta-stats trust-ir templates per definition:")
            .starts_with("meta-stats trust-ir templates per definition: 5 with both rows; "),
        "the five written templates are disclosed apart from R:\n{}",
        on.out
    );
    // The total line counts every emitted R and S row (687eab86c1): each written template
    // leaves the legacy `template-pending` aggregate for `encoded`, and nothing else moves.
    assert_eq!(
        line(&off.out, "meta-stats trust-ir entries:"),
        "meta-stats trust-ir entries: 2 encoded; 15 unencoded: template-pending=15"
    );
    assert_eq!(
        line(&on.out, "meta-stats trust-ir entries:"),
        "meta-stats trust-ir entries: 7 encoded; 10 unencoded: template-pending=10"
    );
    let (mut sections_off, mut sections_on) = (section_bytes(&off.out), section_bytes(&on.out));
    assert!(sections_off.len() > 10, "the section table was read:\n{}", off.out);
    let bytes = |m: &BTreeMap<String, String>, label: &str| -> usize {
        m[label].replace('_', "").parse().unwrap_or_else(|_| panic!("`{label}` bytes"))
    };
    assert!(
        bytes(&sections_on, "tables") > bytes(&sections_off, "tables"),
        "each written S row adds an entry-table row: {sections_off:?} vs {sections_on:?}"
    );
    for label in ["trust-ir", "Total", "tables"] {
        sections_off.remove(label);
        sections_on.remove(label);
    }
    assert_eq!(sections_off, sections_on, "every other rmeta section's byte count");
    let rest = |s: &str| -> Vec<String> {
        s.lines().filter(|l| !l.starts_with("meta-stats")).map(str::to_string).collect()
    };
    assert_eq!(rest(&off.out), rest(&on.out), "the rest of the output");

    // ── (D) The default: every routed definition reads `template-pending(capture off)` ──
    let templates_off = line(&off.out, "meta-stats trust-ir templates:");
    let routed: usize = templates_off
        .split("unencoded:")
        .next()
        .and_then(|head| head.split(';').nth(1))
        .and_then(|u| u.split_whitespace().next())
        .and_then(|n| n.parse().ok())
        .unwrap_or_else(|| panic!("a count of routed rows: {templates_off}"));
    assert_eq!(routed, 15, "every generic subject (and the two closure bodies) is routed: {templates_off}");
    assert_eq!(
        templates_off,
        format!(
            "meta-stats trust-ir templates: 0 encoded; {routed} unencoded: template-pending={routed}"
        ),
        "with the switch off every routed row is template-pending"
    );
    let rows_off = dep(
        "dep-off-log",
        false,
        &[],
        &[("RUSTC_LOG", "trust_thir_lower::rmeta_entry=info")],
    );
    let reasons_off = template_rows(&rows_off.stderr);
    assert!(reasons_off.len() >= routed, "every routed row is logged: {reasons_off:#?}");
    for (def, reason) in &reasons_off {
        assert!(reason.contains("template-pending(capture off)"), "{def}: {reason}");
    }
    let user_off = user("dep-off", "user-off");
    assert!(!user_off.contains("internal compiler error"), "no ICE:\n{user_off}");
    for def in ["dep::ident", "dep::bump", "dep::fwd", "dep::located"] {
        assert_eq!(rmeta_of(&user_off, def), "absent(template-pending)", "{def} with the switch off");
    }
    assert!(
        line(&off.out, "meta-stats trust-ir entries:").contains(&format!("template-pending={routed}")),
        "the level-R line counts every routed row as template-pending, as it did before the \
         template builder existed: {}",
        line(&off.out, "meta-stats trust-ir entries:")
    );

    // ── (B) Each subject's class with the switch on (measured at landing, pinned) ──
    let templates_on = line(&on.out, "meta-stats trust-ir templates:");
    let rows_on =
        dep("dep-on-log", true, &[], &[("RUSTC_LOG", "trust_thir_lower::rmeta_entry=info")]);
    let reasons_on = template_rows(&rows_on.stderr);
    // Keyed by the definition's path in its own crate (`def_path_str`, untrimmed).
    // 687eab86c1 writes every template that passes the gates and logs it as `template`.
    let written = "encoded authenticated level-S metadata";
    let expected_reasons: &[(&str, &str)] = &[
        ("ident", written),
        ("phantom", written),
        ("raw_arr", written),
        ("cst", written),
        ("bump", "unsited-panic(overflow)"),
        // 347171f45a (CALLABLE-S-IDENTITY): a generic Rust callee (`T::tag()`) is a typed level-S
        // hole bound to its stable definition and positional arguments, no longer the runtime
        // lane's unnamed havoc edge, and so `pick` is written with the others.
        ("pick", written),
        ("fwd", "template-unsupported(parameter-dependent pointer metadata)"),
        ("Foo::n", "template-unsupported(parameter-dependent pointer metadata)"),
        ("mut_slice", "template-unsupported(&mut to a DST (thin posture))"),
        // A parameter-dependent nominal (`Option<&T>`, `Wrapper<T>`) is a checked type hole in
        // the S lane before any R nominal row is registered (74ecf91eab), and a hole has no
        // field, construction or match rule: the match and the constructor refuse at their own
        // arms. Before 74ecf91eab these read `template-unsupported(parameter-dependent ADT row
        // (6.5.2))` (INC6.5-SENTINEL) and `not-lowered(Adt(non-scalar field seed))`.
        ("opt_ref", "not-lowered(EnumMatch(non-enum mapped ty))"),
        ("wrap", "not-lowered(Adt(non-struct mapped ty))"),
        // Trust: keep the more specific declared-opaque-return refusal pinned.
        ("later", "not-lowered(symbolic; unsubstituted opaque return)"),
        ("later::{closure#0}", "template-unsupported(coroutine body (INC6.5-CLOSURES))"),
        (
            "located",
            "caller-location(the body is #[track_caller]: its symbol takes a hidden &'static \
             Location parameter its trust-ir signature does not have)",
        ),
        (
            "make_closure::{closure#0}",
            "template-pending(non-generic closure: level R (design §2.1), not routed in 6.5 \
             (INC6.5-CLOSURES))",
        ),
    ];
    let measured_reasons: Vec<(&str, Option<&String>)> =
        expected_reasons.iter().map(|(def, _)| (*def, reasons_on.get(*def))).collect();
    for ((def, reason), (_, expected)) in measured_reasons.iter().zip(expected_reasons) {
        assert_eq!(
            reason.map(String::as_str),
            Some(*expected),
            "`{def}`'s recorded reason; every row: {reasons_on:#?}"
        );
    }
    assert_eq!(reasons_on.len(), expected_reasons.len(), "no other routed row: {reasons_on:#?}");
    assert_eq!(
        templates_on,
        "meta-stats trust-ir templates: 5 encoded; 10 unencoded: caller-location=1 not-lowered=3 \
         template-pending=1 template-unsupported=4 unsited-panic=1",
    );
    let user_on = user("dep-on", "user-on");
    assert!(!user_on.contains("internal compiler error"), "no ICE:\n{user_on}");
    // A written S row is refused by the level-R reader by magic (687eab86c1: "the old R reader
    // continues rejecting S magic"); no consumer admits a level-S row.
    let expected: &[(&str, &str)] = &[
        ("dep::ident", "entry-refused(magic)"),
        ("dep::phantom", "entry-refused(magic)"),
        ("dep::raw_arr", "entry-refused(magic)"),
        ("dep::bump", "absent(unsited-panic)"),
        ("dep::pick", "entry-refused(magic)"),
        ("dep::fwd", "absent(template-unsupported)"),
        ("dep::Foo::n", "absent(template-unsupported)"),
        ("dep::mut_slice", "absent(template-unsupported)"),
        ("dep::wrap", "absent(not-lowered)"),
        ("dep::later", "absent(not-lowered)"),
        ("dep::later::{closure#0}", "absent(template-unsupported)"),
        ("dep::located", "absent(caller-location)"),
        ("dep::make_closure::{closure#0}", "absent(template-pending)"),
        ("dep::cst", "entry-refused(magic)"),
        ("dep::opt_ref", "absent(not-lowered)"),
    ];
    let measured: Vec<(&str, String)> =
        expected.iter().map(|(def, _)| (*def, rmeta_of(&user_on, def))).collect();
    let pinned: Vec<(&str, String)> =
        expected.iter().map(|(def, class)| (*def, class.to_string())).collect();
    assert_eq!(measured, pinned, "each subject's class:\n{}\n{templates_on}", channel_c(&user_on));

    // ── (A') Nothing reaches strict or the scorecard ─────────────────────────
    let log = [("RUSTC_LOG", "rustc_mir_build::builder=info")];
    let strict_off = dep("strict-off", false, &["-Ztrust-ir-lower=strict"], &log);
    let strict_on = dep("strict-on", true, &["-Ztrust-ir-lower=strict"], &log);
    assert!(!strict_on.out.contains("internal compiler error"), "no ICE:\n{}", strict_on.out);
    assert_eq!(strict_off.success, strict_on.success, "the same exit status");
    let events_off = conservation_events(&strict_off.stderr);
    assert!(!events_off.is_empty(), "the info events are emitted:\n{}", strict_off.stderr);
    assert_eq!(events_off, conservation_events(&strict_on.stderr), "the same conservation events");
    let diagnostics = |s: &str| -> Vec<String> {
        s.lines()
            .filter(|l| l.starts_with("error") || l.starts_with("warning"))
            .map(str::to_string)
            .collect()
    };
    assert_eq!(diagnostics(&strict_off.stderr), diagnostics(&strict_on.stderr), "the same diagnostics");

    // ── (C) No ICE in a silent session ────────────────────────────────────────
    let silent = dep("dep-silent", true, &[], &[("TRUST_VANILLA_ANNOUNCED", "1")]);
    assert!(silent.success, "the silent switch-on build succeeds:\n{}", silent.out);
    assert!(!silent.out.contains("internal compiler error"), "no ICE:\n{}", silent.out);
    assert_eq!(
        line(&silent.out, "meta-stats trust-ir templates:"),
        templates_on,
        "and records the same classes"
    );
}
