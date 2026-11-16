//! Step 2 increment 6, step 6.2: trust-ir in metadata — the carrier
//! (`docs/design/2026-10-02-step2-inc6-trust-ir-in-metadata.md` §2.6, §10 step 6.2).
//!
//! A dependency built with the direct producer on writes one opaque trust-ir entry per
//! definition rustc encodes `optimized_mir` for and the producer could encode (the `trust_ir_entry`
//! table), plus a crate header naming why every other such definition carries none. A consumer
//! reads them back through the `trust_ir_entry` / `trust_ir_crate_header` queries; probe channel
//! C prints what it found per upstream plain item (`rmeta=`), after decoding the entry and
//! checking its magic, schema, producing trust-ir version, binding (`StableCrateId`,
//! `DefPathHash`) and recomputed digest.
//!
//! Pins:
//!  * `mix` (`x ^ 0x5a5a_5a5a`, the design's subject) and `twice` (two calls to `mix`) travel:
//!    `rmeta=entry(digest-ok,functions=1,..)` and `functions=2` (the body plus `mix`'s
//!    declaration, named by the producing session's v0 symbol, never by a display path or a
//!    reserved name);
//!  * `bump` (`x + 1` with overflow checks) is absent with the encoder's recorded reason,
//!    `unsited-panic` (D19: trust-ir v51 spells no panic site), and `ident::<u32>` with
//!    `template-pending` (level S needs trust-ir amendment S);
//!  * `checked` (`x.unwrap()`, a call to the `#[track_caller]` `Option::unwrap`) and `located`
//!    (itself `#[track_caller]`) are absent, `caller-location`: the symbol's ABI takes a hidden
//!    `&'static Location` the trust-ir signature and call do not carry (review 2026-10-05; both
//!    were ENCODED before, declared and named with the wrong arity);
//!  * `-Zmeta-stats` reports the entries as their own `trust-ir` section;
//!  * two builds of the dependency write byte-identical entries;
//!  * under `--remap-path-prefix` no entry, and nothing else in rmeta, carries the build
//!    directory (review 2026-10-05: every entry carried the unremapped absolute path before);
//!  * builds from two DIFFERENT directories (of different lengths), each remapping its own
//!    directory to the same prefix, write byte-identical entries, equal to the remapped build's
//!    (review 2026-10-05: the two builds above share one source path, so they could not see a
//!    path, or anything else that depends on the build directory, in an entry);
//!  * a dependency built with the producer OFF has no header, and the consumer says so
//!    (`rmeta=no-header(..)`), for every upstream row; its `-Zmeta-stats` has no `trust-ir` row
//!    at all, as before the table existed;
//!  * a proc-macro crate built with the producer ON writes its header, carrying its crate-wide
//!    refusal `proc-macro` and no row (review 2026-10-05: the encoder wrote none, so a header-less
//!    crate did not mean "built without the producer", and the header the crate reported locally
//!    differed from the one a consumer read).
//@ ignore-cross-compile

use run_make_support::{rfs, rustc};

const DEP: &str = r#"#![crate_type = "lib"]

#[inline]
pub fn mix(x: u32) -> u32 {
    x ^ 0x5a5a_5a5a
}

#[inline]
pub fn twice(x: u32) -> u32 {
    mix(mix(x))
}

#[inline]
pub fn bump(x: u32) -> u32 {
    x + 1
}

#[inline(never)]
pub fn ident<T>(x: T) -> T {
    x
}

#[inline]
pub fn checked(x: Option<u32>) -> u32 {
    x.unwrap()
}

#[inline]
#[track_caller]
pub fn located(x: u32) -> u32 {
    x ^ 0x0f0f
}
"#;

const PM: &str = r#"extern crate proc_macro;

use proc_macro::TokenStream;

#[proc_macro]
pub fn nothing(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}
"#;

const USER: &str = r#"#![crate_type = "lib"]

pub fn use_all(x: u32) -> u32 {
    dep::mix(x) ^ dep::twice(x) ^ dep::bump(x) ^ dep::ident(x) ^ dep::checked(Some(x))
        ^ dep::located(x)
}
"#;

fn dep(out: &str, producer: bool) -> String {
    dep_at(out, producer, "dep.rs", None)
}

fn dep_at(out: &str, producer: bool, input: &str, remap: Option<&str>) -> String {
    rfs::create_dir_all(out);
    let mut cmd = rustc();
    if let Some(remap) = remap {
        cmd.arg(format!("--remap-path-prefix={remap}"));
    }
    cmd.input(input)
        .crate_name("dep")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Coverflow-checks=on")
        .arg("-Ztrust-verify=off")
        .arg("--emit=metadata,link")
        .arg("-Zmeta-stats")
        .out_dir(out);
    if producer {
        cmd.arg("-Ztrust-ir-lower");
    }
    let out = cmd.run();
    format!("{}{}", out.stdout_utf8(), out.stderr_utf8())
}

fn user(dep_out: &str) -> String {
    let out = rustc()
        .input("user.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .extern_("dep", format!("{dep_out}/libdep.rlib"))
        .out_dir("user-out")
        .run();
    out.stderr_utf8()
}

fn row<'a>(stderr: &'a str, def: &str) -> &'a str {
    let rows: Vec<&str> = stderr
        .lines()
        .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym=") && l.contains(&format!(" def={def} ")))
        .collect();
    assert_eq!(rows.len(), 1, "one channel-C row for `{def}`:\n{stderr}");
    rows[0]
}

/// Every trust-ir entry blob in an rmeta file. An entry rides rmeta as raw bytes
/// (`TrustIrEntryBlob`), framed by the producer: magic `TRIRENTR`, schema and trust-ir version
/// (u32 each), the whole-envelope digest and a length-framed payload. The payload carries the
/// binding, producing overflow mode, module digest, and length-framed module/evidence bytes.
fn entries(rmeta: &[u8]) -> Vec<Vec<u8>> {
    let u64_at = |at: usize| u64::from_le_bytes(rmeta[at..at + 8].try_into().unwrap()) as usize;
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(found) = rmeta[at..].windows(8).position(|w| w == b"TRIRENTR") {
        let start = at + found;
        // Trust: entry schema 6 frames the complete owner/mode/module/evidence payload.
        assert_eq!(u32::from_le_bytes(rmeta[start + 8..start + 12].try_into().unwrap()), 6);
        let p = start + 56 + u64_at(start + 48);
        out.push(rmeta[start..p].to_vec());
        at = p;
    }
    out
}

/// Schema-6 module bytes: after the 56-byte header and payload owner, mode and module digest.
fn module_bytes(entry: &[u8]) -> &[u8] {
    let at = 56 + 16 + 1 + 32;
    let len = u64::from_le_bytes(entry[at..at + 8].try_into().unwrap()) as usize;
    &entry[at + 8..at + 8 + len]
}

fn contains(haystack: &[u8], needle: &str) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle.as_bytes())
}

/// The `-Zmeta-stats` row of the `trust-ir` section (`meta-stats trust-ir  1_234 (..)`), if any.
fn trust_ir_row(stats: &str) -> Option<&str> {
    stats.lines().find(|l| l.split_whitespace().nth(1) == Some("trust-ir"))
}

/// The size `-Zmeta-stats` reports for the `trust-ir` section.
fn trust_ir_section(stats: &str) -> usize {
    let line = trust_ir_row(stats)
        .unwrap_or_else(|| panic!("-Zmeta-stats has no trust-ir section:\n{stats}"));
    line.split_whitespace().nth(2).unwrap().replace('_', "").parse().unwrap()
}

fn main() {
    rfs::write("dep.rs", DEP);
    rfs::write("user.rs", USER);

    // ── The producer on: entries and a header ───────────────────────────────
    let stats = dep("dep-a", true);
    assert!(trust_ir_section(&stats) > 0, "the trust-ir section carries the entries:\n{stats}");
    assert!(
        stats.contains("meta-stats trust-ir per definition: 2 with both rows;"),
        "-Zmeta-stats compares `mix`'s and `twice`'s entries with their optimized_mir:\n{stats}"
    );
    assert!(
        stats.contains(
            "meta-stats trust-ir entries: 2 encoded; 4 unencoded: caller-location=2 \
             template-pending=1 unsited-panic=1"
        ),
        "the header's refusals, counted by class:\n{stats}"
    );

    let stderr = user("dep-a");
    assert!(!stderr.contains("internal compiler error"), "no ICE:\n{stderr}");
    let mix = row(&stderr, "dep::mix");
    assert!(mix.contains("rmeta=entry(digest-ok,functions=1,"), "`mix` travels: {mix}");
    let twice = row(&stderr, "dep::twice");
    assert!(
        twice.contains("rmeta=entry(digest-ok,functions=2,"),
        "`twice` travels with `mix` declared by symbol: {twice}"
    );
    let bump = row(&stderr, "dep::bump");
    assert!(
        bump.contains("rmeta=absent(unsited-panic)"),
        "an unsited overflow check is not encoded, and the header says why: {bump}"
    );
    let ident = row(&stderr, "dep::ident");
    assert!(
        ident.contains("rmeta=absent(template-pending)"),
        "a generic definition waits for level S, and the header says why: {ident}"
    );
    for def in ["dep::checked", "dep::located"] {
        let r = row(&stderr, def);
        assert!(
            r.contains("rmeta=absent(caller-location)"),
            "a #[track_caller] callee or body is never written with the wrong arity: {r}"
        );
    }

    // ── Deterministic: a second build writes the same entries ────────────────
    // The entries, not the whole file: an rmeta may differ between two builds for reasons that
    // predate trust-ir (measured on itoa 1.0.18 with the producer off), and an entry is the
    // claim this fixture pins.
    dep("dep-b", true);
    let (a, b) = (entries(&rfs::read("dep-a/libdep.rmeta")), entries(&rfs::read("dep-b/libdep.rmeta")));
    assert_eq!(a.len(), 2, "`mix` and `twice` carry entries");
    assert_eq!(a, b, "two builds of the dependency write byte-identical entries");

    // ── Callees by symbol: `twice` declares `mix` by its v0 symbol ────────────
    // (The PRODUCING session's symbol: for an `#[inline]` callee at -O0 it embeds the
    // instantiating crate, which a consumer re-derives; see `rmeta_entry`'s module doc.)
    let (mix_entry, twice_entry) = (module_bytes(&a[0]), module_bytes(&a[1]));
    assert!(contains(mix_entry, "3dep3mix"), "`mix`'s body is named by its symbol");
    assert!(contains(twice_entry, "3dep5twice"), "`twice`'s body is named by its symbol");
    assert!(contains(twice_entry, "3dep3mix"), "`twice` declares `mix` by its symbol");
    for entry in [mix_entry, twice_entry] {
        assert!(!contains(entry, "dep::mix"), "no display path names a function");
        assert!(!contains(entry, "!trust_"), "no reserved name remains");
    }

    // ── --remap-path-prefix: no entry carries the build directory ────────────
    let cwd = std::env::current_dir().unwrap();
    let cwd = cwd.to_str().unwrap().to_string();
    let absolute = format!("{cwd}/dep.rs");
    dep_at("dep-remap", true, &absolute, Some(&format!("{cwd}=/REMAPPED")));
    let rmeta = rfs::read("dep-remap/libdep.rmeta");
    let remapped = entries(&rmeta);
    assert_eq!(remapped.len(), 2, "the remapped build writes the same two entries");
    for entry in &remapped {
        assert!(contains(module_bytes(entry), "/REMAPPED/dep.rs"), "the remapped name travels");
        assert!(!contains(entry, &cwd), "an entry never carries the unremapped build directory");
    }
    assert!(!contains(&rmeta, &cwd), "nothing in rmeta carries the unremapped build directory");

    // ── Deterministic across build directories ───────────────────────────────
    let build_in = |dir: &str| -> Vec<Vec<u8>> {
        let root = format!("{cwd}/{dir}");
        rfs::create_dir_all(&root);
        rfs::write(format!("{root}/dep.rs"), DEP);
        let (out, input, remap) =
            (format!("{dir}-out"), format!("{root}/dep.rs"), format!("{root}=/REMAPPED"));
        dep_at(&out, true, &input, Some(&remap));
        entries(&rfs::read(format!("{dir}-out/libdep.rmeta")))
    };
    let near = build_in("d1");
    let far = build_in("a-much-longer-build-directory-name/nested");
    assert_eq!(near.len(), 2, "the same two entries");
    assert_eq!(near, far, "builds from two directories write byte-identical entries");
    assert_eq!(near, remapped, "the same entries as the build from the fixture's directory");

    // ── The producer off: no header, and the consumer says so ────────────────
    let off_stats = dep("dep-off", false);
    assert!(
        trust_ir_row(&off_stats).is_none(),
        "without the producer -Zmeta-stats has no trust-ir row at all:\n{off_stats}"
    );
    assert!(!off_stats.contains("trust-ir"), "and nothing else about trust-ir");
    let stderr = user("dep-off");
    for def in ["dep::mix", "dep::twice", "dep::bump", "dep::ident", "dep::checked", "dep::located"] {
        let r = row(&stderr, def);
        assert!(
            r.contains("rmeta=no-header(compiled-without-the-producer)"),
            "a dependency built without the producer has no header: {r}"
        );
    }

    // ── A proc-macro crate: its header, with its crate-wide refusal ───────────
    rfs::write("pm.rs", PM);
    let out = rustc()
        .input("pm.rs")
        .crate_type("proc-macro")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .arg("-Zmeta-stats")
        .arg("-Ztrust-ir-lower")
        .out_dir("pm-out")
        .run();
    let pm_stats = format!("{}{}", out.stdout_utf8(), out.stderr_utf8());
    assert!(
        pm_stats.contains("meta-stats trust-ir entries: 0 encoded; 1 unencoded: proc-macro=1"),
        "a proc-macro crate built with the producer writes its header:\n{pm_stats}"
    );
}
