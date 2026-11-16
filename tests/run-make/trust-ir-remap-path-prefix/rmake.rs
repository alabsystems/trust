// Trust (WS5.9, F-117 — G8 `ir-g8-remap`): `--remap-path-prefix` is honoured for
// `Module.files`, so a published trust-ir module does not embed the checkout path.
//
// MEASURED before this increment (critic/g8, and again at 079d96c2e with this test's own
// recipe): the same crate built from two checkouts differed in exactly one row,
// `files[0]`, which carried the absolute source path; `--remap-path-prefix` changed the
// diagnostics (`--> /src/...`) but not the module, because `to_source_span` interned
// `FileName::prefer_local_unconditionally()` — the rendering rustc documents as "Avoid
// embedding this in build artifacts". Since `ModuleImport.digest` IS `stable_digest`, a
// dependency built on one machine could never authenticate on another.
//
// Rows, each with its twin (roadmap §2.4: a PASS row carries a right-reason negative):
//   * POSITIVE   — two checkouts, each remapped to `/src`: byte-identical `.trust-ir.bin`
//                  and `.trust-ir.txt`, equal per-body lineage digests, and the checkout
//                  path occurs NOWHERE in either artifact (`files[0]` is `/src/<file>`).
//   * NEGATIVE   — the same two checkouts WITHOUT the remap differ, and each artifact
//                  carries its own checkout path exactly where F-117 measured it.
//   * MUTATION 1 — remapping only ONE of the two builds keeps the bytes different, so the
//                  positive row cannot pass vacuously (WS8.9 control).
//   * MUTATION 2 — two source files remapped to ONE name (a non-injective remap) never
//                  yield a module whose spans are bound to whichever file the source map
//                  loaded first (WS8.9 control): the build FAILS with WS8.9's named
//                  load-time refusal (`rustc_span::SourceMap::refuse_remap_collision`,
//                  "non-injective --remap-path-prefix") and publishes nothing. Its twin:
//                  the same two files under an injective remap round-trip (`agreed`).
//
// This test was written for WS5.9 and reconciled onto WS8.9 (the ONE F-117 change,
// roadmap assembly note). WS8.9's own `trust-ir-remap-path-identity` holds the positive,
// negative, one-sided and non-injective rows over its p01 program; the rows here that it
// does not hold are the per-body lineage equality, the remapped `files[0]` value, the
// derived-MIR `agreed` round trip through `to_mir.rs::ResolvedFiles`, and the ANCHOR ROW.
//   * ANCHOR ROW  — the rule is EVERY file string in the module, not `files[]` alone. A
//                  `#[trust::action]` crate also publishes `SpecAnchor.span`
//                  (`file:line:col: line:col`), which was rendered by
//                  `span_to_diagnostic_string` — a rendering that follows the DIAGNOSTICS
//                  component of `--remap-path-scope`, so under cargo's `trim-paths`
//                  default (`object`) it kept the checkout while `files[]` lost it. Built
//                  under `--remap-path-scope=object` (the scope where the two renderings
//                  DIFFER, so the row cannot pass by accident), two checkouts are
//                  byte-identical and the anchor span starts with `/src/`; its twin, the
//                  unremapped build, embeds the checkout exactly twice (files row and
//                  anchor row).
//
// The `stable_digest` equality the roadmap names is implied by byte identity of the binary
// encoding (the digest is a function of the decoded module); the trust-ir `digest`
// subcommand is not on this test's path, so the bytes are the witness here.

use std::path::{Path, PathBuf};

use run_make_support::{bin_name, cmd, cwd, rfs, rustc_path, serde_json};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const CRATE_NAME: &str = "remap_probe";
const SOURCE_FILE: &str = "remap_probe.rs";
const REMAP_TARGET: &str = "/src";

const PROBE_SOURCE: &str = "pub fn clamp_add(x: u64, y: u64) -> u64 {\n    x + y\n}\n\
                            pub fn countdown(n: u64) -> u64 {\n    \
                            if n > 0 { countdown(n - 1) } else { 7 }\n}\n";

/// A crate that publishes a `SpecAnchor` (the temporal-carry shape of
/// `tests/run-make/trust-temporal-carry`), so the module carries a file string OUTSIDE
/// `files[]`: the anchor's `span`.
const TEMPORAL_PROBE_SOURCE: &str = "#![feature(register_tool)]\n\
                                     #![register_tool(trust)]\n\
                                     #![allow(dead_code)]\n\
                                     pub struct Grid {\n    \
                                     #[trust::var(name = \"scrollback\", kind = \"Seq\")]\n    \
                                     scrollback: u64,\n}\n\
                                     impl Grid {\n    \
                                     #[trust::action(name = \"Erase\", guard = \"enabled\")]\n    \
                                     pub fn erase(&mut self) {}\n}\n";

struct Artifacts {
    binary: Vec<u8>,
    text: String,
    coverage: serde_json::Value,
}

fn trustc() -> PathBuf {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    if trustc.exists() { trustc } else { rustc }
}

/// One checkout: `<cwd>/<name>/<SOURCE_FILE>`, compiled by ABSOLUTE path (the shape that
/// embeds the checkout; a relative invocation never had a prefix to strip).
fn checkout(name: &str, source: &str) -> PathBuf {
    let dir = cwd().join(name);
    rfs::create_dir_all(&dir);
    rfs::write(dir.join(SOURCE_FILE), source);
    dir
}

/// Compile `checkout` into a published trust-ir artifact set under `<checkout>/ir`, with the
/// given extra flags (`--remap-path-prefix=...` or none).
fn publish(checkout: &Path, extra: &[String]) -> Artifacts {
    let out = checkout.join("ir");
    let mut command = cmd(trustc());
    command
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg(format!("-Ztrust-dump=ir:{}", out.display()))
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={CRATE_NAME}"))
        .arg("--emit=metadata")
        .arg("-o")
        .arg(checkout.join(format!("{CRATE_NAME}.rmeta")));
    for flag in extra {
        command.arg(flag);
    }
    command.arg(checkout.join(SOURCE_FILE)).run();
    let binary = rfs::read(out.join(format!("{CRATE_NAME}.trust-ir.bin")));
    let text = rfs::read_to_string(out.join(format!("{CRATE_NAME}.trust-ir.txt")));
    let coverage =
        serde_json::from_slice(&rfs::read(out.join(format!("{CRATE_NAME}.coverage.json"))))
            .expect("coverage commit marker must be valid JSON");
    assert!(!binary.is_empty() && !text.is_empty(), "publication produced an empty artifact");
    Artifacts { binary, text, coverage }
}

fn remap(checkout: &Path) -> String {
    format!("--remap-path-prefix={}={REMAP_TARGET}", checkout.display())
}

fn count_bytes(haystack: &[u8], needle: &[u8]) -> usize {
    if needle.is_empty() || haystack.len() < needle.len() {
        return 0;
    }
    haystack.windows(needle.len()).filter(|window| *window == needle).count()
}

/// The `file <n> "<name>"` rows of the text encoding, in table order.
fn file_rows(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|line| line.strip_prefix("file "))
        .map(|rest| {
            let (_, name) = rest.split_once(' ').expect("file row carries an index and a name");
            name.trim_matches('"').to_string()
        })
        .collect()
}

/// The `span "<file>:<line>:<col>: <line>:<col>"` of the ONE `anchor machine ...` row of
/// the text encoding (the temporal probe declares exactly one action).
fn anchor_span(text: &str) -> String {
    let rows: Vec<&str> =
        text.lines().filter(|line| line.trim_start().starts_with("anchor machine ")).collect();
    assert_eq!(rows.len(), 1, "temporal probe must publish exactly one anchor:\n{text}");
    let (_, tail) = rows[0].split_once(" span \"").expect("anchor row carries a span");
    let (span, _) = tail.split_once('"').expect("anchor span is quoted");
    span.to_string()
}

fn lineages(coverage: &serde_json::Value) -> Vec<(String, String)> {
    coverage["bodies"]
        .as_array()
        .expect("coverage must inventory every body")
        .iter()
        .map(|body| {
            (
                body["def_path"].as_str().expect("def_path").to_string(),
                body["lineage"].as_str().expect("lineage").to_string(),
            )
        })
        .collect()
}

fn derived_mir_verdicts(coverage: &serde_json::Value) -> Vec<(String, String, String)> {
    coverage["bodies"]
        .as_array()
        .expect("coverage must inventory every body")
        .iter()
        .map(|body| {
            let derived = &body["differentials"]["derived_mir"];
            (
                body["def_path"].as_str().expect("def_path").to_string(),
                derived["verdict"].as_str().expect("derived-MIR verdict").to_string(),
                derived["detail"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let a = checkout("checkout-a", PROBE_SOURCE);
    let b = checkout("checkout-b", PROBE_SOURCE);
    let a_path = a.to_string_lossy().into_owned();
    let b_path = b.to_string_lossy().into_owned();
    assert_ne!(a_path, b_path);

    // ---- POSITIVE: two checkouts, both remapped, one module ---------------------------------
    let ra = publish(&a, &[remap(&a)]);
    let rb = publish(&b, &[remap(&b)]);
    assert_eq!(
        ra.binary, rb.binary,
        "remapped builds from two checkouts must be byte-identical (G8 ir-g8-remap)"
    );
    assert_eq!(ra.text, rb.text, "remapped text encodings must be identical");
    assert_eq!(lineages(&ra.coverage), lineages(&rb.coverage), "per-body lineage digests differ");
    assert_eq!(
        file_rows(&ra.text),
        vec![format!("{REMAP_TARGET}/{SOURCE_FILE}")],
        "`Module.files` must carry the REMAPPED name and nothing else"
    );
    for (label, artifact) in [("a", &ra), ("b", &rb)] {
        for (needle, what) in [(&a_path, "checkout A"), (&b_path, "checkout B")] {
            assert_eq!(
                count_bytes(&artifact.binary, needle.as_bytes()),
                0,
                "remapped binary from {label} still embeds the {what} path"
            );
            assert_eq!(
                artifact.text.matches(needle.as_str()).count(),
                0,
                "remapped text from {label} still embeds the {what} path"
            );
        }
    }
    // The round trip still binds every span: a remapped module must not degrade the
    // derived-MIR differential (the reverse lookup resolves the remapped name).
    for (def_path, verdict, detail) in derived_mir_verdicts(&ra.coverage) {
        assert_eq!(
            verdict, "agreed",
            "remapped body `{def_path}` lost its derived-MIR agreement: {detail}"
        );
    }

    // ---- NEGATIVE TWIN: without the remap the checkout path is in the module ---------------
    let na = publish(&a, &[]);
    let nb = publish(&b, &[]);
    assert_ne!(na.binary, nb.binary, "unremapped builds from two checkouts must differ (F-117)");
    assert_eq!(file_rows(&na.text), vec![format!("{a_path}/{SOURCE_FILE}")]);
    assert_eq!(file_rows(&nb.text), vec![format!("{b_path}/{SOURCE_FILE}")]);
    assert_eq!(count_bytes(&na.binary, a_path.as_bytes()), 1, "F-117's measured shape");
    assert_eq!(na.text.matches(a_path.as_str()).count(), 1, "F-117's measured shape");
    // Without any remap, the remapped rendering IS the local one: the unremapped module is
    // what this compiler always published (no byte-level behaviour change off the flag).
    assert_ne!(na.binary, ra.binary);

    // ---- MUTATION 1: remapping only one side cannot satisfy the positive row --------------
    let half = publish(&b, &[]);
    assert_ne!(ra.binary, half.binary, "one-sided remap must not read as byte-identical");

    // ---- ANCHOR ROW: every file string in the module, not `files[]` alone ------------------
    // `--remap-path-scope=object` is the witness scope: DIAGNOSTICS is not in it, so a row
    // still rendered by `span_to_diagnostic_string` (the pre-WS5.9 `SpecAnchor.span`) would
    // carry the checkout here while `files[0]` does not. Under the default scope (`all`)
    // the two renderings coincide and this row would pass vacuously.
    let ta = checkout("checkout-temporal-a", TEMPORAL_PROBE_SOURCE);
    let tb = checkout("checkout-temporal-b", TEMPORAL_PROBE_SOURCE);
    let ta_path = ta.to_string_lossy().into_owned();
    let tb_path = tb.to_string_lossy().into_owned();
    let object_scope = "--remap-path-scope=object".to_string();
    let rta = publish(&ta, &[remap(&ta), object_scope.clone()]);
    let rtb = publish(&tb, &[remap(&tb), object_scope]);
    assert_eq!(
        rta.binary, rtb.binary,
        "remapped temporal builds from two checkouts must be byte-identical (anchor row)"
    );
    assert_eq!(rta.text, rtb.text);
    let remapped_anchor = anchor_span(&rta.text);
    assert!(
        remapped_anchor.starts_with(&format!("{REMAP_TARGET}/{SOURCE_FILE}:")),
        "`SpecAnchor.span` must render the REMAPPED file under --remap-path-scope=object; \
         got {remapped_anchor:?}"
    );
    assert_eq!(file_rows(&rta.text), vec![format!("{REMAP_TARGET}/{SOURCE_FILE}")]);
    for (label, artifact) in [("a", &rta), ("b", &rtb)] {
        for (needle, what) in [(&ta_path, "checkout A"), (&tb_path, "checkout B")] {
            assert_eq!(
                count_bytes(&artifact.binary, needle.as_bytes()),
                0,
                "remapped temporal binary from {label} still embeds the {what} path"
            );
            assert_eq!(
                artifact.text.matches(needle.as_str()).count(),
                0,
                "remapped temporal text from {label} still embeds the {what} path"
            );
        }
    }
    // Twin: unremapped, the checkout is in the module exactly TWICE — the `files[0]` row
    // and the anchor span — which is the count a `files[]`-only fix would leave at one.
    let nta = publish(&ta, &[]);
    let ntb = publish(&tb, &[]);
    assert_ne!(nta.binary, ntb.binary, "unremapped temporal builds must differ (F-117)");
    assert_eq!(file_rows(&nta.text), vec![format!("{ta_path}/{SOURCE_FILE}")]);
    assert!(anchor_span(&nta.text).starts_with(&format!("{ta_path}/{SOURCE_FILE}:")));
    assert_eq!(nta.text.matches(ta_path.as_str()).count(), 2, "files row + anchor row");
    assert_eq!(count_bytes(&nta.binary, ta_path.as_bytes()), 2, "files row + anchor row");

    // ---- MUTATION 2: a non-injective remap never yields a silently mis-bound module -------
    // Two source files, `<c>/one/<SOURCE_FILE>` and `<c>/two/<SOURCE_FILE>`, in one crate.
    // Under `one=/x` AND `two=/x` both render to `/x/<SOURCE_FILE>`.
    //
    // MEASURED (2026-09-22, stage1, before WS8.9): such a build does not reach trust-ir
    // lowering at all. `RealFileName`'s `Hash` deliberately hashes ONLY the remapped path of
    // a fully remapped file (rustc_span/src/lib.rs, "#70924"), so the two files share one
    // `StableSourceFileId` and the source map handed the SECOND load the FIRST file's
    // contents — `trustc` stopped with `error: circular modules` + E0425 here, and WS8.9
    // measured the silent variant (a second module compiled from the first's text). WS8.9
    // refuses it BY NAME at load time (`SourceMap::refuse_remap_collision`, before the
    // substitution). The hazard the roadmap names (a span bound to whichever file the source
    // map loaded first) is therefore refused twice over: at load time, and — for an
    // ambiguity that does reach it, i.e. an imported file or a VIRTUAL file name — by
    // `to_mir.rs::ResolvedFiles::resolve`, whose refusal texts are pinned by the crate-lane
    // control `span_normalization_parity.rs::debug_info_round_trip_binds_the_interned_rendering`.
    // This row asserts the fail-closed half that is reachable end to end: the build fails
    // with the named refusal and publishes no module, rather than emitting one whose spans
    // point at the wrong file.
    let c = cwd().join("checkout-c");
    let one = c.join("one");
    let two = c.join("two");
    rfs::create_dir_all(&one);
    rfs::create_dir_all(&two);
    rfs::write(
        two.join(SOURCE_FILE),
        "pub fn helper(n: u64) -> u64 {\n    if n > 0 { n - 1 } else { 0 }\n}\n",
    );
    rfs::write(
        one.join(SOURCE_FILE),
        format!(
            "#[path = {:?}]\npub mod inner;\npub fn caller(n: u64) -> u64 {{\n    \
             inner::helper(n)\n}}\n",
            two.join(SOURCE_FILE).to_string_lossy()
        ),
    );
    let publish_c = |maps: &[String]| {
        let out = c.join("ir");
        let mut command = cmd(trustc());
        command
            .arg("-Ztrust-verify=off")
            .arg("-Ztrust-ir-lower")
            .arg(format!("-Ztrust-dump=ir:{}", out.display()))
            .arg("--crate-type=lib")
            .arg(format!("--crate-name={CRATE_NAME}"))
            .arg("--emit=metadata")
            .arg("-o")
            .arg(c.join(format!("{CRATE_NAME}.rmeta")));
        for map in maps {
            command.arg(map);
        }
        command.arg(one.join(SOURCE_FILE)).run();
        let text = rfs::read_to_string(out.join(format!("{CRATE_NAME}.trust-ir.txt")));
        let coverage: serde_json::Value =
            serde_json::from_slice(&rfs::read(out.join(format!("{CRATE_NAME}.coverage.json"))))
                .expect("coverage commit marker must be valid JSON");
        (text, coverage)
    };

    // Twin first: an INJECTIVE remap of the same two files round-trips.
    let (text, coverage) = publish_c(&[
        format!("--remap-path-prefix={}=/x", one.display()),
        format!("--remap-path-prefix={}=/y", two.display()),
    ]);
    let mut rows = file_rows(&text);
    rows.sort();
    assert_eq!(rows, vec![format!("/x/{SOURCE_FILE}"), format!("/y/{SOURCE_FILE}")]);
    let verdicts = derived_mir_verdicts(&coverage);
    assert!(
        verdicts.iter().any(|(def_path, _, _)| def_path == "caller")
            && verdicts.iter().any(|(def_path, _, _)| def_path == "inner::helper"),
        "probe must lower both files' bodies: {verdicts:?}"
    );
    for (def_path, verdict, detail) in &verdicts {
        assert_eq!(verdict, "agreed", "injective remap: `{def_path}` did not round-trip: {detail}");
    }

    // The control: NON-injective — both directories to `/x`. No module is published.
    let non_injective_out = c.join("ir-non-injective");
    let mut command = cmd(trustc());
    command
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg(format!("-Ztrust-dump=ir:{}", non_injective_out.display()))
        .arg("--crate-type=lib")
        .arg(format!("--crate-name={CRATE_NAME}"))
        .arg("--emit=metadata")
        .arg("-o")
        .arg(c.join(format!("{CRATE_NAME}.rmeta")))
        .arg(format!("--remap-path-prefix={}=/x", one.display()))
        .arg(format!("--remap-path-prefix={}=/x", two.display()))
        .arg(one.join(SOURCE_FILE));
    let failed = command.run_fail();
    let stderr = failed.stderr_utf8();
    assert!(
        stderr.contains("non-injective --remap-path-prefix"),
        "the non-injective build must fail with WS8.9's NAMED load-time refusal, not with \
         whatever the substituted text happens to break (`circular modules`, E0425):\n{stderr}"
    );
    assert!(
        stderr.contains(&format!("/x/{SOURCE_FILE}")),
        "the refusal must name the COLLIDED rendering the two files share:\n{stderr}"
    );
    assert!(
        !non_injective_out.join(format!("{CRATE_NAME}.trust-ir.txt")).exists()
            && !non_injective_out.join(format!("{CRATE_NAME}.trust-ir.bin")).exists(),
        "a non-injective remap must publish NO module; found one under {}",
        non_injective_out.display()
    );
}
