//! Trust (WS5.9 / WS8.9, F-117 producer half; G8 "module identity must not depend on
//! the checkout path").
//!
//! `Module.files` is module CONTENT: `stable_digest`, the executable digest and the
//! `.trust-ir.bin` sha256 all cover it. The producer used to intern
//! `prefer_local_unconditionally()` — the checkout path — so the same crate built from
//! two directories produced two modules that differed in exactly `files[0]` (measured,
//! `critic/g8`), and `--remap-path-prefix` changed the diagnostics but not the module.
//! The producer now interns the REMAPPED rendering, and the consumer
//! (`to_mir.rs::ResolvedFiles`) resolves it by the same projection. The identity lane
//! (`trust_verify::source_span_from_rustc_span` and its two lockstep copies) renders the
//! same way before `stable_obligation_file`, so an obligation's sealed identity and the
//! `request_digest` a certificate projects are equally path-free under the remap.
//!
//! This is the in-repo port of the proof program's `critic/g8` row (finding F-117,
//! `crit.unex03`: "same path: byte-identical; moved path: the only delta is `files[0]`;
//! `--remap-path-prefix` changed nothing") — the same `p01_rust_contracts` source, the
//! same three shapes (same-path, moved, remapped A/B), now with the expected verdicts
//! inverted for the remapped pair and pinned as assertions.
//!
//! Rows, in the roadmap's shape:
//!
//! * POSITIVE — p01 compiled at paths A and B with `--remap-path-prefix=<A>=/src` and
//!   `<B>=/src` gives byte-identical `.trust-ir.bin` (hence equal `stable_digest` and
//!   executable digest: both are functions of the bytes) and byte-identical canonical
//!   text; the checkout path appears nowhere in either; `files[0]` is `/src/…`.
//! * NEGATIVE TWIN — without the remap the two modules differ, and the ONLY line of the
//!   canonical text that differs is `file 0`, which names the checkout path
//!   (`/files/0`, the pointer WS4.10's `--forbid-prefix` will report).
//! * MUTATION CONTROL (vacuity) — remapping only ONE of the two builds keeps the bytes
//!   different, so the positive row cannot pass vacuously.
//! * MUTATION CONTROL (non-injective remap) — two DIFFERENT source files remapped to ONE
//!   name (`x/m.rs` = `a + 1`, `y/m.rs` = `a + 2`, both rendered `/src/m.rs`) are REFUSED
//!   at load time with the named reason `non-injective --remap-path-prefix`, naming both
//!   local files and the shared virtual name. Measured before the refusal existed: rustc's
//!   stable file id ignores the local path of a fully remapped file, so `y/m.rs` was
//!   silently compiled from `x/m.rs`'s text (`y::m` lowered to `a + 1`) and NO consumer,
//!   including trust-ir's span resolver, could see it — there was one `SourceFile`. Two
//!   sub-controls pin the exact shape of the gate: the same crate under an INJECTIVE
//!   remap compiles, is refused nowhere (no derived-MIR `non-injective` verdict either)
//!   and is byte-identical across checkouts with both files distinct in `files`; and two
//!   BYTE-IDENTICAL files that render alike are admitted (they are indistinguishable by
//!   construction), sharing one `/src/m.rs` row.
use std::path::{Path, PathBuf};

use run_make_support::{cwd, rfs, rustc, serde_json};

const P01: &str = "p01_rust_contracts";
const COLLIDE: &str = "collide";
const NON_INJECTIVE: &str = "non-injective --remap-path-prefix";

/// Compile `<cwd>/<dir>/<krate>.rs` (an ABSOLUTE input path, the spelling that leaks a
/// checkout) as a lib with `--emit=trust-ir` into `<dir>-out`, under the given remaps.
fn emit(dir: &str, krate: &str, remaps: &[(PathBuf, &str)]) -> PathBuf {
    let out = cwd().join(format!("{dir}-out-{krate}"));
    rfs::create_dir_all(&out);
    let mut cmd = rustc();
    cmd.input(cwd().join(dir).join(format!("{krate}.rs")))
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&out)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Awarnings");
    for (from, to) in remaps {
        cmd.arg(format!("--remap-path-prefix={}={to}", from.display()));
    }
    cmd.run();
    assert!(out.join(format!("{krate}.trust-ir.bin")).is_file(), "missing .bin in {dir}");
    out
}

/// Like [`emit`], but the compile must FAIL; returns its stderr.
fn emit_refused(dir: &str, krate: &str, remaps: &[(PathBuf, &str)]) -> String {
    let out = cwd().join(format!("{dir}-out-{krate}"));
    rfs::create_dir_all(&out);
    let mut cmd = rustc();
    cmd.input(cwd().join(dir).join(format!("{krate}.rs")))
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&out)
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Awarnings");
    for (from, to) in remaps {
        cmd.arg(format!("--remap-path-prefix={}={to}", from.display()));
    }
    let output = cmd.run_fail();
    assert!(
        !out.join(format!("{krate}.trust-ir.bin")).is_file(),
        "a refused compile must not publish a module in {dir}"
    );
    output.stderr_utf8()
}

fn artifact(out: &Path, krate: &str, suffix: &str) -> PathBuf {
    out.join(format!("{krate}.trust-ir.{suffix}"))
}

/// Copy the fixture tree for `krate` into `<cwd>/<dir>` so the same source exists at two
/// distinct absolute paths.
fn checkout(dir: &str, krate: &str) {
    let root = cwd().join(dir);
    rfs::create_dir_all(&root);
    rfs::copy(format!("{krate}.rs"), root.join(format!("{krate}.rs")));
    if krate == COLLIDE {
        for sub in ["x", "y"] {
            rfs::create_dir_all(root.join(sub));
            rfs::copy(format!("{sub}/m.rs"), root.join(sub).join("m.rs"));
        }
    }
}

fn bytes_contain(haystack: &[u8], needle: &str) -> bool {
    let needle = needle.as_bytes();
    haystack.windows(needle.len()).any(|w| w == needle)
}

/// The `file <n> "<path>"` rows of a canonical-text dump.
fn file_rows(text: &str) -> Vec<&str> {
    text.lines().filter(|l| l.starts_with("file ")).collect()
}

/// `(def_path, derived_mir.verdict, derived_mir.detail)` for every body in coverage.json.
fn derived_verdicts(out: &Path, krate: &str) -> Vec<(String, String, String)> {
    let cov: serde_json::Value =
        serde_json::from_slice(&rfs::read(artifact(out, krate, "coverage.json")))
            .expect("coverage.json must be JSON");
    cov["bodies"]
        .as_array()
        .expect("coverage bodies")
        .iter()
        .map(|b| {
            let d = &b["differentials"]["derived_mir"];
            (
                b["def_path"].as_str().unwrap_or("").to_string(),
                d["verdict"].as_str().unwrap_or("").to_string(),
                d["detail"].as_str().unwrap_or("").to_string(),
            )
        })
        .collect()
}

fn main() {
    let a = cwd().join("a");
    let b = cwd().join("b");
    checkout("a", P01);
    checkout("b", P01);

    // ---- POSITIVE: remapped at both paths -> byte-identical module ------------------
    let a_remap = emit("a", P01, &[(a.clone(), "/src")]);
    let b_remap = emit("b", P01, &[(b.clone(), "/src")]);
    let a_bin = rfs::read(artifact(&a_remap, P01, "bin"));
    let b_bin = rfs::read(artifact(&b_remap, P01, "bin"));
    let a_txt = rfs::read_to_string(artifact(&a_remap, P01, "txt"));
    let b_txt = rfs::read_to_string(artifact(&b_remap, P01, "txt"));
    assert!(
        a_bin == b_bin,
        "G8: the same crate built at two remapped checkouts must give a byte-identical \
         .trust-ir.bin (sha256, stable_digest and executable digest are all functions of \
         these bytes)"
    );
    assert_eq!(a_txt, b_txt, "G8: the canonical text must be byte-identical as well");
    for (what, blob) in [("bin", &a_bin), ("txt", &a_txt.clone().into_bytes())] {
        assert!(
            !bytes_contain(blob, &a.display().to_string()),
            "the checkout path `{}` leaked into the remapped .{what}",
            a.display()
        );
        assert!(!bytes_contain(blob, &cwd().display().to_string()), "cwd leaked into .{what}");
    }
    let rows = file_rows(&a_txt);
    assert!(
        rows.iter().any(|r| r.starts_with("file 0 \"/src/p01_rust_contracts.rs\"")),
        "files[0] must be the REMAPPED name; file rows were: {rows:?}"
    );

    // ---- NEGATIVE TWIN: no remap -> the modules differ, in exactly files[0] -----------
    let a_raw = emit("a", P01, &[]);
    let b_raw = emit("b", P01, &[]);
    let a_raw_bin = rfs::read(artifact(&a_raw, P01, "bin"));
    let b_raw_bin = rfs::read(artifact(&b_raw, P01, "bin"));
    assert!(a_raw_bin != b_raw_bin, "negative twin: unremapped builds must differ");
    assert!(
        bytes_contain(&a_raw_bin, &a.join("p01_rust_contracts.rs").display().to_string()),
        "negative twin: the unremapped .bin must embed the checkout path"
    );
    let a_raw_txt = rfs::read_to_string(artifact(&a_raw, P01, "txt"));
    let b_raw_txt = rfs::read_to_string(artifact(&b_raw, P01, "txt"));
    let differing: Vec<(&str, &str)> =
        a_raw_txt.lines().zip(b_raw_txt.lines()).filter(|(l, r)| l != r).collect();
    assert_eq!(a_raw_txt.lines().count(), b_raw_txt.lines().count());
    assert_eq!(
        differing.len(),
        1,
        "negative twin: exactly ONE canonical-text line may differ between the two \
         checkouts (files[0]); got {differing:#?}"
    );
    let (l, r) = differing[0];
    let a_name = format!("file 0 \"{}\"", a.join("p01_rust_contracts.rs").display());
    let b_name = format!("file 0 \"{}\"", b.join("p01_rust_contracts.rs").display());
    assert_eq!(l, a_name, "the differing line must be /files/0 naming checkout A");
    assert_eq!(r, b_name, "the differing line must be /files/0 naming checkout B");
    // Every other row of the module — obligation text, names, constants — is
    // path-free even without a remap, so `files` is the only lane the remap has to
    // close (the identity-lane converters stay as they are; measured here).

    // ---- MUTATION CONTROL (vacuity): remap only one side -> still different ---------
    assert!(
        a_bin != b_raw_bin && a_raw_bin != b_bin,
        "control: remapping only one of the two builds must keep the modules different"
    );
    assert!(
        rfs::read(artifact(&emit("a", P01, &[(a.clone(), "/src")]), P01, "bin")) == a_bin,
        "control: the remapped build must be reproducible at the same path"
    );

    // ---- MUTATION CONTROL (non-injective remap): refused at LOAD time, by NAME --------
    checkout("ca", COLLIDE);
    checkout("cb", COLLIDE);
    let ca = cwd().join("ca");
    let cb = cwd().join("cb");
    // Both `ca/x` and `ca/y` render as `/src`, so `x/m.rs` (`a + 1`) and `y/m.rs`
    // (`a + 2`) both become `/src/m.rs`. rustc keys loaded files on the REMAPPED name, so
    // without the gate the second file is compiled from the first's text: the refusal
    // must fire before that, naming the remap, both local files and the virtual name.
    let stderr = emit_refused("ca", COLLIDE, &[(ca.join("x"), "/src"), (ca.join("y"), "/src")]);
    assert!(stderr.contains(NON_INJECTIVE), "control: the named refusal is missing:\n{stderr}");
    for needle in [
        "both render as `/src/m.rs`",
        &ca.join("x").join("m.rs").display().to_string(),
        &ca.join("y").join("m.rs").display().to_string(),
        "their contents differ",
    ] {
        assert!(stderr.contains(needle), "control: refusal does not name `{needle}`:\n{stderr}");
    }

    // Sub-control: two BYTE-IDENTICAL files that render alike are admitted (nothing a
    // consumer could check distinguishes them), and share one `files` row.
    checkout("cs", COLLIDE);
    let cs = cwd().join("cs");
    rfs::copy(cs.join("x").join("m.rs"), cs.join("y").join("m.rs"));
    let same = emit("cs", COLLIDE, &[(cs.join("x"), "/src"), (cs.join("y"), "/src")]);
    for (def_path, verdict, detail) in derived_verdicts(&same, COLLIDE) {
        assert!(
            !detail.contains(NON_INJECTIVE),
            "identical twins must not be refused: {def_path} {verdict} {detail}"
        );
    }
    let same_txt = rfs::read_to_string(artifact(&same, COLLIDE, "txt"));
    assert_eq!(
        file_rows(&same_txt).iter().filter(|r| r.contains("\"/src/m.rs\"")).count(),
        1,
        "identical twins share one virtual file row: {:?}",
        file_rows(&same_txt)
    );

    // The same crate under an INJECTIVE remap: refused nowhere, identical across paths.
    let ca_ok = emit("ca", COLLIDE, &[(ca.clone(), "/src")]);
    let cb_ok = emit("cb", COLLIDE, &[(cb.clone(), "/src")]);
    for (def_path, verdict, detail) in derived_verdicts(&ca_ok, COLLIDE) {
        assert!(
            !detail.contains(NON_INJECTIVE),
            "an injective remap must not be refused: {def_path} {verdict} {detail}"
        );
    }
    assert!(
        rfs::read(artifact(&ca_ok, COLLIDE, "bin")) == rfs::read(artifact(&cb_ok, COLLIDE, "bin")),
        "G8: a multi-file crate under an injective remap is byte-identical across checkouts"
    );
    let ca_ok_txt = rfs::read_to_string(artifact(&ca_ok, COLLIDE, "txt"));
    let ok_rows = file_rows(&ca_ok_txt);
    assert!(
        ok_rows.iter().any(|r| r.contains("\"/src/x/m.rs\""))
            && ok_rows.iter().any(|r| r.contains("\"/src/y/m.rs\"")),
        "the injective remap keeps both files distinct: {ok_rows:?}"
    );
}
