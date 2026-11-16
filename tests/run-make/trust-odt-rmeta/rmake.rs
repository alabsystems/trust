// Trust: actual rmeta data transport under verification on and off. Kernel B1
// mutant/refusal controls live in trust-certify::odt::tests and use the same wire.
// This fixture claims transport and ordinary Rust compatibility, not E6 import
// (TG11) or a compiler proof of its Rust reader.
use run_make_support::{cmd, rfs, rustc_path, serde_json};
use serde_json::Value;

fn entries(path: &str) -> Vec<Value> {
    let bytes = rfs::read(path);
    let prefix = b"{\"version\":1,\"declaration\":";
    let mut entries = Vec::new();
    for (start, window) in bytes.windows(prefix.len()).enumerate() {
        if window == prefix {
            let mut stream = serde_json::Deserializer::from_slice(&bytes[start..]).into_iter::<Value>();
            entries.push(stream.next().expect("entry starts here").expect("canonical ODT JSON"));
        }
    }
    entries.sort_by_key(|v| v["logical_face"]["kernel_name"].as_str().unwrap().to_owned());
    assert_eq!(entries.len(), 5, "every eligible exported ADT has a row");
    let text = String::from_utf8_lossy(&bytes);
    for refused in ["usize", "isize", "char", "f32", "f64", "u128", "i128", "generic parameters", "enum payloads", "is a union"] {
        assert!(text.contains(refused), "missing named refusal {refused}");
    }
    for entry in &entries {
        assert_eq!(entry["version"], 1);
        assert_eq!(entry["declaration"]["shape"], entry["logical_face"]["shape"]);
        assert_eq!(entry["content_digest"].as_str().unwrap().len(), 64);
    }
    entries
}

fn compile(mode: &str, changed: bool, output: &str) {
    let mut compiler = cmd(rustc_path());
    compiler.args(["aux.rs", "--crate-name=odt_aux", "--crate-type=lib", "--emit=metadata", "-o", output]);
    compiler.arg(format!("-Ztrust-verify={mode}"));
    if changed { compiler.arg("--cfg=changed"); }
    compiler.run();
}

// Each name and the member count fit the source bounds, but both copies in
// the wire entry exceed 1 MiB. Ordinary valid Rust still compiles; no face leaks.
fn oversized_face_is_refused_without_rejecting_rust() {
    let mut source = String::from("#![allow(dead_code)]\npub struct Oversized {\n");
    for i in 0..1000 {
        source.push_str(&format!("pub f{i}_{}: u8,\n", "x".repeat(600)));
    }
    source.push_str("}\n");
    rfs::write("oversized.rs", source);
    cmd(rustc_path()).args(["oversized.rs", "--crate-type=lib", "--emit=metadata",
        "-Ztrust-verify=off", "-o", "liboversized.rmeta"]).run();
    let bytes = rfs::read("liboversized.rmeta");
    let text = String::from_utf8_lossy(&bytes);
    assert!(text.contains("trust-odt-refused-v1:ODT transport exceeds 1 MiB"));
    assert!(!text.contains("{\"version\":1,\"declaration\":"), "oversized candidate earned no face");
}

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    oversized_face_is_refused_without_rejecting_rust();
    compile("off", false, "liboff.rmeta");
    let baseline = entries("liboff.rmeta");
    // Independent expectations from the actual Rust fixture: comparing only
    // the producer's declaration and generated face could share a reader bug.
    let fields = baseline.iter().filter_map(|v| v["declaration"]["shape"]["ScalarStruct"]["fields"].as_array())
        .find(|fields| fields.first().is_some_and(|f| f["name"] == "flag")).unwrap();
    let names: Vec<_> = fields.iter().map(|f| f["name"].as_str().unwrap()).collect();
    let scalars: Vec<_> = fields.iter().map(|f| f["scalar"].as_str().unwrap()).collect();
    assert_eq!(names, ["flag", "a", "b", "c", "d", "e", "f", "g", "h"]);
    assert_eq!(scalars, ["Bool", "U8", "U16", "U32", "U64", "I8", "I16", "I32", "I64"]);
    compile("on", false, "libon.rmeta");
    let verified = entries("libon.rmeta");
    assert_eq!(baseline, verified, "ODT faces do not depend on the verifier lane");
    cmd(rustc_path()).args(["consumer.rs", "--crate-type=lib", "--emit=metadata",
        "--extern=odt_aux=liboff.rmeta", "-Ztrust-verify=off"]).run();
    compile("off", true, "libchanged.rmeta");
    let changed = entries("libchanged.rmeta");
    let old_digests: Vec<_> = baseline.iter().map(|v| v["content_digest"].clone()).collect();
    let new_digests: Vec<_> = changed.iter().map(|v| v["content_digest"].clone()).collect();
    assert_ne!(old_digests, new_digests, "changed fields/tags invalidate content identity");
    let tags: Vec<_> = baseline.iter().filter_map(|v| v["declaration"]["shape"]["FieldlessEnum"]["variants"].as_array())
        .find(|v| !v.is_empty()).unwrap().iter().map(|v| v["discriminant"].as_str().unwrap()).collect();
    assert_eq!(tags, ["-3", "42"], "source order and signed tags survive rmeta");
}
