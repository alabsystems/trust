//@ ignore-cross-compile
//! Compare an ordinary FnOnce capture frame with native size/alignment and require its typed caller.
use run_make_support::{cmd, rfs, rustc_path, serde_json, trust_ir};
use trust_ir::reference::{binary::deserialize_module, Ty};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    rfs::write(
        "native.rs",
        format!(
            "{}\nfn main() {{ let (s, a, v) = native_layout(); assert_eq!(v, 12); println!(\"{{s}} {{a}}\"); }}",
            rfs::read_to_string("subject.rs")
        ),
    );
    cmd(rustc_path())
        .args([
            "native.rs", "--edition=2021", "-Ztrust-verify=off", "-Ztrust-ir-lower=off",
            "-Coverflow-checks=on", "-Copt-level=0", "-o", "native",
        ])
        .run();
    let native = cmd("./native").run().stdout_utf8();
    let expected: Vec<u64> = native.split_whitespace().map(|s| s.parse().unwrap()).collect();
    assert_eq!(expected.len(), 2);
    cmd(rustc_path())
        .args([
            "subject.rs", "--edition=2021", "--crate-type=lib", "--crate-name=closure_layout",
            "--emit=metadata", "-Coverflow-checks=on", "-Copt-level=0", "-Zthreads=1",
            "-Ztrust-verify=off", "-Ztrust-ir-lower=on", "-Ztrust-ir-flip=no",
            "-Ztrust-dump=ir:ir", "-o", "subject.rmeta",
        ])
        .run();
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read("ir/closure_layout.coverage.json")).unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    let module = deserialize_module(&rfs::read("ir/closure_layout.trust-ir.bin")).unwrap();
    module.validate_closure_layouts().unwrap();
    let functions: Vec<_> = module.functions.iter().filter(|f| {
        f.display_path.as_deref() == Some("once_layout::{closure#0}")
    }).collect();
    assert_eq!(functions.len(), 1, "the actual lowered closure body must be retained");
    let function = functions[0];
    let signature = module.func_type(function.ty).unwrap();
    let Ty::Closure(id) = signature.params[0] else {
        panic!("FnOnce environment must retain its first-class closure type");
    };
    let frame = module.closure_layout_descriptor(id).unwrap().unwrap();
    assert_eq!([frame.size, frame.align], [expected[0], expected[1]]);
    assert_eq!(frame.capture_offsets.len(), 2);
    assert_ne!(frame.capture_offsets[0], frame.capture_offsets[1]);
    let rows = coverage["bodies"].as_array().unwrap();
    for path in ["once_layout::{closure#0}", "moved_mutable_write::{closure#0}"] {
        let row = rows.iter().find(|row| row["def_path"] == path).unwrap();
        assert_eq!(row["lowered"], true, "{path}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{path}: {row}");
    }
    let raw = rows.iter().find(|row| row["def_path"] == "moved_raw_pointer::{closure#0}").unwrap();
    assert_eq!(raw["lowered"], false, "raw pointer must not gain reference rights");
    assert!(raw["unsupported"].as_array().unwrap().iter()
        .any(|reason| reason[0] == "Deref(non-borrow ptr)"));
    let escaped = rows.iter().find(|row| row["def_path"] == "escaped_local").unwrap();
    assert_eq!(escaped["lowered"], false, "closure must retain captured frame provenance");
    assert!(escaped["unsupported"].as_array().unwrap().iter()
        .any(|reason| reason[0] == "Return(borrow ptr escapes tail)"));
    for name in ["returned_param", "alias_returned_param", "local_write_through_result"] {
        let row = rows.iter().find(|row| row["def_path"] == name).unwrap();
        assert_eq!(row["lowered"], true, "{name}: {row}");
        assert!(row["unsupported"].as_array().unwrap().is_empty(), "{name}: {row}");
    }
    let caller = rows.iter().find(|row| row["def_path"] == "once_layout").unwrap();
    assert_eq!(caller["lowered"], true, "{caller}");
    assert!(caller["unsupported"].as_array().unwrap().is_empty(), "{caller}");
    let closure = rows.iter().find(|row| row["def_path"] == "once_layout::{closure#0}").unwrap();
    assert_eq!(closure["lowered"], true, "{closure}");
    assert!(closure["unsupported"].as_array().unwrap().is_empty(), "{closure}");
}
