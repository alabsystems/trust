//! Trust: a public callable Lean definition is a root of an F1 rlib even
//! without a Rust caller. Its consumer links the emitted native symbol without
//! LLVM recompilation, and linking still requires local kernel readmission.

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::{rfs, run, run_fail, rustc};

fn main() {
    rfs::write(
        "island.rs",
        r#"clean {
    def island_double (x : UInt64) : UInt64 := x + x
}
"#,
    );
    rfs::write("driver.rs", "fn main() { assert_eq!(island::island_double(21), 42); }");
    rfs::write("wrong_driver.rs", "fn main() { assert_eq!(island::island_double(21), 43); }");
    for verification in ["on", "off"] {
        let output = rustc()
            .input("island.rs")
            .crate_type("rlib")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-cg-f1-backend=compiler")
            .arg("-Ztrust-ir-lower=on")
            .arg(format!("-Ztrust-verify={verification}"))
            .arg("-Zprint-mono-items=yes")
            .env_remove("TRUST_NO_VERIFY")
            .run();
        output.assert_stdout_contains("island_double");
        output.assert_stderr_contains("compiled 1 function(s) in 1 module(s)");
        output.assert_stderr_contains(
            "`clean_origin_mir` reached: codegen 0, inventory 0, recorder 0",
        );
        let linked = rustc()
            .input("driver.rs")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg(format!("-Ztrust-verify={verification}"))
            .arg("-Zprint-mono-items=yes")
            .extern_("island", "libisland.rlib")
            .output("driver")
            .env_remove("TRUST_NO_VERIFY")
            .run();
        linked.assert_stdout_not_contains("MONO_ITEM fn island::island_double");
        run("driver");

        // The imported definition supplies an equality, not permission to prove
        // any caller assertion. A wrong claim must remain refused on the verified
        // lane and fail its retained runtime assertion on the unverified lane.
        let mut wrong = rustc();
        wrong.input("wrong_driver.rs")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg(format!("-Ztrust-verify={verification}"))
            .extern_("island", "libisland.rlib")
            .output("wrong_driver")
            .env_remove("TRUST_NO_VERIFY");
        if verification == "on" {
            let refused = wrong.run_fail();
            refused.assert_stderr_contains("Trust Level 0 safety verification");
            refused.assert_stderr_not_contains("internal compiler error");
        } else {
            wrong.run();
            run_fail("wrong_driver");
        }

        // The shared v1/v2 digest prefix is magic, format, declaration,
        // kernel version. Keep framing intact and alter only a version digit.
        let mut bytes = rfs::read("libisland.rlib");
        let hits: Vec<_> = bytes.windows(4).enumerate()
            .filter_map(|(at, word)| (word == b"TVDG").then_some(at)).collect();
        assert_eq!(hits.len(), 1, "one exported Clean digest");
        let mut at = hits[0] + 4;
        assert!(matches!(bytes[at], 1 | 2));
        at += 1;
        let decl_len = u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize;
        at += 4;
        assert_eq!(&bytes[at..at + decl_len], b"island_double");
        at += decl_len;
        let version_len = u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize;
        at += 4;
        assert!(version_len > 0 && bytes[at].is_ascii_digit());
        let original = String::from_utf8(bytes[at..at + version_len].to_vec()).unwrap();
        bytes[at] = if bytes[at] == b'9' { b'8' } else { b'9' };
        let tampered = String::from_utf8(bytes[at..at + version_len].to_vec()).unwrap();
        rfs::write("libisland_tampered.rlib", bytes);
        let refused = rustc()
            .input("driver.rs")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg(format!("-Ztrust-verify={verification}"))
            .extern_("island", "libisland_tampered.rlib")
            .output("tampered_driver")
            .env_remove("TRUST_NO_VERIFY")
            .run_fail();
        refused.assert_stderr_contains(format!(
            "minted under Clean kernel {tampered}, but this build links kernel {original}"
        ));
        refused.assert_stderr_not_contains("internal compiler error");
    }
}
