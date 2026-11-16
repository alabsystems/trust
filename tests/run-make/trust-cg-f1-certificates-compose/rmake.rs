//! Trust (step 2 increment 5, sub-step 5.4.2; design `docs/design/2026-10-01-step2-inc5-real-calls-
//! retarget.md` §5 "Certificate" and "Closure report"): the compiler lane's CERTIFICATES FILE
//! composes and is bound to the object that ships.
//!
//! `-Ztrust-cg-f1-backend=compiler` writes `<stem>.trust-cg-certificates.json` beside the rlib: one
//! `trust-cg-bridge.call-refinement.v1` record per function, each call it makes recorded as an
//! assumption, `CoEmitted(g)` for a callee in the same object and `External(g)` for any other. Pinned:
//!
//! * `object_sha256` is the SHA-256 of the object INSIDE the rlib (a consumer reading the file can
//!   bind it to the bytes the linker sees);
//! * every `CoEmitted(g)` names a function with its own certificate in the same file (a premise
//!   that is not discharged by a certificate would be a premise nobody checks);
//! * the External set is EMPTY on Darwin: nothing outside the object is called, so no
//!   EXTERNAL-CALLEE premise is in play (the Linux `Pic` case, where a co-emitted default-visibility
//!   callee is External, is pinned by the bridge's `pic_external_default_callee_is_external_internal_callee_is_coemitted`);
//! * under the default strict policy the closure closes every function (it ships).

//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::{cmd, rfs, rust_lib_name, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

const SOURCE: &str = r#"#[inline(never)] fn cc_leaf(x: u64) -> u64 { x ^ 9 }
#[inline(never)] fn cc_mid(x: u64) -> u64 { cc_leaf(x) + 3 }
#[unsafe(no_mangle)] pub extern "C" fn cc_top(x: u64) -> u64 { cc_mid(x) ^ cc_leaf(x) }
"#;

fn object_member(rlib: &str) -> Vec<u8> {
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
    objects.pop().unwrap()
}

fn sha256(path: &str) -> String {
    let out = cmd("shasum").arg("-a").arg("256").arg(path).run().stdout_utf8();
    out.split_whitespace().next().expect("a digest").to_string()
}

fn main() {
    rfs::write("compose.rs", SOURCE);
    for opt in ["0", "2"] {
        let out = format!("out_o{opt}");
        rfs::create_dir_all(&out);
        let stderr = rustc()
            .input("compose.rs")
            .crate_name("compose")
            .crate_type("rlib")
            .edition("2021")
            .arg("-Cpanic=abort")
            .arg("-Ccodegen-units=1")
            .arg("-Coverflow-checks=off")
            .arg(format!("-Copt-level={opt}"))
            .arg("-Ztrust-verify=off")
            .arg("-Zunstable-options")
            .arg("-Zcodegen-backend=trust-cg")
            .arg("-Ztrust-cg-frontend=trust-ir")
            .arg("-Ztrust-ir-lower")
            .arg("-Ztrust-cg-f1-backend=compiler")
            .out_dir(&out)
            .env_remove(TRUST_NO_VERIFY_ENV)
            .run()
            .stderr_utf8();
        assert!(!stderr.contains("internal compiler error"), "-O{opt}: {stderr}");

        // The object inside the rlib, hashed by a tool outside the compiler. Darwin's archive
        // format may pad a member with newlines; a Mach-O object ends in its string table, so a
        // trailing newline is padding, never object bytes.
        let mut object = object_member(&format!("{out}/{}", rust_lib_name("compose")));
        while object.last() == Some(&b'\n') {
            object.pop();
        }
        let object_path = format!("compose_o{opt}.o");
        rfs::write(&object_path, &object);
        let digest = sha256(&object_path);

        let text = rfs::read_to_string(format!("{out}/compose.trust-cg-certificates.json"));
        let json: serde_json::Value = serde_json::from_str(&text).expect("certificates JSON");
        assert_eq!(json["schema"], "trust-cg-bridge.call-refinement.v1", "{text}");
        assert_eq!(json["object_sha256"], digest.as_str(), "-O{opt}: bound to the shipped object");

        let certs = json["certificates"].as_array().expect("certificates");
        let symbols: Vec<&str> = certs.iter().map(|c| c["symbol"].as_str().unwrap()).collect();
        for fragment in ["cc_leaf", "cc_mid", "cc_top"] {
            assert_eq!(
                symbols.iter().filter(|s| s.contains(fragment)).count(),
                1,
                "-O{opt}: one certificate for `{fragment}`: {symbols:?}"
            );
        }
        let mut co_emitted = 0;
        for cert in certs {
            for assumption in cert["assumptions"].as_array().expect("assumptions") {
                // `{"kind": "CoEmitted" | "External", "symbol": ...}`
                let g = assumption["symbol"].as_str().expect("an assumption names its callee");
                match assumption["kind"].as_str() {
                    Some("CoEmitted") => {
                        assert!(
                            symbols.contains(&g),
                            "-O{opt}: `CoEmitted({g})` has no certificate"
                        );
                        co_emitted += 1;
                    }
                    _ => panic!(
                        "-O{opt}: an assumption other than CoEmitted on Darwin: {assumption}"
                    ),
                }
            }
        }
        assert!(co_emitted >= 2, "-O{opt}: the calls compose through co-emitted premises: {text}");
        let closed = json["closure"]["closed_kernel"].as_array().expect("closed_kernel");
        assert_eq!(closed.len(), certs.len(), "-O{opt}: strict closed every function: {text}");
        assert!(json["closure"]["unclosed"].as_array().expect("unclosed").is_empty());
    }
}
