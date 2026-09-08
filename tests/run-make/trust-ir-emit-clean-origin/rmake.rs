//! Trust (IR-1, docs/design/2026-08-27-two-language-direct-to-trust-ir.md §3):
//! the Clean-origin RECORDING PATH — under verification, `--emit=trust-ir` on a
//! crate holding both languages publishes ONE Module carrying BOTH producers'
//! rows, with the Clean rows tier-marked and the coverage sidecar disclosing
//! exactly what was recorded.
//!
//! Pins, per the review-amended design:
//!  * the capability/authority header is BYTE-EXACT `obligation-bearing-pending-v2`
//!    (the owner-signed tier move, c2ac761224; authority axes still false)
//!    / `proof_authority: false` / `native_verification_requests: false` — the
//!    pre-existing test pins containment only; a diff here is a soundness
//!    event, not a golden to re-bless;
//!  * the `clean_origin` coverage section records `cleanWsum` at tier `gate`,
//!    with carrier-faithfulness and a digest-bound actual-Function subject;
//!  * the canonical text carries both languages' function names — the
//!    two-languages-one-module witness — and this fixture now also asserts the
//!    landed IR-5 same-crate edge repoint from Rust to the exact gated Clean
//!    FuncId. This is not G5 digest-bound cross-crate linking;
//!  * a called `Nat -> Nat` Clean definition pins the compiler-minted Rust ABI
//!    on its HIR-less Rust-callable declaration, while a called local
//!    `extern "C"` definition remains C — an exact-classifier mutation control;
//!  * under `-Ztrust-verify=off` the same crate records `"recorded": false`
//!    with the lane reason — a DISCLOSED absence, and no new fatal surface on
//!    the verification-off artifact lane.

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn main() {
    // ── verification ON: the recording path runs ────────────────────────────
    let on_dir = Path::new("emit-on");
    rfs::create_dir(&on_dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&on_dir)
        .arg("-Ztrust-verify=on")
        // Bootstrap may deauthorize its own nested compiler processes through
        // this inherited override. A run-make recipe is a new policy boundary:
        // its explicit tracked flag must determine this subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();

    let coverage = rfs::read_to_string(on_dir.join("foo.trust-ir.coverage.json"));
    let coverage_json: serde_json::Value =
        serde_json::from_str(&coverage).expect("coverage sidecar must be valid JSON");
    // Capability header, byte-exact (the design's soundness-event pin).
    for exact in [
        "\"direct_obligation_capability\": \"obligation-bearing-pending-v2\",",
        "\"proof_authority\": false,",
        "\"native_verification_requests\": false,",
    ] {
        assert!(
            coverage.contains(exact),
            "capability header line missing or altered — a soundness event, not a golden \
             to re-bless. wanted byte-exact `{exact}` in:\n{coverage}"
        );
    }
    // The clean_origin section: recorded, with exactly the target row inspected
    // structurally rather than by unrelated substring presence.
    assert!(
        coverage.contains("\"recorded\": true"),
        "clean_origin section must record under verification:\n{coverage}"
    );
    let rows =
        coverage_json["clean_origin"]["emitted"].as_array().expect("clean_origin.emitted array");
    let clean_wsum = rows
        .iter()
        .find(|row| row["clean_name"] == "cleanWsum")
        .expect("cleanWsum must have one emitted row");
    assert_eq!(clean_wsum["shape"], "wrapping-binop");
    assert_eq!(clean_wsum["tier"], "gate");
    assert_eq!(clean_wsum["judgment"], "actual-TrustIR-Function-carrier-defeq");
    assert_eq!(clean_wsum["carrier_faithfulness"], "established");
    assert_eq!(clean_wsum["body_gate"], "carrier-faithful");
    assert_eq!(clean_wsum["gate_carrier"], "UInt64");
    assert_eq!(clean_wsum["gate_method"], "definitional-equality");
    assert!(
        clean_wsum["gate_subject_digest"]
            .as_str()
            .is_some_and(|digest| digest.starts_with("sha256:")),
        "gate row must bind the exact signature/Function by SHA-256: {clean_wsum}"
    );
    assert!(
        clean_wsum["gate_scope"]
            .as_str()
            .is_some_and(|scope| scope.contains("not G5 cross-crate") && scope.contains("not G7")),
        "gate scope must not overclaim completion: {clean_wsum}"
    );
    // IR-5: the caller's declared edge is re-pointed at the appended
    // definition, disclosed in the linked array.
    let linked =
        coverage_json["clean_origin"]["linked"].as_array().expect("clean_origin.linked array");
    let clean_wsum_link = linked
        .iter()
        .find(|row| row["def_path"] == clean_wsum["def_path"])
        .expect("cleanWsum same-crate link row");
    assert_eq!(clean_wsum_link["edges_repointed"], 1);
    assert!(
        clean_wsum_link["decl_func_id"].as_u64().is_some(),
        "the linked row must preserve the exact declaration identity: {clean_wsum_link}"
    );
    let source_def_index = clean_wsum_link["source_def_index"]
        .as_u64()
        .expect("the linked row must carry a numeric source_def_index");
    let emitted_def_index = clean_wsum["def_index"]
        .as_u64()
        .expect("the emitted row must carry a numeric def_index");
    assert_eq!(source_def_index, emitted_def_index);
    assert_eq!(clean_wsum_link["target_func_id"], clean_wsum["func_id"]);
    // The GENERAL lane (totality campaign): `triRank` is an inductive `match`
    // the 13-shape planner cannot spell — it must reach the module through
    // clean-compiler's general pipeline, at tier general, disclosed.
    assert!(
        coverage.contains("\"clean_name\": \"triRank\""),
        "the general-lane def must have a row:\n{coverage}"
    );
    assert!(
        coverage.contains("\"tier\": \"general\""),
        "general rows must carry their honest tier:\n{coverage}"
    );
    assert!(
        coverage.contains("\"disposition\": \"compiled\""),
        "triRank must actually compile through the general pipeline:\n{coverage}"
    );

    // Both languages' markers in ONE module's canonical text.
    let text = rfs::read_to_string(on_dir.join("foo.trust-ir.txt"));
    assert!(text.contains("rust_half"), "the Rust producer's row is missing:\n{text}");
    assert!(text.contains("cleanWsum"), "the Clean producer's row is missing:\n{text}");
    assert!(text.contains("calls_clean"), "the Rust caller's row is missing:\n{text}");
    for clean_name in ["m::cleanWsum", "cleanWsum"] {
        let rust_header = format!("rustcc fn @{clean_name}(");
        assert!(
            text.lines().any(|line| line.trim_start().starts_with(&rust_header)),
            "Clean-origin declaration/definition `{clean_name}` must carry rustcc:\n{text}"
        );
    }

    // A generated companion keeps the locked Clean corpus population stable
    // while permanently exercising the ABI seam with a repr(Rust) carrier.
    rfs::write(
        "abi_probe.rs",
        r#"
extern crate trust_bignum;

mod abi_m {
    clean {
        def abiNatId (n : Nat) : Nat := n
    }
}

pub fn calls_clean_nat(x: trust_bignum::Nat) -> trust_bignum::Nat {
    abi_m::abiNatId(x)
}

pub extern "C" fn trust_scalar_c_abi<const N: u64>(x: u64) -> u64 {
    let _ignored = N;
    x
}

pub fn calls_c_abi(x: u64) -> u64 {
    trust_scalar_c_abi::<1>(x)
}
"#,
    );
    let abi_dir = Path::new("abi-probe");
    rfs::create_dir(&abi_dir);
    rustc()
        .input("abi_probe.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&abi_dir)
        .arg("-Ztrust-verify=on")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    let abi_text = rfs::read_to_string(abi_dir.join("abi_probe.trust-ir.txt"));

    // The Rust-callable Clean-origin signature is installed by the compiler as
    // Rust ABI even though its synthetic DefId has no HIR fn item. Nat is
    // repr(Rust), so a C label on this row makes final validation fail closed.
    // The general-lane `abiNatId` pointer-runtime row is separate, claim-free,
    // and explicitly not callable from Rust; `cleanWsum` above already pins the
    // planner lane's appended Rust-callable definition as `rustcc`.
    assert!(
        abi_text.lines().any(|line| line.trim_start().starts_with("rustcc fn @abi_m::abiNatId(")),
        "the HIR-less Clean-origin declaration must carry rustcc:\n{abi_text}"
    );
    let nat_struct = abi_text
        .lines()
        .find(|line| line.starts_with("struct @trust_bignum::Nat { "))
        .expect("the Nat carrier struct must be present in canonical TrustIR");
    assert!(
        !nat_struct.contains("repr="),
        "Nat must retain canonical default repr(Rust), not acquire an FFI representation: \
         {nat_struct}"
    );

    // The const generic deliberately keeps this called local callee symbolic:
    // it traverses the same bodyless-declaration classifier as the HIR-less
    // Clean row. The registry exception must be exact, not a blanket rule for
    // called local callees. Canonical C has no convention prefix.
    assert!(
        abi_text.lines().any(|line| line.trim_start().starts_with("fn @trust_scalar_c_abi(")),
        "the local extern-C definition must retain the canonical C convention:\n{abi_text}"
    );
    assert!(
        !abi_text
            .lines()
            .any(|line| line.trim_start().starts_with("rustcc fn @trust_scalar_c_abi(")),
        "the Clean-origin ABI exception must not relabel a local extern-C definition:\n{abi_text}"
    );

    // ── verification OFF: no recording, DISCLOSED ───────────────────────────
    let off_dir = Path::new("emit-off");
    rfs::create_dir(&off_dir);
    rustc()
        .input("foo.rs")
        .crate_type("lib")
        .emit("trust-ir")
        .out_dir(&off_dir)
        .arg("-Ztrust-verify=off")
        .run();
    let coverage_off = rfs::read_to_string(off_dir.join("foo.trust-ir.coverage.json"));
    assert!(
        coverage_off.contains("\"recorded\": false"),
        "verification-off must disclose the absent recording:\n{coverage_off}"
    );
    assert!(
        !coverage_off.contains("\"clean_name\""),
        "verification-off must not record rows:\n{coverage_off}"
    );
}
