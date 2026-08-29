//! Trust (IR-1, docs/design/2026-08-27-two-language-direct-to-trust-ir.md §3):
//! the Clean-origin RECORDING PATH — under verification, `--emit=trust-ir` on a
//! crate holding both languages publishes ONE Module carrying BOTH producers'
//! rows, with the Clean rows tier-marked and the coverage sidecar disclosing
//! exactly what was recorded.
//!
//! Pins, per the review-amended design:
//!  * the capability/authority header is BYTE-EXACT `structural-parity-only-v1`
//!    / `proof_authority: false` / `native_verification_requests: false` — the
//!    pre-existing test pins containment only; a diff here is a soundness
//!    event, not a golden to re-bless;
//!  * the `clean_origin` coverage section records the island def at tier
//!    `structural` with a minted `func_id`;
//!  * the canonical text carries both languages' function names — the
//!    two-languages-one-module witness at marker-presence strength (call-edge
//!    linkage is increment IR-5, not claimed here);
//!  * under `-Ztrust-verify=off` the same crate records `"recorded": false`
//!    with the lane reason — a DISCLOSED absence, and no new fatal surface on
//!    the verification-off artifact lane.

use std::path::Path;

use run_make_support::{rfs, rustc};

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
        .run();

    let coverage = rfs::read_to_string(on_dir.join("foo.trust-ir.coverage.json"));
    // Capability header, byte-exact (the design's soundness-event pin).
    for exact in [
        "\"direct_obligation_capability\": \"structural-parity-only-v1\",",
        "\"proof_authority\": false,",
        "\"native_verification_requests\": false,",
    ] {
        assert!(
            coverage.contains(exact),
            "capability header line missing or altered — a soundness event, not a golden \
             to re-bless. wanted byte-exact `{exact}` in:\n{coverage}"
        );
    }
    // The clean_origin section: recorded, the island def at tier structural.
    assert!(
        coverage.contains("\"recorded\": true"),
        "clean_origin section must record under verification:\n{coverage}"
    );
    assert!(
        coverage.contains("\"clean_name\": \"cleanWsum\""),
        "the island def must have a clean_origin row:\n{coverage}"
    );
    // kernel-tv (design §4): the wrapping-binop shape is inside the TV
    // denotation fragment, so the row records the kernel-decided tier WITH its
    // honesty qualifiers — and never anything stronger (carrier faithfulness
    // is NOT established; the body stays ungated).
    assert!(
        coverage.contains("\"tier\": \"kernel-tv\""),
        "the wrapping-binop row must reach tier kernel-tv:\n{coverage}"
    );
    assert!(
        coverage.contains("\"judgment\": \"denotation-at-Nat-mod-2^w\""),
        "a kernel-tv row must carry the at-Nat qualifier:\n{coverage}"
    );
    assert!(
        coverage.contains("\"carrier_faithfulness\": \"not-established\""),
        "a kernel-tv row must state what it does NOT establish:\n{coverage}"
    );
    assert!(
        coverage.contains("\"shape\": \"wrapping-binop\""),
        "the recorded row must carry its shape tag:\n{coverage}"
    );
    // IR-5: the caller's declared edge is re-pointed at the appended
    // definition, disclosed in the linked array.
    assert!(
        coverage.contains("\"edges_repointed\": 1"),
        "the caller's edge must be linked (edges_repointed 1):\n{coverage}"
    );
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
