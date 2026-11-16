// Trust (2026-09-16, non-exportable notice — transport + adversarial control):
// a LIBRARY may DEFINE a well-founded Clean def; NO crate may call it across
// the boundary; and RELABELLING its notice as a certificate buys nothing.
//
// The crate-level halves live in
// `crates/trust-clean-origin/tests/control_28_non_exportable_notice.rs` (a
// notice never decodes as a digest, a digest is never recognised as a notice)
// and `control_8_wf_rec_emitter_mutation.rs` (the export seam yields a notice
// for the honest well-founded body and NONE for a mistranslated one). The ui
// halves are `tests/ui/trust/clean_origin_wf_lib_{wrapper_call,
// direct_call_refused,proof_only}.rs`. What only a run-make test can prove is
// the TRANSPORT, in the style of `trust-clean-origin-kernel-skew`: that the
// row an importer reads really is the bytes in the dependency's rmeta, and
// that an attacker (or a bug) who rewrites those bytes cannot turn "no
// certificate crosses" into a served body.
//
// FOUR BUILDS, in the order that makes each refusal mean something:
//
//   (1) the aux builds as an rlib AT ALL — the measured defect (wf1 probes
//       36b/36d/18b/18c: `error: internal: refusing to export a certificate
//       for Clean declaration …` after the local gate had admitted the def);
//   (2) POSITIVE: an importer that calls the aux's ordinary wrapper `fn`
//       builds, runs, and gets the value the emitted recursion computes;
//   (3) NEGATIVE TWIN: an importer that names the Clean def itself is refused
//       at the readmission chokepoint with the notice's v7/D3 note — what,
//       why (no wire tag for the evidence form), options;
//   (4) ADVERSARIAL: the same importer against an rlib whose notice magic was
//       rewritten to the certificate magic (same length, framing untouched).
//       The row now CLAIMS to be a certificate. It must still be refused —
//       by the certificate decoder this time — and never build.
//
// WHY (4) LANDS ON "does not decode" AND WHY THAT IS THE RIGHT CONTROL HERE
// (the kernel-skew fixture deliberately avoids that headline; this one wants
// it): the notice layout is `magic · format u8 · decl · reason u8 · [evidence
// text]` and the certificate layout is `magic · format u8 · decl ·
// kernel_version · …` (`export_notice.rs`, `admission.rs`). After the shared
// prefix a certificate reader takes the next four bytes as kernel_version's
// length: `reason = 1` followed by the low three bytes of the evidence text's
// length — thousands of bytes the row does not have — so the decode truncates.
// A notice is not merely tagged differently from a certificate; it does not
// CONTAIN one. Forging a whole certificate instead is the kernel-skew
// fixture's family and is refused by the local re-gate: the importer re-earns
// the faithfulness method itself and no wire tag names the well-founded one
// (`control_4_readmission_digest.rs`).
//
// `-Ztrust-verify=off` is load-bearing evidence, not convenience: the mint,
// the export row and the importer's chokepoint are deliberately NOT behind
// the verification switch.

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, run, rust_lib_name, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

fn main() {
    // The vanilla replay wrapper drives upstream rustc, which has neither
    // `clean { … }` islands nor `-Ztrust-verify`. Nothing here applies to it.
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    // ── (1) the DEFINING library builds ─────────────────────────────────────
    let pristine_rlib = rust_lib_name("wf_notice_aux");
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=wf_notice_aux")
        .arg("--crate-type=rlib")
        .arg("aux.rs")
        .run();

    // ── locate the notice row ───────────────────────────────────────────────
    // The row travels verbatim in the rlib (the metadata encoder writes a byte
    // vector's elements raw — the property the kernel-skew fixture measured).
    // Exactly one: this crate mints exactly one Clean-origin def, and `aux.rs`
    // is careful not to spell the magic in a doc comment.
    let notice_magic = b"TVNX";
    let certificate_magic = b"TVDG";
    let mut bytes = rfs::read(&pristine_rlib);
    let find = |bytes: &[u8], magic: &[u8]| -> Vec<usize> {
        bytes
            .windows(magic.len())
            .enumerate()
            .filter(|(_, window)| *window == magic)
            .map(|(at, _)| at)
            .collect()
    };
    let hits = find(&bytes, notice_magic);
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one non-exportable notice in the rlib (one Clean-origin def, whose \
         evidence form has no wire tag); found {} at {hits:?} — the notice format or the encoder \
         changed, re-derive this against export_notice.rs",
        hits.len()
    );
    assert!(
        find(&bytes, certificate_magic).is_empty(),
        "A CERTIFICATE WAS EXPORTED for a crate whose only Clean-origin def is well-founded: \
         the wire has no tag for that evidence form, so these bytes relabel it as another"
    );

    // Walk the framing, so a drifted layout fails HERE with a reason rather
    // than as a confusing refusal text below.
    let at = hits[0] + notice_magic.len();
    assert_eq!(bytes[at], 1, "notice format version is not 1; re-derive against export_notice.rs");
    let decl_len = u32::from_le_bytes(bytes[at + 1..at + 5].try_into().unwrap()) as usize;
    assert_eq!(
        &bytes[at + 5..at + 5 + decl_len],
        b"countdownSum",
        "the notice's decl field is not `countdownSum`; the framing walk is off"
    );
    assert_eq!(
        bytes[at + 5 + decl_len],
        1,
        "the notice's reason is not 1 (faithfulness evidence without a wire spelling)"
    );

    // ── (2) POSITIVE: the wrapper importer builds and runs ──────────────────
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=wrapper_main")
        .arg("--extern")
        .arg(format!("wf_notice_aux={pristine_rlib}"))
        .arg("-o")
        .arg(bin_name("wrapper_main"))
        .arg("wrapper_main.rs")
        .run();
    run("wrapper_main").assert_stdout_contains("triangle=Some(15)");

    // ── (3) NEGATIVE TWIN: the direct importer is refused by the notice ─────
    let refused = cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=direct_main")
        .arg("--extern")
        .arg(format!("wf_notice_aux={pristine_rlib}"))
        .arg("-o")
        .arg(bin_name("direct_main"))
        .arg("direct_main.rs")
        .run_fail();
    refused.assert_stderr_contains("cannot be called from another crate");
    refused.assert_stderr_contains("`wf_notice_aux` exported no certificate for `countdownSum`");
    // v7/D3 — why, and the options.
    refused.assert_stderr_contains("has no wire tag in the Clean-origin certificate format yet");
    refused.assert_stderr_contains("WellFoundedFunctionalDefeq");
    refused.assert_stderr_contains("options:");
    // Never the pre-2026-09-16 misdirection, and never an ICE.
    refused.assert_stderr_not_contains("internal:");
    refused.assert_stderr_not_contains("internal compiler error");
    refused.assert_stderr_not_contains("the compiler unexpectedly panicked");

    // ── (4) ADVERSARIAL: relabel the notice as a certificate ────────────────
    bytes[hits[0]..hits[0] + notice_magic.len()].copy_from_slice(certificate_magic);
    let tampered_rlib = "libwf_notice_aux_tampered.rlib";
    rfs::write(tampered_rlib, &bytes);

    let refused = cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=tampered_direct_main")
        .arg("--extern")
        .arg(format!("wf_notice_aux={tampered_rlib}"))
        .arg("-o")
        .arg(bin_name("tampered_direct_main"))
        .arg("direct_main.rs")
        .run_fail();
    // The certificate lane's decode fatal (clean_origin_import.rs, step 2).
    refused.assert_stderr_contains(
        "the Clean-origin certificate for `wf_notice_aux::m::countdownSum` in `wf_notice_aux` \
         does not decode; refusing to import the definition",
    );
    refused.assert_stderr_contains("options:");
    refused.assert_stderr_not_contains("internal compiler error");
    refused.assert_stderr_not_contains("the compiler unexpectedly panicked");
    assert!(
        !std::path::Path::new(&bin_name("tampered_direct_main")).exists(),
        "A BINARY WAS PRODUCED from an rlib whose non-exportable notice was relabelled as a \
         certificate"
    );
}
