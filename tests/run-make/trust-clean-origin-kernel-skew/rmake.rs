// Trust (I7, transport control): a TAMPERED RLIB must be REFUSED — the
// rustc-level half of the acceptance control whose crate-level half lives in
// `crates/trust-clean-origin/tests/control_4_readmission_digest.rs`.
//
// The acceptance control, verbatim from the design
// (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7):
//
// > an imported certificate minted under a different kernel version must be
// > re-checked or refused, never accepted on a matching source hash
//
// The crate-level fixture proves the DECISION (`readmit` refuses with
// `KernelVersionSkew`); what only a run-make test can prove is the TRANSPORT:
// that the digest an importer decodes really is the bytes sitting in the
// dependency's rmeta, with no integrity layer silently in between, and that
// the refusal reaches the user as an ordinary build error — never a
// successful build, never an ICE. `tests/ui/trust/clean_origin_cross_crate_call.rs`
// records this exact test as the boundary a ui test cannot express ("the
// planned run-make byte-patch of the digest's kernel_version bytes inside the
// emitted rlib").
//
// THE PATCH, and why it lands on the STRONG control
// (`KernelVersionSkew`, not the weaker `DecodeRefusal`): wire format v1
// (`crates/trust-clean-origin/src/admission.rs`, `VerdictDigest::encode`) is
//
//   magic "TVDG" · format u8 · decl (u32-LE len + UTF-8)
//   · kernel_version (u32-LE len + UTF-8) · ...
//
// with NO checksum or integrity layer over the digest bytes — a digest is a
// CLAIM; the authority is `readmit`'s comparison against locally recomputed
// facts. A same-length rewrite of the kernel_version VALUE (leading digit
// flipped, u32 length prefix untouched) therefore keeps the wire well-formed
// v1: `VerdictDigest::decode` succeeds, and the SEMANTIC comparison is what
// must catch the skew. Measured end to end on the stage2 trustc 2026-08-20:
// the tampered build fails with the `KernelVersionSkew` note naming both
// versions ("minted under Clean kernel 9.1.0, but this build links kernel
// 0.1.0"), no ICE; the pristine build runs and prints `picked=41`.
//
// `-Ztrust-verify=off` is load-bearing evidence, not convenience: the mint,
// the digest export, and the importer's readmission are all deliberately NOT
// behind the verification switch, so this fixture proves the chokepoint runs
// even with verification off.

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

    // ── (a) the exporting island crate, as an rlib ─────────────────────────
    let pristine_rlib = rust_lib_name("clean_origin_aux");
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=clean_origin_aux")
        .arg("--crate-type=rlib")
        .arg("aux.rs")
        .run();

    // ── (b) locate the digest row in the rmeta and patch the kernel_version
    //        VALUE, framing untouched ──────────────────────────────────────
    let mut bytes = rfs::read(&pristine_rlib);

    // The digest travels verbatim in the rlib (the metadata encoder writes a
    // byte vector's elements raw), so the magic is findable directly. Exactly
    // one row: this crate exports exactly one Clean-origin def, and none of
    // the wire's other fields can imitate the magic (`admission.rs` chose four
    // bytes for precisely this shape check).
    let magic = b"TVDG";
    let hits: Vec<usize> = bytes
        .windows(magic.len())
        .enumerate()
        .filter(|(_, window)| *window == magic)
        .map(|(at, _)| at)
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one verdict digest in the rlib (one exported def); \
         found {} occurrence(s) of the TVDG magic at {hits:?} — the wire format \
         or the encoder changed, re-derive this patch against admission.rs",
        hits.len()
    );

    let mut at = hits[0] + magic.len();
    // The digest's leading prefix — format u8 · decl · kernel_version — is
    // byte-identical across wire v1 and v2 (v2 appends env/carrier/faithfulness
    // records strictly AFTER kernel_version; see admission.rs VerdictDigest::encode,
    // whose decoder accepts `VERDICT_DIGEST_FORMAT_V1 | V2`). Walk only that shared
    // prefix: accept either version, fail closed on any future format not re-derived.
    assert!(
        matches!(bytes[at], 1 | 2),
        "wire format version {} is neither v1 nor v2; the field offsets below assume          the v1/v2 shared prefix (format u8 · decl · kernel_version) — re-derive this          patch against admission.rs",
        bytes[at]
    );
    at += 1;

    let read_u32_le = |bytes: &[u8], at: usize| -> usize {
        u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize
    };

    // decl: u32-LE length + UTF-8.
    let decl_len = read_u32_le(&bytes, at);
    at += 4;
    assert_eq!(
        &bytes[at..at + decl_len],
        b"pick",
        "the digest's decl field is not `pick`; the framing walk is off"
    );
    at += decl_len;

    // kernel_version: u32-LE length + UTF-8. THE PATCH TARGET.
    let version_len = read_u32_le(&bytes, at);
    at += 4;
    let original_version = String::from_utf8(bytes[at..at + version_len].to_vec())
        .expect("the kernel_version field must be UTF-8");
    assert!(
        !original_version.is_empty()
            && original_version.bytes().all(|b| b.is_ascii_digit() || b == b'.'),
        "kernel_version `{original_version}` is not digits-and-dots shaped; \
         re-derive this patch"
    );

    // Flip the leading digit: same length (the u32 prefix stays true), still a
    // valid-shaped semver, guaranteed different from the local kernel.
    bytes[at] = if bytes[at] == b'9' { b'8' } else { b'9' };
    let tampered_version = String::from_utf8(bytes[at..at + version_len].to_vec()).unwrap();
    assert_ne!(tampered_version, original_version);

    let tampered_rlib = "libclean_origin_aux_tampered.rlib";
    rfs::write(tampered_rlib, &bytes);

    // ── (2) the UNTAMPERED positive control FIRST: B against the pristine
    //        rlib builds and runs, printing the projected value. Without this
    //        half, the refusal below could be about anything. ────────────────
    cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=pristine_main")
        .arg("--extern")
        .arg(format!("clean_origin_aux={pristine_rlib}"))
        .arg("-o")
        .arg(bin_name("pristine_main"))
        .arg("main.rs")
        .run();
    run("pristine_main").assert_stdout_contains("picked=41");

    // ── (c)+(d) B against the byte-patched rlib: the build must FAIL with
    //        the KernelVersionSkew refusal — the STRONG control. The wire
    //        stayed well-formed, so a decode refusal here would mean the
    //        semantic comparison never ran; assert its text ABSENT. ──────────
    let refused = cmd(&trustc)
        .arg("-Ztrust-verify=off")
        .arg("--crate-name=tampered_main")
        .arg("--extern")
        .arg(format!("clean_origin_aux={tampered_rlib}"))
        .arg("-o")
        .arg(bin_name("tampered_main"))
        .arg("main.rs")
        .run_fail();

    // The chokepoint's fatal (clean_origin_import.rs, readmit arm) …
    refused.assert_stderr_contains(
        "cannot import the Clean-origin certificate for `pick` from `clean_origin_aux`",
    );
    // … carrying KernelVersionSkew's note, which names BOTH versions
    // (`ReadmissionRefusal::note`, admission.rs).
    refused.assert_stderr_contains(format!(
        "the imported certificate for `pick` was minted under Clean kernel \
         {tampered_version}, but this build links kernel {original_version}"
    ));
    // v7/D3: the refusal must carry the fix, with options.
    refused.assert_stderr_contains("options:");
    refused.assert_stderr_contains(format!(
        "rebuild the dependency with this toolchain, so its certificates are \
         minted under kernel {original_version}"
    ));
    // Never an ICE — the control demands an ordinary, actionable build error.
    refused.assert_stderr_not_contains("internal compiler error");
    refused.assert_stderr_not_contains("the compiler unexpectedly panicked");
    // And never the WEAKER control: "does not decode" is the DecodeRefusal
    // fatal's headline. The framing-preserving patch must decode whole and be
    // refused by `readmit`'s field comparison, or this test is measuring
    // corrupted framing instead of the acceptance control.
    refused.assert_stderr_not_contains("does not decode");
}
