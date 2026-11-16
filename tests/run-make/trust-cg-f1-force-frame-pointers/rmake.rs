//! Actual Rust CLI -> F1 Compiler -> framed AArch64 object regression.
//! Native checks are observations; neither frame presence nor AllowUnknown is proof.
//@ needs-trust-cg-backend
//@ only-apple
//@ only-aarch64

use run_make_support::object::read::archive::ArchiveFile;
use run_make_support::object::{Object, ObjectSection};
use run_make_support::{cc, rfs, run, rust_lib_name, rustc, serde_json};

fn object_member(bytes: &[u8]) -> Vec<u8> {
    let archive = ArchiveFile::parse(bytes).expect("rlib");
    let objects: Vec<_> = archive
        .members()
        .map(|member| member.unwrap())
        .filter(|member| member.name().ends_with(b".o"))
        .map(|member| member.data(bytes).unwrap().to_vec())
        .collect();
    assert_eq!(objects.len(), 1, "one codegen unit");
    objects.into_iter().next().unwrap()
}

fn entry_frame(words: &[u32]) -> bool {
    let first_control = words
        .iter()
        .position(|word| {
            word & 0x7c00_0000 == 0x1400_0000 // B / BL
            || word & 0xff00_0010 == 0x5400_0000 // B.cond
            || word & 0x7e00_0000 == 0x3400_0000 // CBZ / CBNZ
            || word & 0x7e00_0000 == 0x3600_0000 // TBZ / TBNZ
            || word & 0xfe00_0000 == 0xd600_0000 // BR / BLR / RET
        })
        .unwrap_or(words.len());
    let prefix = &words[..first_control.min(4)];
    const MASK: u32 = 0xFFC0_7FFF;
    const PAIR: u32 = (30 << 10) | (31 << 5) | 29;
    let add_fp_sp = |offset: u32| 0x9100_0000u32 | (offset << 10) | (31 << 5) | 29;
    prefix.iter().any(|word| match word & MASK {
        value if value == 0xA980_0000 | PAIR => prefix.contains(&add_fp_sp(0)),
        value if value == 0xA900_0000 | PAIR => {
            let offset = ((word >> 15) & 0x7f) * 8;
            offset < 4096 && prefix.contains(&add_fp_sp(offset))
        }
        _ => false,
    })
}

// Bridge certificates name a Mach-O segment AND section. ObjectSection::name
// contains only the section half, so never discard or guess the segment.
fn certificate_section_matches<'data>(
    section: &impl ObjectSection<'data>,
    qualified: &str,
) -> bool {
    let Some((segment, name)) = qualified.split_once(',') else {
        return false;
    };
    if segment.is_empty() || name.is_empty() || name.contains(',') {
        return false;
    }
    section.segment_name().expect("Mach-O segment name") == Some(segment)
        && section.name().expect("Mach-O section name") == name
}

fn compiler(opt: &str, forced: bool, out: &str) -> run_make_support::Rustc {
    let mut command = rustc();
    command
        .input("subject.rs")
        .crate_name("forced_frames")
        .crate_type("rlib")
        .edition("2021")
        .arg("-Cpanic=abort")
        .arg("-Ccodegen-units=1")
        .arg("-Coverflow-checks=off")
        .arg(format!("-Copt-level={opt}"))
        .arg(format!(
            "-Cforce-frame-pointers={}",
            if forced { "yes" } else { "no" }
        ))
        .arg("-Ztrust-verify=off")
        .arg("-Zunstable-options")
        .arg("-Zcodegen-backend=trust-cg")
        .arg("-Ztrust-cg-frontend=trust-ir")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-cg-f1-backend=compiler")
        .env_remove("TRUST_NO_VERIFY")
        .out_dir(out);
    command
}

fn main() {
    rfs::write(
        "subject.rs",
        r#"
#[unsafe(no_mangle)] pub extern "C" fn frame_zero(_: u64) -> u64 { 0 }
#[unsafe(no_mangle)] pub extern "C" fn frame_branch(x: u64) -> u64 {
    if x == 0 { 0 } else { x ^ 0x55 }
}
"#,
    );
    rfs::write(
        "driver.c",
        r#"
#include <stdint.h>
extern uint64_t frame_zero(uint64_t), frame_branch(uint64_t);
int main(void) {
    const uint64_t inputs[] = {0, 1, 255, 0x8000000000000000ULL, UINT64_MAX};
    for (unsigned i=0; i<sizeof(inputs)/sizeof(inputs[0]); ++i) {
        uint64_t sp0, fp0, sp1, fp1;
        __asm__ volatile("mov %0, sp\nmov %1, x29" : "=r"(sp0), "=r"(fp0));
        uint64_t a=frame_zero(inputs[i]), b=frame_branch(inputs[i]);
        __asm__ volatile("mov %0, sp\nmov %1, x29" : "=r"(sp1), "=r"(fp1));
        uint64_t expected=inputs[i] == 0 ? 0 : inputs[i] ^ 0x55;
        if (a != 0 || b != expected || sp0 != sp1 || fp0 != fp1) return 1;
    }
    return 0;
}
"#,
    );
    for opt in ["0", "3"] {
        for forced in [false, true] {
            let out = format!("out-{opt}-{forced}");
            rfs::create_dir(&out);
            let result = compiler(opt, forced, &out)
                .arg("-Ztrust-cg-output-gate=allow-unknown")
                .run();
            let stderr = result.stderr_utf8();
            assert!(!stderr.contains("INC5.4-FRAME"), "{stderr}");
            assert!(
                stderr.contains(
                    "reachable function(s) completed source -> trust_ir_of -> codegen_module"
                ),
                "{stderr}"
            );
            assert!(!stderr.contains("lower_module_to_lir"), "{stderr}");
            let bytes = object_member(&rfs::read(format!(
                "{out}/{}",
                rust_lib_name("forced_frames")
            )));
            rfs::write(format!("{out}/subject.o"), &bytes);
            let object = run_make_support::object::File::parse(&*bytes).unwrap();
            let report: serde_json::Value = serde_json::from_str(&rfs::read_to_string(format!(
                "{out}/forced_frames.trust-cg-certificates.json"
            )))
            .unwrap();
            let certificates = report["certificates"]
                .as_array()
                .expect("full certificates");
            assert_eq!(certificates.len(), 2, "complete two-function denominator");
            for symbol in ["frame_zero", "frame_branch"] {
                let certificate = certificates
                    .iter()
                    .find(|c| c["symbol"] == symbol)
                    .expect("named certificate");
                let qualified = certificate["section"].as_str().expect("qualified section");
                let mut matching: Vec<_> = object
                    .sections()
                    .filter(|section| certificate_section_matches(section, qualified))
                    .collect();
                assert_eq!(
                    matching.len(),
                    1,
                    "one exact certificate segment/section: {qualified}"
                );
                let section = matching.pop().unwrap();
                for malformed in [
                    "__text",
                    "__WRONG,__text",
                    "__TEXT,__wrong",
                    "__TEXT,__text,extra",
                ] {
                    assert!(
                        object
                            .sections()
                            .all(|section| !certificate_section_matches(&section, malformed)),
                        "malformed or mismatched section accepted: {malformed}"
                    );
                }
                let text = section.data().unwrap();
                let start = certificate["extent"][0].as_u64().unwrap() as usize;
                let end = certificate["extent"][1].as_u64().unwrap() as usize;
                assert!(
                    start < end && end <= text.len() && (end - start) % 4 == 0,
                    "complete aligned function extent"
                );
                let words: Vec<_> = text[start..end]
                    .chunks_exact(4)
                    .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
                    .collect();
                if forced {
                    assert!(entry_frame(&words), "{opt} {symbol}: {words:08x?}");
                }
                if !forced && symbol == "frame_zero" {
                    assert!(!entry_frame(&words), "ordinary zero-storage leaf control");
                }
            }
            let executable = format!("native-{opt}-{forced}");
            cc().input("driver.c")
                .input(format!("{out}/subject.o"))
                .arg("-O0")
                .arg("-fno-omit-frame-pointer")
                .out_exe(&executable)
                .run();
            run(&executable);
        }
    }
    // The new codegen request cannot turn the compiler lane into an ungated lane.
    let output = compiler("3", true, "refused")
        .arg("-Ztrust-cg-output-gate=off")
        .run_fail();
    assert!(
        output
            .stderr_utf8()
            .contains("refuses -Ztrust-cg-output-gate=off")
    );
}

#[test]
fn entry_frame_checker_requires_setup_before_control_transfer() {
    let record = [0xa9bf_7bfd, 0x9100_03fd, 0xd65f_03c0];
    assert!(entry_frame(&record));
    assert!(!entry_frame(&[0xd65f_03c0]));
    assert!(!entry_frame(&[0xa9bf_7bfd, 0xd65f_03c0]));
    for branch in [
        0x1400_0000,
        0x9400_0000,
        0x5400_0000,
        0x3400_0000,
        0x3500_0000,
        0x3600_0000,
        0x3700_0000,
        0xd61f_0000,
        0xd63f_0000,
    ] {
        assert!(
            !entry_frame(&[branch, record[0], record[1], record[2]]),
            "a frame after {branch:08x} is not an entry record"
        );
    }
}
