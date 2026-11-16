//! Step 2 increment 6 (6.2) review, 2026-10-05: the trust-ir rmeta carrier must not cost an
//! incremental session its metadata reuse.
//!
//! The metadata encoder runs inside the metadata dep-node task, and rustc marks that node green
//! (and copies the previous session's rmeta instead of encoding it) only when every query the
//! encoder read is green. The carrier first read `trust_ir_local_entries`, an `eval_always` +
//! `no_hash` query, unconditionally: an `eval_always` node is re-executed in every session and a
//! node with no fingerprint is then red, so EVERY incremental session re-encoded its rmeta, with
//! the producer off as well as on (measured on stage 1 of `201590b697`: `-Zmeta-stats` printed in
//! sessions 1, 2 and 3; stock rustc and installed trustc print in session 1 only).
//!
//! Pins, for a library built twice with no source change under `-Cincremental`:
//!  * the producer OFF (the drop-in lane): session 2 reuses its metadata (`-Zmeta-stats`, which
//!    prints only when the encoder runs, prints nothing), and session 1's `-Zmeta-stats` has no
//!    `trust-ir` row (the encoder reads no trust-ir query at all);
//!  * the producer ON: session 1 writes the crate header with the crate-wide `incremental`
//!    refusal and no entry; session 2 reuses its metadata; and a consumer's probe channel C reads
//!    that refusal back for the dependency's item (`rmeta=absent(incremental)`).
//@ ignore-cross-compile

use run_make_support::{rfs, rustc};

const LIB: &str = r#"#![crate_type = "lib"]

#[inline]
pub fn mix(x: u32) -> u32 {
    x ^ 0x5a5a_5a5a
}

pub fn other(x: u32) -> u32 {
    mix(x) ^ 3
}
"#;

const USER: &str = r#"#![crate_type = "lib"]

pub fn use_it(x: u32) -> u32 {
    reuse::mix(x)
}
"#;

fn session(dir: &str, producer: bool) -> String {
    let mut cmd = rustc();
    cmd.input("lib.rs")
        .crate_name("reuse")
        .crate_type("lib")
        .edition("2021")
        .arg("-Ztrust-verify=off")
        .arg(format!("-Cincremental={dir}/inc"))
        .arg("--emit=metadata,link")
        .arg("-Zmeta-stats")
        .out_dir(format!("{dir}/out"));
    if producer {
        cmd.arg("-Ztrust-ir-lower");
    }
    cmd.run().stderr_utf8()
}

/// Did this session run the metadata encoder? `-Zmeta-stats` prints only when it does.
fn encoded(stderr: &str) -> bool {
    stderr.lines().any(|l| l.starts_with("meta-stats"))
}

fn main() {
    rfs::write("lib.rs", LIB);
    rfs::write("user.rs", USER);

    for (dir, producer) in [("off", false), ("on", true)] {
        let first = session(dir, producer);
        assert!(encoded(&first), "session 1 ({dir}) encodes its metadata:\n{first}");
        let trust_ir_row =
            first.lines().any(|l| l.split_whitespace().nth(1) == Some("trust-ir"));
        assert_eq!(
            trust_ir_row, producer,
            "a trust-ir section exactly when the producer runs ({dir}):\n{first}"
        );
        if producer {
            assert!(
                first.contains("meta-stats trust-ir entries: 0 encoded; 1 unencoded: incremental=1"),
                "an incremental session refuses the whole crate, by name:\n{first}"
            );
        }
        let second = session(dir, producer);
        assert!(
            !encoded(&second),
            "an unchanged incremental session reuses its metadata ({dir}):\n{second}"
        );
    }

    // A consumer reads the dependency's crate-wide refusal back.
    let out = rustc()
        .input("user.rs")
        .crate_type("lib")
        .edition("2021")
        .arg("-Copt-level=0")
        .arg("-Ccodegen-units=1")
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower")
        .arg("-Ztrust-instance-flip-probe=*")
        .extern_("reuse", "on/out/libreuse.rlib")
        .out_dir("user-out")
        .run();
    let stderr = out.stderr_utf8();
    let rows: Vec<&str> = stderr
        .lines()
        .filter(|l| l.starts_with("TRUST-WALLA-PROBE C sym=") && l.contains(" def=reuse::mix "))
        .collect();
    assert_eq!(rows.len(), 1, "one channel-C row for `reuse::mix`:\n{stderr}");
    assert!(
        rows[0].contains("rmeta=absent(incremental)"),
        "the consumer names the dependency's crate-wide refusal: {}",
        rows[0]
    );
}
