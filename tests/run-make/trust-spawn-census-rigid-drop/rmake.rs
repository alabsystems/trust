//! A census consumer must instantiate and renormalize a dropped metadata place
//! before querying `needs_drop` in its own typing environment. The producer is
//! compiled with the next solver: its generic MIR retains a rigid projection in
//! `AttributeValue<R, <R as Reader>::Offset>`. The consumer uses both solvers.
//! A debug-assertions compiler used to pass that raw type to the old solver and
//! panic in `TypeRelating::tys`; a release compiler silently missed that check.
//!
//! The quiet control must remain quiet, while the spawning associated type must
//! retain its spawn refusal through the generic dependency's drop glue.

//@ ignore-cross-compile

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path};

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() {
        return;
    }
    // As in the other verifier recipes, bypass compiletest's vanilla wrapper.
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };
    rfs::write(
        "projected_drop.rs",
        r#"
pub trait Reader { type Offset; }
pub enum AttributeValue<R: Reader, Offset = <R as Reader>::Offset> {
    Reader(R),
    Offset(Offset),
}
#[inline(never)]
pub fn consume<R: Reader>(_value: AttributeValue<R>) {}
"#,
    );
    cmd(&trustc)
        .arg("projected_drop.rs")
        .arg("--crate-type=rlib")
        .arg("-Znext-solver=globally")
        .arg("-Ztrust-verify=off")
        .env_remove("TRUST_NO_VERIFY")
        .run();

    rfs::write(
        "consumer.rs",
        r#"
extern crate projected_drop;
use projected_drop::{AttributeValue, Reader};
pub struct Source;
#[cfg(spawning)]
pub struct Offset;
#[cfg(spawning)]
impl Drop for Offset {
    fn drop(&mut self) { let _handle = std::thread::spawn(|| {}); }
}
#[cfg(quiet)]
type Offset = ();
impl Reader for Source { type Offset = Offset; }
pub fn drops_projected(value: AttributeValue<Source>) {
    projected_drop::consume(value);
}
"#,
    );

    for solver in ["coherence", "globally"] {
        for control in ["quiet", "spawning"] {
            let stderr = cmd(&trustc)
                .arg("consumer.rs")
                .arg("--crate-type=lib")
                .arg("--edition=2021")
                .arg("--extern=projected_drop=libprojected_drop.rlib")
                .arg(format!("--cfg={control}"))
                .arg("--emit=metadata")
                .arg(format!("-Znext-solver={solver}"))
                .arg("-Ztrust-verify=on")
                .arg("-Ztrust-policy=advisory")
                .env_remove("TRUST_NO_VERIFY")
                .run()
                .stderr_utf8();
            assert_eq!(
                stderr.contains("UnmodeledThreadSpawnEffect"),
                control == "spawning",
                "{solver}/{control}: census dropped a refusal or refused the quiet control:\n{stderr}"
            );
            if control == "spawning" {
                assert!(
                    stderr.contains("callee reaches a std thread spawn through calls and drops"),
                    "{solver}: no spawn witness through the generic dependency:\n{stderr}"
                );
            }
        }
    }
}
