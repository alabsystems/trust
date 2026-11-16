//@ only-apple
//@ proc-macro: forger.rs
//@ revisions: in_process isolated
//@[isolated] compile-flags: -Ztrust-proc-macro-isolation
//@[in_process] rustc-env:FORGE_DIR={{build-base}}/trust/proc_macro_isolation/macro_cannot_write_into_output_dir.in_process
//@[isolated] rustc-env:FORGE_DIR={{build-base}}/trust/proc_macro_isolation/macro_cannot_write_into_output_dir.isolated
//@ run-pass
//! Trust (D21): a macro that plants a file in the directory rustc writes this
//! crate's output to, and looks at the descriptors its process holds.
//!
//! `FORGE_DIR` is that directory: this revision's own output directory, which is
//! where the executable being run was written (`main` checks that), and the macro
//! refuses to expand if it is not an existing directory.
//!
//! * `in_process` is the control: the macro is rustc, so the file appears.
//! * `isolated`: the write is denied and no file appears, while a write to the
//!   worker's private temporary directory succeeds; and the worker holds its
//!   socket (standard input and the owned duplicate), the null device twice,
//!   and nothing else.

extern crate forger;

const WROTE: (bool, bool) = forger::write_into_output_dir!();
const DESCRIPTORS: &str = forger::open_descriptors!();

fn main() {
    let directory = std::path::Path::new(env!("FORGE_DIR"));
    let executable = std::env::current_exe().unwrap();
    assert_eq!(
        executable.parent().unwrap().canonicalize().unwrap(),
        directory.canonicalize().unwrap(),
        "FORGE_DIR is not the directory rustc wrote this executable to"
    );
    let planted = directory.join("planted-by-macro.rmeta");
    let (wrote_output, wrote_scratch) = WROTE;
    assert!(wrote_scratch, "the macro could not write to its temporary directory");
    if cfg!(isolated) {
        assert!(!wrote_output, "the isolated macro wrote into the output directory");
        assert!(!planted.exists(), "the isolated macro's file is in the output directory");
        assert_eq!(DESCRIPTORS, "0:socket,1:null,2:null,3:socket");
    } else {
        assert!(wrote_output, "control: the in-process macro could not write its file");
        assert!(planted.exists(), "control: the in-process macro's file is missing");
        std::fs::remove_file(planted).unwrap();
    }
}
