use std::path::{Path, PathBuf};

use super::{ProcMacroBoundary, decide};

#[test]
fn only_a_marked_verifying_session_is_bounded() {
    let dylib = Path::new("/nonexistent/libunaudited.dylib");
    assert_eq!(decide(false, true, true, false, &[], dylib, "m"), ProcMacroBoundary::Admitted);
    assert_eq!(decide(true, false, true, false, &[], dylib, "m"), ProcMacroBoundary::Admitted);
}

#[test]
fn an_unaudited_dylib_is_refused_or_forfeited_by_the_policy() {
    let dylib = Path::new("/nonexistent/libunaudited.dylib");
    assert!(matches!(
        decide(true, true, true, false, &[], dylib, "m"),
        ProcMacroBoundary::Refused(message) if message.contains("no-proc-macro TCB boundary")
    ));
    assert!(matches!(
        decide(true, true, false, false, &[], dylib, "m"),
        ProcMacroBoundary::Forfeited(message) if message.contains("forfeits proof authority")
    ));
}

#[test]
fn an_audited_dylib_is_admitted_and_a_different_one_is_not() {
    let audited = vec![PathBuf::from("/nonexistent/libaudited.dylib")];
    assert_eq!(
        decide(true, true, true, false, &audited, Path::new("/nonexistent/libaudited.dylib"), "a"),
        ProcMacroBoundary::Admitted
    );
    assert!(matches!(
        decide(true, true, true, false, &audited, Path::new("/nonexistent/libother.dylib"), "o"),
        ProcMacroBoundary::Refused(_)
    ));
}

#[test]
fn an_isolated_session_admits_what_this_process_never_opens() {
    let dylib = Path::new("/nonexistent/libunaudited.dylib");
    // Strict, certify and memory-safe all claim proof; advisory does not.
    for proof_claimed in [true, false] {
        assert_eq!(
            decide(true, true, proof_claimed, true, &[], dylib, "m"),
            ProcMacroBoundary::Admitted
        );
    }
    // The negative control: the same dylib expanded in process is still refused.
    assert!(matches!(
        decide(true, true, true, false, &[], dylib, "m"),
        ProcMacroBoundary::Refused(message) if message.contains("no-proc-macro TCB boundary")
    ));
}
