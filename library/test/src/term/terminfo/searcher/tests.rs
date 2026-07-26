// Blessed env_mutation (2026-07-20): pre-existing code that predates the
// toolchain's deny-by-default ENV_MUTATION lint. Mutates process-global env
// under local save/restore, an RAII guard, or single-threaded harness/CLI
// context. Marked for later migration to a lock-scoped helper; the wall stays
// armed for all NEW code outside these marked modules. unknown_lints keeps the
// stock-toolchain build green (the lint name is Trust-only).
#![allow(unknown_lints)]
#![allow(env_mutation)]
use super::*;

#[test]
#[ignore = "buildbots don't have ncurses installed and I can't mock everything I need"]
fn test_get_dbpath_for_term() {
    // woefully inadequate test coverage
    // note: current tests won't work with non-standard terminfo hierarchies (e.g., macOS's)
    use std::env;
    fn x(t: &str) -> PathBuf {
        get_dbpath_for_term(t).expect(&format!("no terminfo entry found for {t:?}"))
    }
    assert_eq!(x("screen"), PathBuf::from("/usr/share/terminfo/s/screen"));
    assert_eq!(get_dbpath_for_term(""), None);
    unsafe {
        env::set_var("TERMINFO_DIRS", ":");
    }
    assert_eq!(x("screen"), PathBuf::from("/usr/share/terminfo/s/screen"));
    unsafe {
        env::remove_var("TERMINFO_DIRS");
    }
}
