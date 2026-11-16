//! Trust TG6: a fact key holds no path, so two worktrees of one crate on one
//! machine (one cargo home) share one entry: the second checkout imports what
//! the first stored, and stores nothing new.
//!
//! NEGATIVE CONTROL: the second checkout under another cargo home elaborates.

use run_make_support::{cwd, rfs, rustc};

const SOURCE: &str = r#"
clean {
    theorem tg6_shared : forall (n : Nat), n + 0 = n := fun n => rfl
}

pub fn f() -> u64 { 1 }
"#;

fn build(worktree: &str, cargo_home: &str) -> String {
    rfs::create_dir_all(worktree);
    let input = format!("{worktree}/src/lib.rs");
    rfs::create_dir_all(format!("{worktree}/src"));
    rfs::write(&input, SOURCE);
    rustc()
        .input(&input)
        .crate_name("tg6_shared")
        .crate_type("lib")
        .emit("metadata")
        .out_dir(worktree)
        .env("CARGO_HOME", cwd().join(cargo_home))
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

fn count(stderr: &str, event: &str) -> usize {
    let prefix = format!("TRUST_CLEAN_FACT {event} ");
    stderr.lines().filter(|line| line.starts_with(&prefix)).count()
}

fn index_entries(cargo_home: &str) -> usize {
    let index = cwd().join(cargo_home).join("trust/results/v1/clean-kernel-facts-v1/index");
    rfs::read_dir(index).map(|shard| rfs::read_dir(shard.unwrap().path()).count()).sum()
}

fn main() {
    let first = build("worktree-a", "cargo-home");
    assert!(count(&first, "STORE") >= 1, "{first}");
    let entries = index_entries("cargo-home");

    let second = build("worktree-b", "cargo-home");
    let misses = second
        .lines()
        .filter(|line| line.starts_with("TRUST_CLEAN_FACT ELABORATE ") && !line.ends_with(" audit"))
        .count();
    assert_eq!(misses, 0, "the second worktree imports the first one's facts:\n{second}");
    assert_eq!(index_entries("cargo-home"), entries, "one entry, shared");

    // NEGATIVE CONTROL: another cargo home has no facts.
    let elsewhere = build("worktree-c", "other-cargo-home");
    assert!(count(&elsewhere, "STORE") >= 1, "{elsewhere}");
}
