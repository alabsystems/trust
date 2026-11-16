//! Trust TG6 (`COMPILE-TIME-FACTS-1`): "if the functions and proofs don't
//! change, you don't rerun! you already hav facts!" — an edit to a Rust body no
//! island reaches elaborates no island again: every Clean session of the second
//! build imports its local kernel fact.
//!
//! NEGATIVE CONTROL: an edited island is elaborated (and stored) again.
//!
//! Every hit in 32 is AUDITED (re-elaborated by design, chosen by key prefix),
//! so "nothing" means no elaboration except an audit, and every audit matched.

use run_make_support::{cwd, rfs, rustc};

const ISLANDS: &str = r#"
clean {
    theorem tg6_add_zero : forall (n : Nat), n + 0 = n := fun n => rfl
}

clean {
    theorem tg6_add_zero_again : forall (n : Nat), n + 0 = n := tg6_add_zero
}
"#;

fn source(unrelated: u64, last_island: &str) -> String {
    format!(
        "{ISLANDS}\nclean {{\n    {last_island}\n}}\n\n\
         pub fn unrelated() -> u64 {{\n    {unrelated}\n}}\n"
    )
}

fn build(source: &str) -> String {
    rfs::write("lib.rs", source);
    rustc()
        .input("lib.rs")
        .crate_name("tg6_unrelated_edit")
        .crate_type("lib")
        .emit("metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .env("CARGO_HOME", cwd().join("cargo-home"))
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

fn lines<'a>(stderr: &'a str, event: &str) -> Vec<&'a str> {
    let prefix = format!("TRUST_CLEAN_FACT {event} ");
    stderr.lines().filter(|line| line.starts_with(&prefix)).collect()
}

fn main() {
    const LAST: &str = "theorem tg6_zero_add : 0 + 0 = 0 := rfl";
    let first = build(&source(1, LAST));
    assert!(!lines(&first, "STORE").is_empty(), "the first build stores facts:\n{first}");
    assert!(!lines(&first, "ELABORATE").is_empty(), "and elaborates:\n{first}");

    // The edit: one line of a Rust body no island reaches.
    let second = build(&source(2, LAST));
    let elaborated: Vec<&str> =
        lines(&second, "ELABORATE").into_iter().filter(|line| !line.ends_with(" audit")).collect();
    assert!(elaborated.is_empty(), "an unrelated edit elaborates nothing:\n{second}");
    assert!(!lines(&second, "HIT").is_empty() || !lines(&second, "AUDIT").is_empty(), "{second}");
    assert_eq!(
        lines(&second, "AUDIT").len(),
        lines(&second, "AUDIT-MATCH").len(),
        "every audited hit matched:\n{second}"
    );
    assert!(lines(&second, "QUARANTINE").is_empty(), "{second}");

    // NEGATIVE CONTROL: an edited island misses, is elaborated, and is stored.
    let third = build(&source(2, "theorem tg6_zero_add_edited : 0 + 0 = 0 := rfl"));
    assert!(
        lines(&third, "ELABORATE").iter().any(|line| line.ends_with(" miss")),
        "an edited island is elaborated again:\n{third}"
    );
    assert!(!lines(&third, "STORE").is_empty(), "{third}");
}
