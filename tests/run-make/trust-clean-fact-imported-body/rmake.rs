//! Trust TG6: a deferred island's local kernel fact is keyed by the E6 term of
//! every program function it reaches. An edit to a body it does NOT reach
//! imports the fact; a change to the body it names misses — and when the
//! theorem is now false, the build fails.
//!
//! NEGATIVE CONTROL: the unchanged and the unrelated-edit builds elaborate no
//! deferred island.

use run_make_support::{cwd, rfs, rustc};

const ISLANDS: &str = r#"
clean {
    theorem tg6_u64_le_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

clean {
    theorem tg6_min2_le : forall (a : UInt64) (b : UInt64),
        Nat.le
            (UInt64.toNat (trust_import_tg6_imported_body__min2 a b))
            (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => @Nat.le.refl (UInt64.toNat a))
}
"#;

fn source(min2: &str, other: u64) -> String {
    format!(
        "#![allow(dead_code)]\n{ISLANDS}\npub fn min2(a: u64, b: u64) -> u64 {{\n    {min2}\n}}\n\n\
         pub fn other() -> u64 {{\n    {other}\n}}\n"
    )
}

fn build(source: &str) -> (bool, String) {
    rfs::write("lib.rs", source);
    let output = rustc()
        .input("lib.rs")
        .crate_name("tg6_imported_body")
        .crate_type("lib")
        .emit("metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .env("CARGO_HOME", cwd().join("cargo-home"))
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run_unchecked();
    (output.status().success(), output.stderr_utf8())
}

/// Elaborations a fact did not avoid (an audited hit is elaborated by design).
fn misses(stderr: &str) -> usize {
    stderr
        .lines()
        .filter(|line| line.starts_with("TRUST_CLEAN_FACT ELABORATE ") && !line.ends_with(" audit"))
        .count()
}

fn main() {
    const MIN2: &str = "if a < b { a } else { b }";
    let (ok, first) = build(&source(MIN2, 1));
    assert!(ok, "the theorem holds:\n{first}");
    assert!(
        first.lines().filter(|line| line.starts_with("TRUST_CLEAN_FACT STORE ")).count() >= 2,
        "the island batch and the deferred island are stored facts:\n{first}"
    );

    // NEGATIVE CONTROL: an edit to `other`, which the island does not reach.
    let (ok, unrelated) = build(&source(MIN2, 2));
    assert!(ok, "{unrelated}");
    assert_eq!(misses(&unrelated), 0, "an unrelated body imports the fact:\n{unrelated}");

    // The body the island names changes: a miss, and the theorem is false.
    let (ok, changed) = build(&source("if a < b { b } else { a }", 2));
    assert!(misses(&changed) >= 1, "a changed imported body misses:\n{changed}");
    assert!(
        changed.lines().any(|line| line.starts_with("TRUST_CLEAN_FACT MISS ")
            && line.contains("changed=trust_import_tg6_imported_body__min2")),
        "the miss names the changed import:\n{changed}"
    );
    assert!(!ok, "a theorem the new body falsifies is an error:\n{changed}");
    assert!(changed.contains("tg6_min2_le"), "the error names the theorem:\n{changed}");
}
