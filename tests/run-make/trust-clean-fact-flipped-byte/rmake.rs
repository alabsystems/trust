//! Trust TG6: every read of a local kernel fact re-hashes it against its
//! content address. A flipped byte is quarantined (kept for a person under the
//! store's `quarantine/`) and the island is checked again.
//!
//! NEGATIVE CONTROL: the untouched store is imported with no elaboration.

use run_make_support::{cwd, rfs, rustc};

const SOURCE: &str = r#"
clean {
    theorem tg6_flip : forall (n : Nat), n + 0 = n := fun n => rfl
}

pub fn f() -> u64 { 1 }
"#;

fn build() -> String {
    rfs::write("lib.rs", SOURCE);
    rustc()
        .input("lib.rs")
        .crate_name("tg6_flipped_byte")
        .crate_type("lib")
        .emit("metadata")
        .env("CARGO_HOME", cwd().join("cargo-home"))
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .env("TRUST_CLEAN_FACT_STATS", "1")
        .env_remove("TRUST_NO_VERIFY")
        .run()
        .stderr_utf8()
}

fn misses(stderr: &str) -> usize {
    stderr
        .lines()
        .filter(|line| line.starts_with("TRUST_CLEAN_FACT ELABORATE ") && !line.ends_with(" audit"))
        .count()
}

fn main() {
    let store = cwd().join("cargo-home/trust/results/v1/clean-kernel-facts-v1");
    let first = build();
    assert!(first.contains("TRUST_CLEAN_FACT STORE "), "{first}");

    // NEGATIVE CONTROL: untouched, the fact is imported.
    let untouched = build();
    assert_eq!(misses(&untouched), 0, "{untouched}");

    let mut flipped = 0;
    for shard in rfs::read_dir(store.join("objects")) {
        for object in rfs::read_dir(shard.unwrap().path()) {
            let path = object.unwrap().path();
            let mut bytes = rfs::read(&path);
            let middle = bytes.len() / 2;
            bytes[middle] ^= 0x01;
            rfs::write(&path, bytes);
            flipped += 1;
        }
    }
    assert!(flipped > 0);

    let after = build();
    assert!(
        after.contains("TRUST_CLEAN_FACT QUARANTINE "),
        "the flipped fact is quarantined:\n{after}"
    );
    assert!(misses(&after) >= 1, "and the island checked again:\n{after}");
    assert!(after.contains("TRUST_CLEAN_FACT STORE "), "and its fact stored again:\n{after}");
    assert!(rfs::read_dir(store.join("quarantine")).count() > 0);

    // The re-stored fact is sound again.
    let again = build();
    assert_eq!(misses(&again), 0, "{again}");
}
