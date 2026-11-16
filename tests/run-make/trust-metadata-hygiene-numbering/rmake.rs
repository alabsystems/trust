//! Trust (LINUX-SELF-HOST-1): a crate's metadata, and so its crate hash, must not depend on how
//! much hygiene data the session decoded from its dependencies before or during metadata
//! encoding.
//!
//! The encoder numbered every `SyntaxContext` it wrote by its rank among all the contexts the
//! session held when `encode_crate_root` started, or by its raw session index when allocated
//! later. A foreign context is allocated when a span carrying it is first decoded, so that
//! number moved with work that encodes nothing:
//!  * the default `-Ztrust-witness=auto` lane replays the typeck root `mix` from the
//!    `<StableCrateId>.twit` the first compile minted, and so decodes fewer of core's contexts;
//!  * `-Zthreads=2` runs `prefetch_mir` before encoding, `-Zthreads=1` inside `encode_mir`.
//! `later` calls `<[u8]>::swap` and `same` uses `assert_eq!`; at `-Copt-level=3` their MIR puts
//! foreign spans with macro contexts into this crate's metadata. Before the fix every
//! byte comparison below failed on 82bb867edd and 6762badf3c except `auto cold vs off`, which
//! checks that minting a store leaves the cold bytes alone (measured 2026-11-12, GB10).
//!
//! Two guards keep the test from passing vacuously: the warm compiles must replay a root, and
//! `-Zmeta-stats` must show more hygiene written at `-Copt-level=3` than at `-Copt-level=0`.
//! `user.rs` then uses the exported macro and the inlined generic function against every
//! variant, so the renumbered tables are decoded, not only compared.
//!
//! `-Ztrust-verify=off`: the compile that diverged is bootstrap's, which passes it; this test
//! checks metadata bytes, not verdicts.

//@ needs-target-std

use run_make_support::{rfs, run, rustc};

fn compile(out: &str, extra: &[&str]) -> String {
    let mut cmd = rustc();
    cmd.input("lib.rs")
        .crate_name("hyg")
        .crate_type("lib")
        .edition("2021")
        .emit("metadata,link")
        .out_dir(out)
        .arg("-Copt-level=3")
        .arg("-Ztrust-verify=off")
        .env("TRUST_WITNESS_STATS", "1")
        .env_remove("TRUST_WITNESS_MIN_NODES");
    for arg in extra {
        cmd.arg(arg);
    }
    cmd.run().stderr_utf8()
}

fn crate_hash(rmeta: &str) -> String {
    let listing = rustc().arg("-Zls=root").input(rmeta).run().stdout_utf8();
    listing
        .lines()
        .find_map(|line| line.strip_prefix("hash "))
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or_else(|| panic!("`-Zls=root` printed no crate hash for {rmeta}"))
        .to_owned()
}

fn first_difference(a: &[u8], b: &[u8]) -> String {
    match a.iter().zip(b).position(|(x, y)| x != y) {
        Some(at) => format!("first differing byte at {at:#x} ({:#04x} vs {:#04x})", a[at], b[at]),
        None => format!("sizes {} vs {}", a.len(), b.len()),
    }
}

fn assert_same_file(what: &str, a: &str, b: &str) {
    let (x, y) = (rfs::read(a), rfs::read(b));
    assert!(x == y, "{what}: {a} and {b} differ, {}", first_difference(&x, &y));
}

/// The bytes `-Zmeta-stats` reports for the hygiene tables at `opt`.
fn hygiene_bytes(opt: &str) -> u64 {
    let dir = format!("stats-o{opt}");
    rfs::create_dir(&dir);
    let out = rustc()
        .input("lib.rs")
        .crate_name("hyg")
        .crate_type("lib")
        .edition("2021")
        .emit("metadata,link")
        .out_dir(&dir)
        .arg(format!("-Copt-level={opt}"))
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-witness=off")
        .arg("-Zmeta-stats")
        .run();
    let text = format!("{}{}", out.stdout_utf8(), out.stderr_utf8());
    text.lines()
        .find_map(|line| {
            let mut words = line.split_whitespace();
            (words.next() == Some("meta-stats") && words.next() == Some("hygiene"))
                .then(|| words.next())
                .flatten()
        })
        .unwrap_or_else(|| panic!("`-Zmeta-stats` printed no hygiene row at -O{opt}:\n{text}"))
        .replace('_', "")
        .parse()
        .expect("a byte count")
}

fn cold_then_warm(dir: &str, threads: &str) {
    rfs::create_dir(dir);
    let cold = compile(dir, &[threads]);
    assert!(!cold.contains("TRUST_REPLAY ACCEPT"), "the cold compile found a store:\n{cold}");
    rfs::copy(format!("{dir}/libhyg.rmeta"), format!("{dir}-cold.rmeta"));
    rfs::copy(format!("{dir}/libhyg.rlib"), format!("{dir}-cold.rlib"));

    let warm = compile(dir, &[threads]);
    // Fail closed: a warm compile that replays nothing would compare the cold bytes with
    // themselves.
    assert!(warm.contains("TRUST_REPLAY ACCEPT"), "the warm compile replayed no root:\n{warm}");

    let (cold_rmeta, warm_rmeta) = (format!("{dir}-cold.rmeta"), format!("{dir}/libhyg.rmeta"));
    let (cold_hash, warm_hash) = (crate_hash(&cold_rmeta), crate_hash(&warm_rmeta));
    assert_eq!(cold_hash, warm_hash, "{threads}: replay moved the crate hash");
    assert_same_file(&format!("{threads}: warm rmeta"), &cold_rmeta, &warm_rmeta);
    let (cold_rlib, warm_rlib) = (format!("{dir}-cold.rlib"), format!("{dir}/libhyg.rlib"));
    assert_same_file(&format!("{threads}: warm rlib"), &cold_rlib, &warm_rlib);
}

/// Build and run `user.rs` against the `libhyg` in `dir`.
fn use_from(dir: &str) {
    let exe = format!("user-{dir}");
    rustc()
        .input("user.rs")
        .edition("2021")
        .arg("-Copt-level=3")
        .arg("-Ztrust-verify=off")
        .extern_("hyg", format!("{dir}/libhyg.rlib"))
        .output(&exe)
        .run();
    run(&exe);
}

fn main() {
    // 0. The fixture writes foreign macro contexts at -O3 at all.
    let (o0, o3) = (hygiene_bytes("0"), hygiene_bytes("3"));
    assert!(o3 > o0, "-Copt-level=3 wrote no more hygiene than -Copt-level=0 ({o3} <= {o0})");

    // 1. Witness replay, one frontend thread: cold and warm compiles into one --out-dir.
    cold_then_warm("w1", "-Zthreads=1");

    // 2. Frontend threads, no witness: one cold compile each into separate --out-dirs.
    for (dir, threads) in [("t1", "-Zthreads=1"), ("t2", "-Zthreads=2")] {
        rfs::create_dir(dir);
        compile(dir, &[threads, "-Ztrust-witness=off"]);
    }
    let (t1_hash, t2_hash) = (crate_hash("t1/libhyg.rmeta"), crate_hash("t2/libhyg.rmeta"));
    assert_eq!(t1_hash, t2_hash, "-Zthreads moved the crate hash");
    assert_same_file("-Zthreads=1 vs 2", "t1/libhyg.rmeta", "t2/libhyg.rmeta");
    // The witness lane writes the cold bytes of a `-Ztrust-witness=off` compile.
    assert_same_file("auto cold vs off", "w1-cold.rmeta", "t1/libhyg.rmeta");

    // 3. Both at once: the configuration `targo --unverified` uses when -j > 1.
    cold_then_warm("w2", "-Zthreads=2");
    assert_same_file("-Zthreads=2 cold vs -Zthreads=1 cold", "w2-cold.rmeta", "w1-cold.rmeta");

    // 4. Every variant decodes: the macro, the inlined generic and its `assert_eq!`.
    for dir in ["w1", "w2", "t1", "t2"] {
        use_from(dir);
    }
}
