// Trust: TG11 nominal enum/struct imports are checked in ordinary builds.
// The source mutants must fail in both ordinary optimization modes.
use run_make_support::{cmd, rustc_path};

// Every mutant island names `trust_import_`, so the deferred suffix refuses it
// after program admissions are minted, and its errors carry this note. (Before
// TG14 batched that suffix, each island was checked alone and its errors began
// "Clean island declaration"; the batch reports Clean's own message.)
const DEFERRED_ISLAND_REFUSAL: &str = "checked after program admissions were minted";

fn main() {
    if std::env::var_os("__COMPILETEST_TRUST_VANILLA_REAL_RUSTC").is_some() { return; }
    cmd(rustc_path()).args(["aux.rs", "--crate-name=e6_odt_aux", "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", "-o", "libe6_odt_aux.rmeta"]).run();
    for opt in ["0", "2"] {
        let opt = format!("-Copt-level={opt}");
        cmd(rustc_path()).args(["consumer.rs", "--crate-type=lib", "--emit=metadata", "--extern=e6_odt_aux=libe6_odt_aux.rmeta", "-Ztrust-verify=off", &opt]).run();
        cmd(rustc_path()).args(["reserved.rs", "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt]).run();
        for fixture in ["enum.rs", "projection.rs", "aterm_kernel.rs"] {
            cmd(rustc_path()).args([fixture, "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt]).run();
            cmd(rustc_path()).args([fixture, "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt, "--cfg=mutant"])
                .run_fail().assert_stderr_contains(DEFERRED_ISLAND_REFUSAL);
        }
        // The Rust match's branch values stay unchanged; only the ODT tag
        // table/toTag changes. A fact key must bind that dependency too.
        cmd(rustc_path()).args(["enum.rs", "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt, "--cfg=tag_mutant"])
            .run_fail().assert_stderr_contains(DEFERRED_ISLAND_REFUSAL);
        cmd(rustc_path()).args(["guarded.rs", "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt])
            .run_fail().assert_stderr_contains("guarded enum match");
        cmd(rustc_path()).args(["non_exhaustive.rs", "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt])
            .run_fail().assert_stderr_contains("non-exhaustive patterns");
        for outside in ["host_width.rs", "character.rs"] {
            cmd(rustc_path()).args([outside, "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt])
                .run_fail().assert_stderr_contains("fixed-width scalar slice");
        }
        // Uncited unsupported shapes remain valid ordinary Rust.
        cmd(rustc_path()).args(["uncited.rs", "--crate-type=lib", "--emit=metadata", "-Ztrust-verify=off", &opt]).run();
    }
}
