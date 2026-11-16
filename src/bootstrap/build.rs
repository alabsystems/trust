use std::env;

// Trust: x.py gives Cargo the bootstrap shim as both RUSTC and RUSTC_WRAPPER
// and binds its numeric stage to RUSTC_REAL (core/builder/cargo.rs). Merely
// inheriting RUSTC_REAL in a direct Targo run must not select another compiler.
pub(crate) fn test_build_rustc<'a>(
    rustc: Option<&'a str>,
    wrapper: Option<&str>,
    stage: Option<&str>,
    real: Option<&'a str>,
) -> Result<Option<&'a str>, &'static str> {
    let Some(rustc) = rustc else { return Ok(None) };
    if !rustc.is_empty()
        && wrapper == Some(rustc)
        && stage.is_some_and(|stage| stage.parse::<u32>().is_ok())
    {
        let real = real.filter(|real| !real.is_empty() && *real != rustc).ok_or(
            "bootstrap test compiler binding requires a nonempty RUSTC_REAL distinct from its shim",
        )?;
        return Ok(Some(real));
    }
    Ok(Some(rustc))
}

fn main() {
    // this is needed because `HOST` is only available to build scripts.
    let host = env::var("HOST").unwrap();
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-env=BUILD_TRIPLE={host}");
    // Trust: record the underlying compiler, never x.py's recursive shim, for
    // real-compiler subprocess fixtures and direct-test config fallback. A
    // direct Targo run keeps its RUSTC selection. Track the complete binding
    // so a changed driver behind an unchanged shim rebuilds these fixtures.
    for variable in ["RUSTC", "RUSTC_WRAPPER", "RUSTC_STAGE", "RUSTC_REAL"] {
        println!("cargo:rerun-if-env-changed={variable}");
    }
    let rustc = env::var("RUSTC").ok();
    let wrapper = env::var("RUSTC_WRAPPER").ok();
    let stage = env::var("RUSTC_STAGE").ok();
    let real = env::var("RUSTC_REAL").ok();
    if let Some(rustc) =
        test_build_rustc(rustc.as_deref(), wrapper.as_deref(), stage.as_deref(), real.as_deref())
            .expect("invalid bootstrap test compiler binding")
    {
        println!("cargo:rustc-env=BOOTSTRAP_TEST_BUILD_RUSTC={rustc}");
    }
}

// Trust: compiled by the maintained Bootstrap library test owner as well as
// shared verbatim with this build script; no process environment is mutated.
#[cfg(test)]
#[path = "tests/build_script/tests.rs"]
mod tests;
