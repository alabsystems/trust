// Trust (fix6, CLOSURE-ABSENT-CALLEE, docs/DECISION_QUEUE.md): a caller whose local
// closure's body the native lane refuses must not lose its own rows.
//
// The closure below builds a `Box<[u32]>` (an unsizing coercion the trust-ir
// bridge refuses). The native lane's survivor retry drops it from the caller's bundle,
// and the caller's `<{closure} as FnMut>::call_mut` used to fail the caller's
// whole lowering ("closure body is not present in the TrustIr module"): every
// row of the caller became a `native-verification-gap` (preview4: 7 functions,
// 214 rows). The shim is now the ordinary fail-closed absent callee.
//
// Pinned, from the advisory JSON transport:
//  * the CLOSURE stays unproved (its refused body is not hidden behind the fix,
//    and this precondition keeps the recipe exercising the dropped-body shape);
//  * the CALLER carries no `native-verification-gap` row;
//  * the CALLER carries the fail-closed absent-callee row naming the closure,
//    and it is not proved.
// The `&mut` capture havoc is pinned at the bridge level
// (`crates/trust-ir-bridge/src/absent_closure_body_tests.rs`).

use std::path::PathBuf;

use run_make_support::{bin_name, cmd, rfs, rustc_path};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";

const SOURCE: &str = r#"#![crate_type = "lib"]
pub fn caller(n: u32) -> u32 {
    let mut count = 0u32;
    let mut f = |x: u32| {
        let b: Box<[u32]> = Box::new([x, x]);
        count = b.len() as u32;
    };
    f(n);
    let y: u32 = 3;
    y + 1
}
"#;

const CALLER: &str = "closure_caller::caller";
const CLOSURE: &str = "closure_caller::caller::{closure#0}";

fn row<'a>(output: &'a str, function: &str) -> &'a str {
    let token = format!("\"type\":\"function_result\",\"function\":\"{function}\"");
    let mut rows = output
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:") && line.contains(&token));
    let found = rows.next().unwrap_or_else(|| panic!("no function_result for {function}:\n{output}"));
    assert!(rows.next().is_none(), "more than one function_result for {function}:\n{output}");
    found
}

fn main() {
    let rustc = PathBuf::from(rustc_path());
    let trustc = rustc.with_file_name(bin_name("trustc"));
    let trustc = if trustc.exists() { trustc } else { rustc };

    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler does not know Trust's policy/output options.
        return;
    }

    rfs::write("closure_caller.rs", SOURCE);
    let out = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg("closure_caller.rs")
        .arg("-o")
        .arg("libclosure_caller.rlib")
        .run()
        .stderr_utf8();

    let closure = row(&out, CLOSURE);
    assert!(
        closure.contains("native-verification-gap"),
        "precondition: the closure's body must stay refused, or this recipe no longer \
         exercises a dropped closure body: {closure}"
    );

    let caller = row(&out, CALLER);
    assert!(
        !caller.contains("native-verification-gap"),
        "a dropped closure body must not cost its caller every row: {caller}"
    );
    let absent =
        "[trust-absent-callee-assumption] call to absent callee `<{closure@closure_caller.rs";
    let at = caller
        .find(absent)
        .unwrap_or_else(|| panic!("the call must carry the absent-callee row: {caller}"));
    let tail = &caller[at..];
    assert!(
        tail.contains(&format!("(closure body `{CLOSURE}` not in the lowered bundle) may panic")),
        "the absent-callee row must name the closure: {caller}"
    );
    let outcome_at = tail.find("\"outcome\":\"").expect("the row carries an outcome") + 11;
    let outcome = &tail[outcome_at..];
    assert!(
        !outcome.starts_with("proved\""),
        "the absent closure call must never be proved: {caller}"
    );

    // The default (strict) policy still refuses the caller on that row.
    let strict = cmd(&trustc)
        .arg("--edition=2021")
        .arg("-Ztrust-verify=on")
        .arg("closure_caller.rs")
        .arg("-o")
        .arg("libclosure_caller_strict.rlib")
        .run_fail()
        .stderr_utf8();
    assert!(
        strict.contains(&format!("Trust strict verification failed for `{CALLER}`")),
        "strict must still refuse the caller:\n{strict}"
    );
}
