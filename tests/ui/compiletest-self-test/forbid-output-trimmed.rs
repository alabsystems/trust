// Trust: meta test for compiletest. A `forbid-output` pattern must be matched TRIMMED,
// as `error-pattern` is. The directive's value keeps the space after the colon, so
// before the fix the pattern below was searched for with a leading space. In JSON
// output `"code":"deprecated"` follows a `{`, never a space, so the forbidden text went
// unseen and the test passed. It must now fail.

//@ check-pass
//@ should-fail
//@ compile-flags: --error-format=json
//@ dont-check-compiler-stderr
//@ forbid-output: "code":"deprecated"

#[deprecated]
fn f() {}

fn main() {
    f(); //~ WARN use of deprecated function
}
