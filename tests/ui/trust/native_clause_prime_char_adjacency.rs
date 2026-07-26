//@ revisions: rust2015 rust2018 rust2021
//@[rust2015] edition: 2015
//@[rust2018] edition: 2018
//@[rust2021] edition: 2021
//@[rust2015] run-pass
//@[rust2018] run-pass
//@[rust2021] check-fail
//@ compile-flags: -Z trust-verify=off

// A token-boundary heuristic is insufficient for prime recognition: spaces,
// escapes, and non-identifier Unicode can all be valid character contents.
// Preserve the vanilla pre-2021 tokenization and the 2021 reserved-prefix
// diagnostics for every case.
fn main() {
    assert_eq!(stringify!(x' '), "x' '");
    //[rust2021]~^ ERROR prefix `x` is unknown
    assert_eq!(stringify!(x'\n'), "x'\\n'");
    //[rust2021]~^ ERROR prefix `x` is unknown
    assert_eq!(stringify!(x'💩'), "x'💩'");
    //[rust2021]~^ ERROR prefix `x` is unknown
    assert_eq!(stringify!(x'\''), "x'\\''");
    //[rust2021]~^ ERROR prefix `x` is unknown

    // The cooked-lexer fallback also tracks raw identifiers, but valid
    // character literals adjacent to them remain character literals.
    assert_eq!(stringify!(r#type' '), "r#type' '");
    assert_eq!(stringify!(r#type'\n'), "r#type'\\n'");
    assert_eq!(stringify!(r#type'💩'), "r#type'💩'");
    assert_eq!(stringify!(r#type'\''), "r#type'\\''");
}
