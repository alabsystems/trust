// Trust: KNOWN_HAZARDS "`certify` exits 0 on a literal `clamp` whose only row is a
// `native-verification-gap` `unknown`". `Ord::clamp` panics when `min > max`, and the
// call-site recognizer (`trust-vcgen` `numeric_panic`) decides that from literal bounds.
// For a pair that cannot panic it minted NOTHING, so each function below had an empty
// bridged inventory, its only published row was the `native-verification-gap` `unknown`,
// and `certify` passed it on the empty-inventory early return with zero proved rows. The
// recognizer now mints the decided row (violation `false`), which proves, so the gap row
// is gone and the green rests on that row.
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ compile-flags: -Ztrust-verify-output=json --error-format=human
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ forbid-output: did not produce a complete obligation inventory
//@ forbid-output: "outcome":"unknown"

pub fn symmetric(x: i32) -> i32 {
    x.clamp(-10, 10)
}

pub fn digit(x: u8) -> u8 {
    x.clamp(b'0', b'9')
}

pub fn point(x: i32) -> i32 {
    x.clamp(5, 5)
}

pub fn full(x: i32) -> i32 {
    x.clamp(i32::MIN, i32::MAX)
}
