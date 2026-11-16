//@rustc-env:RUST_BACKTRACE=0
// Trust: normalize only the branded identity fields; the ICE body stays exact.
//@normalize-stderr-test: "(?m)^note: Tippy version: tippy [0-9]+\.[0-9]+\.[0-9]+ \([0-9a-f]{10} [0-9]{4}-[0-9]{2}-[0-9]{2}\)$" -> "note: Clippy version: foo"
//@normalize-stderr-test: "Clippy version: .*" -> "Clippy version: foo"
//@normalize-stderr-test: "custom_ice_message.rs:\d*:\d*" -> "custom_ice_message.rs"
//@normalize-stderr-test: "(?:rustc|tippy-driver) 1\.\d+.* running on .*" -> "rustc <version> running on <target>"
//@normalize-stderr-test: "(?ms)query stack during panic:\n.*end of query stack\n" -> ""
//@normalize-stderr-test: "note: delayed at .*" -> "note: delayed at <location>"
//@normalize-stderr-test: "note: compiler flags: .*" -> "note: compiler flags: <flags>"

#![feature(rustc_attrs)]

#[rustc_delayed_bug_from_inside_query]
fn main() {}
//~^ ice: delayed bug triggered by
