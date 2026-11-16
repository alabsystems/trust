#![warn(clippy::trust_external_dependency_source)]

fn main() {
    assert_eq!(vendored::value(), 42);
}
