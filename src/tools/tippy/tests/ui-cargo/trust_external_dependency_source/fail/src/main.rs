#![warn(clippy::trust_external_dependency_source)]

fn main() {
    let mut buffer = itoa::Buffer::new();
    assert_eq!(buffer.format(42), "42");
}
