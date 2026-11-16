//! Binding DATA only. No decoder below constructs an actual closed-source owner.
use super::*;
fn closed() -> Closed {
    let current = super::super::tests::advanced();
    Closed {
        request: CloseRequest { key: current.key },
        source: current.source,
        output: current.output,
    }
}
#[test]
fn full_close_roundtrip_binds_original_compilation_source_and_output() {
    let value = closed();
    let request = value.request.encode().unwrap();
    assert!(CloseRequest::decode(&request).unwrap() == value.request);
    let bytes = value.encode().unwrap();
    assert!(Closed::decode(&bytes).unwrap() == value);
    assert!(CloseRequest::decode(&bytes).is_err());
    assert!(Closed::decode(&request).is_err());
    for end in 0..bytes.len() {
        assert!(Closed::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Closed::decode(&trailing).is_err());
    for edit in [0, 1, 2] {
        let mut changed = value.clone();
        match edit {
            0 => changed.request.key.compilation = [0; 16],
            1 => changed.source.key.graph[0] ^= 1,
            _ => changed.output.key.graph[0] ^= 1,
        }
        assert!(changed.encode().is_err());
    }
}
