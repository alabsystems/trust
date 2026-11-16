//! Frame/book restrictions only. No fabricated native Full/SDK/closed owner.
use super::*;
use crate::bootstrap_graph::compilation::tests::advanced;
#[test]
fn full_close_requires_every_actual_retained_binding() {
    let actual = advanced();
    let closed = Closed {
        request: CloseRequest { key: actual.key.clone() },
        source: actual.source.clone(),
        output: actual.output.clone(),
    };
    same_bindings(&actual, &closed).unwrap();
    for field in 0..5 {
        let mut other = closed.clone();
        match field {
            0 => other.request.key.compilation = [91; 16],
            1 => other.source.source_directory.inode += 1,
            2 => other.source.original_record.sha256[0] ^= 1,
            3 => other.source.withheld_record.sha256[0] ^= 1,
            _ => other.output.lock.inode += 1,
        }
        assert!(same_bindings(&actual, &other).is_err());
    }
}
