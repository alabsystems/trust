//! Binding DATA controls only; these construct no resident workspace or Root.
use super::*;

#[test]
fn accepted_contents_data_refuses_source_or_output_aliases() {
    let source = FileIdentity { device: 1, inode: 2 };
    let contents = FileIdentity { device: 1, inode: 3 };
    let mut prepared = PreparedContents {
        request: MaterializationPreparation {
            key: crate::bootstrap_graph::Key {
                query: crate::ContextQuery {
                    binding: crate::JobBinding {
                        session: "s-abcd".into(),
                        root_attempt: [1; 16],
                        capability: [9; 32],
                    },
                    call_attempt: [2; 16],
                },
                graph: [3; 16],
            },
            input_remaining_ns: 1_000_000_000,
        },
        contents,
    };
    prepared.check(source, None).unwrap();
    assert_eq!(prepared.contents, contents);
    assert!(prepared.check(contents, None).is_err());
    prepared.contents.inode = 0;
    assert!(prepared.check(source, None).is_err());
    prepared.contents = contents;
    let mut output = crate::bootstrap_graph::OutputAttachment {
        key: prepared.request.key.clone(),
        root: FileIdentity { device: 1, inode: 4 },
        lock: FileIdentity { device: 1, inode: 5 },
    };
    prepared.check(source, Some(&output)).unwrap();
    output.root = contents;
    assert!(prepared.check(source, Some(&output)).is_err());
    output.root.inode = 4;
    output.lock = contents;
    assert!(prepared.check(source, Some(&output)).is_err());
}
