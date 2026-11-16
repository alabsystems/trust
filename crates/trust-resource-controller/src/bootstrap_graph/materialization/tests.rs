use super::*;

#[test]
fn fresh_preparation_binds_original_graph_and_finite_input_restriction() {
    let request = MaterializationPreparation {
        key: crate::bootstrap_graph::tests::key(),
        input_remaining_ns: 5_000_000_000,
    };
    let frame = request.encode().unwrap();
    assert!(MaterializationPreparation::decode(&frame).unwrap() == request);
    for length in 0..frame.len() {
        assert!(MaterializationPreparation::decode(&frame[..length]).is_err());
    }
    for input_remaining_ns in [0, super::super::configuration::MAX_INPUT_NS + 1, u64::MAX] {
        let mut invalid = request.clone();
        invalid.input_remaining_ns = input_remaining_ns;
        assert!(invalid.encode().is_err());
    }
    let digest = [31; 32];
    let reply = MaterializationReply::Prepared {
        key: request.key.clone(),
        preparation_sha256: digest,
        remaining_input_ns: 1_000_000_000,
        contents_directory: FileIdentity { device: 7, inode: 8 },
        context: Box::new(crate::bootstrap_graph::tests::context()),
    };
    let frame = reply.encode().unwrap();
    assert!(MaterializationReply::decode(&frame, &request, digest).unwrap() == reply);
    assert!(MaterializationReply::decode(&frame, &request, [32; 32]).is_err());
    let mut foreign = request.clone();
    foreign.key.graph[0] ^= 1;
    assert!(MaterializationReply::decode(&frame, &foreign, digest).is_err());
    assert!(crate::bootstrap_graph::ConfigurationAttachment::decode(&frame).is_err());
    for length in 0..frame.len() {
        assert!(MaterializationReply::decode(&frame[..length], &request, digest).is_err());
    }

    // Reconstruct the original ACK bytes: neither a v1 reply nor that old
    // payload relabelled v2 can supply the now-required actual observation.
    for version in [1, 2] {
        let mut old = Encoder::new(117);
        old.number(version);
        old.number(0);
        request.key.write(&mut old).unwrap();
        old.0.extend(digest);
        old.number(1_000_000_000);
        old.frame_bytes(&crate::bootstrap_graph::tests::context().encode().unwrap()).unwrap();
        assert!(MaterializationReply::decode(&old.finish().unwrap(), &request, digest).is_err());
    }
    // A zero inode is never a usable binding, even though all the other fields
    // still match this request. No decoder may synthesize a default identity.
    let mut zero = reply.clone();
    if let MaterializationReply::Prepared { contents_directory, .. } = &mut zero {
        contents_directory.inode = 0;
    }
    assert!(zero.encode().is_err());
}
