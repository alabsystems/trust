use super::*;
#[test]
fn create_only_replay_publication_preserves_existing_bytes() {
    let dir = std::env::temp_dir()
        .join(format!("trust-object-replay-publication-{}", std::process::id()));
    let bytes = b"{\"diagnostic\":true}";
    let path = publish(&dir, "first-cgu", bytes).expect("fresh diagnostic");
    assert_eq!(fs::read(&path).unwrap(), bytes);
    assert!(publish(&dir, "first-cgu", bytes).is_err());
    assert_eq!(fs::read(&path).unwrap(), bytes);
    let second = publish(&dir, "second-cgu", bytes).expect("distinct CGU does not collide");
    assert_ne!(path, second);
    assert_eq!(fs::read(&second).unwrap(), bytes);
    // Only the exact test-created file/directory are removed.
    fs::remove_file(path).unwrap();
    fs::remove_file(second).unwrap();
    fs::remove_dir(dir).unwrap();
}
