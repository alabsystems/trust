use std::time::Duration;

use super::*;

#[test]
fn original_target_file_observations_match_portable_sha256_at_padding_and_read_boundaries() {
    let scratch = tempfile::tempdir().unwrap();
    let root_path = std::fs::canonicalize(scratch.path()).unwrap();
    let target = root_path.join("lib/rustlib").join(TARGET).join("lib");
    std::fs::create_dir_all(&target).unwrap();
    let mut expected = BTreeMap::new();
    for length in [0, 1, 55, 56, 63, 64, 65, 65535, 65536, 65537, 131133] {
        let bytes = (0..length).map(|index| (index % 251) as u8).collect::<Vec<_>>();
        let path = target.join(format!("input-{length}.rlib"));
        std::fs::write(&path, &bytes).unwrap();
        expected.insert(path, (length as u64, crate::schema::hex(&Sha256::digest(bytes))));
    }
    let root = File::open(&root_path).unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    let held = Namespace::capture(&root, &root_path, deadline, MAX_DESCRIPTORS, |_| {}).unwrap();
    assert_eq!(held.files.len(), expected.len());
    for file in held.files.values() {
        assert_eq!(
            &(file.observation.bytes, file.observation.sha256.clone()),
            expected.get(&file.observation.path).unwrap(),
        );
    }
    held.validate(&root, deadline).unwrap();
}
