use std::sync::atomic::{AtomicU64, Ordering};

use super::*;

struct TestDirectory(PathBuf);
impl TestDirectory {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "trust-compiler-input-publish-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn path(&self) -> &Path {
        &self.0
    }
}
impl Drop for TestDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn compiler_input_publication_is_create_only_and_names_do_not_become_paths() {
    let dir = TestDirectory::new();
    let path = publish(dir.path(), "../../escape", b"actual non-authorizing data").unwrap();
    assert_eq!(path.parent(), Some(dir.path()));
    assert!(publish(dir.path(), "../../escape", b"actual non-authorizing data").is_err());
    assert_eq!(std::fs::read(path).unwrap(), b"actual non-authorizing data");
}

#[test]
fn compiler_input_publication_preserves_existing_directory_and_refusal_data() {
    let dir = TestDirectory::new();
    let file = dir.path().join("existing");
    std::fs::write(&file, b"preserve").unwrap();
    assert!(publish(&file, "unit", b"data").is_err());
    assert_eq!(std::fs::read(file).unwrap(), b"preserve");
    let refusal = Err(CaptureIncomplete::new("capacity refusal"));
    let path = persist(dir.path(), "unit", &refusal).unwrap();
    let text = std::fs::read_to_string(path).unwrap();
    assert!(text.contains("capture-incomplete-non-authorizing"));
    assert!(!text.contains("complete-cer-input"));
}
