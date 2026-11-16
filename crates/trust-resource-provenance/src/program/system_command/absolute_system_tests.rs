use std::time::Duration;

use super::*;

/// Explicit installed-input acceptance; no historical file or package record supplies custody.
#[test]
#[ignore = "requires explicitly selected actual native linker and debug helper images"]
fn actual_native_helpers_with_unused_rpaths_keep_distinct_absolute_import_custody() {
    for key in ["TRUST_TEST_NATIVE_LINKER", "TRUST_TEST_NATIVE_DEBUG"] {
        let path =
            std::env::var_os(key).map(PathBuf::from).expect("explicit actual native helper path");
        assert!(path.is_absolute());
        let deadline = Instant::now() + Duration::from_secs(60);
        assert!(
            HeldSystemCommand::open(&path, deadline).is_err(),
            "strict command profile changed"
        );
        let held = HeldSystemCommand::open_absolute_system_imports(&path, deadline).unwrap();
        assert!(held.observation().runtime.is_empty());
        assert!(held.observation().loader_paths.is_empty());
        assert_eq!(
            held.observation().policy,
            "native-command/macho-arm64-absolute-system-imports-v1"
        );
        held.validate(deadline).unwrap();
        println!(
            "actual absolute helper {key}: {} bytes={} sha256={}",
            path.display(),
            held.observation().executable.bytes,
            held.observation().executable.sha256
        );
    }
}
