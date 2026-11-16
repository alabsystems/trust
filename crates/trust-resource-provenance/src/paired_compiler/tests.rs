use std::path::PathBuf;

use super::*;
use crate::program::FileObservation;

fn observed(root: &Path) -> ProgramObservation {
    let file = |name: &str, hash: char| FileObservation {
        path: root.join(name),
        sha256: hash.to_string().repeat(64),
        bytes: 1024,
        device: 1,
        inode: 2,
    };
    ProgramObservation {
        policy: crate::program::RUNTIME_POLICY,
        scope: crate::program::INPUT_SCOPE,
        executable: file("bin/rustc", 'a'),
        runtime: vec![file("lib/driver.dylib", 'b'), file("lib-alt/runtime.dylib", 'c')],
        loader_paths: vec![root.join("lib"), root.join("lib-alt")],
        system_dependencies: vec!["/usr/lib/libSystem.B.dylib".to_owned()],
        host: "observed-host".to_owned(),
        boot: "observed-boot".to_owned(),
    }
}

#[test]
fn pairing_is_portable_but_runtime_content_is_part_of_the_contract() {
    let first =
        Profile::from_observation(Path::new("/original"), &observed(Path::new("/original")))
            .unwrap();
    let mut moved = observed(Path::new("/relocated"));
    moved.executable.path = PathBuf::from("/relocated/bin/trustc");
    moved.executable.device = 40;
    moved.executable.inode = 50;
    moved.host = "another-host".to_owned();
    moved.boot = "another-boot".to_owned();
    assert_eq!(first, Profile::from_observation(Path::new("/relocated"), &moved).unwrap());
    moved.runtime[0].sha256 = "d".repeat(64);
    assert_ne!(first, Profile::from_observation(Path::new("/relocated"), &moved).unwrap());
    moved.runtime[0].path = PathBuf::from("/outside/runtime.dylib");
    assert!(Profile::from_observation(Path::new("/relocated"), &moved).is_err());
}

#[test]
fn malformed_or_widened_compiled_profiles_are_refused() {
    let profile =
        Profile::from_observation(Path::new("/sdk"), &observed(Path::new("/sdk"))).unwrap();
    let encoded = serde_json::to_string(&profile).unwrap();
    assert_eq!(Profile::decode(&encoded).unwrap(), profile);
    for invalid in [
        encoded.replacen("\"version\":1", "\"version\":1,\"version\":1", 1),
        encoded.replacen("\"version\":1", "\"unknown\":true,\"version\":1", 1),
        encoded.replacen("\"worker_protocol\":2", "\"worker_protocol\":3", 1),
        " ".repeat(MAX_PROFILE_BYTES + 1),
    ] {
        assert!(Profile::decode(&invalid).is_err());
    }
    let mut value = serde_json::to_value(&profile).unwrap();
    value["runtime"][0]["relative_path"] = serde_json::json!(b"../foreign.dylib".to_vec());
    assert!(Profile::decode(&serde_json::to_string(&value).unwrap()).is_err());
    value = serde_json::to_value(&profile).unwrap();
    value["executable"]["bytes"] = serde_json::json!(0);
    assert!(Profile::decode(&serde_json::to_string(&value).unwrap()).is_err());
}

#[test]
fn producer_requires_a_bounded_exact_native_compiler_reply() {
    assert!(require_reply(br#"{"version":1,"protocol":2,"cpu_workers":true}"#).is_ok());
    for invalid in [
        br#"{"version":1,"protocol":2,"cpu_workers":false}"#.as_slice(),
        br#"{"version":1,"protocol":2,"cpu_workers":1}"#,
        br#"{"version":1,"protocol":3,"cpu_workers":true}"#,
        br#"{"version":1,"protocol":2,"cpu_workers":true,"extra":0}"#,
        br#"{"version":1,"protocol":2,"cpu_workers":true,"cpu_workers":true}"#,
        b"trustc 0.12.0",
    ] {
        assert!(require_reply(invalid).is_err());
    }
    assert!(require_reply(&vec![b' '; 1025]).is_err());
}
