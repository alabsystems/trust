#![cfg(unix)]

use std::fs;
use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _, symlink};
use std::path::{Path, PathBuf};

use sha2::{Digest as _, Sha256};

use super::super::CERTIFIED_MONITOR_EVIDENCE_MANIFEST;
use super::*;

const HEAD: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

struct PayloadFixture {
    _root: tempfile::TempDir,
    repo_root: PathBuf,
    payload: PathBuf,
}

impl PayloadFixture {
    fn new() -> Self {
        let root = tempfile::tempdir().expect("payload fixture root");
        let repo_root = root.path().canonicalize().expect("canonical fixture root");
        let payload = repo_root.join("evidence");
        fs::create_dir(&payload).expect("create payload directory");
        for name in CERTIFIED_MONITOR_PAYLOAD_FILES {
            let bytes = if *name == "gate-identity.txt" {
                payload_identity(HEAD).into_bytes()
            } else {
                format!("reviewed payload for {name}\n").into_bytes()
            };
            fs::write(payload.join(name), bytes).expect("write payload leaf");
        }
        let fixture = Self { _root: root, repo_root, payload };
        fixture.rewrite_manifest();
        fixture.seal();
        fixture
    }

    fn rewrite_manifest(&self) {
        let manifest = CERTIFIED_MONITOR_PAYLOAD_FILES
            .iter()
            .map(|name| {
                let bytes = fs::read(self.payload.join(name)).expect("read payload leaf");
                format!("{}  {name}\n", sha256(&bytes))
            })
            .collect::<String>();
        let path = self.payload.join(CERTIFIED_MONITOR_EVIDENCE_MANIFEST);
        make_writable_if_present(&path);
        fs::write(path, manifest).expect("write payload manifest");
    }

    fn rewrite_identity(&self, identity: &str) {
        let path = self.payload.join("gate-identity.txt");
        make_writable_if_present(&path);
        fs::write(path, identity).expect("rewrite identity");
        self.rewrite_manifest();
        self.seal();
    }

    fn seal(&self) {
        for name in CERTIFIED_MONITOR_PAYLOAD_FILES
            .iter()
            .copied()
            .chain(std::iter::once(CERTIFIED_MONITOR_EVIDENCE_MANIFEST))
        {
            let path = self.payload.join(name);
            if fs::symlink_metadata(&path).is_ok() {
                set_mode(&path, 0o400);
            }
        }
        set_mode(&self.payload, 0o500);
    }

    fn unseal_directory(&self) {
        set_mode(&self.payload, 0o700);
    }

    fn validate(&self) -> Result<ValidatedCertifiedMonitorPayload, String> {
        validate_certified_monitor_payload(&self.payload, HEAD)
    }
}

fn set_mode(path: &Path, mode: u32) {
    fs::set_permissions(path, fs::Permissions::from_mode(mode)).expect("set fixture mode");
}

fn make_writable_if_present(path: &Path) {
    if path.exists() {
        set_mode(path, 0o600);
    }
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn payload_identity(head: &str) -> String {
    let digest = "1".repeat(64);
    format!(
        "schema={CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA}\n\
result_scope=payload-only\n\
source_authority=unverified\n\
head={head}\n\
host_os=Darwin\n\
host_arch=arm64\n\
stage2_sysroot=/reviewed/build/aarch64-apple-darwin/stage2\n\
trustc_sha256={digest}\n\
targo_sha256={digest}\n\
targo_trust_sha256={digest}\n\
trustd_sha256={digest}\n\
stage2_tree_sha256={digest}\n\
manifest_sha256={digest}\n\
lock_sha256={digest}\n\
targo_commit={head}\n\
targo_trust_commit={head}\n\
trustd_commit={head}\n\
trustc_version_begin\n\
binary: trustc\n\
commit-hash: {head}\n\
trustc_version_end\n\
targo_version_begin\n\
targo 1.99.0\n\
trust-repo-commit-hash: {head}\n\
targo_version_end\n\
targo_trust_version_begin\n\
targo-trust 0.1.0\n\
trust-repo-commit-hash: {head}\n\
targo_trust_version_end\n\
trustd_version_begin\n\
trustd 1.99.0\n\
trust-repo-commit-hash: {head}\n\
trustd_version_end\n"
    )
}

#[test]
fn valid_payload_mints_one_canonical_no_replace_native_receipt() {
    let fixture = PayloadFixture::new();
    let payload = fixture.validate().expect("valid payload must authenticate");
    let receipt_path = certified_monitor_authority_receipt_path(&fixture.payload);
    let first = render_certified_monitor_native_authority_receipt(
        &fixture.repo_root,
        &receipt_path,
        HEAD,
        &payload,
    )
    .expect("render native receipt");
    let second = render_certified_monitor_native_authority_receipt(
        &fixture.repo_root,
        &receipt_path,
        HEAD,
        &payload,
    )
    .expect("render native receipt twice");
    assert_eq!(first, second, "serialization must be canonical and timestamp-free");
    assert!(first.ends_with(b"\n"));

    let digest = publish_certified_monitor_native_authority_receipt(&receipt_path, &first)
        .expect("fresh receipt publishes");
    assert_eq!(digest, sha256(&first));
    assert_eq!(fs::symlink_metadata(&receipt_path).unwrap().mode() & 0o777, 0o400);
    let value: serde_json::Value = serde_json::from_slice(&first).expect("receipt JSON");
    assert_eq!(value["schema"], CERTIFIED_MONITOR_NATIVE_AUTHORITY_SCHEMA);
    assert_eq!(value["status"], "pass");
    assert_eq!(value["head"], HEAD);
    assert_eq!(value["authority"]["before"]["status"], "verified");
    assert_eq!(value["authority"]["after"]["status"], "verified");
    assert_eq!(value["payload"]["evidence_manifest_sha256"], payload.evidence_manifest_sha256);
    assert_eq!(value["payload"]["stage2_tree_sha256"], "1".repeat(64));
    assert_eq!(value["payload"]["trustc_commit"], HEAD);
    assert_eq!(
        fs::read_dir(&fixture.payload).unwrap().count(),
        CERTIFIED_MONITOR_PAYLOAD_FILES.len() + 1,
        "adjacent authority receipt must not reopen or mutate the shell-sealed payload"
    );

    let error = publish_certified_monitor_native_authority_receipt(&receipt_path, &first)
        .expect_err("authority receipt must never replace an existing leaf");
    assert!(error.contains("fresh no-replace leaf"), "{error}");
}

#[test]
fn native_layout_owns_one_explicit_fresh_log_directory() {
    let root = tempfile::tempdir().unwrap();
    let repo = root.path().canonicalize().unwrap();
    let args = vec!["--log-dir".to_string(), "reviewed/run".to_string()];
    let layout = certified_monitor_evidence_layout(
        &repo,
        &args,
        HEAD,
        Some("ignored/environment".into()),
        None,
    )
    .expect("explicit CLI layout");
    assert_eq!(layout.payload_directory, repo.join("reviewed/run"));
    assert_eq!(layout.authority_receipt, repo.join("reviewed/run.native-authority.json"));
    preflight_certified_monitor_evidence_layout(&layout).expect("fresh paths");

    let duplicate = vec![
        "--log-dir".to_string(),
        "one".to_string(),
        "--log-dir".to_string(),
        "two".to_string(),
    ];
    assert!(certified_monitor_evidence_layout(&repo, &duplicate, HEAD, None, None).is_err());
    fs::create_dir_all(&layout.payload_directory).unwrap();
    assert!(preflight_certified_monitor_evidence_layout(&layout).is_err());
}

#[test]
fn payload_rejects_missing_unexpected_and_malformed_manifest_entries() {
    let missing = PayloadFixture::new();
    missing.unseal_directory();
    fs::remove_file(missing.payload.join(CERTIFIED_MONITOR_EVIDENCE_MANIFEST)).unwrap();
    missing.seal();
    assert!(missing.validate().unwrap_err().contains("exact reviewed file set"));

    let unexpected = PayloadFixture::new();
    unexpected.unseal_directory();
    fs::write(unexpected.payload.join("extra.log"), b"unreviewed\n").unwrap();
    set_mode(&unexpected.payload.join("extra.log"), 0o400);
    set_mode(&unexpected.payload, 0o500);
    assert!(unexpected.validate().unwrap_err().contains("exact reviewed file set"));

    let malformed = PayloadFixture::new();
    let manifest = malformed.payload.join(CERTIFIED_MONITOR_EVIDENCE_MANIFEST);
    make_writable_if_present(&manifest);
    fs::write(&manifest, format!("{}  ../escape\n", "1".repeat(64))).unwrap();
    set_mode(&manifest, 0o400);
    assert!(malformed.validate().unwrap_err().contains("exactly 6 entries"));
}

#[test]
fn payload_rejects_digest_tamper_wrong_identity_and_noncanonical_schema() {
    let tampered = PayloadFixture::new();
    let log = tampered.payload.join(CERTIFIED_MONITOR_PAYLOAD_FILES[2]);
    make_writable_if_present(&log);
    fs::write(&log, b"changed after manifest\n").unwrap();
    set_mode(&log, 0o400);
    assert!(tampered.validate().unwrap_err().contains("digest mismatch"));

    let wrong_head = PayloadFixture::new();
    wrong_head.rewrite_identity(&payload_identity("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"));
    assert!(wrong_head.validate().unwrap_err().contains("differs from controlled-Git HEAD"));

    let wrong_schema = PayloadFixture::new();
    wrong_schema.rewrite_identity(&payload_identity(HEAD).replace(
        CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA,
        "trust.certified-monitor-e2e-payload-identity.v999",
    ));
    assert!(
        wrong_schema.validate().unwrap_err().contains("unrecognized schema or authority scope")
    );
}

#[test]
fn payload_identity_rejects_noncanonical_row_and_version_block_order() {
    let reordered_scalar = PayloadFixture::new();
    let identity = payload_identity(HEAD);
    let reordered = identity.replacen(
        &format!("schema={CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA}\nresult_scope=payload-only\n"),
        &format!("result_scope=payload-only\nschema={CERTIFIED_MONITOR_PAYLOAD_IDENTITY_SCHEMA}\n"),
        1,
    );
    reordered_scalar.rewrite_identity(&reordered);
    assert!(reordered_scalar.validate().unwrap_err().contains("expected ordered scalar `schema`"));

    let reordered_blocks = PayloadFixture::new();
    let trustc_begin = identity.find("trustc_version_begin\n").unwrap();
    let targo_begin = identity.find("targo_version_begin\n").unwrap();
    let targo_trust_begin = identity.find("targo_trust_version_begin\n").unwrap();
    let reordered = format!(
        "{}{}{}{}",
        &identity[..trustc_begin],
        &identity[targo_begin..targo_trust_begin],
        &identity[trustc_begin..targo_begin],
        &identity[targo_trust_begin..]
    );
    reordered_blocks.rewrite_identity(&reordered);
    assert!(reordered_blocks.validate().unwrap_err().contains("expected `trustc_version_begin`"));

    let overlapping_blocks = PayloadFixture::new();
    overlapping_blocks.rewrite_identity(&identity.replacen(
        "trustc_version_end\n",
        "targo_version_begin\ntrustc_version_end\n",
        1,
    ));
    assert!(overlapping_blocks.validate().unwrap_err().contains("before `trustc_version_end`"));

    let trailing_row = PayloadFixture::new();
    trailing_row.rewrite_identity(&format!("{identity}unreviewed_trailing_row\n"));
    assert!(
        trailing_row
            .validate()
            .unwrap_err()
            .contains("trailing rows after the final version block")
    );
}

#[test]
fn payload_rejects_unsealed_and_symlink_substitution() {
    let unsealed_directory = PayloadFixture::new();
    unsealed_directory.unseal_directory();
    assert!(unsealed_directory.validate().unwrap_err().contains("mode 0500"));

    let unsealed_file = PayloadFixture::new();
    set_mode(&unsealed_file.payload.join("compiled-test-inventory.log"), 0o600);
    assert!(unsealed_file.validate().unwrap_err().contains("mode 0400"));

    let linked = PayloadFixture::new();
    linked.unseal_directory();
    let leaf = linked.payload.join(CERTIFIED_MONITOR_PAYLOAD_FILES[1]);
    let target = linked.repo_root.join("outside-inventory.log");
    fs::copy(&leaf, &target).unwrap();
    fs::remove_file(&leaf).unwrap();
    symlink(&target, &leaf).unwrap();
    set_mode(&linked.payload, 0o500);
    assert!(linked.validate().unwrap_err().contains("not an exact regular file"));

    let hardlinked = PayloadFixture::new();
    hardlinked.unseal_directory();
    let leaf = hardlinked.payload.join(CERTIFIED_MONITOR_PAYLOAD_FILES[1]);
    let alias = hardlinked.repo_root.join("outside-inventory-hardlink.log");
    fs::hard_link(&leaf, &alias).unwrap();
    set_mode(&hardlinked.payload, 0o500);
    assert!(hardlinked.validate().unwrap_err().contains("link count 2"));
}
