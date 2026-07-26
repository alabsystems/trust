use super::parse_stage0_content;

#[test]
fn parses_stage0_dist_channel_overrides() {
    let parsed = parse_stage0_content(
        r#"
dist_server=https://dist.example
artifacts_server=https://artifacts.example
artifacts_with_llvm_assertions_server=https://assertions.example
git_merge_commit_email=merge@example.com
nightly_branch=main
compiler_dist_channel=nightly
rustfmt_dist_channel=nightly
compiler_channel_manifest_hash=compiler-hash
compiler_git_commit_hash=compiler-git
compiler_date=2026-04-23
compiler_version=nightly
rustfmt_channel_manifest_hash=rustfmt-hash
rustfmt_git_commit_hash=rustfmt-git
rustfmt_date=2026-04-23
rustfmt_version=nightly
dist/2026-04-23/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz=deadbeef
"#,
    );

    assert_eq!(parsed.config.compiler_dist_channel, "nightly");
    assert_eq!(parsed.config.rustfmt_dist_channel, "nightly");
    assert_eq!(parsed.compiler.version, "nightly");
    assert_eq!(parsed.rustfmt.as_ref().unwrap().version, "nightly");
    assert_eq!(
        parsed
            .checksums_sha256
            .get("dist/2026-04-23/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz")
            .unwrap(),
        "deadbeef"
    );
}

#[test]
fn leaves_dist_channel_overrides_empty_when_unspecified() {
    let parsed = parse_stage0_content(
        r#"
dist_server=https://dist.example
artifacts_server=https://artifacts.example
artifacts_with_llvm_assertions_server=https://assertions.example
git_merge_commit_email=merge@example.com
nightly_branch=main
compiler_channel_manifest_hash=compiler-hash
compiler_git_commit_hash=compiler-git
compiler_date=2026-04-23
compiler_version=beta
"#,
    );

    assert!(parsed.config.compiler_dist_channel.is_empty());
    assert!(parsed.config.rustfmt_dist_channel.is_empty());
}
