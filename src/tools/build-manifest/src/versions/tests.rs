use super::*;
use flate2::Compression;
use flate2::write::GzEncoder;
use std::env;
use std::io::Cursor;
use std::time::{SystemTime, UNIX_EPOCH};
use tar::{Builder as TarBuilder, Header};

fn temp_dist_dir(test_name: &str) -> PathBuf {
    let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let dir = env::temp_dir()
        .join(format!("build-manifest-versions-{test_name}-{}-{nanos}", std::process::id()));
    fs::create_dir(&dir).unwrap();
    dir
}

fn append_file(tar: &mut TarBuilder<GzEncoder<File>>, path: &str, contents: &[u8]) {
    let mut header = Header::new_gnu();
    header.set_size(contents.len() as u64);
    header.set_mode(0o644);
    header.set_cksum();
    tar.append_data(&mut header, path, Cursor::new(contents)).unwrap();
}

fn write_version_tarball(path: &Path, prefix: &str) {
    let file = File::create(path).unwrap();
    let encoder = GzEncoder::new(file, Compression::default());
    let mut tar = TarBuilder::new(encoder);
    append_file(&mut tar, &format!("{prefix}/version"), b"1.96.0-dev\n");
    append_file(&mut tar, &format!("{prefix}/git-commit-hash"), b"abc123\n");
    let encoder = tar.into_inner().unwrap();
    encoder.finish().unwrap();
}

#[test]
fn version_metadata_falls_back_to_available_host_archive() {
    let dist = temp_dist_dir("fallback-host");
    let package = PkgType::Rust;
    let mut versions = Versions::new("dev", &dist).unwrap();
    let filename = versions.archive_name(&package, "aarch64-apple-darwin", "tar.gz").unwrap();
    let prefix = filename.strip_suffix(".tar.gz").unwrap();
    write_version_tarball(&dist.join(&filename), prefix);

    let version = versions.version(&package).unwrap();

    assert!(version.present);
    assert_eq!(version.version.as_deref(), Some("1.96.0-dev\n"));
    assert_eq!(version.git_commit.as_deref(), Some("abc123\n"));

    fs::remove_dir_all(dist).unwrap();
}
