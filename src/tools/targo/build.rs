use flate2::{Compression, GzBuilder};
use std::ffi::OsStr;
use std::fs;
use std::path::Path;

// Trust: the discovery logic lives in its own file so `version.rs` can compile
// it under the unit-test harness — a build script is never executed by `cargo
// test`, so logic kept inline here would be untestable.
mod build_commit_info;

fn main() {
    commit_info();
    compress_man();
    windows_manifest();
    #[expect(
        clippy::disallowed_methods,
        reason = "not `cargo`, not needing to load from config"
    )]
    let target = std::env::var("TARGET").unwrap();
    println!("cargo:rustc-env=RUST_HOST_TARGET={target}");
}

fn compress_man() {
    #[expect(
        clippy::disallowed_methods,
        reason = "not `cargo`, not needing to load from config"
    )]
    let out_path = Path::new(&std::env::var("OUT_DIR").unwrap()).join("man.tgz");
    let dst = fs::File::create(out_path).unwrap();
    let encoder = GzBuilder::new()
        .filename("man.tar")
        .write(dst, Compression::best());
    let mut ar = tar::Builder::new(encoder);
    ar.mode(tar::HeaderMode::Deterministic);

    let mut add_files = |dir, extension| {
        let mut files = fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect::<Vec<_>>();
        files.sort();
        for path in files {
            if path.extension() != Some(extension) {
                continue;
            }
            println!("cargo:rerun-if-changed={}", path.display());
            ar.append_path_with_name(&path, path.file_name().unwrap())
                .unwrap();
        }
    };

    add_files(Path::new("src/etc/man"), OsStr::new("1"));
    add_files(Path::new("src/doc/man/generated_txt"), OsStr::new("txt"));
    let encoder = ar.into_inner().unwrap();
    encoder.finish().unwrap();
}

fn commit_info() {
    // Var set by bootstrap whenever omit-git-hash is enabled in the inherited config.toml.
    println!("cargo:rerun-if-env-changed=CFG_OMIT_GIT_HASH");
    #[expect(
        clippy::disallowed_methods,
        reason = "not `cargo`, not needing to load from config"
    )]
    let omit_git_hash = std::env::var_os("CFG_OMIT_GIT_HASH").is_some();

    for name in build_commit_info::BOOTSTRAP_COMMIT_ENV {
        println!("cargo:rerun-if-env-changed={name}");
    }

    // Trust: fail the build rather than silently stamping an unknown commit.
    // Upstream falls back to "no info" because a missing git repo is normal for
    // a source tarball; here the bootstrap-supplied tuple is the primary input,
    // so its absence means the build was not driven the way it must be.
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let git = build_commit_info::discover(manifest_dir, omit_git_hash).unwrap_or_else(|error| {
        panic!("failed to determine validated Targo commit metadata: {error}")
    });
    let Some(git) = git else {
        return;
    };

    println!("cargo:rustc-env=CARGO_COMMIT_HASH={}", git.hash);
    println!("cargo:rustc-env=CARGO_COMMIT_SHORT_HASH={}", git.short_hash);
    println!("cargo:rustc-env=CARGO_COMMIT_DATE={}", git.date);
}

#[expect(
    clippy::disallowed_methods,
    reason = "not `cargo`, not needing to load from config"
)]
fn windows_manifest() {
    use std::env;
    let target_os = env::var("CARGO_CFG_TARGET_OS");
    let target_env = env::var("CARGO_CFG_TARGET_ENV");
    if Ok("windows") == target_os.as_deref() && Ok("msvc") == target_env.as_deref() {
        static WINDOWS_MANIFEST_FILE: &str = "windows.manifest.xml";

        let mut manifest = env::current_dir().unwrap();
        manifest.push(WINDOWS_MANIFEST_FILE);

        println!("cargo:rerun-if-changed={WINDOWS_MANIFEST_FILE}");
        // Embed the Windows application manifest file.
        println!("cargo:rustc-link-arg-bin=cargo=/MANIFEST:EMBED");
        println!(
            "cargo:rustc-link-arg-bin=cargo=/MANIFESTINPUT:{}",
            manifest.to_str().unwrap()
        );
        // Turn linker warnings into errors.
        println!("cargo:rustc-link-arg-bin=cargo=/WX");
    }
}
