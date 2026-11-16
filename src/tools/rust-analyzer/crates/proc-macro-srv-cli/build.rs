//! Construct version in the `commit-hash date channel` format

use std::{env, path::PathBuf, process::Command};

/// Trust: the commit tuple bootstrap hands a tool's build script: the hash, the short hash and
/// the date of the commit the build is named by (a dev stage-1 build's source identity, HEAD's
/// commit otherwise; docs/DECISION_QUEUE.md, TB1-SOURCE-IDENTITY-1). When it is handed, it is
/// the version's commit, and git is neither asked nor watched.
const BOOTSTRAP_COMMIT_ENV: [&str; 3] =
    ["CFG_COMMIT_HASH", "CFG_SHORT_COMMIT_HASH", "CFG_COMMIT_DATE"];

fn main() {
    let bootstrap = bootstrap_commit_info();
    set_rerun(bootstrap.is_none());
    match bootstrap {
        Some(commit) => set_bootstrap_commit_info(commit),
        None => set_commit_info(),
    }
}

fn set_rerun(watch_git: bool) {
    println!("cargo:rerun-if-env-changed=CFG_RELEASE");
    for name in BOOTSTRAP_COMMIT_ENV {
        println!("cargo:rerun-if-env-changed={name}");
    }
    if !watch_git {
        return;
    }

    let mut manifest_dir = PathBuf::from(
        env::var("CARGO_MANIFEST_DIR").expect("`CARGO_MANIFEST_DIR` is always set by cargo."),
    );

    while manifest_dir.parent().is_some() {
        let head_ref = manifest_dir.join(".git/HEAD");
        if head_ref.exists() {
            println!("cargo:rerun-if-changed={}", head_ref.display());
            return;
        }

        manifest_dir.pop();
    }

    println!("cargo:warning=Could not find `.git/HEAD` from manifest dir!");
}

/// Trust: the commit tuple bootstrap handed this build script, whole, or `None` when it handed
/// none. A tuple handed in part names no commit and is refused.
fn bootstrap_commit_info() -> Option<[String; 3]> {
    let values = BOOTSTRAP_COMMIT_ENV.map(|name| env::var(name).ok());
    if values.iter().all(Option::is_none) {
        return None;
    }
    let [Some(hash), Some(short_hash), Some(date)] = values else {
        panic!("set all of CFG_COMMIT_HASH, CFG_SHORT_COMMIT_HASH and CFG_COMMIT_DATE, or none");
    };
    Some([hash, short_hash, date])
}

fn set_bootstrap_commit_info([hash, short_hash, date]: [String; 3]) {
    println!("cargo:rustc-env=RA_COMMIT_HASH={hash}");
    println!("cargo:rustc-env=RA_COMMIT_SHORT_HASH={short_hash}");
    println!("cargo:rustc-env=RA_COMMIT_DATE={date}");
}

fn set_commit_info() {
    #[allow(clippy::disallowed_methods)]
    let output = match Command::new("git")
        .arg("log")
        .arg("-1")
        .arg("--date=short")
        .arg("--format=%H %h %cd")
        .output()
    {
        Ok(output) if output.status.success() => output,
        _ => return,
    };
    let stdout = String::from_utf8(output.stdout).unwrap();
    let mut parts = stdout.split_whitespace();
    let mut next = || parts.next().unwrap();
    println!("cargo:rustc-env=RA_COMMIT_HASH={}", next());
    println!("cargo:rustc-env=RA_COMMIT_SHORT_HASH={}", next());
    println!("cargo:rustc-env=RA_COMMIT_DATE={}", next())
}
