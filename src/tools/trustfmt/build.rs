use std::env;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Trust: the commit tuple bootstrap hands a tool's build script: the hash, the short hash and
/// the date of the commit the build is named by (a dev stage-1 build's source identity, HEAD's
/// commit otherwise; docs/DECISION_QUEUE.md, TB1-SOURCE-IDENTITY-1). When it is handed, it is
/// the version's commit, and git is neither asked nor watched.
const BOOTSTRAP_COMMIT_ENV: [&str; 3] = [
    "CFG_COMMIT_HASH",
    "CFG_SHORT_COMMIT_HASH",
    "CFG_COMMIT_DATE",
];

fn main() {
    let bootstrap = bootstrap_commit();
    // Only check .git/HEAD dirty status if it exists - doing so when
    // building dependent crates may lead to false positives and rebuilds
    if bootstrap.is_none() && Path::new(".git/HEAD").exists() {
        println!("cargo:rerun-if-changed=.git/HEAD");
    }

    println!("cargo:rerun-if-env-changed=CFG_RELEASE_CHANNEL");
    for name in BOOTSTRAP_COMMIT_ENV {
        println!("cargo:rerun-if-env-changed={name}");
    }

    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());

    File::create(out_dir.join("commit-info.txt"))
        .unwrap()
        .write_all(commit_info(bootstrap).as_bytes())
        .unwrap();
}

// Try to get hash and date of the last commit on a best effort basis. If anything goes wrong
// (git not installed or if this is not a git repository) just return an empty string.
fn commit_info(bootstrap: Option<(String, String)>) -> String {
    let commit = bootstrap.or_else(|| Some((commit_hash()?, commit_date()?)));
    match (channel(), commit) {
        (channel, Some((hash, date))) => format!("{} ({} {})", channel, hash, date),
        _ => String::new(),
    }
}

// Trust: the hash, cut to 10 digits as `commit_hash` cuts HEAD's, and the date of the commit
// bootstrap's tuple names, or `None` when bootstrap handed none. A tuple handed in part names
// no commit and is refused.
fn bootstrap_commit() -> Option<(String, String)> {
    let values = BOOTSTRAP_COMMIT_ENV.map(|name| env::var(name).ok());
    if values.iter().all(Option::is_none) {
        return None;
    }
    let [Some(hash), Some(_), Some(date)] = values else {
        panic!("set all of CFG_COMMIT_HASH, CFG_SHORT_COMMIT_HASH and CFG_COMMIT_DATE, or none");
    };
    Some((hash.chars().take(10).collect(), date))
}

fn channel() -> String {
    if let Ok(channel) = env::var("CFG_RELEASE_CHANNEL") {
        channel
    } else {
        "nightly".to_owned()
    }
}

fn commit_hash() -> Option<String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()?;
    let mut stdout = output.status.success().then_some(output.stdout)?;
    stdout.truncate(10);
    String::from_utf8(stdout).ok()
}

fn commit_date() -> Option<String> {
    let output = Command::new("git")
        .args(["log", "-1", "--date=short", "--pretty=format:%cd"])
        .output()
        .ok()?;
    let stdout = output.status.success().then_some(output.stdout)?;
    String::from_utf8(stdout).ok()
}
