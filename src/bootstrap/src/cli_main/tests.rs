// Trust: this file is Trust-owned. It pins the build-start line an `x.py` run leaves for aterm
// (`build_start` in `cli_main.rs`, DC-12c).

use std::collections::HashMap;
use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::{PermissionsExt as _, symlink};
use std::path::{Path, PathBuf};

use super::build_start::{self, RECORD, SESSION_ENV};
use crate::core::builder::Kind;

const TAB: &str = "t0qje5bafqr";
const LEGACY: &str = "s-0123456789abcdef0123";

/// A home with aterm's state folder made (`made`), a checkout reached through a link, and a
/// build directory.
struct Home {
    _tmp: tempfile::TempDir,
    home: PathBuf,
    state: PathBuf,
    checkout: PathBuf,
    linked_checkout: PathBuf,
    build: PathBuf,
}

impl Home {
    fn new(made: bool) -> Self {
        let tmp = tempfile::tempdir().unwrap();
        let root = tmp.path().canonicalize().unwrap();
        let home = root.join("home");
        let state = build_start::state_dir(
            &|name| (name == "HOME").then(|| home.clone().into_os_string()),
            cfg!(target_os = "macos"),
        )
        .unwrap();
        fs::create_dir_all(&home).unwrap();
        if made {
            fs::create_dir_all(&state).unwrap();
        }
        let checkout = root.join("trust");
        let build = checkout.join("build");
        fs::create_dir_all(&build).unwrap();
        let linked_checkout = root.join("trust-link");
        symlink(&checkout, &linked_checkout).unwrap();
        Home { _tmp: tmp, home, state, checkout, linked_checkout, build }
    }

    fn env(&self, vars: &[(&str, &str)]) -> HashMap<String, OsString> {
        let mut env: HashMap<String, OsString> =
            vars.iter().map(|(k, v)| (k.to_string(), OsString::from(v))).collect();
        env.insert("HOME".into(), self.home.clone().into_os_string());
        env
    }

    fn append(&self, env: &HashMap<String, OsString>, workspace: &Path, build: &Path) -> bool {
        build_start::append(&|name| env.get(name).cloned(), workspace, build, 4242, 1_700_000)
    }

    fn record(&self) -> PathBuf {
        self.state.join(RECORD)
    }
}

#[test]
fn disk_custody_a_run_in_a_tab_writes_the_start_line() {
    let h = Home::new(true);
    let env = h.env(&[(SESSION_ENV, TAB), ("ATERM_SESSION_ID", "t1111111111")]);
    // The checkout is named through a link; the line names it with its links resolved.
    assert!(h.append(&env, &h.linked_checkout, &h.linked_checkout.join("build")));
    let text = fs::read_to_string(h.record()).unwrap();
    assert!(text.ends_with('\n') && text.lines().count() == 1, "{text:?}");
    assert!(text.len() <= build_start::MAX_LINE);
    let line: serde_json::Value = serde_json::from_str(text.trim_end()).unwrap();
    assert_eq!(line["v"], 1);
    // The tab's own session, never a nested aterm's `ATERM_SESSION_ID`.
    assert_eq!(line["session"], TAB);
    assert_eq!(line["workspace"], h.checkout.to_str().unwrap());
    assert_eq!(line["build"], h.build.to_str().unwrap());
    assert_eq!(line["pid"], 4242);
    assert_eq!(line["at_ms"], 1_700_000);
    // A private file.
    assert_eq!(fs::metadata(h.record()).unwrap().permissions().mode() & 0o777, 0o600);

    // A second run appends; a legacy tab's session is a session too.
    let legacy = h.env(&[(SESSION_ENV, LEGACY)]);
    assert!(h.append(&legacy, &h.checkout, &h.build));
    let again = fs::read_to_string(h.record()).unwrap();
    assert!(again.starts_with(&text), "{again:?}");
    let second: serde_json::Value = serde_json::from_str(again.lines().nth(1).unwrap()).unwrap();
    assert_eq!(second["session"], LEGACY);

    // A run that may build writes; the place on other Unix systems is XDG's state folder.
    assert!(build_start::wanted(false, Kind::Build));
    assert!(build_start::wanted(false, Kind::Test));
    let xdg = |name: &str| match name {
        "XDG_STATE_HOME" => Some(OsString::from("/x/state")),
        "HOME" => Some(OsString::from("/h")),
        _ => None,
    };
    assert_eq!(build_start::state_dir(&xdg, false), Some(PathBuf::from("/x/state/aterm")));
    assert_eq!(
        build_start::state_dir(&xdg, true),
        Some(PathBuf::from("/h/Library/Application Support/aterm"))
    );
    let relative_xdg = |name: &str| match name {
        "XDG_STATE_HOME" => Some(OsString::from("state")),
        "HOME" => Some(OsString::from("/h")),
        _ => None,
    };
    assert_eq!(
        build_start::state_dir(&relative_xdg, false),
        Some(PathBuf::from("/h/.local/state/aterm"))
    );
}

#[test]
fn disk_custody_a_run_outside_a_tab_or_dry_writes_none() {
    let h = Home::new(true);
    // Outside a tab: no `ATERM_PARENT_SESSION_ID`, whatever else aterm put there.
    assert!(!h.append(&h.env(&[("ATERM_SESSION_ID", TAB)]), &h.checkout, &h.build));
    // A value that is no session: too short, upper case, a letter outside the alphabet.
    for bad in ["t0qje5bafq", "T0QJE5BAFQR", "t0qje5bafqi", "s-0123456789ABCDEF0123", ""] {
        assert!(!h.append(&h.env(&[(SESSION_ENV, bad)]), &h.checkout, &h.build), "{bad}");
    }
    // A checkout or build directory that cannot be resolved.
    let tab = h.env(&[(SESSION_ENV, TAB)]);
    assert!(!h.append(&tab, &h.checkout.join("gone"), &h.build));
    assert!(!h.append(&tab, &h.checkout, &h.checkout.join("gone")));
    assert!(!h.record().exists(), "nothing was written");
    // A dry run, and a run that writes no build output, leave no line.
    assert!(!build_start::wanted(true, Kind::Build));
    for kind in [Kind::Clean, Kind::Setup, Kind::Format, Kind::Vendor] {
        assert!(!build_start::wanted(false, kind), "{kind:?}");
    }
    // A record that is a link is never followed, nor one that is no regular file.
    let elsewhere = h.home.join("elsewhere");
    fs::write(&elsewhere, b"").unwrap();
    symlink(&elsewhere, h.record()).unwrap();
    assert!(!h.append(&tab, &h.checkout, &h.build));
    assert_eq!(fs::read(&elsewhere).unwrap(), b"");
    fs::remove_file(h.record()).unwrap();
    fs::create_dir(h.record()).unwrap();
    assert!(!h.append(&tab, &h.checkout, &h.build));
    fs::remove_dir(h.record()).unwrap();
    // The control: with a regular record (or none) the same run writes.
    assert!(h.append(&tab, &h.checkout, &h.build));

    // Where aterm made no state folder, none is made and nothing is written.
    let bare = Home::new(false);
    assert!(!bare.append(&bare.env(&[(SESSION_ENV, TAB)]), &bare.checkout, &bare.build));
    assert!(!bare.state.exists());
    // A line that would be too long is no line.
    let long = Path::new("/").join("x".repeat(build_start::MAX_LINE));
    assert_eq!(build_start::line(TAB, &long, Path::new("/b"), 1, 1), None);
    assert!(build_start::line(TAB, Path::new("/w"), Path::new("/b"), 1, 1).is_some());
    assert_eq!(build_start::line(TAB, Path::new("w"), Path::new("/b"), 1, 1), None);
}

/// A line of `session` on `workspace` at `at_ms`, as a writer appends it.
fn record_line(session: &str, workspace: &str, at_ms: u64) -> String {
    build_start::line(session, Path::new(workspace), Path::new("/b"), 1, at_ms).unwrap()
}

#[test]
fn the_start_record_stays_bounded_where_bootstrap_writes_alone() {
    use std::os::fd::AsRawFd as _;
    const WEEK: u64 = build_start::KEEP_PAIR_MS;
    let h = Home::new(true);
    let now = 1_700_000_000_000;
    // A record past the cap: the old lines of 40 workspaces, the newest last, a line aterm's
    // reader skips, and a session's young line of a workspace a later session built in.
    let mut text = String::new();
    let mut at = 0;
    while (text.len() as u64) <= build_start::CAP {
        text.push_str(&record_line(TAB, &format!("/w/{}", at % 40), now - 3 * WEEK + at));
        at += 1;
    }
    text.push_str("{\"v\":2,\"session\":\"t0qje5bafqr\"}\n");
    text.push_str(&record_line(LEGACY, "/w/young", now - 1000));
    text.push_str(&record_line(TAB, "/w/young", now - 500));
    text.push_str(&record_line(LEGACY, "/w/stale", now - 2 * WEEK));
    text.push_str(&record_line(TAB, "/w/stale", now - 2 * WEEK + 1));
    fs::write(h.record(), &text).unwrap();
    let tab = h.env(&[(SESSION_ENV, TAB)]);

    // The control: while another writer holds the rewrite's lock, the line is appended and the
    // record left as it is.
    let lock = fs::File::create(h.state.join(build_start::LOCK)).unwrap();
    // SAFETY: `lock` is open for the call.
    assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) }, 0);
    assert!(build_start::append(&|n| tab.get(n).cloned(), &h.checkout, &h.build, 7, now));
    let held = fs::read_to_string(h.record()).unwrap();
    assert!(held.starts_with(&text) && held.len() > text.len());
    // Release the lock itself, not only this descriptor: a process another test thread is
    // starting can hold a copy of the open description, and closing ours would leave the lock
    // held for the rewrite's non-blocking take (`crate::utils::tests::isolated` says how).
    // `copy` is such a copy, held until the rewrite is judged, so every run takes that path.
    let copy = lock.try_clone().unwrap();
    // SAFETY: `lock` is open for the call.
    assert_eq!(unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) }, 0);
    drop(lock);
    let probe = fs::OpenOptions::new().append(true).open(h.state.join(build_start::LOCK)).unwrap();
    // SAFETY: `probe` is open for the call.
    assert_eq!(
        unsafe { libc::flock(probe.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) },
        0,
        "the control's lock outlived its release"
    );
    // SAFETY: `probe` is open for the call.
    assert_eq!(unsafe { libc::flock(probe.as_raw_fd(), libc::LOCK_UN) }, 0);
    drop(probe);

    // The next line rewrites it to what aterm's rewrite keeps, under half the cap.
    assert!(build_start::append(&|n| tab.get(n).cloned(), &h.checkout, &h.build, 8, now));
    let kept = fs::read_to_string(h.record()).unwrap();
    assert!(
        (kept.len() as u64) <= build_start::KEEP_MAX,
        "{} bytes kept; a staged rewrite left behind: {}",
        kept.len(),
        h.state.join(build_start::STAGE).exists()
    );
    drop(copy);
    let said: Vec<(String, String, u64)> =
        kept.lines().map(|line| build_start::parse(line).unwrap()).collect();
    // The newest line of each workspace, oldest first.
    let last = at - 1;
    let mut times = Vec::new();
    for w in 0..40 {
        let workspace = format!("/w/{w}");
        let lines: Vec<u64> =
            said.iter().filter(|(_, ws, _)| *ws == workspace).map(|(_, _, t)| *t).collect();
        assert_eq!(lines, [now - 3 * WEEK + last - (last - w) % 40], "{workspace}");
        times.push(lines[0]);
    }
    let in_order: Vec<u64> =
        said.iter().filter(|(_, ws, _)| ws.len() <= 5).map(|(_, _, t)| *t).collect();
    times.sort();
    assert_eq!(in_order, times);
    // A young line of an earlier session stays beside the newest of its workspace; a stale one
    // goes.
    let of = |ws: &str| -> Vec<&str> {
        said.iter().filter(|(_, w, _)| w == ws).map(|(s, _, _)| s.as_str()).collect()
    };
    assert_eq!(of("/w/young"), [LEGACY, TAB]);
    assert_eq!(of("/w/stale"), [TAB]);
    // The skipped line went; both lines of this run are there, the newest last.
    assert!(!kept.contains("\"v\":2"));
    let checkout = h.checkout.to_str().unwrap();
    assert_eq!(of(checkout), [TAB]);
    let newest: serde_json::Value = serde_json::from_str(kept.lines().last().unwrap()).unwrap();
    assert_eq!((&newest["workspace"], &newest["pid"]), (&checkout.into(), &8.into()));
    assert!(!h.state.join(build_start::STAGE).exists());
    // Under the cap, a line is appended alone.
    assert!(build_start::append(&|n| tab.get(n).cloned(), &h.checkout, &h.build, 9, now));
    assert!(fs::read_to_string(h.record()).unwrap().starts_with(&kept));
}
