//! Tests for running multiple `cargo` processes at the same time.

use std::fs;
use std::net::TcpListener;
use std::process::Stdio;
use std::sync::mpsc::channel;
use std::thread;
use std::{env, str};

use crate::prelude::*;
use crate::utils::cargo_process;
use cargo_test_support::git;
use cargo_test_support::install::assert_has_installed_exe;
use cargo_test_support::paths;
use cargo_test_support::registry::Package;
use cargo_test_support::str;
use cargo_test_support::{basic_manifest, execs, project, retry, sleep_ms, slow_cpu_multiplier};

struct OwnedChild(std::process::Child);
impl Drop for OwnedChild {
    fn drop(&mut self) {
        if self.0.try_wait().ok().flatten().is_none() {
            #[cfg(unix)]
            unsafe {
                libc::kill(-(self.0.id() as i32), libc::SIGKILL);
            }
            #[cfg(not(unix))]
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
}

#[cargo_test]
fn opposite_dirty_siblings_acquire_without_read_upgrade_deadlock() {
    use std::io::{BufRead, BufReader, Read};
    use std::time::Instant;
    use targo::util::{Filesystem, GlobalContext};

    let p = project()
        .file("Cargo.toml", "[package]\nname='foo'\nversion='0.1.0'\nedition='2021'\n[dependencies]\na={path='a'}\nb={path='b'}\n")
        .file("src/main.rs", "fn main() { println!(\"{}{}\", a::value(), b::value()); }\n")
        .file("a/Cargo.toml", &basic_manifest("a", "0.1.0"))
        .file("a/src/lib.rs", "pub fn value() -> &'static str { env!(\"CASE_A\") }\n")
        .file("b/Cargo.toml", &basic_manifest("b", "0.1.0"))
        .file("b/src/lib.rs", "pub fn value() -> &'static str { env!(\"CASE_B\") }\n")
        .file(".cargo/config.toml", "[build]\nbuild-dir='shared'\n")
        .build();
    let command = |a: &str, b: &str| {
        let mut command = p.process(snapbox::cmd::cargo_bin!("targo"));
        command
            .args(&[
                "--unverified",
                "build",
                "-Zfine-grain-locking",
                "--message-format=json",
            ])
            .env("CASE_A", a)
            .env("CASE_B", b)
            .masquerade_as_nightly_cargo(&["fine grain locking"]);
        command
    };
    command("0", "0").run();
    let gctx = GlobalContext::default().unwrap();
    let mut held = Vec::new();
    for name in ["a", "b"] {
        let fingerprint = p
            .glob(&format!(
                "shared/debug/build/{name}/*/fingerprint/lib-{name}"
            ))
            .next()
            .unwrap()
            .unwrap();
        let lock = fingerprint
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join(".lock");
        held.push(
            Filesystem::new(p.root())
                .open_ro_shared(&lock, &gctx, "test producer barrier")
                .unwrap(),
        );
    }
    let (blocked, waiting) = channel();
    let mut children = Vec::new();
    let mut readers = Vec::new();
    for (target, a, b) in [("one", "1", "0"), ("two", "0", "1")] {
        let mut command = command(a, b)
            .arg("--target-dir")
            .arg(target)
            .build_command();
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        let mut child = OwnedChild(
            command
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap(),
        );
        let mut stdout = child.0.stdout.take().unwrap();
        let stderr = child.0.stderr.take().unwrap();
        let notice = blocked.clone();
        let out = thread::spawn(move || {
            let mut text = String::new();
            stdout.read_to_string(&mut text).unwrap();
            text
        });
        let err = thread::spawn(move || {
            let mut text = String::new();
            let mut sent = false;
            for line in BufReader::new(stderr).lines() {
                let line = line.unwrap();
                if !sent
                    && line.contains("Blocking")
                    && (line.contains("a (") || line.contains("b ("))
                {
                    notice.send(()).unwrap();
                    sent = true;
                }
                text.push_str(&line);
                text.push('\n');
            }
            text
        });
        children.push(child);
        readers.push((out, err));
    }
    for _ in 0..2 {
        waiting
            .recv_timeout(slow_cpu_multiplier(60))
            .expect("both source views must reach their contested unit write lease");
    }
    drop(held);
    let deadline = Instant::now() + slow_cpu_multiplier(60);
    loop {
        if children
            .iter_mut()
            .all(|child| child.0.try_wait().unwrap().is_some())
        {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "opposite A/B source views deadlocked on retained read leases"
        );
        sleep_ms(10);
    }
    for (child, (out, err)) in children.iter_mut().zip(readers) {
        let out = out.join().unwrap();
        let err = err.join().unwrap();
        assert!(child.0.wait().unwrap().success(), "{out}\n{err}");
    }
    for (target, expected) in [("one", "10"), ("two", "01")] {
        let binary = p
            .root()
            .join(format!("{target}/debug/foo{}", env::consts::EXE_SUFFIX));
        let result = std::process::Command::new(binary).output().unwrap();
        assert!(result.status.success());
        assert_eq!(
            String::from_utf8(result.stdout).unwrap().trim(),
            expected,
            "each original environment must produce its own program, even after the sibling graph completes"
        );
    }
}

#[cargo_test]
fn mtime_on_use_fresh_unit_keeps_the_policy_without_recompilation() {
    let p = project()
        .file("src/lib.rs", "pub fn answer() -> u32 { 42 }\n")
        .build();
    let command = |mtime: bool| {
        let mut command = p.process(snapbox::cmd::cargo_bin!("targo"));
        command
            .args(&[
                "--unverified",
                "build",
                "--lib",
                "-Zfine-grain-locking",
                "--message-format=json",
            ])
            .masquerade_as_nightly_cargo(&["fine grain locking", "mtime on use"]);
        if mtime {
            command.arg("-Zmtime-on-use");
        }
        command
    };
    command(false).run();
    let fingerprint = p
        .glob("target/debug/build/foo/*/fingerprint/lib-foo")
        .next()
        .unwrap()
        .unwrap();
    let earlier = filetime::FileTime::from_unix_time(1_000_000, 0);
    filetime::set_file_mtime(&fingerprint, earlier).unwrap();
    let output = command(true).exec_with_output().unwrap();
    let artifacts: Vec<serde_json::Value> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .filter(|row: &serde_json::Value| row["reason"] == "compiler-artifact")
        .collect();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(
        artifacts[0]["fresh"], true,
        "mtime ownership must not force a compiler invocation"
    );
    assert!(
        filetime::FileTime::from_last_modification_time(&fs::metadata(&fingerprint).unwrap())
            > earlier
    );
}

/// A parent must not cache its dependency's old output before that dependency's
/// shared lock is acquired. The existing producer changes the dependency while
/// this invocation waits, so both it AND its already-built parent must rebuild.
#[cargo_test]
fn fresh_parent_observes_dependency_only_after_its_build_lock() {
    use std::io::{BufRead, BufReader, Read};
    use std::time::Instant;
    use targo::util::{Filesystem, GlobalContext};

    let p = project()
        .file("Cargo.toml", "[package]\nname='foo'\nversion='0.1.0'\nedition='2021'\n[dependencies]\na={path='a'}\nb={path='b'}\n")
        .file("src/main.rs", "fn main() { let _ = b::stamp(); let _ = a::stamp(); }\n")
        .file("a/Cargo.toml", &basic_manifest("a", "0.1.0"))
        .file("a/src/lib.rs", "pub struct Stamp(pub u32); pub fn stamp() -> Stamp { Stamp(1) }\n")
        .file("b/Cargo.toml", "[package]\nname='b'\nversion='0.1.0'\nedition='2021'\n[dependencies]\na={path='../a'}\n")
        .file("b/src/lib.rs", "pub fn stamp() -> a::Stamp { a::stamp() }\n")
        .file(".cargo/config.toml", "[build]\nbuild-dir='shared'\n")
        .build();
    let command = || {
        let mut command = p.process(snapbox::cmd::cargo_bin!("targo"));
        command
            .args(&[
                "--unverified",
                "build",
                "-Zfine-grain-locking",
                "--message-format=json",
            ])
            .masquerade_as_nightly_cargo(&["fine grain locking"]);
        command
    };
    command().run();
    let fingerprint = p
        .glob("shared/debug/build/a/*/fingerprint/lib-a")
        .next()
        .expect("one dependency fingerprint")
        .unwrap();
    let lock = fingerprint
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join(".lock");
    let gctx = GlobalContext::default().unwrap();
    let held = Filesystem::new(p.root())
        .open_rw_exclusive_create(&lock, &gctx, "test producer barrier")
        .unwrap();
    p.change_file(
        "src/main.rs",
        "fn main() { let _ = b::stamp(); let _ = a::stamp(); } // changed root\n",
    );
    let mut child_command = command().build_command();
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        child_command.process_group(0);
    }
    let mut child = OwnedChild(
        child_command
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    let mut stdout = child.0.stdout.take().unwrap();
    let stderr = child.0.stderr.take().unwrap();
    let (blocked, waiting) = channel();
    let out = thread::spawn(move || {
        let mut text = String::new();
        stdout.read_to_string(&mut text).unwrap();
        text
    });
    let err = thread::spawn(move || {
        let mut text = String::new();
        for line in BufReader::new(stderr).lines() {
            let line = line.unwrap();
            if line.contains("Blocking") && line.contains("a (") {
                let _ = blocked.send(());
            }
            text.push_str(&line);
            text.push('\n');
        }
        text
    });
    waiting
        .recv_timeout(slow_cpu_multiplier(60))
        .expect("graph must wait for its dependency's original lock");
    p.change_file(
        "a/src/lib.rs",
        "pub struct Stamp(pub u64); pub fn stamp() -> Stamp { Stamp(2) }\n",
    );
    fs::remove_file(&fingerprint).unwrap();
    drop(held);
    let deadline = Instant::now() + slow_cpu_multiplier(60);
    let status = loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < deadline,
            "dependency observation deadlocked"
        );
        sleep_ms(10);
    };
    let out = out.join().unwrap();
    let err = err.join().unwrap();
    assert!(
        status.success(),
        "old parent metadata must not survive its dependency's rebuild: {out}\n{err}"
    );
    let artifacts: Vec<serde_json::Value> = out
        .lines()
        .filter_map(|line| serde_json::from_str(line).ok())
        .filter(|row: &serde_json::Value| row["reason"] == "compiler-artifact")
        .collect();
    for name in ["a", "b", "foo"] {
        let rows: Vec<_> = artifacts
            .iter()
            .filter(|row| row["target"]["name"] == name)
            .collect();
        assert_eq!(rows.len(), 1, "{name}: {out}");
        assert_eq!(
            rows[0]["fresh"], false,
            "{name} reused an output from before the producer transition"
        );
    }
}

/// Both invocations decide the unit is dirty before either may acquire its
/// exclusive lock. The loser must consume the winner's artifact, not compile
/// again using its old decision. Distinct target dirs avoid serializing on the
/// final-artifact directory and exercise the per-unit lock itself.
#[cargo_test]
fn identical_units_are_rechecked_after_waiting_for_the_build_lock() {
    assert_units_coalesce_after_lock(false);
}

#[cargo_test]
fn changed_source_is_checked_after_waiting_for_the_build_lock() {
    assert_units_coalesce_after_lock(true);
}

fn assert_units_coalesce_after_lock(change_source_while_waiting: bool) {
    use std::io::{BufRead, BufReader, Read};
    use std::process::Command;
    use std::time::Instant;
    use targo::util::{Filesystem, GlobalContext};

    fn own_process_group(command: &mut Command) {
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
    }

    let p = project()
        .file("src/lib.rs", "pub fn answer() -> u32 { 42 }")
        .file(".cargo/config.toml", "[build]\nbuild-dir = 'shared'\n")
        .build();
    // This exercises native compilation reuse, not verification authority.
    p.process(snapbox::cmd::cargo_bin!("targo"))
        .arg("--unverified")
        .arg("build")
        .arg("--lib")
        .arg("-Zfine-grain-locking")
        .masquerade_as_nightly_cargo(&["fine grain locking"])
        .run();

    let fingerprint = p
        .glob("shared/debug/build/foo/*/fingerprint/lib-foo")
        .next()
        .expect("one library fingerprint")
        .unwrap();
    let lock_path = fingerprint
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join(".lock");
    let gctx = GlobalContext::default().unwrap();
    let held = Filesystem::new(p.root())
        .open_ro_shared(&lock_path, &gctx, "test producer barrier")
        .unwrap();
    fs::remove_file(&fingerprint).unwrap();

    let (started, starts) = channel();
    let mut children = Vec::new();
    let mut readers = Vec::new();
    for target in ["target-a", "target-b"] {
        let mut command = p
            .process(snapbox::cmd::cargo_bin!("targo"))
            .arg("--unverified")
            .arg("build")
            .arg("--lib")
            .arg("-Zfine-grain-locking")
            .arg("--message-format=json")
            .arg("--target-dir")
            .arg(target)
            .masquerade_as_nightly_cargo(&["fine grain locking"])
            .build_command();
        own_process_group(&mut command);
        let mut child = command
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();
        let started = started.clone();
        let out = thread::spawn(move || {
            let mut bytes = Vec::new();
            stdout.read_to_end(&mut bytes).unwrap();
            String::from_utf8(bytes).unwrap()
        });
        let err = thread::spawn(move || {
            let mut text = String::new();
            for line in BufReader::new(stderr).lines() {
                let line = line.unwrap();
                if line.contains("Blocking") && line.contains("foo (") {
                    started.send(()).unwrap();
                }
                text.push_str(&line);
                text.push('\n');
            }
            text
        });
        children.push(OwnedChild(child));
        readers.push((out, err));
    }
    for _ in 0..2 {
        starts
            .recv_timeout(slow_cpu_multiplier(60))
            .expect("both builds must reach the unit lock");
    }
    if change_source_while_waiting {
        p.change_file("src/lib.rs", "pub fn answer() -> u32 { 43 }");
    }
    drop(held);

    let deadline = Instant::now() + slow_cpu_multiplier(60);
    loop {
        let statuses: Vec<_> = children
            .iter_mut()
            .map(|c| c.0.try_wait().unwrap())
            .collect();
        if statuses.iter().all(Option::is_some) {
            assert!(statuses.iter().all(|s| s.unwrap().success()));
            break;
        }
        assert!(Instant::now() < deadline, "concurrent build deadlocked");
        sleep_ms(10);
    }

    let mut fresh = Vec::new();
    for (out, err) in readers {
        let out = out.join().unwrap();
        let err = err.join().unwrap();
        let artifacts: Vec<serde_json::Value> = out
            .lines()
            .filter_map(|line| serde_json::from_str(line).ok())
            .filter(|row: &serde_json::Value| row["reason"] == "compiler-artifact")
            .collect();
        assert_eq!(artifacts.len(), 1, "{out}\n{err}");
        fresh.push(artifacts[0]["fresh"].as_bool().unwrap());
    }
    fresh.sort();
    assert_eq!(fresh, [false, true], "one compile and one reused artifact");
    if change_source_while_waiting {
        p.change_file(
            "src/main.rs",
            "fn main() { assert_eq!(foo::answer(), 43); }",
        );
        p.process(snapbox::cmd::cargo_bin!("targo"))
            .arg("--unverified")
            .arg("run")
            .arg("--quiet")
            .arg("-Zfine-grain-locking")
            .masquerade_as_nightly_cargo(&["fine grain locking"])
            .run();
    }
}

fn pkg(name: &str, vers: &str) {
    Package::new(name, vers)
        .file("src/main.rs", "fn main() {{}}")
        .publish();
}

#[cargo_test]
fn multiple_installs() {
    let p = project()
        .no_manifest()
        .file("a/Cargo.toml", &basic_manifest("foo", "0.0.0"))
        .file("a/src/main.rs", "fn main() {}")
        .file("b/Cargo.toml", &basic_manifest("bar", "0.0.0"))
        .file("b/src/main.rs", "fn main() {}");
    let p = p.build();

    let mut a = p.cargo("install").cwd("a").build_command();
    let mut b = p.cargo("install").cwd("b").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs().run_output(&a);
    execs().run_output(&b);

    assert_has_installed_exe(paths::cargo_home(), "foo");
    assert_has_installed_exe(paths::cargo_home(), "bar");
}

#[cargo_test]
fn concurrent_installs() {
    const LOCKED_BUILD: &str = "waiting for file lock on build directory";

    pkg("foo", "0.0.1");
    pkg("bar", "0.0.1");

    let mut a = cargo_process("install foo").build_command();
    let mut b = cargo_process("install bar").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    assert!(!str::from_utf8(&a.stderr).unwrap().contains(LOCKED_BUILD));
    assert!(!str::from_utf8(&b.stderr).unwrap().contains(LOCKED_BUILD));

    execs().run_output(&a);
    execs().run_output(&b);

    assert_has_installed_exe(paths::cargo_home(), "foo");
    assert_has_installed_exe(paths::cargo_home(), "bar");
}

#[cargo_test]
fn one_install_should_be_bad() {
    let p = project()
        .no_manifest()
        .file("a/Cargo.toml", &basic_manifest("foo", "0.0.0"))
        .file("a/src/main.rs", "fn main() {}")
        .file("b/Cargo.toml", &basic_manifest("foo", "0.0.0"))
        .file("b/src/main.rs", "fn main() {}");
    let p = p.build();

    let mut a = p.cargo("install").cwd("a").build_command();
    let mut b = p.cargo("install").cwd("b").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs().run_output(&a);
    execs().run_output(&b);

    assert_has_installed_exe(paths::cargo_home(), "foo");
}

#[cargo_test]
fn multiple_registry_fetches() {
    let mut pkg = Package::new("bar", "1.0.2");
    for i in 0..10 {
        let name = format!("foo{}", i);
        Package::new(&name, "1.0.0").publish();
        pkg.dep(&name, "*");
    }
    pkg.publish();

    let p = project()
        .no_manifest()
        .file(
            "a/Cargo.toml",
            r#"
                [package]
                name = "foo"
                authors = []
                version = "0.0.0"

                [dependencies]
                bar = "*"
            "#,
        )
        .file("a/src/main.rs", "fn main() {}")
        .file(
            "b/Cargo.toml",
            r#"
                [package]
                name = "bar"
                authors = []
                version = "0.0.0"

                [dependencies]
                bar = "*"
            "#,
        )
        .file("b/src/main.rs", "fn main() {}");
    let p = p.build();

    let mut a = p.cargo("build").cwd("a").build_command();
    let mut b = p.cargo("build").cwd("b").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs().run_output(&a);
    execs().run_output(&b);

    let suffix = env::consts::EXE_SUFFIX;
    assert!(
        p.root()
            .join("a/target/debug")
            .join(format!("foo{}", suffix))
            .is_file()
    );
    assert!(
        p.root()
            .join("b/target/debug")
            .join(format!("bar{}", suffix))
            .is_file()
    );
}

#[cargo_test]
fn git_same_repo_different_tags() {
    let a = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.5.0"))
            .file("src/lib.rs", "pub fn tag1() {}")
    });

    let repo = git2::Repository::open(&a.root()).unwrap();
    git::tag(&repo, "tag1");

    a.change_file("src/lib.rs", "pub fn tag2() {}");
    git::add(&repo);
    git::commit(&repo);
    git::tag(&repo, "tag2");

    let p = project()
        .no_manifest()
        .file(
            "a/Cargo.toml",
            &format!(
                r#"
                    [package]
                    name = "foo"
                    authors = []
                    version = "0.0.0"

                    [dependencies]
                    dep = {{ git = '{}', tag = 'tag1' }}
                "#,
                a.url()
            ),
        )
        .file(
            "a/src/main.rs",
            "extern crate dep; fn main() { dep::tag1(); }",
        )
        .file(
            "b/Cargo.toml",
            &format!(
                r#"
                    [package]
                    name = "bar"
                    authors = []
                    version = "0.0.0"

                    [dependencies]
                    dep = {{ git = '{}', tag = 'tag2' }}
                "#,
                a.url()
            ),
        )
        .file(
            "b/src/main.rs",
            "extern crate dep; fn main() { dep::tag2(); }",
        );
    let p = p.build();

    let mut a = p.cargo("build -v").cwd("a").build_command();
    let mut b = p.cargo("build -v").cwd("b").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs().run_output(&a);
    execs().run_output(&b);
}

#[cargo_test]
fn git_same_branch_different_revs() {
    let a = git::new("dep", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep", "0.5.0"))
            .file("src/lib.rs", "pub fn f1() {}")
    });

    let p = project()
        .no_manifest()
        .file(
            "a/Cargo.toml",
            &format!(
                r#"
                    [package]
                    name = "foo"
                    authors = []
                    version = "0.0.0"

                    [dependencies]
                    dep = {{ git = '{}' }}
                "#,
                a.url()
            ),
        )
        .file(
            "a/src/main.rs",
            "extern crate dep; fn main() { dep::f1(); }",
        )
        .file(
            "b/Cargo.toml",
            &format!(
                r#"
                    [package]
                    name = "bar"
                    authors = []
                    version = "0.0.0"

                    [dependencies]
                    dep = {{ git = '{}' }}
                "#,
                a.url()
            ),
        )
        .file(
            "b/src/main.rs",
            "extern crate dep; fn main() { dep::f2(); }",
        );
    let p = p.build();

    // Generate a Cargo.lock pointing at the current rev, then clear out the
    // target directory
    p.cargo("build").cwd("a").run();
    fs::remove_dir_all(p.root().join("a/target")).unwrap();

    // Make a new commit on the master branch
    let repo = git2::Repository::open(&a.root()).unwrap();
    a.change_file("src/lib.rs", "pub fn f2() {}");
    git::add(&repo);
    git::commit(&repo);

    // Now run both builds in parallel. The build of `b` should pick up the
    // newest commit while the build of `a` should use the locked old commit.
    let mut a = p.cargo("build").cwd("a").build_command();
    let mut b = p.cargo("build").cwd("b").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs().run_output(&a);
    execs().run_output(&b);
}

#[cargo_test]
fn same_project() {
    let p = project()
        .file("src/main.rs", "fn main() {}")
        .file("src/lib.rs", "");
    let p = p.build();

    let mut a = p.cargo("build").build_command();
    let mut b = p.cargo("build").build_command();

    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());

    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs().run_output(&a);
    execs().run_output(&b);
}

// Make sure that if Cargo dies while holding a lock that it's released and the
// next Cargo to come in will take over cleanly.
#[cargo_test]
fn killing_cargo_releases_the_lock() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                authors = []
                version = "0.0.0"
                build = "build.rs"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .file(
            "build.rs",
            r#"
                use std::net::TcpStream;

                fn main() {
                    if std::env::var("A").is_ok() {
                        TcpStream::connect(&std::env::var("ADDR").unwrap()[..])
                                  .unwrap();
                        std::thread::sleep(std::time::Duration::new(10, 0));
                    }
                }
            "#,
        );
    let p = p.build();

    // Our build script will connect to our local TCP socket to inform us that
    // it's started  and that's how we know that `a` will have the lock
    // when we kill it.
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let mut a = p.cargo("build").build_command();
    let mut b = p.cargo("build").build_command();
    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());
    a.env("ADDR", l.local_addr().unwrap().to_string())
        .env("A", "a");
    b.env("ADDR", l.local_addr().unwrap().to_string())
        .env_remove("A");

    // Spawn `a`, wait for it to get to the build script (at which point the
    // lock is held), then kill it.
    let mut a = a.spawn().unwrap();
    l.accept().unwrap();
    a.kill().unwrap();

    // Spawn `b`, then just finish the output of a/b the same way the above
    // tests does.
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    // We killed `a`, so it shouldn't succeed, but `b` should have succeeded.
    assert!(!a.status.success());
    execs().run_output(&b);
}

#[cargo_test]
fn debug_release_ok() {
    let p = project().file("src/main.rs", "fn main() {}");
    let p = p.build();

    p.cargo("build").run();
    fs::remove_dir_all(p.root().join("target")).unwrap();

    let mut a = p.cargo("build").build_command();
    let mut b = p.cargo("build --release").build_command();
    a.stdout(Stdio::piped()).stderr(Stdio::piped());
    b.stdout(Stdio::piped()).stderr(Stdio::piped());
    let a = a.spawn().unwrap();
    let b = b.spawn().unwrap();
    let a = thread::spawn(move || a.wait_with_output().unwrap());
    let b = b.wait_with_output().unwrap();
    let a = a.join().unwrap();

    execs()
        .with_stderr_data(str![[r#"
...
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `dev` profile [unoptimized + debuginfo] target(s) in [ELAPSED]s

"#]])
        .run_output(&a);
    execs()
        .with_stderr_data(str![[r#"
...
[COMPILING] foo v0.0.1 ([ROOT]/foo)
[FINISHED] `release` profile [optimized] target(s) in [ELAPSED]s

"#]])
        .run_output(&b);
}

#[cargo_test]
fn no_deadlock_with_git_dependencies() {
    let dep1 = git::new("dep1", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep1", "0.5.0"))
            .file("src/lib.rs", "")
    });

    let dep2 = git::new("dep2", |project| {
        project
            .file("Cargo.toml", &basic_manifest("dep2", "0.5.0"))
            .file("src/lib.rs", "")
    });

    let p = project()
        .file(
            "Cargo.toml",
            &format!(
                r#"
                    [package]
                    name = "foo"
                    authors = []
                    version = "0.0.0"

                    [dependencies]
                    dep1 = {{ git = '{}' }}
                    dep2 = {{ git = '{}' }}
                "#,
                dep1.url(),
                dep2.url()
            ),
        )
        .file("src/main.rs", "fn main() { }");
    let p = p.build();

    let n_concurrent_builds = 5;

    let (tx, rx) = channel();
    for _ in 0..n_concurrent_builds {
        let cmd = p
            .cargo("build")
            .build_command()
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn();
        let tx = tx.clone();
        thread::spawn(move || {
            let result = cmd.unwrap().wait_with_output().unwrap();
            tx.send(result).unwrap()
        });
    }

    for _ in 0..n_concurrent_builds {
        let result = rx.recv_timeout(slow_cpu_multiplier(30)).expect("Deadlock!");
        execs().run_output(&result);
    }
}

#[cargo_test]
fn verbose_file_lock_blocking() {
    let p = project()
        .file(
            "Cargo.toml",
            r#"
                [package]
                name = "foo"
                edition = "2024"
            "#,
        )
        .file("src/main.rs", "fn main() {}")
        .file(
            "build.rs",
            r#"
                fn main() {
                    let blocking = std::env::var("BLOCKING").unwrap_or_default();
                    if blocking == "1" {
                        std::fs::write("blocking", "").unwrap();
                        let path = std::path::Path::new("ready");
                        loop {
                            if path.exists() {
                                break;
                            } else {
                                std::thread::sleep(std::time::Duration::from_millis(100))
                            }
                        }
                    }
                }
            "#,
        )
        .build();

    // start a build that will hold the lock on the build directory
    let mut a = p
        .cargo("check")
        .build_command()
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("BLOCKING", "1")
        .spawn()
        .unwrap();

    // wait for the build script to start
    retry(100, || p.root().join("blocking").exists().then_some(()));

    let blocked_p = p
        .cargo("check -vv")
        .build_command()
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .env("BLOCKING", "0")
        .spawn()
        .unwrap();

    sleep_ms(500);

    // release the lock on the build directory
    std::fs::write(p.root().join("ready"), "").unwrap();

    let blocked_p_otpt = blocked_p.wait_with_output().unwrap();

    assert!(a.wait().unwrap().success());
    execs()
        .with_stderr_contains("[BLOCKING] waiting for file lock on build directory ([ROOT]/foo/target/debug/.cargo-build-lock)")
        .run_output(&blocked_p_otpt);
}
