//! Trust (COMPILETEST-JOBSERVER-CUSTODY-1): the compiletest root's captured GNU
//! transport still reaches its fixed queries, and its advertisement never
//! reaches an ordinary per-case child that is handed no descriptor.
//!
//! The fixture launches this very unit binary the way Bootstrap launches the
//! compiletest root (`metadata_scheduler::configure_original_transport`): an
//! actual empty pipe, advertised in the three variables `configure_make` writes
//! and explicitly inherited. Every role re-enters through the genuine native
//! entry (`query_test_main`), so the real capture, the real std spawn and the
//! real importer decide; no synthetic owner is installed. The `case` role is
//! launched as a ui or run-make case's compiler is: an ordinary `Command` that
//! inherits the root's environment.

use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::process::CommandExt;
use std::process::{Command, Output};

use trust_resource_controller::client;

const ROLE: &str = "TRUST_COMPILETEST_ENTRY_TRANSPORT_ROLE";

/// Every GNU option a fixed query must receive open: run as that query.
const ADVERTISED_DESCRIPTORS_OPEN: &str = r#"
for value in "${CARGO_MAKEFLAGS-}" "${MAKEFLAGS-}" "${MFLAGS-}"; do
  case "$value" in *--jobserver-auth=*) ;; *) echo "no GNU auth in: [$value]" >&2; exit 3 ;; esac
  auth=${value##*--jobserver-auth=}
  auth=${auth%% *}
  read=${auth%%,*}
  write=${auth##*,}
  if [ ! -e "/dev/fd/$read" ] || [ ! -e "/dev/fd/$write" ]; then
    echo "advertised $auth is not open in the query" >&2
    exit 4
  fi
done
echo "entry-transport query: open"
"#;

fn reenter(role: &str) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    let test = format!("tests::entry_transport::{role}_role");
    command
        .args(["--ignored", "--exact", &test, "--test-threads=1", "--nocapture"])
        .env(ROLE, role);
    command
}

fn in_role(role: &str) -> bool {
    std::env::var_os(ROLE).is_some_and(|actual| actual == role)
}

/// Success alone is not a pass: a filter that selects nothing also exits 0.
/// (A serial libtest prints the test's name before its output, on one line.)
fn passed(output: &Output, marker: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains(marker),
        "expected `{marker}`; {}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        output.status
    );
}

/// Hand `pipe` to `root` as Bootstrap's original transport does
/// (`jobserver_utils::Jobserver::configure_make`, then
/// `client::inherit_descriptions`): no descendant handoff, the same auth in all
/// three variables, the pair explicitly inherited and inheritable across exec.
fn advertise(root: &mut Command, pipe: [RawFd; 2]) {
    let auth = format!("{},{}", pipe[0], pipe[1]);
    let flags = format!("-j --jobserver-fds={auth} --jobserver-auth={auth}");
    root.env_remove("CARGO_JOBSERVER_HANDOFF")
        .env("CARGO_MAKEFLAGS", &flags)
        .env("MAKEFLAGS", &flags)
        .env("MFLAGS", &flags);
    if client::explicit_inheritance_supported() {
        client::inherit_descriptions(root, &pipe).unwrap();
    }
    // SAFETY: only async-signal-safe fcntl calls run after fork; the caller
    // keeps both descriptors open through the root's complete wait.
    unsafe {
        root.pre_exec(move || {
            for fd in pipe {
                let flags = libc::fcntl(fd, libc::F_GETFD);
                if flags < 0 || libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
}

#[test]
fn ordinary_case_children_inherit_no_dangling_gnu_advertisement() {
    // An empty pipe, as a new owned scheduler with no tokens is.
    let (read, write) = std::io::pipe().unwrap();
    let mut root = reenter("root");
    // The measured route carries GNU transport only. This process's own SDK
    // lease, if any, is not forwarded here, so its locator must not be either.
    root.env_remove(client::sdk::SDK_LEASE_ENV);
    advertise(&mut root, [read.as_raw_fd(), write.as_raw_fd()]);
    passed(&root.output().unwrap(), "entry-transport root: ok");
    // The owner outlives the root's complete wait above.
    drop((read, write));
}

#[test]
#[ignore = "a role, re-entered by ordinary_case_children_inherit_no_dangling_gnu_advertisement"]
fn root_role() {
    if !in_role("root") {
        return;
    }
    // The failing route: an ordinary launch whose genuine entry imports any
    // inherited GNU advertisement, exactly as each case's compiler does.
    passed(&reenter("case").output().unwrap(), "entry-transport case: ok");
    for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
        assert!(std::env::var_os(name).is_none(), "{name} still advertises the captured transport");
    }
    // A stale advertisement still fails at genuine native entry. Do not let
    // per-case forwarding turn malformed ambient numbers into a fresh pool.
    let mut stale = reenter("case");
    for name in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
        stale.env(name, "-j --jobserver-auth=999998,999999");
    }
    let rejected = stale.output().unwrap();
    assert_eq!(rejected.status.code(), Some(75));
    assert!(String::from_utf8_lossy(&rejected.stderr).contains("invalid advertised jobserver"));

    // Query custody is unchanged: a fixed query receives open descriptors.
    let mut query = Command::new("/bin/sh");
    query.args(["-c", ADVERTISED_DESCRIPTORS_OPEN]);
    let query = crate::query_output(&mut query);
    if client::explicit_inheritance_supported() {
        passed(&query.unwrap(), "entry-transport query: open");
    } else {
        // Stock std cannot forward the captured transport and refuses instead.
        assert_eq!(query.unwrap_err().kind(), std::io::ErrorKind::Unsupported);
    }
    // Producing case launch borrows the SAME retained transport, explicitly
    // forwarding it instead of mistaking query-only capture for admission.
    if client::explicit_inheritance_supported() {
        let mut command = reenter("case");
        passed(&crate::case_scheduler::output(&mut command).unwrap(), "entry-transport case: ok");
        let mut command = Command::new("/bin/sh");
        command.args(["-c", ADVERTISED_DESCRIPTORS_OPEN]);
        passed(
            &crate::case_scheduler::output(&mut command).unwrap(),
            "entry-transport query: open",
        );
    }
    println!("entry-transport root: ok");
}

#[test]
#[ignore = "a role, re-entered by root_role"]
fn case_role() {
    if !in_role("case") {
        return;
    }
    // Reaching this line means this child's own entry capture accepted the
    // environment an ordinary case launch gave it.
    println!("entry-transport case: ok");
}
