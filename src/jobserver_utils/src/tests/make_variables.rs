// Trust (JOBSERVER-STALE-MAKEFLAGS-1): what a configured child is told in the GNU
// variables, read back from the command and from a real child.
use std::ffi::OsStr;
use std::process::Command;

use super::Jobserver;

fn variable(command: &Command, name: &str) -> Option<String> {
    command
        .get_envs()
        .find(|(key, _)| *key == OsStr::new(name))
        .and_then(|(_, value)| value)
        .map(|value| value.to_str().unwrap().to_owned())
}

fn handed_pair(command: &Command) -> String {
    let flags = variable(command, "CARGO_MAKEFLAGS").expect("a configured child has the pool");
    flags.rsplit_once("--jobserver-auth=").unwrap().1.to_owned()
}

#[test]
fn an_inherited_numeric_advertisement_names_the_pair_handed_over() {
    let server = Jobserver::new(2).unwrap();
    let mut command = Command::new("__metadata_only__");
    // The outer scheduler's numbers, which this child will not have.
    command.env("MAKEFLAGS", "w -j --jobserver-fds=250,251 --jobserver-auth=250,251 -- V=1");
    command.env("MFLAGS", "-j --jobserver-auth=250,251");
    server.configure(&mut command);
    let pair = handed_pair(&command);
    assert_ne!(pair, "250,251");
    assert_eq!(
        variable(&command, "MAKEFLAGS").unwrap(),
        format!("w -j --jobserver-fds={pair} --jobserver-auth={pair} -- V=1"),
        "the other make flags are kept and only the pair moves"
    );
    assert_eq!(variable(&command, "MFLAGS").unwrap(), format!("-j --jobserver-auth={pair}"));
}

#[test]
fn a_child_told_of_no_numeric_jobserver_is_still_told_of_none() {
    let server = Jobserver::new(2).unwrap();
    for flags in ["-k -j8", "w -j --jobserver-auth=fifo:/tmp/tjs-pool"] {
        let mut command = Command::new("__metadata_only__");
        command.env("MAKEFLAGS", flags);
        server.configure(&mut command);
        assert_eq!(variable(&command, "MAKEFLAGS").as_deref(), Some(flags));
    }
    // A variable removed for the child stays removed: nothing is advertised to
    // a make client that the caller did not advertise to.
    let mut command = Command::new("__metadata_only__");
    command.env_remove("MAKEFLAGS").env_remove("MFLAGS");
    server.configure(&mut command);
    assert_eq!(variable(&command, "MAKEFLAGS"), None);
    assert_eq!(variable(&command, "MFLAGS"), None);
}

#[test]
fn every_descriptor_a_child_is_told_of_is_open_in_it() {
    let server = Jobserver::new(2).unwrap();
    let mut command = Command::new("/bin/sh");
    command.env("MAKEFLAGS", "-j --jobserver-fds=250,251 --jobserver-auth=250,251").args([
        "-c",
        r#"for flags in "$MAKEFLAGS" "$CARGO_MAKEFLAGS"; do
             pair=${flags##*--jobserver-auth=}
             for fd in ${pair%%,*} ${pair##*,}; do
               [ -e "/dev/fd/$fd" ] || { echo "fd $fd of '$flags' is closed"; exit 9; }
             done
           done"#,
    ]);
    server.configure(&mut command);
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
