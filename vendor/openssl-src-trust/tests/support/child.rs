// Trust: native process fixture. Capture authority before parsing even its mode.
#[cfg(unix)]
fn main() {
    unix::run();
}

#[cfg(not(unix))]
fn main() {
    panic!("the descriptor/Make fixture requires Unix");
}

#[cfg(unix)]
mod unix {
    use std::io::{BufRead, BufReader, Write};
    use std::os::unix::net::UnixStream;
    use std::process::Command;

    use jobserver_utils::Jobserver;

    fn canary_is_open() -> bool {
        let identity = std::env::var("OPENSSL_TEST_CANARY").unwrap();
        let numbers: Vec<u64> = identity.split(',').map(|n| n.parse().unwrap()).collect();
        let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: query the inherited numeric slot, without claiming ownership.
        unsafe {
            libc::fstat(numbers[0] as i32, stat.as_mut_ptr()) == 0
                && stat.assume_init_ref().st_dev as u64 == numbers[1]
                && stat.assume_init_ref().st_ino as u64 == numbers[2]
        }
    }

    pub fn run() {
        // SAFETY: first operation, before any argument/files/sidecar processing.
        let inherited = unsafe { Jobserver::from_env() };
        match std::env::var("OPENSSL_TEST_MODE").unwrap().as_str() {
            "invalid" => assert!(inherited.is_err(), "invalid scheduler was accepted"),
            "absent" => assert!(inherited.unwrap().is_none(), "invented scheduler"),
            "relay" => {
                let server = inherited.unwrap().unwrap();
                assert!(canary_is_open(), "first hop did not receive the canary");
                let mut command = Command::new(std::env::current_exe().unwrap());
                command.env("OPENSSL_TEST_MODE", "probe");
                server.configure_make(&mut command);
                let flags = command
                    .get_envs()
                    .find_map(|(key, value)| (key == "CARGO_MAKEFLAGS").then_some(value).flatten())
                    .unwrap()
                    .to_owned();
                command.env("OPENSSL_TEST_FLAGS", flags);
                // Only Command's hook retains the fresh pair across this spawn.
                drop(server);
                assert!(command.status().unwrap().success());
            }
            "probe" => {
                let server = inherited.unwrap().unwrap();
                assert!(!canary_is_open(), "SP-1 leaked an unrelated descriptor");
                let flags = std::env::var("OPENSSL_TEST_FLAGS").unwrap();
                for key in ["CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"] {
                    assert_eq!(std::env::var(key).unwrap(), flags);
                }
                let _token = server.client().acquire().unwrap();
            }
            "leaf" => {
                assert!(
                    inherited.unwrap().is_some(),
                    "make lost the inherited scheduler"
                );
                let stream =
                    UnixStream::connect(std::env::var("OPENSSL_TEST_SOCKET").unwrap()).unwrap();
                stream
                    .set_read_timeout(Some(std::time::Duration::from_secs(15)))
                    .unwrap();
                let mut control = BufReader::new(stream);
                writeln!(control.get_mut(), "ready").unwrap();
                let mut reply = String::new();
                control.read_line(&mut reply).unwrap();
                assert_eq!(reply, "finish\n");
                if std::env::var_os("OPENSSL_TEST_FAIL").is_some() {
                    std::process::exit(3);
                }
            }
            mode => panic!("unknown fixture mode {mode}"),
        }
    }
}
