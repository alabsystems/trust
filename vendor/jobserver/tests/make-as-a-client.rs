use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::net::{TcpListener, TcpStream};
use std::process::Command;
use std::time::{Duration, Instant};

use jobserver::Client;

macro_rules! t {
    ($e:expr) => {
        match $e {
            Ok(e) => e,
            Err(e) => panic!("{} failed with {}", stringify!($e), e),
        }
    };
}

fn main() {
    if env::var("_DO_THE_TEST").is_ok() {
        // Forwarding environment strings alone does not hand the descriptors
        // across this second spawn, especially with Trust's fd inheritance
        // guard. Import the pool and explicitly configure every child hop.
        let client = unsafe { Client::from_env() }.expect("wrapper did not inherit the jobserver");
        let mut cmd = Command::new(env::var_os("MAKE").unwrap());
        cmd.env_remove("_DO_THE_TEST")
            .args(&env::args_os().skip(1).collect::<Vec<_>>());
        client.configure_make(&mut cmd);
        std::process::exit(cmd.status().unwrap().code().unwrap_or(1));
    }

    if let Ok(s) = env::var("TEST_ADDR") {
        let mut stream = t!(TcpStream::connect(&s));
        t!(stream.set_read_timeout(Some(Duration::from_secs(10))));
        let mut contents = Vec::new();
        t!(stream.read_to_end(&mut contents));
        return;
    }

    let c = t!(Client::new(1));
    let td = tempfile::tempdir().unwrap();

    let prog = env::var("MAKE").unwrap_or_else(|_| "make".to_string());

    let me = t!(env::current_exe());
    let me = me.to_str().unwrap();

    let mut cmd = Command::new(&me);
    cmd.current_dir(td.path());
    cmd.env("MAKE", prog);
    cmd.env("_DO_THE_TEST", "1");

    t!(t!(File::create(td.path().join("Makefile"))).write_all(
        format!(
            "\
all: foo bar
foo:
\t{0}
bar:
\t{0}
",
            me
        )
        .as_bytes()
    ));

    // We're leaking one extra token to `make` sort of violating the makefile
    // jobserver protocol. It has the desired effect though.
    c.configure(&mut cmd);

    let listener = t!(TcpListener::bind("127.0.0.1:0"));
    t!(listener.set_nonblocking(true));
    let addr = t!(listener.local_addr());
    cmd.env("TEST_ADDR", addr.to_string());
    let mut child = t!(cmd.spawn());

    // Both recipes must connect before either is released. Bound the barrier
    // so a lost jobserver (make falling back to -j1) fails instead of waiting
    // forever for the second recipe while the first waits for EOF.
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut connections = Vec::new();
    loop {
        if connections.len() < 2 {
            match listener.accept() {
                Ok(connection) => connections.push(connection),
                Err(err) if err.kind() == std::io::ErrorKind::WouldBlock => {}
                Err(err) => panic!("accept failed: {}", err),
            }
            if connections.len() == 2 {
                connections.clear();
                break;
            }
        }
        if let Some(status) = t!(child.try_wait()) {
            panic!("make exited before both recipes connected: {}", status);
        }
        if Instant::now() >= deadline {
            t!(child.kill());
            t!(child.wait());
            panic!("make did not run both recipes concurrently");
        }
        std::thread::sleep(Duration::from_millis(10));
    }

    loop {
        if let Some(status) = t!(child.try_wait()) {
            assert!(status.success());
            break;
        }
        if Instant::now() >= deadline {
            t!(child.kill());
            t!(child.wait());
            panic!("make did not exit after both recipes were released");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}
