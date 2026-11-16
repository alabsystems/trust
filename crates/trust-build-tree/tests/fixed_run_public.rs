//! Opt-in actual CLI qualification, outside the compiler's build-slot epoch.
//! No private CPU domain, marker-based admission, or invented scheduler.

#![cfg(all(
    target_os = "macos",
    target_arch = "aarch64",
    feature = "native-cli-tests",
    feature = "native-exec"
))]

use std::io::{self, Read as _};
use std::os::fd::AsRawFd as _;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[test]
fn actual_fixed_run_keeps_the_original_gnu_pool_below_its_cpu_ceiling() -> io::Result<()> {
    assert!(std::env::var_os("BUILD_SLOT_HELD").is_none(), "run after compiler admission ends");
    assert!(
        std::env::var_os("CARGO_MAKEFLAGS").is_none(),
        "supply only this fixture's actual GNU owner"
    );
    let case = std::env::var("TRUST_FIXED_RUN_CASE").unwrap_or_else(|_| "cap2".into());
    let (bench, behavior) =
        case.strip_prefix("bench-").map_or((false, case.as_str()), |v| (true, v));
    assert!(
        matches!(behavior, "cap1" | "cap2" | "nonzero" | "cancel" | "unknown"),
        "unsupported real case"
    );
    let cap = if behavior == "cap1" { "1" } else { "2" };
    let selected = std::path::PathBuf::from(
        std::env::var_os("TRUST_BUILD_TREE_TARGO").expect("select immutable actual Targo"),
    );
    let image = trust_resource_provenance::program::HeldSystemCommand::open(
        &selected,
        Instant::now() + Duration::from_secs(30),
    )?;
    assert_eq!(
        image.observation().executable.sha256,
        std::env::var("TRUST_BUILD_TREE_TARGO_SHA256").unwrap()
    );
    let artifact_root =
        std::env::var_os("TRUST_FIXED_RUN_ARTIFACT_ROOT").expect("retain actual fixture inputs");
    std::fs::create_dir_all(&artifact_root)?;
    let root = tempfile::Builder::new().prefix("fixed-run-").tempdir_in(artifact_root)?.keep();
    let root = std::fs::canonicalize(root)?;
    assert!(Command::new("/usr/bin/git").args(["init", "--quiet"]).arg(&root).status()?.success());
    std::fs::create_dir(root.join("src"))?;
    std::fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='actual-fixed-run-gnu'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[[bench]]\nname='fixed-run-probe'\npath='src/main.rs'\nharness=false\n",
    )?;
    if bench && behavior == "cancel" {
        let extra =
            "\n[[bench]]\nname='zz-after-cancel'\npath='src/after_cancel.rs'\nharness=false\n";
        use std::io::Write as _;
        std::fs::OpenOptions::new()
            .append(true)
            .open(root.join("Cargo.toml"))?
            .write_all(extra.as_bytes())?;
        std::fs::write(
            root.join("src/after_cancel.rs"),
            "fn main(){std::fs::write(std::env::var_os(\"NATIVE_FIXED_RUN_NEXT\").unwrap(),b\"incorrect dispatch\").unwrap();}\n",
        )?;
    }
    std::fs::write(
        root.join("src/main.rs"),
        r#"
use std::io::{Read,Write};
use std::os::fd::{FromRawFd,AsRawFd};
use std::os::unix::fs::OpenOptionsExt;
#[repr(C)] struct PollFd { fd:i32, events:i16, revents:i16 }
unsafe extern "C" { fn poll(fds:*mut PollFd,n:u32,timeout:i32)->i32; fn signal(sig:i32,handler:usize)->usize; }
static CANCELLED:std::sync::atomic::AtomicBool=std::sync::atomic::AtomicBool::new(false);
extern "C" fn term(_:i32){CANCELLED.store(true,std::sync::atomic::Ordering::SeqCst);}
fn main(){
    let mode=std::env::var("NATIVE_FIXED_RUN_MODE").unwrap();
    let cap=std::env::var("NATIVE_FIXED_RUN_CEILING").unwrap().parse::<usize>().unwrap();
    if mode=="cancel" {assert_ne!(unsafe{signal(15,term as *const () as usize)},usize::MAX);}
    let flags=std::env::var("CARGO_MAKEFLAGS").unwrap();
    let auth=flags.split_whitespace().find_map(|s|s.strip_prefix("--jobserver-auth=")).unwrap();
    let (mut read,mut write)=if let Some(path)=auth.strip_prefix("fifo:") {
        (std::fs::OpenOptions::new().read(true).custom_flags(4).open(path).unwrap(),
         std::fs::OpenOptions::new().write(true).custom_flags(4).open(path).unwrap())
    } else {
        let mut fds=auth.split(',').map(|v|v.parse::<i32>().unwrap());
        unsafe{(std::fs::File::from_raw_fd(fds.next().unwrap()),std::fs::File::from_raw_fd(fds.next().unwrap()))}
    };
    let deadline=std::time::Instant::now()+std::time::Duration::from_secs(10);
    let mut credits=Vec::new();
    while credits.is_empty() && cap>1 {
        let mut p=PollFd{fd:read.as_raw_fd(),events:1,revents:0};
        if unsafe{poll(&mut p,1,1)}>0 { let mut b=[0]; read.read_exact(&mut b).unwrap(); credits.push(b[0]); }
        assert!(std::time::Instant::now()<deadline,"actual funded supplementary credit missing");
    }
    let until=std::time::Instant::now()+std::time::Duration::from_millis(150);
    while std::time::Instant::now()<until {
        let mut p=PollFd{fd:read.as_raw_fd(),events:1,revents:0};
        if unsafe{poll(&mut p,1,1)}>0 { let mut b=[0]; read.read_exact(&mut b).unwrap(); credits.push(b[0]); }
    }
    if mode=="cancel" {
        std::fs::write(std::env::var_os("NATIVE_FIXED_RUN_READY").unwrap(),b"actual-token-held").unwrap();
        let deadline=std::time::Instant::now()+std::time::Duration::from_secs(60);
        while !CANCELLED.load(std::sync::atomic::Ordering::SeqCst){
            assert!(std::time::Instant::now()<deadline,"original owner did not forward cancellation");
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
        println!("ACTUAL_FIXED_RUN_CANCELLED=1");
    }
    if mode!="unknown" {write.write_all(&credits).unwrap();}
    println!("ACTUAL_FIXED_RUN_GNU_SUPPLEMENTARY={}",credits.len());
    println!("ACTUAL_FIXED_RUN_GNU_AUTH={auth}");
    assert_eq!(std::env::var("MAKEFLAGS").unwrap(),flags,"MAKEFLAGS selected another pool");
    assert_eq!(std::env::var("MFLAGS").unwrap(),flags,"MFLAGS selected another pool");
    if mode=="nonzero" {std::process::exit(3);}
    if mode=="unknown" {println!("ACTUAL_TARGET_EXIT=0-WITH-UNRETURNED-BYTE");}
}
"#,
    )?;
    let original = jobserver_utils::Jobserver::new(6)?;
    original.client().acquire_raw()?;
    assert_eq!(original.client().available()?, 5);
    let fd = original.pipe_descriptors().unwrap()[0].as_raw_fd();
    let before = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    assert_ne!(before, -1);
    let mut command = Command::new(image.program());
    command
        .current_dir(&root)
        .args([
            "--unverified",
            "resource",
            "fixed",
            "--cpus",
            cap,
            "--wait-seconds",
            "60",
            "--",
            if bench { "bench" } else { "run" },
            "--offline",
        ])
        .arg(format!("-j{cap}"))
        .env("CARGO_BUILD_JOBS", cap)
        .env("NATIVE_FIXED_RUN_MODE", behavior)
        .env("NATIVE_FIXED_RUN_CEILING", cap)
        .env("NATIVE_FIXED_RUN_READY", root.join("target-ready"))
        .env("NATIVE_FIXED_RUN_NEXT", root.join("incorrect-next-dispatch"))
        .env(
            "RUSTC",
            std::env::var_os("TRUST_FIXED_RUN_COMPILER").expect("select genuine retained compiler"),
        )
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    if bench {
        command.args(["--bench", "fixed-run-probe"]);
        if behavior == "cancel" {
            command.args(["--bench", "zz-after-cancel", "--no-fail-fast"]);
        }
    }
    original.configure_make(&mut command);
    let mut child = command.spawn()?;
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    let drain = |mut stream: Box<dyn io::Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            stream.by_ref().take(1024 * 1024 + 1).read_to_end(&mut bytes).unwrap();
            assert!(bytes.len() <= 1024 * 1024);
            bytes
        })
    };
    let out = drain(Box::new(stdout));
    let err = drain(Box::new(stderr));
    if behavior == "cancel" {
        let deadline = Instant::now() + Duration::from_secs(90);
        while !root.join("target-ready").exists() {
            assert!(
                child.try_wait()?.is_none(),
                "actual fixed owner exited before target readiness"
            );
            if Instant::now() >= deadline {
                // This is this test's original unreaped root. Ask its actual
                // group owner to cancel, then retain the owning wait.
                unsafe {
                    libc::kill(child.id() as libc::pid_t, libc::SIGTERM);
                }
                let _ = child.wait();
                panic!("actual run target never reached its cancellation boundary");
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        assert_eq!(std::fs::read(root.join("target-ready"))?, b"actual-token-held");
        assert!(child.try_wait()?.is_none(), "cancellation requires our original unreaped root");
        assert_eq!(unsafe { libc::kill(child.id() as libc::pid_t, libc::SIGTERM) }, 0);
    }
    let status = child.wait()?;
    let stdout = out.join().unwrap();
    let stderr = err.join().unwrap();
    std::fs::write(root.join("actual-stdout"), &stdout)?;
    std::fs::write(root.join("actual-stderr"), &stderr)?;
    println!("retained actual fixed run world={}", root.display());
    println!(
        "status={status} stdout={} stderr={}",
        String::from_utf8_lossy(&stdout),
        String::from_utf8_lossy(&stderr)
    );
    assert_eq!(unsafe { libc::fcntl(fd, libc::F_GETFL) }, before, "parent GNU flags changed");
    assert_eq!(
        original.client().available()?,
        if behavior == "unknown" { 4 } else { 5 },
        "actual original GNU settlement disagreed with the observed outcome"
    );
    image.validate(Instant::now() + Duration::from_secs(30))?;
    if behavior == "unknown" {
        assert_eq!(status.code(), Some(101), "target0 cannot make failed retirement successful");
        assert!(
            String::from_utf8_lossy(&stdout).contains("ACTUAL_TARGET_EXIT=0-WITH-UNRETURNED-BYTE")
        );
        assert!(String::from_utf8_lossy(&stderr).contains("target ended (exit status: 0)"));
        assert!(String::from_utf8_lossy(&stderr).contains("GNU credits remain outstanding"));
    } else if bench && behavior == "cancel" {
        assert_eq!(status.code(), Some(101), "canceled phase cannot continue bench dispatch");
        assert!(
            !root.join("incorrect-next-dispatch").exists(),
            "cancellation dispatched a later bench under no-fail-fast"
        );
        assert!(String::from_utf8_lossy(&stderr).contains("signal mask"));
        assert!(String::from_utf8_lossy(&stderr).contains("target ended (exit status: 0)"));
    } else if behavior == "nonzero" {
        assert_eq!(status.code(), Some(3), "actual target status must survive positive retirement");
    } else {
        assert!(status.success(), "actual fixed run failed");
    }
    let expected =
        format!("ACTUAL_FIXED_RUN_GNU_SUPPLEMENTARY={}\n", if cap == "1" { 0 } else { 1 });
    assert!(
        String::from_utf8_lossy(&stdout).contains(&expected),
        "run target escaped actual fixed CPU ceiling {cap}"
    );
    if behavior == "cancel" {
        assert!(String::from_utf8_lossy(&stdout).contains("ACTUAL_FIXED_RUN_CANCELLED=1"));
    }
    Ok(())
}
