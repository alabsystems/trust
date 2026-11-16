#![cfg(target_os = "macos")]

use cargo_util::{ActionSandbox, ProcessBuilder};
use std::fs;
use std::path::PathBuf;
use std::time::Duration;

#[test]
fn sandbox_child() {
    let Some(root) = std::env::var_os("TARGO_SANDBOX_FIXTURE") else {
        return;
    };
    let root = PathBuf::from(root);
    assert_eq!(fs::read(root.join("input/allowed")).unwrap(), b"declared");
    fs::write(root.join("output/created"), b"written").unwrap();
    assert!(fs::read(root.join("private/secret")).is_err());
    assert!(fs::metadata(root.join("private/secret")).is_err());
    assert!(fs::read_dir(root.join("private")).is_err());
    assert!(fs::write(root.join("private/created"), b"escape").is_err());
    assert!(fs::read(root.join("input/link")).is_err());
    assert!(fs::write(root.join("output/link"), b"overwrite").is_err());
    let address = std::env::var("TARGO_SANDBOX_ADDRESS")
        .unwrap()
        .parse()
        .unwrap();
    assert!(std::net::TcpStream::connect_timeout(&address, Duration::from_secs(1)).is_err());
    let mut bytes = [0_u8; 128];
    let mut length = bytes.len();
    let result = unsafe {
        libc::sysctlbyname(
            c"vm.loadavg".as_ptr(),
            bytes.as_mut_ptr().cast(),
            &mut length,
            std::ptr::null_mut(),
            0,
        )
    };
    assert_ne!(result, 0, "unlisted sysctl reads must be denied");
    let platform = cargo_util::PlatformInputs::capture().unwrap();
    let parent = std::env::var("TARGO_SANDBOX_PLATFORM").unwrap();
    let (image, binding) = parent.split_once(' ').unwrap();
    assert_eq!(
        platform.digest(),
        image,
        "the confined child must observe the platform image captured by its parent"
    );
    assert_eq!(
        platform.binding(),
        binding,
        "the confined child must observe the local binding captured by its parent"
    );
    platform.ensure_current().unwrap();
    assert!(fs::read("/System/Library/CoreServices/Finder.app/Contents/Info.plist").is_err());
}

#[test]
fn kernel_enforces_declared_paths_and_denies_network() {
    let root = tempfile::tempdir().unwrap();
    for dir in ["input", "output", "private"] {
        fs::create_dir(root.path().join(dir)).unwrap();
    }
    fs::write(root.path().join("input/allowed"), b"declared").unwrap();
    fs::write(root.path().join("private/secret"), b"secret").unwrap();
    for link in ["input/link", "output/link"] {
        std::os::unix::fs::symlink(root.path().join("private/secret"), root.path().join(link))
            .unwrap();
    }
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let executable = std::env::current_exe().unwrap();
    let mut sandbox = ActionSandbox::new();
    sandbox.executable(&executable).unwrap();
    sandbox.read_directory(&root.path().join("input")).unwrap();
    sandbox
        .write_directory(&root.path().join("output"))
        .unwrap();
    for path in cargo_util::PLATFORM_READ_DIRECTORIES {
        sandbox.read_directory(std::path::Path::new(path)).unwrap();
    }
    for path in cargo_util::PLATFORM_READ_FILES {
        sandbox.read_file(std::path::Path::new(path)).unwrap();
    }
    let platform = cargo_util::PlatformInputs::capture().unwrap();
    let mut command = ProcessBuilder::new(executable);
    command
        .args(&["--exact", "sandbox_child", "--nocapture"])
        .env("TARGO_SANDBOX_FIXTURE", root.path())
        .env(
            "TARGO_SANDBOX_PLATFORM",
            format!("{} {}", platform.digest(), platform.binding()),
        )
        .env(
            "TARGO_SANDBOX_ADDRESS",
            listener.local_addr().unwrap().to_string(),
        );
    command.action_sandbox(sandbox).unwrap();
    let secret = std::sync::Arc::new(std::os::fd::OwnedFd::from(
        fs::File::open(root.path().join("private/secret")).unwrap(),
    ));
    assert!(command.inherit_fd_for_exec(secret).is_err());
    command.exec_with_output().unwrap();
    assert_eq!(
        fs::read(root.path().join("output/created")).unwrap(),
        b"written"
    );
    assert_eq!(
        fs::read(root.path().join("private/secret")).unwrap(),
        b"secret"
    );
    assert!(!root.path().join("private/created").exists());
    // The argument-file retry must not drop the policy or read a temporary
    // file that was never declared as an action input.
    command
        .retry_with_argfile(true)
        .arg("x".repeat(1024 * 1024));
    let error = command.exec_with_output().unwrap_err();
    assert!(format!("{error:#}").contains("undeclared argument file"));
}
