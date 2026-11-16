use super::*;

#[test]
fn captures_both_large_streams_and_exact_failure_status() {
    let mut process = ProcessBuilder::new("/bin/sh");
    process.args(&[
        "-c",
        "i=0; while [ $i -lt 4096 ]; do printf a; printf b >&2; i=$((i+1)); done; exit 7",
    ]);
    let output = process.output_owned().unwrap();
    assert_eq!(output.status.code(), Some(7));
    assert_eq!(output.stdout, vec![b'a'; 4096]);
    assert_eq!(output.stderr, vec![b'b'; 4096]);
}

#[test]
fn stdin_error_reaps_the_real_still_running_child() {
    let directory = tempfile::tempdir().unwrap();
    let pidfile = directory.path().join("pid");
    let mut process = ProcessBuilder::new("/bin/sh");
    process
        .args(&[
            "-c",
            "printf '%s' \"$$\" > \"$1\"; exec 0<&-; exec /bin/sleep 30",
            "sh",
        ])
        .arg(&pidfile);
    process.stdin(vec![b'x'; 1 << 20]);
    assert!(process.output_owned().is_err());
    let pid: libc::pid_t = std::fs::read_to_string(pidfile).unwrap().parse().unwrap();
    let mut status = 0;
    // SAFETY: this scalar PID names the child the tested API already reaped.
    assert_eq!(
        unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) },
        -1
    );
    assert_eq!(
        io::Error::last_os_error().raw_os_error(),
        Some(libc::ECHILD)
    );
}

#[test]
fn unwind_reaps_before_the_retained_child_owner_drops() {
    let (send, receive) = std::sync::mpsc::channel();
    let thread = std::thread::spawn(move || {
        let child = Command::new("/bin/sleep").arg("30").spawn().unwrap();
        send.send(child.id()).unwrap();
        let _running = Running(child);
        panic!("exercise owner unwind");
    });
    let pid = receive.recv().unwrap() as libc::pid_t;
    assert!(thread.join().is_err());
    let mut status = 0;
    // SAFETY: observe only this already reaped child and our scalar output.
    assert_eq!(
        unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) },
        -1
    );
    assert_eq!(
        io::Error::last_os_error().raw_os_error(),
        Some(libc::ECHILD)
    );
}

// Trust (RL-64): the query's cause names what was refused and where.
#[test]
fn a_refused_capture_file_names_its_folder() {
    let directory = tempfile::tempdir().unwrap();
    let file = directory.path().join("not-a-folder");
    std::fs::write(&file, b"").unwrap();
    let error = capture_file_in(&file).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::NotADirectory);
    assert_eq!(
        error.to_string(),
        format!(
            "could not create an output capture file in {}: {}",
            file.display(),
            io::Error::from_raw_os_error(libc::ENOTDIR)
        )
    );
}
