use super::*;
use std::os::fd::OwnedFd;
use std::process::{ChildStderr, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};
#[test]
fn controlled_reader_drains_final_partial_output_after_owned_target_exit_without_waiting_on_other_writers()
 {
    let (out, out_writer) = std::io::pipe().unwrap();
    let (err, err_writer) = std::io::pipe().unwrap();
    let mut child = Command::new("/usr/bin/printf")
        .arg("partial")
        .stdout(Stdio::from(out_writer.try_clone().unwrap()))
        .stderr(Stdio::from(err_writer.try_clone().unwrap()))
        .spawn()
        .unwrap();
    let mut captured = Vec::new();
    let result = read2_controlled(
        ChildStdout::from(OwnedFd::from(out)),
        ChildStderr::from(OwnedFd::from(err)),
        Some(Instant::now() + Duration::from_secs(2)),
        &mut |is_out, bytes, _| {
            if is_out {
                captured.extend_from_slice(bytes);
            }
            bytes.clear();
            Read2Action::Continue
        },
        &mut || {
            Ok(if child.try_wait()?.is_some() {
                Read2Control::Drain
            } else {
                Read2Control::Continue
            })
        },
    )
    .unwrap();
    // These original writer descriptions still prevent pipe EOF. Only the real
    // owned finite printf process has exited; no target PID is reconstructed.
    drop((out_writer, err_writer));
    assert_eq!(result, Read2Action::Continue);
    assert_eq!(captured, b"partial");
}
