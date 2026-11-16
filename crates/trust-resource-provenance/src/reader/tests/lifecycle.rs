// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;

pub(super) const STARTED: &str = "native-provenance-fixture-running";
pub(super) const HANG: Duration = Duration::from_secs(60);

/// A copied image remains on disk until its child has written execution proof.
/// Failed fixtures also remain available for diagnosis.
pub(super) struct FixtureRoot {
    root: Option<tempfile::TempDir>,
    armed: bool,
    ran: bool,
}

impl FixtureRoot {
    pub(super) fn new(root: tempfile::TempDir) -> Self {
        Self { root: Some(root), armed: false, ran: false }
    }

    pub(super) fn path(&self) -> &Path {
        self.root.as_ref().unwrap().path()
    }

    pub(super) fn arm(&mut self) {
        self.armed = true;
    }

    pub(super) fn ran(&mut self) {
        assert!(self.armed, "copied fixture was not armed");
        self.ran = true;
    }

    pub(super) fn may_remove(&self) -> bool {
        (!self.armed || self.ran) && !std::thread::panicking()
    }
}

impl Drop for FixtureRoot {
    fn drop(&mut self) {
        if !self.may_remove() {
            let path = self.root.take().unwrap().keep();
            eprintln!("retained native provenance fixture: {}", path.display());
            if !std::thread::panicking() {
                panic!("copied native fixture supplied no execution proof");
            }
        }
    }
}

/// Owns only the actual direct child spawned by this fixture.
pub(super) struct OwnedFixtureChild(std::process::Child);

impl OwnedFixtureChild {
    pub(super) fn new(child: std::process::Child) -> Self {
        Self(child)
    }
}

impl std::ops::Deref for OwnedFixtureChild {
    type Target = std::process::Child;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::ops::DerefMut for OwnedFixtureChild {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Drop for OwnedFixtureChild {
    fn drop(&mut self) {
        if let Ok(None) = self.0.try_wait() {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
}

pub(super) fn bounded_child(
    mut child: OwnedFixtureChild,
    deadline: Instant,
) -> std::process::Output {
    let out = child.stdout.take().unwrap();
    let err = child.stderr.take().unwrap();
    let read = |stream: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            stream.take(1024 * 1024 + 1).read_to_end(&mut bytes).unwrap();
            bytes
        })
    };
    let stdout = read(Box::new(out));
    let stderr = read(Box::new(err));
    let mut timed_out = false;
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if Instant::now() >= deadline {
            timed_out = true;
            child.kill().unwrap();
            break child.wait().unwrap();
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let output = std::process::Output {
        status,
        stdout: stdout.join().unwrap(),
        stderr: stderr.join().unwrap(),
    };
    assert!(!timed_out, "owned native fixture hang detector expired: {output:?}");
    assert!(output.stdout.len() <= 1024 * 1024 && output.stderr.len() <= 1024 * 1024, "{output:?}");
    output
}

pub(super) fn prove_child_started(child: &mut OwnedFixtureChild) -> std::thread::JoinHandle<()> {
    use std::io::BufRead as _;
    let out = child.stdout.take().unwrap();
    let (sent, received) = std::sync::mpsc::sync_channel(1);
    let reader = std::thread::spawn(move || {
        let mut sent = Some(sent);
        for line in std::io::BufReader::new(out).lines() {
            let line = line.unwrap();
            if line.ends_with(STARTED)
                && let Some(sent) = sent.take()
            {
                sent.send(()).unwrap();
            }
        }
    });
    if let Err(error) = received.recv_timeout(HANG) {
        let _ = child.kill();
        let _ = child.wait();
        reader.join().unwrap();
        panic!("owned native fixture did not prove execution: {error}");
    }
    reader
}
