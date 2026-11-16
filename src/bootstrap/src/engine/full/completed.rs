//! Trust: completed library I/O retains the actual original Full owner. This
//! is ordinary command DATA, never a Child, member retirement or CPU credit.
use std::io::{self, Cursor, Read};
use std::process::{ExitStatus, Output};
use std::sync::Arc;

use crate::engine::OriginalBootstrapCompilation;

pub(crate) struct CompletedCommand {
    owner: Arc<OriginalBootstrapCompilation>,
    output: Output,
}

impl CompletedCommand {
    // Only the actual checked command dispatch in the parent module calls
    // this; neither a path, an Output nor a saved observation is a constructor.
    pub(super) fn new(owner: Arc<OriginalBootstrapCompilation>, output: Output) -> Self {
        Self { owner, output }
    }

    pub(super) fn into_output(self) -> Output {
        self.output
    }

    pub(crate) fn take_stdout(&mut self) -> CompletedReader {
        let bytes = std::mem::take(&mut self.output.stdout);
        self.reader(bytes)
    }

    pub(crate) fn take_stderr(&mut self) -> CompletedReader {
        let bytes = std::mem::take(&mut self.output.stderr);
        self.reader(bytes)
    }

    fn reader(&self, bytes: Vec<u8>) -> CompletedReader {
        CompletedReader { _owner: Arc::clone(&self.owner), bytes: Cursor::new(bytes) }
    }

    pub(crate) fn wait(self) -> io::Result<ExitStatus> {
        self.owner.check_current()?;
        Ok(self.output.status)
    }
}

/// The immutable bytes cannot be mistaken for a live process pipe. A reader
/// taken out of StreamingCommand still retains the SAME source/output owner.
pub(crate) struct CompletedReader {
    _owner: Arc<OriginalBootstrapCompilation>,
    bytes: Cursor<Vec<u8>>,
}

impl Read for CompletedReader {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        // The checked issuer already completed the command, including its
        // actual queued/native work and source postcheck. These immutable
        // bytes issue no execution/artifact/retirement authority. Keep the
        // original guards alive, then validate that SAME owner in wait();
        // do not repeat Host RPCs for each memory-buffer read.
        self.bytes.read(bytes)
    }
}
