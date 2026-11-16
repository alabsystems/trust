//! Trust: owned dep-info bytes prepared while the type context is still live.
//!
//! This carrier has no session or query-context borrow. The opt-in linker-input
//! producer retains it until successful terminal codegen/link; legacy emission
//! uses the same canonical formatter at its original early point.

use std::borrow::Cow;
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};

use rustc_data_structures::indexmap::IndexMap;
use rustc_session::config::OutFileName;
use rustc_session::tool_inputs::{DEP_INFO_PREFIX, Terminal, UNAVAILABLE};
use rustc_span::SourceFileHash;

pub struct PreparedDepInfo {
    destination: OutFileName,
    output_paths: Vec<PathBuf>,
    files: IndexMap<String, (u64, Option<SourceFileHash>)>,
    envs: Vec<(String, Option<String>)>,
    managed_witness: Option<u64>,
    emit_checksums: bool,
    tool_inputs: Option<Terminal>,
}

impl PreparedDepInfo {
    pub(super) fn new(
        destination: OutFileName,
        output_paths: Vec<PathBuf>,
        files: IndexMap<String, (u64, Option<SourceFileHash>)>,
        mut envs: Vec<(String, Option<String>)>,
        managed_witness: Option<u64>,
        emit_checksums: bool,
    ) -> Self {
        envs.sort_unstable();
        Self {
            destination,
            output_paths,
            files,
            envs,
            managed_witness,
            emit_checksums,
            tool_inputs: None,
        }
    }

    pub(super) fn set_tool_inputs(&mut self, tool_inputs: Option<Terminal>) {
        self.tool_inputs = tool_inputs;
    }

    pub(super) fn destination(&self) -> &Path {
        self.destination.as_path()
    }

    pub(super) fn write(&self) -> io::Result<()> {
        match &self.destination {
            OutFileName::Stdout => self.write_buffered(BufWriter::new(io::stdout())),
            // Trust: preserve buffer allocation before the file is truncated.
            OutFileName::Real(path) => self.write_buffered(fs::File::create_buffered(path)?),
        }
    }

    fn write_buffered<W: Write>(&self, mut file: BufWriter<W>) -> io::Result<()> {
        self.write_body(&mut file)?;
        // Trust: a successful body can still leave unwritten buffered bytes.
        // Surface final I/O failure before the caller notifies an artifact.
        file.flush()
    }

    fn write_body(&self, file: &mut dyn Write) -> io::Result<()> {
        for path in &self.output_paths {
            write!(file, "{}:", path.display())?;
            if self.files.is_empty() {
                write!(file, " ")?;
            } else {
                for dep in self.files.keys() {
                    write!(file, " {dep}")?;
                }
            }
            writeln!(file, "\n")?;
        }

        // Emit a fake target for each input file to the compilation. This
        // prevents `make` from spitting out an error if a file is later
        // deleted. For more info see #28735.
        for path in self.files.keys() {
            writeln!(file, "{path}:")?;
        }

        if let Some(crate_id) = self.managed_witness {
            writeln!(file, "# trust-witness-output-v1:{crate_id:016x}.twit")?;
        }

        if !self.envs.is_empty() {
            writeln!(file)?;
            for (key, value) in &self.envs {
                write!(file, "# env-dep:{key}")?;
                if let Some(value) = value {
                    write!(file, "={value}")?;
                }
                writeln!(file)?;
            }
        }

        if self.emit_checksums {
            self.files
                .iter()
                .filter_map(|(path, (file_len, hash))| hash.map(|hash| (path, file_len, hash)))
                .try_for_each(|(path, file_len, hash)| {
                    writeln!(file, "# checksum:{hash} file_len:{file_len} {path}")
                })?;
        }
        // Trust: terminal data has one shared bounded codec. Absence is not a
        // checksum row, and unavailable observations cannot masquerade as empty.
        if let Some(terminal) = &self.tool_inputs {
            write!(file, "{DEP_INFO_PREFIX}")?;
            match terminal {
                Terminal::Available(bytes) => file.write_all(bytes)?,
                Terminal::Unavailable => file.write_all(UNAVAILABLE.as_bytes())?,
            }
            writeln!(file)?;
        }
        Ok(())
    }
}

pub(super) fn escape_dep_filename<'a>(filename: impl Into<Cow<'a, str>>) -> String {
    // Apparently clang and gcc *only* escape spaces:
    // https://llvm.org/klaus/clang/commit/9d50634cfc268ecc9a7250226dd5ca0e945240d4
    let filename = filename.into();
    if filename.contains(' ') { filename.replace(' ', "\\ ") } else { filename.into_owned() }
}

// Makefile comments only need escaping newlines and `\`.
// The result can be unescaped by anything that can unescape `escape_default` and friends.
pub(super) fn escape_dep_env(value: &str) -> String {
    if !value.bytes().any(|byte| matches!(byte, b'\n' | b'\r' | b'\\')) {
        return value.to_owned();
    }
    let mut escaped = String::with_capacity(value.len());
    for c in value.chars() {
        match c {
            '\n' => escaped.push_str(r"\n"),
            '\r' => escaped.push_str(r"\r"),
            '\\' => escaped.push_str(r"\\"),
            _ => escaped.push(c),
        }
    }
    escaped
}

#[cfg(test)]
mod tests;
