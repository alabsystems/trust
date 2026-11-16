//! Live original-Root input work. Frames are binding/observation DATA. Only an
//! actual pinned client exchange and the owning native operation can close it.
use std::io;

use super::{Mode, Request};
use crate::bootstrap_graph::{OutputAttachment, SourceAttachment, absolute};
use crate::wire::{Encoder, header, invalid};
use crate::{CommandSpec, MetadataFile, MetadataPrepared};

pub const PURPOSE: &str = "native-bootstrap-dependency-work-v1";
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Action {
    Inputs,
    Checkpoint(u32),
    Close,
}
#[derive(Clone, PartialEq, Eq)]
pub struct WorkRequest {
    pub attempt: Request,
    pub action: Action,
}
impl WorkRequest {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.attempt.validate()?;
        let mut e = Encoder::new(152);
        e.number(1);
        e.frame_bytes(&self.attempt.encode()?)?;
        match self.action {
            Action::Inputs => e.number(0),
            Action::Checkpoint(index) => {
                e.number(1);
                e.number(index.into());
            }
            Action::Close => e.number(2),
        }
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 152)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let attempt = Request::decode(&d.frame_bytes()?)?;
        let action = match d.number()? {
            0 => Action::Inputs,
            1 => Action::Checkpoint(d.narrow()?),
            2 => Action::Close,
            _ => return Err(invalid()),
        };
        d.done()?;
        Ok(Self { attempt, action })
    }
    pub fn hello(&self) -> io::Result<Vec<u8>> {
        self.attempt.validate()?;
        self.attempt.key.graph.hello(PURPOSE)
    }
}

/// Observation of the actual complete closed native compiler request. This is
/// DATA inside the live pinned input owner, never a reusable completion issuer.
#[derive(Clone, PartialEq, Eq)]
pub struct RetainedCompilerQuery {
    pub request: crate::bootstrap_graph::query::Request,
    pub prepared: MetadataPrepared,
    pub command: CommandSpec,
    pub stdin: QueryStdin,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum QueryStdin {
    Null,
}
impl RetainedCompilerQuery {
    pub(in crate::bootstrap_graph) fn write(&self, e: &mut Encoder) -> io::Result<()> {
        self.request.validate_prepared(&self.prepared)?;
        if self.request.tool != crate::bootstrap_graph::query::Tool::Compiler
            || self.command.program != self.request.program.path
            || self.command.args != self.request.arguments
            || self.command.cwd != self.request.cwd
            || self.command.arg0.is_some()
            || self.command.environment.len() > 64
            || self.stdout.len() > 65536
            || self.stderr.len() > 65536
        {
            return Err(invalid());
        }
        let mut seen = std::collections::BTreeSet::new();
        for (key, value) in &self.command.environment {
            if key.is_empty()
                || key.contains(&0)
                || key.contains(&b'=')
                || value.contains(&0)
                || !seen.insert(key)
            {
                return Err(invalid());
            }
        }
        if self.request.environment.iter().any(|item| !self.command.environment.contains(item)) {
            return Err(invalid());
        }
        e.frame_bytes(&self.request.encode()?)?;
        e.frame_bytes(&self.prepared.encode()?)?;
        e.bytes(&self.command.program)?;
        e.number(0);
        e.number(self.command.args.len() as u64);
        for arg in &self.command.args {
            e.bytes(arg)?;
        }
        e.bytes(&self.command.cwd)?;
        e.number(self.command.environment.len() as u64);
        for (key, value) in &self.command.environment {
            e.bytes(key)?;
            e.bytes(value)?;
        }
        e.number(0);
        e.bytes(&self.stdout)?;
        e.bytes(&self.stderr)
    }
    pub(in crate::bootstrap_graph) fn read(d: &mut crate::wire::Decoder<'_>) -> io::Result<Self> {
        let request = crate::bootstrap_graph::query::Request::decode(&d.frame_bytes()?)?;
        let prepared = MetadataPrepared::decode(
            &d.frame_bytes()?,
            request.key.graph.query.binding.root_attempt,
            request.key.operation,
        )?;
        let program = d.bytes()?;
        if d.number()? != 0 {
            return Err(invalid());
        }
        let mut args = Vec::new();
        for _ in 0..d.count(4)? {
            args.push(d.bytes()?);
        }
        let cwd = d.bytes()?;
        let mut environment = Vec::new();
        for _ in 0..d.count(64)? {
            environment.push((d.bytes()?, d.bytes()?));
        }
        if d.number()? != 0 {
            return Err(invalid());
        }
        let value = Self {
            request,
            prepared,
            command: CommandSpec { program, arg0: None, args, cwd, environment },
            stdin: QueryStdin::Null,
            stdout: d.bytes()?,
            stderr: d.bytes()?,
        };
        value.write(&mut Encoder::new(0))?;
        Ok(value)
    }
}

/// Paths and actual captured compiler output are DATA selected by the native
/// original owner. They never instantiate SDK, source, cache or CPU custody.
#[derive(Clone, PartialEq, Eq)]
pub struct InputData {
    pub attempt: Request,
    pub source: Vec<u8>,
    pub cargo_home: Vec<u8>,
    pub seed_root: Vec<u8>,
    pub compiler: MetadataFile,
    pub compiler_queries: Vec<RetainedCompilerQuery>,
    pub compiler_verbose: Vec<u8>,
    pub sysroot: Vec<u8>,
    pub target_libdir: Vec<u8>,
    pub manifests: Vec<Vec<u8>>,
    pub source_inputs_sha256: [u8; 32],
}
impl InputData {
    pub fn validate(&self) -> io::Result<()> {
        self.attempt.validate()?;
        if !absolute(&self.source)
            || !absolute(&self.cargo_home)
            || !absolute(&self.seed_root)
            || self.manifests.is_empty()
            || self.manifests.len() > 1024
            || self.compiler_verbose.is_empty()
            || self.compiler_verbose.len() > 65536
            || self.sysroot.len() > 4096
            || self.target_libdir.len() > 4096
        {
            return Err(invalid());
        }
        self.compiler.validate(&self.seed_root)?;
        if self.compiler_queries.len() != 2 {
            return Err(invalid());
        }
        let mut seen = [false; 2];
        for issued in &self.compiler_queries {
            issued.write(&mut Encoder::new(0))?;
            let index = if issued.request.arguments == [b"-vV".to_vec()] {
                0
            } else if issued.request.arguments == [b"--print=sysroot".to_vec()] {
                1
            } else {
                return Err(invalid());
            };
            if (index == 0 && issued.stdout != self.compiler_verbose)
                || (index == 1 && issued.stdout != self.sysroot)
                || std::mem::replace(&mut seen[index], true)
                || issued.request.key.graph != self.attempt.key.graph
                || issued.request.key.sequence <= self.attempt.key.sequence
                || issued.request.key.operation == self.attempt.key.operation
                || issued.request.program != self.compiler
                || issued.request.cwd != self.source
                || issued.request.sdk_root != self.seed_root
                || !issued
                    .request
                    .environment
                    .contains(&(b"CARGO_HOME".to_vec(), self.cargo_home.clone()))
            {
                return Err(invalid());
            }
        }
        if self.compiler_queries[0].request.gnu != self.compiler_queries[1].request.gnu {
            return Err(invalid());
        }
        let mut expected = self.seed_root.clone();
        expected.extend(b"/bin/trustc");
        if self.compiler.path != expected {
            return Err(invalid());
        }
        let mut previous: Option<&[u8]> = None;
        for path in &self.manifests {
            if path.is_empty()
                || path.len() > 4096
                || path[0] == b'/'
                || path.contains(&0)
                || !path.ends_with(b"Cargo.toml")
                || path.split(|c| *c == b'/').any(|c| c.is_empty() || c == b"." || c == b"..")
                || previous.is_some_and(|old| old >= path.as_slice())
            {
                return Err(invalid());
            }
            previous = Some(path);
        }
        Ok(())
    }
    pub fn total(&self) -> io::Result<u32> {
        self.validate()?;
        u32::try_from(self.manifests.len() * if self.attempt.mode == Mode::Prepare { 2 } else { 1 })
            .map_err(|_| invalid())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(153);
        e.number(2);
        e.frame_bytes(&self.attempt.encode()?)?;
        for value in [&self.source, &self.cargo_home, &self.seed_root] {
            e.bytes(value)?;
        }
        self.compiler.encode(&mut e)?;
        e.number(self.compiler_queries.len() as u64);
        for issued in &self.compiler_queries {
            issued.write(&mut e)?;
        }
        for value in [&self.compiler_verbose, &self.sysroot, &self.target_libdir] {
            e.bytes(value)?;
        }
        e.number(self.manifests.len() as u64);
        for value in &self.manifests {
            e.bytes(value)?;
        }
        e.0.extend(self.source_inputs_sha256);
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 153)?;
        if d.number()? != 2 {
            return Err(invalid());
        }
        let attempt = Request::decode(&d.frame_bytes()?)?;
        let source = d.bytes()?;
        let cargo_home = d.bytes()?;
        let seed_root = d.bytes()?;
        let compiler = MetadataFile::decode(&mut d)?;
        let mut compiler_queries = Vec::new();
        for _ in 0..d.count(2)? {
            compiler_queries.push(RetainedCompilerQuery::read(&mut d)?);
        }
        let compiler_verbose = d.bytes()?;
        let sysroot = d.bytes()?;
        let target_libdir = d.bytes()?;
        let mut manifests = Vec::new();
        for _ in 0..d.count(1024)? {
            manifests.push(d.bytes()?);
        }
        let source_inputs_sha256 = d.array()?;
        d.done()?;
        let value = Self {
            attempt,
            source,
            cargo_home,
            seed_root,
            compiler,
            compiler_queries,
            compiler_verbose,
            sysroot,
            target_libdir,
            manifests,
            source_inputs_sha256,
        };
        value.validate()?;
        Ok(value)
    }
}
#[derive(Clone, PartialEq, Eq)]
pub enum WorkReply {
    Inputs(Box<InputData>),
    Checked { attempt: Request, finished: u32 },
    Closed { attempt: Request, source: Box<SourceAttachment>, output: OutputAttachment },
}
impl WorkReply {
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        let mut e = Encoder::new(154);
        e.number(1);
        match self {
            Self::Inputs(data) => {
                e.number(0);
                e.frame_bytes(&data.encode()?)?;
            }
            Self::Checked { attempt, finished } => {
                e.number(1);
                e.frame_bytes(&attempt.encode()?)?;
                e.number((*finished).into());
            }
            Self::Closed { attempt, source, output } => {
                if attempt.key.graph != source.key || attempt.key.graph != output.key {
                    return Err(invalid());
                }
                e.number(2);
                e.frame_bytes(&attempt.encode()?)?;
                e.frame_bytes(&source.encode()?)?;
                e.frame_bytes(&output.encode()?)?;
            }
        };
        e.finish()
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        let mut d = header(bytes, 154)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let value = match d.number()? {
            0 => Self::Inputs(Box::new(InputData::decode(&d.frame_bytes()?)?)),
            1 => Self::Checked {
                attempt: Request::decode(&d.frame_bytes()?)?,
                finished: d.narrow()?,
            },
            2 => Self::Closed {
                attempt: Request::decode(&d.frame_bytes()?)?,
                source: Box::new(SourceAttachment::decode(&d.frame_bytes()?)?),
                output: OutputAttachment::decode(&d.frame_bytes()?)?,
            },
            _ => return Err(invalid()),
        };
        d.done()?;
        value.encode()?;
        Ok(value)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    pub(crate) fn inputs() -> InputData {
        let attempt = super::super::tests::request();
        let mut compiler = crate::bootstrap_graph::query::tests::request();
        compiler.key.graph = attempt.key.graph.clone();
        compiler.key.operation = [6; 16];
        compiler.key.sequence = 2;
        compiler.sdk_root = b"/private/seed".to_vec();
        compiler.program.path = b"/private/seed/bin/trustc".to_vec();
        compiler.environment.iter_mut().for_each(|(key, value)| match key.as_slice() {
            b"CARGO" => *value = b"/private/seed/bin/targo".to_vec(),
            b"RUSTC" => *value = b"/private/seed/bin/trustc".to_vec(),
            b"CARGO_HOME" => *value = b"/original/cargo-home".to_vec(),
            _ => {}
        });
        compiler.arguments = vec![b"-vV".to_vec()];
        let first = RetainedCompilerQuery {
            prepared: crate::bootstrap_graph::query::tests::prepared(&compiler),
            command: CommandSpec {
                program: compiler.program.path.clone(),
                arg0: None,
                args: compiler.arguments.clone(),
                environment: compiler.environment.clone(),
                cwd: compiler.cwd.clone(),
            },
            request: compiler.clone(),
            stdin: QueryStdin::Null,
            stdout: b"trustc original\ncommit-hash: original\n".to_vec(),
            stderr: b"captured diagnostic DATA".to_vec(),
        };
        compiler.arguments = vec![b"--print=sysroot".to_vec()];
        compiler.key.operation = [7; 16];
        compiler.key.sequence = 7;
        let second = RetainedCompilerQuery {
            prepared: crate::bootstrap_graph::query::tests::prepared(&compiler),
            command: CommandSpec {
                program: compiler.program.path.clone(),
                arg0: None,
                args: compiler.arguments.clone(),
                environment: compiler.environment.clone(),
                cwd: compiler.cwd.clone(),
            },
            request: compiler.clone(),
            stdin: QueryStdin::Null,
            stdout: b"/private/seed\n".to_vec(),
            stderr: vec![],
        };
        InputData {
            compiler_queries: vec![first, second],
            attempt: super::super::tests::request(),
            source: b"/source".to_vec(),
            cargo_home: b"/original/cargo-home".to_vec(),
            seed_root: b"/private/seed".to_vec(),
            compiler: compiler.program.clone(),
            compiler_verbose: b"trustc original\ncommit-hash: original\n".to_vec(),
            sysroot: b"/private/seed\n".to_vec(),
            target_libdir: b"/private/seed/lib\n".to_vec(),
            manifests: vec![b"Cargo.toml".to_vec(), b"library/Cargo.toml".to_vec()],
            source_inputs_sha256: [9; 32],
        }
    }
    #[test]
    fn full_live_inputs_roundtrip_and_keep_original_attempt_and_closed_grammar() {
        let data = inputs();
        assert!(InputData::decode(&data.encode().unwrap()).unwrap() == data);
        for action in [Action::Inputs, Action::Checkpoint(1), Action::Close] {
            let request = WorkRequest { attempt: data.attempt.clone(), action };
            assert!(WorkRequest::decode(&request.encode().unwrap()).unwrap() == request);
            let mut trailing = request.encode().unwrap();
            trailing.push(0);
            assert!(WorkRequest::decode(&trailing).is_err());
        }
        assert_eq!(data.total().unwrap(), 2);
        let mut prepare = data;
        prepare.attempt.mode = Mode::Prepare;
        assert_eq!(prepare.total().unwrap(), 4);
    }
    #[test]
    fn retained_compiler_projection_requires_every_original_query_bookend() {
        let original = inputs();
        original.validate().unwrap();
        let mut changed = original.clone();
        changed.compiler_queries[0].command.cwd = b"/other".to_vec();
        assert!(changed.encode().is_err());
        let mut changed = original.clone();
        changed.compiler_queries[0].command.arg0 = Some(b"other".to_vec());
        assert!(changed.encode().is_err());
        let mut changed = original.clone();
        changed.compiler_queries[0].command.environment.retain(|(key, _)| key != b"CARGO_HOME");
        assert!(changed.encode().is_err());
        let mut changed = original.clone();
        changed.compiler_queries[0].command.args =
            vec![b"--version".to_vec(), b"--verbose".to_vec()];
        assert!(changed.encode().is_err());
        let mut changed = original.clone();
        changed.compiler_queries[0].prepared.root = b"/other-sdk".to_vec();
        assert!(changed.encode().is_err());
        let mut changed = original.clone();
        changed.compiler_queries[1].request.gnu = crate::bootstrap_graph::GnuIdentity::NamedFifo {
            path: b"/other/credits".to_vec(),
            backing: crate::FileIdentity { device: 1, inode: 99 },
        };
        assert!(changed.encode().is_err());
        let mut changed = original.clone();
        changed.compiler_queries[0].stdout.push(0);
        assert!(changed.encode().is_err());
        let mut changed = original;
        changed.compiler_queries.clear();
        assert!(changed.encode().is_err());
    }

    #[test]
    fn recipe_traversal_duplicates_reordering_and_replacement_compiler_refuse() {
        for manifest in [
            b"../Cargo.toml".as_slice(),
            b"/Cargo.toml",
            b"a//Cargo.toml",
            b"a/./Cargo.toml",
            b"a/not-a-manifest",
        ] {
            let mut data = inputs();
            data.manifests = vec![manifest.to_vec()];
            assert!(data.encode().is_err());
        }
        let mut data = inputs();
        data.manifests.push(data.manifests[0].clone());
        assert!(data.encode().is_err());
        let mut data = inputs();
        data.manifests.reverse();
        assert!(data.encode().is_err());
        let mut data = inputs();
        data.compiler.path = b"/control/bin/trustc".to_vec();
        assert!(data.encode().is_err());
        let mut data = inputs();
        data.manifests.clear();
        assert!(data.encode().is_err());
    }
}
