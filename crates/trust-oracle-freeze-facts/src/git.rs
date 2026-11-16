// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufRead, BufReader, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use crate::Error;

const MAX_TREE_BYTES: u64 = 64 * 1024 * 1024;
const MAX_BLOB_BYTES: usize = 64 * 1024 * 1024;

fn command(repo: &Path) -> Command {
    let mut command = Command::new("git");
    command.arg("-C").arg(repo);
    command
}

struct Owned(Option<Child>);

impl Owned {
    fn wait(&mut self) -> Result<bool, Error> {
        Ok(self.wait_status()?.success())
    }

    fn wait_status(&mut self) -> Result<std::process::ExitStatus, Error> {
        let status = self.0.as_mut().expect("owned child").wait()?;
        self.0 = None;
        Ok(status)
    }
}

impl Drop for Owned {
    fn drop(&mut self) {
        if let Some(child) = &mut self.0 {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

fn output(mut command: Command) -> Result<Option<Vec<u8>>, Error> {
    let mut child =
        command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::null()).spawn()?;
    let mut stdout = child.stdout.take().expect("piped Git output");
    let mut owned = Owned(Some(child));
    let mut bytes = Vec::new();
    (&mut stdout).take(MAX_TREE_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_TREE_BYTES {
        return Err(Error::Unsupported("Git observation exceeds byte budget".into()));
    }
    Ok(owned.wait()?.then_some(bytes))
}

fn hexadecimal(value: &str) -> bool {
    matches!(value.len(), 40 | 64)
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub(crate) fn require_supported(repo: &Path, commit: &str) -> Result<(), Error> {
    for name in [
        "GIT_NAMESPACE",
        "GIT_REPLACE_REF_BASE",
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_INDEX_FILE",
        "GIT_ICASE_PATHSPECS",
        "GIT_LITERAL_PATHSPECS",
        "GIT_GLOB_PATHSPECS",
        "GIT_NOGLOB_PATHSPECS",
    ] {
        if std::env::var_os(name).is_some() {
            return Err(Error::Unsupported(format!("explicit {name} uses the original reader")));
        }
    }
    if !hexadecimal(commit) {
        return Err(Error::Unavailable("commit must be one resolved full object ID".into()));
    }
    let mut peel = command(repo);
    peel.args(["rev-parse", "--verify", "--quiet", &format!("{commit}^{{commit}}")]);
    let Some(peeled) = output(peel)? else {
        return Err(Error::Unavailable("cannot read committed citation subject".into()));
    };
    if peeled != format!("{commit}\n").as_bytes() {
        return Err(Error::Unavailable("citation subject differs from resolved commit".into()));
    }
    let mut replacements = command(repo);
    replacements.args(["for-each-ref", "--format=%(refname)", "refs/replace/"]);
    let Some(replacements) = output(replacements)? else {
        return Err(Error::Unavailable("cannot observe replacement namespace".into()));
    };
    if !replacements.is_empty() {
        return Err(Error::Unsupported("replacement refs use the original reader".into()));
    }
    // A batch reader must not silently start a promisor fetch and acquire a
    // network subprocess. The old reader remains responsible for that profile.
    let child = command(repo)
        .args([
            "config",
            "--name-only",
            "--get-regexp",
            "^extensions[.]partialclone$|^remote[.].*[.]promisor$",
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()?;
    match Owned(Some(child)).wait_status()?.code() {
        Some(1) => {}
        Some(0) => {
            return Err(Error::Unsupported(
                "promisor object stores use the original reader".into(),
            ));
        }
        _ => return Err(Error::Unavailable("cannot classify the Git object-store profile".into())),
    }
    let mut alternate_path = command(repo);
    alternate_path.args(["rev-parse", "--git-path", "objects/info/alternates"]);
    let Some(alternate_path) = output(alternate_path)? else {
        return Err(Error::Unavailable("cannot locate the object-store profile".into()));
    };
    let alternate_path = std::str::from_utf8(&alternate_path)
        .map_err(|_| {
            Error::Unsupported("non-UTF8 object-store path uses the original reader".into())
        })?
        .strip_suffix('\n')
        .ok_or_else(|| Error::Unavailable("invalid object-store path".into()))?;
    let alternate_path = repo.join(alternate_path);
    match std::fs::symlink_metadata(alternate_path) {
        Ok(_) => {
            return Err(Error::Unsupported(
                "alternate object stores use the original reader".into(),
            ));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(_) => {
            return Err(Error::Unavailable("cannot classify alternate object storage".into()));
        }
    }
    Ok(())
}

#[derive(Clone, Debug)]
pub(crate) enum Entry {
    Blob(String),
    NotFile,
    GitError,
}

fn parse_entries(bytes: &[u8]) -> Result<BTreeMap<String, Entry>, Error> {
    let mut entries = BTreeMap::new();
    for row in bytes.split(|byte| *byte == 0).filter(|row| !row.is_empty()) {
        let Some(tab) = row.iter().position(|byte| *byte == b'\t') else {
            return Err(Error::Unavailable("invalid ls-tree record".into()));
        };
        let metadata = std::str::from_utf8(&row[..tab])
            .map_err(|_| Error::Unavailable("invalid tree metadata".into()))?;
        let fields = metadata.split_ascii_whitespace().collect::<Vec<_>>();
        if fields.len() != 3 || !hexadecimal(fields[2]) {
            return Err(Error::Unavailable("invalid tree object identity".into()));
        }
        // Only request paths use the citation's ASCII grammar. Unrelated tree
        // names (including newline-bearing names) confer no lookup authority.
        let Ok(path) = std::str::from_utf8(&row[tab + 1..]) else { continue };
        entries.insert(
            path.to_owned(),
            if fields[1] == "blob" { Entry::Blob(fields[2].into()) } else { Entry::NotFile },
        );
    }
    Ok(entries)
}

pub(crate) fn entries(
    repo: &Path,
    commit: &str,
    paths: &BTreeSet<String>,
) -> Result<BTreeMap<String, Entry>, Error> {
    if paths.is_empty() {
        return Ok(BTreeMap::new());
    }
    let mut batch = command(repo);
    batch.args(["ls-tree", "-r", "-t", "-z", "--full-tree", commit, "--"]).args(paths);
    if let Some(bytes) = output(batch)? {
        return parse_entries(&bytes);
    }
    // A malformed path must not turn every other citation into a Git error.
    // Preserve the old per-path command's failure/absence and exact-name split.
    let mut entries = BTreeMap::new();
    for path in paths {
        let mut single = command(repo);
        single.args(["ls-tree", "-z", "--full-tree", commit, "--", path]);
        let entry = match output(single)? {
            None => Entry::GitError,
            Some(bytes) => {
                let first = bytes.split(|byte| *byte == 0).next().unwrap_or_default();
                let parsed = parse_entries(first)?;
                parsed.get(path).cloned().unwrap_or(Entry::NotFile)
            }
        };
        entries.insert(path.clone(), entry);
    }
    Ok(entries)
}

/// One checked, owned raw Git reader; saved data cannot restore this process.
pub(crate) struct Blobs {
    child: Owned,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
}

impl Blobs {
    pub(crate) fn open(repo: &Path) -> Result<Self, Error> {
        let mut child = command(repo)
            .args(["cat-file", "--batch"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let input = child.stdin.take().expect("piped Git input");
        let output = BufReader::new(child.stdout.take().expect("piped Git output"));
        Ok(Self { child: Owned(Some(child)), input: Some(input), output })
    }

    pub(crate) fn read(&mut self, object: &str) -> Result<Option<Vec<u8>>, Error> {
        writeln!(self.input.as_mut().expect("live Git input"), "{object}")?;
        self.input.as_mut().unwrap().flush()?;
        let mut header = Vec::new();
        (&mut self.output).take(257).read_until(b'\n', &mut header)?;
        if header.len() > 256 || header.last() != Some(&b'\n') {
            return Err(Error::Unavailable("invalid Git batch header".into()));
        }
        let header = std::str::from_utf8(&header)
            .map_err(|_| Error::Unavailable("non-ASCII Git header".into()))?;
        let fields = header.split_ascii_whitespace().collect::<Vec<_>>();
        if fields == [object, "missing"] {
            return Ok(None);
        }
        if fields.len() != 3 || fields[0] != object {
            return Err(Error::Unavailable("Git batch object identity differs".into()));
        }
        let size = fields[2]
            .parse::<usize>()
            .map_err(|_| Error::Unavailable("invalid Git blob size".into()))?;
        if size > MAX_BLOB_BYTES {
            return Err(Error::Unsupported("source blob exceeds parser byte budget".into()));
        }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(size).map_err(|error| Error::Unavailable(error.to_string()))?;
        bytes.resize(size, 0);
        self.output.read_exact(&mut bytes)?;
        let mut newline = [0];
        self.output.read_exact(&mut newline)?;
        if newline != *b"\n" {
            return Err(Error::Unavailable("invalid Git blob framing".into()));
        }
        Ok((fields[1] == "blob").then_some(bytes))
    }

    pub(crate) fn finish(mut self) -> Result<(), Error> {
        drop(self.input.take());
        let mut extra = [0];
        if self.output.read(&mut extra)? != 0 || !self.child.wait()? {
            return Err(Error::Unavailable("Git batch reader did not finish cleanly".into()));
        }
        Ok(())
    }
}
