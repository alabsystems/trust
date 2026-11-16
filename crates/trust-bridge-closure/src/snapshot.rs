//! Export exact producer blobs, without consulting live files or Git filters.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::rc::Rc;

const PREFIX: &str = "lean/trust_ir-semantics/";

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::other(message.into())
}

fn object_id(text: &str) -> bool {
    matches!(text.len(), 40 | 64)
        && text.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn reserved_component(part: &str) -> bool {
    let base = part.split('.').next().unwrap_or(part).to_ascii_uppercase();
    matches!(base.as_str(), "CON" | "PRN" | "AUX" | "NUL")
        || ((base.starts_with("COM") || base.starts_with("LPT"))
            && base.len() == 4
            && matches!(base.as_bytes()[3], b'1'..=b'9'))
}

pub(crate) struct Git {
    repo: PathBuf,
    object_store: bool,
    local_env: Vec<OsString>,
    protected: Vec<PathBuf>,
    blob_streams: Rc<RefCell<BTreeMap<(PathBuf, bool), BlobStream>>>,
}

impl Git {
    pub(crate) fn new(repo: &Path) -> io::Result<Self> {
        let local_env = std::env::vars_os()
            .map(|(key, _)| key)
            .filter(|key| key.as_encoded_bytes().starts_with(b"GIT_"))
            .collect();
        let repo = fs::canonicalize(repo)?;
        if !repo.is_dir() {
            return Err(invalid("snapshot repository must be a directory"));
        }
        let mut git = Self {
            repo,
            object_store: false,
            local_env,
            protected: Vec::new(),
            blob_streams: Rc::default(),
        };
        let git_dir = git.directory(&["rev-parse", "--absolute-git-dir"])?;
        let root = match git.output(&["rev-parse", "--is-bare-repository"])?.as_slice() {
            b"true\n" => git_dir.clone(),
            b"false\n" => git.directory(&["rev-parse", "--show-toplevel"])?,
            _ => return Err(invalid("cannot identify snapshot repository")),
        };
        if root != git.repo {
            return Err(invalid(
                "snapshot repository must name its worktree or bare repository root",
            ));
        }
        git.protected.push(root);
        git.protected.push(git_dir);
        let common = git.directory(&["rev-parse", "--path-format=absolute", "--git-common-dir"])?;
        git.protected.push(common);
        Ok(git)
    }

    /// Read an explicitly selected submodule object store without permitting
    /// Git's upward worktree discovery to select the parent repository.
    pub(crate) fn store(repo: &Path) -> io::Result<Self> {
        let repo = fs::canonicalize(repo)?;
        let local_env = std::env::vars_os()
            .map(|(key, _)| key)
            .filter(|key| key.as_encoded_bytes().starts_with(b"GIT_"))
            .collect();
        let mut git = Self {
            repo,
            object_store: true,
            local_env,
            protected: Vec::new(),
            blob_streams: Rc::default(),
        };
        let actual = git.directory(&["rev-parse", "--absolute-git-dir"])?;
        if actual != git.repo || !actual.join("objects").is_dir() {
            return Err(invalid("submodule object store is not the selected Git directory"));
        }
        git.protected.push(actual);
        Ok(git)
    }

    fn command(&self) -> Command {
        let mut command = Command::new("git");
        command.args(["--no-replace-objects", "--no-optional-locks", "-c", "core.fsmonitor=false"]);
        if self.object_store {
            // Absorbed submodules retain a core.worktree pointing at a
            // possibly absent checkout. Object reads must not chdir there.
            // Apple Git 2.54 still consults core.worktree under --bare.
            // Bind both roots to this existing canonical store; no physical
            // source checkout or ambient working directory is involved.
            command
                .arg("--git-dir")
                .arg(&self.repo)
                .arg("--bare")
                .arg("--work-tree")
                .arg(&self.repo);
        } else {
            command.arg("-C").arg(&self.repo);
        }
        for key in &self.local_env {
            command.env_remove(key);
        }
        // A snapshot reads local immutable objects, never replacement refs or
        // an implicit network fetch from a promisor remote.
        command
            .env("GIT_NO_LAZY_FETCH", "1")
            .env("GIT_GRAFT_FILE", if cfg!(windows) { "NUL" } else { "/dev/null" })
            .env("GIT_ALLOW_PROTOCOL", "")
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", if cfg!(windows) { "NUL" } else { "/dev/null" })
            .env("GIT_TERMINAL_PROMPT", "0")
            .stdin(Stdio::null());
        command
    }

    pub(crate) fn output(&self, args: &[&str]) -> io::Result<Vec<u8>> {
        let output = self.command().args(args).output()?;
        if !output.status.success() {
            return Err(invalid(format!(
                "git {} failed: {}",
                args[0],
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
        Ok(output.stdout)
    }

    /// Share only live byte-reader processes after the child's root checks.
    /// No object bytes, query results or mutable source state are cached.
    pub(crate) fn share_blob_reads(mut self, parent: &Self) -> Self {
        self.blob_streams = Rc::clone(&parent.blob_streams);
        self
    }

    /// Read every requested full OID, including duplicates, through the same
    /// hardened Git process for this canonical root/store mode. The caller
    /// must finish the streams before returning a successful source judgment.
    pub(crate) fn full_oid_blob(&self, oid: &str) -> io::Result<Vec<u8>> {
        if !object_id(oid) {
            return Err(invalid("blob stream requires a full lowercase object ID"));
        }
        let key = (self.repo.clone(), self.object_store);
        let mut streams = self.blob_streams.borrow_mut();
        if !streams.contains_key(&key) {
            let stream = BlobStream::spawn(self.command().args(["cat-file", "--batch"]))?;
            streams.insert(key.clone(), stream);
        }
        streams.get_mut(&key).unwrap().read(oid)
    }

    /// Closing stdin, checking the final framing and waiting for every child
    /// are part of the judgment, not best-effort cleanup after success.
    pub(crate) fn finish_blob_reads(&self) -> io::Result<()> {
        let streams = std::mem::take(&mut *self.blob_streams.borrow_mut());
        let mut result = Ok(());
        for (_, stream) in streams {
            if let Err(error) = stream.finish() {
                if result.is_ok() {
                    result = Err(error);
                }
            }
        }
        result
    }

    pub(crate) fn directory(&self, args: &[&str]) -> io::Result<PathBuf> {
        let output = self.output(args)?;
        let path =
            output.strip_suffix(b"\n").ok_or_else(|| invalid("invalid Git directory response"))?;
        #[cfg(unix)]
        let path = {
            use std::os::unix::ffi::OsStringExt;
            PathBuf::from(OsString::from_vec(path.to_vec()))
        };
        #[cfg(not(unix))]
        let path = PathBuf::from(
            std::str::from_utf8(path).map_err(|_| invalid("invalid Git directory encoding"))?,
        );
        fs::canonicalize(path)
    }
}

struct BlobStream {
    child: Child,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
    failed: bool,
    reaped: bool,
}

impl BlobStream {
    fn spawn(command: &mut Command) -> io::Result<Self> {
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let input = child.stdin.take().expect("piped Git stdin");
        let output = BufReader::new(child.stdout.take().expect("piped Git stdout"));
        Ok(Self { child, input: Some(input), output, failed: false, reaped: false })
    }

    fn read(&mut self, oid: &str) -> io::Result<Vec<u8>> {
        let result = self.read_inner(oid);
        if result.is_err() {
            self.failed = true;
        }
        result
    }

    fn read_inner(&mut self, oid: &str) -> io::Result<Vec<u8>> {
        if self.failed || !object_id(oid) {
            return Err(invalid("invalid or failed Git blob stream request"));
        }
        let input = self.input.as_mut().ok_or_else(|| invalid("closed Git blob stream"))?;
        // Only hexadecimal OIDs enter the line protocol. One outstanding
        // request avoids a full stdin/stdout pipe deadlock.
        writeln!(input, "{oid}")?;
        input.flush()?;
        let mut header = Vec::new();
        self.output.by_ref().take(129).read_until(b'\n', &mut header)?;
        if header.len() > 128 || !header.ends_with(b"\n") {
            return Err(invalid("missing or excessive Git blob header"));
        }
        let header = std::str::from_utf8(&header[..header.len() - 1])
            .map_err(|_| invalid("non-UTF8 Git blob header"))?;
        let fields: Vec<_> = header.split(' ').collect();
        if fields.len() != 3 || fields[0] != oid || fields[1] != "blob" {
            return Err(invalid("Git returned an unexpected blob identity or type"));
        }
        let size = fields[2];
        if size.is_empty()
            || !size.bytes().all(|b| b.is_ascii_digit())
            || (size.len() > 1 && size.starts_with('0'))
        {
            return Err(invalid("invalid Git blob size"));
        }
        let mut remaining: u64 = size.parse().map_err(|_| invalid("excessive Git blob size"))?;
        let mut data = Vec::new();
        let mut block = [0; 64 * 1024];
        while remaining != 0 {
            let count = remaining.min(block.len() as u64) as usize;
            self.output.read_exact(&mut block[..count])?;
            // Do not allocate from an untrusted advertised size up front.
            data.try_reserve(count).map_err(|_| invalid("Git blob exceeds memory bounds"))?;
            data.extend_from_slice(&block[..count]);
            remaining -= count as u64;
        }
        let mut separator = [0];
        self.output.read_exact(&mut separator)?;
        if separator != *b"\n" {
            return Err(invalid("invalid Git blob framing"));
        }
        Ok(data)
    }

    fn finish(mut self) -> io::Result<()> {
        self.input.take();
        if self.failed {
            return Err(invalid("Git blob stream had an unsuccessful request"));
        }
        let mut trailing = [0];
        if self.output.read(&mut trailing)? != 0 {
            return Err(invalid("unexpected trailing Git blob output"));
        }
        let status = self.child.wait()?;
        self.reaped = true;
        if !status.success() {
            return Err(invalid(format!("git cat-file stream failed: {status}")));
        }
        Ok(())
    }
}

impl Drop for BlobStream {
    fn drop(&mut self) {
        if !self.reaped {
            self.input.take();
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

struct Entry {
    path: PathBuf,
    oid: String,
    executable: bool,
}

fn entries(listing: &[u8]) -> io::Result<Vec<Entry>> {
    let listing = listing.strip_suffix(&[0]).ok_or_else(|| invalid("empty producer tree"))?;
    let mut entries = Vec::new();
    let mut names = BTreeMap::new();
    for row in listing.split(|byte| *byte == 0) {
        let row = std::str::from_utf8(row).map_err(|_| invalid("producer paths must be UTF-8"))?;
        let (header, path) = row.split_once('\t').ok_or_else(|| invalid("invalid Git tree row"))?;
        let fields: Vec<_> = header.split_ascii_whitespace().collect();
        if fields.len() != 3 || fields[1] != "blob" || !object_id(fields[2]) {
            return Err(invalid("producer tree contains a non-blob entry"));
        }
        let executable = match fields[0] {
            "100644" => false,
            "100755" => true,
            _ => return Err(invalid("producer tree contains a symlink or unsupported file mode")),
        };
        let relative =
            path.strip_prefix(PREFIX).ok_or_else(|| invalid("path outside producer tree"))?;
        if relative.is_empty()
            || relative.contains(['\\', ':'])
            || relative.split('/').any(|part| {
                part.is_empty()
                    || matches!(part, "." | "..")
                    || part.eq_ignore_ascii_case(".git")
                    || part.ends_with(['.', ' '])
                    || reserved_component(part)
            })
            || relative.split('/').next().is_some_and(|part| part.eq_ignore_ascii_case(".lake"))
        {
            return Err(invalid("unsafe producer path"));
        }
        // Reject portable name collisions before writing, including two directory
        // spellings that a case-insensitive filesystem would merge silently.
        let parts: Vec<_> = relative.split('/').collect();
        for index in 0..parts.len() {
            let path = parts[..=index].join("/");
            let is_file = index + 1 == parts.len();
            if let Some((previous, previous_file)) =
                names.insert(path.to_lowercase(), (path.clone(), is_file))
                && (previous != path || previous_file || is_file)
            {
                return Err(invalid("colliding producer paths"));
            }
        }
        entries.push(Entry { path: PathBuf::from(relative), oid: fields[2].into(), executable });
    }
    if !entries.iter().any(|entry| entry.path == Path::new("lean-toolchain")) {
        return Err(invalid("producer tree has no regular lean-toolchain file"));
    }
    Ok(entries)
}

// Removes only the fresh directory this invocation created, on any failure.
struct Destination<'a> {
    path: &'a Path,
    complete: bool,
}

impl Drop for Destination<'_> {
    fn drop(&mut self) {
        if !self.complete {
            let _ = fs::remove_dir_all(self.path);
        }
    }
}

fn write_blobs(git: &Git, entries: &[Entry], destination: &Path) -> io::Result<()> {
    let mut child = git
        .command()
        .args(["cat-file", "--batch"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()?;
    let result = (|| {
        let mut input = child.stdin.take().ok_or_else(|| invalid("Git stdin unavailable"))?;
        let output = child.stdout.take().ok_or_else(|| invalid("Git stdout unavailable"))?;
        let mut output = BufReader::new(output);
        for entry in entries {
            // One request at a time prevents a full stdin/stdout pipe deadlock.
            writeln!(input, "{}", entry.oid)?;
            input.flush()?;
            let mut header = String::new();
            output.read_line(&mut header)?;
            let fields: Vec<_> = header.split_ascii_whitespace().collect();
            if fields.len() != 3 || fields[0] != entry.oid || fields[1] != "blob" {
                return Err(invalid("Git returned an unexpected blob header"));
            }
            let size: u64 = fields[2].parse().map_err(|_| invalid("invalid Git blob size"))?;
            let path = destination.join(&entry.path);
            let parent = path.parent().ok_or_else(|| invalid("producer file has no parent"))?;
            fs::create_dir_all(parent)?;
            let mut file = File::create_new(&path)?;
            let written = io::copy(&mut output.by_ref().take(size), &mut file)?;
            if written != size {
                return Err(invalid("truncated Git blob"));
            }
            let mut separator = [0];
            output.read_exact(&mut separator)?;
            if separator != *b"\n" {
                return Err(invalid("invalid Git blob framing"));
            }
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                file.set_permissions(fs::Permissions::from_mode(if entry.executable {
                    0o755
                } else {
                    0o644
                }))?;
            }
            #[cfg(not(unix))]
            let _ = entry.executable;
        }
        drop(input);
        let mut trailing = [0];
        if output.read(&mut trailing)? != 0 {
            return Err(invalid("unexpected trailing Git blob output"));
        }
        Ok(())
    })();
    if result.is_err() {
        let _ = child.kill();
        let _ = child.wait();
        return result;
    }
    if !child.wait()?.success() {
        return Err(invalid("git cat-file failed while exporting producer blobs"));
    }
    Ok(())
}

/// Whether `commit` names ITSELF here: Git resolves it, peeled to a commit, to exactly the same
/// full ID. A full-length hex string of the OTHER object format is not an object ID to Git,
/// which then resolves it by NAME (a 64-hex ref in a SHA-1 repository; a 40-hex ref, tag or
/// unique prefix in a SHA-256 one), so the bytes would be chosen by a mutable ref rather than by
/// the ID; `object_id` alone accepts both lengths. Such a name is refused.
fn names_itself(git: &Git, commit: &str) -> io::Result<bool> {
    let peeled = format!("{commit}^{{commit}}");
    let resolved = git.output(&["rev-parse", "--verify", "--end-of-options", &peeled])?;
    Ok(resolved.strip_suffix(b"\n") == Some(commit.as_bytes()))
}

/// Export the fixed producer subtree. Neither HEAD, index nor worktree bytes
/// select its content; attributes, checkout filters and replacement refs do not
/// transform it. The destination must not exist, including as a symlink.
pub fn export(repo: &Path, commit: &str, destination: &Path) -> io::Result<usize> {
    if !object_id(commit) {
        return Err(invalid("snapshot requires a full lowercase Git commit ID"));
    }
    let git = Git::new(repo)?;
    if git.output(&["cat-file", "-t", commit])? != b"commit\n" {
        return Err(invalid("snapshot revision is not a commit object"));
    }
    if !names_itself(&git, commit)? {
        return Err(invalid("snapshot revision is not named by its own full commit ID"));
    }
    let listing = git.output(&["ls-tree", "-r", "-z", "--full-tree", commit, "--", PREFIX])?;
    let entries = entries(&listing)?;
    let parent = destination
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let parent = fs::canonicalize(parent)?;
    let name =
        destination.file_name().ok_or_else(|| invalid("snapshot destination needs a file name"))?;
    let destination = parent.join(name);
    if git.protected.iter().any(|root| destination.starts_with(root))
        || destination
            .components()
            .any(|part| part.as_os_str().as_encoded_bytes().eq_ignore_ascii_case(b".git"))
    {
        return Err(invalid(
            "snapshot destination must be outside the source repository and Git metadata",
        ));
    }
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(&destination)?;
    let mut destination = Destination { path: &destination, complete: false };
    write_blobs(&git, &entries, destination.path)?;
    destination.complete = true;
    Ok(entries.len())
}

/// Read the runtime obligation disclosure from the selected immutable producer.
/// Absence means no disclosure was recorded, never that runtime is certified.
/// This is input data only; it grants no kernel or correspondence authority.
pub fn read_runtime_boundary_input(repo: &Path, commit: &str) -> io::Result<Option<Vec<u8>>> {
    if !object_id(commit) {
        return Err(invalid("runtime boundary requires a full lowercase Git commit ID"));
    }
    let git = Git::new(repo)?;
    if git.output(&["cat-file", "-t", commit])? != b"commit\n" {
        return Err(invalid("runtime boundary revision is not a commit object"));
    }
    if !names_itself(&git, commit)? {
        return Err(invalid("runtime boundary revision is not named by its own full commit ID"));
    }
    let path = format!("{PREFIX}runtime-boundary.json");
    let listing = git.output(&["ls-tree", "-z", "--full-tree", commit, "--", &path])?;
    if listing.is_empty() {
        return Ok(None);
    }
    let row = listing
        .strip_suffix(&[0])
        .and_then(|row| std::str::from_utf8(row).ok())
        .ok_or_else(|| invalid("invalid runtime boundary tree entry"))?;
    let (header, actual) =
        row.split_once('\t').ok_or_else(|| invalid("invalid runtime boundary tree entry"))?;
    let fields: Vec<_> = header.split_whitespace().collect();
    if actual != path
        || fields.len() != 3
        || !matches!(fields[0], "100644" | "100755")
        || fields[1] != "blob"
    {
        return Err(invalid("runtime boundary must be an exact regular producer blob"));
    }
    let bytes = git.full_oid_blob(fields[2]);
    let finished = git.finish_blob_reads();
    let bytes = bytes?;
    finished?;
    Ok(Some(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_boundary_reads_selected_objects_and_distinguishes_absence() {
        let dir = tempfile::tempdir().unwrap();
        assert!(
            Command::new("git")
                .args(["init", "-q"])
                .current_dir(dir.path())
                .status()
                .unwrap()
                .success()
        );
        let git = Git::new(dir.path()).unwrap();
        let leaf = dir.path().join(format!("{PREFIX}runtime-boundary.json"));
        fs::create_dir_all(leaf.parent().unwrap()).unwrap();
        fs::write(&leaf, b"original source ledger\n").unwrap();
        git.output(&["add", "--", &format!("{PREFIX}runtime-boundary.json")]).unwrap();
        git.output(&[
            "-c",
            "user.name=Boundary test",
            "-c",
            "user.email=boundary@example.invalid",
            "-c",
            "commit.gpgSign=false",
            "commit",
            "-qm",
            "source",
        ])
        .unwrap();
        let commit = String::from_utf8(git.output(&["rev-parse", "HEAD"]).unwrap()).unwrap();
        fs::write(&leaf, b"uncommitted substitution\n").unwrap();
        assert_eq!(
            read_runtime_boundary_input(dir.path(), commit.trim()).unwrap(),
            Some(b"original source ledger\n".to_vec())
        );
        fs::remove_file(&leaf).unwrap();
        git.output(&["add", "--", &format!("{PREFIX}runtime-boundary.json")]).unwrap();
        git.output(&[
            "-c",
            "user.name=Boundary test",
            "-c",
            "user.email=boundary@example.invalid",
            "-c",
            "commit.gpgSign=false",
            "commit",
            "-qm",
            "no disclosure",
        ])
        .unwrap();
        let absent = String::from_utf8(git.output(&["rev-parse", "HEAD"]).unwrap()).unwrap();
        assert_eq!(read_runtime_boundary_input(dir.path(), absent.trim()).unwrap(), None);
        assert!(read_runtime_boundary_input(dir.path(), "HEAD").is_err());
        assert!(read_runtime_boundary_input(dir.path(), &"0".repeat(40)).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn runtime_boundary_refuses_a_committed_symlink() {
        let dir = tempfile::tempdir().unwrap();
        assert!(
            Command::new("git")
                .args(["init", "-q"])
                .current_dir(dir.path())
                .status()
                .unwrap()
                .success()
        );
        let git = Git::new(dir.path()).unwrap();
        let leaf = dir.path().join(format!("{PREFIX}runtime-boundary.json"));
        fs::create_dir_all(leaf.parent().unwrap()).unwrap();
        std::os::unix::fs::symlink("outside-ledger", &leaf).unwrap();
        git.output(&["add", "--", &format!("{PREFIX}runtime-boundary.json")]).unwrap();
        git.output(&[
            "-c",
            "user.name=Boundary test",
            "-c",
            "user.email=boundary@example.invalid",
            "-c",
            "commit.gpgSign=false",
            "commit",
            "-qm",
            "link",
        ])
        .unwrap();
        let commit = String::from_utf8(git.output(&["rev-parse", "HEAD"]).unwrap()).unwrap();
        assert!(read_runtime_boundary_input(dir.path(), commit.trim()).is_err());
    }

    #[cfg(unix)]
    mod blob_stream {
        use super::*;

        fn fake(program: &str) -> BlobStream {
            BlobStream::spawn(Command::new("/bin/sh").args(["-c", program])).unwrap()
        }

        #[test]
        fn binary_frames_and_both_full_oid_widths() {
            let mut stream =
                fake("while IFS= read -r oid; do printf '%s blob 3\nA\\000B\n' \"$oid\"; done");
            for oid in ["a".repeat(40), "b".repeat(64)] {
                assert_eq!(stream.read(&oid).unwrap(), b"A\0B");
            }
            stream.finish().unwrap();
        }

        #[test]
        fn duplicate_requests_are_not_cached() {
            // The synthetic peer changes each response, so reusing bytes
            // instead of issuing the second request is observable here.
            let mut stream = fake(
                "n=0; while IFS= read -r oid; do n=$((n+1)); printf '%s blob 1\n%s\n' \"$oid\" \"$n\"; done",
            );
            let oid = "a".repeat(40);
            assert_eq!(stream.read(&oid).unwrap(), b"1");
            assert_eq!(stream.read(&oid).unwrap(), b"2");
            stream.finish().unwrap();
        }

        #[test]
        fn malformed_identity_type_and_size_refuse() {
            let oid = "a".repeat(40);
            for header in [
                format!("{} blob 0", "b".repeat(40)),
                format!("{oid} tree 0"),
                format!("{oid} blob -1"),
                format!("{oid} blob +1"),
                format!("{oid} blob 00"),
                format!("{oid} blob 999999999999999999999999999999999"),
                format!("{oid} blob 0 extra"),
                format!("{oid} missing"),
                "x".repeat(129),
            ] {
                let mut stream = fake(&format!("IFS= read -r oid; printf '%s\\n' '{header}'"));
                assert!(stream.read(&oid).is_err(), "{header}");
                assert!(stream.finish().is_err());
            }
        }

        #[test]
        fn early_eof_and_wrong_size_or_separator_refuse() {
            for response in [
                "",                    // No header.
                "$oid blob 0",         // Unterminated header.
                "$oid blob 4\\nAB",    // Truncated body.
                "$oid blob 1\\nA",     // Missing separator.
                "$oid blob 1\\nAB\\n", // Advertised size is too small.
                "$oid blob 1\\nA!",    // Wrong separator.
            ] {
                let mut stream = fake(&format!("IFS= read -r oid; printf \"{response}\""));
                assert!(stream.read(&"a".repeat(40)).is_err(), "{response}");
                assert!(stream.finish().is_err());
            }
        }

        #[test]
        fn invalid_requests_cannot_inject_protocol_lines() {
            for oid in [
                "HEAD",
                "",
                &"A".repeat(40),
                &"a".repeat(39),
                &format!("{}\n{}", "a".repeat(40), "b".repeat(40)),
                &format!("{} x", "a".repeat(40)),
            ] {
                let mut stream = fake("cat >/dev/null");
                assert!(stream.read(oid).is_err(), "{oid:?}");
                assert!(stream.finish().is_err());
            }
        }

        #[test]
        fn a_failed_request_poison_cannot_be_ignored() {
            let mut stream =
                fake("while IFS= read -r oid; do printf '%s tree 0\n\n' \"$oid\"; done");
            let oid = "a".repeat(40);
            assert!(stream.read(&oid).is_err());
            assert!(stream.read(&oid).is_err());
            assert!(stream.finish().is_err());
        }

        #[test]
        fn successful_response_does_not_hide_child_failure() {
            let mut stream = fake("IFS= read -r oid; printf '%s blob 1\nA\n' \"$oid\"; exit 17");
            assert_eq!(stream.read(&"a".repeat(40)).unwrap(), b"A");
            assert!(stream.finish().is_err());
        }

        #[test]
        fn unrequested_trailing_output_refuses() {
            let mut stream = fake("IFS= read -r oid; printf '%s blob 1\nA\nextra' \"$oid\"");
            assert_eq!(stream.read(&"a".repeat(40)).unwrap(), b"A");
            assert!(stream.finish().is_err());
        }

        #[test]
        fn actual_git_binary_repeated_reads_and_checked_shared_pool() {
            let dir = tempfile::tempdir().unwrap();
            assert!(
                Command::new("git")
                    .args(["init", "-q"])
                    .current_dir(dir.path())
                    .status()
                    .unwrap()
                    .success()
            );
            fs::write(dir.path().join("body"), b"real\0binary\n").unwrap();
            let git = Git::new(dir.path()).unwrap();
            let oid =
                String::from_utf8(git.output(&["hash-object", "-w", "body"]).unwrap()).unwrap();
            let oid = oid.trim();
            let child = Git::new(dir.path()).unwrap().share_blob_reads(&git);
            assert_eq!(git.full_oid_blob(oid).unwrap(), b"real\0binary\n");
            assert_eq!(child.full_oid_blob(oid).unwrap(), b"real\0binary\n");
            assert_eq!(git.blob_streams.borrow().len(), 1);
            git.finish_blob_reads().unwrap();
            assert!(child.blob_streams.borrow().is_empty());
            // Finishing one judgment does not retain a live child or bytes
            // for the next judgment.
            assert_eq!(child.full_oid_blob(oid).unwrap(), b"real\0binary\n");
            child.finish_blob_reads().unwrap();
        }

        #[test]
        fn actual_git_missing_and_nonblob_objects_refuse() {
            let dir = tempfile::tempdir().unwrap();
            assert!(
                Command::new("git")
                    .args(["init", "-q"])
                    .current_dir(dir.path())
                    .status()
                    .unwrap()
                    .success()
            );
            let git = Git::new(dir.path()).unwrap();
            let tree = String::from_utf8(git.output(&["mktree"]).unwrap()).unwrap();
            assert!(git.full_oid_blob(tree.trim()).is_err());
            assert!(git.finish_blob_reads().is_err());
            assert!(git.full_oid_blob(&"0".repeat(40)).is_err());
            assert!(git.finish_blob_reads().is_err());
        }
    }

    fn row(path: &str) -> String {
        format!("100644 blob {}\t{PREFIX}{path}\0", "a".repeat(40))
    }

    #[test]
    fn unsafe_paths_and_name_collisions_refuse() {
        let pin = row("lean-toolchain");
        for path in [
            "../escape",
            "/absolute",
            "a//b",
            "a/./b",
            "a/../b",
            "a\\b",
            "C:drive",
            ".Git/config",
            ".lake/build/lib/stale.olean",
            "trailing.",
            "trailing ",
            "NUL",
            "aux.lean",
            "COM1.txt",
        ] {
            assert!(entries(format!("{pin}{}", row(path)).as_bytes()).is_err(), "{path}");
        }
        for paths in [["A.lean", "a.lean"], ["Case/A.lean", "case/B.lean"], ["node", "node/child"]]
        {
            assert!(
                entries(format!("{pin}{}{}", row(paths[0]), row(paths[1])).as_bytes()).is_err()
            );
        }
    }

    #[test]
    fn malformed_tree_records_refuse() {
        let pin = row("lean-toolchain");
        for listing in [
            Vec::new(),
            pin.trim_end_matches('\0').as_bytes().to_vec(),
            format!("{pin}\0").into_bytes(),
            format!("{pin}100644 blob bad\t{PREFIX}x\0").into_bytes(),
        ] {
            assert!(entries(&listing).is_err());
        }
        let listing = format!("{pin}{}", row("nested/tab\tand\nline.lean"));
        assert_eq!(entries(listing.as_bytes()).unwrap().len(), 2);
    }
}
