//! Trust (DC-18a, `-Ztrust-path-free`): which absolute host path a value would carry
//! into crate metadata.
//!
//! A unit may be shared between checkouts only when the compiler can show that its
//! metadata names no host path. These functions decide that; they only classify. They
//! never rewrite a value; the refusal and its diagnostic are `rustc_metadata`'s, and
//! nothing here runs unless that option is on. Three judgments, each fail-closed:
//!
//! * A source file's name (with the working directory it was resolved against), by
//!   provenance, not shape ([`RealFileName::trust_unrewritten_host_path`]). A path field
//!   counts as rewritten only when the session holds the local form it was made from,
//!   the two differ, and the rewritten path's root (its first component) is not on this
//!   host. Remap scopes are not evidence: `FilePathMapping::to_real_filename` marks a
//!   name as remapped when only its working directory matched a rule, so an absolute
//!   name that matched none still says `RemapPathScopeComponents::all()` (the "does not
//!   match any prefix" case in `source_map/tests.rs`). A name with no local form (one
//!   decoded from another crate's metadata) cannot show which rule rewrote it, so each of
//!   its absolute fields is refused; a rule that maps a prefix to itself, or into another
//!   host path (`/Users=/home`, `/w=/System/Volumes/Data/w`), is refused the same way,
//!   since the value it writes still names this host.
//! * A value (an environment read, a native library's name): [`host_path_in_value`]
//!   finds an absolute path anywhere in it, not only a value that is one whole path.
//! * The encoded metadata's bytes: [`HostPrefixes::occurrences`] finds every place this
//!   session's host prefixes (its working directory, every remap source, the sysroot,
//!   the output, temporary and incremental directories, the home directory) are written,
//!   whatever wrote them: a constant or static copied from a dependency, a string a
//!   proc macro made from an untracked read, an attribute, a Trust-IR entry.

use std::path::{Component, Path, PathBuf};

use crate::{FileName, InnerRealFileName, RealFileName, Span};

#[cfg(test)]
mod tests;

/// The version tag of the machine-readable record [`record`] writes.
pub const RECORD_SCHEMA: &str = "trust-path-free-v1";

/// Where a refused file-name path came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HostPathOrigin {
    /// The source file's own name (an absolute path, or one made absolute from it).
    SourceFileName,
    /// The working directory a relative source-file name was resolved against.
    WorkingDirectory,
}

impl HostPathOrigin {
    /// The record's spelling of this origin.
    pub fn as_str(self) -> &'static str {
        match self {
            HostPathOrigin::SourceFileName => "source-file",
            HostPathOrigin::WorkingDirectory => "working-directory",
        }
    }

    /// The diagnostic's spelling of this origin.
    pub fn describe(self) -> &'static str {
        match self {
            HostPathOrigin::SourceFileName => "a source-file name",
            HostPathOrigin::WorkingDirectory => "the working directory",
        }
    }
}

/// A refused path as the record carries it: its text, and its bytes when they are not
/// UTF-8 (a lossy rendering alone would name a path a tool cannot find).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordPath {
    /// The path, rendered lossily when it is not UTF-8.
    pub text: String,
    /// The path's bytes (`OsStr::as_encoded_bytes`) when they are not UTF-8.
    pub bytes: Option<Vec<u8>>,
}

impl RecordPath {
    pub fn from_bytes(bytes: &[u8]) -> RecordPath {
        match std::str::from_utf8(bytes) {
            Ok(text) => RecordPath { text: text.to_owned(), bytes: None },
            Err(_) => RecordPath {
                text: String::from_utf8_lossy(bytes).into_owned(),
                bytes: Some(bytes.to_vec()),
            },
        }
    }

    pub fn from_path(path: &Path) -> RecordPath {
        RecordPath::from_bytes(path.as_os_str().as_encoded_bytes())
    }
}

/// One refusal, as `rustc_metadata` reports it. A compile collects them in its session
/// and reports the first, counting the others.
#[derive(Clone, Debug)]
pub struct Refusal {
    /// The record's `origin`: `source-file`, `working-directory`, `imported-source-file`,
    /// `env`, `native-library` or `metadata`.
    pub origin: &'static str,
    /// The diagnostic's words for where the path came from.
    pub describe: String,
    /// The refused host path.
    pub path: RecordPath,
    /// The record's other fields, in order, between `origin` and `path`.
    pub fields: Vec<(&'static str, String)>,
    /// What the diagnostic points at, when there is a place in the source.
    pub span: Option<Span>,
}

/// The host prefixes of one session: absolute directories a path in metadata must not
/// start with. Each is kept as given and, when that differs, as `canonicalize` renders it.
/// A prefix with no normal component (a root, a bare drive) is dropped: it would match
/// every absolute path, including the virtual ones a remap rule writes.
#[derive(Clone, Debug)]
pub struct HostPrefixes {
    /// Longest first, so the first prefix that matches at an offset is the most specific.
    prefixes: Vec<Vec<u8>>,
    /// Which bytes some prefix starts with.
    first: [bool; 256],
}

/// One place a host prefix is written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Occurrence {
    /// Where the path starts.
    pub offset: usize,
    /// The host prefix that matched there.
    pub prefix: Vec<u8>,
    /// The path written there, from the prefix to the first byte a path does not hold.
    pub path: Vec<u8>,
}

/// Whether `b` continues a file-name component, so that a prefix followed by it names a
/// different directory (`/w` against `/w2`).
fn continues_component(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-' | b'+' | b'~' | b'@') || b >= 0x80
}

/// Whether `b` ends a path written in a value: whitespace, a control byte, a quote or a
/// list separator.
fn ends_path(b: u8) -> bool {
    b < 0x21 || b == 0x7f || matches!(b, b'"' | b'\'' | b'`' | b',' | b';')
}

/// The path that starts at `bytes[start..]`, at most 4096 bytes.
fn path_at(bytes: &[u8], start: usize) -> &[u8] {
    let rest = &bytes[start..];
    let rest = &rest[..rest.len().min(4096)];
    let end = rest.iter().position(|&b| ends_path(b)).unwrap_or(rest.len());
    &rest[..end]
}

/// Whether `path` has a component below its root.
fn has_normal_component(path: &Path) -> bool {
    path.components().any(|c| matches!(c, Component::Normal(_)))
}

impl Default for HostPrefixes {
    fn default() -> HostPrefixes {
        HostPrefixes { prefixes: Vec::new(), first: [false; 256] }
    }
}

impl HostPrefixes {
    /// The prefixes of `candidates`, each made absolute against `working_dir`.
    pub fn new(working_dir: &Path, candidates: impl IntoIterator<Item = PathBuf>) -> HostPrefixes {
        let mut prefixes: Vec<Vec<u8>> = Vec::new();
        for candidate in candidates {
            let absolute =
                if candidate.is_absolute() { candidate } else { working_dir.join(candidate) };
            let canonical = std::fs::canonicalize(&absolute).ok();
            for path in std::iter::once(absolute).chain(canonical) {
                if !path.is_absolute() || !has_normal_component(&path) {
                    continue;
                }
                let mut bytes = path.as_os_str().as_encoded_bytes().to_vec();
                while bytes.len() > 1 && matches!(bytes.last(), Some(b'/' | b'\\')) {
                    bytes.pop();
                }
                prefixes.push(bytes);
            }
        }
        prefixes.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));
        prefixes.dedup();
        let mut first = [false; 256];
        for prefix in &prefixes {
            first[usize::from(prefix[0])] = true;
        }
        HostPrefixes { prefixes, first }
    }

    pub fn is_empty(&self) -> bool {
        self.prefixes.is_empty()
    }

    /// Every place in `bytes` a host prefix is written as a whole directory (followed by
    /// a separator, the end, or a byte no file name continues with), in order; a path is
    /// counted once even when several prefixes match it.
    pub fn occurrences(&self, bytes: &[u8]) -> Vec<Occurrence> {
        let mut found = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            if self.first[usize::from(bytes[i])]
                && let Some(prefix) = self.prefixes.iter().find(|prefix| {
                    bytes[i..].starts_with(prefix)
                        && bytes.get(i + prefix.len()).is_none_or(|&b| !continues_component(b))
                })
            {
                let path = path_at(bytes, i);
                found.push(Occurrence { offset: i, prefix: prefix.clone(), path: path.to_vec() });
                i += path.len().max(prefix.len());
                continue;
            }
            i += 1;
        }
        found
    }
}

/// Whether `bytes[i]` starts a token of a value: the value's start, or after whitespace,
/// a quote, `=`, `:`, `,`, `;`, or `file://`.
fn starts_token(bytes: &[u8], i: usize) -> bool {
    i == 0
        || matches!(
            bytes[i - 1],
            b' ' | b'\t' | b'\n' | b'\r' | b'=' | b':' | b',' | b';' | b'"' | b'\''
        )
        || bytes[..i].ends_with(b"file://")
}

/// The first absolute path written anywhere in `value`, or `None`: a host prefix of this
/// session; the whole value when it is an absolute path on this host; a token that starts
/// with `/` or `\` and a path component (`--sysroot=/x`, `/usr/bin:/bin`,
/// `file:///x`, ` /x`, an MSYS `/c/x`); a token that starts with a drive (`X:\`, `X:/`);
/// or a `\\` share anywhere. A URL's `//host` is not a path component.
pub fn host_path_in_value(value: &str, prefixes: &HostPrefixes) -> Option<String> {
    let bytes = value.as_bytes();
    if let Some(found) = prefixes.occurrences(bytes).into_iter().next() {
        return Some(String::from_utf8_lossy(&found.path).into_owned());
    }
    let component = |b: Option<&u8>| b.is_some_and(|&b| !ends_path(b) && b != b'/' && b != b'\\');
    for i in 0..bytes.len() {
        let b = bytes[i];
        let rooted =
            (b == b'/' || b == b'\\') && starts_token(bytes, i) && component(bytes.get(i + 1));
        let drive = b.is_ascii_alphabetic()
            && starts_token(bytes, i)
            && bytes.get(i + 1) == Some(&b':')
            && matches!(bytes.get(i + 2), Some(b'/' | b'\\'));
        let share = b == b'\\' && bytes.get(i + 1) == Some(&b'\\') && component(bytes.get(i + 2));
        if rooted || drive || share {
            let path = path_at(bytes, i);
            // `/usr/bin:/bin` names `/usr/bin`; a drive's own `:` stays.
            let end = path.iter().skip(2).position(|&b| b == b':').map_or(path.len(), |p| p + 2);
            return Some(String::from_utf8_lossy(&path[..end]).into_owned());
        }
    }
    Path::new(value).is_absolute().then(|| value.to_owned())
}

/// The fields of one `InnerRealFileName` that reach metadata, in the order a refusal
/// names them, each with its origin. The embeddable name is the source file's own when
/// the name is absolute and the working directory's join otherwise.
fn fields(inner: &InnerRealFileName) -> [(&Path, HostPathOrigin); 3] {
    let embeddable_origin = if inner.name.is_absolute() {
        HostPathOrigin::SourceFileName
    } else {
        HostPathOrigin::WorkingDirectory
    };
    [
        (&inner.name, HostPathOrigin::SourceFileName),
        (&inner.working_directory, HostPathOrigin::WorkingDirectory),
        (&inner.embeddable_name, embeddable_origin),
    ]
}

/// The root of an absolute path: everything up to and including its first normal
/// component (`/home` of `/home/a/w`, `C:\virtual` of `C:\virtual\x`); `None` for a path
/// with no normal component, which names nothing on any host.
fn root(path: &Path) -> Option<PathBuf> {
    let mut out = PathBuf::new();
    for component in path.components() {
        out.push(component);
        if matches!(component, Component::Normal(_)) {
            return Some(out);
        }
    }
    None
}

impl RealFileName {
    /// The first absolute host path `exported` (the form of `self` that is written into
    /// crate metadata) carries that no remap rule rewrote away from this host, with its
    /// origin; `None` when it carries none. `on_host` says whether a path exists here
    /// (`rustc_metadata` asks the file system; tests inject it). See the module
    /// documentation for the rule.
    pub fn trust_unrewritten_host_path(
        &self,
        exported: &RealFileName,
        on_host: &dyn Fn(&Path) -> bool,
    ) -> Option<(HostPathOrigin, PathBuf)> {
        // A local part that survives export is the host form itself.
        if let Some(local) = &exported.local {
            for (path, origin) in fields(local) {
                if path.is_absolute() {
                    return Some((origin, path.to_path_buf()));
                }
            }
        }
        let original = self.local.as_ref().map(fields);
        for (index, (path, origin)) in fields(&exported.maybe_remapped).into_iter().enumerate() {
            if !path.is_absolute() {
                continue;
            }
            let changed = original.as_ref().is_some_and(|original| original[index].0 != path);
            let off_host = root(path).is_none_or(|root| !on_host(&root));
            if !(changed && off_host) {
                return Some((origin, path.to_path_buf()));
            }
        }
        None
    }
}

impl FileName {
    /// [`RealFileName::trust_unrewritten_host_path`] for any file name: `self` is the
    /// session's name, `exported` the one written into metadata. A doctest name is
    /// written as it is; a driver's custom name is refused when it holds an absolute path;
    /// the hash-named virtual files carry no path.
    pub fn trust_unrewritten_host_path(
        &self,
        exported: &FileName,
        on_host: &dyn Fn(&Path) -> bool,
    ) -> Option<(HostPathOrigin, PathBuf)> {
        match (self, exported) {
            (FileName::Real(original), FileName::Real(exported))
            | (FileName::DocTest(original, _), FileName::DocTest(exported, _)) => {
                original.trust_unrewritten_host_path(exported, on_host)
            }
            // Different variants: nothing proves a rewrite, so judge the exported name
            // against no local form (every absolute field is refused).
            (_, FileName::Real(exported)) | (_, FileName::DocTest(exported, _)) => {
                let unproven = RealFileName { local: None, ..exported.clone() };
                unproven.trust_unrewritten_host_path(exported, on_host)
            }
            (_, FileName::Custom(name)) => host_path_in_value(name, &HostPrefixes::default())
                .map(|path| (HostPathOrigin::SourceFileName, PathBuf::from(path))),
            (_, FileName::CfgSpec(_))
            | (_, FileName::Anon(_))
            | (_, FileName::MacroExpansion(_))
            | (_, FileName::ProcMacroSourceCode(_))
            | (_, FileName::CliCrateAttr(_))
            | (_, FileName::InlineAsm(_)) => None,
        }
    }
}

/// The machine-readable record of one refusal: a single line, `trust-path-free-v1 `
/// followed by a JSON object with `origin`, then `fields` in order (`var` and `read` for
/// an `env` origin; `file` and `crate` for a file name; `kind` for a native library;
/// `prefix`, `offset` and `output` for a `metadata` occurrence), then `path`, then
/// `path_bytes` (lowercase hex) when the path is not UTF-8, then `further`: how many
/// other refusals the same check found. The checks run in order (environment reads before
/// anything is encoded; file names and native libraries while encoding; the encoded
/// bytes last, only when nothing before refused) and a compile stops at the first that
/// refuses, so `further` counts refusals of that check only.
pub fn record(origin: &str, fields: &[(&str, &str)], path: &RecordPath, further: usize) -> String {
    let mut out = String::with_capacity(path.text.len() + 96);
    out.push_str(RECORD_SCHEMA);
    out.push_str(" {\"origin\":");
    push_json_string(&mut out, origin);
    for (key, value) in fields {
        out.push(',');
        push_json_string(&mut out, key);
        out.push(':');
        push_json_string(&mut out, value);
    }
    out.push_str(",\"path\":");
    push_json_string(&mut out, &path.text);
    if let Some(bytes) = &path.bytes {
        out.push_str(",\"path_bytes\":\"");
        for b in bytes {
            out.push_str(&format!("{b:02x}"));
        }
        out.push('"');
    }
    out.push_str(",\"further\":");
    out.push_str(&further.to_string());
    out.push('}');
    out
}

/// Appends `value` as a JSON string literal (RFC 8259 escaping).
fn push_json_string(out: &mut String, value: &str) {
    out.push('"');
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}
