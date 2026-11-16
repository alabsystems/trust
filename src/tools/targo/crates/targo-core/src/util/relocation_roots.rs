//! Trust: `-Ztrust-relocation-roots` (EW-9).
//!
//! A tree's build directory may be seeded by cloning another tree's green
//! build. A unit of the clone must be fresh exactly when its inputs match those
//! of the original after each root of the original is replaced by the same
//! root of the clone, and no build of the clone may read or link the
//! original's files. Bootstrap names the roots with this flag, in a fixed order (the
//! source tree, then its git dir); root `i` is recorded as the token
//! `\0trust-relocation-root-<i>\0`.
//!
//! NUL cannot occur in a path or an environment value, so a token never
//! collides with recorded text. Records that are hashed into a fingerprint
//! ([`RelocationRoots::record_path`], [`RelocationRoots::record_value`]) match
//! only the roots as given and escape any text that already holds a NUL, so
//! with the same roots recording is injective and inside one tree this
//! changes only the stored representation, never a freshness decision.
//! Dep-info paths and replayed output, which are not hashed, also match each
//! root's canonical spelling (the same directory).
//!
//! Matching is textual and fail-closed:
//!
//! * A path names root `i` only when it is that root or lies below it at a
//!   component boundary (`/a/root` names neither `/a/rootx` nor `/x/a/root`).
//!   When one root contains another, the longest spelling wins.
//! * Inside free text (an environment value, a build-script directive) a root
//!   occurrence must also start at the beginning of the text or after a
//!   separator, and end at `/`, the end of the text or a separator (see
//!   [`is_separator`]). Other occurrences are left alone: the stored value then
//!   differs and the script reruns.
//! * A token whose index names no current root expands to nothing; callers
//!   treat it as a missing input (stale).

use std::borrow::Cow;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use anyhow::bail;

use crate::CargoResult;

const FLAG: &str = "-Ztrust-relocation-roots";
const TOKEN_PREFIX: &str = "\u{0}trust-relocation-root-";
const TOKEN_END: char = '\u{0}';
/// Header of the `root-relocation` record a build-script run leaves beside
/// `root-output`.
const RECORD_MAGIC: &[u8] = b"trust-relocation-roots-v1\0";

/// The relocation roots in effect for this invocation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelocationRoots {
    /// Root `i` as given, without trailing `/`.
    roots: Vec<String>,
    /// The roots as given, longest first, so a nested root wins.
    given: Vec<(usize, String)>,
    /// Every spelling that names a root: as given and, where it differs, its
    /// canonical form. Longest first.
    spellings: Vec<(usize, String)>,
}

impl RelocationRoots {
    /// Parses the flag value: comma-separated absolute paths.
    pub fn parse(value: &str) -> CargoResult<RelocationRoots> {
        RelocationRoots::new(value.split(',').map(str::to_owned).collect())
    }

    /// Validates `roots` and records each one's canonical spelling, when it
    /// exists and differs, as another spelling of the same root.
    pub fn new(roots: Vec<String>) -> CargoResult<RelocationRoots> {
        let roots = validate(roots)?;
        let canonical = roots
            .iter()
            .map(|root| {
                std::fs::canonicalize(root)
                    .ok()
                    .and_then(|path| path.into_os_string().into_string().ok())
                    .map(|path| path.trim_end_matches('/').to_owned())
            })
            .collect();
        Ok(RelocationRoots::with_canonical(roots, canonical))
    }

    fn with_canonical(roots: Vec<String>, canonical: Vec<Option<String>>) -> RelocationRoots {
        let longest_first = |a: &(usize, String), b: &(usize, String)| {
            b.1.len().cmp(&a.1.len()).then(a.0.cmp(&b.0))
        };
        let mut given: Vec<(usize, String)> = roots.iter().cloned().enumerate().collect();
        given.sort_by(longest_first);
        let mut spellings = given.clone();
        for (index, canonical) in canonical.into_iter().enumerate() {
            if let Some(canonical) = canonical
                && !canonical.is_empty()
                && canonical.starts_with('/')
                && !spellings.iter().any(|(_, spelling)| *spelling == canonical)
            {
                spellings.push((index, canonical));
            }
        }
        spellings.sort_by(longest_first);
        RelocationRoots {
            roots,
            given,
            spellings,
        }
    }

    /// The roots as given, in order.
    pub fn roots(&self) -> &[String] {
        &self.roots
    }

    /// The token form of a dep-info `path` when it names a root (in any
    /// spelling) or lies below one.
    pub fn tokenize_path(&self, path: &Path) -> Option<PathBuf> {
        tokenize_prefix(path, &self.spellings)
    }

    /// The recorded form of a build script's `rerun-if-changed` path, hashed
    /// into its fingerprint and expanded by [`expand_path`] when checked.
    pub fn record_path(&self, path: PathBuf) -> PathBuf {
        if path.as_os_str().as_encoded_bytes().first() == Some(&0) {
            // Not a real path: keep it unexpandable, so it stays missing.
            let mut escaped = std::ffi::OsString::from("\0\0");
            escaped.push(path);
            return escaped.into();
        }
        tokenize_prefix(&path, &self.given).unwrap_or(path)
    }

    /// The recorded form of a `rerun-if-env-changed` value, hashed into the
    /// fingerprint: every delimited root occurrence replaced by its token.
    pub fn record_value(&self, value: &str) -> String {
        if value.contains(TOKEN_END) {
            // Escaped so it cannot equal another value's recorded form.
            return format!("\0\0{value}");
        }
        let tokens: Vec<String> = (0..self.roots.len()).map(token).collect();
        rewrite(value, &self.given, &tokens, None)
            .expect("tokenizing is never strict about residual roots")
            .into_owned()
    }

    /// The record of these roots that a build-script run leaves beside its
    /// output, so a later replay in a relocated tree can re-root it.
    pub fn record(&self) -> Vec<u8> {
        let mut record = RECORD_MAGIC.to_vec();
        for (index, root) in self.roots.iter().enumerate() {
            let canonical = self
                .spellings
                .iter()
                .find(|(i, spelling)| *i == index && spelling != root)
                .map_or("", |(_, spelling)| spelling.as_str());
            for field in [root.as_str(), canonical] {
                record.extend_from_slice(field.as_bytes());
                record.push(0);
            }
        }
        record
    }

    /// How to replay output recorded under the roots `record` names in the
    /// tree these roots name: `Ok(None)` (replay verbatim) when it names
    /// exactly these roots (nothing moved), and `Err` when the record is
    /// malformed or names a different number of roots. Output recorded beside
    /// such a record may name another tree's files, so it is never replayed:
    /// the script runs again.
    pub fn relocation_from(&self, record: &[u8]) -> Result<Option<OutputRelocation>, ()> {
        let body = record.strip_prefix(RECORD_MAGIC).ok_or(())?;
        let body = std::str::from_utf8(body).map_err(drop)?;
        let fields: Vec<&str> = body.strip_suffix('\0').ok_or(())?.split('\0').collect();
        if fields.len() != 2 * self.roots.len() {
            return Err(());
        }
        let old_roots: Vec<String> = fields.iter().step_by(2).map(|s| s.to_string()).collect();
        if old_roots == self.roots {
            return Ok(None);
        }
        let old_roots = validate(old_roots).map_err(drop)?;
        let canonical = fields
            .iter()
            .skip(1)
            .step_by(2)
            .map(|s| (!s.is_empty()).then(|| s.to_string()))
            .collect();
        let old = RelocationRoots::with_canonical(old_roots, canonical);
        Ok(Some(OutputRelocation {
            spellings: old.spellings,
            roots: self.roots.clone(),
        }))
    }
}

/// Re-roots cached build-script directives recorded in another tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputRelocation {
    /// Spellings of the recording tree's roots, longest first.
    spellings: Vec<(usize, String)>,
    /// The current roots, by index.
    roots: Vec<String>,
}

impl OutputRelocation {
    /// One directive value: the recorded `OUT_DIR` becomes the current one
    /// (exactly as without relocation), then each delimited old root becomes
    /// the current root with the same index, in a single pass over the
    /// recorded text. An old root at any other position is an error: such
    /// output cannot be replayed without referring to the recording tree, so
    /// the script must run again.
    pub fn relocate<'v>(&self, value: &'v str, out_dir: (&str, &str)) -> CargoResult<Cow<'v, str>> {
        match rewrite(value, &self.spellings, &self.roots, Some(out_dir)) {
            Ok(value) => Ok(value),
            Err(root) => bail!(
                "cached build-script output names relocated root `{root}` at a position \
                 that cannot be re-rooted: `{value}`"
            ),
        }
    }
}

/// Expands a leading token of a recorded path with the current `roots`.
/// A path without a token is returned unchanged; `None` means the token names
/// no current root (or is malformed), which callers treat as a missing input.
pub fn expand_path<'p>(path: &'p Path, roots: Option<&RelocationRoots>) -> Option<Cow<'p, Path>> {
    if path.as_os_str().as_encoded_bytes().first() != Some(&0) {
        return Some(Cow::Borrowed(path));
    }
    let (index, rest) = take_token(path.to_str()?)?;
    let root = roots?.roots.get(index)?;
    (rest.is_empty() || rest.starts_with('/'))
        .then(|| Cow::Owned(PathBuf::from(format!("{root}{rest}"))))
}

/// Recorded text for diagnostics: each token becomes `{relocation-root-<i>}`.
pub fn display(value: &str) -> Cow<'_, str> {
    if !value.contains(TOKEN_END) {
        return Cow::Borrowed(value);
    }
    let mut out = String::with_capacity(value.len());
    let mut rest = value;
    while let Some(ch) = rest.chars().next() {
        if let Some((index, after)) = take_token(rest) {
            let _ = write!(out, "{{relocation-root-{index}}}");
            rest = after;
        } else {
            if ch == TOKEN_END {
                out.push_str("\\0");
            } else {
                out.push(ch);
            }
            rest = &rest[ch.len_utf8()..];
        }
    }
    Cow::Owned(out)
}

/// [`display`] for a recorded path.
pub fn display_path(path: &Path) -> PathBuf {
    match path.to_str() {
        Some(path) => PathBuf::from(display(path).into_owned()),
        None => path.to_owned(),
    }
}

/// A character that can delimit a path inside free text.
fn is_separator(ch: char) -> bool {
    ch.is_whitespace() || matches!(ch, ':' | ';' | ',' | '=' | '"' | '\'')
}

fn tokenize_prefix(path: &Path, spellings: &[(usize, String)]) -> Option<PathBuf> {
    let path = path.to_str()?;
    spellings.iter().find_map(|(index, spelling)| {
        let rest = path.strip_prefix(spelling.as_str())?;
        (rest.is_empty() || rest.starts_with('/'))
            .then(|| PathBuf::from(format!("{}{rest}", token(*index))))
    })
}

fn token(index: usize) -> String {
    format!("{TOKEN_PREFIX}{index}{TOKEN_END}")
}

/// Splits a token off the front of `s`.
fn take_token(s: &str) -> Option<(usize, &str)> {
    let after = s.strip_prefix(TOKEN_PREFIX)?;
    let end = after.find(TOKEN_END)?;
    let digits = &after[..end];
    if digits.is_empty()
        || !digits.bytes().all(|b| b.is_ascii_digit())
        || (digits.len() > 1 && digits.starts_with('0'))
    {
        return None;
    }
    Some((digits.parse().ok()?, &after[end + 1..]))
}

fn validate(roots: Vec<String>) -> CargoResult<Vec<String>> {
    if roots.is_empty() {
        bail!("`{FLAG}` needs at least one absolute path");
    }
    let mut valid: Vec<String> = Vec::with_capacity(roots.len());
    for root in roots {
        if root.is_empty() {
            bail!("`{FLAG}` has an empty root; expected comma-separated absolute paths");
        }
        if root.contains('\0') || root.contains(',') {
            bail!(
                "`{FLAG}` root `{}` contains a NUL or a comma",
                root.escape_debug()
            );
        }
        if !root.starts_with('/') || !Path::new(&root).is_absolute() {
            bail!("`{FLAG}` root `{root}` is not an absolute path");
        }
        let root = root.trim_end_matches('/');
        if root.is_empty() {
            bail!("`{FLAG}` root must name a directory below `/`");
        }
        if valid.iter().any(|seen| seen == root) {
            bail!("`{FLAG}` names root `{root}` twice");
        }
        valid.push(root.to_owned());
    }
    Ok(valid)
}

/// One pass over `value`: an `out_dir` occurrence (as recorded) is replaced
/// first, exactly like the plain replacement used without relocation; then a
/// delimited spelling of root `i` becomes `replacements[i]`. With `out_dir`
/// set (replaying output), an undelimited spelling is an error.
fn rewrite<'v>(
    value: &'v str,
    spellings: &[(usize, String)],
    replacements: &[String],
    out_dir: Option<(&str, &str)>,
) -> Result<Cow<'v, str>, String> {
    let strict = out_dir.is_some();
    let out_dir = out_dir.filter(|(old, _)| !old.is_empty());
    if out_dir.is_none_or(|(old, _)| !value.contains(old))
        && !spellings
            .iter()
            .any(|(_, spelling)| value.contains(spelling.as_str()))
    {
        return Ok(Cow::Borrowed(value));
    }
    let mut out = String::with_capacity(value.len());
    let mut at = 0;
    'scan: while let Some(ch) = value[at..].chars().next() {
        let rest = &value[at..];
        if let Some((old, new)) = out_dir
            && rest.starts_with(old)
        {
            out.push_str(new);
            at += old.len();
            continue;
        }
        let mut undelimited = None;
        for (index, spelling) in spellings {
            if !rest.starts_with(spelling.as_str()) {
                continue;
            }
            let end = at + spelling.len();
            let before = value[..at].chars().next_back().is_none_or(is_separator);
            let after = value[end..]
                .chars()
                .next()
                .is_none_or(|next| next == '/' || is_separator(next));
            if before && after {
                out.push_str(&replacements[*index]);
                at = end;
                continue 'scan;
            }
            undelimited.get_or_insert(spelling);
        }
        if strict && let Some(spelling) = undelimited {
            return Err(spelling.clone());
        }
        out.push(ch);
        at += ch.len_utf8();
    }
    Ok(Cow::Owned(out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn roots(roots: &[&str]) -> RelocationRoots {
        // No filesystem lookups: canonical spellings are tested separately.
        let roots = validate(roots.iter().map(|s| s.to_string()).collect()).unwrap();
        let canonical = vec![None; roots.len()];
        RelocationRoots::with_canonical(roots, canonical)
    }

    fn tok(index: usize, rest: &str) -> String {
        format!("{}{rest}", token(index))
    }

    #[test]
    fn parse_refuses_malformed_roots() {
        for bad in [
            "", "/a,", ",/a", "/a,,/b", "relative", "./a", "/", "//", "/a\0b", "/a,/a", "/a,/a/",
        ] {
            assert!(RelocationRoots::parse(bad).is_err(), "accepted {bad:?}");
        }
        assert!(RelocationRoots::new(vec!["/a,b".to_owned()]).is_err());
        let parsed = RelocationRoots::parse("/w/a/,/w/a/.git").unwrap();
        assert_eq!(parsed.roots(), ["/w/a", "/w/a/.git"]);
    }

    #[test]
    fn path_boundary_is_a_component_boundary() {
        let r = roots(&["/a/root"]);
        assert_eq!(
            r.tokenize_path(Path::new("/a/root")),
            Some(PathBuf::from(tok(0, "")))
        );
        assert_eq!(
            r.tokenize_path(Path::new("/a/root/x/y")),
            Some(PathBuf::from(tok(0, "/x/y")))
        );
        for outside in ["/a/rootx", "/a/rootx/y", "/x/a/root/y", "a/root/y"] {
            assert_eq!(r.tokenize_path(Path::new(outside)), None);
            assert_eq!(r.record_path(outside.into()), Path::new(outside));
        }
        assert_eq!(
            r.record_path("/a/root/x".into()),
            PathBuf::from(tok(0, "/x"))
        );
    }

    #[test]
    fn longest_root_wins_when_one_contains_another() {
        // Root order is the flag's; nesting decides, not position.
        for r in [roots(&["/w/a", "/w/a/.git"]), roots(&["/w/a/.git", "/w/a"])] {
            let git = r
                .roots()
                .iter()
                .position(|root| root == "/w/a/.git")
                .unwrap();
            let tree = 1 - git;
            assert_eq!(
                r.tokenize_path(Path::new("/w/a/.git/modules/x/HEAD")),
                Some(PathBuf::from(tok(git, "/modules/x/HEAD")))
            );
            assert_eq!(
                r.tokenize_path(Path::new("/w/a/.gitignore")),
                Some(PathBuf::from(tok(tree, "/.gitignore")))
            );
            assert_eq!(
                r.record_value("/w/a/.git/HEAD:/w/a/.gitmodules"),
                format!("{}:{}", tok(git, "/HEAD"), tok(tree, "/.gitmodules"))
            );
        }
    }

    #[test]
    fn expand_inverts_tokenize_and_fails_closed() {
        let a = roots(&["/w/a", "/w/common/worktrees/a"]);
        let b = roots(&["/w/b", "/w/common/worktrees/b"]);
        let path = Path::new("/w/common/worktrees/a/modules/first-party/trust-ir/HEAD");
        let stored = a.tokenize_path(path).unwrap();
        assert_eq!(expand_path(&stored, Some(&a)).unwrap(), path);
        assert_eq!(
            expand_path(&stored, Some(&b)).unwrap(),
            Path::new("/w/common/worktrees/b/modules/first-party/trust-ir/HEAD")
        );
        // A path without a token passes through.
        let plain = Path::new("/elsewhere/file");
        assert!(matches!(expand_path(plain, None), Some(Cow::Borrowed(p)) if p == plain));
        // An index with no current root, no roots at all, or a malformed token.
        assert_eq!(expand_path(&stored, Some(&roots(&["/w/b"]))), None);
        assert_eq!(expand_path(&stored, None), None);
        for bad in [
            format!("{TOKEN_PREFIX}x{TOKEN_END}/f"),
            format!("{TOKEN_PREFIX}{TOKEN_END}/f"),
            format!("{TOKEN_PREFIX}01{TOKEN_END}/f"),
            format!("{TOKEN_PREFIX}0"),
            format!("{}x", token(0)),
            "\0/f".to_owned(),
        ] {
            assert_eq!(expand_path(Path::new(&bad), Some(&a)), None, "{bad:?}");
        }
    }

    #[test]
    fn value_tokens_need_delimiters_on_both_sides() {
        let r = roots(&["/a/root"]);
        assert_eq!(r.record_value("/a/root"), tok(0, ""));
        assert_eq!(r.record_value("/a/root/bin/tool"), tok(0, "/bin/tool"));
        assert_eq!(
            r.record_value("x=/a/root/lib:/a/root;'/a/root' \"/a/root\"\t/a/root,/a/root"),
            format!(
                "x={}:{};'{}' \"{}\"\t{},{}",
                tok(0, "/lib"),
                tok(0, ""),
                tok(0, ""),
                tok(0, ""),
                tok(0, ""),
                tok(0, "")
            )
        );
        for untouched in [
            "/a/rootx",
            "/a/rootx/bin",
            "/x/a/root",
            "-L/a/root",
            "/a/root.d",
        ] {
            assert_eq!(r.record_value(untouched), untouched);
        }
        assert_eq!(r.record_value("plain"), "plain");
    }

    #[test]
    fn hashed_records_ignore_canonical_spellings() {
        // `/private/w/a` names the same directory as `/w/a`, but as an env
        // value it is a different string, so it must record differently.
        let r = RelocationRoots::with_canonical(
            vec!["/w/a".to_owned()],
            vec![Some("/private/w/a".to_owned())],
        );
        assert_eq!(r.record_value("/w/a/x"), tok(0, "/x"));
        assert_eq!(r.record_value("/private/w/a/x"), "/private/w/a/x");
        assert_eq!(
            r.record_path("/private/w/a/x".into()),
            Path::new("/private/w/a/x")
        );
        // Dep-info and replayed output do use it (same directory, not hashed).
        assert_eq!(
            r.tokenize_path(Path::new("/private/w/a/x")),
            Some(PathBuf::from(tok(0, "/x")))
        );
    }

    #[test]
    fn text_already_holding_nul_never_expands() {
        let r = roots(&["/w/a"]);
        // A build script could print a token literally; it names no file.
        let literal = PathBuf::from(tok(0, "/x"));
        let recorded = r.record_path(literal.clone());
        assert_ne!(recorded, literal);
        assert_eq!(expand_path(&recorded, Some(&r)), None);
        assert_ne!(r.record_value(&tok(0, "/x")), r.record_value("/w/a/x"));
    }

    #[test]
    fn tokenizing_is_injective_for_fixed_roots() {
        // Inside one tree the flag must not merge two distinct values.
        let r = roots(&["/w/a", "/w/a/.git"]);
        let values = [
            "/w/a",
            "/w/a/",
            "/w/a/.git",
            "/w/a/.git/",
            "/w/a/.gitx",
            "/w/ab",
            "/w/b",
            "x=/w/a",
            "x=/w/b",
        ];
        for (i, x) in values.iter().enumerate() {
            for y in &values[i + 1..] {
                assert_ne!(r.record_value(x), r.record_value(y), "{x} vs {y}");
                // Paths compare by component (`/w/a` is `/w/a/`); records
                // must agree exactly when the paths do.
                assert_eq!(
                    r.record_path(x.into()) == r.record_path(y.into()),
                    Path::new(x) == Path::new(y),
                    "{x} vs {y}"
                );
            }
            // Same roots: the stored form expands back to the original.
            let stored = r.record_path(x.into());
            assert_eq!(expand_path(&stored, Some(&r)).unwrap(), Path::new(x));
        }
    }

    #[test]
    fn display_is_readable() {
        assert_eq!(
            display(&tok(1, "/modules/x")),
            "{relocation-root-1}/modules/x"
        );
        assert_eq!(
            display_path(Path::new(&tok(0, "/a"))),
            Path::new("{relocation-root-0}/a")
        );
        assert!(matches!(display("/plain"), Cow::Borrowed("/plain")));
        assert_eq!(display("a\0b"), "a\\0b");
    }

    #[test]
    fn record_round_trips_and_relocates_output() {
        let a = RelocationRoots::with_canonical(
            vec!["/w/a".to_owned(), "/w/a/.git".to_owned()],
            vec![Some("/private/w/a".to_owned()), None],
        );
        let b = roots(&["/w/b", "/w/b/.git"]);
        // Same roots: replay verbatim.
        assert_eq!(a.relocation_from(&a.record()), Ok(None));
        // Different root count or malformed record: never replayed.
        assert_eq!(roots(&["/w/b"]).relocation_from(&a.record()), Err(()));
        assert_eq!(b.relocation_from(b"garbage"), Err(()));
        assert_eq!(b.relocation_from(RECORD_MAGIC), Err(()));
        let mut truncated = a.record();
        truncated.pop();
        assert_eq!(b.relocation_from(&truncated), Err(()));

        let relocation = b.relocation_from(&a.record()).unwrap().unwrap();
        let out_dir = ("/w/a/target/debug/build/x/out", "/t/b/debug/build/x/out");
        assert_eq!(
            relocation
                .relocate("native=/w/a/build/llvm/lib", out_dir)
                .unwrap(),
            "native=/w/b/build/llvm/lib"
        );
        // The canonical spelling of the recording root is re-rooted too.
        assert_eq!(
            relocation.relocate("/private/w/a/x", out_dir).unwrap(),
            "/w/b/x"
        );
        // OUT_DIR is replaced as recorded, before any root.
        assert_eq!(
            relocation
                .relocate("all=/w/a/target/debug/build/x/out/lib", out_dir)
                .unwrap(),
            "all=/t/b/debug/build/x/out/lib"
        );
        assert_eq!(
            relocation
                .relocate("/w/a/.git/modules/m/HEAD", out_dir)
                .unwrap(),
            "/w/b/.git/modules/m/HEAD"
        );
        // Unrelated text is untouched.
        assert!(matches!(
            relocation.relocate("static=LLVM", out_dir).unwrap(),
            Cow::Borrowed("static=LLVM")
        ));
        // An old root that cannot be re-rooted must not be replayed.
        assert!(relocation.relocate("-L/w/a/lib", out_dir).is_err());
        assert!(relocation.relocate("/w/ab/lib", out_dir).is_err());
    }
}
