//! Read the historical measurement formats, independently of proof readers.

use std::{fs, io};

use super::*;

#[derive(Clone, Debug)]
pub(super) struct Parity {
    pub(super) corpus: String,
    pub(super) function: Function,
    pub(super) oracle: String,
    pub(super) rows: u64,
    pub(super) mismatches: u64,
}

#[derive(Default)]
pub(super) struct Audit {
    pub(super) elided: Counter<Identity>,
    pub(super) kept: BTreeMap<Identity, Counter<String>>,
    pub(super) origins: BTreeMap<Function, Counter<String>>,
    pub(super) origin_states: Counter<String>,
    pub(super) verdicts: BTreeMap<Identity, Counter<Verdict>>,
    pub(super) t9_keys: BTreeMap<Function, BTreeSet<String>>,
    pub(super) verdict_rows: usize,
    pub(super) unkeyed: usize,
    pub(super) malformed: Vec<String>,
    pub(super) ignored: Counter<String>,
    pub(super) rowdigests: BTreeMap<Function, Counter<RowDigest>>,
    pub(super) rowdigest_rows: usize,
    pub(super) stops: BTreeMap<Function, Vec<(String, String)>>,
    pub(super) certify_stops: BTreeMap<Function, Vec<(String, String)>>,
    pub(super) caps: BTreeMap<Function, Counter<String>>,
    pub(super) parity: Vec<Parity>,
    pub(super) corpora: BTreeSet<String>,
}

impl Audit {
    pub(super) fn read(directory: &Path, l4: bool) -> io::Result<Self> {
        let files = audit_files(directory)?;
        if files.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("{}: no elide-audit-*.tsv file", directory.display()),
            ));
        }
        let mut audit = Self::default();
        for path in files {
            let relative = path.strip_prefix(directory).unwrap_or(&path);
            let corpus = corpus_name(relative).map_err(|error| {
                io::Error::new(error.kind(), format!("{}: {error}", path.display()))
            })?;
            let bytes = read_bytes(&path)?;
            let text = String::from_utf8_lossy(&bytes);
            for line in historical_lines(&text).filter(|line| !line.is_empty()) {
                audit.read_row(&corpus, line, l4);
            }
        }
        Ok(audit)
    }

    fn read_row(&mut self, corpus: &str, line: &str, l4: bool) {
        self.corpora.insert(corpus.to_owned());
        let row = line.split('\t').map(str::to_owned).collect::<Vec<_>>();
        let Some(kind) = row.first().map(String::as_str) else {
            return;
        };
        let Some(width) = width(kind) else {
            self.malformed.push(line.into());
            return;
        };
        let Some(columns) = row.len().checked_sub(1 + FUNCTION_COLUMNS) else {
            self.malformed.push(line.into());
            return;
        };
        let width_valid = if kind == "VERDICT" {
            columns == 6 || (!l4 && columns == 5)
        } else {
            columns == width
        };
        if !width_valid {
            self.malformed.push(line.into());
            return;
        }
        let function = function_of(&row[1..]);
        let rest = &row[1 + FUNCTION_COLUMNS..];
        if matches!(kind, "ROWDIGEST" | "STOP" | "CERTIFY-STOP" | "CAP" | "PARITY") {
            if !l4 {
                increment(&mut self.ignored, kind.to_owned());
            } else if !self.read_l4(corpus, kind, function, rest) {
                self.malformed.push(line.into());
            }
            return;
        }
        match kind {
            "ELIDED" => increment(&mut self.elided, identity(&function, rest.iter().cloned())),
            "KEPT" => increment(
                self.kept.entry(identity(&function, [rest[3].clone()])).or_default(),
                rest[0].clone(),
            ),
            "ORIGINS" => {
                increment(self.origins.entry(function).or_default(), rest[1].clone());
                increment(&mut self.origin_states, format!("{} {}", rest[0], rest[1]));
            }
            "VERDICT" => {
                self.verdict_rows += 1;
                let t9_key = &rest[0];
                let key = if l4 { &rest[5] } else { t9_key };
                if t9_key != "-" {
                    self.t9_keys.entry(function.clone()).or_default().insert(t9_key.clone());
                }
                let mut suffix = vec![key.clone()];
                if key == "-" {
                    self.unkeyed += 1;
                    suffix.extend([rest[3].clone(), rest[4].clone()]);
                }
                increment(
                    self.verdicts.entry(identity(&function, suffix)).or_default(),
                    (rest[1].clone(), rest[2].clone()),
                );
            }
            _ => unreachable!("row kind checked above"),
        }
    }

    fn read_l4(&mut self, corpus: &str, kind: &str, function: Function, rest: &[String]) -> bool {
        match kind {
            "ROWDIGEST" => {
                if !digits(&rest[0]) || !digest(&rest[3]) {
                    return false;
                }
                increment(
                    self.rowdigests.entry(function).or_default(),
                    (rest[1].clone(), rest[2].clone(), rest[3].clone()),
                );
                self.rowdigest_rows += 1;
            }
            "STOP" | "CERTIFY-STOP" => {
                if trust_types::determinism::StopCause::parse(&rest[1]).is_none() {
                    return false;
                }
                if kind == "STOP" {
                    self.stops
                        .entry(function)
                        .or_default()
                        .push((rest[0].clone(), rest[1].clone()));
                } else {
                    if !digits(&rest[0]) && rest[0] != "-" {
                        return false;
                    }
                    self.certify_stops
                        .entry(function)
                        .or_default()
                        .push((rest[0].clone(), rest[1].clone()));
                }
            }
            "CAP" => {
                if caps::site_commit(&rest[0]).is_none() {
                    return false;
                }
                increment(self.caps.entry(function).or_default(), rest[0].clone());
            }
            "PARITY" => {
                let Some(rows) = parse_count(&rest[1], "rows") else {
                    return false;
                };
                let Some(mismatches) = parse_count(&rest[2], "mismatches") else {
                    return false;
                };
                if !ORACLES.contains(&rest[0].as_str()) && rest[0] != "identity-scope" {
                    return false;
                }
                self.parity.push(Parity {
                    corpus: corpus.into(),
                    function,
                    oracle: rest[0].clone(),
                    rows,
                    mismatches,
                });
            }
            _ => unreachable!("L4 kind checked above"),
        }
        true
    }

    pub(super) fn table_states(&self, function: &Function) -> String {
        self.origins
            .get(function)
            .map(|states| states.keys().cloned().collect::<Vec<_>>().join(","))
            .unwrap_or_else(|| "none".into())
    }

    pub(super) fn unreproducible_functions(&self) -> BTreeSet<Function> {
        let mut functions = BTreeSet::new();
        for (key, entries) in &self.verdicts {
            if entries.keys().any(|(_, stop)| clock_verdict(stop)) {
                functions.insert(function_of(key));
            }
        }
        for table in [&self.stops, &self.certify_stops] {
            for (function, entries) in table {
                if !is_crate_level(function)
                    && entries.iter().any(|(_, cause)| !reproducible(cause))
                {
                    functions.insert(function.clone());
                }
            }
        }
        functions
    }

    pub(super) fn census(&self) -> Census {
        let mut kept = Counter::new();
        for reasons in self.kept.values() {
            for (reason, count) in reasons {
                *kept.entry(reason.clone()).or_default() += count;
            }
        }
        Census {
            elided: sum(&self.elided),
            kept,
            origins: self.origin_states.clone(),
            verdict_rows: self.verdict_rows,
            unkeyed: self.unkeyed,
            malformed_rows: self.malformed.len(),
            ignored: self.ignored.clone(),
            rowdigest_rows: self.rowdigest_rows,
            rowdigest_functions: self.rowdigests.len(),
            corpora: self.corpora.clone(),
            obligations: 0,
        }
    }
}

/// The corpus is the first directory under the comparison root, or `.` for
/// files directly in it. Reject unrepresentable names instead of merging two
/// distinct native paths through lossy Unicode conversion.
pub(super) fn corpus_name(relative: &Path) -> io::Result<String> {
    let mut components = relative.components();
    let Some(first) = components.next() else {
        return Ok(".".into());
    };
    if components.next().is_none() {
        return Ok(".".into());
    }
    first
        .as_os_str()
        .to_str()
        .map(str::to_owned)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "corpus name is not valid UTF-8"))
}

fn width(kind: &str) -> Option<usize> {
    Some(match kind {
        "ELIDED" | "KEPT" | "ORIGINS" | "ROWDIGEST" => 4,
        "VERDICT" => 5,
        "STOP" | "CERTIFY-STOP" => 2,
        "CAP" => 1,
        "PARITY" => 3,
        _ => return None,
    })
}
fn digits(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())
}
fn parse_count(value: &str, name: &str) -> Option<u64> {
    let digits = value.strip_prefix(name)?.strip_prefix('=')?;
    if !self::digits(digits) {
        return None;
    }
    digits.parse().ok()
}
fn digest(value: &str) -> bool {
    value == "-"
        || (value.len() == 64
            && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)))
}

pub(super) fn audit_files(directory: &Path) -> io::Result<Vec<PathBuf>> {
    let mut files = walk_files(directory)?;
    files.retain(|path| {
        path.file_name().is_some_and(|name| {
            let name = name.to_string_lossy();
            name.starts_with("elide-audit-") && name.ends_with(".tsv")
        })
    });
    Ok(files)
}

pub(crate) fn walk_files(root: &Path) -> io::Result<Vec<PathBuf>> {
    if !root.is_dir() {
        return Ok(Vec::new());
    }
    let mut directories = vec![root.to_owned()];
    let mut files = Vec::new();
    while let Some(directory) = directories.pop() {
        for entry in fs::read_dir(directory)? {
            let entry = entry?;
            let kind = entry.file_type()?;
            let path = entry.path();
            // Like rglob, never follow directory symlinks into another corpus.
            if kind.is_dir() {
                directories.push(path.clone());
            }
            // Include every matching path in the later selection, including
            // special files/directories. A named audit input must be refused,
            // never silently disappear from the corpus denominator.
            files.push(path);
        }
    }
    files.sort();
    Ok(files)
}

pub(crate) fn read_bytes(path: &Path) -> io::Result<Vec<u8>> {
    use std::io::Read as _;
    let mut options = fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        // A replaced FIFO cannot block the coordinator before fstat rejects it.
        // Regular-file symlinks remain observational inputs, as in rglob.
        options.custom_flags(libc::O_NONBLOCK);
    }
    let mut file = options.open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{}: audit input is not a regular file", path.display()),
        ));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}

/// Historical producers/readers use Python's complete splitlines vocabulary.
/// Retain every empty interior line, treat CRLF as one boundary, and produce
/// no synthetic empty line after a trailing separator. These separators must
/// not become new scope/key characters merely because this reader is native.
pub(super) fn historical_lines(mut text: &str) -> impl Iterator<Item = &str> {
    std::iter::from_fn(move || {
        if text.is_empty() {
            return None;
        }
        if let Some((index, separator)) = text.char_indices().find(|(_, ch)| {
            matches!(
                ch,
                '\n' | '\r'
                    | '\u{b}'
                    | '\u{c}'
                    | '\u{1c}'
                    | '\u{1d}'
                    | '\u{1e}'
                    | '\u{85}'
                    | '\u{2028}'
                    | '\u{2029}'
            )
        }) {
            let line = &text[..index];
            let mut after = index + separator.len_utf8();
            if separator == '\r' && text[after..].starts_with('\n') {
                after += 1;
            }
            text = &text[after..];
            Some(line)
        } else {
            let line = text;
            text = "";
            Some(line)
        }
    })
}

#[derive(Default)]
pub(super) struct Attributions {
    pub(super) named: BTreeSet<[String; 4]>,
    pub(super) functions: BTreeMap<Function, BTreeSet<String>>,
    lines: Vec<(String, [String; 4])>,
    pub(super) errors: Vec<String>,
}

impl Attributions {
    pub(super) fn read(path: Option<&Path>) -> io::Result<Self> {
        let mut result = Self::default();
        let Some(path) = path else {
            return Ok(result);
        };
        let text = String::from_utf8(read_bytes(path)?)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        for (index, line) in historical_lines(&text).enumerate() {
            if line.trim().is_empty() || line.trim_start().starts_with('#') {
                continue;
            }
            let fields = line.split('\t').collect::<Vec<_>>();
            let location = format!("{}:{}: {line}", path.display(), index + 1);
            if fields.len() < 5 || caps::site_commit(fields[3]).is_none() || fields[4].is_empty() {
                result.errors.push(location);
                continue;
            }
            let named = [fields[0].into(), fields[1].into(), fields[2].into(), fields[3].into()];
            result.named.insert(named.clone());
            result.lines.push((location, named));
            if fields[4] != "-" {
                let function =
                    [fields[0].into(), fields[1].into(), fields[2].into(), fields[4].into()];
                result.functions.entry(function).or_default().insert(fields[3].into());
            }
        }
        Ok(result)
    }

    pub(super) fn validate(&mut self, parent: &Audit, judged: &BTreeSet<String>) {
        let hits = parent
            .caps
            .iter()
            .filter(|(function, _)| is_crate_level(*function))
            .flat_map(|(function, sites)| {
                sites.keys().map(move |site| {
                    [function[0].clone(), function[1].clone(), function[2].clone(), site.clone()]
                })
            })
            .collect::<BTreeSet<_>>();
        for (location, named) in &self.lines {
            let reason = if !judged.contains(&named[3]) {
                Some("a site --deleted-caps does not judge")
            } else if caps::answer_preserving(&named[3]) {
                Some("an answer-preserving site attributes nothing")
            } else if !hits.contains(named) {
                Some("the parent has no crate-level hit of it there")
            } else {
                None
            };
            if let Some(reason) = reason {
                self.errors.push(format!("{location} ({reason})"));
            }
        }
    }

    pub(super) fn no_parent(&mut self) {
        self.errors.extend(self.lines.iter().map(|(location, _)| {
            format!("{location} (no parent audit beside the records to attribute it in)")
        }));
    }
}
