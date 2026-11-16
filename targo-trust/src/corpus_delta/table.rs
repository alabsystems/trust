//! `tests/corpora.toml` (schema `trust.corpora.v1`): the daily-driver corpora
//! as data. The file's own header describes each key.
//!
//! The table is read whole and refused whole: an unknown key, a glob that
//! matches no file, a case declared twice or a pin for a case that is not
//! there is an error, never a smaller corpus.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};

use serde::Deserialize;

use super::Pin;
use crate::input_limits;

/// The table's path in a checkout.
pub(crate) const TABLE: &str = "tests/corpora.toml";
pub(crate) const SCHEMA: &str = "trust.corpora.v1";

const MAX_TABLE_BYTES: usize = 1 << 20;

/// The argument the verb adds to every compile; a row may not name it.
const OUT_DIR: &str = "--out-dir";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTable {
    schema: String,
    #[serde(default)]
    corpus: Vec<RawCorpus>,
    #[serde(default)]
    not_on_yet: Vec<RawNotOnYet>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawCorpus {
    id: String,
    glob: Option<String>,
    args: Vec<String>,
    pin: Option<Pin>,
    #[serde(default)]
    pins: BTreeMap<String, Pin>,
    #[serde(default, rename = "case")]
    cases: Vec<RawCase>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawCase {
    id: String,
    file: String,
    args: Option<Vec<String>>,
    pin: Option<Pin>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawNotOnYet {
    id: String,
    script: String,
    why: String,
}

/// One compile: a source file, the compiler's arguments, and what the corpus
/// requires of the result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Case {
    pub(crate) id: String,
    pub(crate) source: PathBuf,
    pub(crate) args: Vec<String>,
    pub(crate) pin: Option<Pin>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Corpus {
    pub(crate) id: String,
    pub(crate) cases: Vec<Case>,
}

/// A daily-driver corpus that is still a script and has no row here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NotOnYet {
    pub(crate) id: String,
    pub(crate) script: String,
    pub(crate) why: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Table {
    pub(crate) corpora: Vec<Corpus>,
    pub(crate) not_on_yet: Vec<NotOnYet>,
}

impl Table {
    fn ids(&self) -> String {
        self.corpora.iter().map(|corpus| corpus.id.as_str()).collect::<Vec<_>>().join(", ")
    }

    /// The corpora `--corpora` names, in the order given; every corpus in the
    /// table when it is absent.
    pub(crate) fn select(&self, list: Option<&str>) -> Result<Vec<&Corpus>, String> {
        let Some(list) = list else {
            return Ok(self.corpora.iter().collect());
        };
        let mut chosen: Vec<&Corpus> = Vec::new();
        for id in list.split(',') {
            if chosen.iter().any(|corpus| corpus.id == id) {
                return Err(format!("--corpora names {id} twice"));
            }
            if let Some(corpus) = self.corpora.iter().find(|corpus| corpus.id == id) {
                chosen.push(corpus);
            } else if let Some(absent) = self.not_on_yet.iter().find(|absent| absent.id == id) {
                return Err(format!(
                    "corpus {id} is not in {TABLE} yet ({}: {}); the table has: {}",
                    absent.script,
                    absent.why,
                    self.ids()
                ));
            } else {
                return Err(format!("unknown corpus: {id:?} (the table has: {})", self.ids()));
            }
        }
        Ok(chosen)
    }
}

/// Load `root`'s table and resolve every corpus to its cases.
pub(crate) fn load(root: &Path) -> Result<Table, String> {
    let text = input_limits::read_bounded_utf8_file(&root.join(TABLE), MAX_TABLE_BYTES)
        .map_err(|error| format!("cannot read it: {error}"))?;
    parse(&text, root)
}

pub(crate) fn parse(text: &str, root: &Path) -> Result<Table, String> {
    let raw: RawTable = toml::from_str(text).map_err(|error| error.to_string())?;
    if raw.schema != SCHEMA {
        return Err(format!("schema is {:?}, not {SCHEMA:?}", raw.schema));
    }
    if raw.corpus.is_empty() {
        return Err("it holds no [[corpus]]".into());
    }
    let mut seen = BTreeSet::new();
    let mut corpora = Vec::new();
    for corpus in raw.corpus {
        if !corpus_id_ok(&corpus.id) {
            return Err(format!("{:?} is not a corpus id", corpus.id));
        }
        if !seen.insert(corpus.id.clone()) {
            return Err(format!("corpus {} is declared twice", corpus.id));
        }
        corpora.push(resolve(corpus, root)?);
    }
    let mut not_on_yet = Vec::new();
    for absent in raw.not_on_yet {
        if !corpus_id_ok(&absent.id) {
            return Err(format!("not_on_yet: {:?} is not a corpus id", absent.id));
        }
        if !seen.insert(absent.id.clone()) {
            return Err(format!(
                "not_on_yet: {} is declared twice, or is a corpus of this table",
                absent.id
            ));
        }
        if absent.why.trim().is_empty() {
            return Err(format!("not_on_yet {}: `why` is empty", absent.id));
        }
        inside(&absent.script).map_err(|error| format!("not_on_yet {}: {error}", absent.id))?;
        if !root.join(&absent.script).is_file() {
            return Err(format!(
                "not_on_yet {}: there is no {} (a corpus whose script is gone has a row, or is \
                 gone too)",
                absent.id, absent.script
            ));
        }
        not_on_yet.push(NotOnYet { id: absent.id, script: absent.script, why: absent.why });
    }
    Ok(Table { corpora, not_on_yet })
}

fn resolve(raw: RawCorpus, root: &Path) -> Result<Corpus, String> {
    let id = raw.id;
    let within = |error: String| format!("corpus {id}: {error}");
    if raw.glob.is_none() && raw.cases.is_empty() {
        return Err(within("it has neither `glob` nor a [[corpus.case]]".into()));
    }
    args_ok(&raw.args).map_err(&within)?;
    let mut cases: Vec<Case> = Vec::new();
    let mut own_pin = BTreeSet::new();
    if let Some(pattern) = &raw.glob {
        for (case, source) in glob_cases(root, pattern).map_err(&within)? {
            cases.push(Case { id: case, source, args: raw.args.clone(), pin: raw.pin });
        }
    }
    for case in raw.cases {
        if !case_id_ok(&case.id) {
            return Err(within(format!("{:?} is not a case id", case.id)));
        }
        inside(&case.file).map_err(|error| within(format!("case {}: {error}", case.id)))?;
        let source = root.join(&case.file);
        if !source.is_file() {
            return Err(within(format!("case {}: there is no file {}", case.id, case.file)));
        }
        let args = match case.args {
            Some(args) => {
                args_ok(&args).map_err(|error| within(format!("case {}: {error}", case.id)))?;
                args
            }
            None => raw.args.clone(),
        };
        if case.pin.is_some() {
            own_pin.insert(case.id.clone());
        }
        cases.push(Case { id: case.id, source, args, pin: case.pin.or(raw.pin) });
    }
    let mut seen = BTreeSet::new();
    for case in &cases {
        if !seen.insert(case.id.as_str()) {
            return Err(within(format!(
                "case {} is declared twice, so its verdict would be ambiguous",
                case.id
            )));
        }
    }
    for (case, pin) in &raw.pins {
        if own_pin.contains(case) {
            return Err(within(format!("case {case} is pinned twice (`pins` and its own `pin`)")));
        }
        let Some(pinned) = cases.iter_mut().find(|candidate| candidate.id == *case) else {
            return Err(within(format!("`pins` names {case}, which is not a case")));
        };
        pinned.pin = Some(*pin);
    }
    Ok(Corpus { id, cases })
}

/// The files `pattern` matches under `root`, each with its stem as the case
/// id, in path order.
fn glob_cases(root: &Path, pattern: &str) -> Result<Vec<(String, PathBuf)>, String> {
    inside(pattern)?;
    let root = root
        .to_str()
        .ok_or_else(|| format!("the checkout's path {} is not UTF-8", root.display()))?;
    let full = format!("{}/{pattern}", glob::Pattern::escape(root));
    // A shell's rules: `*` stays inside one directory and skips dotfiles.
    let options = glob::MatchOptions {
        case_sensitive: true,
        require_literal_separator: true,
        require_literal_leading_dot: true,
    };
    let paths = glob::glob_with(&full, options)
        .map_err(|error| format!("glob {pattern:?} is not a pattern: {error}"))?;
    let mut cases = Vec::new();
    for path in paths {
        let path = path.map_err(|error| format!("glob {pattern:?}: {error}"))?;
        if !path.is_file() {
            continue;
        }
        let stem = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .filter(|stem| case_id_ok(stem))
            .ok_or_else(|| format!("glob {pattern:?}: {} names no case id", path.display()))?
            .to_owned();
        cases.push((stem, path));
    }
    if cases.is_empty() {
        return Err(format!("glob {pattern:?} matches no file"));
    }
    Ok(cases)
}

/// A path inside the checkout: relative, with no `.` or `..` component.
fn inside(value: &str) -> Result<(), String> {
    let path = Path::new(value);
    if value.is_empty()
        || path.components().any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!("{value:?} is not a path inside the checkout"));
    }
    Ok(())
}

fn args_ok(args: &[String]) -> Result<(), String> {
    match args.iter().find(|arg| *arg == OUT_DIR || arg.starts_with("--out-dir=")) {
        Some(_) => Err(format!("`args` names {OUT_DIR}, which the verb sets")),
        None => Ok(()),
    }
}

fn corpus_id_ok(id: &str) -> bool {
    !id.is_empty()
        && id
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || matches!(c, '-' | '_'))
}

/// A case id names its log under the side's directory, so each `/`-separated
/// part is a plain file name.
fn case_id_ok(id: &str) -> bool {
    id.split('/').all(|part| {
        !part.is_empty()
            && !matches!(part, "." | "..")
            && part
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '@' | '+' | '-'))
    })
}
