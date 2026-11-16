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
use super::headers::{self, Dialect};
use super::run::SCRUBBED_ENV;
use crate::input_limits;

/// The table's path in a checkout.
pub(crate) const TABLE: &str = "tests/corpora.toml";
pub(crate) const SCHEMA: &str = "trust.corpora.v1";

const MAX_TABLE_BYTES: usize = 1 << 20;
/// The largest case file a `headers` group reads its row from.
const MAX_HEADED_FILE_BYTES: usize = 1 << 20;
/// The longest text a row may ask a compile's output to hold, in bytes.
const MAX_NEEDLE_BYTES: usize = 512;

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
    args: Option<Vec<String>>,
    pin: Option<Pin>,
    #[serde(default)]
    pins: BTreeMap<String, Pin>,
    conditional: Option<RawConditional>,
    #[serde(default, rename = "group")]
    groups: Vec<RawGroup>,
    #[serde(default, rename = "case")]
    cases: Vec<RawCase>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawConditional {
    disclosure: String,
    certify_args: Vec<String>,
    certify_refusal: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawGroup {
    glob: String,
    args: Vec<String>,
    #[serde(default)]
    env: BTreeMap<String, String>,
    ids_under: Option<String>,
    headers: Option<Dialect>,
    dependencies: Option<String>,
    dependency_args: Option<Vec<String>>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawCase {
    id: String,
    file: String,
    args: Option<Vec<String>>,
    pin: Option<Pin>,
    log_contains: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawNotOnYet {
    id: String,
    script: String,
    why: String,
}

/// One case: a source file, the compiler's arguments, and what the corpus
/// requires of the result (`judge` has what each field asks of a compile).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Case {
    pub(crate) id: String,
    pub(crate) source: PathBuf,
    pub(crate) args: Vec<String>,
    pub(crate) pin: Option<Pin>,
    /// Variables the case's compile is given.
    pub(crate) env: Vec<(String, String)>,
    /// A text the compile's output must hold for the case to be as pinned: its
    /// own, or its corpus's disclosure where it is pinned `conditional` and
    /// has none.
    pub(crate) log_contains: Option<String>,
    /// The second compile of a case pinned `conditional`.
    pub(crate) certify: Option<Certify>,
    /// The crate the case is built against.
    pub(crate) dependency: Option<DependencyUse>,
}

/// The certify compile of a case pinned `conditional`: the case's own
/// arguments and these, and the text its output must hold when it refuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Certify {
    pub(crate) args: Vec<String>,
    pub(crate) refusal: String,
}

/// A case's use of one of its corpus's dependencies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DependencyUse {
    /// [`Dependency::name`].
    pub(crate) name: String,
    /// The case's arguments after the dependency's (`--extern`, `-L`).
    pub(crate) then_args: Vec<String>,
}

/// A crate some cases are built against. It is built once for a side, before
/// the first case that uses it, and is not a case.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Dependency {
    /// The crate's name: its file's stem.
    pub(crate) name: String,
    /// What the report and the logs call it: a case id's form.
    pub(crate) id: String,
    pub(crate) source: PathBuf,
    pub(crate) args: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Corpus {
    pub(crate) id: String,
    pub(crate) cases: Vec<Case>,
    pub(crate) dependencies: Vec<Dependency>,
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
    if raw.glob.is_none() && raw.groups.is_empty() && raw.cases.is_empty() {
        return Err(within(
            "it has neither `glob` nor a [[corpus.group]] nor a [[corpus.case]]".into(),
        ));
    }
    if let Some(args) = &raw.args {
        args_ok(args).map_err(&within)?;
    }
    let plain = |id: String, source: PathBuf, args: Vec<String>, pin: Option<Pin>| Case {
        id,
        source,
        args,
        pin,
        env: Vec::new(),
        log_contains: None,
        certify: None,
        dependency: None,
    };
    let mut cases: Vec<Case> = Vec::new();
    let mut dependencies: Vec<Dependency> = Vec::new();
    // The cases whose pin is their own: `pins` may not name one.
    let mut own_pin = BTreeSet::new();
    if let Some(pattern) = &raw.glob {
        let args = raw.args.as_ref().ok_or_else(|| within("`glob` needs `args`".into()))?;
        for (case, source) in glob_cases(root, pattern, None).map_err(&within)? {
            cases.push(plain(case, source, args.clone(), raw.pin));
        }
    }
    for group in raw.groups {
        let pattern = group.glob.clone();
        let (found, built) = resolve_group(group, raw.pin, root)
            .map_err(|error| within(format!("group {pattern:?}: {error}")))?;
        for (case, headed) in found {
            if headed {
                own_pin.insert(case.id.clone());
            }
            cases.push(case);
        }
        for dependency in built {
            if dependencies.iter().any(|other| other.name == dependency.name) {
                return Err(within(format!(
                    "group {pattern:?}: dependency {} is declared twice",
                    dependency.name
                )));
            }
            dependencies.push(dependency);
        }
    }
    for case in raw.cases {
        if !case_id_ok(&case.id) {
            return Err(within(format!("{:?} is not a case id", case.id)));
        }
        let of_case = |error: String| within(format!("case {}: {error}", case.id));
        inside(&case.file).map_err(&of_case)?;
        let source = root.join(&case.file);
        if !source.is_file() {
            return Err(of_case(format!("there is no file {}", case.file)));
        }
        let args = match case.args {
            Some(args) => {
                args_ok(&args).map_err(&of_case)?;
                args
            }
            None => raw
                .args
                .clone()
                .ok_or_else(|| of_case("it has no `args`, and neither has its corpus".into()))?,
        };
        if case.pin.is_some() {
            own_pin.insert(case.id.clone());
        }
        if let Some(needle) = &case.log_contains {
            needle_ok(needle).map_err(&of_case)?;
        }
        let mut resolved = plain(case.id, source, args, case.pin.or(raw.pin));
        resolved.log_contains = case.log_contains;
        cases.push(resolved);
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
    if let Some(case) = cases.iter().find(|case| case.log_contains.is_some() && case.pin.is_none())
    {
        return Err(within(format!(
            "case {} has `log_contains` and no pin: the text is what makes a pinned verdict the \
             pinned one",
            case.id
        )));
    }
    for dependency in &dependencies {
        let used =
            |case: &Case| case.dependency.as_ref().is_some_and(|used| used.name == dependency.name);
        if !cases.iter().any(used) {
            return Err(within(format!(
                "dependency {} is built for no case; a dependency nothing is built against has \
                 no row to answer for it",
                dependency.id
            )));
        }
    }
    conditional(&mut cases, raw.conditional).map_err(&within)?;
    Ok(Corpus { id, cases, dependencies })
}

/// A group's cases, each with whether its pin is its own (read from its
/// file), and the dependencies the group builds them against.
fn resolve_group(
    group: RawGroup,
    corpus_pin: Option<Pin>,
    root: &Path,
) -> Result<(Vec<(Case, bool)>, Vec<Dependency>), String> {
    args_ok(&group.args)?;
    let env = env_ok(group.env)?;
    let under = match &group.ids_under {
        Some(directory) => {
            inside(directory).map_err(|error| format!("`ids_under`: {error}"))?;
            Some(root.join(directory))
        }
        None => None,
    };
    let xcrate = group.headers == Some(Dialect::LadderXcrate);
    let mut dependencies = Vec::new();
    match (&group.dependencies, &group.dependency_args) {
        (Some(pattern), Some(args)) if xcrate => {
            args_ok(args).map_err(|error| format!("`dependency_args`: {error}"))?;
            for (dependency, source) in glob_cases(root, pattern, under.as_deref())? {
                let name = file_stem(&source, pattern)?;
                let text = read_headed(&source, &dependency)?;
                let mut args = args.clone();
                args.extend(headers::dependency_flags(&text));
                args_ok(&args).map_err(|error| format!("dependency {dependency}: {error}"))?;
                dependencies.push(Dependency { name, id: dependency, source, args });
            }
        }
        (None, None) if !xcrate => {}
        _ => {
            return Err(format!(
                "`dependencies` and `dependency_args` go with `headers = {:?}`, both or neither",
                Dialect::LadderXcrate.pin_header()
            ));
        }
    }
    let mut cases = Vec::new();
    for (id, source) in glob_cases(root, &group.glob, under.as_deref())? {
        let mut case = Case {
            id,
            source,
            args: group.args.clone(),
            pin: corpus_pin,
            env: env.clone(),
            log_contains: None,
            certify: None,
            dependency: None,
        };
        let Some(dialect) = group.headers else {
            cases.push((case, false));
            continue;
        };
        let id = case.id.clone();
        let of_case = |error: String| format!("case {id}: {error}");
        let row = headers::row(dialect, &read_headed(&case.source, &id)?).map_err(&of_case)?;
        if let Some(needle) = &row.log_contains {
            needle_ok(needle).map_err(&of_case)?;
        }
        if let Some((name, _)) = &row.dependency {
            if !dependencies.iter().any(|dependency| dependency.name == *name) {
                return Err(of_case(format!(
                    "it is built against {name}, and `dependencies` matches no {name}.rs"
                )));
            }
        }
        args_ok(&row.args).map_err(&of_case)?;
        case.args.extend(row.args);
        case.pin = Some(row.pin);
        case.log_contains = row.log_contains;
        case.dependency = row.dependency.map(|(name, then_args)| DependencyUse { name, then_args });
        cases.push((case, true));
    }
    Ok((cases, dependencies))
}

/// Give every case pinned `conditional` its disclosure and its certify
/// compile. The corpus's `[corpus.conditional]` and such a case go together:
/// either without the other is refused.
fn conditional(cases: &mut [Case], raw: Option<RawConditional>) -> Result<(), String> {
    let pinned = cases.iter().any(|case| case.pin == Some(Pin::Conditional));
    let Some(raw) = raw else {
        return match cases.iter().find(|case| case.pin == Some(Pin::Conditional)) {
            Some(case) => Err(format!(
                "case {} is pinned conditional, and the corpus has no [corpus.conditional] to \
                 say what that asks",
                case.id
            )),
            None => Ok(()),
        };
    };
    if !pinned {
        return Err("it has a [corpus.conditional] and no case pinned conditional".into());
    }
    needle_ok(&raw.disclosure)
        .map_err(|error| format!("[corpus.conditional] disclosure: {error}"))?;
    needle_ok(&raw.certify_refusal)
        .map_err(|error| format!("[corpus.conditional] certify_refusal: {error}"))?;
    if raw.certify_args.is_empty() {
        return Err("[corpus.conditional] certify_args is empty, so the certify compile would be \
                    the compile it is to differ from"
            .into());
    }
    args_ok(&raw.certify_args).map_err(|error| format!("[corpus.conditional]: {error}"))?;
    for case in cases.iter_mut().filter(|case| case.pin == Some(Pin::Conditional)) {
        case.log_contains.get_or_insert_with(|| raw.disclosure.clone());
        case.certify =
            Some(Certify { args: raw.certify_args.clone(), refusal: raw.certify_refusal.clone() });
    }
    Ok(())
}

/// The contents of a file that states its own row or flags.
fn read_headed(source: &Path, id: &str) -> Result<String, String> {
    input_limits::read_bounded_utf8_file(source, MAX_HEADED_FILE_BYTES)
        .map_err(|error| format!("case {id}: cannot read its headers: {error}"))
}

fn file_stem(path: &Path, pattern: &str) -> Result<String, String> {
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .filter(|stem| case_id_ok(stem) && !stem.contains('/'))
        .map(str::to_owned)
        .ok_or_else(|| format!("glob {pattern:?}: {} names no case id", path.display()))
}

/// The files `pattern` matches under `root`, in path order, each with its case
/// id: its path under `under` without its extension, or its stem when there is
/// no `under`.
fn glob_cases(
    root: &Path,
    pattern: &str,
    under: Option<&Path>,
) -> Result<Vec<(String, PathBuf)>, String> {
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
        let id = match under {
            None => file_stem(&path, pattern)?,
            Some(under) => path
                .strip_prefix(under)
                .ok()
                .map(|relative| relative.with_extension(""))
                .and_then(|relative| relative.to_str().map(str::to_owned))
                .filter(|id| case_id_ok(id))
                .ok_or_else(|| {
                    format!(
                        "glob {pattern:?}: {} names no case id under `ids_under`",
                        path.display()
                    )
                })?,
        };
        cases.push((id, path));
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

/// A text a compile's output is searched for: it is on one line, as the
/// corpus scripts' `grep -F` reads a log.
fn needle_ok(needle: &str) -> Result<(), String> {
    if needle.is_empty() {
        return Err("the text its output must hold is empty".into());
    }
    if needle.contains(['\n', '\r']) {
        return Err("the text its output must hold spans a line".into());
    }
    if needle.len() > MAX_NEEDLE_BYTES {
        return Err(format!("the text its output must hold is over {MAX_NEEDLE_BYTES} bytes"));
    }
    Ok(())
}

/// A group's `env`, as the pairs a compile is given.
fn env_ok(env: BTreeMap<String, String>) -> Result<Vec<(String, String)>, String> {
    for (name, value) in &env {
        if name.is_empty() || name.contains(['=', '\0']) || value.contains('\0') {
            return Err(format!("`env`: {name:?} is not a variable a process can be given"));
        }
        if SCRUBBED_ENV.contains(&name.as_str()) {
            return Err(format!("`env` names {name}, which the verb removes from every compile"));
        }
    }
    Ok(env.into_iter().collect())
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
