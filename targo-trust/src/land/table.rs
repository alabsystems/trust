//! `gates/land.toml` (schema `trust.land-rows.v1`): the landing gate's row
//! table. The file's own header describes each key.
//!
//! Two programs read this table until the Python gate goes: this reader and
//! `scripts/lib/land_select.py` (`parse_land_rows`, `read_land_rows_text`,
//! `land_rows_coverage`). They accept the same tables and refuse the same
//! tables; `targo-trust/tests/fixtures/land_select_cases.json` holds both to
//! that. Each rule below names the Python rule it mirrors by its message.
//!
//! The table is read whole and refused whole: a table that breaks a rule
//! selects nothing, never fewer rows.
//!
//! Three limits are this reader's own. A table over [`MAX_TABLE_BYTES`] is
//! refused, where the Python reader has no bound. A table that opens with a
//! byte-order mark is refused before it is parsed, as `tomllib` refuses it.
//! What is TOML at all is each parser's answer (`toml` here, `tomllib` there).

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use toml::Value;

use crate::input_limits;

/// The table's path in a checkout.
pub(crate) const TABLE: &str = "gates/land.toml";
pub(crate) const SCHEMA: &str = "trust.land-rows.v1";
/// The Python reader. A change to the table selects what a change to this
/// file selects (`land_select.validation_program_tests`).
pub(crate) const READER: &str = "scripts/lib/land_select.py";
/// The argv of a validation row, less its module: the one command either
/// reader knows.
pub(crate) const RUNNER: [&str; 4] = ["python3", "-B", "scripts/land_gate.py", "validation-tests"];
/// The program a row's command starts once it is a targo verb or a test
/// target. No row is one yet.
pub(crate) const TARGO: &str = "targo";

const ID_PREFIX: &str = "validation.";
const MAX_TABLE_BYTES: usize = 16 << 20;

/// Why a covered file has no row.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum NotRunKind {
    Red,
    Unjudgeable,
}

impl NotRunKind {
    pub(crate) const ALL: [Self; 2] = [Self::Red, Self::Unjudgeable];

    pub(crate) fn word(self) -> &'static str {
        match self {
            Self::Red => "red",
            Self::Unjudgeable => "unjudgeable",
        }
    }
}

/// One check: the command that judges it and the paths whose change selects
/// it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) id: String,
    /// The tracked file of the module the command runs.
    pub(crate) file: String,
    pub(crate) command: Vec<String>,
    pub(crate) selects_on: Vec<String>,
    pub(crate) catches: String,
    pub(crate) not_yet_targo: String,
}

impl Row {
    /// Whether the command is a targo verb or a test target (section 5, rule
    /// 1 of the live-edit-loop design). No row is, yet.
    pub(crate) fn is_targo(&self) -> bool {
        self.command.first().is_some_and(|program| program == TARGO)
    }
}

/// A covered file that nothing selects, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NotRun {
    pub(crate) id: String,
    pub(crate) path: String,
    pub(crate) kind: NotRunKind,
    pub(crate) why: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Table {
    pub(crate) covered: Vec<String>,
    /// Sorted by id.
    pub(crate) rows: Vec<Row>,
    /// Sorted by id.
    pub(crate) not_run: Vec<NotRun>,
    /// `[validation_programs]`: path -> the ids of its rows, as listed.
    pub(crate) programs: BTreeMap<String, Vec<String>>,
}

impl Table {
    pub(crate) fn row(&self, id: &str) -> Option<&Row> {
        self.rows.binary_search_by(|row| row.id.as_str().cmp(id)).ok().map(|at| &self.rows[at])
    }

    /// The ids of the rows whose `selects_on` names `path`, in id order.
    pub(crate) fn selected_by<'a>(&'a self, path: &'a str) -> impl Iterator<Item = &'a str> + 'a {
        self.rows
            .iter()
            .filter(move |row| {
                row.selects_on.binary_search_by(|listed| listed.as_str().cmp(path)).is_ok()
            })
            .map(|row| row.id.as_str())
    }

    /// What breaks the table's `covered` rule in a tree that tracks `tracked`
    /// (`land_select.land_rows_coverage`, message for message): a covered file
    /// that is not exactly one `[[row]]` or exactly one `[[not_run]]`, and an
    /// entry whose file the tree does not track. Empty when the rule holds.
    pub(crate) fn coverage(&self, tracked: &BTreeSet<String>) -> Vec<String> {
        let mut owners: BTreeMap<&str, Vec<String>> = BTreeMap::new();
        for row in &self.rows {
            owners.entry(&row.file).or_default().push(format!("[[row]] {}", row.id));
        }
        for entry in &self.not_run {
            owners.entry(&entry.path).or_default().push(format!("[[not_run]] {}", entry.id));
        }
        let mut problems = Vec::new();
        for path in tracked {
            if !self.covered.iter().any(|pattern| covered_match(path, pattern)) {
                continue;
            }
            match owners.get(path.as_str()).map(Vec::as_slice) {
                None | Some([]) => {
                    problems.push(format!("{path}: neither a [[row]] nor a [[not_run]]"));
                }
                Some([_]) => {}
                Some(mine) => problems
                    .push(format!("{path}: {} (exactly one, never both)", mine.join(" and "))),
            }
        }
        for (path, mine) in &owners {
            if !tracked.contains(*path) {
                problems.push(format!("{}: {path} is not a tracked file", mine[0]));
            }
        }
        problems
    }
}

/// Load `root`'s table.
pub(crate) fn load(root: &Path) -> Result<Table, String> {
    parse(&read_text(root)?)
}

/// The table's text under `root`, read only from a regular file reached
/// through real directories (`land_select.read_land_rows_text`): git can track
/// a symbolic link at either name, and a link's target is a file the gate
/// neither hashes nor watches.
pub(crate) fn read_text(root: &Path) -> Result<String, String> {
    let parts: Vec<&str> = TABLE.split('/').collect();
    let mut here = root.to_path_buf();
    for (position, part) in parts.iter().enumerate() {
        here.push(part);
        let name = parts[..=position].join("/");
        let kind = fs::symlink_metadata(&here)
            .map_err(|error| format!("cannot read {name} under {}: {error}", root.display()))?
            .file_type();
        let last = position + 1 == parts.len();
        if kind.is_symlink() {
            return Err(format!(
                "{name} is a symbolic link under {}; the row table is read only from a regular \
                 file in a real directory (the gate hashes and watches this path, not a link's \
                 target)",
                root.display()
            ));
        }
        if !last && !kind.is_dir() {
            return Err(format!("{name} is not a directory under {}", root.display()));
        }
        if last && !kind.is_file() {
            return Err(format!("{name} is not a regular file under {}", root.display()));
        }
    }
    // The bounded reader opens without following a link and re-checks that
    // what it opened is the regular file the check above saw.
    input_limits::read_bounded_utf8_file(&here, MAX_TABLE_BYTES)
        .map_err(|error| format!("cannot read {TABLE} under {}: {error}", root.display()))
}

/// The row table from its text, or the first rule it breaks
/// (`land_select.parse_land_rows`). Pure: the rule that needs the tree is
/// [`Table::coverage`].
pub(crate) fn parse(text: &str) -> Result<Table, String> {
    if text.starts_with('\u{feff}') {
        return Err("not TOML: it opens with a byte-order mark".into());
    }
    let document: toml::Table = text.parse().map_err(|error| format!("not TOML: {error}"))?;
    let document = Value::Table(document);
    let top = fields(
        "the table",
        &document,
        &[
            ("schema", Kind::Str),
            ("covered", Kind::Array),
            ("validation_programs", Kind::Table),
            ("row", Kind::Array),
            ("not_run", Kind::Array),
        ],
    )?;
    let schema = text_of(&top["schema"]);
    if schema != SCHEMA {
        return Err(format!("schema is {schema:?}; this reader knows {SCHEMA:?}"));
    }
    let covered = strings("covered", array_of(&top["covered"]), true)?;

    let mut rows = Vec::new();
    for (id, name, entry) in ids(
        "row",
        array_of(&top["row"]),
        &[
            ("id", Kind::Str),
            ("command", Kind::Array),
            ("selects_on", Kind::Array),
            ("catches", Kind::Str),
            ("not_yet_targo", Kind::Str),
        ],
    )? {
        let within = format!("[[row]] {id}");
        let module = format!("scripts.tests.{name}");
        let runner: Vec<&str> = RUNNER.iter().copied().chain([module.as_str()]).collect();
        let command: Option<Vec<&str>> =
            array_of(&entry["command"]).iter().map(Value::as_str).collect();
        if command.as_deref() != Some(runner.as_slice()) {
            return Err(format!(
                "{within}: command is not this row's validation runner {runner:?} (the one \
                 command this reader and {READER} know)"
            ));
        }
        let listed = array_of(&entry["selects_on"]);
        if listed.is_empty() {
            return Err(format!(
                "{within}: empty selects_on (a row no path selects never runs: declare what \
                 selects it, or move it to [[not_run]] with the reason)"
            ));
        }
        let selects_on = strings(&format!("{within}: selects_on"), listed, true)?;
        let catches = text_of(&entry["catches"]);
        if blank(catches) {
            return Err(format!(
                "{within}: empty catches (say what defect the row exists to catch)"
            ));
        }
        let not_yet_targo = text_of(&entry["not_yet_targo"]);
        if blank(not_yet_targo) {
            return Err(format!(
                "{within}: empty not_yet_targo (the command is not a targo verb or a test \
                 target; say why not yet)"
            ));
        }
        rows.push(Row {
            file: format!("scripts/tests/{name}.py"),
            command: runner.iter().map(|part| (*part).to_owned()).collect(),
            selects_on,
            catches: catches.to_owned(),
            not_yet_targo: not_yet_targo.to_owned(),
            id,
        });
    }

    let mut not_run = Vec::new();
    for (id, name, entry) in ids(
        "not_run",
        array_of(&top["not_run"]),
        &[("id", Kind::Str), ("path", Kind::Str), ("kind", Kind::Str), ("why", Kind::Str)],
    )? {
        let within = format!("[[not_run]] {id}");
        if rows.binary_search_by(|row| row.id.cmp(&id)).is_ok() {
            return Err(format!(
                "{within}: also a [[row]] (a module is one or the other, never both)"
            ));
        }
        let path = text_of(&entry["path"]);
        let file = format!("scripts/tests/{name}.py");
        if path != file {
            return Err(format!("{within}: path is {path:?}, not its module's file {file:?}"));
        }
        let word = text_of(&entry["kind"]);
        let Some(kind) = NotRunKind::ALL.into_iter().find(|kind| kind.word() == word) else {
            return Err(format!("{within}: kind is {word:?}, not one of red, unjudgeable"));
        };
        let why = text_of(&entry["why"]);
        if blank(why) {
            return Err(format!("{within}: empty why"));
        }
        not_run.push(NotRun { id, path: file, kind, why: why.to_owned() });
    }

    let mut table = Table { covered, rows, not_run, programs: BTreeMap::new() };
    for (path, listed) in table_of(&top["validation_programs"]) {
        let within = format!("validation_programs {path:?}");
        let Some(listed) = listed.as_array() else {
            return Err(format!("{within}: not an array of row ids"));
        };
        let ids = strings(&within, listed, false)?;
        if let Some(unknown) = ids.iter().find(|id| table.row(id).is_none()) {
            return Err(format!("{within}: {unknown} is not a [[row]]"));
        }
        let named: BTreeSet<&str> = ids.iter().map(String::as_str).collect();
        let selecting: BTreeSet<&str> = table.selected_by(path).collect();
        if named != selecting {
            let differ: Vec<&str> = named.symmetric_difference(&selecting).copied().collect();
            return Err(format!(
                "{within}: its rows are not exactly the rows whose selects_on names the path \
                 ({} is in one and not the other)",
                differ.join(", ")
            ));
        }
        table.programs.insert(path.clone(), ids);
    }
    Ok(table)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Str,
    Array,
    Table,
}

impl Kind {
    fn of(value: &Value) -> Option<Self> {
        match value {
            Value::String(_) => Some(Self::Str),
            Value::Array(_) => Some(Self::Array),
            Value::Table(_) => Some(Self::Table),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Str => "a string",
            Self::Array => "an array",
            Self::Table => "a table",
        }
    }
}

/// `value` as a table holding exactly `spec`'s keys, each of its kind.
fn fields<'a>(
    within: &str,
    value: &'a Value,
    spec: &[(&str, Kind)],
) -> Result<&'a toml::Table, String> {
    let Value::Table(table) = value else {
        return Err(format!("{within}: not a table"));
    };
    let unknown: Vec<String> = table
        .keys()
        .filter(|key| !spec.iter().any(|(known, _)| known == key))
        .map(|key| format!("{key:?}"))
        .collect();
    if !unknown.is_empty() {
        let known: Vec<&str> = spec.iter().map(|(key, _)| *key).collect();
        return Err(format!(
            "{within}: unknown key {} (this reader knows {})",
            unknown.join(", "),
            known.join(", ")
        ));
    }
    for (key, kind) in spec {
        let Some(found) = table.get(*key) else {
            let hint = if *key == "not_yet_targo" {
                " (required while the command's argv[0] is not `targo`: say why the row is not \
                 yet a targo verb or a test target)"
            } else {
                ""
            };
            return Err(format!("{within}: missing key {key:?}{hint}"));
        };
        if Kind::of(found) != Some(*kind) {
            return Err(format!("{within}: {key} is not {}", kind.name()));
        }
    }
    Ok(table)
}

/// A value [`fields`] found to be a string.
fn text_of(value: &Value) -> &str {
    value.as_str().unwrap_or_default()
}

/// A value [`fields`] found to be an array.
fn array_of(value: &Value) -> &[Value] {
    value.as_array().map_or(&[], Vec::as_slice)
}

/// A value [`fields`] found to be a table.
fn table_of(value: &Value) -> impl Iterator<Item = (&String, &Value)> {
    value.as_table().into_iter().flatten()
}

/// A non-empty array of non-empty strings without a repeat; sorted, when
/// `ordered`.
fn strings(within: &str, values: &[Value], ordered: bool) -> Result<Vec<String>, String> {
    if values.is_empty() {
        return Err(format!("{within}: empty"));
    }
    let mut out: Vec<String> = Vec::with_capacity(values.len());
    for value in values {
        match value.as_str() {
            Some(text) if !blank(text) => out.push(text.to_owned()),
            _ => return Err(format!("{within}: {value} is not a non-empty string")),
        }
    }
    let mut seen = BTreeSet::new();
    let mut repeated = BTreeSet::new();
    for text in &out {
        if !seen.insert(text.as_str()) {
            repeated.insert(text.as_str());
        }
    }
    if let Some(twice) = repeated.first() {
        return Err(format!("{within}: {twice:?} is listed twice"));
    }
    if ordered {
        if let Some(pair) = out.windows(2).find(|pair| pair[1] < pair[0]) {
            return Err(format!("{within}: not sorted ({:?} is out of order)", pair[1]));
        }
    }
    Ok(out)
}

/// `(id, module name, entry)` of each `[[kind]]` entry: known keys, and ids
/// that are well formed, unique and sorted.
fn ids<'a>(
    kind: &str,
    entries: &'a [Value],
    spec: &[(&str, Kind)],
) -> Result<Vec<(String, &'a str, &'a toml::Table)>, String> {
    let mut out: Vec<(String, &str, &toml::Table)> = Vec::new();
    let mut seen = BTreeSet::new();
    for (position, entry) in entries.iter().enumerate() {
        let Some(id) = entry.as_table().and_then(|table| table.get("id")).and_then(Value::as_str)
        else {
            return Err(format!("[[{kind}]] #{}: no string id", position + 1));
        };
        let within = format!("[[{kind}]] {id}");
        let entry = fields(&within, entry, spec)?;
        let Some(name) = module_name(id) else {
            return Err(format!(
                "{within}: the id is not validation.<module> (the one kind of row this reader \
                 knows)"
            ));
        };
        if !seen.insert(id) {
            return Err(format!("{within}: duplicate id"));
        }
        if let Some((before, _, _)) = out.last() {
            if id < before.as_str() {
                return Err(format!("{within}: ids are not sorted (it follows {before})"));
            }
        }
        out.push((id.to_owned(), name, entry));
    }
    Ok(out)
}

/// `<module>` of `validation.<module>`: a Python identifier in ASCII.
fn module_name(id: &str) -> Option<&str> {
    let name = id.strip_prefix(ID_PREFIX)?;
    let mut characters = name.chars();
    let first = characters.next()?;
    let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
    ((first.is_ascii_alphabetic() || first == '_') && characters.all(word)).then_some(name)
}

/// Whether Python's `str.strip()` leaves nothing of `text`: the rule both
/// readers hold a required text to.
pub(crate) fn blank(text: &str) -> bool {
    text.chars().all(python_space)
}

/// Python's `str.isspace` for one character: Unicode `White_Space`, and the
/// four information separators Python also strips.
pub(crate) fn python_space(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}

/// A `covered` glob against a path (`land_select._covered_match`): matched a
/// component at a time, so `*` stays inside one.
pub(crate) fn covered_match(path: &str, pattern: &str) -> bool {
    let parts: Vec<&str> = path.split('/').collect();
    let wanted: Vec<&str> = pattern.split('/').collect();
    parts.len() == wanted.len()
        && parts.iter().zip(&wanted).all(|(part, glob)| {
            let name: Vec<char> = part.chars().collect();
            let glob: Vec<char> = glob.chars().collect();
            glob_match(&glob, &name)
        })
}

/// One piece of a glob, as Python's `fnmatch.translate` reads it.
enum Piece {
    Star,
    Any,
    Literal(char),
    /// A bracket class: its ranges, and whether it is negated. With no range
    /// and no negation it matches nothing.
    Class(Vec<(char, char)>, bool),
}

/// Python's `fnmatch.fnmatchcase`: `*`, `?`, `[seq]`, `[!seq]`; everything
/// else is itself, an unclosed `[` included.
fn glob_match(pattern: &[char], name: &[char]) -> bool {
    let pieces = glob_pieces(pattern);
    // reach[i]: the pieces so far can match exactly the first i characters.
    let mut reach = vec![false; name.len() + 1];
    reach[0] = true;
    for piece in &pieces {
        let mut next = vec![false; name.len() + 1];
        match piece {
            Piece::Star => {
                let mut open = false;
                for (at, reached) in reach.iter().enumerate() {
                    open |= *reached;
                    next[at] = open;
                }
            }
            one => {
                for (at, c) in name.iter().enumerate() {
                    next[at + 1] = reach[at]
                        && match one {
                            Piece::Any => true,
                            Piece::Literal(literal) => literal == c,
                            Piece::Class(ranges, negated) => {
                                ranges.iter().any(|(low, high)| low <= c && c <= high) != *negated
                            }
                            Piece::Star => false,
                        };
                }
            }
        }
        reach = next;
    }
    reach[name.len()]
}

fn glob_pieces(pattern: &[char]) -> Vec<Piece> {
    let mut pieces = Vec::new();
    let mut at = 0;
    while at < pattern.len() {
        let c = pattern[at];
        at += 1;
        match c {
            '*' => pieces.push(Piece::Star),
            '?' => pieces.push(Piece::Any),
            '[' => {
                // The class closes at the first `]` that is not its first
                // character (after a `!`).
                let mut close = at;
                if pattern.get(close) == Some(&'!') {
                    close += 1;
                }
                if pattern.get(close) == Some(&']') {
                    close += 1;
                }
                while close < pattern.len() && pattern[close] != ']' {
                    close += 1;
                }
                if close >= pattern.len() {
                    pieces.push(Piece::Literal('['));
                    continue;
                }
                pieces.push(class_piece(&pattern[at..close]));
                at = close + 1;
            }
            literal => pieces.push(Piece::Literal(literal)),
        }
    }
    pieces
}

/// One sign of a bracket class's text once its ranges are known.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Sign {
    Char(char),
    /// The hyphen of a range: the signs on either side are its ends.
    Through,
}

/// A bracket class from the text between its brackets, in the order
/// `fnmatch.translate` reads it. The order is the rule: the ranges are found
/// first, a range whose ends are out of order is then dropped with both its
/// ends, and only what is left says whether the class is negated. So `[b-a!x]`
/// is "any character but x" and `[z-a!]` is "any character", though neither
/// is written with a leading `!`.
fn class_piece(body: &[char]) -> Piece {
    // Cut the text at each hyphen that makes a range: the first one at or
    // after the second character (the third, when the text opens with `!`),
    // and then the first one at least three characters past the hyphen before.
    let mut chunks: Vec<Vec<char>> = Vec::new();
    let mut start = 0;
    let mut from = if body.first() == Some(&'!') { 2 } else { 1 };
    while let Some(hyphen) = (from..body.len()).find(|at| body[*at] == '-') {
        chunks.push(body[start..hyphen].to_vec());
        start = hyphen + 1;
        from = hyphen + 3;
    }
    if start < body.len() {
        chunks.push(body[start..].to_vec());
    } else if let Some(last) = chunks.last_mut() {
        // The text ends in a hyphen with nothing to reach: it is itself.
        last.push('-');
    }
    // A range runs from the last character of one chunk to the first of the
    // next. From the last range to the first, one whose ends are out of order
    // goes, and the two chunks become one without those ends.
    for next in (1..chunks.len()).rev() {
        let (Some(low), Some(high)) = (chunks[next - 1].last(), chunks[next].first()) else {
            continue;
        };
        if low > high {
            let tail = chunks.remove(next);
            let head = &mut chunks[next - 1];
            head.pop();
            head.extend_from_slice(&tail[1..]);
        }
    }
    let mut stuff: Vec<Sign> = Vec::new();
    for (position, chunk) in chunks.iter().enumerate() {
        if position > 0 {
            stuff.push(Sign::Through);
        }
        stuff.extend(chunk.iter().map(|c| Sign::Char(*c)));
    }
    // Nothing left matches nothing; a lone `!` negates nothing, which is any
    // character; any other leading `!` negates the rest.
    let negated = match stuff.as_slice() {
        [] => return Piece::Class(Vec::new(), false),
        [Sign::Char('!')] => return Piece::Any,
        [first, ..] => *first == Sign::Char('!'),
    };
    let mut rest = &stuff[usize::from(negated)..];
    let mut ranges = Vec::new();
    while let [first, after @ ..] = rest {
        rest = match (first, after) {
            (Sign::Char(low), [Sign::Through, Sign::Char(high), beyond @ ..]) => {
                ranges.push((*low, *high));
                beyond
            }
            (Sign::Char(c), _) => {
                ranges.push((*c, *c));
                after
            }
            // A range whose first end was the `!` that negates the class
            // (`[b-a!-z]` leaves `!-z`): a hyphen that opens a class is a
            // hyphen.
            (Sign::Through, _) => {
                ranges.push(('-', '-'));
                after
            }
        };
    }
    Piece::Class(ranges, negated)
}
