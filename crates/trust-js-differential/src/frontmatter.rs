// Tolerant hand-rolled parser for test262 YAML frontmatter (the block between
// the FIRST "/*---" and the following "---*/"). Extracts exactly the keys the
// harness consumes — flags / features / includes (flow or block lists) and
// negative (block map {phase, type}) — skipping everything else (description,
// info block scalars, esid, ...). Fail-closed: a file whose flags / features /
// includes / negative cannot be parsed is a HarnessError at the consumer,
// never a silent skip.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// The `negative:` expectation of a test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Negative {
    pub phase: String,
    pub type_name: String,
}

/// The parsed frontmatter keys the harness consumes. A file with no
/// frontmatter block has empty flags/features/includes and no negative.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Frontmatter {
    pub flags: Vec<String>,
    pub features: Vec<String>,
    pub includes: Vec<String>,
    pub negative: Option<Negative>,
}

impl Frontmatter {
    pub fn has_flag(&self, flag: &str) -> bool {
        self.flags.iter().any(|f| f == flag)
    }
}

fn strip_quotes(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 && ((b[0] == b'"' && b[b.len() - 1] == b'"') || (b[0] == b'\'' && b[b.len() - 1] == b'\'')) {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

fn is_indented(line: &str) -> bool {
    line.starts_with(' ') || line.starts_with('\t')
}

/// Parse a flow (`[a, b]`, possibly spanning lines) or block (`- item`) list
/// value. Returns the items and the index of the first unconsumed line.
fn parse_list(lines: &[String], i: usize, rest: &str, key: &str) -> Result<(Vec<String>, usize), String> {
    if rest.starts_with('[') {
        let mut acc = rest.to_string();
        let mut j = i;
        while !acc.contains(']') {
            j += 1;
            if j >= lines.len() {
                return Err(format!("{key}: unterminated flow list"));
            }
            acc.push(' ');
            acc.push_str(lines[j].trim());
        }
        let open = acc.find('[').expect("starts with [");
        let close = acc.rfind(']').expect("contains ]");
        if close < open {
            return Err(format!("{key}: malformed flow list {acc:?}"));
        }
        let items = acc[open + 1..close]
            .split(',')
            .map(|s| strip_quotes(s.trim()).to_string())
            .filter(|s| !s.is_empty())
            .collect();
        Ok((items, j + 1))
    } else if rest.is_empty() {
        let mut items = Vec::new();
        let mut j = i + 1;
        while j < lines.len() {
            let l = &lines[j];
            if l.trim().is_empty() {
                j += 1;
                continue;
            }
            if !is_indented(l) {
                break;
            }
            let lt = l.trim();
            let Some(item) = lt.strip_prefix('-') else {
                return Err(format!("{key}: block list line is not a '-' item: {lt:?}"));
            };
            items.push(strip_quotes(item.trim()).to_string());
            j += 1;
        }
        if items.is_empty() {
            return Err(format!("{key}: empty list value"));
        }
        Ok((items, j))
    } else {
        Err(format!("{key}: unsupported scalar list value {rest:?}"))
    }
}

/// Parse the frontmatter of one test file. `Ok(default)` when the file has no
/// `/*---` block; `Err` when a consumed key is unparseable (fail-closed).
pub fn parse_frontmatter(content: &str) -> Result<Frontmatter, String> {
    let Some(start) = content.find("/*---") else {
        return Ok(Frontmatter::default());
    };
    let after = &content[start + "/*---".len()..];
    let Some(end) = after.find("---*/") else {
        return Err("unterminated frontmatter block (no ---*/)".to_string());
    };
    let block = &after[..end];
    let lines: Vec<String> = block.lines().map(|l| l.trim_end_matches('\r').to_string()).collect();

    let mut fm = Frontmatter::default();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].clone();
        if line.trim().is_empty() || is_indented(&line) {
            // Blank, or continuation of a skipped key (info/description block
            // scalars are indented, so their content can never be mistaken
            // for a top-level key).
            i += 1;
            continue;
        }
        let Some(colon) = line.find(':') else {
            return Err(format!("frontmatter line without a key: {line:?}"));
        };
        let key = line[..colon].trim().to_string();
        let rest = line[colon + 1..].trim().to_string();
        match key.as_str() {
            "flags" | "features" | "includes" => {
                let (items, next) = parse_list(&lines, i, &rest, &key)?;
                match key.as_str() {
                    "flags" => fm.flags = items,
                    "features" => fm.features = items,
                    _ => fm.includes = items,
                }
                i = next;
            }
            "negative" => {
                if !rest.is_empty() {
                    return Err(format!("negative: unsupported inline value {rest:?}"));
                }
                let mut phase: Option<String> = None;
                let mut type_name: Option<String> = None;
                i += 1;
                while i < lines.len() {
                    let l = &lines[i];
                    if l.trim().is_empty() {
                        i += 1;
                        continue;
                    }
                    if !is_indented(l) {
                        break;
                    }
                    let lt = l.trim();
                    let Some(c) = lt.find(':') else {
                        return Err(format!("negative: unparseable block line {lt:?}"));
                    };
                    let k = lt[..c].trim();
                    let v = strip_quotes(lt[c + 1..].trim()).to_string();
                    match k {
                        "phase" => phase = Some(v),
                        "type" => type_name = Some(v),
                        other => return Err(format!("negative: unknown key {other:?}")),
                    }
                    i += 1;
                }
                fm.negative = Some(Negative {
                    phase: phase.ok_or_else(|| "negative: missing phase".to_string())?,
                    type_name: type_name.ok_or_else(|| "negative: missing type".to_string())?,
                });
            }
            _ => {
                // Skipped key (description, info, esid, es5id, es6id, author,
                // locale, defines, ...). Its indented continuation lines are
                // consumed by the is_indented branch above.
                i += 1;
            }
        }
    }
    Ok(fm)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flow_lists() {
        let src = "/*---\nesid: sec-foo\nflags: [onlyStrict, generated]\nfeatures: [Symbol.iterator]\nincludes: [propertyHelper.js, compareArray.js]\n---*/\ncode();";
        let fm = parse_frontmatter(src).unwrap();
        assert_eq!(fm.flags, ["onlyStrict", "generated"]);
        assert_eq!(fm.features, ["Symbol.iterator"]);
        assert_eq!(fm.includes, ["propertyHelper.js", "compareArray.js"]);
        assert!(fm.negative.is_none());
    }

    #[test]
    fn block_includes_and_negative() {
        let src = "/*---\nincludes:\n  - propertyHelper.js\n  - sta.js\nnegative:\n  phase: parse\n  type: SyntaxError\n---*/\n";
        let fm = parse_frontmatter(src).unwrap();
        assert_eq!(fm.includes, ["propertyHelper.js", "sta.js"]);
        let neg = fm.negative.unwrap();
        assert_eq!(neg.phase, "parse");
        assert_eq!(neg.type_name, "SyntaxError");
    }

    #[test]
    fn crlf_and_no_block() {
        let src = "/*---\r\nflags: [noStrict]\r\nnegative:\r\n  phase: runtime\r\n  type: TypeError\r\n---*/\r\nvar x;";
        let fm = parse_frontmatter(src).unwrap();
        assert_eq!(fm.flags, ["noStrict"]);
        assert_eq!(fm.negative.unwrap().phase, "runtime");
        assert_eq!(parse_frontmatter("var x = 1;").unwrap(), Frontmatter::default());
    }

    #[test]
    fn info_block_scalar_is_inert() {
        // An indented "flags:" inside an info block scalar must not count.
        let src = "/*---\ninfo: |\n  This test has notes.\n  flags: [async]\n  includes: [nope.js]\ndescription: >\n  wrapped\n  text\nflags: [raw]\n---*/\n";
        let fm = parse_frontmatter(src).unwrap();
        assert_eq!(fm.flags, ["raw"]);
        assert!(fm.includes.is_empty());
    }

    #[test]
    fn multiline_flow_list() {
        let src = "/*---\nfeatures: [Symbol.iterator,\n  Symbol.asyncIterator]\nflags: [module]\n---*/\n";
        let fm = parse_frontmatter(src).unwrap();
        assert_eq!(fm.features, ["Symbol.iterator", "Symbol.asyncIterator"]);
        assert_eq!(fm.flags, ["module"]);
    }

    #[test]
    fn quoted_items() {
        let src = "/*---\nfeatures: [\"Intl.DurationFormat\", 'Atomics']\n---*/\n";
        let fm = parse_frontmatter(src).unwrap();
        assert_eq!(fm.features, ["Intl.DurationFormat", "Atomics"]);
    }

    #[test]
    fn failures_are_errors() {
        assert!(parse_frontmatter("/*---\nflags: [async\n").is_err()); // no ---*/
        assert!(parse_frontmatter("/*---\nflags: [async\n---*/\n").is_err()); // unterminated list
        assert!(parse_frontmatter("/*---\nnegative:\n  phase: parse\n---*/\n").is_err()); // missing type
        assert!(parse_frontmatter("/*---\nincludes:\nflags: [raw]\n---*/\n").is_err()); // empty block list
        assert!(parse_frontmatter("/*---\nflags: async\n---*/\n").is_err()); // scalar list
    }
}
