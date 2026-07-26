//! mdman markdown to man converter.
//!
//! > This crate is maintained by the Cargo team, primarily for use by Cargo
//! > and not intended for external use (except as a transitive dependency). This
//! > crate may make major changes to its APIs or be deprecated without warning.

use anyhow::{Context, Error, bail};
use pulldown_cmark::{CowStr, Event, LinkType, Options, Parser, Tag, TagEnd};
use std::collections::HashMap;
use std::fs;
use std::io::{self, BufRead};
use std::ops::Range;
use std::path::Path;
use url::Url;

mod format;
mod hbs;
mod util;

use format::Formatter;

/// Mapping of `(name, section)` of a man page to a URL.
pub type ManMap = HashMap<(String, u8), String>;

/// A man section.
pub type Section = u8;

/// The output formats supported by mdman.
#[derive(Copy, Clone)]
pub enum Format {
    Man,
    Md,
    Text,
}

impl Format {
    /// The filename extension for the format.
    pub fn extension(&self, section: Section) -> String {
        match self {
            Format::Man => section.to_string(),
            Format::Md => "md".to_string(),
            Format::Text => "txt".to_string(),
        }
    }
}

/// Converts the handlebars markdown file at the given path into the given
/// format, returning the translated result.
pub fn convert(
    file: &Path,
    format: Format,
    url: Option<Url>,
    man_map: ManMap,
) -> Result<String, Error> {
    let formatter: Box<dyn Formatter + Send + Sync> = match format {
        Format::Man => Box::new(format::man::ManFormatter::new(url)),
        Format::Md => Box::new(format::md::MdFormatter::new(man_map)),
        Format::Text => Box::new(format::text::TextFormatter::new(url)),
    };
    let expanded = hbs::expand(file, &*formatter)?;
    // pulldown-cmark can behave a little differently with Windows newlines,
    // just normalize it.
    let expanded = expanded.replace("\r\n", "\n");
    formatter.render(&expanded)
}

/// Pulldown-cmark iterator yielding an `(event, range)` tuple.
type EventIter<'a> = Box<dyn Iterator<Item = (Event<'a>, Range<usize>)> + 'a>;

/// Creates a new markdown parser with the given input.
pub(crate) fn md_parser(input: &str, url: Option<Url>) -> EventIter<'_> {
    let parser = Parser::new_ext(input, markdown_options());
    let parser = parser.into_offset_iter();
    // Trust: translate all links to include the base url. Upstream unwraps the
    // join here, so a malformed authored destination aborts the build with a
    // panic. Public render entry points validate destinations before
    // constructing the iterator; this map stays total for internal callers, so
    // malformed input is a typed render error rather than a process abort.
    let parser = parser.map(move |(event, range)| match event {
        Event::Start(Tag::Link {
            link_type,
            dest_url,
            title,
            id,
        }) if !matches!(link_type, LinkType::Email) => {
            let joined = join_url(url.as_ref(), dest_url.clone()).unwrap_or(dest_url);
            (
                Event::Start(Tag::Link {
                    link_type,
                    dest_url: joined,
                    title,
                    id,
                }),
                range,
            )
        }
        Event::End(TagEnd::Link) => (Event::End(TagEnd::Link), range),
        _ => (event, range),
    });
    Box::new(parser)
}

fn markdown_options() -> Options {
    let mut options = Options::empty();
    options.insert(Options::ENABLE_TABLES);
    options.insert(Options::ENABLE_FOOTNOTES);
    options.insert(Options::ENABLE_TASKLISTS);
    options.insert(Options::ENABLE_MATH);
    options.insert(Options::ENABLE_STRIKETHROUGH);
    options.insert(Options::ENABLE_SMART_PUNCTUATION);
    options
}

fn join_url<'a>(base: Option<&Url>, dest: CowStr<'a>) -> Result<CowStr<'a>, url::ParseError> {
    match base {
        Some(base_url) => {
            // Trust: a page-relative anchor deliberately stays local to the
            // generated man/text document. `Url::join` handles both absolute
            // and relative URLs correctly; upstream's `contains(':')` test does
            // not, because a valid relative path may carry a colon outside its
            // first segment and would then be treated as already absolute.
            if dest.starts_with('#') {
                Ok(dest)
            } else {
                base_url
                    .join(&dest)
                    .map(|joined| String::from(joined).into())
            }
        }
        None => Ok(dest),
    }
}

/// Trust: validate every URL that the man/text renderers will resolve against
/// `base`.
///
/// This separate pass keeps the event iterator infallible for pulldown-cmark's
/// HTML adapter while ensuring malformed authored destinations return through
/// mdman's ordinary `Result` surface. It is called for every recursive render
/// fragment as well as the final document.
pub(crate) fn validate_link_destinations(input: &str, base: Option<&Url>) -> Result<(), Error> {
    let Some(base) = base else {
        return Ok(());
    };
    for (event, range) in Parser::new_ext(input, markdown_options()).into_offset_iter() {
        if let Event::Start(Tag::Link {
            link_type,
            dest_url,
            ..
        }) = event
        {
            if matches!(link_type, LinkType::Email) {
                continue;
            }
            join_url(Some(base), dest_url.clone()).with_context(|| {
                format!(
                    "failed to resolve link destination `{dest_url}` at offset {} against `{base}`",
                    range.start
                )
            })?;
        }
    }
    Ok(())
}

pub fn extract_section(file: &Path) -> Result<Section, Error> {
    let f = fs::File::open(file).with_context(|| format!("could not open `{}`", file.display()))?;
    let mut f = io::BufReader::new(f);
    let mut line = String::new();
    f.read_line(&mut line)?;
    if !line.starts_with("# ") {
        bail!("expected input file to start with # header");
    }
    let (_name, section) = util::parse_name_and_section(&line[2..].trim()).with_context(|| {
        format!(
            "expected input file to have header with the format `# command-name(1)`, found: `{}`",
            line
        )
    })?;
    Ok(section)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_relative_link_is_a_typed_error() {
        let base = Url::parse("https://example.invalid/manual/").expect("valid base URL");

        let error = validate_link_destinations("[broken](//)", Some(&base))
            .expect_err("an empty authority cannot be resolved");

        let message = format!("{error:#}");
        assert!(
            message.contains("failed to resolve link destination `//`")
                && message.contains("empty host"),
            "unexpected error: {message}"
        );

        for renderer in [
            Box::new(format::text::TextFormatter::new(Some(base.clone()))) as Box<dyn Formatter>,
            Box::new(format::man::ManFormatter::new(Some(base.clone()))) as Box<dyn Formatter>,
        ] {
            assert!(
                renderer.render("[broken](//)").is_err(),
                "every base-URL renderer must return the malformed link as an error"
            );
        }
    }

    #[test]
    fn colon_in_later_relative_path_segment_is_resolved() {
        let base = Url::parse("https://example.invalid/manual/").expect("valid base URL");
        let joined =
            join_url(Some(&base), CowStr::from("guide/topic:detail")).expect("valid relative URL");

        assert_eq!(
            joined.as_ref(),
            "https://example.invalid/manual/guide/topic:detail"
        );
    }

    #[test]
    fn page_anchor_remains_document_relative() {
        let base = Url::parse("https://example.invalid/manual/").expect("valid base URL");
        let joined = join_url(Some(&base), CowStr::from("#options")).expect("valid page anchor");

        assert_eq!(joined.as_ref(), "#options");
    }
}
