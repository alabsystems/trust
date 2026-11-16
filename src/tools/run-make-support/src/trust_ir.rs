//! Trust: reading a dumped TrustIr text module (`-Ztrust-dump=ir:<dir>`) by def path.
//!
//! Since WS5.2 a function header names the function's link-time SYMBOL
//! (`rustcc fn @_RNvCs.._2dm5set_n(functy.2) {`), and its def path follows as the
//! `; #display-path: "<path>"` directive. The recipes that find a body by its def path
//! (`fn @set_n(`, `fn @"PLAIN::__rust_std_internal_init_fn"(`) read the module through
//! [`by_display_path`].

/// The pinned reference codec and interpreter for comparing emitted IR with native tests.
/// Executing samples through this library supplies test evidence, not proof authority.
pub use trust_ir_reference as reference;

/// The text module with every function header that carries a `; #display-path:` directive
/// renamed to that def path, spelled as the TrustIr printer spells a symbol: bare when it is
/// in the bare alphabet (ASCII alphanumerics, `_`, `.` and `$`), otherwise the directive's own
/// quoted string. A header without the directive, every other line, and the order of the
/// headers (a `call @func.N` names the N-th one) are unchanged.
pub fn by_display_path(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let mut out = String::with_capacity(text.len());
    for (index, &line) in lines.iter().enumerate() {
        let renamed = header_symbol(line).and_then(|(start, end)| {
            let path = lines[index + 1..]
                .iter()
                .take_while(|next| next.trim_start().starts_with("; #"))
                .find_map(|next| next.trim_start().strip_prefix("; #display-path: "))?;
            Some(format!("{}{}{}", &line[..start], symbol_spelling(path.trim()), &line[end..]))
        });
        out.push_str(renamed.as_deref().unwrap_or(line));
        out.push('\n');
    }
    out
}

/// The byte range of the symbol in a function header (`[cc ]fn @<symbol>(functy.N) {`), or
/// `None` when `line` is not one. An instruction is indented, so it never matches.
fn header_symbol(line: &str) -> Option<(usize, usize)> {
    if line.starts_with(char::is_whitespace) || !line.trim_end().ends_with('{') {
        return None;
    }
    let start = line.find("fn @")? + "fn @".len();
    let rest = &line[start..];
    let len = if let Some(quoted) = rest.strip_prefix('"') {
        let mut escaped = false;
        let close = quoted.char_indices().find_map(|(at, c)| match (escaped, c) {
            (false, '\\') => {
                escaped = true;
                None
            }
            (false, '"') => Some(at),
            _ => {
                escaped = false;
                None
            }
        })?;
        close + 2
    } else {
        rest.find('(')?
    };
    rest[len..].starts_with("(functy.").then_some((start, start + len))
}

/// A `#display-path` value (a quoted string) spelled as a header symbol.
fn symbol_spelling(quoted: &str) -> &str {
    let inner = quoted.strip_prefix('"').and_then(|q| q.strip_suffix('"')).unwrap_or(quoted);
    let bare = !inner.is_empty()
        && inner.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '$'));
    if bare { inner } else { quoted }
}
