use std::iter::once;
use std::path::{self, Path, PathBuf};

use rustc_ast::{AttrVec, Attribute, CleanIslandDecl, Inline, Item, ModSpans};
use rustc_attr_parsing::template;
use rustc_attr_parsing::validate_attr::emit_malformed_attribute;
use rustc_data_structures::fx::FxHashMap;
use rustc_errors::{Diag, ErrorGuaranteed};
use rustc_parse::lexer::StripTokens;
use rustc_parse::{exp, new_parser_from_file, trust_parse_clean_unit_decls, unwrap_or_emit_fatal};
use rustc_session::Session;
use rustc_session::parse::ParseSess;
use rustc_span::fatal_error::FatalError;
use rustc_span::{Ident, Span, Symbol, sym};
use thin_vec::ThinVec;

use crate::base::ModuleData;
use crate::diagnostics::{
    ModuleCircular, ModuleFileNotFound, ModuleInBlock, ModuleInBlockName, ModuleMultipleCandidates,
};

#[derive(Copy, Clone)]
pub enum DirOwnership {
    Owned {
        // None if `mod.rs`, `Some("foo")` if we're in `foo.rs`.
        relative: Option<Ident>,
    },
    UnownedViaBlock,
}

// Public for rustfmt usage.
pub struct ModulePathSuccess {
    pub file_path: PathBuf,
    pub dir_ownership: DirOwnership,
}

pub(crate) struct ParsedExternalMod {
    pub items: ThinVec<Box<Item>>,
    pub spans: ModSpans,
    pub file_path: PathBuf,
    pub dir_path: PathBuf,
    pub dir_ownership: DirOwnership,
    pub had_parse_error: Result<(), ErrorGuaranteed>,
}

pub enum ModError<'a> {
    CircularInclusion(Vec<PathBuf>),
    ModInBlock(Option<Ident>),
    FileNotFound(Ident, PathBuf, PathBuf),
    MultipleCandidates(Ident, PathBuf, PathBuf),
    ParserError(Diag<'a>),
}

pub(crate) fn parse_external_mod(
    sess: &Session,
    ident: Ident,
    span: Span, // The span to blame on errors.
    module: &ModuleData,
    mut dir_ownership: DirOwnership,
    attrs: &mut AttrVec,
) -> ParsedExternalMod {
    // We bail on the first error, but that error does not cause a fatal error... (1)
    let result: Result<_, ModError<'_>> = try {
        // Extract the file path and the new ownership.
        let mp = mod_file_path(sess, ident, attrs, &module.dir_path, dir_ownership)?;
        dir_ownership = mp.dir_ownership;

        // Ensure file paths are acyclic.
        if let Some(pos) = module.file_path_stack.iter().position(|p| p == &mp.file_path) {
            do yeet ModError::CircularInclusion(module.file_path_stack[pos..].to_vec());
        }

        // Actually parse the external file as a module.
        let mut parser = unwrap_or_emit_fatal(new_parser_from_file(
            &sess.psess,
            &mp.file_path,
            StripTokens::ShebangAndFrontmatter,
            Some(span),
        ));
        let (inner_attrs, items, inner_span) =
            parser.parse_mod(exp!(Eof)).map_err(ModError::ParserError)?;
        attrs.extend(inner_attrs);
        (items, inner_span, mp.file_path)
    };

    // (1) ...instead, we return a dummy module.
    let ((items, spans, file_path), had_parse_error) = match result {
        Err(err) => (Default::default(), Err(err.report(sess, span))),
        Ok(result) => (result, Ok(())),
    };

    // Extract the directory path for submodules of the module.
    let dir_path = file_path.parent().unwrap_or(&file_path).to_owned();

    ParsedExternalMod { items, spans, file_path, dir_path, dir_ownership, had_parse_error }
}

pub(crate) fn mod_dir_path(
    sess: &Session,
    ident: Ident,
    attrs: &[Attribute],
    module: &ModuleData,
    mut dir_ownership: DirOwnership,
    inline: Inline,
) -> (PathBuf, DirOwnership) {
    match inline {
        Inline::Yes
            if let Some(file_path) = mod_file_path_from_attr(sess, attrs, &module.dir_path) =>
        {
            // For inline modules file path from `#[path]` is actually the directory path
            // for historical reasons, so we don't pop the last segment here.
            (file_path, DirOwnership::Owned { relative: None })
        }
        Inline::Yes => {
            // We have to push on the current module name in the case of relative
            // paths in order to ensure that any additional module paths from inline
            // `mod x { ... }` come after the relative extension.
            //
            // For example, a `mod z { ... }` inside `x/y.rs` should set the current
            // directory path to `/x/y/z`, not `/x/z` with a relative offset of `y`.
            let mut dir_path = module.dir_path.clone();
            if let DirOwnership::Owned { relative } = &mut dir_ownership {
                if let Some(ident) = relative.take() {
                    // Remove the relative offset.
                    dir_path.push(ident.as_str());
                }
            }
            dir_path.push(ident.as_str());

            (dir_path, dir_ownership)
        }
        Inline::No { .. } => {
            // FIXME: This is a subset of `parse_external_mod` without actual parsing,
            // check whether the logic for unloaded, loaded and inline modules can be unified.
            let file_path = mod_file_path(sess, ident, attrs, &module.dir_path, dir_ownership)
                .map(|mp| {
                    dir_ownership = mp.dir_ownership;
                    mp.file_path
                })
                .unwrap_or_default();

            // Extract the directory path for submodules of the module.
            let dir_path = file_path.parent().unwrap_or(&file_path).to_owned();

            (dir_path, dir_ownership)
        }
    }
}

fn mod_file_path<'a>(
    sess: &'a Session,
    ident: Ident,
    attrs: &[Attribute],
    dir_path: &Path,
    dir_ownership: DirOwnership,
) -> Result<ModulePathSuccess, ModError<'a>> {
    if let Some(file_path) = mod_file_path_from_attr(sess, attrs, dir_path) {
        // All `#[path]` files are treated as though they are a `mod.rs` file.
        // This means that `mod foo;` declarations inside `#[path]`-included
        // files are siblings,
        //
        // Note that this will produce weirdness when a file named `foo.rs` is
        // `#[path]` included and contains a `mod foo;` declaration.
        // If you encounter this, it's your own darn fault :P
        let dir_ownership = DirOwnership::Owned { relative: None };
        return Ok(ModulePathSuccess { file_path, dir_ownership });
    }

    let relative = match dir_ownership {
        DirOwnership::Owned { relative } => relative,
        DirOwnership::UnownedViaBlock => None,
    };
    let result = default_submod_path(&sess.psess, ident, relative, dir_path);
    match dir_ownership {
        DirOwnership::Owned { .. } => result,
        DirOwnership::UnownedViaBlock => Err(ModError::ModInBlock(match result {
            Ok(_) | Err(ModError::MultipleCandidates(..)) => Some(ident),
            _ => None,
        })),
    }
}

/// Derive a submodule path from the first found `#[path = "path_string"]`.
/// The provided `dir_path` is joined with the `path_string`.
pub(crate) fn mod_file_path_from_attr(
    sess: &Session,
    attrs: &[Attribute],
    dir_path: &Path,
) -> Option<PathBuf> {
    // FIXME(154781) use a parsed attribute here
    // Extract path string from first `#[path = "path_string"]` attribute.
    let first_path = attrs.iter().find(|at| at.has_name(sym::path))?;
    let Some(path_sym) = first_path.value_str() else {
        // This check is here mainly to catch attempting to use a macro,
        // such as `#[path = concat!(...)]`. This isn't supported because
        // otherwise the `InvocationCollector` would need to defer loading
        // a module until the `#[path]` attribute was expanded, and it
        // doesn't support that (and would likely add a bit of complexity).
        // Usually bad forms are checked during semantic analysis via
        // `TyCtxt::check_mod_attrs`), but by the time that runs the macro
        // is expanded, and it doesn't give an error.
        emit_malformed_attribute(
            &sess.psess,
            first_path.style,
            first_path.span,
            sym::path,
            template!(
                NameValueStr: "file",
                "https://doc.rust-lang.org/reference/items/modules.html#the-path-attribute"
            ),
        );
        FatalError.raise()
    };

    let path_str = path_sym.as_str();

    // On windows, the base path might have the form
    // `\\?\foo\bar` in which case it does not tolerate
    // mixed `/` and `\` separators, so canonicalize
    // `/` to `\`.
    #[cfg(windows)]
    let path_str = path_str.replace("/", "\\");

    Some(dir_path.join(path_str))
}

/// Returns a path to a module.
// Public for rustfmt usage.
pub fn default_submod_path<'a>(
    psess: &'a ParseSess,
    ident: Ident,
    relative: Option<Ident>,
    dir_path: &Path,
) -> Result<ModulePathSuccess, ModError<'a>> {
    // If we're in a foo.rs file instead of a mod.rs file,
    // we need to look for submodules in
    // `./foo/<ident>.rs` and `./foo/<ident>/mod.rs` rather than
    // `./<ident>.rs` and `./<ident>/mod.rs`.
    let relative_prefix_string;
    let relative_prefix = if let Some(ident) = relative {
        relative_prefix_string = format!("{}{}", ident.name, path::MAIN_SEPARATOR);
        &relative_prefix_string
    } else {
        ""
    };

    let default_path_str = format!("{}{}.rs", relative_prefix, ident.name);
    let secondary_path_str =
        format!("{}{}{}mod.rs", relative_prefix, ident.name, path::MAIN_SEPARATOR);
    let default_path = dir_path.join(&default_path_str);
    let secondary_path = dir_path.join(&secondary_path_str);
    let default_exists = psess.source_map().file_exists(&default_path);
    let secondary_exists = psess.source_map().file_exists(&secondary_path);

    match (default_exists, secondary_exists) {
        (true, false) => Ok(ModulePathSuccess {
            file_path: default_path,
            dir_ownership: DirOwnership::Owned { relative: Some(ident) },
        }),
        (false, true) => Ok(ModulePathSuccess {
            file_path: secondary_path,
            dir_ownership: DirOwnership::Owned { relative: None },
        }),
        (false, false) => Err(ModError::FileNotFound(ident, default_path, secondary_path)),
        (true, true) => Err(ModError::MultipleCandidates(ident, default_path, secondary_path)),
    }
}

/// Trust (I8): one loaded out-of-line Clean unit — the payload half of an
/// `ItemKind::CleanIsland` whose `unloaded_unit` marker has just been
/// resolved. After the caller installs it, the unit is indistinguishable from
/// an inline island everywhere downstream, which is I8's acceptance control.
pub(crate) struct LoadedCleanUnit {
    pub content_span: Span,
    pub text: Symbol,
    pub decls: ThinVec<CleanIslandDecl>,
}

/// Trust (I8): load and REALLY PARSE the `.clean` unit named by
/// `clean mod <ident>;`, at the same expansion seam where out-of-line
/// `mod <ident>;` bodies load — so `#[cfg]` stripping has already run, and the
/// directory state (`ModuleData` + `DirOwnership`, including `#[path]`) is the
/// real one `mod` itself would use.
///
/// Path resolution is Rust's, with ONE deliberate subtraction: a single
/// candidate `<dir>/<relative-prefix><ident>.clean`, no `<ident>/mod.clean`
/// secondary. A `.clean` unit is a leaf by construction — its contents are
/// Clean text, which cannot contain `clean mod`, so no unit ever owns a
/// directory of sub-units — and one candidate also deletes the
/// multiple-candidates ambiguity class, letting "file not found" name the
/// exact path it looked for. `#[path = "…"]` is honoured through the same
/// function `mod` uses (`mod_file_path_from_attr`), with the same semantics.
///
/// The loaded file becomes a real `SourceFile` (`SourceMap::load_file`), so
/// Clean parse errors — and later, elaboration/kernel diagnostics remapped by
/// the verify pass — land in `<ident>.clean` at the right line. `text` is the
/// NORMALIZED source (BOM stripped, newlines folded by `SourceFile::new`),
/// which is the same byte indexing rustc span arithmetic uses, so
/// `content_span.lo() + offset` stays exact.
///
/// A `.clean` unit may be included ONCE per crate, and the refusal is eager
/// (ruling v7/D3). The crate's Clean environment is a single header-first
/// batch, so a second inclusion could never be right: it would either declare
/// every name twice (a Clean-level rejection) or — because `load_file` dedups
/// by path, giving both islands the SAME `content_span` — trip the verify
/// pass's collapsed-span ambiguity error, whose macro-oriented wording would
/// mislead. `loaded_units` is the crate-wide ledger (`ExtCtxt`); the second
/// inclusion errors at its own span pointing at the first.
///
/// Every error path returns the inert empty payload (zero-width span, empty
/// text, no decls — the shape of an empty inline island): fail-closed, no
/// decls to mint, nothing to elaborate, never a claim.
pub(crate) fn load_clean_unit(
    sess: &Session,
    ident: Ident,
    span: Span, // the `clean mod ident;` item, blamed on errors
    module: &ModuleData,
    dir_ownership: DirOwnership,
    attrs: &[Attribute],
    loaded_units: &mut FxHashMap<PathBuf, Span>,
) -> LoadedCleanUnit {
    let empty = || LoadedCleanUnit {
        content_span: span.shrink_to_lo(),
        text: sym::empty,
        decls: ThinVec::new(),
    };

    // `#[path]` first, byte-identically to `mod` (same function). Otherwise
    // the single default candidate, honouring the same relative offset
    // (`foo.rs` vs `mod.rs`) `default_submod_path` applies.
    let file_path = if let Some(path) = mod_file_path_from_attr(sess, attrs, &module.dir_path) {
        path
    } else {
        match dir_ownership {
            DirOwnership::Owned { relative } => {
                let relative_prefix = match relative {
                    Some(relative) => format!("{}{}", relative.name, path::MAIN_SEPARATOR),
                    None => String::new(),
                };
                module.dir_path.join(format!("{}{}.clean", relative_prefix, ident.name))
            }
            DirOwnership::UnownedViaBlock => {
                // The mod-in-block rule, applied unchanged (ruling v7/D3:
                // refusal with options).
                sess.dcx()
                    .struct_span_err(
                        span,
                        format!("`clean mod {ident};` inside a block needs a `#[path]` attribute"),
                    )
                    .with_note(
                        "the enclosing block owns no directory, so there is no place to \
                         resolve the `.clean` file from — the same rule as `mod …;` in a block",
                    )
                    .with_help(
                        "options: add `#[path = \"…\"]` naming the file; move the unit to \
                         module scope; or write the declarations inline as `clean { … }`",
                    )
                    .emit();
                return empty();
            }
        }
    };

    if let Some(&first) = loaded_units.get(&file_path) {
        sess.dcx()
            .struct_span_err(
                span,
                format!("the Clean unit `{}` is included twice in this crate", file_path.display()),
            )
            .with_span_note(first, "first included here")
            .with_note(
                "a `.clean` unit registers its declarations in the crate's single Clean \
                 environment, so a second inclusion would declare every name a second time",
            )
            .with_help(
                "options: include the unit once — its declarations are citable from every \
                 `clean { … }` island in the crate and callable through the module that \
                 includes it; or split the text into two files if two units were intended",
            )
            .emit();
        return empty();
    }

    if !sess.psess.source_map().file_exists(&file_path) {
        sess.dcx()
            .struct_span_err(span, format!("file not found for out-of-line Clean unit `{ident}`"))
            .with_note(format!(
                "`clean mod {ident};` loads Clean (Lean) source from `{}`, which does not exist",
                file_path.display()
            ))
            .with_help(
                "options: create the file at that path; name a different file with \
                 `#[path = \"…\"]` on this item; or write the declarations inline as \
                 `clean { … }`",
            )
            .emit();
        return empty();
    }

    // Recorded before the read: a second inclusion after an I/O failure is
    // still a duplicate of the same authored intent, and the refusal above is
    // the better message than a repeated read error.
    loaded_units.insert(file_path.clone(), span);

    let file = match sess.psess.source_map().load_file(&file_path) {
        Ok(file) => file,
        Err(err) => {
            sess.dcx().span_err(span, format!("couldn't read `{}`: {}", file_path.display(), err));
            return empty();
        }
    };
    let Some(src) = file.src.as_deref() else {
        // Unreachable for a file loaded this instant, but never a panic: fail
        // closed to the empty unit like every other arm.
        sess.dcx().span_err(
            span,
            format!("source of `{}` is unavailable after loading", file_path.display()),
        );
        return empty();
    };

    // The unit file's OWN `SourceFile` range. Root syntax context, like every
    // span an out-of-line Rust module's text gets from being parsed.
    let content_span = Span::with_root_ctxt(file.start_pos, file.end_position());
    let decls = trust_parse_clean_unit_decls(&sess.psess, content_span, src, ident);

    LoadedCleanUnit { content_span, text: Symbol::intern(src), decls }
}

impl ModError<'_> {
    fn report(self, sess: &Session, span: Span) -> ErrorGuaranteed {
        match self {
            ModError::CircularInclusion(file_paths) => {
                let path_to_string = |path: &PathBuf| path.display().to_string();

                let paths = file_paths
                    .iter()
                    .map(path_to_string)
                    .chain(once(path_to_string(&file_paths[0])))
                    .collect::<Vec<_>>();

                let modules = paths.join(" -> ");

                sess.dcx().emit_err(ModuleCircular { span, modules })
            }
            ModError::ModInBlock(ident) => sess.dcx().emit_err(ModuleInBlock {
                span,
                name: ident.map(|name| ModuleInBlockName { span, name }),
            }),
            ModError::FileNotFound(name, default_path, secondary_path) => {
                sess.dcx().emit_err(ModuleFileNotFound {
                    span,
                    name,
                    default_path: default_path.display().to_string(),
                    secondary_path: secondary_path.display().to_string(),
                })
            }
            ModError::MultipleCandidates(name, default_path, secondary_path) => {
                sess.dcx().emit_err(ModuleMultipleCandidates {
                    span,
                    name,
                    default_path: default_path.display().to_string(),
                    secondary_path: secondary_path.display().to_string(),
                })
            }
            ModError::ParserError(err) => err.emit(),
        }
    }
}
