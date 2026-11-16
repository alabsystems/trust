use std::borrow::Cow;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use rustc_ast::ast;
use rustc_ast::visit::Visitor;
use rustc_data_structures::thin_vec::ThinVec; // Trust: the one linked thin_vec
use rustc_span::Span;
use rustc_span::symbol::{self, Symbol, sym};
use thiserror::Error;

use crate::attr::MetaVisitor;
use crate::config::FileName;
use crate::items::is_mod_decl;
use crate::parse::macros::include::parse_include_path;
use crate::parse::parser::{
    Directory, DirectoryOwnership, ModError, ModulePathSuccess, Parser, ParserError,
};
use crate::parse::session::ParseSess;
use crate::utils::{contains_custom_attributes, contains_skip, mk_sp};

mod visitor;

type FileModMap<'ast> = BTreeMap<FileName, Module<'ast>>;

/// Represents module with its inner attributes.
#[derive(Debug, Clone)]
pub(crate) struct Module<'a> {
    ast_mod_kind: Option<Cow<'a, ast::ModKind>>,
    pub(crate) items: Cow<'a, ThinVec<Box<ast::Item>>>,
    inner_attr: ast::AttrVec,
    pub(crate) span: Span,
}

impl<'a> Module<'a> {
    pub(crate) fn new(
        mod_span: Span,
        ast_mod_kind: Option<Cow<'a, ast::ModKind>>,
        mod_items: Cow<'a, ThinVec<Box<ast::Item>>>,
        mod_attrs: Cow<'a, ast::AttrVec>,
    ) -> Self {
        let inner_attr = mod_attrs
            .iter()
            .filter(|attr| attr.style == ast::AttrStyle::Inner)
            .cloned()
            .collect();
        Module {
            items: mod_items,
            inner_attr,
            span: mod_span,
            ast_mod_kind,
        }
    }

    pub(crate) fn attrs(&self) -> &[ast::Attribute] {
        &self.inner_attr
    }
}

/// Maps each module to the corresponding file.
pub(crate) struct ModResolver<'ast, 'psess> {
    psess: &'psess ParseSess,
    directory: Directory,
    file_map: FileModMap<'ast>,
    recursive: bool,
    // Trust (T14d): the `include!`s this resolver did not follow.
    unfollowed_includes: Vec<UnfollowedInclude>,
    // Trust (T14d): the directory of the package that owns the crate root
    // (`None` for a file no package owns), and how many leading lines of an
    // included file may carry the `@generated` marker.
    root_package: Option<PathBuf>,
    generated_marker_line_search_limit: usize,
}

/// Trust (T14d, DECISION_QUEUE T14-FMT-1): an `include!` the resolver did not
/// follow, so the file it names was not formatted: its path is no string
/// literal; it sits in expression, statement or associated-item position,
/// where the included text is not a list of module items; or the file it
/// names is missing, does not parse as items, or belongs to another package.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnfollowedInclude {
    /// `<file>:<line>` of the `include!`.
    pub(crate) location: String,
    pub(crate) reason: &'static str,
}

/// Represents errors while trying to resolve modules.
#[derive(Debug, Error)]
#[error("failed to resolve mod `{module}`: {kind}")]
pub struct ModuleResolutionError {
    pub(crate) module: String,
    pub(crate) kind: ModuleResolutionErrorKind,
}

/// Defines variants similar to those of [rustc_expand::module::ModError]
#[derive(Debug, Error)]
pub(crate) enum ModuleResolutionErrorKind {
    /// Find a file that cannot be parsed.
    #[error("cannot parse {file}")]
    ParseError { file: PathBuf },
    /// File cannot be found.
    #[error("{file} does not exist")]
    NotFound { file: PathBuf },
    /// File a.rs and a/mod.rs both exist
    #[error("file for module found at both {default_path:?} and {secondary_path:?}")]
    MultipleCandidates {
        default_path: PathBuf,
        secondary_path: PathBuf,
    },
}

#[derive(Clone)]
enum SubModKind<'a, 'ast> {
    /// `mod foo;`
    External(PathBuf, DirectoryOwnership, Module<'ast>),
    /// `mod foo;` with multiple sources.
    MultiExternal(Vec<(PathBuf, DirectoryOwnership, Module<'ast>)>),
    /// `mod foo {}`
    Internal(&'a ast::Item),
}

impl<'ast, 'psess, 'c> ModResolver<'ast, 'psess> {
    /// Creates a new `ModResolver`.
    pub(crate) fn new(
        psess: &'psess ParseSess,
        directory_ownership: DirectoryOwnership,
        recursive: bool,
    ) -> Self {
        ModResolver {
            directory: Directory {
                path: PathBuf::new(),
                ownership: directory_ownership,
            },
            file_map: BTreeMap::new(),
            psess,
            recursive,
            unfollowed_includes: Vec::new(),
            root_package: None,
            generated_marker_line_search_limit: 5,
        }
    }

    /// Trust (T14d): how many leading lines of an included file are searched
    /// for the `@generated` marker (`generated_marker_line_search_limit`).
    pub(crate) fn generated_marker_line_search_limit(mut self, limit: usize) -> Self {
        self.generated_marker_line_search_limit = limit;
        self
    }

    /// Creates a map that maps a file name to the module in AST, and names the
    /// `include!`s it did not follow.
    pub(crate) fn visit_crate(
        mut self,
        krate: &'ast ast::Crate,
    ) -> Result<(FileModMap<'ast>, Vec<UnfollowedInclude>), ModuleResolutionError> {
        let root_filename = self.psess.span_to_filename(krate.spans.inner_span);
        self.directory.path = match root_filename {
            FileName::Real(ref p) => p.parent().unwrap_or(Path::new("")).to_path_buf(),
            _ => PathBuf::new(),
        };
        if let FileName::Real(ref root) = root_filename {
            self.root_package = owning_package_dir(root);
        }

        // Skip visiting sub modules when the input is from stdin.
        if self.recursive {
            self.visit_mod_from_ast(&krate.items)?;
        }

        let snippet_provider = self.psess.snippet_provider(krate.spans.inner_span);

        self.file_map.insert(
            root_filename,
            Module::new(
                mk_sp(snippet_provider.start_pos(), snippet_provider.end_pos()),
                None,
                Cow::Borrowed(&krate.items),
                Cow::Borrowed(&krate.attrs),
            ),
        );
        // Trust (T14d): name every `include!` outside module-item position.
        if self.recursive {
            let mut nested = NestedIncludeVisitor {
                psess: self.psess,
                found: Vec::new(),
            };
            for module in self.file_map.values() {
                for item in module.items.iter() {
                    nested.visit_module_item(item);
                }
            }
            self.unfollowed_includes.extend(nested.found);
        }
        Ok((self.file_map, self.unfollowed_includes))
    }

    /// Trust (T14d): follow an item-position `include!("<literal>")` as an
    /// out-of-line module: the named file, resolved against the directory of
    /// the file that holds the macro (as rustc resolves it), is parsed as a
    /// list of items and formatted like any other module file. Its items join
    /// the including module, so its own `mod` declarations and `include!`s
    /// resolve from that module's directory.
    ///
    /// Not followed, and never failing the run:
    /// * a file marked `@generated` (in its first
    ///   `generated_marker_line_search_limit` lines) or an `include!` marked
    ///   `#[rustfmt::skip]`, silently, as a skipped module is: `include!`ing
    ///   generated text so the formatter leaves it to its generator is a
    ///   common idiom, and the generator's drift test owns its layout;
    /// * a file that is missing (generated at build time, or behind a `cfg`),
    ///   that does not parse as a list of items, or that belongs to another
    ///   package than the crate root (that package formats it, at its own
    ///   edition): each is named as not formatted.
    fn visit_include(&mut self, item: &ast::Item) -> Result<(), ModuleResolutionError> {
        let ast::ItemKind::MacCall(ref mac) = item.kind else {
            return Ok(());
        };
        if contains_skip(&item.attrs) {
            return Ok(());
        }
        let Some(literal) = parse_include_path(self.psess, mac) else {
            self.unfollow(item.span, "its path is not a string literal");
            return Ok(());
        };
        let base = match self.psess.span_to_filename(item.span) {
            FileName::Real(file) => file.parent().unwrap_or(Path::new("")).to_path_buf(),
            FileName::Stdin => return Ok(()),
        };
        let path = base.join(literal);
        if self.psess.is_file_parsed(&path) {
            return Ok(());
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            self.unfollow(
                item.span,
                "the file it names does not exist or cannot be read: generated at build time, \
                 or behind a `cfg`",
            );
            return Ok(());
        };
        if crate::formatting::generated::has_generated_marker(
            &text,
            self.generated_marker_line_search_limit,
        ) {
            return Ok(());
        }
        if owning_package_dir(&path) != self.root_package {
            self.unfollow(
                item.span,
                "the file it names belongs to another package, which formats it at its own \
                 edition",
            );
            return Ok(());
        }
        match Parser::parse_included_file_as_module(self.psess, &path, item.span) {
            Some((ref attrs, _, _)) if contains_skip(attrs) => Ok(()),
            Some((attrs, items, span)) => {
                let nested = items.clone();
                self.file_map
                    .entry(FileName::Real(path))
                    .or_insert(Module::new(
                        span,
                        Some(Cow::Owned(ast::ModKind::Unloaded)),
                        Cow::Owned(items),
                        Cow::Owned(attrs),
                    ));
                self.visit_mod_outside_ast(nested)
            }
            None => {
                self.unfollow(
                    item.span,
                    "the file it names does not parse as a list of items",
                );
                Ok(())
            }
        }
    }

    fn unfollow(&mut self, span: Span, reason: &'static str) {
        let location = self.location(span);
        self.unfollowed_includes
            .push(UnfollowedInclude { location, reason });
    }

    fn location(&self, span: Span) -> String {
        format!(
            "{}:{}",
            self.psess.span_to_filename(span),
            self.psess.line_of_byte_pos(span.lo())
        )
    }

    /// Visit `cfg_if` macro and look for module declarations.
    fn visit_cfg_if(&mut self, item: Cow<'ast, ast::Item>) -> Result<(), ModuleResolutionError> {
        let mut visitor = visitor::CfgIfVisitor::new(self.psess);
        visitor.visit_item(&item);
        for module_item in visitor.mods() {
            if let ast::ItemKind::Mod(_, _, ref sub_mod_kind) = module_item.item.kind {
                self.visit_sub_mod(
                    &module_item.item,
                    Module::new(
                        module_item.item.span,
                        Some(Cow::Owned(sub_mod_kind.clone())),
                        Cow::Owned(ThinVec::new()),
                        Cow::Owned(ast::AttrVec::new()),
                    ),
                )?;
            }
        }
        Ok(())
    }

    fn visit_cfg_select(
        &mut self,
        item: Cow<'ast, ast::Item>,
    ) -> Result<(), ModuleResolutionError> {
        let mut visitor = visitor::CfgSelectVisitor::new(self.psess);
        visitor.visit_item(&item);
        for module_item in visitor.mods() {
            if let ast::ItemKind::Mod(_, _, ref sub_mod_kind) = module_item.item.kind {
                self.visit_sub_mod(
                    &module_item.item,
                    Module::new(
                        module_item.item.span,
                        Some(Cow::Owned(sub_mod_kind.clone())),
                        Cow::Owned(ThinVec::new()),
                        Cow::Owned(ast::AttrVec::new()),
                    ),
                )?;
            }
        }
        Ok(())
    }

    /// Visit modules defined inside macro calls.
    fn visit_mod_outside_ast(
        &mut self,
        items: ThinVec<Box<ast::Item>>,
    ) -> Result<(), ModuleResolutionError> {
        for item in items {
            if is_cfg_if(&item) {
                self.visit_cfg_if(Cow::Owned(*item))?;
                continue;
            }

            if is_cfg_select(&item) {
                self.visit_cfg_select(Cow::Owned(*item))?;
                continue;
            }

            // Trust (T14d): a literal `include!` is an out-of-line module.
            if is_include(&item) {
                self.visit_include(&item)?;
                continue;
            }

            if let ast::ItemKind::Mod(_, _, ref sub_mod_kind) = item.kind {
                let span = item.span;
                self.visit_sub_mod(
                    &item,
                    Module::new(
                        span,
                        Some(Cow::Owned(sub_mod_kind.clone())),
                        Cow::Owned(ThinVec::new()),
                        Cow::Owned(ast::AttrVec::new()),
                    ),
                )?;
            }
        }
        Ok(())
    }

    /// Visit modules from AST.
    fn visit_mod_from_ast(
        &mut self,
        items: &'ast [Box<ast::Item>],
    ) -> Result<(), ModuleResolutionError> {
        for item in items {
            if is_cfg_if(item) {
                self.visit_cfg_if(Cow::Borrowed(item))?;
            }

            if is_cfg_select(item) {
                self.visit_cfg_select(Cow::Borrowed(item))?;
            }

            // Trust (T14d): a literal `include!` is an out-of-line module.
            if is_include(item) {
                self.visit_include(item)?;
            }

            if let ast::ItemKind::Mod(_, _, ref sub_mod_kind) = item.kind {
                let span = item.span;
                self.visit_sub_mod(
                    item,
                    Module::new(
                        span,
                        Some(Cow::Borrowed(sub_mod_kind)),
                        Cow::Owned(ThinVec::new()),
                        Cow::Borrowed(&item.attrs),
                    ),
                )?;
            }
        }
        Ok(())
    }

    fn visit_sub_mod(
        &mut self,
        item: &'c ast::Item,
        sub_mod: Module<'ast>,
    ) -> Result<(), ModuleResolutionError> {
        let old_directory = self.directory.clone();
        let sub_mod_kind = self.peek_sub_mod(item, &sub_mod)?;
        if let Some(sub_mod_kind) = sub_mod_kind {
            self.insert_sub_mod(sub_mod_kind.clone())?;
            self.visit_sub_mod_inner(sub_mod, sub_mod_kind)?;
        }
        self.directory = old_directory;
        Ok(())
    }

    /// Inspect the given sub-module which we are about to visit and returns its kind.
    fn peek_sub_mod(
        &self,
        item: &'c ast::Item,
        sub_mod: &Module<'ast>,
    ) -> Result<Option<SubModKind<'c, 'ast>>, ModuleResolutionError> {
        if contains_skip(&item.attrs) {
            return Ok(None);
        }

        if is_mod_decl(item) {
            // mod foo;
            // Look for an extern file.
            self.find_external_module(item.kind.ident().unwrap(), &item.attrs, sub_mod)
        } else {
            // An internal module (`mod foo { /* ... */ }`);
            Ok(Some(SubModKind::Internal(item)))
        }
    }

    fn insert_sub_mod(
        &mut self,
        sub_mod_kind: SubModKind<'c, 'ast>,
    ) -> Result<(), ModuleResolutionError> {
        match sub_mod_kind {
            SubModKind::External(mod_path, _, sub_mod) => {
                self.file_map
                    .entry(FileName::Real(mod_path))
                    .or_insert(sub_mod);
            }
            SubModKind::MultiExternal(mods) => {
                for (mod_path, _, sub_mod) in mods {
                    self.file_map
                        .entry(FileName::Real(mod_path))
                        .or_insert(sub_mod);
                }
            }
            _ => (),
        }
        Ok(())
    }

    fn visit_sub_mod_inner(
        &mut self,
        sub_mod: Module<'ast>,
        sub_mod_kind: SubModKind<'c, 'ast>,
    ) -> Result<(), ModuleResolutionError> {
        match sub_mod_kind {
            SubModKind::External(mod_path, directory_ownership, sub_mod) => {
                let directory = Directory {
                    path: mod_path.parent().unwrap().to_path_buf(),
                    ownership: directory_ownership,
                };
                self.visit_sub_mod_after_directory_update(sub_mod, Some(directory))
            }
            SubModKind::Internal(item) => {
                self.push_inline_mod_directory(item.kind.ident().unwrap(), &item.attrs);
                self.visit_sub_mod_after_directory_update(sub_mod, None)
            }
            SubModKind::MultiExternal(mods) => {
                for (mod_path, directory_ownership, sub_mod) in mods {
                    let directory = Directory {
                        path: mod_path.parent().unwrap().to_path_buf(),
                        ownership: directory_ownership,
                    };
                    self.visit_sub_mod_after_directory_update(sub_mod, Some(directory))?;
                }
                Ok(())
            }
        }
    }

    fn visit_sub_mod_after_directory_update(
        &mut self,
        sub_mod: Module<'ast>,
        directory: Option<Directory>,
    ) -> Result<(), ModuleResolutionError> {
        if let Some(directory) = directory {
            self.directory = directory;
        }
        match (sub_mod.ast_mod_kind, sub_mod.items) {
            (Some(Cow::Borrowed(ast::ModKind::Loaded(items, _, _))), _) => {
                self.visit_mod_from_ast(items)
            }
            (Some(Cow::Owned(ast::ModKind::Loaded(items, _, _))), _) | (_, Cow::Owned(items)) => {
                self.visit_mod_outside_ast(items)
            }
            (_, _) => Ok(()),
        }
    }

    /// Find a file path in the filesystem which corresponds to the given module.
    fn find_external_module(
        &self,
        mod_name: symbol::Ident,
        attrs: &[ast::Attribute],
        sub_mod: &Module<'ast>,
    ) -> Result<Option<SubModKind<'c, 'ast>>, ModuleResolutionError> {
        let relative = match self.directory.ownership {
            DirectoryOwnership::Owned { relative } => relative,
            DirectoryOwnership::UnownedViaBlock => None,
        };
        if let Some(path) = Parser::submod_path_from_attr(attrs, &self.directory.path) {
            if self.psess.is_file_parsed(&path) {
                return Ok(None);
            }
            return match Parser::parse_file_as_module(self.psess, &path, sub_mod.span) {
                Ok((ref attrs, _, _)) if contains_skip(attrs) => Ok(None),
                Ok((attrs, items, span)) => Ok(Some(SubModKind::External(
                    path,
                    DirectoryOwnership::Owned { relative: None },
                    Module::new(
                        span,
                        Some(Cow::Owned(ast::ModKind::Unloaded)),
                        Cow::Owned(items),
                        Cow::Owned(attrs),
                    ),
                ))),
                Err(ParserError::ParseError) => Err(ModuleResolutionError {
                    module: mod_name.to_string(),
                    kind: ModuleResolutionErrorKind::ParseError { file: path },
                }),
                Err(..) => Err(ModuleResolutionError {
                    module: mod_name.to_string(),
                    kind: ModuleResolutionErrorKind::NotFound { file: path },
                }),
            };
        }

        // Look for nested path, like `#[cfg_attr(feature = "foo", path = "bar.rs")]`.
        let mut mods_outside_ast = self.find_mods_outside_of_ast(attrs, sub_mod);

        match self
            .psess
            .default_submod_path(mod_name, relative, &self.directory.path)
        {
            Ok(ModulePathSuccess {
                file_path,
                dir_ownership,
                ..
            }) => {
                let outside_mods_empty = mods_outside_ast.is_empty();
                let should_insert = !mods_outside_ast
                    .iter()
                    .any(|(outside_path, _, _)| outside_path == &file_path);
                if self.psess.is_file_parsed(&file_path) {
                    if outside_mods_empty {
                        return Ok(None);
                    } else {
                        if should_insert {
                            mods_outside_ast.push((file_path, dir_ownership, sub_mod.clone()));
                        }
                        return Ok(Some(SubModKind::MultiExternal(mods_outside_ast)));
                    }
                }
                match Parser::parse_file_as_module(self.psess, &file_path, sub_mod.span) {
                    Ok((ref attrs, _, _)) if contains_skip(attrs) => Ok(None),
                    Ok((attrs, items, span)) if outside_mods_empty => {
                        Ok(Some(SubModKind::External(
                            file_path,
                            dir_ownership,
                            Module::new(
                                span,
                                Some(Cow::Owned(ast::ModKind::Unloaded)),
                                Cow::Owned(items),
                                Cow::Owned(attrs),
                            ),
                        )))
                    }
                    Ok((attrs, items, span)) => {
                        mods_outside_ast.push((
                            file_path.clone(),
                            dir_ownership,
                            Module::new(
                                span,
                                Some(Cow::Owned(ast::ModKind::Unloaded)),
                                Cow::Owned(items),
                                Cow::Owned(attrs),
                            ),
                        ));
                        if should_insert {
                            mods_outside_ast.push((file_path, dir_ownership, sub_mod.clone()));
                        }
                        Ok(Some(SubModKind::MultiExternal(mods_outside_ast)))
                    }
                    Err(ParserError::ParseError) => Err(ModuleResolutionError {
                        module: mod_name.to_string(),
                        kind: ModuleResolutionErrorKind::ParseError { file: file_path },
                    }),
                    Err(..) if outside_mods_empty => Err(ModuleResolutionError {
                        module: mod_name.to_string(),
                        kind: ModuleResolutionErrorKind::NotFound { file: file_path },
                    }),
                    Err(..) => {
                        if should_insert {
                            mods_outside_ast.push((file_path, dir_ownership, sub_mod.clone()));
                        }
                        Ok(Some(SubModKind::MultiExternal(mods_outside_ast)))
                    }
                }
            }
            Err(mod_err) if !mods_outside_ast.is_empty() => {
                if let ModError::ParserError(e) = mod_err {
                    e.cancel();
                }
                Ok(Some(SubModKind::MultiExternal(mods_outside_ast)))
            }
            Err(e) => match e {
                ModError::FileNotFound(_, default_path, _secondary_path) => {
                    if contains_custom_attributes(attrs) {
                        // It's possible that at least one of the attributes is a custom proc macro
                        // that takes the module tokens as an input. It's hard to know for sure
                        // since rustfmt only operates on the AST pre-expansion. In this case we'll
                        // be overly permissive and just ignore the file not found error so rustfmt
                        // can still try formatting the input.
                        tracing::warn!("Couldn't find file for mod {};`", mod_name.to_string());
                        return Ok(None);
                    }

                    Err(ModuleResolutionError {
                        module: mod_name.to_string(),
                        kind: ModuleResolutionErrorKind::NotFound { file: default_path },
                    })
                }
                ModError::MultipleCandidates(_, default_path, secondary_path) => {
                    Err(ModuleResolutionError {
                        module: mod_name.to_string(),
                        kind: ModuleResolutionErrorKind::MultipleCandidates {
                            default_path,
                            secondary_path,
                        },
                    })
                }
                ModError::ParserError(_)
                | ModError::CircularInclusion(_)
                | ModError::ModInBlock(_) => Err(ModuleResolutionError {
                    module: mod_name.to_string(),
                    kind: ModuleResolutionErrorKind::ParseError {
                        file: self.directory.path.clone(),
                    },
                }),
            },
        }
    }

    fn push_inline_mod_directory(&mut self, id: symbol::Ident, attrs: &[ast::Attribute]) {
        if let Some(path) = find_path_value(attrs) {
            self.directory.path.push(path.as_str());
            self.directory.ownership = DirectoryOwnership::Owned { relative: None };
        } else {
            let id = id.as_str();
            // We have to push on the current module name in the case of relative
            // paths in order to ensure that any additional module paths from inline
            // `mod x { ... }` come after the relative extension.
            //
            // For example, a `mod z { ... }` inside `x/y.rs` should set the current
            // directory path to `/x/y/z`, not `/x/z` with a relative offset of `y`.
            if let DirectoryOwnership::Owned { relative } = &mut self.directory.ownership {
                if let Some(ident) = relative.take() {
                    // remove the relative offset
                    self.directory.path.push(ident.as_str());

                    // In the case where there is an x.rs and an ./x directory we want
                    // to prevent adding x twice. For example, ./x/x
                    if self.directory.path.exists() && !self.directory.path.join(id).exists() {
                        return;
                    }
                }
            }
            self.directory.path.push(id);
        }
    }

    fn find_mods_outside_of_ast(
        &self,
        attrs: &[ast::Attribute],
        sub_mod: &Module<'ast>,
    ) -> Vec<(PathBuf, DirectoryOwnership, Module<'ast>)> {
        // Filter nested path, like `#[cfg_attr(feature = "foo", path = "bar.rs")]`.
        let mut path_visitor = visitor::PathVisitor::default();
        for attr in attrs.iter() {
            if let Some(meta) = attr.meta() {
                path_visitor.visit_meta_item(&meta)
            }
        }
        let mut result = vec![];
        for path in path_visitor.paths() {
            let mut actual_path = self.directory.path.clone();
            actual_path.push(&path);
            if !actual_path.exists() {
                continue;
            }
            if self.psess.is_file_parsed(&actual_path) {
                // If the specified file is already parsed, then we just use that.
                result.push((
                    actual_path,
                    DirectoryOwnership::Owned { relative: None },
                    sub_mod.clone(),
                ));
                continue;
            }
            let (attrs, items, span) =
                match Parser::parse_file_as_module(self.psess, &actual_path, sub_mod.span) {
                    Ok((ref attrs, _, _)) if contains_skip(attrs) => continue,
                    Ok(m) => m,
                    Err(..) => continue,
                };

            result.push((
                actual_path,
                DirectoryOwnership::Owned { relative: None },
                Module::new(
                    span,
                    Some(Cow::Owned(ast::ModKind::Unloaded)),
                    Cow::Owned(items),
                    Cow::Owned(attrs),
                ),
            ));
        }
        result
    }
}

fn path_value(attr: &ast::Attribute) -> Option<Symbol> {
    if attr.has_name(sym::path) {
        attr.value_str()
    } else {
        None
    }
}

// N.B., even when there are multiple `#[path = ...]` attributes, we just need to
// examine the first one, since rustc ignores the second and the subsequent ones
// as unused attributes.
fn find_path_value(attrs: &[ast::Attribute]) -> Option<Symbol> {
    attrs.iter().flat_map(path_value).next()
}

fn is_cfg_if(item: &ast::Item) -> bool {
    match item.kind {
        ast::ItemKind::MacCall(ref mac) => {
            if let Some(first_segment) = mac.path.segments.first() {
                if first_segment.ident.name == Symbol::intern("cfg_if") {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

/// Trust (T14d): the directory of the nearest manifest with a `[package]`
/// table at or above `path`'s directory: the package that compiles it.
fn owning_package_dir(path: &Path) -> Option<PathBuf> {
    let path = path.canonicalize().ok()?;
    let mut directory = path.parent();
    while let Some(dir) = directory {
        let owns = std::fs::read_to_string(dir.join("Cargo.toml"))
            .ok()
            .and_then(|text| text.parse::<toml::Table>().ok())
            .is_some_and(|manifest| manifest.contains_key("package"));
        if owns {
            return Some(dir.to_path_buf());
        }
        directory = dir.parent();
    }
    None
}

// Trust (T14d): `include!` or a path ending in it (`std::include!`).
fn is_include_path(path: &ast::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident.name == sym::include)
}

fn is_include(item: &ast::Item) -> bool {
    matches!(item.kind, ast::ItemKind::MacCall(ref mac) if is_include_path(&mac.path))
}

/// Trust (T14d): every `include!` that is not a module item: in a function
/// body, an expression, a statement or an associated-item list. Module items
/// (at file level or in an inline `mod`) are the resolver's.
struct NestedIncludeVisitor<'a> {
    psess: &'a ParseSess,
    found: Vec<UnfollowedInclude>,
}

impl<'a> NestedIncludeVisitor<'a> {
    fn visit_module_item(&mut self, item: &ast::Item) {
        match item.kind {
            ast::ItemKind::MacCall(ref mac) if is_include_path(&mac.path) => {}
            ast::ItemKind::Mod(_, _, ast::ModKind::Loaded(ref items, ast::Inline::Yes, ..)) => {
                for item in items.iter() {
                    self.visit_module_item(item);
                }
            }
            _ => self.visit_item(item),
        }
    }
}

impl<'a, 'ast> Visitor<'ast> for NestedIncludeVisitor<'a> {
    fn visit_mac_call(&mut self, mac: &'ast ast::MacCall) {
        if is_include_path(&mac.path) {
            self.found.push(UnfollowedInclude {
                location: format!(
                    "{}:{}",
                    self.psess.span_to_filename(mac.span()),
                    self.psess.line_of_byte_pos(mac.span().lo())
                ),
                reason: "it is not in module-item position",
            });
        }
        rustc_ast::visit::walk_mac(self, mac);
    }
}

fn is_cfg_select(item: &ast::Item) -> bool {
    match item.kind {
        ast::ItemKind::MacCall(ref mac) => {
            if let Some(last_segment) = mac.path.segments.last() {
                if last_segment.ident.name == Symbol::intern("cfg_select") {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}
