// module_lower: sound lowering of an import-free ES module to a strict Script.
//
// An import-free module whose top level uses no module-only construct is
// SEMANTICALLY EQUIVALENT to a strict Script with the `export` keywords
// stripped: the export record is unobservable with no importer, module
// bindings and strict-eval bindings agree (the interpreter runs a strict body
// in a fresh declarative environment — interp.rs `run_script` — so top-level
// `var`/`function` do NOT reflect onto the global object either way), and a
// synchronous module evaluation drains and completes exactly like the strict
// script goal. The ONLY differences a strict script cannot reproduce are the
// module-only constructs guarded below; each one REFUSES (sound NoCoverage),
// never a guessed trace. Zero wrong traces is the bar.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::HashSet;

use trust_js_parse::ast::{
    Arg, Class, ClassElement, DeclKind, Expr, ExportDecl, ForHead, ForInit, Func, ImportDecl,
    ModuleExportName, ObjProp, Pat, PropKey, Stmt,
};
use trust_js_parse::Program;

/// Function-nesting context for the `this` / `super` / `new.target` / `await`
/// guards. All four are lexical through arrow functions, so an arrow inherits;
/// a non-arrow function establishes fresh bindings.
#[derive(Clone, Copy)]
struct Ctx {
    /// Inside a non-arrow function body (or a class field initializer / static
    /// block), where `this` / `super` / `new.target` have a fresh binding that
    /// a strict script and a module agree on. False at module top level, where
    /// module `this` is `undefined` but a strict-eval body's `this` is
    /// `globalThis`.
    in_regular_fn: bool,
    /// The nearest enclosing await context is an async function (arrows
    /// transparent). False at module top level, where an `await` is top-level
    /// await (an async module) that the strict-script model cannot reproduce.
    in_async: bool,
}

const TOP: Ctx = Ctx { in_regular_fn: false, in_async: false };

/// A context whose `this` / `super` / `new.target` bind fresh (a method body,
/// constructor, class field initializer, or static block) and that is not an
/// await context.
const METHODISH: Ctx = Ctx { in_regular_fn: true, in_async: false };

/// Lower an import-free positive module `Program` to an equivalent strict
/// Script, or return a precise refusal reason. Conservative by construction:
/// any construct whose module semantics could differ from a strict script
/// refuses.
pub(crate) fn lower(prog: Program) -> Result<Program, String> {
    // Guard: scan the WHOLE program (top level + every nesting) for a
    // module-only construct.
    for stmt in &prog.body {
        scan_stmt(stmt, TOP)?;
    }
    // Transform: strip the export wrappers. Every disallowed export shape was
    // already refused by the scan, so only `export <decl>` (unwrap) and a
    // from-less `export { … }` (a no-op standalone: its locals are declared —
    // the parser proved it — and the record is unobservable with no importer,
    // so drop it) can reach here.
    let mut body = Vec::with_capacity(prog.body.len());
    for stmt in prog.body {
        match stmt {
            Stmt::Export(ExportDecl::Decl(inner)) => body.push(*inner),
            Stmt::Export(ExportDecl::Named { source: None, .. }) => { /* drop: unobservable */ }
            // `export default <inner>`: emit the inner declaration/binding in
            // place (its local binding + side effects are the only observables
            // with no importer; the export record itself is unobservable).
            Stmt::Export(ExportDecl::Default(inner)) => {
                let (_local, lowered) = lower_default_export(*inner)?;
                body.push(lowered);
            }
            // Star / Named-with-source were refused by the scan; this arm is
            // defensively unreachable, so drop rather than emit a stray `export`
            // into a script body.
            Stmt::Export(_) => {}
            other => body.push(other),
        }
    }
    Ok(Program { body, strict: true })
}

fn scan_stmt(stmt: &Stmt, ctx: Ctx) -> Result<(), String> {
    match stmt {
        Stmt::Expr(e) | Stmt::Throw(e) => scan_expr(e, ctx),
        Stmt::Block(stmts) => scan_stmts(stmts, ctx),
        Stmt::Empty | Stmt::Debugger | Stmt::Continue(_) | Stmt::Break(_) => Ok(()),
        Stmt::Decl { kind, decls } => {
            if matches!(kind, DeclKind::AwaitUsing) && !ctx.in_async {
                return Err(
                    "top-level `await using` declaration (async module, out of slice)".to_string(),
                );
            }
            for (pat, init) in decls {
                scan_pat(pat, ctx)?;
                if let Some(e) = init {
                    scan_expr(e, ctx)?;
                }
            }
            Ok(())
        }
        Stmt::If { test, cons, alt } => {
            scan_expr(test, ctx)?;
            scan_stmt(cons, ctx)?;
            if let Some(a) = alt {
                scan_stmt(a, ctx)?;
            }
            Ok(())
        }
        Stmt::DoWhile { body, test } | Stmt::While { test, body } => {
            scan_expr(test, ctx)?;
            scan_stmt(body, ctx)
        }
        Stmt::For { init, test, update, body } => {
            if let Some(init) = init {
                match init {
                    ForInit::Decl(_, decls) => {
                        for (pat, e) in decls {
                            scan_pat(pat, ctx)?;
                            if let Some(e) = e {
                                scan_expr(e, ctx)?;
                            }
                        }
                    }
                    ForInit::Expr(e) => scan_expr(e, ctx)?,
                }
            }
            if let Some(e) = test {
                scan_expr(e, ctx)?;
            }
            if let Some(e) = update {
                scan_expr(e, ctx)?;
            }
            scan_stmt(body, ctx)
        }
        Stmt::ForIn { left, right, body } => {
            scan_forhead(left, ctx)?;
            scan_expr(right, ctx)?;
            scan_stmt(body, ctx)
        }
        Stmt::ForOf { left, right, body, is_await } => {
            if *is_await && !ctx.in_async {
                return Err("top-level `for await` (async module, out of slice)".to_string());
            }
            scan_forhead(left, ctx)?;
            scan_expr(right, ctx)?;
            scan_stmt(body, ctx)
        }
        Stmt::Return(e) => {
            if let Some(e) = e {
                scan_expr(e, ctx)?;
            }
            Ok(())
        }
        Stmt::With { obj, body } => {
            scan_expr(obj, ctx)?;
            scan_stmt(body, ctx)
        }
        Stmt::Labeled { body, .. } => scan_stmt(body, ctx),
        Stmt::Switch { disc, cases } => {
            scan_expr(disc, ctx)?;
            for c in cases {
                if let Some(t) = &c.test {
                    scan_expr(t, ctx)?;
                }
                scan_stmts(&c.body, ctx)?;
            }
            Ok(())
        }
        Stmt::Try { block, catch, finally } => {
            scan_stmts(block, ctx)?;
            if let Some((pat, body)) = catch {
                if let Some(p) = pat {
                    scan_pat(p, ctx)?;
                }
                scan_stmts(body, ctx)?;
            }
            if let Some(body) = finally {
                scan_stmts(body, ctx)?;
            }
            Ok(())
        }
        Stmt::FuncDecl(f) => scan_func(f, ctx),
        Stmt::ClassDecl(c) => scan_class(c, ctx),
        Stmt::Import(_) => {
            Err("`import` declaration (module loader, out of slice)".to_string())
        }
        Stmt::Export(exp) => match exp {
            ExportDecl::Star { .. } => {
                Err("`export *` re-export (module loader, out of slice)".to_string())
            }
            ExportDecl::Named { source: Some(_), .. } => {
                Err("`export … from` re-export (module loader, out of slice)".to_string())
            }
            // `export default <inner>`: with no importer the export record is
            // unobservable, so the lowering emits the inner declaration/binding
            // in place (see `lower_default_export`) and only the inner's own
            // constructs matter — scan it in the same context.
            ExportDecl::Default(inner) => scan_stmt(inner, ctx),
            // A from-less `export { … }` is dropped by the transform (no-op);
            // its specs are declared locals (parser-proved), nothing to scan.
            ExportDecl::Named { source: None, .. } => Ok(()),
            // `export <decl>`: scan the wrapped declaration in the same context.
            ExportDecl::Decl(inner) => scan_stmt(inner, ctx),
        },
    }
}

fn scan_stmts(stmts: &[Stmt], ctx: Ctx) -> Result<(), String> {
    for s in stmts {
        scan_stmt(s, ctx)?;
    }
    Ok(())
}

fn scan_forhead(head: &ForHead, ctx: Ctx) -> Result<(), String> {
    match head {
        ForHead::Decl(_, pat) | ForHead::Pat(pat) => scan_pat(pat, ctx),
    }
}

fn scan_expr(expr: &Expr, ctx: Ctx) -> Result<(), String> {
    match expr {
        Expr::Ident(_)
        | Expr::Null
        | Expr::Bool(_)
        | Expr::Num(_)
        | Expr::BigInt(_)
        | Expr::Str { .. }
        | Expr::Regex { .. }
        | Expr::PrivateRef(_) => Ok(()),
        Expr::This => {
            if ctx.in_regular_fn {
                Ok(())
            } else {
                Err("module top-level `this` (is `undefined`, not `globalThis`)".to_string())
            }
        }
        Expr::NewTarget => {
            if ctx.in_regular_fn {
                Ok(())
            } else {
                Err("module top-level `new.target`".to_string())
            }
        }
        Expr::ImportMeta => Err("`import.meta` (module meta object, out of slice)".to_string()),
        Expr::ImportCall(_) => {
            Err("dynamic `import()` (module loader, out of slice)".to_string())
        }
        Expr::SuperProp(prop) => {
            if !ctx.in_regular_fn {
                return Err("module top-level `super`".to_string());
            }
            scan_propkey(prop, ctx)
        }
        Expr::SuperCall(args) => {
            if !ctx.in_regular_fn {
                return Err("module top-level `super`".to_string());
            }
            scan_args(args, ctx)
        }
        Expr::Await(arg) => {
            if !ctx.in_async {
                return Err("top-level `await` (async module, out of slice)".to_string());
            }
            scan_expr(arg, ctx)
        }
        Expr::Template { exprs, .. } => scan_exprs(exprs, ctx),
        Expr::TaggedTemplate { tag, exprs, .. } => {
            scan_expr(tag, ctx)?;
            scan_exprs(exprs, ctx)
        }
        Expr::Array { elems, .. } => {
            for e in elems.iter().flatten() {
                scan_arg(e, ctx)?;
            }
            Ok(())
        }
        Expr::Object(props) => {
            for p in props {
                scan_objprop(p, ctx)?;
            }
            Ok(())
        }
        Expr::Function(f) | Expr::Arrow(f) => scan_func(f, ctx),
        Expr::Class(c) => scan_class(c, ctx),
        Expr::Paren(e) | Expr::Unary { arg: e, .. } | Expr::Update { arg: e, .. } => {
            scan_expr(e, ctx)
        }
        Expr::Seq(exprs) => scan_exprs(exprs, ctx),
        Expr::Binary { left, right, .. } | Expr::Logical { left, right, .. } => {
            scan_expr(left, ctx)?;
            scan_expr(right, ctx)
        }
        Expr::Assign { target, value, .. } => {
            scan_pat(target, ctx)?;
            scan_expr(value, ctx)
        }
        Expr::Cond { test, cons, alt } => {
            scan_expr(test, ctx)?;
            scan_expr(cons, ctx)?;
            scan_expr(alt, ctx)
        }
        Expr::Member { obj, prop, .. } => {
            scan_expr(obj, ctx)?;
            scan_propkey(prop, ctx)
        }
        Expr::Call { callee, args, .. } => {
            scan_expr(callee, ctx)?;
            scan_args(args, ctx)
        }
        Expr::New { callee, args } => {
            scan_expr(callee, ctx)?;
            scan_args(args, ctx)
        }
        Expr::Yield { arg, .. } => {
            if let Some(a) = arg {
                scan_expr(a, ctx)?;
            }
            Ok(())
        }
    }
}

fn scan_exprs(exprs: &[Expr], ctx: Ctx) -> Result<(), String> {
    for e in exprs {
        scan_expr(e, ctx)?;
    }
    Ok(())
}

fn scan_args(args: &[Arg], ctx: Ctx) -> Result<(), String> {
    for a in args {
        scan_arg(a, ctx)?;
    }
    Ok(())
}

fn scan_arg(arg: &Arg, ctx: Ctx) -> Result<(), String> {
    match arg {
        Arg::Expr(e) | Arg::Spread(e) => scan_expr(e, ctx),
    }
}

fn scan_objprop(prop: &ObjProp, ctx: Ctx) -> Result<(), String> {
    match prop {
        ObjProp::KeyValue { key, value } => {
            scan_propkey(key, ctx)?;
            scan_expr(value, ctx)
        }
        ObjProp::Shorthand(_) => Ok(()),
        ObjProp::CoverInit(_, e) => scan_expr(e, ctx),
        ObjProp::Method { key, func, .. } => {
            scan_propkey(key, ctx)?;
            scan_func(func, ctx)
        }
        ObjProp::Spread(e) => scan_expr(e, ctx),
    }
}

fn scan_propkey(key: &PropKey, ctx: Ctx) -> Result<(), String> {
    // A computed key expression is evaluated in the ENCLOSING context (`ctx`),
    // not inside the member/method it keys — so the enclosing `this`/`await`
    // rules apply to it.
    match key {
        PropKey::Computed(e) => scan_expr(e, ctx),
        _ => Ok(()),
    }
}

fn scan_pat(pat: &Pat, ctx: Ctx) -> Result<(), String> {
    match pat {
        Pat::Ident(_) => Ok(()),
        Pat::Expr(e) => scan_expr(e, ctx),
        Pat::Array { elems, rest } => {
            for p in elems.iter().flatten() {
                scan_pat(p, ctx)?;
            }
            if let Some(r) = rest {
                scan_pat(r, ctx)?;
            }
            Ok(())
        }
        Pat::Object { props, rest } => {
            for p in props {
                scan_propkey(&p.key, ctx)?;
                scan_pat(&p.value, ctx)?;
            }
            if let Some(r) = rest {
                scan_pat(r, ctx)?;
            }
            Ok(())
        }
        Pat::Default(inner, e) => {
            scan_pat(inner, ctx)?;
            scan_expr(e, ctx)
        }
        Pat::Rest(inner) => scan_pat(inner, ctx),
    }
}

fn scan_func(func: &Func, outer: Ctx) -> Result<(), String> {
    // Descend into the function with the appropriate binding context. Arrows
    // are transparent to `this`/`super`/`new.target` and to the await context;
    // a non-arrow function establishes fresh ones.
    let inner = Ctx {
        in_regular_fn: if func.is_arrow { outer.in_regular_fn } else { true },
        in_async: if func.is_arrow {
            func.is_async || outer.in_async
        } else {
            func.is_async
        },
    };
    // Parameter default initializers run in the function's own scope (inner).
    for p in &func.params {
        scan_pat(p, inner)?;
    }
    scan_stmts(&func.body, inner)?;
    if let Some(e) = &func.expr_body {
        scan_expr(e, inner)?;
    }
    Ok(())
}

fn scan_class(class: &Class, ctx: Ctx) -> Result<(), String> {
    // The heritage expression is evaluated in the enclosing context.
    if let Some(h) = &class.heritage {
        scan_expr(h, ctx)?;
    }
    for el in &class.elements {
        match el {
            ClassElement::Method { key, func, .. } => {
                // A computed method key is evaluated in the enclosing context.
                scan_propkey(key, ctx)?;
                scan_func(func, ctx)?;
            }
            ClassElement::Field { key, init, .. } => {
                // The computed key is evaluated in the enclosing context; the
                // initializer runs with `this` = the instance (a fresh
                // this/super binding), like a method body.
                scan_propkey(key, ctx)?;
                if let Some(e) = init {
                    scan_expr(e, METHODISH)?;
                }
            }
            ClassElement::StaticBlock(stmts) => {
                // A static block runs with `this` = the class constructor.
                scan_stmts(stmts, METHODISH)?;
            }
        }
    }
    Ok(())
}

// ===========================================================================
// Multi-module linking (increment 2b-part-3): the SOUND conservative subset.
//
// A module M that imports NAMED bindings (or side-effect-only) from sibling
// modules is lowered to (1) an export-stripped strict Script body, plus
// (2) the structured import/export metadata the graph linker needs. Only the
// sound subset is admitted; every richer module shape (default / namespace /
// star / re-export imports & exports, string module-export-names, module-only
// constructs, or a binding that could be MUTATED after its module finished
// evaluating — a live binding) refuses (`Err`), never a guessed trace.
// ===========================================================================

/// One named-import binding request in the sound subset:
/// `import { <imported> as <local> } from "<source>"`.
#[derive(Debug, Clone)]
pub(crate) struct ImportBinding {
    /// The local binding this module introduces.
    pub local: String,
    /// The name exported by the source module (IdentifierName only).
    pub imported: String,
    /// The (unresolved) module specifier as written.
    pub source: String,
}

/// One named RE-EXPORT specifier in the sound subset:
/// `export { <imported> as <exported> } from "<source>"`. Unlike a local
/// export, this introduces NO local binding — the exported name resolves
/// (ResolveExport) directly to `<imported>` of `<source>` (which is itself a
/// covered dependency). All names are IdentifierNames (string
/// module-export-names refuse in `lower_linked`).
#[derive(Debug, Clone)]
pub(crate) struct NamedReexport {
    /// The externally visible export name this module provides.
    pub exported: String,
    /// The name looked up in the source module.
    pub imported: String,
    /// The (unresolved) source module specifier.
    pub source: String,
}

/// A module lowered for the linking lane: its export-stripped strict Script
/// body, the ordered dependency specifiers (source order, drives the DFS
/// evaluation order), the named-import bindings, and the `(exported, local)`
/// export map (both IdentifierNames).
#[derive(Debug, Clone)]
pub(crate) struct LoweredModule {
    pub body: Program,
    /// Every import declaration's specifier, in source order (side-effect
    /// imports included). Duplicates preserved (first occurrence orders the
    /// DFS visit; later ones are already-visited DAG re-references).
    pub dep_specs: Vec<String>,
    pub imports: Vec<ImportBinding>,
    /// `(local, source)` namespace-import requests: `import * as <local> from
    /// "<source>"` binds `local` to the source module's Module Namespace Exotic
    /// Object (built from the source's complete, sorted export set at link time).
    pub namespace_imports: Vec<(String, String)>,
    /// `(exported_name, local_name)` pairs — the module's LOCAL exports only
    /// (re-exports are separate). Within the subset an exported name is unique
    /// (a duplicate is a parse-time SyntaxError parse_module catches). A
    /// `default` export appears here as `("default", <local>)` — a real local
    /// for a named `export default function f`/`class C`, else the synthetic
    /// `default` binding the anonymous / expression forms lower to.
    pub exports: Vec<(String, String)>,
    /// `export { a, b as c } from "src"` — named re-exports. Each re-exports a
    /// name of `src` (a dependency); no local binding is created.
    pub named_reexports: Vec<NamedReexport>,
    /// `export * from "src"` — the source specifiers whose every named export
    /// (except `default`, except names this module provides locally / by an
    /// explicit re-export) this module additionally exports. Ambiguity across
    /// two star sources is resolved by the graph linker (§16.2.1.6.3).
    pub star_reexports: Vec<String>,
    /// `export * as ns from "src"` — `(ns, src)`: export a Module Namespace
    /// Exotic Object of `src` under the name `ns`.
    pub namespace_reexports: Vec<(String, String)>,
}

/// Lower a parsed module `Program` for the linking lane, or refuse (sound
/// `Err`). Conservative by construction: any construct whose linked module
/// semantics this lane cannot reproduce byte-for-byte refuses.
pub(crate) fn lower_linked(prog: Program) -> Result<LoweredModule, String> {
    let mut body_stmts: Vec<Stmt> = Vec::with_capacity(prog.body.len());
    let mut dep_specs: Vec<String> = Vec::new();
    let mut imports: Vec<ImportBinding> = Vec::new();
    let mut namespace_imports: Vec<(String, String)> = Vec::new();
    let mut exports: Vec<(String, String)> = Vec::new();
    let mut named_reexports: Vec<NamedReexport> = Vec::new();
    let mut star_reexports: Vec<String> = Vec::new();
    let mut namespace_reexports: Vec<(String, String)> = Vec::new();

    for stmt in prog.body {
        match stmt {
            Stmt::Import(ImportDecl {
                default,
                namespace,
                named,
                source,
            }) => {
                // `import d from "src"`: the default binding is a named import of
                // the reserved export name "default".
                if let Some(local) = default {
                    imports.push(ImportBinding {
                        local,
                        imported: "default".to_string(),
                        source: source.clone(),
                    });
                }
                // `import * as ns from "src"`: bind `ns` to src's namespace object.
                if let Some(local) = namespace {
                    namespace_imports.push((local, source.clone()));
                }
                for entry in named {
                    let imported = match entry.imported {
                        ModuleExportName::Ident(n) => n,
                        ModuleExportName::Str(_) => {
                            return Err("string module-export-name import (out of slice)".to_string())
                        }
                    };
                    imports.push(ImportBinding {
                        local: entry.local,
                        imported,
                        source: source.clone(),
                    });
                }
                dep_specs.push(source);
            }
            // `export * from "src"` / `export * as ns from "src"`: a star or
            // namespace re-export. `src` becomes a dependency (added to
            // dep_specs so the graph builder resolves + cycle-detects it).
            Stmt::Export(ExportDecl::Star { alias, source }) => {
                match alias {
                    None => star_reexports.push(source.clone()),
                    Some(ModuleExportName::Ident(ns)) => {
                        namespace_reexports.push((ns, source.clone()))
                    }
                    Some(ModuleExportName::Str(_)) => {
                        return Err(
                            "string module-export-name in `export * as` (out of slice)".to_string(),
                        )
                    }
                }
                dep_specs.push(source);
            }
            // `export { a, b as c } from "src"`: named re-exports. Each names a
            // binding of `src` (a dependency) — no local binding introduced.
            Stmt::Export(ExportDecl::Named { specs, source: Some(source) }) => {
                for e in specs {
                    let imported = match e.local {
                        ModuleExportName::Ident(n) => n,
                        ModuleExportName::Str(_) => {
                            return Err(
                                "string module-export-name re-export source (out of slice)"
                                    .to_string(),
                            )
                        }
                    };
                    let exported = match e.exported {
                        ModuleExportName::Ident(n) => n,
                        ModuleExportName::Str(_) => {
                            return Err(
                                "string module-export-name re-export (out of slice)".to_string(),
                            )
                        }
                    };
                    named_reexports.push(NamedReexport { exported, imported, source: source.clone() });
                }
                dep_specs.push(source);
            }
            Stmt::Export(ExportDecl::Default(inner)) => {
                let (local, lowered) = lower_default_export(*inner)?;
                exports.push(("default".to_string(), local));
                body_stmts.push(lowered);
            }
            Stmt::Export(ExportDecl::Named { specs, source: None }) => {
                // A from-less `export { a as b }`: b is the export name, a is an
                // already-declared local (parser-proved). No body contribution.
                for e in specs {
                    let local = match e.local {
                        ModuleExportName::Ident(n) => n,
                        ModuleExportName::Str(_) => {
                            return Err("string module-export-name local (out of slice)".to_string())
                        }
                    };
                    let exported = match e.exported {
                        ModuleExportName::Ident(n) => n,
                        ModuleExportName::Str(_) => {
                            return Err("string module-export-name (out of slice)".to_string())
                        }
                    };
                    exports.push((exported, local));
                }
            }
            Stmt::Export(ExportDecl::Decl(inner)) => {
                for name in export_decl_names(&inner)? {
                    exports.push((name.clone(), name));
                }
                body_stmts.push(*inner);
            }
            other => body_stmts.push(other),
        }
    }

    // The export-stripped body must use no module-only construct (top-level
    // this/await/super/new.target/import.meta/dynamic import): each refuses.
    for s in &body_stmts {
        scan_stmt(s, TOP)?;
    }

    // Live-binding guard: capturing an exported binding's VALUE (rather than an
    // indirect cell) is only faithful when that binding is never mutated after
    // its module finished evaluating. Over-approximate soundly: if ANY exported
    // local name is ever an assignment / update target anywhere in the module
    // (including inside a function that may run later), refuse. `const`,
    // `function`, `class`, and never-reassigned `let`/`var` exports pass.
    let mut assigned: HashSet<String> = HashSet::new();
    collect_assigned_idents(&body_stmts, &mut assigned);
    for (_, local) in &exports {
        if assigned.contains(local) {
            return Err(format!(
                "exported binding `{local}` is reassigned (live binding, out of slice)"
            ));
        }
    }

    Ok(LoweredModule {
        body: Program { body: body_stmts, strict: true },
        dep_specs,
        imports,
        namespace_imports,
        exports,
        named_reexports,
        star_reexports,
        namespace_reexports,
    })
}

/// Lower an `export default <inner>` to `(local_name, statement)`: the local
/// binding the default export's value ends up in (captured as export
/// "default"), plus the in-place statement that produces it. Faithful to the
/// SetFunctionName / BoundNames rules:
///
/// - `export default function f(){}` / `class C{}` (NAMED): the declaration is
///   emitted verbatim; the export's local is its own name `f`/`C` (BoundNames),
///   and its `.name` is `f`/`C`. There is no separate `*default*` binding.
/// - `export default function(){}` / `class{}` (ANONYMOUS): the declaration is
///   given the name `default` (SetFunctionName gives `.name` "default"); the
///   local is the reserved word `default` — unreferenceable in source, so
///   binding under it collides with nothing and is unobservable but for the
///   captured value. A function default still hoists; a class default is
///   evaluated in place — exactly as the real forms do.
/// - `export default <AssignmentExpression>`: lowered to `let default = <expr>`.
///   NamedEvaluation over the binding name `default` reproduces the spec's
///   `NamedEvaluation(expr, "default")` for an anonymous function/class/arrow
///   value; any other value is just captured.
fn lower_default_export(inner: Stmt) -> Result<(String, Stmt), String> {
    match inner {
        Stmt::FuncDecl(mut f) => {
            let local = match &f.name {
                Some(n) => n.clone(),
                None => {
                    f.name = Some("default".to_string());
                    "default".to_string()
                }
            };
            Ok((local, Stmt::FuncDecl(f)))
        }
        Stmt::ClassDecl(mut c) => {
            let local = match &c.name {
                Some(n) => n.clone(),
                None => {
                    c.name = Some("default".to_string());
                    "default".to_string()
                }
            };
            Ok((local, Stmt::ClassDecl(c)))
        }
        Stmt::Expr(e) => {
            let decl = Stmt::Decl {
                kind: DeclKind::Let,
                decls: vec![(Pat::Ident("default".to_string()), Some(e))],
            };
            Ok(("default".to_string(), decl))
        }
        _ => Err("unsupported `export default` shape (out of slice)".to_string()),
    }
}

/// The BoundNames of an `export <Declaration>` inner statement, or `Err` for an
/// out-of-slice declaration kind.
fn export_decl_names(inner: &Stmt) -> Result<Vec<String>, String> {
    match inner {
        Stmt::FuncDecl(f) => Ok(vec![f
            .name
            .clone()
            .ok_or_else(|| "unnamed exported function".to_string())?]),
        Stmt::ClassDecl(c) => Ok(vec![c
            .name
            .clone()
            .ok_or_else(|| "unnamed exported class".to_string())?]),
        Stmt::Decl { kind, decls } => {
            if matches!(kind, DeclKind::Using | DeclKind::AwaitUsing) {
                return Err("`using` export declaration (out of slice)".to_string());
            }
            let mut names = Vec::new();
            for (pat, _) in decls {
                crate::interp::hoist::pat_bound_names(pat, &mut names);
            }
            Ok(names)
        }
        _ => Err("unsupported export declaration shape".to_string()),
    }
}

// --- Assignment / update target collection (the live-binding scan) ---------

pub(crate) fn collect_assigned_idents(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        ca_stmt(s, out);
    }
}

fn ca_stmts(stmts: &[Stmt], out: &mut HashSet<String>) {
    for s in stmts {
        ca_stmt(s, out);
    }
}

fn ca_stmt(s: &Stmt, out: &mut HashSet<String>) {
    match s {
        Stmt::Expr(e) | Stmt::Throw(e) => ca_expr(e, out),
        Stmt::Block(b) => ca_stmts(b, out),
        Stmt::Empty | Stmt::Debugger | Stmt::Continue(_) | Stmt::Break(_) => {}
        Stmt::Decl { decls, .. } => {
            for (pat, init) in decls {
                ca_pat_exprs(pat, out);
                if let Some(e) = init {
                    ca_expr(e, out);
                }
            }
        }
        Stmt::If { test, cons, alt } => {
            ca_expr(test, out);
            ca_stmt(cons, out);
            if let Some(a) = alt {
                ca_stmt(a, out);
            }
        }
        Stmt::DoWhile { body, test } | Stmt::While { test, body } => {
            ca_expr(test, out);
            ca_stmt(body, out);
        }
        Stmt::For { init, test, update, body } => {
            if let Some(init) = init {
                match init {
                    ForInit::Decl(_, decls) => {
                        for (p, e) in decls {
                            ca_pat_exprs(p, out);
                            if let Some(e) = e {
                                ca_expr(e, out);
                            }
                        }
                    }
                    ForInit::Expr(e) => ca_expr(e, out),
                }
            }
            if let Some(e) = test {
                ca_expr(e, out);
            }
            if let Some(e) = update {
                ca_expr(e, out);
            }
            ca_stmt(body, out);
        }
        Stmt::ForIn { left, right, body } | Stmt::ForOf { left, right, body, .. } => {
            ca_forhead(left, out);
            ca_expr(right, out);
            ca_stmt(body, out);
        }
        Stmt::Return(e) => {
            if let Some(e) = e {
                ca_expr(e, out);
            }
        }
        Stmt::With { obj, body } => {
            ca_expr(obj, out);
            ca_stmt(body, out);
        }
        Stmt::Labeled { body, .. } => ca_stmt(body, out),
        Stmt::Switch { disc, cases } => {
            ca_expr(disc, out);
            for c in cases {
                if let Some(t) = &c.test {
                    ca_expr(t, out);
                }
                ca_stmts(&c.body, out);
            }
        }
        Stmt::Try { block, catch, finally } => {
            ca_stmts(block, out);
            if let Some((p, b)) = catch {
                if let Some(p) = p {
                    ca_pat_exprs(p, out);
                }
                ca_stmts(b, out);
            }
            if let Some(f) = finally {
                ca_stmts(f, out);
            }
        }
        Stmt::FuncDecl(f) => ca_func(f, out),
        Stmt::ClassDecl(c) => ca_class(c, out),
        // The stripped body carries no import/export declarations.
        Stmt::Import(_) | Stmt::Export(_) => {}
    }
}

fn ca_forhead(h: &ForHead, out: &mut HashSet<String>) {
    match h {
        // `for (x of …)` assigns to the existing binding `x`.
        ForHead::Pat(pat) => collect_target_names(pat, out),
        ForHead::Decl(_, pat) => ca_pat_exprs(pat, out),
    }
}

fn ca_expr(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Assign { target, value, .. } => {
            collect_target_names(target, out);
            ca_pat_exprs(target, out);
            ca_expr(value, out);
        }
        Expr::Update { arg, .. } => {
            collect_update_target(arg, out);
            ca_expr(arg, out);
        }
        Expr::Ident(_)
        | Expr::This
        | Expr::Null
        | Expr::Bool(_)
        | Expr::Num(_)
        | Expr::BigInt(_)
        | Expr::Str { .. }
        | Expr::Regex { .. }
        | Expr::NewTarget
        | Expr::ImportMeta
        | Expr::PrivateRef(_) => {}
        Expr::Template { exprs, .. } => ca_exprs(exprs, out),
        Expr::TaggedTemplate { tag, exprs, .. } => {
            ca_expr(tag, out);
            ca_exprs(exprs, out);
        }
        Expr::Array { elems, .. } => {
            for el in elems.iter().flatten() {
                ca_arg(el, out);
            }
        }
        Expr::Object(props) => {
            for p in props {
                ca_objprop(p, out);
            }
        }
        Expr::Function(f) | Expr::Arrow(f) => ca_func(f, out),
        Expr::Class(c) => ca_class(c, out),
        Expr::Paren(e) | Expr::Unary { arg: e, .. } | Expr::Await(e) => ca_expr(e, out),
        Expr::Seq(es) => ca_exprs(es, out),
        Expr::Binary { left, right, .. } | Expr::Logical { left, right, .. } => {
            ca_expr(left, out);
            ca_expr(right, out);
        }
        Expr::Cond { test, cons, alt } => {
            ca_expr(test, out);
            ca_expr(cons, out);
            ca_expr(alt, out);
        }
        Expr::Member { obj, prop, .. } => {
            ca_expr(obj, out);
            ca_propkey(prop, out);
        }
        Expr::Call { callee, args, .. } => {
            ca_expr(callee, out);
            ca_args(args, out);
        }
        Expr::New { callee, args } => {
            ca_expr(callee, out);
            ca_args(args, out);
        }
        Expr::ImportCall(es) => ca_exprs(es, out),
        Expr::SuperProp(pk) => ca_propkey(pk, out),
        Expr::SuperCall(args) => ca_args(args, out),
        Expr::Yield { arg, .. } => {
            if let Some(a) = arg {
                ca_expr(a, out);
            }
        }
    }
}

fn ca_exprs(es: &[Expr], out: &mut HashSet<String>) {
    for e in es {
        ca_expr(e, out);
    }
}

fn ca_args(args: &[Arg], out: &mut HashSet<String>) {
    for a in args {
        ca_arg(a, out);
    }
}

fn ca_arg(a: &Arg, out: &mut HashSet<String>) {
    match a {
        Arg::Expr(e) | Arg::Spread(e) => ca_expr(e, out),
    }
}

fn ca_objprop(p: &ObjProp, out: &mut HashSet<String>) {
    match p {
        ObjProp::KeyValue { key, value } => {
            ca_propkey(key, out);
            ca_expr(value, out);
        }
        ObjProp::Shorthand(_) => {}
        ObjProp::CoverInit(_, e) => ca_expr(e, out),
        ObjProp::Method { key, func, .. } => {
            ca_propkey(key, out);
            ca_func(func, out);
        }
        ObjProp::Spread(e) => ca_expr(e, out),
    }
}

fn ca_propkey(k: &PropKey, out: &mut HashSet<String>) {
    if let PropKey::Computed(e) = k {
        ca_expr(e, out);
    }
}

fn ca_func(f: &Func, out: &mut HashSet<String>) {
    for p in &f.params {
        ca_pat_exprs(p, out);
    }
    ca_stmts(&f.body, out);
    if let Some(e) = &f.expr_body {
        ca_expr(e, out);
    }
}

fn ca_class(c: &Class, out: &mut HashSet<String>) {
    if let Some(h) = &c.heritage {
        ca_expr(h, out);
    }
    for el in &c.elements {
        match el {
            ClassElement::Method { key, func, .. } => {
                ca_propkey(key, out);
                ca_func(func, out);
            }
            ClassElement::Field { key, init, .. } => {
                ca_propkey(key, out);
                if let Some(e) = init {
                    ca_expr(e, out);
                }
            }
            ClassElement::StaticBlock(stmts) => ca_stmts(stmts, out),
        }
    }
}

/// Expressions embedded inside a binding/assignment pattern (default
/// initializers, computed keys, member targets) — walked for nested assigns.
fn ca_pat_exprs(p: &Pat, out: &mut HashSet<String>) {
    match p {
        Pat::Ident(_) => {}
        Pat::Expr(e) => ca_expr(e, out),
        Pat::Array { elems, rest } => {
            for e in elems.iter().flatten() {
                ca_pat_exprs(e, out);
            }
            if let Some(r) = rest {
                ca_pat_exprs(r, out);
            }
        }
        Pat::Object { props, rest } => {
            for pp in props {
                ca_propkey(&pp.key, out);
                ca_pat_exprs(&pp.value, out);
            }
            if let Some(r) = rest {
                ca_pat_exprs(r, out);
            }
        }
        Pat::Default(inner, e) => {
            ca_pat_exprs(inner, out);
            ca_expr(e, out);
        }
        Pat::Rest(inner) => ca_pat_exprs(inner, out),
    }
}

/// The simple-identifier binding names an assignment PATTERN writes to (a
/// member target `Pat::Expr` writes an object property, not a binding).
fn collect_target_names(p: &Pat, out: &mut HashSet<String>) {
    match p {
        Pat::Ident(n) => {
            out.insert(n.clone());
        }
        Pat::Expr(_) => {}
        Pat::Array { elems, rest } => {
            for e in elems.iter().flatten() {
                collect_target_names(e, out);
            }
            if let Some(r) = rest {
                collect_target_names(r, out);
            }
        }
        Pat::Object { props, rest } => {
            for pp in props {
                collect_target_names(&pp.value, out);
            }
            if let Some(r) = rest {
                collect_target_names(r, out);
            }
        }
        Pat::Default(inner, _) | Pat::Rest(inner) => collect_target_names(inner, out),
    }
}

fn collect_update_target(e: &Expr, out: &mut HashSet<String>) {
    match e {
        Expr::Ident(n) => {
            out.insert(n.clone());
        }
        Expr::Paren(inner) => collect_update_target(inner, out),
        _ => {}
    }
}
