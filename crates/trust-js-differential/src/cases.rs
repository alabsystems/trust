// Case preparation: corpus test file → frontmatter → mandated run modes +
// harness-include assembly (RUN-MODE CONTRACT). Non-raw runs prepend the
// default includes [harness/assert.js, harness/sta.js], then the frontmatter
// includes in frontmatter order, deduped. Raw runs get no driver, no includes.
// Fail-closed: an unparseable case is an error the caller must count as a
// tool failure, never a silent skip.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::frontmatter::{parse_frontmatter, Frontmatter};
use crate::heads::{AssembledCase, RunMode};

/// A corpus case with its mandated modes, ready to be assembled per mode.
#[derive(Debug, Clone)]
pub struct PreparedCase {
    pub rel_path: String,
    pub abs_path: PathBuf,
    pub body: String,
    /// Parsed per the case-model contract; negative-test interpretation and
    /// feature gating consume it post-M0.
    #[allow(dead_code)]
    pub frontmatter: Frontmatter,
    /// Absolute include paths for non-raw modes (defaults + frontmatter).
    pub includes: Vec<PathBuf>,
    pub modes: Vec<RunMode>,
}

/// The RUN-MODE CONTRACT: module ? [module] : raw ? [raw] :
/// onlyStrict ? [strict] : noStrict ? [bare] : [bare, strict].
///
/// The `module` flag wins over everything: a module-goal test runs ONCE as an ES
/// module (always strict — no bare/strict split), evaluated from its real corpus
/// location so relative imports resolve. It takes precedence over `raw` because a
/// module file spawned directly as a plain script (the raw lane) would be a
/// spurious SyntaxError (module syntax is not valid in a script). `onlyStrict`/
/// `noStrict` are meaningless for modules (modules are always strict).
pub fn mandated_modes(fm: &Frontmatter) -> Vec<RunMode> {
    if fm.has_flag("module") {
        vec![RunMode::Module]
    } else if fm.has_flag("raw") {
        vec![RunMode::Raw]
    } else if fm.has_flag("onlyStrict") {
        vec![RunMode::Strict]
    } else if fm.has_flag("noStrict") {
        vec![RunMode::Bare]
    } else {
        vec![RunMode::Bare, RunMode::Strict]
    }
}

/// Default + async + frontmatter includes as absolute harness paths, deduped,
/// in that order.
///
/// The async-test-harness protocol: a `flags: [async]` case signals completion
/// by calling `$DONE()`, which is defined by `harness/doneprintHandle.js`
/// (it `print`s `Test262:AsyncTestComplete` / `Test262:AsyncTestFailure:<err>`).
/// Real test262 harnesses AUTO-ADD `doneprintHandle.js` for async tests — it is
/// never listed in a test's `includes` frontmatter (verified: 0 corpus cases
/// declare it) — so we prepend it here after the defaults. `asyncHelpers.js`
/// (the `asyncTest`/`assert.throwsAsync` wrappers), by contrast, IS declared in
/// the frontmatter includes whenever a test uses it (verified: 0 corpus cases
/// call `asyncTest` without declaring it), so it flows through the normal
/// frontmatter path below — no special-casing needed. Dedup keeps a single copy
/// even if a case ever declared `doneprintHandle.js` itself.
pub fn assemble_includes(corpus: &Path, fm: &Frontmatter) -> Vec<PathBuf> {
    let mut names: Vec<&str> = vec!["assert.js", "sta.js"];
    if fm.has_flag("async") {
        names.push("doneprintHandle.js");
    }
    for inc in &fm.includes {
        if !names.iter().any(|n| n == inc) {
            names.push(inc);
        }
    }
    names.into_iter().map(|n| corpus.join("harness").join(n)).collect()
}

/// Prepare one corpus case. `Err` = unreadable file or unparseable
/// frontmatter (fail-closed at the caller).
pub fn prepare_case(corpus: &Path, rel_path: &str) -> Result<PreparedCase, String> {
    let abs_path = corpus.join(rel_path);
    let body = std::fs::read_to_string(&abs_path)
        .map_err(|e| format!("{rel_path}: unreadable: {e}"))?;
    let frontmatter = parse_frontmatter(&body).map_err(|e| format!("{rel_path}: {e}"))?;
    let modes = mandated_modes(&frontmatter);
    let includes = if modes == [RunMode::Raw] {
        vec![]
    } else {
        assemble_includes(corpus, &frontmatter)
    };
    Ok(PreparedCase { rel_path: rel_path.to_string(), abs_path, body, frontmatter, includes, modes })
}

impl PreparedCase {
    /// The runnable case for one mandated mode.
    pub fn assemble(&self, mode: RunMode, timeout: Duration) -> AssembledCase {
        AssembledCase {
            rel_path: self.rel_path.clone(),
            source_path: self.abs_path.clone(),
            body: self.body.clone(),
            includes: if mode == RunMode::Raw { vec![] } else { self.includes.clone() },
            mode,
            is_async: self.frontmatter.flags.iter().any(|f| f == "async"),
            timeout,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fm(flags: &[&str], includes: &[&str]) -> Frontmatter {
        Frontmatter {
            flags: flags.iter().map(|s| s.to_string()).collect(),
            features: vec![],
            includes: includes.iter().map(|s| s.to_string()).collect(),
            negative: None,
        }
    }

    #[test]
    fn run_mode_contract() {
        assert_eq!(mandated_modes(&fm(&[], &[])), [RunMode::Bare, RunMode::Strict]);
        assert_eq!(mandated_modes(&fm(&["onlyStrict"], &[])), [RunMode::Strict]);
        assert_eq!(mandated_modes(&fm(&["noStrict"], &[])), [RunMode::Bare]);
        assert_eq!(mandated_modes(&fm(&["raw"], &[])), [RunMode::Raw]);
        // raw wins over anything else present.
        assert_eq!(mandated_modes(&fm(&["raw", "noStrict"], &[])), [RunMode::Raw]);
        assert_eq!(mandated_modes(&fm(&["onlyStrict", "generated"], &[])), [RunMode::Strict]);
        // module wins over everything, incl. raw (a module spawned as a plain
        // script would be a spurious SyntaxError). A module runs ONCE.
        assert_eq!(mandated_modes(&fm(&["module"], &[])), [RunMode::Module]);
        assert_eq!(mandated_modes(&fm(&["module", "raw"], &[])), [RunMode::Module]);
        assert_eq!(mandated_modes(&fm(&["module", "async"], &[])), [RunMode::Module]);
    }

    #[test]
    fn module_case_prepares_with_module_goal() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::create_dir_all(root.join("test/language/module-code")).unwrap();
        std::fs::write(
            root.join("test/language/module-code/m.js"),
            "/*---\nflags: [module]\n---*/\nexport const x = 1;",
        )
        .unwrap();
        let prepared = prepare_case(root, "test/language/module-code/m.js").unwrap();
        // A module-goal test runs ONCE (no bare/strict split).
        assert_eq!(prepared.modes, [RunMode::Module]);
        // Harness globals are still assembled (installed as sloppy scripts,
        // shared via globalThis before the module import).
        let names: Vec<String> = prepared
            .includes
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js"]);
        // assemble for Module keeps the includes and the REAL corpus source path
        // (the driver imports it so relative imports resolve).
        let case = prepared.assemble(RunMode::Module, Duration::from_secs(10));
        assert_eq!(case.mode, RunMode::Module);
        assert_eq!(case.includes.len(), 2);
        assert_eq!(case.source_path, prepared.abs_path);

        // A module + async (TLA) test still runs once, and auto-adds the async
        // $DONE provider.
        std::fs::write(
            root.join("test/language/module-code/tla.js"),
            "/*---\nflags: [module, async]\n---*/\n$DONE();",
        )
        .unwrap();
        let tla = prepare_case(root, "test/language/module-code/tla.js").unwrap();
        assert_eq!(tla.modes, [RunMode::Module]);
        let names: Vec<String> = tla
            .includes
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "doneprintHandle.js"]);
    }

    #[test]
    fn include_assembly_dedups_after_defaults() {
        let corpus = Path::new("/c");
        let incs = assemble_includes(corpus, &fm(&[], &["propertyHelper.js", "sta.js", "propertyHelper.js"]));
        let names: Vec<String> = incs
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "propertyHelper.js"]);
        assert!(incs[0].starts_with("/c/harness"));
    }

    #[test]
    fn async_include_assembly_auto_adds_doneprinthandle() {
        let corpus = Path::new("/c");
        // No frontmatter includes: doneprintHandle.js is auto-added after the
        // defaults (this is the only $DONE provider such a case gets).
        let incs = assemble_includes(corpus, &fm(&["async"], &[]));
        let names: Vec<String> = incs
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "doneprintHandle.js"]);

        // asyncHelpers.js flows through the frontmatter includes, after the
        // auto-added doneprintHandle.js; dedup is order-stable.
        let incs = assemble_includes(corpus, &fm(&["async"], &["asyncHelpers.js"]));
        let names: Vec<String> = incs
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "doneprintHandle.js", "asyncHelpers.js"]);

        // A sync case gets no doneprintHandle.js.
        let incs = assemble_includes(corpus, &fm(&[], &["compareArray.js"]));
        let names: Vec<String> = incs
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "compareArray.js"]);

        // If a case ever declared doneprintHandle.js itself, dedup keeps one.
        let incs = assemble_includes(corpus, &fm(&["async"], &["doneprintHandle.js"]));
        let names: Vec<String> = incs
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "doneprintHandle.js"]);
    }

    #[test]
    fn async_case_prepares_with_async_harness() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::create_dir_all(root.join("test/built-ins/Promise")).unwrap();
        std::fs::write(
            root.join("test/built-ins/Promise/p.js"),
            "/*---\nflags: [async]\n---*/\n$DONE();",
        )
        .unwrap();
        let prepared = prepare_case(root, "test/built-ins/Promise/p.js").unwrap();
        // async (no noStrict/onlyStrict/raw) still runs both mandated modes.
        assert_eq!(prepared.modes, [RunMode::Bare, RunMode::Strict]);
        let names: Vec<String> = prepared
            .includes
            .iter()
            .map(|p| p.file_name().unwrap().to_string_lossy().into_owned())
            .collect();
        assert_eq!(names, ["assert.js", "sta.js", "doneprintHandle.js"]);
        // The assembled case carries the async harness include for each mode.
        let case = prepared.assemble(RunMode::Bare, Duration::from_secs(10));
        assert_eq!(case.includes.len(), 3);
    }

    #[test]
    fn prepare_and_assemble() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path();
        std::fs::create_dir_all(root.join("test/language")).unwrap();
        std::fs::write(
            root.join("test/language/x.js"),
            "/*---\nincludes: [compareArray.js]\n---*/\n1;",
        )
        .unwrap();
        let prepared = prepare_case(root, "test/language/x.js").unwrap();
        assert_eq!(prepared.modes, [RunMode::Bare, RunMode::Strict]);
        let case = prepared.assemble(RunMode::Strict, Duration::from_secs(10));
        assert_eq!(case.includes.len(), 3);
        assert_eq!(case.mode, RunMode::Strict);
        assert_eq!(case.body, "/*---\nincludes: [compareArray.js]\n---*/\n1;");

        std::fs::write(root.join("test/language/r.js"), "/*---\nflags: [raw]\n---*/\n1;").unwrap();
        let raw = prepare_case(root, "test/language/r.js").unwrap();
        assert_eq!(raw.modes, [RunMode::Raw]);
        assert!(raw.includes.is_empty());
    }
}
