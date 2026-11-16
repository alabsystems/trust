//! Project the actual consuming workspace's reader graph, including path
//! patches. Clean's standalone lock is an additional input, not this graph.

use std::cell::RefCell;
use std::path::PathBuf;

use super::*;

struct Image<'a> {
    git: &'a Git,
    root: &'a Path,
    tree: &'a str,
    checkout: bool,
    modules: BTreeMap<String, String>,
    children: RefCell<BTreeMap<String, (Git, String)>>,
    reads: RefCell<BTreeMap<String, Vec<u8>>>,
    trees: RefCell<BTreeMap<String, BTreeMap<String, (String, String)>>>,
}

impl<'a> Image<'a> {
    fn new(git: &'a Git, root: &'a Path, tree: &'a str, checkout: bool) -> io::Result<Self> {
        Ok(Self {
            git,
            root,
            tree,
            checkout,
            modules: parse_gitmodules(git, tree)?,
            children: RefCell::new(BTreeMap::new()),
            reads: RefCell::new(BTreeMap::new()),
            trees: RefCell::new(BTreeMap::new()),
        })
    }
    fn located<T>(
        &self,
        path: &str,
        f: impl FnOnce(&Git, &str, &str) -> io::Result<T>,
    ) -> io::Result<T> {
        relative(path)?;
        let found: Vec<_> =
            self.modules.keys().filter(|prefix| path.starts_with(&format!("{prefix}/"))).collect();
        require(found.len() <= 1, "ambiguous source submodule")?;
        if let Some(prefix) = found.first() {
            let mut children = self.children.borrow_mut();
            if !children.contains_key(*prefix) {
                let child = child_git(self.git, self.root, self.tree, prefix, self.checkout)?;
                let rev = pin(self.git, self.tree, prefix)?;
                if self.checkout {
                    require(
                        output(&child, &["rev-parse", "HEAD"])? == rev
                            && output(&child, &["status", "--porcelain", "--untracked-files=all"])?
                                .is_empty(),
                        "effective reader source checkout is not the selected clean input",
                    )?;
                }
                children.insert((*prefix).clone(), (child, rev));
            }
            let (child, rev) = children.get(*prefix).unwrap();
            f(child, rev, path.strip_prefix(&format!("{prefix}/")).unwrap())
        } else {
            f(self.git, self.tree, path)
        }
    }

    fn read(&self, path: &str) -> io::Result<Vec<u8>> {
        if let Some(bytes) = self.reads.borrow().get(path) {
            return Ok(bytes.clone());
        }
        let bytes = self.located(path, blob)?;
        if self.checkout {
            let mode =
                self.located(path, |git, rev, path| output(git, &["ls-tree", rev, "--", path]))?;
            let mode =
                mode.split_whitespace().next().ok_or_else(|| invalid("missing input mode"))?;
            working_file(self.root, path, &bytes, mode)?;
        }
        self.reads.borrow_mut().insert(path.to_owned(), bytes.clone());
        Ok(bytes)
    }

    fn tree(&self, path: &str) -> io::Result<BTreeMap<String, (String, String)>> {
        if let Some(rows) = self.trees.borrow().get(path) {
            return Ok(rows.clone());
        }
        let rows = self.located(path, |git, rev, prefix| {
            let rows = files(git, rev, prefix)?;
            let mut relative_rows = BTreeMap::new();
            for (name, (mode, hash)) in rows {
                let bytes = git.full_oid_blob(&hash)?;
                let suffix =
                    name.strip_prefix(prefix).ok_or_else(|| invalid("source prefix mismatch"))?;
                if self.checkout {
                    working_file(self.root, &format!("{path}{suffix}"), &bytes, &mode)?;
                }
                relative_rows.insert(suffix.to_owned(), (mode, hash));
            }
            Ok(relative_rows)
        })?;
        self.trees.borrow_mut().insert(path.to_owned(), rows.clone());
        Ok(rows)
    }

    fn workspace(&self, dir: &str) -> io::Result<(String, Value)> {
        let mut parent = PathBuf::from(dir);
        loop {
            let path = if parent.as_os_str().is_empty() {
                "Cargo.toml".to_owned()
            } else {
                format!("{}/Cargo.toml", parent.display())
            };
            if let Ok(bytes) = self.read(&path) {
                let doc = parse(&bytes)?;
                if doc.get("workspace").is_some() {
                    return Ok((parent.to_string_lossy().into_owned(), doc));
                }
            }
            require(parent.pop(), "cannot resolve effective reader workspace")?;
        }
    }
}

fn joined(base: &str, path: &str) -> io::Result<String> {
    require(!Path::new(path).is_absolute(), "absolute reader path")?;
    let mut result = Vec::new();
    for part in Path::new(base).join(path).components() {
        match part {
            Component::Normal(p) => result.push(p.to_string_lossy().into_owned()),
            Component::ParentDir => {
                require(result.pop().is_some(), "reader path escaped root")?;
            }
            _ => return Err(invalid("unsupported reader source path")),
        }
    }
    let path = result.join("/");
    relative(&path)?;
    Ok(path)
}

fn patches(doc: &Value) -> io::Result<BTreeMap<String, (String, Value)>> {
    let mut result = BTreeMap::new();
    if let Some(tables) = doc.get("patch").and_then(Value::as_table) {
        for table in tables.values() {
            for (name, spec) in table.as_table().ok_or_else(|| invalid("invalid patch table"))? {
                if let Some(path) = spec.get("path").and_then(Value::as_str) {
                    relative(path)?;
                    let name =
                        spec.get("package").and_then(Value::as_str).unwrap_or(name).to_owned();
                    // Different source URLs may name the exact same patch;
                    // genuinely ambiguous paths do not grant source identity.
                    let selected = (path.to_owned(), spec.clone());
                    if let Some(prior) = result.insert(name, selected.clone()) {
                        require(prior == selected, "ambiguous effective reader path patch")?;
                    }
                }
            }
        }
    }
    Ok(result)
}

fn strings(value: Option<&Value>) -> io::Result<BTreeSet<String>> {
    match value {
        None => Ok(BTreeSet::new()),
        Some(value) => value
            .as_array()
            .ok_or_else(|| invalid("invalid feature list"))?
            .iter()
            .map(|v| {
                v.as_str().map(str::to_owned).ok_or_else(|| invalid("invalid feature spelling"))
            })
            .collect(),
    }
}

fn requested(spec: &Value, direct: Option<&Value>) -> io::Result<BTreeSet<String>> {
    let mut result = strings(spec.get("features"))?;
    if let Some(direct) = direct {
        result.extend(strings(direct.get("features"))?);
    }
    if spec.get("default-features").and_then(Value::as_bool) != Some(false)
        && direct.and_then(|v| v.get("default-features")).and_then(Value::as_bool) != Some(false)
    {
        result.insert("default".to_owned());
    }
    Ok(result)
}

fn source_package(
    before: &Image<'_>,
    after: &Image<'_>,
    path: &str,
    id: &PackageId,
    locators: &mut BTreeMap<String, String>,
    selected: &mut BTreeMap<String, BTreeSet<String>>,
    uncertain: bool,
) -> io::Result<BTreeSet<String>> {
    require(before.tree(path)? == after.tree(path)?, "effective reader patched source changed")?;
    let doc = parse(&before.read(&format!("{path}/Cargo.toml"))?)?;
    let package = doc.get("package").ok_or_else(|| invalid("reader path has no package"))?;
    require(string(package, "name")? == id.name, "reader path package name mismatch")?;
    let (workspace_path, workspace) = before.workspace(path)?;
    let (new_path, new_workspace) = after.workspace(path)?;
    require(workspace_path == new_path, "reader workspace ownership changed")?;
    for (key, value) in package.as_table().ok_or_else(|| invalid("invalid reader package"))? {
        if value.get("workspace").and_then(Value::as_bool) == Some(true) {
            require(
                at(&workspace, &["workspace", "package", key])
                    == at(&new_workspace, &["workspace", "package", key]),
                "reader inherited package input changed",
            )?;
        }
    }
    let version = if package.get("version").and_then(Value::as_str).is_some() {
        package.get("version")
    } else {
        at(&workspace, &["workspace", "package", "version"])
    };
    require(
        version.and_then(Value::as_str) == Some(id.version.as_str()),
        "reader path version mismatch",
    )?;
    let mut dependencies = BTreeMap::new();
    let mut blocks = vec![&doc];
    if let Some(targets) = doc.get("target").and_then(Value::as_table) {
        blocks.extend(targets.values());
    }
    for block in blocks {
        for section in ["dependencies", "build-dependencies"] {
            if let Some(deps) = block.get(section).and_then(Value::as_table) {
                for (alias, direct) in deps {
                    let inherited = direct.get("workspace").and_then(Value::as_bool) == Some(true);
                    let spec = if inherited {
                        let keys = ["workspace", "dependencies", alias];
                        let old = at(&workspace, &keys)
                            .ok_or_else(|| invalid("unresolved reader dependency"))?;
                        require(
                            Some(old) == at(&new_workspace, &keys),
                            "effective reader inherited dependency changed",
                        )?;
                        old
                    } else {
                        direct
                    };
                    let name =
                        spec.get("package").and_then(Value::as_str).unwrap_or(alias).to_owned();
                    if let Some(relative) = spec.get("path").and_then(Value::as_str) {
                        let base = if inherited { &workspace_path } else { path };
                        let child = joined(base, relative)?;
                        if let Some(old) = locators.insert(name.clone(), child.clone()) {
                            require(old == child, "ambiguous reader dependency source")?;
                        }
                    }
                    dependencies.entry(alias.clone()).or_insert_with(Vec::new).push((
                        name,
                        spec.clone(),
                        direct.clone(),
                    ));
                }
            }
        }
    }
    let definitions = doc.get("features").and_then(Value::as_table);
    let mut active = BTreeSet::new();
    let mut todo: Vec<_> =
        selected.get(&id.name).cloned().unwrap_or_default().into_iter().collect();
    let mut enabled = BTreeSet::new();
    let mut forwarded = BTreeMap::<String, BTreeSet<String>>::new();
    while let Some(feature) = todo.pop() {
        if !active.insert(feature.clone()) {
            continue;
        }
        if let Some(alias) = feature.strip_prefix("dep:") {
            require(dependencies.contains_key(alias), "feature enables unknown dependency")?;
            enabled.insert(alias.to_owned());
        } else if let Some((alias, child)) = feature.split_once('/') {
            let weak = alias.ends_with('?');
            let alias = alias.trim_end_matches('?');
            require(dependencies.contains_key(alias), "feature forwards unknown dependency")?;
            if !weak {
                enabled.insert(alias.to_owned());
            }
            forwarded.entry(alias.to_owned()).or_default().insert(child.to_owned());
        } else if let Some(values) = definitions.and_then(|d| d.get(&feature)) {
            todo.extend(strings(Some(values))?);
        } else if dependencies.contains_key(&feature) {
            enabled.insert(feature);
        } else {
            require(feature == "default", "unsupported selected reader feature")?;
        }
    }
    let mut names = BTreeSet::new();
    for (alias, variants) in dependencies {
        for (name, spec, direct) in variants {
            let optional = spec.get("optional").and_then(Value::as_bool) == Some(true)
                || direct.get("optional").and_then(Value::as_bool) == Some(true);
            if optional && !enabled.contains(&alias) && !uncertain {
                continue;
            }
            let target = selected.entry(name.clone()).or_default();
            target.extend(requested(&spec, Some(&direct))?);
            if let Some(features) = forwarded.get(&alias) {
                target.extend(features.iter().cloned());
            }
            names.insert(name);
        }
    }
    Ok(names)
}

pub(super) fn effective_reader_inputs(
    git: &Git,
    root: &Path,
    old: &str,
    new: &str,
    _clean_production: &BTreeMap<String, BTreeSet<String>>,
    checkout: bool,
) -> io::Result<()> {
    let before = Image::new(git, root, old, false)?;
    let after = Image::new(git, root, new, checkout)?;
    let old_doc = parse(&before.read("Cargo.toml")?)?;
    let new_doc = parse(&after.read("Cargo.toml")?)?;
    for keys in [["workspace", "resolver"], ["workspace", "package"]] {
        require(
            at(&old_doc, &keys) == at(&new_doc, &keys),
            "effective reader workspace policy changed",
        )?;
    }
    require(old_doc.get("profile") == new_doc.get("profile"), "effective reader profiles changed")?;
    for path in [".cargo/config.toml", "rust-toolchain.toml"] {
        require(before.read(path)? == after.read(path)?, "effective reader configuration changed")?;
    }
    // These are the actual runtime reader selectors. The complete crate
    // manifests retain feature/default-feature, target and dependency-kind data.
    let old_consumer = parse(&before.read("crates/trust-clean/Cargo.toml")?)?;
    let new_consumer = parse(&after.read("crates/trust-clean/Cargo.toml")?)?;
    for name in ["clean-olean", "clean-kernel"] {
        require(
            at(&old_doc, &["workspace", "dependencies", name])
                == at(&new_doc, &["workspace", "dependencies", name]),
            "effective reader workspace selector changed",
        )?;
        for section in ["dependencies", "build-dependencies", "target", "features"] {
            let a = if section == "target" || section == "features" {
                old_consumer.get(section)
            } else {
                at(&old_consumer, &[section, name])
            };
            let b = if section == "target" || section == "features" {
                new_consumer.get(section)
            } else {
                at(&new_consumer, &[section, name])
            };
            require(a == b, "effective reader consumer selector changed")?;
        }
    }
    let old_patches = patches(&old_doc)?;
    let new_patches = patches(&new_doc)?;
    let mut locators = BTreeMap::new();
    let mut selected = BTreeMap::<String, BTreeSet<String>>::new();
    for name in ["clean-olean", "clean-kernel"] {
        let spec = at(&old_doc, &["workspace", "dependencies", name])
            .ok_or_else(|| invalid("missing actual reader selector"))?;
        let path = spec
            .get("path")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("reader must select an exact local source"))?;
        relative(path)?;
        locators.insert(name.to_owned(), path.to_owned());
        let direct = at(&old_consumer, &["dependencies", name]);
        selected.insert(name.to_owned(), requested(spec, direct)?);
    }
    let old_lock = before.read("Cargo.lock")?;
    let new_lock = after.read("Cargo.lock")?;
    let mut stable = false;
    for _ in 0..128 {
        let previous = selected.clone();
        let mut discover = |id: &PackageId, uncertain: bool| {
            if let Some((path, declaration)) = old_patches.get(&id.name) {
                require(
                    new_patches.get(&id.name) == Some(&(path.clone(), declaration.clone())),
                    "effective reader patch changed",
                )?;
                if let Some(prior) = locators.insert(id.name.clone(), path.clone()) {
                    require(prior == *path, "ambiguous effective reader locator")?;
                }
            }
            let path = locators
                .get(&id.name)
                .cloned()
                .ok_or_else(|| invalid("unresolved effective reader path package"))?;
            source_package(&before, &after, &path, id, &mut locators, &mut selected, uncertain)
        };
        let old_graph = lock_closure_with(&old_lock, BTreeMap::new(), &mut discover)?;
        let new_graph = lock_closure_with(&new_lock, BTreeMap::new(), &mut discover)?;
        require(
            old_graph == new_graph,
            "effective reader lock source/checksum/version/edges changed",
        )?;
        if selected == previous {
            stable = true;
            break;
        }
    }
    require(stable, "effective reader feature closure did not converge")?;
    // Model islands are compile-time external kernel inputs when enabled.
    // Compare the complete bounded source directory, independent of whether
    // the caller currently selects the optional kernel configuration.
    let spec = "first-party/clean/crates/clean-verify/spec";
    require(before.tree(spec)? == after.tree(spec)?, "external kernel model inputs changed")?;
    Ok(())
}
