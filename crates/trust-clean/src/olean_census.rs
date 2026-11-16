//! Raw external Lean dependency observation, deliberately without Environment,
//! registration, kernel checking, source admission, or publication capability.
//!
//! Captured file bytes and typed raw Name witnesses identify the population.
//! Clean's existing full parser interprets payloads; its display-name projection
//! is cross-checked, never used as identity. Present malformed parts, parser
//! limits, search ambiguities and lost extension information remain incomplete.

mod ir;
mod names;
mod runtime;
#[cfg(test)]
mod tests;

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Read;
#[cfg(unix)]
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

use clean_olean::{OleanHeader, ParsedModule, parse_module, parse_module_incremental};
use clean_parser::{SurfaceDecl, SurfaceName};
pub use names::{ModuleName, Segment};
use serde::Serialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

/// Untrusted retained source snapshots. Module is a diagnostic label, not a
/// parsed Name; only a unique, non-dotted one-segment string key is matched
/// here. Projected dotted labels remain ambiguous candidates, not resolution.
pub struct OleanCensusSource {
    pub module: String,
    pub path: PathBuf,
    pub source: Result<String, String>,
}

/// Explicit typed resolution to one retained source snapshot. This is a
/// diagnostic input, not source admission: the caller must derive it from its
/// accepted source context. The observer checks index, identity uniqueness and
/// exact snapshot bytes before using any binding; projected labels never mint
/// these bindings.
#[derive(Clone, Debug, Serialize)]
pub struct OleanCensusSourceBinding {
    pub module: ModuleName,
    pub source_index: usize,
    pub source_sha256: String,
}

#[derive(Clone, Copy, Debug, Serialize)]
pub struct OleanCensusLimits {
    pub modules: usize,
    pub part_bytes: usize,
    pub total_bytes: usize,
    pub rows_per_array: usize,
    /// Shared bounded raw IR object accesses for each captured part.
    pub ir_object_accesses: usize,
}

impl Default for OleanCensusLimits {
    fn default() -> Self {
        Self {
            modules: 4096,
            part_bytes: 64 * 1024 * 1024,
            total_bytes: 512 * 1024 * 1024,
            rows_per_array: 1_000_000,
            ir_object_accesses: 200_000,
        }
    }
}

/// A diagnostic report only. No accepted-context constructor consumes it.
#[derive(Debug, Serialize)]
pub struct OleanClosureObservation {
    #[serde(skip)]
    observed_paths: Vec<PathBuf>,
    pub schema: &'static str,
    pub authority: &'static str,
    pub sources: Vec<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_bindings: Option<Vec<OleanCensusSourceBinding>>,
    pub search_roots: Vec<Value>,
    pub file_observations: Vec<Value>,
    pub modules: Vec<Value>,
    pub cycles: Vec<Vec<ModuleName>>,
    pub deferred_modules: Vec<ModuleName>,
    pub duplicate_declarations: Vec<Value>,
    pub issues: Vec<String>,
    pub limits: OleanCensusLimits,
    pub denominator_status: &'static str,
    pub runtime_body_universe: &'static str,
    pub limitations: Vec<&'static str>,
}

impl OleanClosureObservation {
    /// Exact paths inspected, including missing candidates. Diagnostic callers
    /// may protect these from output aliasing; this grants no input authority.
    pub fn observed_paths(&self) -> &[PathBuf] {
        &self.observed_paths
    }
}

/// Same-read bytes retained for a diagnostic computational consumer. These are
/// not an admitted module, a kernel environment, or a refinement capability.
/// Failed/absent parts and every competing search-root candidate stay present.
#[derive(Debug)]
pub struct OleanCapturedPart {
    pub path: PathBuf,
    pub bytes: Option<Vec<u8>>,
    pub observation: Value,
}

#[derive(Debug)]
pub struct OleanCapturedCandidate {
    pub module: ModuleName,
    pub root_index: usize,
    pub parts: Vec<OleanCapturedPart>,
}

#[derive(Debug)]
pub struct OleanClosureCapture {
    pub observation: OleanClosureObservation,
    pub candidates: Vec<OleanCapturedCandidate>,
    search_roots: Vec<(PathBuf, Value)>,
}

impl OleanClosureCapture {
    /// Re-observe paths after diagnostic production, including absent
    /// candidates. This detects observed drift, not atomic filesystem races.
    /// It never replaces the bytes originally supplied to a consumer.
    pub fn recheck_paths(&self) -> Vec<String> {
        let mut errors = Vec::new();
        for candidate in &self.candidates {
            for part in &candidate.parts {
                let limit = part.observation["capture_limit"]
                    .as_u64()
                    .and_then(|n| usize::try_from(n).ok())
                    .unwrap_or(0);
                if capture(&part.path, limit).record != part.observation {
                    errors.push(format!(
                        "captured dependency path/bytes changed: {}",
                        part.path.display()
                    ));
                }
            }
        }
        for (path, before) in &self.search_roots {
            if path_state(path) != *before {
                errors.push(format!("captured search root changed: {}", path.display()));
            }
        }
        errors
    }
}

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn path_identity(path: &Path) -> Value {
    json!({"display": path.display().to_string(), "os_bytes_hex": path.as_os_str().as_encoded_bytes().iter().map(|b| format!("{b:02x}")).collect::<String>()})
}

fn path_state(path: &Path) -> Value {
    match path.canonicalize() {
        Ok(resolved) => {
            json!({"status": "resolved", "path": path_identity(&resolved), "is_directory": resolved.is_dir(), "is_file": resolved.is_file()})
        }
        Err(error) => json!({"status": "unresolved", "error": error.to_string()}),
    }
}

struct Captured {
    bytes: Option<Vec<u8>>,
    record: Value,
}

fn capture(path: &Path, limit: usize) -> Captured {
    let mut record = json!({"path": path_identity(path), "resolution": path_state(path), "capture_limit": limit});
    let result = (|| -> Result<(Vec<u8>, Option<(u64, u64)>), (&str, String)> {
        // Avoid opening a known FIFO/device as though it were a bounded regular
        // file. This is an observation, not an atomic filesystem snapshot.
        if let Ok(metadata) = std::fs::metadata(path) {
            if !metadata.is_file() {
                return Err(("not-regular-file", "not a regular file".into()));
            }
        }
        let mut file = std::fs::File::open(path).map_err(|error| {
            (
                if error.kind() == std::io::ErrorKind::NotFound { "absent" } else { "unreadable" },
                error.to_string(),
            )
        })?;
        let metadata = file.metadata().map_err(|e| ("unreadable", e.to_string()))?;
        if !metadata.is_file() {
            return Err(("not-regular-file", "not a regular file".into()));
        }
        // Use the opened file, not the pre-open path lookup, for Unix alias identity.
        #[cfg(unix)]
        let file_identity = Some((metadata.dev(), metadata.ino()));
        #[cfg(not(unix))]
        let file_identity = None;
        if metadata.len() > limit as u64 {
            return Err((
                "bounded",
                format!("{} bytes exceed remaining capture limit {limit}", metadata.len()),
            ));
        }
        let mut bytes = Vec::new();
        file.by_ref()
            .take((limit as u64).saturating_add(1))
            .read_to_end(&mut bytes)
            .map_err(|e| ("unreadable", e.to_string()))?;
        if bytes.len() > limit {
            return Err(("bounded", "file grew beyond capture limit".into()));
        }
        Ok((bytes, file_identity))
    })();
    match result {
        Ok((bytes, file_identity)) => {
            record["status"] = json!("captured");
            record["sha256"] = json!(hash(&bytes));
            record["bytes"] = json!(bytes.len());
            if let Some((device, inode)) = file_identity {
                record["file_identity"] = json!({"device": device, "inode": inode});
            }
            Captured { bytes: Some(bytes), record }
        }
        Err((status, error)) => {
            record["status"] = json!(status);
            record["error"] = json!(error);
            Captured { bytes: None, record }
        }
    }
}

fn module_path(root: &Path, name: &ModuleName) -> Result<PathBuf, String> {
    if name.0.is_empty() {
        return Err("anonymous import module".into());
    }
    let mut path = root.to_path_buf();
    for segment in &name.0 {
        let Segment::Str(value) = segment else {
            return Err(
                "numeric module-name segment has no source-path resolution in this observer".into(),
            );
        };
        if value.is_empty()
            || matches!(value.as_str(), "." | "..")
            || value.contains(['/', '\\', '\0'])
        {
            return Err("module-name segment is not a single safe path component".into());
        }
        path.push(value);
    }
    // append, never set_extension: a quoted dot belongs to this component.
    let mut filename = path.file_name().ok_or("module has no final component")?.to_os_string();
    filename.push(".olean");
    path.set_file_name(filename);
    Ok(path)
}

fn imports(
    decls: &[SurfaceDecl],
    source: &str,
    tokens: &[clean_parser::lexer::Token],
    rows: &mut Vec<Value>,
    names: &mut Vec<ModuleName>,
    depth: usize,
) {
    if depth > 256 {
        rows.push(json!({"status": "bounded", "error": "source AST nesting exceeds 256"}));
        return;
    }
    for declaration in decls {
        match declaration {
            SurfaceDecl::Import { span, paths } => {
                let witnessed = import_tokens(source, tokens, span.start, paths);
                for (index, path) in paths.iter().enumerate() {
                    let ast_name = payload_name(path.name());
                    let display_segments = ast_name
                        .0
                        .iter()
                        .map(|part| match part {
                            Segment::Str(value) => value.clone(),
                            Segment::Num(value) => value.to_string(),
                        })
                        .collect::<Vec<_>>();
                    match &witnessed {
                        Ok((modules, all)) => {
                            let name = &modules[index];
                            rows.push(json!({"status": "parsed-import", "module": name, "ast_display_segments": display_segments, "ast_name": ast_name, "span": [span.start, span.end], "import_all_modifier": all,
                                "identity_witness": "existing-lexer-ident-and-dot-tokens-cross-checked-with-ast"}));
                            names.push(name.clone());
                        }
                        Err(error) => rows.push(json!({"status": "unresolved-import-identity", "module": null, "ast_display_segments": display_segments, "ast_name": ast_name, "span": [span.start, span.end], "error": error})),
                    }
                }
            }
            SurfaceDecl::Namespace { decls, .. }
            | SurfaceDecl::Section { decls, .. }
            | SurfaceDecl::Mutual { decls, .. } => {
                imports(decls, source, tokens, rows, names, depth + 1)
            }
            SurfaceDecl::RawDecl { span, .. } => {
                rows.push(json!({"status": "unparsed-region", "span": [span.start, span.end]}))
            }
            _ => {}
        }
    }
}

/// Cross-check the typed AST name against the independent lexer token sequence.
/// A Dot token, not a display dot, separates Name.str components. This witnesses
/// only AST-selected imports and never reparses their diagnostic projection.
fn import_tokens(
    source: &str,
    tokens: &[clean_parser::lexer::Token],
    start: usize,
    ast_paths: &[SurfaceName],
) -> Result<(Vec<ModuleName>, bool), String> {
    use clean_parser::lexer::TokenKind;
    let mut index = tokens
        .iter()
        .position(|t| t.span.start == start && matches!(t.kind, TokenKind::Import))
        .ok_or("no exact lexer token for AST import")?
        + 1;
    let all = matches!(tokens.get(index).map(|t| &t.kind), Some(TokenKind::Ident(name)) if name == "all")
        && matches!(tokens.get(index + 1).map(|t| &t.kind), Some(TokenKind::Ident(_)));
    if all {
        let token = &tokens[index];
        let raw = source.get(token.span.start..token.span.end);
        if raw != Some("all") || tokens[index + 1].preceded_by_newline {
            return Err(format!(
                "ambiguous import-all token: raw spelling {raw:?}, next identifier on new line {}; AST modifier erasure cannot establish this import identity",
                tokens[index + 1].preceded_by_newline
            ));
        }
        index += 1;
    }
    let mut modules = Vec::new();
    for ast in ast_paths {
        let mut parts = Vec::new();
        loop {
            let Some(clean_parser::lexer::Token { kind: TokenKind::Ident(name), .. }) =
                tokens.get(index)
            else {
                return Err(
                    "import identifier token unavailable; AST projection is not identity".into()
                );
            };
            parts.push(Segment::Str(name.clone()));
            index += 1;
            if matches!(tokens.get(index).map(|t| &t.kind), Some(TokenKind::Dot)) {
                index += 1;
            } else {
                break;
            }
        }
        let name = ModuleName(parts);
        if name != payload_name(ast.name()) {
            return Err("import token/AST structural name mismatch".into());
        }
        modules.push(name);
        if matches!(tokens.get(index).map(|t| &t.kind), Some(TokenKind::Comma)) {
            index += 1;
        }
    }
    Ok((modules, all))
}

fn header_record(header: &OleanHeader) -> Value {
    json!({"format": header.version, "flags": header.flags, "lean_version": header.lean_version,
        "lean_git_hash": std::str::from_utf8(&header.git_hash).ok(),
        "lean_git_hash_bytes": header.git_hash.as_slice(), "base_address": header.base_addr})
}

fn parsed_rows(
    module: &ParsedModule,
    witness: &names::Witness,
    issues: &mut Vec<String>,
) -> Vec<Value> {
    let projections = |rows: &[names::NameRow]| {
        rows.iter().map(|r| r.name.as_ref().map(ModuleName::projection)).collect::<Vec<_>>()
    };
    for (label, raw, projected) in [
        (
            "const_names",
            projections(&witness.const_names),
            module.const_names.iter().map(|n| Some(n.clone())).collect::<Vec<_>>(),
        ),
        (
            "extra_const_names",
            projections(&witness.extra_const_names),
            module.extra_const_names.iter().map(|n| Some(n.clone())).collect::<Vec<_>>(),
        ),
        (
            "constants",
            projections(&witness.constants),
            module.constants.iter().map(|n| Some(n.name.clone())).collect::<Vec<_>>(),
        ),
        (
            "imports",
            projections(&witness.imports),
            module.imports.iter().map(|n| Some(n.module_name.clone())).collect::<Vec<_>>(),
        ),
    ] {
        if raw != projected {
            issues.push(format!("typed witness/parser projection mismatch: {label}"));
        }
    }
    if witness.imports.iter().map(names::NameRow::parser_first_flag_projection).collect::<Vec<_>>()
        != module.imports.iter().map(|i| Some(i.runtime_only)).collect::<Vec<_>>()
    {
        issues.push("typed witness/parser first import-flag projection mismatch (legacy parser field name is not modern import semantics)".into());
    }
    module.constants.iter().enumerate().map(|(index, constant)| {
        json!({"index": index, "name": witness.constants.get(index).and_then(|r| r.name.as_ref()), "parser_display": constant.name,
            "raw_kind": format!("{:?}", constant.kind), "type_present": constant.type_.is_some(), "value_present": constant.value.is_some(),
            "safety": constant.definition_safety.map(|v| format!("{v:?}")), "inductive_unsafe": constant.inductive_val.as_ref().map(|v| v.is_unsafe),
            "constructor_unsafe": constant.constructor_val.as_ref().map(|v| v.is_unsafe), "recursor_unsafe": constant.recursor_val.as_ref().map(|v| v.is_unsafe),
            "kernel_classification": "not-checked", "runtime_classification": "unmeasured"})
    }).collect()
}

fn payload_name(name: &clean_kernel::Name) -> ModuleName {
    use clean_kernel::name::NameInner;
    let mut parts = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, value) => {
                parts.push(Segment::Str(value.to_string()));
                current = parent;
            }
            NameInner::Num(parent, value) => {
                parts.push(Segment::Num(*value));
                current = parent;
            }
        }
    }
    parts.reverse();
    ModuleName(parts)
}

fn payload_rosters(payload: &clean_olean::CleanPayload) -> Value {
    // Retain each original array independently. A raw/payload duplicate is not
    // permission to discard a row or assume its type/value agrees.
    json!({
        "constants": payload.constants.iter().enumerate().map(|(index, row)| json!({"index": index, "name": payload_name(&row.name), "kind": format!("{:?}", row.kind), "type_present": true, "value_present": row.value.is_some()})).collect::<Vec<_>>(),
        "inductives": payload.inductives.iter().enumerate().map(|(index, row)| json!({"index": index, "name": payload_name(&row.name)})).collect::<Vec<_>>(),
        "constructors": payload.constructors.iter().enumerate().map(|(index, row)| json!({"index": index, "name": payload_name(&row.name)})).collect::<Vec<_>>(),
        "recursors": payload.recursors.iter().enumerate().map(|(index, row)| json!({"index": index, "name": payload_name(&row.name)})).collect::<Vec<_>>(),
        "structure_fields": payload.structure_fields.iter().enumerate().map(|(index, (name, fields))| json!({"index": index, "name": payload_name(name), "fields": fields.iter().map(payload_name).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "relationship_to_raw_rows": "separate-captured-arrays-not-deduplicated-or-assumed-equivalent",
        "kernel_classification": "not-checked", "runtime_classification": "unmeasured",
    })
}

fn part_dependencies(
    bytes: &[u8],
    base: Option<&[u8]>,
    server: Option<&[u8]>,
    index: usize,
) -> Result<Vec<usize>, String> {
    if index == 0 {
        return Ok(vec![]);
    }
    let base = base.ok_or("present companion has no captured base dependency")?;
    let bh = OleanHeader::parse(base).map_err(|e| e.to_string())?;
    let ph = OleanHeader::parse(bytes).map_err(|e| e.to_string())?;
    if (bh.version, bh.flags, bh.git_hash, &bh.lean_version)
        != (ph.version, ph.flags, ph.git_hash, &ph.lean_version)
    {
        return Err("companion header identity differs from base".into());
    }
    // Modern .ir is independently serialized, not a fourth incremental
    // kernel region. Its header must still match the captured module base.
    if index == 3 {
        return Ok(vec![]);
    }
    let end = bh.base_addr.checked_add(base.len() as u64).ok_or("base address overflow")?;
    if index == 1 && ph.base_addr < end {
        return Ok(vec![]);
    }
    if index == 2 {
        let server = server.ok_or("present private part requires a captured server dependency")?;
        let sh = OleanHeader::parse(server).map_err(|e| e.to_string())?;
        if (bh.version, bh.flags, bh.git_hash, &bh.lean_version)
            != (sh.version, sh.flags, sh.git_hash, &sh.lean_version)
        {
            return Err("server header identity differs from base".into());
        }
        return Ok(vec![0, 1]);
    }
    Ok(vec![0])
}

fn cycles(graph: &BTreeMap<ModuleName, BTreeSet<ModuleName>>) -> Vec<Vec<ModuleName>> {
    // Iterative DFS detects back edges without consuming native stack for a
    // long dependency chain. These are cycle witnesses, not all simple cycles.
    let mut done = BTreeSet::new();
    let mut found = BTreeSet::new();
    for name in graph.keys() {
        let mut stack = vec![(name.clone(), false)];
        let mut path = Vec::<ModuleName>::new();
        while let Some((name, leaving)) = stack.pop() {
            if leaving {
                path.pop();
                continue;
            }
            if let Some(index) = path.iter().position(|n| n == &name) {
                let mut cycle = path[index..].to_vec();
                cycle.push(name);
                found.insert(cycle);
                continue;
            }
            if !done.insert(name.clone()) {
                continue;
            }
            path.push(name.clone());
            stack.push((name.clone(), true));
            if let Some(edges) = graph.get(&name) {
                stack.extend(edges.iter().rev().map(|name| (name.clone(), false)));
            }
        }
    }
    found.into_iter().collect()
}

/// Observe all AST imports in the retained source unit, then every raw external
/// candidate and dependency. Search roots are EXPLICIT and ordered: no ambient
/// LEAN_PATH, package scan, current toolchain fallback or first-writer winner.
/// Ambiguous candidates are all inspected and remain explicitly ambiguous.
#[must_use]
pub fn observe_olean_closure(
    sources: &[OleanCensusSource],
    search_roots: &[PathBuf],
    limits: OleanCensusLimits,
) -> OleanClosureObservation {
    observe_olean_closure_inner(sources, search_roots, limits, false, None).observation
}

/// Runs the identical observer and additionally retains its original captured
/// buffers. Never reconstruct Expr from JSON or reopen a selected file to get
/// computational bytes after hashing it. The existing report schema is intact.
#[must_use]
pub fn capture_olean_closure(
    sources: &[OleanCensusSource],
    search_roots: &[PathBuf],
    limits: OleanCensusLimits,
) -> OleanClosureCapture {
    observe_olean_closure_inner(sources, search_roots, limits, true, None)
}

/// Same-read capture with explicit typed source resolution. Each import must
/// match the exact Name constructors and snapshot binding. Invalid or duplicate
/// bindings retain an issue and all external candidates, with no label fallback.
/// Raw imports inside external .olean files are still traversed unchanged.
#[must_use]
pub fn capture_olean_closure_with_source_bindings(
    sources: &[OleanCensusSource],
    bindings: &[OleanCensusSourceBinding],
    search_roots: &[PathBuf],
    limits: OleanCensusLimits,
) -> OleanClosureCapture {
    observe_olean_closure_inner(sources, search_roots, limits, true, Some(bindings))
}

fn observe_olean_closure_inner(
    sources: &[OleanCensusSource],
    search_roots: &[PathBuf],
    limits: OleanCensusLimits,
    retain_bytes: bool,
    source_bindings: Option<&[OleanCensusSourceBinding]>,
) -> OleanClosureCapture {
    let mut captured_candidates = Vec::new();
    let mut out = OleanClosureObservation {
        observed_paths: sources.iter().map(|s| s.path.clone()).collect(),
        schema: "trust.lean.olean-closure-observation/v1",
        authority: "diagnostic-only-no-import-admission",
        sources: Vec::new(),
        source_bindings: source_bindings.map(|bindings| bindings.to_vec()),
        search_roots: search_roots
            .iter()
            .map(|p| json!({"supplied": path_identity(p), "before": path_state(p)}))
            .collect(),
        modules: Vec::new(),
        file_observations: Vec::new(),
        cycles: Vec::new(),
        deferred_modules: Vec::new(),
        duplicate_declarations: Vec::new(),
        issues: Vec::new(),
        limits,
        denominator_status: "denominator_unverified",
        runtime_body_universe: "unmeasured",
        limitations: vec![
            "No declaration is registered or kernel checked. This cannot enable external imports, accepted contexts, proof authority or library publication.",
            "Typed raw-name witnesses use a bounded read-only adapter because Clean's public parser exposes lossy display names; a public typed-name API remains needed.",
            "The full Clean parser supplies payload observations. Incremental companion extension entries are not decoded by that parser and remain unmeasured.",
            "Generic extension counts and separately decoded Lean IR syntax are not semantic completeness. Identifier binding diagnostics do not check types, effects, refcounts, lifetimes, external implementations or source refinement.",
            "Source Import ASTs lose quoted-dot boundaries; existing lexer token witnesses recover segments and import-all modifiers only when cross-checking succeeds. Recovery failures retain unresolved rows.",
            "Supplied source module labels are untyped: only unique non-dotted one-segment matches are treated as source-satisfied. Dotted or duplicate candidate labels remain ambiguous and never suppress external observations; this is not resolver authority.",
            "Cycle rows are deterministic DFS cycle witnesses, not an enumeration of every simple cycle.",
            "Only explicit source Import ASTs are roots; implicit prelude imports, .ilean/native artifacts and specialized runtime dependency closure are not measured. Present .ir companions are observed as independent serialized regions.",
            "Byte/module/row/name bounds do not bound the existing full expression parser's total time or memory. Full parsing is not kernel replay; unexpected recoverable parser panics remain incomplete.",
            "Base is required; server/private absence is observed optional, not malformed. A present private region requires its base/server decoding dependencies.",
            "Raw kinds, value presence and imported code-generator names are NOT executable classifications or a complete specialized runtime universe.",
        ],
    };
    let mut typed_sources = BTreeMap::new();
    let mut valid_bindings = true;
    if let Some(bindings) = source_bindings {
        out.limitations.push("Explicit typed source bindings are diagnostic caller inputs checked against the retained snapshot bytes. They do not admit external imports; raw external dependency traversal is unchanged.");
        for (index, binding) in bindings.iter().enumerate() {
            let mut errors = Vec::new();
            if let Err(error) = module_path(Path::new(""), &binding.module) {
                errors.push(format!("malformed module identity: {error}"));
            }
            match sources.get(binding.source_index) {
                None => errors.push("source index is out of range".into()),
                Some(source) => match &source.source {
                    Err(_) => errors.push("source snapshot is unreadable".into()),
                    Ok(text) if hash(text.as_bytes()) != binding.source_sha256 => {
                        errors.push("source snapshot digest differs".into());
                    }
                    Ok(_) => {}
                },
            }
            if typed_sources.insert(binding.module.clone(), binding).is_some() {
                errors.push("duplicate or conflicting typed module identity".into());
            }
            if !errors.is_empty() {
                valid_bindings = false;
                out.issues.push(format!("source binding {index} refused: {}", errors.join("; ")));
            }
        }
        if !valid_bindings {
            typed_sources.clear();
        }
    }
    let mut pending = VecDeque::new();
    for (index, source) in sources.iter().enumerate() {
        let mut rows = Vec::new();
        let mut source_imports = Vec::new();
        let (sha, errors) = match &source.source {
            Err(error) => (None, vec![error.clone()]),
            Ok(text) => {
                let errors = match clean_parser::parse_file_with_diagnostics(text) {
                    Ok(parsed) => {
                        imports(
                            &parsed.decls,
                            text,
                            &clean_parser::lexer::Lexer::tokenize(text),
                            &mut rows,
                            &mut source_imports,
                            0,
                        );
                        parsed.diagnostics.iter().map(|d| format!("{d:?}")).collect()
                    }
                    Err(error) => vec![error.to_string()],
                };
                (Some(hash(text.as_bytes())), errors)
            }
        };
        if !errors.is_empty() || rows.iter().any(|r| r["status"] != "parsed-import") {
            out.issues.push(format!("source {index} has incomplete import parsing"));
        }
        for name in &source_imports {
            // Projection is useful only to retain POSSIBLE source candidates.
            // A.B may mean two segments or one quoted segment; an untyped label
            // cannot choose between them or hide either external population.
            let projection = name.projection();
            let supplied: Vec<_> = sources
                .iter()
                .enumerate()
                .filter_map(|(i, s)| (s.module == projection).then_some(i))
                .collect();
            let unambiguous = supplied.len() == 1
                && matches!(name.0.as_slice(), [Segment::Str(part)] if !part.is_empty() && !part.contains('.'));
            let binding = typed_sources.get(name).copied();
            let resolution = if source_bindings.is_some() {
                if binding.is_some() {
                    "source-satisfied-typed-binding"
                } else {
                    pending.push_back(name.clone());
                    if valid_bindings {
                        "external-no-exact-source-binding"
                    } else {
                        "invalid-source-bindings"
                    }
                }
            } else if unambiguous {
                "source-satisfied-single-component"
            } else {
                pending.push_back(name.clone());
                if supplied.is_empty() {
                    "external-no-supplied-label"
                } else {
                    out.issues.push(format!("source {index} import has ambiguous supplied source labels; external candidates retained"));
                    "ambiguous-supplied-label"
                }
            };
            rows.iter_mut().filter(|r| r["module"] == json!(name)).for_each(|r| {
                r["supplied_source_candidates"] = json!(supplied);
                r["supplied_source_resolution"] = json!(resolution);
                if let Some(binding) = binding {
                    r["source_binding"] = json!(binding);
                }
            });
        }
        let disk = capture(&source.path, limits.part_bytes);
        let matches = sha.as_ref().is_some_and(|h| disk.record["sha256"] == *h);
        if source.source.is_ok() && !matches {
            out.issues.push(format!("source {index} differs from captured check snapshot"));
        }
        out.sources.push(json!({"index": index, "module_label": source.module, "path": path_identity(&source.path), "checked_snapshot_sha256": sha,
            "errors": errors, "imports": rows, "path_after_check": disk.record, "matches_checked_snapshot": matches}));
    }
    let mut seen = BTreeSet::new();
    let mut graph = BTreeMap::<ModuleName, BTreeSet<ModuleName>>::new();
    let mut raw_declarations = BTreeMap::<ModuleName, Vec<Value>>::new();
    let mut captured_bases = BTreeMap::<String, (String, BTreeSet<ModuleName>)>::new();
    let mut module_positions = BTreeMap::<ModuleName, usize>::new();
    let mut consumed = 0usize;
    let mut files_to_recheck = Vec::<(PathBuf, Value)>::new();
    while let Some(name) = pending.pop_front() {
        if seen.contains(&name) {
            continue;
        }
        if seen.len() >= limits.modules {
            out.deferred_modules.push(name);
            out.deferred_modules.extend(pending);
            break;
        }
        seen.insert(name.clone());
        let mut candidates = Vec::new();
        let mut present = 0usize;
        let mut unresolved_base_path = false;
        for (root_index, root) in search_roots.iter().enumerate() {
            let base_path = match module_path(root, &name) {
                Ok(path) => path,
                Err(error) => {
                    candidates.push(json!({"root_index": root_index, "status": "unresolvable-name", "error": error}));
                    continue;
                }
            };
            let companion = |suffix: &str| {
                let mut path = base_path.as_os_str().to_os_string();
                path.push(suffix);
                PathBuf::from(path)
            };
            // Only the appended .olean suffix is replaced. A quoted dot in
            // the module component is not an extension boundary.
            let ir_path = base_path.with_extension("ir");
            let paths = [base_path.clone(), companion(".server"), companion(".private"), ir_path];
            out.observed_paths.extend(paths.iter().cloned());
            let captured: Vec<_> = paths
                .iter()
                .map(|path| {
                    let cap = capture(
                        path,
                        limits.part_bytes.min(limits.total_bytes.saturating_sub(consumed)),
                    );
                    consumed += cap.bytes.as_ref().map_or(0, Vec::len);
                    files_to_recheck.push((path.clone(), cap.record.clone()));
                    cap
                })
                .collect();
            if captured[0].record["status"] != "absent" {
                present += 1;
            }
            if captured[0].record["status"] == "captured" {
                let resolved = &captured[0].record["resolution"]["path"];
                let file_identity = &captured[0].record["file_identity"];
                let identity = file_identity["device"]
                    .as_u64()
                    .zip(file_identity["inode"].as_u64())
                    .map(|(device, inode)| format!("file:{device}:{inode}"))
                    .or_else(|| resolved["os_bytes_hex"].as_str().map(|key| format!("path:{key}")));
                match identity {
                    Some(key) => {
                        let display = resolved["display"]
                            .as_str()
                            .map_or_else(|| base_path.display().to_string(), str::to_owned);
                        captured_bases
                            .entry(key)
                            .or_insert_with(|| (display, BTreeSet::new()))
                            .1
                            .insert(name.clone());
                    }
                    _ => {
                        unresolved_base_path = true;
                        out.issues.push(format!(
                            "module {:?}, root {root_index}: captured .olean has no file or resolved path identity",
                            name.0
                        ));
                    }
                }
            }
            let declaration_content = runtime::observe(&captured);
            let mut parts = Vec::new();
            for (part_index, part) in captured.iter().enumerate() {
                let mut record = json!({"part": (["base", "server", "private", "ir"][part_index]), "requirement": if part_index == 0 { "required" } else { "optional-if-absent" }, "capture": part.record});
                record["declaration_content"] = declaration_content[part_index].clone();
                if let Some(bytes) = &part.bytes {
                    record["header"] = match OleanHeader::parse(bytes) {
                        Ok(h) => header_record(&h),
                        Err(e) => json!({"error": e.to_string()}),
                    };
                    let layout = part_dependencies(
                        bytes,
                        captured[0].bytes.as_deref(),
                        captured[1].bytes.as_deref(),
                        part_index,
                    );
                    record["dependency_resolution"] = match &layout {
                        Ok(indices) => {
                            json!({"status": "resolved-captured-part-layout", "part_indices": indices})
                        }
                        Err(error) => json!({"status": "unresolved", "error": error}),
                    };
                    let dependencies: Vec<&[u8]> = match &layout {
                        Ok(dependencies) => dependencies
                            .iter()
                            .filter_map(|&i| captured[i].bytes.as_deref())
                            .collect(),
                        Err(_) => Vec::new(),
                    };
                    let witness = names::witness(bytes, &dependencies, limits.rows_per_array);
                    if part_index < 3 {
                        runtime::reconcile(&mut record["declaration_content"], &witness);
                    }
                    let (runtime_ir, ir_errors) = match &layout {
                        Ok(_) => {
                            let observation = ir::observe(
                                bytes,
                                &dependencies,
                                limits.rows_per_array,
                                limits.ir_object_accesses,
                            );
                            (observation.report, observation.errors)
                        }
                        Err(error) => (
                            json!({"status":"unmeasured", "rows":[], "errors":[error], "authority":"diagnostic-only"}),
                            vec![error.clone()],
                        ),
                    };
                    record["runtime_ir"] = runtime_ir;
                    let parsed = layout.and_then(|dependencies| {
                        if part_index == 3 {
                            return Ok(None);
                        }
                        if !witness.errors.is_empty() {
                            return Err("full payload parsing not attempted after an incomplete/bounded raw inventory".into());
                        }
                        let parsed = std::panic::catch_unwind(|| if dependencies.is_empty() {
                            parse_module(bytes)
                        } else {
                            parse_module_incremental(
                                dependencies
                                    .first()
                                    .and_then(|&i| captured[i].bytes.as_deref())
                                    .expect("captured dependency"),
                                if dependencies.len() == 2 {
                                    captured[1].bytes.as_deref()
                                } else {
                                    None
                                },
                                bytes,
                            )
                        }).map_err(|_| "existing full parser panicked; payload observation incomplete".to_string())?;
                        parsed.map(|m| Some((m, dependencies))).map_err(|e| e.to_string())
                    });
                    let mut issues = witness.errors.clone();
                    issues.extend(ir_errors);
                    for row in witness
                        .imports
                        .iter()
                        .chain(&witness.const_names)
                        .chain(&witness.constants)
                        .chain(&witness.extra_const_names)
                    {
                        if let Some(error) = &row.error {
                            issues.push(format!("row {}: {error}", row.index));
                        }
                    }
                    for import in &witness.imports {
                        if let Some(target) = &import.name {
                            graph.entry(name.clone()).or_default().insert(target.clone());
                            pending.push_back(target.clone());
                        }
                    }
                    for row in &witness.constants {
                        if let Some(declaration) = &row.name {
                            raw_declarations.entry(declaration.clone()).or_default().push(json!({"module": name, "root_index": root_index, "part": part_index, "part_sha256": part.record["sha256"], "row_index": row.index}));
                        }
                    }
                    match parsed {
                        Ok(Some((module, dependencies))) => {
                            record["parse_status"] = json!("parsed");
                            record["part_dependencies"] = json!(dependencies);
                            record["declarations"] =
                                json!(parsed_rows(&module, &witness, &mut issues));
                            record["clean_payload_rosters"] = module
                                .clean_payload
                                .as_ref()
                                .map(payload_rosters)
                                .unwrap_or(Value::Null);
                            record["clean_payload"] = match module.clean_payload {
                                Some(payload) => {
                                    serde_json::to_value(payload).unwrap_or_else(|e| {
                                        issues.push(e.to_string());
                                        Value::Null
                                    })
                                }
                                None => Value::Null,
                            };
                            record["extensions"] = json!({"status": if dependencies.is_empty() { "parsed-with-parser-residues" } else { "unmeasured-incremental-format" },
                                "entry_count_semantics": "generic-parser-projection-counts-only",
                                "ir_computational_body_semantics": "unmeasured",
                                "entries": module.entries.iter().map(|e| json!({"parser_display_name": e.extension_name, "decoded_entries": e.entries.len(), "undecoded_entries": e.undecoded_entries})).collect::<Vec<_>>()});
                        }
                        Ok(None) => {
                            record["parse_status"] = json!("runtime-ir-part-only");
                            record["kernel_payload_semantics"] =
                                json!("not-interpreted-as-kernel-declarations");
                        }
                        Err(error) => {
                            record["parse_status"] = json!("malformed-or-unresolved-part");
                            issues.push(error);
                        }
                    }
                    record["raw_name_witness"] = json!(witness);
                    record["issues"] = json!(issues);
                    if !issues.is_empty() {
                        out.issues.push(format!("module {:?}, root {root_index}, part {part_index}: incomplete parse/witness", name.0));
                    }
                } else if part.record["status"] != "absent" {
                    out.issues.push(format!(
                        "module {:?}, root {root_index}, part {part_index}: capture failed",
                        name.0
                    ));
                }
                parts.push(record);
            }
            candidates.push(json!({"root_index": root_index, "path": path_identity(&base_path), "parts": parts}));
            if retain_bytes {
                captured_candidates.push(OleanCapturedCandidate {
                    module: name.clone(),
                    root_index,
                    parts: paths
                        .into_iter()
                        .zip(captured)
                        .map(|(path, captured)| OleanCapturedPart {
                            path,
                            bytes: captured.bytes,
                            observation: captured.record,
                        })
                        .collect(),
                });
            }
        }
        let status = match present {
            0 => "missing",
            1 if unresolved_base_path => "unresolved-candidate-path",
            1 => "one-observed-candidate",
            _ => "ambiguous-candidates",
        };
        if status != "one-observed-candidate" {
            out.issues.push(format!("module {:?}: {status}", name.0));
        }
        module_positions.insert(name.clone(), out.modules.len());
        out.modules.push(json!({"name": name, "status": status, "candidates": candidates}));
    }
    for (_, (path, modules)) in captured_bases {
        if modules.len() > 1 {
            out.issues
                .push(format!("distinct modules share captured .olean file {path}: {modules:?}"));
            for name in modules {
                let module = &mut out.modules[module_positions[&name]];
                if module["status"] == "one-observed-candidate" {
                    module["status"] = json!("aliased-candidate");
                }
            }
        }
    }
    out.cycles = cycles(&graph);
    if !out.cycles.is_empty() {
        out.issues.push("external module dependency cycle".into());
    }
    if !out.deferred_modules.is_empty() {
        out.issues.push("external module-count bound reached; pending roots retained".into());
    }
    for (name, occurrences) in raw_declarations {
        if occurrences.len() > 1 {
            out.duplicate_declarations.push(json!({"name": name, "relation": "equal-typed-name-not-equal-payload", "occurrences": occurrences}));
        }
    }
    for (path, before) in files_to_recheck {
        let limit =
            before["capture_limit"].as_u64().and_then(|n| usize::try_from(n).ok()).unwrap_or(0);
        let after = capture(&path, limit).record;
        if before != after {
            out.issues.push(format!("external path/bytes drift: {}", path.display()));
        }
        // Every before observation remains in its candidate part; retain both.
        out.file_observations
            .push(json!({"path": path_identity(&path), "before": before, "after": after}));
    }
    for (index, root) in search_roots.iter().enumerate() {
        let after = path_state(root);
        let before = out.search_roots[index]["before"].clone();
        out.search_roots[index]["after"] = after.clone();
        if before != after {
            out.issues.push(format!("search root {index} changed"));
        }
    }
    for (index, source) in sources.iter().enumerate() {
        let after = capture(&source.path, limits.part_bytes).record;
        if out.sources[index]["path_after_check"] != after {
            out.issues
                .push(format!("source {index} path/bytes changed during external observation"));
        }
        out.sources[index]["path_after_observation"] = after;
    }
    let retained_roots = search_roots
        .iter()
        .enumerate()
        .map(|(i, root)| (root.clone(), out.search_roots[i]["after"].clone()))
        .collect();
    OleanClosureCapture {
        observation: out,
        candidates: captured_candidates,
        search_roots: retained_roots,
    }
}
