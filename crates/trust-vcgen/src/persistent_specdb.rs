// trust_vcgen/persistent_specdb.rs: Persistent spec database with JSON storage
//
// Provides `PersistentSpecDatabase` — a persistent storage layer for function
// specifications. Specs come from three sources: User (explicit annotations),
// Inferred (automatic analysis), and Heuristic (name/pattern-based guesses).
// The database is serialized to/from `trust-specs.json` for cross-session persistence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use serde::{Deserialize, Serialize};
use trust_types::fx::FxHashMap;
use trust_types::{Formula, FunctionSpec, SpecParseError};

// ---------------------------------------------------------------------------
// SpecSource — where the spec came from
// ---------------------------------------------------------------------------

/// Origin of a spec entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SpecSource {
    /// Explicit user annotation (`#[requires]`, `#[ensures]`).
    User,
    /// Inferred from function signatures, bodies, or assertions.
    Inferred,
    /// Heuristic guess from naming conventions or patterns.
    Heuristic,
}

impl std::fmt::Display for SpecSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpecSource::User => f.write_str("user"),
            SpecSource::Inferred => f.write_str("inferred"),
            SpecSource::Heuristic => f.write_str("heuristic"),
        }
    }
}

// ---------------------------------------------------------------------------
// InferenceConfidence — how confident the inference is
// ---------------------------------------------------------------------------

/// Confidence level for an inferred spec.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum InferenceConfidence {
    /// Low confidence — heuristic guess, may be wrong.
    Low,
    /// Medium confidence — structural inference with some evidence.
    Medium,
    /// High confidence — strong type-level or assertion-based evidence.
    High,
    /// Certain — from user annotation or trivially true.
    Certain,
}

impl std::fmt::Display for InferenceConfidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InferenceConfidence::Low => f.write_str("low"),
            InferenceConfidence::Medium => f.write_str("medium"),
            InferenceConfidence::High => f.write_str("high"),
            InferenceConfidence::Certain => f.write_str("certain"),
        }
    }
}

// ---------------------------------------------------------------------------
// SpecEntry — one spec record in the database
// ---------------------------------------------------------------------------

/// A single spec entry in the persistent database.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SpecEntry {
    /// Fully qualified function name.
    pub function_name: String,
    /// Module path (e.g., `crate::module::submodule`).
    pub module_path: String,
    /// The specification itself.
    pub spec: FunctionSpec,
    /// Where the spec came from.
    pub source: SpecSource,
    /// Confidence in the spec's correctness.
    pub confidence: InferenceConfidence,
    /// Timestamp of last successful verification (epoch seconds), if any.
    pub last_verified: Option<u64>,
    /// Optional content hash of the function body when the spec was recorded.
    /// Used to detect when the function has changed and the spec may be stale.
    #[serde(default)]
    pub body_hash: Option<String>,
}

impl SpecEntry {
    /// Create a new spec entry.
    pub fn new(
        function_name: impl Into<String>,
        module_path: impl Into<String>,
        spec: FunctionSpec,
        source: SpecSource,
        confidence: InferenceConfidence,
    ) -> Self {
        Self {
            function_name: function_name.into(),
            module_path: module_path.into(),
            spec,
            source,
            confidence,
            last_verified: None,
            body_hash: None,
        }
    }

    /// Create a user-annotated entry (always Certain confidence).
    pub fn user(
        function_name: impl Into<String>,
        module_path: impl Into<String>,
        spec: FunctionSpec,
    ) -> Self {
        Self::new(function_name, module_path, spec, SpecSource::User, InferenceConfidence::Certain)
    }

    /// The lookup key for this entry: `module_path::function_name`.
    #[must_use]
    pub fn key(&self) -> String {
        if self.module_path.is_empty() {
            self.function_name.clone()
        } else {
            format!("{}::{}", self.module_path, self.function_name)
        }
    }

    /// Mark this entry as verified now (unix timestamp).
    pub fn mark_verified(&mut self, timestamp: u64) {
        self.last_verified = Some(timestamp);
    }

    /// Check if this entry's body hash matches a given hash.
    /// Returns true if no body hash is stored (optimistic).
    #[must_use]
    pub fn body_matches(&self, current_hash: &str) -> bool {
        match &self.body_hash {
            Some(h) => h == current_hash,
            None => true,
        }
    }
}

// ---------------------------------------------------------------------------
// SpecDiff — differences between two databases
// ---------------------------------------------------------------------------

/// A difference record between two spec databases.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SpecDiff {
    /// Entries added in the new database.
    pub added: Vec<SpecEntry>,
    /// Entries removed from the old database.
    pub removed: Vec<SpecEntry>,
    /// Entries that changed (old, new).
    pub changed: Vec<(SpecEntry, SpecEntry)>,
}

impl SpecDiff {
    /// Returns true if there are no differences.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.added.is_empty() && self.removed.is_empty() && self.changed.is_empty()
    }

    /// Total number of differences.
    #[must_use]
    pub fn len(&self) -> usize {
        self.added.len() + self.removed.len() + self.changed.len()
    }
}

// ---------------------------------------------------------------------------
// PersistentSpecDatabase — the main database
// ---------------------------------------------------------------------------

/// Persistent database of function specifications.
///
/// Stores specs keyed by `module_path::function_name` and supports
/// JSON file persistence via `load`/`save`.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PersistentSpecDatabase {
    /// Version for forward compatibility.
    #[serde(default = "default_version")]
    pub version: u32,
    /// Spec entries keyed by fully qualified function path.
    pub entries: FxHashMap<String, SpecEntry>,
}

fn default_version() -> u32 {
    1
}

/// Errors that can occur during specdb operations.
#[derive(Debug, thiserror::Error)]
pub enum SpecDbError {
    /// I/O error reading or writing the database file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// JSON serialization/deserialization error.
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
}

impl PersistentSpecDatabase {
    /// Create an empty database.
    #[must_use]
    pub fn new() -> Self {
        Self { version: 1, entries: FxHashMap::default() }
    }

    /// Number of entries in the database.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Returns true if the database has no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    // -- Persistence --

    /// Load from a JSON file. Returns an empty database if the file does not exist.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, SpecDbError> {
        let path = path.as_ref();
        if !path.exists() {
            return Ok(Self::new());
        }
        let contents = std::fs::read_to_string(path)?;
        let db: Self = serde_json::from_str(&contents)?;
        Ok(db)
    }

    /// Save to a JSON file (pretty-printed for human readability).
    pub fn save(&self, path: impl AsRef<Path>) -> Result<(), SpecDbError> {
        let json = serde_json::to_string_pretty(self)?;
        std::fs::write(path, json)?;
        Ok(())
    }

    // -- CRUD operations --

    /// Insert or update a spec entry. Returns the previous entry if one existed.
    pub fn insert(&mut self, entry: SpecEntry) -> Option<SpecEntry> {
        let key = entry.key();
        self.entries.insert(key, entry)
    }

    /// Look up a spec entry by fully qualified path.
    #[must_use]
    pub fn lookup(&self, qualified_path: &str) -> Option<&SpecEntry> {
        self.entries.get(qualified_path)
    }

    /// Look up a spec entry by function name (searches all entries).
    /// Returns the first match. Use `lookup` for precise matching.
    #[must_use]
    pub fn lookup_by_name(&self, function_name: &str) -> Option<&SpecEntry> {
        self.entries.values().find(|e| e.function_name == function_name)
    }

    /// Remove an entry by qualified path.
    pub fn remove(&mut self, qualified_path: &str) -> Option<SpecEntry> {
        self.entries.remove(qualified_path)
    }

    /// Iterate over all entries.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &SpecEntry)> {
        self.entries.iter().map(|(k, v)| (k.as_str(), v))
    }

    // -- Merge --

    /// Merge another database into this one.
    ///
    /// Conflict resolution: higher confidence wins. On tie, the newer entry
    /// (from `other`) wins. User specs always override inferred/heuristic.
    pub fn merge(&mut self, other: &PersistentSpecDatabase) {
        for (key, new_entry) in &other.entries {
            match self.entries.get(key) {
                Some(existing) => {
                    if should_replace(existing, new_entry) {
                        self.entries.insert(key.clone(), new_entry.clone());
                    }
                }
                None => {
                    self.entries.insert(key.clone(), new_entry.clone());
                }
            }
        }
    }

    // -- Diff --

    /// Compute the difference between this database and another.
    /// `self` is treated as "old", `other` as "new".
    #[must_use]
    pub fn diff(&self, other: &PersistentSpecDatabase) -> SpecDiff {
        let mut added = Vec::new();
        let mut removed = Vec::new();
        let mut changed = Vec::new();

        // Find added and changed entries.
        for (key, new_entry) in &other.entries {
            match self.entries.get(key) {
                Some(old_entry) => {
                    if old_entry != new_entry {
                        changed.push((old_entry.clone(), new_entry.clone()));
                    }
                }
                None => added.push(new_entry.clone()),
            }
        }

        // Find removed entries.
        for (key, old_entry) in &self.entries {
            if !other.entries.contains_key(key) {
                removed.push(old_entry.clone());
            }
        }

        SpecDiff { added, removed, changed }
    }

    // -- Prune stale --

    /// Remove entries whose body hash does not match the current hash.
    ///
    /// Takes a map from qualified path to current body hash. Entries not
    /// in the map are left untouched (they may belong to functions not
    /// currently being compiled).
    pub fn prune_stale(&mut self, current_hashes: &FxHashMap<String, String>) -> Vec<SpecEntry> {
        let mut pruned = Vec::new();
        self.entries.retain(|key, entry| {
            if let Some(current_hash) = current_hashes.get(key) {
                if entry.body_matches(current_hash) {
                    true
                } else {
                    pruned.push(entry.clone());
                    false
                }
            } else {
                true // not in current compilation, keep
            }
        });
        pruned
    }

    /// Collect entries filtered by source.
    #[must_use]
    pub fn entries_by_source(&self, source: SpecSource) -> Vec<&SpecEntry> {
        self.entries.values().filter(|e| e.source == source).collect()
    }

    /// Collect entries filtered by minimum confidence.
    #[must_use]
    pub fn entries_by_min_confidence(
        &self,
        min_confidence: InferenceConfidence,
    ) -> Vec<&SpecEntry> {
        self.entries.values().filter(|e| e.confidence >= min_confidence).collect()
    }

    /// Convert all stored specs to a map of function name -> Formula vectors
    /// for use in VC generation. Only includes entries at or above the given
    /// minimum confidence.
    pub fn preconditions_map(
        &self,
        min_confidence: InferenceConfidence,
    ) -> Result<FxHashMap<String, Vec<Formula>>, SpecParseError> {
        let mut map: FxHashMap<String, Vec<Formula>> = FxHashMap::default();
        for entry in self.entries.values() {
            if entry.confidence >= min_confidence {
                let formulas = entry.spec.parse_requires()?;
                if !formulas.is_empty() {
                    map.entry(entry.function_name.clone()).or_default().extend(formulas);
                }
            }
        }
        Ok(map)
    }
}

/// Determine if `new_entry` should replace `existing`.
fn should_replace(existing: &SpecEntry, new_entry: &SpecEntry) -> bool {
    // User specs always win over non-user.
    if new_entry.source == SpecSource::User && existing.source != SpecSource::User {
        return true;
    }
    if existing.source == SpecSource::User && new_entry.source != SpecSource::User {
        return false;
    }
    // Higher confidence wins.
    new_entry.confidence >= existing.confidence
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_entry(name: &str, module: &str, source: SpecSource) -> SpecEntry {
        SpecEntry::new(
            name,
            module,
            FunctionSpec {
                requires: vec!["x > 0".to_string()],
                ensures: vec!["result >= 0".to_string()],
                invariants: vec![],
            },
            source,
            InferenceConfidence::High,
        )
    }

    #[test]
    fn test_spec_entry_key() {
        let entry = make_entry("foo", "crate::bar", SpecSource::User);
        assert_eq!(entry.key(), "crate::bar::foo");
    }

    #[test]
    fn test_spec_entry_key_empty_module() {
        let entry = make_entry("foo", "", SpecSource::User);
        assert_eq!(entry.key(), "foo");
    }

    #[test]
    fn test_spec_entry_body_matches() {
        let mut entry = make_entry("f", "m", SpecSource::User);
        assert!(entry.body_matches("any"), "no hash stored => optimistic match");

        entry.body_hash = Some("abc123".to_string());
        assert!(entry.body_matches("abc123"));
        assert!(!entry.body_matches("def456"));
    }

    #[test]
    fn test_spec_entry_mark_verified() {
        let mut entry = make_entry("f", "m", SpecSource::User);
        assert!(entry.last_verified.is_none());
        entry.mark_verified(1234567890);
        assert_eq!(entry.last_verified, Some(1234567890));
    }

    #[test]
    fn test_persistent_specdb_new_empty() {
        let db = PersistentSpecDatabase::new();
        assert!(db.is_empty());
        assert_eq!(db.len(), 0);
        assert_eq!(db.version, 1);
    }

    #[test]
    fn test_persistent_specdb_insert_and_lookup() {
        let mut db = PersistentSpecDatabase::new();
        let entry = make_entry("foo", "crate::bar", SpecSource::User);
        assert!(db.insert(entry.clone()).is_none());

        assert_eq!(db.len(), 1);
        let found = db.lookup("crate::bar::foo").expect("should find entry");
        assert_eq!(found.function_name, "foo");
    }

    #[test]
    fn test_persistent_specdb_insert_replaces() {
        let mut db = PersistentSpecDatabase::new();
        let entry1 = make_entry("foo", "mod", SpecSource::User);
        let mut entry2 = make_entry("foo", "mod", SpecSource::Inferred);
        entry2.confidence = InferenceConfidence::Low;

        db.insert(entry1);
        let old = db.insert(entry2);
        assert!(old.is_some());
        assert_eq!(db.len(), 1);
    }

    #[test]
    fn test_persistent_specdb_lookup_by_name() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(make_entry("foo", "a::b", SpecSource::User));
        db.insert(make_entry("bar", "c::d", SpecSource::Inferred));

        let found = db.lookup_by_name("bar").expect("should find");
        assert_eq!(found.module_path, "c::d");

        assert!(db.lookup_by_name("nonexistent").is_none());
    }

    #[test]
    fn test_persistent_specdb_remove() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(make_entry("foo", "mod", SpecSource::User));
        assert_eq!(db.len(), 1);

        let removed = db.remove("mod::foo");
        assert!(removed.is_some());
        assert!(db.is_empty());
    }

    #[test]
    fn test_persistent_specdb_json_roundtrip() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(make_entry("foo", "crate::bar", SpecSource::User));
        db.insert(make_entry("baz", "crate::qux", SpecSource::Inferred));

        let json = serde_json::to_string_pretty(&db).expect("serialize");
        let round: PersistentSpecDatabase = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.len(), 2);
        assert!(round.lookup("crate::bar::foo").is_some());
        assert!(round.lookup("crate::qux::baz").is_some());
    }

    #[test]
    fn test_persistent_specdb_file_roundtrip() {
        let dir = std::env::temp_dir().join("trust_vcgen-test-specdb");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("trust-specs.json");

        let mut db = PersistentSpecDatabase::new();
        db.insert(make_entry("hello", "world", SpecSource::User));
        db.save(&path).expect("save");

        let loaded = PersistentSpecDatabase::load(&path).expect("load");
        assert_eq!(loaded.len(), 1);
        assert!(loaded.lookup("world::hello").is_some());

        // Cleanup
        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_dir(&dir);
    }

    #[test]
    fn test_persistent_specdb_load_nonexistent_returns_empty() {
        let loaded = PersistentSpecDatabase::load("/tmp/trust_vcgen-nonexistent-12345.json")
            .expect("should not error");
        assert!(loaded.is_empty());
    }

    #[test]
    fn test_persistent_specdb_merge_adds_new() {
        let mut db1 = PersistentSpecDatabase::new();
        db1.insert(make_entry("foo", "m", SpecSource::User));

        let mut db2 = PersistentSpecDatabase::new();
        db2.insert(make_entry("bar", "m", SpecSource::Inferred));

        db1.merge(&db2);
        assert_eq!(db1.len(), 2);
    }

    #[test]
    fn test_persistent_specdb_merge_user_wins() {
        let mut db1 = PersistentSpecDatabase::new();
        db1.insert(SpecEntry::new(
            "foo",
            "m",
            FunctionSpec { requires: vec!["x > 0".into()], ..Default::default() },
            SpecSource::Inferred,
            InferenceConfidence::High,
        ));

        let mut db2 = PersistentSpecDatabase::new();
        db2.insert(SpecEntry::new(
            "foo",
            "m",
            FunctionSpec { requires: vec!["x >= 0".into()], ..Default::default() },
            SpecSource::User,
            InferenceConfidence::Certain,
        ));

        db1.merge(&db2);
        assert_eq!(db1.len(), 1);
        let entry = db1.lookup("m::foo").unwrap();
        assert_eq!(entry.source, SpecSource::User);
        assert_eq!(entry.spec.requires[0], "x >= 0");
    }

    #[test]
    fn test_persistent_specdb_merge_higher_confidence_wins() {
        let mut db1 = PersistentSpecDatabase::new();
        db1.insert(SpecEntry::new(
            "foo",
            "m",
            FunctionSpec::default(),
            SpecSource::Inferred,
            InferenceConfidence::Low,
        ));

        let mut db2 = PersistentSpecDatabase::new();
        db2.insert(SpecEntry::new(
            "foo",
            "m",
            FunctionSpec { requires: vec!["x > 0".into()], ..Default::default() },
            SpecSource::Inferred,
            InferenceConfidence::High,
        ));

        db1.merge(&db2);
        let entry = db1.lookup("m::foo").unwrap();
        assert_eq!(entry.confidence, InferenceConfidence::High);
    }

    #[test]
    fn test_persistent_specdb_diff_empty() {
        let db1 = PersistentSpecDatabase::new();
        let db2 = PersistentSpecDatabase::new();
        let diff = db1.diff(&db2);
        assert!(diff.is_empty());
        assert_eq!(diff.len(), 0);
    }

    #[test]
    fn test_persistent_specdb_diff_added() {
        let db1 = PersistentSpecDatabase::new();
        let mut db2 = PersistentSpecDatabase::new();
        db2.insert(make_entry("foo", "m", SpecSource::User));

        let diff = db1.diff(&db2);
        assert_eq!(diff.added.len(), 1);
        assert!(diff.removed.is_empty());
        assert!(diff.changed.is_empty());
    }

    #[test]
    fn test_persistent_specdb_diff_removed() {
        let mut db1 = PersistentSpecDatabase::new();
        db1.insert(make_entry("foo", "m", SpecSource::User));
        let db2 = PersistentSpecDatabase::new();

        let diff = db1.diff(&db2);
        assert!(diff.added.is_empty());
        assert_eq!(diff.removed.len(), 1);
    }

    #[test]
    fn test_persistent_specdb_diff_changed() {
        let mut db1 = PersistentSpecDatabase::new();
        db1.insert(make_entry("foo", "m", SpecSource::User));

        let mut db2 = PersistentSpecDatabase::new();
        let mut changed = make_entry("foo", "m", SpecSource::User);
        changed.confidence = InferenceConfidence::Low;
        db2.insert(changed);

        let diff = db1.diff(&db2);
        assert!(diff.added.is_empty());
        assert!(diff.removed.is_empty());
        assert_eq!(diff.changed.len(), 1);
    }

    #[test]
    fn test_persistent_specdb_prune_stale() {
        let mut db = PersistentSpecDatabase::new();
        let mut entry1 = make_entry("foo", "m", SpecSource::User);
        entry1.body_hash = Some("hash_a".to_string());
        db.insert(entry1);

        let mut entry2 = make_entry("bar", "m", SpecSource::Inferred);
        entry2.body_hash = Some("hash_b".to_string());
        db.insert(entry2);

        let mut hashes = FxHashMap::default();
        hashes.insert("m::foo".to_string(), "hash_a".to_string()); // matches
        hashes.insert("m::bar".to_string(), "hash_CHANGED".to_string()); // stale

        let pruned = db.prune_stale(&hashes);
        assert_eq!(pruned.len(), 1);
        assert_eq!(pruned[0].function_name, "bar");
        assert_eq!(db.len(), 1);
        assert!(db.lookup("m::foo").is_some());
    }

    #[test]
    fn test_persistent_specdb_entries_by_source() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(make_entry("a", "m", SpecSource::User));
        db.insert(make_entry("b", "m", SpecSource::Inferred));
        db.insert(make_entry("c", "m", SpecSource::Heuristic));

        assert_eq!(db.entries_by_source(SpecSource::User).len(), 1);
        assert_eq!(db.entries_by_source(SpecSource::Inferred).len(), 1);
        assert_eq!(db.entries_by_source(SpecSource::Heuristic).len(), 1);
    }

    #[test]
    fn test_persistent_specdb_entries_by_min_confidence() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(SpecEntry::new(
            "a",
            "m",
            FunctionSpec::default(),
            SpecSource::Heuristic,
            InferenceConfidence::Low,
        ));
        db.insert(SpecEntry::new(
            "b",
            "m",
            FunctionSpec::default(),
            SpecSource::Inferred,
            InferenceConfidence::Medium,
        ));
        db.insert(SpecEntry::new(
            "c",
            "m",
            FunctionSpec::default(),
            SpecSource::Inferred,
            InferenceConfidence::High,
        ));
        db.insert(SpecEntry::new(
            "d",
            "m",
            FunctionSpec::default(),
            SpecSource::User,
            InferenceConfidence::Certain,
        ));

        assert_eq!(db.entries_by_min_confidence(InferenceConfidence::Low).len(), 4);
        assert_eq!(db.entries_by_min_confidence(InferenceConfidence::Medium).len(), 3);
        assert_eq!(db.entries_by_min_confidence(InferenceConfidence::High).len(), 2);
        assert_eq!(db.entries_by_min_confidence(InferenceConfidence::Certain).len(), 1);
    }

    #[test]
    fn test_persistent_specdb_preconditions_map() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(SpecEntry::new(
            "foo",
            "m",
            FunctionSpec { requires: vec!["x > 0".into()], ..Default::default() },
            SpecSource::User,
            InferenceConfidence::Certain,
        ));
        db.insert(SpecEntry::new(
            "bar",
            "m",
            FunctionSpec { requires: vec!["y >= 0".into()], ..Default::default() },
            SpecSource::Heuristic,
            InferenceConfidence::Low,
        ));

        // High confidence threshold: only foo
        let map = db.preconditions_map(InferenceConfidence::High).expect("valid preconditions");
        assert_eq!(map.len(), 1);
        assert!(map.contains_key("foo"));

        // Low confidence threshold: both
        let map = db.preconditions_map(InferenceConfidence::Low).expect("valid preconditions");
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_persistent_specdb_preconditions_map_rejects_invalid_clause() {
        let mut db = PersistentSpecDatabase::new();
        db.insert(SpecEntry::new(
            "broken",
            "m",
            FunctionSpec { requires: vec!["???".into()], ..Default::default() },
            SpecSource::User,
            InferenceConfidence::Certain,
        ));

        assert!(db.preconditions_map(InferenceConfidence::Low).is_err());
    }

    #[test]
    fn test_inference_confidence_ordering() {
        assert!(InferenceConfidence::Low < InferenceConfidence::Medium);
        assert!(InferenceConfidence::Medium < InferenceConfidence::High);
        assert!(InferenceConfidence::High < InferenceConfidence::Certain);
    }

    #[test]
    fn test_spec_source_display() {
        assert_eq!(format!("{}", SpecSource::User), "user");
        assert_eq!(format!("{}", SpecSource::Inferred), "inferred");
        assert_eq!(format!("{}", SpecSource::Heuristic), "heuristic");
    }

    #[test]
    fn test_spec_diff_len() {
        let diff = SpecDiff {
            added: vec![make_entry("a", "m", SpecSource::User)],
            removed: vec![make_entry("b", "m", SpecSource::User)],
            changed: vec![(
                make_entry("c", "m", SpecSource::User),
                make_entry("c", "m", SpecSource::Inferred),
            )],
        };
        assert_eq!(diff.len(), 3);
        assert!(!diff.is_empty());
    }
}
