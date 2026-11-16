// ignore-tidy-file-todo -- the census needle list names `todo!` as data; tidy's check is textual
//! Trust (W4 HASHMAP r2, 2026-09-27): the PANIC CENSUS of the crate behind std's
//! `HashMap`/`HashSet` — `hashbrown` — pinned to the version this repository's
//! sysroot is built from.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! # Why a census, and why pinned
//!
//! The policy-B vanilla class tolerates an absent sysroot callee's panic as "std's
//! own defined behaviour reacting to its environment". Since W4 HASHMAP it credits
//! ONE crate beyond `core`/`alloc`/`std`: the crate std's `HashMap`/`HashSet` field
//! is declared in (`trust_mir_extract::def_is_in_std_hash_table_crate`, structural,
//! never a name). hashbrown bodies are NEVER bundled, so no row is ever minted for a
//! panic inside one: every panic site hashbrown has is either unreachable from the
//! calls std makes, charged at the std call site by some other lane, or it is a
//! FALSE ACCEPT. The redo's first round claimed the disjoint-key lookups were "the
//! one caller-value panic family behind std's hash tables"; its prober refuted that
//! with nine programs through `HashSet::get_or_insert_with` (hashbrown's
//! key-equivalence `assert!`, `map.rs:4735`), each built rc=0 and panicking.
//!
//! So the whole list is written down here, site by site, with what answers each,
//! and [`tests::census_matches_the_sysroot_hashbrown`] pins it to
//! [`STD_HASH_TABLE_CRATE_VERSION`] — the version `library/Cargo.lock` builds. A
//! hashbrown bump fails that test until someone re-takes the census, so a new panic
//! site can never silently join the vanilla credit.
//!
//! # What the census scans
//!
//! Every `.rs` file under hashbrown's `src/`, up to its `#[cfg(test)] mod`: a line
//! (comments stripped, `debug_assert*` skipped — std is built without debug
//! assertions) with `panic!`, `assert!`, `assert_eq!`, `assert_ne!`,
//! `unreachable!`, `unimplemented!`, `todo!`, `.expect(`, `.unwrap()`,
//! `handle_alloc_error(` or `abort(` is a PANIC site, and a line with a bounds-checked
//! index expression (`x[i]`) is an INDEX site. Arithmetic overflow cannot panic in
//! the sysroot build (no `overflow-checks`).

/// The hashbrown version the census below was taken against — the one entry
/// `library/Cargo.lock` holds.
pub const STD_HASH_TABLE_CRATE_VERSION: &str = "0.17.1";

/// What answers one panic site of the crate behind std's hash tables.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HashTablePanicDisposition {
    /// The panic is about the CALLER's own value, and the item that holds it is
    /// EXCLUDED from the policy-B vanilla class by identity (the item's own name in
    /// the structurally identified crate — see
    /// [`std_hash_table_crate_item_panics_on_caller_value`] — and its std entry
    /// point by its owner's diagnostic item), so a call reaching it is refused.
    ExcludedByIdentity,
    /// "Hash table capacity overflow" on a caller-sized allocation: charged at the
    /// std call site by vcgen's `[unbounded_allocation]` row (the extractor's
    /// hash-table token and hashbrown's bucket-layout bound).
    ChargedByAllocationLane,
    /// Allocation failure: `handle_alloc_error` ABORTS (no unwind, no `panic!`),
    /// exactly like `Vec`'s — outside the modeled panic set.
    AllocationFailureAbort,
    /// Dead: guarded on the same line or the one above by a check that makes it
    /// unreachable.
    Unreachable,
}

/// One site of the census.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HashTablePanicSite {
    /// `(file under src/, 1-based line)`.
    pub file: &'static str,
    pub line: u32,
    /// The enclosing function (for the reader; the scan does not check it).
    pub item: &'static str,
    pub disposition: HashTablePanicDisposition,
}

use HashTablePanicDisposition::*;

/// The PANIC sites of hashbrown [`STD_HASH_TABLE_CRATE_VERSION`], every one.
pub const STD_HASH_TABLE_PANIC_SITES: &[HashTablePanicSite] = &[
    // `impl Index<&Q> for HashMap`: `self.get(key).expect("no entry found for key")`.
    // std never calls it (std's own `Index` calls hashbrown `get`, and vcgen's
    // `map-index-key-presence` row charges std's `expect`); excluded by name anyway.
    HashTablePanicSite {
        file: "map.rs",
        line: 2101,
        item: "index",
        disposition: ExcludedByIdentity,
    },
    // `OccupiedEntry::replace_key`: "replaced key is not equivalent to the one in the
    // entry". No std entry point today; excluded by name.
    HashTablePanicSite {
        file: "map.rs",
        line: 3823,
        item: "replace_key",
        disposition: ExcludedByIdentity,
    },
    // `VacantEntryRef::insert_entry_with_key`: "key used for Entry creation is not
    // equivalent to the one used for insertion". Reached from std through
    // `HashSet::get_or_insert_with` -> hashbrown `HashSet::get_or_insert_with`
    // (`set.rs:942`), and from hashbrown's `insert_with_key` (`map.rs:4618`); all
    // three are excluded by name, and std's `HashSet::get_or_insert_with` by its
    // owner's diagnostic item.
    HashTablePanicSite {
        file: "map.rs",
        line: 4735,
        item: "insert_entry_with_key",
        disposition: ExcludedByIdentity,
    },
    // `Fallibility::capacity_overflow` (Infallible arm): "Hash table capacity
    // overflow", reached from `with_capacity*`, `reserve`, `extend*`, `from_iter`,
    // `collect`/`collect_into`/`unzip` into a table.
    HashTablePanicSite {
        file: "raw.rs",
        line: 36,
        item: "capacity_overflow",
        disposition: ChargedByAllocationLane,
    },
    // `Fallibility::alloc_err` (Infallible arm): `handle_alloc_error(layout)`.
    HashTablePanicSite {
        file: "raw.rs",
        line: 45,
        item: "alloc_err",
        disposition: AllocationFailureAbort,
    },
    // `RawTable::get_disjoint_mut`: "duplicate keys found".
    HashTablePanicSite {
        file: "raw.rs",
        line: 1289,
        item: "get_disjoint_mut",
        disposition: ExcludedByIdentity,
    },
    // `find_insert_index_in_group`: `bit.unwrap()` under `if likely(bit.is_some())`.
    HashTablePanicSite {
        file: "raw.rs",
        line: 1754,
        item: "find_insert_index_in_group",
        disposition: Unreachable,
    },
];

/// The bounds-checked INDEX sites of hashbrown [`STD_HASH_TABLE_CRATE_VERSION`]:
/// every one is inside the disjoint-key family (`get_disjoint_*`, excluded by name,
/// and its private helper `build_hashes_inner`), indexing an `[_; N]` array at
/// `i < N`.
pub const STD_HASH_TABLE_INDEX_SITES: &[HashTablePanicSite] = &[
    HashTablePanicSite {
        file: "map.rs",
        line: 1755,
        item: "get_disjoint_mut_inner",
        disposition: ExcludedByIdentity,
    },
    HashTablePanicSite {
        file: "map.rs",
        line: 1768,
        item: "get_disjoint_unchecked_mut_inner",
        disposition: ExcludedByIdentity,
    },
    // `for i in 0..N { hashes[i] = .. ks[i] .. }` over two `[_; N]` arrays: in
    // bounds by construction (and only the disjoint family calls it).
    HashTablePanicSite {
        file: "map.rs",
        line: 1778,
        item: "build_hashes_inner",
        disposition: Unreachable,
    },
    HashTablePanicSite {
        file: "raw.rs",
        line: 1288,
        item: "get_disjoint_mut",
        disposition: ExcludedByIdentity,
    },
    HashTablePanicSite {
        file: "raw.rs",
        line: 1314,
        item: "get_disjoint_mut_pointers",
        disposition: ExcludedByIdentity,
    },
];

/// The items of the crate behind std's hash tables whose panics are about the
/// CALLER's values, by their own name ([`std_hash_table_crate_item_panics_on_caller_value`]).
/// `insert_with_key` and `get_or_insert_with` hold no `assert!` themselves: they are
/// the callers of `insert_entry_with_key` a std body can reach, excluded so the
/// refusal lands at the call std makes.
pub const STD_HASH_TABLE_CALLER_VALUE_PANIC_ITEMS: &[&str] =
    &["index", "replace_key", "insert_entry_with_key", "insert_with_key", "get_or_insert_with"];

/// The disjoint-key family, by name prefix (`get_disjoint_mut`,
/// `get_disjoint_key_value_mut`, `get_many_mut`, their `unchecked` forms and
/// private helpers): "duplicate keys found" when two of the caller's keys are
/// equal. Over-inclusive — the unchecked forms are UB instead — and only ever a
/// refusal.
pub const STD_HASH_TABLE_CALLER_VALUE_PANIC_PREFIXES: &[&str] = &["get_disjoint_", "get_many_"];

/// Is `item_name` (a DefId's own `opt_item_name`, never a rendering) one of the
/// caller-value panic items of the crate behind std's hash tables? The CALLER must
/// already have established that the item is in that crate
/// (`trust_mir_extract::def_is_in_std_hash_table_crate`).
#[must_use]
pub fn std_hash_table_crate_item_panics_on_caller_value(item_name: &str) -> bool {
    STD_HASH_TABLE_CALLER_VALUE_PANIC_ITEMS.contains(&item_name)
        || STD_HASH_TABLE_CALLER_VALUE_PANIC_PREFIXES.iter().any(|p| item_name.starts_with(p))
}

/// Is `item_name` an INHERENT method of std's `HashMap` whose panic is about the
/// caller's values — the std entry points of the disjoint-key family
/// (`get_disjoint_mut`, `get_disjoint_unchecked_mut`)? The caller must already
/// have established that the item is an inherent method of std's `HashMap`
/// diagnostic item.
#[must_use]
pub fn std_hash_map_method_panics_on_caller_value(item_name: &str) -> bool {
    STD_HASH_TABLE_CALLER_VALUE_PANIC_PREFIXES.iter().any(|p| item_name.starts_with(p))
}

/// Is `item_name` an INHERENT method of std's `HashSet` whose panic is about the
/// caller's values — `get_or_insert_with` (nightly `hash_set_entry`), which hands
/// the CALLER's `f(value)` to hashbrown's key-equivalence `assert!`? The caller
/// must already have established that the item is an inherent method of std's
/// `HashSet` diagnostic item.
#[must_use]
pub fn std_hash_set_method_panics_on_caller_value(item_name: &str) -> bool {
    item_name == "get_or_insert_with"
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::*;

    /// The `hashbrown` version(s) `library/Cargo.lock` builds.
    fn sysroot_hashbrown_versions() -> Vec<String> {
        let lock = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/Cargo.lock");
        let text = std::fs::read_to_string(&lock)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", lock.display()));
        let mut versions = Vec::new();
        let mut lines = text.lines();
        while let Some(line) = lines.next() {
            if line.trim() == "name = \"hashbrown\"" {
                let version = lines
                    .next()
                    .and_then(|v| v.trim().strip_prefix("version = \""))
                    .and_then(|v| v.strip_suffix('"'))
                    .expect("a Cargo.lock package entry carries its version on the next line");
                versions.push(version.to_string());
            }
        }
        versions
    }

    #[test]
    fn census_is_pinned_to_the_hashbrown_the_sysroot_builds() {
        assert_eq!(
            sysroot_hashbrown_versions(),
            vec![STD_HASH_TABLE_CRATE_VERSION.to_string()],
            "library/Cargo.lock no longer builds hashbrown {STD_HASH_TABLE_CRATE_VERSION}. \
             The policy-B vanilla class credits that crate's panics as std behaviour \
             (docs/TCB.md, \"hashbrown behind std's HashMap/HashSet\"): RE-TAKE the panic \
             census in crates/trust-vcgen/src/std_hash_table_census.rs against the new \
             version (every new site needs a disposition and, if it is about a caller's \
             value, an exclusion), then move STD_HASH_TABLE_CRATE_VERSION."
        );
    }

    /// Scan one hashbrown source file the way the module doc says.
    fn scan(
        rel: &str,
        text: &str,
        panics: &mut Vec<(String, u32)>,
        indexes: &mut Vec<(String, u32)>,
    ) {
        const PANIC_PATTERNS: &[&str] = &[
            "panic!",
            "assert!",
            "assert_eq!",
            "assert_ne!",
            "unreachable!",
            "unimplemented!",
            "todo!",
            ".expect(",
            ".unwrap()",
            "handle_alloc_error(",
            "abort(",
        ];
        let mut after_cfg_test = false;
        for (index, raw) in text.lines().enumerate() {
            let line = raw.trim();
            let is_mod = line.starts_with("mod ")
                || line.starts_with("pub mod ")
                || line.starts_with("pub(crate) mod ");
            if after_cfg_test && is_mod {
                break;
            }
            after_cfg_test =
                line.starts_with("#[cfg(test)]") || (after_cfg_test && line.starts_with("#["));
            if line.starts_with("//") {
                continue;
            }
            let code = line.split("//").next().unwrap_or(line);
            if code.contains("debug_assert") {
                continue;
            }
            let lineno = u32::try_from(index + 1).expect("line numbers fit in u32");
            if PANIC_PATTERNS.iter().any(|p| code.contains(p)) {
                panics.push((rel.to_string(), lineno));
            } else if is_index_expression(code) {
                indexes.push((rel.to_string(), lineno));
            }
        }
    }

    /// `x[i]` / `f()[i]` / `a[b][c]` as an EXPRESSION — not a type (`[T; N]`,
    /// `&[T]`, `-> [..]`, `: [..]`, `<[T]>`), not an attribute, not a signature.
    fn is_index_expression(code: &str) -> bool {
        if code.starts_with("#[")
            || code.contains("fn ")
            || [": [", "-> [", "<[", "&["].iter().any(|t| code.contains(t))
        {
            return false;
        }
        let bytes = code.as_bytes();
        bytes.windows(3).any(|w| {
            (w[0].is_ascii_alphanumeric() || matches!(w[0], b'_' | b')' | b']'))
                && w[1] == b'['
                && !matches!(w[2], b']' | b' ' | b'\t')
        })
    }

    /// hashbrown's `src/` for [`STD_HASH_TABLE_CRATE_VERSION`] in the local cargo
    /// registry, if one is there.
    fn registry_source() -> Option<PathBuf> {
        let cargo_home = std::env::var_os("CARGO_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")))?;
        let dir = format!("hashbrown-{STD_HASH_TABLE_CRATE_VERSION}");
        std::fs::read_dir(cargo_home.join("registry/src"))
            .ok()?
            .filter_map(Result::ok)
            .map(|index| index.path().join(&dir).join("src"))
            .find(|src| src.join("raw.rs").is_file())
    }

    fn walk(dir: &Path, root: &Path, files: &mut Vec<(String, PathBuf)>) {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
            .expect("readable source directory")
            .filter_map(Result::ok)
            .map(|e| e.path())
            .collect();
        entries.sort();
        for path in entries {
            if path.is_dir() {
                walk(&path, root, files);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(root).expect("under root").to_string_lossy();
                files.push((rel.replace('\\', "/"), path));
            }
        }
    }

    /// Re-take the census from the registry source when it is present, and compare
    /// it SITE FOR SITE with the pinned tables. Absent source (a machine that never
    /// fetched it) only skips this half; the version pin above still holds.
    #[test]
    fn census_matches_the_sysroot_hashbrown() {
        let Some(src) = registry_source() else {
            eprintln!(
                "hashbrown-{STD_HASH_TABLE_CRATE_VERSION} source not in the cargo registry; \
                 the site-for-site census comparison is skipped (the version pin still runs)"
            );
            return;
        };
        let mut files = Vec::new();
        walk(&src, &src, &mut files);
        let (mut panics, mut indexes) = (Vec::new(), Vec::new());
        for (rel, path) in &files {
            let text = std::fs::read_to_string(path).expect("readable source file");
            scan(rel, &text, &mut panics, &mut indexes);
        }
        let pinned = |sites: &[HashTablePanicSite]| -> Vec<(String, u32)> {
            sites.iter().map(|s| (s.file.to_string(), s.line)).collect()
        };
        assert_eq!(
            panics,
            pinned(STD_HASH_TABLE_PANIC_SITES),
            "hashbrown {STD_HASH_TABLE_CRATE_VERSION}'s PANIC sites differ from the pinned census"
        );
        assert_eq!(
            indexes,
            pinned(STD_HASH_TABLE_INDEX_SITES),
            "hashbrown {STD_HASH_TABLE_CRATE_VERSION}'s INDEX sites differ from the pinned census"
        );
    }

    #[test]
    fn every_caller_value_site_is_excluded_by_its_items_name() {
        for site in STD_HASH_TABLE_PANIC_SITES.iter().chain(STD_HASH_TABLE_INDEX_SITES) {
            if site.disposition == ExcludedByIdentity {
                assert!(
                    std_hash_table_crate_item_panics_on_caller_value(site.item),
                    "{}:{} ({}) is marked excluded but its item is not",
                    site.file,
                    site.line,
                    site.item
                );
            }
        }
        // The std entry points.
        assert!(std_hash_set_method_panics_on_caller_value("get_or_insert_with"));
        assert!(!std_hash_set_method_panics_on_caller_value("get_or_insert"));
        assert!(std_hash_map_method_panics_on_caller_value("get_disjoint_mut"));
        assert!(std_hash_map_method_panics_on_caller_value("get_disjoint_unchecked_mut"));
        assert!(!std_hash_map_method_panics_on_caller_value("get_mut"));
        // Ordinary table operations stay credited.
        for ok in ["insert", "get", "remove", "reserve", "with_capacity_and_hasher", "extend"] {
            assert!(!std_hash_table_crate_item_panics_on_caller_value(ok), "{ok}");
        }
    }
}
