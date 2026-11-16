//! Critique C-3 change 2: the link-level backstop, the SYMBOL census.
//!
//! The trust-ir census sees only the bodies the producer spliced, and the
//! HIR site census only direct calls in this crate's source. A spawn inside
//! an upstream crate (`nix`, `async-process`, a vendored helper) leaves no
//! trace in either (the review's F12: `upstream_spawn::spawn_leaky` — fork,
//! `dup`, exec, no strip). Its object code does: an undefined reference to
//! `_fork`/`_execv`/`_posix_spawn`/…, or to std's mangled `Command::spawn`.
//!
//! [`classify`] reads the undefined symbols of one crate's objects (`nm -u`
//! over its rlib, MIR-free and rustc-free) into capability references;
//! [`check`] applies the rule: every crate with a spawn-, lock- or
//! descriptor-capable reference is under the policy or listed, with a
//! reason, in an audited third-party table (`third-party-spawners.tsv`).
//! [`spawn_capable`] is the set [`crate::CensusContext::spawn_capable_crates`]
//! hands the trust-ir census: a call into one of those crates is a site
//! (`SiteKind::UpstreamSpawn`), refused (`PC-UPSTREAM`) until its fragment
//! is analysed (C8).

use std::collections::{BTreeMap, BTreeSet};

/// What a referenced symbol can do.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Capability {
    /// Creates a process or replaces an image.
    Spawn,
    /// Takes or releases a file lock.
    Lock,
    /// Operates on descriptor numbers (or may: `syscall`, `dlsym`).
    FdNumber,
}

/// libc symbols by capability (Mach-O spells them with a leading `_`).
const LIBC: &[(&str, Capability)] = &[
    ("fork", Capability::Spawn),
    ("vfork", Capability::Spawn),
    ("forkpty", Capability::Spawn),
    ("posix_spawn", Capability::Spawn),
    ("posix_spawnp", Capability::Spawn),
    ("execv", Capability::Spawn),
    ("execve", Capability::Spawn),
    ("execvp", Capability::Spawn),
    ("execvP", Capability::Spawn),
    ("execl", Capability::Spawn),
    ("execle", Capability::Spawn),
    ("execlp", Capability::Spawn),
    ("system", Capability::Spawn),
    ("popen", Capability::Spawn),
    ("daemon", Capability::Spawn),
    ("flock", Capability::Lock),
    ("lockf", Capability::Lock),
    ("fcntl", Capability::FdNumber),
    ("dup", Capability::FdNumber),
    ("dup2", Capability::FdNumber),
    ("close", Capability::FdNumber),
    ("ioctl", Capability::FdNumber),
    ("syscall", Capability::FdNumber),
    ("dlsym", Capability::FdNumber),
];

/// std's spawning functions, by a substring of their mangled names: legacy
/// `_ZN…` and v0 `_R…` manglings both spell identifiers with their lengths,
/// and v0 may split a path with back-references, so the pattern is the
/// last two segments; the symbol must also name the `std` crate (`3std`).
const STD_MANGLED: &[(&str, &str, Capability)] = &[
    ("7Command5spawn", "std::process::Command::spawn", Capability::Spawn),
    ("7Command6output", "std::process::Command::output", Capability::Spawn),
    ("7Command6status", "std::process::Command::status", Capability::Spawn),
    ("11CommandExt4exec", "std::os::unix::process::CommandExt::exec", Capability::Spawn),
    ("4File4lock", "std::fs::File::lock", Capability::Lock),
    ("4File11lock_shared", "std::fs::File::lock_shared", Capability::Lock),
    ("4File8try_lock", "std::fs::File::try_lock", Capability::Lock),
];

/// One capability reference of a crate's object code.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Reference {
    /// The symbol as `nm` printed it.
    pub symbol: String,
    /// What it names (`fork`, `std::process::Command::spawn`).
    pub names: String,
    pub capability: Capability,
}

/// The undefined symbols in `nm -u` output (`U <symbol>` lines, or bare
/// symbols; object headers and "no symbols" notes are skipped).
#[must_use]
pub fn parse_nm(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|l| {
            let t = l.trim();
            if t.is_empty() || t.ends_with(':') || t.contains("no symbols") {
                return None;
            }
            Some(t.strip_prefix("U ").unwrap_or(t).trim().to_string())
        })
        .collect()
}

/// The capability references among `undefined` (one symbol per entry, as
/// `nm -u` prints them; Mach-O's leading `_` is accepted and not required).
#[must_use]
pub fn classify(undefined: &[String]) -> Vec<Reference> {
    let mut out = Vec::new();
    for raw in undefined {
        let sym = raw.trim();
        if sym.is_empty() || sym.ends_with(':') {
            continue;
        }
        let c_name = sym.strip_prefix('_').unwrap_or(sym);
        if let Some((n, cap)) = LIBC.iter().find(|(n, _)| *n == c_name) {
            out.push(Reference {
                symbol: sym.to_string(),
                names: (*n).to_string(),
                capability: *cap,
            });
            continue;
        }
        if sym.contains("3std")
            && let Some((_, path, cap)) = STD_MANGLED.iter().find(|(k, _, _)| sym.contains(k))
        {
            out.push(Reference {
                symbol: sym.to_string(),
                names: (*path).to_string(),
                capability: *cap,
            });
        }
    }
    out.sort();
    out.dedup();
    out
}

fn has_spawn_capability(undefined: &[String]) -> bool {
    for raw in undefined {
        let sym = raw.trim();
        if sym.is_empty() || sym.ends_with(':') {
            continue;
        }
        let c_name = sym.strip_prefix('_').unwrap_or(sym);
        if LIBC.iter().any(|(n, cap)| *cap == Capability::Spawn && *n == c_name) {
            return true;
        }
        if sym.contains("3std")
            && STD_MANGLED.iter().any(|(k, _, cap)| *cap == Capability::Spawn && sym.contains(k))
        {
            return true;
        }
    }
    false
}

/// One row of the audited third-party table: a crate the policy does not
/// cover whose reference to `symbol` was reviewed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Audited {
    pub krate: String,
    pub version: String,
    pub symbol: String,
    pub why: String,
}

/// Parse `third-party-spawners.tsv`: `crate<TAB>version<TAB>symbol<TAB>why`,
/// `#` comments. A row without a reason is an error.
pub fn parse_audited(tsv: &str) -> Result<Vec<Audited>, String> {
    let mut out = Vec::new();
    for (i, line) in tsv.lines().enumerate() {
        let line = line.trim_end();
        if line.trim().is_empty() || line.trim_start().starts_with('#') {
            continue;
        }
        let mut it = line.split('\t');
        match (it.next(), it.next(), it.next(), it.next(), it.next()) {
            (Some(k), Some(v), Some(s), Some(why), None) if !why.trim().is_empty() => {
                out.push(Audited {
                    krate: k.to_string(),
                    version: v.to_string(),
                    symbol: s.to_string(),
                    why: why.to_string(),
                });
            }
            _ => return Err(format!("line {}: want crate, version, symbol, why", i + 1)),
        }
    }
    Ok(out)
}

/// A crate whose object code references a capable symbol that neither the
/// policy nor the audited table covers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unpoliced {
    pub krate: String,
    pub version: String,
    pub reference: Reference,
}

impl std::fmt::Display for Unpoliced {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "crate `{}` {} references `{}` ({:?}: {}) and is neither under the platform policy \
             nor in third-party-spawners.tsv",
            self.krate,
            self.version,
            self.reference.symbol,
            self.reference.capability,
            self.reference.names
        )
    }
}

/// The rule: every `(crate, version) -> undefined symbols` entry whose
/// capability references are not all covered — the crate under the policy,
/// or each `(crate, version, symbol)` audited — is reported.
#[must_use]
pub fn check(
    crates: &BTreeMap<(String, String), Vec<String>>,
    under_policy: &BTreeSet<String>,
    audited: &[Audited],
) -> Vec<Unpoliced> {
    let mut out = Vec::new();
    for ((krate, version), syms) in crates {
        if under_policy.contains(krate) {
            continue;
        }
        for r in classify(syms) {
            let ok = audited.iter().any(|a| {
                a.krate == *krate
                    && a.version == *version
                    && (a.symbol == r.symbol || a.symbol == r.names)
            });
            if !ok {
                out.push(Unpoliced {
                    krate: krate.clone(),
                    version: version.clone(),
                    reference: r,
                });
            }
        }
    }
    out
}

/// The crates whose object code references a SPAWN-capable symbol (the set
/// the trust-ir census turns into `SiteKind::UpstreamSpawn` sites).
#[must_use]
pub fn spawn_capable(crates: &BTreeMap<(String, String), Vec<String>>) -> BTreeSet<String> {
    crates
        .iter()
        .filter(|(_, syms)| has_spawn_capability(syms))
        .map(|((k, _), _)| k.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(v: &[&str]) -> Vec<String> {
        v.iter().map(|x| (*x).to_string()).collect()
    }

    #[test]
    fn libc_and_mangled_std_references_are_classified() {
        let r = classify(&s(&[
            "_fork",
            "_execv",
            "_dup",
            "_malloc",
            "__ZN3std7process7Command5spawn17h0123456789abcdefE",
            "_RNvMs_NtCs1_3std7processNtB4_7Command6output",
            "libfoo.o:",
        ]));
        let names: Vec<&str> = r.iter().map(|x| x.names.as_str()).collect();
        assert!(names.contains(&"fork") && names.contains(&"execv") && names.contains(&"dup"));
        assert!(names.contains(&"std::process::Command::spawn"));
        assert!(names.contains(&"std::process::Command::output"));
        assert!(!names.contains(&"malloc"));
    }

    #[test]
    fn an_unlisted_spawner_is_reported_and_an_audited_one_is_not() {
        let mut crates = BTreeMap::new();
        crates.insert(("spawner".to_string(), "0.1.0".to_string()), s(&["_fork", "_execv"]));
        crates.insert(("plain".to_string(), "1.0.0".to_string()), s(&["_malloc"]));
        let bad = check(&crates, &BTreeSet::new(), &[]);
        assert_eq!(bad.len(), 2, "{bad:?}");
        let audited = parse_audited(
            "# crate\tversion\tsymbol\twhy\nspawner\t0.1.0\tfork\tthe child execs at once\n\
             spawner\t0.1.0\texecv\tits caller strips first\n",
        )
        .expect("parses");
        assert!(check(&crates, &BTreeSet::new(), &audited).is_empty());
        assert!(parse_audited("spawner\t0.1.0\tfork\t\n").is_err(), "a row needs a reason");
        assert_eq!(spawn_capable(&crates), ["spawner".to_string()].into_iter().collect());
    }
}
