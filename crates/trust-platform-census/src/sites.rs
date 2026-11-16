//! The static scan: every site in the module's trust-ir (Critique C-3's
//! wide definition — any call to a spawn-, lock- or descriptor-number-
//! capable name, the named gaps included), the direct call graph, the
//! `pre_exec` closure edges, the roots (D4, C-4) and what each reaches.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{BlockId, Constant, FuncId, Inst, Module};

use crate::{
    Callee, CensusContext, CensusOptions, IrSite, Property, RootKind, SiteId, SiteKind, SiteRecord,
    SiteRefusal, fn_path,
};

/// Foreign names that create a process or replace an image, beyond the
/// modeled clauses (C-3: each is a site, refused until modeled).
const SPAWN_GAPS: &[&str] =
    &["vfork", "forkpty", "system", "popen", "daemon", "syscall", "dlsym", "objc_msgSend"];
const EXEC_NAMES: &[&str] = &["execve", "execv", "execvp", "execvP", "execl", "execlp", "execle"];
const LOCK_NAMES: &[&str] = &["flock", "lockf"];
const FD_NUMBER_NAMES: &[&str] = &[
    "fcntl",
    "close",
    "dup",
    "dup2",
    "ioctl",
    "fstat",
    "kevent",
    "select",
    "poll",
    "posix_spawn_file_actions_adddup2",
    "posix_spawn_file_actions_addclose",
    "posix_spawn_file_actions_addinherit_np",
];

/// Remove generic arguments from a Rust path (`Vec::<T>::new` -> `Vec::new`),
/// borrowing `path` when no generic arguments or redundant colons are present.
#[must_use]
pub fn strip_generics_cow(path: &str) -> std::borrow::Cow<'_, str> {
    let trimmed = path.trim_end_matches("::");
    if !trimmed.contains(['<', '>']) && !trimmed.contains("::::") {
        return std::borrow::Cow::Borrowed(trimmed);
    }
    let mut out = String::with_capacity(trimmed.len());
    let mut depth = 0usize;
    for c in trimmed.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }
    if out.contains("::::") {
        out = out.replace("::::", "::");
    }
    let new_len = out.trim_end_matches("::").len();
    out.truncate(new_len);
    std::borrow::Cow::Owned(out)
}

/// Remove generic arguments from a Rust path (`Vec::<T>::new` -> `Vec::new`).
#[must_use]
pub fn strip_generics(path: &str) -> String {
    strip_generics_cow(path).into_owned()
}

/// Whether a std callee's candidate paths name `want` (generics removed).
#[must_use]
pub fn std_is(paths: &[String], want: &str) -> bool {
    paths.iter().any(|p| p == want || strip_generics_cow(p) == want)
}

/// The std path among `paths` that starts with `prefix`, generics removed.
#[must_use]
pub fn std_under(paths: &[String], prefix: &str) -> Option<String> {
    paths
        .iter()
        .map(|p| strip_generics_cow(p))
        .find(|p| p.starts_with(prefix))
        .map(std::borrow::Cow::into_owned)
}

/// The kind of site a call to `callee` is, with the symbol it is filed
/// under. `spawners` is the symbol census's set of spawn-capable upstream
/// crates (C-3); `None` (it did not run) makes every upstream call a site.
#[must_use]
pub fn site_kind(
    callee: &Callee,
    spawners: Option<&BTreeSet<String>>,
) -> Option<(SiteKind, String)> {
    match callee {
        Callee::Upstream { krate, path } => spawners
            .is_none_or(|set| set.contains(krate))
            .then(|| (SiteKind::UpstreamSpawn, path.clone())),
        Callee::Foreign { link_name, .. } => {
            let n = link_name.as_str();
            let kind = if n == "fork" {
                SiteKind::Fork
            } else if n == "posix_spawn" || n == "posix_spawnp" {
                SiteKind::PosixSpawn
            } else if SPAWN_GAPS.contains(&n) {
                SiteKind::SpawnGap
            } else if EXEC_NAMES.contains(&n) {
                SiteKind::Exec
            } else if n == "pthread_create" {
                SiteKind::ThreadSpawn
            } else if LOCK_NAMES.contains(&n) {
                SiteKind::Lock
            } else if FD_NUMBER_NAMES.contains(&n) {
                SiteKind::FdNumber
            } else {
                return None;
            };
            Some((kind, link_name.clone()))
        }
        Callee::Std { paths } => {
            let stripped: Vec<_> = paths.iter().map(|p| strip_generics_cow(p)).collect();
            for (want, kind) in [
                ("std::process::Command::spawn", SiteKind::StdSpawn),
                ("std::process::Command::output", SiteKind::StdSpawn),
                ("std::process::Command::status", SiteKind::StdSpawn),
                ("std::os::unix::process::CommandExt::exec", SiteKind::StdSpawn),
                ("std::os::unix::process::CommandExt::pre_exec", SiteKind::PreExecHook),
                ("std::os::unix::process::CommandExt::before_exec", SiteKind::PreExecHook),
                ("std::thread::spawn", SiteKind::ThreadSpawn),
                ("std::thread::Builder::spawn", SiteKind::ThreadSpawn),
                ("std::thread::scope", SiteKind::ThreadSpawn),
                ("std::fs::File::lock", SiteKind::Lock),
                ("std::fs::File::try_lock", SiteKind::Lock),
                ("std::fs::File::lock_shared", SiteKind::Lock),
                ("std::fs::File::try_lock_shared", SiteKind::Lock),
            ] {
                if stripped.iter().any(|p| p == want) {
                    return Some((kind, want.to_string()));
                }
            }
            None
        }
        _ => None,
    }
}

/// Whether a site kind is under one of the requested properties.
#[must_use]
pub fn is_policy(kind: SiteKind, o: &CensusOptions) -> bool {
    o.properties.iter().any(|p| match p {
        Property::FdInherit => kind.under_fd_inherit(),
    })
}

/// The scan of a module.
#[derive(Clone, Debug, Default)]
pub struct Scan {
    pub sites: Vec<SiteRecord>,
    pub by_at: BTreeMap<(FuncId, BlockId, usize), SiteId>,
    /// caller -> spliced local callees and bound `pre_exec` closures.
    pub calls: BTreeMap<FuncId, BTreeSet<FuncId>>,
    /// callee -> callers (direct calls between spliced bodies only).
    pub callers: BTreeMap<FuncId, BTreeSet<FuncId>>,
    /// `pre_exec` registrations: the closure each binds, or why not.
    pub hooks: BTreeMap<(FuncId, BlockId, usize), Result<FuncId, String>>,
    pub hook_closures: BTreeSet<FuncId>,
    /// Local bodies used as values (fn pointers): callable from anywhere.
    pub value_refs: BTreeSet<FuncId>,
    pub roots: Vec<(FuncId, RootKind)>,
    pub root_reach: BTreeMap<FuncId, BTreeSet<SiteId>>,
    pub refusals: Vec<SiteRefusal>,
}

impl Scan {
    /// The census site at a trust-ir position.
    #[must_use]
    pub fn site_at(&self, a: IrSite) -> Option<SiteId> {
        self.by_at.get(&(a.func, a.block, a.inst)).copied()
    }

    /// Every function reachable from `f` (itself included).
    #[must_use]
    pub fn reachable(&self, f: FuncId) -> BTreeSet<FuncId> {
        let mut seen = BTreeSet::new();
        let mut stack = vec![f];
        while let Some(g) = stack.pop() {
            if seen.insert(g)
                && let Some(cs) = self.calls.get(&g)
            {
                stack.extend(cs.iter().copied());
            }
        }
        seen
    }
}

/// Scan `m`.
#[must_use]
pub fn scan(
    m: &Module,
    cx: &dyn CensusContext,
    callees: &[Callee],
    o: &CensusOptions,
    spawners: Option<&BTreeSet<String>>,
) -> Scan {
    let mut s = Scan::default();
    for (fi, func) in m.functions.iter().enumerate() {
        if func.blocks.is_empty() {
            continue;
        }
        let f = FuncId::new(fi as u32);
        let body = fn_path(m, f);
        for block in &func.blocks {
            for (ii, node) in block.body.iter().enumerate() {
                // C-3: a site is any REFERENCE to a capable symbol — a call,
                // or a function used as a value (an fn pointer).
                let (callee, by_value) = match &node.inst {
                    Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => (*callee, false),
                    Inst::Const { value: Constant::FnDef(g), .. } => (*g, true),
                    _ => continue,
                };
                let Some(c) = callees.get(callee.as_usize()) else { continue };
                if let Callee::Body { .. } = c {
                    if by_value {
                        s.value_refs.insert(callee);
                    } else {
                        s.calls.entry(f).or_default().insert(callee);
                        s.callers.entry(callee).or_default().insert(f);
                    }
                }
                let Some((kind, symbol)) = site_kind(c, spawners) else { continue };
                let at = IrSite { func: f, block: block.id, inst: ii, span: node.span };
                if kind == SiteKind::PreExecHook {
                    let bound = cx.closure_body_of(callee, node.span);
                    if let Ok(cl) = &bound {
                        s.calls.entry(f).or_default().insert(*cl);
                        s.hook_closures.insert(*cl);
                    }
                    s.hooks.insert((f, block.id, ii), bound);
                }
                let id = s.sites.len();
                s.sites.push(SiteRecord {
                    id,
                    at,
                    body: body.clone(),
                    kind,
                    symbol,
                    span_text: node.span.map(|sp| cx.render_span(sp)).unwrap_or_default(),
                    policy: is_policy(kind, o),
                });
                s.by_at.insert((f, block.id, ii), id);
            }
        }
    }
    // Roots (D4; C-4: a body whose in-IR callers are all refused has no
    // in-IR caller, so it is a root).
    for (fi, func) in m.functions.iter().enumerate() {
        if func.blocks.is_empty() {
            continue;
        }
        let f = FuncId::new(fi as u32);
        let Some(Callee::Body { is_local_root_candidate, is_pub, is_test, .. }) = callees.get(fi)
        else {
            continue;
        };
        if s.hook_closures.contains(&f) {
            continue;
        }
        let no_ir_callers = s.callers.get(&f).is_none_or(BTreeSet::is_empty);
        let candidate = *is_local_root_candidate || s.value_refs.contains(&f);
        if !(*is_pub || *is_test || candidate || no_ir_callers) {
            continue;
        }
        let reach: BTreeSet<SiteId> = s
            .reachable(f)
            .into_iter()
            .flat_map(|g| {
                s.by_at
                    .range((g, BlockId::new(0), 0)..=(g, BlockId::new(u32::MAX), usize::MAX))
                    .map(|(_, &id)| id)
            })
            .collect();
        if !reach.iter().any(|id| s.sites[*id].policy) {
            continue;
        }
        s.root_reach.insert(f, reach);
        s.roots.push((f, RootKind::Function { is_pub: *is_pub, is_test: *is_test, no_ir_callers }));
    }
    s
}
