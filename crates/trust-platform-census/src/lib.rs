//! trust-platform-census: the census of design 2026-10-01 Part 2 (PR 7,
//! "C0") — a trust-ir crate module in, one trust-platform-derive
//! [`EventProgram`] per root and a fail-closed site census out.
//!
//! # Pipeline ([`run`])
//!
//! 1. **Identity** ([`CensusContext::callee`]): every assembled function is
//!    a local body, a foreign item, a std / core / alloc function, a local
//!    body the producer refused, an upstream function, or unresolved. The
//!    compiler half (`DeclResolver`, design §2.2) implements the trait in the
//!    host; [`stub::SidecarContext`] implements it for tests from the module
//!    plus a sidecar table, and says which of its answers are name-based.
//! 2. **Sites** ([`sites`]): every call to a spawn-, lock- or
//!    descriptor-number-capable symbol (Critique C-3's wider definition:
//!    named gaps included) and every `pre_exec` registration, with the roots
//!    that reach it on the static call graph (D4 roots; C-4: a body whose
//!    in-IR callers are all refused is itself a root).
//! 3. **Translation** ([`translate`], design §2.3-§2.4): per root, the
//!    scalar CFG of every body on its path — block parameters as variables
//!    with parallel copies, aggregates flattened to per-field variables,
//!    non-escaping `alloca` cells promoted to variables, constant folding,
//!    bounded inlining (`StmtKind::Call`), libc calls bound to
//!    `trust_platform` clauses through `trust_platform::symbols`, a raw
//!    `fork` split into the parent's continuation and a cloned child
//!    continuation (`StmtKind::Fork`), a `pre_exec` closure run in the child
//!    of a harness spawn, untracked values as `Expr::Opaque` and untracked
//!    guards as `Cond::Nondet` (X1), and the `ForRange` recognizer
//!    ([`forrange`]) for descriptor loops in a forked child.
//! 4. **Gates** ([`coverage`]): I-EFFECTS-COVERED (C-16: every HIR call
//!    whose callee is not audited effect-free — local helpers and core
//!    combinators included — is in the body's trust-ir), the drop gate
//!    (C-2, widened: a value on the path whose drop glue may have an
//!    effect — an fd carrier, a `Drop` impl — from typeck's REQUIRED facts
//!    and the module's own Drop impls), I-SITES-COVERED's cross-check
//!    against the host's HIR site census and C-7's product census — merged
//!    into [`CensusOutput::refusals`], site-linked, by [`run`].
//! 5. **Verdicts** ([`verdict`]): a site's verdict is the join over every
//!    root that reaches it (C-4); "not refuted" is admitted only with no
//!    refusal, evidence from EVERY library environment ([`env`]: limits
//!    that do not depend on the host), exhaustive exploration, agreement
//!    between the derivation and ty, and a refuted per-site non-vacuity
//!    check (C-1) — the input of that check is
//!    [`RootProgram::site_program`]. A refutation that takes an
//!    over-approximating choice is `PC-OVERAPPROX` (C-9).
//! 6. **The symbol census** ([`symcensus`], C-3's link-level backstop):
//!    `nm -u` over each crate's objects; a crate referencing a spawn-, lock-
//!    or descriptor-capable symbol is under the policy or audited, and a
//!    call into a spawn-capable upstream crate is a site.
//!
//! Anything the census does not understand is a NAMED refusal
//! ([`refusal::Refusal`], stable `PC-*` codes), never a silent omission, and
//! a site with a refusal can never read "not refuted".
//!
//! # What C0 does not do yet (each is a named refusal today)
//!
//! * `Command` objects (C4): every std `Command::spawn` is
//!   `PC-COMMAND-UNKNOWN`; a `pre_exec` closure is checked in the child of a
//!   harness spawn (premise `P-HOOK-HARNESS`).
//! * `posix_spawn` builder objects (C5): `PC-SPAWN-BUILDER-ESCAPE`.
//! * Out-parameters through memory beyond promoted cells (C3), drops (Step-2
//!   inc 4b: `PC-DROP-ELIDED`), dynamic threads (M2: `PC-THREAD-UNRESOLVED`),
//!   cross-crate fragments (C8: `PC-UPSTREAM`), lock-release and fd-identity
//!   (C6, C7: only `fd-inherit` is supported).
//! * A raw fork's failure and a std row's error path are not explored
//!   (printed premises `P-FORK-SUCCEEDS`, `P-STD-ROW-NOMINAL`); a libc
//!   event explores one representative environment failure.

pub mod audit;
pub mod coverage;
pub mod env;
pub mod forrange;
pub mod refusal;
pub mod rules;
pub mod shape;
pub mod sites;
pub mod stub;
pub mod symcensus;
pub mod translate;
pub mod verdict;

use std::collections::{BTreeMap, BTreeSet};

pub use refusal::Refusal;
use trust_ir::{BlockId, FuncId, Module, SourceSpan};
use trust_platform_derive::program::{EventProgram, Loc, SiteId as ProgSiteId};

/// Identity of an assembled function (design §2.1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Callee {
    /// A local body the producer spliced.
    Body {
        path: String,
        is_local_root_candidate: bool,
        is_pub: bool,
        is_test: bool,
    },
    /// A foreign item; `link_name` is looked up in `trust_platform::symbols`.
    Foreign {
        link_name: String,
        abi: String,
    },
    /// A std function: candidate spellings, tried in order (the item's
    /// path, then the trait method's path for an impl method).
    Std {
        paths: Vec<String>,
    },
    CoreAlloc {
        path: String,
    },
    /// A local def whose body the producer did not splice.
    LocalRefused {
        path: String,
    },
    /// Any other crate.
    Upstream {
        krate: String,
        path: String,
    },
    Unresolved {
        name: String,
        why: String,
    },
}

/// One call the HIR of a body makes (I-EFFECTS-COVERED, Critique C-16), by
/// the span the producer stamps on the call (`line`, 0-based `col` of the
/// callee's name). The host lists EVERY call whose callee is not on the
/// census's audited effect-free lists ([`coverage::effect_free`]): foreign
/// items, std/core/alloc functions, local bodies (spliced or refused) and
/// upstream functions, indirect calls (`<indirect>`) — an erased call to
/// any of them can hide an effect (a local helper's `dup`, a core
/// combinator running a closure). Constructors (`Ok(..)`, `Some(..)`) are
/// not calls.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HirEffect {
    pub line: u32,
    pub col: u32,
    /// The foreign link name, or the callee's path as the census names
    /// functions ([`fn_path`] for a local body, the std/core path, the
    /// upstream path).
    pub callee: String,
}

/// One call site the host's HIR site census sees (design §2.5), for
/// I-SITES-COVERED.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct HirSite {
    /// The enclosing body's path (as the census names functions).
    pub body: String,
    pub line: u32,
    pub col: u32,
    /// The foreign link name or the std path.
    pub callee: String,
}

/// Every compiler fact the census uses enters here (design §2.1).
pub trait CensusContext {
    /// Identity of an assembled function (body or bodyless declaration).
    fn callee(&self, f: FuncId) -> Callee;
    /// The closure body a `pre_exec` / `thread::spawn` declaration instance
    /// receives at this call.
    fn closure_body_of(
        &self,
        decl: FuncId,
        call_span: Option<SourceSpan>,
    ) -> Result<FuncId, String>;
    /// `file:line:col` of a span.
    fn render_span(&self, s: SourceSpan) -> String;
    /// The body's HIR calls (Critique C-16; see [`HirEffect`] for which).
    /// `None`: not available, so I-EFFECTS-COVERED cannot be checked and no
    /// root through this body can be "not refuted".
    fn hir_effects(&self, _f: FuncId) -> Option<Vec<HirEffect>> {
        None
    }
    /// typeck's drop facts of the body (Critique C-2): the types of its
    /// locals, temporaries and by-value parameters that need drop and whose
    /// drop glue is not audited effect-free — a type holding an fd carrier,
    /// or one whose glue runs a `Drop` impl (a user guard, an upstream
    /// type). `Some(vec![])`: typeck found none. `None`: not available, so
    /// the drop gate cannot run and no root through this body can be "not
    /// refuted" (`PC-DROP-ELIDED`). Unioned with the census's own trust-ir
    /// scan ([`coverage::drop_gate`]).
    fn drops(&self, _f: FuncId) -> Option<Vec<String>> {
        None
    }
    /// Parameter indices typeck says are descriptors (`OwnedFd`, `File`,
    /// `RawFd`, a reference to one): RL-INIT places them (`FdParam`).
    fn fd_params(&self, _f: FuncId) -> Vec<usize> {
        Vec::new()
    }
    /// The host's HIR site census of the crate (design §2.5), for
    /// I-SITES-COVERED. `None`: not run, so no site is "not refuted"
    /// (`PC-CENSUS-SKEW` on every site).
    fn hir_sites(&self) -> Option<Vec<HirSite>> {
        None
    }
    /// The HIR site census of the PRODUCT configuration (Critique C-7: no
    /// verification cfg, the binaries' unified features, every shipped
    /// target). `None`: not run — a crate-level `PC-CFG-SKEW` refusal.
    fn product_sites(&self) -> Option<Vec<HirSite>> {
        None
    }
    /// Critique C-3's symbol census ([`symcensus`]): the upstream crates
    /// whose object code references a spawn-, lock- or descriptor-capable
    /// symbol. A call into one of them is a site (`SiteKind::UpstreamSpawn`).
    /// `None`: the symbol census did not run, so EVERY upstream call is
    /// such a site (fail closed).
    fn spawn_capable_crates(&self) -> Option<BTreeSet<String>> {
        None
    }
}

/// A property the census can prepare programs for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Property {
    /// P-FD-INHERIT (the only property C0 translates).
    FdInherit,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusOptions {
    pub properties: Vec<Property>,
    /// Calls deeper than this on a root's path are `PC-SIZE`.
    pub max_inline_depth: usize,
    /// Program bodies per root.
    pub max_bodies: usize,
    /// Program blocks per body.
    pub max_blocks: usize,
}

impl Default for CensusOptions {
    fn default() -> CensusOptions {
        CensusOptions {
            properties: vec![Property::FdInherit],
            max_inline_depth: 16,
            max_bodies: 256,
            max_blocks: 4096,
        }
    }
}

/// A position in the trust-ir module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IrSite {
    pub func: FuncId,
    pub block: BlockId,
    pub inst: usize,
    pub span: Option<SourceSpan>,
}

impl IrSite {
    fn key(&self) -> (FuncId, BlockId, usize, Option<(u32, u32, u32)>) {
        (self.func, self.block, self.inst, self.span.map(|s| (s.file, s.line, s.col)))
    }
}

impl PartialOrd for IrSite {
    fn partial_cmp(&self, other: &IrSite) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for IrSite {
    fn cmp(&self, other: &IrSite) -> std::cmp::Ordering {
        self.key().cmp(&other.key())
    }
}

impl std::fmt::Display for IrSite {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f{}.bb{}#{}", self.func.0, self.block.0, self.inst)
    }
}

/// A census site id (index into [`CensusOutput::sites`]).
pub type SiteId = usize;

/// What a site does.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SiteKind {
    /// A raw `fork(2)`.
    Fork,
    /// An `exec*` (in a forked child it is part of that fork's site).
    Exec,
    /// `posix_spawn` / `posix_spawnp`.
    PosixSpawn,
    /// std `Command::{spawn,output,status}`, `CommandExt::exec`.
    StdSpawn,
    /// `CommandExt::pre_exec` registration (checked in a harness spawn).
    PreExecHook,
    /// A call into an upstream crate that the symbol census (C-3) lists as
    /// spawn-capable (every upstream call when it did not run).
    UpstreamSpawn,
    /// Spawn-capable names the model does not cover (`vfork`, `forkpty`,
    /// `system`, `popen`, `daemon`, `syscall`, `dlsym`, `objc_msgSend`).
    SpawnGap,
    /// `pthread_create`, `thread::spawn`.
    ThreadSpawn,
    /// `flock`, `lockf`, `File::lock*` (and `fcntl` lock commands).
    Lock,
    /// A descriptor-number operation (`fcntl`, `close`, `dup*`, `ioctl`, …).
    FdNumber,
}

impl SiteKind {
    /// Whether the site is checked under fd-inherit. An `exec*` is: in a
    /// forked child its verdict is its fork's (the census maps it to that
    /// fork's program site); in the root process it replaces the image with
    /// every unflagged descriptor inherited, like `CommandExt::exec`.
    #[must_use]
    pub fn under_fd_inherit(self) -> bool {
        matches!(
            self,
            SiteKind::Fork
                | SiteKind::Exec
                | SiteKind::PosixSpawn
                | SiteKind::StdSpawn
                | SiteKind::PreExecHook
                | SiteKind::UpstreamSpawn
                | SiteKind::SpawnGap
                | SiteKind::ThreadSpawn
        )
    }
}

/// One site the census saw in trust-ir.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiteRecord {
    pub id: SiteId,
    pub at: IrSite,
    /// The enclosing function's path.
    pub body: String,
    pub kind: SiteKind,
    /// The callee's link name or std path.
    pub symbol: String,
    /// `file:line:col`.
    pub span_text: String,
    /// Under one of the requested properties.
    pub policy: bool,
}

/// A refusal, with where it applies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiteRefusal {
    /// The root whose program it blocks (every site that root reaches is
    /// then unanalysed through it).
    pub root: Option<FuncId>,
    /// The census site it concerns directly, if any.
    pub site: Option<SiteId>,
    pub at: Option<IrSite>,
    /// A HIR site with no census twin (I-SITES-COVERED's
    /// `PC-SITE-NOT-IN-IR` / `PC-BODY-NOT-LOWERED`, C-7's `PC-CFG-SKEW`):
    /// unanalysed by identity ([`CensusOutput::unanalysed_hir_sites`]).
    pub hir: Option<HirSite>,
    pub refusal: Refusal,
}

/// Why a root is a root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RootKind {
    /// D4: `pub`, a test, a host-declared root candidate, or no caller in
    /// the trust-ir (its callers, if any, were refused by the producer).
    Function { is_pub: bool, is_test: bool, no_ir_callers: bool },
}

/// A premise a root's verdict rests on (printed in every verdict).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CensusPremise {
    pub code: &'static str,
    pub text: String,
    /// Where it was taken.
    pub at: Vec<String>,
}

/// One policy site in a root's program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PolicySite {
    pub site: SiteId,
    pub program_site: ProgSiteId,
}

/// One root: its event program and what maps it back to trust-ir.
#[derive(Clone, Debug)]
pub struct RootProgram {
    pub root: FuncId,
    pub name: String,
    pub kind: RootKind,
    pub program: EventProgram,
    /// `Loc` text -> trust-ir position.
    pub locs: BTreeMap<Loc, IrSite>,
    pub policy_sites: Vec<PolicySite>,
    pub premises: Vec<CensusPremise>,
    /// Every trust-ir body on the root's path (callees and hooks included).
    pub bodies: BTreeSet<FuncId>,
    /// Over-approximations and untracked values, in words.
    pub notes: Vec<String>,
}

impl RootProgram {
    /// The program with only `program_site` under the policy: the input of
    /// the per-site non-vacuity check (Critique C-1 — `policy_exec` then
    /// means "a child of THIS site exec'd") and of a per-site refutation.
    #[must_use]
    pub fn site_program(&self, program_site: ProgSiteId) -> EventProgram {
        let mut p = self.program.clone();
        for (i, s) in p.sites.iter_mut().enumerate() {
            if i != program_site {
                s.policy = None;
            }
        }
        p.name = format!("{}__site{}", p.name, program_site);
        p
    }
}

/// Counts for reports.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CensusStats {
    pub functions: usize,
    pub bodies: usize,
    pub root_candidates: usize,
    pub roots_translated: usize,
    pub roots_refused: usize,
    pub sites: usize,
    pub policy_sites: usize,
    pub refusals_by_code: BTreeMap<&'static str, usize>,
}

/// The census of one module.
#[derive(Clone, Debug)]
pub struct CensusOutput {
    /// Roots whose program was translated with no refusal.
    pub roots: Vec<RootProgram>,
    pub sites: Vec<SiteRecord>,
    pub refusals: Vec<SiteRefusal>,
    /// Every root candidate and the sites it reaches on the static call
    /// graph, translated or not.
    pub root_reach: BTreeMap<FuncId, BTreeSet<SiteId>>,
    pub stats: CensusStats,
}

/// What the host must do for one site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiteGate {
    /// The site is unanalysed; these are the reasons.
    Unanalysed(Vec<Refusal>),
    /// Check these (root index into [`CensusOutput::roots`], program site)
    /// pairs; the verdict is their join ([`verdict::site_verdict`]).
    Check(Vec<(usize, ProgSiteId)>),
}

impl CensusOutput {
    /// The roots that reach `site` on the static call graph.
    #[must_use]
    pub fn roots_reaching(&self, site: SiteId) -> Vec<FuncId> {
        self.root_reach.iter().filter(|(_, s)| s.contains(&site)).map(|(r, _)| *r).collect()
    }

    /// Every refusal that bears on `site`: its own, and every refusal of a
    /// root that reaches it.
    #[must_use]
    pub fn refusals_for(&self, site: SiteId) -> Vec<Refusal> {
        let roots = self.roots_reaching(site);
        let mut out: Vec<Refusal> = self
            .refusals
            .iter()
            .filter(|r| r.site == Some(site) || r.root.is_some_and(|x| roots.contains(&x)))
            .map(|r| r.refusal.clone())
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// What the host must do for `site` (fail closed: any refusal, or no
    /// root, is unanalysed).
    #[must_use]
    pub fn gate(&self, site: SiteId) -> SiteGate {
        let mut refusals = self.refusals_for(site);
        let roots = self.roots_reaching(site);
        if roots.is_empty() {
            refusals.push(Refusal::NoRoot);
        }
        if !refusals.is_empty() {
            return SiteGate::Unanalysed(refusals);
        }
        let mut checks = Vec::new();
        for r in roots {
            let Some(i) = self.roots.iter().position(|p| p.root == r) else {
                return SiteGate::Unanalysed(vec![Refusal::Internal {
                    detail: format!("root f{} reaches site {site} but has no program", r.0),
                }]);
            };
            let ps: Vec<_> = self.roots[i].policy_sites.iter().filter(|p| p.site == site).collect();
            if ps.is_empty() {
                // Reached on the static call graph, not in the translated
                // program (a pruned constant branch): no program site to
                // check through this root.
                continue;
            }
            for p in ps {
                checks.push((i, p.program_site));
            }
        }
        if checks.is_empty() {
            return SiteGate::Unanalysed(vec![Refusal::NoRoot]);
        }
        SiteGate::Check(checks)
    }

    /// The root program for `f`.
    #[must_use]
    pub fn root(&self, f: FuncId) -> Option<&RootProgram> {
        self.roots.iter().find(|r| r.root == f)
    }

    /// The refusals recorded against root `f`.
    #[must_use]
    pub fn root_refusals(&self, f: FuncId) -> Vec<&Refusal> {
        self.refusals.iter().filter(|r| r.root == Some(f)).map(|r| &r.refusal).collect()
    }

    /// Sites whose body is `body` (by path).
    #[must_use]
    pub fn sites_in(&self, body: &str) -> Vec<&SiteRecord> {
        self.sites.iter().filter(|s| s.body == body).collect()
    }

    /// HIR sites with no census twin, with why each is unanalysed (a site
    /// the producer refused or erased, a shipped site the checked build does
    /// not have). Each is an unanalysed site of the crate by identity.
    #[must_use]
    pub fn unanalysed_hir_sites(&self) -> Vec<(&HirSite, &Refusal)> {
        self.refusals.iter().filter_map(|r| r.hir.as_ref().map(|h| (h, &r.refusal))).collect()
    }

    /// Refusals that concern the crate, not one site or root (a census that
    /// did not run, such as C-7's product-configuration census).
    #[must_use]
    pub fn crate_refusals(&self) -> Vec<&Refusal> {
        self.refusals
            .iter()
            .filter(|r| r.root.is_none() && r.site.is_none() && r.hir.is_none())
            .map(|r| &r.refusal)
            .collect()
    }
}

/// The function's path as the census names it (its display path, else its
/// symbol).
#[must_use]
pub fn fn_path(m: &Module, f: FuncId) -> String {
    m.functions
        .get(f.as_usize())
        .map(|func| func.display_path.clone().unwrap_or_else(|| func.name.clone()))
        .unwrap_or_else(|| format!("func.{}", f.0))
}

/// Run the census over `m`: identities, sites, per-root translation and
/// gates, and the crate-level cross-checks (I-SITES-COVERED against the
/// host's HIR site census, C-7's product census) — every refusal lands in
/// [`CensusOutput::refusals`], linked to its site, root or HIR identity, so
/// [`CensusOutput::gate`] and [`verdict::site_verdict`] see all of them.
#[must_use]
pub fn run(m: &Module, cx: &dyn CensusContext, o: &CensusOptions) -> CensusOutput {
    let callees: Vec<Callee> =
        (0..m.functions.len()).map(|i| cx.callee(FuncId::new(i as u32))).collect();
    let spawners = cx.spawn_capable_crates();
    let scan = sites::scan(m, cx, &callees, o, spawners.as_ref());
    let mut refusals = scan.refusals.clone();
    let mut roots = Vec::new();
    let mut stats = CensusStats {
        functions: m.functions.len(),
        bodies: m.functions.iter().filter(|f| !f.blocks.is_empty()).count(),
        root_candidates: scan.root_reach.len(),
        sites: scan.sites.len(),
        policy_sites: scan.sites.iter().filter(|s| s.policy).count(),
        ..CensusStats::default()
    };
    for (root, kind) in &scan.roots {
        match translate::translate_root(m, cx, o, &callees, &scan, *root, kind.clone()) {
            Ok(mut rp) => {
                let mut gate = coverage::root_gates(m, cx, &callees, &rp);
                if gate.is_empty() {
                    gate = translate::derive_precheck(&rp);
                }
                if gate.is_empty() {
                    rp.premises.sort();
                    rp.premises.dedup();
                    roots.push(rp);
                    stats.roots_translated += 1;
                } else {
                    stats.roots_refused += 1;
                    for (at, r) in gate {
                        refusals.push(SiteRefusal {
                            root: Some(*root),
                            site: at.and_then(|a| scan.site_at(a)),
                            at,
                            hir: None,
                            refusal: r,
                        });
                    }
                }
            }
            Err(rs) => {
                stats.roots_refused += 1;
                for (at, r) in rs {
                    refusals.push(SiteRefusal {
                        root: Some(*root),
                        site: at.and_then(|a| scan.site_at(a)),
                        at,
                        hir: None,
                        refusal: r,
                    });
                }
            }
        }
    }
    let mut out =
        CensusOutput { roots, sites: scan.sites, refusals, root_reach: scan.root_reach, stats };
    // I-SITES-COVERED (§2.5, C-4) and C-7, merged: a refusal returned on the
    // side would never reach a verdict.
    let hir = cx.hir_sites();
    let crosscheck = match &hir {
        Some(h) => coverage::sites_covered(m, &out, h),
        None => out
            .sites
            .iter()
            .map(|s| SiteRefusal {
                root: None,
                site: Some(s.id),
                at: Some(s.at),
                hir: None,
                refusal: Refusal::CensusSkew {
                    detail: "the host gave no HIR site census: I-SITES-COVERED could not be \
                             checked"
                        .into(),
                },
            })
            .collect(),
    };
    out.refusals.extend(crosscheck);
    match (&hir, cx.product_sites()) {
        (Some(checked), Some(product)) => {
            out.refusals.extend(coverage::cfg_skew(checked, &product));
        }
        (_, product) => out.refusals.push(SiteRefusal {
            root: None,
            site: None,
            at: None,
            hir: None,
            refusal: Refusal::CfgSkew {
                detail: if product.is_none() {
                    "the product configuration (no verification cfg, the binaries' unified \
                     features, every shipped target) was not censused: shipped sites the \
                     checked build lacks are unknown (C-7)"
                        .into()
                } else {
                    "no HIR site census of the checked build to compare the product census with"
                        .into()
                },
            },
        }),
    }
    for r in &out.refusals {
        *out.stats.refusals_by_code.entry(r.refusal.code()).or_default() += 1;
    }
    out
}
