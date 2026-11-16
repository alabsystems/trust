//! A [`CensusContext`] without the compiler: identities from the trust-ir
//! module's own names, overridden and completed by a sidecar table.
//!
//! This is the test half of design §2.2's resolver. The compiler half
//! (`DeclResolver`: hashed bodyless instances decoded to `DefPathHash`es,
//! the `def_path_str` reverse index, foreign-item classification by
//! `tcx.is_foreign_item`) comes with the host (PR 9/12). What the module
//! alone can say, and what it cannot:
//!
//! * a function with blocks is a spliced local body — but whether it is
//!   `pub` or a test is not in trust-ir: the sidecar says (`body … pub`);
//! * a bodyless declaration named `std::…`/`core::…`/`alloc::…` (or a
//!   qualified `<… as …>::…` path, or a hashed
//!   `!trust_bodyless_instance::<path>::<hash>` instance) is std/core/alloc,
//!   with the trait method's path and an inherent `<impl T>` method's
//!   `T::method` as further candidates;
//! * a bodyless C-ABI declaration `krate::name` is the foreign item `name`
//!   — a NAME-BASED guess (a Rust `const fn` of the `libc` crate also has
//!   that spelling; the sidecar corrects it with `upstream`);
//! * any other bodyless declaration is unresolved (a refused local body and
//!   a local foreign item look alike: the producer mints both `rustcc`,
//!   increment S2): the sidecar must say `refused` or `foreign`;
//! * a `pre_exec` instance's closure argument is a `DefPathHash` inside the
//!   instance's hex suffix: only the sidecar's `closure` rows bind it;
//! * HIR effect lists, typeck drop facts, the HIR site census (derived from
//!   the `effects` rows — one HIR walk gives both — plus `site` rows for
//!   bodies the module does not carry), the product census and the symbol
//!   census exist only in the sidecar.
//!
//! # Sidecar syntax (one row per line, `#` comments)
//!
//! A function is `func.N` or its name (quoted when it has spaces).
//!
//! ```text
//! body <fn> [pub] [test] [root]
//! foreign <fn> <link_name>
//! std <fn> <path>...
//! core <fn> <path>
//! refused <fn>
//! upstream <fn> <krate>
//! unresolved <fn> <why>...
//! closure <pre_exec decl fn> <closure body fn>
//! effects <fn> [<line>:<col>=<callee>]...     every HIR call (not audited effect-free)
//! drops <fn> [<type>]...                      typeck's facts (an empty row: none)
//! fd-params <fn> <index>...
//! site <body path> [<line>:<col>=<callee>]... HIR sites of a body not in the module
//! product-census                              the product census ran: the checked sites,
//! product-site <body path> [<line>:<col>=<callee>]...   plus these shipped ones
//! spawners [<crate>]...                       the symbol census ran: these crates spawn
//! ```

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{CallingConv, FuncId, Module, SourceSpan};

use crate::sites::strip_generics;
use crate::{Callee, CensusContext, HirEffect, HirSite, fn_path};

/// The test context: the module plus a sidecar.
pub struct SidecarContext<'m> {
    m: &'m Module,
    rows: BTreeMap<FuncId, Callee>,
    closures: BTreeMap<FuncId, FuncId>,
    effects: BTreeMap<FuncId, Vec<HirEffect>>,
    drops: BTreeMap<FuncId, Vec<String>>,
    fd_params: BTreeMap<FuncId, Vec<usize>>,
    /// `site` rows: HIR sites of bodies the module does not carry.
    extra_sites: Vec<HirSite>,
    /// `product-census` / `product-site` rows.
    product: Option<Vec<HirSite>>,
    /// `spawners` row.
    spawners: Option<BTreeSet<String>>,
}

/// `<line>:<col>=<callee>` entries of a row.
fn positions(rest: &[String]) -> Result<Vec<(u32, u32, String)>, String> {
    let mut v = Vec::new();
    for e in rest {
        let (pos, callee) = e.split_once('=').ok_or_else(|| format!("bad entry `{e}`"))?;
        let (l, c) = pos.split_once(':').ok_or_else(|| format!("bad position `{pos}`"))?;
        v.push((
            l.parse().map_err(|_| format!("bad line `{l}`"))?,
            c.parse().map_err(|_| format!("bad column `{c}`"))?,
            callee.to_string(),
        ));
    }
    Ok(v)
}

fn tokens(line: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut quoted = false;
    let mut had = false;
    for c in line.chars() {
        match c {
            '"' => {
                quoted = !quoted;
                had = true;
            }
            c if c.is_whitespace() && !quoted => {
                if had || !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
                had = false;
            }
            c => cur.push(c),
        }
    }
    if had || !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// The line up to a `#` outside double quotes (a closure's name contains
/// `#`: `install::{closure#0}`).
fn strip_comment(line: &str) -> &str {
    let mut quoted = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => quoted = !quoted,
            '#' if !quoted => return &line[..i],
            _ => {}
        }
    }
    line
}

/// The std/core/alloc crate a path belongs to, if any.
fn std_crate(path: &str) -> Option<&'static str> {
    let p = path.trim_start_matches('<');
    for k in ["std", "core", "alloc"] {
        if p.starts_with(&format!("{k}::")) {
            return Some(k);
        }
    }
    None
}

/// Candidate spellings of a std path: itself, a qualified path's trait
/// method (`<A as B>::m` -> `B::m`), an inherent impl's `T::m`
/// (`m::<impl T>::f` -> `T::f`).
#[must_use]
pub fn std_candidates(path: &str) -> Vec<String> {
    let mut out = vec![path.to_string()];
    if let Some(rest) = path.strip_prefix('<')
        && let Some(close) = rest.rfind(">::")
    {
        let inner = &rest[..close];
        let method = &rest[close + 3..];
        if let Some(pos) = inner.find(" as ") {
            let tr = strip_generics(&inner[pos + 4..]);
            out.push(format!("{tr}::{method}"));
        }
    }
    if let Some(start) = path.find("<impl ")
        && let Some(end) = path[start..].find(">::")
    {
        let ty = &path[start + 6..start + end];
        let method = &path[start + end + 3..];
        out.push(format!("{}::{method}", strip_generics(ty)));
    }
    let mut seen = Vec::new();
    for c in out {
        if !seen.contains(&c) {
            seen.push(c);
        }
    }
    seen
}

/// The path a hashed bodyless instance names.
#[must_use]
pub fn instance_path(name: &str) -> Option<String> {
    let rest = name.strip_prefix("!trust_bodyless_instance::")?;
    let cut = rest.rfind("::")?;
    Some(rest[..cut].to_string())
}

impl<'m> SidecarContext<'m> {
    /// Name-only identities, no sidecar rows.
    #[must_use]
    pub fn new(m: &'m Module) -> SidecarContext<'m> {
        SidecarContext {
            m,
            rows: BTreeMap::new(),
            closures: BTreeMap::new(),
            effects: BTreeMap::new(),
            drops: BTreeMap::new(),
            fd_params: BTreeMap::new(),
            extra_sites: Vec::new(),
            product: None,
            spawners: None,
        }
    }

    /// The function a sidecar token names.
    pub fn func(&self, tok: &str) -> Result<FuncId, String> {
        if let Some(n) = tok.strip_prefix("func.")
            && let Ok(i) = n.parse::<u32>()
            && (i as usize) < self.m.functions.len()
        {
            return Ok(FuncId::new(i));
        }
        let hits: Vec<usize> = self
            .m
            .functions
            .iter()
            .enumerate()
            .filter(|(_, f)| f.name == tok || f.display_path.as_deref() == Some(tok))
            .map(|(i, _)| i)
            .collect();
        match hits.as_slice() {
            [i] => Ok(FuncId::new(*i as u32)),
            [] => Err(format!("no function `{tok}`")),
            _ => Err(format!("`{tok}` names {} functions: use func.N", hits.len())),
        }
    }

    /// Name-only identities plus the sidecar's rows.
    pub fn parse(m: &'m Module, sidecar: &str) -> Result<SidecarContext<'m>, String> {
        let mut cx = SidecarContext::new(m);
        for (ln, line) in sidecar.lines().enumerate() {
            let line = strip_comment(line).trim();
            if line.is_empty() {
                continue;
            }
            let t = tokens(line);
            let err = |e: String| format!("sidecar line {}: {e}", ln + 1);
            // Rows that name no module function.
            match t[0].as_str() {
                "site" | "product-site" => {
                    let body = t.get(1).ok_or_else(|| err("no body".into()))?.clone();
                    let rest: Vec<String> = t.iter().skip(2).cloned().collect();
                    let sites: Vec<HirSite> = positions(&rest)
                        .map_err(err)?
                        .into_iter()
                        .map(|(line, col, callee)| HirSite {
                            body: body.clone(),
                            line,
                            col,
                            callee,
                        })
                        .collect();
                    if t[0] == "site" {
                        cx.extra_sites.extend(sites);
                    } else {
                        cx.product.get_or_insert_with(Vec::new).extend(sites);
                    }
                    continue;
                }
                "product-census" => {
                    cx.product.get_or_insert_with(Vec::new);
                    continue;
                }
                "spawners" => {
                    cx.spawners.get_or_insert_with(BTreeSet::new).extend(t.iter().skip(1).cloned());
                    continue;
                }
                _ => {}
            }
            let f = cx.func(t.get(1).ok_or_else(|| err("no function".into()))?).map_err(err)?;
            let path = fn_path(m, f);
            let rest: Vec<String> = t.iter().skip(2).cloned().collect();
            match t[0].as_str() {
                "body" => {
                    let has = |w: &str| rest.iter().any(|x| x == w);
                    cx.rows.insert(
                        f,
                        Callee::Body {
                            path,
                            is_pub: has("pub"),
                            is_test: has("test"),
                            is_local_root_candidate: has("root"),
                        },
                    );
                }
                "foreign" => {
                    let link = rest.first().ok_or_else(|| err("no link name".into()))?.clone();
                    cx.rows.insert(f, Callee::Foreign { link_name: link, abi: "C".into() });
                }
                "std" => {
                    cx.rows.insert(f, Callee::Std { paths: rest });
                }
                "core" => {
                    let p = rest.first().cloned().unwrap_or(path);
                    cx.rows.insert(f, Callee::CoreAlloc { path: p });
                }
                "refused" => {
                    cx.rows.insert(f, Callee::LocalRefused { path });
                }
                "upstream" => {
                    let k = rest.first().cloned().unwrap_or_default();
                    cx.rows.insert(f, Callee::Upstream { krate: k, path });
                }
                "unresolved" => {
                    cx.rows.insert(f, Callee::Unresolved { name: path, why: rest.join(" ") });
                }
                "closure" => {
                    let c = cx
                        .func(rest.first().ok_or_else(|| err("no closure".into()))?)
                        .map_err(err)?;
                    cx.closures.insert(f, c);
                }
                "effects" => {
                    let v = positions(&rest)
                        .map_err(err)?
                        .into_iter()
                        .map(|(line, col, callee)| HirEffect { line, col, callee })
                        .collect();
                    cx.effects.insert(f, v);
                }
                "drops" => {
                    cx.drops.insert(f, rest);
                }
                "fd-params" => {
                    let v: Result<Vec<usize>, _> = rest.iter().map(|x| x.parse()).collect();
                    cx.fd_params.insert(f, v.map_err(|_| err("bad index".into()))?);
                }
                other => return Err(err(format!("unknown row `{other}`"))),
            }
        }
        Ok(cx)
    }

    /// What the module's own names say about `f`.
    #[must_use]
    pub fn name_only(&self, f: FuncId) -> Callee {
        let Some(func) = self.m.functions.get(f.as_usize()) else {
            return Callee::Unresolved {
                name: format!("func.{}", f.0),
                why: "no such function".into(),
            };
        };
        let path = fn_path(self.m, f);
        if !func.blocks.is_empty() {
            return Callee::Body {
                path,
                is_local_root_candidate: false,
                is_pub: false,
                is_test: false,
            };
        }
        let p = instance_path(&path).unwrap_or_else(|| path.clone());
        match std_crate(&p) {
            Some("std") => return Callee::Std { paths: std_candidates(&p) },
            Some(_) => {
                // A core/alloc impl of a std-facing trait or type keeps its
                // std spellings as candidates too (`alloc::io::…` is std's
                // io::Error).
                let c = std_candidates(&p);
                if c.iter().any(|x| x.starts_with("std::")) {
                    return Callee::Std { paths: c };
                }
                return Callee::CoreAlloc { path: p };
            }
            None => {}
        }
        if func.calling_conv == CallingConv::C
            && let Some((_, last)) = p.rsplit_once("::")
        {
            return Callee::Foreign { link_name: last.to_string(), abi: "C".into() };
        }
        Callee::Unresolved {
            name: path,
            why: "a bodyless declaration the name-only resolver cannot classify (a refused local \
                  body, a local foreign item minted rustcc, or an upstream function): the \
                  compiler resolver decides"
                .into(),
        }
    }
}

impl CensusContext for SidecarContext<'_> {
    fn callee(&self, f: FuncId) -> Callee {
        self.rows.get(&f).cloned().unwrap_or_else(|| self.name_only(f))
    }

    fn closure_body_of(
        &self,
        decl: FuncId,
        _call_span: Option<SourceSpan>,
    ) -> Result<FuncId, String> {
        self.closures.get(&decl).copied().ok_or_else(|| {
            let name = fn_path(self.m, decl);
            format!(
                "the closure argument of `{}` (func.{}) is not bound: the name-only resolver \
                 cannot decode the instance's DefPathHash (design §2.2, resolver source 1)",
                instance_path(&name).unwrap_or(name),
                decl.0
            )
        })
    }

    fn render_span(&self, s: SourceSpan) -> String {
        let file = self.m.files.get(s.file as usize).map_or("?", String::as_str);
        format!("{file}:{}:{}", s.line, s.col)
    }

    fn hir_effects(&self, f: FuncId) -> Option<Vec<HirEffect>> {
        self.effects.get(&f).cloned()
    }

    fn drops(&self, f: FuncId) -> Option<Vec<String>> {
        self.drops.get(&f).cloned()
    }

    fn fd_params(&self, f: FuncId) -> Vec<usize> {
        self.fd_params.get(&f).cloned().unwrap_or_default()
    }

    /// The HIR sites one walk with the `effects` rows gives: each effect
    /// whose callee is a site kind (classified as the module's function of
    /// that name is, else by spelling), plus the `site` rows. `None` when
    /// the sidecar has neither.
    fn hir_sites(&self) -> Option<Vec<HirSite>> {
        if self.effects.is_empty() && self.extra_sites.is_empty() {
            return None;
        }
        let spawners = self.spawners.clone();
        let mut out = self.extra_sites.clone();
        for (f, effects) in &self.effects {
            let body = fn_path(self.m, *f);
            for e in effects {
                let callee = self.classify_name(&e.callee);
                if let Some((_, symbol)) = crate::sites::site_kind(&callee, spawners.as_ref()) {
                    out.push(HirSite {
                        body: body.clone(),
                        line: e.line,
                        col: e.col,
                        callee: symbol,
                    });
                }
            }
        }
        Some(out)
    }

    fn product_sites(&self) -> Option<Vec<HirSite>> {
        let extra = self.product.clone()?;
        let mut out = self.hir_sites().unwrap_or_default();
        out.extend(extra);
        Some(out)
    }

    fn spawn_capable_crates(&self) -> Option<BTreeSet<String>> {
        self.spawners.clone()
    }
}

impl SidecarContext<'_> {
    /// The identity of a HIR callee name: the module's function that
    /// carries it (by link name or path), else a guess from its spelling.
    fn classify_name(&self, name: &str) -> Callee {
        for (i, _) in self.m.functions.iter().enumerate() {
            let f = FuncId::new(i as u32);
            let c = self.callee(f);
            let hit = match &c {
                Callee::Foreign { link_name, .. } => link_name == name,
                Callee::Std { paths } => {
                    paths.iter().any(|p| p == name || strip_generics(p) == strip_generics(name))
                }
                Callee::Body { path, .. }
                | Callee::CoreAlloc { path }
                | Callee::LocalRefused { path }
                | Callee::Upstream { path, .. } => path == name,
                Callee::Unresolved { .. } => false,
            };
            if hit {
                return c;
            }
        }
        if name.contains("::") {
            Callee::Std { paths: std_candidates(name) }
        } else {
            Callee::Foreign { link_name: name.to_string(), abi: "C".into() }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokens_keep_quoted_names_whole() {
        assert_eq!(
            tokens(r#"closure func.44 "install::{closure#0}""#),
            vec!["closure", "func.44", "install::{closure#0}"]
        );
        assert_eq!(strip_comment(r#"closure "a#b" # note"#), r#"closure "a#b" "#);
    }

    #[test]
    fn std_candidates_add_trait_and_inherent_spellings() {
        let c = std_candidates("<std::os::fd::OwnedFd as std::os::fd::AsRawFd>::as_raw_fd");
        assert!(c.contains(&"std::os::fd::AsRawFd::as_raw_fd".to_string()), "{c:?}");
        let c = std_candidates("std::io::error::<impl std::io::Error>::from_raw_os_error");
        assert!(c.contains(&"std::io::Error::from_raw_os_error".to_string()), "{c:?}");
        let c = std_candidates(
            "<std::process::Command as std::os::unix::process::CommandExt>::pre_exec",
        );
        assert!(c.contains(&"std::os::unix::process::CommandExt::pre_exec".to_string()));
    }

    #[test]
    fn instance_paths_drop_the_hash() {
        assert_eq!(
            instance_path("!trust_bodyless_instance::std::mem::drop::1612-6861").as_deref(),
            Some("std::mem::drop")
        );
        assert_eq!(instance_path("libc::fork"), None);
    }
}
