//! The census's fail-closed gates (Critique P0 items that live here).
//!
//! * **I-EFFECTS-COVERED** (C-16): for every trust-ir body on a root's path,
//!   every HIR call whose callee is not audited effect-free
//!   ([`effect_free`]) must appear in the body's trust-ir, counted by span
//!   and callee — foreign items and std rows, and ALSO local bodies (an
//!   erased call to a local helper hides the helper's effects: the review's
//!   F1), core/alloc functions (a combinator that runs a closure) and
//!   upstream functions. A missing call (the producer erased it, as the
//!   wave-ER `for` summary does today) is `PC-PRODUCER-ERASED`; a body whose
//!   HIR list the host cannot give is `PC-PRODUCER-ERASED` too (the check
//!   could not run). A counted trust-ir call with no HIR twin is
//!   `PC-CENSUS-SKEW`.
//! * **The drop gate** (C-2): until Step-2 increment 4b emits `Inst::Drop`,
//!   a body on the path that holds a value whose drop glue may have a
//!   platform effect — an fd carrier (a `close`), or a type with a `Drop`
//!   impl (a user guard: the review's F2) — is `PC-DROP-ELIDED`: from
//!   typeck's facts (REQUIRED: without them the gate cannot run, which is
//!   `PC-DROP-ELIDED` too), unioned with the census's own trust-ir scan.
//! * **I-SITES-COVERED** (§2.5, C-4): the host's HIR site census against
//!   the census's sites, as multisets of `(body, line, col, callee)`.
//! * **CFG skew** (C-7): a site of the shipped configuration with no
//!   counterpart in the checked one.
//!
//! [`crate::run`] merges every refusal of the cross-checks into the census
//! output, linked to its site (or to its HIR identity), so no refusal is
//! returned "on the side" where a verdict would not see it.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{FuncId, Inst, Module, Ty};

use crate::sites::{strip_generics, strip_generics_cow};
use crate::{
    Callee, CensusContext, CensusOutput, HirEffect, HirSite, IrSite, Refusal, RootProgram,
    SiteRefusal, fn_path,
};

/// The HIR effect callee of an indirect call (an fn pointer, a `dyn`).
pub const INDIRECT: &str = "<indirect>";

/// Whether a call to `c` may be erased without changing any effect the
/// census models: an audited effect-free std/core path or a panic. Every
/// other call counts for I-EFFECTS-COVERED.
#[must_use]
pub fn effect_free(c: &Callee) -> bool {
    match c {
        Callee::Std { paths } => {
            crate::audit::lookup(paths).is_some() || paths.iter().any(|p| crate::audit::is_panic(p))
        }
        Callee::CoreAlloc { path } => {
            crate::audit::lookup_str(path).is_some() || crate::audit::is_panic(path)
        }
        _ => false,
    }
}

/// Whether a HIR effect's callee string names an effect-free callee (the
/// host lists every call; the census skips the audited ones on both sides).
fn hir_effect_free(callee: &str) -> bool {
    crate::audit::lookup_str(callee).is_some() || crate::audit::is_panic(callee)
}

/// Whether an IR callee is the HIR effect's callee.
fn callee_is(c: &Callee, name: &str) -> bool {
    let name_stripped = strip_generics_cow(name);
    let same = |p: &str| p == name || strip_generics_cow(p) == name_stripped;
    match c {
        Callee::Foreign { link_name, .. } => link_name == name,
        Callee::Std { paths } => paths.iter().any(|p| same(p)),
        Callee::Body { path, .. }
        | Callee::CoreAlloc { path }
        | Callee::LocalRefused { path }
        | Callee::Upstream { path, .. } => same(path),
        Callee::Unresolved { name: n, .. } => same(n),
    }
}

/// The counted calls of a body's trust-ir: `(line, col, callee, site)`.
fn ir_effects(m: &Module, callees: &[Callee], f: FuncId) -> Vec<(u32, u32, Callee, IrSite)> {
    let mut out = Vec::new();
    let Some(func) = m.functions.get(f.as_usize()) else { return out };
    for b in &func.blocks {
        for (i, n) in b.body.iter().enumerate() {
            let c = match &n.inst {
                Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                    let Some(c) = callees.get(callee.as_usize()) else { continue };
                    c.clone()
                }
                // An erased indirect call hides whatever it calls: the host
                // lists it as `<indirect>`.
                Inst::CallIndirect { .. } => {
                    Callee::Unresolved { name: INDIRECT.into(), why: "an indirect call".into() }
                }
                _ => continue,
            };
            let c = &c;
            if effect_free(c) {
                continue;
            }
            let (line, col) = n.span.map_or((0, 0), |s| (s.line, s.col));
            out.push((
                line,
                col,
                c.clone(),
                IrSite { func: f, block: b.id, inst: i, span: n.span },
            ));
        }
    }
    out
}

/// I-EFFECTS-COVERED for one body.
#[must_use]
pub fn effects_covered(
    m: &Module,
    cx: &dyn CensusContext,
    callees: &[Callee],
    f: FuncId,
) -> Vec<(Option<IrSite>, Refusal)> {
    let body = fn_path(m, f);
    let Some(hir) = cx.hir_effects(f) else {
        return vec![(
            None,
            Refusal::ProducerErased {
                body,
                detail: "the host gave no HIR effect list, so I-EFFECTS-COVERED could not be \
                         checked"
                    .into(),
            },
        )];
    };
    let ir = ir_effects(m, callees, f);
    let mut used = vec![false; ir.len()];
    let mut out = Vec::new();
    for HirEffect { line, col, callee } in &hir {
        if hir_effect_free(callee) {
            continue;
        }
        match ir
            .iter()
            .enumerate()
            .find(|(i, (l, c, ic, _))| !used[*i] && l == line && c == col && callee_is(ic, callee))
        {
            Some((i, _)) => used[i] = true,
            None => out.push((
                None,
                Refusal::ProducerErased {
                    body: body.clone(),
                    detail: format!(
                        "`{callee}` at {line}:{col} is in the HIR but not in the trust-ir (the \
                         producer erased it)"
                    ),
                },
            )),
        }
    }
    for (i, (l, c, ic, at)) in ir.iter().enumerate() {
        if !used[i] {
            out.push((
                Some(*at),
                Refusal::CensusSkew {
                    detail: format!(
                        "trust-ir call {ic:?} at {l}:{c} in `{body}` has no HIR effect twin"
                    ),
                },
            ));
        }
    }
    out
}

/// The drop gate (C-2) for one body: typeck's facts (required) unioned with
/// the census's own scan of the body's trust-ir — every value, parameter,
/// cell or call result whose type holds, by value, a type with effectful
/// drop glue ([`crate::shape::effectful_drop`]: an fd carrier, a type whose
/// `Drop` impl is in the module, a std composite that owns descriptors).
#[must_use]
pub fn drop_gate(m: &Module, cx: &dyn CensusContext, f: FuncId) -> Vec<(Option<IrSite>, Refusal)> {
    let impls = crate::shape::drop_impl_types(m);
    drop_gate_with_impls(m, cx, f, &impls)
}

fn drop_gate_with_impls(
    m: &Module,
    cx: &dyn CensusContext,
    f: FuncId,
    impls: &BTreeSet<String>,
) -> Vec<(Option<IrSite>, Refusal)> {
    let body = fn_path(m, f);
    let mut found: BTreeMap<String, Option<IrSite>> = BTreeMap::new();
    let mut out = Vec::new();
    match cx.drops(f) {
        Some(drops) => {
            for ty in drops {
                found.entry(ty).or_insert(None);
            }
        }
        None => out.push((
            None,
            Refusal::DropElided {
                body: body.clone(),
                ty: "(any type: the host gave no typeck drop facts, so the drop gate could not \
                     run)"
                    .into(),
            },
        )),
    }
    let Some(func) = m.functions.get(f.as_usize()) else { return out };
    let mut note = |t: &Ty, at: Option<IrSite>| {
        if let Some(c) = crate::shape::effectful_drop(m, t, impls) {
            found.entry(c).or_insert(at);
        }
    };
    if let Some(ft) = m.func_types.get(func.ty.as_usize()) {
        for t in &ft.params {
            note(t, None);
        }
    }
    for b in &func.blocks {
        for (_, t) in &b.params {
            note(t, None);
        }
        for (i, n) in b.body.iter().enumerate() {
            let at = Some(IrSite { func: f, block: b.id, inst: i, span: n.span });
            match &n.inst {
                Inst::Alloca { ty, .. }
                | Inst::Load { ty, .. }
                | Inst::Store { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::InsertField { ty, .. }
                | Inst::ExtractField { ty, .. }
                | Inst::Undef { ty } => note(ty, at),
                Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => {
                    if let Some(ft) = m
                        .functions
                        .get(callee.as_usize())
                        .and_then(|g| m.func_types.get(g.ty.as_usize()))
                    {
                        for t in ft.returns.iter().chain(ft.params.iter()) {
                            note(t, at);
                        }
                    }
                }
                _ => {}
            }
        }
    }
    out.extend(
        found.into_iter().map(|(ty, at)| (at, Refusal::DropElided { body: body.clone(), ty })),
    );
    out
}

/// Every gate of a translated root.
#[must_use]
pub fn root_gates(
    m: &Module,
    cx: &dyn CensusContext,
    callees: &[Callee],
    rp: &RootProgram,
) -> Vec<(Option<IrSite>, Refusal)> {
    let impls = crate::shape::drop_impl_types(m);
    let mut out = Vec::new();
    for f in &rp.bodies {
        out.extend(effects_covered(m, cx, callees, *f));
        out.extend(drop_gate_with_impls(m, cx, *f, &impls));
    }
    out
}

/// I-SITES-COVERED: the host's HIR sites against the census's, as multisets
/// of `(body, line, col, callee)` (C-4: two calls of one macro expansion
/// share a span, so counts, not sets).
#[must_use]
pub fn sites_covered(m: &Module, out: &CensusOutput, hir: &[HirSite]) -> Vec<SiteRefusal> {
    let key = |b: &str, l: u32, c: u32, s: &str| (b.to_string(), l, c, strip_generics(s));
    let mut census: BTreeMap<(String, u32, u32, String), Vec<usize>> = BTreeMap::new();
    for s in &out.sites {
        let (l, c) = s.at.span.map_or((0, 0), |sp| (sp.line, sp.col));
        census.entry(key(&s.body, l, c, &s.symbol)).or_default().push(s.id);
    }
    let mut want: BTreeMap<(String, u32, u32, String), usize> = BTreeMap::new();
    for h in hir {
        *want.entry(key(&h.body, h.line, h.col, &h.callee)).or_default() += 1;
    }
    let lowered = |b: &str| {
        m.functions
            .iter()
            .any(|f| !f.blocks.is_empty() && f.display_path.as_deref().unwrap_or(&f.name) == b)
    };
    let mut refusals = Vec::new();
    for (k, n) in &want {
        let have = census.get(k).map_or(0, Vec::len);
        for _ in have..*n {
            let r = if lowered(&k.0) {
                Refusal::SiteNotInIr {
                    body: k.0.clone(),
                    callee: k.3.clone(),
                    at: format!("{}:{}", k.1, k.2),
                }
            } else {
                Refusal::BodyNotLowered { path: k.0.clone() }
            };
            let h = HirSite { body: k.0.clone(), line: k.1, col: k.2, callee: k.3.clone() };
            refusals.push(SiteRefusal {
                root: None,
                site: None,
                at: None,
                hir: Some(h),
                refusal: r,
            });
        }
    }
    for (k, ids) in &census {
        let n = want.get(k).copied().unwrap_or(0);
        for id in ids.iter().skip(n) {
            refusals.push(SiteRefusal {
                root: None,
                site: Some(*id),
                at: Some(out.sites[*id].at),
                hir: None,
                refusal: Refusal::CensusSkew {
                    detail: format!(
                        "census site `{}` at {}:{} in `{}` has no HIR site-census twin",
                        k.3, k.1, k.2, k.0
                    ),
                },
            });
        }
    }
    refusals
}

/// C-7: sites of the shipped (product) configuration with no counterpart in
/// the checked one, each an unanalysed site by its HIR identity.
#[must_use]
pub fn cfg_skew(checked: &[HirSite], product: &[HirSite]) -> Vec<SiteRefusal> {
    let mut have: BTreeMap<&HirSite, usize> = BTreeMap::new();
    for s in checked {
        *have.entry(s).or_default() += 1;
    }
    let mut out = Vec::new();
    for s in product {
        match have.get_mut(s) {
            Some(n) if *n > 0 => *n -= 1,
            _ => out.push(SiteRefusal {
                root: None,
                site: None,
                at: None,
                hir: Some(s.clone()),
                refusal: Refusal::CfgSkew {
                    detail: format!(
                        "`{}` at {}:{} in `{}` ships but is not in the checked build",
                        s.callee, s.line, s.col, s.body
                    ),
                },
            }),
        }
    }
    out
}
