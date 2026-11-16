// Trust (cross-crate PROOF-position citation, increment 2): the compiler side
// of `trust_certify::clean_island::extern_proof`. This whole file is
// Trust-owned; it has no upstream counterpart.
//
//! Gathering the dependency crates that transported Clean proof material, and
//! saying so in the one diagnostic that today refuses a citation with no
//! options at all.
//!
//! # What this file does and does not do
//!
//! It GATHERS. [`extern_proof_units`] turns what rmeta transported into the
//! `ExternProofUnit` values `compose_extern_proof_batch` consumes, and
//! [`proof_material_crates`] answers the question a diagnostic needs — *which
//! dependencies carry Clean proof material at all*.
//!
//! It does not COMPOSE. No caller of this module runs a kernel batch, changes
//! a verdict, grades a citation or admits a name. Composition is increment 3;
//! the reasons it is not here are written down in
//! `docs/design-notes/2026-09-18-cross-crate-proof-citation.md` §12 and in the
//! NOTES of this lane, and the short form is that the accept path needs an
//! owner ruling on the E9 payload schema (R3) and a second session threaded
//! through the citation sweep. Until then a cross-crate citation is REFUSED,
//! exactly as it is today — the only thing that changes is that the refusal
//! now says what it is refusing and what the spelling would be.
//!
//! # Why the diagnostic may not simply run the composition
//!
//! Composing costs `n + 2` full kernel batches. Running that inside an error
//! path, to sharpen a message on a compilation that is already failing, buys a
//! better sentence for an unbounded amount of work and a new way for a
//! diagnostic to be the slowest thing in the build. So the diagnostic reports
//! only what TRANSPORT already knows — which crates carry islands, how many,
//! and under which kernel — and never claims that a cited name exists in one
//! of them. Saying "`spec` carries Clean proof material" is true from the
//! manifest; saying "`spec` declares `cap_le`" would require the kernel.

use rustc_hir::def_id::CrateNum;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use trust_certify::clean_island::{ExternProofUnit, ExternProofUnitId};

/// One dependency crate that transported Clean proof material, as the
/// diagnostics need it: the name a citation would spell, and how many islands
/// crossed.
pub(crate) struct ProofMaterialCrate {
    pub(crate) name: Symbol,
    pub(crate) islands: usize,
}

/// Every crate loaded into this compilation that transported `clean { … }`
/// island sources, in a canonical order that does not depend on the load
/// order of the crate graph.
///
/// `CrateNum` is load order and must never decide anything a user can see, so
/// the result is sorted by `(crate name, stable crate id)` — the same
/// canonical order `compose_extern_proof_batch` re-establishes for itself.
///
/// This is the whole crate graph, not the direct dependencies: a citation can
/// only name a crate this compilation actually loaded, and which of those are
/// direct is a Cargo fact the compiler does not have. A unit that should not
/// have been composed is refused by the composition, not filtered out here.
pub(crate) fn proof_material_crates(tcx: TyCtxt<'_>) -> Vec<ProofMaterialCrate> {
    let mut crates: Vec<(Symbol, u64, usize)> = Vec::new();
    for &cnum in tcx.crates(()) {
        let Some(count) = transported_island_count(tcx, cnum) else { continue };
        crates.push((tcx.crate_name(cnum), tcx.stable_crate_id(cnum).as_u64(), count));
    }
    crates.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()).then(a.1.cmp(&b.1)));
    crates.into_iter().map(|(name, _, islands)| ProofMaterialCrate { name, islands }).collect()
}

/// The transported units, ready for `compose_extern_proof_batch`.
///
/// A crate is included exactly when it carries BOTH a manifest and at least
/// one island source. Either half alone is a transport defect rather than a
/// crate to compose: the manifest's digest is taken over the sources, so one
/// without the other identifies nothing. Such a crate is dropped here and the
/// composition never sees it — a unit with no sources would be refused by
/// `ExternProofRefusal::NoSources` anyway, but naming a crate in a refusal
/// because the compiler mis-encoded it teaches the author nothing they can
/// act on.
///
/// NOTHING CALLS THIS YET. It is the input half of increment 3, landed with
/// the transport it reads so the two are reviewed together; `#[allow(dead_
/// code)]` is deliberate and is removed by the increment that composes.
#[allow(dead_code)]
pub(crate) fn extern_proof_units(tcx: TyCtxt<'_>) -> Vec<ExternProofUnit> {
    let mut units: Vec<ExternProofUnit> = Vec::new();
    for &cnum in tcx.crates(()) {
        let Some(manifest) = tcx.trust_clean_proof_manifest(cnum) else { continue };
        let sources = tcx.trust_clean_island_sources(cnum);
        if sources.is_empty() {
            continue;
        }
        units.push(ExternProofUnit {
            id: ExternProofUnitId {
                crate_name: tcx.crate_name(cnum).to_string(),
                stable_crate_id: tcx.stable_crate_id(cnum).as_u64(),
            },
            kernel_version: manifest.kernel_version.clone(),
            declared_source_digest: manifest.source_digest.clone(),
            sources: sources.clone(),
        });
    }
    // Canonical order, for the same reason as above. The composition sorts
    // again; doing it here too means a caller that reports the units before
    // composing reports them in the order the refusals will use.
    units.sort_by(|a, b| a.id.cmp(&b.id));
    units
}

/// How many islands `cnum` transported, or `None` when it transported no Clean
/// proof material at all (every ordinary crate).
fn transported_island_count(tcx: TyCtxt<'_>, cnum: CrateNum) -> Option<usize> {
    tcx.trust_clean_proof_manifest(cnum)?;
    let sources = tcx.trust_clean_island_sources(cnum);
    (!sources.is_empty()).then_some(sources.len())
}

/// The v7/D3 options for a citation this crate's own Clean environment does
/// not resolve, when some dependency carries Clean proof material.
///
/// Returns `None` when no dependency carries any — in which case the existing
/// diagnostic is already complete and gains nothing from a list of no crates.
///
/// Every sentence here is a fact of TRANSPORT, never of the kernel: the
/// manifest says a crate published islands, and nothing in this function
/// claims that any particular declaration is in them. An option that cannot be
/// taken is worse than no option (commit `3e9b1e3d2de`), so the one thing this
/// must not do is suggest citing `krate.name` as though it worked today.
pub(crate) fn cross_crate_citation_notes(tcx: TyCtxt<'_>, cited: &str) -> Option<Vec<String>> {
    let crates = proof_material_crates(tcx);
    if crates.is_empty() {
        return None;
    }
    let listed = crates
        .iter()
        .map(|krate| format!("`{}` ({} island(s))", krate.name, krate.islands))
        .collect::<Vec<_>>()
        .join(", ");
    let head = cited.split_once('.').map(|(head, _)| head);
    // "crates loaded into this compilation", never "dependencies of this
    // crate": `proof_material_crates` walks the whole crate graph, and a
    // TRANSITIVE crate the author never named in a manifest would be called a
    // dependency by a sentence this compiler has no Cargo fact to support.
    let mut notes = vec![format!(
        "these crates loaded into this compilation transported Clean proof material: \
         {listed}. Some may be transitive — which are direct dependencies is a Cargo fact \
         the compiler does not have. A citation is resolved against THIS crate's \
         `clean {{ … }}` islands and the Clean prelude only — a dependency's theorems do \
         not cross into proof position yet, so none of them could have answered for \
         `{cited}`"
    )];
    if let Some(head) = head
        && crates.iter().any(|krate| krate.name.as_str() == head)
    {
        notes.push(format!(
            "`{head}` names one of those crates, and `{cited}` is spelled the way a \
             dependency's theorem WILL be cited — the crate name, a `.`, then the \
             declaration's own Clean name, which is the reserved spelling and the only \
             one (`::` is refused). It is not wired yet, so this is a refusal about the \
             capability, not about how you wrote it"
        ));
    }
    notes.push(
        "options: (1) mount the shared Clean source in THIS crate as well — `#[path = \
         \"../shared/Defs.lean\"] clean mod defs;` is re-elaborated per crate and is the \
         cross-crate share that works today; (2) vendor the declaration into this crate as \
         a `clean { … }` island; (3) prove the clause from this crate's own islands"
            .to_string(),
    );
    Some(notes)
}
