//! Trust (plan step 3.0, docs/design/2026-10-02-step3-lean-through-trust-ir.md §9): ONE NAME for
//! every refusal F1 makes because of a Clean-origin (Lean) body, `[clean-below-gate]`.
//!
//! Before this module the refusals F1 made for a Clean-origin body were spread over four classes
//! and said different amounts: the Clean `def`'s own item was `[producer-declined]` with a bare
//! `DefIndex(4), <hash>` and no Clean reason; a Rust caller was `[converter-refused]` (the
//! converter's `CleanOriginBelowCodegenGate`) when verification was on and `[instance-assembly]`
//! ("has no assembled handoff body") when it was off; on the crate-module lane every item was
//! `[crate-module-unavailable]`. The class decides what a census reader thinks retires the gap,
//! and none of those classes named the Clean carrier work that does.
//!
//! # What it does not rename (plan step 3.4)
//!
//! A refusal of a class that reports a producer/consumer contract break
//! (`[malformed-producer-module]`) keeps its class even when the item is a Clean-origin def: it is
//! a defect to investigate, not Clean carrier work to schedule, and naming it `[clean-below-gate]`
//! would hide it behind the class's options. And since plan step 3.4 the producer's codegen
//! license is per function (owner ruling D37), so no whole-module withholding is ever caused by a
//! Clean-origin body any more: a crate-module lane `[crate-module-unavailable]` refusal keeps its
//! class. (Before 3.4 this module named every such refusal after the first Clean body in the
//! producer's three-item sample, which blamed the whole withholding on one def even when other
//! bodies were named beside it.)
//!
//! # What this module does, and what it never does
//!
//! [`name`] RENAMES a refusal the lane already made. It never produces a refusal, never suppresses
//! one and never admits anything: every input is an `Err` and every output is an `Err`, so the
//! census count, the fatal and the no-fallback contract are unchanged. The original refusal is
//! kept in [`CleanRowRefusal::why`]: verbatim where the lane made a message (the converter's, the
//! instance lane's and the crate-module lane's detail), as its census sample line for any other
//! class, and for the Clean def's own `ExactAssembledBodyAbsent` as one sentence that carries its
//! `DefIndex` and definition hash.
//!
//! # Where the options are printed
//!
//! Once per census, for the class ([`CLASS_OPTIONS`], through `RefusalClass::options`), under the
//! class's `retired by:` line: they are the same for every Clean refusal, so a per-sample copy
//! would repeat one paragraph three times and bury the symbols. [`CleanRowRefusal::message`]
//! (the `Display` of one refusal) carries them too.
//!
//! # Imported Clean-origin bodies
//!
//! The source metadata importer reads Rust's exported Clean-origin identities and refuses
//! them without querying MIR. The retired upstream-MIR bridge no longer reaches codegen.
//! A cross-crate Clean carrier needs its own checked admission; a Rust R entry cannot stand in.
//!
//! # Where the tier and shape come from
//!
//! From the clean-origin DISCLOSURE (`clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME`) of the
//! module the lane lowered against: the same rows `--emit=trust-ir` prints. That is disclosure,
//! read here to word a refusal, and it is never authority: nothing here can turn a refusal into
//! an admission, so a wrong disclosure can at worst mis-word one. A def with no disclosure row
//! says so ("not recorded on this lane"). Since plan step 3.5 the recorder runs on every F1
//! compile, verification on or off, so a local def has no row on F1 only when this compile's
//! finalization published none (before 3.5: every verification-off F1 compile).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use super::FrontendRefusal;

/// Which item a `[clean-below-gate]` refusal is about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CleanRole {
    /// The refused item IS the Clean-origin def.
    Own,
    /// The refused item is a Rust body that reaches the Clean-origin def (a call the converter
    /// would inline or the instance lane would splice).
    Reaches,
    /// The refused item is an upstream body whose MIR (the exporting crate's, which the
    /// `-Ztrust-ir-upstream-mir` lane would bridge) has the Clean-origin def's body inlined into
    /// it: `SourceScopeData::inlined` names the def.
    Inlines,
}

/// What the clean-origin disclosure says about one row. Disclosure only, never authority.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DisclosedRow {
    /// `fn:<id>` rows carry the published `FuncId`; skipped rows carry none.
    pub(crate) func_id: Option<u32>,
    pub(crate) def_path: String,
    pub(crate) clean_name: Option<String>,
    pub(crate) shape: Option<String>,
    /// `gate`, `kernel-tv`, `structural`, or `skipped` (a planner row the recorder did not emit).
    pub(crate) tier: String,
}

/// The payload of a `[clean-below-gate]` refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CleanRowRefusal {
    pub(crate) role: CleanRole,
    /// The Clean-origin def's Rust path (`m::cleanWsum`), or its Clean name when only that is
    /// known.
    pub(crate) def: String,
    /// `None`: no disclosure row on this lane (nothing was recorded, or the def is imported).
    pub(crate) row: Option<DisclosedRow>,
    /// The crate the Clean-origin def was imported from; `None` for a def of this crate.
    pub(crate) imported_from: Option<String>,
    /// The refusal the lane made, verbatim.
    pub(crate) why: String,
}

/// Why no Clean-origin body reaches F1 codegen today, and the options (v7/D3): printed ONCE per
/// census for the `[clean-below-gate]` class (`RefusalClass::options`), and at the end of every
/// [`CleanRowRefusal::message`].
pub(crate) const CLASS_OPTIONS: &str = "No F1 lane admits a Clean-origin Function yet, whatever \
    its tier: since plan step 3.4 a tier-`gate` row carries an authenticated `clean-carrier-gate` \
    license beside its session-ledger entry, and only the `Compiler::compile` lane will honor it \
    (step 3.6). Options: (1) build this crate on the \
    MIR lane, the \
    value-producing path for Clean-origin bodies today: the default LLVM backend, or trust-cg's \
    MIR frontend (`-Ztrust-cg-frontend=mir`) under the strict output gate (owner ruling D38; \
    docs/TCB.md \"Clean-origin body on trust-cg's MIR frontend\"); (2) wait for plan step 3: a \
    tier-`gate` row is admitted through the authenticated `clean-carrier-gate` carrier on the \
    `Compiler::compile` lane (steps 3.4-3.6, D36/D37), a row below `gate` first needs carrier-gate \
    coverage for its shape (step 3.1), and a local def with no row was not published by this \
    compile's finalization (the recorder runs on every F1 compile since step 3.5); (3) keep the \
    Clean call outside this trust-ir-frontend unit. This frontend never falls back to the MIR \
    path";

impl CleanRowRefusal {
    fn role_text(&self) -> String {
        match self.role {
            CleanRole::Own => format!("the Clean-origin def `{}`", self.def),
            CleanRole::Reaches => format!("reaches the Clean-origin def `{}`", self.def),
            CleanRole::Inlines => format!("its MIR inlines the Clean-origin def `{}`", self.def),
        }
    }

    fn tier_text(&self) -> String {
        if let Some(krate) = &self.imported_from {
            return format!(
                "imported from crate `{krate}`: this compile has no trust-ir row for an upstream \
                 Clean body, only the exporting crate's `clean_origin_mir` MIR (cross-crate Clean \
                 bodies are increment 6)"
            );
        }
        match &self.row {
            Some(row) => format!(
                "tier `{}`, shape `{}`",
                row.tier,
                row.shape.as_deref().unwrap_or("unknown")
            ),
            None => "not recorded on this lane: no tier, shape unknown (the Clean recorder runs \
                     on every F1 compile since plan step 3.5, so this compile's finalization \
                     published no row for it)"
                .to_string(),
        }
    }

    /// The census sample: role, def, tier and shape, and the lane's own refusal.
    pub(crate) fn sample(&self) -> String {
        format!("{} ({}): {}", self.role_text(), self.tier_text(), self.why)
    }

    /// The full message: the sample, why F1 admits no Clean-origin body today, and the options.
    pub(crate) fn message(&self) -> String {
        format!(
            "{} ({}) is not admitted to F1 codegen: {}. {CLASS_OPTIONS}",
            self.role_text(),
            self.tier_text(),
            self.why
        )
    }
}

/// Read one JSON string field (`"key":"value"`) out of a flat disclosure formula, undoing the
/// minimal escaping `clean_origin_join::json_escape_min` applies. PURE.
pub(crate) fn json_string_field(formula: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\":\"");
    let start = formula.find(&needle)? + needle.len();
    let mut out = String::new();
    let mut chars = formula[start..].chars();
    while let Some(c) = chars.next() {
        match c {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
                }
                other => out.push(other),
            },
            c => out.push(c),
        }
    }
    None
}

/// Every row the clean-origin disclosure of `module` lists (emitted `fn:<id>` rows and planner
/// `skipped:<def_index>` rows; general-lane rows have no Rust path and are never callable from
/// Rust, so they are not listed). PURE.
pub(crate) fn disclosed_rows(module: &trust_ir::Module) -> Vec<DisclosedRow> {
    let mut rows = Vec::new();
    for spec in &module.spec_modules {
        if spec.name != trust_thir_lower::clean_origin_join::CLEAN_ORIGIN_DISCLOSURE_NAME {
            continue;
        }
        for invariant in &spec.invariants {
            let (func_id, tier) = if let Some(id) = invariant.name.strip_prefix("fn:") {
                let Ok(id) = id.parse::<u32>() else { continue };
                let Some(tier) = json_string_field(&invariant.formula, "tier") else { continue };
                (Some(id), tier)
            } else if invariant.name.starts_with("skipped:") {
                (None, "skipped".to_string())
            } else {
                continue;
            };
            let Some(def_path) = json_string_field(&invariant.formula, "def_path") else {
                continue;
            };
            rows.push(DisclosedRow {
                func_id,
                def_path,
                clean_name: json_string_field(&invariant.formula, "clean_name"),
                shape: json_string_field(&invariant.formula, "shape"),
                tier,
            });
        }
    }
    rows
}

/// The backticked tokens of a refusal detail, in order. PURE.
pub(crate) fn backticked(detail: &str) -> Vec<&str> {
    detail.split('`').skip(1).step_by(2).collect()
}

/// The instance lane's refusal names a Clean-origin body: the frozen `instance_assembly.rs`
/// phrases ("maps to the Clean-origin body", "reaches a Clean-origin body", owner ruling D17
/// freezes them byte for byte), or a token that is a Clean-origin def's mangled symbol (the
/// verification-off "monomorphic callee `<symbol>` has no assembled handoff body"). Returns the
/// Clean def it names, when the detail names one. PURE.
pub(crate) fn instance_lane_names_clean(
    detail: &str,
    clean_symbols: &[(String, String)],
    rows: &[DisclosedRow],
) -> Option<Option<String>> {
    let tokens = backticked(detail);
    for token in &tokens {
        if let Some((_, def)) = clean_symbols.iter().find(|(symbol, _)| symbol == token) {
            return Some(Some(def.clone()));
        }
    }
    if !detail.contains("Clean-origin body") {
        return None;
    }
    for token in &tokens {
        if let Some(row) = rows.iter().find(|row| row.clean_name.as_deref() == Some(*token)) {
            return Some(Some(row.def_path.clone()));
        }
    }
    Some(None)
}

/// The Clean-origin defs of this crate, with their untrimmed Rust paths (the recorder's
/// `def_path` spelling, so a disclosure row matches by equality).
fn clean_defs(tcx: TyCtxt<'_>) -> Vec<(LocalDefId, String)> {
    tcx.resolutions(())
        .clean_origin_defs
        .iter()
        .map(|&(def, _, _)| {
            let path =
                rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def.to_def_id()));
            (def, path)
        })
        .collect()
}

/// The disclosure rows of the module this session lowers against: the F1 handoff's assembled
/// module, or else the published crate module.
fn session_rows(tcx: TyCtxt<'_>) -> Vec<DisclosedRow> {
    let handoff =
        tcx.sess.with_trust_compiler_state::<trust_thir_lower::AssembledCrateModuleForCodegen, _>(
            |handoff| handoff.assembled_module().ok(),
        );
    if let Some(module) = handoff {
        return disclosed_rows(&module);
    }
    trust_thir_lower::crate_module::with_published_crate_module(tcx.sess, |published| {
        published.map(|published| disclosed_rows(published.module())).unwrap_or_default()
    })
}

fn row_for(rows: &[DisclosedRow], def: &str) -> Option<DisclosedRow> {
    rows.iter().find(|row| row.def_path == def).cloned()
}

/// A Clean-origin def another crate exports (`trust_clean_origin_exports`, the I7 export list:
/// every Clean-origin def of that crate), with its untrimmed Rust path and its crate's name.
#[derive(Debug, Clone)]
struct ImportedCleanDef {
    def_id: DefId,
    path: String,
    krate: String,
}

/// Every Clean-origin def this compile's dependencies export. A crate with no island exports an
/// empty list, so this costs one cached root-array read per crate.
fn imported_clean_defs(tcx: TyCtxt<'_>) -> Vec<ImportedCleanDef> {
    let mut defs = Vec::new();
    for &krate in tcx.crates(()) {
        for &index in tcx.trust_clean_origin_exports(krate).iter() {
            let def_id = DefId { krate, index };
            defs.push(ImportedCleanDef {
                def_id,
                path: rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def_id)),
                krate: tcx.crate_name(krate).to_string(),
            });
        }
    }
    defs
}

/// `def_id` as a Clean-origin def: of this crate (`Some(None)`), imported from the named crate
/// (`Some(Some(krate))`), or not one (`None`).
fn clean_origin_of(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Option<String>> {
    match def_id.as_local() {
        Some(local) => tcx
            .resolutions(())
            .clean_origin_defs
            .iter()
            .any(|&(def, _, _)| def == local)
            .then_some(None),
        None => tcx
            .trust_clean_origin_exports(def_id.krate)
            .contains(&def_id.index)
            .then(|| Some(tcx.crate_name(def_id.krate).to_string())),
    }
}

/// Read only the actual Rust Clean-origin metadata, never an upstream MIR body.
pub(crate) fn source_origin_refusal(tcx: TyCtxt<'_>, def: DefId) -> Option<CleanRowRefusal> {
    let imported_from = clean_origin_of(tcx, def)?;
    Some(CleanRowRefusal {
        role: CleanRole::Own,
        def: rustc_middle::ty::print::with_no_trimmed_paths!(tcx.def_path_str(def)),
        row: None,
        imported_from,
        why: "the Rust level-R metadata importer grants no Clean carrier admission; a checked cross-crate Clean carrier is required".into(),
    })
}

/// Step (1) of [`name`], pure: how the lane's refusal of a Clean-origin def's OWN item reads under
/// `[clean-below-gate]` — the sentence kept in [`CleanRowRefusal::why`] — or `None` when the
/// refusal keeps its own class.
///
/// `None` for a `[malformed-producer-module]` refusal (plan step 3.4, the step-3 lander's
/// hand-over): a producer/consumer contract break is a defect to investigate, never Clean carrier
/// work, and the census stays fatal either way. For the handoff lane's `ExactAssembledBodyAbsent`
/// the sentence says why the handoff holds no body: since plan step 3.4 it indexes a
/// `Producer::Clean` row only as an entry of the Session's carrier ledger
/// (`trust_thir_lower::AssembledCrateModuleForCodegen::checked_with_ledger`), and this def has
/// none (its row is below tier `gate`, not recorded on this lane, or kept no license).
pub(crate) fn own_def_why(refusal: &FrontendRefusal) -> Option<String> {
    if refusal.class() == super::RefusalClass::MalformedProducerModule {
        return None;
    }
    Some(match refusal {
        FrontendRefusal::CleanBelowGate { row, .. } => row.why.clone(),
        FrontendRefusal::ExactAssembledBodyAbsent { def_index, definition, .. } => format!(
            "the assembled handoff indexes no body for it (DefIndex({def_index}), {definition}): \
             it indexes a `Producer::Clean` row only as an entry of this Session's carrier ledger \
             (a tier-`gate` row stamped `clean-carrier-gate` whose gate token authenticates its \
             exact Function, `trust_thir_lower::AssembledCrateModuleForCodegen::\
             checked_with_ledger`), and this def has none"
        ),
        other => {
            format!("the lane refused it as [{}]: {}", other.class().tag(), other.sample_line())
        }
    })
}

/// THE ONE ENTRY: rename `refusal`, which F1 made for `instance`, to `[clean-below-gate]` when it
/// is a refusal because of a Clean-origin body; return every other refusal unchanged.
pub(crate) fn name<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    refusal: FrontendRefusal,
) -> FrontendRefusal {
    let defs = clean_defs(tcx);
    let imported = imported_clean_defs(tcx);
    if defs.is_empty() && imported.is_empty() {
        return refusal;
    }
    let symbol = tcx.symbol_name(instance).name.to_string();

    // (1) The item IS a Clean-origin def, of this crate or imported (an imported one is the
    // downstream copy every Clean-origin def gets, being `cross_crate_inlinable`): whatever the
    // lane refused it as.
    let own = match instance.def {
        ty::InstanceKind::Item(def_id) => match def_id.as_local() {
            Some(local) => {
                defs.iter().find(|(d, _)| *d == local).map(|(_, def)| (def.clone(), None))
            }
            None => imported
                .iter()
                .find(|def| def.def_id == def_id)
                .map(|def| (def.path.clone(), Some(def.krate.clone()))),
        },
        _ => None,
    };
    if let Some((def, imported_from)) = own {
        let Some(why) = own_def_why(&refusal) else {
            return refusal;
        };
        let row = if imported_from.is_some() { None } else { row_for(&session_rows(tcx), &def) };
        return FrontendRefusal::CleanBelowGate {
            symbol,
            row: CleanRowRefusal { role: CleanRole::Own, def, row, imported_from, why },
        };
    }

    if let FrontendRefusal::CleanBelowGate { symbol, mut row } = refusal {
        // Trust (WS5.2): the converter's refusal names a callee it reached by its def path
        // ([`converter_refusal`]); a callee with no disclosure row that is an imported Clean def
        // is said to be one, exactly as the instance lane's refusal of it says (below).
        if row.role == CleanRole::Reaches && row.row.is_none() && row.imported_from.is_none() {
            row.imported_from =
                imported.iter().find(|def| def.path == row.def).map(|def| def.krate.clone());
        }
        return FrontendRefusal::CleanBelowGate { symbol, row };
    }
    let rows = session_rows(tcx);

    // (2) The instance lane refused a Rust body because of a Clean-origin callee, of this crate
    // or imported (an imported callee is refused as an upstream body, increment 6).
    if let FrontendRefusal::InstanceAssembly { detail, .. } = &refusal {
        let clean_symbols: Vec<(String, String)> = defs
            .iter()
            .map(|(local, def)| (local.to_def_id(), def))
            .chain(imported.iter().map(|def| (def.def_id, &def.path)))
            // A Clean-origin def carries no generics today (its signature is carriers only);
            // a generic one has no single symbol, so it is never matched by symbol.
            .filter(|(def_id, _)| tcx.generics_of(*def_id).count() == 0)
            .map(|(def_id, def)| {
                let mono = ty::Instance::mono(tcx, def_id);
                (tcx.symbol_name(mono).name.to_string(), def.clone())
            })
            .collect();
        if let Some(named) = instance_lane_names_clean(detail, &clean_symbols, &rows) {
            let def = named.unwrap_or_else(|| "<a Clean-origin body the detail names>".to_string());
            let imported_from =
                imported.iter().find(|imported| imported.path == def).map(|def| def.krate.clone());
            return FrontendRefusal::CleanBelowGate {
                symbol,
                row: CleanRowRefusal {
                    role: CleanRole::Reaches,
                    row: if imported_from.is_some() { None } else { row_for(&rows, &def) },
                    def,
                    imported_from,
                    why: format!("the instance lane refused it: {detail}"),
                },
            };
        }
    }

    // (3) Until plan step 3.4 a crate-module-lane `[crate-module-unavailable]` refusal was renamed
    // here after the first Clean body named in the producer's leg-4 sample (a three-item sample, so
    // the whole withholding was blamed on one def). Leg 4 is per function now (owner ruling D37):
    // no Clean-origin body withholds the module, so that refusal keeps its own class.
    refusal
}

/// The converter's `CleanOriginBelowCodegenGate` for the item `symbol`: the Clean function
/// `clean_fn` of `module` was the function being lowered or a callee the converter would have
/// inlined or called. Worded from `module`'s own disclosure; `converter` is the converter's
/// message, kept verbatim.
pub(crate) fn converter_refusal(
    symbol: &str,
    module: &trust_ir::Module,
    clean_fn: &str,
    converter: String,
) -> FrontendRefusal {
    let rows = disclosed_rows(module);
    let clean = module
        .functions
        .iter()
        .find(|f| f.name == clean_fn && f.producer == Some(trust_ir::Producer::Clean));
    let func_id = clean.map(|f| f.id.index());
    let row = rows
        .iter()
        .find(|row| func_id.is_some() && row.func_id == func_id)
        .or_else(|| rows.iter().find(|row| row.clean_name.as_deref() == Some(clean_fn)))
        .cloned();
    // Trust (WS5.2): with no disclosure row (an imported Clean def has none here), the def is
    // named by the function's `display_path` — its Rust def path — never by `Function.name`,
    // which is the link-time symbol; [`name`] then says which crate it was imported from.
    let def = row.as_ref().map(|row| row.def_path.clone()).unwrap_or_else(|| {
        clean.and_then(|f| f.display_path.clone()).unwrap_or_else(|| clean_fn.to_string())
    });
    FrontendRefusal::CleanBelowGate {
        symbol: symbol.to_string(),
        row: CleanRowRefusal {
            role: CleanRole::Reaches,
            def,
            row,
            imported_from: None,
            why: converter,
        },
    }
}
