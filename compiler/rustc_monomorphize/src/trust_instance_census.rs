//! Diagnostic census of the actual local-codegen collector, not its DefId-only
//! summary or the Trust producer's admitted subset. Collection is never forced.
//! Even a completed census is NOT the whole-program computational denominator:
//! unvisited allocations/vtables, intrinsics, linked external bodies and
//! backend/runtime synthesis need additional observers. Successful exit is required.

mod dependencies;

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::path::Path;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_middle::mono::{CodegenUnit, MonoItem};
use rustc_middle::ty::{InstanceKind, ShimKind, TyCtxt};
use rustc_session::Session;
use rustc_span::{FileName, SourceFileHash, SourceFileHashAlgorithm};
use serde_json::{Value, json};

use crate::collector::UsageMap;

const SCHEMA: &str = "trust.rust.mono-item-census.v3";
const SCOPE: &str = "actual-local-codegen-collector";
const UNMEASURED: &[&str] = &[
    "constant-allocations-outside-visited-collector-results",
    "eager-constant-root-dependencies",
    "unvisited-or-backend-synthesized-vtables",
    "constant-evaluation-interpreter-execution",
    "allocation-bytes-and-relocation-codegen-semantics",
    "caller-expanded-intrinsics",
    "external-linked-and-foreign-bodies",
    "indirect-runtime-call-targets",
    "backend-synthesized-functions",
    "runtime-startup-and-linker-inputs",
    "pre-optimization-computational-population",
    "dependency-and-build-input-closure",
];

#[derive(Default)]
struct State {
    output: Option<File>,
    roots: Option<Vec<String>>,
    snapshot: Option<(usize, String)>,
}

fn sha256(bytes: &[u8]) -> String {
    SourceFileHash::new_in_memory(SourceFileHashAlgorithm::Sha256, bytes)
        .to_string()
        .strip_prefix("sha256=")
        .expect("SHA-256 prefix")
        .to_owned()
}

fn absolute(path: &Path) -> Result<String, String> {
    let path = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().map_err(|error| error.to_string())?.join(path)
    };
    path.to_str().map(str::to_owned).ok_or_else(|| "non-UTF-8 census path".into())
}

fn require<T>(sess: &Session, result: Result<T, String>) -> T {
    result.unwrap_or_else(|error| sess.dcx().fatal(format!("Rust instance census: {error}")))
}

fn record(file: &mut File, value: &Value) -> Result<String, String> {
    let mut bytes = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    file.write_all(&bytes).map_err(|error| error.to_string())?;
    file.flush().map_err(|error| error.to_string())?;
    Ok(sha256(&bytes))
}

/// Start before parsing, using create_new so a failed invocation cannot reuse a
/// prior report. Nothing is emitted when the diagnostic option is absent.
pub fn prepare(sess: &Session, compiler_version: &str) {
    let Some(path) = &sess.opts.unstable_opts.trust_instance_census else { return };
    if sess.opts.unstable_opts.checksum_hash_algorithm != Some(SourceFileHashAlgorithm::Sha256) {
        sess.dcx().fatal("-Ztrust-instance-census requires -Zchecksum-hash-algorithm=sha256");
    }
    let input = require(
        sess,
        sess.io.input.opt_path().ok_or_else(|| "requires a file input".into()).and_then(absolute),
    );
    let mut output = require(
        sess,
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| format!("cannot create NEW output {}: {error}", path.display())),
    );
    require(
        sess,
        record(
            &mut output,
            &json!({
                "schema": SCHEMA, "event": "begin", "scope": SCOPE,
                "input": input, "compiler_version": compiler_version,
                "target": sess.opts.target_triple.to_string(),
                "edition": sess.edition().to_string(),
                "direct_lowering": sess.trust_ir_lower_enabled(),
                "verification_enabled": sess.trust_verification_enabled(),
                "collection_strategy": if sess.link_dead_code() { "eager" } else { "lazy" },
                "optimization": format!("{:?}", sess.opts.optimize),
                "incremental": sess.opts.incremental.is_some(),
                "codegen_requested": sess.opts.output_types.should_codegen() && !sess.opts.unstable_opts.no_codegen,
                "identity_scheme": "rustc-stable-mono-item-fingerprint-128-diagnostic-only",
                "dependency_identity_scheme": "typed-instances-and-vtables-stable-128-allocations-invocation-local",
                "dependency_scope": "existing-collector-visits-including-cached-query-results",
                "eager_const_root_scope": "successful-existing-eager-free-const-value-scans",
                "eager_const_root_identity_scheme": "rustc-def-path-hash-128-diagnostic-only",
                "unmeasured": UNMEASURED,
            }),
        ),
    );
    sess.with_trust_compiler_state::<State, _>(|state| {
        *state = State { output: Some(output), ..State::default() };
    });
}

// Includes the COMPLETE InstanceKind and generic args, unlike DefIdSet and a
// name/arity key. This compiler fingerprint is not a cryptographic certificate
// identity. Its collisions/duplicate rows are refused within this observation.
fn identity(tcx: TyCtxt<'_>, item: MonoItem<'_>) -> String {
    tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        item.stable_hash(&mut hcx, &mut hasher);
        let fingerprint: Fingerprint = hasher.finish();
        fingerprint.to_le_bytes().iter().map(|byte| format!("{byte:02x}")).collect()
    })
}

pub(crate) fn roots(tcx: TyCtxt<'_>, items: &[MonoItem<'_>]) {
    if tcx.sess.opts.unstable_opts.trust_instance_census.is_none() {
        return;
    }
    let mut ids = items.iter().map(|item| identity(tcx, *item)).collect::<Vec<_>>();
    ids.sort();
    // collect_roots already deduplicates MonoItems. Do not hide a fingerprint
    // collision or repeated observer population by silently deduplicating here.
    if ids.windows(2).any(|pair| pair[0] == pair[1]) {
        tcx.dcx().fatal("Rust instance census: duplicate root identity");
    }
    require(
        tcx.sess,
        tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            if state.output.is_none() || state.roots.is_some() {
                return Err("missing begin or duplicate root observation".into());
            }
            state.roots = Some(ids);
            Ok(())
        }),
    );
}

fn instance_kind(kind: InstanceKind<'_>) -> &'static str {
    match kind {
        InstanceKind::Item(_) => "item",
        InstanceKind::Intrinsic(_) => "intrinsic",
        // Upstream 1.101: LLVM intrinsics are their own instance kind.
        InstanceKind::LlvmIntrinsic(_) => "llvm-intrinsic",
        InstanceKind::Virtual(..) => "virtual",
        InstanceKind::Shim(shim) => match shim {
            ShimKind::VTable(_) => "shim-vtable",
            ShimKind::Reify(..) => "shim-reify",
            ShimKind::FnPtr(..) => "shim-fn-ptr",
            ShimKind::ClosureOnce { .. } => "shim-closure-once",
            ShimKind::ConstructCoroutineInClosure { .. } => "shim-construct-coroutine",
            ShimKind::ThreadLocal(_) => "shim-thread-local",
            ShimKind::FutureDropPoll(..) => "shim-future-drop-poll",
            ShimKind::DropGlue(..) => "shim-drop-glue",
            ShimKind::Clone(..) => "shim-clone",
            ShimKind::FnPtrAsPtr(..) | ShimKind::FnPtrFromPtr(..) => "shim-fn-ptr-addr",
            ShimKind::AsyncDropGlueCtor(..) => "shim-async-drop-ctor",
            ShimKind::AsyncDropGlue(..) => "shim-async-drop",
        },
    }
}

pub(crate) fn snapshot<'tcx>(
    tcx: TyCtxt<'tcx>,
    items: &[MonoItem<'tcx>],
    usage: &UsageMap<'tcx>,
    cgus: &[CodegenUnit<'tcx>],
) {
    let sess = tcx.sess;
    if sess.opts.unstable_opts.trust_instance_census.is_none() {
        return;
    }
    let mut rows = BTreeMap::new();
    let mut edges = BTreeSet::new();
    for item in items {
        let id = identity(tcx, *item);
        let def = item.def_id();
        let (kind, detail, args) = match item {
            MonoItem::Fn(instance) => (
                instance_kind(instance.def),
                format!("{:?}", instance.def),
                format!("{:?}", instance.args),
            ),
            MonoItem::Static(_) => ("static", String::new(), String::new()),
            MonoItem::GlobalAsm(_) => ("global-asm", String::new(), String::new()),
        };
        let row = json!({
            "id": id, "kind": kind, "instance_detail": detail, "generic_args": args,
            "def": tcx.def_path_debug_str(def), "def_path_hash": format!("{:?}", tcx.def_path_hash(def)),
            "def_kind": format!("{:?}", tcx.def_kind(def)), "definition_is_local": def.is_local(),
            "symbol": item.symbol_name(tcx).to_string(),
        });
        if rows.insert(id.clone(), row).is_some() {
            sess.dcx().fatal("Rust instance census: duplicate mono-item identity");
        }
        let used =
            require(sess, usage.used_map.get(item).ok_or_else(|| "missing usage-map owner".into()));
        for target in used {
            edges.insert((id.clone(), identity(tcx, *target)));
        }
    }
    let mut units = BTreeMap::new();
    let mut placed = BTreeSet::new();
    for cgu in cgus {
        let mut placements = BTreeMap::new();
        for (item, data) in cgu.items() {
            let id = identity(tcx, *item);
            placed.insert(id.clone());
            if placements
                .insert(
                    id.clone(),
                    json!({
                        "id": id, "linkage": format!("{:?}", data.linkage),
                        "visibility": format!("{:?}", data.visibility), "inlined": data.inlined,
                    }),
                )
                .is_some()
            {
                sess.dcx().fatal("Rust instance census: duplicate CGU placement");
            }
        }
        if units
            .insert(cgu.name().to_string(), placements.into_values().collect::<Vec<_>>())
            .is_some()
        {
            sess.dcx().fatal("Rust instance census: duplicate codegen unit");
        }
    }
    let ids = rows.keys().cloned().collect::<BTreeSet<_>>();
    if !placed.is_subset(&ids) || edges.iter().any(|(a, b)| !ids.contains(a) || !ids.contains(b)) {
        sess.dcx().fatal("Rust instance census: collector/usage/CGU populations disagree");
    }
    // The partitioner may leave an inline-only collector root unplaced when
    // no globally shared item reaches it. Preserve it in the denominator;
    // collection and actual CGU placement are different observed populations.
    let unplaced = ids.difference(&placed).cloned().collect::<Vec<_>>();
    let count = rows.len();
    let dependencies = dependencies::snapshot(tcx, items, usage);
    require(
        sess,
        sess.with_trust_compiler_state::<State, _>(|state| {
            let roots =
                state.roots.as_ref().ok_or_else(|| "missing root observation".to_owned())?;
            if roots.iter().any(|root| !ids.contains(root)) || state.snapshot.is_some() {
                return Err("unknown root or duplicate snapshot".into());
            }
            let output = state.output.as_mut().ok_or_else(|| "missing begin".to_owned())?;
            let digest = record(
                output,
                &json!({
                    "schema": SCHEMA, "event": "mono_snapshot", "item_count": count,
                    "items": rows.into_values().collect::<Vec<_>>(), "roots": roots,
                "usage_edges": edges.into_iter().collect::<Vec<_>>(), "codegen_units": units,
                "unplaced_items": unplaced,
                "dependency_node_count": dependencies.nodes.len(),
                "dependency_owner_count": dependencies.owners.len(),
                "dependency_occurrence_count": dependencies.occurrences.len(),
                "dependency_nodes": dependencies.nodes,
                "dependency_owners": dependencies.owners,
                "dependency_occurrences": dependencies.occurrences,
                "eager_const_root_owner_count": dependencies.eager_const_owners.len(),
                "eager_const_root_occurrence_count": dependencies.eager_const_occurrences.len(),
                "eager_const_root_owners": dependencies.eager_const_owners,
                "eager_const_root_occurrences": dependencies.eager_const_occurrences,
                }),
            )?;
            state.snapshot = Some((count, digest));
            Ok(())
        }),
    );
}

/// After the backend's synchronous collection, but not after linking. Consumers
/// must still require exit 0. Metadata-only compiles remain explicitly unmeasured;
/// this diagnostic does not trigger collection and change their semantics.
pub fn complete(tcx: TyCtxt<'_>) {
    let sess = tcx.sess;
    if sess.opts.unstable_opts.trust_instance_census.is_none()
        || sess.dcx().has_errors_or_delayed_bugs().is_some()
    {
        return;
    }
    let mut sources = BTreeMap::new();
    for source in sess.source_map().files().iter() {
        if source.src.is_none() {
            continue;
        }
        let FileName::Real(real) = &source.name else { continue };
        let path = require(
            sess,
            real.local_path().ok_or_else(|| "local source path missing".into()).and_then(absolute),
        );
        let hash = require(
            sess,
            source
                .checksum_hash
                .filter(|hash| hash.kind == SourceFileHashAlgorithm::Sha256)
                .ok_or_else(|| format!("missing consumption-time SHA-256 for {path}")),
        );
        // Two conflicting loaded versions cannot collapse to a single map entry.
        if let Some(previous) = sources.insert(path, hash.to_string())
            && previous != hash.to_string()
        {
            sess.dcx().fatal("Rust instance census: conflicting loaded source hashes");
        }
    }
    require(
        sess,
        sess.with_trust_compiler_state::<State, _>(|state| {
            let mut output = state.output.take().ok_or_else(|| "missing begin".to_owned())?;
            let (status, count, digest) = match state.snapshot.take() {
                Some((count, digest)) => ("collector_observed", Some(count), Some(digest)),
                None => ("unmeasured", None, None),
            };
            record(
                &mut output,
                &json!({
                    "schema": SCHEMA, "event": "complete", "status": status,
                    "item_count": count, "snapshot_sha256": digest,
                    "sources": sources, "unmeasured": UNMEASURED,
                    "whole_program_complete": false,
                }),
            )?;
            output.sync_all().map_err(|error| error.to_string())
        }),
    );
}
