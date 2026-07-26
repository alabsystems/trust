// expr_fold_corpus — RUNGS C + D of the structural-fold lane
// (docs/design/2026-07-10-structural-fold-lane.md §5): the DEPTHLESS (rung C)
// and DEPTH-THREADING (rung D) memoized Expr folders. REAL trustc MIR dumps
// (never hand-transcribed — see fixtures/expr-fold-corpus/PROVENANCE.md) of
// clean-kernel's eight `ExprFolderOpt` folder impls + the full generic
// dispatch SCC, through the production pipeline.
//
// What this pins (rung C, unchanged):
//   * `FVarSubst::fold_expr_opt` recognizes (memo idiom peeled, 33-ctor
//     flattened TExpr table from the dump's own type info) and its
//     leaf-parametric kernel witness + memoAdequate mint modulo 3; the row
//     certifies FULLY_FAITHFUL via trust-ir on the production gate.
//   * `LevelParamSubst{,Slice}::fold_expr_opt` recognize the SAME shape but
//     stay HONESTLY hostage (`leaf_uncertified`): their `fold_sort_opt` /
//     `fold_const_opt` overrides (Level::substitute_map, Iterator::collect)
//     are out of every lane's reach until rung E.
//   * ADVERSARIAL MEMO PROBES: put-of-a-non-result, get/put key drift (expr
//     operand and depth literal), partial cached-value use, a second memo
//     touch — each a NAMED decline on doctored MIR.
//   * FORGERY PROBES: swapped merge children / wrong ctor / wrong merge
//     arity / guard-polarity swap claims against the kernel witness are
//     KernelRejected.
//
// What this pins (rung D, new):
//   * The five DEPTH-THREADING folders recognize as SCC UNITS — wrapper +
//     `fold_binder_body_opt` save/inc/call/restore override jointly:
//     `Instantiator`/`MultiInstantiator` (depth field 1), `Lifter`/`Lowerer`
//     (depth field 0, the `start` counter), all via the `FoldMemo` depth-key
//     idiom, and `Abstractor` (depth field 1) via the INLINE-HashMap memo
//     idiom. Binder marks (Lam/Pi/Let body, CubicalPathLam body,
//     ZFCComprehension pred, zfc Separation/Replacement) are read off the
//     REAL dispatch MIR.
//   * The DEPTH witness (`foldD`/`memoFoldD` + per-ctor theorems +
//     `memoAdequateD`) mints modulo 3 on the real 33-ctor table.
//   * PRODUCTION-GATE verdicts: Abstractor, Lifter, and Instantiator flip
//     FULLY_FAITHFUL — BOTH SCC rows each (wrapper + binder-body, one joint
//     certificate). Instantiator's leaf also certifies on its exact
//     ordering-dispatch lane. MultiInstantiator / Lowerer recognize but stay
//     HONESTLY hostage to their uncertifiable `fold_bvar_opt` overrides
//     (MultiInstantiator's `depth + n` overflow is real; Lowerer's REACHABLE
//     debug-assert panic arm) — the module-doc leaf-honesty decision: NO
//     opaque-total-slot shortcut for partial leaves.
//   * DEPTH-SPECIFIC PROBES: missing restore / restore-of-wrong-value /
//     extra depth write / stale-depth put key / binder-field mismatch /
//     inline insert-key drift / inline return-of-clone — each a NAMED
//     decline on doctored REAL MIR; binder-mark forgeries against the depth
//     witness (IH at `d` instead of `dsucc d`) are KernelRejected.
//
// Run with:
//   RUSTC_BOOTSTRAP=1 cargo test -p trust-clean --manifest-path crates/Cargo.toml \
//       --test expr_fold_corpus -- --nocapture
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use trust_clean::diagnose_expr_fold_scc;
use trust_clean::trustir_anchor::RefinementVerdict;
use trust_clean::trustir_fold::DumpBodies;
use trust_clean::trustir_fold_expr::{
    ExprFoldDecline, LeafResolution, LeafSlot, SemExprFold, TArm, TCtor,
    check_expr_fold_refinement_cached, check_expr_fold_refinement_cached_d,
    check_expr_fold_refinement_claimed, check_expr_fold_refinement_claimed_d, probe_arm_rhs,
    probe_arm_rhs_d, sem_binder_body_row_of, sem_expr_fold_shape_of,
};
use trust_types::{CallableDefPathHash, CallableKind, ConstValue, Operand, VerifiableFunction};

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/expr-fold-corpus")
}

const CORPUS_JSON_COUNT: usize = 124;

/// One immutable, hash-checked corpus generation. The root row and every
/// co-member used by a recognition attempt are cloned from this same snapshot;
/// no recognition can accidentally combine two individually valid generations
/// when the publisher commits between filesystem reads.
struct CorpusSnapshot {
    manifest: BTreeMap<String, String>,
    toolchain: BTreeMap<String, (String, String)>,
    functions_by_file: BTreeMap<String, VerifiableFunction>,
    bodies: DumpBodies,
}

impl CorpusSnapshot {
    fn open(dir: &Path) -> Result<Self, String> {
        Self::open_with_manifest_hook(dir, || {})
    }

    fn open_with_manifest_hook(
        dir: &Path,
        after_manifest_read: impl FnOnce(),
    ) -> Result<Self, String> {
        let manifest_path = dir.join("MANIFEST.sha256");
        let manifest_bytes = std::fs::read(&manifest_path)
            .map_err(|error| format!("read {}: {error}", manifest_path.display()))?;
        let manifest_text = std::str::from_utf8(&manifest_bytes)
            .map_err(|error| format!("{} is not UTF-8: {error}", manifest_path.display()))?;
        let mut manifest = BTreeMap::new();
        let mut previous_file: Option<&str> = None;
        for (line_number, line) in manifest_text.lines().enumerate() {
            let (hash, file) = line
                .split_once('\t')
                .ok_or_else(|| format!("manifest line {} is not TSV", line_number + 1))?;
            if hash.len() != 64
                || !hash.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
            {
                return Err(format!("manifest line {} has a non-SHA256 digest", line_number + 1));
            }
            if file.contains('\t')
                || !file.ends_with(".json")
                || Path::new(file).file_name().and_then(|name| name.to_str()) != Some(file)
            {
                return Err(format!(
                    "manifest line {} has an unsafe/non-JSON filename",
                    line_number + 1
                ));
            }
            if previous_file.is_some_and(|previous| previous >= file) {
                return Err(format!(
                    "manifest line {} is duplicate or not bytewise sorted",
                    line_number + 1
                ));
            }
            if manifest.insert(file.to_string(), hash.to_string()).is_some() {
                return Err(format!("duplicate manifest filename {file}"));
            }
            previous_file = Some(file);
        }
        if manifest.len() != CORPUS_JSON_COUNT {
            return Err(format!(
                "corpus manifest has {} entries, want {CORPUS_JSON_COUNT}",
                manifest.len()
            ));
        }

        let toolchain_path = dir.join("TOOLCHAIN.sha256");
        let toolchain_bytes = std::fs::read(&toolchain_path)
            .map_err(|error| format!("read {}: {error}", toolchain_path.display()))?;
        let toolchain_text = std::str::from_utf8(&toolchain_bytes)
            .map_err(|error| format!("{} is not UTF-8: {error}", toolchain_path.display()))?;
        let expected_labels = [
            "cargo",
            "trustc",
            "jq",
            "python3",
            "rustc_wrapper",
            "regeneration_script",
            "corpus_manifest",
        ];
        let lines = toolchain_text.lines().collect::<Vec<_>>();
        if lines.len() != expected_labels.len() {
            return Err(format!(
                "toolchain manifest has {} entries, want {}",
                lines.len(),
                expected_labels.len()
            ));
        }
        let mut toolchain = BTreeMap::new();
        for (line_number, (line, expected_label)) in
            lines.into_iter().zip(expected_labels).enumerate()
        {
            let fields = line.split('\t').collect::<Vec<_>>();
            let [hash, label, version] = fields.as_slice() else {
                return Err(format!("toolchain line {} is not three-field TSV", line_number + 1));
            };
            if hash.len() != 64
                || !hash.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
            {
                return Err(format!("toolchain line {} has a non-SHA256 digest", line_number + 1));
            }
            if *label != expected_label || version.is_empty() {
                return Err(format!(
                    "toolchain line {} identity drift: got {label:?}/{version:?}, want {expected_label:?}",
                    line_number + 1
                ));
            }
            if toolchain
                .insert(label.to_string(), (hash.to_string(), version.to_string()))
                .is_some()
            {
                return Err(format!("duplicate toolchain label {label}"));
            }
        }
        let mut repository_files = Vec::new();
        for (label, path, version) in [
            ("rustc_wrapper", dir.join("regenerate-rustc-wrapper.sh"), "repository-script"),
            ("regeneration_script", dir.join("regenerate.sh"), "repository-script"),
        ] {
            let bytes = std::fs::read(&path)
                .map_err(|error| format!("read pinned {label} {}: {error}", path.display()))?;
            let actual = trust_types::stable_sha256_hex(&bytes);
            let Some((expected, recorded_version)) = toolchain.get(label) else {
                return Err(format!("missing toolchain label {label}"));
            };
            if &actual != expected || recorded_version != version {
                return Err(format!(
                    "{label} provenance drift: hash {actual}, recorded {expected}/{recorded_version}"
                ));
            }
            repository_files.push((label, path, bytes));
        }
        let actual_manifest_hash = trust_types::stable_sha256_hex(&manifest_bytes);
        let Some((recorded_manifest_hash, recorded_manifest_name)) =
            toolchain.get("corpus_manifest")
        else {
            return Err("missing corpus_manifest toolchain entry".to_string());
        };
        if recorded_manifest_hash != &actual_manifest_hash
            || recorded_manifest_name != "MANIFEST.sha256"
        {
            return Err(format!(
                "toolchain/corpus manifest mismatch: got {recorded_manifest_hash}/{recorded_manifest_name}, want {actual_manifest_hash}/MANIFEST.sha256"
            ));
        }

        after_manifest_read();

        let raw_files = std::fs::read_dir(dir)
            .map_err(|error| format!("read corpus directory {}: {error}", dir.display()))?
            .map(|entry| entry.map_err(|error| error.to_string()))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .filter_map(|entry| {
                let path = entry.path();
                (path.extension().and_then(|extension| extension.to_str()) == Some("json"))
                    .then(|| entry.file_name().to_string_lossy().into_owned())
            })
            .collect::<BTreeSet<_>>();
        let manifested_files = manifest.keys().cloned().collect::<BTreeSet<_>>();
        if raw_files != manifested_files {
            return Err("raw corpus JSON inventory differs from the manifest".to_string());
        }

        let mut functions_by_file = BTreeMap::new();
        let mut bodies = DumpBodies::new();
        for (file, expected_hash) in &manifest {
            let path = dir.join(file);
            let bytes = std::fs::read(&path)
                .map_err(|error| format!("read {}: {error}", path.display()))?;
            let actual_hash = trust_types::stable_sha256_hex(&bytes);
            if &actual_hash != expected_hash {
                return Err(format!(
                    "corpus generation/hash drift for {}: got {actual_hash}, want {expected_hash}",
                    path.display()
                ));
            }
            let function: VerifiableFunction =
                trust_clean::prove::decode_verifiable_function_with_authenticated_legacy_metadata(
                    &bytes,
                )
                .map_err(|error| format!("parse {file}: {error}"))?;
            let owner = function.def_path.clone();
            if bodies.insert(owner.clone(), function.clone()).is_some() {
                return Err(format!("duplicate corpus def_path owner {owner}"));
            }
            functions_by_file.insert(file.clone(), function);
        }
        if bodies.len() != CORPUS_JSON_COUNT {
            return Err(format!(
                "corpus has {} unique owners, want {CORPUS_JSON_COUNT}",
                bodies.len()
            ));
        }

        // The files above are already owned by this snapshot, so a commit after
        // this comparison is harmless. A commit during the batch is rejected.
        let manifest_after = std::fs::read(&manifest_path)
            .map_err(|error| format!("re-read {}: {error}", manifest_path.display()))?;
        if manifest_after != manifest_bytes {
            return Err("corpus manifest changed while building one snapshot".to_string());
        }
        let toolchain_after = std::fs::read(&toolchain_path)
            .map_err(|error| format!("re-read {}: {error}", toolchain_path.display()))?;
        if toolchain_after != toolchain_bytes {
            return Err("toolchain manifest changed while building one snapshot".to_string());
        }
        for (label, path, before) in repository_files {
            let after = std::fs::read(&path)
                .map_err(|error| format!("re-read pinned {label} {}: {error}", path.display()))?;
            if after != before {
                return Err(format!("pinned {label} changed while building one snapshot"));
            }
        }
        Ok(Self { manifest, toolchain, functions_by_file, bodies })
    }
}

fn corpus_snapshot() -> &'static CorpusSnapshot {
    static CORPUS: OnceLock<CorpusSnapshot> = OnceLock::new();
    CORPUS.get_or_init(|| {
        CorpusSnapshot::open(&corpus_dir()).unwrap_or_else(|error| panic!("load corpus: {error}"))
    })
}

fn load(name: &str) -> VerifiableFunction {
    let file = format!("{name}.json");
    corpus_snapshot()
        .functions_by_file
        .get(&file)
        .unwrap_or_else(|| panic!("unmanifested corpus row {file}"))
        .clone()
}

fn all_bodies() -> DumpBodies {
    corpus_snapshot().bodies.clone()
}

const FVS_ROW: &str =
    "<expr__subst__FVarSubst<'_> as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";

fn recognize(row_file: &str) -> Result<SemExprFold, ExprFoldDecline> {
    let func = load(row_file);
    let bodies = all_bodies();
    sem_expr_fold_shape_of(&func, &bodies)
}

#[test]
fn corpus_toolchain_provenance_is_current_and_complete() {
    let snapshot = corpus_snapshot();
    assert_eq!(snapshot.manifest.len(), CORPUS_JSON_COUNT);
    assert_eq!(snapshot.toolchain.len(), 7);
}

fn callable_call_arg_mut<'a>(
    func: &'a mut VerifiableFunction,
    callable_path: &str,
) -> &'a mut ConstValue {
    for block in &mut func.body.blocks {
        let trust_types::Terminator::Call { args, .. } = &mut block.terminator else {
            continue;
        };
        for arg in args {
            let Operand::Constant(value) = arg else { continue };
            if matches!(value, ConstValue::CallableItem { def_path, .. } if def_path == callable_path)
            {
                return value;
            }
        }
    }
    panic!("missing callable operand {callable_path} in {}", func.def_path)
}

fn assert_callable_drift_declines(bodies: &DumpBodies, expected_name: &str) {
    let decline = sem_expr_fold_shape_of(&load(FVS_ROW), bodies)
        .expect_err("callable-identity drift must fail closed");
    assert_eq!(decline.name(), expected_name, "{decline:?}");
}

/// Even two valid manifests for the same files are distinct publication
/// generations. Force each commit-boundary manifest and one pinned repository
/// script to change after the snapshot captures it; the loader must reject the
/// batch instead of returning a root/co-member/provenance mix.
#[test]
fn corpus_snapshot_rejects_manifest_swap_during_batch() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let temp = std::env::temp_dir()
        .join(format!("trust-expr-fold-snapshot-{}-{nonce}", std::process::id()));
    std::fs::create_dir(&temp).expect("create snapshot adversary directory");
    for file in corpus_snapshot().manifest.keys() {
        let source = corpus_dir().join(file);
        let destination = temp.join(file);
        std::fs::hard_link(&source, &destination)
            .or_else(|_| std::fs::copy(&source, &destination).map(|_| ()))
            .unwrap_or_else(|error| panic!("stage {}: {error}", source.display()));
    }
    let manifest_path = temp.join("MANIFEST.sha256");
    std::fs::copy(corpus_dir().join("MANIFEST.sha256"), &manifest_path)
        .expect("stage snapshot manifest");
    let toolchain_path = temp.join("TOOLCHAIN.sha256");
    std::fs::copy(corpus_dir().join("TOOLCHAIN.sha256"), &toolchain_path)
        .expect("stage toolchain manifest");
    for script in ["regenerate.sh", "regenerate-rustc-wrapper.sh"] {
        std::fs::copy(corpus_dir().join(script), temp.join(script))
            .unwrap_or_else(|error| panic!("stage {script}: {error}"));
    }

    let result = CorpusSnapshot::open_with_manifest_hook(&temp, || {
        let text = std::fs::read_to_string(&manifest_path).expect("read staged manifest");
        let mut lines = text.lines().collect::<Vec<_>>();
        lines.reverse();
        std::fs::write(&manifest_path, format!("{}\n", lines.join("\n")))
            .expect("swap staged manifest");
    });
    let error = match result {
        Ok(_) => panic!("manifest swap produced an accepted corpus snapshot"),
        Err(error) => error,
    };
    assert!(error.contains("manifest changed"), "unexpected decline: {error}");

    std::fs::copy(corpus_dir().join("MANIFEST.sha256"), &manifest_path)
        .expect("restore snapshot manifest");
    std::fs::copy(corpus_dir().join("TOOLCHAIN.sha256"), &toolchain_path)
        .expect("restore toolchain manifest");
    let result = CorpusSnapshot::open_with_manifest_hook(&temp, || {
        let mut text = std::fs::read_to_string(&toolchain_path).expect("read staged toolchain");
        text.push('\n');
        std::fs::write(&toolchain_path, text).expect("swap staged toolchain manifest");
    });
    let error = match result {
        Ok(_) => panic!("toolchain swap produced an accepted corpus snapshot"),
        Err(error) => error,
    };
    assert!(error.contains("toolchain manifest changed"), "unexpected decline: {error}");

    std::fs::copy(corpus_dir().join("TOOLCHAIN.sha256"), &toolchain_path)
        .expect("restore toolchain manifest after swap probe");
    let script_path = temp.join("regenerate.sh");
    let result = CorpusSnapshot::open_with_manifest_hook(&temp, || {
        let mut bytes = std::fs::read(&script_path).expect("read staged regeneration script");
        bytes.push(b'\n');
        std::fs::write(&script_path, bytes).expect("swap staged regeneration script");
    });
    let error = match result {
        Ok(_) => panic!("script swap produced an accepted corpus snapshot"),
        Err(error) => error,
    };
    assert!(error.contains("pinned regeneration_script changed"), "unexpected decline: {error}");
    std::fs::remove_dir_all(&temp).expect("remove snapshot adversary directory");
}

/// The regenerated extraction must carry exactly the 16 audited callable
/// identities (30 occurrences): 14 local constructor closures, App's fn item,
/// and Arc::new at all 15 merge-pick positions. This is an explicit table
/// exhaustion gate, not merely an incidental consequence of recognition.
#[test]
fn callable_identity_table_is_exact_and_exhaustive() {
    fn collect(
        value: &serde_json::Value,
        counts: &mut std::collections::BTreeMap<(String, String, String, String), usize>,
    ) {
        match value {
            serde_json::Value::Object(object) => {
                if let Some(serde_json::Value::Object(item)) = object.get("CallableItem") {
                    let field = |name: &str| {
                        item.get(name)
                            .and_then(serde_json::Value::as_str)
                            .unwrap_or_else(|| panic!("CallableItem.{name}"))
                            .to_string()
                    };
                    let hash = item
                        .get("def_path_hash")
                        .and_then(serde_json::Value::as_object)
                        .expect("CallableItem.def_path_hash");
                    let hash_field = |name: &str| {
                        hash.get(name)
                            .and_then(serde_json::Value::as_str)
                            .unwrap_or_else(|| panic!("CallableItem.def_path_hash.{name}"))
                            .to_string()
                    };
                    *counts
                        .entry((
                            field("def_path"),
                            field("kind"),
                            hash_field("stable_crate_id"),
                            hash_field("local_hash"),
                        ))
                        .or_default() += 1;
                }
                for child in object.values() {
                    collect(child, counts);
                }
            }
            serde_json::Value::Array(values) => {
                for child in values {
                    collect(child, counts);
                }
            }
            _ => {}
        }
    }

    let mut actual = std::collections::BTreeMap::new();
    for function in all_bodies().values() {
        collect(&serde_json::to_value(function).expect("serialize dump"), &mut actual);
    }
    let mut expected = std::collections::BTreeMap::new();
    let mut pin = |count: usize, path: &str, kind: &str, stable: &str, local: &str| {
        expected.insert(
            (path.to_string(), kind.to_string(), stable.to_string(), local.to_string()),
            count,
        );
    };
    pin(1, "expr::kind::ExprKind::App", "fn_def", "7508ca85e6100c00", "bc8c212df299ed62");
    for (owner, closure, local) in [
        ("fold_expr_opt_inner_full", 5, "6b7b4c5cfd70ffdd"),
        ("fold_expr_opt_extensions", 0, "5fdcc31917fb4403"),
        ("fold_expr_opt_extensions", 1, "e564c15855b3eedd"),
        ("fold_expr_opt_extensions", 2, "6d644c3f403ba3dc"),
        ("fold_expr_opt_extensions", 3, "f62ee26e807b71f2"),
        ("fold_expr_opt_extensions", 4, "57da621320568a7c"),
        ("fold_expr_opt_extensions", 5, "73d8d0b61d768ad6"),
        ("fold_expr_opt_zfc", 0, "4de23e93e74105f5"),
        ("fold_expr_opt_zfc", 1, "f4556b7b11df89e4"),
        ("fold_expr_opt_zfc", 2, "acc35f8aa986b6c6"),
        ("fold_zfc_set_expr_opt", 0, "249a80707f2bb911"),
        ("fold_zfc_set_expr_opt", 3, "5cf869889fb25a13"),
        ("fold_zfc_set_expr_opt", 4, "83215fd4b3fd48f4"),
        ("fold_zfc_set_expr_opt", 9, "568dd947806e692e"),
    ] {
        pin(
            1,
            &format!("expr::visitor::opt::ExprFolderOpt::{owner}::{{closure#{closure}}}"),
            "closure",
            "7508ca85e6100c00",
            local,
        );
    }
    pin(15, "std::sync::Arc::<T>::new", "fn_def", "9d72b10b12841225", "e31a916e7093729f");
    assert_eq!(actual.values().sum::<usize>(), 30);
    assert_eq!(actual, expected);

    let bodies = all_bodies();
    for (path, expected_hash) in [
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full::{closure#5}",
            "b331095a3a727ace9235cc5212be3940ae0d3f867077d4e8656904bc4aad78f6",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#0}",
            "cadac6b6f1303466d22529d2c63443b57606adcae2fdea48a95b2e9e970ffd04",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#1}",
            "c2694fbf36863dec2022e5cf7e4c57378698d5b9138a29d3f58590053c51c001",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#2}",
            "70f1df0d0f7aac15a36d5597da9f60bac41f9a7ff95fc26b0bdbee56251d52a2",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#3}",
            "b08f89bb120a64755aef6fc1aa89e61f47671f7d6ae473a5817f90d1a5b53c25",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#4}",
            "5fbdd97953675930e72f57a343a2cc051abfd391ede3d798ef65aea0b8c3f3b2",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#5}",
            "825f339ef2d305b30147b6eda666a45c3976ccfe167e0b14db618ea0b7236712",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#0}",
            "8897f37073ffa74c4f2d617ff82eccf57bef04fe5455fd3dd76a289b1e3fb411",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#1}",
            "fdefa28216db730415139536f84a8e23b030d0bca8c89f669913df13fa5cf2c9",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_zfc::{closure#2}",
            "9e6d2ff4bbe388fde7c95a6ec565629efbb5862c11fa9968182ccf5a396e9fc1",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#0}",
            "08c88099c46a7a6d28ea2b1c754415fecfbdb09762eb4af00e9b66a56178040a",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#3}",
            "5264cc84b793060a7386453510338dd508157f0e66944adee554da694e227150",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#4}",
            "a90669d59b46f70a5cab76e19d9ad1783566af78d311fb606e7ef25b56b6c42f",
        ),
        (
            "expr::visitor::opt::ExprFolderOpt::fold_zfc_set_expr_opt::{closure#9}",
            "0dbd990ce9a09aa8f37e30f061666d90b9928ed77d59d093aa7dbf1c46cc9d1c",
        ),
    ] {
        assert_eq!(
            bodies.get(path).unwrap_or_else(|| panic!("missing {path}")).content_hash(),
            expected_hash,
            "callable body identity drift for {path}"
        );
    }
}

/// Callable identity is conjunctive: legacy Unit, wrong path/kind, either
/// DefPathHash component, or a complete same-shaped callback substitution all
/// decline. Arc::new is pinned separately from the App constructor fn item.
#[test]
fn callable_identity_adversaries_decline() {
    const EXTENSIONS: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions";
    const EXT_2: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#2}";
    const EXT_3: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#3}";
    const INNER_FULL: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full";
    const APP: &str = "expr::kind::ExprKind::App";

    let mut bodies = all_bodies();
    *callable_call_arg_mut(bodies.get_mut(INNER_FULL).expect("inner_full"), APP) = ConstValue::Unit;
    assert_callable_drift_declines(&bodies, "arm_shape");

    let mut bodies = all_bodies();
    let ConstValue::CallableItem { def_path, .. } =
        callable_call_arg_mut(bodies.get_mut(EXTENSIONS).expect("extensions"), EXT_2)
    else {
        unreachable!()
    };
    *def_path = EXT_3.to_string();
    assert_callable_drift_declines(&bodies, "arm_shape");

    let mut bodies = all_bodies();
    let ConstValue::CallableItem { kind, .. } =
        callable_call_arg_mut(bodies.get_mut(EXTENSIONS).expect("extensions"), EXT_2)
    else {
        unreachable!()
    };
    *kind = CallableKind::FnDef;
    assert_callable_drift_declines(&bodies, "arm_shape");

    let mut bodies = all_bodies();
    let ConstValue::CallableItem { def_path_hash, .. } =
        callable_call_arg_mut(bodies.get_mut(EXTENSIONS).expect("extensions"), EXT_2)
    else {
        unreachable!()
    };
    *def_path_hash =
        CallableDefPathHash::new(def_path_hash.stable_crate_id(), 0xf62e_e26e_807b_71f2);
    assert_callable_drift_declines(&bodies, "arm_shape");

    let mut bodies = all_bodies();
    let ConstValue::CallableItem { def_path_hash, .. } =
        callable_call_arg_mut(bodies.get_mut(EXTENSIONS).expect("extensions"), EXT_2)
    else {
        unreachable!()
    };
    *def_path_hash = CallableDefPathHash::new(0x9d72_b10b_1284_1225, def_path_hash.local_hash());
    assert_callable_drift_declines(&bodies, "arm_shape");

    let mut bodies = all_bodies();
    let swapped =
        callable_call_arg_mut(bodies.get_mut(EXTENSIONS).expect("extensions"), EXT_3).clone();
    *callable_call_arg_mut(bodies.get_mut(EXTENSIONS).expect("extensions"), EXT_2) = swapped;
    assert_callable_drift_declines(&bodies, "arm_shape");

    let mut bodies = all_bodies();
    let app = callable_call_arg_mut(bodies.get_mut(INNER_FULL).expect("inner_full"), APP).clone();
    *callable_call_arg_mut(
        bodies.get_mut("expr::visitor::opt::merge2").expect("merge2"),
        "std::sync::Arc::<T>::new",
    ) = app;
    assert_callable_drift_declines(&bodies, "co_member_drift");
}

/// Constructor-body credibility is closed independently of the callsite
/// identity. Whole-body hashes reject any non-capturing closure drift before
/// the structural walker; the walker itself pins arity, RawParam→Arc::new
/// provenance, enum/value domain, plain-call flags/destinations, acyclic
/// control flow, and final output. Capturing closures receive the same strict
/// structural checks even though their identity is carried by the aggregate.
#[test]
fn callable_ctor_body_adversaries_decline() {
    const EXT_MAP: &str =
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#1}";
    const EXT_MERGE: &str =
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_extensions::{closure#2}";
    const CAPTURED_MERGE: &str =
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full::{closure#0}";
    const CAPTURED_MAP: &str =
        "expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full::{closure#3}";

    let mut bodies = all_bodies();
    bodies.get_mut(EXT_MERGE).expect("extension closure").body.arg_count -= 1;
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(EXT_MAP).expect("map closure");
    let mut doctored = false;
    for block in &mut closure.body.blocks {
        for statement in &mut block.stmts {
            if let trust_types::Statement::Assign {
                rvalue: trust_types::Rvalue::Aggregate(_, operands),
                ..
            } = statement
                && let Some(operand) = operands.first_mut()
            {
                *operand = Operand::Copy(trust_types::Place::local(2));
                doctored = true;
            }
        }
    }
    assert!(doctored, "doctor must bypass the Arc::new result");
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(EXT_MAP).expect("map closure");
    let mut doctored = false;
    for block in &mut closure.body.blocks {
        if let trust_types::Terminator::Call { func, .. } = &mut block.terminator
            && func == "std::sync::Arc::<T>::new"
        {
            *func = "std::sync::Arc::forged::new".into();
            doctored = true;
        }
    }
    assert!(doctored, "doctor must hit Arc::new");
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(EXT_MAP).expect("map closure");
    let mut doctored = false;
    for block in &mut closure.body.blocks {
        if let trust_types::Terminator::Call { func, is_foreign, .. } = &mut block.terminator
            && func == "std::sync::Arc::<T>::new"
        {
            *is_foreign = true;
            doctored = true;
        }
    }
    assert!(doctored, "doctor must hit Arc::new flags");
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(EXT_MERGE).expect("merge closure");
    let return_block = closure
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Return))
        .expect("return block");
    return_block.terminator = trust_types::Terminator::Goto(trust_types::BlockId(0));
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(EXT_MERGE).expect("merge closure");
    let return_block = closure
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Return))
        .expect("return block");
    return_block.stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place::local(0),
        rvalue: trust_types::Rvalue::Use(Operand::Copy(trust_types::Place::local(0))),
        span: trust_types::SourceSpan::default(),
    });
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(EXT_MERGE).expect("merge closure");
    let mut doctored = false;
    for block in &mut closure.body.blocks {
        for statement in &mut block.stmts {
            if let trust_types::Statement::Assign {
                rvalue:
                    trust_types::Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, _),
                ..
            } = statement
            {
                *name = "expr::kind::ZFCSetExpr".into();
                doctored = true;
            }
        }
    }
    assert!(doctored, "doctor must hit non-capturing aggregate enum");
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(CAPTURED_MERGE).expect("captured merge closure");
    let mut doctored = false;
    for block in &mut closure.body.blocks {
        for statement in &mut block.stmts {
            if let trust_types::Statement::Assign {
                rvalue:
                    trust_types::Rvalue::Aggregate(trust_types::AggregateKind::Adt { name, .. }, _),
                ..
            } = statement
            {
                *name = "expr::kind::ZFCSetExpr".into();
                doctored = true;
            }
        }
    }
    assert!(doctored, "doctor must hit captured aggregate enum");
    assert_callable_drift_declines(&bodies, "co_member_drift");

    let mut bodies = all_bodies();
    let closure = bodies.get_mut(CAPTURED_MAP).expect("captured map closure");
    let mut doctored = false;
    for block in &mut closure.body.blocks {
        if let trust_types::Terminator::Call { func, dest, .. } = &mut block.terminator
            && func == "std::sync::Arc::<T>::new"
        {
            dest.projections.push(trust_types::Projection::Field(0));
            doctored = true;
        }
    }
    assert!(doctored, "doctor must hit captured Arc::new destination");
    assert_callable_drift_declines(&bodies, "co_member_drift");
}

/// The FVarSubst row recognizes: 33 flattened ctors, memo field 2, leaf
/// resolutions = fvar override + 4 defaults.
#[test]
fn fvarsubst_row_recognizes() {
    let shape = recognize(FVS_ROW).unwrap_or_else(|d| {
        panic!("FVarSubst::fold_expr_opt must recognize, got {} ({d:?})", d.name())
    });
    assert_eq!(shape.folder, "expr::subst::FVarSubst");
    assert_eq!(shape.memo_field, 2, "FVarSubst memo is field 2 (id, replacement, memo)");
    assert_eq!(shape.ctors.len(), 33, "25 real − ZFCSet + 9 flattened zfc");
    let over: Vec<_> = shape
        .leaves
        .iter()
        .filter(|(_, r)| matches!(r, LeafResolution::Override(_)))
        .map(|(s, _)| *s)
        .collect();
    assert_eq!(over, vec![LeafSlot::FVar], "FVarSubst overrides exactly fold_fvar_opt");
    // Spot-check reconstructed arms: App is a merge2 over fields (0, 1);
    // Lam merges (1, 2) with the BODY a binder-marked child (read off the
    // real dispatch MIR — rung D's (d+1) IH slot; inert for this depthless
    // folder per the checked pure delegation); Proj maps child 2; SProp is a
    // none-arm.
    let by_name = |n: &str| shape.ctors.iter().find(|c| c.name == n).expect(n);
    assert_eq!(
        by_name("App").arm,
        TArm::Merge { children: vec![0, 1], binders: vec![false, false] }
    );
    assert_eq!(
        by_name("Lam").arm,
        TArm::Merge { children: vec![1, 2], binders: vec![false, true] }
    );
    assert_eq!(by_name("Pi").arm, TArm::Merge { children: vec![1, 2], binders: vec![false, true] });
    assert_eq!(
        by_name("Let").arm,
        TArm::Merge { children: vec![1, 2, 3], binders: vec![false, false, true] }
    );
    assert_eq!(by_name("Proj").arm, TArm::Map1 { child: 2, binder: false });
    assert_eq!(by_name("SProp").arm, TArm::NoneArm);
    assert_eq!(
        by_name("CubicalHComp").arm,
        TArm::Merge { children: vec![0, 1, 2, 3], binders: vec![false; 4] }
    );
    assert_eq!(by_name("CubicalPathLam").arm, TArm::Map1 { child: 0, binder: true });
    assert_eq!(
        by_name("ZFCComprehension").arm,
        TArm::Merge { children: vec![0, 1], binders: vec![false, true] }
    );
    assert_eq!(
        by_name("ZfcPair").arm,
        TArm::Merge { children: vec![0, 1], binders: vec![false, false] }
    );
    assert_eq!(
        by_name("ZfcSeparation").arm,
        TArm::Merge { children: vec![0, 1], binders: vec![false, true] }
    );
    assert_eq!(
        by_name("ZfcReplacement").arm,
        TArm::Merge { children: vec![0, 1], binders: vec![false, true] }
    );
    assert_eq!(by_name("ZfcSingleton").arm, TArm::Map1 { child: 0, binder: false });
    assert_eq!(by_name("ZfcEmpty").arm, TArm::NoneArm);
    assert_eq!(by_name("BVar").arm, TArm::Leaf(LeafSlot::BVar));
    assert_eq!(by_name("Const").arm, TArm::Leaf(LeafSlot::Const));
}

fn app_child_type_mut(bodies: &mut DumpBodies) -> &mut trust_types::Ty {
    let dispatch = bodies
        .get_mut("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full")
        .expect("generic full dispatch");
    let trust_types::Ty::Ref { inner, .. } = &mut dispatch.body.locals[2].ty else {
        panic!("dispatch Expr parameter must be a ref")
    };
    let trust_types::Ty::Adt { fields, .. } = inner.as_mut() else {
        panic!("dispatch parameter pointee must be Expr")
    };
    let kind =
        fields.iter_mut().find(|(name, _)| name == "kind").map(|(_, ty)| ty).expect("Expr.kind");
    let trust_types::Ty::Adt { variants, .. } = kind else { panic!("expanded ExprKind table") };
    let app = variants.iter_mut().find(|variant| variant.name == "App").expect("App");
    &mut app.fields[0].1
}

fn replace_app_child_type(bodies: &mut DumpBodies, replacement: trust_types::Ty) {
    *app_child_type_mut(bodies) = replacement;
}

fn rust_identifiers(source: &str) -> std::collections::BTreeSet<&str> {
    source
        .split(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .filter(|token| {
            token
                .as_bytes()
                .first()
                .is_some_and(|first| first.is_ascii_alphabetic() || *first == b'_')
        })
        .collect()
}

/// Executable P-ACYC gate: recursive Expr edges may only be direct
/// `Arc<Expr>` children. Weak/interior-mutable/mutable-reference channels and
/// recursion hidden inside another payload all decline by name.
#[test]
fn p_acyc_type_graph_adversaries_decline_by_name() {
    let expr_backref = trust_types::Ty::Datatype { name: "expr::Expr".into(), variants: vec![] };
    for (case, replacement) in [
        (
            "Weak edge",
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "std::sync::Weak".into(),
                fields: vec![("data".into(), expr_backref.clone())],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        ),
        (
            "UnsafeCell edge",
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "std::cell::UnsafeCell".into(),
                fields: vec![("value".into(), expr_backref.clone())],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        ),
        (
            "mutable ref edge",
            trust_types::Ty::Ref { mutable: true, inner: Box::new(expr_backref.clone()) },
        ),
        (
            "hidden Option edge",
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "std::option::Option".into(),
                fields: vec![("payload".into(), expr_backref.clone())],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        ),
        (
            "unknown opaque datatype",
            trust_types::Ty::Datatype { name: "user::OpaquePayload".into(), variants: vec![] },
        ),
        (
            "container-erased Cell payload",
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "smallvec::SmallVec".into(),
                fields: vec![(
                    "logical_payload".into(),
                    trust_types::Ty::Adt { adt_kind: None, layout: None, 
                        name: "std::cell::Cell".into(),
                        fields: vec![("value".into(), expr_backref.clone())],
                        variants: vec![],
                        disc_index_safe: false,
                        faithful_enum_repr: None, enum_layout: None, },
                )],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        ),
    ] {
        let mut bodies = all_bodies();
        replace_app_child_type(&mut bodies, replacement);
        let decline = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies)
            .expect_err("P-ACYC drift must fail closed");
        assert_eq!(decline.name(), "acyclicity_premise_drift", "{case}: {decline:?}");
    }

    // Retaining the real Arc pointee path is not enough: an added side field
    // must invalidate the full-layout pin instead of being hidden by the
    // early direct-Arc classification.
    let mut bodies = all_bodies();
    let trust_types::Ty::Adt { fields, .. } = app_child_type_mut(&mut bodies) else {
        panic!("App child must be the expanded Arc layout")
    };
    fields.push((
        "hidden_cycle_channel".into(),
        trust_types::Ty::Adt { adt_kind: None, layout: None, 
            name: "std::sync::Weak".into(),
            fields: vec![("data".into(), expr_backref)],
            variants: vec![],
            disc_index_safe: false,
            faithful_enum_repr: None, enum_layout: None, },
    ));
    let decline = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies)
        .expect_err("an Arc-shaped type with an extra side channel must fail closed");
    assert_eq!(decline.name(), "acyclicity_premise_drift", "{decline:?}");
}

/// Source-side companion to the dump type-graph gate. The clean-kernel crate
/// must keep unsafe code forbidden, and Expr's defining modules must not grow
/// direct Weak/interior-mutable storage without updating the executable model.
#[test]
fn p_acyc_clean_kernel_source_tripwire() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let lib =
        std::fs::read_to_string(repo.join("first-party/clean/crates/clean-kernel/src/lib.rs"))
            .expect("clean-kernel lib.rs");
    assert!(
        lib.contains("#![cfg_attr(not(kani), forbid(unsafe_code))]"),
        "P-ACYC requires clean-kernel's unsafe-code prohibition"
    );
    let read_source = |rel: &str| {
        std::fs::read_to_string(repo.join("first-party/clean/crates/clean-kernel/src").join(rel))
            .unwrap_or_else(|err| panic!("read {rel}: {err}"))
    };
    fn read_rust_tree(dir: &Path) -> String {
        let mut paths = std::fs::read_dir(dir)
            .unwrap_or_else(|err| panic!("read {}: {err}", dir.display()))
            .map(|entry| entry.expect("source-tree entry").path())
            .collect::<Vec<_>>();
        paths.sort();
        let mut sources = Vec::new();
        for path in paths {
            if path.is_dir() {
                sources.push(read_rust_tree(&path));
            } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
                sources.push(
                    std::fs::read_to_string(&path)
                        .unwrap_or_else(|err| panic!("read {}: {err}", path.display())),
                );
            }
        }
        sources.join("\n")
    }
    let expr_tree_sources =
        read_rust_tree(&repo.join("first-party/clean/crates/clean-kernel/src/expr"));
    let types_source = read_source("expr/types.rs");
    assert!(
        types_source.contains("pub type LevelVec = SmallVec<[Level; 2]>;"),
        "P-ACYC's pinned SmallVec type graph requires the exact LevelVec alias"
    );
    assert!(
        types_source.contains("pub type MDataMap = Vec<(Name, MDataValue)>;"),
        "P-ACYC's pinned Vec type graph requires the exact MDataMap alias"
    );
    let name_source = read_source("name.rs");
    // Name's independent thread-local interning cache legitimately uses a
    // RefCell, but no Name value points back into that cache. Scan from the
    // first NameInner definition onward so the value representation and all
    // of its implementations remain pinned without conflating global cache
    // machinery with an interior-mutable Name payload.
    let name_defs = name_source
        .get(name_source.find("pub enum NameInner").expect("NameInner definition")..)
        .expect("Name definition suffix");
    let level_tree_sources =
        read_rust_tree(&repo.join("first-party/clean/crates/clean-kernel/src/level"));
    let payload_sources =
        [expr_tree_sources.as_str(), level_tree_sources.as_str(), name_defs].join("\n");
    let identifiers = rust_identifiers(&payload_sources);
    for forbidden in ["new_cyclic", "Weak", "UnsafeCell", "RefCell", "Cell"] {
        assert!(
            !identifiers.contains(forbidden),
            "P-ACYC source tripwire found identifier {forbidden} in Expr payload definitions"
        );
    }
}

/// The source tripwire is token-based rather than substring-based: it catches
/// whitespace and import aliases, while an unrelated identifier such as
/// `unsafe_code` cannot masquerade as the `unsafe` keyword or `Cell` type.
#[test]
fn p_acyc_source_identifier_scan_is_alias_and_whitespace_resistant() {
    for (source, forbidden) in [
        ("use std :: sync :: Weak as W;", "Weak"),
        ("Arc :: new_cyclic ( |_| unreachable!() )", "new_cyclic"),
        ("use core::cell::{UnsafeCell as U};", "UnsafeCell"),
        ("type Hidden = RefCell < u8 >;", "RefCell"),
        ("use std::cell::Cell as C;", "Cell"),
    ] {
        assert!(rust_identifiers(source).contains(forbidden), "missed {forbidden}: {source}");
    }
    assert!(!rust_identifiers("#![forbid(unsafe_code)]").contains("unsafe"));
}

fn retarget_first_call(
    func: &mut VerifiableFunction,
    callee: &str,
    args: Vec<trust_types::Operand>,
) {
    let block = func
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Call { .. }))
        .expect("call-return body");
    let trust_types::Terminator::Call { func: target, args: call_args, .. } = &mut block.terminator
    else {
        unreachable!()
    };
    *target = callee.to_string();
    *call_args = args;
}

fn add_should_descend_chain(bodies: &mut DumpBodies, len: usize) -> Vec<String> {
    let root = "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::should_descend";
    let template = bodies.get(root).expect("G override").clone();
    let names = (0..len).map(|i| format!("adversary::g_chain_{i}")).collect::<Vec<_>>();
    for (index, name) in names.iter().enumerate() {
        let mut helper = template.clone();
        helper.name = format!("g_chain_{index}");
        helper.def_path = name.clone();
        if let Some(next) = names.get(index + 1) {
            retarget_first_call(
                &mut helper,
                next,
                vec![
                    trust_types::Operand::Copy(trust_types::Place::local(1)),
                    trust_types::Operand::Copy(trust_types::Place::local(2)),
                ],
            );
        }
        bodies.insert(name.clone(), helper);
    }
    retarget_first_call(
        bodies.get_mut(root).expect("G override"),
        &names[0],
        vec![
            trust_types::Operand::Copy(trust_types::Place::local(1)),
            trust_types::Operand::Copy(trust_types::Place::local(2)),
        ],
    );
    names
}

/// Standalone leaf certification is a finite tri-color DFS, not a depth-4
/// search. A six-helper call chain must retain the same positive SCC verdict.
#[test]
fn leaf_certification_chain_deeper_than_four_certifies() {
    let mut bodies = all_bodies();
    add_should_descend_chain(&mut bodies, 6);
    let shape = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect("deep G chain shape");
    diagnose_expr_fold_scc(&shape, &bodies)
        .unwrap_or_else(|decline| panic!("finite depth>4 chain must certify: {decline:?}"));
}

/// A reachable in-corpus cycle is rejected explicitly. Make the calls
/// non-folder-derived so this exercises the leaf DFS cycle gate rather than
/// the independent purity-cycle gate.
#[test]
fn leaf_certification_cycle_fails_closed() {
    let mut bodies = all_bodies();
    let names = add_should_descend_chain(&mut bodies, 6);
    let root = "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::should_descend";
    // Remove the tainted self argument from every adversarial edge; MIR is
    // doctored but the call graph remains the intended six-node cycle.
    retarget_first_call(
        bodies.get_mut(root).expect("G override"),
        &names[0],
        vec![trust_types::Operand::Copy(trust_types::Place::local(2))],
    );
    for index in 0..names.len() {
        let next = if index + 1 == names.len() { &names[0] } else { &names[index + 1] };
        retarget_first_call(
            bodies.get_mut(&names[index]).expect("chain member"),
            next,
            vec![trust_types::Operand::Copy(trust_types::Place::local(2))],
        );
    }
    let shape = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect("cycle still recognizes");
    let decline = diagnose_expr_fold_scc(&shape, &bodies).expect_err("leaf cycle must decline");
    assert_eq!(decline.name(), "leaf_uncertified", "{decline:?}");
    assert!(
        matches!(decline, ExprFoldDecline::LeafUncertified(path) if path == root),
        "cycle must be attributed to G"
    );
}

fn body_key_ending(bodies: &DumpBodies, suffix: &str) -> String {
    bodies
        .keys()
        .find(|path| path.ends_with(suffix))
        .unwrap_or_else(|| panic!("no body ending {suffix}"))
        .clone()
}

fn replace_authenticated_paddr_scalar_with_raw(func: &mut VerifiableFunction) {
    for block in &mut func.body.blocks {
        for statement in &mut block.stmts {
            let trust_types::Statement::Assign {
                rvalue:
                    trust_types::Rvalue::Use(Operand::Constant(
                        value @ ConstValue::OpaqueScalar { width: 64, signed: false },
                    )),
                ..
            } = statement
            else {
                continue;
            };
            *value = ConstValue::OpaqueConst;
            return;
        }
    }
    panic!("missing authenticated P-ADDR scalar in {}", func.def_path);
}

/// Raw pre-canonical `OpaqueConst` is decoder input only. It must never be
/// accepted at either the SCC root or a caller-supplied co-member boundary.
#[test]
fn raw_paddr_constants_cannot_bypass_authenticated_decoding() {
    for suffix in ["FoldMemo::get", "FoldMemo::put"] {
        let mut bodies = all_bodies();
        let key = body_key_ending(&bodies, suffix);
        replace_authenticated_paddr_scalar_with_raw(bodies.get_mut(&key).expect("memo body"));
        let decline = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies)
            .expect_err("raw memo co-member must fail closed");
        assert_eq!(decline.name(), "co_member_drift", "{suffix}: {decline:?}");
    }

    let mut inline = load(ABS_ROW);
    replace_authenticated_paddr_scalar_with_raw(&mut inline);
    let decline = sem_expr_fold_shape_of(&inline, &all_bodies())
        .expect_err("raw inline root must fail closed");
    assert_eq!(decline.name(), "wrapper_shape", "{decline:?}");
}

/// Expr-scale fail-closed coverage for the named composed-walker declines
/// that were previously exercised only by smaller pilots (or not at all).
/// Every probe mutates a real corpus body.
#[test]
fn expr_composed_named_decline_adversaries() {
    // Missing pinned co-member.
    let mut bodies = all_bodies();
    let merge2 = body_key_ending(&bodies, "::merge2");
    bodies.remove(&merge2);
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("missing merge2");
    assert_eq!(d.name(), "missing_co_member", "{d:?}");

    // Present but fingerprint-drifted co-member.
    let mut bodies = all_bodies();
    let memo_get = body_key_ending(&bodies, "FoldMemo::get");
    bodies.get_mut(&memo_get).expect("memo get").body.blocks.clear();
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("drifted memo get");
    assert_eq!(d.name(), "co_member_drift", "{d:?}");

    // Folder-specific dispatch override invalidates the generic body basis.
    let mut bodies = all_bodies();
    let mut injected = bodies
        .get("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner")
        .expect("generic inner")
        .clone();
    injected.def_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_expr_opt_inner"
            .into();
    bodies.insert(injected.def_path.clone(), injected);
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("dispatch override");
    assert_eq!(d.name(), "dispatch_overridden", "{d:?}");

    // The exhaustive dispatch marker is part of the TyCtxt-vetted total map.
    let mut bodies = all_bodies();
    let dispatch = bodies
        .get_mut("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full")
        .expect("full dispatch");
    let switch = dispatch
        .body
        .blocks
        .iter_mut()
        .find_map(|block| match &mut block.terminator {
            trust_types::Terminator::SwitchInt { exhaustive_enum_unreachable, .. }
                if *exhaustive_enum_unreachable =>
            {
                Some(exhaustive_enum_unreachable)
            }
            _ => None,
        })
        .expect("exhaustive ExprKind switch");
    *switch = false;
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("unvetted switch");
    assert_eq!(d.name(), "unmapped_switch_target", "{d:?}");

    // Recursive call on the whole Expr parameter rather than a field subterm.
    let mut bodies = all_bodies();
    let dispatch = bodies
        .get_mut("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full")
        .expect("full dispatch");
    let call = dispatch
        .body
        .blocks
        .iter_mut()
        .find_map(|block| match &mut block.terminator {
            trust_types::Terminator::Call { func, args, .. }
                if func == "expr::visitor::opt::ExprFolderOpt::fold_expr_opt" =>
            {
                Some(args)
            }
            _ => None,
        })
        .expect("recursive fold call");
    call[1] = trust_types::Operand::Copy(trust_types::Place::local(2));
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("whole-node recursion");
    assert_eq!(d.name(), "non_subterm_recursive_arg", "{d:?}");

    // App's second recursive call reuses its first child.
    let mut bodies = all_bodies();
    let dispatch = bodies
        .get_mut("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full")
        .expect("full dispatch");
    let first_arg = match &dispatch
        .body
        .blocks
        .iter()
        .find(|block| block.id == trust_types::BlockId(17))
        .expect("App first block")
        .terminator
    {
        trust_types::Terminator::Call { args, .. } => args[1].clone(),
        _ => panic!("App first fold call"),
    };
    let second = dispatch
        .body
        .blocks
        .iter_mut()
        .find(|block| block.id == trust_types::BlockId(19))
        .expect("App second block");
    let trust_types::Terminator::Call { args, .. } = &mut second.terminator else {
        panic!("App second fold call")
    };
    args[1] = first_arg;
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("duplicate App child");
    assert_eq!(d.name(), "duplicate_recursive_call", "{d:?}");

    // Const leaf payload arguments are declaration-ordered; swapping them is
    // a payload use, not an equivalent leaf call.
    let mut bodies = all_bodies();
    let dispatch = bodies
        .get_mut("expr::visitor::opt::ExprFolderOpt::fold_expr_opt_inner_full")
        .expect("full dispatch");
    let leaf = dispatch
        .body
        .blocks
        .iter_mut()
        .find(|block| block.id == trust_types::BlockId(13))
        .expect("Const leaf block");
    let trust_types::Terminator::Call { args, .. } = &mut leaf.terminator else {
        panic!("Const leaf call")
    };
    args.swap(1, 2);
    let d = sem_expr_fold_shape_of(&load(FVS_ROW), &bodies).expect_err("swapped leaf payloads");
    assert_eq!(d.name(), "payload_misuse", "{d:?}");
}

/// Stable-name inventory for every decline constructor, including gate-only
/// leaf/kernel failures. This catches accidental aliases/renames in tooling.
#[test]
fn expr_fold_decline_names_are_unique_and_pinned() {
    let declines = vec![
        ExprFoldDecline::SignatureUnsupported(String::new()),
        ExprFoldDecline::WrapperShape(String::new()),
        ExprFoldDecline::DepthKeyUnsupported(String::new()),
        ExprFoldDecline::KeyMismatch(String::new()),
        ExprFoldDecline::ImpureState(String::new()),
        ExprFoldDecline::MissingCoMember(String::new()),
        ExprFoldDecline::CoMemberDrift { member: String::new(), detail: String::new() },
        ExprFoldDecline::UnmappedSwitchTarget(String::new()),
        ExprFoldDecline::NonSubtermRecursiveArg(String::new()),
        ExprFoldDecline::DuplicateRecursiveCall(String::new()),
        ExprFoldDecline::PayloadMisuse(String::new()),
        ExprFoldDecline::ArmShape { variant: String::new(), detail: String::new() },
        ExprFoldDecline::StackSafeDrift(String::new()),
        ExprFoldDecline::DispatchOverridden(String::new()),
        ExprFoldDecline::LeafUncertified(String::new()),
        ExprFoldDecline::KernelWitnessRejected(String::new()),
        ExprFoldDecline::AcyclicityPremiseDrift(String::new()),
        ExprFoldDecline::MissingRestore(String::new()),
        ExprFoldDecline::BinderBodyShape(String::new()),
    ];
    let names = declines.iter().map(ExprFoldDecline::name).collect::<Vec<_>>();
    assert_eq!(
        names,
        vec![
            "signature_unsupported",
            "wrapper_shape",
            "fold_memo::depth_key_unsupported",
            "fold_memo::key_mismatch",
            "fold_memo::impure_state",
            "missing_co_member",
            "co_member_drift",
            "unmapped_switch_target",
            "non_subterm_recursive_arg",
            "duplicate_recursive_call",
            "payload_misuse",
            "arm_shape",
            "stack_safe_drift",
            "dispatch_overridden",
            "leaf_uncertified",
            "kernel_witness_rejected",
            "acyclicity_premise_drift",
            "fold_memo::missing_restore",
            "binder_body_shape",
        ]
    );
    assert_eq!(names.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), names.len());
}

/// The universal leaf-parametric witness + memoAdequate mint modulo 3 (and
/// the measured build cost is printed for the design-§7 budget report).
#[test]
fn expr_fold_witness_mints_modulo3() {
    let shape = recognize(FVS_ROW).expect("recognize");
    let (verdict, dt) = check_expr_fold_refinement_cached(&shape.ctors);
    println!("witness build: {dt:?}");
    assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
}

// ===========================================================================
// Production-gate verdicts (the judge/census surface)
// ===========================================================================

/// The FVarSubst row flips FULLY_FAITHFUL on the production gate (via
/// trust-ir): shape via the rung-C arm, safety pillars on top.
#[test]
fn fvarsubst_row_fully_faithful_on_production_gate() {
    let func = load(FVS_ROW);
    let bodies = all_bodies();
    let empty = std::collections::BTreeMap::new();
    let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
    let scc =
        sem_expr_fold_shape_of(&func, &bodies).map(|shape| diagnose_expr_fold_scc(&shape, &bodies));
    assert!(diag.via_ir_shape, "rung-C arm must witness the shape: {diag:?}; SCC={scc:?}");
    assert!(diag.via_ir_safety, "trust-ir safety pillar must hold");
    assert_eq!(diag.expr_fold_decline, None, "the Expr SCC itself certified");
    assert!(diag.fully_faithful, "the row must be FULLY_FAITHFUL");
}

/// The LevelParamSubst/Slice rows RECOGNIZE (same shape) but stay HONESTLY
/// hostage on the gate: their fold_sort_opt/fold_const_opt overrides are out
/// of every lane's reach at rung C (Level::substitute_map; Iterator::collect).
#[test]
fn levelparamsubst_rows_recognize_but_stay_hostage() {
    let bodies = all_bodies();
    let empty = std::collections::BTreeMap::new();
    for (row, folder) in [
        (
            "<expr__subst__LevelParamSubst<'_> as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt",
            "expr::subst::LevelParamSubst",
        ),
        (
            "<expr__subst__LevelParamSubstSlice<'_> as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt",
            "expr::subst::LevelParamSubstSlice",
        ),
    ] {
        let func = load(row);
        let shape = sem_expr_fold_shape_of(&func, &bodies)
            .unwrap_or_else(|d| panic!("{row} must recognize, got {} ({d:?})", d.name()));
        assert_eq!(shape.folder, folder);
        let over: Vec<_> = shape
            .leaves
            .iter()
            .filter(|(_, r)| matches!(r, LeafResolution::Override(_)))
            .map(|(s, _)| *s)
            .collect();
        assert_eq!(over, vec![LeafSlot::Sort, LeafSlot::Const]);
        // The typed SCC diagnostic must preserve the exact first hostage;
        // a broad SAFETY_GAP/false verdict is not enough to keep census
        // attribution honest.
        let decline = diagnose_expr_fold_scc(&shape, &bodies)
            .expect_err("the LevelParam fold must retain its leaf hostage");
        assert_eq!(decline.name(), "leaf_uncertified", "{decline:?}");
        let ExprFoldDecline::LeafUncertified(path) = decline else {
            panic!("expected exact leaf_uncertified decline")
        };
        assert_eq!(
            path,
            format!("<{folder}<'_> as expr::visitor::opt::ExprFolderOpt>::fold_sort_opt"),
            "{row}: exact first uncertified override"
        );
        // The production gate consumes the same typed SCC result and declines.
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(
            !diag.fully_faithful,
            "{row} must stay honestly hostage to its uncertified leaf overrides"
        );
        assert_eq!(diag.expr_fold_decline, Some("leaf_uncertified"), "{row}");
    }
}

// ===========================================================================
// RUNG D — the depth-threading folders as SCC units
// ===========================================================================

const INST_ROW: &str =
    "<expr__subst__Instantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";
const MULTI_ROW: &str =
    "<expr__subst__MultiInstantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";
const LIFTER_ROW: &str =
    "<expr__subst__Lifter as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";
const LOWERER_ROW: &str =
    "<expr__subst__Lowerer as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";
const ABS_ROW: &str =
    "<expr__subst__Abstractor as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";

/// All five depth-threading folders RECOGNIZE as SCC units, with the right
/// depth facts (depth field, binder-body co-member, memo idiom) and leaf
/// resolutions. The binder marks are checked once on Instantiator (the
/// generic dispatch is shared).
#[test]
fn depth_wrappers_recognize_with_scc_facts() {
    let bodies = all_bodies();
    let cases: [(&str, &str, usize, bool, Vec<LeafSlot>); 5] = [
        (INST_ROW, "expr::subst::Instantiator", 1, false, vec![LeafSlot::BVar]),
        (MULTI_ROW, "expr::subst::MultiInstantiator", 1, false, vec![LeafSlot::BVar]),
        (LIFTER_ROW, "expr::subst::Lifter", 0, false, vec![LeafSlot::BVar]),
        (LOWERER_ROW, "expr::subst::Lowerer", 0, false, vec![LeafSlot::BVar]),
        (ABS_ROW, "expr::subst::Abstractor", 1, true, vec![LeafSlot::BVar, LeafSlot::FVar]),
    ];
    for (row, folder, depth_field, inline, overrides) in cases {
        let func = load(row);
        let shape = sem_expr_fold_shape_of(&func, &bodies)
            .unwrap_or_else(|d| panic!("{row} must recognize, got {} ({d:?})", d.name()));
        assert_eq!(shape.folder, folder);
        assert_eq!(shape.ctors.len(), 33);
        let depth = shape.depth.as_ref().unwrap_or_else(|| panic!("{folder}: no depth facts"));
        assert_eq!(depth.depth_field, depth_field, "{folder} depth field");
        assert_eq!(depth.inline_memo, inline, "{folder} memo idiom");
        assert!(
            depth.binder_body.ends_with(">::fold_binder_body_opt")
                && depth.binder_body.contains(folder),
            "{folder} binder-body co-member: {}",
            depth.binder_body
        );
        let over: Vec<_> = shape
            .leaves
            .iter()
            .filter(|(_, r)| matches!(r, LeafResolution::Override(_)))
            .map(|(s, _)| *s)
            .collect();
        assert_eq!(over, overrides, "{folder} leaf overrides");
    }
    // Binder marks on the shared dispatch (via Instantiator's table).
    let shape = sem_expr_fold_shape_of(&load(INST_ROW), &bodies).expect("recognize");
    let by_name = |n: &str| shape.ctors.iter().find(|c| c.name == n).expect(n);
    assert_eq!(
        by_name("Lam").arm,
        TArm::Merge { children: vec![1, 2], binders: vec![false, true] }
    );
    assert_eq!(by_name("CubicalPathLam").arm, TArm::Map1 { child: 0, binder: true });
    assert_eq!(
        by_name("ZfcReplacement").arm,
        TArm::Merge { children: vec![0, 1], binders: vec![false, true] }
    );
}

/// The standalone binder-body rows recognize with the matching facts.
#[test]
fn binder_body_rows_recognize() {
    for (row, folder, df) in [
        (
            "<expr__subst__Instantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
            "expr::subst::Instantiator",
            1usize,
        ),
        (
            "<expr__subst__Lifter as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
            "expr::subst::Lifter",
            0,
        ),
        (
            "<expr__subst__Abstractor as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
            "expr::subst::Abstractor",
            1,
        ),
    ] {
        let func = load(row);
        let (f, d) = sem_binder_body_row_of(&func)
            .unwrap_or_else(|e| panic!("{row} must recognize, got {} ({e:?})", e.name()));
        assert_eq!(f, folder);
        assert_eq!(d, df);
    }
}

/// The DEPTH witness (foldD/memoFoldD + 66 per-ctor theorems + memoAdequateD)
/// mints modulo 3 on the REAL 33-ctor table.
#[test]
fn depth_witness_mints_modulo3_on_real_table() {
    let bodies = all_bodies();
    let shape = sem_expr_fold_shape_of(&load(ABS_ROW), &bodies).expect("recognize");
    let (verdict, dt) = check_expr_fold_refinement_cached_d(&shape.ctors);
    println!("depth witness build: {dt:?}");
    assert_eq!(verdict, RefinementVerdict::ProvenModulo3);
}

/// PAYOFF: Abstractor and Lifter certify FULLY_FAITHFUL — BOTH rows each
/// (wrapper + binder-body; one joint SCC certificate).
#[test]
fn abstractor_and_lifter_scc_rows_fully_faithful_on_production_gate() {
    let bodies = all_bodies();
    let empty = std::collections::BTreeMap::new();
    for row in [
        ABS_ROW,
        LIFTER_ROW,
        "<expr__subst__Abstractor as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
        "<expr__subst__Lifter as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
    ] {
        let func = load(row);
        if row.ends_with("__fold_expr_opt") {
            let shape = sem_expr_fold_shape_of(&func, &bodies).expect("wrapper recognizes");
            let scc = diagnose_expr_fold_scc(&shape, &bodies);
            assert!(scc.is_ok(), "{row}: joint SCC diagnosis: {scc:?}");
        }
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(diag.via_ir_shape, "{row}: rung-D arm must witness the shape: {diag:?}");
        assert!(diag.via_ir_safety, "{row}: trust-ir safety pillar must hold");
        assert_eq!(diag.expr_fold_decline, None, "{row}: SCC certificate succeeded");
        assert!(diag.fully_faithful, "{row} must be FULLY_FAITHFUL");
    }
}

/// Instantiator's exact ordering-dispatch leaf certifies, so all three affected
/// production rows (leaf + wrapper + binder-body) are FULLY_FAITHFUL.
#[test]
fn instantiator_scc_rows_fully_faithful_on_production_gate() {
    let bodies = all_bodies();
    let empty = std::collections::BTreeMap::new();
    for row in [
        INST_ROW,
        "<expr__subst__Instantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
        "<expr__subst__Instantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
    ] {
        let func = load(row);
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(diag.via_ir_shape, "{row}: exact trust-ir shape must witness");
        assert!(diag.via_ir_safety, "{row}: trust-ir safety pillar must hold");
        assert_eq!(diag.expr_fold_decline, None, "{row}: SCC certificate succeeded");
        assert!(diag.fully_faithful, "{row} must be FULLY_FAITHFUL: {diag:?}");
    }
    let shape = sem_expr_fold_shape_of(&load(INST_ROW), &bodies).expect("recognize Instantiator");
    assert!(diagnose_expr_fold_scc(&shape, &bodies).is_ok());
}

/// HONESTY: MultiInstantiator / Lowerer recognize but stay hostage to their
/// uncertifiable `fold_bvar_opt` overrides (leaf honesty decision in the
/// module doc: NO opaque-total-slot for partial leaves). MultiInstantiator's
/// `self.depth + n` overflow is genuinely satisfiable; Lowerer's debug-assert
/// panic arm is live MIR.
#[test]
fn multiinstantiator_lowerer_stay_hostage() {
    let bodies = all_bodies();
    let empty = std::collections::BTreeMap::new();
    for row in [
        MULTI_ROW,
        LOWERER_ROW,
        "<expr__subst__MultiInstantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
        "<expr__subst__Lowerer as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
    ] {
        let func = load(row);
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(
            !diag.fully_faithful,
            "{row} must stay honestly hostage to its uncertified fold_bvar_opt leaf"
        );
        assert_eq!(diag.expr_fold_decline, Some("leaf_uncertified"), "{row}");
    }
    for (row, blocker) in [
        (
            MULTI_ROW,
            "<expr::subst::MultiInstantiator<'_> as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt",
        ),
        (LOWERER_ROW, "<expr::subst::Lowerer as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt"),
    ] {
        let shape = sem_expr_fold_shape_of(&load(row), &bodies).expect("recognize hostage SCC");
        let decline = diagnose_expr_fold_scc(&shape, &bodies)
            .expect_err("the depth folder must retain its leaf hostage");
        assert_eq!(decline.name(), "leaf_uncertified", "{decline:?}");
        let ExprFoldDecline::LeafUncertified(path) = decline else {
            panic!("expected exact leaf_uncertified decline")
        };
        assert_eq!(path, blocker, "{row}: exact uncertified override");
    }
    // The binder rows consume the same SCC certificate and must retain the
    // same exact blocker, not merely a broad false verdict.
    for (row, blocker) in [
        (
            "<expr__subst__MultiInstantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
            "<expr::subst::MultiInstantiator<'_> as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt",
        ),
        (
            "<expr__subst__Lowerer as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt",
            "<expr::subst::Lowerer as expr::visitor::opt::ExprFolderOpt>::fold_bvar_opt",
        ),
    ] {
        let decline = trust_clean::diagnose_expr_fold_scc_for_function(&load(row), &bodies)
            .expect("binder row candidate")
            .expect_err("binder row must retain the SCC leaf hostage");
        assert_eq!(decline.name(), "leaf_uncertified", "{decline:?}");
        let ExprFoldDecline::LeafUncertified(path) = decline else {
            panic!("expected exact leaf_uncertified decline")
        };
        assert_eq!(path, blocker, "{row}: exact uncertified override");
    }
    // The blockers themselves stay short too (the leaves are the reason).
    for leaf in [
        "<expr__subst__MultiInstantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
        "<expr__subst__Lowerer as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
    ] {
        let func = load(leaf);
        let diag = trust_clean::diagnose_fully_faithful_gate_with_bodies(&func, &empty, &bodies);
        assert!(!diag.fully_faithful, "{leaf} is the honest blocker and must not be FF");
    }
}

// ===========================================================================
// Exact Instantiator ORDERING-DISPATCH leaf — production, structural, safety,
// and kernel-forgery probes on the real extracted body.
// ===========================================================================

const INST_ORD_LEAF: &str =
    "<expr__subst__Instantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt";

fn assert_instantiator_ord_doctor_declines(label: &str, func: &VerifiableFunction) {
    use trust_clean::mirsem::{
        INSTANTIATOR_ORD_LEAF_CONTENT_HASH, INSTANTIATOR_ORD_LEAF_DEF_PATH,
        sem_adt_return_opaque_ord_shape_of,
    };

    assert!(
        func.def_path != INSTANTIATOR_ORD_LEAF_DEF_PATH
            || func.content_hash() != INSTANTIATOR_ORD_LEAF_CONTENT_HASH,
        "{label}: the doctor must change the pinned identity or body hash"
    );
    assert!(
        sem_adt_return_opaque_ord_shape_of(func).is_none(),
        "{label}: exact ordering recognizer must fail closed"
    );
    let diagnosis = trust_clean::diagnose_fully_faithful_gate_with_bodies(
        func,
        &BTreeMap::new(),
        &all_bodies(),
    );
    assert!(
        !diagnosis.fully_faithful,
        "{label}: doctored leaf must not certify through another production lane: {diagnosis:?}"
    );
}

#[test]
fn instantiator_ord_leaf_shape_is_exact() {
    use trust_clean::mirsem::{SemChainVal, sem_adt_return_opaque_ord_shape_of};

    let shape = sem_adt_return_opaque_ord_shape_of(&load(INST_ORD_LEAF))
        .expect("the audited Instantiator ordering leaf must recognize");
    assert_eq!(shape.cmp_step, 0);
    assert_eq!(shape.steps.len(), 3, "cmp + lift_at + bvar");
    assert_eq!(shape.steps[1].callee, "expr::subst::<impl expr::Expr>::lift_at");
    assert_eq!(shape.steps[2].callee, "expr::constructors::<impl expr::Expr>::bvar");
    assert_eq!(
        shape.ord_variants,
        vec![("Less".into(), 255), ("Equal".into(), 0), ("Greater".into(), 1)]
    );
    assert_eq!(shape.crossed_asserts, 1);
    let arms =
        shape.arms.iter().map(|(name, arm)| (name.as_str(), arm)).collect::<BTreeMap<_, _>>();
    assert_eq!(arms["Less"].variant, 0);
    assert_eq!(arms["Less"].payload, None);
    assert_eq!(arms["Equal"].payload, Some(SemChainVal::Step(1)));
    assert_eq!(arms["Greater"].payload, Some(SemChainVal::Step(2)));
}

#[test]
fn instantiator_ord_leaf_identity_and_type_forgeries_decline() {
    use trust_types::Ty;

    let mut wrong_owner = load(INST_ORD_LEAF);
    wrong_owner.def_path = "forged::fold_bvar_opt".to_string();
    assert_instantiator_ord_doctor_declines("wrong def-path", &wrong_owner);

    let mut wrong_sentinel = load(INST_ORD_LEAF);
    let trust_types::Terminator::Call { func, .. } = &mut wrong_sentinel.body.blocks[0].terminator
    else {
        panic!("bb0 must be cmp call");
    };
    *func = "forged::cmp".to_string();
    assert_instantiator_ord_doctor_declines("forged sentinel", &wrong_sentinel);

    for (block_id, forged_callee) in [(5, "forged::lift_at"), (7, "forged::bvar")] {
        let mut wrong_step = load(INST_ORD_LEAF);
        let block = wrong_step
            .body
            .blocks
            .iter_mut()
            .find(|block| block.id == trust_types::BlockId(block_id))
            .expect("pinned step block");
        let trust_types::Terminator::Call { func, .. } = &mut block.terminator else {
            panic!("pinned step must be a call");
        };
        *func = forged_callee.to_string();
        assert_instantiator_ord_doctor_declines(forged_callee, &wrong_step);
    }

    let mut wrong_ordering = load(INST_ORD_LEAF);
    let Ty::Adt { name, variants, .. } = &mut wrong_ordering.body.locals[3].ty else {
        panic!("_3 must be Ordering");
    };
    *name = "forged::Ordering".to_string();
    variants[0].discriminant = -1;
    assert_instantiator_ord_doctor_declines("forged Ordering carrier/tag", &wrong_ordering);

    let mut wrong_outer = load(INST_ORD_LEAF);
    let Ty::Adt { name, variants, .. } = &mut wrong_outer.body.return_ty else {
        panic!("return must be Option");
    };
    *name = "forged::Option".to_string();
    variants[1].discriminant = 2;
    assert_instantiator_ord_doctor_declines("forged outer carrier/tag", &wrong_outer);

    for interior_name in ["std::cell::Cell", "std::cell::UnsafeCell"] {
        let mut interior_depth = load(INST_ORD_LEAF);
        let Ty::Ref { inner, .. } = &mut interior_depth.body.locals[1].ty else {
            panic!("self must be &mut Instantiator");
        };
        let Ty::Adt { fields, .. } = inner.as_mut() else {
            panic!("self referent must be Instantiator");
        };
        fields[1].1 = Ty::adt(
            interior_name,
            vec![("value".to_string(), Ty::Int { width: 32, signed: false })],
        );
        assert_instantiator_ord_doctor_declines(interior_name, &interior_depth);
    }
}

#[test]
fn instantiator_ord_leaf_alias_and_intervening_effects_decline() {
    use trust_types::{
        BasicBlock, BlockId, Operand, Place, Rvalue, Statement, Terminator, UnwindEdge,
    };

    let mut moved_mut_self = load(INST_ORD_LEAF);
    let bb5 =
        moved_mut_self.body.blocks.iter_mut().find(|block| block.id == BlockId(5)).expect("bb5");
    let Terminator::Call { args, .. } = &mut bb5.terminator else {
        panic!("bb5 must call lift_at");
    };
    args[0] = Operand::Move(Place::local(1));
    assert_instantiator_ord_doctor_declines("moved &mut self alias", &moved_mut_self);

    let mut intervening_write = load(INST_ORD_LEAF);
    let bb4 =
        intervening_write.body.blocks.iter_mut().find(|block| block.id == BlockId(4)).expect("bb4");
    bb4.stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: Default::default(),
    });
    assert_instantiator_ord_doctor_declines("intervening write", &intervening_write);

    let mut intervening_call = load(INST_ORD_LEAF);
    let bb4 =
        intervening_call.body.blocks.iter_mut().find(|block| block.id == BlockId(4)).expect("bb4");
    let Terminator::Assert { target, .. } = &mut bb4.terminator else {
        panic!("bb4 must assert checked subtraction");
    };
    *target = BlockId(10);
    intervening_call.body.blocks.push(BasicBlock {
        id: BlockId(10),
        stmts: vec![],
        terminator: Terminator::Call {
            func: "forged::mutate".to_string(),
            args: vec![Operand::Move(Place::local(1))],
            dest: Place::local(10),
            target: Some(BlockId(7)),
            unwind: UnwindEdge::Unreachable,
            span: Default::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
        },
    });
    assert_instantiator_ord_doctor_declines("intervening call", &intervening_call);
}

#[test]
fn instantiator_ord_leaf_wrong_checked_sub_and_dispatch_decline() {
    use trust_types::{BinOp, BlockId, Operand, Rvalue, Terminator};

    let mut wrong_subtrahend = load(INST_ORD_LEAF);
    let bb4 =
        wrong_subtrahend.body.blocks.iter_mut().find(|block| block.id == BlockId(4)).expect("bb4");
    let trust_types::Statement::Assign {
        rvalue: Rvalue::CheckedBinaryOp(BinOp::Sub, _, rhs), ..
    } = &mut bb4.stmts[0]
    else {
        panic!("bb4 must compute CheckedSub");
    };
    *rhs = Operand::Constant(ConstValue::Uint(2, 32));
    assert_instantiator_ord_doctor_declines("wrong checked-sub VC", &wrong_subtrahend);

    let mut wrong_dispatch_source = load(INST_ORD_LEAF);
    let bb1 = wrong_dispatch_source
        .body
        .blocks
        .iter_mut()
        .find(|block| block.id == BlockId(1))
        .expect("bb1");
    let trust_types::Statement::Assign { rvalue: Rvalue::Discriminant(source), .. } =
        &mut bb1.stmts[0]
    else {
        panic!("bb1 must read the Ordering discriminant");
    };
    source.local = 7;
    assert_instantiator_ord_doctor_declines("wrong discriminant source", &wrong_dispatch_source);

    let mut non_exhaustive = load(INST_ORD_LEAF);
    let bb1 =
        non_exhaustive.body.blocks.iter_mut().find(|block| block.id == BlockId(1)).expect("bb1");
    let Terminator::SwitchInt { exhaustive_enum_unreachable, .. } = &mut bb1.terminator else {
        panic!("bb1 must switch on Ordering");
    };
    *exhaustive_enum_unreachable = false;
    assert_instantiator_ord_doctor_declines("non-exhaustive dispatch", &non_exhaustive);
}

#[test]
fn instantiator_ord_wrong_arm_and_payload_claims_are_kernel_rejected() {
    use trust_clean::mirsem::sem_adt_return_opaque_ord_shape_of;
    use trust_clean::trustir_adt::{
        check_adt_return_opaque_ord_refinement_claimed, opaque_ord_arm_value_probe,
    };

    let shape = sem_adt_return_opaque_ord_shape_of(&load(INST_ORD_LEAF)).expect("recognize");
    let less_value = opaque_ord_arm_value_probe(&shape, 0).expect("Less value");
    let wrong_arm =
        check_adt_return_opaque_ord_refinement_claimed(&shape, [None, None, Some(&less_value)]);
    assert!(matches!(wrong_arm, RefinementVerdict::KernelRejected(_)), "{wrong_arm:?}");

    let greater_value = opaque_ord_arm_value_probe(&shape, 2).expect("Greater value");
    let swapped_payload =
        check_adt_return_opaque_ord_refinement_claimed(&shape, [None, Some(&greater_value), None]);
    assert!(matches!(swapped_payload, RefinementVerdict::KernelRejected(_)), "{swapped_payload:?}");
    assert_eq!(
        check_adt_return_opaque_ord_refinement_claimed(&shape, [None, None, None]),
        RefinementVerdict::ProvenModulo3
    );
}

#[test]
fn instantiator_ord_lane_rejects_every_other_real_bvar_leaf() {
    use trust_clean::mirsem::sem_adt_return_opaque_ord_shape_of;

    for leaf in [
        "<expr__subst__MultiInstantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
        "<expr__subst__Lowerer as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
        "<expr__subst__Abstractor as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
        "<expr__subst__Lifter as expr__visitor__opt__ExprFolderOpt>__fold_bvar_opt",
    ] {
        assert!(sem_adt_return_opaque_ord_shape_of(&load(leaf)).is_none(), "{leaf}");
    }
}

// ===========================================================================
// RUNG D — adversarial depth probes (doctored REAL MIR, NAMED declines)
// ===========================================================================

fn recognize_with_mutated_binder(
    row: &str,
    binder_file: &str,
    f: impl FnOnce(&mut VerifiableFunction),
) -> Result<SemExprFold, ExprFoldDecline> {
    let func = load(row);
    let mut bodies = all_bodies();
    {
        let binder_path = {
            let b = load(binder_file);
            b.def_path.clone()
        };
        let binder = bodies.get_mut(&binder_path).expect("binder body in corpus");
        f(binder);
    }
    sem_expr_fold_shape_of(&func, &bodies)
}

const INST_BINDER_FILE: &str =
    "<expr__subst__Instantiator<'_> as expr__visitor__opt__ExprFolderOpt>__fold_binder_body_opt";

/// MISSING RESTORE (design §6 kill): drop the restore statement →
/// `fold_memo::missing_restore`.
#[test]
fn depth_probe_missing_restore_declines() {
    let d = recognize_with_mutated_binder(INST_ROW, INST_BINDER_FILE, |b| {
        let last = b.body.blocks.last_mut().expect("bb2");
        last.stmts.clear();
    })
    .expect_err("a binder body without the restore must decline");
    assert_eq!(d.name(), "fold_memo::missing_restore", "{d:?}");
}

/// RESTORE OF THE WRONG VALUE (save/restore reorder): the restore writes the
/// INCREMENT result instead of the saved entry depth →
/// `fold_memo::missing_restore`.
#[test]
fn depth_probe_restore_of_wrong_value_declines() {
    let d = recognize_with_mutated_binder(INST_ROW, INST_BINDER_FILE, |b| {
        let last = b.body.blocks.last_mut().expect("bb2");
        for s in &mut last.stmts {
            if let trust_types::Statement::Assign {
                rvalue:
                    trust_types::Rvalue::Use(
                        trust_types::Operand::Copy(p) | trust_types::Operand::Move(p),
                    ),
                ..
            } = s
            {
                // The saved depth is _3; the increment result is _4.
                p.local = 4;
            }
        }
    })
    .expect_err("a restore of a non-saved value must decline");
    assert_eq!(d.name(), "fold_memo::missing_restore", "{d:?}");
}

/// A SECOND depth write inside the binder body (outside the pattern) →
/// `fold_memo::impure_state`.
#[test]
fn depth_probe_extra_depth_write_declines() {
    let d = recognize_with_mutated_binder(INST_ROW, INST_BINDER_FILE, |b| {
        let bb1 = &mut b.body.blocks[1];
        let dup = bb1.stmts[0].clone();
        bb1.stmts.push(dup);
    })
    .expect_err("an extra depth write must decline");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// STALE-DEPTH PUT KEY: the put's depth operand re-pointed away from the
/// pinned PRE-call copy → `fold_memo::key_mismatch`.
#[test]
fn depth_probe_stale_put_key_declines() {
    let mut func = load(INST_ROW);
    {
        let blk = func
            .body
            .blocks
            .iter_mut()
            .find(|b| matches!(&b.terminator, trust_types::Terminator::Call { func: c, .. } if c == "expr::subst::FoldMemo::put"))
            .expect("put block");
        let trust_types::Terminator::Call { args, .. } = &mut blk.terminator else {
            unreachable!()
        };
        // Re-point the depth operand at the GET-block key copy (_7) instead
        // of the pinned miss-arm pre-call copy (_10).
        args[2] = trust_types::Operand::Copy(trust_types::Place { local: 7, projections: vec![] });
    }
    let d = sem_expr_fold_shape_of(&func, &all_bodies())
        .expect_err("a put keyed off the miss-arm pre-call copy must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// BINDER-FIELD MISMATCH: the binder body threads a DIFFERENT folder field
/// than the memo key → `fold_memo::key_mismatch`.
#[test]
fn depth_probe_binder_field_mismatch_declines() {
    let d = recognize_with_mutated_binder(INST_ROW, INST_BINDER_FILE, |b| {
        for blk in &mut b.body.blocks {
            for s in &mut blk.stmts {
                if let trust_types::Statement::Assign { place, rvalue, .. } = s {
                    for p in [Some(place)]
                        .into_iter()
                        .flatten()
                        .map(Some)
                        .chain([match rvalue {
                            trust_types::Rvalue::Use(
                                trust_types::Operand::Copy(p) | trust_types::Operand::Move(p),
                            ) => Some(p),
                            _ => None,
                        }])
                        .flatten()
                    {
                        for proj in &mut p.projections {
                            if let trust_types::Projection::Field(f) = proj {
                                if *f == 1 {
                                    *f = 0;
                                }
                            }
                        }
                    }
                }
            }
        }
    })
    .expect_err("a binder body threading a different field must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// INLINE (Abstractor) INSERT-KEY DRIFT: the insert keyed on something other
/// than THE key tuple → `fold_memo::key_mismatch`.
#[test]
fn depth_probe_inline_insert_key_drift_declines() {
    let mut func = load(ABS_ROW);
    {
        let blk = func
            .body
            .blocks
            .iter_mut()
            .find(|b| matches!(&b.terminator, trust_types::Terminator::Call { func: c, .. } if c.contains("HashMap") && c.contains("insert")))
            .expect("insert block");
        let trust_types::Terminator::Call { args, .. } = &mut blk.terminator else {
            unreachable!()
        };
        // Key tuple is _5; re-point at the result clone (_18).
        args[1] = trust_types::Operand::Copy(trust_types::Place { local: 18, projections: vec![] });
    }
    let d = sem_expr_fold_shape_of(&func, &all_bodies())
        .expect_err("an insert not keyed on THE key tuple must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// INLINE RETURN-OF-CLONE: returning the inserted CLONE instead of the fold
/// result → `fold_memo::key_mismatch`.
#[test]
fn depth_probe_inline_return_of_clone_declines() {
    let mut func = load(ABS_ROW);
    for b in &mut func.body.blocks {
        for s in &mut b.stmts {
            if let trust_types::Statement::Assign {
                place,
                rvalue:
                    trust_types::Rvalue::Use(
                        trust_types::Operand::Move(src) | trust_types::Operand::Copy(src),
                    ),
                ..
            } = s
            {
                // The final `_0 = mv _14` → `_0 = mv _18` (the clone).
                if place.local == 0 && place.projections.is_empty() && src.local == 14 {
                    src.local = 18;
                }
            }
        }
    }
    let d = sem_expr_fold_shape_of(&func, &all_bodies())
        .expect_err("returning the clone instead of the result must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// KERNEL FORGERY on the REAL table: the binder mark dropped from Lam (IH at
/// `d` instead of `dsucc d`) → KernelRejected; the dual (mark added to App)
/// → KernelRejected.
#[test]
fn depth_forgery_wrong_ih_depth_on_real_table_rejected() {
    let bodies = all_bodies();
    let honest = sem_expr_fold_shape_of(&load(ABS_ROW), &bodies).expect("recognize").ctors;
    let lam = honest.iter().position(|c| c.name == "Lam").expect("Lam");
    let mut wrong = honest.clone();
    wrong[lam].arm = TArm::Merge { children: vec![1, 2], binders: vec![false, false] };
    let rhs = probe_arm_rhs_d(&wrong, lam).expect("render");
    let mut claims: Vec<Option<clean_kernel::Expr>> = vec![None; honest.len()];
    claims[lam] = Some(rhs);
    assert!(
        matches!(
            check_expr_fold_refinement_claimed_d(&honest, &claims),
            RefinementVerdict::KernelRejected(_)
        ),
        "Lam body IH claimed at d must be KernelRejected"
    );
    let app = honest.iter().position(|c| c.name == "App").expect("App");
    let mut wrong2 = honest.clone();
    wrong2[app].arm = TArm::Merge { children: vec![0, 1], binders: vec![false, true] };
    let rhs2 = probe_arm_rhs_d(&wrong2, app).expect("render");
    let mut claims2: Vec<Option<clean_kernel::Expr>> = vec![None; honest.len()];
    claims2[app] = Some(rhs2);
    assert!(
        matches!(
            check_expr_fold_refinement_claimed_d(&honest, &claims2),
            RefinementVerdict::KernelRejected(_)
        ),
        "App arg IH claimed at dsucc d must be KernelRejected"
    );
}

// ===========================================================================
// Adversarial memo probes — doctored REAL MIR, each a NAMED decline
// ===========================================================================

fn mutate_row(f: impl FnOnce(&mut VerifiableFunction)) -> Result<SemExprFold, ExprFoldDecline> {
    let mut func = load(FVS_ROW);
    f(&mut func);
    sem_expr_fold_shape_of(&func, &all_bodies())
}

fn call_mut<'a>(func: &'a mut VerifiableFunction, callee: &str) -> &'a mut trust_types::Terminator {
    let blk = func
        .body
        .blocks
        .iter_mut()
        .find(|b| matches!(&b.terminator, trust_types::Terminator::Call { func: c, .. } if c == callee))
        .unwrap_or_else(|| panic!("no call to {callee}"));
    &mut blk.terminator
}

/// PUT OF A NON-RESULT VALUE: put's value argument re-pointed at the memo-GET
/// result instead of the fold result → `fold_memo::key_mismatch`.
#[test]
fn memo_probe_put_of_non_result_declines() {
    let d = mutate_row(|func| {
        // The get result is _5; the fold result is _9 (see the wrapper walk).
        let trust_types::Terminator::Call { args, .. } =
            call_mut(func, "expr::subst::FoldMemo::put")
        else {
            unreachable!()
        };
        args[3] = trust_types::Operand::Copy(trust_types::Place { local: 5, projections: vec![] });
    })
    .expect_err("put of a non-result value must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// GET/PUT KEY DRIFT (expr operand): put keyed on a different local →
/// `fold_memo::key_mismatch`.
#[test]
fn memo_probe_key_drift_declines() {
    let d = mutate_row(|func| {
        let trust_types::Terminator::Call { args, .. } =
            call_mut(func, "expr::subst::FoldMemo::put")
        else {
            unreachable!()
        };
        args[1] = trust_types::Operand::Copy(trust_types::Place { local: 9, projections: vec![] });
    })
    .expect_err("get/put key drift must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// DEPTH-LITERAL DRIFT: the get keyed at depth 1 (not the depthless 0) →
/// `fold_memo::depth_key_unsupported`; a put-side drift (get 0 / put 1) →
/// `fold_memo::key_mismatch`.
#[test]
fn memo_probe_depth_drift_declines() {
    let d = mutate_row(|func| {
        let trust_types::Terminator::Call { args, .. } =
            call_mut(func, "expr::subst::FoldMemo::get")
        else {
            unreachable!()
        };
        args[2] = trust_types::Operand::Constant(trust_types::ConstValue::Uint(1, 32));
    })
    .expect_err("nonzero get depth must decline");
    assert_eq!(d.name(), "fold_memo::depth_key_unsupported", "{d:?}");

    let d = mutate_row(|func| {
        let trust_types::Terminator::Call { args, .. } =
            call_mut(func, "expr::subst::FoldMemo::put")
        else {
            unreachable!()
        };
        args[2] = trust_types::Operand::Constant(trust_types::ConstValue::Uint(1, 32));
    })
    .expect_err("get/put depth drift must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// PARTIAL CACHED USE: the hit arm projects INTO the cached value instead of
/// returning it whole → `fold_memo::key_mismatch`.
#[test]
fn memo_probe_partial_cached_use_declines() {
    let d = mutate_row(|func| {
        for b in &mut func.body.blocks {
            for s in &mut b.stmts {
                if let trust_types::Statement::Assign { rvalue, .. } = s {
                    if let trust_types::Rvalue::Use(
                        trust_types::Operand::Move(p) | trust_types::Operand::Copy(p),
                    ) = rvalue
                    {
                        if p.projections
                            == vec![
                                trust_types::Projection::Downcast(1),
                                trust_types::Projection::Field(0),
                            ]
                        {
                            p.projections.push(trust_types::Projection::Field(0));
                        }
                    }
                }
            }
        }
    })
    .expect_err("partial cached use must decline");
    assert_eq!(d.name(), "fold_memo::key_mismatch", "{d:?}");
}

/// HIDDEN FOLDER-STATE MUTATION: a write through the folder reference
/// anywhere in the row → `fold_memo::impure_state`.
#[test]
fn memo_probe_impure_state_declines() {
    let d = mutate_row(|func| {
        func.body.blocks[0].stmts.push(trust_types::Statement::Assign {
            place: trust_types::Place {
                local: 1,
                projections: vec![
                    trust_types::Projection::Deref,
                    trust_types::Projection::Field(0),
                ],
            },
            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                trust_types::ConstValue::Uint(0, 64),
            )),
            span: trust_types::SourceSpan::default(),
        });
    })
    .expect_err("a folder-state write must decline");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// DELEGATION-CLOSURE CAPTURE DRIFT: swapped captures → stack_safe drift.
#[test]
fn memo_probe_swapped_closure_captures_declines() {
    let d =
        mutate_row(|func| {
            for b in &mut func.body.blocks {
                for s in &mut b.stmts {
                    if let trust_types::Statement::Assign {
                        rvalue:
                            trust_types::Rvalue::Aggregate(
                                trust_types::AggregateKind::Closure { .. },
                                ops,
                            ),
                        ..
                    } = s
                    {
                        ops.swap(0, 1);
                    }
                }
            }
        })
        .expect_err("swapped closure captures must decline");
    assert_eq!(d.name(), "stack_safe_drift", "{d:?}");
}

// ===========================================================================
// Kernel forgery probes — wrong claims must be KernelRejected
// ===========================================================================

fn honest_ctors() -> Vec<TCtor> {
    recognize(FVS_ROW).expect("recognize").ctors
}

fn claim_against_honest(
    ctors: &[TCtor],
    i: usize,
    wrong_rhs: clean_kernel::Expr,
) -> RefinementVerdict {
    let mut claims: Vec<Option<clean_kernel::Expr>> = vec![None; ctors.len()];
    claims[i] = Some(wrong_rhs);
    check_expr_fold_refinement_claimed(ctors, &claims)
}

/// SWAPPED MERGE CHILDREN (design §6's headline forgery): claim App's arm
/// with children [1, 0] — not def-eq to the interpreter's reduct → rejected.
#[test]
fn forgery_swapped_children_is_kernel_rejected() {
    let honest = honest_ctors();
    let i = honest.iter().position(|c| c.name == "App").expect("App");
    let mut wrong = honest.clone();
    wrong[i].arm = TArm::Merge { children: vec![1, 0], binders: vec![false, false] };
    let rhs = probe_arm_rhs(&wrong, i).expect("render");
    assert!(
        matches!(claim_against_honest(&honest, i, rhs), RefinementVerdict::KernelRejected(_)),
        "a swapped-children claim must be KernelRejected"
    );
}

/// WRONG CTOR: claim App's rebuild as CubicalPathApp (same 2-rec-field shape,
/// well-typed, semantically wrong) → rejected.
#[test]
fn forgery_wrong_ctor_is_kernel_rejected() {
    let honest = honest_ctors();
    let i = honest.iter().position(|c| c.name == "App").expect("App");
    let mut wrong = honest.clone();
    wrong[i].name = "CubicalPathApp".to_string();
    let rhs = probe_arm_rhs(&wrong, i).expect("render");
    assert!(
        matches!(claim_against_honest(&honest, i, rhs), RefinementVerdict::KernelRejected(_)),
        "a wrong-ctor claim must be KernelRejected"
    );
}

/// WRONG MERGE ARITY: claim App's arm as a single-child map (drops the second
/// child's fold) → rejected.
#[test]
fn forgery_wrong_merge_arity_is_kernel_rejected() {
    let honest = honest_ctors();
    let i = honest.iter().position(|c| c.name == "App").expect("App");
    let mut wrong = honest.clone();
    wrong[i].arm = TArm::Map1 { child: 0, binder: false };
    let rhs = probe_arm_rhs(&wrong, i).expect("render");
    assert!(
        matches!(claim_against_honest(&honest, i, rhs), RefinementVerdict::KernelRejected(_)),
        "a wrong-arity claim must be KernelRejected"
    );
}

/// GUARD-POLARITY FORGERY: claim the guard-TRUE result is `none` (the
/// guard-false value) for a recursive arm → rejected.
#[test]
fn forgery_guard_polarity_is_kernel_rejected() {
    let honest = honest_ctors();
    let i = honest.iter().position(|c| c.name == "App").expect("App");
    let mut wrong = honest.clone();
    wrong[i].arm = TArm::NoneArm;
    let rhs = probe_arm_rhs(&wrong, i).expect("render");
    assert!(
        matches!(claim_against_honest(&honest, i, rhs), RefinementVerdict::KernelRejected(_)),
        "a guard-polarity claim must be KernelRejected"
    );
}

/// SCC-WIDE PURITY: a leaf OVERRIDE that writes through its `&mut self`
/// param (doctored MIR) voids the fixed-state-folder premise →
/// `fold_memo::impure_state`.
#[test]
fn memo_probe_leaf_override_self_write_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    let leaf = bodies.get_mut(leaf_path).expect("leaf");
    leaf.body.blocks[0].stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place {
            local: 1,
            projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
        },
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
            trust_types::ConstValue::Uint(0, 64),
        )),
        span: trust_types::SourceSpan::default(),
    });
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("a self-writing leaf override must decline");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// SCC-WIDE PURITY: copying `&mut self` to a temporary must not launder its
/// provenance. A later write through that alias is the same forbidden state
/// mutation as a direct `_1` write.
#[test]
fn memo_probe_leaf_copied_self_alias_write_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    let leaf = bodies.get_mut(leaf_path).expect("leaf");
    let alias = leaf.body.locals.len();
    leaf.body.locals.push(trust_types::LocalDecl {
        index: alias,
        ty: leaf.body.locals[1].ty.clone(),
        name: Some("copied_self".into()),
    });
    leaf.body.blocks[0].stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place::local(alias),
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(trust_types::Place::local(1))),
        span: trust_types::SourceSpan::default(),
    });
    leaf.body.blocks[0].stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place {
            local: alias,
            projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
        },
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
            trust_types::ConstValue::Uint(0, 64),
        )),
        span: trust_types::SourceSpan::default(),
    });
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("a write through a copied self alias must decline");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// SCC-WIDE PURITY: raw-pointer provenance must survive (or reject) casts.
/// Casting a copied `&mut self` alias through `usize` and back must not make a
/// subsequent write appear detached from the folder.
#[test]
fn memo_probe_leaf_pointer_integer_alias_laundering_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    let leaf = bodies.get_mut(leaf_path).expect("leaf");
    let trust_types::Ty::Ref { inner: folder_ty, .. } = &leaf.body.locals[1].ty else {
        panic!("leaf self argument must be a reference")
    };
    let raw_ty = trust_types::Ty::RawPtr { mutable: true, pointee: folder_ty.clone() };
    let raw_before = leaf.body.locals.len();
    leaf.body.locals.push(trust_types::LocalDecl {
        index: raw_before,
        ty: raw_ty.clone(),
        name: Some("raw_self_before_integer_cast".into()),
    });
    let address = leaf.body.locals.len();
    leaf.body.locals.push(trust_types::LocalDecl {
        index: address,
        ty: trust_types::Ty::Int { width: 64, signed: false },
        name: Some("laundered_self_address".into()),
    });
    let raw_after = leaf.body.locals.len();
    leaf.body.locals.push(trust_types::LocalDecl {
        index: raw_after,
        ty: raw_ty.clone(),
        name: Some("raw_self_after_integer_cast".into()),
    });
    leaf.body.blocks[0].stmts.extend([
        trust_types::Statement::Assign {
            place: trust_types::Place::local(raw_before),
            rvalue: trust_types::Rvalue::Cast(
                trust_types::Operand::Copy(trust_types::Place::local(1)),
                raw_ty.clone(),
            ),
            span: trust_types::SourceSpan::default(),
        },
        trust_types::Statement::Assign {
            place: trust_types::Place::local(address),
            rvalue: trust_types::Rvalue::Cast(
                trust_types::Operand::Copy(trust_types::Place::local(raw_before)),
                trust_types::Ty::Int { width: 64, signed: false },
            ),
            span: trust_types::SourceSpan::default(),
        },
        trust_types::Statement::Assign {
            place: trust_types::Place::local(raw_after),
            rvalue: trust_types::Rvalue::Cast(
                trust_types::Operand::Copy(trust_types::Place::local(address)),
                raw_ty,
            ),
            span: trust_types::SourceSpan::default(),
        },
        trust_types::Statement::Assign {
            place: trust_types::Place {
                local: raw_after,
                projections: vec![
                    trust_types::Projection::Deref,
                    trust_types::Projection::Field(0),
                ],
            },
            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                trust_types::ConstValue::Uint(0, 64),
            )),
            span: trust_types::SourceSpan::default(),
        },
    ]);
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("a pointer/integer cast chain must not launder the self alias");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// SCC-WIDE PURITY: storing `&mut self` into a field of an otherwise
/// untainted aggregate must taint the aggregate root. Passing that root to an
/// unavailable callee is an escape, not a way to launder folder provenance.
#[test]
fn memo_probe_leaf_self_alias_stored_in_aggregate_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    let leaf = bodies.get_mut(leaf_path).expect("leaf");
    let carrier = leaf.body.locals.len();
    leaf.body.locals.push(trust_types::LocalDecl {
        index: carrier,
        ty: trust_types::Ty::Tuple(vec![leaf.body.locals[1].ty.clone()]),
        name: Some("alias_carrier".into()),
    });
    let block = leaf
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Call { .. }))
        .expect("leaf call");
    block.stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place {
            local: carrier,
            projections: vec![trust_types::Projection::Field(0)],
        },
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(trust_types::Place::local(1))),
        span: trust_types::SourceSpan::default(),
    });
    let trust_types::Terminator::Call { func: callee, args, .. } = &mut block.terminator else {
        unreachable!()
    };
    *callee = "adversary::consume_alias_carrier".into();
    *args = vec![trust_types::Operand::Move(trust_types::Place::local(carrier))];
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("an alias stored into an aggregate field must remain tainted");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// SCC-WIDE PURITY: a shared reference copied from the folder is detached
/// only when its complete logical payload is pinned immutable. A collection
/// def-path alone must not hide a `Cell` element and launder the alias before
/// an external call.
#[test]
fn memo_probe_leaf_shared_container_cell_alias_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    let leaf = bodies.get_mut(leaf_path).expect("leaf");
    let alias = leaf.body.locals.len();
    let hidden_cell = trust_types::Ty::Adt { adt_kind: None, layout: None, 
        name: "std::collections::VecDeque".into(),
        fields: vec![(
            "logical_payload".into(),
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "std::cell::Cell".into(),
                fields: vec![("value".into(), trust_types::Ty::Int { width: 64, signed: false })],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        )],
        variants: vec![],
        disc_index_safe: false,
        faithful_enum_repr: None, enum_layout: None, };
    leaf.body.locals.push(trust_types::LocalDecl {
        index: alias,
        ty: trust_types::Ty::Ref { mutable: false, inner: Box::new(hidden_cell) },
        name: Some("hidden_cell_alias".into()),
    });
    let block = leaf
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Call { .. }))
        .expect("leaf call");
    block.stmts.push(trust_types::Statement::Assign {
        place: trust_types::Place::local(alias),
        rvalue: trust_types::Rvalue::Use(trust_types::Operand::Copy(trust_types::Place {
            local: 1,
            projections: vec![trust_types::Projection::Deref, trust_types::Projection::Field(0)],
        })),
        span: trust_types::SourceSpan::default(),
    });
    let trust_types::Terminator::Call { func: callee, args, .. } = &mut block.terminator else {
        unreachable!()
    };
    *callee = "adversary::mutate_hidden_cell".into();
    *args = vec![trust_types::Operand::Copy(trust_types::Place::local(alias))];
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("a collection-hidden Cell alias must remain folder-derived");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// The real LevelParamSubst HashMap field is admitted only by its complete
/// extracted type hash. Adding an interior-mutable logical field must break
/// that pin and keep the copied shared state folder-derived.
#[test]
fn memo_probe_pinned_hashmap_fixed_state_drift_declines() {
    let row =
        "<expr__subst__LevelParamSubst<'_> as expr__visitor__opt__ExprFolderOpt>__fold_expr_opt";
    let leaf_path =
        "<expr::subst::LevelParamSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_sort_opt";
    let mut bodies = all_bodies();
    let leaf = bodies.get_mut(leaf_path).expect("LevelParamSubst sort leaf");
    let trust_types::Ty::Ref { mutable: false, inner } = &mut leaf.body.locals[9].ty else {
        panic!("_9 must be the copied shared HashMap reference");
    };
    let trust_types::Ty::Adt { fields, .. } = inner.as_mut() else {
        panic!("_9 pointee must be the extracted HashMap graph");
    };
    fields.push((
        "adversarial_cell".into(),
        trust_types::Ty::adt(
            "std::cell::Cell",
            vec![("value".into(), trust_types::Ty::Int { width: 64, signed: false })],
        ),
    ));
    let decline = sem_expr_fold_shape_of(&load(row), &bodies)
        .expect_err("HashMap graph drift must invalidate the fixed-state pin");
    assert_eq!(decline.name(), "fold_memo::impure_state", "{decline:?}");
}

/// SCC-WIDE PURITY: a folder-derived alias passed to a local helper is
/// followed into that helper. The helper's write cannot hide behind the call
/// boundary.
#[test]
fn memo_probe_leaf_mutating_helper_call_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    let mut helper = bodies.get(leaf_path).expect("leaf").clone();
    helper.name = "mutate_folder".into();
    helper.def_path = "adversary::mutate_folder".into();
    helper.body.arg_count = 1;
    helper.body.blocks = vec![trust_types::BasicBlock {
        id: trust_types::BlockId(0),
        stmts: vec![trust_types::Statement::Assign {
            place: trust_types::Place {
                local: 1,
                projections: vec![
                    trust_types::Projection::Deref,
                    trust_types::Projection::Field(0),
                ],
            },
            rvalue: trust_types::Rvalue::Use(trust_types::Operand::Constant(
                trust_types::ConstValue::Uint(0, 64),
            )),
            span: trust_types::SourceSpan::default(),
        }],
        terminator: trust_types::Terminator::Return,
    }];
    bodies.insert(helper.def_path.clone(), helper);
    let leaf = bodies.get_mut(leaf_path).expect("leaf");
    let block = leaf
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Call { .. }))
        .expect("leaf call");
    let trust_types::Terminator::Call { func: callee, args, .. } = &mut block.terminator else {
        unreachable!()
    };
    *callee = "adversary::mutate_folder".into();
    *args = vec![trust_types::Operand::Copy(trust_types::Place::local(1))];
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("a mutating helper reached with self must decline");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}

/// Generic Clone is not a purity axiom. Reject (a) an explicit `Cell`, (b) an
/// opaque datatype whose absent field graph hides Cell, and (c) an ordinary-
/// looking user ADT whose custom Clone can mutate globals. Only exact audited
/// clean-kernel payloads may use the external clone exception.
#[test]
fn memo_probe_interior_mutating_clone_declines() {
    let func = load(FVS_ROW);
    let leaf_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::fold_fvar_opt";
    for (case, payload) in [
        (
            "explicit Cell",
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "std::cell::Cell".into(),
                fields: vec![],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        ),
        (
            "opaque hidden Cell",
            trust_types::Ty::Datatype { name: "user::HiddenCell".into(), variants: vec![] },
        ),
        (
            "custom side-effecting Clone",
            trust_types::Ty::Adt { adt_kind: None, layout: None, 
                name: "user::LooksImmutableButCloneTouchesGlobal".into(),
                fields: vec![],
                variants: vec![],
                disc_index_safe: false,
                faithful_enum_repr: None, enum_layout: None, },
        ),
    ] {
        let mut bodies = all_bodies();
        let leaf = bodies.get_mut(leaf_path).expect("leaf");
        leaf.body.locals[5].ty = trust_types::Ty::Ref { mutable: false, inner: Box::new(payload) };
        let block = leaf
            .body
            .blocks
            .iter_mut()
            .find(|block| matches!(block.terminator, trust_types::Terminator::Call { .. }))
            .expect("clone call");
        let trust_types::Terminator::Call { func: callee, args, .. } = &mut block.terminator else {
            unreachable!()
        };
        *callee = "std::clone::Clone::clone".into();
        *args = vec![trust_types::Operand::Move(trust_types::Place::local(5))];
        let d = match sem_expr_fold_shape_of(&func, &bodies) {
            Err(decline) => decline,
            Ok(_) => panic!("{case}: untrusted Clone payload must decline"),
        };
        assert_eq!(d.name(), "fold_memo::impure_state", "{case}: {d:?}");
    }
}

/// G (`should_descend`) is part of the fixed-state SCC premise too. Passing
/// the folder itself to an interior-mutating operation must decline before a
/// witness is considered.
#[test]
fn memo_probe_should_descend_interior_mutation_declines() {
    let func = load(FVS_ROW);
    let mut bodies = all_bodies();
    let g_path =
        "<expr::subst::FVarSubst<'_> as expr::visitor::opt::ExprFolderOpt>::should_descend";
    let g = bodies.get_mut(g_path).expect("G override");
    let block = g
        .body
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, trust_types::Terminator::Call { .. }))
        .expect("G call");
    let trust_types::Terminator::Call { func: callee, args, .. } = &mut block.terminator else {
        unreachable!()
    };
    *callee = "std::cell::Cell::set".into();
    *args = vec![trust_types::Operand::Copy(trust_types::Place::local(1))];
    let d = sem_expr_fold_shape_of(&func, &bodies)
        .expect_err("an interior-mutating G call must decline");
    assert_eq!(d.name(), "fold_memo::impure_state", "{d:?}");
}
