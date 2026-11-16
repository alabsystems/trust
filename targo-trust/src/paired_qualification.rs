//! Native paired candidate qualification. Input and receipt checks retain the
//! same live owner; neither stage grants execution, proof or publication.

use std::process::ExitCode;

#[cfg(unix)]
mod ledger;
#[cfg(any(target_os = "linux", target_os = "macos"))]
mod native;

#[cfg(unix)]
fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        out.push(char::from(DIGITS[(byte >> 4) as usize]));
        out.push(char::from(DIGITS[(byte & 15) as usize]));
    }
    out
}
#[cfg(unix)]
mod protocol;

const USAGE: &str = "\
Usage: targo trust gate qualify-pair <inspect|receipts|probes|dependencies|workloads|paired> [options]

Inspect and retain the complete inputs for a paired qualification experiment.
`inspect` binds bytes. `receipts` also validates native stage receipts, listed
executable hashes and the completed candidate's self-reported source closure.
The original inputs are rebound around these checks. Neither stage runs or
qualifies a compiler. Reports name the remaining probe, execution, comparison
and landing stages. `probes` runs the sealed compiler metadata through a
separately admitted native Targo service, then rebinds the original inputs.
It checks labels/sysroots and native input observations; workload execution,
source/build authentication, proof and publication remain separate.
`dependencies` continues those successful probes with the same retained pair
through the exact sealed control and candidate Targo full locked/offline resolver.
Older SDKs without native resolver support refuse before project configuration.
`workloads` retains those same dependencies through one native compilation per
side, both complete native inventories and every repeated sample, followed by
positive original root retirement. It requires matching workload-capable native
hosts and SDKs; unavailable custody refuses without a local execution fallback.
`paired` adds native AY compilation and independent advisory/strict graph nodes
to that same original root, with complete source-bound ledgers and a distinct
paired host/SDK protocol. Old workload-v1 is never relabeled AY complete.

Required options:
  --control PATH              Canonical immutable control seal outside build/
  --candidate PATH            Canonical immutable candidate seal outside build/
  --candidate-receipt PATH     Exact receipt also present in the candidate seal
  --candidate-commit SHA       Expected full lowercase candidate Git commit
  --ay PATH                    Owned clean AY repository with Cargo.lock
  --trust-vc PATH              Owned clean trust-vc repository with Cargo.lock
  --trust-spec-source PATH     Exact scaffold consumed by the AY census
  --out NEW_FILE               New retained report outside every input tree
Optional:
  --dependency PATH            Bind an actual resolved dependency tree (repeatable)
  --probe-service PATH          Native Targo service (default: sibling targo)
  --probe-host-store PATH       Explicit private native discovery store; no fallback
Workloads options:
  --workload-output NEW_DIR     New native build/evidence directory outside inputs
  --repetitions N               Samples per target, 1..32 (default: 3)
  --timeout SECONDS             Each original phase budget (default: 3600)
  --paired-cache PATH           New or existing private paired cache (paired only)
  -h, --help                   Show this help

Inspection never implies a completed or measured experiment. Saved records do
not establish who produced a receipt and grant no proof or execution authority.
";

pub(crate) fn run(args: &[String]) -> ExitCode {
    if args.iter().any(|arg| matches!(arg.as_str(), "--help" | "-h")) {
        print!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    #[cfg(unix)]
    {
        unix::run(args)
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        eprintln!(
            "targo trust gate qualify-pair: native paired input custody currently requires Unix"
        );
        ExitCode::from(3)
    }
}

#[cfg(unix)]
mod unix {
    use std::collections::BTreeMap;
    use std::fs;
    use std::path::{Component, Path, PathBuf};
    use std::time::Duration;

    use trust_qualification::{Git, Refusal, Result, pair};

    use super::*;

    struct ControlledGit;
    impl Git for ControlledGit {
        fn probe(&self, root: &Path, args: &[&str]) -> Result<Vec<u8>> {
            let output = crate::controlled_git::output(
                root,
                args,
                "paired qualification source inventory",
                128 * 1024 * 1024,
                Duration::from_secs(60),
            )
            .map_err(Refusal)?;
            if !output.status.success() || !output.stderr.is_empty() {
                return Err(Refusal(format!(
                    "paired qualification Git probe failed ({}): {}",
                    output.status,
                    String::from_utf8_lossy(&output.stderr)
                )));
            }
            Ok(output.stdout)
        }
        fn validate_repository(&self, root: &Path) -> Result<()> {
            crate::controlled_git::validate_status_authority(
                root,
                "paired qualification source authority",
                128 * 1024 * 1024,
                Duration::from_secs(60),
            )
            .map_err(Refusal)
        }
    }

    #[derive(Clone, Copy, Debug)]
    enum Stage {
        Inspect,
        Receipts,
        Probes,
        Dependencies,
        Workloads,
        Paired,
    }

    impl Stage {
        fn name(self) -> &'static str {
            match self {
                Self::Inspect => "input-inspection",
                Self::Receipts => "stage-receipt-validation",
                Self::Probes => "compiler-metadata-probes",
                Self::Dependencies => "locked-offline-dependencies",
                Self::Workloads => "native-consumer-workload",
                Self::Paired => "native-AY-and-consumer-graphs",
            }
        }
    }

    #[derive(Debug)]
    struct Options {
        stage: Stage,
        request: pair::Request,
        out: PathBuf,
        probe_service: Option<PathBuf>,
        probe_host_store: Option<PathBuf>,
        workloads: Option<trust_qualification::workloads::Options>,
        paired_cache: Option<PathBuf>,
    }

    fn parse(args: &[String]) -> std::result::Result<Options, String> {
        let stage = match args.first().map(String::as_str) {
            Some("inspect") => Stage::Inspect,
            Some("receipts") => Stage::Receipts,
            Some("probes") => Stage::Probes,
            Some("dependencies") => Stage::Dependencies,
            Some("workloads") => Stage::Workloads,
            Some("paired") => Stage::Paired,
            _ => return Err("supported stages are `inspect`, `receipts`, `probes`, `dependencies`, `workloads` and `paired`".into()),
        };
        let mut values = BTreeMap::new();
        let mut dependencies = Vec::new();
        let mut i = 1;
        while i < args.len() {
            let key = args[i].as_str();
            if !matches!(
                key,
                "--control"
                    | "--candidate"
                    | "--candidate-receipt"
                    | "--candidate-commit"
                    | "--ay"
                    | "--trust-vc"
                    | "--trust-spec-source"
                    | "--out"
                    | "--dependency"
                    | "--probe-service"
                    | "--probe-host-store"
                    | "--workload-output"
                    | "--repetitions"
                    | "--timeout"
                    | "--paired-cache"
            ) {
                return Err(format!("unknown option `{key}`"));
            }
            let value = args
                .get(i + 1)
                .filter(|value| !value.is_empty() && !value.starts_with('-'))
                .ok_or_else(|| format!("{key} requires a value"))?;
            if key == "--dependency" {
                dependencies.push(PathBuf::from(value));
            } else if values.insert(key, value.clone()).is_some() {
                return Err(format!("duplicate option `{key}`"));
            }
            i += 2;
        }
        let get = |key| {
            values.get(key).cloned().ok_or_else(|| format!("missing required option `{key}`"))
        };
        if values.contains_key("--paired-cache") && !matches!(stage, Stage::Paired) {
            return Err("--paired-cache requires the distinct paired stage".into());
        }
        let cargo_home = std::env::var_os("CARGO_HOME")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")))
            .ok_or_else(|| "CARGO_HOME and HOME are both unavailable".to_owned())?;
        if !matches!(stage, Stage::Probes | Stage::Dependencies | Stage::Workloads | Stage::Paired)
            && (values.contains_key("--probe-service") || values.contains_key("--probe-host-store"))
        {
            return Err(
                "probe service/discovery options need the probes, dependencies, workloads or paired stage"
                    .into(),
            );
        }
        let workloads = if matches!(stage, Stage::Workloads | Stage::Paired) {
            let number = |name: &str, default: u64| -> std::result::Result<u64, String> {
                match values.get(name) {
                    None => Ok(default),
                    Some(value) if value.bytes().all(|b| b.is_ascii_digit()) => {
                        value.parse::<u64>().map_err(|_| format!("invalid finite {name}"))
                    }
                    _ => Err(format!("invalid finite {name}")),
                }
            };
            let repetitions = number("--repetitions", 3)?;
            let seconds = number("--timeout", 3600)?;
            let ns = seconds
                .checked_mul(1_000_000_000)
                .filter(|ns| *ns > 0)
                .ok_or("invalid finite --timeout")?;
            let repetitions = u32::try_from(repetitions).map_err(|_| "invalid --repetitions")?;
            if matches!(stage, Stage::Paired) {
                trust_resource_controller::paired_qualification::budget::Budget::new(
                    repetitions,
                    ns,
                )
                .map_err(|_| "invalid complete finite paired budget")?;
            } else {
                trust_resource_controller::workload::budget::Budget::new(repetitions, ns)
                    .map_err(|_| "invalid complete finite workload budget")?;
            }
            Some(trust_qualification::workloads::Options {
                output: prospective_path(Path::new(&get("--workload-output")?))?,
                repetitions,
                timeout: Duration::from_secs(seconds),
            })
        } else {
            if ["--workload-output", "--repetitions", "--timeout"]
                .iter()
                .any(|key| values.contains_key(key))
            {
                return Err("workload options require workloads stage".into());
            }
            None
        };
        Ok(Options {
            stage,
            request: pair::Request {
                control: PathBuf::from(get("--control")?),
                candidate: PathBuf::from(get("--candidate")?),
                candidate_receipt: PathBuf::from(get("--candidate-receipt")?),
                candidate_commit: get("--candidate-commit")?,
                ay: PathBuf::from(get("--ay")?),
                trust_vc: PathBuf::from(get("--trust-vc")?),
                trust_spec_source: PathBuf::from(get("--trust-spec-source")?),
                cargo_home,
                dependency_roots: dependencies,
            },
            out: PathBuf::from(get("--out")?),
            probe_service: values.get("--probe-service").map(PathBuf::from),
            probe_host_store: values.get("--probe-host-store").map(PathBuf::from),
            workloads,
            paired_cache: values
                .get("--paired-cache")
                .map(|path| prospective_path(Path::new(path)))
                .transpose()?,
        })
    }

    /// Resolve existing ancestors before any write. An output alias into an
    /// input tree must not create even a refusal record there.
    fn prospective_path(path: &Path) -> std::result::Result<PathBuf, String> {
        let absolute = if path.is_absolute() {
            path.into()
        } else {
            std::env::current_dir().map_err(|e| e.to_string())?.join(path)
        };
        if absolute.components().any(|component| matches!(component, Component::ParentDir)) {
            return Err("output paths containing `..` refuse".into());
        }
        let mut parent = absolute.as_path();
        let mut suffix = Vec::new();
        while !parent.try_exists().map_err(|e| e.to_string())? {
            suffix.push(parent.file_name().ok_or("output has no existing ancestor")?.to_owned());
            parent = parent.parent().ok_or("output has no parent")?;
        }
        let mut resolved = fs::canonicalize(parent).map_err(|e| e.to_string())?;
        for name in suffix.into_iter().rev() {
            resolved.push(name);
        }
        Ok(resolved)
    }

    fn admit_output(options: &Options) -> std::result::Result<PathBuf, String> {
        let out = prospective_path(&options.out)?;
        if options.workloads.as_ref().is_some_and(|workloads| {
            out.starts_with(&workloads.output) || workloads.output.starts_with(&out)
        }) {
            return Err(
                "paired report must be outside its native workload build/evidence directory".into(),
            );
        }
        if options
            .paired_cache
            .as_ref()
            .is_some_and(|cache| out.starts_with(cache) || cache.starts_with(&out))
        {
            return Err("paired report must be outside its warm cache".into());
        }
        if options.paired_cache.as_ref().is_some_and(|cache| {
            options.workloads.as_ref().is_some_and(|workload| {
                cache.starts_with(&workload.output) || workload.output.starts_with(cache)
            })
        }) {
            return Err("paired warm cache must be disjoint from new build/evidence output".into());
        }
        for root in [
            &options.request.control,
            &options.request.candidate,
            &options.request.ay,
            &options.request.trust_vc,
        ]
        .into_iter()
        .chain(options.request.dependency_roots.iter())
        {
            let root = prospective_path(root)?;
            if out.starts_with(&root)
                || options
                    .paired_cache
                    .as_ref()
                    .is_some_and(|cache| cache.starts_with(&root) || root.starts_with(cache))
            {
                return Err(
                    "results must be outside every source/toolchain/dependency input".into()
                );
            }
        }
        if out.try_exists().map_err(|e| e.to_string())? {
            return Err("output file already exists".into());
        }
        Ok(out)
    }

    fn publish_new(path: &Path, bytes: &[u8]) -> std::result::Result<(), String> {
        crate::durable_io::atomic_write_new_private(path, bytes).map_err(|error| error.to_string())
    }

    pub(super) fn run(args: &[String]) -> ExitCode {
        let options = match parse(args) {
            Ok(options) => options,
            Err(error) => {
                eprintln!("targo trust gate qualify-pair: {error}\n\n{USAGE}");
                return ExitCode::from(2);
            }
        };
        let output = match admit_output(&options) {
            Ok(path) => path,
            Err(error) => {
                eprintln!("targo trust gate qualify-pair: refused before output creation: {error}");
                return ExitCode::from(1);
            }
        };
        let requested_inputs = match serde_json::to_value(&options.request) {
            Ok(request) => request,
            Err(error) => {
                eprintln!(
                    "targo trust gate qualify-pair: cannot encode exact requested paths: {error}"
                );
                return ExitCode::from(1);
            }
        };
        let stage = options.stage;
        let inspection = (|| -> std::result::Result<serde_json::Value, String> {
            let image = std::env::current_exe().map_err(|error| error.to_string())?;
            let runner = pair::file_identity(&image).map_err(|error| error.to_string())?;
            let pair = pair::inspect(&ControlledGit, options.request)
                .map_err(|error| error.to_string())?;
            let mut report = match stage {
                Stage::Inspect => {
                    serde_json::to_value(pair.report()).map_err(|error| error.to_string())?
                }
                Stage::Receipts => {
                    let checked =
                        pair.check_receipts(&ControlledGit).map_err(|error| error.to_string())?;
                    serde_json::to_value(checked.report()).map_err(|error| error.to_string())?
                }
                Stage::Probes | Stage::Dependencies | Stage::Workloads | Stage::Paired => {
                    let checked =
                        pair.check_receipts(&ControlledGit).map_err(|error| error.to_string())?;
                    let mut runner = crate::native_metadata_root::NativeMetadataRunner::new(
                        options.probe_service,
                        options.probe_host_store.clone(),
                    );
                    let probes = checked.probe_compilers(&ControlledGit, &mut runner);
                    if matches!(stage, Stage::Dependencies | Stage::Workloads | Stage::Paired) {
                        let mut resolver =
                            crate::native_dependency_root::NativeDependencyResolver::new(
                                options.probe_host_store.clone(),
                            );
                        let dependencies =
                            probes.resolve_dependencies(&ControlledGit, &mut resolver);
                        if matches!(stage, Stage::Paired) {
                            #[cfg(any(target_os = "linux", target_os = "macos"))]
                            {
                                super::native::run(
                                    dependencies,
                                    &ControlledGit,
                                    options.workloads.expect("paired stage requires options"),
                                    options.probe_host_store,
                                    options.paired_cache,
                                )
                            }
                            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
                            {
                                serde_json::json!({"status":"refused","reason":"native paired ownership is unsupported on this platform","dependencies":dependencies.report()})
                            }
                        } else if matches!(stage, Stage::Workloads) {
                            let mut producer =
                                crate::native_workload_root::NativeWorkloadProducer::new(
                                    options.probe_host_store,
                                );
                            dependencies
                                .execute_workloads(
                                    &ControlledGit,
                                    &mut producer,
                                    options.workloads.expect("workloads stage requires options"),
                                )
                                .report()
                        } else {
                            dependencies.report()
                        }
                    } else {
                        probes.report()
                    }
                }
            };
            match pair::file_identity(&image) {
                Ok(current) if current == runner => {}
                changed => {
                    report["status"] = serde_json::json!("refused");
                    report["runner_image_refusal"] = serde_json::json!(match changed {
                        Err(error) => format!("paired runner image after checks: {error}"),
                        _ => "paired runner image path bytes changed during checks".into(),
                    });
                }
            }
            // This is an observation of pathname bytes, not authentication of
            // the process image or receipt writer and never launch authority.
            report["runner_image_observation"] =
                serde_json::to_value(runner).map_err(|error| error.to_string())?;
            report["argv"] = serde_json::json!(args);
            Ok(report)
        })();
        let (report, status) = match inspection {
            Ok(report) => {
                let code = if matches!(
                    report["status"].as_str(),
                    Some("refused" | "consumer-workload-observed-with-failures")
                ) {
                    1
                } else {
                    0
                };
                (report, code)
            }
            Err(error) => (
                serde_json::json!({"schema":"trust.paired-qualification.v1", "stage":stage.name(), "status":"refused",
                "claim_scope":"no execution, proof, candidate qualification or publication authority", "reason":error.to_string(),
                "pending_stages":pair::PENDING_STAGES, "requested_inputs":requested_inputs, "argv":args}),
                1,
            ),
        };
        let mut bytes = match serde_json::to_vec_pretty(&report) {
            Ok(bytes) => bytes,
            Err(error) => {
                eprintln!("targo trust gate qualify-pair: cannot encode report: {error}");
                return ExitCode::from(1);
            }
        };
        bytes.push(b'\n');
        if let Err(error) = publish_new(&output, &bytes) {
            eprintln!("targo trust gate qualify-pair: cannot retain report: {error}");
            return ExitCode::from(1);
        }
        println!("{}: {}", report["status"].as_str().unwrap_or("refused"), output.display());
        ExitCode::from(status)
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn unsupported_or_duplicate_stage_options_never_select_execution() {
            assert!(parse(&["run".into()]).unwrap_err().contains("supported stages"));
            assert!(
                parse(&["inspect".into(), "--out".into(), "a".into(), "--out".into(), "b".into()])
                    .unwrap_err()
                    .contains("duplicate")
            );
            let dependency_error = parse(&["dependencies".into()]).unwrap_err();
            assert!(dependency_error.contains("missing required option"));
            assert!(!dependency_error.contains("not implemented"));
            let receipt_error = parse(&["receipts".into()]).unwrap_err();
            assert!(receipt_error.contains("missing required option"));
            assert!(!receipt_error.contains("not implemented"));
        }
        #[test]
        fn forbidden_output_and_alias_are_refused_before_writes() {
            let temporary = tempfile::tempdir().unwrap();
            let root = fs::canonicalize(temporary.path()).unwrap();
            let request = pair::Request {
                control: root.join("control"),
                candidate: root.join("candidate"),
                candidate_commit: "a".repeat(40),
                candidate_receipt: root.join("receipt"),
                ay: root.join("ay"),
                trust_vc: root.join("vc"),
                trust_spec_source: root.join("spec"),
                cargo_home: root.join("home"),
                dependency_roots: Vec::new(),
            };
            fs::create_dir(&request.ay).unwrap();
            std::os::unix::fs::symlink(&request.ay, root.join("alias")).unwrap();
            let options = Options {
                stage: Stage::Inspect,
                request,
                out: root.join("alias/new/report.json"),
                probe_service: None,
                probe_host_store: None,
                workloads: None,
                paired_cache: None,
            };
            assert!(admit_output(&options).is_err());
            assert!(!root.join("ay/new").exists());
        }
        #[test]
        fn publishing_never_overwrites_prior_or_symlink_results() {
            let temporary = tempfile::tempdir().unwrap();
            let path = temporary.path().join("result.json");
            publish_new(&path, b"first").unwrap();
            assert!(publish_new(&path, b"second").is_err());
            assert_eq!(fs::read(&path).unwrap(), b"first");
            let link = temporary.path().join("link.json");
            std::os::unix::fs::symlink(&path, &link).unwrap();
            assert!(publish_new(&link, b"second").is_err());
            assert_eq!(fs::read(&path).unwrap(), b"first");
        }
        #[test]
        fn workloads_plan_keeps_full_finite_budget_and_requires_its_own_new_output() {
            let parent = tempfile::tempdir().unwrap();
            let mut args = vec!["workloads".into()];
            for (name, value) in [
                ("--control", "control"),
                ("--candidate", "candidate"),
                ("--candidate-receipt", "receipt"),
                ("--candidate-commit", "commit"),
                ("--ay", "ay"),
                ("--trust-vc", "vc"),
                ("--trust-spec-source", "spec"),
                ("--out", "report"),
            ] {
                args.push(name.into());
                args.push(parent.path().join(value).to_str().unwrap().into());
            }
            assert!(parse(&args).unwrap_err().contains("--workload-output"));
            args.extend([
                "--workload-output".into(),
                parent.path().join("workload").to_str().unwrap().into(),
                "--repetitions".into(),
                "32".into(),
                "--timeout".into(),
                "3600".into(),
            ]);
            let options = parse(&args).unwrap();
            let native = options.workloads.as_ref().unwrap();
            assert_eq!(native.repetitions, 32);
            assert_eq!(native.timeout, Duration::from_secs(3600));
            assert!(admit_output(&options).is_ok());
            let mut paired = args.clone();
            paired[0] = "paired".into();
            let paired_options = parse(&paired).unwrap();
            assert!(matches!(paired_options.stage, Stage::Paired));
            let paired_budget =
                trust_resource_controller::paired_qualification::budget::Budget::new(
                    32,
                    3_600_000_000_000,
                )
                .unwrap();
            assert_eq!(paired_budget.phases, 70);
            assert!(admit_output(&paired_options).is_ok());
            paired.extend([
                "--paired-cache".into(),
                parent.path().join("cache").to_str().unwrap().into(),
            ]);
            let cached = parse(&paired).unwrap();
            assert!(cached.paired_cache.as_ref().unwrap().ends_with("cache"));
            assert!(admit_output(&cached).is_ok());
            assert!(
                !parent.path().join("cache").exists(),
                "parsing cache locations grants no owner and writes no data"
            );
            let mut wrong_stage = paired.clone();
            wrong_stage[0] = "workloads".into();
            assert!(parse(&wrong_stage).unwrap_err().contains("distinct paired"));
            let mut overlap = paired.clone();
            *overlap.last_mut().unwrap() = parent.path().join("workload").to_str().unwrap().into();
            assert!(admit_output(&parse(&overlap).unwrap()).is_err());
            let mut bad = args.clone();
            *bad.last_mut().unwrap() = "0".into();
            assert!(parse(&bad).is_err());
            let mut bad = args.clone();
            let at = bad.len() - 3;
            bad[at] = "33".into();
            assert!(parse(&bad).is_err());
            let mut bad = args.clone();
            bad[0] = "dependencies".into();
            assert!(parse(&bad).unwrap_err().contains("workload options"));
            assert!(
                !parent.path().join("workload").exists(),
                "parsing a plan grants no output or process owner"
            );
        }
    }
}
