//! Invoke the maintained Bootstrap engine inside the SAME managed Targo root.
//! Original argv selects this route before aliases or project configuration.
//! This does not admit an arbitrary Bootstrap image or construct SDK custody.

use std::ffi::{OsStr, OsString};
use std::io::Write as _;
use std::num::NonZeroU32;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use anyhow::{Context as _, Result, bail, ensure};
use targo::util::GlobalContext;
use trust_resource_controller::client::bootstrap_graph::{EarlyHostStore, PendingHostStore};
use trust_resource_controller::{
    BirthKind, Context, ContextQuery, Cpu, Identity, JobBinding, Subject,
    client::{Client, sdk::validate_sdk_keeper},
};
use trust_resource_provenance::process;

mod commands;

const USAGE: &str = "Usage: targo --unverified resource bootstrap-runtime --bootstrap-shims ABSOLUTE_DIRECTORY -- <Bootstrap arguments>\n\nRuns the maintained engine in this original managed Targo process. Only the sole parsed native-object-leaf build may execute with original fixed Host/GNU/SDK/source/output owners. The closed dependency-inputs <check|prepare> --source ABS --output ABS entry prepares the complete source-declared input envelope before Bootstrap configuration. Other graphs remain unavailable. The shim directory selects inputs; no standalone Bootstrap, replacement pool, runtime directory or saved receipt supplies those owners.\n";
const BRIDGE_UNAVAILABLE: &str = "in-process Bootstrap execution has no qualified Host subgroup/descendant graph bridge; no Bootstrap Steps executed";

pub(super) fn help_command() -> clap::Command {
    clap::Command::new("bootstrap-runtime")
        .about("Use the maintained Bootstrap engine inside the original managed Targo job")
        .after_help(USAGE)
}

/// Read-only compiled classification before admission or Python's Manager.
/// This response routes a request; it never supplies source/readiness custody.
fn scope_request(args: &[OsString]) -> Option<Result<bootstrap::engine::PreparationScope>> {
    if args
        .get(..3)
        .is_none_or(|prefix| prefix != ["--unverified", "resource", "bootstrap-scope"])
    {
        return None;
    }
    Some((|| {
        ensure!(
            args.get(3).is_some_and(|arg| arg == "--"),
            "bootstrap-scope requires -- before the complete original x.py arguments"
        );
        bootstrap::engine::xpy_preparation_scope(&args[4..]).map_err(anyhow::Error::msg)
    })())
}
pub(super) fn scope_help_command() -> clap::Command {
    clap::Command::new("bootstrap-scope")
        .about("Classify original x.py arguments with compiled Bootstrap Flags; routing data only")
}
fn print_scope(scope: bootstrap::engine::PreparationScope) -> std::io::Result<()> {
    use bootstrap::engine::PreparationScope;
    let value = match scope {
        PreparationScope::NotProducer => "none",
        PreparationScope::RequestSources => "request",
        PreparationScope::FullEnvelope => "full",
    };
    let mut output = std::io::stdout().lock();
    writeln!(output, "trust-bootstrap-preparation-scope-v1 {value}")?;
    output.flush()
}

enum Invocation<'a> {
    Help,
    Run {
        shims: &'a OsStr,
        args: &'a [OsString],
    },
}

/// Inspect only the exact original purpose prefix before descriptor imports,
/// logging or threads. Selection tightens creation permissions; it grants no
/// frontend identity, Host context, execution or SDK authority.
pub(super) fn selected_at_entry(args: impl IntoIterator<Item = OsString>) -> bool {
    use trust_resource_controller::bootstrap_graph::{
        ROOT_ARGUMENT_PREFIX as purpose, ROOT_WORKER_ARGUMENT_PREFIX as workers,
    };
    let mut args = args.into_iter();
    let first = args.next();
    let lane = if first.as_deref() == Some(OsStr::new(workers[0])) {
        if args.next().as_deref() != Some(OsStr::new(workers[1])) {
            return false;
        }
        args.next()
    } else {
        first
    };
    lane.as_deref() == Some(OsStr::new(purpose[0]))
        && args.next().as_deref() == Some(OsStr::new(purpose[1]))
        && args.next().as_deref() == Some(OsStr::new(purpose[2]))
}

/// Snapshot only the distinct Host-mapped store7 at the first native entry.
/// This performs no FD allocation/discovery and never selects a pool/SDK.
#[expect(
    clippy::disallowed_methods,
    reason = "original native-entry locators must be checked before configuration can replace or snapshot their custody inputs"
)]
pub(super) fn snapshot_original_store_at_entry(
    args: impl IntoIterator<Item = OsString>,
) -> std::io::Result<PendingHostStore> {
    let selected = selected_at_entry(args);
    let advertised =
        std::env::var_os(trust_resource_controller::bootstrap_graph::HOST_STORE_FD_ENV).is_some();
    if advertised && !selected {
        return Err(std::io::Error::other(
            "original Bootstrap Host-store locator cannot enter another purpose",
        ));
    }
    if selected {
        for name in [
            "BUILD_SLOT_HELD",
            "TRUST_BUILD_LOCK_TOKEN",
            "TRUST_CPU_HANDOFF",
            "TRUST_CPU_IMPLICIT_FD",
            "TRUST_FIXED_CLAIM_HANDOFF_V1",
            trust_build_tree::admission::FIXED_HANDOFF_ENV,
        ] {
            if std::env::var_os(name).is_some() {
                return Err(std::io::Error::other(format!(
                    "Bootstrap original Root cannot replace inherited {name}",
                )));
            }
        }
    }
    trust_resource_controller::client::bootstrap_graph::snapshot_host_store()
}

fn invocation(args: &[OsString]) -> Option<Result<Invocation<'_>>> {
    if !selected_at_entry(args.iter().cloned()) {
        return None;
    }
    let (worker, args) = if args
        .get(..2)
        .is_some_and(|words| words == ["--resource-worker-v3", "--resource-subgroups-v3"])
    {
        (true, &args[2..])
    } else {
        (false, args)
    };
    Some((|| {
        if args
            .get(3)
            .is_some_and(|word| word == "--help" || word == "-h")
            && args.len() == 4
        {
            return Ok(Invocation::Help);
        }
        ensure!(
            worker,
            "Bootstrap engine entry requires the original Host worker/subgroup route"
        );
        ensure!(
            args.get(3).is_some_and(|word| word == "--bootstrap-shims")
                && args.get(5).is_some_and(|word| word == "--"),
            "{USAGE}"
        );
        let shims = args[4].as_os_str();
        ensure!(
            Path::new(shims).is_absolute(),
            "Bootstrap shim input directory must be absolute"
        );
        ensure!(
            shims.as_encoded_bytes().len() <= 4096,
            "Bootstrap shim input path exceeds its bound"
        );
        let original = &args[6..];
        ensure!(
            !original.is_empty(),
            "Bootstrap engine entry requires an explicit closed request"
        );
        ensure!(
            original.len() <= 1024,
            "Bootstrap argument population exceeds its bound"
        );
        let bytes = original.iter().try_fold(0usize, |total, word| {
            total.checked_add(word.as_encoded_bytes().len())
        });
        ensure!(
            bytes.is_some_and(|bytes| bytes <= 1024 * 1024),
            "Bootstrap argument bytes exceed their bound"
        );
        Ok(Invocation::Run {
            shims,
            args: original,
        })
    })())
}

/// Distinct original Full purpose before source/seed creation. The marker is
/// routing DATA only; the SAME compiled Flags parser must classify the whole
/// unchanged x.py request as Full. It grants no engine or native child owner.
fn full_selection(args: &[OsString]) -> Result<Option<&[OsString]>> {
    if args.first().is_none_or(|word| word != "full-request-v1") {
        return Ok(None);
    }
    ensure!(
        args.get(1).is_some_and(|word| word == "--") && args.len() > 2,
        "full-request-v1 requires -- followed by the complete original x.py arguments"
    );
    let original = &args[2..];
    ensure!(
        bootstrap::engine::xpy_preparation_scope(original).map_err(anyhow::Error::msg)?
            == bootstrap::engine::PreparationScope::FullEnvelope,
        "explicit full-request-v1 requires an actual full producing request; display, dry runs and selected developer requests retain their normal entry"
    );
    Ok(Some(original))
}

/// Closed original-Root dependency input grammar; paths select inputs only.
struct DependencySelection<'a> {
    mode: trust_resource_controller::bootstrap_graph::preparation::Mode,
    source: &'a Path,
    output: &'a Path,
}
fn dependency_selection(args: &[OsString]) -> Result<Option<DependencySelection<'_>>> {
    if args.first().is_none_or(|word| word != "dependency-inputs") {
        return Ok(None);
    }
    ensure!(
        args.len() == 6 && args[2] == "--source" && args[4] == "--output",
        "dependency-inputs requires exactly <check|prepare> --source ABS --output ABS"
    );
    use trust_resource_controller::bootstrap_graph::preparation::Mode;
    let mode = match args[1].to_str() {
        Some("check") => Mode::Check,
        Some("prepare") => Mode::Prepare,
        _ => bail!("dependency-inputs mode must be check or prepare"),
    };
    let source = Path::new(&args[3]);
    let output = Path::new(&args[5]);
    ensure!(
        [source, output].iter().all(|path| path.is_absolute()
            && path.as_os_str().as_encoded_bytes().len() <= 4096
            && !path.as_os_str().as_encoded_bytes().contains(&0)),
        "dependency input selections must be bounded absolute paths"
    );
    Ok(Some(DependencySelection {
        mode,
        source,
        output,
    }))
}

fn dependency_inputs(
    root: &OriginalRoot,
    gctx: &GlobalContext,
    selected: DependencySelection<'_>,
) -> Result<()> {
    use trust_resource_controller::bootstrap_graph::preparation::Phase;
    root.revalidate()?;
    let mut inputs =
        root.graph
            .begin_dependency_inputs(selected.source, selected.output, selected.mode)?;
    loop {
        let observation = inputs.observe()?;
        match observation.phase {
            Phase::Fetching | Phase::CheckingOffline => break,
            Phase::Materializing | Phase::ValidatingSeed => {
                inputs.check_current()?;
                std::thread::sleep(Duration::from_millis(50));
            }
            Phase::Quarantined => bail!(
                "native dependency inputs were quarantined; actual original owners remain retained"
            ),
            Phase::Complete => {
                bail!("dependency input progress cannot substitute for actual scoped library work")
            }
        }
    }
    let work = inputs.input_work()?;
    let finished = inputs.scoped_input_work(|| {
        targo::context::dependency_inputs::fetch_all(
            work,
            inputs.original_source()?,
            inputs.original_scheduler(),
            gctx,
        )
        .map_err(std::io::Error::other)
    })?;
    let retired = inputs.finish(finished.into_work())?;
    ensure!(
        retired.belongs_to(&root.graph),
        "retired dependency inputs belong to a different original Root"
    );
    retired.check_current()?;
    root.revalidate_context()?;
    retired.check_current()?;
    Ok(())
}

/// Holds the actual pinned Client and immutable original context through the
/// engine call. The observation and numerical ceiling grant no new resources.
struct OriginalRoot {
    client: Client,
    query: ContextQuery,
    context: Context,
    graph: std::sync::Arc<bootstrap::engine::OriginalHostGraph>,
    ceiling: NonZeroU32,
}

fn deadline() -> Result<Instant> {
    Instant::now()
        .checked_add(Duration::from_secs(8))
        .context("Bootstrap context deadline overflows")
}

fn own_identity() -> Result<Identity> {
    let actual = process::read_identity(std::process::id())?;
    Ok(Identity {
        pid: actual.pid,
        birth: actual.birth,
        birth_kind: BirthKind::MacosWallMicroseconds,
    })
}

fn fixed_root(context: &Context, own: Identity) -> Result<NonZeroU32> {
    ensure!(
        context.original_root == own && context.subject == (Subject::Root { identity: own }),
        "Bootstrap engine requires this actual original Root, not a borrowed member"
    );
    let Cpu::RetainedFixed { units, .. } = context.cpu else {
        bail!(
            "Bootstrap engine requires an original paid fixed Root; context data cannot acquire CPU"
        );
    };
    NonZeroU32::new(units).context("Bootstrap original Root has no fixed execution ceiling")
}

fn require_unadvertised_manager(token: Option<&OsStr>) -> Result<()> {
    ensure!(
        token.is_none(),
        "Bootstrap engine cannot promote an inherited Manager holder into owned custody"
    );
    Ok(())
}

impl OriginalRoot {
    #[expect(
        clippy::disallowed_methods,
        reason = "authenticate the live original Manager and private Host-job locators, not project configuration or a cached environment projection"
    )]
    fn authenticate(gctx: &GlobalContext, original_store: EarlyHostStore) -> Result<Self> {
        require_unadvertised_manager(std::env::var_os("TRUST_BUILD_LOCK_TOKEN").as_deref())?;
        // This clones the SAME checked native-entry object, never reimports
        // environment numbers or substitutes a fresh zero/token server.
        let scheduler = gctx
            .jobserver_from_env()?
            .cloned()
            .context("Bootstrap engine requires the original early-captured GNU owner")?;
        let binding = JobBinding::from_locator(
            &std::env::var("ATERM_RESOURCE_JOB_V3")
                .context("Bootstrap engine has no original private Host job locator")?,
        )?;
        let mut call_attempt = [0; 16];
        use std::io::Read as _;
        let mut random = std::fs::File::open("/dev/urandom")?;
        while call_attempt == [0; 16] || call_attempt == binding.root_attempt {
            random.read_exact(&mut call_attempt)?;
        }
        let query = ContextQuery {
            binding,
            call_attempt,
        };
        let at = deadline()?;
        let client = original_store.discover(at)?;
        let reply = client.context_with_sdk(&query, at)?;
        let ceiling = fixed_root(&reply.context, own_identity()?)?;
        validate_sdk_keeper(&reply.context)
            .context("Bootstrap original managed Targo SDK custody is unavailable")?;
        ensure!(
            Instant::now() < at,
            "Bootstrap original context lookup crossed its deadline"
        );
        let mut graph_nonce = [0; 16];
        while graph_nonce == [0; 16]
            || graph_nonce == query.call_attempt
            || graph_nonce == query.binding.root_attempt
        {
            random.read_exact(&mut graph_nonce)?;
        }
        let support = client.bootstrap_graph_support(
            &trust_resource_controller::bootstrap_graph::SupportQuery {
                key: trust_resource_controller::bootstrap_graph::Key {
                    query: query.clone(),
                    graph: graph_nonce,
                },
            },
            at,
        )?;
        ensure!(
            support.observation() == &reply,
            "Bootstrap original graph context changed"
        );
        // SAFETY: this actual native entry retained the same early GNU owner,
        // authenticated its own original fixed Root/SDK and pinned Client, and
        // obtained this opaque support from that exact Client. No replacement
        // Jobserver, environment reimport, borrowed holder or data owner exists.
        let graph = unsafe {
            bootstrap::engine::OriginalHostGraph::from_original_root(
                client.clone(),
                support,
                scheduler,
            )
        }?;
        Ok(Self {
            client,
            query,
            context: reply.context,
            graph: std::sync::Arc::new(graph),
            ceiling,
        })
    }

    fn revalidate(&self) -> Result<()> {
        self.graph.check()?;
        self.revalidate_context()
    }

    // Final Root/SDK observation is independent of the deliberately consumed
    // source graph. Only the typed retirement caller may use this after close.
    fn revalidate_context(&self) -> Result<()> {
        let at = deadline()?.min(self.graph.original_deadline());
        let reply = self.client.context_with_sdk(&self.query, at)?;
        ensure!(
            reply.context == self.context,
            "Bootstrap original Host/root resource context changed"
        );
        ensure!(
            fixed_root(&reply.context, own_identity()?)? == self.ceiling,
            "Bootstrap original fixed ceiling changed"
        );
        validate_sdk_keeper(&reply.context)?;
        ensure!(
            Instant::now() < at,
            "Bootstrap original context recheck crossed its deadline"
        );
        Ok(())
    }
}

pub(super) fn dispatch(args: &[OsString], original_store: EarlyHostStore) -> Option<Result<()>> {
    if let Some(scope) = scope_request(args) {
        return Some(scope.and_then(|scope| print_scope(scope).map_err(Into::into)));
    }
    let invocation = invocation(args)?;
    Some((|| {
        let invocation = invocation?;
        let Invocation::Run {
            shims,
            args: original,
        } = invocation
        else {
            let mut output = std::io::stdout().lock();
            output.write_all(USAGE.as_bytes())?;
            output.flush()?;
            return Ok(());
        };
        dependency_selection(original)?;
        let full = full_selection(original)?;
        super::configure_trust_execution_policy("build", false, true)?;
        let gctx = GlobalContext::default()?;
        let original_root = OriginalRoot::authenticate(&gctx, original_store)?;
        if let Some(selected) = dependency_selection(original)? {
            return dependency_inputs(&original_root, &gctx, selected);
        }
        if full.is_some() {
            // The native issuer/member/queued-credit/engine continuation must
            // exist together before this route can acquire source or report
            // support. No prep-then-standalone, saved marker or empty graph.
            bail!(
                "original full-request-v1 compilation continuation is not yet qualified; no source owner or Bootstrap Steps acquired"
            );
        }
        let request = bootstrap::engine::Request::new(original.to_vec(), original_root.ceiling)
            .with_bootstrap_shims(PathBuf::from(shims));
        let outcome = bootstrap::engine::run_with_original_graph(
            request,
            std::sync::Arc::clone(&original_root.graph),
            |preparation| {
                original_root
                    .revalidate()
                    .map_err(|error| error.to_string())?;
                // The complete parsed selection is necessary but grants no
                // owner. Only this actual Preparation can consume the SAME
                // command lease and bind its original source/protected scope.
                if !preparation.plan().is_native_object_leaf()||preparation.plan().dry_run() {
                    return Err(BRIDGE_UNAVAILABLE.to_owned());
                }
                if original_root.ceiling.get()<2 {
                    return Err("native object needs a real supplementary original Root GNU credit; width one remains unsupported".into());
                }
                preparation.protect(original_root.graph.original_deadline())
            },
        )
        .map_err(anyhow::Error::msg)?;
        // A parsed selector or an empty Step cache cannot report production.
        // Require the actual SAME retained Host completion and sealed artifact.
        outcome
            .check_execution_scope()
            .map_err(anyhow::Error::msg)?;
        ensure!(
            !outcome.has_completed_runtime(),
            "native object must not claim a completed runtime"
        );
        let observation = original_root.graph.native_object_result()?;
        ensure!(observation.bytes >= 32, "native object result is empty");
        original_root.revalidate()?;
        // This Outcome remains open and owns the actual original guards. No
        // local join/status/marker releases WITHHELD or claims whole-graph/SDK
        // completion; the original Host still retires its real Root after exit.
        Ok(())
    })())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn words(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }
    fn hosted(values: &[&str]) -> Vec<OsString> {
        let mut out = words(&[
            "--resource-worker-v3",
            "--resource-subgroups-v3",
            "--unverified",
            "resource",
            "bootstrap-runtime",
        ]);
        out.extend(words(values));
        out
    }
    #[test]
    fn original_full_grammar_preserves_entire_native_request_without_selecting_subsets() {
        let words = |args: &[&str]| args.iter().map(OsString::from).collect::<Vec<_>>();
        for args in [
            vec!["full-request-v1", "--", "build"],
            vec!["full-request-v1", "--", "b", "--stage=2", "compiler/rustc"],
            vec![
                "full-request-v1",
                "--",
                "test",
                "tests/ui",
                "--",
                "--stage=1",
            ],
        ] {
            let args = words(&args);
            assert_eq!(full_selection(&args).unwrap().unwrap(), &args[2..]);
        }
        for args in [
            vec!["full-request-v1"],
            vec!["full-request-v1", "--"],
            vec!["full-request-v1", "build"],
            vec!["full-request-v1", "--", "--help"],
            vec!["full-request-v1", "--", "build", "--dry-run"],
            vec![
                "full-request-v1",
                "--",
                "build",
                "--stage=1",
                "compiler/rustc",
            ],
            vec!["full-request-v1", "--", "build", "--invented-bypass"],
        ] {
            assert!(full_selection(&words(&args)).is_err(), "{args:?}");
        }
        assert!(
            full_selection(&words(&["dependency-inputs", "check"]))
                .unwrap()
                .is_none()
        );
        assert!(
            full_selection(&words(&["build", "--stage=1", "native-object-leaf"]))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn scope_data_uses_only_complete_compiled_flags_without_original_root_import() {
        let command = |tail: &[&str]| {
            let mut args = words(&["--unverified", "resource", "bootstrap-scope", "--"]);
            args.extend(words(tail));
            args
        };
        use bootstrap::engine::PreparationScope;
        assert!(matches!(
            scope_request(&command(&["build"])),
            Some(Ok(PreparationScope::FullEnvelope))
        ));
        assert!(matches!(
            scope_request(&command(&["b", "--stage=1", "compiler/rustc"])),
            Some(Ok(PreparationScope::RequestSources))
        ));
        assert!(matches!(
            scope_request(&command(&["test", "tests/ui", "--", "--stage=1"])),
            Some(Ok(PreparationScope::FullEnvelope))
        ));
        assert!(matches!(
            scope_request(&command(&["build", "--help"])),
            Some(Ok(PreparationScope::NotProducer))
        ));
        assert!(matches!(
            scope_request(&command(&["build", "--skip-full-envelope"])),
            Some(Err(_))
        ));
        assert!(!selected_at_entry(command(&["build"])));
    }

    #[test]
    fn dependency_input_entry_is_closed_and_does_not_accept_subsets() {
        for mode in ["check", "prepare"] {
            let args = words(&[
                "dependency-inputs",
                mode,
                "--source",
                "/repo",
                "--output",
                "/out",
            ]);
            let selected = dependency_selection(&args).unwrap().unwrap();
            assert_eq!(selected.source, Path::new("/repo"));
            assert_eq!(selected.output, Path::new("/out"));
        }
        for tail in [
            vec!["dependency-inputs"],
            vec![
                "dependency-inputs",
                "complete",
                "--source",
                "/repo",
                "--output",
                "/out",
            ],
            vec![
                "dependency-inputs",
                "check",
                "--source",
                "relative",
                "--output",
                "/out",
            ],
            vec![
                "dependency-inputs",
                "check",
                "--output",
                "/out",
                "--source",
                "/repo",
            ],
            vec![
                "dependency-inputs",
                "prepare",
                "--source",
                "/repo",
                "--output",
                "/out",
                "--manifest-path",
                "x/Cargo.toml",
            ],
            vec![
                "dependency-inputs",
                "check",
                "--source",
                "/repo",
                "--output",
                "/out",
                "--target",
                "x",
            ],
        ] {
            assert!(dependency_selection(&words(&tail)).is_err(), "{tail:?}");
        }
        assert!(
            dependency_selection(&words(&["build", "--stage", "0", "compiler/rustc"]))
                .unwrap()
                .is_none()
        );
    }
    #[test]
    fn bootstrap_entry_is_only_the_original_exact_purpose_and_lane() {
        for value in [
            words(&["resource", "bootstrap-runtime", "--help"]),
            words(&["--unverified", "bootstrap-runtime", "--help"]),
            words(&[
                "--unverified",
                "resource",
                "fixed",
                "--",
                "bootstrap-runtime",
            ]),
            words(&["--unverified", "run", "--", "resource", "bootstrap-runtime"]),
        ] {
            assert!(invocation(&value).is_none());
        }
        for flag in ["--help", "-h"] {
            for args in [
                words(&["--unverified", "resource", "bootstrap-runtime", flag]),
                hosted(&[flag]),
            ] {
                assert!(matches!(invocation(&args), Some(Ok(Invocation::Help))));
            }
        }
    }
    #[test]
    fn bootstrap_entry_refuses_missing_host_or_explicit_request_before_engine() {
        assert!(matches!(
            invocation(&words(&[
                "--unverified",
                "resource",
                "bootstrap-runtime",
                "--",
                "build"
            ])),
            Some(Err(_))
        ));
        for tail in [vec![], vec!["--"], vec!["build"]] {
            assert!(matches!(invocation(&hosted(&tail)), Some(Err(_))));
        }
        for flag in ["--help", "-h"] {
            for args in [
                words(&[
                    "--unverified",
                    "resource",
                    "bootstrap-runtime",
                    flag,
                    "extra",
                ]),
                hosted(&[flag, "extra"]),
            ] {
                assert!(matches!(invocation(&args), Some(Err(_))));
            }
        }
    }
    #[test]
    fn bootstrap_native_setup_selects_only_the_exact_bounded_original_prefix() {
        for value in [
            words(&["--unverified", "resource", "bootstrap-runtime"]),
            hosted(&[]),
        ] {
            assert!(selected_at_entry(value.into_iter().chain(
                std::iter::from_fn(|| {
                    panic!("entry selector inspected arguments beyond the purpose prefix")
                })
            )));
        }
        for value in [
            words(&["--unverified", "run", "--", "resource", "bootstrap-runtime"]),
            words(&[
                "--unverified",
                "resource",
                "fixed",
                "--",
                "bootstrap-runtime",
            ]),
            words(&["trust", "resource", "bootstrap-runtime"]),
            words(&[
                "--resource-worker-v3",
                "--unverified",
                "resource",
                "bootstrap-runtime",
            ]),
            words(&["--unverified", "resource"]),
        ] {
            assert!(!selected_at_entry(value));
        }
    }
    #[test]
    fn bootstrap_entry_passes_the_same_complete_engine_arguments() {
        let args = hosted(&[
            "--bootstrap-shims",
            "/original/shims",
            "--",
            "build",
            "--stage",
            "1",
            "--src",
            "/original source",
            "--config",
            "/actual/config.toml",
            "frontend-runtime-owner",
        ]);
        let Some(Ok(Invocation::Run {
            shims,
            args: actual,
        })) = invocation(&args)
        else {
            panic!("closed route refused");
        };
        assert_eq!(shims, OsStr::new("/original/shims"));
        assert_eq!(actual, &args[8..]);
        assert_eq!(
            actual.last().map(OsString::as_os_str),
            Some(OsStr::new("frontend-runtime-owner"))
        );
    }
    #[test]
    fn bootstrap_entry_checks_complete_argument_population_and_bytes() {
        let mut args = hosted(&["--bootstrap-shims", "/original/shims", "--"]);
        args.extend((0..1025).map(|_| OsString::from("x")));
        assert!(matches!(invocation(&args), Some(Err(_))));
        let mut args = hosted(&["--bootstrap-shims", "/original/shims", "--"]);
        args.push(OsString::from("x".repeat(1024 * 1024 + 1)));
        assert!(matches!(invocation(&args), Some(Err(_))));
    }
    #[test]
    fn bootstrap_entry_never_promotes_even_an_empty_or_plausible_manager_token() {
        assert!(require_unadvertised_manager(None).is_ok());
        for token in ["", "actual-looking-parent-token", "invalid"] {
            assert!(require_unadvertised_manager(Some(OsStr::new(token))).is_err());
        }
    }
    #[test]
    fn bootstrap_entry_requires_an_explicit_bounded_absolute_shim_input() {
        for value in ["", ".", "relative/path"] {
            let args = hosted(&["--bootstrap-shims", value, "--", "build"]);
            assert!(matches!(invocation(&args), Some(Err(_))));
        }
        let path = format!("/{}", "x".repeat(4096));
        let args = hosted(&["--bootstrap-shims", &path, "--", "build"]);
        assert!(matches!(invocation(&args), Some(Err(_))));
        let args = hosted(&["--bootstrap-shims", "/original/shims", "--"]);
        assert!(matches!(invocation(&args), Some(Err(_))));
    }
    #[test]
    fn bootstrap_entry_checks_the_actual_root_subject_and_paid_fixed_ceiling() {
        use trust_resource_controller::{FileIdentity, Memory};
        let own = Identity {
            pid: 42,
            birth: 7,
            birth_kind: BirthKind::MacosWallMicroseconds,
        };
        let context = Context {
            session: "observation-only".into(),
            root_attempt: [1; 16],
            host: "host".into(),
            boot: "boot".into(),
            original_root: own,
            subject: Subject::Root { identity: own },
            cpu: Cpu::RetainedFixed {
                units: 2,
                native_manifest: FileIdentity {
                    device: 1,
                    inode: 2,
                },
            },
            memory: Memory {
                bytes: 1024,
                namespace: [2; 16],
                marker: "memory".into(),
                epoch: [3; 16],
                guard: FileIdentity {
                    device: 1,
                    inode: 3,
                },
            },
            // This DATA fixture cannot authenticate a Host or SDK. Production
            // separately requires the live Client exchange and actual keeper.
            sdk: None,
        };
        assert_eq!(fixed_root(&context, own).unwrap().get(), 2);
        let mut changed = context.clone();
        changed.original_root.birth += 1;
        assert!(fixed_root(&changed, own).is_err());
        let mut changed = context.clone();
        changed.subject = Subject::RegisteredMember {
            identity: own,
            attempt: [4; 16],
        };
        assert!(fixed_root(&changed, own).is_err());
        let mut changed = context.clone();
        changed.cpu = Cpu::RetainedFixed {
            units: 0,
            native_manifest: FileIdentity {
                device: 1,
                inode: 2,
            },
        };
        assert!(fixed_root(&changed, own).is_err());
        let mut changed = context;
        changed.cpu = Cpu::CooperativeShared {
            ceiling: 2,
            native_manifest: FileIdentity {
                device: 1,
                inode: 2,
            },
        };
        assert!(fixed_root(&changed, own).is_err());
    }
}
