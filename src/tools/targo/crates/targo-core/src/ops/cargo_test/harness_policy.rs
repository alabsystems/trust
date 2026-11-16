//! Trust: per-harness weight and exclusivity for native test actions.
//!
//! `build.test-weight` is how many credits of the build's CPU pool, and so
//! how many libtest threads, an admitted harness holds by default.
//! `build.test-harnesses.<package>.<kind>[.<name>]` sets `weight` or
//! `exclusive` for one target. Both shape admission inside one invocation;
//! neither confers anything on what a test may do.
//!
//! Under a test plan the per-target entries are the plan's `[harness]`
//! table and nothing else: a gate reads one source, so a
//! `build.test-harnesses` entry beside a plan is refused, not merged.
//! `build.test-weight` stays the caller's, as `-j` does.

use std::collections::{BTreeMap, BTreeSet};

use super::plan::ResolvedPlan;
use crate::context::{ConfigKey, ConfigValue, TestHarnessConfig, TestHarnessPackageConfig};
use crate::util::{CargoResult, GlobalContext};
use crate::workspace::{Package, Target, TargetKind, Workspace};

/// The selector spelling of a target's kind (`--lib`, `--bin`, `--test`,
/// `--bench`, `--example`), as the config keys and the JSON records name it.
pub(crate) fn kind_key(target: &Target) -> &'static str {
    match target.kind() {
        TargetKind::Lib(_) => "lib",
        TargetKind::Bin => "bin",
        TargetKind::Test => "test",
        TargetKind::Bench => "bench",
        TargetKind::ExampleLib(_) | TargetKind::ExampleBin => "example",
        TargetKind::CustomBuild => "custom-build",
    }
}

/// How the queue admits one test action, before the invocation's bound.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Admission {
    pub weight: usize,
    /// The weight is a test plan's `[run] test-weight`: the lane's wish for
    /// every harness, which a pool that grants one credit at a time lowers
    /// to 1. A weight the configuration or a harness entry states is an
    /// ask for that harness, and such a pool refuses it.
    pub planned_weight: bool,
    pub exclusive: bool,
    /// Mebibytes counted against the tests' memory budget; 0 counts for
    /// nothing.
    pub memory: usize,
    /// Expected run time in seconds; 0 where nothing says.
    pub seconds: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct HarnessPolicy {
    default_weight: usize,
    /// `default_weight` is a test plan's `[run] test-weight`.
    planned_weight: bool,
    /// A test plan's `[run] harness-memory-mib`: what a harness with no
    /// `memory-mib` of its own is counted for.
    default_memory: usize,
    /// The table the entries came from, as its keys are spelled:
    /// `build.test-harnesses`, or a test plan's `harness`.
    table: &'static str,
    packages: BTreeMap<String, TestHarnessPackageConfig>,
    /// Packages the policy names that are not members of this workspace.
    foreign: BTreeSet<String>,
}

/// What `HarnessPolicy::check_selected` does with an entry for a package
/// outside the workspace that the run does not test.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Unselected {
    /// Warn: the test graph applies the policy, and the entry shapes nothing.
    Warn,
    /// Say nothing: the sequential runner applies none of the policy, and one
    /// configuration file serving several workspaces would otherwise warn on
    /// every plain `targo test`.
    Ignore,
}

impl HarnessPolicy {
    /// The weight of a harness without an entry is a test plan's `[run]
    /// test-weight` (no `build.test-weight` stands over it).
    pub(crate) fn plans_weight(&self) -> bool {
        self.planned_weight
    }

    /// Read and check the configured policy. A zero weight, an unknown kind
    /// or key, or a target a workspace member does not have is refused: a
    /// typo is a policy its author believes is in force.
    ///
    /// With a test plan, the entries are the plan's `[harness]` table, and a
    /// non-empty `build.test-harnesses` beside it is refused.
    pub(crate) fn load(ws: &Workspace<'_>, plan: Option<&ResolvedPlan>) -> CargoResult<Self> {
        refuse_unknown_keys(ws.gctx())?;
        let config = ws.gctx().build_config()?;
        anyhow::ensure!(
            config.test_weight != Some(0),
            "build.test-weight must be positive"
        );
        // A plan states its lane's pool; the configuration's stands over it.
        let planned = plan.and_then(|plan| plan.plan.run.test_weight);
        let planned_weight = config.test_weight.is_none() && planned.is_some();
        let default_weight = config.test_weight.or(planned).unwrap_or(1);
        let configured = config.test_harnesses.clone().unwrap_or_default();
        let (table, packages) = match plan {
            Some(plan) => {
                if let Some(package) = configured.keys().next() {
                    anyhow::bail!(
                        "build.test-harnesses.{package} is set beside test plan `{}`: a plan's \
                         `[harness]` table is the only harness policy of its run; move the \
                         entry into the plan",
                        plan.path.display()
                    );
                }
                ("harness", plan.harness_config())
            }
            None => ("build.test-harnesses", configured),
        };
        let mut policy = Self {
            default_weight,
            planned_weight,
            default_memory: plan
                .and_then(|plan| plan.plan.run.harness_memory_mib)
                .unwrap_or(0),
            table,
            packages,
            foreign: BTreeSet::new(),
        };
        for (package, kind, name, entry) in policy.entries() {
            anyhow::ensure!(
                entry.weight != Some(0),
                "{}.weight must be positive",
                policy.entry_key(package, kind, name)
            );
            anyhow::ensure!(
                entry.memory_mib != Some(0) && entry.seconds != Some(0),
                "{}: `memory-mib` and `seconds` must be 1 or more",
                policy.entry_key(package, kind, name)
            );
        }
        // Configuration is found from the working directory, so one file can
        // serve several workspaces, and a package outside this one may still be
        // tested with `-p`: such entries are checked by `check_selected`.
        let foreign: BTreeSet<String> = policy
            .packages
            .keys()
            .filter(|package| {
                !ws.members()
                    .any(|member| member.name().as_str() == *package)
            })
            .cloned()
            .collect();
        for member in ws.members() {
            policy.check_package(member)?;
        }
        policy.foreign = foreign;
        Ok(policy)
    }

    /// Check the entries naming packages outside the workspace against the
    /// packages this run tests, its harnesses' and its doctests': every
    /// tested version of a package must have each target its entries name.
    /// An entry for a package the run does not test shapes nothing, and is
    /// reported as `unselected` says.
    pub(crate) fn check_selected<'a>(
        &self,
        gctx: &GlobalContext,
        selected: impl IntoIterator<Item = &'a Package>,
        unselected: Unselected,
    ) -> CargoResult<()> {
        let mut versions: BTreeMap<&str, Vec<&Package>> = BTreeMap::new();
        for package in selected {
            let tested = versions.entry(package.name().as_str()).or_default();
            if !tested
                .iter()
                .any(|known| known.package_id() == package.package_id())
            {
                tested.push(package);
            }
        }
        for package in &self.foreign {
            match versions.get(package.as_str()) {
                Some(tested) => {
                    for version in tested {
                        self.check_package(version)?;
                    }
                }
                None => match unselected {
                    Unselected::Warn => gctx.shell().warn(format!(
                        "{}.{package} names no package this run tests",
                        self.table
                    ))?,
                    Unselected::Ignore => {}
                },
            }
        }
        Ok(())
    }

    /// Each entry naming `package` names one of its targets, and gives no
    /// weight above 1 to a target libtest does not run.
    fn check_package(&self, package: &Package) -> CargoResult<()> {
        let name = package.name();
        for (_, kind, target_name, entry) in self
            .entries()
            .filter(|(entry_package, ..)| *entry_package == name.as_str())
        {
            let key = self.entry_key(name.as_str(), kind, target_name);
            let target = package.targets().iter().find(|target| {
                kind_key(target) == kind && target_name.is_none_or(|wanted| target.name() == wanted)
            });
            let Some(target) = target else {
                anyhow::bail!("{key} names no {kind} target of package `{name}`");
            };
            check_unharnessed(&key, target, entry)?;
        }
        Ok(())
    }

    fn entries(
        &self,
    ) -> impl Iterator<Item = (&str, &'static str, Option<&str>, &TestHarnessConfig)> {
        self.packages.iter().flat_map(|(package, config)| {
            let named = [
                ("bin", &config.bin),
                ("test", &config.test),
                ("bench", &config.bench),
                ("example", &config.example),
            ];
            config
                .lib
                .iter()
                .map(move |entry| (package.as_str(), "lib", None, entry))
                .chain(named.into_iter().flat_map(move |(kind, targets)| {
                    targets.iter().flatten().map(move |(name, entry)| {
                        (package.as_str(), kind, Some(name.as_str()), entry)
                    })
                }))
        })
    }

    fn entry(&self, package: &str, target: &Target) -> Option<&TestHarnessConfig> {
        let config = self.packages.get(package)?;
        let named = match target.kind() {
            TargetKind::Lib(_) => return config.lib.as_ref(),
            TargetKind::Bin => &config.bin,
            TargetKind::Test => &config.test,
            TargetKind::Bench => &config.bench,
            TargetKind::ExampleLib(_) | TargetKind::ExampleBin => &config.example,
            TargetKind::CustomBuild => return None,
        };
        named.as_ref()?.get(target.name())
    }

    /// Whether any harness is counted against the memory budget: a plan's
    /// default, or an entry of its own.
    pub(crate) fn counts_memory(&self) -> bool {
        self.default_memory > 0
            || self
                .entries()
                .any(|(_, _, _, entry)| entry.memory_mib.is_some())
    }

    fn entry_key(&self, package: &str, kind: &str, name: Option<&str>) -> String {
        let table = self.table;
        match name {
            Some(name) => format!("{table}.{package}.{kind}.{name}"),
            None => format!("{table}.{package}.{kind}"),
        }
    }

    /// The configured admission of `target` in `package`. An unharnessed
    /// target's process is its own; it holds one credit and is judged by
    /// its exit status, so the default weight never applies to it.
    pub(crate) fn admission(&self, package: &str, target: &Target) -> CargoResult<Admission> {
        let entry = self.entry(package, target).copied().unwrap_or_default();
        check_unharnessed(
            &format!("{}.{package}.{}", self.table, kind_key(target)),
            target,
            &entry,
        )?;
        let weight = match entry.weight {
            Some(weight) => weight,
            None if target.harness() => self.default_weight,
            None => 1,
        };
        Ok(Admission {
            weight,
            planned_weight: self.planned_weight && entry.weight.is_none(),
            exclusive: entry.exclusive.unwrap_or(false),
            memory: entry.memory_mib.unwrap_or(self.default_memory),
            seconds: entry.seconds.unwrap_or(0),
        })
    }
}

/// The config deserializer only warns about a key a struct does not name;
/// `build.test-harnesses.<package>.test.<name>.wieght` would then be a policy
/// its author believes is in force and the queue never sees.
fn refuse_unknown_keys(gctx: &GlobalContext) -> CargoResult<()> {
    const KINDS: [&str; 5] = ["lib", "bin", "test", "bench", "example"];
    // An environment variable cannot spell this map faithfully: package and
    // target names lose their case and separators, and without
    // `-Zadvanced-env` nested keys are not read at all, so such a policy would
    // be silently ignored or misread.
    if let Some((name, _)) = gctx
        .env()
        .find(|(name, _)| name.starts_with("CARGO_BUILD_TEST_HARNESSES"))
    {
        anyhow::bail!(
            "{name} cannot set build.test-harnesses; set it in a config file or with --config"
        );
    }
    let root = ConfigKey::from_str("build.test-harnesses");
    let Some(ConfigValue::Table(packages, _)) = gctx.get_cv_with_env(&root)? else {
        // Absent, or not a table, which deserialization refuses.
        return Ok(());
    };
    for (package, kinds) in sorted(&packages) {
        let ConfigValue::Table(kinds, _) = kinds else {
            continue;
        };
        for (kind, entries) in sorted(kinds) {
            let key = format!("build.test-harnesses.{package}.{kind}");
            anyhow::ensure!(
                KINDS.contains(&kind),
                "{key} (in {}) is not a target kind; expected one of `lib`, `bin`, `test`, `bench` or `example`",
                entries.definition()
            );
            if kind == "lib" {
                refuse_unknown_fields(&key, entries)?;
            } else if let ConfigValue::Table(names, _) = entries {
                for (name, entry) in sorted(names) {
                    refuse_unknown_fields(&format!("{key}.{name}"), entry)?;
                }
            }
        }
    }
    Ok(())
}

fn refuse_unknown_fields(key: &str, entry: &ConfigValue) -> CargoResult<()> {
    if let ConfigValue::Table(fields, _) = entry {
        for (field, value) in sorted(fields) {
            anyhow::ensure!(
                matches!(field, "weight" | "exclusive" | "memory-mib" | "seconds"),
                "{key}.{field} (in {}) is not a harness setting; expected `weight`, `exclusive`, `memory-mib` or `seconds`",
                value.definition()
            );
        }
    }
    Ok(())
}

fn sorted(
    table: &crate::util::data_structures::HashMap<String, ConfigValue>,
) -> Vec<(&str, &ConfigValue)> {
    let mut entries: Vec<_> = table
        .iter()
        .map(|(key, value)| (key.as_str(), value))
        .collect();
    entries.sort_by_key(|(key, _)| *key);
    entries
}

fn check_unharnessed(key: &str, target: &Target, entry: &TestHarnessConfig) -> CargoResult<()> {
    anyhow::ensure!(
        target.harness() || entry.weight.is_none_or(|weight| weight == 1),
        "{key} sets a weight on `{}`, which has `harness = false`; such a target holds one credit and libtest does not run its threads",
        target.name()
    );
    Ok(())
}
