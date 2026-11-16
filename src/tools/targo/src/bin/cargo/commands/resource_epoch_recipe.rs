// Trust: bounded startup data for a checked harness plan, never execution authority.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use anyhow::{Context as _, Result, ensure};
use serde::{Deserialize, Deserializer};
use std::fs::{File, OpenOptions};
use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _};
use std::path::{Component, Path, PathBuf};
use std::process::Command;

const MAX_RECIPE: usize = 16 * 1024;
const MAX_RECIPES: usize = 64 * 1024;

// This is exactly atpkg-publish artifact::pack::SCRUBBED_ENV. No caller can
// supply an environment map or an inherited authority marker through a recipe.
const SCRUBBED_ENV: &[&str] = &[
    "ALAB_HARNESS_VERSION",
    "CARGO_ENCODED_RUSTFLAGS",
    "CARGO_BUILD_RUSTFLAGS",
    "CARGO_BUILD_RUSTC",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "RUSTUP_TOOLCHAIN",
];

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum Profile {
    Dev,
    Release,
}

// deserialize_with makes the nullable field required, just like every other
// schema field: absent package and an explicitly selected null are distinct.
fn package<'de, D: Deserializer<'de>>(input: D) -> std::result::Result<Option<String>, D::Error> {
    Option::<String>::deserialize(input)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BuildAnalysis {
    cargo_home: PathBuf,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    schema: u32,
    id: u32,
    profile: Profile,
    bin: String,
    jobs: u32,
    #[serde(deserialize_with = "package")]
    package: Option<String>,
    features: Vec<String>,
    default_features: bool,
    all_features: bool,
    offline: bool,
    // Trust: absent requests retain exact-source isolation; only this fixed
    // capability selects complete content freshness, never arbitrary config.
    #[serde(default)]
    content_inputs_v1: bool,
    // Trust: only a fixed observation request with the original dispatch home,
    // never an arbitrary environment/configuration map or a new cache home.
    #[serde(default)]
    build_analysis: Option<BuildAnalysis>,
    version: String,
    rustc: PathBuf,
    rustdoc: PathBuf,
    path: Vec<PathBuf>,
}

#[derive(PartialEq, Eq)]
struct Stamp(u64, u64, u64, i64, i64, i64, i64, u32, u32);

impl Stamp {
    fn of(file: &File) -> Result<Self> {
        let m = file.metadata()?;
        // SAFETY: geteuid observes this process's account only.
        let uid = unsafe { libc::geteuid() };
        ensure!(
            m.is_file()
                && m.mode() & 0o111 != 0
                && m.mode() & 0o222 == 0
                && (m.uid() == uid || m.uid() == 0),
            "recipe SDK driver must be an owned immutable executable"
        );
        Ok(Self(
            m.dev(),
            m.ino(),
            m.len(),
            m.mtime(),
            m.mtime_nsec(),
            m.ctime(),
            m.ctime_nsec(),
            m.mode(),
            m.uid(),
        ))
    }
}

struct Driver {
    path: PathBuf,
    file: File,
    stamp: Stamp,
}

fn absolute(path: &Path) -> bool {
    path.is_absolute()
        && !path
            .components()
            .any(|part| matches!(part, Component::ParentDir))
        && path
            .to_str()
            .is_some_and(|path| !path.chars().any(char::is_control))
}

impl Driver {
    fn open(path: &Path, name: &str) -> Result<Self> {
        ensure!(
            absolute(path)
                && path.file_name().and_then(|part| part.to_str()) == Some(name)
                && !path.components().any(|part| {
                    let part = part.as_os_str().to_string_lossy();
                    part.len() == 6
                        && part.starts_with("stage")
                        && part.as_bytes()[5].is_ascii_digit()
                })
                && path.canonicalize()? == path,
            "recipe must name its exact immutable SDK driver"
        );
        let file = Self::read(path)?;
        let stamp = Stamp::of(&file)?;
        Ok(Self {
            path: path.to_owned(),
            file,
            stamp,
        })
    }

    fn read(path: &Path) -> Result<File> {
        Ok(OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
            .open(path)?)
    }

    fn validate(&self) -> Result<()> {
        ensure!(
            self.path.canonicalize()? == self.path
                && Stamp::of(&self.file)? == self.stamp
                && Stamp::of(&Self::read(&self.path)?)? == self.stamp,
            "recipe SDK driver changed before root launch"
        );
        Ok(())
    }
}

// Only parsed startup data can construct this value. It authorizes no child,
// CPU unit, source acceptance or release; the original controller owns those.
pub(super) struct Recipe {
    input: Input,
    rustc: Driver,
    rustdoc: Driver,
    // Trust: analysis must execute the same immutable SDK Targo that the
    // original plan probes and later queries, rather than the helper's image.
    targo: Option<Driver>,
    path: std::ffi::OsString,
}

fn name(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value.as_bytes()[0].is_ascii_alphanumeric()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
}

fn feature(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && !value.starts_with('-')
        && value.bytes().all(|byte| {
            byte.is_ascii_alphanumeric()
                || matches!(byte, b'_' | b'-' | b'/' | b':' | b'.' | b'+' | b',')
        })
}

impl Recipe {
    pub(super) fn parse_all(rows: &[String], roots: u32) -> Result<Vec<Option<Self>>> {
        ensure!(rows.len() <= roots as usize, "too many root recipes");
        let total = rows.iter().try_fold(0usize, |total, row| {
            ensure!(
                !row.is_empty() && row.len() <= MAX_RECIPE,
                "root recipe exceeded bound"
            );
            total
                .checked_add(row.len())
                .context("root recipe size overflow")
        })?;
        ensure!(
            total <= MAX_RECIPES,
            "root recipes exceeded aggregate bound"
        );
        let mut recipes: Vec<_> = (0..roots).map(|_| None).collect();
        for row in rows {
            let input: Input = serde_json::from_str(row).context("invalid root recipe")?;
            ensure!(
                input.schema == 1 && input.id < roots,
                "foreign root recipe schema or ID"
            );
            let id = input.id as usize;
            ensure!(recipes[id].is_none(), "duplicate root recipe ID");
            ensure!(
                name(&input.bin)
                    && (1..=256).contains(&input.jobs)
                    && input.package.as_deref().is_none_or(name)
                    && input.features.len() <= 64
                    && input.features.iter().all(|value| feature(value)),
                "unsupported root recipe build selection"
            );
            ensure!(
                input.version.len() <= 256 && semver::Version::parse(&input.version).is_ok(),
                "invalid root recipe version"
            );
            ensure!(
                input
                    .build_analysis
                    .as_ref()
                    .is_none_or(|analysis| absolute(&analysis.cargo_home)),
                "analysis request must preserve an absolute cargo cache home"
            );
            ensure!(
                !input.path.is_empty()
                    && input.path.len() <= 64
                    && input.path.iter().all(|path| absolute(path))
                    && input.rustc.parent() == input.rustdoc.parent()
                    && input.path.first().map(PathBuf::as_path) == input.rustc.parent(),
                "recipe PATH must begin with its exact SDK bin directory"
            );
            let path = std::env::join_paths(&input.path).context("invalid recipe PATH")?;
            let rustc = Driver::open(&input.rustc, "trustc")?;
            let rustdoc = Driver::open(&input.rustdoc, "trustdoc")?;
            let targo = input
                .build_analysis
                .as_ref()
                .map(|_| {
                    let bin = input
                        .rustc
                        .parent()
                        .context("recipe SDK has no bin directory")?;
                    Driver::open(&bin.join("targo"), "targo")
                })
                .transpose()?;
            recipes[id] = Some(Self {
                input,
                rustc,
                rustdoc,
                targo,
                path,
            });
        }
        Ok(recipes)
    }

    // Trust: the path is derived from the already checked SDK, never from
    // arbitrary startup executable data. configure revalidates its original pin.
    pub(super) fn program(&self) -> Option<&Path> {
        self.targo.as_ref().map(|driver| driver.path.as_path())
    }

    pub(super) fn configure(&self, command: &mut Command) -> Result<()> {
        self.rustc.validate()?;
        self.rustdoc.validate()?;
        if let Some(targo) = &self.targo {
            targo.validate()?;
        }
        command
            .args(["--locked", "--message-format=json", "--profile"])
            .arg(match self.input.profile {
                Profile::Dev => "dev",
                Profile::Release => "release",
            })
            .arg("-j")
            .arg(self.input.jobs.to_string())
            .arg("--bin")
            .arg(&self.input.bin);
        if let Some(package) = &self.input.package {
            command.arg("--package").arg(package);
        }
        for feature in &self.input.features {
            command.arg("--features").arg(feature);
        }
        if !self.input.default_features {
            command.arg("--no-default-features");
        }
        if self.input.all_features {
            command.arg("--all-features");
        }
        if self.input.offline {
            command.arg("--offline");
        }
        if self.input.content_inputs_v1 {
            command.args([
                "--config",
                "build.fingerprint=\"content\"",
                "-Zchecksum-freshness",
            ]);
        }
        if let Some(analysis) = &self.input.build_analysis {
            command.args([
                "-Zbuild-analysis",
                "--config",
                "build.analysis.enabled=true",
            ]);
            command.env("CARGO_HOME", &analysis.cargo_home);
        }
        for key in SCRUBBED_ENV {
            command.env_remove(key);
        }
        command
            .env("RUSTC", &self.input.rustc)
            .env("RUSTDOC", &self.input.rustdoc)
            .env("PATH", &self.path)
            .env("ALAB_HARNESS_VERSION", &self.input.version);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::os::unix::fs::PermissionsExt as _;

    // These are parser/identity fixtures, never executed or claimed as a SDK.
    fn input() -> (tempfile::TempDir, serde_json::Value) {
        let world = tempfile::tempdir().unwrap();
        let root = world.path().canonicalize().unwrap();
        let bin = root.join("bin");
        std::fs::create_dir(&bin).unwrap();
        for name in ["trustc", "trustdoc", "targo"] {
            let path = bin.join(name);
            std::fs::write(&path, b"unexecuted parser fixture").unwrap();
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o555)).unwrap();
        }
        let value = json!({
            "schema":1,"id":0,"profile":"release","bin":"fixture-tool","jobs":2,
            "package":null,"features":["fixture/feature"],"default_features":false,
            "all_features":false,"offline":true,"version":"1.2.0+g012345678",
            "rustc":bin.join("trustc"),"rustdoc":bin.join("trustdoc"),"path":[bin]
        });
        (world, value)
    }

    #[test]
    fn typed_recipe_lowers_build_choices_and_removes_inherited_wrappers() {
        let (_world, value) = input();
        let rows = [serde_json::to_string(&value).unwrap()];
        let recipes = Recipe::parse_all(&rows, 1).unwrap();
        let mut command = Command::new("unexecuted-targo-fixture");
        recipes[0]
            .as_ref()
            .unwrap()
            .configure(&mut command)
            .unwrap();
        let arguments: Vec<_> = command
            .get_args()
            .map(|arg| arg.to_string_lossy())
            .collect();
        assert!(
            arguments
                .windows(2)
                .any(|pair| pair == ["--profile", "release"])
        );
        assert!(
            arguments
                .windows(2)
                .any(|pair| pair == ["--bin", "fixture-tool"])
        );
        assert!(arguments.iter().any(|arg| arg == "--locked"));
        assert!(arguments.iter().any(|arg| arg == "--message-format=json"));
        assert!(arguments.iter().any(|arg| arg == "--no-default-features"));
        let changes: std::collections::BTreeMap<_, _> = command.get_envs().collect();
        assert_eq!(changes[std::ffi::OsStr::new("RUSTC_WRAPPER")], None);
        assert_eq!(changes[std::ffi::OsStr::new("RUSTUP_TOOLCHAIN")], None);
        assert_eq!(
            changes[std::ffi::OsStr::new("ALAB_HARNESS_VERSION")],
            Some(std::ffi::OsStr::new("1.2.0+g012345678"))
        );
    }

    #[test]
    fn complete_input_request_selects_only_the_fixed_checksum_policy() {
        let (_world, mut value) = input();
        value["content_inputs_v1"] = serde_json::json!(true);
        let recipes = Recipe::parse_all(&[value.to_string()], 1).unwrap();
        let mut command = Command::new("unexecuted-targo-fixture");
        recipes[0]
            .as_ref()
            .unwrap()
            .configure(&mut command)
            .unwrap();
        let arguments: Vec<_> = command.get_args().collect();
        assert!(
            arguments
                .windows(2)
                .any(|pair| pair == ["--config", "build.fingerprint=\"content\""])
        );
        assert!(arguments.iter().any(|arg| *arg == "-Zchecksum-freshness"));
        value["content_inputs_v1"] = serde_json::json!("mtime");
        assert!(Recipe::parse_all(&[value.to_string()], 1).is_err());
    }

    #[test]
    fn analysis_request_preserves_the_original_home_and_only_fixed_options() {
        let (world, mut value) = input();
        let home = world
            .path()
            .canonicalize()
            .unwrap()
            .join("original-cargo-home");
        value["build_analysis"] = json!({"cargo_home":home});
        let recipes = Recipe::parse_all(&[value.to_string()], 1).unwrap();
        assert_eq!(
            recipes[0].as_ref().unwrap().program(),
            Path::new(value["rustc"].as_str().unwrap())
                .parent()
                .map(|bin| bin.join("targo"))
                .as_deref()
        );
        let mut command = Command::new("unexecuted-targo-fixture");
        recipes[0]
            .as_ref()
            .unwrap()
            .configure(&mut command)
            .unwrap();
        let args: Vec<_> = command.get_args().collect();
        assert!(args.iter().any(|arg| *arg == "-Zbuild-analysis"));
        assert!(
            args.windows(2)
                .any(|pair| pair == ["--config", "build.analysis.enabled=true"])
        );
        let changes: std::collections::BTreeMap<_, _> = command.get_envs().collect();
        assert_eq!(
            changes[std::ffi::OsStr::new("CARGO_HOME")],
            Some(home.as_os_str())
        );
        for bad in [
            json!({"cargo_home":"relative"}),
            json!({"cargo_home":"/cache/../other"}),
            json!({"cargo_home":home,"env":{"RUSTFLAGS":"override"}}),
        ] {
            value["build_analysis"] = bad;
            assert!(Recipe::parse_all(&[value.to_string()], 1).is_err());
        }
    }

    #[test]
    fn analysis_targo_replacement_is_refused_after_recipe_admission() {
        let (world, mut value) = input();
        value["build_analysis"] = json!({"cargo_home":world.path().canonicalize().unwrap()});
        let recipes = Recipe::parse_all(&[value.to_string()], 1).unwrap();
        let recipe = recipes[0].as_ref().unwrap();
        let path = recipe.program().unwrap();
        std::fs::rename(path, path.with_file_name("prior-targo")).unwrap();
        std::fs::write(path, b"replacement unexecuted targo fixture").unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o555)).unwrap();
        let mut command = Command::new(path);
        assert!(recipe.configure(&mut command).is_err());
    }

    #[test]
    fn only_analysis_requires_an_existing_immutable_sdk_targo() {
        let (world, mut value) = input();
        let path = world.path().canonicalize().unwrap().join("bin/targo");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        let recipes = Recipe::parse_all(&[value.to_string()], 1).unwrap();
        assert!(recipes[0].as_ref().unwrap().program().is_none());
        value["build_analysis"] = json!({"cargo_home":world.path().canonicalize().unwrap()});
        assert!(Recipe::parse_all(&[value.to_string()], 1).is_err());
        std::fs::remove_file(&path).unwrap();
        assert!(Recipe::parse_all(&[value.to_string()], 1).is_err());
        value.as_object_mut().unwrap().remove("build_analysis");
        let recipes = Recipe::parse_all(&[value.to_string()], 1).unwrap();
        let recipe = recipes[0].as_ref().unwrap();
        assert!(recipe.program().is_none());
        recipe
            .configure(&mut Command::new("unexecuted-helper-fixture"))
            .unwrap();
        value["build_analysis"] = serde_json::Value::Null;
        assert!(
            Recipe::parse_all(&[value.to_string()], 1).unwrap()[0]
                .as_ref()
                .unwrap()
                .program()
                .is_none()
        );
        assert!(Recipe::parse_all(&[], 1).unwrap()[0].is_none());
    }

    #[test]
    fn replaced_sdk_driver_is_refused_after_recipe_admission() {
        let (_world, value) = input();
        let rows = [serde_json::to_string(&value).unwrap()];
        let recipes = Recipe::parse_all(&rows, 1).unwrap();
        let path = Path::new(value["rustc"].as_str().unwrap());
        std::fs::rename(path, path.with_file_name("prior-trustc")).unwrap();
        std::fs::write(path, b"replacement unexecuted fixture").unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o555)).unwrap();
        let mut command = Command::new("unexecuted-targo-fixture");
        assert!(
            recipes[0]
                .as_ref()
                .unwrap()
                .configure(&mut command)
                .is_err()
        );
    }

    #[test]
    fn recipe_requires_explicit_schema_fields_and_rejects_environment_maps() {
        let (_world, value) = input();
        let mut missing = value.clone();
        missing.as_object_mut().unwrap().remove("package");
        assert!(Recipe::parse_all(&[missing.to_string()], 1).is_err());
        let mut environment = value.clone();
        environment["env"] = json!({"RUSTC_WRAPPER":"arbitrary"});
        assert!(Recipe::parse_all(&[environment.to_string()], 1).is_err());
        let duplicate = format!("{},\"id\":0}}", value.to_string().trim_end_matches('}'));
        assert!(Recipe::parse_all(&[duplicate], 1).is_err());
        assert!(Recipe::parse_all(&[value.to_string(), value.to_string()], 2).is_err());
    }

    #[test]
    fn recipe_bounds_apply_before_parsing_or_opening_sdk_files() {
        assert!(Recipe::parse_all(&[" ".repeat(MAX_RECIPE + 1)], 1).is_err());
        assert!(Recipe::parse_all(&vec![" ".repeat(MAX_RECIPE); 5], 5).is_err());
    }
}
