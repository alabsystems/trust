// We need this feature as it changes `dylib` linking behavior and allows us to link to
// `rustc_driver`.
#![feature(rustc_private)]

use std::env;
use std::ffi::OsString;
use std::io::stdout;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr;
use std::{collections::BTreeSet, fs};

use getopts::{Matches, Options};
use rustfmt_nightly as rustfmt;
use tracing::debug;
use tracing_subscriber::EnvFilter;

use crate::rustfmt::{
    CliOptions, EmitMode, FormatReportFormatterBuilder, Input, Session, Version, load_config,
};

fn command_stdout(command: &mut Command, purpose: &str) -> Result<Vec<u8>, String> {
    let output = command
        .output()
        .map_err(|error| format!("could not run {purpose}: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!(
            "{purpose} failed with {}{}{}",
            output.status,
            if stderr.trim().is_empty() { "" } else { ": " },
            stderr.trim(),
        ));
    }
    Ok(output.stdout)
}

#[cfg(unix)]
fn path_from_git_bytes(bytes: Vec<u8>) -> Result<PathBuf, String> {
    use std::os::unix::ffi::OsStringExt as _;

    Ok(PathBuf::from(OsString::from_vec(bytes)))
}

#[cfg(not(unix))]
fn path_from_git_bytes(bytes: Vec<u8>) -> Result<PathBuf, String> {
    String::from_utf8(bytes)
        .map(PathBuf::from)
        .map_err(|error| format!("Git returned a path that is not valid UTF-8: {error}"))
}

fn nul_delimited_paths(output: Vec<u8>) -> Result<Vec<PathBuf>, String> {
    if output.is_empty() {
        return Ok(Vec::new());
    }
    if output.last() != Some(&0) {
        return Err("Git's NUL-delimited path output was truncated".to_owned());
    }
    output[..output.len() - 1]
        .split(|byte| *byte == 0)
        .map(|bytes| {
            if bytes.is_empty() {
                Err("Git returned an empty path".to_owned())
            } else {
                path_from_git_bytes(bytes.to_vec())
            }
        })
        .collect()
}

fn git_changed_files(repo: &Path, commits: &str) -> Result<Vec<PathBuf>, String> {
    let mut cmd = Command::new("git");
    cmd.current_dir(repo)
        .args(["diff", "--name-only", "-z", "--diff-filter=ACMRTUXB"]);
    if commits != "0" {
        cmd.arg(format!("HEAD~{commits}"));
    }
    cmd.arg("--");
    nul_delimited_paths(command_stdout(&mut cmd, "`git diff`")?)
}

fn uncommitted_files(repo: &Path) -> Result<Vec<PathBuf>, String> {
    let mut cmd = Command::new("git");
    cmd.current_dir(repo).args([
        "ls-files",
        "-z",
        "--others",
        "--modified",
        "--exclude-standard",
    ]);
    let mut files = nul_delimited_paths(command_stdout(&mut cmd, "`git ls-files`")?)?
        .into_iter()
        .collect::<BTreeSet<_>>();

    // `git ls-files --modified` compares the worktree to the index, so a
    // staged-only edit is otherwise invisible. An uncommitted check must cover
    // both sides of the index boundary.
    let mut staged = Command::new("git");
    staged.current_dir(repo).args([
        "diff",
        "--cached",
        "--name-only",
        "-z",
        "--diff-filter=ACMRTUXB",
        "--",
    ]);
    files.extend(nul_delimited_paths(command_stdout(
        &mut staged,
        "`git diff --cached`",
    )?)?);
    Ok(files.into_iter().collect())
}

fn is_rust_path(path: &Path) -> bool {
    path.extension().is_some_and(|extension| extension == "rs")
}

fn select_existing_rust_files(
    repo: &Path,
    files: impl IntoIterator<Item = PathBuf>,
) -> Result<Vec<PathBuf>, String> {
    let mut selected = Vec::new();
    for file in files {
        if !is_rust_path(&file) {
            continue;
        }
        let components = file.components().collect::<Vec<_>>();
        if components.is_empty()
            || components
                .iter()
                .any(|component| !matches!(component, std::path::Component::Normal(_)))
        {
            return Err(format!(
                "Git returned an unsafe repository path `{}`",
                file.display()
            ));
        }

        let mut current = repo.to_path_buf();
        let mut missing = false;
        for (index, component) in components.iter().copied().enumerate() {
            let std::path::Component::Normal(component) = component else {
                unreachable!("repository path components were validated above")
            };
            current.push(component);
            let metadata = match fs::symlink_metadata(&current) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    // Deleted/renamed-away inputs need no formatting.
                    missing = true;
                    break;
                }
                Err(error) => {
                    return Err(format!(
                        "could not inspect `{}`: {error}",
                        current.display()
                    ));
                }
            };
            if metadata.file_type().is_symlink() {
                return Err(format!(
                    "refusing to format Rust source through symlink `{}`",
                    current.display()
                ));
            }
            let is_final = index + 1 == components.len();
            if !is_final && !metadata.is_dir() {
                return Err(format!(
                    "Rust source parent `{}` is not a directory",
                    current.display()
                ));
            }
            if is_final && !metadata.is_file() {
                return Err(format!(
                    "Rust source `{}` is not a regular file",
                    current.display()
                ));
            }
        }
        if missing {
            continue;
        }
        selected.push(file);
    }
    Ok(selected)
}

fn candidate_files(
    repo: &Path,
    commits: &str,
    include_uncommitted: bool,
) -> Result<Vec<PathBuf>, String> {
    let mut files = git_changed_files(repo, commits)?
        .into_iter()
        .collect::<BTreeSet<_>>();
    if include_uncommitted {
        files.extend(uncommitted_files(repo)?);
    }
    select_existing_rust_files(repo, files)
}

fn fmt_files(files: &[PathBuf], check: bool) -> Result<i32, String> {
    let (mut config, _) = load_config::<NullOptions>(Some(Path::new(".")), None)
        .map_err(|error| format!("could not load trustfmt configuration: {error}"))?;
    if check {
        // Diff emission never rewrites the input file and records a session
        // difference, which `has_no_errors` maps to a non-zero exit below.
        config.set_cli().emit_mode(EmitMode::Diff);
    }
    // Each Git-selected path is formatted independently. This avoids duplicate
    // module-tree walks and prevents an unselected or symlinked child module
    // from becoming an implicit write target.
    config.set_cli().skip_children(true);

    let mut exit_code = 0;
    let mut out = stdout();
    let mut session = Session::new(config, Some(&mut out));
    for file in files {
        let report = session
            .format(Input::File(file.clone()))
            .map_err(|error| format!("could not format `{}`: {error:?}", file.display()))?;
        if report.has_warnings() {
            eprintln!("{}", FormatReportFormatterBuilder::new(&report).build());
        }
        if !session.has_no_errors() {
            exit_code = 1;
        }
    }
    Ok(exit_code)
}

struct NullOptions;

impl CliOptions for NullOptions {
    fn apply_to(self, _: &mut rustfmt::Config) {
        unreachable!();
    }
    fn config_path(&self) -> Option<&Path> {
        unreachable!();
    }
    fn edition(&self) -> Option<rustfmt_nightly::Edition> {
        unreachable!();
    }
    fn style_edition(&self) -> Option<rustfmt_nightly::StyleEdition> {
        unreachable!();
    }
    fn version(&self) -> Option<Version> {
        unreachable!();
    }
}

fn check_uncommitted(repo: &Path) -> Result<(), String> {
    let uncommitted = uncommitted_files(repo)?
        .into_iter()
        .filter(|path| is_rust_path(path))
        .collect::<Vec<_>>();
    debug!("uncommitted files: {:?}", uncommitted);
    if !uncommitted.is_empty() {
        println!("Found uncommitted Rust source changes:");
        for f in &uncommitted {
            println!("  {}", f.display());
        }
        println!("Commit your work, or run with `-u`.");
        println!("Exiting.");
        return Err("uncommitted Rust source files are present".to_owned());
    }
    Ok(())
}

fn make_opts() -> Options {
    let mut opts = Options::new();
    opts.optflag("h", "help", "show this message");
    opts.optflag("c", "check", "check only, don't modify files");
    opts.optflag("u", "uncommitted", "format uncommitted files");
    opts
}

#[derive(Debug)]
struct Config {
    commits: String,
    uncommitted: bool,
    check: bool,
}

impl Config {
    fn from_args(matches: &Matches, opts: &Options) -> Result<Config, String> {
        // `--help` display help message and quit
        if matches.opt_present("h") {
            let message = format!(
                "\nusage: {} <commits> [options]\n\n\
                 commits: number of commits to format, default: 1",
                env::args_os()
                    .next()
                    .unwrap_or_else(|| OsString::from("git-rustfmt"))
                    .to_string_lossy()
            );
            println!("{}", opts.usage(&message));
            std::process::exit(0);
        }

        let mut config = Config {
            commits: "1".to_owned(),
            uncommitted: false,
            check: false,
        };

        config.check = matches.opt_present("c");

        if matches.opt_present("u") {
            config.uncommitted = true;
        }

        if matches.free.len() > 1 {
            return Err("unknown arguments; use `-h` for usage".to_owned());
        }
        if matches.free.len() == 1 {
            let commits = matches.free[0].trim();
            if u32::from_str(commits).is_err() {
                return Err(format!(
                    "invalid commit count `{commits}`; expected a non-negative integer"
                ));
            }
            config.commits = commits.to_owned();
        }

        Ok(config)
    }
}

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_env("RUSTFMT_LOG"))
        .init();

    let result = (|| {
        let opts = make_opts();
        let matches = opts
            .parse(env::args().skip(1))
            .map_err(|error| format!("could not parse command line: {error}"))?;
        let config = Config::from_args(&matches, &opts)?;
        let repo = Path::new(".");
        if !config.uncommitted {
            check_uncommitted(repo)?;
        }
        let files = candidate_files(repo, &config.commits, config.uncommitted)?;
        debug!("files: {:?}", files);
        fmt_files(&files, config.check)
    })();

    let exit_code = result.unwrap_or_else(|error: String| {
        eprintln!("git-rustfmt: {error}");
        1
    });
    std::process::exit(exit_code);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_option_is_parsed_without_panicking() {
        let opts = make_opts();
        let matches = opts
            .parse(["--check", "--uncommitted", "2"])
            .expect("valid options");
        let config = Config::from_args(&matches, &opts).expect("valid configuration");
        assert!(config.check);
        assert!(config.uncommitted);
        assert_eq!(config.commits, "2");
    }

    #[test]
    fn invalid_commit_counts_are_reported_without_panicking() {
        let opts = make_opts();
        let matches = opts
            .parse(["not-a-count"])
            .expect("syntactically valid options");
        let error = Config::from_args(&matches, &opts).expect_err("invalid count must fail");
        assert!(error.contains("invalid commit count"), "{error}");
    }

    #[test]
    fn nul_delimited_paths_preserve_spaces_and_newlines() {
        assert_eq!(
            nul_delimited_paths(b"src/space name.rs\0src/line\nbreak.rs\0".to_vec()).unwrap(),
            [
                PathBuf::from("src/space name.rs"),
                PathBuf::from("src/line\nbreak.rs")
            ]
        );
        assert!(nul_delimited_paths(b"src/truncated.rs".to_vec()).is_err());
    }

    #[test]
    fn failed_git_commands_are_not_misreported_as_an_empty_diff() {
        let mut command = Command::new("git");
        command.arg("definitely-not-a-git-subcommand");
        let error = command_stdout(&mut command, "test Git command")
            .expect_err("a failed Git command must fail the check");
        assert!(error.contains("failed with"), "{error}");
    }

    #[test]
    fn uncommitted_discovery_includes_staged_only_and_untracked_rust_files() {
        use std::time::{SystemTime, UNIX_EPOCH};

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "git-rustfmt-uncommitted-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&root).expect("create Git fixture");
        let run_git = |args: &[&str]| {
            let mut command = Command::new("git");
            command.current_dir(&root).args(args);
            command_stdout(&mut command, "fixture Git command").expect("fixture Git command");
        };
        run_git(&["init", "--quiet"]);
        run_git(&["config", "user.name", "Trustfmt Test"]);
        run_git(&["config", "user.email", "trustfmt@example.invalid"]);
        run_git(&["config", "commit.gpgsign", "false"]);
        fs::create_dir(root.join("empty-hooks")).expect("create empty hooks directory");
        run_git(&["config", "core.hooksPath", "empty-hooks"]);
        fs::write(root.join("staged.rs"), "fn staged() {}\n").expect("write tracked fixture");
        run_git(&["add", "staged.rs"]);
        run_git(&["commit", "--quiet", "-m", "fixture"]);

        fs::write(root.join("staged.rs"), "fn staged( ) { }\n").expect("modify fixture");
        run_git(&["add", "staged.rs"]);
        fs::write(root.join("untracked.rs"), "fn untracked( ) { }\n")
            .expect("write untracked fixture");

        let files = uncommitted_files(&root).expect("discover uncommitted files");
        assert!(files.contains(&PathBuf::from("staged.rs")));
        assert!(files.contains(&PathBuf::from("untracked.rs")));
        let candidates = candidate_files(&root, "0", true).expect("select candidates");
        assert!(candidates.contains(&PathBuf::from("staged.rs")));
        assert!(candidates.contains(&PathBuf::from("untracked.rs")));

        fs::remove_dir_all(root).expect("remove Git fixture");
    }

    #[cfg(unix)]
    #[test]
    fn rust_source_symlinks_are_rejected() {
        use std::os::unix::fs::symlink;
        use std::time::{SystemTime, UNIX_EPOCH};

        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        let root = env::temp_dir().join(format!(
            "git-rustfmt-symlink-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&root).expect("create test repository root");
        fs::write(root.join("outside.rs"), "fn outside() {}\n").expect("write symlink target");
        symlink("outside.rs", root.join("redirect.rs")).expect("create Rust source symlink");

        let error = select_existing_rust_files(&root, [PathBuf::from("redirect.rs")])
            .expect_err("Rust source symlinks must fail closed");
        assert!(error.contains("symlink"), "{error}");

        fs::create_dir(root.join("outside-dir")).expect("create parent-symlink target");
        fs::write(
            root.join("outside-dir/redirected.rs"),
            "fn redirected() {}\n",
        )
        .expect("write redirected source");
        symlink("outside-dir", root.join("redirect-dir")).expect("create parent symlink");
        let error =
            select_existing_rust_files(&root, [PathBuf::from("redirect-dir/redirected.rs")])
                .expect_err("Rust source parent symlinks must fail closed");
        assert!(error.contains("symlink"), "{error}");
        fs::remove_dir_all(root).expect("remove test repository root");
    }
}
