use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;
use std::{env, fs};

use super::claims::WALKTHROUGH_SPECS;
use super::report::{WalkthroughBin, WalkthroughExecution};
use super::terminal::display_path;

pub(super) fn run_walkthroughs(manifest_path: &Path) -> Result<Vec<WalkthroughExecution>, String> {
    let targo = resolve_targo()?;
    let bins = discover_walkthrough_bins(manifest_path)?;
    let manifest_directory = manifest_dir(manifest_path)?;
    let mut executions = Vec::new();

    for spec in WALKTHROUGH_SPECS {
        if let Some(source) = bins.get(spec.name) {
            let bin = WalkthroughBin { name: spec.name.to_string(), source: source.clone() };
            executions.push(run_walkthrough_bin(manifest_path, &targo, &bin, spec.validate));
        } else {
            executions.push(missing_walkthrough_execution(manifest_directory, spec.name));
        }
    }

    for (name, source) in bins {
        if WALKTHROUGH_SPECS.iter().any(|spec| spec.name == name) {
            continue;
        }
        executions.push(unexpected_walkthrough_execution(manifest_directory, &name, &source));
    }

    Ok(executions)
}

fn discover_walkthrough_bins(manifest_path: &Path) -> Result<BTreeMap<String, PathBuf>, String> {
    let manifest_directory = manifest_dir(manifest_path)?;
    let src_bin = manifest_directory.join("src/bin");
    if !src_bin.is_dir() {
        return Ok(BTreeMap::new());
    }

    let entries = fs::read_dir(&src_bin).map_err(|error| {
        format!(
            "targo trust hardened-lab: could not read walkthrough bin directory {}: {error}",
            src_bin.display()
        )
    })?;
    let mut bins = BTreeMap::<String, PathBuf>::new();

    for entry in entries {
        let entry = entry.map_err(|error| {
            format!(
                "targo trust hardened-lab: could not read walkthrough bin entry in {}: {error}",
                src_bin.display()
            )
        })?;
        let path = entry.path();
        let file_type = entry.file_type().map_err(|error| {
            format!(
                "targo trust hardened-lab: could not inspect walkthrough bin entry {}: {error}",
                path.display()
            )
        })?;

        if file_type.is_file()
            && path.extension().and_then(|extension| extension.to_str()) == Some("rs")
        {
            let name = path.file_stem().and_then(|stem| stem.to_str()).ok_or_else(|| {
                format!(
                    "targo trust hardened-lab: walkthrough bin path is not valid UTF-8: {}",
                    path.display()
                )
            })?;
            if !name.starts_with('.') {
                bins.insert(name.to_string(), path);
            }
        } else if file_type.is_dir() && path.join("main.rs").is_file() {
            let name = path.file_name().and_then(|stem| stem.to_str()).ok_or_else(|| {
                format!(
                    "targo trust hardened-lab: walkthrough bin path is not valid UTF-8: {}",
                    path.display()
                )
            })?;
            if !name.starts_with('.') {
                bins.insert(name.to_string(), path.join("main.rs"));
            }
        }
    }

    Ok(bins)
}

fn host_executable_name(tool: &str) -> String {
    if cfg!(windows) { format!("{tool}.exe") } else { tool.to_string() }
}

fn path_is_executable_file(path: &Path) -> bool {
    if !path.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        path.metadata().map(|metadata| metadata.permissions().mode() & 0o111 != 0).unwrap_or(false)
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn require_canonical_targo(path: PathBuf, source: &str) -> Result<PathBuf, String> {
    let expected_name = host_executable_name("targo");
    let actual_name = path.file_name().and_then(|name| name.to_str());
    if actual_name != Some(expected_name.as_str()) {
        return Err(format!(
            "targo trust hardened-lab: {source} must point at canonical `{expected_name}`, got {}",
            path.display()
        ));
    }
    if !path_is_executable_file(&path) {
        return Err(format!(
            "targo trust hardened-lab: {source} is not an executable canonical `{expected_name}`: {}",
            path.display()
        ));
    }
    Ok(path)
}

fn resolve_targo() -> Result<PathBuf, String> {
    // Hardened-lab does not produce compiler-backed proof evidence: it combines
    // the standalone source analyzer with tracked, executable walkthroughs.
    // Requiring a trustc merely to build those walkthroughs makes the command
    // unusable in standalone/test installations and does not authenticate any
    // evidence it actually claims. Keep compiler-anchored discovery confined to
    // verification commands; here an explicit canonical TARGO or installed
    // sibling targo is the complete frontend requirement.
    if let Some(path) = env::var_os("TARGO").map(PathBuf::from) {
        return require_canonical_targo(path, "TARGO");
    }

    let current_exe = env::current_exe().map_err(|error| {
        format!("targo trust hardened-lab: could not resolve current executable: {error}")
    })?;
    let bin_dir = current_exe.parent().ok_or_else(|| {
        format!(
            "targo trust hardened-lab: current executable path has no parent directory: {}",
            current_exe.display()
        )
    })?;
    require_canonical_targo(bin_dir.join(host_executable_name("targo")), "sibling Trust tool")
}

fn run_walkthrough_bin(
    manifest_path: &Path,
    targo: &Path,
    bin: &WalkthroughBin,
    validate: fn(&str) -> Vec<String>,
) -> WalkthroughExecution {
    let manifest_directory =
        manifest_dir(manifest_path).expect("validated manifest path has a parent");
    let command = format!(
        "{} build --message-format=json --manifest-path {} --bin {}",
        targo.display(),
        manifest_path.display(),
        bin.name
    );

    let mut build_command = Command::new(targo);
    build_command
        .args(["--unverified", "build", "--message-format=json", "--manifest-path"])
        .arg(manifest_path)
        .args(["--bin", &bin.name])
        .current_dir(manifest_directory);
    let build_output = match crate::bounded_process::output(
        &mut build_command,
        &format!("hardened-lab walkthrough build `{}`", bin.name),
        64 * 1024 * 1024,
        Duration::from_secs(10 * 60),
    ) {
        Ok(output) => output,
        Err(error) => {
            return WalkthroughExecution {
                bin: bin.name.clone(),
                source: display_path(&bin.source),
                command,
                working_directory: display_path(manifest_directory),
                success: false,
                process_success: false,
                transcript_passed: false,
                status: "targo build spawn failed".to_string(),
                status_code: None,
                stdout: String::new(),
                stderr: format!("failed to run targo walkthrough build command: {error}"),
                transcript_errors: vec!["walkthrough build did not start".to_string()],
            };
        }
    };
    let build_status = build_output.status;
    let build_stdout = match String::from_utf8(build_output.stdout) {
        Ok(stdout) => stdout,
        Err(error) => {
            return WalkthroughExecution {
                bin: bin.name.clone(),
                source: display_path(&bin.source),
                command,
                working_directory: display_path(manifest_directory),
                success: false,
                process_success: false,
                transcript_passed: false,
                status: format!("targo build {build_status}"),
                status_code: build_status.code(),
                stdout: String::from_utf8_lossy(&error.into_bytes()).into_owned(),
                stderr: String::from_utf8_lossy(&build_output.stderr).into_owned(),
                transcript_errors: vec!["targo build stdout must be valid UTF-8".to_string()],
            };
        }
    };
    let build_stderr = String::from_utf8_lossy(&build_output.stderr).into_owned();
    if !build_status.success() {
        return WalkthroughExecution {
            bin: bin.name.clone(),
            source: display_path(&bin.source),
            command,
            working_directory: display_path(manifest_directory),
            success: false,
            process_success: false,
            transcript_passed: false,
            status: format!("targo build {build_status}"),
            status_code: build_status.code(),
            stdout: build_stdout,
            stderr: build_stderr,
            transcript_errors: vec!["walkthrough targo build failed".to_string()],
        };
    }

    let Some(executable) = targo_build_executable(&build_stdout, &bin.name) else {
        return WalkthroughExecution {
            bin: bin.name.clone(),
            source: display_path(&bin.source),
            command,
            working_directory: display_path(manifest_directory),
            success: false,
            process_success: false,
            transcript_passed: false,
            status: "targo build did not report executable".to_string(),
            status_code: Some(0),
            stdout: build_stdout,
            stderr: build_stderr,
            transcript_errors: vec![format!(
                "walkthrough targo build did not report executable for `{}`",
                bin.name
            )],
        };
    };
    let command = format!("{command} && {}", executable.display());

    let mut walkthrough_command = Command::new(&executable);
    walkthrough_command.current_dir(manifest_directory);
    match crate::bounded_process::output(
        &mut walkthrough_command,
        &format!("hardened-lab walkthrough `{}`", bin.name),
        8 * 1024 * 1024,
        Duration::from_secs(60),
    ) {
        Ok(output) => {
            let process_success = output.status.success();
            let mut transcript_errors = Vec::new();
            let (stdout, stdout_valid_utf8) =
                decode_walkthrough_stream(output.stdout, "stdout", &mut transcript_errors);
            let (stderr, _stderr_valid_utf8) =
                decode_walkthrough_stream(output.stderr, "stderr", &mut transcript_errors);
            if stdout_valid_utf8 {
                transcript_errors.extend(validate(&stdout));
            }
            if !stderr.is_empty() {
                transcript_errors.push("walkthrough stderr must be empty".to_string());
            }
            let transcript_passed = transcript_errors.is_empty();
            WalkthroughExecution {
                bin: bin.name.clone(),
                source: display_path(&bin.source),
                command,
                working_directory: display_path(manifest_directory),
                success: process_success && transcript_passed,
                process_success,
                transcript_passed,
                status: output.status.to_string(),
                status_code: output.status.code(),
                stdout,
                stderr,
                transcript_errors,
            }
        }
        Err(error) => WalkthroughExecution {
            bin: bin.name.clone(),
            source: display_path(&bin.source),
            command,
            working_directory: display_path(manifest_directory),
            success: false,
            process_success: false,
            transcript_passed: false,
            status: "spawn failed".to_string(),
            status_code: None,
            stdout: String::new(),
            stderr: format!("failed to run targo walkthrough command: {error}"),
            transcript_errors: vec!["walkthrough process did not start".to_string()],
        },
    }
}

fn targo_build_executable(stdout: &str, bin_name: &str) -> Option<PathBuf> {
    stdout.lines().find_map(|line| {
        let message = serde_json::from_str::<serde_json::Value>(line).ok()?;
        if message.get("reason").and_then(serde_json::Value::as_str) != Some("compiler-artifact") {
            return None;
        }
        if message
            .get("target")
            .and_then(|target| target.get("name"))
            .and_then(serde_json::Value::as_str)
            != Some(bin_name)
        {
            return None;
        }
        let target_kinds = message
            .get("target")
            .and_then(|target| target.get("kind"))
            .and_then(serde_json::Value::as_array)?;
        if !target_kinds.iter().any(|kind| kind.as_str() == Some("bin")) {
            return None;
        }
        message.get("executable").and_then(serde_json::Value::as_str).map(PathBuf::from)
    })
}

fn missing_walkthrough_execution(manifest_directory: &Path, name: &str) -> WalkthroughExecution {
    let source = manifest_directory.join("src/bin").join(format!("{name}.rs"));
    WalkthroughExecution {
        bin: name.to_string(),
        source: display_path(&source),
        command: String::new(),
        working_directory: display_path(manifest_directory),
        success: false,
        process_success: false,
        transcript_passed: false,
        status: "missing tracked walkthrough bin".to_string(),
        status_code: None,
        stdout: String::new(),
        stderr: String::new(),
        transcript_errors: vec![format!("required walkthrough bin `{name}` is missing")],
    }
}

fn unexpected_walkthrough_execution(
    manifest_directory: &Path,
    name: &str,
    source: &Path,
) -> WalkthroughExecution {
    WalkthroughExecution {
        bin: name.to_string(),
        source: display_path(source),
        command: String::new(),
        working_directory: display_path(manifest_directory),
        success: false,
        process_success: false,
        transcript_passed: false,
        status: "unexpected walkthrough bin".to_string(),
        status_code: None,
        stdout: String::new(),
        stderr: String::new(),
        transcript_errors: vec![format!(
            "unexpected walkthrough bin `{name}`; hardened-lab runs only the tracked corpus"
        )],
    }
}

fn decode_walkthrough_stream(
    bytes: Vec<u8>,
    stream: &str,
    errors: &mut Vec<String>,
) -> (String, bool) {
    match String::from_utf8(bytes) {
        Ok(text) => (text, true),
        Err(error) => {
            errors.push(format!("walkthrough {stream} must be valid UTF-8"));
            (String::from_utf8_lossy(&error.into_bytes()).into_owned(), false)
        }
    }
}

pub(super) fn manifest_dir(manifest_path: &Path) -> Result<&Path, String> {
    manifest_path.parent().ok_or_else(|| {
        format!(
            "targo trust hardened-lab: manifest path has no parent directory: {}",
            manifest_path.display()
        )
    })
}
