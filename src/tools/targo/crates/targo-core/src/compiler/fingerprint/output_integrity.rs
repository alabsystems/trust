//! Byte integrity for completed native compilation outputs.
//!
//! This supplements input fingerprints with the selected compiler-input snapshot
//! and, when configured, a domain-bound explicit linker-content observation.
//! It is not execution attestation or proof evidence, nor does it establish input
//! completeness, private-generation custody or authority to move/delete artifacts.
//! A damaged or missing receipt is a cache miss, never permission to bless the
//! bytes that happen to be present. Publish only after the compiler succeeds.

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use anyhow::{Context, bail};
use cargo_util::Sha256;
use serde::{Deserialize, Serialize};

use super::CompileMode;
use crate::CargoResult;
use crate::compiler::output_observation::{Emit, Seal};
use crate::util::interning::InternedString;

const SCHEMA: u32 = 4;
const MAX_RECEIPT_BYTES: u64 = 1024 * 1024;
const MAX_OUTPUTS: usize = 4096;
const MAX_OUTPUT_BYTES: u64 = 8 * 1024 * 1024 * 1024;

/// Trust: whether Cargo's expected files still describe this compiler command.
/// This is selected from current arguments, never restored from a saved record.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum OutputPolicy {
    #[default]
    Unselected,
    Standard,
    CallerEmit,
    CallerArgfile,
    CallerOutputFile,
    CallerOutputSelection,
}

impl OutputPolicy {
    pub(super) fn selected(
        profile_rustflags: &[InternedString],
        extra_args: &[String],
        rustflags: &[String],
    ) -> Self {
        // These are the caller vectors appended after Cargo's own --emit,
        // in execution order. This deliberately conservative token check also
        // refuses option-looking operand data; it is not a rustc argv parser.
        // rustc expands every original @ token before option parsing, even
        // operand data. Do not read or expand caller files here. Cargo's own
        // later retry-with-argfile transport is not part of these vectors.
        // Query/type/target/directory overrides also cannot inherit Cargo's
        // ordinary executable requirement or a receipt for its planned files.
        let classify = |arg: &str| {
            if arg.starts_with('@') {
                Some(Self::CallerArgfile)
            } else if arg == "--emit" || arg.starts_with("--emit=") {
                Some(Self::CallerEmit)
            } else if Self::has_output_filename_override(arg) {
                Some(Self::CallerOutputFile)
            } else if [
                "--out-dir",
                "--print",
                "--crate-type",
                "--target",
                "--explain",
            ]
            .iter()
            .any(|flag| {
                arg == *flag
                    || arg
                        .strip_prefix(*flag)
                        .is_some_and(|rest| rest.starts_with('='))
            }) || matches!(
                arg,
                "--help" | "-h" | "--version" | "-V" | "-Whelp" | "-W=help"
            ) || arg
                .strip_prefix("-Z")
                .is_some_and(Self::debugging_changes_output)
                || arg
                    .strip_prefix("-C")
                    .is_some_and(Self::codegen_changes_output)
            {
                Some(Self::CallerOutputSelection)
            } else {
                None
            }
        };
        let mut args = profile_rustflags
            .iter()
            .map(|arg| arg.as_str())
            .chain(extra_args.iter().chain(rustflags).map(String::as_str))
            .peekable();
        while let Some(arg) = args.next() {
            if (arg == "-Z"
                && args
                    .peek()
                    .is_some_and(|next| Self::debugging_changes_output(next)))
                || (arg == "-C"
                    && args
                        .peek()
                        .is_some_and(|next| Self::codegen_changes_output(next)))
                || (arg == "-W" && args.peek() == Some(&"help"))
            {
                return Self::CallerOutputSelection;
            }
            if let Some(policy) = classify(arg) {
                return policy;
            }
        }
        Self::Standard
    }

    fn debugging_changes_output(option: &str) -> bool {
        // These actual compiler options suppress/replace ordinary codegen.
        // Other -Z flags retain the executable requirement; this is no waiver.
        matches!(
            option.split('=').next(),
            Some("unpretty" | "no-analysis" | "no-codegen" | "no-link" | "parse-crate-root-only")
        )
    }

    fn codegen_changes_output(option: &str) -> bool {
        option.split('=').next() == Some("extra-filename")
    }

    fn has_output_filename_override(arg: &str) -> bool {
        // getopts accepts short clusters, including `-go path` and `-gopath`.
        // An argument-taking short option consumes the remainder of its token:
        // `-gClink-arg=-oelsewhere` therefore has no output-file switch. Stop at
        // rustc's value-taking short options, but conservatively scan unknown
        // prefixes rather than assuming a new flag cannot precede `o`.
        arg.strip_prefix('-')
            .filter(|short| !short.starts_with('-'))
            .is_some_and(|short| {
                short
                    .bytes()
                    .take_while(|byte| !b"ACDFLWZjl".contains(byte))
                    .any(|byte| byte == b'o')
            })
    }

    fn require_standard(self) -> CargoResult<()> {
        match self {
            Self::Standard => Ok(()),
            Self::CallerEmit => {
                bail!("caller-supplied --emit is not covered by Cargo's expected output inventory")
            }
            Self::CallerArgfile => {
                bail!(
                    "caller response-file arguments are opaque to Cargo's expected output inventory"
                )
            }
            Self::CallerOutputFile => {
                bail!("caller-supplied -o is not covered by Cargo's expected output inventory")
            }
            Self::CallerOutputSelection => {
                bail!(
                    "caller-supplied compiler query/output selection is not covered by Cargo's expected output inventory"
                )
            }
            Self::Unselected => bail!("compilation output policy is unavailable"),
        }
    }
}

/// Trust: planning-time compiler inputs, additionally bound to the configured
/// linker observation where selected. Not a witness that the compiler stayed
/// unchanged or that an executor dispatched that compiler; the narrow linker
/// execution-window observation likewise grants no execution attestation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CompilerObservation {
    rustc_key: u64,
    content_blake3: [u8; 32],
    workspace: bool,
    mode: OutputMode,
    build_script: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum OutputMode {
    Build,
    Check,
    CheckTest,
    Test,
}

impl CompilerObservation {
    pub(super) fn selected(
        rustc_key: u64,
        content_blake3: Option<[u8; 32]>,
        workspace: bool,
        mode: CompileMode,
        build_script: bool,
    ) -> Option<Self> {
        let mode = match mode {
            CompileMode::Build => OutputMode::Build,
            CompileMode::Check { test: false } => OutputMode::Check,
            CompileMode::Check { test: true } => OutputMode::CheckTest,
            CompileMode::Test => OutputMode::Test,
            CompileMode::Doc
            | CompileMode::Doctest
            | CompileMode::Docscrape
            | CompileMode::RunCustomBuild => return None,
        };
        Some(Self {
            rustc_key,
            content_blake3: content_blake3?,
            workspace,
            mode,
            build_script,
        })
    }
}

/// Current tool facts checked separately from the memoized short action key.
/// Defaults and unavailable readsets never mean that no tool facts are needed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum ToolInputExpectation {
    NotRequired,
    Observed([u8; 32]),
    #[default]
    Unavailable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
enum ToolInputReceipt {
    NotRequired,
    Observed { sha256: [u8; 32] },
}

impl ToolInputExpectation {
    fn recorded(self) -> CargoResult<ToolInputReceipt> {
        match self {
            Self::NotRequired => Ok(ToolInputReceipt::NotRequired),
            Self::Observed(sha256) => Ok(ToolInputReceipt::Observed { sha256 }),
            Self::Unavailable => bail!("compiler tool-input facts are unavailable"),
        }
    }
}

/// The original output seal paired with facts from that same completed Work.
/// One use, no serialization and no way to restore it from a saved receipt.
pub(super) struct Completion {
    seal: Seal,
    tool_inputs: ToolInputReceipt,
}

impl Completion {
    pub(super) fn new(seal: Seal, tools: ToolInputExpectation) -> CargoResult<Self> {
        Ok(Self {
            seal,
            tool_inputs: tools.recorded()?,
        })
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Receipt {
    schema: u32,
    fingerprint: u64,
    compiler: CompilerObservation,
    tool_inputs: ToolInputReceipt,
    compiler_outputs: Vec<CompilerOutput>,
    outputs: Vec<Output>,
}

/// Coverage of planned compiler-owned files, not an authenticated execution.
#[derive(Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct CompilerOutput {
    path_sha256: String,
    emit: Emit,
}

fn compiler_inventory(
    expected: &[(PathBuf, Emit)],
    outputs: &[PathBuf],
) -> CargoResult<Vec<CompilerOutput>> {
    if expected.is_empty() || expected.len() > MAX_OUTPUTS {
        bail!("invalid compiler output coverage count");
    }
    let mut expected: Vec<_> = expected.iter().collect();
    expected.sort_unstable_by(|a, b| a.0.cmp(&b.0));
    if expected.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        bail!("duplicate compiler output coverage");
    }
    expected
        .into_iter()
        .map(|(path, emit)| {
            if !path.is_absolute() || !outputs.contains(path) {
                bail!("compiler output coverage is outside the planned receipt inventory");
            }
            Ok(CompilerOutput {
                path_sha256: path_digest(path),
                emit: *emit,
            })
        })
        .collect()
}

#[derive(Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Output {
    path_sha256: String,
    size: u64,
    sha256: String,
}

fn path_digest(path: &Path) -> String {
    // Native paths need not be UTF-8. JSON must not add a path restriction.
    Sha256::new()
        .update(path.as_os_str().as_encoded_bytes())
        .finish_hex()
}

fn open_regular(path: &Path) -> CargoResult<File> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK);
    }
    if !fs::symlink_metadata(path)?.is_file() {
        bail!("output is not a regular file: {}", path.display());
    }
    let file = options.open(path)?;
    if !file.metadata()?.is_file() {
        bail!("opened output is not a regular file: {}", path.display());
    }
    Ok(file)
}

fn capture(path: &Path) -> CargoResult<Output> {
    let mut file = open_regular(path)?;
    let before = file.metadata()?;
    let size = before.len();
    if size > MAX_OUTPUT_BYTES {
        bail!("compilation output exceeds size limit: {}", path.display());
    }
    let mut hash = Sha256::new();
    let mut count = 0_u64;
    let mut bytes = [0; 64 * 1024];
    loop {
        let read = file.read(&mut bytes)?;
        if read == 0 {
            break;
        }
        count += read as u64;
        if count > size {
            bail!("compilation output grew while hashing: {}", path.display());
        }
        hash.update(&bytes[..read]);
    }
    let sha256 = hash.finish_hex();
    let after = file.metadata()?;
    if count != size || size != after.len() || before.modified()? != after.modified()? {
        bail!(
            "compilation output changed while hashing: {}",
            path.display()
        );
    }
    Ok(Output {
        path_sha256: path_digest(path),
        size,
        sha256,
    })
}

fn sorted_outputs(outputs: &[PathBuf]) -> CargoResult<Vec<&Path>> {
    if outputs.is_empty() || outputs.len() > MAX_OUTPUTS {
        bail!("invalid compilation output count");
    }
    let mut paths: Vec<_> = outputs.iter().map(PathBuf::as_path).collect();
    paths.sort_unstable();
    if paths.windows(2).any(|pair| pair[0] == pair[1]) {
        bail!("duplicate compilation output");
    }
    Ok(paths)
}

pub(super) fn publish(
    path: &Path,
    fingerprint: u64,
    outputs: &[PathBuf],
    compiler: Option<&CompilerObservation>,
    policy: OutputPolicy,
    expected: &[(PathBuf, Emit)],
    completion: Option<Completion>,
) -> CargoResult<()> {
    policy.require_standard()?;
    let Completion { seal, tool_inputs } =
        completion.context("live compiler output completion is unavailable")?;
    let observed = seal.outputs();
    let compiler_outputs = compiler_inventory(expected, outputs)?;
    if compiler_outputs != compiler_inventory(&observed, outputs)? {
        bail!("live compiler output coverage differs from the planned inventory");
    }
    let compiler = compiler
        .copied()
        .context("selected compiler content identity is unavailable")?;
    let outputs = sorted_outputs(outputs)?
        .into_iter()
        .map(capture)
        .collect::<CargoResult<_>>()?;
    let bytes = serde_json::to_vec(&Receipt {
        schema: SCHEMA,
        fingerprint,
        compiler,
        tool_inputs,
        compiler_outputs,
        outputs,
    })?;
    if bytes.len() as u64 > MAX_RECEIPT_BYTES {
        bail!("compilation output receipt exceeds size limit");
    }
    let parent = path.parent().context("output receipt has no parent")?;
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(&bytes)?;
    temporary.as_file().sync_all()?;
    // Rename replaces a destination symlink rather than following it. Never
    // use paths::write_atomic here, which deliberately follows symlinks.
    temporary.persist(path).map_err(|error| error.error)?;
    Ok(())
}

pub(super) fn verify(
    path: &Path,
    fingerprint: u64,
    outputs: &[PathBuf],
    compiler: Option<&CompilerObservation>,
    policy: OutputPolicy,
    compiler_outputs: &[(PathBuf, Emit)],
    tools: ToolInputExpectation,
) -> CargoResult<()> {
    policy.require_standard()?;
    let compiler = compiler.context("selected compiler content identity is unavailable")?;
    let tool_inputs = tools.recorded()?;
    let receipt = read_receipt(path)?;
    let expected = sorted_outputs(outputs)?;
    if receipt.schema != SCHEMA
        || receipt.fingerprint != fingerprint
        || receipt.compiler != *compiler
        || receipt.tool_inputs != tool_inputs
        || receipt.compiler_outputs != compiler_inventory(compiler_outputs, outputs)?
        || receipt.outputs.len() != expected.len()
    {
        bail!("compilation output receipt does not match this action");
    }
    for (record, path) in receipt.outputs.iter().zip(expected) {
        // Check the declared inventory before opening anything named by the
        // receipt. A cache file cannot make the reader inspect arbitrary paths.
        if record.path_sha256 != path_digest(path) {
            bail!("compilation output receipt has a different inventory");
        }
    }
    for (record, path) in receipt.outputs.iter().zip(sorted_outputs(outputs)?) {
        if fs::symlink_metadata(path)?.len() != record.size {
            bail!("compilation output size changed: {}", path.display());
        }
        if *record != capture(path)? {
            bail!("compilation output bytes changed: {}", path.display());
        }
    }
    Ok(())
}

/// Repeat the current full tool identity immediately before Fresh even when
/// the graph's filesystem state was memoized. Output bytes/inventory still
/// pass the separate ordinary check_filesystem receipt gate.
pub(super) fn verify_tool_inputs(
    path: &Path,
    fingerprint: u64,
    tools: ToolInputExpectation,
) -> CargoResult<()> {
    let tools = tools.recorded()?;
    let receipt = read_receipt(path)?;
    if receipt.schema != SCHEMA
        || receipt.fingerprint != fingerprint
        || receipt.tool_inputs != tools
    {
        bail!("compilation tool-input receipt does not match this action");
    }
    Ok(())
}

fn read_receipt(path: &Path) -> CargoResult<Receipt> {
    let file = open_regular(path)?;
    if file.metadata()?.len() > MAX_RECEIPT_BYTES {
        bail!("compilation output receipt exceeds size limit");
    }
    let mut bytes = Vec::new();
    file.take(MAX_RECEIPT_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_RECEIPT_BYTES {
        bail!("compilation output receipt grew beyond size limit");
    }
    Ok(serde_json::from_slice(&bytes)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compiler_outputs(outputs: &[PathBuf]) -> Vec<(PathBuf, Emit)> {
        outputs
            .iter()
            .cloned()
            .map(|path| (path, Emit::Link))
            .collect()
    }

    fn seal(outputs: &[PathBuf]) -> Option<Seal> {
        let mut observer = crate::compiler::output_observation::Observer::new(
            compiler_outputs(outputs),
            std::env::current_dir().unwrap(),
        );
        for path in outputs {
            observer.observe(
                &serde_json::json!({
                    "$message_type": "artifact", "artifact": path, "emit": "link",
                })
                .to_string(),
            );
        }
        observer.finish()
    }

    fn publish(
        path: &Path,
        fingerprint: u64,
        outputs: &[PathBuf],
        compiler: Option<&CompilerObservation>,
    ) -> CargoResult<()> {
        super::publish(
            path,
            fingerprint,
            outputs,
            compiler,
            OutputPolicy::Standard,
            &compiler_outputs(outputs),
            completion(outputs, ToolInputExpectation::NotRequired),
        )
    }

    fn verify(
        path: &Path,
        fingerprint: u64,
        outputs: &[PathBuf],
        compiler: Option<&CompilerObservation>,
    ) -> CargoResult<()> {
        super::verify(
            path,
            fingerprint,
            outputs,
            compiler,
            OutputPolicy::Standard,
            &compiler_outputs(outputs),
            ToolInputExpectation::NotRequired,
        )
    }

    fn completion(outputs: &[PathBuf], tools: ToolInputExpectation) -> Option<Completion> {
        seal(outputs).and_then(|seal| Completion::new(seal, tools).ok())
    }

    const COMPILER: Option<&CompilerObservation> = Some(&CompilerObservation {
        rustc_key: 91,
        content_blake3: [7; 32],
        workspace: true,
        mode: OutputMode::Build,
        build_script: false,
    });

    #[test]
    fn full_tool_binding_is_required_even_when_short_key_and_outputs_match() {
        let root = tempfile::tempdir().unwrap();
        let artifact = root.path().join("program");
        let receipt = root.path().join("receipt.json");
        fs::write(&artifact, b"same compiled bytes").unwrap();
        let outputs = vec![artifact];
        let tools = ToolInputExpectation::Observed([7; 32]);
        super::publish(
            &receipt,
            17,
            &outputs,
            COMPILER,
            OutputPolicy::Standard,
            &compiler_outputs(&outputs),
            completion(&outputs, tools),
        )
        .unwrap();
        let check = |tools| {
            super::verify(
                &receipt,
                17,
                &outputs,
                COMPILER,
                OutputPolicy::Standard,
                &compiler_outputs(&outputs),
                tools,
            )
        };
        check(tools).unwrap();
        let mut changed = [7; 32];
        changed[31] ^= 1;
        for tools in [
            ToolInputExpectation::Observed(changed),
            ToolInputExpectation::Unavailable,
            ToolInputExpectation::NotRequired,
        ] {
            assert!(check(tools).is_err());
        }

        let original = fs::read(&receipt).unwrap();
        let mut malformed: serde_json::Value = serde_json::from_slice(&original).unwrap();
        malformed.as_object_mut().unwrap().remove("tool_inputs");
        fs::write(&receipt, serde_json::to_vec(&malformed).unwrap()).unwrap();
        assert!(check(ToolInputExpectation::NotRequired).is_err());
        assert!(check(tools).is_err());
        fs::write(&receipt, original).unwrap();
        check(tools).unwrap();
    }

    #[test]
    fn unavailable_tool_facts_cannot_pair_with_a_new_output_seal_or_replace_a_receipt() {
        let root = tempfile::tempdir().unwrap();
        let artifact = root.path().join("program");
        let receipt = root.path().join("receipt.json");
        fs::write(&artifact, b"compiled bytes").unwrap();
        let outputs = vec![artifact];
        publish(&receipt, 17, &outputs, COMPILER).unwrap();
        let original = fs::read(&receipt).unwrap();
        assert!(
            Completion::new(seal(&outputs).unwrap(), ToolInputExpectation::Unavailable).is_err()
        );
        assert!(
            super::publish(
                &receipt,
                17,
                &outputs,
                COMPILER,
                OutputPolicy::Standard,
                &compiler_outputs(&outputs),
                None,
            )
            .is_err()
        );
        assert_eq!(fs::read(&receipt).unwrap(), original);
        verify(&receipt, 17, &outputs, COMPILER).unwrap();
    }

    #[test]
    fn coverage_is_mandatory_for_publication_and_old_receipts_cannot_supply_it() {
        let root = tempfile::tempdir().unwrap();
        let artifact = root.path().join("lib.rlib");
        let receipt = root.path().join("outputs.json");
        fs::write(&artifact, b"old bytes").unwrap();
        let paths = vec![artifact];
        let expected = compiler_outputs(&paths);
        assert!(
            super::publish(
                &receipt,
                17,
                &paths,
                COMPILER,
                OutputPolicy::Standard,
                &expected,
                None
            )
            .is_err()
        );
        assert!(!receipt.exists());
        publish(&receipt, 17, &paths, COMPILER).unwrap();
        let original: serde_json::Value =
            serde_json::from_slice(&fs::read(&receipt).unwrap()).unwrap();
        for schema in [1, 2, 3] {
            let mut legacy = original.clone();
            legacy["schema"] = schema.into();
            fs::write(&receipt, serde_json::to_vec(&legacy).unwrap()).unwrap();
            assert!(verify(&receipt, 17, &paths, COMPILER).is_err());
        }
        let mut missing = original;
        missing.as_object_mut().unwrap().remove("compiler_outputs");
        fs::write(&receipt, serde_json::to_vec(&missing).unwrap()).unwrap();
        assert!(verify(&receipt, 17, &paths, COMPILER).is_err());
        assert!(
            super::publish(
                &receipt,
                17,
                &paths,
                COMPILER,
                OutputPolicy::Standard,
                &[(paths[0].clone(), Emit::Metadata)],
                completion(&paths, ToolInputExpectation::NotRequired)
            )
            .is_err()
        );
    }

    #[test]
    fn current_caller_emit_tokens_conservatively_refuse_the_default_inventory() {
        let flags = |values: &[&str]| {
            values
                .iter()
                .map(|value| value.to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            OutputPolicy::selected(&[], &[], &[]),
            OutputPolicy::Standard
        );
        for values in [
            flags(&["--emit=metadata=elsewhere"]),
            flags(&["--emit", "metadata=elsewhere"]),
            flags(&["--emit=metadata", "--emit=link"]),
            // This is operand data, so the conservative check can cause an
            // extra miss. It must never incorrectly authorize output reuse.
            flags(&["--remap-path-prefix", "--emit=from=to"]),
        ] {
            let profile: Vec<_> = values.iter().map(InternedString::from).collect();
            assert_eq!(
                OutputPolicy::selected(&profile, &[], &[]),
                OutputPolicy::CallerEmit
            );
            assert_eq!(
                OutputPolicy::selected(&[], &values, &[]),
                OutputPolicy::CallerEmit
            );
            assert_eq!(
                OutputPolicy::selected(&[], &[], &values),
                OutputPolicy::CallerEmit
            );
        }
        let unrelated = flags(&["--emitter", "-Clink-arg=--emit=elsewhere", "--cfg=emit"]);
        let profile: Vec<_> = unrelated.iter().map(InternedString::from).collect();
        assert_eq!(
            OutputPolicy::selected(&profile, &[], &[]),
            OutputPolicy::Standard
        );
        assert_eq!(
            OutputPolicy::selected(&[], &unrelated, &[]),
            OutputPolicy::Standard
        );
        assert_eq!(
            OutputPolicy::selected(&[], &[], &unrelated),
            OutputPolicy::Standard
        );
        assert!(OutputPolicy::default().require_standard().is_err());
    }

    #[test]
    fn caller_output_filename_overrides_refuse_each_caller_source() {
        let flags = |values: &[&str]| values.iter().map(|arg| arg.to_string()).collect::<Vec<_>>();
        for values in [
            flags(&["-o", "elsewhere"]),
            flags(&["-oelsewhere"]),
            flags(&["-go", "elsewhere"]),
            flags(&["-goelsewhere"]),
            flags(&["-gOoelsewhere"]),
        ] {
            let profile: Vec<_> = values.iter().map(InternedString::from).collect();
            assert_eq!(
                OutputPolicy::selected(&profile, &[], &[]),
                OutputPolicy::CallerOutputFile
            );
            assert_eq!(
                OutputPolicy::selected(&[], &values, &[]),
                OutputPolicy::CallerOutputFile
            );
            assert_eq!(
                OutputPolicy::selected(&[], &[], &values),
                OutputPolicy::CallerOutputFile
            );
        }
        // Embedded data belongs to another compiler option, rather than the
        // compiler's output-file switch. Ordinary output reuse stays available.
        let embedded = flags(&[
            "-Clink-arg=-oelsewhere",
            "-gClink-arg=-oelsewhere",
            "-gLsome-output",
            "-gWsome_lint",
            "--cfg=output",
        ]);
        let profile: Vec<_> = embedded.iter().map(InternedString::from).collect();
        assert_eq!(
            OutputPolicy::selected(&profile, &embedded, &embedded),
            OutputPolicy::Standard
        );
        // This is a real directory override rather than embedded -o data.
        // Its output inventory is caller-selected even when named "standard".
        let selected = flags(&["--out-dir=standard"]);
        let profile: Vec<_> = selected.iter().map(InternedString::from).collect();
        for policy in [
            OutputPolicy::selected(&profile, &[], &[]),
            OutputPolicy::selected(&[], &selected, &[]),
            OutputPolicy::selected(&[], &[], &selected),
        ] {
            assert_eq!(policy, OutputPolicy::CallerOutputSelection);
        }
    }

    #[test]
    fn original_response_file_tokens_refuse_each_caller_source_without_expansion() {
        let flags = |values: &[&str]| values.iter().map(|arg| arg.to_string()).collect::<Vec<_>>();
        for values in [
            flags(&["@missing-response-file"]),
            flags(&["@shell:missing-response-file"]),
            flags(&["@"]),
            // The compiler expands these tokens before parsing operands or
            // the option terminator, so they are opaque in these positions.
            flags(&["--cfg", "@missing-response-file"]),
            flags(&["--", "@missing-response-file"]),
        ] {
            let profile: Vec<_> = values.iter().map(InternedString::from).collect();
            assert_eq!(
                OutputPolicy::selected(&profile, &[], &[]),
                OutputPolicy::CallerArgfile
            );
            assert_eq!(
                OutputPolicy::selected(&[], &values, &[]),
                OutputPolicy::CallerArgfile
            );
            assert_eq!(
                OutputPolicy::selected(&[], &[], &values),
                OutputPolicy::CallerArgfile
            );
        }
        let embedded = flags(&["-Clink-arg=@linker-owned", "--cfg=contains_at"]);
        let profile: Vec<_> = embedded.iter().map(InternedString::from).collect();
        assert_eq!(
            OutputPolicy::selected(&profile, &embedded, &embedded),
            OutputPolicy::Standard
        );
        let emit = flags(&["--emit=metadata"]);
        let response = flags(&["@missing"]);
        let profile: Vec<_> = response.iter().map(InternedString::from).collect();
        assert_eq!(
            OutputPolicy::selected(&profile, &emit, &[]),
            OutputPolicy::CallerArgfile
        );
        assert_eq!(
            OutputPolicy::selected(&[], &emit, &response),
            OutputPolicy::CallerEmit
        );
    }

    #[test]
    fn caller_emit_cannot_publish_or_replay_unchanged_old_default_bytes() {
        let temp = tempfile::tempdir().unwrap();
        let artifact = temp.path().join("lib.rmeta");
        let receipt = temp.path().join("receipt.json");
        fs::write(&artifact, b"surviving old default metadata").unwrap();
        let paths = vec![artifact.clone()];
        publish(&receipt, 17, &paths, COMPILER).unwrap();
        verify(&receipt, 17, &paths, COMPILER).unwrap();
        let original = fs::read(&receipt).unwrap();
        for policy in [
            OutputPolicy::CallerEmit,
            OutputPolicy::CallerArgfile,
            OutputPolicy::CallerOutputFile,
            OutputPolicy::Unselected,
        ] {
            assert!(
                super::verify(
                    &receipt,
                    17,
                    &paths,
                    COMPILER,
                    policy,
                    &compiler_outputs(&paths),
                    ToolInputExpectation::NotRequired
                )
                .is_err()
            );
            assert!(
                super::publish(
                    &receipt,
                    18,
                    &paths,
                    COMPILER,
                    policy,
                    &compiler_outputs(&paths),
                    completion(&paths, ToolInputExpectation::NotRequired)
                )
                .is_err()
            );
            assert_eq!(fs::read(&receipt).unwrap(), original);
            assert_eq!(
                fs::read(&artifact).unwrap(),
                b"surviving old default metadata"
            );
        }
        // Fresh selection is supplied independently of the receipt's matching
        // action key/compiler/bytes. Its serialized shape remains unchanged.
        assert!(
            serde_json::from_slice::<serde_json::Value>(&original)
                .unwrap()
                .get("policy")
                .is_none()
        );
        verify(&receipt, 17, &paths, COMPILER).unwrap();
    }

    #[test]
    fn selected_compiler_snapshot_is_required_beyond_bytes_and_the_short_action_key() {
        let temp = tempfile::tempdir().unwrap();
        let artifact = temp.path().join("lib.rmeta");
        let receipt = temp.path().join("receipt.json");
        fs::write(&artifact, b"same output bytes").unwrap();
        let paths = vec![artifact];
        let original = *COMPILER.unwrap();
        publish(&receipt, 17, &paths, Some(&original)).unwrap();
        verify(&receipt, 17, &paths, Some(&original)).unwrap();
        for changed in [
            CompilerObservation {
                rustc_key: 92,
                ..original
            },
            CompilerObservation {
                content_blake3: [8; 32],
                ..original
            },
            CompilerObservation {
                workspace: false,
                ..original
            },
            CompilerObservation {
                mode: OutputMode::Check,
                ..original
            },
            CompilerObservation {
                build_script: true,
                ..original
            },
        ] {
            assert!(
                verify(&receipt, 17, &paths, Some(&changed)).is_err(),
                "{changed:?}"
            );
        }
        assert!(verify(&receipt, 17, &paths, None).is_err());
        let intact = fs::read(&receipt).unwrap();
        assert!(publish(&receipt, 17, &paths, None).is_err());
        assert_eq!(
            fs::read(&receipt).unwrap(),
            intact,
            "failed publication cannot replace an existing receipt"
        );
        let mut legacy: serde_json::Value = serde_json::from_slice(&intact).unwrap();
        legacy.as_object_mut().unwrap().remove("compiler");
        fs::write(&receipt, serde_json::to_vec(&legacy).unwrap()).unwrap();
        assert!(
            verify(&receipt, 17, &paths, COMPILER).is_err(),
            "missing observations cannot be backfilled from current inputs"
        );
        legacy["schema"] = 1.into();
        fs::write(&receipt, serde_json::to_vec(&legacy).unwrap()).unwrap();
        assert!(verify(&receipt, 17, &paths, COMPILER).is_err());
    }

    #[test]
    fn supported_compilation_modes_round_trip_but_other_producers_stay_unclassified() {
        let temp = tempfile::tempdir().unwrap();
        let artifact = temp.path().join("lib.rmeta");
        let receipt = temp.path().join("receipt.json");
        fs::write(&artifact, b"output").unwrap();
        let paths = vec![artifact];
        for mode in [
            CompileMode::Build,
            CompileMode::Check { test: false },
            CompileMode::Check { test: true },
            CompileMode::Test,
        ] {
            let observation =
                CompilerObservation::selected(91, Some([7; 32]), true, mode, true).unwrap();
            publish(&receipt, 17, &paths, Some(&observation)).unwrap();
            verify(&receipt, 17, &paths, Some(&observation)).unwrap();
        }
        assert_ne!(
            CompilerObservation::selected(
                91,
                Some([7; 32]),
                true,
                CompileMode::Check { test: false },
                false
            ),
            CompilerObservation::selected(
                91,
                Some([7; 32]),
                true,
                CompileMode::Check { test: true },
                false
            )
        );
        for mode in [
            CompileMode::Doc,
            CompileMode::Doctest,
            CompileMode::Docscrape,
            CompileMode::RunCustomBuild,
        ] {
            assert!(CompilerObservation::selected(91, Some([7; 32]), true, mode, false).is_none());
        }
        assert!(CompilerObservation::selected(91, None, true, CompileMode::Build, false).is_none());
    }

    #[cfg(unix)]
    #[test]
    fn path_identity_does_not_require_utf8() {
        use std::os::unix::ffi::OsStringExt;
        // APFS refuses creating non-UTF-8 filenames, but OsString can still
        // represent one. Test our format independently of that OS restriction.
        let path = PathBuf::from(std::ffi::OsString::from_vec(b"lib-\xff.rlib".to_vec()));
        let digest = path_digest(&path);
        assert_eq!(digest.len(), 64);
        assert_ne!(digest, path_digest(Path::new("lib-replacement.rlib")));
        let record = Output {
            path_sha256: digest,
            size: 0,
            sha256: "0".repeat(64),
        };
        serde_json::to_vec(&record).unwrap();
    }

    #[test]
    fn bytes_and_inventory_are_required_even_with_equal_size_and_mtime() {
        let temp = tempfile::tempdir().unwrap();
        let artifact = temp.path().join("lib-é.rlib");
        let receipt = temp.path().join("receipt.json");
        fs::write(&artifact, b"original").unwrap();
        let paths = vec![artifact.clone()];
        publish(&receipt, 17, &paths, COMPILER).unwrap();
        verify(&receipt, 17, &paths, COMPILER).unwrap();
        assert!(verify(&receipt, 18, &paths, COMPILER).is_err());
        let mtime =
            filetime::FileTime::from_last_modification_time(&fs::metadata(&artifact).unwrap());
        fs::write(&artifact, b"corrupt!").unwrap();
        filetime::set_file_mtime(&artifact, mtime).unwrap();
        assert!(verify(&receipt, 17, &paths, COMPILER).is_err());
        fs::write(&artifact, b"original").unwrap();
        verify(&receipt, 17, &paths, COMPILER).unwrap();
        fs::remove_file(&artifact).unwrap();
        assert!(verify(&receipt, 17, &paths, COMPILER).is_err());
    }

    #[test]
    fn malformed_missing_and_oversized_receipts_are_misses() {
        let temp = tempfile::tempdir().unwrap();
        let artifact = temp.path().join("lib.rmeta");
        let receipt = temp.path().join("receipt.json");
        fs::write(&artifact, b"metadata").unwrap();
        let paths = vec![artifact];
        assert!(verify(&receipt, 1, &paths, COMPILER).is_err());
        fs::write(&receipt, b"{").unwrap();
        assert!(verify(&receipt, 1, &paths, COMPILER).is_err());
        File::create(&receipt)
            .unwrap()
            .set_len(MAX_RECEIPT_BYTES + 1)
            .unwrap();
        assert!(verify(&receipt, 1, &paths, COMPILER).is_err());
        publish(&receipt, 1, &paths, COMPILER).unwrap();
        assert!(verify(&receipt, 1, &[], COMPILER).is_err());
        assert!(verify(&receipt, 1, &[temp.path().join("elsewhere")], COMPILER).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn symlink_receipts_and_outputs_are_not_followed() {
        use std::os::unix::fs::symlink;
        let temp = tempfile::tempdir().unwrap();
        let artifact = temp.path().join("lib.rmeta");
        let receipt = temp.path().join("receipt.json");
        let victim = temp.path().join("victim");
        fs::write(&artifact, b"metadata").unwrap();
        fs::write(&victim, b"preserved").unwrap();
        symlink(&victim, &receipt).unwrap();
        let paths = vec![artifact.clone()];
        assert!(verify(&receipt, 1, &paths, COMPILER).is_err());
        publish(&receipt, 1, &paths, COMPILER).unwrap();
        assert_eq!(fs::read(&victim).unwrap(), b"preserved");
        verify(&receipt, 1, &paths, COMPILER).unwrap();
        fs::remove_file(&artifact).unwrap();
        symlink(&victim, &artifact).unwrap();
        assert!(verify(&receipt, 1, &paths, COMPILER).is_err());
        assert!(publish(&receipt, 1, &paths, COMPILER).is_err());
    }
}
