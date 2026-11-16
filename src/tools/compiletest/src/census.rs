//! Trust: passive, create-only harness observations. These records bind what
//! compiletest planned and attempted; they are not a complete language corpus,
//! a source-refinement certificate, or a new test/proof verdict.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::sync::{Arc, Mutex};

use camino::Utf8Path;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::common::{Config, TestMode, TestPaths};
use crate::directives::TestProps;
use crate::executor::{CollectedTest, ShouldFail, TestVariant};

#[cfg(test)]
mod tests;

const SCHEMA: &str = "trust.compiletest.invocation-census.v1";
const MAX_RECORD: usize = 8 * 1024 * 1024;
const MAX_OBSERVATION: u64 = 32 * 1024 * 1024;

#[derive(Debug)]
struct State {
    output: File,
    sequence: u64,
    previous: Option<String>,
    planned: BTreeSet<String>,
    selected: BTreeSet<String>,
    terminal: BTreeSet<String>,
    next_command: u64,
    pending_commands: BTreeSet<u64>,
    collection_exclusions: Vec<Value>,
}

#[derive(Debug)]
pub(crate) struct Census {
    directory: PathBuf,
    state: Mutex<State>,
}

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn os_value(value: &OsStr) -> Value {
    json!({"utf8": value.to_str(), "encoded_bytes_hex":
        value.as_encoded_bytes().iter().map(|byte| format!("{byte:02x}")).collect::<String>()})
}

fn file_record(path: &Path) -> Value {
    let result = (|| -> io::Result<Value> {
        let metadata = fs::metadata(path)?;
        if !metadata.is_file() {
            return Ok(json!({"path": path, "status": "not-regular-file"}));
        }
        let mut stream = File::open(path)?;
        let mut hash = Sha256::new();
        let mut buffer = [0; 64 * 1024];
        loop {
            let n = stream.read(&mut buffer)?;
            if n == 0 {
                break;
            }
            hash.update(&buffer[..n]);
        }
        Ok(json!({"path": path, "status": "read", "bytes": metadata.len(),
                  "sha256": format!("{:x}", hash.finalize())}))
    })();
    result.unwrap_or_else(
        |error| json!({"path": path, "status": "unreadable", "error": error.to_string()}),
    )
}

fn key(config: &Config, paths: &TestPaths, variant: &TestVariant) -> String {
    // Trust: incremental revisions execute inside one collected harness case.
    // Keep its aggregate identity; command events separately retain the revision.
    let revision = if config.mode == TestMode::Incremental { None } else { variant.revision() };
    digest(
        serde_json::to_string(&json!([
            paths.file.as_str(),
            revision,
            format!("{:?}", variant.debugger),
            config.mode.to_string(),
            config.target
        ]))
        .unwrap()
        .as_bytes(),
    )
}

impl Census {
    pub(crate) fn create(path: &Utf8Path) -> io::Result<Self> {
        if !path.is_absolute() {
            return Err(io::Error::other("Trust census requires an absolute NEW directory"));
        }
        fs::create_dir(path)?;
        let output =
            OpenOptions::new().write(true).create_new(true).open(path.join("events.jsonl"))?;
        Ok(Self {
            directory: path.as_std_path().to_owned(),
            state: Mutex::new(State {
                output,
                sequence: 0,
                previous: None,
                planned: BTreeSet::new(),
                selected: BTreeSet::new(),
                terminal: BTreeSet::new(),
                next_command: 0,
                pending_commands: BTreeSet::new(),
                collection_exclusions: Vec::new(),
            }),
        })
    }

    fn write(state: &mut State, mut event: Value) -> io::Result<()> {
        event["schema"] = json!(SCHEMA);
        event["sequence"] = json!(state.sequence);
        event["previous_record_sha256"] = json!(state.previous);
        let mut bytes = serde_json::to_vec(&event)?;
        if bytes.len() > MAX_RECORD {
            return Err(io::Error::other("Trust census record exceeded bound; no complete footer"));
        }
        bytes.push(b'\n');
        state.output.write_all(&bytes)?;
        state.output.flush()?;
        state.previous = Some(digest(&bytes));
        state.sequence = state
            .sequence
            .checked_add(1)
            .ok_or_else(|| io::Error::other("census sequence exhausted"))?;
        Ok(())
    }

    pub(crate) fn plan(&self, config: &Config, tests: &[CollectedTest]) -> io::Result<()> {
        let mut state = self.state.lock().unwrap();
        Self::write(
            &mut state,
            json!({"event": "begin", "scope": "harness-plans-and-command-observations",
            "argv": std::env::args_os().map(|a| os_value(&a)).collect::<Vec<_>>(),
            "source_root": config.src_root.as_str(), "suite_root": config.src_test_suite_root.as_str(),
            "mode": config.mode.to_string(), "suite": config.suite.to_string(),
            "host": config.host, "target": config.target, "stage": config.stage_id,
            "compiler": file_record(config.rustc_path.as_std_path()),
            "collection_only_modified": config.only_modified,
            "limitations": ["not an owner-admitted or complete language corpus",
                "no automatic compiler flag injection", "runtime/nested run-make commands are not all intercepted",
                "ambient environment, dynamic I/O and linked inputs remain unmeasured"]}),
        )?;
        for excluded in std::mem::take(&mut state.collection_exclusions) {
            Self::write(&mut state, excluded)?;
        }
        for test in tests {
            let case = key(config, &test.testpaths, &test.variant);
            if !state.planned.insert(case.clone()) {
                return Err(io::Error::other("duplicate planned case identity"));
            }
            let path = if config.mode == TestMode::RunMake {
                test.testpaths.file.join("rmake.rs")
            } else {
                test.testpaths.file.clone()
            };
            let source = fs::read_to_string(&path)?;
            // Trust: `should-fail` self-tests deliberately exercise directive
            // validation panics. Only their ordinary executor may interpret
            // those failures. Planning retains their complete source/directives,
            // revision and auxiliary population without executing that validation
            // before selection. Unavailable effective properties are null, never
            // empty flags or a claim that the self-test has valid properties.
            let expected_harness_failure = test.desc.should_fail == ShouldFail::Yes;
            let props = (!expected_harness_failure).then(|| {
                TestProps::from_file(&test.testpaths.file, test.variant.revision(), config)
            });
            let auxiliaries =
                props.as_ref().map(|props| &props.aux).unwrap_or(&test.auxiliary_inputs);
            let declared = auxiliaries
                .all_aux_path_strings()
                .map(|name| {
                    file_record(path.parent().unwrap().join("auxiliary").join(name).as_std_path())
                })
                .collect::<Vec<_>>();
            Self::write(
                &mut state,
                json!({"event": "planned", "case": case,
                "name": test.desc.name.as_str(), "source": file_record(path.as_std_path()),
                "revision": test.variant.revision(), "all_revisions": test.revisions,
                "debugger": format!("{:?}", test.variant.debugger),
                "ignore_reason": test.desc.ignore_message,
                "expected_harness_failure": expected_harness_failure,
                "properties_status": if expected_harness_failure {
                    "deferred-to-expected-failure-self-test-execution"
                } else { "loaded" },
                "expected_phase_outcome": props.as_ref().and_then(|p| p.pass_fail_mode)
                    .map(|mode| mode.to_string()),
                "expected_failure_status": props.as_ref().and_then(|p| p.failure_status),
                "compile_flags": props.as_ref().map(|p| &p.compile_flags),
                "run_flags": props.as_ref().map(|p| &p.run_flags),
                "edition": props.as_ref().and_then(|p| p.edition).map(|edition| edition.to_string()),
                "source_directives": source.lines().filter(|line| line.trim_start().starts_with("//@")
                    || line.contains("//~")).collect::<Vec<_>>(),
                "direct_auxiliary_inputs": declared,
                "dependency_scope": "declared-direct-auxiliaries; actual command inputs and compiler source maps are separate"}),
            )?;
        }
        let count = state.planned.len();
        Self::write(&mut state, json!({"event": "plan-complete", "planned": count}))
    }

    pub(crate) fn collection_excluded(&self, path: &Utf8Path, reason: &str) {
        self.state.lock().unwrap().collection_exclusions.push(json!({
            "event": "collection-excluded", "path": path.as_str(), "reason": reason,
            "input": file_record(path.as_std_path()),
            "expansion": "not expanded by the ordinary harness; no invented case count",
        }));
    }

    pub(crate) fn selected(&self, config: &Config, tests: &[CollectedTest]) -> io::Result<()> {
        let mut state = self.state.lock().unwrap();
        for test in tests {
            state.selected.insert(key(config, &test.testpaths, &test.variant));
        }
        let selected = state.selected.clone();
        Self::write(&mut state, json!({"event": "selection", "cases": selected}))
    }

    pub(crate) fn case_finished(
        &self,
        config: &Config,
        test: &CollectedTest,
        outcome: &str,
    ) -> io::Result<()> {
        let mut state = self.state.lock().unwrap();
        let case = key(config, &test.testpaths, &test.variant);
        state.terminal.insert(case.clone());
        Self::write(&mut state, json!({"event": "case-terminal", "case": case, "outcome": outcome}))
    }

    pub(crate) fn finish(&self, suite_passed: bool) -> io::Result<()> {
        let mut state = self.state.lock().unwrap();
        let pending_cases = state.selected.difference(&state.terminal).cloned().collect::<Vec<_>>();
        let pending_commands = state.pending_commands.clone();
        Self::write(
            &mut state,
            json!({"event": "end", "suite_passed": suite_passed,
            "pending_cases": pending_cases, "pending_commands": pending_commands,
            "authority": "diagnostic-only", "runtime_body_universe": "unmeasured"}),
        )
    }

    pub(crate) fn command_started(
        self: &Arc<Self>,
        config: &Config,
        paths: &TestPaths,
        variant: &TestVariant,
        command: &Command,
        input: Option<&str>,
    ) -> io::Result<Invocation> {
        let cwd = command.get_current_dir().map(Path::to_owned).unwrap_or(std::env::current_dir()?);
        let args = command.get_args().map(|a| a.to_owned()).collect::<Vec<_>>();
        let rustc = command.get_program() == config.rustc_path.as_os_str();
        let mut observations = BTreeMap::new();
        for (index, arg) in args.iter().enumerate() {
            let Some(arg) = arg.to_str() else { continue };
            let flag = if arg == "-Z" {
                args.get(index + 1).and_then(|a| a.to_str())
            } else {
                arg.strip_prefix("-Z")
            };
            for kind in ["trust-body-census", "trust-instance-census", "trust-lean-census"] {
                if let Some(path) = flag.and_then(|s| s.strip_prefix(&format!("{kind}="))) {
                    let path = cwd.join(path);
                    observations
                        .entry(kind.to_owned())
                        .or_insert_with(Vec::new)
                        .push((path.clone(), path.exists()));
                }
            }
        }
        let input_paths = args
            .iter()
            .filter_map(|a| a.to_str())
            .filter_map(|arg| {
                let candidate =
                    arg.rsplit_once('=').map_or(arg, |(_, value)| value).trim_start_matches('@');
                let path = cwd.join(candidate);
                path.is_file().then_some(path)
            })
            .collect::<Vec<_>>();
        let inputs = input_paths.iter().map(|path| file_record(path)).collect::<Vec<_>>();
        let mut state = self.state.lock().unwrap();
        let id = state.next_command;
        state.next_command =
            id.checked_add(1).ok_or_else(|| io::Error::other("command ID exhausted"))?;
        state.pending_commands.insert(id);
        let event = json!({"event": "command-attempt", "command": id,
            "case": key(config, paths, variant), "revision": variant.revision(),
            "kind": if rustc { "selected-rustc" } else { "other-command" },
            "program": os_value(command.get_program()), "program_file": file_record(Path::new(command.get_program())),
            "argv": args.iter().map(|a| os_value(a)).collect::<Vec<_>>(), "cwd": cwd,
            "stdin_sha256": input.map(|s| digest(s.as_bytes())), "argument_files": inputs,
            "environment_overrides": command.get_envs().map(|(k,v)| json!({"name": os_value(k),
                "value_sha256": v.map(|v| digest(v.as_encoded_bytes())), "unset": v.is_none()})).collect::<Vec<_>>(),
            "observation_requests": observations.iter().map(|(kind,paths)|json!({"kind":kind,
                "paths":paths.iter().map(|(path,existed)|json!({"path":path,"existed_before":existed})).collect::<Vec<_>>()
            })).collect::<Vec<_>>()});
        Self::write(&mut state, event)?;
        Ok(Invocation {
            census: self.clone(),
            id,
            observations,
            program: PathBuf::from(command.get_program()),
            input_paths,
        })
    }
}

pub(crate) struct Invocation {
    census: Arc<Census>,
    id: u64,
    observations: BTreeMap<String, Vec<(PathBuf, bool)>>,
    program: PathBuf,
    input_paths: Vec<PathBuf>,
}

impl Invocation {
    pub(crate) fn spawned(&self, pid: u32) -> io::Result<()> {
        Census::write(
            &mut self.census.state.lock().unwrap(),
            json!({"event":"command-spawned", "command":self.id,"pid":pid}),
        )
    }

    pub(crate) fn spawn_failed(&self, error: &io::Error) -> io::Result<()> {
        let mut state = self.census.state.lock().unwrap();
        state.pending_commands.remove(&self.id);
        Census::write(
            &mut state,
            json!({"event":"command-spawn-failed","command":self.id,"error":error.to_string()}),
        )
    }

    fn save(&self, name: &str, bytes: &[u8]) -> io::Result<Value> {
        let path = self.census.directory.join(format!("command-{}-{name}", self.id));
        let mut output = OpenOptions::new().write(true).create_new(true).open(&path)?;
        output.write_all(bytes)?;
        Ok(json!({"path":path,"bytes":bytes.len(),"sha256":digest(bytes)}))
    }

    pub(crate) fn finished(
        &self,
        status: &ExitStatus,
        stdout: &[u8],
        stderr: &[u8],
        truncated: bool,
    ) -> io::Result<()> {
        let mut observations = Vec::new();
        for (kind, paths) in &self.observations {
            for (index, (path, existed)) in paths.iter().enumerate() {
                let result = (|| -> io::Result<Value> {
                    if *existed || paths.len() != 1 {
                        return Ok(
                            json!({"kind":kind,"status":"preexisting-or-ambiguous","path":path}),
                        );
                    }
                    if fs::symlink_metadata(path)?.file_type().is_symlink() {
                        return Err(io::Error::other("observation is a symlink"));
                    }
                    let mut bytes = Vec::new();
                    File::open(path)?.take(MAX_OBSERVATION + 1).read_to_end(&mut bytes)?;
                    if bytes.len() as u64 > MAX_OBSERVATION {
                        return Err(io::Error::other("observation exceeds capture bound"));
                    }
                    Ok(
                        json!({"kind":kind,"status":"retained-unvalidated","artifact":self.save(&format!("{kind}-{index}.jsonl"),&bytes)?}),
                    )
                })();
                observations.push(result.unwrap_or_else(|error|json!({"kind":kind,"path":path,"status":"unavailable","error":error.to_string()})));
            }
        }
        let stdout = self.save("stdout", stdout)?;
        let stderr = self.save("stderr", stderr)?;
        let mut state = self.census.state.lock().unwrap();
        state.pending_commands.remove(&self.id);
        Census::write(
            &mut state,
            json!({"event":"command-terminal","command":self.id,
            "success":status.success(),"exit_code":status.code(),"stdout":stdout,"stderr":stderr,
            "output_truncated":truncated,"observations":observations,
            "program_after":file_record(&self.program),
            "argument_files_after":self.input_paths.iter().map(|path|file_record(path)).collect::<Vec<_>>()}),
        )
    }
}
