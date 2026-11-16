//! The retained paired owner supplies exact compiler/Targo identities. This
//! adapter captures a distinct native root and explicitly extracts metadata
//! from its report; the entry's raw stdout is never labeled metadata JSON.
use std::path::PathBuf;

use serde_json::{Value, json};
use trust_qualification::dependencies::{
    DependencyResolver, ResolverCapture, ResolverOutcome, ResolverRequest,
};
use trust_qualification::{Refusal, Result, pair};
use trust_resource_controller::resolver::{
    RESOLVER_REPORT_MAX_BYTES, RESOLVER_STARTUP_ARGUMENT, ResolverInvocation, ResolverReport,
};

use crate::native_root_transport::{self as transport, RootSpec, hex, validate_statuses};
pub(crate) struct NativeDependencyResolver {
    host_store: Option<PathBuf>,
    observation: Option<Value>,
}
impl NativeDependencyResolver {
    pub(crate) fn new(host_store: Option<PathBuf>) -> Self {
        Self { host_store, observation: None }
    }
}
fn digest(value: &str) -> Result<[u8; 32]> {
    if value.len() != 64 {
        return Err(Refusal("resolver input digest is not SHA256".into()));
    }
    let mut out = [0; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        let text = std::str::from_utf8(pair).map_err(|e| Refusal(e.to_string()))?;
        out[index] = u8::from_str_radix(text, 16).map_err(|e| Refusal(e.to_string()))?;
    }
    Ok(out)
}
fn invocation(request: &ResolverRequest, store: &Option<PathBuf>) -> Result<ResolverInvocation> {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        return Err(Refusal("native full resolver requires macOS arm64 custody".into()));
    }
    if request.program.path != request.sdk_root.join("bin/targo")
        || request.compiler.path != request.sdk_root.join("bin/trustc")
        || pair::file_identity(&request.program.path)? != request.program
        || pair::file_identity(&request.compiler.path)? != request.compiler
    {
        return Err(Refusal(
            "original paired Targo/compiler changed or selected a different SDK".into(),
        ));
    }
    let value = ResolverInvocation {
        host_store: store.as_ref().map(|p| p.as_os_str().as_encoded_bytes().to_vec()),
        root: request.sdk_root.as_os_str().as_encoded_bytes().to_vec(),
        program: request.program.path.as_os_str().as_encoded_bytes().to_vec(),
        program_sha256: digest(&request.program.sha256)?,
        compiler: request.compiler.path.as_os_str().as_encoded_bytes().to_vec(),
        compiler_sha256: digest(&request.compiler.sha256)?,
        cwd: request.cwd.as_os_str().as_encoded_bytes().to_vec(),
        cargo_home: request.cargo_home.as_os_str().as_encoded_bytes().to_vec(),
    };
    value.validate()?;
    Ok(value)
}
impl DependencyResolver for NativeDependencyResolver {
    fn execution_observation(&self) -> Option<Value> {
        self.observation.clone()
    }
    fn resolve(&mut self, request: &ResolverRequest) -> Result<ResolverCapture> {
        self.observation = Some(
            json!({"scope":"attempted separately negotiated resolver; no source/build authentication or proof",
            "request":request,"semantic_resolver_argv":request.arguments(),"actual_entry_argv":[RESOLVER_STARTUP_ARGUMENT]}),
        );
        let invocation = invocation(request, &self.host_store)?;
        let input = invocation.encode()?;
        let environment = [
            ("CARGO_HOME", request.cargo_home.as_os_str()),
            ("CARGO", request.program.path.as_os_str()),
            ("RUSTC", request.compiler.path.as_os_str()),
            ("CARGO_CACHE_RUSTC_INFO", std::ffi::OsStr::new("0")),
        ];
        let capture = transport::capture(
            RootSpec {
                program: &request.program.path,
                cwd: &request.cwd,
                entry: RESOLVER_STARTUP_ARGUMENT,
                environment: &environment,
                input: &input,
                max_output: RESOLVER_REPORT_MAX_BYTES,
                max_stderr: trust_qualification::dependencies::MAX_STDERR_BYTES,
                job: "trust-native-paired-resolver",
            },
            &self.host_store,
        )?;
        let mut execution = capture.observation;
        execution["semantic_resolver_argv"] = json!(request.arguments());
        execution["schema"] = json!("trust.native-resolver-attempt/v1");
        let mut result = ResolverCapture {
            stdout: Vec::new(),
            stderr: Vec::new(),
            outcome: ResolverOutcome::Unknown,
            cleanup_confirmed: false,
            output_limit_exceeded: false,
            failure: None,
            execution: None,
        };
        match capture.output {
            Err(error) => {
                result.failure = Some(format!(
                    "native resolver capture failed; actual available prefixes retained: {error}"
                ));
            }
            Ok(output) => {
                result.stderr = output.stderr.clone();
                let checked = (|| -> Result<()> {
                    if !capture.image_valid {
                        return Err(Refusal(
                            "resolver custodian image changed; bytes remain unauthenticated".into(),
                        ));
                    }
                    let terminal =
                        validate_statuses(&capture.statuses.map_err(Refusal)?, &output.status)?;
                    result.cleanup_confirmed = true;
                    result.outcome = terminal.outcome;
                    // Decode the root envelope as data and extract only its
                    // actual normal metadata component. Raw envelope remains above.
                    let report = ResolverReport::decode(&output.stdout, &invocation)?;
                    result.stdout = report.metadata.clone().unwrap_or_default();
                    let runner = report.runner.as_ref().ok_or_else(|| {
                        Refusal("resolver report lacks original runner observation".into())
                    })?;
                    let context = trust_resource_controller::ContextReply::decode_observation(
                        &runner.context_frame,
                    )?
                    .context;
                    if runner.identity.pid != terminal.pid
                        || runner.identity.birth != terminal.birth
                        || context.session != terminal.session
                        || hex(&context.root_attempt) != terminal.attempt
                    {
                        return Err(Refusal("actual native root lifecycle differs from resolver report process/context".into()));
                    }
                    execution["semantic_metadata_extracted"] = json!(true);
                    execution["query_count"] = json!(report.queries.len());
                    execution["queries"]=json!(report.queries.iter().map(|query|json!({
                        "member_attempt":hex(&query.member_attempt),
                        "actual_program_hex":hex(&query.command.program),
                        "actual_argv_hex":query.command.args.iter().map(|arg|hex(arg)).collect::<Vec<_>>(),
                        "actual_cwd_hex":hex(&query.command.cwd),
                        "forwarded_semantic_environment_hex":query.command.environment.iter().map(|(name,value)|(hex(name),hex(value))).collect::<Vec<_>>(),
                        "observed_process_builder_environment_hex":query.observed_environment.iter().map(|(name,value)|(hex(name),hex(value))).collect::<Vec<_>>(),
                        "omitted_private_environment_names":query.omitted_environment.iter().map(|name|String::from_utf8_lossy(name)).collect::<Vec<_>>(),
                        "completed":query.result.as_ref().map(|result|json!({
                            "stdout_hex":hex(&result.stdout),"stderr_hex":hex(&result.stderr),
                            "prepared_frame_hex":result.prepared.encode().ok().map(|bytes|hex(&bytes)),
                            "actual_started":{"pid":result.started.identity.pid,"birth":result.started.identity.birth,
                                "monotonic_ns":result.started.monotonic_ns,"unix_ns":result.started.unix_ns},
                            "actual_finished":format!("{:?}",result.completion.finished.status),
                            "inputs_unchanged":result.completion.inputs_unchanged,
                            "output_limit_exceeded":result.output_limit_exceeded})),
                        "failure_started":query.failure_started.as_ref().map(|frame|format!("{:?}",frame.status)),
                        "failure_observation_frame_hex":query.failure_observation.as_ref().and_then(|failure|failure.encode().ok()).map(|bytes|hex(&bytes)),
                        "failure":query.failure,
                    })).collect::<Vec<_>>());
                    execution["report_failure"] = json!(report.failure);
                    if let Some(failure) = report.failure {
                        return Err(Refusal(format!("native full resolver failed: {failure}")));
                    }
                    if !terminal.normal || !output.status.success() {
                        return Err(Refusal(
                            "resolver root did not retire with normal successful exit".into(),
                        ));
                    }
                    if result.stderr.len() > trust_qualification::dependencies::MAX_STDERR_BYTES {
                        result.output_limit_exceeded = true;
                        return Err(Refusal("resolver raw stderr exceeds finite bound".into()));
                    }
                    Ok(())
                })();
                if let Err(error) = checked {
                    result.failure = Some(error.to_string());
                }
            }
        }
        // These original executable bindings supplement the retained pair's
        // complete source/dependency/SDK checks before and after every outcome.
        for original in [&request.program, &request.compiler] {
            match pair::file_identity(&original.path) {
                Ok(current) if &current == original => {}
                changed => {
                    result.failure = Some(format!(
                        "original resolver executable changed at handoff: {}",
                        match changed {
                            Err(e) => e.to_string(),
                            _ => original.path.display().to_string(),
                        }
                    ));
                }
            }
        }
        self.observation = Some(execution.clone());
        result.execution = Some(execution);
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_original_compiler_binding_is_not_replaced_by_a_fresh_path_hash() {
        let temporary = tempfile::tempdir().unwrap();
        let root = temporary.path().canonicalize().unwrap();
        let sdk = root.join("sdk");
        std::fs::create_dir_all(sdk.join("bin")).unwrap();
        std::fs::write(sdk.join("bin/targo"), b"saved Targo input only").unwrap();
        std::fs::write(sdk.join("bin/trustc"), b"saved compiler input only").unwrap();
        let request = ResolverRequest {
            side: trust_qualification::dependencies::Side::Control,
            subject: trust_qualification::dependencies::Subject::Ay,
            sdk_root: sdk.clone(),
            program: pair::file_identity(&sdk.join("bin/targo")).unwrap(),
            compiler: pair::file_identity(&sdk.join("bin/trustc")).unwrap(),
            cwd: root.clone(),
            cargo_home: root.join("cargo"),
        };
        // Only request data construction; no host, native image or admission.
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            invocation(&request, &None).unwrap();
            std::fs::write(sdk.join("bin/trustc"), b"replacement compiler").unwrap();
            assert!(invocation(&request, &None).is_err());
        } else {
            assert!(invocation(&request, &None).is_err());
        }
    }
}
