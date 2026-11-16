// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Untrusted case-set transport. Only the caller's fresh kernel replay admits a candidate.
//! Directory names live in a trusted private namespace; this is not a filesystem sandbox.

use std::error::Error;
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::{CompilerIdentity, EXTRACTION_FLAGS, SOURCE_PATH_POLICY, Suite, failure, sha256};

const SCHEMA: &str = "trust.source-case-set/v2";
const PROPERTY_SCHEMA: &str = "trust.source-property-set/v2";
const MANIFEST_LIMIT: u64 = 1024 * 1024;
const CERTIFICATE_LIMIT: u64 = 64 * 1024 * 1024;

#[path = "reuse/import.rs"]
mod import;
pub(super) use import::ImportedProofCandidates;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CaseInputs {
    source: PathBuf,
    source_sha256: String,
    compiler: CompilerIdentity,
    source_path_policy: String,
    extraction_flags: Vec<String>,
    suite: Suite,
    module_sha256: String,
    function_id: u32,
}

impl CaseInputs {
    pub(super) fn new(
        source: &Path,
        source_bytes: &[u8],
        compiler: &CompilerIdentity,
        suite: &Suite,
        module: &[u8],
        function_id: u32,
    ) -> Result<Self, Box<dyn Error>> {
        super::validate(suite)?;
        Ok(Self {
            // The caller captured this canonical origin before reading its owned bytes.
            // Never observe the pathname again after a long compile or proof operation.
            source: source.to_owned(),
            source_sha256: sha256(source_bytes),
            compiler: compiler.clone(),
            source_path_policy: SOURCE_PATH_POLICY.to_owned(),
            extraction_flags: EXTRACTION_FLAGS.iter().map(|flag| (*flag).to_owned()).collect(),
            suite: suite.clone(),
            module_sha256: sha256(module),
            function_id,
        })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CaseArtifact {
    index: usize,
    sha256: String,
}

impl CaseArtifact {
    pub(super) fn new(index: usize, bytes: &[u8]) -> Self {
        Self { index, sha256: sha256(bytes) }
    }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: String,
    inputs: CaseInputs,
    certificates: Vec<CaseArtifact>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PropertyManifest {
    schema: String,
    api_schema: String,
    inputs: CaseInputs,
    certificates: Vec<CaseArtifact>,
}

fn inventory(certificates: &[CaseArtifact], count: usize) -> Result<(), Box<dyn Error>> {
    if certificates.len() != count
        || certificates.iter().enumerate().any(|(index, case)| {
            case.index != index
                || case.sha256.len() != 64
                || !case.sha256.bytes().all(|byte| byte.is_ascii_hexdigit())
        })
    {
        return Err(failure("case-set inventory is not the complete ordered input suite"));
    }
    Ok(())
}

pub(super) struct CaseSet {
    directory: PathBuf,
    manifest: Manifest,
    manifest_sha256: String,
}

impl CaseSet {
    pub(super) fn load(directory: &Path, expected: &CaseInputs) -> Result<Self, Box<dyn Error>> {
        let manifest_bytes = read_regular(&directory.join("case-set.json"), MANIFEST_LIMIT)?;
        let manifest: Manifest = serde_json::from_slice(&manifest_bytes)?;
        if manifest.schema != SCHEMA || manifest.inputs != *expected {
            return Err(failure(
                "case-set schema, source, compiler, recipe, suite or module differs",
            ));
        }
        inventory(&manifest.certificates, expected.suite.cases.len())?;
        Ok(Self {
            directory: directory.to_owned(),
            manifest,
            manifest_sha256: sha256(&manifest_bytes),
        })
    }

    pub(super) fn manifest_sha256(&self) -> &str {
        &self.manifest_sha256
    }

    /// Read once. These bytes are still untrusted and must pass fresh kernel replay.
    pub(super) fn read_case(&self, index: usize) -> Result<Vec<u8>, Box<dyn Error>> {
        let descriptor = self.manifest.certificates.get(index).ok_or("case index absent")?;
        let bytes =
            read_regular(&self.directory.join(format!("case-{index}.json")), CERTIFICATE_LIMIT)?;
        if sha256(&bytes) != descriptor.sha256 {
            return Err(failure(format!("case-{index}.json differs from its recorded digest")));
        }
        Ok(bytes)
    }
}

/// Transport only. A matching inventory never replaces current fixed-input replay.
pub(super) struct SourcePropertySet {
    directory: PathBuf,
    manifest: PropertyManifest,
    manifest_sha256: String,
}

impl SourcePropertySet {
    pub(super) fn load(directory: &Path, expected: &CaseInputs) -> Result<Self, Box<dyn Error>> {
        let bytes = read_regular(&directory.join("source-property-set.json"), MANIFEST_LIMIT)?;
        let manifest: PropertyManifest = serde_json::from_slice(&bytes)?;
        if manifest.schema != PROPERTY_SCHEMA
            || manifest.api_schema
                != trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1
            || manifest.inputs != *expected
        {
            return Err(failure(
                "source-property schema, API, source, compiler, recipe, suite or module differs",
            ));
        }
        inventory(&manifest.certificates, expected.suite.cases.len())?;
        Ok(Self { directory: directory.to_owned(), manifest, manifest_sha256: sha256(&bytes) })
    }

    pub(super) fn manifest_sha256(&self) -> &str {
        &self.manifest_sha256
    }

    pub(super) fn read_case(&self, index: usize) -> Result<Vec<u8>, Box<dyn Error>> {
        let descriptor = self.manifest.certificates.get(index).ok_or("property index absent")?;
        let bytes = read_regular(
            &self.directory.join(format!("source-refinement-{index}.json")),
            CERTIFICATE_LIMIT,
        )?;
        if sha256(&bytes) != descriptor.sha256 {
            return Err(failure(format!(
                "source-refinement-{index}.json differs from its recorded digest"
            )));
        }
        Ok(bytes)
    }
}

/// Keep complete, individually checked facts even if a later hostile control fails.
pub(super) fn publish_source_property_set(
    directory: &Path,
    inputs: CaseInputs,
    certificates: Vec<CaseArtifact>,
) -> Result<String, Box<dyn Error>> {
    inventory(&certificates, inputs.suite.cases.len())?;
    let bytes = serde_json::to_vec_pretty(&PropertyManifest {
        schema: PROPERTY_SCHEMA.to_owned(),
        api_schema: trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1.to_owned(),
        inputs,
        certificates,
    })?;
    check_manifest_size(&bytes)?;
    write_new(&directory.join("source-property-set.json"), &bytes)?;
    Ok(sha256(&bytes))
}

/// A complete case set is independent of success in later model/mutation phases.
/// This manifest is provenance, never proof authority or a saved verdict.
pub(super) fn publish_case_set(
    directory: &Path,
    inputs: CaseInputs,
    certificates: Vec<CaseArtifact>,
) -> Result<String, Box<dyn Error>> {
    inventory(&certificates, inputs.suite.cases.len())?;
    let bytes =
        serde_json::to_vec_pretty(&Manifest { schema: SCHEMA.to_owned(), inputs, certificates })?;
    check_manifest_size(&bytes)?;
    write_new(&directory.join("case-set.json"), &bytes)?;
    Ok(sha256(&bytes))
}

fn check_manifest_size(bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    if bytes.len() as u64 > MANIFEST_LIMIT {
        return Err(failure("qualification manifest exceeds its 1 MiB reader bound"));
    }
    Ok(())
}

/// Refuse an oversized current identity before any expensive proof generation
/// or replay. Every actual certificate digest has the same fixed 64-byte size.
pub(super) fn validate_transport_capacity(inputs: &CaseInputs) -> Result<(), Box<dyn Error>> {
    let certificates = (0..inputs.suite.cases.len())
        .map(|index| CaseArtifact { index, sha256: "0".repeat(64) })
        .collect::<Vec<_>>();
    check_manifest_size(&serde_json::to_vec_pretty(&Manifest {
        schema: SCHEMA.to_owned(),
        inputs: inputs.clone(),
        certificates: certificates.clone(),
    })?)?;
    check_manifest_size(&serde_json::to_vec_pretty(&PropertyManifest {
        schema: PROPERTY_SCHEMA.to_owned(),
        api_schema: trust_spec_temporal::INVARIANT_MODEL_PROGRAM_PROPERTY_SCHEMA_V1.to_owned(),
        inputs: inputs.clone(),
        certificates,
    })?)
}

pub(super) fn write_new(path: &Path, bytes: &[u8]) -> Result<(), Box<dyn Error>> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.mode(0o600);
    }
    let mut file = options.open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

pub(super) fn read_regular(path: &Path, limit: u64) -> Result<Vec<u8>, Box<dyn Error>> {
    #[cfg(not(unix))]
    {
        let _ = (path, limit);
        Err(failure("case reuse requires no-follow, nonblocking regular-file admission"))
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(path)?;
        let metadata = file.metadata()?;
        if !metadata.is_file() || metadata.len() > limit {
            return Err(failure("case-set input is not a bounded regular file"));
        }
        let mut bytes = Vec::new();
        file.take(limit + 1).read_to_end(&mut bytes)?;
        if bytes.len() as u64 > limit {
            return Err(failure("case-set input grew beyond its bounded read"));
        }
        Ok(bytes)
    }
}

/// Admit disjoint namespaces before creating output. Parent directories are trusted:
/// canonical paths and no-follow leaves do not defeat hostile directory replacement.
pub(super) fn admit_directories(
    requested: &Path,
    prior: Option<&Path>,
    source_properties: Option<&Path>,
) -> Result<(PathBuf, Option<PathBuf>, Option<PathBuf>), Box<dyn Error>> {
    let parent =
        requested.parent().filter(|path| !path.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let output = fs::canonicalize(parent)?.join(requested.file_name().ok_or("output has no leaf")?);
    let prior = prior.map(fs::canonicalize).transpose()?;
    let source_properties = source_properties.map(fs::canonicalize).transpose()?;
    for prior in [&prior, &source_properties].into_iter().flatten() {
        if !prior.is_dir() || output.starts_with(prior) || prior.starts_with(&output) {
            return Err(failure("prior evidence and new output must be disjoint directories"));
        }
    }
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt as _;
        builder.mode(0o700);
    }
    builder.create(&output)?;
    Ok((output, prior, source_properties))
}

#[cfg(all(test, unix))]
#[path = "reuse/property_tests.rs"]
mod property_tests;

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    pub(super) fn fixture(directory: &Path) -> (CaseInputs, Vec<u8>) {
        let source = directory.join("subject.rs");
        fs::write(&source, b"fixture source").unwrap();
        let suite = Suite {
            function: "answer".to_owned(),
            fuel: 8,
            cases: vec![super::super::Case { arguments: vec![], expected: true, permitted: true }],
            mutation_from: "true".to_owned(),
            mutation_to: "false".to_owned(),
        };
        let compiler = super::super::identity::fixture();
        let inputs =
            CaseInputs::new(&source, b"fixture source", &compiler, &suite, b"module", 0).unwrap();
        // Transport fixture, not a proof. Acceptance still requires the caller's kernel check.
        let bytes = b"untrusted candidate".to_vec();
        write_new(&directory.join("case-0.json"), &bytes).unwrap();
        publish_case_set(directory, inputs.clone(), vec![CaseArtifact::new(0, &bytes)]).unwrap();
        (inputs, bytes)
    }

    #[test]
    fn a_recomputed_transport_digest_cannot_admit_a_tampered_kernel_proof() {
        use trust_ir::{
            Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module,
            Ty, ValueId,
        };
        use trust_spec_temporal::literal_refinement::LiteralRefinementError;
        // Codec fixture only. Actual source qualification always uses compiler output.
        let mut module = Module::new("reuse_kernel_fixture");
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        });
        let mut function =
            Function::new(FuncId::new(0), "answer", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        function.blocks.push(block);
        module.functions.push(function);
        let module = trust_ir::binary::serialize_module(&module).unwrap();
        let dir = tempfile::tempdir().unwrap();
        let (mut inputs, _) = fixture(dir.path());
        inputs.module_sha256 = sha256(&module);
        let case = &inputs.suite.cases[0];
        let claim = super::super::property(case, inputs.suite.fuel);
        let mut certificate = super::super::certify_literal_property(
            &module,
            0,
            &super::super::invocation(case),
            &claim,
            "SourceQualification.checked",
        )
        .unwrap();
        let good = serde_json::to_vec(&certificate).unwrap();
        super::super::recheck_case_blob(&good, &module, 0, case, inputs.suite.fuel).unwrap();
        certificate.property.proof_term.clear();
        let tampered = serde_json::to_vec(&certificate).unwrap();
        fs::write(dir.path().join("case-0.json"), &tampered).unwrap();
        let manifest = Manifest {
            schema: SCHEMA.to_owned(),
            inputs: inputs.clone(),
            certificates: vec![CaseArtifact::new(0, &tampered)],
        };
        fs::write(dir.path().join("case-set.json"), serde_json::to_vec(&manifest).unwrap())
            .unwrap();
        let loaded = CaseSet::load(dir.path(), &inputs).unwrap();
        let candidate = loaded.read_case(0).expect("the attack has a matching transport digest");
        let error =
            super::super::recheck_case_blob(&candidate, &module, 0, case, inputs.suite.fuel)
                .unwrap_err();
        assert!(matches!(
            error.downcast_ref::<LiteralRefinementError>(),
            Some(LiteralRefinementError::ArtifactMismatch { .. })
        ));
    }

    #[test]
    fn changed_semantic_inputs_or_unknown_policy_never_reuse_a_manifest() {
        let dir = tempfile::tempdir().unwrap();
        let (inputs, _) = fixture(dir.path());
        CaseSet::load(dir.path(), &inputs).unwrap();
        let mut changed = Vec::new();
        let mut source = inputs.clone();
        source.source_sha256.push('0');
        changed.push(source);
        let mut compiler = inputs.clone();
        compiler.compiler.driver_files[0].1.push('0');
        changed.push(compiler);
        let mut version = inputs.clone();
        version.compiler.version.push(0);
        changed.push(version);
        let mut policy = inputs.clone();
        policy.source_path_policy.push('0');
        changed.push(policy);
        let mut flags = inputs.clone();
        flags.extraction_flags.push("-O".to_owned());
        changed.push(flags);
        let mut module = inputs.clone();
        module.module_sha256.push('0');
        changed.push(module);
        let mut function = inputs.clone();
        function.function_id += 1;
        changed.push(function);
        let mut claim = inputs.clone();
        claim.suite.cases[0].permitted = false;
        changed.push(claim);
        let mut fuel = inputs.clone();
        fuel.suite.fuel += 1;
        changed.push(fuel);
        for different in changed {
            assert!(CaseSet::load(dir.path(), &different).is_err());
        }
        let path = dir.path().join("case-set.json");
        let mut manifest: Manifest = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        manifest.schema = "unknown".to_owned();
        fs::write(path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        assert!(CaseSet::load(dir.path(), &inputs).is_err());
    }

    #[test]
    fn missing_duplicate_swapped_or_changed_cases_are_refused() {
        let dir = tempfile::tempdir().unwrap();
        let (inputs, _) = fixture(dir.path());
        let path = dir.path().join("case-set.json");
        let original = fs::read(&path).unwrap();
        for certificates in [
            vec![],
            vec![CaseArtifact::new(1, b"candidate")],
            vec![CaseArtifact::new(0, b"candidate"); 2],
        ] {
            let mut manifest: Manifest = serde_json::from_slice(&original).unwrap();
            manifest.certificates = certificates;
            fs::write(&path, serde_json::to_vec(&manifest).unwrap()).unwrap();
            assert!(CaseSet::load(dir.path(), &inputs).is_err());
        }
        fs::write(path, original).unwrap();
        let loaded = CaseSet::load(dir.path(), &inputs).unwrap();
        fs::write(dir.path().join("case-0.json"), b"different candidate").unwrap();
        assert!(loaded.read_case(0).is_err());
        fs::remove_file(dir.path().join("case-0.json")).unwrap();
        assert!(loaded.read_case(0).is_err());
    }

    #[test]
    fn candidate_bytes_are_owned_and_the_prior_file_is_never_copied_again() {
        let dir = tempfile::tempdir().unwrap();
        let (inputs, expected) = fixture(dir.path());
        let loaded = CaseSet::load(dir.path(), &inputs).unwrap();
        let bytes = loaded.read_case(0).unwrap();
        fs::write(dir.path().join("case-0.json"), b"replaced after read").unwrap();
        let output = tempfile::tempdir().unwrap();
        write_new(&output.path().join("case-0.json"), &bytes).unwrap();
        assert_eq!(fs::read(output.path().join("case-0.json")).unwrap(), expected);
        assert!(write_new(&output.path().join("case-0.json"), b"overwrite").is_err());
    }

    #[test]
    fn output_overlap_and_symlink_parent_aliases_refuse_before_writing() {
        let dir = tempfile::tempdir().unwrap();
        let prior = dir.path().join("prior");
        fs::create_dir(&prior).unwrap();
        for output in [&prior, &prior.join("nested")] {
            assert!(admit_directories(output, Some(&prior), None).is_err());
        }
        let alias = dir.path().join("alias");
        std::os::unix::fs::symlink(&prior, &alias).unwrap();
        assert!(admit_directories(&alias.join("nested"), Some(&prior), None).is_err());
        assert_eq!(fs::read_dir(&prior).unwrap().count(), 0);
        let output = dir.path().join("output");
        admit_directories(&output, Some(&alias), None).unwrap();
        assert!(admit_directories(&output, Some(&prior), None).is_err());
    }

    #[test]
    fn symlinks_directories_fifos_and_oversize_inputs_do_not_block_or_enter() {
        use std::os::unix::ffi::OsStrExt as _;
        let dir = tempfile::tempdir().unwrap();
        let regular = dir.path().join("regular");
        fs::write(&regular, b"value").unwrap();
        let link = dir.path().join("link");
        std::os::unix::fs::symlink(&regular, &link).unwrap();
        assert!(read_regular(&link, 32).is_err());
        assert!(read_regular(dir.path(), 32).is_err());
        let fifo = dir.path().join("fifo");
        let name = std::ffi::CString::new(fifo.as_os_str().as_bytes()).unwrap();
        // SAFETY: one owned temporary pathname, valid for the duration of this call.
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        assert!(read_regular(&fifo, 32).is_err());
        fs::File::create(&regular).unwrap().set_len(33).unwrap();
        assert!(read_regular(&regular, 32).is_err());
    }
}
