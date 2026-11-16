// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! A finite general native job, separate from workload40 and paired60. Plan
//! bytes describe a graph; they never create Root/SDK/resource/input owners,
//! compiler materializations, proof grades, application captures or Git rights.
use std::collections::BTreeSet;
use std::io;

use crate::wire::{Decoder, Encoder, header, invalid};
use crate::workload::InputFile;

pub mod comparison;
pub mod host;
pub mod query;
pub mod service;

pub const STARTUP_ARGUMENT: &str = "--resource-native-job-v1";
pub const READY_ROLE: &str = "native-job-ready-v1";
pub const MAX_NODES: usize = 256;
pub const MAX_SOURCES: usize = 64;
pub const MAX_OUTPUTS: usize = 64;
pub const MAX_PLAN_BYTES: usize = 1024 * 1024;
pub const MAX_ROOT_NS: u64 = 86_400_000_000_000;
pub const HASH_DOMAIN: &[u8] = b"trust.native-job.whole-plan.v1\0";

pub const PROTOCOL_MARKER: [u8; 64] = marker();
const fn marker() -> [u8; 64] {
    let mut result = [0; 64];
    let magic = *b"TRUSTNATIVEJOB01";
    let mut i = 0;
    while i < 16 {
        result[i] = magic[i];
        i += 1;
    }
    let fields = [3u64, 6, 7, 106, 48, 3];
    let mut field = 0;
    while field < fields.len() {
        let bytes = fields[field].to_be_bytes();
        let mut byte = 0;
        while byte < 8 {
            result[16 + field * 8 + byte] = bytes[byte];
            byte += 1;
        }
        field += 1;
    }
    result
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeCondition {
    Retired,
    Succeeded,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dependency {
    pub node: NodeId,
    pub condition: EdgeCondition,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompileMode {
    Build,
    Check,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TargetKind {
    Library,
    Binary,
    Test,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnitSelector {
    pub package: String,
    pub target: String,
    pub kind: TargetKind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Artifact {
    pub producer: NodeId,
    pub unit: UnitSelector,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Frontend {
    OriginalSdk,
    Produced(Artifact),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofPolicy {
    Advisory,
    Certify,
}

/// Semantic inputs only. Actual output/source/SDK descriptions are captured
/// independently by the original Host and retained native Root before use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootInputs {
    pub sdk_root: Vec<u8>,
    pub program: InputFile,
    pub compiler: InputFile,
    pub cwd: Vec<u8>,
    pub cargo_home: Vec<u8>,
    pub output_root: Vec<u8>,
    pub environment: Vec<(Vec<u8>, Vec<u8>)>,
    pub observed_host_store: Option<Vec<u8>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    pub root: Vec<u8>,
    pub manifest: InputFile,
    pub namespace_sha256: [u8; 32],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Output {
    pub name: String,
    pub root: Vec<u8>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    Compile {
        source: u32,
        output: u32,
        unit: UnitSelector,
        mode: CompileMode,
        features: Vec<String>,
        frontend: Frontend,
    },
    Verify {
        artifact: Artifact,
        policy: ProofPolicy,
    },
    Tests {
        artifact: Artifact,
        arguments: Vec<Vec<u8>>,
    },
    Run {
        artifact: Artifact,
        arguments: Vec<Vec<u8>>,
    },
    /// Both produced frontends run the SAME complete maintained behavior
    /// workload. Timing/report bytes remain DATA; the original parent owns
    /// real applications, current proof requirements and native retirement.
    Compare {
        baseline: Artifact,
        candidate: Artifact,
        selection: comparison::Selection,
    },
    /// Development publication only. A plan cannot manufacture the required
    /// original repository/write lease, current gate owners or credentials.
    Land {
        source: u32,
        comparison: NodeId,
        selection: comparison::LandSelection,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub name: String,
    pub dependencies: Vec<Dependency>,
    pub timeout_ns: u64,
    pub kind: Kind,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    pub invocation: [u8; 16],
    pub inputs: RootInputs,
    pub sources: Vec<Source>,
    pub outputs: Vec<Output>,
    pub nodes: Vec<Node>,
    pub timeout_ns: u64,
}

fn path(value: &[u8]) -> bool {
    value.len() > 1
        && value.len() <= 4096
        && value[0] == b'/'
        && !value.contains(&0)
        && value[1..]
            .split(|byte| *byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}
fn within(root: &[u8], child: &[u8]) -> bool {
    root == child || (child.starts_with(root) && child.get(root.len()) == Some(&b'/'))
}
fn name(value: &str) -> bool {
    !value.is_empty() && value.len() <= 256 && !value.contains('\0')
}
fn selector(unit: &UnitSelector) -> bool {
    name(&unit.package) && name(&unit.target)
}
fn file(input: &InputFile) -> bool {
    path(&input.path) && input.sha256 != [0; 32]
}
fn words(values: &[Vec<u8>]) -> bool {
    values.len() <= 256
        && values
            .iter()
            .all(|value| value.len() <= 4096 && !value.contains(&0))
}
/// Borrowed equality inputs common to native Root protocols. This never
/// converts a general job into the fixed workload or paired plan.
#[derive(Clone, Copy)]
pub struct RootHeader<'a> {
    pub root: &'a Vec<u8>,
    pub program: &'a InputFile,
    pub compiler: &'a InputFile,
    pub cwd: &'a Vec<u8>,
    pub cargo_home: &'a Vec<u8>,
    pub output_root: &'a Vec<u8>,
    pub timeout_ns: u64,
}
impl<'a> RootHeader<'a> {
    pub fn workload(plan: &'a crate::workload::WorkloadInvocation) -> Self {
        Self {
            root: &plan.root,
            program: &plan.program,
            compiler: &plan.compiler,
            cwd: &plan.cwd,
            cargo_home: &plan.cargo_home,
            output_root: &plan.output_root,
            timeout_ns: plan.timeout_ns,
        }
    }
}
impl Plan {
    pub fn header(&self) -> RootHeader<'_> {
        RootHeader {
            root: &self.inputs.sdk_root,
            program: &self.inputs.program,
            compiler: &self.inputs.compiler,
            cwd: &self.inputs.cwd,
            cargo_home: &self.inputs.cargo_home,
            output_root: &self.inputs.output_root,
            timeout_ns: self.timeout_ns,
        }
    }
}
impl RootInputs {
    pub fn validate(&self) -> io::Result<()> {
        if !path(&self.sdk_root)
            || !file(&self.program)
            || !file(&self.compiler)
            || self.program.path != [self.sdk_root.as_slice(), b"/bin/targo"].concat()
            || self.compiler.path != [self.sdk_root.as_slice(), b"/bin/trustc"].concat()
            || self.program.path == self.compiler.path
            || !path(&self.cwd)
            || !path(&self.cargo_home)
            || !path(&self.output_root)
            || within(&self.sdk_root, &self.output_root)
            || within(&self.output_root, &self.sdk_root)
            || self
                .observed_host_store
                .as_ref()
                .is_some_and(|value| !path(value))
            || self.environment.len() > 4096
        {
            return Err(invalid());
        }
        let mut names = BTreeSet::new();
        for (key, value) in &self.environment {
            if key.is_empty()
                || key.len() > 4096
                || key.contains(&0)
                || key.contains(&b'=')
                || value.len() > 65536
                || value.contains(&0)
                || !names.insert(key)
            {
                return Err(invalid());
            }
        }
        for (key, expected) in [
            (b"LANG".as_slice(), b"C".as_slice()),
            (b"LC_ALL", b"C"),
            (b"CARGO", self.program.path.as_slice()),
            (b"RUSTC", self.compiler.path.as_slice()),
            (b"CARGO_HOME", self.cargo_home.as_slice()),
            (b"CARGO_CACHE_RUSTC_INFO", b"0"),
        ] {
            if !self
                .environment
                .iter()
                .any(|(name, value)| name == key && value == expected)
            {
                return Err(invalid());
            }
        }
        Ok(())
    }
}
impl Plan {
    pub fn validate(&self) -> io::Result<()> {
        self.inputs.validate()?;
        if self.invocation == [0; 16]
            || self.sources.is_empty()
            || self.sources.len() > MAX_SOURCES
            || self.outputs.is_empty()
            || self.outputs.len() > MAX_OUTPUTS
            || self.nodes.is_empty()
            || self.nodes.len() > MAX_NODES
            || self.timeout_ns == 0
            || self.timeout_ns > MAX_ROOT_NS
        {
            return Err(invalid());
        }
        let mut sources = BTreeSet::new();
        for source in &self.sources {
            if !path(&source.root)
                || !file(&source.manifest)
                || !within(&source.root, &source.manifest.path)
                || source.namespace_sha256 == [0; 32]
                || !sources.insert(&source.root)
                || within(&source.root, &self.inputs.output_root)
                || within(&self.inputs.output_root, &source.root)
                || within(&self.inputs.sdk_root, &source.root)
                || within(&source.root, &self.inputs.sdk_root)
            {
                return Err(invalid());
            }
        }
        let mut output_names = BTreeSet::new();
        let mut output_paths = BTreeSet::new();
        for (index, output) in self.outputs.iter().enumerate() {
            if self.outputs[..index].iter().any(|earlier| {
                within(&earlier.root, &output.root) || within(&output.root, &earlier.root)
            }) || !name(&output.name)
                || !path(&output.root)
                || !within(&self.inputs.output_root, &output.root)
                || output.root == self.inputs.output_root
                || !output_names.insert(&output.name)
                || !output_paths.insert(&output.root)
            {
                return Err(invalid());
            }
        }
        let mut node_names = BTreeSet::new();
        let mut adjacency = vec![Vec::new(); self.nodes.len()];
        let mut indegree = vec![0usize; self.nodes.len()];
        for (index, node) in self.nodes.iter().enumerate() {
            if !name(&node.name)
                || !node_names.insert(&node.name)
                || node.timeout_ns == 0
                || node.timeout_ns > self.timeout_ns
                || node.dependencies.len() > MAX_NODES
            {
                return Err(invalid());
            }
            let mut seen = BTreeSet::new();
            for edge in &node.dependencies {
                let dependency = edge.node.0 as usize;
                if dependency >= self.nodes.len() || dependency == index || !seen.insert(edge.node)
                {
                    return Err(invalid());
                }
                adjacency[dependency].push(index);
                indegree[index] += 1;
            }
            let dependency = |id: NodeId| (id.0 as usize) < self.nodes.len() && seen.contains(&id);
            let artifact = |value: &Artifact| {
                selector(&value.unit)
                    && node.dependencies.iter().any(|edge| {
                        edge.node == value.producer && edge.condition == EdgeCondition::Succeeded
                    })
                    && dependency(value.producer)
                    && matches!(
                        &self.nodes[value.producer.0 as usize].kind,
                        Kind::Compile { unit, .. } if unit == &value.unit
                    )
            };
            let executable = |value: &Artifact| {
                artifact(value)
                    && matches!(
                        self.nodes[value.producer.0 as usize].kind,
                        Kind::Compile {
                            mode: CompileMode::Build,
                            ..
                        }
                    )
                    && matches!(value.unit.kind, TargetKind::Binary | TargetKind::Test)
            };
            match &node.kind {
                Kind::Compile {
                    source,
                    output,
                    unit,
                    features,
                    frontend,
                    ..
                } => {
                    if *source as usize >= self.sources.len()
                        || *output as usize >= self.outputs.len()
                        || !selector(unit)
                        || features.len() > 256
                        || features.iter().any(|value| !name(value))
                        || features.iter().collect::<BTreeSet<_>>().len() != features.len()
                        || matches!(frontend,Frontend::Produced(value)if !executable(value) || value.unit.kind != TargetKind::Binary)
                    {
                        return Err(invalid());
                    }
                }
                Kind::Verify {
                    artifact: value, ..
                } => {
                    if !artifact(value) {
                        return Err(invalid());
                    }
                }
                Kind::Tests {
                    artifact: value,
                    arguments,
                }
                | Kind::Run {
                    artifact: value,
                    arguments,
                } => {
                    if !executable(value)
                        || !words(arguments)
                        || matches!(&node.kind, Kind::Tests { .. })
                            && value.unit.kind != TargetKind::Test
                    {
                        return Err(invalid());
                    }
                }
                Kind::Compare {
                    baseline,
                    candidate,
                    selection,
                } => {
                    if !executable(baseline)
                        || !executable(candidate)
                        || baseline.producer == candidate.producer
                    {
                        return Err(invalid());
                    }
                    selection.validate(self, baseline, candidate, NodeId(index as u32))?;
                }
                Kind::Land {
                    source,
                    comparison,
                    selection,
                } => {
                    if *source as usize >= self.sources.len()
                        || !dependency(*comparison)
                        || !matches!(self.nodes[comparison.0 as usize].kind, Kind::Compare { .. })
                    {
                        return Err(invalid());
                    }
                    selection.validate(self, *source, *comparison)?;
                }
            }
        }
        let mut ready = indegree
            .iter()
            .enumerate()
            .filter_map(|(index, count)| (*count == 0).then_some(index))
            .collect::<Vec<_>>();
        let mut retired = 0;
        while let Some(index) = ready.pop() {
            retired += 1;
            for next in &adjacency[index] {
                indegree[*next] -= 1;
                if indegree[*next] == 0 {
                    ready.push(*next);
                }
            }
        }
        if retired != self.nodes.len() {
            return Err(invalid());
        }
        self.preflight_bytes()?;
        Ok(())
    }
    fn preflight_bytes(&self) -> io::Result<()> {
        let mut bytes = 0usize;
        let mut add = |length: usize| -> io::Result<()> {
            bytes = bytes
                .checked_add(length)
                .and_then(|n| n.checked_add(32))
                .ok_or_else(invalid)?;
            if bytes > MAX_PLAN_BYTES {
                return Err(invalid());
            }
            Ok(())
        };
        for value in [
            &self.inputs.sdk_root,
            &self.inputs.program.path,
            &self.inputs.compiler.path,
            &self.inputs.cwd,
            &self.inputs.cargo_home,
            &self.inputs.output_root,
        ] {
            add(value.len())?;
        }
        if let Some(value) = &self.inputs.observed_host_store {
            add(value.len())?;
        }
        for (key, value) in &self.inputs.environment {
            add(key.len())?;
            add(value.len())?;
        }
        for source in &self.sources {
            add(source.root.len())?;
            add(source.manifest.path.len() + 64)?;
        }
        for output in &self.outputs {
            add(output.name.len())?;
            add(output.root.len())?;
        }
        fn unit(
            value: &UnitSelector,
            add: &mut impl FnMut(usize) -> io::Result<()>,
        ) -> io::Result<()> {
            add(value.package.len())?;
            add(value.target.len())
        }
        for node in &self.nodes {
            add(node.name.len())?;
            add(node.dependencies.len() * 32 + 64)?;
            match &node.kind {
                Kind::Compile {
                    unit: value,
                    features,
                    frontend,
                    ..
                } => {
                    unit(value, &mut add)?;
                    for feature in features {
                        add(feature.len())?;
                    }
                    if let Frontend::Produced(value) = frontend {
                        unit(&value.unit, &mut add)?;
                    }
                }
                Kind::Verify { artifact, .. } => unit(&artifact.unit, &mut add)?,
                Kind::Tests {
                    artifact,
                    arguments,
                }
                | Kind::Run {
                    artifact,
                    arguments,
                } => {
                    unit(&artifact.unit, &mut add)?;
                    for word in arguments {
                        add(word.len())?;
                    }
                }
                Kind::Compare {
                    baseline,
                    candidate,
                    selection,
                } => {
                    unit(&baseline.unit, &mut add)?;
                    unit(&candidate.unit, &mut add)?;
                    if selection.pairs.len() > MAX_NODES / 2
                        || selection.workload_sources.len() > MAX_SOURCES
                    {
                        return Err(invalid());
                    }
                    add(selection.focus.len())?;
                    for pair in &selection.pairs {
                        add(pair.action.len())?;
                        add(32)?;
                    }
                    add(selection
                        .workload_sources
                        .len()
                        .checked_mul(8)
                        .ok_or_else(invalid)?)?;
                }
                Kind::Land { .. } => {}
            }
        }
        Ok(())
    }
    pub fn encode(&self) -> io::Result<Vec<u8>> {
        self.validate()?;
        let mut e = Encoder::new(106);
        e.number(1);
        e.0.extend(self.invocation);
        e.number(self.timeout_ns);
        self.inputs.write(&mut e)?;
        e.number(self.sources.len() as u64);
        for source in &self.sources {
            e.bytes(&source.root)?;
            write_file(&source.manifest, &mut e)?;
            e.0.extend(source.namespace_sha256);
        }
        e.number(self.outputs.len() as u64);
        for output in &self.outputs {
            e.bytes(output.name.as_bytes())?;
            e.bytes(&output.root)?;
        }
        e.number(self.nodes.len() as u64);
        for node in &self.nodes {
            e.bytes(node.name.as_bytes())?;
            e.number(node.timeout_ns);
            e.number(node.dependencies.len() as u64);
            for edge in &node.dependencies {
                e.number(edge.node.0.into());
                e.number(match edge.condition {
                    EdgeCondition::Retired => 0,
                    EdgeCondition::Succeeded => 1,
                });
            }
            node.kind.write(&mut e)?;
        }
        let bytes = e.finish()?;
        if bytes.len() > MAX_PLAN_BYTES {
            return Err(invalid());
        }
        Ok(bytes)
    }
    pub fn decode(bytes: &[u8]) -> io::Result<Self> {
        if bytes.len() > MAX_PLAN_BYTES {
            return Err(invalid());
        }
        let mut d = header(bytes, 106)?;
        if d.number()? != 1 {
            return Err(invalid());
        }
        let invocation = d.array()?;
        let timeout_ns = d.number()?;
        let inputs = RootInputs::read(&mut d)?;
        let count = d.count(MAX_SOURCES)?;
        let mut sources = Vec::new();
        sources.try_reserve_exact(count).map_err(|_| invalid())?;
        for _ in 0..count {
            sources.push(Source {
                root: d.bytes()?,
                manifest: read_file(&mut d)?,
                namespace_sha256: d.array()?,
            });
        }
        let count = d.count(MAX_OUTPUTS)?;
        let mut outputs = Vec::new();
        outputs.try_reserve_exact(count).map_err(|_| invalid())?;
        for _ in 0..count {
            outputs.push(Output {
                name: d.text()?,
                root: d.bytes()?,
            });
        }
        let count = d.count(MAX_NODES)?;
        let mut nodes = Vec::new();
        nodes.try_reserve_exact(count).map_err(|_| invalid())?;
        for _ in 0..count {
            let name = d.text()?;
            let timeout_ns = d.number()?;
            let count = d.count(MAX_NODES)?;
            let mut dependencies = Vec::new();
            dependencies
                .try_reserve_exact(count)
                .map_err(|_| invalid())?;
            for _ in 0..count {
                dependencies.push(Dependency {
                    node: NodeId(d.narrow()?),
                    condition: match d.number()? {
                        0 => EdgeCondition::Retired,
                        1 => EdgeCondition::Succeeded,
                        _ => return Err(invalid()),
                    },
                });
            }
            nodes.push(Node {
                name,
                dependencies,
                timeout_ns,
                kind: Kind::read(&mut d)?,
            });
        }
        d.done()?;
        let plan = Self {
            invocation,
            inputs,
            sources,
            outputs,
            nodes,
            timeout_ns,
        };
        plan.validate()?;
        Ok(plan)
    }
    pub fn binding_preimage(&self) -> io::Result<Vec<u8>> {
        let encoded = self.encode()?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(HASH_DOMAIN.len() + encoded.len())
            .map_err(|_| invalid())?;
        bytes.extend(HASH_DOMAIN);
        bytes.extend(encoded);
        Ok(bytes)
    }
}

fn write_file(input: &InputFile, e: &mut Encoder) -> io::Result<()> {
    e.bytes(&input.path)?;
    e.0.extend(input.sha256);
    Ok(())
}
fn read_file(d: &mut Decoder<'_>) -> io::Result<InputFile> {
    Ok(InputFile {
        path: d.bytes()?,
        sha256: d.array()?,
    })
}
impl RootInputs {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        e.bytes(&self.sdk_root)?;
        write_file(&self.program, e)?;
        write_file(&self.compiler, e)?;
        e.bytes(&self.cwd)?;
        e.bytes(&self.cargo_home)?;
        e.bytes(&self.output_root)?;
        e.number(self.environment.len() as u64);
        for (name, value) in &self.environment {
            e.bytes(name)?;
            e.bytes(value)?;
        }
        e.number(u64::from(self.observed_host_store.is_some()));
        if let Some(value) = &self.observed_host_store {
            e.bytes(value)?;
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        let sdk_root = d.bytes()?;
        let program = read_file(d)?;
        let compiler = read_file(d)?;
        let cwd = d.bytes()?;
        let cargo_home = d.bytes()?;
        let output_root = d.bytes()?;
        let count = d.count(4096)?;
        let mut environment = Vec::new();
        environment
            .try_reserve_exact(count)
            .map_err(|_| invalid())?;
        for _ in 0..count {
            environment.push((d.bytes()?, d.bytes()?));
        }
        let observed_host_store = match d.number()? {
            0 => None,
            1 => Some(d.bytes()?),
            _ => return Err(invalid()),
        };
        Ok(Self {
            sdk_root,
            program,
            compiler,
            cwd,
            cargo_home,
            output_root,
            environment,
            observed_host_store,
        })
    }
}
impl UnitSelector {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        e.bytes(self.package.as_bytes())?;
        e.bytes(self.target.as_bytes())?;
        e.number(match self.kind {
            TargetKind::Library => 0,
            TargetKind::Binary => 1,
            TargetKind::Test => 2,
        });
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(Self {
            package: d.text()?,
            target: d.text()?,
            kind: match d.number()? {
                0 => TargetKind::Library,
                1 => TargetKind::Binary,
                2 => TargetKind::Test,
                _ => return Err(invalid()),
            },
        })
    }
}
impl Artifact {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        e.number(self.producer.0.into());
        self.unit.write(e)
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(Self {
            producer: NodeId(d.narrow()?),
            unit: UnitSelector::read(d)?,
        })
    }
}
impl Kind {
    fn write(&self, e: &mut Encoder) -> io::Result<()> {
        match self {
            Self::Compile {
                source,
                output,
                unit,
                mode,
                features,
                frontend,
            } => {
                e.number(0);
                e.number((*source).into());
                e.number((*output).into());
                unit.write(e)?;
                e.number(match mode {
                    CompileMode::Build => 0,
                    CompileMode::Check => 1,
                });
                e.number(features.len() as u64);
                for feature in features {
                    e.bytes(feature.as_bytes())?;
                }
                match frontend {
                    Frontend::OriginalSdk => e.number(0),
                    Frontend::Produced(artifact) => {
                        e.number(1);
                        artifact.write(e)?;
                    }
                }
            }
            Self::Verify { artifact, policy } => {
                e.number(1);
                artifact.write(e)?;
                e.number(match policy {
                    ProofPolicy::Advisory => 0,
                    ProofPolicy::Certify => 1,
                });
            }
            Self::Tests {
                artifact,
                arguments,
            }
            | Self::Run {
                artifact,
                arguments,
            } => {
                e.number(if matches!(self, Self::Tests { .. }) {
                    2
                } else {
                    3
                });
                artifact.write(e)?;
                e.number(arguments.len() as u64);
                for word in arguments {
                    e.bytes(word)?;
                }
            }
            Self::Compare {
                baseline,
                candidate,
                selection,
            } => {
                e.number(4);
                baseline.write(e)?;
                candidate.write(e)?;
                selection.write(e)?;
            }
            Self::Land {
                source,
                comparison,
                selection,
            } => {
                e.number(5);
                e.number((*source).into());
                e.number(comparison.0.into());
                selection.write(e)?;
            }
        }
        Ok(())
    }
    fn read(d: &mut Decoder<'_>) -> io::Result<Self> {
        Ok(match d.number()? {
            0 => {
                let source = d.narrow()?;
                let output = d.narrow()?;
                let unit = UnitSelector::read(d)?;
                let mode = match d.number()? {
                    0 => CompileMode::Build,
                    1 => CompileMode::Check,
                    _ => return Err(invalid()),
                };
                let count = d.count(256)?;
                let mut features = Vec::new();
                features.try_reserve_exact(count).map_err(|_| invalid())?;
                for _ in 0..count {
                    features.push(d.text()?);
                }
                let frontend = match d.number()? {
                    0 => Frontend::OriginalSdk,
                    1 => Frontend::Produced(Artifact::read(d)?),
                    _ => return Err(invalid()),
                };
                Self::Compile {
                    source,
                    output,
                    unit,
                    mode,
                    features,
                    frontend,
                }
            }
            1 => Self::Verify {
                artifact: Artifact::read(d)?,
                policy: match d.number()? {
                    0 => ProofPolicy::Advisory,
                    1 => ProofPolicy::Certify,
                    _ => return Err(invalid()),
                },
            },
            kind @ (2 | 3) => {
                let artifact = Artifact::read(d)?;
                let count = d.count(256)?;
                let mut arguments = Vec::new();
                arguments.try_reserve_exact(count).map_err(|_| invalid())?;
                for _ in 0..count {
                    arguments.push(d.bytes()?);
                }
                if kind == 2 {
                    Self::Tests {
                        artifact,
                        arguments,
                    }
                } else {
                    Self::Run {
                        artifact,
                        arguments,
                    }
                }
            }
            4 => Self::Compare {
                baseline: Artifact::read(d)?,
                candidate: Artifact::read(d)?,
                selection: comparison::Selection::read(d)?,
            },
            5 => Self::Land {
                source: d.narrow()?,
                comparison: NodeId(d.narrow()?),
                selection: comparison::LandSelection::read(d)?,
            },
            _ => return Err(invalid()),
        })
    }
}

#[cfg(test)]
pub(crate) mod tests;
