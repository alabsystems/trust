// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Parent-selected real Rust behavior for a produced Targo comparison.
//!
//! This is source/expectation DATA, never compilation, execution or proof
//! authority. The concrete native graph owns directories, inputs, programs,
//! admission and retirement. It must compile with its original real compiler
//! and linker, execute produced apps itself, and validate these bytes against
//! the actual app capture. Candidate-Targo reports cannot substitute for that
//! execution. This workload does not establish mathematical verification.

use serde::Serialize;
use trust_sha2::{Digest as _, Sha256};

use crate::{Result, refusal};

const SCHEMA: &str = "trust.native-targo-behavior.v2";
const MAX_REPETITIONS: u32 = 31;
const ARGUMENTS: [u32; 3] = [0, 17, 251];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Scenario {
    Cold,
    Warm,
    PreservedMtimeSourceChange,
    FeatureChange,
    ConcurrentConsumers,
    AmbiguousModuleRefusal,
}

impl Scenario {
    pub fn action(self) -> &'static str {
        match self {
            Self::Cold => "cold-build-and-runtime",
            Self::Warm => "warm-build-and-runtime",
            Self::PreservedMtimeSourceChange => "preserved-mtime-source-and-runtime",
            Self::FeatureChange => "feature-change-and-runtime",
            Self::ConcurrentConsumers => "concurrent-consumers-and-runtime",
            Self::AmbiguousModuleRefusal => "ambiguous-module-refusal",
        }
    }

    /// Planned source state at this stage, not permission to mutate a live
    /// admitted namespace. Retire prior phase inputs and capture the new ones.
    pub fn source_variant(self) -> SourceVariant {
        match self {
            Self::Cold | Self::Warm | Self::ConcurrentConsumers => SourceVariant::Initial,
            Self::PreservedMtimeSourceChange | Self::FeatureChange => SourceVariant::Changed,
            Self::AmbiguousModuleRefusal => SourceVariant::Ambiguous,
        }
    }

    pub fn required_consumers(self) -> &'static [&'static str] {
        match self {
            Self::ConcurrentConsumers => &["app", "peer"],
            Self::AmbiguousModuleRefusal => &[],
            _ => &["app"],
        }
    }

    /// Each side/repetition owns two separate cache domains. Concurrent work
    /// starts cold in its own domain; it never resets the sequential inputs
    /// under the still-retained original source owners.
    pub fn cache_domain(self) -> CacheDomain {
        match self {
            Self::ConcurrentConsumers => CacheDomain::Concurrent,
            _ => CacheDomain::Sequential,
        }
    }

    pub fn transition(self) -> Transition {
        match self {
            Self::Cold | Self::ConcurrentConsumers => Transition::FreshInputsAndCache,
            Self::Warm => Transition::Unchanged,
            Self::PreservedMtimeSourceChange => Transition::ReplaceSameSizePreservingMtime,
            Self::FeatureChange => Transition::ConfigurationOnly,
            Self::AmbiguousModuleRefusal => Transition::AddAmbiguousModule,
        }
    }

    pub fn features(self) -> &'static [&'static str] {
        match self {
            Self::FeatureChange => &["offset"],
            _ => &[],
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum CacheDomain {
    /// Reuse one side/repetition's original output/cache namespace through
    /// cold, warm and invalidation phases. Each mutation retires old owners.
    Sequential,
    /// Fresh shared dependency cache, with distinct app/peer output roots.
    /// Both consumers start concurrently against the same selected leaf.
    Concurrent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Transition {
    FreshInputsAndCache,
    Unchanged,
    ReplaceSameSizePreservingMtime,
    ConfigurationOnly,
    AddAmbiguousModule,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum SourceVariant {
    Initial,
    Changed,
    Ambiguous,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SourceFile {
    /// Canonical relative path under an exclusively owned side input root.
    pub path: String,
    pub bytes: Vec<u8>,
}

/// One fixed complete population. Caller cannot omit a slow/failed scenario.
/// Side/repetition/domain roots must be disjoint. Reuse is deliberate within
/// the selected sequential domain; concurrency uses its own cold cache.
pub struct WorkloadPlan {
    repetitions: u32,
}

impl WorkloadPlan {
    pub fn new(repetitions: u32) -> Result<Self> {
        if !(1..=MAX_REPETITIONS).contains(&repetitions) {
            return Err(refusal("native behavior repetitions must be between one and31"));
        }
        Ok(Self { repetitions })
    }

    pub fn repetitions(&self) -> u32 {
        self.repetitions
    }

    pub fn scenarios(&self) -> &'static [Scenario] {
        &[
            Scenario::Cold,
            Scenario::Warm,
            Scenario::PreservedMtimeSourceChange,
            Scenario::FeatureChange,
            Scenario::ConcurrentConsumers,
            Scenario::AmbiguousModuleRefusal,
        ]
    }

    pub fn arguments(&self) -> &[u32] {
        &ARGUMENTS
    }

    /// Includes ALL source variants, stage order, repetitions, runtime inputs,
    /// feature selection and preservation requirements, not just initial bytes.
    pub fn identity_sha256(&self) -> String {
        let variants = [SourceVariant::Initial, SourceVariant::Changed, SourceVariant::Ambiguous];
        let files = variants.map(|variant| (variant, self.sources(variant)));
        let phases = self
            .scenarios()
            .iter()
            .map(|&scenario| {
                (
                    scenario,
                    scenario.cache_domain(),
                    scenario.transition(),
                    scenario.source_variant(),
                    scenario.features(),
                    scenario.required_consumers(),
                )
            })
            .collect::<Vec<_>>();
        let bytes = serde_json::to_vec(&(
            SCHEMA,
            self.repetitions,
            phases,
            ARGUMENTS,
            files,
            "distinct-side-repetition-domain-caches;sequential-within-domain-reuse;concurrent-distinct-consumer-output-roots;retire-old-input-owners-before-mutation;parent-app-execution;actual-module-refusal",
        )).expect("finite static workload data is serializable");
        format!("{:x}", Sha256::digest(bytes))
    }

    /// Ordinary Rust projects: no registry, network, build script, proc macro,
    /// fake compiler or fake linker. Only the implementation file changes42→43.
    pub fn sources(&self, variant: SourceVariant) -> Vec<SourceFile> {
        let mut files = vec![
            source(
                "leaf/Cargo.toml",
                "[package]\nname='native_leaf'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[features]\noffset=[]\n",
            ),
            source(
                "leaf/src/lib.rs",
                "mod implementation;\npub fn value() -> u32 { implementation::base() + if cfg!(feature = \"offset\") { 1000 } else { 0 } }\n",
            ),
            source(
                "leaf/src/implementation.rs",
                if variant == SourceVariant::Initial {
                    "pub fn base() -> u32 { 42 }\n"
                } else {
                    "pub fn base() -> u32 { 43 }\n"
                },
            ),
        ];
        for consumer in ["app", "peer"] {
            // The selected child runs locked/offline. A missing lockfile is
            // an input error, not a cold build; preselect the real local graph.
            files.push(source(&format!("{consumer}/Cargo.lock"), &format!(
                "# This file is automatically @generated by Cargo.\n# It is not intended for manual editing.\nversion = 4\n\n[[package]]\nname = \"native_{consumer}\"\nversion = \"0.0.0\"\ndependencies = [\n \"native_leaf\",\n]\n\n[[package]]\nname = \"native_leaf\"\nversion = \"0.0.0\"\n"
            )));
            files.push(source(&format!("{consumer}/Cargo.toml"), &format!(
                "[package]\nname='native_{consumer}'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[dependencies]\nnative_leaf={{path='../leaf'}}\n[features]\noffset=['native_leaf/offset']\n"
            )));
            files.push(source(&format!("{consumer}/src/main.rs"),
                "fn main() {\n    let mut args = std::env::args();\n    let _program = args.next().unwrap();\n    let input: u32 = args.next().expect(\"input\").parse().expect(\"bounded integer\");\n    assert!(input <= 251 && args.next().is_none());\n    let result = native_leaf::value().checked_add(input).unwrap();\n    println!(\"native-targo-behavior-v1:{result}\");\n}\n"
            ));
        }
        if variant == SourceVariant::Ambiguous {
            files.push(source("leaf/src/implementation/mod.rs", "pub fn base() -> u32 { 43 }\n"));
        }
        files.sort_by(|left, right| left.path.cmp(&right.path));
        files
    }

    /// Check the parent's actual execution of the independently located app.
    /// Native exit/capture/input/retirement checks remain separate requirements.
    /// In particular this must NEVER be fed candidate build stdout instead.
    pub fn validate_app_output(
        &self,
        scenario: Scenario,
        consumer: &str,
        argument: u32,
        stdout: &[u8],
        stderr: &[u8],
    ) -> Result<()> {
        if !scenario.required_consumers().contains(&consumer) || !ARGUMENTS.contains(&argument) {
            return Err(refusal("unselected behavior scenario, consumer or runtime argument"));
        }
        let base = match scenario.source_variant() {
            SourceVariant::Initial => 42,
            SourceVariant::Changed => 43,
            SourceVariant::Ambiguous => {
                return Err(refusal("ambiguous source must not yield a runtime sample"));
            }
        };
        let offset = if scenario == Scenario::FeatureChange { 1000 } else { 0 };
        let expected = format!("native-targo-behavior-v1:{}\n", base + offset + argument);
        if stdout != expected.as_bytes() || !stderr.is_empty() {
            return Err(refusal(
                "actual app behavior differs from parent-selected source/configuration",
            ));
        }
        Ok(())
    }
}

fn source(path: &str, bytes: &str) -> SourceFile {
    SourceFile { path: path.into(), bytes: bytes.as_bytes().into() }
}

#[cfg(test)]
mod tests;
