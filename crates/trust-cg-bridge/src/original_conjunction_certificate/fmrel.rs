// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Canonical Formula cohort admission. Artifact bytes are untrusted until
//! their exact pinned identity AND dependency-closed reference replay pass.
//! A checked wrapper additionally requires the actual final source proof.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Path, PathBuf};

use clean_kernel::{
    BigNat, ConstantKind, Declaration, DeclarationVerification, Environment, Expr, ExprKind, Level,
    Name, ReferenceKernel,
};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{
    CapturedModuleBytes, ImportError, load_modules_with_deps_checked, reference_base_closed,
};
use clean_reflect::source_equation::{
    CheckedSourceGoalRelation, check_source_goal_relation_with_proof,
};
use serde::Deserialize;
use sha2::{Digest, Sha256};

const COHORT_SHA256: &str = "8791dc25723bbbbc0ada78fbdba2cc695f07add681bff03167bba3ee7facab51";
const IR_SOURCE: &str = "c50fa44ae14c8da7d8851ace168f8a05aa42e26e";
const SOURCE: &str = "TrustIr.Formula.V2.ConjHoldsB";
const GOAL: &str = "TrustIr.Formula.V2.GoalB";
const RELATION: &str = "TrustIr.Formula.V2.original_bytes_iff_goal";
const BYTE_COUNT: &str = "Trust.Fmrel.Input.ByteCount";
const BYTE_VALUE: &str = "Trust.Fmrel.Input.ByteValue";

mod admission;
mod packet;

pub(super) fn produce(
    original: &[(trust_types::Formula, trust_types::Formula)],
) -> Result<super::CheckedOriginalConjunction, String> {
    packet::produce(original)
}

pub(super) fn replay(
    packet: &super::OriginalConjunctionPacket,
    original: &[(trust_types::Formula, trust_types::Formula)],
) -> Result<super::CheckedOriginalConjunction, String> {
    packet::replay(packet, original)
}

pub(super) fn produce_with_preconditions(
    original: &[(trust_types::Formula, trust_types::Formula)],
    preconditions: &[(trust_types::Formula, trust_types::Formula)],
) -> Result<super::CheckedOriginalConjunction, String> {
    packet::produce_with_preconditions(original, preconditions)
}

pub(super) fn replay_with_preconditions(
    packet: &super::OriginalConjunctionPacket,
    original: &[(trust_types::Formula, trust_types::Formula)],
    preconditions: &[(trust_types::Formula, trust_types::Formula)],
) -> Result<super::CheckedOriginalConjunction, String> {
    packet::replay_with_preconditions(packet, original, preconditions)
}

/// Checked terms are still separate from an object/IR/P/target-bound consumer
/// certificate. Private construction requires the actual final source proof.
pub(super) struct CheckedTerms {
    pub(super) theorem: Declaration,
    pub(super) relation: Declaration,
    pub(super) declarations: Vec<Declaration>,
    pub(super) strings: BTreeMap<Name, String>,
}

#[derive(Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Parts {
    base: String,
    server: Option<String>,
    private: Option<String>,
    ir: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: String,
    ir_commit: String,
    lean_version: String,
    lean_githash: String,
    source_sha256: BTreeMap<String, String>,
    modules: BTreeMap<String, Parts>,
}

fn hash(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn refused(name: &Name, reason: &str) -> ImportError {
    ImportError::UnsupportedModule { module: name.to_string(), reason: reason.into() }
}

/// Private construction retains an ACTUAL admitted reference kernel, never an
/// environment deserialized from a status/snapshot. The concrete artifact pin
/// is distinct from both Clean's source pin and any per-function proof grade.
pub(super) struct Cohort {
    kernel: ReferenceKernel,
    foundations: Vec<String>,
}

impl Cohort {
    fn configured() -> Result<&'static Self, String> {
        static BASE: std::sync::OnceLock<Cohort> = std::sync::OnceLock::new();
        static INIT: std::sync::Mutex<()> = std::sync::Mutex::new(());
        if let Some(base) = BASE.get() {
            return Ok(base);
        }
        let _guard = INIT.lock().map_err(|_| "FMREL: cohort initialization poisoned")?;
        if let Some(base) = BASE.get() {
            return Ok(base);
        }
        let path = std::env::var_os("TRUST_FMREL_COHORT")
            .ok_or("FMREL: exact canonical artifact cohort is unavailable")?;
        let base = Self::load(Path::new(&path))?;
        BASE.set(base).map_err(|_| "FMREL: cohort initialized twice")?;
        BASE.get().ok_or_else(|| "FMREL: admitted cohort missing".into())
    }

    pub(super) fn load(directory: &Path) -> Result<Self, String> {
        let directory = directory.canonicalize().map_err(|error| error.to_string())?;
        let manifest_path = directory.join("MANIFEST.json");
        let mut manifest_bytes = Vec::new();
        std::fs::File::open(&manifest_path)
            .map_err(|error| error.to_string())?
            .take(super::MAX_WIRE_BYTES as u64 + 1)
            .read_to_end(&mut manifest_bytes)
            .map_err(|error| error.to_string())?;
        if manifest_bytes.len() > super::MAX_WIRE_BYTES {
            return Err("FMREL: canonical manifest byte bound".into());
        }
        if hash(&manifest_bytes) != COHORT_SHA256 {
            return Err("FMREL: cohort differs from the exact qualified artifact pin".into());
        }
        let manifest: Manifest =
            serde_json::from_slice(&manifest_bytes).map_err(|error| error.to_string())?;
        if manifest.schema != "trust.formula-relation-cohort.v2"
            || manifest.ir_commit != IR_SOURCE
            || manifest.lean_version != "4.30.0-rc2"
            || manifest.lean_githash.len() != 40
            || manifest.modules.is_empty()
            || manifest.source_sha256.is_empty()
        {
            return Err("FMREL: canonical cohort metadata mismatch".into());
        }
        let mut imported = Environment::for_lean_replay();
        let mut seen = BTreeSet::new();
        let mut before = |name: &Name, path: &Path, index: usize| {
            let module = name.to_string();
            if index != 0
                || !manifest.modules.contains_key(&module)
                || module.split('.').any(|part| {
                    part.is_empty()
                        || !part.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
                })
            {
                return Err(refused(name, "outside exact canonical Formula cohort"));
            }
            let expected = directory.join(module.replace('.', "/") + ".olean");
            if path != expected || path.canonicalize().ok().as_ref() != Some(&expected) {
                return Err(refused(name, "canonical Formula artifact path differs"));
            }
            Ok(())
        };
        let mut captured = |name: &Name, _: &Path, bytes: CapturedModuleBytes<'_>| {
            let module = name.to_string();
            let actual = Parts {
                base: hash(bytes.base),
                server: bytes.server.map(hash),
                private: bytes.private.map(hash),
                ir: bytes.ir.map(hash),
            };
            if manifest.modules.get(&module) != Some(&actual) || !seen.insert(module) {
                return Err(refused(name, "captured Formula artifact bytes differ or repeat"));
            }
            Ok(())
        };
        load_modules_with_deps_checked(
            &mut imported,
            &["TrustIr.Formula.V2.ReflectSound".into(), "TrustIr.Formula.V1.CleanCompat".into()],
            &[PathBuf::from(&directory)],
            &mut before,
            &mut captured,
        )
        .map_err(|error| format!("FMREL canonical import: {error:?}"))?;
        if seen != manifest.modules.keys().cloned().collect() {
            return Err("FMREL: canonical module population mismatch".into());
        }
        let targets: BTreeSet<_> = [
            SOURCE,
            GOAL,
            RELATION,
            "TrustIr.Formula.V1.Compat.Nat.div_add_mod",
            "TrustIr.Formula.V1.Compat.Nat.mul_succ",
            "TrustIr.Formula.V1.Compat.Nat.succ_mul",
        ]
        .into_iter()
        .map(Name::from_string)
        .collect();
        let replay = reference_base_closed(&imported, &targets, &ClosedRecheckOptions::default())
            .map_err(|error| format!("FMREL canonical reference replay: {error:?}"))?;
        if !replay.report.passed()
            || !replay.report.extension_bindings_pinned
            || !replay.entry_refusals.is_empty()
            || !targets.is_subset(&replay.admitted)
        {
            return Err(format!(
                "FMREL canonical admission refused: {} {:?}",
                replay.report.verdict_sentence(),
                replay.entry_refusals
            ));
        }
        let foundations = replay.report.axioms_admitted.clone();
        let kernel = replay.into_kernel().map_err(|report| report.verdict_sentence())?;
        Ok(Self { kernel, foundations })
    }

    pub(super) fn environment(&self) -> &Environment {
        self.kernel.environment()
    }

    pub(super) fn original_input(bytes: &[u8]) -> Result<[Expr; 2], String> {
        if bytes.is_empty() || bytes.len() > super::MAX_ORIGINAL_BYTES {
            return Err("FMREL: whole original-byte population bound".into());
        }
        let limbs = bytes
            .chunks(8)
            .map(|chunk| {
                let mut limb = [0; 8];
                limb[..chunk.len()].copy_from_slice(chunk);
                u64::from_le_bytes(limb)
            })
            .collect();
        Ok([Expr::nat_lit(bytes.len() as u64), Expr::bignat_lit(BigNat::from_limbs(limbs))])
    }

    fn input_names() -> [Expr; 2] {
        [Expr::const_str(BYTE_COUNT), Expr::const_str(BYTE_VALUE)]
    }

    /// These are ordinary closed Nat DATA, not a Formula quotation or an
    /// opaque semantic witness. Rebuild them from independently expected full
    /// bytes for every producer and retained replay environment.
    pub(super) fn install_input(environment: &mut Environment, bytes: &[u8]) -> Result<(), String> {
        for (name, value) in [BYTE_COUNT, BYTE_VALUE].into_iter().zip(Self::original_input(bytes)?)
        {
            environment
                .add_decl(Declaration::Definition {
                    name: Name::from_string(name),
                    level_params: vec![],
                    type_: Expr::const_str("Nat"),
                    value,
                    is_reducible: true,
                })
                .map_err(|error| format!("FMREL original-byte DATA admission: {error:?}"))?;
        }
        Ok(())
    }

    fn require_input(environment: &Environment, bytes: &[u8]) -> Result<(), String> {
        for (name, value) in [BYTE_COUNT, BYTE_VALUE].into_iter().zip(Self::original_input(bytes)?)
        {
            let name = Name::from_string(name);
            let data = environment.get_const(&name).ok_or("FMREL: missing original-byte DATA")?;
            if data.kind != ConstantKind::Definition
                || !data.level_params.is_empty()
                || data.type_ != Expr::const_str("Nat")
                || data.value.as_ref() != Some(&value)
                || environment.declaration_verification(&name)
                    != Some(DeclarationVerification::FullKernelCheck)
            {
                return Err("FMREL: original-byte DATA differs or is not fully checked".into());
            }
        }
        Ok(())
    }

    pub(super) fn expected_goals(
        environment: &Environment,
        bytes: &[u8],
    ) -> Result<(Expr, Expr), String> {
        Self::require_input(environment, bytes)?;
        let arguments = Self::input_names();
        Ok((
            Expr::apps(Expr::const_str(SOURCE), arguments.clone()),
            Expr::apps(Expr::const_str(GOAL), arguments),
        ))
    }

    /// Retained replay checks the supplied relation against the independently
    /// expected original bytes, source closure and complete consumer goal.
    /// Requiring the canonical relation application also retains its checked
    /// readiness premise: empty, malformed and unavailable inputs cannot use
    /// an unrelated equivalence to bypass this route's admission precondition.
    pub(super) fn check_relation(
        &self,
        environment: &Environment,
        bytes: &[u8],
        theorem_name: Name,
        proof: Expr,
    ) -> Result<CheckedSourceGoalRelation, String> {
        let (_, goal) = Self::expected_goals(environment, bytes)?;
        let source = Name::from_string(SOURCE);
        self.require_canonical_source(environment)?;
        let arguments = Self::input_names();
        let recipe_matches = {
            let head = proof.get_app_fn();
            let retained = proof.get_app_args();
            matches!(head.kind(), ExprKind::Const(name, levels) if *name == Name::from_string(RELATION) && levels.is_empty())
                && retained.len() == 3
                && *retained[0] == arguments[0]
                && *retained[1] == arguments[1]
        };
        if !recipe_matches {
            return Err("FMREL: retained relation recipe or original input identity differs".into());
        }
        check_source_goal_relation_with_proof(
            environment,
            &source,
            &[],
            &arguments,
            &goal,
            theorem_name,
            proof,
        )
        .map_err(|error| error.to_string())
    }

    fn require_canonical_source(&self, environment: &Environment) -> Result<(), String> {
        let source = Name::from_string(SOURCE);
        let actual = environment.closure_digest(&source).map_err(|error| error.to_string())?;
        let canonical =
            self.environment().closure_digest(&source).map_err(|error| error.to_string())?;
        if actual != canonical {
            return Err(
                "FMREL: original semantic source closure differs from canonical cohort".into()
            );
        }
        Ok(())
    }

    pub(super) fn produce_relation(
        &self,
        environment: &Environment,
        bytes: &[u8],
        theorem_name: Name,
    ) -> Result<CheckedSourceGoalRelation, String> {
        #[cfg(any(test, feature = "test-hooks"))]
        super::require_production_allowed();
        let [count, value] = Self::input_names();
        let ready = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [Expr::const_str("Bool"), Expr::const_str("Bool.true")],
        );
        let proof = Expr::apps(Expr::const_str(RELATION), [count, value, ready]);
        self.check_relation(environment, bytes, theorem_name, proof)
    }

    pub(super) fn prove_advice(
        &self,
        bytes: &[u8],
        advice: crate::verify_output_instantiate::FormulaAdvice,
    ) -> Result<CheckedTerms, String> {
        #[cfg(any(test, feature = "test-hooks"))]
        super::require_production_allowed();
        let mut environment = self.environment().clone();
        Self::install_input(&mut environment, bytes)?;
        admission::admit(&mut environment, &advice.strings, &advice.declarations)?;
        let relation = self.produce_relation(
            &environment,
            bytes,
            Name::from_string("Trust.Fmrel.SourceGoalRelation"),
        )?;
        let Declaration::Theorem { value: relation_proof, .. } = relation.declaration() else {
            return Err("FMREL: source relation did not retain a theorem".into());
        };
        let (original, goal) = Self::expected_goals(&environment, bytes)?;
        // Check the actual canonical GoalB, not the producer's proposed goal.
        let proof = Expr::apps(
            Expr::const_str("Iff.mpr"),
            [original, goal, relation_proof.clone(), advice.proof],
        );
        let theorem = admission::final_theorem(self, &environment, bytes, proof)?;
        Ok(CheckedTerms {
            theorem,
            relation: relation.declaration().clone(),
            declarations: advice.declarations,
            strings: advice.strings,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_signed_inputs_require_final_source_admission_and_retained_replay() {
        crate::verify_output_instantiate::on_route_stack(|| {
            for (name, bytes) in [
                (
                    "sdiv_var-O0",
                    include_bytes!(
                        "../verify_output_instantiate/div_split/fixtures/sdiv_var-O0.json"
                    )
                    .as_slice(),
                ),
                (
                    "sdiv_var-O2",
                    include_bytes!(
                        "../verify_output_instantiate/div_split/fixtures/sdiv_var-O2.json"
                    )
                    .as_slice(),
                ),
                (
                    "srem_var-O0",
                    include_bytes!(
                        "../verify_output_instantiate/div_split/fixtures/srem_var-O0.json"
                    )
                    .as_slice(),
                ),
                (
                    "srem_var-O2",
                    include_bytes!(
                        "../verify_output_instantiate/div_split/fixtures/srem_var-O2.json"
                    )
                    .as_slice(),
                ),
            ] {
                let original =
                    serde_json::from_slice::<Vec<_>>(bytes).expect("original typed fixture");
                let checked = produce(&original).unwrap_or_else(|error| panic!("{name}: {error}"));
                assert_eq!(checked.packet().model, super::super::FORMULA_MODEL);
                let wire = serde_json::to_vec(checked.packet()).unwrap();
                let retained: super::super::OriginalConjunctionPacket =
                    serde_json::from_slice(&wire).unwrap();
                let replayed = super::super::without_production(|| retained.replay(&original))
                    .unwrap_or_else(|error| panic!("{name} replay: {error}"));
                assert_eq!(checked, replayed);
                let mut reordered = original.clone();
                reordered.swap(0, 1);
                assert_ne!(original, reordered, "ordered-input control must change the subject");
                assert!(super::super::without_production(|| retained.replay(&reordered)).is_err());
                eprintln!(
                    "{name}: FINAL original source admitted; retained replay passed; reordered whole input refused; bytes={}",
                    wire.len()
                );
            }
        });
    }
}
