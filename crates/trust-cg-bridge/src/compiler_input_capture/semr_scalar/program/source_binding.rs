// Copyright 2026 Andrew Yates | Apache-2.0
//! Separately labelled, exact source extension and selected shared foundation;
//! it is never claimed to contain this new whole-program construction.
use std::collections::BTreeMap;

use serde::Deserialize;

pub(super) use super::program_contract::MODEL_IR;
use super::source_contract::{FOUNDATION_IR, PROFILE_IR};
use crate::object_replay::artifact_digest;
const SOURCES: &[(&str, &[u8], &str)] = &[
    (
        "MiniRust.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../first-party/trust-ir/lean/semr/MiniRust.lean"
        )),
        "3bf00652679675fd80e304a36766b5e2f7f200949f99c79a76fb742fe388e0e5",
    ),
    (
        "MiniRustAllocate.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustAllocate.lean"
        )),
        "75621b8a7b4b82b35e95dec4aab4854266b32a64fb585d5322a7aeb0ad4cdb59",
    ),
    (
        "MiniRustAllocate8Audit.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustAllocate8Audit.lean"
        )),
        "5f306eccf024ed9add05ac6e2b9a7dc7706c8bdac885bb9c23d8150856ff785b",
    ),
    (
        "MiniRustAllocate8Room.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustAllocate8Room.lean"
        )),
        "2c4e270bbc731c569fd6f65f85510a5523b77dad80a6da89ebf8e11430929f7b",
    ),
    (
        "MiniRustAllocate8Safety.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustAllocate8Safety.lean"
        )),
        "2f585180712bbe3ce7ff65f8d99f98e1380ec8e72fe2c6ad4a02e4c0f251eb2b",
    ),
    (
        "MiniRustAllocateCheck.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustAllocateCheck.lean"
        )),
        "8ef7f412f8722e72cb144b132ab680bca6bdae85f74056c257c2cf19b0d276e1",
    ),
    (
        "MiniRustMachineNew.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustMachineNew.lean"
        )),
        "76f9d12dea69f43bcfa273088ed6e882b9fe67aafbfacb49754d5b4eeec2bcb4",
    ),
    (
        "MiniRustProgramCall.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustProgramCall.lean"
        )),
        "d210dc4d314ccb0f126b532f0d9c74fc8795e877a5e540ac7ebab8ae1e8238dc",
    ),
    (
        "MiniRustProgramExit.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustProgramExit.lean"
        )),
        "05c8a2a078791beff9858ddb8bf9b2c5bbf4fd78c2d9d7fdd1e083122e4f2cf8",
    ),
    (
        "MiniRustProgramStep.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustProgramStep.lean"
        )),
        "92f8a70339071879a183a04b3b9bdc42a85a065a2a562afa603d55091cf0ffb9",
    ),
    (
        "MiniRustU64AllocatedCall.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64AllocatedCall.lean"
        )),
        "0789bd78e8e6ef69a3b6c254c38563d431fae7ce8d5b72735dfff2a86e04b6f4",
    ),
    (
        "MiniRustU64Availability.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Availability.lean"
        )),
        "609234697306a8dcb2d228a044b7a38b13168db1853ac9e4fabcce79c8a69732",
    ),
    (
        "MiniRustU64AvailabilityControls.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64AvailabilityControls.lean"
        )),
        "d53beeeb47406d5ac151509b7ecef2c22c80c27fa58357292ceb9f204405406e",
    ),
    (
        "MiniRustU64Call.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Call.lean"
        )),
        "dba8b1ca1601bc77587298b34075ae04c171ab2cec667ea76642228f8c5965e2",
    ),
    (
        "MiniRustU64Controls.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Controls.lean"
        )),
        "305692ea60221dc1e2df3a542a7973ce2e9afe9ac1accfa7247cca2606f4c1d1",
    ),
    (
        "MiniRustU64Correspondence.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Correspondence.lean"
        )),
        "6fb5347b20954e50f83fb42894773450ce98785fcd83efd771e8dc80dc30736b",
    ),
    (
        "MiniRustU64Entry.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Entry.lean"
        )),
        "b565bd8738d24944ec4b9711581f69dca3b7159891254d7bd1cfbe06a0cc525a",
    ),
    (
        "MiniRustU64Execution.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Execution.lean"
        )),
        "ee0804196fa8c538a269013d931813025f58097c69932277cac3fc78ccd09f3e",
    ),
    (
        "MiniRustU64ExitCall.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitCall.lean"
        )),
        "25313f647cf3ca3b27f46f062c83d5a70f18d8c5077e0df98b79412373978484",
    ),
    (
        "MiniRustU64ExitControls.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitControls.lean"
        )),
        "f6a76442331c3a33c09bdfa7ec691bdb1f04314c434b897a3a0bc7a090b2a40c",
    ),
    (
        "MiniRustU64ExitExecution.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitExecution.lean"
        )),
        "dd3de7c067b73259b281227616ae205bcdd249ce8f6e39b26c0b513f90af7bf8",
    ),
    (
        "MiniRustU64ExitProgram.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitProgram.lean"
        )),
        "12ce3a7f09f02348dd3d03ffcb27a5aced6dc270dcca9da9e45750757f55c49a",
    ),
    (
        "MiniRustU64ExitRun.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitRun.lean"
        )),
        "c77f977d0500764d24f45d30fd0635d7bab447936681a2485cc58db664794148",
    ),
    (
        "MiniRustU64ExitStart.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitStart.lean"
        )),
        "30188f1ca8b53a54a1d3012f121ba89da72c1308f3d20d23bf98910fc0f08c64",
    ),
    (
        "MiniRustU64ExitStop.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ExitStop.lean"
        )),
        "4edc50137cde4ab593a7ea6e474aec0c686dd7e13f7b1c3a27e25192ce94e778",
    ),
    (
        "MiniRustU64Function.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Function.lean"
        )),
        "0bd2df9aecc980dc91c9fea9b964bfd7bbdb9076c2181dc02b9bc36bb273430d",
    ),
    (
        "MiniRustU64Program.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Program.lean"
        )),
        "3b065d8a41a8b487a15a3fdc71a650e228ba52a1a7bf819b9a330b715ccb3d41",
    ),
    (
        "MiniRustU64ProgramCall.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramCall.lean"
        )),
        "6333dcec91c854b4d1ca9a4ae83c5e3d418d0bd0eefb6c380fb6b58f58504df1",
    ),
    (
        "MiniRustU64ProgramExecution.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramExecution.lean"
        )),
        "c213279102e2856a24ebf00f01900be99f4c778ceb558302717a56d16b6fdad7",
    ),
    (
        "MiniRustU64ProgramExecutionControls.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramExecutionControls.lean"
        )),
        "a4e4537a6fd0a3a07194c45914d325f77134501e13ddbcfef5977336b7418901",
    ),
    (
        "MiniRustU64ProgramFromBytes.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramFromBytes.lean"
        )),
        "bb0f050d77dd41717ce23f16691a7ccee156513c12e6d60044bafea69b1c7d9e",
    ),
    (
        "MiniRustU64ProgramFromBytesControls.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramFromBytesControls.lean"
        )),
        "860ee9709ac381c961cad63e57757ffe37e6061d6cfacf98c00f7d3188107833",
    ),
    (
        "MiniRustU64ProgramReturn.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramReturn.lean"
        )),
        "77510fe88c6641ce7f475d88a8cf8b29fc8c12c21219b67a98a3bb63f59e3495",
    ),
    (
        "MiniRustU64ProgramRun.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramRun.lean"
        )),
        "d21ed3aefcee2d938206e5f67a9c71e4a73db7aa02391af45054d50891053074",
    ),
    (
        "MiniRustU64ProgramStart.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramStart.lean"
        )),
        "d43ef9c8db5c06242b870e08a3da42b98e6bdf280cf4a86f8acdaa8197c081af",
    ),
    (
        "MiniRustU64ProgramTyping.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ProgramTyping.lean"
        )),
        "b4957b0466e17a9cf1cb0e1509cc3213c9c223f87a1deddb481510267e738944",
    ),
    (
        "MiniRustU64Replay.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Replay.lean"
        )),
        "349ad7968aaeaa348f1793590ddf54cc406e1420f6a3e0d5fcbfebeb2c06a5f8",
    ),
    (
        "MiniRustU64RetainedClaims.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64RetainedClaims.lean"
        )),
        "50d018856ce52ad8bb6c61c97cdf5fbc7e6237bd1a377cea1ac3945ea40764a2",
    ),
    (
        "MiniRustU64Return.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Return.lean"
        )),
        "98c85ba4ab49fc741c701f4406efefaab5d90c6ef91a8cdffcdbbf310ef114c7",
    ),
    (
        "MiniRustU64Run.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Run.lean"
        )),
        "9155f6292c4df2f34c70b30c6136b6aa16b5794e2148dc177a25fc7fd36ccdbf",
    ),
    (
        "MiniRustU64ScalarControls.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ScalarControls.lean"
        )),
        "7ceac41265bed95d2ab179f816802c3c88fd606768e84e25a14eefce392585d9",
    ),
    (
        "MiniRustU64ScalarCorrespondence.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ScalarCorrespondence.lean"
        )),
        "194c80e113ea5bd6a151d71bad4d68cb138093bde21cee2b18e3beb57bcef3df",
    ),
    (
        "MiniRustU64ScalarFixtures.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64ScalarFixtures.lean"
        )),
        "f42d433623baccf37bdc1b49577498f85e1a259c7b95aa5dbbc7672206c2b326",
    ),
    (
        "MiniRustU64Step.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/semr_program_source/MiniRustU64Step.lean"
        )),
        "03ddff51d57939cf4902d95109cc3eb6f0b4aa2052dc3e14a448dc46b88a77da",
    ),
    (
        "SemR.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../first-party/trust-ir/lean/semr/SemR.lean"
        )),
        "0ea0e29f2b0d70a158f0ac54725d5175b9be81f4fc5b0a4d0839e9b968ee180d",
    ),
    (
        "SemRMemory.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../first-party/trust-ir/lean/semr/SemRMemory.lean"
        )),
        "a00a3d42cd6e4e6159f91cf749b712179198f56582772064712cd7879bb0f0b4",
    ),
    (
        "SemRMiniRust.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../first-party/trust-ir/lean/semr/SemRMiniRust.lean"
        )),
        "dffb758f95897cba5a7794207752e36435d9ffd453edcd760a57663a88d4ce5a",
    ),
    (
        "U64Addition.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../first-party/trust-ir/lean/semr/U64Addition.lean"
        )),
        "f504dcc8798ebb49b733f0212b0b7fb4b231d816d942cdd7fa6b6a7c3d605965",
    ),
    (
        "U64ScalarProfile.lean",
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/canonical_scalar_profile_source/U64ScalarProfile.lean"
        )),
        "1dcb55e66457872039dfa7e60964ade44c3262588643005c998843bff0bc1961",
    ),
];
#[derive(Deserialize)]
struct Binding {
    ir_commit: String,
    source_sha256: BTreeMap<String, String>,
}

fn check_file(bytes: &[u8], declared: Option<&String>, canonical: &str) -> Result<(), String> {
    if artifact_digest(bytes) != canonical || declared.map(String::as_str) != Some(canonical) {
        return Err("program model source differs from independently bound exact extension".into());
    }
    Ok(())
}
pub(super) fn check(manifest: &str) -> Result<(), String> {
    let binding: Binding = serde_json::from_str(manifest).map_err(|e| e.to_string())?;
    if binding.ir_commit != MODEL_IR {
        return Err("program cohort is not the separately bound model extension".into());
    }
    super::foundation_source_binding::check_foundation(&binding.source_sha256)?;
    for &(name, source, canonical) in SOURCES {
        // These five files are the selected foundation, not files silently
        // relabelled as the historical program extension after a pin move.
        let owner = match name {
            "MiniRust.lean" | "SemR.lean" | "SemRMemory.lean" | "SemRMiniRust.lean"
            | "U64Addition.lean" => FOUNDATION_IR,
            "U64ScalarProfile.lean" => PROFILE_IR,
            _ => MODEL_IR,
        };
        let key = format!("ir@{owner}/lean/semr/{name}");
        check_file(source, binding.source_sha256.get(&key), canonical)?;
    }
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn program_extension_and_selected_foundation_are_separate_exact_inputs() {
        const MANIFEST: &str = include_str!("cohort.json");
        check(MANIFEST).unwrap();
        let original: serde_json::Value = serde_json::from_str(MANIFEST).unwrap();
        for case in 0..3 {
            let mut changed = original.clone();
            match case {
                0 => changed["ir_commit"] = FOUNDATION_IR.into(),
                1 => {
                    changed["source_sha256"]
                        [format!("ir@{MODEL_IR}/lean/semr/MiniRustU64ProgramFromBytes.lean")] =
                        "0".repeat(64).into();
                }
                _ => {
                    changed["source_sha256"][format!("ir@{FOUNDATION_IR}/lean/semr/SemR.lean")] =
                        "0".repeat(64).into();
                }
            }
            assert!(check(&serde_json::to_string(&changed).unwrap()).is_err());
        }
    }
    #[test]
    fn co_mutated_model_copy_and_manifest_cannot_choose_another_source() {
        let (_, source, canonical) = SOURCES[0];
        let mut changed = source.to_vec();
        changed[0] ^= 1;
        let forged = artifact_digest(&changed);
        assert!(check_file(&changed, Some(&forged), canonical).is_err());
        assert!(check_file(source, Some(&forged), canonical).is_err());
    }
}
