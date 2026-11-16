//! Constructive finite-exhaustion proof over the actual scalar machine.
//!
//! The conclusion quantifies over genuine `UInt8`, runs the fixed seven
//! instructions with `sm_run`, and equates the complete `sm_observe` result
//! to the expected frame, return, false overflow flag, and trace. This is NOT
//! 256 host checks labeled universal: `Nat.casesOn` eliminates every possible
//! Fin value and the remaining tail is contradicted by its actual bound.
//! `Fin.rec`, `BitVec.rec` and `UInt8.rec` lift this to every UInt8.
//! No source/MIR adapter, caller fact or compiler authority is supplied.
//!
//! The versioned bundle retains all four definitions, 257 helpers, and the
//! final theorem. Replay reconstructs the fixed model and the explicitly
//! bound Clean foundation, then checks the complete local proof closure.
//! This is not a self-contained kernel/foundation distribution or a compiler
//! certificate: the replay checker and its built-in Clean foundation are TCB.

use clean_auto::bridge::ay_contract::{deserialize_term, serialize_term};
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker};

use crate::scalar_return::ScalarExecutionModel;

const PROGRAM: &str = "ScalarFamily.program";
const INITIAL: &str = "ScalarFamily.initial";
const EXPECTED: &str = "ScalarFamily.expected";
const OBSERVED: &str = "ScalarFamily.observed";
const THEOREM: &str = "ScalarFamily.widenAddOne";

mod bundle;
pub use bundle::{
    MAX_SCALAR_FAMILY_BUNDLE_BYTES, prove_u8_widen_add_one_family, replay_u8_widen_add_one_family,
};

/// Construct and kernel-check the closed judgment for every `UInt8` input:
/// widening to `UInt16`, checked addition of one, successful overflow
/// assertion, and return of `UInt16.ofNat (UInt8.toNat x + 1)` after seven
/// machine transitions, with the exact complete frame and trace.
///
/// Each definition and proof is serialized, decoded, independently checked
/// against its locally constructed type, and audited for both foundational
/// and non-foundational axiom debt. Exhaustiveness is proved by recursors,
/// not inferred from the number of sampled inputs. The model environment is
/// reconstructed from the fixed `SCALAR_MODEL_SOURCE` on every invocation.
///
/// This is a model-execution theorem only. It does not certify any Rust/MIR
/// body, ABI, instance, caller fact, source refinement, or compiler grade.
/// The complete bundle is constructed and replayed in a fresh environment;
/// this convenience API discards the bytes. Kernel errors,
/// resource failures, and worker panics are errors, never proof success.
pub fn check_u8_widen_add_one_family() -> Result<(), String> {
    let bytes = prove_u8_widen_add_one_family()?;
    replay_u8_widen_add_one_family(&bytes)
}

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
fn app<const N: usize>(name: &str, args: [Expr; N]) -> Expr {
    Expr::apps(c(name), args)
}
fn poly<const N: usize>(name: &str, level: Level, args: [Expr; N]) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![level]), args)
}
fn n(value: u64) -> Expr {
    Expr::nat_lit(value)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, domain, body)
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, body)
}
fn type_level() -> Level {
    Level::succ(Level::zero())
}
fn bool_(value: bool) -> Expr {
    c(if value { "Bool.true" } else { "Bool.false" })
}
fn u16_(value: Expr) -> Expr {
    app("UInt16.ofNat", [value])
}
fn value_u16(value: Expr) -> Expr {
    app("SMValue.u16", [value])
}
fn value_u8(value: Expr) -> Expr {
    app("SMValue.u8", [value])
}

fn frame(values: [Option<Expr>; 6]) -> Expr {
    let types = ["u8", "u16", "u16", "pair16", "bool", "u16"];
    types.into_iter().zip(values).rev().fold(c("SMFrame.nil"), |rest, (ty, value)| {
        let slot = value.map_or_else(|| c("SMSlot.uninitialized"), |v| app("SMSlot.value", [v]));
        app("SMFrame.cons", [c(&format!("SMTy.{ty}")), slot, rest])
    })
}

#[derive(Clone, Copy)]
struct Construction {
    addend: u16,
    checked: bool,
    fuel: u64,
    expected_return_addend: u16,
    assertion_expected: bool,
    expected_overflow: bool,
    expected_widened_local: Option<u16>,
    expected_trace_len: u64,
}
impl Default for Construction {
    fn default() -> Self {
        Self {
            addend: 1,
            checked: true,
            fuel: 7,
            expected_return_addend: 1,
            assertion_expected: false,
            expected_overflow: false,
            expected_widened_local: None,
            expected_trace_len: 7,
        }
    }
}

fn program(control: Construction) -> Expr {
    let assign = |dst, r| app("SMInstruction.assign", [n(dst), r]);
    let instructions = [
        assign(1, app("SMRvalue.widen", [n(0)])),
        assign(2, app("SMRvalue.literal", [value_u16(u16_(n(u64::from(control.addend))))])),
        assign(3, app("SMRvalue.add", [bool_(control.checked), n(1), n(2)])),
        assign(4, app("SMRvalue.flagField", [n(3)])),
        app("SMInstruction.assert", [n(4), bool_(control.assertion_expected)]),
        assign(5, app("SMRvalue.valueField", [n(3)])),
        app("SMInstruction.ret", [n(5)]),
    ];
    instructions
        .into_iter()
        .rev()
        .fold(c("SMProgram.nil"), |rest, i| app("SMProgram.cons", [i, rest]))
}

fn expected(input: Expr, control: Construction) -> Expr {
    let input_nat = app("UInt8.toNat", [input.clone()]);
    let result =
        u16_(app("Nat.add", [input_nat.clone(), n(u64::from(control.expected_return_addend))]));
    let widened = control.expected_widened_local.map_or(input_nat, |value| n(u64::from(value)));
    let final_frame = frame([
        Some(value_u8(input)),
        Some(value_u16(u16_(widened))),
        Some(value_u16(u16_(n(u64::from(control.addend))))),
        Some(app("SMValue.pair16", [result.clone(), bool_(control.expected_overflow)])),
        Some(app("SMValue.bool", [bool_(control.expected_overflow)])),
        Some(value_u16(result.clone())),
    ]);
    let trace = (0..control.expected_trace_len)
        .fold(c("SMTrace.nil"), |rest, index| app("SMTrace.cons", [n(index), rest]));
    app("SMObservation.mk", [app("SMOutcome.returned", [value_u16(result)]), final_frame, trace])
}

fn proposition(input: Expr) -> Expr {
    poly(
        "Eq",
        type_level(),
        [c("SMObservation"), app(OBSERVED, [input.clone()]), app(EXPECTED, [input])],
    )
}
fn refl_expected(input: Expr) -> Expr {
    poly("Eq.refl", type_level(), [c("SMObservation"), app(EXPECTED, [input])])
}
fn unsigned_from_fin(index: Expr) -> Expr {
    app("UInt8.ofBitVec", [app("BitVec.ofFin", [n(8), index])])
}
fn unsigned_from_bound(value: Expr, bound: Expr) -> Expr {
    unsigned_from_fin(app("Fin.mk", [n(256), value, bound]))
}
fn bound(value: Expr) -> Expr {
    app("Nat.lt", [value, n(256)])
}
fn shifted(tail: Expr, offset: u64) -> Expr {
    app("Nat.add", [tail, n(offset)])
}
fn clause_name(offset: u64) -> String {
    format!("ScalarFamily.bound_{offset}")
}

// forall tail, forall h : tail + offset < 256,
//   proposition (UInt8.ofBitVec (BitVec.ofFin (Fin.mk (tail+offset) h)))
fn clause_goal(offset: u64) -> Expr {
    pi(
        c("Nat"),
        pi(
            bound(shifted(Expr::bvar(0), offset)),
            proposition(unsigned_from_bound(shifted(Expr::bvar(1), offset), Expr::bvar(0))),
        ),
    )
}

fn clause_proof(offset: u64) -> Expr {
    if offset == 256 {
        return tail_clause_proof(256);
    }
    let motive = lam(
        c("Nat"),
        pi(
            bound(shifted(Expr::bvar(0), offset)),
            proposition(unsigned_from_bound(shifted(Expr::bvar(1), offset), Expr::bvar(0))),
        ),
    );
    let zero = lam(bound(n(offset)), refl_expected(unsigned_from_bound(n(offset), Expr::bvar(0))));
    // (succ tail)+offset is definitionally tail+(offset+1).
    let successor = lam(c("Nat"), app(&clause_name(offset + 1), [Expr::bvar(0)]));
    lam(c("Nat"), poly("Nat.casesOn", Level::zero(), [motive, Expr::bvar(0), zero, successor]))
}

fn tail_clause_proof(inversions: usize) -> Expr {
    // h : succ^(257) tail <= 256. Invert 256 successor bounds,
    // obtaining succ tail <= 0, then eliminate the contradiction.
    // The parameter is a proof-construction test seam, not a trusted claim:
    // dropping even one inversion must fail the ordinary kernel check.
    let mut proof = Expr::bvar(0);
    for remaining in (1..=256).rev().take(inversions) {
        proof = app(
            "Nat.le_of_succ_le_succ",
            [shifted(Expr::bvar(1), remaining), n(remaining - 1), proof],
        );
    }
    let contradiction = app("Nat.not_succ_le_zero", [Expr::bvar(1), proof]);
    let goal = proposition(unsigned_from_bound(shifted(Expr::bvar(1), 256), Expr::bvar(0)));
    lam(
        c("Nat"),
        lam(
            bound(shifted(Expr::bvar(0), 256)),
            poly("False.elim", Level::zero(), [goal, contradiction]),
        ),
    )
}

fn universal_goal() -> Expr {
    pi(c("UInt8"), proposition(Expr::bvar(0)))
}
fn universal_proof() -> Expr {
    let fin_ty = app("Fin", [n(256)]);
    let bitvec_ty = app("BitVec", [n(8)]);
    let fin_motive = lam(fin_ty.clone(), proposition(unsigned_from_fin(Expr::bvar(0))));
    let fin_minor = lam(
        c("Nat"),
        lam(bound(Expr::bvar(0)), app(&clause_name(0), [Expr::bvar(1), Expr::bvar(0)])),
    );
    let fin_proof = lam(
        fin_ty.clone(),
        poly("Fin.rec", Level::zero(), [n(256), fin_motive, fin_minor, Expr::bvar(0)]),
    );
    let bv_motive = lam(bitvec_ty.clone(), proposition(app("UInt8.ofBitVec", [Expr::bvar(0)])));
    let bv_proof = lam(
        bitvec_ty,
        poly("BitVec.rec", Level::zero(), [n(8), bv_motive, fin_proof, Expr::bvar(0)]),
    );
    let u8_motive = lam(c("UInt8"), proposition(Expr::bvar(0)));
    lam(c("UInt8"), poly("UInt8.rec", Level::zero(), [u8_motive, bv_proof, Expr::bvar(0)]))
}

fn register(
    env: &mut Environment,
    name: &str,
    ty: Expr,
    value: Expr,
    theorem: bool,
) -> Result<Vec<u8>, String> {
    let tc = TypeChecker::new(env);
    let _ = tc.infer_sort(&ty).map_err(|e| format!("{name} goal ill-typed: {e:?}"))?;
    tc.check_type(&value, &ty).map_err(|e| format!("{name} proof rejected: {e:?}"))?;
    let bytes = serialize_term(&value).map_err(|e| format!("{name} serialization: {e:?}"))?;
    drop(tc);
    decode_and_register(env, name, ty, &bytes, theorem)?;
    Ok(bytes)
}

// Names, types, and declaration kinds are supplied by this module, never
// decoded from a claimant-authored envelope. Even valid term bytes carry no
// authority until checked against the canonical locally constructed type.
fn decode_and_register(
    env: &mut Environment,
    name: &str,
    ty: Expr,
    bytes: &[u8],
    theorem: bool,
) -> Result<(), String> {
    let tc = TypeChecker::new(env);
    let _ = tc.infer_sort(&ty).map_err(|e| format!("{name} goal ill-typed: {e:?}"))?;
    let decoded = deserialize_term(bytes).map_err(|e| format!("{name} decode: {e:?}"))?;
    tc.check_type(&decoded, &ty).map_err(|e| format!("{name} roundtrip: {e:?}"))?;
    drop(tc);
    let name = Name::from_string(name);
    let declaration = if theorem {
        Declaration::Theorem { name: name.clone(), level_params: vec![], type_: ty, value: decoded }
    } else {
        Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: decoded,
            is_reducible: true,
        }
    };
    env.add_decl(declaration).map_err(|e| format!("{name} registration: {e:?}"))?;
    if !env.axiom_deps(&name).is_some_and(|a| a.is_empty())
        || !env.foundational_axiom_deps(&name).is_some_and(|a| a.is_empty())
    {
        return Err(format!("{name} has axiom debt"));
    }
    Ok(())
}

#[cfg(test)]
fn prepare_in(mut env: Environment, control: Construction) -> Result<Environment, String> {
    for (name, ty, value) in fixed_definitions(control) {
        register(&mut env, name, ty, value, false)?;
    }
    Ok(env)
}

fn fixed_definitions(control: Construction) -> Vec<(&'static str, Expr, Expr)> {
    let input = Expr::bvar(0);
    let initial = app(
        "SMState.running",
        [
            n(0),
            c(PROGRAM),
            frame([Some(value_u8(input.clone())), None, None, None, None, None]),
            c("SMTrace.nil"),
        ],
    );
    let expected_value = lam(c("UInt8"), expected(input.clone(), control));
    let observed = app("sm_observe", [app("sm_run", [n(control.fuel), app(INITIAL, [input])])]);
    vec![
        (PROGRAM, c("SMProgram"), program(control)),
        (INITIAL, pi(c("UInt8"), c("SMState")), lam(c("UInt8"), initial)),
        (EXPECTED, pi(c("UInt8"), c("SMObservation")), expected_value),
        (OBSERVED, pi(c("UInt8"), c("SMObservation")), lam(c("UInt8"), observed)),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn model_environment() -> Environment {
        static MODEL: std::sync::OnceLock<ScalarExecutionModel> = std::sync::OnceLock::new();
        MODEL
            .get_or_init(|| ScalarExecutionModel::new().expect("fixed model must check"))
            .environment()
            .clone()
    }

    fn worker(f: impl FnOnce() + Send + 'static) {
        crate::checker_core::run_on_large_stack(f).expect("large-stack control worker");
    }

    fn leaf_goal(input: u64) -> Expr {
        pi(bound(n(input)), proposition(unsigned_from_bound(n(input), Expr::bvar(0))))
    }

    fn leaf_proof(input: u64) -> Expr {
        lam(bound(n(input)), refl_expected(unsigned_from_bound(n(input), Expr::bvar(0))))
    }

    fn leaf(control: Construction, input: u64) -> Result<(), String> {
        let mut env = prepare_in(model_environment(), control)?;
        register(&mut env, "ScalarFamily.testLeaf", leaf_goal(input), leaf_proof(input), true)?;
        Ok(())
    }

    #[test]
    fn universal_u8_widen_add_one_executes_and_returns_without_overflow() {
        check_u8_widen_add_one_family().expect("whole model execution must prove for every UInt8");
    }

    #[test]
    fn boundary_cases_and_extra_fuel_preserve_the_whole_observation() {
        worker(|| {
            for input in [0, 254, 255] {
                leaf(Construction::default(), input).expect("actual UInt8 boundary leaf");
            }
            leaf(Construction { fuel: 8, ..Construction::default() }, 255)
                .expect("halted state absorbs extra fuel without changing trace");
        });
    }

    #[test]
    fn actual_program_result_flag_assertion_overflow_and_fuel_mutations_fail() {
        worker(|| {
            for (label, control) in [
                ("changed addend", Construction { addend: 2, ..Construction::default() }),
                (
                    "changed checked flag",
                    Construction { checked: false, ..Construction::default() },
                ),
                (
                    "wrong assertion polarity",
                    Construction { assertion_expected: true, ..Construction::default() },
                ),
                (
                    "actual overflow and panic",
                    Construction {
                        addend: u16::MAX,
                        expected_return_addend: u16::MAX,
                        ..Construction::default()
                    },
                ),
                ("return not yet executed", Construction { fuel: 6, ..Construction::default() }),
            ] {
                let error = leaf(control, 255).expect_err(label);
                assert!(error.contains("proof rejected"), "{label}: {error}");
            }
        });
    }

    #[test]
    fn expected_return_flag_nonreturned_frame_and_trace_mutations_fail() {
        worker(|| {
            for (label, control) in [
                (
                    "wrong return",
                    Construction { expected_return_addend: 2, ..Construction::default() },
                ),
                (
                    "wrong overflow observation",
                    Construction { expected_overflow: true, ..Construction::default() },
                ),
                (
                    "nonreturned local only",
                    Construction { expected_widened_local: Some(254), ..Construction::default() },
                ),
                ("trace only", Construction { expected_trace_len: 6, ..Construction::default() }),
            ] {
                let error = leaf(control, 255).expect_err(label);
                assert!(error.contains("proof rejected"), "{label}: {error}");
            }
        });
    }

    #[test]
    fn omitted_tail_or_interior_case_cannot_establish_exhaustiveness() {
        worker(|| {
            let base = prepare_in(model_environment(), Construction::default()).unwrap();
            let mut missing_tail = base.clone();
            let error = register(
                &mut missing_tail,
                &clause_name(255),
                clause_goal(255),
                clause_proof(255),
                true,
            )
            .unwrap_err();
            assert!(error.contains("proof rejected"), "{error}");
            let mut missing_interior = base;
            for offset in (129..=256).rev() {
                register(
                    &mut missing_interior,
                    &clause_name(offset),
                    clause_goal(offset),
                    clause_proof(offset),
                    true,
                )
                .unwrap();
            }
            // Case 128 is absent: the constructor cannot jump from 127 to 129.
            let error = register(
                &mut missing_interior,
                &clause_name(127),
                clause_goal(127),
                clause_proof(127),
                true,
            )
            .unwrap_err();
            assert!(error.contains("proof rejected"), "{error}");
        });
    }

    #[test]
    fn incomplete_tail_contradiction_is_not_a_proof() {
        worker(|| {
            let mut env = prepare_in(model_environment(), Construction::default()).unwrap();
            let error = register(
                &mut env,
                &clause_name(256),
                clause_goal(256),
                tail_clause_proof(255),
                true,
            )
            .unwrap_err();
            assert!(error.contains("proof rejected"), "{error}");
        });
    }

    #[test]
    fn axiom_authored_case_is_rejected_even_when_the_term_typechecks() {
        worker(|| {
            let mut env = prepare_in(model_environment(), Construction::default()).unwrap();
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(&clause_name(128)),
                level_params: vec![],
                type_: clause_goal(128),
            })
            .unwrap();
            TypeChecker::new(&env)
                .check_type(&clause_proof(127), &clause_goal(127))
                .expect("control really typechecks by borrowing an assumed clause");
            let error =
                register(&mut env, &clause_name(127), clause_goal(127), clause_proof(127), true)
                    .unwrap_err();
            assert!(error.contains("axiom debt"), "{error}");
        });
    }

    #[test]
    fn validly_serialized_forged_helper_and_final_terms_fail_canonical_recheck() {
        worker(|| {
            let base = prepare_in(model_environment(), Construction::default()).unwrap();
            // These bytes are freshly and correctly serialized, not merely a
            // corrupted transport digest. Their propositions are still false.
            let bytes = serialize_term(&leaf_proof(254)).unwrap();
            let mut env = base.clone();
            let error = decode_and_register(
                &mut env,
                "ScalarFamily.testLeaf",
                leaf_goal(255),
                &bytes,
                true,
            )
            .unwrap_err();
            assert!(error.contains("roundtrip"), "{error}");

            // The very same correctly serialized leaf for input 255 must
            // not replay when the actual program adds two. The locally
            // rebuilt goal still demands +1; neither byte validity nor
            // recomputing any external digest can close that equation.
            let bytes = serialize_term(&leaf_proof(255)).unwrap();
            let mut changed_program = prepare_in(
                model_environment(),
                Construction { addend: 2, ..Construction::default() },
            )
            .unwrap();
            let error = decode_and_register(
                &mut changed_program,
                "ScalarFamily.testLeaf",
                leaf_goal(255),
                &bytes,
                true,
            )
            .unwrap_err();
            assert!(error.contains("roundtrip"), "{error}");

            let bytes = serialize_term(&c("True.intro")).unwrap();
            let mut env = base;
            let error =
                decode_and_register(&mut env, THEOREM, universal_goal(), &bytes, true).unwrap_err();
            assert!(error.contains("roundtrip"), "{error}");
        });
    }

    #[test]
    fn malformed_serialized_proof_cannot_reach_registration() {
        worker(|| {
            let mut env = prepare_in(model_environment(), Construction::default()).unwrap();
            let error =
                decode_and_register(&mut env, THEOREM, universal_goal(), b"not a proof term", true)
                    .unwrap_err();
            assert!(error.contains("decode"), "{error}");
            assert!(env.get_const(&Name::from_string(THEOREM)).is_none());
        });
    }
}
