//! Complete local proof closure for the fixed before/after/model observation.
//!
//! This opaque in-process object retains and redecodes every local term. It
//! is not an external wire format or compiler certificate. The fixed scalar
//! and raw-model definitions and Clean foundation are reconstructed on replay;
//! the checker, those definitions and primitive kernel implementation are TCB.

use super::*;

#[cfg(test)]
mod compiler_move_tests;
#[cfg(test)]
mod controls;

const BEFORE: &str = "MirBridge.before";
const AFTER: &str = "MirBridge.after";
const PROGRAM: &str = "MirBridge.scalarProgram";
const INITIAL: &str = "MirBridge.scalarInitial";
const ACTUAL: &str = "MirBridge.actual";
const EXPECTED: &str = "MirBridge.expected";
const THEOREM: &str = "MirBridge.universal";
const COUNT: usize = 6 + 2 + 257 + 1;

/// Retained, kernel-checked model-level evidence, with no compiler conversion.
/// All local proof dependencies are serialized internally; replay rebuilds
/// the exact goals and basis. This is not a portable foundation attestation.
pub struct ScalarMirBridgeCertificate {
    family: ScalarMirSuccessorFamily,
    before: ScalarMirBody,
    after: ScalarMirBody,
    terms: Vec<Vec<u8>>,
}

impl ScalarMirBridgeCertificate {
    /// Independently decode and check the complete closure in a fresh model.
    pub fn replay(&self) -> Result<(), String> {
        if self.terms.len() != COUNT
            || self.terms.iter().any(|t| t.len() > 512 * 1024)
            || self.terms.iter().map(Vec::len).sum::<usize>() > 8 * 1024 * 1024
        {
            return Err("MIR bridge proof closure exceeds limits or has missing terms".into());
        }
        let before = self.before.clone();
        let after = self.after.clone();
        let terms = self.terms.clone();
        let family = self.family;
        crate::checker_core::run_on_large_stack(move || replay(family, &before, &after, &terms))
            .ok_or("MIR bridge replay worker failed")?
    }

    /// Number of local declarations retained; not an authority or coverage count.
    pub fn local_declarations(&self) -> usize {
        self.terms.len()
    }

    /// Exact model family retained by this closure; not a source authority.
    pub fn family(&self) -> ScalarMirSuccessorFamily {
        self.family
    }
}

/// Kernel-check the exact typed bodies and the universal full-observation
/// bridge for every UInt8. Supplied data are model inputs, not rustc identity.
/// A different but equivalent body is outside this fixed certificate family.
pub fn prove_successor_bridge(
    before: &ScalarMirBody,
    after: &ScalarMirBody,
) -> Result<ScalarMirBridgeCertificate, String> {
    prove_successor_bridge_for_family(ScalarMirSuccessorFamily::CopyFixture, before, after)
}

/// Check the complete fixed model family, including its ownership markers.
/// Selecting a family cannot normalize or waive a changed operand/body.
pub fn prove_successor_bridge_for_family(
    family: ScalarMirSuccessorFamily,
    before: &ScalarMirBody,
    after: &ScalarMirBody,
) -> Result<ScalarMirBridgeCertificate, String> {
    // Bound encodings before copying caller-owned collections or spawning work.
    let _ = body_term(before)?;
    let _ = body_term(after)?;
    let before = before.clone();
    let after = after.clone();
    crate::checker_core::run_on_large_stack(move || {
        let declarations = declarations_for_family(family, &before, &after)?;
        let mut env = model::environment()?;
        let mut terms = Vec::with_capacity(COUNT);
        for declaration in declarations {
            let bytes = serialize_term(&declaration.value)
                .map_err(|e| format!("MIR bridge encode: {e:?}"))?;
            register(&mut env, &declaration, &bytes)?;
            terms.push(bytes);
        }
        Ok(ScalarMirBridgeCertificate { family, before, after, terms })
    })
    .ok_or("MIR bridge construction worker failed")?
}

struct Decl {
    name: String,
    ty: Expr,
    value: Expr,
    theorem: bool,
}
fn definition(name: &str, ty: Expr, value: Expr) -> Decl {
    Decl { name: name.into(), ty, value, theorem: false }
}
fn theorem(name: &str, ty: Expr, value: Expr) -> Decl {
    Decl { name: name.into(), ty, value, theorem: true }
}
fn poly<const N: usize>(name: &str, level: Level, args: [Expr; N]) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(name), vec![level]), args)
}
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    poly("Eq", Level::succ(Level::zero()), [ty, a, b])
}
fn refl(ty: Expr, value: Expr) -> Expr {
    poly("Eq.refl", Level::succ(Level::zero()), [ty, value])
}
fn u16_(value: Expr) -> Expr {
    app("UInt16.ofNat", [value])
}
fn v16(value: Expr) -> Expr {
    app("SMValue.u16", [value])
}
fn v8(value: Expr) -> Expr {
    app("SMValue.u8", [value])
}
fn frame(typed: Vec<(ScalarType, Option<Expr>)>) -> Expr {
    typed.into_iter().rev().fold(c("SMFrame.nil"), |rest, (ty, value)| {
        let slot = value.map_or_else(|| c("SMSlot.uninitialized"), |v| app("SMSlot.value", [v]));
        app("SMFrame.cons", [type_term(ty), slot, rest])
    })
}
fn scalar_frame(values: [Option<Expr>; 6]) -> Expr {
    frame(
        [
            ScalarType::U8,
            ScalarType::U16,
            ScalarType::U16,
            ScalarType::CheckedU16,
            ScalarType::Bool,
            ScalarType::U16,
        ]
        .into_iter()
        .zip(values)
        .collect(),
    )
}
fn scalar_program() -> Expr {
    let assign = |i, r| app("SMInstruction.assign", [n(i), r]);
    [
        assign(1, app("SMRvalue.widen", [n(0)])),
        assign(2, app("SMRvalue.literal", [v16(u16_(n(1)))])),
        assign(3, app("SMRvalue.add", [bool_(true), n(1), n(2)])),
        assign(4, app("SMRvalue.flagField", [n(3)])),
        app("SMInstruction.assert", [n(4), bool_(false)]),
        assign(5, app("SMRvalue.valueField", [n(3)])),
        app("SMInstruction.ret", [n(5)]),
    ]
    .into_iter()
    .rev()
    .fold(c("SMProgram.nil"), |rest, instruction| app("SMProgram.cons", [instruction, rest]))
}
fn raw_trace(before: bool) -> Expr {
    [(0, 0, 0), (0, 1, 0), (0, 2, if before { 3 } else { 1 }), (1, 0, 0), (1, 1, 2)]
        .into_iter()
        .fold(c("RMTrace.nil"), |rest, (bb, pc, kind)| {
            app("RMTrace.cons", [n(bb), n(pc), n(kind), rest])
        })
}
#[cfg(test)]
fn raw_expected(input: Expr, before: bool) -> Expr {
    raw_expected_for_family(ScalarMirSuccessorFamily::CopyFixture, input, before)
}
fn raw_expected_for_family(family: ScalarMirSuccessorFamily, input: Expr, before: bool) -> Expr {
    let widened = u16_(app("UInt8.toNat", [input.clone()]));
    let value = u16_(app("Nat.add", [app("UInt8.toNat", [input.clone()]), n(1)]));
    let frame = frame(vec![
        (ScalarType::U16, Some(v16(value.clone()))),
        (ScalarType::U8, Some(v8(input))),
        (ScalarType::U16, Some(v16(widened))),
        (ScalarType::CheckedU16, Some(app("SMValue.pair16", [value.clone(), bool_(false)]))),
    ]);
    let moves = if before {
        app("RMPlaces.cons", [place_term(&ScalarMirPlace::PairFlag(3)), c("RMPlaces.nil")])
    } else {
        c("RMPlaces.nil")
    };
    // The return's Move happens after the assertion's flag Move. The model
    // logs most recent first. Assertion diagnostic operands are not runtime
    // reads here: no fictitious Local(2) consumption is added.
    let moves = if family == ScalarMirSuccessorFamily::CompilerMove {
        app("RMPlaces.cons", [place_term(&ScalarMirPlace::PairValue(3)), moves])
    } else {
        moves
    };
    app(
        "RMObservation.mk",
        [app("RMOutcome.returned", [v16(value)]), frame, moves, raw_trace(before)],
    )
}
fn scalar_expected(input: Expr) -> Expr {
    let widened = u16_(app("UInt8.toNat", [input.clone()]));
    let value = u16_(app("Nat.add", [app("UInt8.toNat", [input.clone()]), n(1)]));
    let frame = scalar_frame([
        Some(v8(input)),
        Some(v16(widened)),
        Some(v16(u16_(n(1)))),
        Some(app("SMValue.pair16", [value.clone(), bool_(false)])),
        Some(app("SMValue.bool", [bool_(false)])),
        Some(v16(value.clone())),
    ]);
    let trace = (0..7).fold(c("SMTrace.nil"), |rest, i| app("SMTrace.cons", [n(i), rest]));
    app("SMObservation.mk", [app("SMOutcome.returned", [v16(value)]), frame, trace])
}
#[cfg(test)]
fn expected(input: Expr) -> Expr {
    expected_for_family(ScalarMirSuccessorFamily::CopyFixture, input)
}
fn expected_for_family(family: ScalarMirSuccessorFamily, input: Expr) -> Expr {
    app(
        "RMBridgeObservation.mk",
        [
            raw_expected_for_family(family, input.clone(), true),
            raw_expected_for_family(family, input.clone(), false),
            scalar_expected(input),
        ],
    )
}
fn actual(input: Expr, raw_fuel: u64, scalar_fuel: u64) -> Expr {
    let raw = |body| {
        app(
            "rm_observe",
            [app("rm_run", [n(raw_fuel), c(body), app("rm_initial", [c(body), input.clone()])])],
        )
    };
    app(
        "RMBridgeObservation.mk",
        [
            raw(BEFORE),
            raw(AFTER),
            app("sm_observe", [app("sm_run", [n(scalar_fuel), app(INITIAL, [input])])]),
        ],
    )
}
#[cfg(test)]
fn fixed_definitions(before: &ScalarMirBody, after: &ScalarMirBody) -> Result<Vec<Decl>, String> {
    fixed_definitions_for_family(ScalarMirSuccessorFamily::CopyFixture, before, after)
}
fn fixed_definitions_for_family(
    family: ScalarMirSuccessorFamily,
    before: &ScalarMirBody,
    after: &ScalarMirBody,
) -> Result<Vec<Decl>, String> {
    let input = Expr::bvar(0);
    Ok(vec![
        definition(BEFORE, c("RMBody"), body_term(before)?),
        definition(AFTER, c("RMBody"), body_term(after)?),
        definition(PROGRAM, c("SMProgram"), scalar_program()),
        definition(
            INITIAL,
            pi(c("UInt8"), c("SMState")),
            lam(
                c("UInt8"),
                app(
                    "SMState.running",
                    [
                        n(0),
                        c(PROGRAM),
                        scalar_frame([Some(v8(input.clone())), None, None, None, None, None]),
                        c("SMTrace.nil"),
                    ],
                ),
            ),
        ),
        definition(
            ACTUAL,
            pi(c("UInt8"), c("RMBridgeObservation")),
            lam(c("UInt8"), actual(input.clone(), 5, 7)),
        ),
        definition(
            EXPECTED,
            pi(c("UInt8"), c("RMBridgeObservation")),
            lam(c("UInt8"), expected_for_family(family, input)),
        ),
    ])
}
#[cfg(test)]
fn body_bindings() -> Result<Vec<Decl>, String> {
    body_bindings_for_family(ScalarMirSuccessorFamily::CopyFixture)
}
fn body_bindings_for_family(family: ScalarMirSuccessorFamily) -> Result<Vec<Decl>, String> {
    [
        ("MirBridge.beforeBinding", BEFORE, family.before()),
        ("MirBridge.afterBinding", AFTER, family.after()),
    ]
    .into_iter()
    .map(|(name, actual, fixed)| {
        let fixed = body_term(&fixed)?;
        Ok(theorem(name, eq(c("RMBody"), c(actual), fixed.clone()), refl(c("RMBody"), fixed)))
    })
    .collect()
}
fn proposition(input: Expr) -> Expr {
    eq(c("RMBridgeObservation"), app(ACTUAL, [input.clone()]), app(EXPECTED, [input]))
}
fn refl_expected(input: Expr) -> Expr {
    refl(c("RMBridgeObservation"), app(EXPECTED, [input]))
}
fn from_fin(index: Expr) -> Expr {
    app("UInt8.ofBitVec", [app("BitVec.ofFin", [n(8), index])])
}
fn from_bound(value: Expr, bound: Expr) -> Expr {
    from_fin(app("Fin.mk", [n(256), value, bound]))
}
fn bound(value: Expr) -> Expr {
    app("Nat.lt", [value, n(256)])
}
fn shifted(tail: Expr, offset: u64) -> Expr {
    app("Nat.add", [tail, n(offset)])
}
fn clause_name(offset: u64) -> String {
    format!("MirBridge.bound_{offset}")
}
fn clause_goal(offset: u64) -> Expr {
    pi(
        c("Nat"),
        pi(
            bound(shifted(Expr::bvar(0), offset)),
            proposition(from_bound(shifted(Expr::bvar(1), offset), Expr::bvar(0))),
        ),
    )
}
fn clause_proof(offset: u64) -> Expr {
    if offset == 256 {
        let mut proof = Expr::bvar(0);
        for remaining in (1..=256).rev() {
            proof = app(
                "Nat.le_of_succ_le_succ",
                [shifted(Expr::bvar(1), remaining), n(remaining - 1), proof],
            );
        }
        let contradiction = app("Nat.not_succ_le_zero", [Expr::bvar(1), proof]);
        let goal = proposition(from_bound(shifted(Expr::bvar(1), 256), Expr::bvar(0)));
        return lam(
            c("Nat"),
            lam(
                bound(shifted(Expr::bvar(0), 256)),
                poly("False.elim", Level::zero(), [goal, contradiction]),
            ),
        );
    }
    let motive = lam(
        c("Nat"),
        pi(
            bound(shifted(Expr::bvar(0), offset)),
            proposition(from_bound(shifted(Expr::bvar(1), offset), Expr::bvar(0))),
        ),
    );
    let zero = lam(bound(n(offset)), refl_expected(from_bound(n(offset), Expr::bvar(0))));
    let successor = lam(c("Nat"), app(&clause_name(offset + 1), [Expr::bvar(0)]));
    lam(c("Nat"), poly("Nat.casesOn", Level::zero(), [motive, Expr::bvar(0), zero, successor]))
}
fn universal_goal() -> Expr {
    pi(c("UInt8"), proposition(Expr::bvar(0)))
}
fn universal_proof() -> Expr {
    let fin_ty = app("Fin", [n(256)]);
    let bv_ty = app("BitVec", [n(8)]);
    let fin_motive = lam(fin_ty.clone(), proposition(from_fin(Expr::bvar(0))));
    let fin_minor = lam(
        c("Nat"),
        lam(bound(Expr::bvar(0)), app(&clause_name(0), [Expr::bvar(1), Expr::bvar(0)])),
    );
    let fin_proof =
        lam(fin_ty, poly("Fin.rec", Level::zero(), [n(256), fin_motive, fin_minor, Expr::bvar(0)]));
    let bv_motive = lam(bv_ty.clone(), proposition(app("UInt8.ofBitVec", [Expr::bvar(0)])));
    let bv_proof =
        lam(bv_ty, poly("BitVec.rec", Level::zero(), [n(8), bv_motive, fin_proof, Expr::bvar(0)]));
    let motive = lam(c("UInt8"), proposition(Expr::bvar(0)));
    lam(c("UInt8"), poly("UInt8.rec", Level::zero(), [motive, bv_proof, Expr::bvar(0)]))
}
#[cfg(test)]
fn declarations(before: &ScalarMirBody, after: &ScalarMirBody) -> Result<Vec<Decl>, String> {
    declarations_for_family(ScalarMirSuccessorFamily::CopyFixture, before, after)
}
fn declarations_for_family(
    family: ScalarMirSuccessorFamily,
    before: &ScalarMirBody,
    after: &ScalarMirBody,
) -> Result<Vec<Decl>, String> {
    let mut declarations = fixed_definitions_for_family(family, before, after)?;
    declarations.extend(body_bindings_for_family(family)?);
    declarations
        .extend((0..=256).rev().map(|i| theorem(&clause_name(i), clause_goal(i), clause_proof(i))));
    declarations.push(theorem(THEOREM, universal_goal(), universal_proof()));
    Ok(declarations)
}
fn register(env: &mut Environment, expected: &Decl, bytes: &[u8]) -> Result<(), String> {
    let decoded =
        deserialize_term(bytes).map_err(|e| format!("{} decode: {e:?}", expected.name))?;
    let tc = TypeChecker::new(env);
    let _ = tc.infer_sort(&expected.ty).map_err(|e| format!("{} goal: {e:?}", expected.name))?;
    tc.check_type(&decoded, &expected.ty)
        .map_err(|e| format!("{} kernel proof: {e:?}", expected.name))?;
    drop(tc);
    let name = Name::from_string(&expected.name);
    let declaration = if expected.theorem {
        Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: expected.ty.clone(),
            value: decoded,
        }
    } else {
        Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: expected.ty.clone(),
            value: decoded,
            is_reducible: true,
        }
    };
    env.add_decl(declaration).map_err(|e| format!("{} registration: {e:?}", expected.name))?;
    if !env.axiom_deps(&name).is_some_and(|a| a.is_empty())
        || !env.foundational_axiom_deps(&name).is_some_and(|a| a.is_empty())
    {
        return Err(format!("{} axiom debt", expected.name));
    }
    Ok(())
}
fn replay(
    family: ScalarMirSuccessorFamily,
    before: &ScalarMirBody,
    after: &ScalarMirBody,
    terms: &[Vec<u8>],
) -> Result<(), String> {
    let declarations = declarations_for_family(family, before, after)?;
    if terms.len() != declarations.len() {
        return Err("incomplete MIR proof closure".into());
    }
    // The first in-process format intentionally admits only the fixed complete
    // construction, not alternate proofs borrowing additional ambient lemmas.
    for (expected, bytes) in declarations.iter().zip(terms) {
        if *bytes
            != serialize_term(&expected.value).map_err(|e| format!("canonical MIR term: {e:?}"))?
        {
            return Err(format!("{} fixed proof closure mismatch", expected.name));
        }
    }
    let mut env = model::environment()?;
    for (declaration, bytes) in declarations.iter().zip(terms) {
        register(&mut env, declaration, bytes)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn prepared() -> Environment {
        let mut env = model::environment().unwrap();
        for declaration in fixed_definitions(&successor_before(), &successor_after())
            .unwrap()
            .into_iter()
            .chain(body_bindings().unwrap())
        {
            let bytes = serialize_term(&declaration.value).unwrap();
            register(&mut env, &declaration, &bytes).unwrap();
        }
        env
    }
    #[test]
    fn full_before_after_scalar_observation_boundary_cases_kernel_check() {
        crate::checker_core::run_on_large_stack(|| {
            let env = prepared();
            for value in [0, 1, 254, 255] {
                let input = app("UInt8.ofNat", [n(value)]);
                let bytes = serialize_term(&refl_expected(input.clone())).unwrap();
                TypeChecker::new(&env)
                    .check_type(&deserialize_term(&bytes).unwrap(), &proposition(input))
                    .unwrap();
            }
        })
        .expect("boundary bridge worker");
    }
    #[test]
    fn universal_before_after_scalar_bridge_replays_complete_closure() {
        let certificate = prove_successor_bridge(&successor_before(), &successor_after()).unwrap();
        assert_eq!(certificate.local_declarations(), COUNT);
        certificate.replay().unwrap();
    }
}
