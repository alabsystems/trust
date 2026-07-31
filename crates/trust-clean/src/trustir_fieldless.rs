// trust-clean/trustir_fieldless.rs — Trust: FIELDLESS-ENUM Clone/eq/select kernel
// witnesses (2026-07-16).
//
// The KERNEL-CHECKED witnesses for the three `mirsem` fieldless-enum shapes
// ([`crate::mirsem::SemFieldlessEnumClone`] and
// [`crate::mirsem::SemFieldlessEnumEq`] plus
// [`crate::mirsem::SemFieldlessEnumThen`]) — the derived `Clone::clone`,
// `PartialEq::eq`, and `Ordering::then`-class guarded identity select of a
// C-LIKE (fieldless, all-nullary-variant) enum.
//
// THE MODEL. A fieldless enum has NO payload, so its entire runtime value is
// determined by WHICH variant it is — i.e. by its DISCRIMINANT. We reflect that
// discriminant as the SAME opaque total carrier the discriminant-switch
// ADT-return witness uses: `idxElem (e p) (-1)` — `Trust.TrustIr.idxElem`
// applied to the `p`-th parameter's env value and the reserved tag key
// [`crate::mirsem::MIRSEM_DISCRIMINANT_TAG_KEY`] (`-1`, unreachable by any real
// `Field(fld: u64)` read). `idxElem : Int → Int → Int` is a registered `Opaque`
// (never δ-reduces, carries no axiom dependency).
//
//   * `clone(&self) -> E { *self }` is the IDENTITY on that discriminant: the
//     returned fieldless-enum value's tag EQUALS `*self`'s tag. Witnessed as
//     `∀ (e:Env), Eq.{1} Int (disc self) (disc self)` — an `Eq.refl` over the
//     `Int` carrier. The recognizer has already confirmed the body copies
//     `*self` (so the returned tag IS `disc self`); the kernel confirms the
//     reflected term is well-typed against the vendored `Int`/`idxElem`/`Eq`
//     semantics, and the `claimed`-override probe (below) confirms a WRONG RHS
//     is rejected — the value is NOT promoted on shape alone.
//   * `eq(&self, &other) -> bool { disc(*self) == disc(*other) }` is a single
//     `Int.beq` of the two tags: `∀ (e:Env), Eq.{1} Bool
//     (Int.beq (disc self) (disc other)) (Int.beq (disc self) (disc other))`.
//     The `Int.beq (disc self) (disc other)` term IS the reflected return
//     value; the kernel type-checks it against the vendored
//     `Int.beq : Int → Int → Bool` (so a wrong compare constant would not
//     type-check), and the `claimed`-override rejects any RHS not def-eq to it
//     (`Bool.true`, the swapped `Int.beq (disc other) (disc self)`, …).
//   * `then(self, other)`-class selects `other` for the sole literal tag `k`
//     read from the MIR `SwitchInt`, otherwise preserving `self`. Its reflected
//     return tag is `Bool.rec (λ_.Int) (disc self) (disc other)
//     (Int.beq (disc self) k)`. The literal is body-derived, not inferred from a
//     variant name or trusted def-path spelling.
//
// HONESTY TIER — the SAME tier as `trustir_multieq`/`trustir_adt`'s witnesses:
// these are self-contained kernel checks that the RECOGNIZER's reflected term
// is well-typed and internally consistent against the vendored bridge
// semantics; the soundness that the model MATCHES the MIR rests on the
// recognizer reading the shape DIRECTLY off the body (`mirsem.rs`'s two
// `sem_fieldless_enum_*_shape_of` functions), which FAIL CLOSED on every
// near-miss (missing explicit variant metadata, payload-bearing enum, non-`Eq`
// compare, extra statement, non-discriminant operand, rebuild-not-copy clone,
// `&mut self`). Because a fieldless enum's value IS its discriminant, a
// discriminant-preserving clone and a discriminant-comparing eq are COMPLETE
// (not merely partial) models. Pre-P4 dumps with `variants: []` deliberately
// decline: they cannot distinguish an enum from `struct S { __tag: isize }`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Declaration, Environment, Expr, Level, Name, TypeChecker,
};

use crate::mirsem::{
    MIRSEM_DISCRIMINANT_TAG_KEY, SemFieldlessEnumClone, SemFieldlessEnumEq,
    SemFieldlessEnumThen,
};
use crate::trustir_anchor::{
    RefinementVerdict, TRUSTIR_IDX_ELEM, cst, env_ty, int_lit, int_ty, trustir_env,
};

fn bd() -> BinderData {
    BinderData::from(BinderInfo::Default)
}

/// The `Int`-valued DISCRIMINANT of parameter `p`, at env-binder depth `e_bvar`:
/// `idxElem (e p) (-1)` — BYTE-IDENTICAL to what
/// `trustir_adt::sem_operand_to_expr(&SemOperand::Discriminant(Box::new(Var p)))`
/// builds, so a fieldless-enum tag denotes the exact opaque carrier term the
/// discriminant-switch witness already uses.
fn disc_of(p: u64, e_bvar: u32) -> Expr {
    let e_p = Expr::app(Expr::bvar(e_bvar), Expr::nat_lit(p));
    Expr::apps(cst(TRUSTIR_IDX_ELEM), [e_p, int_lit(MIRSEM_DISCRIMINANT_TAG_KEY)])
}

/// Build `(env, statement, proof)` for the FIELDLESS-ENUM `clone` refinement.
/// `claimed` overrides the equation's RHS — `None` for the honest identity
/// claim, `Some(wrong)` for the FAIL-CLOSED PROBE (a WRONG returned tag). `None`
/// (fail-closed) only if the shared trust-ir env fails to build.
fn build_clone_refinement(
    r: &SemFieldlessEnumClone,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let env = trustir_env().ok()?;
    let l1 = Level::succ(Level::zero());
    // Under `λ (e:Env)`: e = bvar 0. The returned fieldless-enum value's tag IS
    // `*self`'s tag (the recognizer confirmed the deref-copy).
    let model = disc_of(r.self_param, 0);
    let rhs = claimed.cloned().unwrap_or_else(|| model.clone());
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
        [int_ty(), model.clone(), rhs],
    );
    let statement = Expr::pi(bd(), env_ty(), eq);
    // PROOF: `λ (e:Env), Eq.refl.{1} Int (disc self)` — has type
    // `∀ e, Eq Int (disc self) (disc self)`, so a `claimed` RHS not def-eq to
    // `disc self` makes `check_type` reject.
    let refl = Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1]), [int_ty(), model]);
    let proof = Expr::lam(bd(), env_ty(), refl);
    Some((env, statement, proof))
}

/// Build `(env, statement, proof)` for the FIELDLESS-ENUM `eq` refinement.
/// `claimed` overrides the equation's RHS — `None` for the honest
/// `Int.beq (disc self) (disc other)` claim, `Some(wrong)` for the FAIL-CLOSED
/// PROBE. `None` (fail-closed) only if the shared trust-ir env fails to build.
fn build_eq_refinement(
    r: &SemFieldlessEnumEq,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let env = trustir_env().ok()?;
    let l1 = Level::succ(Level::zero());
    // Under `λ (e:Env)`: e = bvar 0.
    let disc_self = disc_of(r.self_param, 0);
    let disc_other = disc_of(r.other_param, 0);
    // The reflected return value: `disc(*self) ==? disc(*other)` : Bool.
    let model = Expr::apps(cst("Int.beq"), [disc_self, disc_other]);
    let rhs = claimed.cloned().unwrap_or_else(|| model.clone());
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
        [cst("Bool"), model.clone(), rhs],
    );
    let statement = Expr::pi(bd(), env_ty(), eq);
    // PROOF: `λ (e:Env), Eq.refl.{1} Bool (Int.beq (disc self) (disc other))`.
    let refl =
        Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1]), [cst("Bool"), model]);
    let proof = Expr::lam(bd(), env_ty(), refl);
    Some((env, statement, proof))
}

/// The exact returned discriminant for a recognized fieldless guarded select:
/// `if disc(self) == selected_tag { disc(other) } else { disc(self) }`.
/// `Bool.rec` takes its false minor before its true minor.
fn then_select(r: &SemFieldlessEnumThen, e_bvar: u32) -> Expr {
    let l1 = Level::succ(Level::zero());
    let disc_self = disc_of(r.self_param, e_bvar);
    let disc_other = disc_of(r.other_param, e_bvar);
    let guard = Expr::apps(cst("Int.beq"), [disc_self.clone(), int_lit(r.selected_tag)]);
    let motive = Expr::lam(bd(), cst("Bool"), int_ty());
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![l1]),
        [motive, disc_self, disc_other, guard],
    )
}

/// Build `(env, statement, proof)` for the fieldless guarded identity select.
/// The proof is reflexivity over the complete, body-derived select expression;
/// overriding only the statement RHS therefore rejects any claim not
/// definitionally equal to that exact tag/arm selection.
fn build_then_refinement(
    r: &SemFieldlessEnumThen,
    claimed: Option<&Expr>,
) -> Option<(Environment, Expr, Expr)> {
    let env = trustir_env().ok()?;
    let l1 = Level::succ(Level::zero());
    let model = then_select(r, 0);
    let rhs = claimed.cloned().unwrap_or_else(|| model.clone());
    let eq = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
        [int_ty(), model.clone(), rhs],
    );
    let statement = Expr::pi(bd(), env_ty(), eq);
    let refl = Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1]), [int_ty(), model]);
    let proof = Expr::lam(bd(), env_ty(), refl);
    Some((env, statement, proof))
}

/// Add `proof : statement` as a theorem `name` and read its axiom residue — the
/// shared tail of both checks (mirrors `trustir_multieq`'s exactly). Empty
/// residue ⇒ `ProvenModulo3`; a type error / add failure ⇒ `KernelRejected`.
fn check_via_kernel(
    built: Option<(Environment, Expr, Expr)>,
    name: &str,
    shape_msg: &str,
) -> RefinementVerdict {
    let Some((mut env, statement, proof)) = built else {
        return RefinementVerdict::KernelRejected(shape_msg.to_string());
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string(name);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// Check the FIELDLESS-ENUM `clone` (deref-copy identity) refinement against the
/// real clean-kernel, modulo 3.
#[must_use]
pub fn check_fieldless_clone_refinement(r: &SemFieldlessEnumClone) -> RefinementVerdict {
    check_fieldless_clone_refinement_claimed(r, None)
}

/// [`check_fieldless_clone_refinement`] with an explicit `claimed` RHS override
/// — the FAIL-CLOSED PROBE entry point.
#[must_use]
pub(crate) fn check_fieldless_clone_refinement_claimed(
    r: &SemFieldlessEnumClone,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    check_via_kernel(
        build_clone_refinement(r, claimed),
        "Trust.TrustIr.Refinement.fieldless_enum_clone",
        "fieldless-enum clone: shape outside the modeled fragment",
    )
}

/// Check the FIELDLESS-ENUM `eq` (discriminant-compare) refinement against the
/// real clean-kernel, modulo 3.
#[must_use]
pub fn check_fieldless_eq_refinement(r: &SemFieldlessEnumEq) -> RefinementVerdict {
    check_fieldless_eq_refinement_claimed(r, None)
}

/// [`check_fieldless_eq_refinement`] with an explicit `claimed` RHS override —
/// the FAIL-CLOSED PROBE entry point.
#[must_use]
pub(crate) fn check_fieldless_eq_refinement_claimed(
    r: &SemFieldlessEnumEq,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    check_via_kernel(
        build_eq_refinement(r, claimed),
        "Trust.TrustIr.Refinement.fieldless_enum_eq",
        "fieldless-enum eq: shape outside the modeled fragment",
    )
}

/// Check the fieldless guarded identity-select refinement against the real
/// clean-kernel, modulo 3.
#[must_use]
pub fn check_fieldless_then_refinement(r: &SemFieldlessEnumThen) -> RefinementVerdict {
    check_fieldless_then_refinement_claimed(r, None)
}

/// [`check_fieldless_then_refinement`] with an explicit claimed returned-tag
/// override — the fail-closed probe entry point.
#[must_use]
pub(crate) fn check_fieldless_then_refinement_claimed(
    r: &SemFieldlessEnumThen,
    claimed: Option<&Expr>,
) -> RefinementVerdict {
    check_via_kernel(
        build_then_refinement(r, claimed),
        "Trust.TrustIr.Refinement.fieldless_enum_then",
        "fieldless-enum then: shape outside the modeled fragment",
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example_clone() -> SemFieldlessEnumClone {
        SemFieldlessEnumClone { self_param: 0 }
    }
    fn example_eq() -> SemFieldlessEnumEq {
        SemFieldlessEnumEq { self_param: 0, other_param: 1 }
    }
    fn example_then() -> SemFieldlessEnumThen {
        SemFieldlessEnumThen { self_param: 0, other_param: 1, selected_tag: 0 }
    }

    #[test]
    fn clone_refinement_modulo3() {
        assert_eq!(
            check_fieldless_clone_refinement(&example_clone()),
            RefinementVerdict::ProvenModulo3
        );
    }

    #[test]
    fn eq_refinement_modulo3() {
        assert_eq!(check_fieldless_eq_refinement(&example_eq()), RefinementVerdict::ProvenModulo3);
    }

    #[test]
    fn then_refinement_modulo3() {
        assert_eq!(
            check_fieldless_then_refinement(&example_then()),
            RefinementVerdict::ProvenModulo3
        );
    }

    /// FAIL-CLOSED probe (clone): claim the clone returns the CONSTANT tag `0`
    /// even though it copies `*self` — `Eq.refl Int (disc self)` has type
    /// `disc self = disc self`, which is NOT def-eq to `disc self = 0` (the
    /// carrier is opaque), so the kernel rejects.
    #[test]
    fn clone_fail_closed_wrong_constant_claim() {
        let wrong = int_lit(0);
        assert!(matches!(
            check_fieldless_clone_refinement_claimed(&example_clone(), Some(&wrong)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// FAIL-CLOSED probe (clone): claim the clone returns a DIFFERENT parameter's
    /// tag (`disc p1` instead of `disc p0`) — the two opaque carriers are
    /// distinct, so the kernel rejects.
    #[test]
    fn clone_fail_closed_wrong_param_claim() {
        let wrong = disc_of(1, 0);
        assert!(matches!(
            check_fieldless_clone_refinement_claimed(&example_clone(), Some(&wrong)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// FAIL-CLOSED probe (eq): claim eq returns the CONSTANT `Bool.true` — the
    /// `Int.beq` of two opaque tags does not reduce to `true`, so the kernel
    /// rejects.
    #[test]
    fn eq_fail_closed_true_claim() {
        let wrong = cst("Bool.true");
        assert!(matches!(
            check_fieldless_eq_refinement_claimed(&example_eq(), Some(&wrong)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// FAIL-CLOSED probe (eq): claim eq returns the SWAPPED compare
    /// `Int.beq (disc other) (disc self)` — `Int.beq a b` is NOT def-eq to
    /// `Int.beq b a` on opaque `a`, `b`, so the kernel rejects (the model is
    /// the operand ORDER read off the MIR, not an assumed symmetry).
    #[test]
    fn eq_fail_closed_swapped_operands_claim() {
        let disc_self = disc_of(0, 0);
        let disc_other = disc_of(1, 0);
        let swapped = Expr::apps(cst("Int.beq"), [disc_other, disc_self]);
        assert!(matches!(
            check_fieldless_eq_refinement_claimed(&example_eq(), Some(&swapped)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// FAIL-CLOSED probe (then): replacing the complete select with the
    /// unconditional `self` tag drops the selected-tag arm and is not
    /// definitionally equal while the guard remains opaque.
    #[test]
    fn then_fail_closed_unconditional_self_claim() {
        let wrong = disc_of(0, 0);
        assert!(matches!(
            check_fieldless_then_refinement_claimed(&example_then(), Some(&wrong)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// FAIL-CLOSED probe (then): preserve both arms but claim selection on a
    /// different literal tag. The two opaque `Int.beq` guards are not def-eq.
    #[test]
    fn then_fail_closed_wrong_selected_tag_claim() {
        let wrong_shape = SemFieldlessEnumThen { selected_tag: 1, ..example_then() };
        let wrong = then_select(&wrong_shape, 0);
        assert!(matches!(
            check_fieldless_then_refinement_claimed(&example_then(), Some(&wrong)),
            RefinementVerdict::KernelRejected(_)
        ));
    }

    /// REAL-CORPUS METADATA GATE. The migrated cast rows carry explicit,
    /// all-nullary `Ty::Adt::variants` and therefore certify through the
    /// fieldless TrustIR lane. Historical real-partial rows still omit that
    /// metadata (serde decodes the omission as `variants: []`) and must be
    /// declined directly by both fieldless recognizers.
    #[test]
    fn fieldless_corpus_requires_explicit_variant_metadata() {
        use std::collections::BTreeMap;
        use std::path::Path;
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let cast = root.join("fixtures/census-rung2-2026-07-07/cast");
        let rp = root.join("fixtures/census-m6-cleankernel-2026-07-08/real-partial");
        // Trust (2026-07-29 ladder re-freeze): the `cast` rows are re-keyed to
        // the crate-root-qualified `def_path` the current producer emits
        // (`<Error as core::clone::Clone>::clone` →
        // `<lib::Error as core::clone::Clone>::clone`, filename convention
        // `def_path.replace("::","__") + ".json"` following it). The
        // `real-partial` rows are a DIFFERENT corpus that was not re-frozen and
        // keep their spelling. Both arrays open with `unwrap_or_else(panic!)`,
        // never a fallible skip — a rename must FAIL here, not go quiet.
        let accepted = [
            (cast.join("<lib__Error as core__clone__Clone>__clone.json"), true),
            (cast.join("<lib__Error as core__cmp__PartialEq>__eq.json"), false),
        ];
        let declined = [
            rp.join("<cert__metadata__TrustLevel as std__clone__Clone>__clone.json"),
            rp.join("<cert__bundle__BundleInspectIssue as std__clone__Clone>__clone.json"),
            rp.join("<cert__bundle__BundleInspectIssue as std__cmp__PartialEq>__eq.json"),
        ];
        let empty: BTreeMap<String, crate::mirsem::CalleeFact> = BTreeMap::new();
        for (path, is_clone) in &accepted {
            let bytes = std::fs::read(path)
                .unwrap_or_else(|e| panic!("read required fixture {}: {e}", path.display()));
            let func: trust_types::VerifiableFunction = serde_json::from_slice(&bytes)
                .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
            assert_eq!(
                crate::mirsem::sem_fieldless_enum_clone_shape_of(&func).is_some(),
                *is_clone,
                "{} must be recognized by exactly its fieldless operation",
                path.display(),
            );
            assert_eq!(
                crate::mirsem::sem_fieldless_enum_eq_shape_of(&func).is_some(),
                !*is_clone,
                "{} must be recognized by exactly its fieldless operation",
                path.display(),
            );
            let diag = crate::prove::diagnose_fully_faithful_gate(&func, &empty);
            // Error::eq also inhabits the independently checked typed
            // straight-line Bool-equality MirSem lane. That overlap is expected;
            // the metadata gate here requires the fieldless TrustIR path, not
            // exclusivity from every other sound path.
            let via_mirsem = !*is_clone;
            assert_eq!(
                (
                    diag.via_ir_shape,
                    diag.via_ir_safety,
                    diag.via_ir,
                    diag.via_mirsem_shape,
                    diag.via_mirsem,
                    diag.fully_faithful,
                ),
                (true, true, true, via_mirsem, via_mirsem, true),
                "{} must certify through fieldless TrustIR (with only sound lane overlap), got {diag:?}",
                path.display(),
            );
        }

        for path in &declined {
            let bytes = std::fs::read(path)
                .unwrap_or_else(|e| panic!("read required fixture {}: {e}", path.display()));
            let func: trust_types::VerifiableFunction = serde_json::from_slice(&bytes)
                .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
            assert!(
                crate::mirsem::sem_fieldless_enum_clone_shape_of(&func).is_none(),
                "{} lacks explicit variants and must decline the clone recognizer",
                path.display(),
            );
            assert!(
                crate::mirsem::sem_fieldless_enum_eq_shape_of(&func).is_none(),
                "{} lacks explicit variants and must decline the eq recognizer",
                path.display(),
            );
            let diag = crate::prove::diagnose_fully_faithful_gate(&func, &empty);
            assert!(
                !diag.fully_faithful,
                "{} lacks explicit variant metadata and must fail closed, got {diag:?}",
                path.display(),
            );
        }
    }

    /// NO-OVER-ACCEPTANCE guard over mixed current and historical corpora. The
    /// only accepted rows must be the two migrated `Error` operations with
    /// explicit variant metadata; every `variants: []` row must still decline.
    #[test]
    fn mixed_corpora_have_exact_fieldless_recognizer_allowlist() {
        use std::collections::BTreeSet;
        use std::path::Path;
        let root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let dirs = [
            root.join("fixtures/census-rung2-2026-07-07/cast"),
            root.join("fixtures/census-m6-cleankernel-2026-07-08/real-partial"),
            root.join("fixtures/census-m6-cleankernel-2026-07-08/extract-foldmemo-dump"),
        ];
        let mut got_clone: BTreeSet<String> = BTreeSet::new();
        let mut got_eq: BTreeSet<String> = BTreeSet::new();
        let mut parsed = 0usize;
        for dir in &dirs {
            let entries = std::fs::read_dir(dir)
                .unwrap_or_else(|e| panic!("read required corpus {}: {e}", dir.display()));
            for e in entries {
                let e = e.unwrap_or_else(|e| panic!("read corpus entry: {e}"));
                let p = e.path();
                if p.extension().and_then(|s| s.to_str()) != Some("json") {
                    continue;
                }
                let bytes = std::fs::read(&p)
                    .unwrap_or_else(|e| panic!("read required fixture {}: {e}", p.display()));
                let func = serde_json::from_slice::<trust_types::VerifiableFunction>(&bytes)
                    .unwrap_or_else(|e| panic!("parse {}: {e}", p.display()));
                parsed += 1;
                if crate::mirsem::sem_fieldless_enum_clone_shape_of(&func).is_some() {
                    assert!(
                        got_clone.insert(func.def_path.clone()),
                        "duplicate fieldless clone acceptance at {}",
                        p.display(),
                    );
                }
                if crate::mirsem::sem_fieldless_enum_eq_shape_of(&func).is_some() {
                    assert!(
                        got_eq.insert(func.def_path.clone()),
                        "duplicate fieldless eq acceptance at {}",
                        p.display(),
                    );
                }
            }
        }
        assert!(parsed > 0, "required legacy corpora unexpectedly contained no JSON rows");
        // Trust (2026-07-29 ladder re-freeze): re-keyed to the crate-root-qualified
        // `def_path` spelling. The ALLOWLIST IS UNCHANGED IN CONTENT — still
        // exactly the two migrated `cast` `Error` operations, still nothing from
        // the two historical `variants: []` corpora. Only the spelling moved.
        assert_eq!(
            got_clone,
            BTreeSet::from(["<lib::Error as core::clone::Clone>::clone".to_owned()]),
            "fieldless clone recognizer accepted an unexpected corpus row",
        );
        assert_eq!(
            got_eq,
            BTreeSet::from(["<lib::Error as core::cmp::PartialEq>::eq".to_owned()]),
            "fieldless eq recognizer accepted an unexpected corpus row",
        );
    }
}
