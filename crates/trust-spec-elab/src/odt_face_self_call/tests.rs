// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! E9-ODT-FACE-SELF-CALL-1 at the elaborator: a hand-built ODT-shaped face
//! (one constructor, the kernel field table holding `trust_odt::member_name`
//! spellings) and nominal imports over it, so each check is exercised without
//! the compiler's mint. The mint-backed controls are in
//! `trust-certify`'s `clean_island::odt_self_call_tests`.

use clean_kernel::expr::BinderInfo;
use clean_kernel::{
    Constructor, Declaration, Environment, Expr, InductiveDecl, InductiveType, Level, Name,
    TypeChecker,
};

use super::odt_member_rust_name;
use crate::{
    Admission, AdtSchema, Carrier, ConstructorSchema, DeclaredCarriers, Domain, FacetTable,
    FnFacets, MachineSIntWidth, MachineUIntWidth, RegisteredAdt, elaborate_ensures,
};

/// `trust_odt::member_name("degree")`, `("coeff")` and `("off")`, spelled out
/// so this test does not take the dependency edge the module avoids.
const DEGREE: &str = "n646567726565";
const COEFF: &str = "n636f656666";
const OFF: &str = "n6f6666";
const CST: [(&str, &str); 2] = [("c.degree", "u64"), ("c.coeff", "u64")];

fn u64_ty() -> Expr {
    Expr::const_str("UInt64")
}

/// Install a one-constructor structure `name` with `fields`, register its
/// field table under `field_names`, and return its validated carrier.
fn face(env: &mut Environment, name: &str, fields: &[(&str, Expr)]) -> RegisteredAdt {
    let family = Name::from_string(name);
    let result = Expr::const_(family.clone(), vec![]);
    let ctor_ty = fields
        .iter()
        .rev()
        .fold(result, |ty, (_, field)| Expr::pi(BinderInfo::Default, field.clone(), ty));
    let ctor = Name::from_string(&format!("{name}.mk"));
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: family.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor { name: ctor.clone(), type_: ctor_ty.clone() }],
        }],
    })
    .unwrap();
    env.register_structure_fields(
        family.clone(),
        fields.iter().map(|(n, _)| Name::from_string(n)).collect(),
    )
    .unwrap();
    RegisteredAdt::validate(
        env,
        &AdtSchema {
            name: family,
            type_: Expr::type_(),
            num_params: 0,
            constructors: vec![ConstructorSchema { name: ctor, type_: ctor_ty }],
        },
        &[],
    )
    .unwrap()
}

#[derive(Clone)]
enum Param {
    Struct(RegisteredAdt),
    Scalar(Domain),
}

impl Param {
    fn ty(&self) -> Expr {
        match self {
            Param::Struct(adt) => adt.ty(),
            Param::Scalar(d) => d.ty(),
        }
    }
    fn carrier(&self) -> Carrier {
        match self {
            Param::Struct(adt) => Carrier::RegisteredAdt(adt.clone()),
            Param::Scalar(d) => d.carrier(),
        }
    }
}

/// Define `key`'s nominal import, `fun params => proj(<face of params[param]>,
/// field, params[param])` (or the scalar parameter itself when `field` is
/// `None`), and admit it the way TG11 does: `Admission::reflected` with the
/// declared carriers and NO parameter names.
fn admit(
    env: &mut Environment,
    facets: &mut FacetTable,
    key: &str,
    params: &[Param],
    param: usize,
    field: Option<u32>,
    ret: Domain,
) {
    let var = Expr::bvar(u32::try_from(params.len() - param - 1).unwrap());
    let body = match (&params[param], field) {
        (Param::Struct(adt), Some(index)) => Expr::proj(adt.name().clone(), index, var),
        (Param::Scalar(_), None) => var,
        _ => panic!("fixture: a field of a struct parameter or a scalar parameter itself"),
    };
    let value = params.iter().rev().fold(body, |v, p| Expr::lam(BinderInfo::Default, p.ty(), v));
    let type_ = params.iter().rev().fold(ret.ty(), |t, p| Expr::arrow(p.ty(), t));
    let kernel_const = format!("trust_import_{}", key.replace("::", "__"));
    env.add_decl(Declaration::Definition {
        name: Name::from_string(&kernel_const),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap();
    let carriers = DeclaredCarriers {
        params: params.iter().map(Param::carrier).collect(),
        ret: ret.carrier(),
    };
    let admission = Admission::reflected(&kernel_const, params.len())
        .with_declared_signature(Some(ret), Some(carriers));
    assert!(admission.param_names.is_none(), "TG11's admission records no parameter names");
    facets.insert(key, FnFacets::from_structural_certificates(true, true, true, true, "fixture"));
    facets.admit(key, admission);
}

struct Fixture {
    env: Environment,
    facets: FacetTable,
}

/// `degree_bound(c: Cst) -> u64 { c.degree }`, `coeff_of(c) { c.coeff }`,
/// `second(a: Cst, b: Cst) { b.degree }`, `mixed(n: u64, c: Cst) { c.coeff }`
/// and `offset(s: Off) -> i64 { s.off }`.
fn fixture() -> Fixture {
    let mut env = Environment::with_prelude();
    let mut facets = FacetTable::new();
    let cst = face(&mut env, "TrustOdt.kCst", &[(DEGREE, u64_ty()), (COEFF, u64_ty())]);
    let signed = Domain::Signed(MachineSIntWidth::I64);
    let off = face(&mut env, "TrustOdt.kOff", &[(OFF, signed.ty())]);
    let u64d = Domain::Machine(MachineUIntWidth::U64);
    let s = Param::Struct(cst);
    let one = std::slice::from_ref(&s);
    admit(&mut env, &mut facets, "test::degree_bound", one, 0, Some(0), u64d.clone());
    admit(&mut env, &mut facets, "test::coeff_of", one, 0, Some(1), u64d.clone());
    admit(&mut env, &mut facets, "test::second", &[s.clone(), s.clone()], 1, Some(0), u64d.clone());
    admit(
        &mut env,
        &mut facets,
        "test::mixed",
        &[Param::Scalar(u64d.clone()), s],
        1,
        Some(1),
        u64d,
    );
    admit(&mut env, &mut facets, "test::offset", &[Param::Struct(off)], 0, Some(0), signed);
    Fixture { env, facets }
}

/// `fun x0 … x{n-1} => @Eq.refl UInt64 x{pick}`.
fn refl_proof(binders: usize, pick: usize) -> Expr {
    let body = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [u64_ty(), Expr::bvar(u32::try_from(binders - pick - 1).unwrap())],
    );
    (0..binders).fold(body, |v, _| Expr::lam(BinderInfo::Default, u64_ty(), v))
}

fn goal(fx: &Fixture, clause: &str, rows: &[(&str, &str)], self_fn: &str) -> Expr {
    let goal = elaborate_ensures(clause, rows, self_fn, &fx.facets)
        .unwrap_or_else(|e| panic!("`{clause}` must elaborate through the face: {e}"));
    TypeChecker::new(&fx.env)
        .check_type(&goal, &Expr::prop())
        .unwrap_or_else(|e| panic!("the goal must be a Prop: {e:?}\n{goal}"));
    goal
}

fn refusal(fx: &Fixture, clause: &str, rows: &[(&str, &str)], self_fn: &str) -> String {
    elaborate_ensures(clause, rows, self_fn, &fx.facets)
        .expect_err("this flattening must not reach the kernel")
}

#[test]
fn the_self_call_is_rebuilt_through_the_face_constructor() {
    let fx = fixture();
    let g = goal(&fx, "result == c.degree", &CST, "test::degree_bound");
    let text = g.to_string();
    assert!(
        text.contains("trust_import_test__degree_bound") && text.contains("TrustOdt.kCst.mk"),
        "the import is applied to the face constructor: {text}"
    );
    TypeChecker::new(&fx.env).check_type(&refl_proof(2, 0), &g).unwrap();
    // The other field's import is not proved by the same term: the slot a row
    // fills is carried into the goal, not assumed.
    let other = goal(&fx, "result == c.degree", &CST, "test::coeff_of");
    assert!(TypeChecker::new(&fx.env).check_type(&refl_proof(2, 0), &other).is_err());
    let right = goal(&fx, "result == c.coeff", &CST, "test::coeff_of");
    TypeChecker::new(&fx.env).check_type(&refl_proof(2, 1), &right).unwrap();
}

#[test]
fn two_struct_parameters_and_a_scalar_parameter_are_rebuilt_in_order() {
    let fx = fixture();
    let four = [("a.degree", "u64"), ("a.coeff", "u64"), ("b.degree", "u64"), ("b.coeff", "u64")];
    let g = goal(&fx, "result == b.degree", &four, "test::second");
    TypeChecker::new(&fx.env).check_type(&refl_proof(4, 2), &g).unwrap();
    assert!(TypeChecker::new(&fx.env).check_type(&refl_proof(4, 0), &g).is_err());
    let three = [("n", "u64"), ("c.degree", "u64"), ("c.coeff", "u64")];
    let g = goal(&fx, "result == c.coeff", &three, "test::mixed");
    TypeChecker::new(&fx.env).check_type(&refl_proof(3, 2), &g).unwrap();
}

/// THE CHECK THE KERNEL CANNOT MAKE. Both fields are `UInt64`, so an
/// order-only rebuild of these rows types: `f (K.mk c.coeff c.degree)`, which
/// reduces to `c.coeff`, and `fun x y => Eq.refl x` would "prove"
/// `result == c.coeff` about a body that returns `c.degree`.
#[test]
fn a_swapped_flattening_is_refused_by_registered_field_name() {
    let fx = fixture();
    let swapped = [("c.coeff", "u64"), ("c.degree", "u64")];
    let err = refusal(&fx, "result == c.coeff", &swapped, "test::degree_bound");
    assert!(err.contains("does not fill field slot 0"), "{err}");
    assert!(err.contains("registered field is `degree`"), "{err}");
}

#[test]
fn a_missing_extra_or_foreign_row_is_refused() {
    let fx = fixture();
    let err = refusal(&fx, "result <= c.degree", &[("c.degree", "u64")], "test::degree_bound");
    assert!(err.contains("needs 2 field row(s) and 1 remain"), "{err}");
    let extra = [("c.degree", "u64"), ("c.coeff", "u64"), ("x", "u64")];
    let err = refusal(&fx, "result <= x", &extra, "test::degree_bound");
    assert!(err.contains("1 row(s) are left over"), "{err}");
    let two_roots = [("c.degree", "u64"), ("d.coeff", "u64")];
    let err = refusal(&fx, "result <= c.degree", &two_roots, "test::degree_bound");
    assert!(err.contains("does not fill field slot 1"), "{err}");
    let shadowed = [("c", "u64"), ("c.degree", "u64"), ("c.coeff", "u64")];
    let err = refusal(&fx, "result == c.coeff", &shadowed, "test::mixed");
    assert!(err.contains("`c` would fill two parameters"), "{err}");
}

#[test]
fn a_row_at_another_carrier_or_outside_the_odt_scalars_is_refused() {
    let fx = fixture();
    let narrow = [("c.degree", "u32"), ("c.coeff", "u64")];
    let err = refusal(&fx, "result == c.coeff", &narrow, "test::degree_bound");
    assert!(err.contains("is bound at `u32`"), "{err}");
    // `isize64` is `BitVec 64` too, the `i64` slot's kernel type; it is refused
    // because it reads differently, not because the kernel would object. The
    // clause compares the call with itself, so no relation gate sees `s.off`,
    // and the same clause over an `i64` row builds.
    let signed = goal(&fx, "result == result", &[("s.off", "i64")], "test::offset");
    assert!(signed.to_string().contains("TrustOdt.kOff.mk"), "{signed}");
    let err = refusal(&fx, "result == result", &[("s.off", "isize64")], "test::offset");
    assert!(err.contains("is bound at `isize (64-bit target)`"), "{err}");
    let scalar = [("n", "u32"), ("c.degree", "u64"), ("c.coeff", "u64")];
    let err = refusal(&fx, "result == c.coeff", &scalar, "test::mixed");
    assert!(err.contains("parameter 0 is declared `UInt64`"), "{err}");
}

#[test]
fn an_author_written_self_call_is_held_to_the_same_checks() {
    let fx = fixture();
    let err = refusal(
        &fx,
        "test::degree_bound(c.coeff, c.degree) == c.coeff",
        &CST,
        "test::degree_bound",
    );
    assert!(err.contains("does not fill field slot 0"), "{err}");
    let g =
        goal(&fx, "test::degree_bound(c.degree, c.coeff) == c.degree", &CST, "test::degree_bound");
    TypeChecker::new(&fx.env).check_type(&refl_proof(2, 0), &g).unwrap();
}

#[test]
fn a_flattened_call_of_another_function_keeps_the_arity_refusal() {
    let fx = fixture();
    let err =
        refusal(&fx, "test::degree_bound(c.degree, c.coeff) <= c.degree", &CST, "test::coeff_of");
    assert!(err.contains("has arity 1 but is applied to 2 argument(s)"), "{err}");
}

#[test]
fn a_structure_whose_fields_are_not_odt_member_names_is_refused() {
    let mut fx = fixture();
    let plain = face(&mut fx.env, "IslandCst", &[("degree", u64_ty()), ("coeff", u64_ty())]);
    let u64d = Domain::Machine(MachineUIntWidth::U64);
    admit(&mut fx.env, &mut fx.facets, "test::plain", &[Param::Struct(plain)], 0, Some(0), u64d);
    let err = refusal(&fx, "result == c.degree", &CST, "test::plain");
    assert!(err.contains("is registered as `degree`, which is not an ODT member name"), "{err}");
}

#[test]
fn member_names_decode_only_their_exact_encoding() {
    assert_eq!(odt_member_rust_name(&Name::from_string(DEGREE)).as_deref(), Some("degree"));
    assert_eq!(odt_member_rust_name(&Name::from_string("n30")).as_deref(), Some("0"));
    for bad in ["degree", "n64656", "n6465676172G5", "N646567726565", "n6465676172E5", "nff"] {
        assert_eq!(odt_member_rust_name(&Name::from_string(bad)), None, "{bad}");
    }
    let two_components = Name::from_string("n64").str("65");
    assert_eq!(odt_member_rust_name(&two_components), None);
}
