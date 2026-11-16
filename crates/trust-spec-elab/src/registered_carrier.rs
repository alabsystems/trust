// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact, environment-validated ADT types for clause transport.
//!
//! This is kernel-carrier evidence, not Rust representation evidence, a proof
//! grade, or permission to upgrade a reflected function. The initial fragment
//! is a monomorphic singleton family with no indices, whose parameters are
//! `Type`-valued and whose result is `Type`. Consumers must call `validate_in`
//! against their current environment before using an owned handle.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{
    ConstantKind, DeclarationVerification, Environment, Expr, ExprKind, Level, Name,
    RecursorArgOrder, Reducibility, TypeChecker,
};

mod binding;

/// Canonical passive readback of one actual declaration and its side tables.
///
/// This neither audits the record nor discovers its dependency closure. The
/// caller must audit the judgment separately; these bytes confer no proof
/// grade or authority. Missing records or encoding bounds fail closed.
pub fn canonical_declaration_binding(env: &Environment, name: &Name) -> Result<Vec<u8>, String> {
    binding::declaration(name, &DeclarationSnapshot::read(env, name)?)
}

/// Audit and canonically bind the complete declaration/metadata closure of
/// ordered roots. Includes unused constructors and canonical recursor rules
/// of encountered families. No proof grade or Rust-body authority is minted.
///
/// Root order and duplicates are retained; dependency records are uniquely
/// keyed and structurally ordered. The same byte/list bounds as carrier
/// bindings apply. No deserialization shortcut is provided.
pub fn canonical_environment_binding(env: &Environment, roots: &[Name]) -> Result<Vec<u8>, String> {
    if roots.len() > binding::MAX_ENTRIES {
        return Err("canonical binding root list exceeds 4096 entries".into());
    }
    let dependencies = audit_dependencies(env, roots.iter().cloned().collect())?;
    binding::environment(roots, &dependencies)
}

/// Expected constructor data; the type includes the full parameter telescope.
/// Constructing this record grants no authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorSchema {
    pub name: Name,
    pub type_: Expr,
}

/// Expected family data, with constructors in declaration order.
/// This is an input to validation, not a claim of Rust/source correspondence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdtSchema {
    pub name: Name,
    pub type_: Expr,
    pub num_params: u32,
    pub constructors: Vec<ConstructorSchema>,
}

/// An exact instantiated type validated in a kernel environment.
///
/// Fields and construction are private. No deserializer, status token or
/// nominal-name bypass exists. `ty()` preserves the checked expression but is
/// not evidence that another environment still contains its declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegisteredAdt {
    schema: AdtSchema,
    arguments: Vec<Expr>,
    type_: Expr,
    dependencies: BTreeMap<Name, DeclarationSnapshot>,
}

impl RegisteredAdt {
    /// Validate actual ordered metadata, complete declarations, and exact args.
    pub fn validate(
        env: &Environment,
        expected: &AdtSchema,
        arguments: &[Expr],
    ) -> Result<Self, String> {
        let roots = validate_schema(env, expected)?;
        if arguments.len() != expected.num_params as usize {
            return Err("registered ADT requires exactly its declared type arguments".into());
        }
        let mut tc = TypeChecker::new(env);
        tc.set_level_params(vec![]);
        tc.set_allow_unsafe(false);
        tc.set_allow_partial(false);
        let mut pending = BTreeSet::from_iter(roots);
        for (index, argument) in arguments.iter().enumerate() {
            closed(argument).map_err(|e| format!("ADT argument {index}: {e}"))?;
            tc.check_type(argument, &Expr::type_())
                .map_err(|e| format!("ADT argument {index} must inhabit Type: {e:?}"))?;
            pending.extend(audit_expr(env, argument, &Expr::type_())?);
        }
        let type_ = Expr::apps(Expr::const_(expected.name.clone(), vec![]), arguments.to_vec());
        tc.check_type(&type_, &Expr::type_())
            .map_err(|e| format!("instantiated ADT is not a closed Type: {e:?}"))?;
        let dependencies = audit_dependencies(env, pending)?;
        Ok(Self { schema: expected.clone(), arguments: arguments.to_vec(), type_, dependencies })
    }

    /// Revalidate current records and reject stale semantic/provenance snapshots.
    /// Unrelated environment extensions do not invalidate a handle.
    pub fn validate_in(&self, env: &Environment) -> Result<(), String> {
        let current = Self::validate(env, &self.schema, &self.arguments)?;
        if current != *self {
            return Err(
                "registered ADT dependencies changed; validate a fresh carrier in this environment"
                    .into(),
            );
        }
        Ok(())
    }

    /// Compare exact structural type syntax after current-environment validation.
    /// Deliberately not definitional equality: aliases and arguments stay exact.
    pub fn matches_type(&self, env: &Environment, actual: &Expr) -> Result<bool, String> {
        self.validate_in(env)?;
        Ok(self.type_ == *actual)
    }

    /// Versioned passive bytes of the exact type, schema and complete checked
    /// dependency snapshot. Revalidates the current environment first.
    ///
    /// Structural Names, argument syntax, constructor order, provenance and
    /// recursor rules are retained. Output is limited to 8 MiB and each list
    /// to 4096 entries; the existing bounded Clean term codec encodes Expr.
    /// There is deliberately no inverse that deserializes a trusted handle.
    pub fn canonical_binding(&self, env: &Environment) -> Result<Vec<u8>, String> {
        self.validate_in(env)?;
        binding::carrier(self)
    }

    pub fn name(&self) -> &Name {
        &self.schema.name
    }
    pub fn arguments(&self) -> &[Expr] {
        &self.arguments
    }
    pub fn ty(&self) -> Expr {
        self.type_.clone()
    }

    /// Trust (E9-ODT-FACE-SELF-CALL-1): this carrier's single constructor and
    /// its fields in constructor order, each with its REGISTERED name (the
    /// kernel's structure-field side table) and its declared type, read only
    /// from this handle's own validated snapshot.
    ///
    /// `None` unless the family is monomorphic with exactly one constructor, a
    /// registered field table, and a non-dependent telescope of exactly those
    /// fields ending in the family itself. Grants nothing: it names the slots a
    /// caller must fill, and the kernel still types whatever is built from it.
    pub(crate) fn structure_fields(&self) -> Option<(Name, Vec<(Name, Expr)>)> {
        if self.schema.num_params != 0 || !self.arguments.is_empty() {
            return None;
        }
        let [ctor] = self.schema.constructors.as_slice() else {
            return None;
        };
        let names = self.dependencies.get(&self.schema.name)?.fields.as_ref()?;
        let mut tail = &ctor.type_;
        let mut fields = Vec::with_capacity(names.len());
        for name in names {
            let ExprKind::Pi(_, domain, body) = tail.kind() else {
                return None;
            };
            if body.has_loose_bvars() {
                return None;
            }
            fields.push((name.clone(), domain.as_ref().clone()));
            tail = body;
        }
        (*tail == self.type_).then(|| (ctor.name.clone(), fields))
    }
}

fn closed(expr: &Expr) -> Result<(), String> {
    if expr.has_loose_bvars()
        || expr.has_fvar_quick()
        || expr.has_expr_mvar_quick()
        || expr.has_level_param_quick()
        || expr.has_level_mvar_quick()
    {
        return Err(
            "only closed monomorphic expressions are supported; instantiate all variables first"
                .into(),
        );
    }
    Ok(())
}

fn validate_schema(env: &Environment, schema: &AdtSchema) -> Result<Vec<Name>, String> {
    let ind = env
        .get_inductive(&schema.name)
        .ok_or_else(|| format!("missing registered inductive {:?}", schema.name))?;
    if !ind.level_params.is_empty()
        || ind.num_indices != 0
        || ind.all_names.len() != 1
        || ind.all_names[0] != schema.name
        || ind.is_nested
    {
        return Err("registered carrier supports monomorphic singleton non-nested families without indices; use an explicit representation bridge for this family".into());
    }
    if ind.name != schema.name || ind.type_ != schema.type_ || ind.num_params != schema.num_params {
        return Err("registered family name/type/parameter schema mismatch".into());
    }
    closed(&schema.type_)?;
    let mut tail = &schema.type_;
    for _ in 0..schema.num_params {
        let ExprKind::Pi(_, domain, body) = tail.kind() else {
            return Err("registered family lacks its declared Type parameter telescope".into());
        };
        if domain.as_ref() != &Expr::type_() {
            return Err("registered family parameters must be exactly Type; dependent/value parameters are not yet supported".into());
        }
        tail = body;
    }
    if *tail != Expr::type_() {
        return Err("registered family must return exactly Type after its parameters".into());
    }
    check_constant(env, &schema.name, &schema.type_)?;
    if schema.constructors.len() != ind.constructor_names.len()
        || schema
            .constructors
            .iter()
            .zip(&ind.constructor_names)
            .any(|(c, actual)| c.name != *actual)
        || schema.constructors.iter().map(|c| &c.name).collect::<BTreeSet<_>>().len()
            != schema.constructors.len()
    {
        return Err("registered constructor list differs in identity, order or multiplicity".into());
    }
    for (index, expected) in schema.constructors.iter().enumerate() {
        let ctor = env
            .get_constructor(&expected.name)
            .ok_or_else(|| format!("missing registered constructor {:?}", expected.name))?;
        let mut arity = 0u32;
        let mut tail = &expected.type_;
        while let ExprKind::Pi(_, _, body) = tail.kind() {
            arity = arity.checked_add(1).ok_or("constructor arity exceeds u32")?;
            tail = body;
        }
        let fields = arity
            .checked_sub(schema.num_params)
            .ok_or("constructor telescope is shorter than its parameter prefix")?;
        if ctor.name != expected.name
            || ctor.inductive_name != schema.name
            || !ctor.level_params.is_empty()
            || ctor.type_ != expected.type_
            || ctor.num_params != schema.num_params
            || ctor.num_fields != fields
            || usize::try_from(ctor.constructor_idx).ok() != Some(index)
        {
            return Err(format!(
                "constructor {index} disagrees with its ordered registered schema"
            ));
        }
        closed(&expected.type_)?;
        check_constant(env, &expected.name, &expected.type_)?;
    }
    let rec = Name::append(&schema.name, "rec");
    let record = env.get_recursor(&rec).ok_or("registered carrier has no derived recursor")?;
    if record.inductive_name != schema.name {
        return Err("registered carrier recursor has a different family".into());
    }
    env.authenticate_recursor_readonly(&rec)
        .map_err(|e| format!("registered carrier recursor refused: {e}"))?;
    let mut roots = Vec::with_capacity(schema.constructors.len() + 2);
    roots.extend(schema.constructors.iter().map(|c| c.name.clone()));
    roots.push(schema.name.clone());
    roots.push(rec);
    Ok(roots)
}

fn check_constant(env: &Environment, name: &Name, type_: &Expr) -> Result<(), String> {
    let info = env.get_const(name).ok_or_else(|| format!("missing constant record {name:?}"))?;
    if info.name != *name
        || !info.level_params.is_empty()
        || info.type_ != *type_
        || info.value.is_some()
        || info.kind != ConstantKind::Definition
        || info.is_reducible
        || info.reducibility != Reducibility::Regular(0)
        || env.declaration_verification(name) != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(format!("registered constant record/provenance mismatch for {name:?}"));
    }
    Ok(())
}

fn audit_expr(env: &Environment, subject: &Expr, type_: &Expr) -> Result<Vec<Name>, String> {
    let level = TypeChecker::new(env)
        .infer_sort(type_)
        .map_err(|e| format!("carrier audit type is invalid: {e:?}"))?;
    let goal = Expr::apps(
        Expr::const_(Name::interned("Eq"), vec![level.clone()]),
        [type_.clone(), subject.clone(), subject.clone()],
    );
    let proof = Expr::apps(
        Expr::const_(Name::interned("Eq.refl"), vec![level]),
        [type_.clone(), subject.clone()],
    );
    let audit = env.audit_certification(&goal, &proof);
    if !audit.is_certified() {
        return Err(format!("carrier declaration/provenance audit refused: {:?}", audit.issues));
    }
    Ok(audit.dependencies)
}

fn audit_dependencies(
    env: &Environment,
    mut pending: BTreeSet<Name>,
) -> Result<BTreeMap<Name, DeclarationSnapshot>, String> {
    let mut result = BTreeMap::new();
    while let Some(name) = pending.pop_first() {
        if result.contains_key(&name) {
            continue;
        }
        let info =
            env.get_const(&name).ok_or_else(|| format!("missing carrier dependency {name:?}"))?;
        let levels = vec![Level::zero(); info.level_params.len()];
        let type_ = info.type_.instantiate_level_params_direct(&info.level_params, &levels);
        pending.extend(audit_expr(env, &Expr::const_(name.clone(), levels), &type_)?);
        if let Some(ind) = env.get_inductive(&name) {
            pending.extend(ind.all_names.iter().chain(&ind.constructor_names).cloned());
            // Rules may mention declarations absent from the former's type
            // and unused by this particular judgment. Bind them as well.
            pending.insert(Name::append(&ind.name, "rec"));
        }
        if let Some(rec) = env.get_recursor(&name) {
            env.authenticate_recursor_readonly(&name)
                .map_err(|e| format!("dependency recursor refused: {e}"))?;
            pending.insert(rec.inductive_name.clone());
            pending.extend(rec.rules.iter().map(|r| r.constructor_name.clone()));
            for rule in &rec.rules {
                // Use the kernel's certification traversal, including Proj
                // structure names, rather than a Const-only expression walk.
                let levels = vec![Level::zero(); rec.level_params.len()];
                let rhs = rule.rhs.instantiate_level_params_direct(&rec.level_params, &levels);
                let rhs_type = TypeChecker::new(env)
                    .infer_type_full(&rhs)
                    .map_err(|e| format!("recursor rule cannot be audited: {e:?}"))?;
                pending.extend(audit_expr(env, &rhs, &rhs_type)?);
            }
        }
        result.insert(name.clone(), DeclarationSnapshot::read(env, &name)?);
    }
    Ok(result)
}

// Structural snapshots, not Display strings, cached hashes, or a public digest
// supplied by a caller. Side-table rule payloads are included because they
// affect computation even when ConstantInfo has no value.
type InductiveSnapshot = (Name, Vec<Name>, Expr, u32, u32, Vec<Name>, Vec<Name>, [bool; 4]);
type ConstructorSnapshot = (Name, Name, Vec<Name>, Expr, u32, u32, u32);
type RuleSnapshot = (Name, u32, Vec<bool>, Expr);
type RecursorSnapshot =
    (Name, RecursorArgOrder, Vec<Name>, Expr, Name, u32, u32, u32, u32, Vec<RuleSnapshot>, bool);

#[derive(Clone, Debug, PartialEq, Eq)]
struct DeclarationSnapshot {
    name: Name,
    levels: Vec<Name>,
    type_: Expr,
    value: Option<Expr>,
    reducible: bool,
    reducibility: Reducibility,
    kind: ConstantKind,
    verification: Option<DeclarationVerification>,
    unsafe_: bool,
    partial: bool,
    fields: Option<Vec<Name>>,
    inductive: Option<InductiveSnapshot>,
    constructor: Option<ConstructorSnapshot>,
    recursor: Option<RecursorSnapshot>,
}

impl DeclarationSnapshot {
    fn read(env: &Environment, name: &Name) -> Result<Self, String> {
        let c = env.get_const(name).ok_or_else(|| format!("missing dependency {name:?}"))?;
        Ok(Self {
            name: c.name.clone(),
            levels: c.level_params.clone(),
            type_: c.type_.clone(),
            value: c.value.clone(),
            reducible: c.is_reducible,
            reducibility: c.reducibility,
            kind: c.kind,
            verification: env.declaration_verification(name),
            unsafe_: env.is_unsafe(name),
            partial: env.is_partial(name),
            fields: env.get_structure_field_names(name).map(<[Name]>::to_vec),
            inductive: env.get_inductive(name).map(|i| {
                (
                    i.name.clone(),
                    i.level_params.clone(),
                    i.type_.clone(),
                    i.num_params,
                    i.num_indices,
                    i.all_names.clone(),
                    i.constructor_names.clone(),
                    [i.is_recursive, i.is_reflexive, i.is_large_elim, i.is_nested],
                )
            }),
            constructor: env.get_constructor(name).map(|c| {
                (
                    c.name.clone(),
                    c.inductive_name.clone(),
                    c.level_params.clone(),
                    c.type_.clone(),
                    c.num_params,
                    c.num_fields,
                    c.constructor_idx,
                )
            }),
            recursor: env.get_recursor(name).map(|r| {
                (
                    r.name.clone(),
                    r.arg_order,
                    r.level_params.clone(),
                    r.type_.clone(),
                    r.inductive_name.clone(),
                    r.num_params,
                    r.num_indices,
                    r.num_motives,
                    r.num_minors,
                    r.rules
                        .iter()
                        .map(|x| {
                            (
                                x.constructor_name.clone(),
                                x.num_fields,
                                x.recursive_fields.clone(),
                                x.rhs.clone(),
                            )
                        })
                        .collect(),
                    r.is_k,
                )
            }),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use clean_kernel::{BinderInfo, Constructor, Declaration, InductiveDecl, InductiveType};

    use super::*;

    mod binding_tests;

    fn base() -> Environment {
        static ENV: OnceLock<Environment> = OnceLock::new();
        ENV.get_or_init(Environment::with_prelude).clone()
    }

    fn arrow(a: Expr, b: Expr) -> Expr {
        Expr::pi(BinderInfo::Default, a, b)
    }

    fn install(env: &mut Environment, schema: &AdtSchema) {
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: schema.num_params,
            types: vec![InductiveType {
                name: schema.name.clone(),
                type_: schema.type_.clone(),
                constructors: schema
                    .constructors
                    .iter()
                    .map(|c| Constructor { name: c.name.clone(), type_: c.type_.clone() })
                    .collect(),
            }],
        })
        .expect("fixture must pass actual inductive admission");
    }

    fn enumeration(name: Name, payload: Expr) -> AdtSchema {
        let ty = Expr::const_(name.clone(), vec![]);
        AdtSchema {
            name: name.clone(),
            type_: Expr::type_(),
            num_params: 0,
            constructors: vec![
                ConstructorSchema { name: Name::append(&name, "first"), type_: ty.clone() },
                ConstructorSchema {
                    name: Name::append(&name, "second"),
                    type_: arrow(payload, ty),
                },
            ],
        }
    }

    fn pair() -> AdtSchema {
        let name = Name::from_string("TransportPair");
        let result = Expr::apps(Expr::const_(name.clone(), vec![]), [Expr::bvar(3), Expr::bvar(2)]);
        AdtSchema {
            name: name.clone(),
            type_: arrow(Expr::type_(), arrow(Expr::type_(), Expr::type_())),
            num_params: 2,
            constructors: vec![ConstructorSchema {
                name: Name::append(&name, "mk"),
                type_: arrow(
                    Expr::type_(),
                    arrow(Expr::type_(), arrow(Expr::bvar(1), arrow(Expr::bvar(1), result))),
                ),
            }],
        }
    }

    #[test]
    fn registered_enum_roundtrip_and_unrelated_extension() {
        let mut env = base();
        let schema = enumeration(Name::from_string("TransportEnum"), Expr::const_str("Bool"));
        install(&mut env, &schema);
        let handle = RegisteredAdt::validate(&env, &schema, &[]).unwrap();
        assert_eq!(handle.name(), &schema.name);
        assert!(handle.arguments().is_empty());
        assert_eq!(handle.ty(), Expr::const_(schema.name.clone(), vec![]));
        assert!(handle.matches_type(&env, &handle.ty()).unwrap());
        assert!(!handle.matches_type(&env, &Expr::const_str("Bool")).unwrap());
        env.add_decl(Declaration::Definition {
            name: Name::from_string("unrelated"),
            level_params: vec![],
            type_: Expr::const_str("Bool"),
            value: Expr::const_str("Bool.true"),
            is_reducible: true,
        })
        .unwrap();
        handle.validate_in(&env).unwrap();
    }

    #[test]
    fn exact_type_arguments_are_checked_and_not_normalized() {
        let mut env = base();
        let schema = pair();
        install(&mut env, &schema);
        let args = [Expr::const_str("Bool"), Expr::const_str("Nat")];
        let handle = RegisteredAdt::validate(&env, &schema, &args).unwrap();
        assert_eq!(handle.arguments(), &args);
        let swapped = Expr::apps(
            Expr::const_(schema.name.clone(), vec![]),
            [args[1].clone(), args[0].clone()],
        );
        assert!(!handle.matches_type(&env, &swapped).unwrap());
        for bad in [
            vec![],
            vec![args[0].clone()],
            vec![args[0].clone(); 3],
            vec![Expr::bvar(0), args[1].clone()],
            vec![Expr::const_str("Bool.true"), args[1].clone()],
            vec![Expr::type_(), args[1].clone()],
            vec![Expr::sort(Level::param(Name::from_string("u"))), args[1].clone()],
        ] {
            assert!(RegisteredAdt::validate(&env, &schema, &bad).is_err());
        }
        env.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAlias"),
            level_params: vec![],
            type_: Expr::type_(),
            value: args[0].clone(),
            is_reducible: true,
        })
        .unwrap();
        let alias_args = [Expr::const_str("BoolAlias"), args[1].clone()];
        let alias_handle = RegisteredAdt::validate(&env, &schema, &alias_args).unwrap();
        assert_eq!(alias_handle.arguments(), &alias_args);
        assert!(!alias_handle.matches_type(&env, &handle.ty()).unwrap());
    }

    #[test]
    fn schemas_refuse_wrong_identity_order_field_type_and_missing_records() {
        let mut env = base();
        let schema = enumeration(Name::from_string("TransportEnum"), Expr::const_str("Bool"));
        assert!(RegisteredAdt::validate(&env, &schema, &[]).is_err());
        install(&mut env, &schema);
        let mut wrong = schema.clone();
        wrong.constructors.reverse();
        assert!(RegisteredAdt::validate(&env, &wrong, &[]).is_err());
        wrong = schema.clone();
        wrong.constructors[1].type_ =
            arrow(Expr::const_str("Nat"), Expr::const_(schema.name.clone(), vec![]));
        assert!(RegisteredAdt::validate(&env, &wrong, &[]).is_err());
        wrong = schema.clone();
        wrong.name = Name::from_string("Other");
        assert!(RegisteredAdt::validate(&env, &wrong, &[]).is_err());
        wrong = schema.clone();
        wrong.constructors[1].name = wrong.constructors[0].name.clone();
        assert!(RegisteredAdt::validate(&env, &wrong, &[]).is_err());
    }

    #[test]
    fn equal_display_names_do_not_alias() {
        let a = Name::from_string("Twin.leaf");
        let b = Name::anon().str("Twin.leaf");
        assert_ne!(a, b);
        assert_eq!(a.to_string(), b.to_string());
        let mut env = base();
        let first = enumeration(a, Expr::const_str("Bool"));
        let second = enumeration(b, Expr::const_str("Bool"));
        install(&mut env, &first);
        install(&mut env, &second);
        let x = RegisteredAdt::validate(&env, &first, &[]).unwrap();
        let y = RegisteredAdt::validate(&env, &second, &[]).unwrap();
        assert_ne!(x, y);
        assert!(!x.matches_type(&env, &y.ty()).unwrap());
    }

    fn alias_environment(value: &str, structural: bool) -> (Environment, AdtSchema) {
        let mut env = base();
        let decl = Declaration::Definition {
            name: Name::from_string("PayloadAlias"),
            level_params: vec![],
            type_: Expr::type_(),
            value: Expr::const_str(value),
            is_reducible: true,
        };
        if structural {
            env.add_decl_structural(decl).unwrap();
        } else {
            env.add_decl(decl).unwrap();
        }
        let schema = enumeration(Name::from_string("AliasEnum"), Expr::const_str("PayloadAlias"));
        install(&mut env, &schema);
        (env, schema)
    }

    #[test]
    fn stale_dependencies_and_weaker_provenance_are_refused() {
        let (env, schema) = alias_environment("Bool", false);
        let handle = RegisteredAdt::validate(&env, &schema, &[]).unwrap();
        let (changed, same_schema) = alias_environment("Nat", false);
        assert_eq!(schema, same_schema);
        assert!(RegisteredAdt::validate(&changed, &schema, &[]).is_ok());
        assert!(handle.validate_in(&changed).is_err());
        assert!(handle.matches_type(&changed, &handle.ty()).is_err());
        let (structural, _) = alias_environment("Bool", true);
        assert!(RegisteredAdt::validate(&structural, &schema, &[]).is_err());
        let mut unsafe_env = env.clone();
        unsafe_env.mark_unsafe(Name::from_string("PayloadAlias"));
        assert!(handle.validate_in(&unsafe_env).is_err());
        let mut partial_env = env.clone();
        partial_env.mark_partial(Name::from_string("PayloadAlias"));
        assert!(handle.validate_in(&partial_env).is_err());
        assert!(handle.validate_in(&base()).is_err());
    }

    #[test]
    fn domain_axiom_cannot_back_a_registered_carrier() {
        let mut env = base();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("UnprovedPayload"),
            level_params: vec![],
            type_: Expr::type_(),
        })
        .unwrap();
        let schema =
            enumeration(Name::from_string("AxiomaticEnum"), Expr::const_str("UnprovedPayload"));
        install(&mut env, &schema);
        assert!(RegisteredAdt::validate(&env, &schema, &[]).is_err());
    }

    #[test]
    fn indexed_and_universe_polymorphic_families_stay_outside_this_fragment() {
        let env = base();
        for name in ["Eq", "List"] {
            let ind = env.get_inductive(&Name::from_string(name)).unwrap();
            let schema = AdtSchema {
                name: ind.name.clone(),
                type_: ind.type_.clone(),
                num_params: ind.num_params,
                constructors: ind
                    .constructor_names
                    .iter()
                    .map(|n| ConstructorSchema {
                        name: n.clone(),
                        type_: env.get_constructor(n).unwrap().type_.clone(),
                    })
                    .collect(),
            };
            assert!(RegisteredAdt::validate(&env, &schema, &[]).is_err());
        }
    }
}
