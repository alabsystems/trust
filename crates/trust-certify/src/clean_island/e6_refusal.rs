//! Which E6 admission gate refused a function, and the construct it refused —
//! increment I0 of the E6 admission expansion
//! (`docs/design-notes/2026-09-28-e6-admission-expansion.md` §6).
//!
//! [`super::admit_function_into`] runs its gates in a fixed order and answers
//! only `Option`: the FACET gate (Pure ∧ Total ∧ Deterministic ∧ NoPanic), then
//! the SHAPE gate (`recognize_admissible_body`, then island forwarding, then —
//! since I1′ — the E6-only reader `trust_types::e6_expr::read_e6_body`, whose
//! TREE reader since I3′ says what it stopped at), then
//! the MINT (`trust_spec_elab::admit_*`, re-checked by `add_decl`). Before this
//! module a user whose uncited island clause was refused saw one sentence for
//! every one of those outcomes — "requires the specified function to be
//! E6-admitted; it is not" — and only `TRUST_E6_DEBUG` told them apart.
//!
//! DIAGNOSTICS ONLY. This re-runs the gates' PREDICATES over the same inputs
//! and mints nothing; no verdict, facet or admission reads what it returns. A
//! wrong answer here costs a misleading sentence, never a proof — and the texts
//! are pinned by `e6_refusal_tests` below and the UI fixture
//! `tests/ui/trust/e6_refusal_names_the_gate.rs`.
//!
//! **Keep [`E6_IMPORTABLE_SHAPES`] moving with the fragment.** It is quoted
//! verbatim by `docs/TWO_LANGUAGE_CONVERSION_GUIDE.md` §5b; an increment that
//! widens a reader moves the list, the guide and the pinned texts in one
//! commit.

use trust_types::admissible_body::{AdmissibleBody, recognize_admissible_body};
use trust_types::e6_expr::{E6Expr, E6Term, first_construct_outside_fragment, ty_spelling};

/// The kernel-importable body shapes, as the refusal lists them.
pub const E6_IMPORTABLE_SHAPES: &str = "a parameter or field projection, a constant, a \
     wrapping `+`/`-`/`*` tree, a select, a comparison, `checked_*` arithmetic, a guarded \
     narrowing, a widened equality, a `bool` connective tree (`&&`, `||` and `!`, and \
     `&`/`|`/`^`/`==`/`!=` over `bool`, whose leaves are `bool` parameters and comparisons of \
     parameters, literals and fixed-width arithmetic), a decision tree (`if`/`else`, or a `match` or `matches!` on a \
     `bool`, `u8`..`u64` or `i8`..`i128` parameter with literal arms and `_`, whose arms are \
     parameters, literals and decisions), or one call forwarding the parameters to a Clean \
     island definition";

/// The scalar kernel carriers a parameter or return type can have, as the
/// refusal lists them — the SOURCE types [`super::ty_to_domain`] answers for,
/// read through the extraction the E6 lane consumes. That extraction lowers
/// `usize`/`isize` to the fixed-width integer of the target's pointer width
/// and `char` to `u32` (`trust-mir-extract`'s `convert_ty`, legacy mode), so
/// all three reach the mint with a carrier.
pub const E6_SCALAR_CARRIERS: &str = "`bool`, `u8`..`u64`, `u128`, `i8`..`i128`, `usize` and \
     `isize` (at the target's pointer width), and `char` (as its `u32` scalar value)";

/// What a caller can add to [`explain_e6_admission_refusal`]'s view of the
/// function, beyond the extracted body and its facet record. Every field is
/// optional and [`Default`] is the bare view; each one only sharpens a
/// sentence, and none is read by anything that decides.
#[derive(Debug, Clone, Copy, Default)]
pub struct E6RefusalContext<'a> {
    /// The table `admit_function_into` recorded this session's admissions in.
    /// With it, a mint the kernel refused because the function's
    /// `trust_import_*` name is already held by ANOTHER function's import is
    /// named as that collision instead of as a refused equation.
    pub table: Option<&'a trust_spec_elab::FacetTable>,
    /// Each value parameter's SOURCE type spelling, in declaration order. The
    /// extracted body cannot spell `char`, `usize` or `isize`: the extraction
    /// the E6 lane reads lowers them to `u32` and the pointer-width integers.
    /// Ignored unless it has exactly one entry per extracted parameter.
    pub source_param_types: Option<&'a [String]>,
}

fn shape_name(shape: &AdmissibleBody) -> String {
    let debug = format!("{shape:?}");
    debug
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .next()
        .unwrap_or_default()
        .to_string()
}

fn param_label(
    func: &trust_types::VerifiableFunction,
    cx: E6RefusalContext<'_>,
    local: usize,
) -> String {
    let decl = func.body.locals.iter().find(|l| l.index == local);
    let name = decl.and_then(|l| l.name.clone()).unwrap_or_else(|| format!("#{}", local - 1));
    let source = cx
        .source_param_types
        .filter(|spelled| spelled.len() == func.body.arg_count)
        .and_then(|spelled| spelled.get(local.checked_sub(1)?));
    let ty = match (source, decl) {
        (Some(spelled), _) => spelled.clone(),
        (None, Some(decl)) => ty_spelling(&decl.ty),
        (None, None) => "?".to_owned(),
    };
    format!("`{name}: {ty}`")
}

fn param_labels(func: &trust_types::VerifiableFunction, cx: E6RefusalContext<'_>) -> String {
    (1..=func.body.arg_count)
        .map(|local| param_label(func, cx, local))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The CARRIER precondition every mint shares, the frozen chain's producers
/// and the E6-only reader's alike: each parameter and the return type must
/// have a scalar kernel carrier ([`super::param_domains_of`] /
/// [`super::ty_to_domain`] answer `Some`). `None` when they all do.
fn carrier_refusal(
    func: &trust_types::VerifiableFunction,
    cx: E6RefusalContext<'_>,
) -> Option<String> {
    for local in 1..=func.body.arg_count {
        let decl = func.body.locals.iter().find(|l| l.index == local);
        if decl.and_then(|l| super::ty_to_domain(&l.ty)).is_none() {
            return Some(format!(
                "the parameter {} has no scalar kernel carrier (the carriers are \
                 {E6_SCALAR_CARRIERS})",
                param_label(func, cx, local)
            ));
        }
    }
    if super::ty_to_domain(&func.body.return_ty).is_none() {
        return Some(format!(
            "the return type `{}` has no scalar kernel carrier",
            ty_spelling(&func.body.return_ty)
        ));
    }
    None
}

/// The kernel refused the mint because the function's `trust_import_*` name
/// is already held by ANOTHER function's import (`DuplicateName`): two def
/// paths that mangle to one kernel name. Needs the context's table; `None`
/// without it or when no other admission holds the name.
fn kernel_name_collision(
    func: &trust_types::VerifiableFunction,
    cx: E6RefusalContext<'_>,
) -> Option<String> {
    let table = cx.table?;
    let kernel_const = super::mangle_kernel_const(&func.def_path);
    let holders: Vec<&str> = table
        .admission_paths_for_kernel_const(&kernel_const)
        .into_iter()
        .filter(|path| *path != func.def_path)
        .collect();
    // The holder's DEF PATH is the key that mangles to the name itself; a
    // bare spec spelling recorded for the same mint does not.
    let holder = holders
        .iter()
        .find(|path| super::mangle_kernel_const(path) == kernel_const)
        .or_else(|| holders.first())?;
    Some(format!(
        "its kernel name `{kernel_const}` is already held by the import minted for \
         `{holder}`: the two def paths mangle to that one name (every character that is not \
         alphanumeric becomes `_`), and the kernel refuses a second declaration of a name \
         (`DuplicateName`); renaming either function gives each its own import"
    ))
}

/// Why the MINT would refuse a body `recognize_admissible_body` read as
/// `shape`: the first carrier-level precondition of the `admit_*` producers the
/// function misses, else the kernel's own refusal.
fn mint_refusal_reason(
    func: &trust_types::VerifiableFunction,
    cx: E6RefusalContext<'_>,
    shape: &AdmissibleBody,
) -> String {
    if let Some(reason) = carrier_refusal(func, cx) {
        return reason;
    }
    let domains = super::param_domains_of(func).unwrap_or_default();
    let all_bool =
        !domains.is_empty() && domains.iter().all(|d| *d == trust_spec_elab::Domain::Bool);
    // Trust (E6 expansion I1′): a `ComparisonBool` over `bool` operands is
    // dispatched ON THE OPERATOR by the importer — only `==` reaches the bool
    // equality producer, and an ordering is refused, never given its image.
    if let AdmissibleBody::ComparisonBool { cmp, left, right } = shape {
        use trust_types::admissible_body::{CmpOperand, SelectCmp};
        let over_bool = [left, right].into_iter().any(|o| {
            matches!(o, CmpOperand::Param(i)
                if domains.get(*i) == Some(&trust_spec_elab::Domain::Bool))
        });
        if over_bool && !matches!(cmp, SelectCmp::Eq) {
            return "an ordering over `bool` (`<` or `<=`; `>` and `>=` arrive operand-swapped) \
                    has no E6 image: only `==` and `!=` over `bool` are admitted, and an \
                    equality image for an ordering would be a false import"
                .to_owned();
        }
        if over_bool && !all_bool {
            return mixed_bool_domains(func, cx);
        }
    }
    match shape {
        AdmissibleBody::Select { .. }
        | AdmissibleBody::SelectLiteral { .. }
        | AdmissibleBody::BoolBinary { .. }
            if all_bool =>
        {
            "a comparison over `bool` operands has no E6 image: the comparison mints decide over \
             a machine-integer or signed-integer carrier"
                .to_owned()
        }
        AdmissibleBody::Arithmetic { .. }
        | AdmissibleBody::Composed { .. }
        | AdmissibleBody::ComparisonBool { .. }
        | AdmissibleBody::Select { .. }
        | AdmissibleBody::SelectLiteral { .. }
        | AdmissibleBody::BoolBinary { .. }
            if domains.windows(2).any(|w| w[0] != w[1]) =>
        {
            format!(
                "its parameters span more than one carrier ({}), and the `{}` mint is \
                 single-domain",
                param_labels(func, cx),
                shape_name(shape)
            )
        }
        AdmissibleBody::AggregateFields { .. } => "a struct-valued body is imported per field \
             (`result.<field>`), never as one defining equation"
            .to_owned(),
        _ => kernel_name_collision(func, cx).unwrap_or_else(|| {
            "the kernel refused the defining equation (a literal outside its carrier, or a \
             carrier the mint does not pair with this shape; TRUST_E6_DEBUG=1 prints the \
             recogniser's view)"
                .to_owned()
        }),
    }
}

/// Why the MINT refused a body the E6-ONLY reader read: the same carrier
/// precondition as the frozen chain ([`carrier_refusal`]); then, for the I1′
/// node, the `bool` producer's single domain, and for an I3′ tree, a
/// comparison whose carrier has no image; then a kernel-name collision, else
/// the kernel's own refusal.
fn reader_mint_refusal_reason(
    func: &trust_types::VerifiableFunction,
    cx: E6RefusalContext<'_>,
    read: &E6Expr,
) -> String {
    if let Some(reason) = carrier_refusal(func, cx) {
        return reason;
    }
    match read {
        E6Expr::BoolCmp { .. } => {
            let domains = super::param_domains_of(func).unwrap_or_default();
            if !domains.iter().all(|d| *d == trust_spec_elab::Domain::Bool) {
                return mixed_bool_domains(func, cx);
            }
        }
        E6Expr::Tree(term) => {
            if let Some(reason) = tree_carrier_refusal(term) {
                return reason;
            }
            // Trust (E6 expansion I4′): a decision's value carrier.
            let ret = super::ty_to_domain(&func.body.return_ty);
            if !matches!(
                ret,
                Some(
                    trust_spec_elab::Domain::Bool
                        | trust_spec_elab::Domain::Machine(_)
                        | trust_spec_elab::Domain::Signed(_)
                )
            ) {
                return format!(
                    "a tree returning `{}` has no E6 image (a tree returns `bool`, `u8`..`u64` \
                     or `i8`..`i128`)",
                    ty_spelling(&func.body.return_ty)
                );
            }
        }
    }
    kernel_name_collision(func, cx).unwrap_or_else(|| {
        "the kernel refused the defining equation (TRUST_E6_DEBUG=1 prints the reader's view)"
            .to_owned()
    })
}

/// The first comparison of a tree whose operand carrier has no comparison
/// image (the images decide over `bool`, `u8`..`u64` and `i8`..`i128`).
fn tree_carrier_refusal(term: &E6Term) -> Option<String> {
    use trust_types::e6_expr::E6Carrier;
    match term {
        E6Term::Param(_) | E6Term::Bool(_) | E6Term::Int(_) => None,
        E6Term::Checked { value, overflow, .. } => {
            tree_carrier_refusal(value).or_else(|| tree_carrier_refusal(overflow))
        }
        E6Term::CheckedTag { overflow, .. } => tree_carrier_refusal(overflow),
        E6Term::Not(x) => tree_carrier_refusal(x),
        E6Term::And(x, y) | E6Term::Or(x, y) | E6Term::Xor(x, y) => {
            tree_carrier_refusal(x).or_else(|| tree_carrier_refusal(y))
        }
        E6Term::Overflow { carrier, left, right, .. }
        | E6Term::Arith { carrier, left, right, .. }
        | E6Term::Cmp { carrier, left, right, .. } => {
            let ty = match carrier {
                E6Carrier::Bool => trust_types::Ty::Bool,
                E6Carrier::Unsigned(width) => trust_types::Ty::Int { width: *width, signed: false },
                E6Carrier::Signed(width) => trust_types::Ty::Int { width: *width, signed: true },
            };
            let imaged = matches!(
                super::ty_to_domain(&ty),
                Some(
                    trust_spec_elab::Domain::Bool
                        | trust_spec_elab::Domain::Machine(_)
                        | trust_spec_elab::Domain::Signed(_)
                )
            );
            if imaged {
                tree_carrier_refusal(left).or_else(|| tree_carrier_refusal(right))
            } else {
                Some(format!(
                    "a comparison over `{}` has no E6 image (the comparison images decide over \
                     `bool`, `u8`..`u64` and `i8`..`i128`)",
                    ty_spelling(&ty)
                ))
            }
        }
        E6Term::Ite { cond, then, els } => tree_carrier_refusal(cond)
            .or_else(|| tree_carrier_refusal(then))
            .or_else(|| tree_carrier_refusal(els)),
    }
}

/// The refusal of the single-domain `bool` equality producer for a body whose
/// parameters are not all `bool`.
fn mixed_bool_domains(func: &trust_types::VerifiableFunction, cx: E6RefusalContext<'_>) -> String {
    format!(
        "its parameters span more than one carrier ({}), and the `bool` comparison mint is \
         single-domain",
        param_labels(func, cx)
    )
}

/// The refusal a user sees when `func` has no E6 kernel import: WHICH gate of
/// [`super::admit_function_into`] refused — the facet gate, the shape gate
/// (`recognize_admissible_body` and island forwarding) or the mint — and the
/// construct it refused. `facets` is the record `admit_function_into` read.
/// The bare view; [`explain_e6_admission_refusal_with`] takes the context the
/// compiler has.
///
/// DIAGNOSTICS ONLY (see the module docs).
#[must_use]
pub fn explain_e6_admission_refusal(
    func: &trust_types::VerifiableFunction,
    facets: &trust_spec_elab::FnFacets,
) -> String {
    explain_e6_admission_refusal_with(func, facets, E6RefusalContext::default())
}

/// [`explain_e6_admission_refusal`] with what the caller knows beyond the
/// extracted body ([`E6RefusalContext`]): the session's admissions, to name a
/// kernel-name collision, and the source parameter types, to spell `char`,
/// `usize` and `isize` as written.
///
/// DIAGNOSTICS ONLY (see the module docs).
#[must_use]
pub fn explain_e6_admission_refusal_with(
    func: &trust_types::VerifiableFunction,
    facets: &trust_spec_elab::FnFacets,
    cx: E6RefusalContext<'_>,
) -> String {
    let path = &func.def_path;
    let construct = first_construct_outside_fragment(func);
    if !facets.admissible() {
        let mut text = format!(
            "E6 admission of `{path}` was refused by the FACET gate (Pure, Total, Deterministic \
             and NoPanic must all be established): {}",
            facets.deficits().join(", ")
        );
        if let Some(construct) = construct {
            text.push_str(&format!("; the construct outside the E6 fragment is {construct}"));
        }
        return text;
    }
    match recognize_admissible_body(func) {
        Some(shape) => format!(
            "E6 admission of `{path}` was refused at the MINT: all four E6 facets hold and the \
             shape gate (`recognize_admissible_body`) read its body as `{}`, but the kernel \
             import was not minted: {}",
            shape_name(&shape),
            mint_refusal_reason(func, cx, &shape)
        ),
        None => {
            if let Some(forwarding) =
                super::island_forwarding::recognize_island_forwarding_body(func)
            {
                return format!(
                    "E6 admission of `{path}` was refused by the island-FORWARDING gate: all four \
                     E6 facets hold and its body forwards its parameters to `{}`, but that callee \
                     has no kernel-checked Clean island identity of arity {} whose declared \
                     carriers match the forwarded ones",
                    forwarding.callee,
                    forwarding.arg_params.len()
                );
            }
            // Trust (E6 expansion I1′): the E6-ONLY reader runs after the frozen
            // chain and forwarding; if it read the body, the MINT refused it.
            let stopped_at = match trust_types::e6_expr::read_e6_body_explained(func) {
                Ok(read) => {
                    return format!(
                        "E6 admission of `{path}` was refused at the MINT: all four E6 facets \
                         hold and the E6-only reader (`read_e6_body`) read its body as `{}`, but \
                         the kernel import was not minted: {}",
                        read.name(),
                        reader_mint_refusal_reason(func, cx, &read)
                    );
                }
                Err(stopped_at) => stopped_at,
            };
            // Trust (E6 expansion I3′): with no single construct outside the
            // fragment, the TREE reader's own refusal says what kept the body
            // out — it is the reader that refused, so it is the true reason.
            let construct = construct.unwrap_or(stopped_at);
            format!(
                "E6 admission of `{path}` was refused by the SHAPE gate: all four E6 facets hold, \
                 but no E6 reader reads its body (`recognize_admissible_body` found no shape, it \
                 is not an island-forwarding body, and the E6-only reader `read_e6_body` does \
                 not read it); the construct outside the E6 fragment is {construct}. The \
                 kernel-importable shapes are {E6_IMPORTABLE_SHAPES}"
            )
        }
    }
}

#[cfg(test)]
mod e6_refusal_tests {
    use trust_spec_elab::{FacetStatus, FnFacets};
    use trust_types::{
        BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
        Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::*;

    fn certified() -> FnFacets {
        let c = || FacetStatus::Certified { evidence: "test".into() };
        FnFacets { pure: c(), total: c(), deterministic: c(), no_panic: c() }
    }

    fn one_block(params: &[Ty], ret: Ty, rvalue: Rvalue) -> VerifiableFunction {
        let mut locals = vec![LocalDecl { index: 0, ty: ret.clone(), name: None }];
        for (i, ty) in params.iter().enumerate() {
            locals.push(LocalDecl {
                index: i + 1,
                ty: ty.clone(),
                name: Some(["a", "b", "c"][i].into()),
            });
        }
        VerifiableFunction {
            name: "f".into(),
            def_path: "probe::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue,
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                }],
                arg_count: params.len(),
                return_ty: ret,
                datatype_defs: Default::default(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn cp(l: usize) -> Operand {
        Operand::Copy(Place::local(l))
    }

    #[test]
    fn the_facet_gate_is_named_with_its_deficit_and_the_construct() {
        let mut facets = certified();
        facets.no_panic = FacetStatus::Undetermined { reason: "an Assert".into() };
        let u = Ty::u64();
        let f = one_block(&[u.clone(), u.clone()], u, Rvalue::BinaryOp(BinOp::Shl, cp(1), cp(2)));
        assert_eq!(
            explain_e6_admission_refusal(&f, &facets),
            "E6 admission of `probe::f` was refused by the FACET gate (Pure, Total, \
             Deterministic and NoPanic must all be established): NoPanic (not established: \
             an Assert); the construct outside the E6 fragment is the shift `<<` \
             (`BinOp::Shl`) on `u64`"
        );
    }

    #[test]
    fn the_shape_gate_is_named_with_the_construct() {
        let u = Ty::u64();
        let f =
            one_block(&[u.clone(), u.clone()], u, Rvalue::BinaryOp(BinOp::BitXor, cp(1), cp(2)));
        let text = explain_e6_admission_refusal(&f, &certified());
        assert!(
            text.starts_with(
                "E6 admission of `probe::f` was refused by the SHAPE gate: all four E6 facets \
                 hold, but no E6 reader reads its body (`recognize_admissible_body` found no \
                 shape, it is not an island-forwarding body, and the E6-only reader \
                 `read_e6_body` does not read it); the construct outside the E6 fragment is the \
                 bit operation `^` (`BinOp::BitXor`) on `u64`. The kernel-importable shapes are \
                 a parameter or field projection"
            ),
            "{text}"
        );
    }

    #[test]
    fn the_mint_is_named_for_an_ordering_over_bool() {
        let f =
            one_block(&[Ty::Bool, Ty::Bool], Ty::Bool, Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)));
        assert_eq!(
            explain_e6_admission_refusal(&f, &certified()),
            "E6 admission of `probe::f` was refused at the MINT: all four E6 facets hold and \
             the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`, but \
             the kernel import was not minted: an ordering over `bool` (`<` or `<=`; `>` and \
             `>=` arrive operand-swapped) has no E6 image: only `==` and `!=` over `bool` are \
             admitted, and an equality image for an ordering would be a false import"
        );
    }

    #[test]
    fn the_mint_names_a_parameter_without_a_carrier() {
        let f = one_block(&[Ty::Float { width: 64 }], Ty::Float { width: 64 }, Rvalue::Use(cp(1)));
        assert_eq!(
            explain_e6_admission_refusal(&f, &certified()),
            "E6 admission of `probe::f` was refused at the MINT: all four E6 facets hold and \
             the shape gate (`recognize_admissible_body`) read its body as `Projection`, but \
             the kernel import was not minted: the parameter `a: f64` has no scalar kernel \
             carrier (the carriers are `bool`, `u8`..`u64`, `u128`, `i8`..`i128`, `usize` and \
             `isize` (at the target's pointer width), and `char` (as its `u32` scalar value))"
        );
    }

    /// Review (I0 text truth): when the E6-ONLY reader read the body but a
    /// parameter has no carrier, `param_domains_of` answers `None` and the mint
    /// is never asked — so the refusal names the parameter, through the SAME
    /// carrier check the frozen chain's branch uses, never "the kernel refused
    /// the defining equation".
    #[test]
    fn the_e6_only_reader_names_a_parameter_without_a_carrier() {
        let f = one_block(
            &[Ty::Bool, Ty::Bool, Ty::Unit],
            Ty::Bool,
            Rvalue::BinaryOp(BinOp::Ne, cp(1), cp(2)),
        );
        assert_eq!(
            explain_e6_admission_refusal(&f, &certified()),
            "E6 admission of `probe::f` was refused at the MINT: all four E6 facets hold and \
             the E6-only reader (`read_e6_body`) read its body as `BoolCmp(!=)`, but the kernel \
             import was not minted: the parameter `c: ()` has no scalar kernel carrier (the \
             carriers are `bool`, `u8`..`u64`, `u128`, `i8`..`i128`, `usize` and `isize` (at \
             the target's pointer width), and `char` (as its `u32` scalar value))"
        );
    }

    /// Review (I0 text truth): the extraction the E6 lane reads lowers `char`
    /// to `u32` and `isize`/`usize` to the pointer-width integers, so only the
    /// caller's SOURCE spellings can name them as written. A list of the wrong
    /// length is ignored rather than misaligned.
    #[test]
    fn source_parameter_types_are_spelled_as_written() {
        let f = one_block(
            &[Ty::Bool, Ty::Bool, Ty::Int { width: 32, signed: false }],
            Ty::Bool,
            Rvalue::BinaryOp(BinOp::Ne, cp(1), cp(2)),
        );
        let spelled = ["bool".to_owned(), "bool".to_owned(), "char".to_owned()];
        let cx = E6RefusalContext { source_param_types: Some(&spelled), ..Default::default() };
        let text = explain_e6_admission_refusal_with(&f, &certified(), cx);
        assert!(
            text.ends_with(
                "its parameters span more than one carrier (`a: bool`, `b: bool`, `c: char`), \
                 and the `bool` comparison mint is single-domain"
            ),
            "{text}"
        );
        let short = ["bool".to_owned(), "char".to_owned()];
        let cx = E6RefusalContext { source_param_types: Some(&short), ..Default::default() };
        let text = explain_e6_admission_refusal_with(&f, &certified(), cx);
        assert!(text.contains("(`a: bool`, `b: bool`, `c: u32`)"), "{text}");
    }

    /// Review (I0 text truth): a mint the kernel refused with `DuplicateName`
    /// — another function's import already holds the mangled name — says so,
    /// naming the holder by its def path, on both the frozen chain's branch
    /// (`==`) and the E6-only reader's (`!=`). Without the table it cannot
    /// know, and keeps the generic sentence.
    #[test]
    fn a_kernel_name_collision_names_the_holder() {
        let mut table = trust_spec_elab::FacetTable::new();
        // `probe::f` and `probe__f` both mangle to `trust_import_probe__f`;
        // the holder is also recorded under a bare spelling, as the compiler
        // records every mint.
        for key in ["probe__f", "f"] {
            table.admit(key, trust_spec_elab::Admission::reflected("trust_import_probe__f", 2));
        }
        let cx = E6RefusalContext { table: Some(&table), ..Default::default() };
        let collision = "the kernel import was not minted: its kernel name \
             `trust_import_probe__f` is already held by the import minted for `probe__f`: the \
             two def paths mangle to that one name (every character that is not alphanumeric \
             becomes `_`), and the kernel refuses a second declaration of a name \
             (`DuplicateName`); renaming either function gives each its own import";
        for op in [BinOp::Eq, BinOp::Ne] {
            let f = one_block(&[Ty::Bool, Ty::Bool], Ty::Bool, Rvalue::BinaryOp(op, cp(1), cp(2)));
            let text = explain_e6_admission_refusal_with(&f, &certified(), cx);
            assert!(text.ends_with(collision), "{op:?}: {text}");
            let bare = explain_e6_admission_refusal(&f, &certified());
            assert!(!bare.contains("DuplicateName"), "{op:?}: {bare}");
        }
        // The function's OWN admission is never a collision with itself.
        let mut own = trust_spec_elab::FacetTable::new();
        own.admit("probe::f", trust_spec_elab::Admission::reflected("trust_import_probe__f", 2));
        let cx = E6RefusalContext { table: Some(&own), ..Default::default() };
        let f =
            one_block(&[Ty::Bool, Ty::Bool], Ty::Bool, Rvalue::BinaryOp(BinOp::Ne, cp(1), cp(2)));
        let text = explain_e6_admission_refusal_with(&f, &certified(), cx);
        assert!(!text.contains("DuplicateName"), "{text}");
    }

    #[test]
    fn a_bool_comparison_beside_an_integer_is_named_mixed() {
        let f = one_block(
            &[Ty::Bool, Ty::Int { width: 8, signed: false }],
            Ty::Bool,
            Rvalue::BinaryOp(BinOp::Eq, cp(1), cp(1)),
        );
        let text = explain_e6_admission_refusal(&f, &certified());
        assert!(
            text.ends_with(
                "but the kernel import was not minted: its parameters span more than one \
                 carrier (`a: bool`, `b: u8`), and the `bool` comparison mint is single-domain"
            ),
            "{text}"
        );
    }

    /// I3′: a `bool` connective tree the TREE reader read, whose comparison
    /// carrier has no image (`u128`), is refused at the MINT with that
    /// comparison named — never "single-domain", which the tree producer is
    /// not.
    #[test]
    fn a_tree_whose_comparison_has_no_image_is_named_at_the_mint() {
        let u128t = Ty::Int { width: 128, signed: false };
        let f = one_block(
            &[u128t.clone(), u128t, Ty::Bool],
            Ty::Bool,
            Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)),
        );
        // `a < b` over u128 alone is the frozen chain's `ComparisonBool`;
        // put it under a connective so only the tree reader reads it.
        let mut f = f;
        f.body.locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: None });
        f.body.blocks[0].stmts = vec![
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(BinOp::BitAnd, cp(4), cp(3)),
                span: SourceSpan::default(),
            },
        ];
        let text = explain_e6_admission_refusal(&f, &certified());
        assert_eq!(
            text,
            "E6 admission of `probe::f` was refused at the MINT: all four E6 facets hold and \
             the E6-only reader (`read_e6_body`) read its body as `BoolTree`, but the kernel \
             import was not minted: a comparison over `u128` has no E6 image (the comparison \
             images decide over `bool`, `u8`..`u64` and `i8`..`i128`)"
        );
    }

    /// I3′: when no single construct is outside the fragment, the TREE
    /// reader's own refusal is the construct named — here an ordering over
    /// `bool` under a connective, which no E6 reader gives an image.
    #[test]
    fn the_tree_readers_refusal_is_named_at_the_shape_gate() {
        let mut f = one_block(&[Ty::Bool, Ty::Bool, Ty::Bool], Ty::Bool, Rvalue::Use(cp(1)));
        f.body.locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: None });
        f.body.blocks[0].stmts = vec![
            Statement::Assign {
                place: Place::local(4),
                rvalue: Rvalue::BinaryOp(BinOp::Lt, cp(1), cp(2)),
                span: SourceSpan::default(),
            },
            Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::BinaryOp(BinOp::BitOr, cp(4), cp(3)),
                span: SourceSpan::default(),
            },
        ];
        let text = explain_e6_admission_refusal(&f, &certified());
        assert!(
            text.contains(
                "the construct outside the E6 fragment is the ordering comparison `<` \
                 (`BinOp::Lt`) on `bool`"
            ),
            "{text}"
        );
        // `(if a { x } else { 0 }) < 5`: no single construct is outside the
        // fragment (a two-way branch, a `u8` `<`), so the tree reader's refusal
        // names what it stopped at — a comparison over a computed operand.
        let u8t = Ty::Int { width: 8, signed: false };
        let mut g = one_block(&[Ty::Bool, u8t.clone()], Ty::Bool, Rvalue::Use(cp(1)));
        g.body.locals.push(LocalDecl { index: 3, ty: u8t, name: None });
        let asn = |local: usize, rvalue: Rvalue| Statement::Assign {
            place: Place::local(local),
            rvalue,
            span: SourceSpan::default(),
        };
        let u8c = |v: u128| Operand::Constant(trust_types::ConstValue::Uint(v, 8));
        g.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: cp(1),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![asn(3, Rvalue::Use(cp(2)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![asn(3, Rvalue::Use(u8c(0)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![asn(0, Rvalue::BinaryOp(BinOp::Lt, cp(3), u8c(5)))],
                terminator: Terminator::Return,
            },
        ];
        let text = explain_e6_admission_refusal(&g, &certified());
        assert!(
            text.contains(
                "refused by the SHAPE gate: all four E6 facets hold, but no E6 reader reads its \
                 body (`recognize_admissible_body` found no shape, it is not an island-forwarding \
                 body, and the E6-only reader `read_e6_body` does not read it); the construct \
                 outside the E6 fragment is a comparison `<` over `u8` whose operand is \
                 computed outside the arithmetic fragment"
            ),
            "{text}"
        );
    }

    /// I4′: a value decision the tree reader read, over a carrier the
    /// decision image has none for (`u128`), is refused at the MINT naming
    /// the return type.
    #[test]
    fn a_decision_without_an_image_carrier_is_named_at_the_mint() {
        let u128t = Ty::Int { width: 128, signed: false };
        let mut f = one_block(&[Ty::Bool, u128t.clone(), u128t.clone()], u128t, Rvalue::Use(cp(2)));
        let asn = |local: usize, rvalue: Rvalue| Statement::Assign {
            place: Place::local(local),
            rvalue,
            span: SourceSpan::default(),
        };
        f.body.blocks = vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::SwitchInt {
                    discr: cp(1),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![asn(0, Rvalue::Use(cp(2)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![asn(0, Rvalue::Use(cp(3)))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
        ];
        assert_eq!(
            explain_e6_admission_refusal(&f, &certified()),
            "E6 admission of `probe::f` was refused at the MINT: all four E6 facets hold and \
             the E6-only reader (`read_e6_body`) read its body as `DecisionTree`, but the \
             kernel import was not minted: a tree returning `u128` has no E6 image (a tree \
             returns `bool`, `u8`..`u64` or `i8`..`i128`)"
        );
    }

    #[test]
    fn the_e6_only_reader_is_named_when_its_mint_refuses() {
        let f = one_block(
            &[Ty::Bool, Ty::Bool, Ty::Int { width: 8, signed: false }],
            Ty::Bool,
            Rvalue::BinaryOp(BinOp::Ne, cp(1), cp(2)),
        );
        let text = explain_e6_admission_refusal(&f, &certified());
        assert!(
            text.starts_with(
                "E6 admission of `probe::f` was refused at the MINT: all four E6 facets hold and \
                 the E6-only reader (`read_e6_body`) read its body as `BoolCmp(!=)`"
            ),
            "{text}"
        );
    }
}
