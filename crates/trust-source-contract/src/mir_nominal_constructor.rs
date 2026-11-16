//! Bounded declaration/constructor observation, never a source proof or grade.
use std::collections::BTreeSet;

use trust_types::{Ty, VariantDef, VerifiableFunction};

/// A nullary constructor selected from the ORIGINAL borrowed declaration.
/// No caller-provided discriminant, payload, source bound or representation flag.
pub struct MirNominalConstructor<'a> {
    function: &'a VerifiableFunction,
    parameter: usize,
    ordinal: usize,
    nominal_name: &'a str,
    variant: &'a VariantDef,
    word: u64,
}
impl<'a> MirNominalConstructor<'a> {
    pub fn function(&self) -> &'a VerifiableFunction {
        self.function
    }
    pub fn parameter_local(&self) -> usize {
        self.parameter
    }
    pub fn ordinal(&self) -> usize {
        self.ordinal
    }
    pub fn nominal_name(&self) -> &'a str {
        self.nominal_name
    }
    pub fn variant(&self) -> &'a VariantDef {
        self.variant
    }
    pub fn word(&self) -> u64 {
        self.word
    }
}

/// Observe a declared nullary constructor on the exact legacy I64-tag route.
/// All declared variants are checked before selection, including inactive ones.
/// This does not authenticate external AST provenance, a runtime Rust value,
/// physical layout, or a kernel quotation; it returns borrowed DATA only.
pub fn observe_mir_nominal_constructor(
    function: &VerifiableFunction,
    parameter: usize,
    ordinal: usize,
) -> Option<MirNominalConstructor<'_>> {
    super::mir_bool_assignment::bounded_unique_original(function)?;
    if parameter == 0 || parameter > function.body.arg_count {
        return None;
    }
    let local = function.body.locals.iter().find(|local| local.index == parameter)?;
    let Ty::Adt { name, fields, variants, faithful_enum_repr, .. } = &local.ty else {
        return None;
    };
    if name.is_empty()
        || name.len() > 4096
        || variants.is_empty()
        || variants.len() > 256
        || faithful_enum_repr.is_some()
        || fields.len() != 1
    {
        return None;
    }
    let (tag_name, tag_ty) = &fields[0];
    if tag_name != "__tag" || *tag_ty != (Ty::Int { width: 64, signed: true }) {
        return None;
    }
    let mut names = BTreeSet::new();
    let mut tags = BTreeSet::new();
    for variant in variants.iter() {
        if !variant.fields.is_empty()
            || variant.name.is_empty()
            || variant.name.len() > 256
            || i64::try_from(variant.discriminant).is_err()
            || !names.insert(variant.name.as_str())
            || !tags.insert(variant.discriminant)
        {
            return None;
        }
    }
    let variant = variants.get(ordinal)?;
    let tag = i64::try_from(variant.discriminant).ok()?;
    Some(MirNominalConstructor {
        function,
        parameter,
        ordinal,
        nominal_name: name,
        variant,
        // Defined mathematical signed-integer -> width64 residue, NOT enum-as-int.
        word: tag as u64,
    })
}
