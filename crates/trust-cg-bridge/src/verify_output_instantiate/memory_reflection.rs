//! Bounded, original-term reflection of scalar byte memory. No input memory,
//! store, address, width or query is replaced by an interpreted dummy.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::BinderInfo;
use trust_types::{Formula, Sort};

use super::{Expr, Level, Name, Reflected, discharge_env, kx, run_recheck_thread};

#[path = "memory_reflection/frame.rs"]
mod frame;
#[path = "../original_frame_arithmetic.rs"]
mod frame_arithmetic;
#[path = "memory_reflection/frame_assembly.rs"]
mod frame_assembly;
#[path = "memory_reflection/frame_bank.rs"]
mod frame_bank;
#[path = "memory_reflection/frame_offset_model.rs"]
mod frame_offset_model;
#[path = "memory_reflection/frame_offsets.rs"]
mod frame_offsets;
#[path = "memory_reflection/frame_read_model.rs"]
mod frame_read_model;
#[path = "memory_reflection/frame_reads.rs"]
mod frame_reads;
#[path = "memory_reflection/frame_word_model.rs"]
mod frame_word_model;
#[path = "memory_reflection/frame_words.rs"]
mod frame_words;
#[path = "memory_reflection/scalar_bits.rs"]
mod scalar_bits;
pub(crate) fn install_original_frame_bank(
    env: &mut clean_kernel::Environment,
) -> Result<(), String> {
    frame_bank::install(env)
}
pub(crate) fn original_conjunction_model(items: &[(Formula, Formula)]) -> u32 {
    if items.iter().any(|(a, b)| frame::has_shift(a) || frame::has_shift(b)) { 3 } else { 2 }
}

#[derive(Default)]
struct Context {
    bits: BTreeSet<String>,
    memories: BTreeSet<String>,
    sorts: BTreeMap<String, Sort>,
    // The new joint contract earns exact byte outputs. The legacy single lane
    // retains its existing named, opaque list-valued memory over-approximation.
    exact_byte_arrays: bool,
    compact_original: bool,
    frame_model: bool,
}

impl Context {
    fn variable(&mut self, name: &str, sort: &Sort) -> Option<()> {
        match self.sorts.get(name) {
            Some(previous) if previous != sort => None,
            _ => {
                self.sorts.insert(name.to_string(), sort.clone());
                Some(())
            }
        }
    }
}

fn encoded(name: &str) -> String {
    name.as_bytes().iter().map(|byte| format!("{byte:02x}")).collect()
}

fn memory_name(name: &str) -> String {
    format!("BVC_M8_MEM_x{}", encoded(name))
}

fn array_bit_name(name: &str, bit: u32) -> String {
    format!("{}_bit{bit}", memory_name(name))
}

// Both the renderer and the transport manifest use this exact namer. Its
// output order is highest bit first, matching opaque_bit_list's construction.
fn scalar_bits(name: &str, width: u32) -> (Expr, Vec<String>) {
    let key = format!("M8_w{width}_x{}", encoded(name));
    let mut names = Vec::new();
    let bits = kx::opaque_bit_list(&key, width, &mut names);
    (bits, names)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum OriginalParameterRole {
    ScalarBit { variable: String, width: u32, bit: u32 },
    ArrayBit { variable: String, bit: u32 },
}

/// Reconstruct the exact typed renderer roles, without interpreting suffixes.
/// A manifest is usable only if it covers the entire actual data context.
pub(crate) fn original_parameter_roles(
    context: &crate::original_conjunction_certificate::SymbolicContext,
) -> Option<BTreeMap<Name, OriginalParameterRole>> {
    if !context.exact_byte_arrays {
        return None;
    }
    let mut roles = BTreeMap::new();
    let mut bits = BTreeSet::new();
    let mut memories = BTreeSet::new();
    for (variable, sort) in &context.sorts {
        match sort {
            Sort::BitVec(width) if (1..=128).contains(width) => {
                let (_, names) = scalar_bits(variable, *width);
                for (name, bit) in names.into_iter().zip((0..*width).rev()) {
                    bits.insert(name.clone());
                    if roles
                        .insert(
                            Name::from_string(&name),
                            OriginalParameterRole::ScalarBit {
                                variable: variable.clone(),
                                width: *width,
                                bit,
                            },
                        )
                        .is_some()
                    {
                        return None;
                    }
                }
            }
            Sort::Array(address, byte)
                if **address == Sort::BitVec(64) && **byte == Sort::BitVec(8) =>
            {
                for bit in 0..8 {
                    let name = array_bit_name(variable, bit);
                    memories.insert(name.clone());
                    if roles
                        .insert(
                            Name::from_string(&name),
                            OriginalParameterRole::ArrayBit { variable: variable.clone(), bit },
                        )
                        .is_some()
                    {
                        return None;
                    }
                }
            }
            _ => return None,
        }
    }
    (bits == context.bits && memories == context.memories).then_some(roles)
}

// Faithful semantic rendering of the ORIGINAL sign-extension operation.
// BVC lists are LSB-first: retain every input bit, then append exactly `extra`
// copies of its actual final/sign bit. These are terms computed from the same
// operand, never fresh bits, assumptions, normalized-only goals or new axioms.
fn sign_extend_list(value: Expr, extra: u32) -> Expr {
    let sign = kx::last_bit(value.clone());
    let mut high = kx::nil();
    for _ in 0..extra {
        high = kx::cons(sign.clone(), high);
    }
    Expr::apps(Expr::const_str("Clean.BVC.bvAppend"), [value, high])
}
// Version 2 uses only beta-sharing of the SAME append/value/sign expression.
// The value occurs once as a lambda argument; the sign is similarly bound.
// There is no algebraic normalization or loss of original input bits.
fn compact_sign_extend_list(value: Expr, extra: u32) -> Expr {
    let mut high = kx::nil();
    for _ in 0..extra {
        high = kx::cons(Expr::bvar(0), high);
    }
    let body = Expr::apps(Expr::const_str("Clean.BVC.bvAppend"), [Expr::bvar(1), high]);
    let body = Expr::app(lam(kx::bool_ty(), body), kx::last_bit(Expr::bvar(0)));
    Expr::app(lam(kx::list_bool(), body), value)
}

fn sign_extend_cong(inner: Reflected, extra: u32) -> Reflected {
    let original = kx::evalf(inner.bvf);
    let normalized = kx::evalf(inner.core);
    let bvf = kx::leaf(sign_extend_list(original.clone(), extra));
    let core = kx::leaf(sign_extend_list(normalized.clone(), extra));
    let proof = congr(
        kx::list_bool(),
        kx::list_bool(),
        original,
        normalized,
        lam(kx::list_bool(), sign_extend_list(Expr::bvar(0), extra)),
        inner.proof,
    );
    Reflected { bvf, core, proof }
}

fn concat(high: Expr, low: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.BvF.Concat"), [high, low])
}

fn concat_cong(high: Reflected, low: Reflected) -> Reflected {
    let bvf = concat(high.bvf.clone(), low.bvf.clone());
    let core = concat(high.core.clone(), low.core.clone());
    let proof = Expr::apps(
        Expr::const_str("Clean.BVC.bvf_concat_cong"),
        [high.bvf, high.core, low.bvf, low.core, high.proof, low.proof],
    );
    Reflected { bvf, core, proof }
}

/// This is a representation check, never a proof-producing normalization.
pub(super) fn width(formula: &Formula) -> Option<u32> {
    let width = match formula {
        Formula::Var(_, Sort::BitVec(w)) | Formula::BitVec { width: w, .. } => *w,
        Formula::BvZeroExt(inner, extra) | Formula::BvSignExt(inner, extra) => {
            width(inner)?.checked_add(*extra)?
        }
        Formula::BvNot(inner, declared) => {
            if width(inner)? != *declared {
                return None;
            }
            *declared
        }
        Formula::BvExtract { inner, high, low } => {
            if *low > *high || *high >= width(inner)? {
                return None;
            }
            high.checked_sub(*low)?.checked_add(1)?
        }
        Formula::BvConcat(high, low) => width(high)?.checked_add(width(low)?)?,
        Formula::Ite(condition, yes, no) => {
            if trust_types::smt_logic::check_formula_sort(condition).ok()? != Sort::Bool
                || width(yes)? != width(no)?
            {
                return None;
            }
            width(yes)?
        }
        Formula::BvAdd(left, right, w)
        | Formula::BvSub(left, right, w)
        | Formula::BvOr(left, right, w)
        | Formula::BvAnd(left, right, w)
        | Formula::BvXor(left, right, w)
        | Formula::BvMul(left, right, w)
        | Formula::BvUDiv(left, right, w)
        | Formula::BvSDiv(left, right, w)
        | Formula::BvShl(left, right, w)
        | Formula::BvLShr(left, right, w)
        | Formula::BvAShr(left, right, w) => {
            if width(left)? != *w || width(right)? != *w {
                return None;
            }
            *w
        }
        Formula::Select(memory, address) => {
            memory_sort(memory)?;
            if width(address)? != 64 {
                return None;
            }
            8
        }
        _ => return None,
    };
    (1..=128).contains(&width).then_some(width)
}

fn memory_sort(memory: &Formula) -> Option<()> {
    match memory {
        Formula::Var(_, Sort::Array(address, byte))
            if **address == Sort::BitVec(64) && **byte == Sort::BitVec(8) =>
        {
            Some(())
        }
        Formula::Store(previous, address, value) if width(address)? == 64 && width(value)? == 8 => {
            memory_sort(previous)
        }
        _ => None,
    }
}

fn array_type() -> Expr {
    Expr::arrow(kx::list_bool(), kx::list_bool())
}

fn equality(ty: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty, left, right],
    )
}
fn refl(ty: Expr, term: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [ty, term],
    )
}
fn trans(ty: Expr, a: Expr, b: Expr, c: Expr, ab: Expr, bc: Expr) -> Expr {
    // These are literal endpoint identities, not a semantic normalizer. The
    // returned proof must still type-check against the unchanged original goal.
    if a == c {
        return refl(ty, a);
    }
    if a == b {
        return bc;
    }
    if b == c {
        return ab;
    }
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]),
        [ty, a, b, c, ab, bc],
    )
}
fn congr(input: Expr, output: Expr, left: Expr, right: Expr, function: Expr, proof: Expr) -> Expr {
    if left == right {
        return refl(output, Expr::app(function, left));
    }
    let level = Level::succ(Level::zero());
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![level.clone(), level]),
        [input, output, left, right, function, proof],
    )
}
fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

struct MemoryReflection {
    original: Expr,
    core: Expr,
    proof: Expr,
}

fn memory_term(memory: &Formula, context: &mut Context) -> Option<MemoryReflection> {
    memory_sort(memory)?;
    match memory {
        Formula::Var(name, sort) => {
            context.variable(name, sort)?;
            if !context.exact_byte_arrays {
                let symbol = memory_name(name);
                context.memories.insert(symbol.clone());
                let original = Expr::const_str(&symbol);
                return Some(MemoryReflection {
                    original: original.clone(),
                    core: original.clone(),
                    proof: refl(array_type(), original),
                });
            }
            // An arbitrary byte array has eight independent Boolean bit functions.
            // Building a byte from them preserves BV8 width without a length axiom.
            let mut byte = kx::nil();
            for bit in (0..8).rev() {
                let symbol = array_bit_name(name, bit);
                context.memories.insert(symbol.clone());
                byte = kx::cons(Expr::app(Expr::const_str(&symbol), Expr::bvar(0)), byte);
            }
            let original = lam(kx::list_bool(), byte);
            Some(MemoryReflection {
                original: original.clone(),
                core: original.clone(),
                proof: refl(array_type(), original),
            })
        }
        Formula::Store(previous, address, value) => {
            let previous = memory_term(previous, context)?;
            let address = reflect(address, context)?;
            let value = reflect(value, context)?;
            let a = kx::evalf(address.bvf.clone());
            let ac = kx::evalf(address.core);
            let v = kx::evalf(value.bvf);
            let vc = kx::evalf(value.core);
            let original = kx::bv_store(previous.original.clone(), a.clone(), v.clone());
            if !context.exact_byte_arrays {
                return Some(MemoryReflection {
                    original: original.clone(),
                    core: original.clone(),
                    proof: refl(array_type(), original),
                });
            }
            let middle1 = kx::bv_store(previous.core.clone(), a.clone(), v.clone());
            let middle2 = kx::bv_store(previous.core.clone(), ac.clone(), v.clone());
            let core = kx::bv_store(previous.core.clone(), ac.clone(), vc.clone());
            let pm = congr(
                array_type(),
                array_type(),
                previous.original,
                previous.core.clone(),
                lam(array_type(), kx::bv_store(Expr::bvar(0), a, v.clone())),
                previous.proof,
            );
            let pa = congr(
                kx::list_bool(),
                array_type(),
                kx::evalf(address.bvf),
                ac.clone(),
                lam(kx::list_bool(), kx::bv_store(previous.core.clone(), Expr::bvar(0), v.clone())),
                address.proof,
            );
            let pv = congr(
                kx::list_bool(),
                array_type(),
                v,
                vc,
                lam(kx::list_bool(), kx::bv_store(previous.core, ac, Expr::bvar(0))),
                value.proof,
            );
            let proof = trans(
                array_type(),
                original.clone(),
                middle1.clone(),
                core.clone(),
                pm,
                trans(array_type(), middle1, middle2, core.clone(), pa, pv),
            );
            Some(MemoryReflection { original, core, proof })
        }
        _ => None,
    }
}

fn reflexive(bvf: Expr) -> Reflected {
    Reflected { bvf: bvf.clone(), core: bvf.clone(), proof: kx::eq_refl_list(kx::evalf(bvf)) }
}

fn reflect(formula: &Formula, context: &mut Context) -> Option<Reflected> {
    let output_width = width(formula)?;
    let reflected = match formula {
        Formula::Var(name, Sort::BitVec(w)) => {
            // Injective UTF-8 encoding, width and bit index preserve ALL original
            // input bits. In particular a fresh query retains its entire BV64 domain.
            context.variable(name, &Sort::BitVec(*w))?;
            let (bits, names) = scalar_bits(name, *w);
            context.bits.extend(names);
            Some(reflexive(kx::leaf(bits)))
        }
        Formula::BitVec { value, width } => Some(reflexive(kx::const_(kx::bits(*value, *width)))),
        Formula::BvConcat(high, low) => {
            Some(concat_cong(reflect(high, context)?, reflect(low, context)?))
        }
        Formula::BvSignExt(inner, extra) => {
            Some(sign_extend_cong(reflect(inner, context)?, *extra))
        }
        Formula::BvNot(inner, _) => {
            // MOVN and MVN contribute a real bitwise complement to the
            // machine formula. Preserve that operation in the original goal;
            // transport only the checked equality for its operand.
            let inner = reflect(inner, context)?;
            let original = kx::evalf(inner.bvf);
            let normalized = kx::evalf(inner.core);
            let bvf = kx::leaf(kx::bv_not(original.clone()));
            let core = kx::leaf(kx::bv_not(normalized.clone()));
            let proof = congr(
                kx::list_bool(),
                kx::list_bool(),
                original,
                normalized,
                lam(kx::list_bool(), kx::bv_not(Expr::bvar(0))),
                inner.proof,
            );
            Some(Reflected { bvf, core, proof })
        }
        Formula::BvZeroExt(inner, extra) => {
            let inner = reflect(inner, context)?;
            let extra = kx::nat_lit(*extra);
            let bvf = kx::zext(inner.bvf.clone(), extra.clone());
            let core = kx::zext(inner.core.clone(), extra.clone());
            let proof = kx::zext_cong(inner.bvf, inner.core, extra, inner.proof);
            Some(Reflected { bvf, core, proof })
        }
        Formula::BvExtract { inner, low: 0, .. } => {
            let reflected = reflect(inner, context)?;
            let tag = kx::const_(kx::bits(0, output_width));
            let bvf = kx::extract(reflected.bvf.clone(), tag.clone());
            let mut core = kx::extract(reflected.core.clone(), tag.clone());
            let mut proof =
                kx::extract_cong1(reflected.bvf, reflected.core.clone(), tag, reflected.proof);
            if let Formula::BvConcat(high, low) = &**inner
                && width(low)? == output_width
            {
                let high = reflect(high, context)?;
                let low = reflect(low, context)?;
                let projected = Expr::apps(
                    Expr::const_str("Clean.BVC.bvf_concat_low"),
                    [high.core, low.core.clone()],
                );
                // The final kernel check must match the ACTUAL fixed-width tag
                // to this theorem's low tag; an opaque wrong-width read cannot
                // gain permission from an unchecked Rust substitution.
                proof = kx::eq_trans_list(
                    kx::evalf(bvf.clone()),
                    kx::evalf(core),
                    kx::evalf(low.core.clone()),
                    proof,
                    projected,
                );
                core = low.core;
            }
            Some(Reflected { bvf, core, proof })
        }
        Formula::BvAdd(left, right, _)
        | Formula::BvSub(left, right, _)
        | Formula::BvOr(left, right, _)
        | Formula::BvAnd(left, right, _)
        | Formula::BvXor(left, right, _) => {
            let left = reflect(left, context)?;
            let right = reflect(right, context)?;
            let (make, congruence): (
                fn(Expr, Expr) -> Expr,
                fn(Expr, Expr, Expr, Expr, Expr, Expr) -> Expr,
            ) = match formula {
                Formula::BvAdd(..) => (kx::add, kx::add_cong),
                Formula::BvSub(..) => (kx::sub, kx::sub_cong),
                Formula::BvOr(..) => (kx::or, kx::or_cong),
                Formula::BvAnd(..) => (kx::and, kx::and_cong),
                Formula::BvXor(..) => (kx::xor, kx::xor_cong),
                _ => return None,
            };
            // Each reduction carries a real proof against the ORIGINAL term.
            // In particular the A64 register-move OR(0, value) must not lose
            // its actual fixed-width zero operand in the retained goal.
            let zero_identity = if context.exact_byte_arrays {
                match formula {
                    Formula::BvAdd(a, _, _) if matches!(&**a, Formula::BitVec { value: 0, .. }) => {
                        Some((right.core.clone(), 0))
                    }
                    Formula::BvAdd(_, b, _) if matches!(&**b, Formula::BitVec { value: 0, .. }) => {
                        Some((left.core.clone(), 1))
                    }
                    Formula::BvOr(a, _, _) if matches!(&**a, Formula::BitVec { value: 0, .. }) => {
                        Some((right.core.clone(), 2))
                    }
                    _ => None,
                }
            } else {
                None
            };
            let bvf = make(left.bvf.clone(), right.bvf.clone());
            let mut core = make(left.core.clone(), right.core.clone());
            let mut proof =
                congruence(left.bvf, left.core, right.bvf, right.core, left.proof, right.proof);
            if let Some((target, identity_kind)) = zero_identity {
                let identity = match identity_kind {
                    0 => kx::add_zero_id(target.clone()),
                    1 => Expr::app(
                        Expr::const_str("Clean.BVC.add_right_zero_id"),
                        kx::evalf(target.clone()),
                    ),
                    2 => kx::or_zero_id(target.clone()),
                    _ => return None,
                };
                proof = kx::eq_trans_list(
                    kx::evalf(bvf.clone()),
                    kx::evalf(core),
                    kx::evalf(target.clone()),
                    proof,
                    identity,
                );
                core = target;
            }
            Some(Reflected { bvf, core, proof })
        }
        Formula::Select(memory, address) => {
            let memory_reflected = memory_term(memory, context)?;
            let original_memory = memory_reflected.original.clone();
            let address_reflected = reflect(address, context)?;
            let actual =
                kx::bv_select(original_memory.clone(), kx::evalf(address_reflected.bvf.clone()));
            let bvf = kx::leaf(actual.clone());
            if let Formula::Store(previous, stored_address, value) = &**memory {
                if stored_address == address {
                    let previous = memory_term(previous, context)?.original;
                    let stored_address = reflect(stored_address, context)?;
                    let value = reflect(value, context)?;
                    let read_over_write = kx::select_store_same(
                        previous,
                        kx::evalf(stored_address.bvf),
                        kx::evalf(value.bvf.clone()),
                    );
                    let proof = kx::eq_trans_list(
                        actual,
                        kx::evalf(value.bvf),
                        kx::evalf(value.core.clone()),
                        read_over_write,
                        value.proof,
                    );
                    return Some(Reflected { bvf, core: value.core, proof });
                }
                // Only an ACTUAL literal/literal inequality selects this case.
                // A symbolic query is never replaced by a chosen address.
                if let (
                    Formula::BitVec { value: a, width: 64 },
                    Formula::BitVec { value: q, width: 64 },
                ) = (&**stored_address, &**address)
                    && (*a as u64) != (*q as u64)
                {
                    let below = Formula::Select(previous.clone(), address.clone());
                    let below = reflect(&below, context)?;
                    let previous = memory_term(previous, context)?.original;
                    let stored_address = reflect(stored_address, context)?;
                    let value = reflect(value, context)?;
                    let guard = Expr::apps(
                        Expr::const_(
                            Name::from_string("Eq.refl"),
                            vec![Level::succ(Level::zero())],
                        ),
                        [kx::bool_ty(), Expr::const_str("Bool.false")],
                    );
                    let read_over_write = Expr::apps(
                        Expr::const_str("Clean.BVC.selectStoreDiff"),
                        [
                            previous,
                            kx::evalf(stored_address.bvf),
                            kx::evalf(address_reflected.bvf),
                            kx::evalf(value.bvf),
                            guard,
                        ],
                    );
                    let proof = kx::eq_trans_list(
                        actual,
                        kx::evalf(below.bvf),
                        kx::evalf(below.core.clone()),
                        read_over_write,
                        below.proof,
                    );
                    return Some(Reflected { bvf, core: below.core, proof });
                }
            }
            // Preserve the entire memory term. The only normalization is the
            // separately checked address equality under the SAME array.
            let address_original = kx::evalf(address_reflected.bvf);
            let address_core = kx::evalf(address_reflected.core);
            let middle = kx::bv_select(memory_reflected.core.clone(), address_original.clone());
            let normalized = kx::bv_select(memory_reflected.core.clone(), address_core.clone());
            let memory_proof = congr(
                array_type(),
                kx::list_bool(),
                original_memory,
                memory_reflected.core.clone(),
                lam(array_type(), kx::bv_select(Expr::bvar(0), address_original.clone())),
                memory_reflected.proof,
            );
            let address_proof = kx::select_addr_cong(
                memory_reflected.core,
                address_original,
                address_core,
                address_reflected.proof,
            );
            let core = kx::leaf(normalized.clone());
            let proof = kx::eq_trans_list(actual, middle, normalized, memory_proof, address_proof);
            Some(Reflected { bvf, core, proof })
        }
        _ => None,
    }?;
    // Reflexivity of the SAME structural expression is sufficient. Avoid
    // retaining exponentially repeated congruence proofs for unchanged child
    // terms; neither the original expression nor any proof budget changes.
    Some(if reflected.bvf == reflected.core { reflexive(reflected.bvf) } else { reflected })
}

#[cfg(test)]
pub(super) fn accepts(formula: &Formula) -> bool {
    reflect(formula, &mut Context::default()).is_some()
}

fn equation(machine: &Formula, source: &Formula, context: &mut Context) -> Option<(Expr, Expr)> {
    equation_values(machine, source, context).map(|(goal, proof, _, _)| (goal, proof))
}

fn equation_values(
    machine: &Formula,
    source: &Formula,
    context: &mut Context,
) -> Option<(Expr, Expr, Expr, Expr)> {
    if width(machine)? != width(source)? {
        return None;
    }
    if context.exact_byte_arrays
        && let Some(original) = scalar_bits::equation(machine, source, context)
    {
        return Some(original);
    }
    if let Some(proof) = frame::equation(machine, source, context) {
        return Some(proof);
    }
    // The fallback proof may use the earlier reducible spelling internally,
    // but the retained statement must use the versioned original renderer.
    // The final kernel check validates the conversion, not a new assumption.
    let canonical = if context.compact_original {
        Some((
            kx::evalf(original_value(machine, context)?),
            kx::evalf(original_value(source, context)?),
        ))
    } else {
        None
    };
    let machine = reflect(machine, context)?;
    let source = reflect(source, context)?;
    let left = kx::evalf(machine.bvf.clone());
    let right = kx::evalf(source.bvf.clone());
    let goal = match canonical {
        Some((a, b)) => equality(kx::list_bool(), a, b),
        None => equality(kx::list_bool(), left.clone(), right.clone()),
    };
    let source_reverse = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
        [
            kx::list_bool(),
            kx::evalf(source.bvf.clone()),
            kx::evalf(source.core.clone()),
            source.proof,
        ],
    );
    let proof = kx::eq_trans_list(
        kx::evalf(machine.bvf),
        kx::evalf(machine.core),
        kx::evalf(source.bvf),
        machine.proof,
        source_reverse,
    );
    Some((goal, proof, left, right))
}

fn context_env(context: &Context) -> Option<clean_kernel::Environment> {
    let mut env = discharge_env(&[], &[]).ok()?;
    for name in &context.bits {
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: kx::bool_ty(),
        })
        .ok()?;
    }
    for name in &context.memories {
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::arrow(
                kx::list_bool(),
                if context.exact_byte_arrays { kx::bool_ty() } else { kx::list_bool() },
            ),
        })
        .ok()?;
    }
    Some(env)
}

pub(super) fn discharge(machine: &Formula, source: &Formula) -> Option<String> {
    let mut context = Context::default();
    let (goal, proof) = equation(machine, source, &mut context)?;
    run_recheck_thread("trust-m8-original-memory", move || {
        let env = context_env(&context)?;
        clean_kernel::TypeChecker::with_mode(&env, env.mode()).check_type(&proof, &goal).ok()?;
        Some(
            "Clean.BVC.bvf_concat_cong+selectAddrCong/read-over-write (original memory terms)"
                .to_string(),
        )
    })
    .ok()
    .flatten()
}

struct OriginalConjunction {
    context: Context,
    goal: Expr,
    proof: Expr,
}

#[cfg(any(test, feature = "test-hooks"))]
fn term_profile(value: &Expr) -> serde_json::Value {
    use clean_kernel::ExprKind;
    fn visit(x: &Expr, m: &mut BTreeMap<usize, (u64, u32)>) -> (u64, u32) {
        let key = x.kind() as *const ExprKind as usize;
        if let Some(v) = m.get(&key) {
            return *v;
        }
        let children = match x.kind() {
            ExprKind::App(a, b) | ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => vec![a, b],
            _ => vec![],
        };
        let mut expanded = 1u64;
        let mut depth = 1u32;
        for c in children {
            let (n, d) = visit(c, m);
            expanded = expanded.saturating_add(n);
            depth = depth.max(d.saturating_add(1));
        }
        let result = (expanded, depth);
        m.insert(key, result);
        result
    }
    let mut memo = BTreeMap::new();
    let (n, d) = visit(value, &mut memo);
    serde_json::json!({"expanded":n,"depth":d,"actual_shared_nodes":memo.len()})
}

fn prepare_conjunction(items: &[(Formula, Formula)]) -> Option<OriginalConjunction> {
    if items.is_empty() {
        return None;
    }
    let mut context = Context {
        exact_byte_arrays: true,
        compact_original: true,
        frame_model: original_conjunction_model(items) == 3,
        ..Context::default()
    };
    let mut equations = Vec::with_capacity(items.len());
    for (index, (machine, source)) in items.iter().enumerate() {
        let Some(equation) = equation_values(machine, source, &mut context) else {
            #[cfg(any(test, feature = "test-hooks"))]
            record_test_failure(
                items,
                "reflection",
                &format!("original equation index {index} is unreflectable"),
            );
            return None;
        };
        equations.push(equation);
    }
    #[cfg(any(test, feature = "test-hooks"))]
    if let Some(dir) = std::env::var_os("TRUST_M8_FAILURE_DIR") {
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).ok()?;
        let rows:Vec<_>=equations.iter().enumerate().map(|(i,(g,p,_,_))|serde_json::json!({"index":i,"goal":term_profile(g),"proof":term_profile(p)})).collect();
        std::fs::write(
            dir.join("original-equation-term-profile.json"),
            serde_json::to_vec_pretty(&rows).ok()?,
        )
        .ok()?;
    }
    let count = u32::try_from(equations.len()).ok()?;
    let _ = count.checked_mul(3)?;
    let mut goal = equations.last()?.0.clone();
    for (left, _, _, _) in equations[..equations.len() - 1].iter().rev() {
        goal = Expr::apps(Expr::const_str("And"), [left.clone(), goal]);
    }

    // Bind each pair of List Bool values and its equality proof once. Inside
    // this function all conjunction type arguments contain only bound values,
    // avoiding quadratic copies of large suffix propositions. Applying the
    // function below restores the EXACT original goal. Every proof argument
    // is checked against its dependent Eq domain by the final kernel check.
    // Only existing List/ Eq /And, Lam/App and scoped BVar nodes are used.
    let bound = |index: u32| {
        let base = (count - index - 1) * 3;
        (equality(kx::list_bool(), Expr::bvar(base + 2), Expr::bvar(base + 1)), Expr::bvar(base))
    };
    let (mut bound_goal, mut proof) = bound(count - 1);
    for index in (0..count - 1).rev() {
        let (left, left_proof) = bound(index);
        proof = Expr::apps(
            Expr::const_str("And.intro"),
            [left.clone(), bound_goal.clone(), left_proof, proof],
        );
        bound_goal = Expr::apps(Expr::const_str("And"), [left, bound_goal]);
    }
    for _ in 0..count {
        let hypothesis = equality(kx::list_bool(), Expr::bvar(1), Expr::bvar(0));
        proof = lam(kx::list_bool(), lam(kx::list_bool(), lam(hypothesis, proof)));
    }
    for (_, equality_proof, left, right) in equations {
        proof = Expr::apps(proof, [left, right, equality_proof]);
    }
    Some(OriginalConjunction { context, goal, proof })
}

/// A single checked CIC conjunction of the actual typed input equations.
/// Shared data parameters preserve identities across every conjunct. No scalar
/// verdicts, solver premises or normalized-only goals participate in this proof.
pub(super) fn discharge_conjunction(
    items: &[(Formula, Formula)],
) -> Option<crate::original_conjunction_certificate::CheckedOriginalConjunction> {
    #[cfg(any(test, feature = "test-hooks"))]
    crate::original_conjunction_certificate::require_production_allowed();
    let Some(prepared) = prepare_conjunction(items) else {
        #[cfg(any(test, feature = "test-hooks"))]
        record_test_failure(items, "reflection", "an original equation is unreflectable");
        return None;
    };
    let original = items.to_vec();
    run_recheck_thread("trust-m8-original-conjunction", move || {
        let result = crate::original_conjunction_certificate::check_produced(
            &original,
            &prepared.goal,
            &prepared.proof,
        );
        #[cfg(any(test, feature = "test-hooks"))]
        if let Err(error) = &result {
            record_test_failure(&original, "kernel-or-retention", error);
        }
        result.ok()
    })
    .ok()
    .flatten()
}

#[cfg(any(test, feature = "test-hooks"))]
fn record_test_failure(items: &[(Formula, Formula)], phase: &str, error: &str) {
    let Some(path) = std::env::var_os("TRUST_M8_FAILURE_DIR") else { return };
    #[derive(serde::Serialize)]
    struct Failure<'a> {
        phase: &'a str,
        error: String,
        original: &'a [(Formula, Formula)],
    }
    let result = (|| -> Result<(), String> {
        let original = serde_json::to_vec(items).map_err(|e| e.to_string())?;
        let digest = crate::object_replay::artifact_digest(&original);
        let path = std::path::PathBuf::from(path);
        std::fs::create_dir_all(&path).map_err(|e| e.to_string())?;
        let report = Failure { phase, error: error.chars().take(8192).collect(), original: items };
        std::fs::write(
            path.join(format!("{digest}.failure.json")),
            serde_json::to_vec_pretty(&report).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())
    })();
    // A diagnostic write failure cannot panic, grant evidence or change the
    // already-failed proof result. The qualification harness checks artifacts.
    if let Err(error) = result {
        let _ = std::io::Write::write_all(
            &mut std::io::stderr(),
            format!("original CIC failure capture refused: {error}\n").as_bytes(),
        );
    }
}

// Pure rendering for replay: this constructs the actual original statement and
// typed data context, never a proof, simplified core, solver query or verdict.
fn original_memory(memory: &Formula, context: &mut Context) -> Option<Expr> {
    memory_sort(memory)?;
    match memory {
        Formula::Var(name, sort) => {
            context.variable(name, sort)?;
            let mut byte = kx::nil();
            for bit in (0..8).rev() {
                let symbol = array_bit_name(name, bit);
                context.memories.insert(symbol.clone());
                byte = kx::cons(Expr::app(Expr::const_str(&symbol), Expr::bvar(0)), byte);
            }
            Some(lam(kx::list_bool(), byte))
        }
        Formula::Store(previous, address, value) => Some(kx::bv_store(
            original_memory(previous, context)?,
            kx::evalf(original_value(address, context)?),
            kx::evalf(original_value(value, context)?),
        )),
        _ => None,
    }
}
fn original_value(formula: &Formula, context: &mut Context) -> Option<Expr> {
    let output_width = width(formula)?;
    match formula {
        Formula::Var(name, Sort::BitVec(w)) => {
            context.variable(name, &Sort::BitVec(*w))?;
            let (bits, names) = scalar_bits(name, *w);
            context.bits.extend(names);
            Some(kx::leaf(bits))
        }
        Formula::BitVec { value, width } => Some(kx::const_(kx::bits(*value, *width))),
        Formula::BvConcat(high, low) => {
            Some(concat(original_value(high, context)?, original_value(low, context)?))
        }
        Formula::BvSignExt(inner, extra) => {
            let value = kx::evalf(original_value(inner, context)?);
            Some(kx::leaf(if context.compact_original {
                compact_sign_extend_list(value, *extra)
            } else {
                sign_extend_list(value, *extra)
            }))
        }
        Formula::BvNot(inner, _) => {
            Some(kx::leaf(kx::bv_not(kx::evalf(original_value(inner, context)?))))
        }
        Formula::BvZeroExt(inner, extra) => {
            Some(kx::zext(original_value(inner, context)?, kx::nat_lit(*extra)))
        }
        Formula::Ite(..) if context.compact_original => scalar_bits::render(formula, context),
        Formula::BvExtract { low, .. } if *low != 0 && context.compact_original => {
            scalar_bits::render(formula, context)
        }
        Formula::BvExtract { inner, low: 0, .. } => Some(kx::extract(
            original_value(inner, context)?,
            kx::const_(kx::bits(0, output_width)),
        )),
        Formula::BvShl(left, right, _) if context.frame_model => {
            Some(kx::shl(original_value(left, context)?, original_value(right, context)?))
        }
        Formula::BvAdd(left, right, _)
        | Formula::BvSub(left, right, _)
        | Formula::BvOr(left, right, _)
        | Formula::BvAnd(left, right, _)
        | Formula::BvXor(left, right, _) => {
            let left = original_value(left, context)?;
            let right = original_value(right, context)?;
            Some(match formula {
                Formula::BvAdd(..) => kx::add(left, right),
                Formula::BvSub(..) => kx::sub(left, right),
                Formula::BvOr(..) => kx::or(left, right),
                Formula::BvAnd(..) => kx::and(left, right),
                Formula::BvXor(..) => kx::xor(left, right),
                _ => return None,
            })
        }
        Formula::Select(memory, address) => Some(kx::leaf(kx::bv_select(
            original_memory(memory, context)?,
            kx::evalf(original_value(address, context)?),
        ))),
        _ => None,
    }
}

/// Pure original rendering plus only Eq.refl; no original proof producer is
/// entered when a caller adds an exact reflexive argument/state binding.
pub(crate) fn original_reflexive_equation(formula: &Formula) -> Option<(Expr, Expr)> {
    let mut context =
        Context { exact_byte_arrays: true, compact_original: true, ..Context::default() };
    let value = kx::evalf(original_value(formula, &mut context)?);
    Some((equality(kx::list_bool(), value.clone(), value.clone()), refl(kx::list_bool(), value)))
}

pub(crate) fn original_conjunction_goal(
    items: &[(Formula, Formula)],
) -> Option<(Expr, crate::original_conjunction_certificate::SymbolicContext)> {
    original_conjunction_goal_version(items, original_conjunction_model(items))
}

pub(crate) fn original_conjunction_goal_version(
    items: &[(Formula, Formula)],
    version: u32,
) -> Option<(Expr, crate::original_conjunction_certificate::SymbolicContext)> {
    if !matches!(version, 1 | 2 | 3) {
        return None;
    }
    if items.is_empty() {
        return None;
    }
    let mut context = Context {
        exact_byte_arrays: true,
        compact_original: version >= 2,
        frame_model: version == 3,
        ..Context::default()
    };
    let mut equations = Vec::with_capacity(items.len());
    for (machine, source) in items {
        if width(machine)? != width(source)? {
            return None;
        }
        let machine = original_value(machine, &mut context)?;
        let source = original_value(source, &mut context)?;
        equations.push(equality(kx::list_bool(), kx::evalf(machine), kx::evalf(source)));
    }
    let mut goal = equations.pop()?;
    for left in equations.into_iter().rev() {
        goal = Expr::apps(Expr::const_str("And"), [left, goal]);
    }
    Some((
        goal,
        crate::original_conjunction_certificate::SymbolicContext {
            bits: context.bits,
            memories: context.memories,
            sorts: context.sorts,
            exact_byte_arrays: true,
        },
    ))
}

pub(super) fn contains_concat(formula: &Formula) -> bool {
    match formula {
        Formula::BvConcat(..) => true,
        Formula::BvExtract { inner, .. }
        | Formula::BvZeroExt(inner, _)
        | Formula::BvSignExt(inner, _) => contains_concat(inner),
        Formula::BvAdd(a, b, _)
        | Formula::BvSub(a, b, _)
        | Formula::BvOr(a, b, _)
        | Formula::BvAnd(a, b, _)
        | Formula::BvXor(a, b, _)
        | Formula::Select(a, b) => contains_concat(a) || contains_concat(b),
        Formula::Store(a, b, c) => contains_concat(a) || contains_concat(b) || contains_concat(c),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn b(f: Formula) -> Box<Formula> {
        Box::new(f)
    }
    fn v(name: &str, width: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(width))
    }
    fn c(value: i128, width: u32) -> Formula {
        Formula::BitVec { value, width }
    }
    fn mem(name: &str) -> Formula {
        Formula::Var(
            name.into(),
            Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(8))),
        )
    }
    fn read(m: Formula, q: Formula) -> Formula {
        Formula::Select(b(m), b(q))
    }
    fn store(m: Formula, p: Formula, value: Formula) -> Formula {
        Formula::Store(b(m), b(p), b(value))
    }
    fn cat(h: Formula, l: Formula) -> Formula {
        Formula::BvConcat(b(h), b(l))
    }
    fn slice(f: Formula, high: u32) -> Formula {
        Formula::BvExtract { inner: b(f), high, low: 0 }
    }
    fn zext(f: Formula, k: u32) -> Formula {
        Formula::BvZeroExt(b(f), k)
    }
    fn prove(m: &Formula, s: &Formula) -> bool {
        super::super::try_o1_instantiation_discharge(m, s).is_some()
    }

    #[test]
    fn original_concat_and_low_slice_have_checked_kernel_proofs() {
        let h = v("high", 8);
        let l = v("low", 8);
        let source = cat(h.clone(), l.clone());
        let machine = cat(slice(zext(h.clone(), 24), 7), slice(zext(l.clone(), 24), 7));
        assert!(prove(&machine, &source));
        assert!(!prove(&cat(l.clone(), h.clone()), &source), "wrong concat order");
        assert!(prove(&slice(source.clone(), 7), &l));
        assert!(!prove(&slice(source, 7), &h), "wrong low operand");
    }

    #[test]
    fn nested_memory_retains_original_store_and_complete_readout() {
        let p = v("pointer", 64);
        let value = v("value", 8);
        let under = store(mem("entry"), c(0x1000, 64), v("old_byte", 8));
        let source = read(store(under, p.clone(), value.clone()), p);
        let machine = slice(zext(slice(zext(zext(source.clone(), 32), 32), 31), 32), 7);
        assert!(prove(&machine, &value), "same-address read-over-write with real complete memory");
        assert!(prove(&source, &value));
        assert!(!prove(&source, &v("different_value", 8)), "changed stored byte");
    }

    #[test]
    fn fresh_query_preserves_all_bits_and_refuses_changed_memory() {
        let p = v("pointer", 64);
        let q = v("fresh_query", 64);
        let memory = store(mem("entry"), p.clone(), v("value", 8));
        let source = read(memory.clone(), q.clone());
        assert!(prove(&source, &source));
        for mutant in [
            read(mem("entry"), q.clone()),
            read(store(mem("entry"), p.clone(), v("changed_byte", 8)), q.clone()),
            read(store(mem("other_entry"), p, v("value", 8)), q.clone()),
            read(memory, c(0, 64)),
        ] {
            assert!(
                !prove(&mutant, &source),
                "dropped/changed store, memory, or query must not gain proof"
            );
        }
        let mut context = Context::default();
        reflect(&source, &mut context).unwrap();
        assert_eq!(
            context
                .bits
                .iter()
                .filter(|name| name.contains(&format!("M8_w64_x{}", encoded("fresh_query"))))
                .count(),
            64
        );
    }

    #[test]
    fn literal_read_over_write_other_composes_without_a_disjointness_assumption() {
        let m = store(store(mem("entry"), c(0x1000, 64), v("low", 8)), c(0x1001, 64), v("high", 8));
        let source = cat(read(m.clone(), c(0x1001, 64)), read(m, c(0x1000, 64)));
        assert!(prove(&source, &cat(v("high", 8), v("low", 8))));
        assert!(!prove(&source, &cat(v("low", 8), v("high", 8))));
    }

    #[test]
    fn symbolic_names_and_sorts_cannot_alias_after_encoding() {
        assert_ne!(encoded("a.b"), encoded("a..b"));
        assert!(!prove(&cat(v("a.b", 8), v("tail", 8)), &cat(v("a..b", 8), v("tail", 8))));
        assert!(!prove(&read(mem("a.b"), v("p", 64)), &read(mem("a..b"), v("p", 64))));
        assert!(!prove(
            &cat(zext(v("same", 8), 8), v("tail", 8)),
            &cat(v("same", 16), v("tail", 8))
        ));
        let bad = Formula::Var(
            "entry".into(),
            Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
        );
        assert!(discharge(&read(bad, v("p", 64)), &read(mem("entry"), v("p", 64))).is_none());
    }

    #[test]
    fn narrowing_extract_cannot_be_replaced_by_its_untruncated_operand() {
        let input = v("word", 16);
        let narrowed = slice(zext(input.clone(), 16), 7);
        let machine = slice(zext(narrowed, 8), 15);
        assert!(!prove(&machine, &input), "original scalar shortcut ignored the inner high index");
        let mut context = super::super::ReflectCtx::closed();
        assert!(super::super::reflect_formula(&machine, &mut context).is_err());
        let malformed = cat(Formula::BvAdd(b(v("x", 8)), b(v("y", 16)), 8), v("z", 8));
        assert!(discharge(&malformed, &malformed).is_none(), "declared BV widths are checked");
    }
    #[test]
    fn scalar_width_guard_keeps_existing_multiply_divide_shift_identities() {
        let x = v("scalar_x", 32);
        let y = v("scalar_y", 32);
        for source in [
            Formula::BvMul(b(x.clone()), b(y.clone()), 32),
            Formula::BvUDiv(b(x.clone()), b(y.clone()), 32),
            Formula::BvShl(b(x.clone()), b(y.clone()), 32),
        ] {
            let machine = slice(zext(source.clone(), 32), 31);
            assert!(prove(&machine, &source), "typed scalar wrapper identity");
        }
    }
}

#[cfg(test)]
#[path = "memory_reflection/conjunction_tests.rs"]
mod conjunction_tests;
