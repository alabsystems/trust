//! Pending incoming-pointer memory obligations (PTR.3b, M1–M5).
//!
//! This is a term-building interface, not a verifier. Nothing here grants a
//! grade, classifies a counterexample as a miscompile, supplies an assumption,
//! or changes CER's O5/rely/closure fold. In particular, the current CER gate
//! still refuses incoming-pointer loads/stores and unsupported ABI extensions.
//!
//! A future consumer must derive COMPLETE path accesses from both actual IR
//! and decoded bytes. Source admission must separately establish nonvolatile
//! scalar accesses rooted at an entry argument through approved constant byte
//! GEPs. A closure capture's pointer value does not establish validity or
//! disjointness. `pointer_roots::Arg(i)` alone does not distinguish captures of
//! the same aggregate. These builders infer neither roots nor alias facts.
//!
//! Required integration before any shipping use: shared entry memory (M1),
//! explicitly justified frame separation on both sides (M1′), complete typed
//! source evaluation (M2), byte coverage (M3), exit memory (M4), paired shared
//! call transitions (M5), legal disjoint counterexample witnesses (M6), refusal
//! of all unsupported memory forms (M7), and independent kernel support (M8).
//! See docs/design/2026-10-13-step2-inc5-pointer-args-plan.md §7.2.

use trust_types::{Formula, Sort};

use crate::verify_output::{load_bytes_le_formula, store_bytes_le_formula};

fn b(f: Formula) -> Box<Formula> {
    Box::new(f)
}
fn bv(n: u64) -> Formula {
    Formula::BitVec { value: i128::from(n), width: 64 }
}
fn and(xs: Vec<Formula>) -> Formula {
    Formula::And(xs)
}
fn implies(p: Formula, q: Formula) -> Formula {
    Formula::Or(vec![Formula::Not(b(p)), q])
}
fn eq(a: Formula, c: Formula) -> Formula {
    Formula::Eq(b(a), b(c))
}
fn byte_at(address: &Formula, offset: u32) -> Formula {
    if offset == 0 {
        address.clone()
    } else {
        Formula::BvAdd(b(address.clone()), b(bv(u64::from(offset))), 64)
    }
}
fn memory_sort() -> Sort {
    Sort::Array(b_sort(Sort::BitVec(64)), b_sort(Sort::BitVec(8)))
}
fn b_sort(s: Sort) -> Box<Sort> {
    Box::new(s)
}
fn check(f: &Formula, expected: Sort) -> Result<(), String> {
    let actual = trust_types::smt_logic::check_formula_sort(f).map_err(|e| format!("{e:?}"))?;
    if actual == expected { Ok(()) } else { Err(format!("expected {expected:?}, got {actual:?}")) }
}
fn width(width_bytes: u32) -> Result<(), String> {
    if (1..=8).contains(&width_bytes) {
        Ok(())
    } else {
        Err(format!("memory width {width_bytes} is outside the nonvolatile scalar fragment"))
    }
}

/// One array must be installed on BOTH sides at function entry. `scope` must
/// be unique within the enclosing certificate; this creates no entry premise.
#[must_use]
pub fn shared_entry_memory(scope: &str) -> Formula {
    Formula::Var(format!("CER_MEM0@{scope}"), memory_sort())
}

/// Nonvolatile little-endian scalar read, using the existing machine-compatible
/// byte constructor. Admission/root/validity obligations remain the consumer's.
pub fn load_le(memory: &Formula, address: &Formula, width_bytes: u32) -> Result<Formula, String> {
    check(memory, memory_sort())?;
    check(address, Sort::BitVec(64))?;
    width(width_bytes)?;
    Ok(load_bytes_le_formula(memory, address, width_bytes))
}

/// Nonvolatile little-endian scalar write with an EXACT-width value. This does
/// not silently truncate a wider value or invent a C ABI extension fact.
pub fn store_le(
    memory: Formula,
    address: &Formula,
    value: &Formula,
    width_bytes: u32,
) -> Result<Formula, String> {
    check(&memory, memory_sort())?;
    check(address, Sort::BitVec(64))?;
    width(width_bytes)?;
    check(value, Sort::BitVec(width_bytes * 8))?;
    Ok(store_bytes_le_formula(memory, address, value, width_bytes))
}

/// Access kinds have different coverage requirements (M3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessKind {
    Read,
    Write,
}

/// A reached byte range. The constructor checks sorts/width, not IR admission
/// or pointer validity. Callers must retain every access, including dead loads.
#[derive(Clone, Debug)]
pub struct PathAccess {
    kind: AccessKind,
    reach: Formula,
    address: Formula,
    width_bytes: u32,
}
impl PathAccess {
    pub(crate) fn kind(&self) -> AccessKind {
        self.kind
    }
    pub(crate) fn reach(&self) -> &Formula {
        &self.reach
    }
    pub(crate) fn address(&self) -> &Formula {
        &self.address
    }
    pub(crate) fn width_bytes(&self) -> u32 {
        self.width_bytes
    }

    pub fn new(
        kind: AccessKind,
        reach: Formula,
        address: Formula,
        width_bytes: u32,
    ) -> Result<Self, String> {
        check(&reach, Sort::Bool)?;
        check(&address, Sort::BitVec(64))?;
        width(width_bytes)?;
        Ok(Self { kind, reach, address, width_bytes })
    }
}

/// How a failed obligation may be used. This is deliberately not a grade.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CounterexampleUse {
    /// Failed coverage/separation is inconclusive, never a miscompile verdict.
    Inconclusive,
    /// M6 still needs a constructive legal witness with disjoint argument
    /// ranges. SAT alone must not be promoted to Refuted.
    RequiresLegalDisjointWitness,
}

/// An unproved formula and the conservative policy for a counterexample.
#[derive(Clone, Debug)]
pub struct PendingMemoryObligation {
    pub formula: Formula,
    pub counterexample_use: CounterexampleUse,
}

/// The private half-open frame `[entry_sp - bytes, entry_sp)`. No pointer/frame
/// separation or non-wrapping stack premise is assumed by this descriptor.
#[derive(Clone, Debug)]
pub struct PrivateFrame {
    entry_sp: Formula,
    bytes: u64,
}
impl PrivateFrame {
    pub fn new(entry_sp: Formula, bytes: u64) -> Result<Self, String> {
        check(&entry_sp, Sort::BitVec(64))?;
        Ok(Self { entry_sp, bytes })
    }

    /// A separate pending requirement: frame subtraction must not wrap.
    #[must_use]
    pub fn well_formed(&self) -> Formula {
        Formula::BvULe(b(bv(self.bytes)), b(self.entry_sp.clone()), 64)
    }
    fn outside(&self, address: Formula) -> Formula {
        Formula::Or(vec![
            Formula::BvULt(
                b(address.clone()),
                b(Formula::BvSub(b(self.entry_sp.clone()), b(bv(self.bytes)), 64)),
                64,
            ),
            Formula::BvULe(b(self.entry_sp.clone()), b(address), 64),
        ])
    }
}

/// Explicit M1′ requirements, per source access byte. These are returned as
/// obligations, NEVER inserted as an unrecorded assumption. A future consumer
/// must justify their use on defined IR executions and bind the frame to O5.
#[must_use]
pub fn frame_separation(
    source: &[PathAccess],
    frame: &PrivateFrame,
) -> Vec<PendingMemoryObligation> {
    let mut terms = vec![PendingMemoryObligation {
        formula: frame.well_formed(),
        counterexample_use: CounterexampleUse::Inconclusive,
    }];
    for access in source {
        for offset in 0..access.width_bytes {
            terms.push(PendingMemoryObligation {
                formula: implies(
                    access.reach.clone(),
                    frame.outside(byte_at(&access.address, offset)),
                ),
                counterexample_use: CounterexampleUse::Inconclusive,
            });
        }
    }
    terms
}

/// M3: each MACHINE non-frame byte must be covered by a reached source byte.
/// Writes require source writes; reads permit source reads or writes. Coverage
/// is independent of access order and width, allowing merged/reordered accesses.
/// Supply only accesses independently classified as non-frame; O5 still owns
/// private frame accesses. This function does not classify addresses as private.
#[must_use]
pub fn coverage(
    source: &[PathAccess],
    machine_nonframe: &[PathAccess],
) -> Vec<PendingMemoryObligation> {
    let mut terms = Vec::new();
    for access in machine_nonframe {
        for offset in 0..access.width_bytes {
            let address = byte_at(&access.address, offset);
            let mut alternatives = Vec::new();
            for candidate in source {
                if access.kind == AccessKind::Write && candidate.kind != AccessKind::Write {
                    continue;
                }
                for source_offset in 0..candidate.width_bytes {
                    alternatives.push(and(vec![
                        candidate.reach.clone(),
                        eq(address.clone(), byte_at(&candidate.address, source_offset)),
                    ]));
                }
            }
            terms.push(PendingMemoryObligation {
                formula: implies(access.reach.clone(), Formula::Or(alternatives)),
                counterexample_use: CounterexampleUse::Inconclusive,
            });
        }
    }
    terms
}

/// M4 (also M5's pre-call requirement): equality at an arbitrary outside-frame
/// byte on reached executions. `query` must be a FRESH unrestricted BV64 symbol
/// for a universal validity check, never a chosen sample. Frame well-formedness
/// and source separation are separate required obligations, not hidden premises.
/// No solver verdict or kernel claim is made here.
pub fn outside_memory_equal(
    reach: &Formula,
    source: &Formula,
    machine: &Formula,
    query: &Formula,
    frame: &PrivateFrame,
) -> Result<PendingMemoryObligation, String> {
    check(reach, Sort::Bool)?;
    check(source, memory_sort())?;
    check(machine, memory_sort())?;
    check(query, Sort::BitVec(64))?;
    let Formula::Var(query_name, _) = query else {
        return Err("outside-memory equality requires a fresh BV64 variable".into());
    };
    for input in [reach, source, machine, &frame.entry_sp] {
        let occurs = trust_types::any_formula_node(input, &mut |term| match term {
            Formula::Var(name, _) => name == query_name,
            Formula::SymVar(name, _) => name.as_str() == query_name,
            _ => false,
        });
        if occurs {
            return Err("outside-memory query already occurs in an input".into());
        }
    }
    Ok(PendingMemoryObligation {
        formula: implies(
            and(vec![reach.clone(), frame.outside(query.clone())]),
            eq(
                Formula::Select(b(source.clone()), b(query.clone())),
                Formula::Select(b(machine.clone()), b(query.clone())),
            ),
        ),
        counterexample_use: CounterexampleUse::RequiresLegalDisjointWitness,
    })
}

/// M5's shared OUTSIDE-frame post-call array. Both sides must use this same
/// value only AFTER exact call pairing, pre-call outside-memory equality and
/// the applicable callee obligations have closed. Preserved private-frame
/// overlays and monotone escape are separate obligations; this does not havoc
/// either executor and must not replace its existing rely by itself.
#[must_use]
pub fn shared_post_call_memory(scope: &str, paired_event: u64) -> Formula {
    Formula::Var(format!("CER_MEM@{scope}:{paired_event:x}"), memory_sort())
}

#[cfg(test)]
#[path = "cer_memory/tests.rs"]
mod tests;
