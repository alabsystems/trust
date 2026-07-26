// trust-symex ownership constraint generation
//
// Generates verification conditions from Rust's ownership rules.
// Produces Formula types that encode exclusivity, use-after-move,
// use-after-drop, and borrow lifetime constraints.
//
// Design: Issue #146, VISION.md Section 9 (Memory Abstraction)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use thiserror::Error;
use trust_types::{Formula, Sort, SourceSpan, Ty, VcKind, VerificationCondition};

use crate::region::{OwnershipKind, RegionError, RegionId, RegionMap, RegionState};

// ---------------------------------------------------------------------------
// Ownership constraint kinds
// ---------------------------------------------------------------------------

/// The kind of ownership constraint being checked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum OwnershipConstraintKind {
    /// No aliasing of mutable references (exclusivity).
    MutExclusivity { region_name: String, conflicting_borrows: Vec<String> },
    /// No use after move.
    UseAfterMove { region_name: String, used_at: String },
    /// No use after drop.
    UseAfterDrop { region_name: String, used_at: String },
    /// Borrow does not outlive its owner.
    BorrowLifetime { borrow_name: String, owner_name: String },
    /// Array bounds check for indexed access.
    ArrayBoundsCheck { array_name: String, length: u64 },
    /// Shared reference read-only constraint.
    SharedReadOnly { borrow_name: String },
}

impl OwnershipConstraintKind {
    /// Human-readable description.
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::MutExclusivity { region_name, conflicting_borrows } => {
                format!(
                    "mutable reference exclusivity: `{region_name}` conflicts with [{}]",
                    conflicting_borrows.join(", ")
                )
            }
            Self::UseAfterMove { region_name, used_at } => {
                format!("use after move: `{region_name}` used at `{used_at}`")
            }
            Self::UseAfterDrop { region_name, used_at } => {
                format!("use after drop: `{region_name}` used at `{used_at}`")
            }
            Self::BorrowLifetime { borrow_name, owner_name } => {
                format!("borrow `{borrow_name}` outlives owner `{owner_name}`")
            }
            Self::ArrayBoundsCheck { array_name, length } => {
                format!("array bounds check: `{array_name}` (length {length})")
            }
            Self::SharedReadOnly { borrow_name } => {
                format!("shared reference `{borrow_name}` is read-only")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Ownership constraint
// ---------------------------------------------------------------------------

/// A single ownership constraint with its formula and metadata.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OwnershipConstraint {
    /// What kind of constraint this is.
    pub kind: OwnershipConstraintKind,
    /// The function this constraint applies to.
    pub function: String,
    /// Source location.
    pub location: SourceSpan,
    /// The formula encoding the constraint.
    ///
    /// Convention: if this formula is SAT, the constraint is VIOLATED.
    /// An UNSAT result means the ownership rule holds.
    pub violation_formula: Formula,
}

impl OwnershipConstraint {
    /// Convert to a standard VerificationCondition.
    #[must_use]
    pub fn to_vc(&self) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: self.kind.description() },
            function: self.function.clone().into(),
            location: self.location.clone(),
            formula: self.violation_formula.clone(),
            contract_metadata: None,
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from ownership constraint generation.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum OwnershipError {
    #[error("region error: {0}")]
    Region(#[from] RegionError),

    #[error("cannot generate constraint: {reason}")]
    ConstraintGeneration { reason: String },
}

// ---------------------------------------------------------------------------
// Counterexample
// ---------------------------------------------------------------------------

/// A counterexample showing how an ownership rule can be violated.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OwnershipCounterexample {
    /// Which constraint was violated.
    pub constraint_kind: OwnershipConstraintKind,
    /// Variable assignments in the counterexample.
    pub assignments: BTreeMap<String, String>,
    /// Human-readable explanation of the violation.
    pub explanation: String,
}

impl std::fmt::Display for OwnershipCounterexample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Ownership violation: {}", self.constraint_kind.description())?;
        writeln!(f, "Explanation: {}", self.explanation)?;
        if !self.assignments.is_empty() {
            writeln!(f, "Assignments:")?;
            for (var, val) in &self.assignments {
                writeln!(f, "  {var} = {val}")?;
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// OwnershipChecker
// ---------------------------------------------------------------------------

/// Generates ownership verification conditions from a RegionMap.
///
/// This is the main entry point for ownership constraint generation.
/// Given the current state of regions, it produces a set of VCs that
/// encode Rust's ownership rules as SMT formulas.
#[derive(Debug, Clone)]
pub struct OwnershipChecker {
    /// The function being checked.
    function_name: String,
    /// Accumulated constraints.
    constraints: Vec<OwnershipConstraint>,
    /// Accumulated counterexamples (from static checks).
    counterexamples: Vec<OwnershipCounterexample>,
}

impl OwnershipChecker {
    /// Create a new ownership checker for the given function.
    #[must_use]
    pub fn new(function_name: impl Into<String>) -> Self {
        Self {
            function_name: function_name.into(),
            constraints: Vec::new(),
            counterexamples: Vec::new(),
        }
    }

    /// Returns the accumulated constraints.
    #[must_use]
    pub fn constraints(&self) -> &[OwnershipConstraint] {
        &self.constraints
    }

    /// Returns the accumulated counterexamples.
    #[must_use]
    pub fn counterexamples(&self) -> &[OwnershipCounterexample] {
        &self.counterexamples
    }

    /// Convert all constraints to verification conditions.
    #[must_use]
    pub fn to_vcs(&self) -> Vec<VerificationCondition> {
        self.constraints.iter().map(|c| c.to_vc()).collect()
    }

    /// Check all ownership constraints on the current region map state.
    ///
    /// This is a comprehensive check that generates VCs for:
    /// - Mutable reference exclusivity
    /// - Use-after-move detection
    /// - Use-after-drop detection
    /// - Borrow lifetime containment
    pub fn check_all(&mut self, regions: &RegionMap) {
        self.check_exclusivity(regions);
        self.check_use_after_move(regions);
        self.check_use_after_drop(regions);
        self.check_borrow_lifetimes(regions);
    }

    /// Check mutable reference exclusivity.
    ///
    /// For each live mutable borrow, verify there are no other active borrows
    /// on the same owner.
    pub fn check_exclusivity(&mut self, regions: &RegionMap) {
        for region in regions.live_regions() {
            if region.ownership() != OwnershipKind::MutBorrow {
                continue;
            }

            let Some(parent_id) = region.parent() else {
                continue;
            };

            // Check for conflicting borrows on the same parent.
            let shared = regions.active_shared_borrows(parent_id);
            let mut_borrows = regions.active_mut_borrows(parent_id);

            // Filter out self.
            let other_mut: Vec<RegionId> =
                mut_borrows.into_iter().filter(|&id| id != region.id()).collect();

            let mut conflicting_names = Vec::new();
            for &id in shared.iter().chain(other_mut.iter()) {
                if let Ok(r) = regions.get_region(id) {
                    conflicting_names.push(r.name().to_owned());
                }
            }

            if !conflicting_names.is_empty() {
                let kind = OwnershipConstraintKind::MutExclusivity {
                    region_name: region.name().to_owned(),
                    conflicting_borrows: conflicting_names.clone(),
                };

                // Formula: the exclusivity constraint is violated when there
                // are concurrent borrows. Encode as: True (always violated).
                let formula = Formula::Bool(true);

                self.constraints.push(OwnershipConstraint {
                    kind: kind.clone(),
                    function: self.function_name.clone(),
                    location: SourceSpan::default(),
                    violation_formula: formula,
                });

                self.counterexamples.push(OwnershipCounterexample {
                    constraint_kind: kind,
                    assignments: BTreeMap::new(),
                    explanation: format!(
                        "Mutable reference `{}` coexists with borrows: [{}]",
                        region.name(),
                        conflicting_names.join(", ")
                    ),
                });
            }
        }
    }

    /// Check for use-after-move violations.
    ///
    /// Any region in the `Moved` state that is still referenced
    /// (has a name mapping) indicates a potential use-after-move.
    pub fn check_use_after_move(&mut self, regions: &RegionMap) {
        for region in regions.all_regions() {
            if region.state() != RegionState::Moved {
                continue;
            }

            let kind = OwnershipConstraintKind::UseAfterMove {
                region_name: region.name().to_owned(),
                used_at: self.function_name.clone(),
            };

            // Generate a formula variable for the moved value.
            // The violation is: the moved region is accessed.
            // We encode this as an assertion that the "valid" flag is false.
            let valid_var = Formula::Var(format!("{}_valid", region.name()), Sort::Bool);
            let violation = Formula::Not(Box::new(valid_var));

            self.constraints.push(OwnershipConstraint {
                kind,
                function: self.function_name.clone(),
                location: SourceSpan::default(),
                violation_formula: violation,
            });
        }
    }

    /// Check for use-after-drop violations.
    pub fn check_use_after_drop(&mut self, regions: &RegionMap) {
        for region in regions.all_regions() {
            if region.state() != RegionState::Dropped {
                continue;
            }

            let kind = OwnershipConstraintKind::UseAfterDrop {
                region_name: region.name().to_owned(),
                used_at: self.function_name.clone(),
            };

            let valid_var = Formula::Var(format!("{}_alive", region.name()), Sort::Bool);
            let violation = Formula::Not(Box::new(valid_var));

            self.constraints.push(OwnershipConstraint {
                kind,
                function: self.function_name.clone(),
                location: SourceSpan::default(),
                violation_formula: violation,
            });
        }
    }

    /// Check borrow lifetime containment.
    ///
    /// Each borrow must not outlive its owner. In the region model,
    /// this is enforced by scope depth: a borrow's scope must be >= its owner's.
    pub fn check_borrow_lifetimes(&mut self, regions: &RegionMap) {
        for region in regions.live_regions() {
            if !matches!(region.ownership(), OwnershipKind::SharedBorrow | OwnershipKind::MutBorrow)
            {
                continue;
            }

            let Some(parent_id) = region.parent() else {
                continue;
            };

            let Ok(parent) = regions.get_region(parent_id) else {
                continue;
            };

            // The borrow's scope should be >= the owner's scope (created later / more nested).
            if region.scope_depth() < parent.scope_depth() {
                let kind = OwnershipConstraintKind::BorrowLifetime {
                    borrow_name: region.name().to_owned(),
                    owner_name: parent.name().to_owned(),
                };

                // Encode as: borrow_scope < owner_scope (violation).
                let borrow_scope = Formula::Int(region.scope_depth() as i128);
                let owner_scope = Formula::Int(parent.scope_depth() as i128);
                let violation = Formula::Lt(Box::new(borrow_scope), Box::new(owner_scope));

                self.constraints.push(OwnershipConstraint {
                    kind: kind.clone(),
                    function: self.function_name.clone(),
                    location: SourceSpan::default(),
                    violation_formula: violation,
                });

                self.counterexamples.push(OwnershipCounterexample {
                    constraint_kind: kind,
                    assignments: BTreeMap::new(),
                    explanation: format!(
                        "Borrow `{}` (scope {}) outlives owner `{}` (scope {})",
                        region.name(),
                        region.scope_depth(),
                        parent.name(),
                        parent.scope_depth(),
                    ),
                });
            }
        }
    }

    /// Generate an array bounds check VC for a symbolic index access.
    pub fn check_array_bounds(
        &mut self,
        regions: &RegionMap,
        array_id: RegionId,
        index_formula: &Formula,
    ) -> Result<(), OwnershipError> {
        let region = regions.get_region(array_id).map_err(OwnershipError::Region)?;

        let length = match &region.ty() {
            Ty::Array { len, .. } => *len,
            _ => {
                return Err(OwnershipError::ConstraintGeneration {
                    reason: format!("region `{}` is not an array type", region.name()),
                });
            }
        };

        let violation =
            regions.array_bounds_check_formula(array_id, index_formula).ok_or_else(|| {
                OwnershipError::ConstraintGeneration {
                    reason: "failed to generate bounds check formula".into(),
                }
            })?;

        let kind = OwnershipConstraintKind::ArrayBoundsCheck {
            array_name: region.name().to_owned(),
            length,
        };

        self.constraints.push(OwnershipConstraint {
            kind,
            function: self.function_name.clone(),
            location: SourceSpan::default(),
            violation_formula: violation,
        });

        Ok(())
    }

    /// Generate a shared read-only constraint VC.
    ///
    /// Encodes that a shared reference region should not be written to.
    pub fn check_shared_read_only(
        &mut self,
        regions: &RegionMap,
        borrow_id: RegionId,
    ) -> Result<(), OwnershipError> {
        let region = regions.get_region(borrow_id).map_err(OwnershipError::Region)?;

        if region.ownership() != OwnershipKind::SharedBorrow {
            return Ok(()); // Not a shared borrow -- nothing to check.
        }

        let kind =
            OwnershipConstraintKind::SharedReadOnly { borrow_name: region.name().to_owned() };

        // The violation formula: writing to a shared ref is always a violation.
        let written_var = Formula::Var(format!("{}_written", region.name()), Sort::Bool);

        self.constraints.push(OwnershipConstraint {
            kind,
            function: self.function_name.clone(),
            location: SourceSpan::default(),
            violation_formula: written_var,
        });

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Convenience: generate all ownership VCs for a RegionMap snapshot
// ---------------------------------------------------------------------------

/// Generate all ownership verification conditions for a function.
///
/// This is the main entry point: given a RegionMap representing the state
/// after symbolic execution of a function, produce the set of VCs that
/// encode Rust's ownership and borrowing rules.
#[must_use]
pub fn generate_ownership_vcs(
    function_name: &str,
    regions: &RegionMap,
) -> Vec<VerificationCondition> {
    let mut checker = OwnershipChecker::new(function_name);
    checker.check_all(regions);
    checker.to_vcs()
}

/// Check a RegionMap for static ownership violations.
///
/// Returns counterexamples for any violations found without needing
/// an SMT solver (these are structural violations detectable from
/// the region graph alone).
#[must_use]
pub fn check_static_ownership(
    function_name: &str,
    regions: &RegionMap,
) -> Vec<OwnershipCounterexample> {
    let mut checker = OwnershipChecker::new(function_name);
    checker.check_all(regions);
    checker.counterexamples().to_vec()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::RegionMap;
    use crate::state::SymbolicValue;
    use trust_types::Ty;

    fn i32_ty() -> Ty {
        Ty::i32()
    }

    fn array_i32_ty(len: u64) -> Ty {
        Ty::Array { elem: Box::new(i32_ty()), len }
    }

    // --- Basic checker creation ---

    #[test]
    fn test_checker_creation() {
        let checker = OwnershipChecker::new("test_fn");
        assert!(checker.constraints().is_empty());
        assert!(checker.counterexamples().is_empty());
    }

    // --- No violations for clean state ---

    #[test]
    fn test_no_violations_clean_state() {
        let mut regions = RegionMap::new();
        regions.bind_param("x", i32_ty());
        regions.bind_param("y", i32_ty());

        let vcs = generate_ownership_vcs("test_fn", &regions);
        assert!(vcs.is_empty(), "clean state should have no violations");
    }

    // --- Use-after-move detection ---

    #[test]
    fn test_use_after_move_detected() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        let _y = regions.move_value(x, "y").expect("move");

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_use_after_move(&regions);

        assert_eq!(checker.constraints().len(), 1);
        assert!(matches!(
            &checker.constraints()[0].kind,
            OwnershipConstraintKind::UseAfterMove { region_name, .. } if region_name == "x"
        ));
    }

    // --- Use-after-drop detection ---

    #[test]
    fn test_use_after_drop_detected() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        regions.drop_region(x).expect("drop");

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_use_after_drop(&regions);

        assert_eq!(checker.constraints().len(), 1);
        assert!(matches!(
            &checker.constraints()[0].kind,
            OwnershipConstraintKind::UseAfterDrop { region_name, .. } if region_name == "x"
        ));
    }

    // --- Borrow lifetime ---

    #[test]
    fn test_borrow_lifetime_ok() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        regions.enter_scope();
        let _borrow = regions.borrow_shared("ref_x", x).expect("borrow");

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_borrow_lifetimes(&regions);

        // Borrow scope (1) >= owner scope (0) -- no violation.
        assert!(checker.constraints().is_empty());
        assert!(checker.counterexamples().is_empty());
    }

    // --- Exclusivity ---

    #[test]
    fn test_exclusivity_no_violation() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        let _mb = regions.borrow_mut("mut_x", x).expect("mut borrow");

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_exclusivity(&regions);

        // Single mutable borrow -- no conflict.
        assert!(checker.constraints().is_empty());
    }

    // --- Array bounds check ---

    #[test]
    fn test_array_bounds_check_vc() {
        let mut regions = RegionMap::new();
        let arr = regions.bind_owned("arr", array_i32_ty(4), SymbolicValue::Symbol("arr".into()));

        let mut checker = OwnershipChecker::new("test_fn");
        let idx = Formula::Var("i".into(), Sort::Int);
        checker.check_array_bounds(&regions, arr, &idx).expect("bounds check");

        assert_eq!(checker.constraints().len(), 1);
        assert!(matches!(
            &checker.constraints()[0].kind,
            OwnershipConstraintKind::ArrayBoundsCheck { length: 4, .. }
        ));
    }

    #[test]
    fn test_array_bounds_check_non_array_fails() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());

        let mut checker = OwnershipChecker::new("test_fn");
        let idx = Formula::Var("i".into(), Sort::Int);
        let err = checker.check_array_bounds(&regions, x, &idx).expect_err("not an array");
        assert!(matches!(err, OwnershipError::ConstraintGeneration { .. }));
    }

    // --- Shared read-only ---

    #[test]
    fn test_shared_read_only_vc() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        let borrow = regions.borrow_shared("ref_x", x).expect("borrow");

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_shared_read_only(&regions, borrow).expect("check");

        assert_eq!(checker.constraints().len(), 1);
        assert!(matches!(
            &checker.constraints()[0].kind,
            OwnershipConstraintKind::SharedReadOnly { borrow_name } if borrow_name == "ref_x"
        ));
    }

    #[test]
    fn test_shared_read_only_skips_owned() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_shared_read_only(&regions, x).expect("check");

        // Owned region -- no shared read-only constraint generated.
        assert!(checker.constraints().is_empty());
    }

    // --- to_vc conversion ---

    #[test]
    fn test_constraint_to_vc() {
        let constraint = OwnershipConstraint {
            kind: OwnershipConstraintKind::UseAfterMove {
                region_name: "x".into(),
                used_at: "fn_test".into(),
            },
            function: "fn_test".into(),
            location: SourceSpan::default(),
            violation_formula: Formula::Bool(true),
        };

        let vc = constraint.to_vc();
        assert_eq!(vc.function, "fn_test");
        assert!(matches!(vc.kind, VcKind::Assertion { .. }));
    }

    // --- Counterexample display ---

    #[test]
    fn test_counterexample_display() {
        let mut assignments = BTreeMap::new();
        assignments.insert("x".into(), "42".into());

        let cex = OwnershipCounterexample {
            constraint_kind: OwnershipConstraintKind::UseAfterMove {
                region_name: "x".into(),
                used_at: "line 10".into(),
            },
            assignments,
            explanation: "x was moved on line 5".into(),
        };

        let display = format!("{cex}");
        assert!(display.contains("use after move"));
        assert!(display.contains("x = 42"));
        assert!(display.contains("x was moved on line 5"));
    }

    // --- check_all comprehensive ---

    #[test]
    fn test_check_all_comprehensive() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        let y = regions.bind_param("y", i32_ty());

        // Move x, drop y.
        let _z = regions.move_value(x, "z").expect("move");
        regions.drop_region(y).expect("drop");

        let mut checker = OwnershipChecker::new("test_fn");
        checker.check_all(&regions);

        // Should find use-after-move for x and use-after-drop for y.
        let move_violations: Vec<_> = checker
            .constraints()
            .iter()
            .filter(|c| matches!(&c.kind, OwnershipConstraintKind::UseAfterMove { .. }))
            .collect();
        assert_eq!(move_violations.len(), 1);

        let drop_violations: Vec<_> = checker
            .constraints()
            .iter()
            .filter(|c| matches!(&c.kind, OwnershipConstraintKind::UseAfterDrop { .. }))
            .collect();
        assert_eq!(drop_violations.len(), 1);
    }

    // --- generate_ownership_vcs convenience ---

    #[test]
    fn test_generate_ownership_vcs() {
        let mut regions = RegionMap::new();
        let x = regions.bind_param("x", i32_ty());
        let _y = regions.move_value(x, "y").expect("move");

        let vcs = generate_ownership_vcs("test_fn", &regions);
        assert!(!vcs.is_empty());
        assert!(vcs.iter().all(|vc| vc.function == "test_fn"));
    }

    // --- check_static_ownership convenience ---

    #[test]
    fn test_check_static_ownership_clean() {
        let mut regions = RegionMap::new();
        regions.bind_param("x", i32_ty());

        let cexs = check_static_ownership("test_fn", &regions);
        assert!(cexs.is_empty());
    }

    // --- Constraint kind description ---

    #[test]
    fn test_constraint_kind_descriptions() {
        let kinds = vec![
            OwnershipConstraintKind::MutExclusivity {
                region_name: "r".into(),
                conflicting_borrows: vec!["b1".into(), "b2".into()],
            },
            OwnershipConstraintKind::UseAfterMove {
                region_name: "x".into(),
                used_at: "line 5".into(),
            },
            OwnershipConstraintKind::UseAfterDrop {
                region_name: "y".into(),
                used_at: "line 10".into(),
            },
            OwnershipConstraintKind::BorrowLifetime {
                borrow_name: "ref_x".into(),
                owner_name: "x".into(),
            },
            OwnershipConstraintKind::ArrayBoundsCheck { array_name: "arr".into(), length: 4 },
            OwnershipConstraintKind::SharedReadOnly { borrow_name: "ref_x".into() },
        ];

        for kind in &kinds {
            let desc = kind.description();
            assert!(!desc.is_empty(), "description should not be empty");
        }

        assert!(kinds[0].description().contains("exclusivity"));
        assert!(kinds[1].description().contains("use after move"));
        assert!(kinds[2].description().contains("use after drop"));
        assert!(kinds[3].description().contains("outlives"));
        assert!(kinds[4].description().contains("bounds check"));
        assert!(kinds[5].description().contains("read-only"));
    }

    // --- OwnershipError display ---

    #[test]
    fn test_ownership_error_display() {
        let err = OwnershipError::ConstraintGeneration { reason: "test reason".into() };
        assert!(err.to_string().contains("test reason"));

        let region_err = RegionError::RegionNotFound { id: 0, name: "x".into() };
        let err2 = OwnershipError::Region(region_err);
        assert!(err2.to_string().contains("region"));
    }

    // --- Complex scenario: function with borrows and moves ---

    #[test]
    fn test_complex_scenario_function_with_borrows() {
        // Simulates: fn process(data: Vec<i32>) -> i32 {
        //     let ref_data = &data;   // shared borrow
        //     let first = ref_data[0]; // read through borrow
        //     drop(ref_data);          // (scope ends)
        //     let owned = data;        // move
        //     first
        // }
        let mut regions = RegionMap::new();
        let data = regions.bind_param("data", array_i32_ty(10));

        // Shared borrow.
        regions.enter_scope();
        let ref_data = regions.borrow_shared("ref_data", data).expect("borrow");

        // Read through borrow (verify accessible).
        assert!(regions.read(ref_data).is_ok());

        // Exit scope expires borrow.
        regions.exit_scope();

        // Move data.
        let _owned = regions.move_value(data, "owned").expect("move");

        // Check: use-after-move for data, no other issues.
        let mut checker = OwnershipChecker::new("process");
        checker.check_all(&regions);

        // data is moved (use-after-move detected as a region in Moved state),
        // ref_data is expired.
        let move_vcs: Vec<_> = checker
            .constraints()
            .iter()
            .filter(|c| matches!(&c.kind, OwnershipConstraintKind::UseAfterMove { .. }))
            .collect();
        assert_eq!(move_vcs.len(), 1);
    }

    // --- Clamp scenario VCs ---

    #[test]
    fn test_clamp_scenario_no_ownership_violations() {
        // fn clamp(x: i32, lo: i32, hi: i32) -> i32
        // Pure function: no moves, no drops, no borrows.
        let mut regions = RegionMap::new();
        regions.bind_param("x", i32_ty());
        regions.bind_param("lo", i32_ty());
        regions.bind_param("hi", i32_ty());

        let cexs = check_static_ownership("clamp", &regions);
        assert!(cexs.is_empty(), "clamp should have no ownership violations");

        let vcs = generate_ownership_vcs("clamp", &regions);
        assert!(vcs.is_empty(), "clamp should generate no ownership VCs");
    }
}
