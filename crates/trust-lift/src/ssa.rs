// trust-lift: SSA construction via dominator-based algorithm
//
// Converts flat register assignments in lifted blocks into SSA form using
// the classic Cytron et al. dominator-based algorithm:
// 1. Compute dominance tree from CFG.
// 2. Compute dominance frontiers.
// 3. Place phi nodes at dominance frontiers of each definition.
// 4. Rename variables with versioned names.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::VecDeque;
use trust_types::fx::{FxHashMap, FxHashSet};

use crate::cfg::Cfg;
use crate::error::LiftError;

/// SSA-converted variable reference: (original name, version).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SsaVar {
    /// Original register/variable name (e.g., "x0", "x1").
    pub name: String,
    /// SSA version number (0 = initial, incremented per definition).
    pub version: u32,
}

/// A phi node placed at a block entry for SSA.
#[derive(Debug, Clone)]
pub struct PhiNode {
    /// The variable this phi defines.
    pub dest: SsaVar,
    /// Incoming values, one per predecessor block: (predecessor block index, variable version).
    pub operands: Vec<(usize, SsaVar)>,
}

/// SSA information for the entire function.
#[derive(Debug, Clone)]
pub struct SsaForm {
    /// Phi nodes per block index.
    pub phi_nodes: FxHashMap<usize, Vec<PhiNode>>,
    /// The latest version assigned to each variable.
    pub max_versions: FxHashMap<String, u32>,
}

/// Compute the immediate dominator tree using the iterative algorithm.
///
/// Returns a vector where `idom[b]` is the immediate dominator of block `b`.
/// The entry block dominates itself (by convention `idom[entry] = entry`).
pub(crate) fn compute_idom(cfg: &Cfg) -> Vec<usize> {
    let n = cfg.block_count();
    if n == 0 {
        return vec![];
    }

    let entry = cfg.entry;
    let mut idom = vec![usize::MAX; n];
    idom[entry] = entry;

    // Compute predecessors.
    let preds = compute_predecessors(cfg);

    // Iterative dominator computation (Cooper, Harvey, Kennedy).
    let rpo = reverse_postorder(cfg);
    let mut rpo_index = vec![0usize; n];
    for (i, &block) in rpo.iter().enumerate() {
        rpo_index[block] = i;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &b in &rpo {
            if b == entry {
                continue;
            }
            let mut new_idom = usize::MAX;
            for &p in &preds[b] {
                if idom[p] == usize::MAX {
                    continue;
                }
                if new_idom == usize::MAX {
                    new_idom = p;
                } else {
                    new_idom = intersect(&idom, &rpo_index, new_idom, p);
                }
            }
            if new_idom != idom[b] {
                idom[b] = new_idom;
                changed = true;
            }
        }
    }

    idom
}

/// Intersect helper for the iterative dominator algorithm.
fn intersect(idom: &[usize], rpo_index: &[usize], mut a: usize, mut b: usize) -> usize {
    while a != b {
        while rpo_index[a] > rpo_index[b] {
            a = idom[a];
        }
        while rpo_index[b] > rpo_index[a] {
            b = idom[b];
        }
    }
    a
}

/// Compute dominance frontiers from the idom tree.
pub(crate) fn compute_dom_frontiers(cfg: &Cfg, idom: &[usize]) -> Vec<FxHashSet<usize>> {
    let n = cfg.block_count();
    let mut df: Vec<FxHashSet<usize>> = vec![FxHashSet::default(); n];
    let preds = compute_predecessors(cfg);

    for b in 0..n {
        if preds[b].len() < 2 {
            continue;
        }
        for &p in &preds[b] {
            let mut runner = p;
            while runner != idom[b] && runner != usize::MAX {
                df[runner].insert(b);
                runner = idom[runner];
            }
        }
    }

    df
}

/// Compute predecessor lists from the CFG.
///
/// Predecessors are stored as positional indices into `cfg.blocks`, not as
/// `block.id` values.  The rename pass in [`rename_block`] searches these
/// lists by block index, so the two representations must agree.
pub(crate) fn compute_predecessors(cfg: &Cfg) -> Vec<Vec<usize>> {
    let n = cfg.block_count();
    let mut preds = vec![Vec::new(); n];

    for (block_idx, block) in cfg.blocks.iter().enumerate() {
        for &succ_addr in &block.successors {
            if let Some(succ_idx) = cfg.block_index(succ_addr) {
                preds[succ_idx].push(block_idx);
            }
        }
    }

    preds
}

/// Compute reverse postorder traversal of the CFG.
fn reverse_postorder(cfg: &Cfg) -> Vec<usize> {
    let n = cfg.block_count();
    let mut visited = vec![false; n];
    let mut postorder = Vec::with_capacity(n);

    fn dfs(cfg: &Cfg, block: usize, visited: &mut Vec<bool>, postorder: &mut Vec<usize>) {
        if block >= visited.len() || visited[block] {
            return;
        }
        visited[block] = true;
        for &succ_addr in &cfg.blocks[block].successors {
            if let Some(succ_idx) = cfg.block_index(succ_addr) {
                dfs(cfg, succ_idx, visited, postorder);
            }
        }
        postorder.push(block);
    }

    dfs(cfg, cfg.entry, &mut visited, &mut postorder);

    // Also visit unreachable blocks to ensure completeness.
    for i in 0..n {
        if !visited[i] {
            dfs(cfg, i, &mut visited, &mut postorder);
        }
    }

    postorder.reverse();
    postorder
}

/// Compute the children in the dominator tree (blocks immediately dominated by each block).
fn dom_tree_children(idom: &[usize]) -> Vec<Vec<usize>> {
    let n = idom.len();
    let mut children: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (b, &parent) in idom.iter().enumerate() {
        if parent != b && parent != usize::MAX {
            children[parent].push(b);
        }
    }
    children
}

/// Rename variables in SSA form using the dominator tree walk (Cytron et al.).
///
/// Updates phi node destination and operand versions to reflect actual reaching definitions.
fn rename_variables(
    cfg: &Cfg,
    idom: &[usize],
    defined_vars: &FxHashMap<usize, Vec<String>>,
    phi_nodes: &mut FxHashMap<usize, Vec<PhiNode>>,
    max_versions: &mut FxHashMap<String, u32>,
) {
    let children = dom_tree_children(idom);
    let preds = compute_predecessors(cfg);
    // Version stacks: top of stack = current reaching definition version.
    let mut stacks: FxHashMap<String, Vec<u32>> = FxHashMap::default();
    // Initialize stacks with version 0 (the entry/initial definition).
    for var in max_versions.keys() {
        stacks.entry(var.clone()).or_default().push(0);
    }

    // Reset max_versions to 0 so the rename pass assigns fresh versions.
    for v in max_versions.values_mut() {
        *v = 0;
    }

    rename_block(
        cfg.entry,
        cfg,
        &children,
        &preds,
        defined_vars,
        phi_nodes,
        max_versions,
        &mut stacks,
    );
}

/// Recursive rename for a single block in the dominator tree walk.
#[allow(clippy::too_many_arguments)]
fn rename_block(
    block: usize,
    cfg: &Cfg,
    children: &[Vec<usize>],
    preds: &[Vec<usize>],
    defined_vars: &FxHashMap<usize, Vec<String>>,
    phi_nodes: &mut FxHashMap<usize, Vec<PhiNode>>,
    max_versions: &mut FxHashMap<String, u32>,
    stacks: &mut FxHashMap<String, Vec<u32>>,
) {
    let mut push_count: FxHashMap<String, usize> = FxHashMap::default();

    // Process phi nodes at this block: each phi is a new definition.
    if let Some(phis) = phi_nodes.get_mut(&block) {
        for phi in phis.iter_mut() {
            let counter = max_versions.entry(phi.dest.name.clone()).or_insert(0);
            *counter += 1;
            phi.dest.version = *counter;
            let stack = stacks.entry(phi.dest.name.clone()).or_default();
            stack.push(*counter);
            *push_count.entry(phi.dest.name.clone()).or_insert(0) += 1;
        }
    }

    // Process ordinary definitions in this block.
    if let Some(vars) = defined_vars.get(&block) {
        for var in vars {
            let counter = max_versions.entry(var.clone()).or_insert(0);
            *counter += 1;
            let stack = stacks.entry(var.clone()).or_default();
            stack.push(*counter);
            *push_count.entry(var.clone()).or_insert(0) += 1;
        }
    }

    // Update phi operands in successor blocks.
    if block < cfg.blocks.len() {
        for &succ_addr in &cfg.blocks[block].successors {
            if let Some(succ_idx) = cfg.block_index(succ_addr)
                && let Some(succ_phis) = phi_nodes.get_mut(&succ_idx)
            {
                // Find which predecessor index we are in the successor's pred list.
                let pred_position = preds[succ_idx].iter().position(|&p| p == block);
                if let Some(pos) = pred_position {
                    for phi in succ_phis.iter_mut() {
                        if pos < phi.operands.len() {
                            let current_version = stacks
                                .get(&phi.operands[pos].1.name)
                                .and_then(|s| s.last().copied())
                                .unwrap_or(0);
                            phi.operands[pos].1.version = current_version;
                        }
                    }
                }
            }
        }
    }

    // Recurse into dominated children.
    let dom_children = children[block].clone();
    for child in dom_children {
        rename_block(child, cfg, children, preds, defined_vars, phi_nodes, max_versions, stacks);
    }

    // Pop stacks to restore state.
    for (var, count) in &push_count {
        if let Some(stack) = stacks.get_mut(var) {
            for _ in 0..*count {
                stack.pop();
            }
        }
    }
}

/// Construct SSA form for the given CFG.
///
/// This is a framework implementation that:
/// 1. Computes dominators and dominance frontiers.
/// 2. Places phi nodes at appropriate join points.
/// 3. Returns the SSA form with phi nodes per block.
///
/// Actual variable definitions are extracted from the lifted instructions
/// (placeholder: we use register names from the disassembled instructions).
pub(crate) fn construct_ssa(
    cfg: &Cfg,
    defined_vars: &FxHashMap<usize, Vec<String>>,
) -> Result<SsaForm, LiftError> {
    let idom = compute_idom(cfg);
    let dom_frontiers = compute_dom_frontiers(cfg, &idom);

    // Phase 1: Place phi nodes.
    // For each variable, find all blocks where it is defined, then place
    // phi nodes at the dominance frontier (iterated).
    let mut phi_nodes: FxHashMap<usize, Vec<PhiNode>> = FxHashMap::default();
    let mut max_versions: FxHashMap<String, u32> = FxHashMap::default();
    let preds = compute_predecessors(cfg);

    // Collect all variable names.
    let all_vars: FxHashSet<&String> = defined_vars.values().flatten().collect();

    for var_name in all_vars {
        // Blocks that define this variable.
        let mut def_blocks: FxHashSet<usize> = FxHashSet::default();
        for (&block_id, vars) in defined_vars {
            if vars.contains(var_name) {
                def_blocks.insert(block_id);
            }
        }

        // Iterated dominance frontier phi placement.
        let mut worklist: VecDeque<usize> = def_blocks.iter().copied().collect();
        let mut phi_placed: FxHashSet<usize> = FxHashSet::default();

        while let Some(block) = worklist.pop_front() {
            for &frontier_block in &dom_frontiers[block] {
                if phi_placed.insert(frontier_block) {
                    // Place a phi node.
                    let version = max_versions.entry(var_name.clone()).or_insert(0);
                    *version += 1;
                    let phi = PhiNode {
                        dest: SsaVar { name: var_name.clone(), version: *version },
                        operands: preds[frontier_block]
                            .iter()
                            .map(|&p| {
                                (
                                    p,
                                    SsaVar {
                                        name: var_name.clone(),
                                        version: 0, // Placeholder — renaming fills this in.
                                    },
                                )
                            })
                            .collect(),
                    };
                    phi_nodes.entry(frontier_block).or_default().push(phi);

                    // The phi itself is a definition, so add to worklist.
                    if def_blocks.insert(frontier_block) {
                        worklist.push_back(frontier_block);
                    }
                }
            }
        }
    }

    // Phase 2: Rename variables to fill in correct version numbers.
    rename_variables(cfg, &idom, defined_vars, &mut phi_nodes, &mut max_versions);

    Ok(SsaForm { phi_nodes, max_versions })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::LiftedBlock;

    fn make_diamond_cfg() -> Cfg {
        // Diamond CFG:
        //   0 (entry)
        //  / \
        // 1   2
        //  \ /
        //   3 (exit)
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1010, 0x1020],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![0x1030],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![0x1030],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 3,
            start_addr: 0x1030,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.entry = 0;
        cfg
    }

    #[test]
    fn test_compute_idom_diamond() {
        let cfg = make_diamond_cfg();
        let idom = compute_idom(&cfg);
        assert_eq!(idom[0], 0); // entry dominates itself
        assert_eq!(idom[1], 0); // 0 dominates 1
        assert_eq!(idom[2], 0); // 0 dominates 2
        assert_eq!(idom[3], 0); // 0 dominates 3 (join point)
    }

    #[test]
    fn test_compute_dom_frontiers_diamond() {
        let cfg = make_diamond_cfg();
        let idom = compute_idom(&cfg);
        let df = compute_dom_frontiers(&cfg, &idom);
        // Block 1's dominance frontier is {3} (the join point).
        assert!(df[1].contains(&3));
        // Block 2's dominance frontier is {3}.
        assert!(df[2].contains(&3));
        // Block 0 has no dominance frontier in a diamond.
        assert!(df[0].is_empty());
    }

    #[test]
    fn test_construct_ssa_phi_placement() {
        let cfg = make_diamond_cfg();
        let mut defined_vars = FxHashMap::default();
        // Variable "x0" defined in blocks 1 and 2.
        defined_vars.insert(1, vec!["x0".to_string()]);
        defined_vars.insert(2, vec!["x0".to_string()]);

        let ssa = construct_ssa(&cfg, &defined_vars).expect("SSA construction should succeed");

        // Block 3 should have a phi node for "x0".
        let phis = ssa.phi_nodes.get(&3).expect("block 3 should have phi nodes");
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].dest.name, "x0");
        // Two predecessors (blocks 1 and 2).
        assert_eq!(phis[0].operands.len(), 2);
        // Verify phi operands have correct versions (not the placeholder 0).
        // Blocks 1 and 2 each define x0 once, so operands should be version 1.
        for op in &phis[0].operands {
            assert_ne!(op.1.version, 0, "phi operand should have non-zero version after rename");
        }
    }

    #[test]
    fn test_predecessors_diamond() {
        let cfg = make_diamond_cfg();
        let preds = compute_predecessors(&cfg);
        assert!(preds[0].is_empty()); // entry has no predecessors
        assert_eq!(preds[1], vec![0]);
        assert_eq!(preds[2], vec![0]);
        let mut p3 = preds[3].clone();
        p3.sort();
        assert_eq!(p3, vec![1, 2]);
    }

    #[test]
    fn test_reverse_postorder_diamond() {
        let cfg = make_diamond_cfg();
        let rpo = reverse_postorder(&cfg);
        // Entry must come first.
        assert_eq!(rpo[0], 0);
        // Exit must come last.
        assert_eq!(*rpo.last().expect("non-empty"), 3);
    }

    /// Test phi operand versions in an if-else diamond where:
    ///   Block 0 (entry): defines x0
    ///   Block 1 (then):  redefines x0
    ///   Block 2 (else):  does NOT define x0 (inherits from block 0)
    ///   Block 3 (join):  phi(x0) with distinct versions from each arm
    #[test]
    fn test_phi_operand_versions_if_else() {
        let cfg = make_diamond_cfg();
        let mut defined_vars = FxHashMap::default();
        defined_vars.insert(0, vec!["x0".to_string()]); // entry defines x0
        defined_vars.insert(1, vec!["x0".to_string()]); // then-branch redefines x0
        // Block 2 does NOT define x0 — it inherits version from block 0.

        let ssa = construct_ssa(&cfg, &defined_vars).expect("SSA construction should succeed");

        let phis = ssa.phi_nodes.get(&3).expect("block 3 should have phi nodes");
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].dest.name, "x0");
        assert_eq!(phis[0].operands.len(), 2);

        // Both operands must have non-zero versions (the rename pass fills them in).
        for (pred, var) in &phis[0].operands {
            assert_ne!(var.version, 0, "phi operand from pred {} should not be version 0", pred,);
        }

        // The two operand versions must differ: one comes from the entry
        // definition (through block 2), the other from block 1's redefinition.
        let versions: Vec<u32> = phis[0].operands.iter().map(|(_, v)| v.version).collect();
        assert_ne!(
            versions[0], versions[1],
            "phi operands should carry different reaching-definition versions"
        );
    }

    fn make_loop_cfg() -> Cfg {
        // Loop CFG:
        //   0 (entry) -> 1 (header)
        //   1 -> 2 (body)
        //   2 -> 1 (back edge)
        //   1 -> 3 (exit)
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1010],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![0x1020, 0x1030],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 2,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![0x1010], // back edge to header
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 3,
            start_addr: 0x1030,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.entry = 0;
        cfg
    }

    /// Test phi operand versions in a loop where:
    ///   Block 0 (entry):  defines x0
    ///   Block 1 (header): join point with phi for x0
    ///   Block 2 (body):   redefines x0, back-edges to block 1
    ///   Block 3 (exit):   no definitions
    ///
    /// The phi at block 1 should have two operands:
    ///   - From block 0: the initial definition version
    ///   - From block 2: the loop body redefinition version
    ///     Both must be non-zero and distinct.
    #[test]
    fn test_phi_operand_versions_loop() {
        let cfg = make_loop_cfg();
        let mut defined_vars = FxHashMap::default();
        defined_vars.insert(0, vec!["x0".to_string()]); // entry defines x0
        defined_vars.insert(2, vec!["x0".to_string()]); // loop body redefines x0

        let ssa = construct_ssa(&cfg, &defined_vars).expect("SSA construction should succeed");

        // Block 1 (header) should have a phi node for x0.
        let phis = ssa.phi_nodes.get(&1).expect("loop header (block 1) should have phi nodes");
        assert_eq!(phis.len(), 1, "expected exactly one phi for x0 at loop header");
        assert_eq!(phis[0].dest.name, "x0");
        assert_eq!(phis[0].operands.len(), 2, "loop header has two predecessors");

        // Both operands must have non-zero versions.
        for (pred, var) in &phis[0].operands {
            assert_ne!(var.version, 0, "phi operand from pred {} should not be version 0", pred,);
        }

        // The two operand versions must differ: one from entry (block 0),
        // one from the loop body (block 2).
        let versions: Vec<u32> = phis[0].operands.iter().map(|(_, v)| v.version).collect();
        assert_ne!(
            versions[0], versions[1],
            "loop phi operands should carry different reaching-definition versions"
        );
    }

    /// Regression test: ensure compute_predecessors uses positional index,
    /// not block.id.  When block.id != positional index, the rename pass
    /// must still find the correct predecessor position.
    #[test]
    fn test_phi_operand_versions_mismatched_block_ids() {
        // Build a diamond where block.id values do NOT match their position
        // in cfg.blocks (ids are 10, 11, 12, 13 but indices are 0, 1, 2, 3).
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 10,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![0x1010, 0x1020],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 11,
            start_addr: 0x1010,
            instructions: vec![],
            successors: vec![0x1030],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 12,
            start_addr: 0x1020,
            instructions: vec![],
            successors: vec![0x1030],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 13,
            start_addr: 0x1030,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });
        cfg.entry = 0;

        // Use positional indices (0, 1, 2) as keys in defined_vars.
        let mut defined_vars = FxHashMap::default();
        defined_vars.insert(0, vec!["x0".to_string()]);
        defined_vars.insert(1, vec!["x0".to_string()]);
        defined_vars.insert(2, vec!["x0".to_string()]);

        let ssa = construct_ssa(&cfg, &defined_vars)
            .expect("SSA construction should succeed even with mismatched block ids");

        // Block 3 (index 3) should have a phi node for x0.
        let phis = ssa.phi_nodes.get(&3).expect("join block should have phi nodes");
        assert_eq!(phis.len(), 1);
        assert_eq!(phis[0].dest.name, "x0");

        // Both operands must have non-zero versions (the old bug would leave them at 0
        // because compute_predecessors stored block.id instead of block index).
        for (pred, var) in &phis[0].operands {
            assert_ne!(
                var.version, 0,
                "phi operand from pred {} should not be version 0 (block.id mismatch regression)",
                pred,
            );
        }
    }
}
