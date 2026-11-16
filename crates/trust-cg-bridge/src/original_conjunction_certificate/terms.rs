//! Compact, bounded transport of the actual original CIC goal and proof.
//!
//! Validation here establishes wire shape and binder scope only. It is NOT a
//! type check, proof verdict, environment admission or subject binding. The
//! caller must restore these terms into its independently rebuilt environment
//! and check the RETAINED proof against the independently expected goal.

use std::collections::BTreeSet;
use std::io::{self, Write};

use serde::{Deserialize, Serialize};

const VERSION: u32 = 1;
const MAX_NODES: usize = 16_384;
const MAX_DEPTH: usize = 256;
const MAX_EXPANDED: usize = 1_000_000;
const MAX_NAME_BYTES: usize = 1024 * 1024;
// Original variable names include injective UTF-8 encodings of object/symbol
// identities. Bound the whole name population as well as each component; do
// not inherit the exact-two-register scalar diagnostic's 256-byte name limit.
const MAX_COMPONENT_BYTES: usize = 64 * 1024;
const MAX_NAME_PARTS: usize = 16;
const MAX_UNIVERSES: usize = 4;
const MAX_UNIVERSE: u8 = 4;
const MAX_PACKET_BYTES: usize = 4 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "component", deny_unknown_fields)]
enum NamePart {
    Str { value: String },
    Num { value: u64 },
}

// This version accepts only the binders emitted by the bounded original-term
// reflector. Flags are represented explicitly and checked, never erased or
// silently replaced by unrestricted explicit binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum BinderInfo {
    Default,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
enum Multiplicity {
    Many,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Binder {
    info: BinderInfo,
    mult: Multiplicity,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "node", deny_unknown_fields)]
enum TermNode {
    Const { name: Vec<NamePart>, universes: Vec<u8> },
    App { function: u32, argument: u32 },
    BVar { index: u32 },
    Lam { binder: Binder, domain: u32, body: u32 },
    Pi { binder: Binder, domain: u32, body: u32 },
}

/// Untrusted wire data. Deserialization grants no proof or environment trust.
/// Kernel-free builds can decode and validate shape; they cannot restore or
/// silently accept an independently checkable proof without kernel-recheck.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct TermPacket {
    version: u32,
    terms: Vec<TermNode>,
    goal: u32,
    proof: u32,
}

#[derive(Clone, Copy)]
struct Shape {
    depth: usize,
    expanded: usize,
    // Minimum number of enclosing binders needed for this term. This remains
    // correct for a shared BVar subtree occurring under different binders.
    binders_needed: u32,
}

struct CountWriter {
    bytes: usize,
}
impl Write for CountWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.bytes = self
            .bytes
            .checked_add(bytes.len())
            .filter(|n| *n <= MAX_PACKET_BYTES)
            .ok_or_else(|| io::Error::other("original CIC packet byte budget"))?;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl TermPacket {
    pub(crate) fn node_count(&self) -> usize {
        self.terms.len()
    }

    /// Count with a bounded writer, without allocating the expanded JSON tree.
    /// Callers must additionally bound the complete enclosing certificate wire.
    pub(crate) fn encoded_len(&self) -> Result<usize, String> {
        let mut output = CountWriter { bytes: 0 };
        serde_json::to_writer(&mut output, self).map_err(|e| e.to_string())?;
        Ok(output.bytes)
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.version != VERSION || self.terms.is_empty() || self.terms.len() > MAX_NODES {
            return Err("original CIC packet version/node population".into());
        }
        let mut seen = BTreeSet::new();
        let mut shapes: Vec<Shape> = Vec::with_capacity(self.terms.len());
        let mut name_bytes = 0usize;
        for (position, node) in self.terms.iter().enumerate() {
            if !seen.insert(node) {
                return Err("original CIC packet duplicate term node".into());
            }
            let child = |index: u32| -> Result<Shape, String> {
                let index = index as usize;
                if index >= position {
                    return Err("original CIC packet forward/cyclic/out-of-range reference".into());
                }
                shapes
                    .get(index)
                    .copied()
                    .ok_or_else(|| "original CIC packet invalid earlier reference".into())
            };
            let shape = match node {
                TermNode::Const { name, universes } => {
                    if name.is_empty()
                        || name.len() > MAX_NAME_PARTS
                        || universes.len() > MAX_UNIVERSES
                        || universes.iter().any(|n| *n > MAX_UNIVERSE)
                    {
                        return Err("original CIC packet name/universe bound".into());
                    }
                    for part in name {
                        if let NamePart::Str { value } = part {
                            if value.is_empty() || value.len() > MAX_COMPONENT_BYTES {
                                return Err("original CIC packet name component bound".into());
                            }
                            name_bytes = name_bytes
                                .checked_add(value.len())
                                .ok_or("original CIC packet name byte overflow")?;
                            if name_bytes > MAX_NAME_BYTES {
                                return Err("original CIC packet name byte budget".into());
                            }
                        }
                    }
                    Shape { depth: 1, expanded: 1, binders_needed: 0 }
                }
                TermNode::BVar { index } => Shape {
                    depth: 1,
                    expanded: 1,
                    binders_needed: index
                        .checked_add(1)
                        .ok_or("original CIC packet bound-variable overflow")?,
                },
                TermNode::App { function, argument } => {
                    let function = child(*function)?;
                    let argument = child(*argument)?;
                    Shape {
                        depth: 1 + function.depth.max(argument.depth),
                        expanded: function
                            .expanded
                            .checked_add(argument.expanded)
                            .and_then(|n| n.checked_add(1))
                            .ok_or("original CIC packet expansion overflow")?,
                        binders_needed: function.binders_needed.max(argument.binders_needed),
                    }
                }
                TermNode::Lam { binder: _, domain, body }
                | TermNode::Pi { binder: _, domain, body } => {
                    // Binder's only representable flags are exact Default/Many.
                    let domain = child(*domain)?;
                    let body = child(*body)?;
                    Shape {
                        depth: 1 + domain.depth.max(body.depth),
                        expanded: domain
                            .expanded
                            .checked_add(body.expanded)
                            .and_then(|n| n.checked_add(1))
                            .ok_or("original CIC packet binder expansion overflow")?,
                        binders_needed: domain
                            .binders_needed
                            .max(body.binders_needed.saturating_sub(1)),
                    }
                }
            };
            if shape.depth > MAX_DEPTH || shape.expanded > MAX_EXPANDED {
                return Err(format!(
                    "original CIC packet expansion/depth budget at node {position}: depth {}, expanded {}",
                    shape.depth, shape.expanded
                ));
            }
            shapes.push(shape);
        }
        let goal = self.goal as usize;
        let proof = self.proof as usize;
        for root in [goal, proof] {
            let shape = shapes.get(root).ok_or("original CIC packet root out of range")?;
            if shape.binders_needed != 0 {
                return Err("original CIC packet out-of-scope bound variable".into());
            }
        }
        let mut reached = BTreeSet::new();
        let mut pending = vec![goal, proof];
        while let Some(index) = pending.pop() {
            let node = self.terms.get(index).ok_or("original CIC packet invalid root/reference")?;
            if reached.insert(index) {
                match node {
                    TermNode::App { function, argument } => {
                        pending.extend([*function as usize, *argument as usize]);
                    }
                    TermNode::Lam { domain, body, .. } | TermNode::Pi { domain, body, .. } => {
                        pending.extend([*domain as usize, *body as usize]);
                    }
                    TermNode::Const { .. } | TermNode::BVar { .. } => {}
                }
            }
        }
        if reached.len() != self.terms.len() {
            return Err("original CIC packet unaccounted term node".into());
        }
        self.encoded_len()?;
        Ok(())
    }
}

#[cfg(feature = "kernel-recheck")]
mod kernel {
    use std::collections::BTreeMap;

    use clean_kernel::name::NameInner;
    use clean_kernel::{BinderData, Expr, ExprKind, Level, Name};

    use super::*;

    fn wire_name(name: &Name) -> Result<Vec<NamePart>, String> {
        let mut result = Vec::new();
        let mut current = name;
        loop {
            match current.inner() {
                NameInner::Anon => break,
                NameInner::Str(parent, value) => {
                    if value.is_empty() || value.len() > MAX_COMPONENT_BYTES {
                        return Err("original CIC packet name component bound".into());
                    }
                    result.push(NamePart::Str { value: value.to_string() });
                    current = parent;
                }
                NameInner::Num(parent, value) => {
                    result.push(NamePart::Num { value: *value });
                    current = parent;
                }
            }
            if result.len() > MAX_NAME_PARTS {
                return Err("original CIC packet name depth".into());
            }
        }
        if result.is_empty() {
            return Err("original CIC packet anonymous constant".into());
        }
        result.reverse();
        Ok(result)
    }

    fn universe(level: &Level) -> Result<u8, String> {
        let mut current = level;
        let mut n = 0;
        loop {
            match current {
                Level::Zero => return Ok(n),
                Level::Succ(parent) if n < MAX_UNIVERSE => {
                    n += 1;
                    current = parent;
                }
                _ => return Err("original CIC packet unsupported universe".into()),
            }
        }
    }

    fn binder(value: &BinderData) -> Result<Binder, String> {
        if value.info != clean_kernel::BinderInfo::Default
            || value.mult != clean_kernel::Multiplicity::Many
        {
            return Err("original CIC packet unsupported binder flags".into());
        }
        Ok(Binder { info: BinderInfo::Default, mult: Multiplicity::Many })
    }

    #[derive(Default)]
    struct Graph {
        nodes: Vec<TermNode>,
        canonical: BTreeMap<TermNode, u32>,
        memo: BTreeMap<usize, u32>,
        visited: usize,
        name_bytes: usize,
    }
    impl Graph {
        fn add(&mut self, expr: &Expr, depth: usize) -> Result<u32, String> {
            self.visited =
                self.visited.checked_add(1).ok_or("original CIC packet visit overflow")?;
            if depth > MAX_DEPTH || self.visited > MAX_EXPANDED {
                return Err(format!(
                    "original CIC packet construction budget: depth={depth}/{MAX_DEPTH} visits={}/{MAX_EXPANDED} nodes={}",
                    self.visited,
                    self.nodes.len()
                ));
            }
            let key = expr.kind() as *const ExprKind as usize;
            if let Some(index) = self.memo.get(&key) {
                return Ok(*index);
            }
            let node = match expr.kind() {
                ExprKind::Const(name, levels) => {
                    if levels.len() > MAX_UNIVERSES {
                        return Err("original CIC packet universe population".into());
                    }
                    TermNode::Const {
                        name: wire_name(name)?,
                        universes: levels.iter().map(universe).collect::<Result<_, _>>()?,
                    }
                }
                ExprKind::App(function, argument) => TermNode::App {
                    function: self.add(function, depth + 1)?,
                    argument: self.add(argument, depth + 1)?,
                },
                ExprKind::BVar(index) => TermNode::BVar { index: *index },
                ExprKind::Lam(flags, domain, body) => TermNode::Lam {
                    binder: binder(flags)?,
                    domain: self.add(domain, depth + 1)?,
                    body: self.add(body, depth + 1)?,
                },
                ExprKind::Pi(flags, domain, body) => TermNode::Pi {
                    binder: binder(flags)?,
                    domain: self.add(domain, depth + 1)?,
                    body: self.add(body, depth + 1)?,
                },
                _ => return Err("original CIC packet unsupported expression constructor".into()),
            };
            let index = if let Some(index) = self.canonical.get(&node) {
                *index
            } else {
                if self.nodes.len() >= MAX_NODES {
                    return Err("original CIC packet node budget".into());
                }
                if let TermNode::Const { name, .. } = &node {
                    for part in name {
                        if let NamePart::Str { value } = part {
                            self.name_bytes = self
                                .name_bytes
                                .checked_add(value.len())
                                .ok_or("original CIC packet name byte overflow")?;
                            if self.name_bytes > MAX_NAME_BYTES {
                                return Err("original CIC packet name byte budget".into());
                            }
                        }
                    }
                }
                let index = self.nodes.len() as u32;
                self.nodes.push(node.clone());
                self.canonical.insert(node, index);
                index
            };
            self.memo.insert(key, index);
            Ok(index)
        }
    }

    impl TermPacket {
        pub(crate) fn capture(goal: &Expr, proof: &Expr) -> Result<Self, String> {
            let mut graph = Graph::default();
            let goal = graph.add(goal, 0).map_err(|e| format!("{e} (original goal)"))?;
            let proof = graph.add(proof, 0).map_err(|e| format!("{e} (retained proof)"))?;
            let packet = Self { version: VERSION, terms: graph.nodes, goal, proof };
            packet.validate()?;
            Ok(packet)
        }

        pub(crate) fn restore(&self) -> Result<(Expr, Expr), String> {
            self.validate()?;
            let mut terms: Vec<Expr> = Vec::with_capacity(self.terms.len());
            for node in &self.terms {
                let expr = match node {
                    TermNode::Const { name, universes } => {
                        let mut exact = Name::anon();
                        for part in name {
                            exact = match part {
                                NamePart::Str { value } => exact.str(value),
                                NamePart::Num { value } => exact.num(*value),
                            };
                        }
                        let levels: Vec<Level> = universes
                            .iter()
                            .map(|n| {
                                let mut level = Level::zero();
                                for _ in 0..*n {
                                    level = Level::succ(level);
                                }
                                level
                            })
                            .collect();
                        Expr::const_(exact, levels)
                    }
                    TermNode::App { function, argument } => Expr::app(
                        terms[*function as usize].clone(),
                        terms[*argument as usize].clone(),
                    ),
                    TermNode::BVar { index } => Expr::bvar(*index),
                    TermNode::Lam { binder: _, domain, body } => Expr::lam(
                        BinderData::new(
                            clean_kernel::BinderInfo::Default,
                            clean_kernel::Multiplicity::Many,
                        ),
                        terms[*domain as usize].clone(),
                        terms[*body as usize].clone(),
                    ),
                    TermNode::Pi { binder: _, domain, body } => Expr::pi(
                        BinderData::new(
                            clean_kernel::BinderInfo::Default,
                            clean_kernel::Multiplicity::Many,
                        ),
                        terms[*domain as usize].clone(),
                        terms[*body as usize].clone(),
                    ),
                };
                terms.push(expr);
            }
            Ok((terms[self.goal as usize].clone(), terms[self.proof as usize].clone()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constant(name: &str) -> TermNode {
        TermNode::Const { name: vec![NamePart::Str { value: name.into() }], universes: vec![] }
    }
    // Wire-shape examples only; no test treats shape as a proof verdict.
    fn wire() -> TermPacket {
        TermPacket { version: VERSION, terms: vec![constant("Bool")], goal: 0, proof: 0 }
    }
    fn binder() -> Binder {
        Binder { info: BinderInfo::Default, mult: Multiplicity::Many }
    }

    #[test]
    fn names_roots_and_binder_flags_roundtrip_without_projection() {
        let mut packet = wire();
        packet.terms.push(TermNode::BVar { index: 0 });
        packet.terms.push(TermNode::Lam { binder: binder(), domain: 0, body: 1 });
        packet.terms.push(TermNode::Pi { binder: binder(), domain: 0, body: 1 });
        packet.goal = 3;
        packet.proof = 2;
        packet.validate().unwrap();
        let encoded = serde_json::to_vec(&packet).unwrap();
        assert_eq!(serde_json::from_slice::<TermPacket>(&encoded).unwrap(), packet);
        assert_eq!(packet.encoded_len().unwrap(), encoded.len());
        assert_ne!(NamePart::Num { value: 7 }, NamePart::Str { value: "7".into() });
        for field in ["info", "mult"] {
            let mut changed = serde_json::to_value(&packet).unwrap();
            changed["terms"][2]["binder"][field] = serde_json::Value::String("Implicit".into());
            assert!(serde_json::from_value::<TermPacket>(changed).is_err());
        }
    }

    #[test]
    fn bad_references_population_and_expansion_refuse() {
        for node in [
            TermNode::App { function: 1, argument: 0 },
            TermNode::App { function: 0, argument: u32::MAX },
        ] {
            let mut packet = wire();
            packet.terms.push(node);
            packet.proof = 1;
            assert!(packet.validate().is_err());
        }
        let mut packet = wire();
        packet.goal = u32::MAX;
        assert!(packet.validate().is_err());
        let mut packet = wire();
        packet.terms.push(constant("Nat"));
        assert!(packet.validate().unwrap_err().contains("unaccounted"));
        let mut packet = wire();
        packet.terms.push(packet.terms[0].clone());
        assert!(packet.validate().unwrap_err().contains("duplicate"));
        let mut packet = wire();
        for index in 0..20 {
            packet.terms.push(TermNode::App { function: index, argument: index });
        }
        packet.goal = 20;
        packet.proof = 20;
        assert!(packet.validate().unwrap_err().contains("budget"));
    }

    #[test]
    fn lambda_binds_only_its_body_and_each_root_must_be_closed() {
        let mut packet = wire();
        packet.terms.push(TermNode::BVar { index: 0 });
        packet.terms.push(TermNode::Lam { binder: binder(), domain: 0, body: 1 });
        packet.proof = 2;
        packet.validate().unwrap();
        packet.goal = 1;
        assert!(packet.validate().unwrap_err().contains("out-of-scope"));
        packet.goal = 0;
        packet.terms[2] = TermNode::Lam { binder: binder(), domain: 1, body: 0 };
        assert!(packet.validate().unwrap_err().contains("out-of-scope"));
        packet.terms[2] = TermNode::Pi { binder: binder(), domain: 0, body: 1 };
        packet.validate().unwrap();
        packet.terms[1] = TermNode::BVar { index: 1 };
        assert!(packet.validate().unwrap_err().contains("out-of-scope"));
    }

    #[cfg(feature = "kernel-recheck")]
    #[test]
    fn actual_cic_names_binders_and_terms_restore_exactly_without_producing_proofs() {
        use clean_kernel::{BinderData, BinderInfo, Expr, Multiplicity, Name};
        let ty = Expr::const_str("Bool");
        let flags = BinderData::new(BinderInfo::Default, Multiplicity::Many);
        let goal = Expr::pi(flags, ty.clone(), ty.clone());
        let proof = Expr::lam(flags, ty.clone(), Expr::bvar(0));
        let packet = TermPacket::capture(&goal, &proof).unwrap();
        assert_eq!(packet.restore().unwrap(), (goal.clone(), proof));
        let numeric = Expr::const_(Name::anon().str("owner").num(7), vec![]);
        let string = Expr::const_(Name::anon().str("owner").str("7"), vec![]);
        assert_ne!(
            TermPacket::capture(&numeric, &numeric).unwrap(),
            TermPacket::capture(&string, &string).unwrap()
        );
        let changed =
            Expr::lam(BinderData::new(BinderInfo::Implicit, Multiplicity::Many), ty, Expr::bvar(0));
        assert!(TermPacket::capture(&goal, &changed).is_err());
    }
}
