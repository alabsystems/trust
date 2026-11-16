//! Retained compact BVC instantiation, for a bounded unconditional U32 Add.
//!
//! This is diagnostic equality of the existing source and decoded-machine
//! models. Their correspondence to Trust-IR/AArch64, the reflector, BVC factory,
//! and kernel remain TCB inputs. It is not a frame, ABI, linker or G7 proof.
//! The original grade and the 2048-step refutation limit are unchanged.

use super::*;

const MODEL: u32 = 1;
const MAX_NODES: usize = 16384;
const MAX_DEPTH: usize = 256;
const MAX_EXPANDED: usize = 1_000_000;
const MAX_NAME_BYTES: usize = 1024 * 1024;
const MAX_CERTIFICATE_BYTES: usize = 2 * 1024 * 1024;

// Independent of the optional kernel dependency so ay-proofs-only builds can
// decode and explicitly refuse this evidence, never silently ignore the row.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "component", deny_unknown_fields)]
enum NamePart {
    Str { value: String },
    Num { value: u64 },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(tag = "node", deny_unknown_fields)]
enum TermNode {
    // Natural universe n denotes exactly Succ^n Zero, not a level parameter.
    Const { name: Vec<NamePart>, universes: Vec<u8> },
    App { function: u32, argument: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct CompactCertificate {
    model: u32,
    leaves: Vec<(String, u32)>,
    environment_sha256: String,
    terms: Vec<TermNode>,
    goal: u32,
    proof: u32,
}

impl CompactCertificate {
    pub(super) fn validate_graph(&self) -> Result<(), String> {
        if self.model != MODEL
            || self.terms.is_empty()
            || self.terms.len() > MAX_NODES
            || self.environment_sha256.len() != 64
            || !self
                .environment_sha256
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || self.leaves != [("X0".into(), 64), ("X1".into(), 64)]
        {
            return Err("compact certificate: model/environment/leaf/population mismatch".into());
        }
        let mut seen = BTreeSet::new();
        let mut depths: Vec<usize> = Vec::with_capacity(self.terms.len());
        let mut expanded: Vec<usize> = Vec::with_capacity(self.terms.len());
        let mut name_bytes = 0usize;
        for (index, node) in self.terms.iter().enumerate() {
            if !seen.insert(node) {
                return Err("compact certificate: duplicate term node".into());
            }
            let (depth, cost) = match node {
                TermNode::Const { name, universes } => {
                    if name.is_empty()
                        || name.len() > 16
                        || universes.len() > 4
                        || universes.iter().any(|n| *n > 4)
                    {
                        return Err("compact certificate: constant/level bound".into());
                    }
                    for part in name {
                        if let NamePart::Str { value } = part {
                            if value.is_empty() || value.len() > 256 {
                                return Err("compact certificate: name component bound".into());
                            }
                            name_bytes = name_bytes
                                .checked_add(value.len())
                                .ok_or("compact certificate: name overflow")?;
                            if name_bytes > MAX_NAME_BYTES {
                                return Err("compact certificate: name budget".into());
                            }
                        }
                    }
                    (1usize, 1usize)
                }
                TermNode::App { function, argument } => {
                    let f = *function as usize;
                    let a = *argument as usize;
                    if f >= index || a >= index {
                        return Err(
                            "compact certificate: forward/cyclic/out-of-range reference".into()
                        );
                    }
                    let depth = 1 + usize::max(depths[f], depths[a]);
                    let cost = expanded[f]
                        .checked_add(expanded[a])
                        .and_then(|n: usize| n.checked_add(1))
                        .ok_or("compact certificate: expanded term overflow")?;
                    (depth, cost)
                }
            };
            if depth > MAX_DEPTH || cost > MAX_EXPANDED {
                return Err("compact certificate: expanded term/depth budget".into());
            }
            depths.push(depth);
            expanded.push(cost);
        }
        let mut reachable = BTreeSet::new();
        let mut stack = vec![self.goal as usize, self.proof as usize];
        while let Some(index) = stack.pop() {
            let node =
                self.terms.get(index).ok_or("compact certificate: root/reference out of range")?;
            if reachable.insert(index) {
                if let TermNode::App { function, argument } = node {
                    stack.push(*function as usize);
                    stack.push(*argument as usize);
                }
            }
        }
        if reachable.len() != self.terms.len() {
            return Err("compact certificate: unaccounted term node".into());
        }
        encode(self, MAX_CERTIFICATE_BYTES)?;
        Ok(())
    }
}

#[cfg(not(feature = "kernel-recheck"))]
pub(super) fn capture(
    _source: &TrustIrGateSource,
    _object: &[u8],
    _arch: TrustCgTargetArch,
) -> Result<CompactCertificate, String> {
    Err("compact certificate: kernel-recheck feature unavailable".into())
}
#[cfg(not(feature = "kernel-recheck"))]
pub(super) fn replay(
    _source: &TrustIrGateSource,
    _object: &[u8],
    _arch: TrustCgTargetArch,
    _certificate: &CompactCertificate,
) -> Result<(), String> {
    Err("compact certificate: kernel-recheck feature unavailable".into())
}

#[cfg(feature = "kernel-recheck")]
pub(super) use kernel::{capture, replay};

#[cfg(feature = "kernel-recheck")]
mod kernel {
    use std::collections::BTreeMap;

    use clean_kernel::name::NameInner;
    use clean_kernel::{Declaration, Environment, Expr, ExprKind, Level, Name, TypeChecker};
    use trust_types::Sort;

    use super::*;
    use crate::verify_output_instantiate::{
        ReflectCtx, discharge_env, kx, reflect_formula, run_recheck_thread,
    };

    fn qualified_obligation(
        source: &TrustIrGateSource,
        object: &[u8],
        arch: TrustCgTargetArch,
    ) -> Result<GateObligation, String> {
        encode(&source.module, MAX_PART_BYTES)?;
        scalar_certificate::qualify_source(source)?;
        scalar_certificate::qualify_machine(source, object, arch)?;
        let function = source
            .module
            .function_by_id(source.func_id)
            .ok_or("compact certificate: missing function")?;
        let signature = source
            .module
            .func_types
            .get(function.ty.index() as usize)
            .ok_or("compact certificate: missing signature")?;
        let block = &function.blocks[0];
        if signature.params != [trust_ir::Ty::U32, trust_ir::Ty::U32]
            || signature.returns != [trust_ir::Ty::U32]
            || block.body.len() != 2
        {
            return Err(
                "compact certificate: only exact two-parameter U32 Add/Return is supported".into(),
            );
        }
        match (&block.body[0].inst, &block.body[1].inst) {
            (
                trust_ir::inst::Inst::BinOp {
                    op: trust_ir::inst::BinOp::Add,
                    ty: trust_ir::Ty::U32,
                    lhs,
                    rhs,
                },
                trust_ir::inst::Inst::Return { values },
            ) if *lhs == block.params[0].0
                && *rhs == block.params[1].0
                && values == &block.body[0].results => {}
            _ => {
                return Err(
                    "compact certificate: unsupported source computation or parameter ownership"
                        .into(),
                );
            }
        }
        let obligation = trust_ir_gate_obligation(source, object, arch)?;
        if obligation.spec_reach != Formula::Bool(true)
            || obligation.machine_reach != Formula::Bool(true)
            || !obligation.ambient_pre.is_empty()
            || !obligation.spec_side_conditions.is_empty()
            || !obligation.abi_residue.is_empty()
        {
            return Err("compact certificate: conditional/effect/modeling obligations".into());
        }
        qualify_formulas(&obligation)?;
        Ok(obligation)
    }

    // Every constructor is checked BEFORE using the existing reflector. In
    // particular its extract-over-zero-extension identity ignores `high`, so
    // this caller must prove that the slice has EXACTLY the original width.
    pub(super) fn formula_width(
        formula: &Formula,
        nodes: &mut usize,
        depth: usize,
        leaves: &mut BTreeSet<(String, u32)>,
        zeroext_child: bool,
    ) -> Result<u32, String> {
        *nodes += 1;
        if *nodes > 512 || depth > 64 {
            return Err("compact certificate: formula population/depth budget".into());
        }
        let width = match formula {
            Formula::Var(name, Sort::BitVec(64)) if name == "X0" || name == "X1" => {
                leaves.insert((name.clone(), 64));
                64
            }
            Formula::BitVec { value, width: 32 | 64 } if *value == 0 => {
                if let Formula::BitVec { width, .. } = formula { *width } else { unreachable!() }
            }
            Formula::BvAdd(left, right, width) | Formula::BvOr(left, right, width) => {
                if matches!(formula, Formula::BvOr(..))
                    && !matches!(&**left, Formula::BitVec { value: 0, .. })
                {
                    return Err(
                        "compact certificate: only zero-left OR wrappers are supported".into()
                    );
                }
                let l = formula_width(left, nodes, depth + 1, leaves, false)?;
                let r = formula_width(right, nodes, depth + 1, leaves, false)?;
                if l != *width || r != *width || !matches!(width, 32 | 64) {
                    return Err("compact certificate: arithmetic width mismatch".into());
                }
                *width
            }
            Formula::BvZeroExt(inner, extra) if zeroext_child => {
                let width = formula_width(inner, nodes, depth + 1, leaves, false)?;
                if width != 32 || *extra != 32 {
                    return Err("compact certificate: unsupported zero-extension width".into());
                }
                64
            }
            Formula::BvExtract { inner, high, low } => {
                if *low != 0 || *high != 31 {
                    return Err("compact certificate: exact low-32 extract required".into());
                }
                let width = formula_width(inner, nodes, depth + 1, leaves, true)?;
                if width != 64 {
                    return Err("compact certificate: extract input width mismatch".into());
                }
                // For a ZeroExt child, the arm above established 32+32, hence
                // high+1 is exactly its pre-extension width. No failed modern
                // or arbitrary slice is reinterpreted as an identity.
                32
            }
            _ => {
                return Err(
                    "compact certificate: unsupported formula constructor/leaf identity".into()
                );
            }
        };
        Ok(width)
    }

    fn qualify_formulas(obligation: &GateObligation) -> Result<(), String> {
        let mut nodes = 0;
        for formula in [&obligation.machine_value, &obligation.spec_value] {
            let mut leaves = BTreeSet::new();
            if formula_width(formula, &mut nodes, 0, &mut leaves, false)? != 32
                || leaves != BTreeSet::from([("X0".into(), 64), ("X1".into(), 64)])
            {
                return Err(
                    "compact certificate: output width or complete owned-leaf population mismatch"
                        .into(),
                );
            }
        }
        Ok(())
    }

    fn terms(obligation: &GateObligation) -> Result<(Expr, Expr, Vec<(String, u32)>), String> {
        qualify_formulas(obligation)?;
        let mut ctx = ReflectCtx::closed();
        let rm = reflect_formula(&obligation.machine_value, &mut ctx)?;
        let ra = reflect_formula(&obligation.spec_value, &mut ctx)?;
        if !ctx.mems.is_empty() {
            return Err("compact certificate: memory leaves".into());
        }
        let leaves: Vec<_> = ctx.leaves.into_iter().collect::<BTreeSet<_>>().into_iter().collect();
        if leaves != [("X0".into(), 64), ("X1".into(), 64)] {
            return Err("compact certificate: reflected leaf identity mismatch".into());
        }
        let goal = kx::eq_list(kx::evalf(rm.bvf.clone()), kx::evalf(ra.bvf.clone()));
        let sym = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]),
            [kx::list_bool(), kx::evalf(ra.bvf.clone()), kx::evalf(ra.core.clone()), ra.proof],
        );
        let proof = kx::eq_trans_list(
            kx::evalf(rm.bvf),
            kx::evalf(rm.core),
            kx::evalf(ra.bvf),
            rm.proof,
            sym,
        );
        Ok((goal, proof, leaves))
    }

    fn wire_name(name: &Name) -> Result<Vec<NamePart>, String> {
        let mut result = Vec::new();
        let mut current = name;
        loop {
            if result.len() > 16 {
                return Err("compact certificate: name depth".into());
            }
            match current.inner() {
                NameInner::Anon => break,
                NameInner::Str(parent, value) => {
                    if value.len() > 256 {
                        return Err("compact certificate: name bytes".into());
                    }
                    result.push(NamePart::Str { value: value.to_string() });
                    current = parent;
                }
                NameInner::Num(parent, value) => {
                    result.push(NamePart::Num { value: *value });
                    current = parent;
                }
            }
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
                Level::Succ(parent) if n < 4 => {
                    n += 1;
                    current = parent;
                }
                _ => return Err("compact certificate: unsupported universe".into()),
            }
        }
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
            self.visited += 1;
            if depth > MAX_DEPTH || self.visited > MAX_EXPANDED {
                return Err("compact certificate: term construction budget".into());
            }
            let key = expr.kind() as *const ExprKind as usize;
            if let Some(index) = self.memo.get(&key) {
                return Ok(*index);
            }
            let node = match expr.kind() {
                ExprKind::Const(name, levels) => {
                    if levels.len() > 4 {
                        return Err("compact certificate: universe population".into());
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
                _ => {
                    return Err(
                        "compact certificate: unsupported proof expression constructor".into()
                    );
                }
            };
            let index = if let Some(index) = self.canonical.get(&node) {
                *index
            } else {
                if self.nodes.len() >= MAX_NODES {
                    return Err("compact certificate: term node budget".into());
                }
                if let TermNode::Const { name, .. } = &node {
                    for part in name {
                        if let NamePart::Str { value } = part {
                            self.name_bytes = self
                                .name_bytes
                                .checked_add(value.len())
                                .ok_or("compact certificate: name byte overflow")?;
                            if self.name_bytes > MAX_NAME_BYTES {
                                return Err("compact certificate: name byte budget".into());
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

    fn restore(certificate: &CompactCertificate) -> Result<(Expr, Expr), String> {
        certificate.validate_graph()?;
        let mut terms: Vec<Expr> = Vec::with_capacity(certificate.terms.len());
        for node in &certificate.terms {
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
                            let mut l = Level::zero();
                            for _ in 0..*n {
                                l = Level::succ(l);
                            }
                            l
                        })
                        .collect();
                    Expr::const_(exact, levels)
                }
                TermNode::App { function, argument } => {
                    Expr::app(terms[*function as usize].clone(), terms[*argument as usize].clone())
                }
            };
            terms.push(expr);
        }
        Ok((terms[certificate.goal as usize].clone(), terms[certificate.proof as usize].clone()))
    }

    struct HashWriter {
        hash: Sha256,
        row_bytes: usize,
        total_bytes: usize,
    }
    impl Write for HashWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.row_bytes = self
                .row_bytes
                .checked_add(bytes.len())
                .ok_or_else(|| io::Error::other("environment row overflow"))?;
            self.total_bytes = self
                .total_bytes
                .checked_add(bytes.len())
                .ok_or_else(|| io::Error::other("environment total overflow"))?;
            if self.row_bytes > 8 * 1024 * 1024 || self.total_bytes > 64 * 1024 * 1024 {
                return Err(io::Error::other("compact environment serialization budget"));
            }
            self.hash.update(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    pub(crate) fn environment_digest(env: &Environment) -> Result<String, String> {
        let mut names = BTreeSet::new();
        for name in env
            .constants()
            .map(|row| &row.name)
            .chain(env.inductives().map(|row| &row.name))
            .chain(env.constructors().map(|row| &row.name))
            .chain(env.recursors().map(|row| &row.name))
            .chain(env.quotients().map(|row| &row.name))
        {
            if names.len() >= 8192 {
                return Err("compact certificate: environment population budget".into());
            }
            names.insert(name.clone());
        }
        let mut writer = HashWriter { hash: Sha256::new(), row_bytes: 0, total_bytes: 0 };
        serde_json::to_writer(
            &mut writer,
            &("compact-BVC-environment/v1", env.mode(), names.len()),
        )
        .map_err(|e| e.to_string())?;
        for name in names {
            writer.row_bytes = 0;
            let fields = env.get_structure_field_names(&name);
            let defaults: Vec<_> = fields
                .unwrap_or(&[])
                .iter()
                .map(|field| (field, env.get_structure_field_default(&name, field)))
                .collect();
            serde_json::to_writer(
                &mut writer,
                &(
                    &name,
                    env.get_const(&name),
                    env.get_inductive(&name),
                    env.get_constructor(&name),
                    env.get_recursor(&name),
                    env.get_quot(&name),
                    env.get_constant_origin(&name),
                    env.declaration_verification(&name),
                    fields,
                    defaults,
                    env.get_structure_parents(&name),
                    env.get_implemented_by(&name),
                ),
            )
            .map_err(|e| e.to_string())?;
        }
        Ok(format!("{:x}", writer.hash.finalize()))
    }

    fn environment(leaves: &[(String, u32)]) -> Result<Environment, String> {
        if leaves != [("X0".into(), 64), ("X1".into(), 64)] {
            return Err("compact certificate: environment leaf mismatch".into());
        }
        // Reuse only the fixed checked factory. Add our exact owned input
        // constants ourselves, checking collisions and every insertion result.
        // They have List Bool type, not proposition type; no result is assumed.
        let mut env = discharge_env(&[], &[])?;
        for (leaf, width) in leaves {
            let name = Name::anon().str(format!("BVC_LEAF_{leaf}_{width}"));
            if env.get_const(&name).is_some() {
                return Err("compact certificate: leaf collision with rebuilt environment".into());
            }
            env.add_decl(Declaration::Axiom { name, level_params: vec![], type_: kx::list_bool() })
                .map_err(|e| format!("compact certificate: input constant refused: {e:?}"))?;
        }
        Ok(env)
    }

    fn expected(
        obligation: &GateObligation,
    ) -> Result<(CompactCertificate, Expr, Expr, Environment), String> {
        let (goal, proof, leaves) = terms(obligation)?;
        let mut graph = Graph::default();
        let goal_root = graph.add(&goal, 0)?;
        let proof_root = graph.add(&proof, 0)?;
        let env = environment(&leaves)?;
        let certificate = CompactCertificate {
            model: MODEL,
            leaves,
            environment_sha256: environment_digest(&env)?,
            terms: graph.nodes,
            goal: goal_root,
            proof: proof_root,
        };
        certificate.validate_graph()?;
        Ok((certificate, goal, proof, env))
    }

    fn replay_obligation(
        obligation: &GateObligation,
        retained: &CompactCertificate,
    ) -> Result<(), String> {
        retained.validate_graph()?;
        let (expected, goal, _constructed_proof, env) = expected(obligation)?;
        // This version intentionally accepts only the canonical construction,
        // not arbitrary alternate proof terms. Exact node/name/universe/leaf
        // equality also forbids injecting a different constant from the base.
        if &expected != retained {
            return Err(
                "compact certificate: reconstructed goal/environment/canonical term mismatch"
                    .into(),
            );
        }
        let (retained_goal, retained_proof) = restore(retained)?;
        if retained_goal != goal {
            return Err("compact certificate: retained goal mismatch".into());
        }
        TypeChecker::with_mode(&env, env.mode())
            .check_type(&retained_proof, &goal)
            .map_err(|e| format!("compact certificate: retained kernel term refused: {e:?}"))
    }

    pub(in super::super) fn capture(
        source: &TrustIrGateSource,
        object: &[u8],
        arch: TrustCgTargetArch,
    ) -> Result<CompactCertificate, String> {
        let obligation = qualified_obligation(source, object, arch)?;
        run_recheck_thread("trust-retain-compact-BVC", move || {
            let (certificate, goal, proof, env) = expected(&obligation)?;
            TypeChecker::with_mode(&env, env.mode()).check_type(&proof, &goal).map_err(|e| {
                format!("compact certificate: generated kernel term refused: {e:?}")
            })?;
            // Serialize/decode the ACTUAL constructed term, then independently
            // reconstruct its context and check the RETAINED term immediately.
            let bytes = encode(&certificate, MAX_CERTIFICATE_BYTES)?;
            let retained: CompactCertificate =
                serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
            replay_obligation(&obligation, &retained)?;
            Ok(retained)
        })
        .map_err(|e| format!("compact certificate: kernel worker {e:?}"))?
    }

    pub(in super::super) fn replay(
        source: &TrustIrGateSource,
        object: &[u8],
        arch: TrustCgTargetArch,
        retained: &CompactCertificate,
    ) -> Result<(), String> {
        retained.validate_graph()?;
        let obligation = qualified_obligation(source, object, arch)?;
        let retained = retained.clone();
        run_recheck_thread("trust-replay-compact-BVC", move || {
            replay_obligation(&obligation, &retained)
        })
        .map_err(|e| format!("compact certificate: kernel worker {e:?}"))?
    }
}

#[cfg(all(test, feature = "kernel-recheck"))]
mod tests;

#[cfg(feature = "kernel-recheck")]
pub(crate) use kernel::environment_digest;
