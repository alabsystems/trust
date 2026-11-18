//! Defined primitive Unit values in the producer evaluator.
//!
//! Unit has one logical value and no register bits. Only the canonical
//! PhantomData constant, a checked copy, or an exact ignored Unit ABI input
//! establishes that value. A declared type alone never establishes definedness.

use super::*;

impl SpecCx<'_> {
    /// Reuse the evaluator's one type census, rather than rebuilding the
    /// complete function metadata for every Unit instruction and argument.
    pub(super) fn unit_type(&mut self, value: ValueId) -> Result<(), String> {
        if self.value_ty(value)? != IrTy::Unit {
            return Err("Unit operand has another declared SSA type".into());
        }
        Ok(())
    }
}

#[derive(Clone, Default)]
pub(super) struct Units(BTreeSet<ValueId>);

impl Units {
    pub(super) fn claims(inst: &Inst) -> bool {
        matches!(inst, Inst::Const { ty: IrTy::Unit, .. } | Inst::Copy { ty: IrTy::Unit, .. })
    }

    pub(super) fn incoming(&mut self, id: ValueId, ty: &IrTy) -> Result<(), String> {
        if *ty != IrTy::Unit {
            return Err(format!("ignored parameter has non-Unit type {ty:?}"));
        }
        self.0.insert(id);
        Ok(())
    }

    pub(super) fn require(&self, id: ValueId, ty: &IrTy) -> Result<(), String> {
        if *ty != IrTy::Unit || !self.0.contains(&id) {
            return Err("ignored argument requires a defined primitive Unit value".into());
        }
        Ok(())
    }

    pub(super) fn contains(&self, id: ValueId) -> bool {
        self.0.contains(&id)
    }

    #[cfg(feature = "test-hooks")]
    pub(super) fn clear(&mut self) {
        self.0.clear();
    }

    pub(super) fn step(&mut self, node: &trust_ir::InstrNode) -> Result<(), String> {
        let defined = match &node.inst {
            Inst::Const { ty: IrTy::Unit, value: Constant::PhantomData } => true,
            Inst::Const { ty: IrTy::Unit, .. } => {
                return Err("Unit constant is not canonical PhantomData".into());
            }
            Inst::Copy { ty: IrTy::Unit, operand } => self.contains(*operand),
            _ => return Err("instruction does not produce a primitive Unit value".into()),
        };
        if !defined {
            return Err("Unit Copy operand has no defined Unit value".into());
        }
        let [result] = node.results.as_slice() else {
            return Err("Unit instruction must bind exactly one result".into());
        };
        self.0.insert(*result);
        Ok(())
    }

    /// Read every incoming fact before adding any destination parameter.
    pub(super) fn edge(
        &self,
        params: &[(ValueId, IrTy)],
        args: &[ValueId],
    ) -> Result<Self, String> {
        if params.len() != args.len() {
            return Err("Unit edge argument count differs from block parameters".into());
        }
        let mut next = self.clone();
        for ((param, ty), arg) in params.iter().zip(args) {
            if *ty == IrTy::Unit || self.contains(*arg) {
                self.require(*arg, ty)?;
                next.0.insert(*param);
            }
        }
        Ok(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{Block, FuncTy, Function, InstrNode};

    fn v(id: u32) -> ValueId { ValueId::new(id) }

    fn module(body: Vec<InstrNode>, params: Vec<IrTy>) -> Module {
        let mut module = Module::new("logical_unit");
        module.func_types.push(FuncTy::unrecorded(params.clone(), vec![], false));
        let mut function = Function::new(FuncId::new(0), "entry", FuncTyId::new(0), BlockId::new(0));
        function.calling_conv = CallingConv::Rust;
        let mut block = Block::new(BlockId::new(0));
        block.params = params.into_iter().enumerate().map(|(n, ty)| (v(n as u32), ty)).collect();
        block.body = body;
        function.blocks.push(block);
        module.functions.push(function);
        module
    }

    fn konst(id: u32) -> InstrNode {
        InstrNode::new(Inst::Const { ty: IrTy::Unit, value: Constant::PhantomData }).with_result(v(id))
    }

    fn evaluate(module: &Module, decisions: &BTreeMap<SiteKey, SiteDecision>) -> Result<SpecResult, String> {
        let bodies = BTreeMap::new();
        let placements = BTreeMap::new();
        let input = CerInput {
            m_cg: module, producers: &[], bodies: &bodies, placements: &placements,
            object: &[], relocation_model: RelocationModel::Static,
        };
        let function = &module.functions[0];
        let signature = signature_of(module, function.ty)?;
        let place = FnPlacement {
            params: signature.0.iter().map(|_| ParamPlace::Ignore).collect(),
            ret: ReturnPlace::Void,
        };
        eval_spec(&input, module, function, &signature, &place, decisions)
    }

    #[test]
    fn canonical_unit_copies_and_simultaneous_edges_have_no_scalar_lanes() {
        let mut units = Units::default();
        units.step(&konst(0)).unwrap();
        let original = units.clone();
        assert!(units.edge(&[(v(1), IrTy::Unit), (v(2), IrTy::Unit)], &[v(0), v(1)]).is_err(),
            "an earlier destination must not define a later incoming argument");
        assert!(!original.contains(v(1)));
        let mut module = module(vec![
            konst(0),
            InstrNode::new(Inst::Copy { ty: IrTy::Unit, operand: v(0) }).with_result(v(1)),
            InstrNode::new(Inst::Br { target: BlockId::new(1), args: vec![v(1)] }),
        ], vec![]);
        let mut target = Block::new(BlockId::new(1)).with_param(v(2), IrTy::Unit);
        target.body = vec![
            InstrNode::new(Inst::Copy { ty: IrTy::Unit, operand: v(2) }).with_result(v(3)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ];
        module.functions[0].blocks.push(target);
        assert!(trust_ir::interpret::Interpreter::with_module(&module).execute_func(FuncId::new(0), []).is_ok());
        let result = evaluate(&module, &BTreeMap::new()).unwrap();
        assert_eq!(result.reach, Formula::Bool(true));
        assert!(result.side.is_empty() && result.events.is_empty());
    }

    #[test]
    fn unit_requires_canonical_defined_values_and_exact_edge_types() {
        for value in [Constant::Uninit, Constant::Int(0)] {
            let mut units = Units::default();
            assert!(units.step(&InstrNode::new(Inst::Const { ty: IrTy::Unit, value }).with_result(v(0))).is_err());
            assert!(!units.contains(v(0)));
        }
        let mut units = Units::default();
        assert!(units.step(&InstrNode::new(Inst::Copy { ty: IrTy::Unit, operand: v(9) }).with_result(v(0))).is_err());
        assert!(units.incoming(v(0), &IrTy::Never).is_err());
        units.incoming(v(0), &IrTy::Unit).unwrap();
        assert!(units.edge(&[(v(1), IrTy::I64)], &[v(0)]).is_err());
        assert!(units.edge(&[(v(1), IrTy::Unit)], &[v(9)]).is_err());
        let bad = module(vec![
            InstrNode::new(Inst::Undef { ty: IrTy::Unit }).with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ], vec![]);
        assert!(evaluate(&bad, &BTreeMap::new()).is_err());
    }

    #[test]
    fn ignored_entry_requires_unit_and_unit_result_is_not_empty_return() {
        let good = module(vec![
            InstrNode::new(Inst::Copy { ty: IrTy::Unit, operand: v(0) }).with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ], vec![IrTy::Unit]);
        assert!(evaluate(&good, &BTreeMap::new()).is_ok());
        let bad = module(vec![InstrNode::new(Inst::Return { values: vec![] })], vec![IrTy::I64]);
        assert!(evaluate(&bad, &BTreeMap::new()).is_err());
        let mut unit_return = module(vec![konst(0), InstrNode::new(Inst::Return { values: vec![v(0)] })], vec![]);
        unit_return.func_types[0].returns = vec![IrTy::Unit];
        assert!(evaluate(&unit_return, &BTreeMap::new()).is_err());
    }

    #[test]
    fn ignored_call_argument_needs_a_live_unit_fact_before_the_event() {
        let mut good = module(vec![
            konst(0),
            InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(0)] }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ], vec![]);
        good.func_types.push(FuncTy::unrecorded(vec![IrTy::Unit], vec![], false));
        let mut callee = Function::new(FuncId::new(1), "consume_unit", FuncTyId::new(1), BlockId::new(0));
        callee.calling_conv = CallingConv::Rust;
        good.functions.push(callee);
        let decisions = BTreeMap::from([((0, 1), SiteDecision::Called {
            symbol: "consume_unit".into(),
            place: FnPlacement { params: vec![ParamPlace::Ignore], ret: ReturnPlace::Void },
            result_width: None,
        })]);
        let result = evaluate(&good, &decisions).unwrap();
        assert_eq!(result.events.len(), 1);
        assert!(result.events[&(0, 1)][0].args.is_empty());
        let mut undefined = good.clone();
        undefined.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Undef { ty: IrTy::Unit }).with_result(v(0));
        assert!(evaluate(&undefined, &decisions).is_err());
        let mut absent = good.clone();
        if let Inst::Call { args, .. } = &mut absent.functions[0].blocks[0].body[1].inst { args[0] = v(99); }
        assert!(evaluate(&absent, &decisions).is_err());
        let mut wrong = good.clone();
        wrong.func_types[1].params = vec![IrTy::I64];
        assert!(evaluate(&wrong, &decisions).is_err());
    }

    #[test]
    fn cached_unit_type_census_refuses_duplicate_ssa_identities() {
        let bad = module(vec![
            konst(0),
            InstrNode::new(Inst::Const { ty: IrTy::I64, value: Constant::Int(7) }).with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ], vec![]);
        let error = evaluate(&bad, &BTreeMap::new()).err().expect("duplicate source identities refuse");
        assert!(error.contains("duplicate typed SSA"), "{error}");
    }
}
