//! Derive the effects of the exact typed adapter protocol from its source rows.
//!
//! This is not a synthetic MIR census. The adapter's own executable protocol is
//! authenticated, and its sole call is to an independently conserved source
//! body. A separate conserved source constructor establishes ownership.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{BodyGate, CallingConv, ClosureTyId, FuncId, Inst, Module, Producer, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Witness {
    pub adapter: FuncId,
    pub owner: FuncId,
    pub body: FuncId,
    pub closure: ClosureTyId,
}

impl Witness {
    pub(super) fn disclosure(&self) -> String {
        format!(
            "{{\"kind\":\"typed-closure-adapter\",\"owner_func_id\":{},\"body_func_id\":{},\"closure_type\":{}}}",
            self.owner.index(),
            self.body.index(),
            self.closure.index()
        )
    }
}

/// Only exact source-licensed adapters with independently conserved owners and
/// targets enter the lowering context. `source_count` comes from pass 1's
/// validated definition map, never from a symbol, display path or gate stamp.
pub(super) fn derive(
    module: &Module,
    source_count: usize,
    conserved: &BTreeSet<FuncId>,
    source_authority: &str,
) -> BTreeMap<FuncId, Witness> {
    let mut derived = BTreeMap::new();
    if module.functions.iter().enumerate().any(|(i, f)| f.id.as_usize() != i) {
        return derived;
    }
    let Some(licensed) = crate::closure_adapter::licensed_adapters(module, source_count) else {
        return derived;
    };
    let source = &module.functions[..source_count];
    let admitted = |f: &trust_ir::Function| {
        conserved.contains(&f.id)
            && !f.is_declaration()
            && f.producer == Some(Producer::TRust)
            && matches!(&f.body_gate, Some(BodyGate::Gated { authority, .. }) if authority == source_authority)
    };
    for id in licensed {
        let Some(adapter) = module.function_by_id(id) else {
            continue;
        };
        if !matches!(&adapter.body_gate, Some(BodyGate::Gated { authority, .. }) if authority == source_authority)
        {
            continue;
        }
        let Some(shape) =
            crate::closure_adapter::inspect(adapter, &module.closure_types, &module.func_types)
        else {
            continue;
        };
        let Some(body) = source.get(shape.body.as_usize()).filter(|f| admitted(f)) else {
            continue;
        };
        let Some(closure) = module.closure_type(shape.closure) else {
            continue;
        };
        let Some(apparent) = module.func_type(closure.func) else {
            continue;
        };
        let Some(signature) = module.func_type(body.ty) else {
            continue;
        };
        let params: Vec<_> = std::iter::once(Ty::Closure(shape.closure))
            .chain(apparent.params.iter().cloned())
            .collect();
        if signature.params != params
            || signature.returns != apparent.returns
            || signature.is_vararg
            || signature.abi.is_some()
            || body.calling_conv != CallingConv::Rust
        {
            continue;
        }
        if body
            .block(body.entry)
            .is_none_or(|entry| entry.params.iter().map(|(_, ty)| ty).ne(signature.params.iter()))
        {
            continue;
        }
        let owner = source.iter().filter(|owner| admitted(owner)).find(|owner| {
            owner.blocks.iter().flat_map(|b| &b.body).any(|node| match &node.inst {
                Inst::MakeClosure { ty, func, captures } if *ty == shape.closure && *func == id => {
                    captures.len() == closure.captures.len()
                        && captures.iter().zip(&closure.captures).all(|(value, expected)| {
                            owner
                                .typed_value(module, *value)
                                .is_some_and(|actual| actual.ty == *expected)
                        })
                }
                _ => false,
            })
        });
        if let Some(owner) = owner {
            derived.insert(
                id,
                Witness { adapter: id, owner: owner.id, body: shape.body, closure: shape.closure },
            );
        }
    }
    derived
}

#[cfg(test)]
mod tests {
    use trust_ir::{
        Block, BlockId, ClosureLayoutDescriptor, ClosureTy, Constant, FuncTy, Function, InstrNode,
        ValueId,
    };

    use super::*;
    const AUTH: &str = "trust-direct-lane-structural";
    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    fn stamp(function: &mut Function) {
        function.producer = Some(Producer::TRust);
        function.calling_conv = CallingConv::Rust;
        function.body_gate = Some(BodyGate::Gated { authority: AUTH.into(), evidence: None });
    }
    fn fixture() -> Module {
        let mut m = Module::new("closure_conservation");
        m.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::default(),
        });
        let apparent = m
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let physical = m
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        let body_ty = m
            .add_func_type(FuncTy {
                params: vec![Ty::Closure(ClosureTyId::new(0))],
                returns: vec![Ty::U64],
                is_vararg: false,
                abi: None,
            })
            .unwrap();
        m.closure_types.push(ClosureTy { func: apparent, captures: vec![Ty::Ptr] });
        m.closure_layouts.push(ClosureLayoutDescriptor {
            origin: None,
            closure: ClosureTyId::new(0),
            size: 8,
            align: 8,
            capture_offsets: vec![0],
        });
        let mut owner = Function::new(FuncId::new(0), "owner", physical, BlockId::new(0));
        stamp(&mut owner);
        owner.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Ptr)],
            body: vec![
                InstrNode::new(Inst::MakeClosure {
                    ty: ClosureTyId::new(0),
                    func: FuncId::new(2),
                    captures: vec![v(0)],
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Call { callee: FuncId::new(1), args: vec![v(1)] })
                    .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![v(2)] }),
            ],
        });
        let mut body = Function::new(FuncId::new(1), "body", body_ty, BlockId::new(0));
        stamp(&mut body);
        body.blocks.push(Block {
            id: BlockId::new(0),
            params: vec![(v(0), Ty::Closure(ClosureTyId::new(0)))],
            body: vec![
                InstrNode::new(Inst::Const { ty: Ty::U64, value: Constant::Int(7) })
                    .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        });
        let mut adapter = crate::closure_adapter::build(
            FuncId::new(2),
            physical,
            "adapter".into(),
            crate::closure_adapter::Shape { closure: ClosureTyId::new(0), body: FuncId::new(1) },
            &m.closure_types[0],
            &m.func_types[apparent.as_usize()],
        )
        .unwrap();
        stamp(&mut adapter);
        m.functions = vec![owner, body, adapter];
        m
    }
    fn project(m: &Module, ids: &[u32]) -> BTreeMap<FuncId, Witness> {
        derive(m, 2, &ids.iter().copied().map(FuncId::new).collect(), AUTH)
    }
    #[test]
    fn canonical_adapter_uses_separate_conserved_owner_and_body() {
        let m = fixture();
        let before = m.clone();
        assert_eq!(
            project(&m, &[0, 1]),
            BTreeMap::from([(
                FuncId::new(2),
                Witness {
                    adapter: FuncId::new(2),
                    owner: FuncId::new(0),
                    body: FuncId::new(1),
                    closure: ClosureTyId::new(0),
                }
            )])
        );
        assert_eq!(m, before);
    }
    #[test]
    fn source_prefix_comes_from_validated_definition_assignments() {
        let module = fixture();
        let source = BTreeSet::from([FuncId::new(0), FuncId::new(1)]);
        let exact = crate::direct_definition_map::DirectDefinitionMap::from_assembly(
            &module,
            &[(7, FuncId::new(0)), (9, FuncId::new(1))],
        );
        assert_eq!(exact.len(), 2);
        assert_eq!(derive(&module, exact.len(), &source, AUTH).len(), 1);
        let malformed = crate::direct_definition_map::DirectDefinitionMap::from_assembly(
            &module,
            &[(7, FuncId::new(0)), (9, FuncId::new(2))],
        );
        assert!(derive(&module, malformed.len(), &source, AUTH).is_empty());
    }

    #[test]
    fn derived_disclosure_names_its_real_owner_and_body() {
        let result = project(&fixture(), &[0, 1]);
        let witness = result.get(&FuncId::new(2)).unwrap();
        let value: serde_json::Value = serde_json::from_str(&witness.disclosure()).unwrap();
        assert_eq!(value["kind"], "typed-closure-adapter");
        assert_eq!(value["owner_func_id"], 0);
        assert_eq!(value["body_func_id"], 1);
        assert_eq!(value["closure_type"], 0);
    }

    #[test]
    fn absent_or_refused_source_verdicts_do_not_bootstrap_an_adapter() {
        for ids in [&[][..], &[0][..], &[1][..], &[2][..], &[0, 2][..], &[1, 2][..]] {
            assert!(project(&fixture(), ids).is_empty(), "{ids:?}");
        }
    }
    #[test]
    fn malformed_protocol_and_wrong_source_target_are_not_conserved() {
        for change in 0..5 {
            let mut m = fixture();
            match change {
                0 => m.functions[2].blocks[0].body.insert(
                    1,
                    InstrNode::new(Inst::Store {
                        ty: Ty::U64,
                        ptr: v(0),
                        value: v(0),
                        volatile: false,
                        align: None,
                    }),
                ),
                1 => {
                    let Inst::MakeClosure { captures, .. } =
                        &mut m.functions[2].blocks[0].body[0].inst
                    else {
                        unreachable!()
                    };
                    captures.clear();
                }
                2 => m.functions[1].producer = Some(Producer::Clean),
                3 => {
                    let signature = m.functions[1].ty;
                    m.func_types[signature.as_usize()].params = vec![Ty::Ptr];
                }
                _ => m.functions[2].body_gate = Some(BodyGate::Ungated),
            }
            assert!(project(&m, &[0, 1]).is_empty(), "mutation {change}");
        }
    }
    #[test]
    fn source_ownership_and_declared_frame_are_mandatory() {
        for change in 0..5 {
            let mut m = fixture();
            match change {
                0 => {
                    m.functions[0].blocks[0].body.remove(0);
                }
                1 => {
                    let Inst::MakeClosure { captures, .. } =
                        &mut m.functions[0].blocks[0].body[0].inst
                    else {
                        unreachable!()
                    };
                    captures.clear();
                }
                2 => m.closure_layouts.clear(),
                3 => m.functions[0].body_gate = None,
                _ => m.functions[2].id = FuncId::new(1),
            }
            assert!(project(&m, &[0, 1]).is_empty(), "mutation {change}");
        }
    }
}
