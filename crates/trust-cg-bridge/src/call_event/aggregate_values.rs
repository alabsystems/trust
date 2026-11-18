//! Register aggregate values for CER's producer-side evaluator (DECISION_QUEUE AGG-SSA-1).
//!
//! A Tuple, Struct, Array or Enum SSA value is a vector of integer lanes, one per field or
//! element; an enum's lanes are its tag and the payload of its one active variant. It is built by
//! `Const` and `InsertField`/`InsertElement` and read by `ExtractField`/`ExtractElement` at a
//! literal, in-range index. Each rule below is the trust-ir reference interpreter's, lane for lane
//! (trust-ir `interpret.rs`: tuple, struct, enum and array constants at 3576-3714 and 3748-3793;
//! the active-variant lane check 7833-7860; `eval_extract_field` 8053-8110; `eval_insert_field`
//! 8112-8205; `eval_extract_element`/`eval_insert_element` 8207-8290; `runtime_index`
//! 10097-10113).
//!
//! This is value transport only. An aggregate never enters `scalars`, `pairs` or `closures`, so
//! every other use of one (a call or `Pair` argument, a return, a store, a copy, a select, a
//! branch operand) still fails in `lookup`. A block edge binds an aggregate only to a parameter
//! of exactly its type ([`bind_edge`]), and a `Switch` on a literal selector follows its one
//! matching edge ([`literal_switch_target`]). No side condition, fresh
//! variable or solver call is made here, and the lane literals are built in this file rather
//! than through the shared scalar evaluator, so what the frozen gate accepts is fixed here.

use super::*;

/// The most lanes one aggregate may carry.
pub(super) const MAX_AGG_LANES: usize = 64;

#[derive(Clone)]
pub(super) struct Lane {
    pub ty: IrTy,
    pub value: IrValue,
}

#[derive(Clone)]
pub(super) struct AggValue {
    pub ty: IrTy,
    /// An enum's active variant; `None` for every other aggregate.
    pub variant: Option<usize>,
    pub lanes: Vec<Lane>,
}

/// Lane width of an integer type, or `None` for every other type: no pointer, `bool`, `char`,
/// float, 128-bit integer or nested aggregate is a lane.
fn lane_width(ty: &IrTy) -> Option<u32> {
    match ty {
        IrTy::I8 | IrTy::U8 => Some(8),
        IrTy::I16 | IrTy::U16 => Some(16),
        IrTy::I32 | IrTy::U32 => Some(32),
        IrTy::I64 | IrTy::U64 | IrTy::Isize | IrTy::Usize => Some(64),
        _ => None,
    }
}

fn is_signed(ty: &IrTy) -> bool {
    matches!(ty, IrTy::I8 | IrTy::I16 | IrTy::I32 | IrTy::I64 | IrTy::Isize)
}

/// Is `ty` an aggregate type this file models? A fieldless enum with a scalar carrier keeps it
/// (`module_to_lir::fieldless_enum_carrier`); every other enum is an aggregate.
pub(super) fn is_modeled(module: &Module, ty: &IrTy) -> bool {
    match ty {
        IrTy::Tuple(_) | IrTy::Struct(_) | IrTy::Array(..) => true,
        IrTy::Enum(_) => crate::module_to_lir::fieldless_enum_carrier(module, ty).is_none(),
        _ => false,
    }
}

/// One lane literal: an `Int` representable in the lane type, as a bit-vector reduced modulo
/// 2^width. Anything else (`Uninit`, `Bool`, `U128`, `Bytes`, a nested constant, an
/// out-of-range integer) is outside the fragment.
fn lane_literal(ty: &IrTy, c: &Constant) -> Result<Lane, String> {
    let (Some(width), Constant::Int(v)) = (lane_width(ty), c) else {
        return Err(format!("aggregate lane {ty:?} = {c:?} is outside the modeled fragment"));
    };
    let v = *v;
    let in_range = if is_signed(ty) {
        let half = 1i128 << (width - 1);
        (-half..half).contains(&v)
    } else {
        (0..(1i128 << width)).contains(&v)
    };
    if !in_range {
        return Err(format!("aggregate lane literal {v} does not fit {ty:?}"));
    }
    let reduced = v.rem_euclid(1i128 << width);
    Ok(Lane {
        ty: ty.clone(),
        value: IrValue { f: Formula::BitVec { value: reduced, width }, width },
    })
}

/// The lane types of a modeled aggregate type, in field (or element) order.
fn lane_types(module: &Module, ty: &IrTy) -> Result<Vec<IrTy>, String> {
    let tys = match ty {
        IrTy::Tuple(tys) => tys.clone(),
        IrTy::Struct(id) => module
            .struct_def(*id)
            .ok_or("aggregate names an undeclared struct")?
            .fields
            .iter()
            .map(|field| field.ty.clone())
            .collect(),
        IrTy::Array(element, n) => {
            let element = module.ty(*element).ok_or("array names an undeclared element type")?;
            let n = usize::try_from(*n).map_err(|_| "array length does not fit usize")?;
            if n > MAX_AGG_LANES {
                return Err(format!("array of {n} elements exceeds {MAX_AGG_LANES} lanes"));
            }
            vec![element.clone(); n]
        }
        other => return Err(format!("aggregate type {other:?} is outside the modeled fragment")),
    };
    if tys.len() > MAX_AGG_LANES {
        return Err(format!("aggregate of {} lanes exceeds {MAX_AGG_LANES}", tys.len()));
    }
    if let Some(bad) = tys.iter().find(|t| lane_width(t).is_none()) {
        return Err(format!("aggregate lane type {bad:?} is outside the modeled fragment"));
    }
    Ok(tys)
}

/// Does `inst` belong to this file? A modeled aggregate constant, or an insert or extract whose
/// aggregate operand is a modeled value on this path.
pub(super) fn claims(module: &Module, inst: &Inst, aggs: &HashMap<ValueId, AggValue>) -> bool {
    match inst {
        Inst::Const { ty, .. } => is_modeled(module, ty),
        Inst::InsertField { aggregate, .. } | Inst::ExtractField { aggregate, .. } => {
            aggs.contains_key(aggregate)
        }
        Inst::InsertElement { array, .. } | Inst::ExtractElement { array, .. } => {
            aggs.contains_key(array)
        }
        _ => false,
    }
}

/// A literal element index in `0..len`: the operand's formula must be a bit-vector literal of
/// its declared integer type. A negative signed index and an index at or past the length are both
/// UB in the interpreter (`runtime_index`, `eval_extract_element`/`eval_insert_element`); the gate
/// does not model those executions, so both stay outside the fragment.
fn literal_index(
    cx: &mut SpecCx<'_>,
    env: &SpecEnv,
    index: ValueId,
    len: usize,
) -> Result<usize, String> {
    let ty = cx.value_ty(index)?;
    let width = lane_width(&ty).ok_or("element index is not an integer")?;
    let v = lookup(&env.scalars, index)?;
    match v.f {
        Formula::BitVec { value, width: w } if w == width && v.width == width => {
            let k = usize::try_from(value).map_err(|_| "element index is negative")?;
            if k >= len {
                return Err(format!("element index {k} is outside an array of {len}"));
            }
            Ok(k)
        }
        _ => Err("element index is not a literal".into()),
    }
}

/// The scalar written into a lane: its declared type and width must be the lane's.
fn lane_operand(
    cx: &mut SpecCx<'_>,
    env: &SpecEnv,
    value: ValueId,
    lane: &IrTy,
) -> Result<IrValue, String> {
    if cx.value_ty(value)? != *lane {
        return Err("aggregate insert writes a value of another type than its lane".into());
    }
    let v = lookup(&env.scalars, value)?;
    if Some(v.width) != lane_width(lane) {
        return Err("aggregate insert writes a value of another width than its lane".into());
    }
    Ok(v)
}

/// An enum constant `[Int(d), payload…]`: `d` must be one of the enum's declared discriminants,
/// which selects the variant; the tag lane is `d` at the enum's tag type and the payload lanes
/// are that variant's fields, in order (interpret.rs 3658-3714).
fn enum_constant(
    module: &Module,
    ty: &IrTy,
    id: trust_ir::EnumId,
    value: &Constant,
) -> Result<AggValue, String> {
    let def = module.enum_def(id).ok_or("aggregate names an undeclared enum")?;
    let discriminants = def.effective_discriminants().ok_or("enum discriminants are invalid")?;
    let tag_ty = def.canonical_tag_repr().ok_or("enum has no tag representation")?.ty();
    let Constant::Aggregate(cs) = value else {
        return Err(format!("enum constant {value:?} is outside the modeled fragment"));
    };
    let Some(Constant::Int(d)) = cs.first() else {
        return Err("enum constant has no integer discriminant".into());
    };
    let variant = discriminants
        .iter()
        .position(|x| x == d)
        .ok_or_else(|| format!("enum constant discriminant {d} is not declared"))?;
    let fields = &def.variants[variant].fields;
    if cs.len() != fields.len() + 1 {
        return Err("enum constant has another field count than its variant".into());
    }
    if cs.len() > MAX_AGG_LANES {
        return Err(format!("enum of {} lanes exceeds {MAX_AGG_LANES}", cs.len()));
    }
    let mut lanes = vec![lane_literal(&tag_ty, &cs[0])?];
    for (t, c) in fields.iter().zip(&cs[1..]) {
        lanes.push(lane_literal(t, c)?);
    }
    Ok(AggValue { ty: ty.clone(), variant: Some(variant), lanes })
}

/// Bind a block edge whose arguments may be aggregates. An aggregate argument binds only to a
/// parameter of exactly its type; a parameter of a modeled aggregate type takes only an
/// aggregate. The scalar parameters bind through the unchanged `bind_block_args`, over a view of
/// the target block that holds only them. Binding is simultaneous: every argument is read from
/// the incoming `env`.
pub(super) fn bind_edge(
    cx: &mut SpecCx<'_>,
    target: BlockId,
    args: &[ValueId],
    env: &SpecEnv,
) -> Result<(HashMap<ValueId, IrValue>, HashMap<ValueId, AggValue>), String> {
    let block = cx
        .blocks
        .get(&target.index())
        .copied()
        .ok_or_else(|| format!("branch to bb{} which the function lacks", target.index()))?;
    if block.params.len() != args.len() {
        return Err(format!(
            "edge to bb{} passes {} arg(s) for {} param(s)",
            target.index(),
            args.len(),
            block.params.len()
        ));
    }
    let mut aggs = env.aggs.clone();
    let mut view = trust_ir::Block::new(target);
    let mut scalar_args = Vec::new();
    for ((param, ty), arg) in block.params.iter().zip(args) {
        if *ty == IrTy::Unit || env.units.contains(*arg) {
            cx.unit_type(*arg)?;
            env.units.require(*arg, ty)?;
            continue;
        }
        match env.aggs.get(arg) {
            Some(agg) if agg.ty == *ty => {
                aggs.insert(*param, agg.clone());
            }
            Some(_) => return Err("an aggregate passed into a parameter of another type".into()),
            None if is_modeled(cx.module, ty) => {
                return Err("a non-aggregate passed into an aggregate parameter".into());
            }
            None => {
                view = view.with_param(*param, ty.clone());
                scalar_args.push(*arg);
            }
        }
    }
    let blocks = HashMap::from([(target.index(), &view)]);
    let scalars = bind_block_args(cx.module, &blocks, target, &scalar_args, &env.scalars)?;
    Ok((scalars, aggs))
}

/// A `Switch` whose selector is a bit-vector literal of 1 to 64 bits takes exactly one edge: the
/// first case equal to it modulo 2^width, otherwise the default. Every case constant is checked
/// as the general rule checks it (an `Int` or a `Bool`). `None` for any other selector, which the
/// general rule evaluates.
pub(super) fn literal_switch_target<'c>(
    sel: &IrValue,
    cases: &'c [trust_ir::inst::SwitchCase],
    default: BlockId,
    default_args: &'c [ValueId],
) -> Result<Option<(BlockId, &'c [ValueId])>, String> {
    let mut values = Vec::with_capacity(cases.len());
    for case in cases {
        values.push(match &case.value {
            Constant::Int(v) => *v,
            Constant::Bool(v) => i128::from(*v),
            other => return Err(format!("switch case constant {other:?} is outside the fragment")),
        });
    }
    let Formula::BitVec { value: s, width } = sel.f else {
        return Ok(None);
    };
    if width != sel.width || !(1..=64).contains(&width) {
        return Ok(None);
    }
    let m = 1i128 << width;
    for (case, v) in cases.iter().zip(values) {
        if v.rem_euclid(m) == s.rem_euclid(m) {
            return Ok(Some((case.target, case.args.as_slice())));
        }
    }
    Ok(Some((default, default_args)))
}

impl SpecCx<'_> {
    /// The declared type of an SSA value, read once per function.
    pub(super) fn value_ty(&mut self, value: ValueId) -> Result<IrTy, String> {
        if self.value_tys.is_none() {
            let function =
                self.module.function_by_id(self.func).ok_or("source function is missing")?;
            let mut types = HashMap::new();
            for metadata in function.typed_values(self.module) {
                if types.insert(metadata.value, metadata.ty).is_some() {
                    return Err("source function has duplicate typed SSA identities".into());
                }
            }
            self.value_tys = Some(types);
        }
        self.value_tys
            .as_ref()
            .and_then(|tys| tys.get(&value))
            .cloned()
            .ok_or_else(|| "aggregate operand has no declared SSA type".into())
    }

    /// Evaluate one claimed instruction into `env.aggs` (an aggregate result) or `env.scalars`
    /// (an extracted lane).
    pub(super) fn aggregate_step(
        &mut self,
        env: &mut SpecEnv,
        inst: &Inst,
        results: &[ValueId],
    ) -> Result<(), String> {
        let [result] = results else {
            return Err("an aggregate instruction must bind one result".into());
        };
        match inst {
            Inst::Const { ty: ty @ IrTy::Enum(id), value } => {
                let agg = enum_constant(self.module, ty, *id, value)?;
                env.aggs.insert(*result, agg);
            }
            Inst::Const { ty, value } => {
                let tys = lane_types(self.module, ty)?;
                let lanes = match (ty, value) {
                    (IrTy::Array(..), Constant::Splat { elem, len }) => {
                        if usize::try_from(*len).ok() != Some(tys.len()) {
                            return Err("array splat length differs from the array's".into());
                        }
                        let lane = match tys.first() {
                            Some(t) => Some(lane_literal(t, elem)?),
                            None => None,
                        };
                        lane.map(|l| vec![l; tys.len()]).unwrap_or_default()
                    }
                    (IrTy::Array(..), Constant::Array(cs) | Constant::Aggregate(cs))
                    | (IrTy::Tuple(_) | IrTy::Struct(_), Constant::Aggregate(cs)) => {
                        if cs.len() != tys.len() {
                            return Err(
                                "aggregate constant has another lane count than its type".into()
                            );
                        }
                        tys.iter()
                            .zip(cs)
                            .map(|(t, c)| lane_literal(t, c))
                            .collect::<Result<_, _>>()?
                    }
                    (ty, c) => {
                        return Err(format!(
                            "aggregate constant {c:?} of {ty:?} is outside the modeled fragment"
                        ));
                    }
                };
                env.aggs.insert(*result, AggValue { ty: ty.clone(), variant: None, lanes });
            }
            Inst::InsertField { ty, aggregate, field, value } => {
                let agg = &env.aggs[aggregate];
                if *ty != agg.ty || matches!(agg.ty, IrTy::Array(..)) {
                    return Err("InsertField type differs from its aggregate's".into());
                }
                // The interpreter refuses to rewrite an enum's tag (interpret.rs 8126-8138); a
                // payload field past the active variant's is absent, so `get` refuses it.
                if agg.variant.is_some() && *field == 0 {
                    return Err("InsertField into an enum's tag".into());
                }
                let k = *field as usize;
                let lane_ty = agg.lanes.get(k).ok_or("InsertField past the last field")?.ty.clone();
                let v = lane_operand(self, env, *value, &lane_ty)?;
                let mut next = env.aggs[aggregate].clone();
                next.lanes[k].value = v;
                env.aggs.insert(*result, next);
            }
            Inst::ExtractField { ty, aggregate, field } => {
                let agg = &env.aggs[aggregate];
                if matches!(agg.ty, IrTy::Array(..)) {
                    return Err("ExtractField of an array".into());
                }
                let lane =
                    agg.lanes.get(*field as usize).ok_or("ExtractField past the last field")?;
                if lane.ty != *ty {
                    return Err("ExtractField type differs from its field's".into());
                }
                let v = lane.value.clone();
                env.scalars.insert(*result, v);
            }
            Inst::InsertElement { ty, array, index, value } => {
                let agg = &env.aggs[array];
                if *ty != agg.ty || !matches!(agg.ty, IrTy::Array(..)) {
                    return Err("InsertElement type differs from its array's".into());
                }
                let len = agg.lanes.len();
                let lane_ty =
                    agg.lanes.first().ok_or("InsertElement into an empty array")?.ty.clone();
                let k = literal_index(self, env, *index, len)?;
                let v = lane_operand(self, env, *value, &lane_ty)?;
                let mut next = env.aggs[array].clone();
                next.lanes[k].value = v;
                env.aggs.insert(*result, next);
            }
            Inst::ExtractElement { ty, array, index } => {
                let agg = &env.aggs[array];
                if !matches!(agg.ty, IrTy::Array(..)) {
                    return Err("ExtractElement of a non-array".into());
                }
                let len = agg.lanes.len();
                let k = literal_index(self, env, *index, len)?;
                let lane = &env.aggs[array].lanes[k];
                if lane.ty != *ty {
                    return Err("ExtractElement type differs from the array's element".into());
                }
                let v = lane.value.clone();
                env.scalars.insert(*result, v);
            }
            other => {
                return Err(format!("aggregate instruction {other:?} is outside the fragment"));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "aggregate_values/tests.rs"]
mod tests;
