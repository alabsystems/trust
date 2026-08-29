// TEMPORARY probe harness (not for commit): drive the F1 proven-output gate over
// either a serialized producer trust_ir::Module or a synthetic select function,
// so gate work can be iterated with plain cargo instead of `x.py build`.
//
// usage: ccc_probe file <module.bin> <symbol-substring>
//        ccc_probe sel  <width> <n_arms>

use trust_cg_bridge::codegen_backend::{
    BridgeOptimizationLevel, TrustCgCodegenBackend, TrustCgTargetArch,
};
use trust_cg_bridge::verify_output_trust_ir::{
    TrustIrGateSource, verify_trust_ir_output_preserved,
};
use trust_ir::inst::{ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Constant, Function as IrFunction, Module, Ty};

fn backend() -> TrustCgCodegenBackend {
    TrustCgCodegenBackend::new_for_triple(TrustCgTargetArch::AArch64, "aarch64-apple-darwin")
        .with_optimization_level(BridgeOptimizationLevel::O0)
}

/// `fn f(x: T) -> T` implementing an `n`-arm equality cascade:
/// `if x == 10 { 1 } else if x == 20 { 2 } ... else { 0 }`, built directly as
/// trust-ir so no compiler rebuild is needed.
fn selects(ty: Ty, n: u32) -> TrustIrGateSource {
    let mut module = Module::new("t");
    module.func_types.push(FuncTy {
        params: vec![ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = IrFunction::new(FuncId::new(0), "k", FuncTyId::new(0), BlockId::new(0));

    // Value numbering: %0 = param. Then per arm i: %(1+3i) = const key,
    // %(2+3i) = icmp, %(3+3i) = const result.
    let param = ValueId::new(0);
    let mut next_val = 1u32;
    let mut next_blk = 0u32;

    // Join block: takes the result as a param and returns it.
    let join = BlockId::new(1_000);
    let join_param = ValueId::new(900_000);
    let mut join_blk = Block::new(join);
    join_blk.params.push((join_param, ty.clone()));
    join_blk.body = vec![InstrNode::new(Inst::Return { values: vec![join_param] })];

    let mut blocks: Vec<Block> = Vec::new();
    for i in 0..n {
        let this = BlockId::new(next_blk);
        next_blk += 1;
        let key = ValueId::new(next_val);
        next_val += 1;
        let cmp = ValueId::new(next_val);
        next_val += 1;
        let res = ValueId::new(next_val);
        next_val += 1;

        // The arm's "matched" block: bind the result constant, jump to join.
        let arm = BlockId::new(500 + i);
        let mut arm_blk = Block::new(arm);
        arm_blk.body = vec![
            InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(i128::from(i) + 1) })
                .with_results(vec![res]),
            InstrNode::new(Inst::Br { target: join, args: vec![res] }),
        ];
        blocks.push(arm_blk);

        // The test block.
        let next_test = if i + 1 == n { BlockId::new(900) } else { BlockId::new(next_blk) };
        let mut blk = Block::new(this);
        if i == 0 {
            blk.params.push((param, ty.clone()));
        }
        blk.body = vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Int(i128::from(i) * 10 + 10),
            })
            .with_results(vec![key]),
            InstrNode::new(Inst::ICmp { op: ICmpOp::Eq, ty: ty.clone(), lhs: param, rhs: key })
                .with_results(vec![cmp]),
            InstrNode::new(Inst::CondBr {
                cond: cmp,
                then_target: arm,
                then_args: vec![],
                else_target: next_test,
                else_args: vec![],
            }),
        ];
        blocks.push(blk);
    }

    // Default block.
    let dflt_val = ValueId::new(800_000);
    let mut dflt = Block::new(BlockId::new(900));
    dflt.body = vec![
        InstrNode::new(Inst::Const { ty: ty.clone(), value: Constant::Int(0) })
            .with_results(vec![dflt_val]),
        InstrNode::new(Inst::Br { target: join, args: vec![dflt_val] }),
    ];
    blocks.push(dflt);
    blocks.push(join_blk);

    f.blocks = blocks;
    module.functions.push(f);
    TrustIrGateSource { symbol: "k".to_string(), module, func_id: FuncId::new(0) }
}

fn report(source: &TrustIrGateSource, label: &str) {
    let t0 = std::time::Instant::now();
    let (verdict, obj) = verify_trust_ir_output_preserved(source, &backend());
    println!(
        "{label:<22} {:>8.2?}  obj={:?}  {verdict:?}",
        t0.elapsed(),
        obj.as_ref().map(|o| o.len())
    );
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mode = args.next().unwrap_or_else(|| "sel".into());

    if mode == "file" {
        let path = args.next().expect("usage: ccc_probe file <module.bin> <symbol>");
        let want = args.next().unwrap_or_default();
        let bytes = std::fs::read(&path).expect("read module");
        let module = trust_ir::binary::deserialize_module(&bytes).expect("deserialize");
        let mut target = None;
        for (i, f) in module.functions.iter().enumerate() {
            if !f.blocks.is_empty() && (want.is_empty() || f.name.contains(&want)) {
                target = Some((FuncId::new(i as u32), f.name.clone()));
            }
        }
        let (func_id, symbol) = target.expect("no matching function");
        println!("== target {symbol}");

        // SPEC SIDE ALONE — the producer's trust-ir semantics, no bytes involved.
        let t = std::time::Instant::now();
        match trust_cg_bridge::verify_output_trust_ir::trust_ir_function_semantics(&module, func_id)
        {
            Ok(spec) => println!(
                "== SPEC-ONLY ok in {:?}  out_width={}  value_chars={}  reach={:?}  side_conds={}",
                t.elapsed(),
                spec.out_width,
                format!("{:?}", spec.value).len(),
                spec.reach,
                spec.side_conditions.len()
            ),
            Err(e) => println!("== SPEC-ONLY err in {:?}: {e}", t.elapsed()),
        }

        let source = TrustIrGateSource { symbol, module, func_id };
        let (verdict, obj) = verify_trust_ir_output_preserved(&source, &backend());
        if let Some(o) = &obj {
            std::fs::write("/tmp/ccc_probe.o", o).expect("write");
        }
        println!("== verdict: {verdict:?}");
        if let Some(o) = &obj {
            match trust_cg_bridge::verify_output_trust_ir::probe_machine_only(o, 32) {
                Ok(_) => println!("== MACHINE-ONLY ok"),
                Err(e) => println!("== MACHINE-ONLY err: {e}"),
            }
        }
        return;
    }

    let width: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(32);
    let n: u32 = args.next().and_then(|s| s.parse().ok()).unwrap_or(1);
    let ty = match width {
        8 => Ty::U8,
        16 => Ty::U16,
        32 => Ty::U32,
        _ => Ty::U64,
    };
    report(&selects(ty, n), &format!("sel u{width} arms={n}"));
}
