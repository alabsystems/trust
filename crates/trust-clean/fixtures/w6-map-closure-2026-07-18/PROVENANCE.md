# w6-map-closure-2026-07-18 — the W6 increment-1 target corpus

14 W16 mono dumps covering every link of the closure-composition chain:
5 wrappers, 4 monomorphized Option::<i32>::{map,and_then,filter} instances,
5 closure bodies. Baseline: 10 SHAPE_GAP / 2 SAFETY_GAP / 2 FULLY_FAITHFUL
(and_then_pos + filter_pos closures already certify as leaves!).

KEY MIR FACTS (key-bodies.txt has the 3 crucial bodies):
- The closure call inside mono map is an EXPLICIT `<{closure@span} as
  FnOnce<(i32,)>>::call_once(move env, move (x,))` Call — NOT inlined, span-string
  func name (no def_path_hash) → callee identity must come from the env operand's
  Ty::Closure.name, EXACT match only (the adversarial phase killed suffix fallback).
- Closure bodies: arg_count=2, _1=env (by-value Closure{upvars,call{kind,params,ret}}
  for FnOnce; &Closure for Fn), upvars = field projections _1.0 (map_cap's sole
  SHAPE_GAP cause — the closure-env-projection increment).
- Non-capturing closures pass as Constant::CallableItem{def_path, def_path_hash};
  capturing build Aggregate[Closure{captures}](copy k).
- |x| x+1 is EXCLUDED from increment 1: its CheckedAdd overflow assert is
  spec-free-undischargeable over full-range i32 (honest).

Design + adversarial verdicts: w6-closure-design workflow (wf_72cc97f9) —
feasible, MODEL-ONLY split-claims tier; 1 CONFIRMED-SOUND (capture gate is
type-authoritative) + 2 NEEDS-GATE converging on EXACT-MATCH-ONLY callee
resolution for the closure lane.
