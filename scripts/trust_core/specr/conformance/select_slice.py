#!/usr/bin/env python3
"""K8 probe: select the minitest tests that exercise only the integer, pointer
and call slice.

usage: select_slice.py <records.jsonl> <schema.json> <out selection.json>

A test is IN the slice iff it ran at least one MiniRust program through the
harness and every one of its recorded runs satisfies all of:
  * entry point `run_program` (stdout-comparing `get_stdout` tests are out:
    PrintStdout/PrintStderr are not in the slice);
  * the test asserts one deterministic outcome: stop, ub, ill_formed, abort or
    memory_leak (`assert_stop_always`, `assert_ub_eventually`, data-race and
    deadlock probes exercise non-determinism and concurrency);
  * the program has no traits and no vtables;
  * every enum value in the program uses a constructor in ALLOWED below, and
    every tuple type is sized (no unsized tail).
The predicate is fixed here, before any conformance run against Clean.
"""

import json
import sys
from mrjson import Walker

ALLOWED = {
    'Type': {'Int', 'Bool', 'Ptr', 'Tuple'},
    'PtrType': {'Ref', 'Box', 'Raw', 'FnPtr'},
    'PointerMetaKind': {'None'},
    'LayoutStrategy': {'Sized'},
    'UnsafeCellStrategy': {'Sized'},
    'ValueExpr': {'Constant', 'Tuple', 'Load', 'AddrOf', 'UnOp', 'BinOp'},
    'Constant': {'Int', 'Bool', 'GlobalPointer', 'FnPointer', 'PointerWithoutProvenance'},
    'UnOp': {'Int', 'Cast'},
    'IntUnOp': {'Neg', 'BitNot', 'CountOnes'},
    'CastOp': {'IntToInt', 'Transmute'},
    'BinOp': {'Int', 'IntWithOverflow', 'Rel', 'PtrOffset', 'PtrOffsetFrom'},
    'IntBinOp': None,             # all
    'IntBinOpWithOverflow': None,  # all
    'RelOp': None,                # all
    'PlaceExpr': {'Local', 'Deref', 'Field'},
    'Statement': {'Assign', 'PlaceMention', 'Validate', 'Deinit', 'StorageLive', 'StorageDead'},
    'Terminator': {'Goto', 'Switch', 'Unreachable', 'Intrinsic', 'Call', 'Return'},
    'ArgumentExpr': None,
    'CallingConvention': None,
    'IntrinsicOp': {'Exit', 'Abort', 'Assume', 'Allocate', 'Deallocate', 'PointerExposeProvenance'},
    'BbKind': {'Regular'},
    'Mutability': None,
    'Signedness': None,
}
EXPECT_KINDS = {'stop', 'ub', 'ill_formed', 'abort', 'memory_leak'}


def main():
    recs = [json.loads(l) for l in open(sys.argv[1])]
    schema = json.load(open(sys.argv[2]))
    w = Walker(schema)
    tests = {}
    for idx, r in enumerate(recs):
        t = tests.setdefault(r['test'], {'records': [], 'reasons': set()})
        t['records'].append(idx)
        if r['entry'] != 'run_program':
            t['reasons'].add(f'entry:{r["entry"]}')
        exp = r.get('expect')
        if exp is None or exp['kind'] not in EXPECT_KINDS:
            t['reasons'].add(f'expect:{exp["kind"] if exp else "none"}')
        p = r['program']
        if p['traits'] or p['vtables']:
            t['reasons'].add('program:traits-or-vtables')

        def visit(adt, variant, payload):
            if adt == 'Type' and variant == 'Tuple' and payload.get('unsized_field') is not None:
                t['reasons'].add('Type::Tuple with unsized field')
            if variant is None or adt not in ALLOWED:
                return
            allowed = ALLOWED[adt]
            if allowed is not None and variant not in allowed:
                t['reasons'].add(f'{adt}::{variant}')
        w.walk(p, ('adt', 'Program'), visit)
    out = {}
    for name in sorted(tests):
        t = tests[name]
        out[name] = {'in_slice': not t['reasons'], 'records': t['records'], 'excluded_by': sorted(t['reasons'])}
    json.dump({'predicate': __doc__, 'allowed_constructors': {k: (sorted(v) if v else 'all') for k, v in ALLOWED.items()},
               'tests': out,
               'counts': {'tests_recorded': len(out), 'in_slice': sum(1 for x in out.values() if x['in_slice'])}},
              open(sys.argv[3], 'w'), indent=1, sort_keys=True)
    print(json.dumps({'tests_recorded': len(out), 'in_slice': sum(1 for x in out.values() if x['in_slice'])}))


if __name__ == '__main__':
    main()
