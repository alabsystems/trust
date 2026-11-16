#!/usr/bin/env python3
"""Per-test result table from a `clean check --json` report and the theorem index.

usage: summarize.py <check report.json> <conformance_index.json> <out.json>
"""

import json
import sys


def main():
    rep = json.load(open(sys.argv[1]))
    idx = json.load(open(sys.argv[2]))
    failed = set()
    for e in rep['errors']:
        failed.add(e.split(':')[0].strip())
    tests = {}
    for th in idx['theorems']:
        t = tests.setdefault(th['test'], {'theorems': [], 'expect': [], 'failed': []})
        t['theorems'].append(th['theorem'])
        t['expect'].append(th['expect'])
        if th['theorem'] in failed:
            t['failed'].append(th['theorem'])
    out = {'steps': idx['steps'], 'fuel': idx['fuel'],
           'declarations': rep['decl_count'], 'declarations_passed': rep['success_count'],
           'declarations_failed': rep['failed_count'], 'diverged': rep['diverged_count'],
           'trust_summary': rep['trust_summary'],
           'tests': {k: {'theorems': v['theorems'], 'pass': not v['failed'], 'failed_theorems': v['failed'],
                         'expect': v['expect']} for k, v in sorted(tests.items())}}
    out['counts'] = {'tests': len(tests), 'tests_passed': sum(1 for v in out['tests'].values() if v['pass']),
                     'tests_failed': sum(1 for v in out['tests'].values() if not v['pass']),
                     'theorems': len(idx['theorems'])}
    json.dump(out, open(sys.argv[3], 'w'), indent=1)
    print(json.dumps(out['counts']))
    for k, v in out['tests'].items():
        if not v['pass']:
            print('FAILED', k, v['failed_theorems'])


if __name__ == '__main__':
    main()
