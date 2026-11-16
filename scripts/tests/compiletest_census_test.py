#!/usr/bin/env python3
"""Adversarial tests of the diagnostic reader, with no compiler/proof authority."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from compiletest_census import SCHEMA, read_census, join_observations, boolean_lane


class CensusReaderTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        def output(name):
            p = self.path/name
            p.write_bytes(b'')
            return {'path': str(p), 'bytes': 0, 'sha256': hashlib.sha256(b'').hexdigest()}
        self.rows = [
            {'event': 'begin'},
            {'event': 'planned', 'case': 'a', 'source': {'status': 'unmeasured'}},
            {'event': 'plan-complete', 'planned': 1},
            {'event': 'selection', 'cases': ['a']},
            {'event': 'command-attempt', 'command': 0, 'case': 'a', 'kind': 'other-command', 'argv': [], 'cwd': str(self.path), 'argument_files': []},
            {'event': 'command-spawned', 'command': 0, 'pid': 5},
            {'event': 'command-terminal', 'command': 0, 'success': True, 'exit_code': 0, 'stdout': output('stdout'), 'stderr': output('stderr'), 'output_truncated': False, 'observations': [], 'argument_files_after': []},
            {'event': 'case-terminal', 'case': 'a', 'outcome': 'ok'},
            {'event': 'end', 'suite_passed': True, 'pending_cases': [], 'pending_commands': [], 'authority': 'diagnostic-only', 'runtime_body_universe': 'unmeasured'},
        ]

    def write(self, rows=None):
        previous = None
        raw = b''
        for i, row in enumerate(copy.deepcopy(self.rows if rows is None else rows)):
            row.update(schema=SCHEMA, sequence=i, previous_record_sha256=previous)
            line = (json.dumps(row)+'\n').encode()
            previous = hashlib.sha256(line).hexdigest()
            raw += line
        (self.path/'events.jsonl').write_bytes(raw)

    def read(self):
        return read_census(self.path)

    def test_valid_is_only_diagnostic(self):
        self.write()
        report = self.read()
        self.assertFalse(report['whole_corpus_complete'])
        self.assertEqual(report['recording_status'], 'footer-present')

    def test_unselected_self_test_keeps_its_population_and_unavailable_properties(self):
        rows = copy.deepcopy(self.rows)
        rows.insert(2, {
            'event': 'planned', 'case': 'negative-self-test',
            'source': {'status': 'unmeasured'}, 'revision': 'bad',
            'all_revisions': ['good', 'bad', 'bad-space'],
            'expected_harness_failure': True,
            'properties_status': 'deferred-to-expected-failure-self-test-execution',
            'compile_flags': None, 'run_flags': None,
            'source_directives': ['//@[bad] compile-flags: -Cincremental=true'],
        })
        rows[3]['planned'] = 2
        self.write(rows)
        report = self.read()
        self.assertEqual(len(report['planned']), 2)
        deferred = report['planned'][1]
        self.assertFalse(deferred['selected'])
        self.assertIsNone(deferred['terminal'])
        self.assertIsNone(deferred['compile_flags'])
        self.assertEqual(deferred['all_revisions'], ['good', 'bad', 'bad-space'])
        self.assertEqual(deferred['source_directives'], rows[2]['source_directives'])
        self.assertFalse(report['whole_corpus_complete'])

    def test_interrupted_is_not_completed(self):
        self.write(self.rows[:-1])
        self.assertEqual(self.read()['recording_status'], 'interrupted')

    def test_omitted_case_rechaining_still_refuses(self):
        self.write([r for r in self.rows if r['event'] != 'planned'])
        with self.assertRaises(ValueError): self.read()

    def test_omitted_command_terminal_refuses(self):
        self.write([r for r in self.rows if r['event'] != 'command-terminal'])
        with self.assertRaises(ValueError): self.read()

    def test_duplicate_or_rebound_command_refuses(self):
        for mutate in ('case', 'command'):
            rows = copy.deepcopy(self.rows)
            rows[4][mutate] = 'different' if mutate == 'case' else 99
            self.write(rows)
            with self.assertRaises(ValueError): self.read()

    def test_payload_mutation_refuses(self):
        self.write()
        (self.path/'stderr').write_bytes(b'changed')
        with self.assertRaises(ValueError): self.read()

    def test_artifact_escape_refuses(self):
        rows = copy.deepcopy(self.rows)
        rows[6]['stderr']['path'] = str(self.path.parent/'other')
        self.write(rows)
        with self.assertRaises(ValueError): self.read()

    def test_status_contradiction_refuses(self):
        rows = copy.deepcopy(self.rows)
        rows[6]['exit_code'] = 1
        self.write(rows)
        with self.assertRaises(ValueError): self.read()

    def test_extra_after_footer_refuses(self):
        self.write(self.rows+[{'event': 'case-terminal', 'case': 'a', 'outcome': 'ok'}])
        with self.assertRaises(ValueError): self.read()

    def test_truncated_and_duplicate_json_refuse(self):
        self.write()
        p = self.path/'events.jsonl'
        data = p.read_bytes()
        p.write_bytes(data[:-1])
        with self.assertRaises(ValueError): self.read()
        p.write_bytes(data.replace(b'"event": "begin"', b'"event": "begin", "event": "begin"', 1))
        with self.assertRaises(ValueError): self.read()

    def test_relative_program_cannot_borrow_absolute_file_binding(self):
        source = self.path/'input.rs'
        source.write_text('pub fn f() {}')
        compiler = Path(sys.executable).resolve()
        def file_row(path):
            raw = path.read_bytes()
            return {'path': str(path), 'status': 'read', 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}
        observed = self.path/'hir'
        observed.write_bytes(b'{}\n')
        artifact = file_row(observed)
        artifact.pop('status')
        args = [str(source), '--crate-type=rlib']
        attempt = {'kind': 'selected-rustc', 'cwd': str(self.path),
                   'program': {'utf8': compiler.name, 'encoded_bytes_hex': compiler.name.encode().hex()},
                   'program_file': file_row(compiler), 'argument_files': [file_row(source)],
                   'argv': [{'utf8': a, 'encoded_bytes_hex': a.encode().hex()} for a in args]}
        terminal = {'exit_code': 0, 'program_after': file_row(compiler),
                    'argument_files_after': [file_row(source)],
                    'observations': [{'kind': 'trust-body-census', 'status': 'retained-unvalidated', 'artifact': artifact}]}
        result = join_observations(self.path, attempt, terminal)
        self.assertEqual(result[0]['status'], 'unjoined')

    def test_strict_lowering_is_a_measured_enabled_lane(self):
        self.assertTrue(boolean_lane(['-Ztrust-ir-lower=strict'], 'trust-ir-lower'))


if __name__ == '__main__':
    unittest.main()
