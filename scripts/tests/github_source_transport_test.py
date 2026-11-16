#!/usr/bin/env python3
"""GitHub submodule reads preserve routing and refuse malformed evidence."""
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch
SUBJECT = 'scripts/lib/github_source_transport.py'
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'lib'))
# Subject: scripts/lib/github_source_transport.py
import github_source_transport as transport

class TransportTests(unittest.TestCase):
    def test_repository_transports(self):
        for url in ('https://github.com/owner/repo.git', 'git@github.com:owner/repo.git',
                    'ssh://git@github.com/owner/repo.git'):
            self.assertEqual(transport.github_repository(url), 'owner/repo')
        for url in ('/local/repo', 'file:///local/repo', 'https://example.org/repo'):
            self.assertIsNone(transport.github_repository(url))
        for url in ('https://token@github.com/owner/repo', 'https://github.com/owner/repo?token=x',
                    'ssh://other@github.com/owner/repo', 'github.com:owner/repo',
                    'https://github.com./owner/repo'):
            with self.assertRaises(ValueError): transport.github_repository(url)

    def read(self, rows):
        result = subprocess.CompletedProcess([], 0, json.dumps(rows), '')
        with patch.object(transport.remote_tips, '_agh', return_value=result) as agh:
            output = transport.pin_refs('git@github.com:owner/repo.git', 7)
            self.assertEqual(agh.call_args.args, ('owner/repo', ['repo', 'refs', 'owner/repo']))
            self.assertEqual(agh.call_args.kwargs['timeout'], 7)
            return output

    def test_only_exact_pin_advertisements(self):
        oid = 'a' * 40
        self.assertEqual(self.read([{'ref': 'refs/heads/main', 'oid': oid},
                                   {'ref': 'refs/pins/release', 'oid': oid}]),
                         [oid + ' refs/pins/release'])

    def test_malformed_and_conflicting_rows_refuse(self):
        for rows in ({}, [{}], [{'ref': 'refs/pins/x', 'oid': 'invalid'}],
                     [{'ref': 'refs/pins/x', 'oid': 'a'*40},
                      {'ref': 'refs/pins/x', 'oid': 'b'*40}]):
            with self.assertRaises(ValueError): self.read(rows)

    def test_provider_refusal_is_terminal(self):
        with patch.object(transport.remote_tips, '_agh', return_value=
                          subprocess.CompletedProcess([], 73, '', 'owner refused')) as agh:
            with self.assertRaisesRegex(RuntimeError, 'owner refused'):
                transport.pin_refs('https://github.com/owner/repo', 7)
            self.assertEqual(agh.call_count, 1)

if __name__ == '__main__': unittest.main()
