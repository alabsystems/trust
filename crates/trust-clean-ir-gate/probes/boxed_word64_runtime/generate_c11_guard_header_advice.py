#!/usr/bin/env python3
"""Retain a WHOLE owner header as untrusted guard-proof advice, never a tail."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def generate(declarations, owners, name, out):
    out.mkdir()
    matches = [row for row in json.loads(declarations.read_text()) if row['name'] == name]
    assert len(matches) == 1
    row = matches[0]
    digest = row['owner_sha256']
    assert re.fullmatch('[0-9a-f]{64}', digest)
    raw = (owners / digest).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest
    assert raw[row['begin']:row['end']].decode('utf-8') == row['raw']
    # Select the complete original owner, not the proposed declaration span.
    (out / 'uint32Full.h').write_bytes(raw)
    (out / 'ROWS.json').write_text(json.dumps([{
        'name': 'uint32Full', 'raw': raw.decode('utf-8'), 'owner': row['owner'],
        'sha256': digest, 'scope': 'WHOLE captured owner; no active-TU/profile claim'
    }], indent=2) + '\n')
    (out / 'C11GuardHeaderData.lean').write_text(
        '-- Copyright 2026 Andrew Yates | Apache-2.0\nimport Init\nnamespace C11GuardHeaderData\n'
        'def uint32Full_0 : String := ' + json.dumps(raw.decode('utf-8'), ensure_ascii=False) +
        '\nend C11GuardHeaderData\n')
    files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in out.iterdir() if p.is_file()}
    (out / 'INDEX.json').write_text(json.dumps({'files': files, 'owner_sha256': digest,
        'owner_bytes': len(raw), 'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'untrusted complete-owner DATA only'}, indent=2) + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--declarations', type=Path, required=True)
    p.add_argument('--owners', type=Path, required=True)
    p.add_argument('--name', required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    generate(a.declarations, a.owners, a.name, a.out)
