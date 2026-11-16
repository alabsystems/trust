#!/usr/bin/env python3
"""Real native Targo filename-boundary consumer; no SDK or proof qualification."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

CASES = {'trailing-space': 'leaf.rs ', 'terminal-backslash': 'leaf.rs\\',
         'terminal-carriage-return': 'leaf.rs\r', 'terminal-newline': 'leaf.rs\n'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--targo', type=Path, required=True)
    parser.add_argument('--rustc', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--cases', nargs='+', choices=CASES, default=list(CASES))
    args = parser.parse_args()
    assert os.name == 'posix', 'these are actual Unix filenames'
    assert args.evidence.is_absolute() and not args.evidence.exists(), 'new owned evidence required'
    for path in (args.targo, args.rustc):
        assert path.is_absolute() and path.is_file(), 'explicit native producers required'
    args.evidence.mkdir(mode=0o700, parents=True)
    for tool, role in ((args.targo, 'targo'), (args.rustc, 'rustc')):
        command = [str(tool), '--unverified', '--version', '--verbose'] if role == 'targo' else [str(tool), '-vV']
        result = subprocess.run(command, capture_output=True)
        (args.evidence / (role + '.version')).write_bytes(result.stdout + result.stderr)
        assert result.returncode == 0, 'actual native producer observation refused'
    observations = []
    for label in args.cases:
        project = args.evidence / label
        source = project / 'src'
        source.mkdir(parents=True)
        (project / 'Cargo.toml').write_text('[package]\nname="boundary_probe"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
        (source / 'main.rs').write_text('#[path=' + json.dumps(CASES[label]) + '] mod leaf;\nfn main(){println!("{}",leaf::answer());}\n')
        leaf = source / CASES[label]
        leaf.write_text('pub fn answer()->u32{42}\n')
        decoy = source / ('leaf.rs\\ ' if label == 'trailing-space' else 'leaf.rs')
        decoy_text = 'pub fn answer()->u32{42}\n' if label == 'terminal-newline' else 'pub fn answer()->u32{99}\n'
        decoy.write_text(decoy_text)
        environment = os.environ.copy()
        for flag in ('RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER'):
            assert not environment.get(flag), 'unsupported caller compiler channel: ' + flag
        environment.update(RUSTC=str(args.rustc), CARGO_HOME=str(project / 'home'), CARGO_TARGET_DIR=str(project / 'target'))
        command = [str(args.targo), '--unverified', '--config', 'target.aarch64-apple-darwin.linker="/usr/bin/cc"',
                   'run', '--offline', '--message-format=json', '-j', '1']
        for phase in ('cold', 'warm', 'changed', 'warm-changed'):
            expected = 43 if phase in ('changed', 'warm-changed') else 42
            if phase == 'changed':
                before = leaf.stat()
                leaf.write_text('pub fn answer()->u32{43}\n')
                os.utime(leaf, ns=(before.st_atime_ns, before.st_mtime_ns))
                assert leaf.stat().st_size == before.st_size and leaf.stat().st_mtime_ns == before.st_mtime_ns
            result = subprocess.run(command, cwd=project, env=environment, capture_output=True)
            (project / (phase + '.stdout')).write_bytes(result.stdout)
            (project / (phase + '.stderr')).write_bytes(result.stderr)
            fresh, values, causes = [], [], []
            for line in result.stdout.splitlines():
                try:
                    row = json.loads(line)
                except ValueError:
                    continue
                if type(row) is int:
                    values.append(row)
                elif type(row) is dict:
                    if row.get('reason') == 'compiler-artifact':
                        fresh.append(row['fresh'])
                    if row.get('reason') == 'compilation-unit-dispatched':
                        causes.append(row.get('dirty_reason'))
            observation = dict(case=label, phase=phase, exit=result.returncode, fresh=fresh, values=values, dirty_reason=causes,
                               actual_sha256=hashlib.sha256(leaf.read_bytes()).hexdigest(),
                               decoy_sha256=hashlib.sha256(decoy.read_bytes()).hexdigest())
            observations.append(observation)
            (args.evidence / 'observations.json').write_text(json.dumps(observations, indent=2) + '\n')
            print(json.dumps(observation), flush=True)
            assert result.returncode == 0 and values == [expected], 'actual consumer failed or read the decoy'
            expected_fresh = label != 'terminal-newline' and phase in ('warm', 'warm-changed')
            assert fresh == [expected_fresh], 'native filename freshness boundary failed'
            if label == 'terminal-newline' and phase != 'cold':
                assert 'content-fingerprint-unavailable' in causes, 'ambiguous input did not take the typed refusal'
            assert decoy.read_text() == decoy_text, 'decoy was changed'
    return 0

if __name__ == '__main__':
    sys.exit(main())
