"""Actual command graph for original629; checking it creates no seed authority."""
from __future__ import annotations

import re
from pathlib import Path

COMMANDS = (
    'external-bootstrap', 'candidate-self-host', 'diverse-ddc', 'dist',
    'full-native-build', 'build-manifest', 'channel-manifest', 'original-trustd',
    'native-pack', 'native-unpack', 'prepare-seed', 'install-seed-trust-std',
    'install-seed-trustc', 'install-seed-trustc-dev', 'install-seed-targo',
    'install-seed-trustfmt', 'archive-rebuild',
)
SPANS = (
    'inputs-before', 'candidate-identity', 'original-trustd-copy',
    'rustdoc-alias-copy', 'full-native-tools', 'full-native-runtime',
    'packaged-native-tools', 'packaged-native-runtime', 'cohort-assembly',
    'installed-seed-surface', 'installed-seed-runtime', 'inputs-after',
)


class CommandGraph:
    def __init__(self, source, work, host, deadline, xpy, orchestration, dist_components):
        self.source, self.work, self.host, self.deadline, self.xpy = source, work, host, deadline, xpy
        self.commands, self.spans = [], []
        self.orchestration, self.dist_components = orchestration, tuple(dist_components)

    def command(self, phase, argv, cwd, environment):
        position = len(self.commands)
        if position >= len(COMMANDS) or phase != COMMANDS[position]:
            raise ValueError('missing, extra or reordered producer command')
        if str(cwd) != str(self.source) or not isinstance(argv, list) or not argv:
            raise ValueError('producer command changed cwd or argument shape')
        if environment.get('CARGO_NET_OFFLINE') != 'true' or environment.get('CARGO_BUILD_JOBS') != '1':
            raise ValueError('producer command is not original offline single-job execution')
        if environment.get('TRUST_SEED_STAIRCASE') != '1':
            raise ValueError('original629 staircase is absent')
        # Every actual vector is checked before launch by the source-bound live
        # context. Artifact/config joins still belong to the non-admitting next
        # stage; no caller-supplied command transcript grants seed authority.
        if phase in {'external-bootstrap','candidate-self-host','diverse-ddc','dist',
                     'full-native-build','build-manifest','archive-rebuild'}:
            config = self.work / ('bootstrap.external.toml' if phase == 'external-bootstrap' else
                'bootstrap.ddc.toml' if phase == 'diverse-ddc' else
                'bootstrap.archive.toml' if phase == 'archive-rebuild' else 'bootstrap.self-host.toml')
            build = self.work / ('external-build' if phase == 'external-bootstrap' else 'comparison-build')
            verb = 'dist' if phase == 'dist' else 'build'
            tail = {'external-bootstrap': ('compiler/rustc','library/std','src/tools/targo','src/tools/trustdoc','src/tools/trustfmt'),
                    'candidate-self-host': ('compiler/rustc','library/std'),
                    'diverse-ddc': ('compiler/rustc','library/std'),
                    'archive-rebuild': ('compiler/rustc','library/std'),
                    'full-native-build': (), 'build-manifest': ('src/tools/build-manifest',)}
            tail['dist'] = self.dist_components
            if argv != self.xpy(self.source,config,build,self.host,verb,*tail[phase]):
                raise ValueError('actual xpy command differs from original629 graph')
        candidate = self.work / 'external-build' / self.host / 'stage2'
        stage2 = self.work / 'comparison-build' / self.host / 'stage2'
        dist = self.work / 'comparison-build/dist'
        native_pack = self.work / f'trust-native-629729f69eef-{self.host}.tar.xz'
        expected = None
        if phase == 'channel-manifest':
            tool = argv[0]
            prefix = str(self.work / 'comparison-build' / self.host) + '/'
            if not tool.startswith(prefix) or not re.fullmatch(
                    r'stage[0-9]+-tools-bin/' + re.escape(self.host) + r'/build-manifest', tool[len(prefix):]):
                raise ValueError('manifest tool is not an actual bootstrap build product')
            expected = [tool,str(dist),str(dist),'2026-07-13','https://trust.invalid','trust']
        elif phase == 'original-trustd':
            expected = [str(candidate / 'bin/targo'),'build','--release','--locked','--offline',
                        '--manifest-path',str(self.source / 'Cargo.toml'),'-p','trust-router',
                        '--bin','trustd','--target',self.host]
            if any(environment.get(key) != value for key,value in {
                'RUSTC':str(candidate/'bin/trustc'),'RUSTDOC':str(candidate/'bin/trustdoc'),
                'CARGO_TARGET_DIR':str(self.work/'original-trustd-target'),'TRUST_NO_VERIFY':'1'}.items()):
                raise ValueError('historical daemon build changed actual compiler or target')
        elif phase == 'native-pack':
            entries = [name for name in ('bin','lib','libexec') if (stage2 / name).is_dir()]
            expected = ['/usr/bin/tar','--create','--xz','--file',str(native_pack),
                        '--exclude=lib/rustlib/src','--exclude=lib/rustlib/rustc-src',
                        '--directory',str(stage2),*entries]
        elif phase == 'native-unpack':
            expected = ['/usr/bin/tar','--extract','--xz','--no-same-owner','--same-permissions',
                        '--file',str(native_pack),'--directory',str(self.work/'native-installation')]
        elif phase == 'prepare-seed':
            prepared = self.work/'prepared-native-only'
            expected = ['/usr/bin/python3','-I','-S','-B',
                str(self.orchestration/'src/tools/trust-stage0-dist/prepare.py'),
                '--input-dist',str(dist),'--source-channel','trust','--owned-channel','trust',
                '--archive-format','xz','--stage0-seed-only','--git-commit-hash',
                '629729f69eefb1cfe6ed766c6c01ee38aa7b0484','--date','2026-07-13',
                '--dist-server','file://repo','--output-root',str(prepared/'bootstrap/trust-stage0'),
                '--stage0-output',str(prepared/'src-stage0')]
        elif phase.startswith('install-seed-'):
            component = phase.removeprefix('install-seed-')
            installer = Path(argv[0])
            parent = self.work/'unpack'/component
            if installer.parent.parent != parent or installer.name != 'install.sh':
                raise ValueError('installer escaped actual selected component unpack tree')
            expected = [str(installer),'--prefix='+str(self.work/'seed-installation'),'--disable-ldconfig']
        if expected is not None and argv != expected:
            raise ValueError('actual native command differs from original629 graph')
        self.commands.append(dict(phase=phase, argv=list(argv), cwd=str(cwd), environment=dict(environment)))

    def span(self, name):
        position = len(self.spans)
        if position >= len(SPANS) or name != SPANS[position]:
            raise ValueError('missing, extra or reordered producer span')
        self.spans.append(name)

    def finish(self):
        if tuple(row['phase'] for row in self.commands) != COMMANDS or tuple(self.spans) != SPANS:
            raise ValueError('native producer command/span graph is incomplete')
