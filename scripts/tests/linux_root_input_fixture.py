"""Tiny physical-continuation fixture; NOT an original629 native owner.

Only authored unit controls use these toy commits, archives and inert custody.
They cannot enter observe()/ClosedProducerObservation or grant native authority.
All fixture execution remains UNRUN in the source proposal.
"""
from __future__ import annotations
import hashlib
import ast
import io
import json
import os
from pathlib import Path
import subprocess
import stat
import sys
import tarfile
import time
import types

HERE = Path(__file__).resolve().parents[1]

# Exact canonical helper closure for these physical-input controls. New imports
# fail closed in BoundSourceLoader until this explicit roster is reviewed.
# Do not discover Python in the checkout: build trees/submodules are unrelated.
FIXTURE_HELPER_SOURCES = (
    'src/bootstrap/stage0_identity.py',
    'scripts/seed_input_closure.py',
    'scripts/seed_input_records.py',
    'scripts/seed_input_committed.py',
    'scripts/seed_input_archives.py',
    'scripts/bootstrap_dependency_closure.py',
    'scripts/initialize_linux_root_seed.py',
    'scripts/mint_seed_support.py',
    'scripts/seed_host_ledger.py',
    'scripts/seed_root_initialization.py',
    'scripts/lib/seed_linux.py',
)
FIXTURE_SOURCE_LIMIT = 4 * 1024 * 1024


def fixture_source(path):
    # Bootstrap only the one known loader; its regular_bytes then authenticates
    # each fixed helper with before/after retained-descriptor identity checks.
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW | os.O_CLOEXEC)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_size > FIXTURE_SOURCE_LIMIT:
            raise ValueError('fixture loader source is not a bounded regular file')
        with os.fdopen(fd, 'rb', closefd=False) as stream:
            raw = stream.read(FIXTURE_SOURCE_LIMIT + 1)
        if len(raw) > FIXTURE_SOURCE_LIMIT:
            raise ValueError('fixture loader source exceeded its finite bound')
        return raw
    finally:
        os.close(fd)


def modules():
    path = HERE / 'seed_custody_source.py'
    namespace = types.ModuleType('input_control_source_loader')
    namespace.__file__ = str(path)
    exec(compile(fixture_source(path),str(path),'exec',dont_inherit=True),namespace.__dict__)
    root = HERE.parent
    hashes = {relative:hashlib.sha256(namespace.regular_bytes(root / relative)).hexdigest()
              for relative in FIXTURE_HELPER_SOURCES}
    loader = namespace.BoundSourceLoader(root,hashes)
    closure = loader.module('test_physical_input_closure',HERE / 'seed_input_closure.py')
    auth = loader.module('test_physical_input_auth',HERE / 'initialize_linux_root_seed.py')
    return loader,closure,auth


def write(path, data, mode=0o644):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(data)
    path.chmod(mode)


def make_archive(path, members, mode='w:xz'):
    path.parent.mkdir(parents=True,exist_ok=True)
    with tarfile.open(path,mode) as archive:
        for name,data,permissions in members:
            info = tarfile.TarInfo(name)
            info.mode = permissions
            if data is None:
                info.type = tarfile.DIRTYPE
                archive.addfile(info)
            else:
                info.size = len(data)
                archive.addfile(info,io.BytesIO(data))
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(root,*args):
    result = subprocess.run(['/usr/bin/git','--no-optional-locks','-C',str(root),*args],
        env={'PATH':'/usr/bin:/bin','HOME':'/','GIT_CONFIG_NOSYSTEM':'1',
             'GIT_CONFIG_GLOBAL':'/dev/null','LC_ALL':'C'},capture_output=True,text=True,timeout=10)
    if result.returncode:
        raise AssertionError(result.stderr)
    return result.stdout.strip()


class LiveFixture:
    def __init__(self,end):
        self.payload = {'deadline':end}
        self.seals = []

    def event(self,kind,**value):
        assert kind == 'input-seal'
        self.seals.append(value)


class PhysicalFixture:
    def __init__(self,root,loader,closure,auth):
        self.root,self.loader,self.closure,self.auth = root,loader,closure,auth
        self.end = time.monotonic() + 120
        self.host = 'x86_64-unknown-linux-gnu'
        self.source = root / 'source'
        self.source.mkdir()
        self.work = self.source / 'build/run'
        self.cache = root / 'supplier-cache'
        self.cache.mkdir()
        self.tool = root / 'native/bin/tool'
        write(self.tool,b'unit fixture executable bytes\n',0o755)
        llvm = root / 'llvm/bin/llvm-config'
        write(llvm,b'unit fixture llvm bytes\n',0o755)
        config = '[target.' + json.dumps(self.host) + ']\n'
        for name in ('llvm-config','cc','cxx','ar','ranlib','linker'):
            config += json.dumps(name) + ' = ' + json.dumps(str(llvm if name == 'llvm-config' else self.tool)) + '\n'
        write(self.source / 'input.toml',config.encode())
        write(self.source / '.gitignore',b'/build/\n')
        write(self.source / 'main.rs',b'fn main() {}\n')
        write(self.source / 'Cargo.lock',b'version = 3\n')
        for directory in ('', 'library', 'src/bootstrap'):
            write(self.source / directory / 'Cargo.toml', b'[workspace]\nmembers = []\n')
            write(self.source / directory / 'Cargo.lock', b'version = 3\n')
        graph_source = (HERE / 'recreate_bootstrap.py').read_text()
        graph = next(node for node in ast.parse(graph_source).body
                     if isinstance(node, ast.ClassDef) and node.name == '_Stage0ManifestGraph')
        write(self.source / 'scripts/recreate_bootstrap.py', ast.get_source_segment(graph_source, graph).encode())
        write(self.source / 'nested/git_mode',b'legal Git filename\n')
        (self.source / 'source-link').symlink_to('main.rs')
        git(self.source,'init','-q')
        git(self.source,'add','.')
        git(self.source,'-c','user.name=Input Fixture','-c','user.email=fixture@example.invalid',
            'commit','-qm','physical input fixture')
        self.commit = git(self.source,'rev-parse','HEAD')
        summary = auth.source_snapshot(self.source,self.commit)
        values = {'source_root':self.source,'config':self.source/'input.toml','cargo_home':self.cache,
                  'work_dir':self.work,'host':self.host,'std_source_archive':root/'shared.tar.xz',
                  'legacy_receipt':root/'legacy.json','legacy_archives':root/'legacy-archives',
                  'legacy_manifest':root/'legacy.toml'}
        write(values['std_source_archive'],b'fixture shared source bytes')
        write(values['legacy_receipt'],b'{}\n')
        write(values['legacy_manifest'],b'fixture legacy manifest bytes\n')
        values['legacy_archives'].mkdir()
        roots = {}
        for role in ('genesis','ddc'):
            sysroot,dist = root/(role+'-sysroot'),root/(role+'-archives')
            sysroot.mkdir()
            dist.mkdir()
            channel = ''
            for name,payload in (('rustc','bin/rustc'),('cargo','bin/cargo'),('rust-std','lib/libstd.rlib')):
                filename = name + '-fixture-' + self.host + '.tar.xz'
                top = filename.removesuffix('.tar.xz')
                inner = 'rust-std-' + self.host if name == 'rust-std' else name
                mode = 0o755 if payload.startswith('bin/') else 0o644
                data = (role + '-' + name + '-original').encode()
                write(sysroot/payload,data,mode)
                parent = payload.rsplit('/',1)[0]
                # Match the installer's archived directory mode despite umask077.
                (sysroot/parent).chmod(0o755)
                sha = make_archive(dist/filename,[(top,None,0o755),(top+'/'+inner,None,0o755),
                    (top+'/'+inner+'/'+parent,None,0o755),(top+'/'+inner+'/'+payload,data,mode)])
                channel += ('[pkg.'+json.dumps(name)+'.target.'+json.dumps(self.host)+']\n'
                            'available = true\nxz_url = '+json.dumps('https://static.rust-lang.org/dist/'+filename)+
                            '\nxz_hash = '+json.dumps(sha)+'\n')
            manifest = root/(role+'.toml')
            write(manifest,channel.encode())
            values[role+'_manifest'],values[role+'_archives'],values[role+'_sysroot'] = manifest,dist,sysroot
            roots[role] = {'runtime':{'observations':{},'links':{}}}
        self.values = values
        self.args = types.SimpleNamespace(**values)
        self.inputs = {'authenticated':{'host':self.host,'source':summary,'external_roots':roots},
            'orchestration':summary,'config':{'files':[{'relative_path':'input.toml'}]},
            'legacy_cohort_inputs':{'archives':{}},
            'producer_interpreter':{'path':str(Path(sys.executable).resolve(strict=True))}}
        self.work.mkdir(parents=True)
        self.live = LiveFixture(self.end)
        self.session = closure.CaptureSession(self.args,self.work,self.inputs,auth,self.end,self.live)
        # Unit fixture uses its own committed source for both source families;
        # production always uses the actual authenticated orchestration root.
        self.session.orchestration = self.source

    def common_files(self):
        (self.work/'cargo-home').mkdir()
        (self.work/'safe-bin').mkdir()
        (self.work/'safe-bin/tool').symlink_to(self.tool)
        for name in ('base','external','self-host','ddc'):
            write(self.work/('bootstrap.'+name+'.toml'),b'fixture original config\n')

    def installers(self):
        for name in ('artifacts','unpack','prepared-native-only','prepared-cohort'):
            (self.work/name).mkdir()
        support = self.auth.support
        rows,pins = [],'compiler_date=2026-07-13\n'
        for component in support.COMPONENTS:
            filename = component+'-1.99.0-trust-'+self.host+'.tar.xz'
            top = filename.removesuffix('.tar.xz')
            installer = b'#!/bin/sh\nexit 0\n'
            payload = b'fixture canonical payload\n'
            sha = make_archive(self.work/'artifacts'/filename,
                [(top,None,0o755),(top+'/install.sh',installer,0o755),(top+'/payload',payload,0o644)])
            unpack = self.work/'unpack'/component/top
            unpack.mkdir(parents=True)
            unpack.chmod(0o755)
            write(unpack/'install.sh',installer,0o755)
            write(unpack/'payload',payload)
            rows.append({'component':component,'filename':filename,'package_root':top,'sha256':sha,
                         'archive_bytes':(self.work/'artifacts'/filename).stat().st_size,
                         'installer_sha256':hashlib.sha256(installer).hexdigest()})
            pins += 'dist/2026-07-13/'+filename+'='+sha+'\n'
        write(self.work/'prepared-cohort/src-stage0',pins.encode())
        self.installation = {'stage0_sha256':hashlib.sha256(pins.encode()).hexdigest(),
            'artifacts':{'artifacts':rows,'source_commit':self.commit,'source_version':'1.99.0','host':self.host}}
        write(self.work/'canonical-seed-installation-inputs.json',json.dumps(self.installation).encode())

    def complete(self):
        self.session.seal('before')
        self.common_files()
        self.session.seal('private-import')
        self.session.seal('common-self-host')
        self.session.seal('common-ddc')
        self.installers()
        self.session.seal('installers')
        self.session.seal('after')
        documents = {'inputs-before.json':self.inputs,'inputs-after.json':self.inputs,
                     'canonical-seed-installation-inputs.json':self.installation}
        for name,value in documents.items():
            if not (self.work/name).exists():
                write(self.work/name,json.dumps(value).encode())
        bound = {name:hashlib.sha256((self.work/name).read_bytes()).hexdigest()
                 for name in (*documents,'INPUT-CLOSURE.json')}
        record = {'native_arguments':{'--'+name.replace('_','-'):str(value) for name,value in self.values.items()},
                  'bound_files':bound,'input_seals':self.live.seals}
        # This inert object is only a physical verifier fixture, not custody:
        # the real entrypoint first consumes its exact live capability/registry.
        owner = types.SimpleNamespace(source=self.source,cargo_home=self.cache,work=self.work,
                                      root=self.source,end=self.end,recheck_source=lambda:None)
        real_loader = self.loader
        class PhysicalOnlyLoader:
            def module(self,name,path):
                return real_loader.module(name,HERE/'mint_seed_support.py')
            def recheck(self):
                real_loader.recheck()
        return owner,record,documents,PhysicalOnlyLoader()
