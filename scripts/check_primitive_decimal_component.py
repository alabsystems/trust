#!/bin/sh
""":"
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
        exec "$candidate" "$0" "$@"
    fi
done
echo "check_primitive_decimal_component.py requires Python 3.11+ (tomllib)" >&2
exit 2
":"""
import os as _floor_os
import shutil as _floor_shutil
import sys as _floor_sys

# Trust: python floor, second half. `python3 check_primitive_decimal_component.py` reads the sh block above
# as a string, so an old `python3` (3.9 on macOS CommandLineTools) re-execs here.
if __name__ == "__main__" and _floor_sys.version_info < (3, 11):
    for _floor_candidate in ("python3.14", "python3.13", "python3.12", "python3.11"):
        _floor_path = _floor_shutil.which(_floor_candidate)
        if _floor_path:
            _floor_argv = [_floor_path, _floor_os.path.abspath(__file__), *_floor_sys.argv[1:]]
            _floor_os.execv(_floor_path, _floor_argv)
    _floor_sys.exit("check_primitive_decimal_component.py requires Python 3.11+ (tomllib); none found on PATH")
__doc__ = """Source-bound SDK component check; separate from canonical x.py integration.

Compile the exact extractor source against the selected SDK's actual private
metadata, through the unchanged qualified private-driver wrapper. The temporary
manifest deliberately replaces ONLY in-tree rustc_* Cargo dependencies with that
SDK view. It retains all noncompiler dependency declarations and root patches.
The fixture adds trust-certify solely to check its actual selected formulas.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import time
import tomllib


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def inline(value):
    if isinstance(value, str):
        return json.dumps(value)
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, list):
        return '[' + ', '.join(inline(item) for item in value) + ']'
    if isinstance(value, dict):
        return '{' + ', '.join(json.dumps(key) + '=' + inline(item) for key, item in value.items()) + '}'
    raise TypeError(type(value))


def verify_sdk_inventory(sdk, inventory_path, expected_sha256):
    """Bind the entire original SDK + relative private metadata view, not just bins."""
    assert sha(inventory_path) == expected_sha256
    inventory = json.loads(Path(inventory_path).read_bytes())
    allowed = {sdk.name, 'rustc-private-sysroots'}
    observed = set()
    for top in allowed:
        for directory, directories, files in os.walk(sdk.parent/top, followlinks=False):
            observed.add(Path(directory).relative_to(sdk.parent).as_posix())
            for name in directories + files:
                observed.add((Path(directory)/name).relative_to(sdk.parent).as_posix())
    assert observed == set(inventory), 'SDK/private hierarchy inventory changed'
    for relative, row in inventory.items():
        part = Path(relative)
        assert not part.is_absolute() and part.parts[0] in allowed and '..' not in part.parts
        path = sdk.parent/part
        info = path.lstat()
        assert stat.S_IMODE(info.st_mode) == row['mode']
        if row['kind'] == 'file':
            assert stat.S_ISREG(info.st_mode) and info.st_size == row['bytes'] and sha(path) == row['sha256']
        elif row['kind'] == 'symlink':
            assert stat.S_ISLNK(info.st_mode) and os.readlink(path) == row['target']
            assert path.resolve(strict=True).is_relative_to(sdk.parent)
        else:
            assert row['kind'] == 'directory' and stat.S_ISDIR(info.st_mode)
    return {'path':str(inventory_path), 'sha256':expected_sha256, 'entries':len(inventory),
            'scope':'Retained original input-byte inventory; not a new P5/package qualification'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('sdk', 'sdk-inventory', 'sdk-inventory-sha256', 'cargo-inputs', 'out',
                 'wrapper', 'build-slot', 'expected-compiler'):
        parser.add_argument('--' + name, required=True)
    parser.add_argument('--cpus', type=int, default=12)
    parser.add_argument('--mem-gb', type=int, default=48)
    parser.add_argument('--prepare-only', action='store_true',
                        help='resolve/check inputs only; no compile or runtime qualification')
    parser.add_argument('--reuse-inputs', type=Path,
                        help='reuse hash-bound owned workspace/cache; Cargo decides every rebuild')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    sdk = Path(args.sdk).resolve(strict=True)
    out = Path(args.out).absolute()
    out.mkdir(mode=0o700)
    def git(*argv):
        return subprocess.check_output(['/usr/bin/git', '-C', str(root), *argv], text=True).strip()
    source = {'commit':git('rev-parse','HEAD'), 'tree':git('rev-parse','HEAD^{tree}'),
              'lock_sha256':sha(root/'Cargo.lock')}
    assert not git('status','--porcelain','--untracked-files=normal'), 'committed clean source required'
    tools = {name:sha(sdk/'bin'/name) for name in ('trustc','targo','rustc','rust-lld','dsymutil')}
    sdk_inventory = verify_sdk_inventory(sdk, args.sdk_inventory, args.sdk_inventory_sha256)
    producer = root/'crates/trust-mir-extract/Cargo.toml'
    declarations = tomllib.loads(producer.read_text())
    workspace = tomllib.loads((root/'Cargo.toml').read_text())
    reuse = None
    cache = out
    if args.reuse_inputs is not None:
        cache = args.reuse_inputs.resolve(strict=True)
        assert cache != out.resolve() and cache.is_dir()
        prior = json.loads((cache/'result.json').read_bytes())
        assert prior['schema'] == 'trust.primitive-decimal-component.v1'
        assert prior['source_and_selected_tools_unchanged'] is True
        # This is an ordinary Cargo input/output cache, not a reused verdict.
        # An unrelated root workspace dev-dependency may change its lock while
        # this component's exact recipe/resolved lock stays unchanged. Keep the
        # component lock byte-bound, re-resolve with --locked, and below require
        # every selected external node to belong to the CURRENT root lock.
        assert prior['sdk'] == str(sdk) and prior['compiler_source'] == args.expected_compiler
        assert prior['tool_sha256'] == tools and prior['sdk_and_private_input_inventory'] == sdk_inventory
        assert prior['root_manifest_sha256'] == sha(root/'Cargo.toml')
        assert prior['producer_manifest_sha256'] == sha(producer)
        for path, expected in [('component/Cargo.toml',prior['component_manifest_sha256']),
                               ('component/Cargo.lock',prior['component_lock_sha256']),
                               ('component/scripts/trustc-private-wrapper.sh',prior['wrapper_sha256'])]:
            assert sha(cache/path) == expected
        reuse = {'prior_result':str(cache/'result.json'),'prior_result_sha256':sha(cache/'result.json'),
                 'prior_context_sha256':sha(cache/'context.json'),'workspace':str(cache/'component'),
                 'prior_root_lock_sha256':prior['source']['lock_sha256'],
                 'current_root_lock_sha256':source['lock_sha256'],
                 'target':str(cache/'target'),'scope':'Ordinary owned Cargo cache only; no verdict, proof or package credit is reused'}
    component = cache/'component'
    (component/'scripts').mkdir(parents=True, exist_ok=reuse is not None)
    wrapper = component/'scripts/trustc-private-wrapper.sh'
    if reuse is None:
        shutil.copy2(args.wrapper, wrapper)
    assert sha(wrapper) == sha(args.wrapper)
    lines = ['[package]', 'name="trust-mir-extract-sdk-component"', 'version="0.0.0"',
             'edition="2021"', '[workspace]', '[lib]', 'name="trust_mir_extract"',
             'path='+inline(str(root/'crates/trust-mir-extract/src/lib.rs')), '[dependencies]']
    compiler_deps = []
    for name, original in declarations['dependencies'].items():
        if name.startswith('rustc_'):
            compiler_deps.append(name)
            continue
        spec = dict(workspace['workspace']['dependencies'][name]) if isinstance(original, dict) and original.get('workspace') else original
        if isinstance(spec, dict):
            spec = dict(spec)
            if 'path' in spec:
                parent = root if isinstance(original, dict) and original.get('workspace') else producer.parent
                spec['path'] = str((parent/spec['path']).resolve(strict=True))
        lines.append(inline(name)+'='+inline(spec))
    lines.extend(['[dev-dependencies]', 'trust-certify='+inline({'path':str(root/'crates/trust-certify')}),
                  '[[test]]', 'name="primitive_decimal_component"',
                  'path='+inline(str(root/'scripts/tests/primitive_decimal_component.rs'))])
    for authority, entries in workspace.get('patch', {}).items():
        lines.append('[patch.'+inline(authority)+']')
        for name, spec in entries.items():
            spec = dict(spec)
            if 'path' in spec:
                spec['path'] = str((root/spec['path']).resolve(strict=True))
            lines.append(inline(name)+'='+inline(spec))
    manifest = component/'Cargo.toml'
    generated = '\n'.join(lines)+'\n'
    if reuse is None:
        manifest.write_text(generated)
        shutil.copy2(root/'Cargo.lock', component/'Cargo.lock')
    else:
        assert manifest.read_text() == generated, 'cache workspace recipe must remain byte-identical'
    cargo = cache/'cargo-home'
    if reuse is None:
        cargo.mkdir(mode=0o700)
        for name in ('registry','git'):
            subprocess.run(['/bin/cp','-cR',str(Path(args.cargo_inputs)/name),str(cargo/name)],check=True)
    env = {key:value for key,value in os.environ.items()
           if not key.startswith(('RUST','CARGO_','TRUST_','TARGO','LD_','DYLD_'))
           and key not in ('CARGO','ATPKG_REGISTRY')}
    env.update(CARGO_HOME=str(cargo), CARGO_TARGET_DIR=str(cache/'target'), CARGO_NET_OFFLINE='true',
               CARGO_BUILD_JOBS=str(args.cpus), RUSTC=str(sdk/'bin/trustc'), RUSTDOC=str(sdk/'bin/rustdoc'),
               RUSTC_WRAPPER=str(wrapper), TRUST_PRIVATE_DRIVER_CRATES='trust_mir_extract:primitive_decimal_component',
               TRUST_STAGE2_BIN=str(sdk/'bin'), TRUST_TEST_SYSROOT=str(sdk),
               PRIMITIVE_DECIMAL_EVIDENCE=str(out),
               PRIMITIVE_DECIMAL_FIXTURE=str(root/'scripts/tests/fixtures/primitive_decimal_source.rs'))
    lean = Path(env['ELAN_HOME'])/'toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean'
    assert lean.resolve(strict=True) == Path.home()/'Library/Application Support/aterm/pkg/store/lean4/3/lib/lean'
    env.update(CLEAN_OLEAN_PINNED_LEAN_LIB=str(lean), CLEAN_OLEAN_REQUIRE_PINNED_LEAN='1')
    env['PATH'] = os.pathsep.join([str(sdk/'bin'), str(Path(sys.executable).parent),
        str(Path.home()/'Library/Application Support/aterm/pkg/bin'),
        str(Path.home()/'Library/Application Support/aterm/pkg/abrew/bin'), '/usr/bin','/bin','/usr/sbin','/sbin'])
    version = subprocess.check_output([str(sdk/'bin/trustc'),'-vV'],env=env,text=True)
    assert re.findall(r'^commit-hash: (.+)$',version,re.M) == [args.expected_compiler]
    context = {'schema':'trust.primitive-decimal-component.v1', 'source':source, 'sdk':str(sdk),
        'compiler_source':args.expected_compiler, 'compiler_vV':version,'tool_sha256':tools,
        'sdk_and_private_input_inventory':sdk_inventory,
        'cargo_cache_reuse':reuse,
        'root_manifest_sha256':sha(root/'Cargo.toml'), 'producer_manifest_sha256':sha(producer),
        'component_manifest_sha256':sha(manifest),'wrapper_sha256':sha(wrapper),
        'omitted_in_tree_compiler_dependencies':compiler_deps,'build_slot_sha256':sha(args.build_slot),
        'operator_sha256':sha(__file__), 'started':datetime.datetime.now(datetime.UTC).isoformat(),
        'scope':'Explicit SDK rustc-private component check; not canonical bootstrap/compiler integration, SDK, P5 or whole-verifier proof'}
    (out/'context.json').write_text(json.dumps(context,indent=2)+'\n')
    phases = []
    def run(label, argv, admitted=False):
        command = [sys.executable,'-I','-B',args.build_slot,'--cpus',str(args.cpus),
                   '--mem-gb',str(args.mem_gb),'--',*argv] if admitted else argv
        start = time.monotonic()
        with (out/(label+'.log')).open('xb') as log:
            result = subprocess.run(command,cwd=component,env=env,stdout=log,stderr=subprocess.STDOUT)
        row = {'name':label,'exit':result.returncode,'seconds':time.monotonic()-start,
               'argv':command,'log_sha256':sha(out/(label+'.log'))}
        phases.append(row)
        print(json.dumps(row),flush=True)
        return result.returncode
    status = run('resolve-offline',[str(sdk/'bin/targo'),'metadata',
        *(['--locked'] if reuse is not None else []),
        '--offline','--format-version','1','--manifest-path',str(manifest)])
    if status == 0:
        old = tomllib.loads((root/'Cargo.lock').read_text())['package']
        old_nodes = {(p['name'],p['version'],p.get('source'),p.get('checksum')) for p in old}
        resolved = tomllib.loads((component/'Cargo.lock').read_text())['package']
        new_external = [p for p in resolved if p.get('source') and
            (p['name'],p['version'],p.get('source'),p.get('checksum')) not in old_nodes]
        assert not new_external, 'component may not silently select new external dependency inputs'
        context['component_lock_sha256'] = sha(component/'Cargo.lock')
        (out/'resolved-inputs.json').write_text(json.dumps({'component_lock_sha256':context['component_lock_sha256'],
            'root_lock_sha256':source['lock_sha256'],'new_external_nodes':new_external},indent=2)+'\n')
        if not args.prepare_only:
            status = run('typed-producer-controls',[str(sdk/'bin/targo'),'--unverified','test','--locked','--offline',
                '--manifest-path',str(manifest),'--test','primitive_decimal_component','--','--nocapture'],admitted=True)
    context.update(exit=status,phases=phases,finished=datetime.datetime.now(datetime.UTC).isoformat())
    context['qualification_complete'] = status == 0 and not args.prepare_only
    assert git('rev-parse','HEAD') == source['commit'] and not git('status','--porcelain','--untracked-files=normal')
    assert sha(root/'Cargo.lock') == source['lock_sha256']
    assert sha(manifest) == context['component_manifest_sha256']
    assert sha(wrapper) == context['wrapper_sha256']
    if 'component_lock_sha256' in context:
        assert sha(component/'Cargo.lock') == context['component_lock_sha256']
    assert verify_sdk_inventory(sdk, args.sdk_inventory, args.sdk_inventory_sha256) == sdk_inventory
    assert all(sha(sdk/'bin'/name)==value for name,value in tools.items())
    context['source_and_selected_tools_unchanged'] = True
    (out/'result.json').write_text(json.dumps(context,indent=2)+'\n')
    print(json.dumps(context),flush=True)
    raise SystemExit(status)


if __name__ == '__main__':
    main()
