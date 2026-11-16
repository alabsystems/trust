#!/usr/bin/env python3
"""Rekey valid same-compiler witnesses into an active deferred-offload context.

Payloads originate in a metadata compile without -Zoffload: that mode does not
populate deferred kernel checks. An active-device compile of the SAME source
must reject its kernel mismatch. Keys are recomputed by the actual compiler;
the adversary refreshes store integrity digests, so an epoch/FNV miss cannot
stand in for source validation. No compiler/tool wrapper is used.
"""
from pathlib import Path
import hashlib
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
TRUSTC = os.environ.get('TRUST_WITNESS_TRUSTC')
if not TRUSTC or not Path(TRUSTC).is_file():
    raise SystemExit('set TRUST_WITNESS_TRUSTC to the actual matching Trust compiler')
WORK = ROOT / 'build/trust-witness-offload-source-rekey'
BASE = ['--crate-type=lib','--edition=2021','--emit=metadata','--color=never',
        '-Zthreads=1','-Ztrust-verify=off']
DEVICE = ['-Zunstable-options','-Zoffload=Device','-Clto=fat']
HEADER = '''#![feature(core_intrinsics)]
#![allow(internal_features)]
fn kernel(_x: u64) {}
pub fn safe_neighbor(x: u32) -> u32 { x }
'''
CASES = {
    'direct': ('', 'pub fn launch(x: u32) { core::intrinsics::offload(kernel, [1,1,1], [1,1,1], 0, -1, (x,)) }\n'),
    'renamed': ('use core::intrinsics::offload as renamed;\n',
                'pub fn launch(x: u32) { renamed(kernel, [1,1,1], [1,1,1], 0, -1, (x,)) }\n'),
    'local_item_value': ('', 'pub fn launch(x: u32) { let local = core::intrinsics::offload; local(kernel, [1,1,1], [1,1,1], 0, -1, (x,)) }\n'),
    'const_child_item_value': ('', 'pub fn launch(x: u32) { let local = const { core::intrinsics::offload }; local(kernel, [1,1,1], [1,1,1], 0, -1, (x,)) }\n'),
    'separate_root': ('', 'fn launch(x: u32) { core::intrinsics::offload(kernel, [1,1,1], [1,1,1], 0, -1, (x,)) }\npub fn dispatch(x: u32) { launch(x) }\n'),
}


def run(src, out, solver, lane, active=True, lookup_log=False):
    out.mkdir(parents=True)
    env = dict(os.environ)
    env['TRUST_WITNESS_STATS'] = '1'
    if lookup_log:
        env['RUSTC_LOG'] = 'rustc_mir_build=debug'
    else:
        env.pop('RUSTC_LOG', None)
    cmd = [TRUSTC,*BASE,*solver,*(DEVICE if active else []),
           '--out-dir',str(out),'-Ztrust-witness='+lane,str(src)]
    p = subprocess.run(cmd,capture_output=True,text=True,env=env)
    out.with_suffix('.stdout').write_text(p.stdout)
    out.with_suffix('.stderr').write_text(p.stderr)
    return p


def digest(key, payload):
    h=0xcbf29ce484222325
    for b in key+payload:
        h=((h^b)*0x100000001b3)&0xffffffffffffffff
    return h


def unpack(path):
    data=path.read_bytes()
    assert data[:8]==b'TWSTORE2'
    n=int.from_bytes(data[8:12],'little');off=12;rows=[]
    for _ in range(n):
        klen=int.from_bytes(data[off:off+2],'little');off+=2
        key=data[off:off+klen];off+=klen
        plen=int.from_bytes(data[off:off+4],'little');off+=4
        payload=data[off:off+plen];off+=plen
        checksum=int.from_bytes(data[off:off+8],'little');off+=8
        assert len(payload)==plen and digest(key,payload)==checksum
        rows.append((key,payload))
    assert off==len(data)
    return rows


def pack(rows):
    data=bytearray(b'TWSTORE2'+len(rows).to_bytes(4,'little'))
    for key,payload in sorted(rows):
        data+=len(key).to_bytes(2,'little')+key
        data+=len(payload).to_bytes(4,'little')+payload
        data+=digest(key,payload).to_bytes(8,'little')
    return bytes(data)


def normalized(stderr):
    return '\n'.join(l for l in stderr.splitlines() if not l.startswith('TRUST_REPLAY '))


def accepted(stderr, root):
    return re.search(r'^TRUST_REPLAY ACCEPT .*::'+root+r'\)',stderr,re.M)


def metadata(out):
    files=list(out.glob('*.rmeta'));assert len(files)==1
    return hashlib.sha256(files[0].read_bytes()).hexdigest()


shutil.rmtree(WORK,ignore_errors=True)
for solver_name,solver in [('coherence',['-Znext-solver=coherence']),('next',[])]:
    for name,(imports,body) in CASES.items():
        work=WORK/solver_name/name;work.mkdir(parents=True)
        src=work/'fixture.rs';src.write_text(HEADER+imports+body)
        original_sha=hashlib.sha256(src.read_bytes()).hexdigest()
        store=work/'inactive-store'
        mint=run(src,work/'inactive-mint',solver,'mint:'+str(store),active=False)
        assert mint.returncode==0,mint.stderr
        stores=list(store.glob('*.twit'));assert len(stores)==1
        rows=unpack(stores[0]);assert len(rows)==(4 if name=='separate_root' else 3)
        empty=work/'empty-store'
        probe=run(src,work/'active-lookup',solver,'replay:'+str(empty),lookup_log=True)
        assert probe.returncode!=0 and 'type mismatch in offload kernel argument' in probe.stderr
        keys=set(re.findall(r'trust-witness: replay lookup key.*?key=([0-9a-f_]+)',probe.stderr))
        assert len(keys)==len(rows),probe.stderr
        by_prefix={key.rsplit('_',1)[0]:key for key in keys}
        rekeyed=[]
        for key,payload in rows:
            new_key=by_prefix[key.decode().rsplit('_',1)[0]].encode()
            assert new_key!=key,'active mode must move the environment key'
            rekeyed.append((new_key,payload))
        forged=work/'forged-store';forged.mkdir()
        forged_path=forged/stores[0].name;forged_path.write_bytes(pack(rekeyed))
        assert unpack(forged_path)==sorted(rekeyed),'all refreshed digests must validate'
        warm=run(src,work/'active-forged',solver,'replay:'+str(forged))
        off=run(src,work/'active-off',solver,'off')
        assert warm.returncode==off.returncode!=0,(warm,off)
        assert normalized(warm.stderr)==normalized(off.stderr),'deferred error masked/changed'
        assert 'type mismatch in offload kernel argument' in off.stderr
        assert not accepted(warm.stderr,'launch'),'unencoded deferred state was accepted'
        assert re.search(r'^TRUST_REPLAY MISS-source-offload .*::launch\)',warm.stderr,re.M),warm.stderr
        assert accepted(warm.stderr,'safe_neighbor'),'safe neighbor was rejected with the offload root'
        if name=='separate_root':
            assert accepted(warm.stderr,'dispatch'),'ordinary cross-root call lost replay'
        assert not list((work/'active-forged').glob('*.rmeta'))
        assert hashlib.sha256(src.read_bytes()).hexdigest()==original_sha
        print(f'PASS {solver_name}/{name}: valid-digest rekey refused; real deferred error retained; safe neighbor ACCEPT')

    # Name collisions carry no authority: ordinary functions named offload must
    # continue to replay under exactly the active-device flags above.
    work=WORK/solver_name/'ordinary-name';work.mkdir(parents=True)
    src=work/'fixture.rs'
    src.write_text('fn offload(x:u32)->u32{x}\npub fn ordinary(x:u32)->u32{offload(x)}\n')
    store=work/'store'
    mint=run(src,work/'mint',solver,'mint:'+str(store))
    warm=run(src,work/'warm',solver,'replay:'+str(store))
    off=run(src,work/'off',solver,'off')
    assert mint.returncode==warm.returncode==off.returncode==0,(mint,warm,off)
    assert normalized(mint.stderr)==normalized(warm.stderr)==normalized(off.stderr)
    assert metadata(work/'mint')==metadata(work/'warm')==metadata(work/'off')
    assert accepted(warm.stderr,'offload') and accepted(warm.stderr,'ordinary'),warm.stderr
    print(f'PASS {solver_name}/ordinary-name: compiler-resolved non-intrinsic names replay identically')
