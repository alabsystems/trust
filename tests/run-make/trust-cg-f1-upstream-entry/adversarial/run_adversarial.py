#!/usr/bin/env python3
"""Actual canonical rlib-carrier importer mutations. Never builds an SDK.

The embedded read-only observer has no official evidence authority. Only the
supplied official trustc runs Compiler::compile/strict. Source-census deletion is
an explicitly open observation, not an intended refusal or full-refinement pass.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
PROBE=REPO/'crates/trust-thir-lower/probes/rmeta_importer_mutations.rs'
REPAIR='e0c96495192431a416b94651595c1b5e7b05d748'
CASES={
 'stale_digest':('chain','digest: envelope-digest'),
 'wrong_owner':('chain','binding: entry names another stable Rust owner'),
 'ledger_missing':('chain','decoded declaration has no retained callee identity'),
 'ledger_duplicate':('chain','extra or duplicate declaration row'),
 'ledger_identity_drift':('chain','[effect-not-conserved]'),
 'source_identity_drift':('chain','[effect-not-conserved]'),
 'ir_call_omitted':('chain','[effect-not-conserved]'),
 'nested_wrong_kind':('nested','legacy site ADT definition kind'),
 'nested_absent':('nested','legacy site stable identity differs from actual Rust metadata'),
}
def digest(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as stream:
  for block in iter(lambda:stream.read(1<<20),b''):h.update(block)
 return h.hexdigest()
def write(path,obj):Path(path).write_text(json.dumps(obj,indent=2)+'\n')
def output(argv,cwd=None,env=None):
 p=subprocess.run(argv,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 if p.returncode:raise RuntimeError(f'{argv!r} exited {p.returncode}: {p.stdout}')
 return p.stdout
def manifest(path,package,source,name,binary=False):
 path.parent.mkdir(parents=True,exist_ok=True)
 target='[[bin]]'if binary else'[lib]'
 path.write_text(f'[package]\nname={json.dumps(package)}\nversion="0.1.0"\nedition="2024"\n{target}\nname={json.dumps(name)}\npath={json.dumps(str(source))}\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n')
def replace_carrier(original,changed,destination):
 data=Path(original).read_bytes();before=Path(changed[0]).read_bytes();after=Path(changed[1]).read_bytes()
 if len(before)!=len(after)or data.count(before)!=1:raise AssertionError('one exact same-length opaque carrier replacement required')
 index=data.index(before);new=data[:index]+after+data[index+len(before):]
 assert new[:index]==data[:index]and new[index+len(before):]==data[index+len(before):]
 Path(destination).parent.mkdir(parents=True,exist_ok=True);Path(destination).write_bytes(new)
 return {'offset':index,'bytes':len(before),'whole_library_before':hashlib.sha256(data).hexdigest(),'whole_library_after':digest(destination),'original_entry_sha256':digest(changed[0]),'changed_entry_sha256':digest(changed[1]),'exact_occurrences':1,'outside_entry_unchanged':True}
def strict_control(target,stderr):
 assert 'completed source -> trust_ir_of -> codegen_module'in stderr
 assert 'lower_module_to_lir'not in stderr
 assert ' 0 not closed, 0 refuted'in stderr
 certs=list(target.rglob('*.trust-cg-certificates.json'));coverage=list(target.rglob('*.trust-instance-coverage.json'))
 assert len(certs)==len(coverage)==1
 cert=json.loads(certs[0].read_text());cov=json.loads(coverage[0].read_text())
 assert cert['schema']=='trust-cg-bridge.call-refinement.v1'
 assert len(cert['certificates'])>0
 assert len(cert['closure']['closed_kernel'])==len(cert['certificates'])and not cert['closure']['unclosed']
 assert sum(len(c['call_sites'])for c in cert['certificates'])>=2
 assert coverage[0].read_text().count('"kind": "upstream-entry"')>=2
 libraries=[p for p in target.rglob('libattack_user.rlib')]
 assert len(libraries)==1
 members=output(['ar','t',str(libraries[0])]).splitlines();objects=[m for m in members if m.endswith('.o')]
 assert len(objects)==1
 image=subprocess.check_output(['ar','p',str(libraries[0]),objects[0]]).rstrip(b'\n')
 assert hashlib.sha256(image).hexdigest()==cert['object_sha256']
 return {'certificates':str(certs[0]),'certificate_sha256':digest(certs[0]),'object_sha256':cert['object_sha256'],'coverage_sha256':digest(coverage[0]),'library_sha256':digest(libraries[0])}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--plan',action='store_true');p.add_argument('--out',type=Path,required=True)
 p.add_argument('--sdk-root',type=Path);p.add_argument('--compiler-source',type=Path);p.add_argument('--compiler-commit');p.add_argument('--build-receipt',type=Path)
 p.add_argument('--private-deps',type=Path);p.add_argument('--private-host-deps',type=Path);args=p.parse_args()
 out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
 sources={str(path):digest(path)for path in [Path(__file__),PROBE,*HERE.glob('*.rs')]}
 record={'schema':'trust.upstream-r.actual-carrier-adversarial.v1','status':'PREPARED_NOT_RUN','required_importer_ancestor':REPAIR,'source_files':sources,'steps':[],'cases':[],'intended_negative_count':len(CASES),'observer_authority':False,'canonical_execution':False,'open_limitation':'Source matcher intentionally ignores extra IR effects; source-census deletion is separately observed, never claimed universally detected.'}
 write(out/'RESULT.json',record)
 if args.plan:return
 if not all([args.sdk_root,args.compiler_source,args.compiler_commit,args.build_receipt]):p.error('execution requires matching fresh SDK, exact source/commit and immutable build receipt')
 if os.environ.get('BUILD_SLOT_HELD')!='1':p.error('execute through build-slot')
 start=time.time();record['status']='RUNNING'
 try:
  sdk=args.sdk_root.resolve();source=args.compiler_source.resolve();commit=args.compiler_commit
  assert re.fullmatch('[0-9a-f]{40}',commit)
  assert output(['git','rev-parse','HEAD'],cwd=source).strip()==commit
  output(['git','merge-base','--is-ancestor',REPAIR,commit],cwd=source)
  assert not output(['git','status','--porcelain','--untracked-files=no'],cwd=source).strip()
  compiler=sdk/'stage1/bin/trustc';version=output([str(compiler),'-vV']);assert f'commit-hash: {commit}\n'in version
  host=next(line[6:]for line in version.splitlines()if line.startswith('host: '))
  deps=(args.private_deps or sdk/f'stage1-rustc/{host}/release/deps').resolve();hostdeps=(args.private_host_deps or sdk/'stage1-rustc/release/deps').resolve()
  drivers=list((sdk/'stage1/lib').glob('librustc_driver-*.dylib'));private=list(deps.glob('librustc_driver-*.dylib'))
  assert len(drivers)==len(private)==1 and digest(drivers[0])==digest(private[0])
  targo=next(path for path in [sdk/'stage1/bin/targo',sdk/f'stage1-tools-bin/{host}/targo']if path.is_file())
  assert output([str(targo),'--unverified','--version']).startswith('targo ')
  record['SDK']={'root':str(sdk),'source':str(source),'commit':commit,'version':version,'compiler_sha256':digest(compiler),'private_driver_sha256':digest(private[0]),'targo_sha256':digest(targo),'build_receipt_sha256':digest(args.build_receipt)}
  env={k:os.environ[k]for k in ['HOME','LANG']if k in os.environ};env.update(PATH=str(targo.parent)+':/usr/bin:/bin:/usr/sbin:/sbin',CARGO_HOME=str(out/'cargo-home'),CARGO_INCREMENTAL='0',RUST_MIN_STACK='134217728',RUSTC=str(compiler),DYLD_LIBRARY_PATH=':'.join(map(str,[deps,hostdeps,sdk/'stage0/lib',sdk/'stage1/lib'])))
  env.update({k:v for k,v in os.environ.items()if k.startswith('BUILD_SLOT_')or k=='CARGO_BUILD_JOBS'})
  def build(label,manifest_path,target,flags,rustc=compiler,extra=None):
   target.mkdir(parents=True);job=dict(env,RUSTC=str(rustc),CARGO_TARGET_DIR=str(target),CARGO_ENCODED_RUSTFLAGS='\x1f'.join(flags));job.update(extra or{})
   argv=[str(targo),'--unverified','build','--offline','--manifest-path',str(manifest_path)]
   step={'label':label,'argv':argv,'target':str(target),'started':time.time()};record['steps'].append(step);write(out/'RESULT.json',record)
   with(out/f'{label}.stdout').open('w')as stdout,(out/f'{label}.stderr').open('w')as stderr:result=subprocess.run(argv,cwd=out,env=job,stdout=stdout,stderr=stderr)
   step.update(exit=result.returncode,seconds=time.time()-step['started']);return result.returncode,(out/f'{label}.stderr').read_text()
  private_flags=['-C','prefer-dynamic','--sysroot',str(sdk/'stage0'),'-L','dependency='+str(deps),'-L','dependency='+str(hostdeps)];inputs={}
  for name in ['rustc_driver','rustc_hir','rustc_interface','rustc_middle','rustc_span','trust_thir_lower','trust_ir','serde_json']:
   found=False
   for extension in ['rmeta','dylib','rlib']:
    matches=list(deps.glob(f'lib{name}-*.{extension}'))
    if not matches:continue
    assert len(matches)==1,(name,extension);path=matches[0];inputs[str(path)]=digest(path);private_flags+=['--extern',name+'='+str(path)];found=True
    if extension=='dylib':break
   assert found,name
  record['private_inputs']=inputs
  probe_manifest=out/'observer/Cargo.toml';manifest(probe_manifest,'carrier-observer',PROBE,'carrier-observer',True)
  code,_=build('observer-build',probe_manifest,out/'observer-target.noindex',private_flags,rustc=sdk/'stage0/bin/trustc');assert code==0
  observer=out/'observer-target.noindex/debug/carrier-observer'
  producer_manifest=out/'producer/Cargo.toml';manifest(producer_manifest,'attack-producer',HERE/'producer.rs','attack_dep')
  flags=['--sysroot',str(sdk/'stage1'),'-Copt-level=0','-Coverflow-checks=on','-Cpanic=abort']
  code,_=build('producer',producer_manifest,out/'producer-target.noindex',flags+['-Ztrust-ir-lower=on','-Ztrust-ir-lower-templates']);assert code==0
  library=out/'producer-target.noindex/debug/libattack_dep.rlib';library_hash=digest(library)
  reader_manifest=out/'reader/Cargo.toml';manifest(reader_manifest,'attack-reader',HERE/'reader.rs','attack_reader')
  code,_=build('read-only-extraction',reader_manifest,out/'reader-target.noindex',flags+['--extern','attack_dep='+str(library)],rustc=observer,extra={'R_IMPORT_MUTATION_OUT':str(out/'carriers'),'R_IMPORT_MUTATION_SYSROOT':str(sdk/'stage1')});assert code==0
  rows=json.loads((out/'carriers/MUTATIONS.json').read_text());assert len(rows)==10
  record['carrier_rows']=rows
  canonical_flags=flags+['-Ccodegen-units=1','-Zshare-generics=no','-Ztrust-ir-lower=on','-Zcodegen-backend=trust-cg','-Ztrust-cg-frontend=trust-ir','-Ztrust-cg-f1-backend=compiler','-Ztrust-cg-output-gate=strict']
  failures=[]
  def consume(case,carrier,nested=False):
   mf=out/case/'Cargo.toml';manifest(mf,'attack-user-'+case,HERE/('nested_consumer.rs'if nested else'consumer.rs'),'attack_user')
   target=out/(case+'-target.noindex');code,stderr=build(case,mf,target,canonical_flags+['--extern','attack_dep='+str(carrier)])
   return target,code,stderr
  def safe(stderr):return 'internal compiler error'not in stderr and 'panicked at'not in stderr
  target,code,stderr=consume('unmodified-control',library)
  try:assert code==0 and safe(stderr);record['unmodified_strict_compiler_control']=strict_control(target,stderr)
  except Exception as error:failures.append({'case':'unmodified-control','error':str(error)})
  for case,(owner,needle)in CASES.items():
   changed=out/case/'libattack_dep.rlib';replacement=replace_carrier(library,(out/f'carriers/{owner}.original.entry',out/f'carriers/{case}.entry'),changed)
   target,code,stderr=consume(case,changed,owner=='nested');row={'case':case,'exit':code,'replacement':replacement,'expected_refusal':needle}
   intended_detail=needle in stderr and (case not in ['ledger_identity_drift','source_identity_drift','ir_call_omitted']or 'NotConserved(Call)'in stderr)
   row['passed']=code!=0 and safe(stderr)and intended_detail and owner in stderr and not list(target.rglob('*.rlib'))
   if not row['passed']:failures.append(row)
   record['cases'].append(row);write(out/'RESULT.json',record)
  target,code,stderr=consume('nested-reference',library,True)
  reference_ok=code!=0 and safe(stderr)and 'level-S instances require sealed template admission (6.6)'in stderr and not list(target.rglob('*.rlib'))
  record['nested_reference']={'exit':code,'named_S_unsupported':reference_ok,'R_or_S_positive_claim':False}
  if not reference_ok:failures.append({'case':'nested-reference','error':'real generic reference must retain its named6.6unsupported refusal'})
  case='census_call_omitted_observe';changed=out/case/'libattack_dep.rlib';replacement=replace_carrier(library,(out/'carriers/chain.original.entry',out/f'carriers/{case}.entry'),changed)
  target,code,stderr=consume(case,changed);observation=next(row for row in rows if row['case']==case)
  record['open_census_asymmetry_observation']={'actual_retained_checker':observation['retained_checker_observation'],'canonical_codegen_exit':code,'replacement':replacement,'all_census_deletions_detected_claim':False,'not_an_intended_negative_pass':True}
  if not safe(stderr):failures.append({'case':case,'error':'canonical observation produced an ICE/panic'})
  assert digest(library)==library_hash
  assert all(digest(path)==value for path,value in inputs.items())and all(digest(path)==value for path,value in sources.items())
  assert digest(compiler)==record['SDK']['compiler_sha256']and digest(targo)==record['SDK']['targo_sha256']
  assert digest(drivers[0])==record['SDK']['private_driver_sha256']and digest(args.build_receipt)==record['SDK']['build_receipt_sha256']
  assert output(['git','rev-parse','HEAD'],cwd=source).strip()==commit and not output(['git','status','--porcelain','--untracked-files=no'],cwd=source).strip()
  record.update(canonical_execution=True,failures=failures,status='FAIL'if failures else'PASS_INTENDED_NEGATIVES_WITH_OPEN_CENSUS_ASYMMETRY')
  if failures:raise AssertionError(f'{len(failures)} declared controls failed; all raw outcomes retained')
 except Exception as error:
  record.update(status='FAIL',error=str(error));raise
 finally:
  record['seconds']=time.time()-start;write(out/'RESULT.json',record)
if __name__=='__main__':main()
