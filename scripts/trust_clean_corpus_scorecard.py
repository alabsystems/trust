#!/usr/bin/env python3
"""Clean-corpus scorecard — the LEAN side of "both languages lower directly to trust-ir".

Every test file carrying a `clean {}` island or a `clean mod` (tests/ui, tests/run-make) is
compiled from the repo root with the Clean-origin recording path ON
(`-Ztrust-ir-lower -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=ir:<dir>`), and the
`clean_origin` section of each crate's coverage sidecar is aggregated per Clean declaration:

  * `emitted:<tier>`   — the 13-shape planner recorded a row (tier structural / kernel-tv);
  * `general:<disposition>` — the totality lane: compiled / not-computational / skipped /
    merge-refused, with the reason the lane disclosed.

A declaration counts as LOWERED when any lane recorded a definition for it; proof-only
declarations (`not-computational`) are excluded from the denominator. Negative tests (the
file is expected to fail to compile) report `no-coverage rc=1` and are excluded.

Usage:  python3 scripts/trust_clean_corpus_scorecard.py <rustc> <out-dir>
Writes <out-dir>/clean_scorecard.json (per-file outcomes + per-declaration rows) and prints
the summary; run it DETACHED — the wf-rec gcd fixtures spend minutes in the solvers.
"""
import os,re,sys,json,subprocess,glob,collections,shutil
repo=os.getcwd(); rustc=sys.argv[1]; out=sys.argv[2]
shutil.rmtree(out,ignore_errors=True); os.makedirs(out)
files=sorted(set(subprocess.run("grep -rlE '^\\s*(pub\\s+)?clean\\s*(\\{|mod )' tests/ui tests/run-make",shell=True,capture_output=True,text=True).stdout.split()))
files=[f for f in files if not f.endswith('rmake.rs')]
rows=[]; per_file=[]
for i,f in enumerate(files):
    src=open(f).read()
    ed=re.search(r'^//@ edition:\s*(\d+)',src,re.M); ed=ed.group(1) if ed else '2021'
    aux=re.findall(r'^//@ aux-build:\s*(\S+)',src,re.M)
    d=os.path.join(out,f'c{i}'); os.makedirs(d)
    extra=[]
    ok_aux=True
    for a in aux:
        ap=os.path.join(os.path.dirname(f),'auxiliary',a)
        if not os.path.isfile(ap): ok_aux=False; break
        name=os.path.splitext(a)[0].replace('-','_')
        r=subprocess.run([rustc,'--edition',ed,'--crate-type','lib','--crate-name',name,'-Ztrust-verify=off','--out-dir',d,ap],capture_output=True,text=True,timeout=300)
        if r.returncode!=0: ok_aux=False; break
        extra+=['-L',d]
    if not ok_aux:
        per_file.append((f,'aux-fail',None)); continue
    name='c%d'%i
    cmd=[rustc,'-Ztrust-ir-lower','-Ztrust-verify=on','-Ztrust-policy=advisory',f'-Ztrust-dump=ir:{d}','--crate-name',name,'--edition',ed,'--crate-type','lib','--emit=metadata','--cap-lints','allow','-o',os.path.join(d,name+'.rmeta')]+extra+[f]
    import time; t0=time.time()
    try: r=subprocess.run(cmd,capture_output=True,text=True,timeout=300)
    except subprocess.TimeoutExpired: per_file.append((f,'timeout',None)); print('TIMEOUT',f,file=sys.stderr,flush=True); continue
    print(f'{time.time()-t0:6.1f}s rc={r.returncode} {f}',file=sys.stderr,flush=True)
    cov=glob.glob(os.path.join(d,'*.coverage.json'))
    if not cov:
        per_file.append((f,'no-coverage rc=%d'%r.returncode, (r.stderr.strip().split('\n')[-1] if r.stderr.strip() else '')[:160])); continue
    co=json.load(open(cov[0])).get('clean_origin')
    if not isinstance(co,dict) or not co.get('recorded'):
        per_file.append((f,'not-recorded',str(co)[:120])); continue
    per_file.append((f,'ok',None))
    for e in co.get('emitted',[]): rows.append((f,e['clean_name'],'emitted:'+e['tier'],e['shape'],''))
    for s in co.get('skipped',[]): rows.append((f,s['clean_name'],'planner-skipped',s['shape'],s['reason'][:90]))
    for g in co.get('general',[]): rows.append((f,g['clean_name'],'general:'+g['disposition'],'',g.get('reason','')[:90]))
json.dump({'per_file':per_file,'rows':rows},open(os.path.join(out,'clean_scorecard.json'),'w'),indent=1)
print('files',len(files),'outcomes',collections.Counter(o for _,o,_ in per_file).most_common())
for f,o,e in per_file:
    if o!='ok': print('  ',o,f,e or '')
# per declaration: the best disposition (emitted or general compiled = lowered)
by_decl=collections.defaultdict(list)
for f,n,disp,shape,reason in rows: by_decl[(f,n)].append((disp,shape,reason))
lowered=0; total=0; dispo=collections.Counter(); reasons=collections.Counter(); notcomp=0
for k,v in by_decl.items():
    ds=[d for d,_,_ in v]
    if any(d=='general:not-computational' for d in ds) and not any(d.startswith('emitted') for d in ds):
        notcomp+=1; continue
    total+=1
    if any(d.startswith('emitted') or d=='general:compiled' for d in ds):
        lowered+=1; dispo['lowered:'+[d for d in ds if d.startswith('emitted') or d=='general:compiled'][0]]+=1
    else:
        dispo['refused']+=1
        for d,_,r in v: reasons[(d,r[:70])]+=1
print(f'computational declarations: {total}  lowered: {lowered} ({100*lowered/max(total,1):.1f}%)  not-computational (proof-only): {notcomp}')
for k,vv in dispo.most_common(): print(f'  {vv:4} {k}')
print('== refusal reasons (per refused decl, all rows) ==')
for k,vv in reasons.most_common(20): print(f'  {vv:4} {k[0]:28} {k[1]}')
