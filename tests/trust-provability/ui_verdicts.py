#!/usr/bin/env python3
"""Capture the pass/fail verdict of every tests/ui/trust fixture under the
DEFAULT policy, so a policy change's blast radius is measured, not guessed."""
import glob, json, os, subprocess, sys, tempfile
# Derive the repo root instead of hardcoding an absolute home path: the
# publication forbidden-content guard rejects one, which blocks trust's entire
# public export.
REPO=os.environ.get("TRUST_REPO") or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
T=os.path.join(REPO,"build/host/stage2/bin/trustc")
out={}
files=sorted(glob.glob(os.path.join(REPO,"tests/ui/trust/*.rs")))
for i,p in enumerate(files):
    d=tempfile.mkdtemp(prefix="uiv_")
    env=dict(os.environ); env["TRUST_SEED_STAIRCASE"]="1"
    try:
        r=subprocess.run([T,"-Zthreads=1","--edition=2021","--crate-type=lib",
                          "--emit=metadata","--out-dir",d,p],
                         capture_output=True,text=True,env=env,timeout=120)
        rc=r.returncode
        ice="unexpectedly panicked" in r.stderr
    except subprocess.TimeoutExpired:
        rc, ice = "timeout", False
    out[os.path.basename(p)]={"rc":rc,"ice":ice}
    if (i+1)%25==0: print(f"  {i+1}/{len(files)}", file=sys.stderr)
json.dump(out, open(sys.argv[1],"w"), indent=1, sort_keys=True)
ok=sum(1 for v in out.values() if v["rc"]==0)
print(f"files={len(out)} pass={ok} fail={len(out)-ok} ice={sum(1 for v in out.values() if v['ice'])}")
