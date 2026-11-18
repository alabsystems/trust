#!/usr/bin/env python3
"""Untrusted full physical-input/record cut advice; Lean checks each line.
No macro/body/target semantics or source authenticity is granted by this writer.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def string(s):return json.dumps(s,ensure_ascii=False)
def chars(s):return '['+', '.join('Char.ofNat '+str(ord(c)) for c in s)+']'


def generate(raw, out):
    assert raw.isascii() and raw.endswith('\n') and '\r' not in raw and '\x00' not in raw
    physical=raw.splitlines(keepends=True)
    assert ''.join(physical)==raw and all(s.endswith('\n') for s in physical)
    data=['-- Copyright 2026 Andrew Yates | Apache-2.0','import C11PredefinedRecords','namespace C11PredefinedData','open C11PredefinedRecords','def reversed0 : List Record := []']
    proof=['-- Copyright 2026 Andrew Yates | Apache-2.0','import C11PredefinedData','namespace C11PredefinedCuts','open C11PredefinedRecords C11PredefinedData','def state0 : Option Scan := some { reversed := reversed0 }']
    names=[]
    for i,line in enumerate(physical):
        match=re.fullmatch(r'#define ([A-Za-z_][A-Za-z_0-9]*)(.*)\n',line);assert match,line
        name,tail=match.groups();function=tail.startswith('(')
        assert not tail or tail[0] in ' ('
        tail=tail if function or not tail else tail[1:]
        assert not names or names[-1]<name
        names.append(name)
        data += [f'def record{i} : Record := {{ name := {string(name)}, functionLike := {str(function).lower()}, tail := {string(tail)} }}',f'def reversed{i+1} : List Record := record{i} :: reversed{i}',f'def line{i} : List Char := {chars(line)}']
        proof += [f'def state{i+1} : Option Scan := some {{ reversed := reversed{i+1} }}',f'theorem line_cut{i} : feed state{i} line{i} = state{i+1} := by rfl']
    def balanced(lo,hi):
        if hi-lo==1:return f'line{lo}',f'line_cut{lo}'
        mid=(lo+hi)//2;l,lp=balanced(lo,mid);r,rp=balanced(mid,hi);node=f'input_{lo}_{hi}'
        data.append(f'def {node} : List Char := {l} ++ {r}')
        proof.extend([f'theorem {node}_read : feed state{lo} {node} = state{hi} := by',f'  rw [{node}, feed_append, {lp}, {rp}]'])
        return node,node+'_read'
    root,rootProof=balanced(0,len(physical))
    data += [f'def actualCharacters : List Char := {root}',f'def actualRecords : List Record := reversed{len(physical)}.reverse','end C11PredefinedData','']
    proof += ['theorem complete_captured_records : finish (feed (some {}) actualCharacters) = some actualRecords := by',f'  change finish (feed state0 {root}) = some actualRecords',f'  rw [{rootProof}]','  rfl','end C11PredefinedCuts','']
    out.mkdir()
    (out/'C11PredefinedData.lean').write_text('\n'.join(data))
    (out/'C11PredefinedCuts.lean').write_text('\n'.join(proof))
    (out/'INPUT.json').write_text(json.dumps({'bytes':len(raw.encode()),'sha256':hashlib.sha256(raw.encode()).hexdigest(),'physical_lines':len(physical),'names':names,'scope':'complete captured inventory DATA; producer suggestions checked by fixed Lean reader; no tool/target/source authenticity'},indent=2)+'\n')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--input',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();generate(a.input.read_bytes().decode('utf-8'),a.out)
