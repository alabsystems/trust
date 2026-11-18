#!/usr/bin/env python3
"""Untrusted complete-record lookup/balancing advice; Lean checks every cut."""
from pathlib import Path
import json
import argparse
p=argparse.ArgumentParser(description='Untrusted full-table lookup proof advice')
p.add_argument('--records-index',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
book=json.loads(a.records_index.read_text());names=book['names'];n=len(names)
assert len(set(names))==n and names==sorted(names)
lines=['-- Copyright 2026 Andrew Yates | Apache-2.0','import C11PredefinedCuts','namespace C11PredefinedLookupCuts','open C11PredefinedRecords C11PredefinedData']
def balanced(lo,hi):
 node=f'rows_{lo}_{hi}';rev=node+'_reversed';seg=node+'_segment';forward=node+'_forward'
 if hi-lo<=16:
  lines.extend([f'def {node} : List Record := ['+', '.join('record'+str(i) for i in range(lo,hi))+']',f'def {rev} : List Record := ['+', '.join('record'+str(i) for i in range(hi-1,lo-1,-1))+']',f'theorem {seg} : reversed{hi} = {rev} ++ reversed{lo} := by rfl',f'theorem {forward} : {rev}.reverse = {node} := by rfl'])
 else:
  mid=(lo+hi)//2;left=balanced(lo,mid);right=balanced(mid,hi)
  lines.extend([f'def {node} : List Record := {left} ++ {right}',f'def {rev} : List Record := {right}_reversed ++ {left}_reversed',f'theorem {seg} : reversed{hi} = {rev} ++ reversed{lo} := by',f'  rw [{right}_segment, {left}_segment]',f'  unfold {rev}', '  simp only [List.append_assoc]',f'theorem {forward} : {rev}.reverse = {node} := by',f'  rw [{rev}, List.reverse_append, {left}_forward, {right}_forward]','  rfl'])
 return node
root=balanced(0,n)
lines.extend(['theorem complete_records_balanced : actualRecords = '+root+' := by','  unfold actualRecords',f'  rw [{root}_segment]','  simp only [reversed0, List.append_nil]',f'  exact {root}_forward'])
queries=[('guard','_ASSERT_H_'),('cpp','__cplusplus'),('version','__STDC_VERSION__'),('builtin','__has_include'),('static','static_assert')]
for tag,name in queries:
 def filtered(lo,hi):
  node=f'rows_{lo}_{hi}';proof=node+'_'+tag;matches=[i for i in range(lo,hi) if names[i]==name];result='['+', '.join('record'+str(i) for i in matches)+']'
  if hi-lo<=16:lines.extend([f'theorem {proof} : {node}.filter (fun record => record.name == {json.dumps(name)}) = {result} := by rfl'])
  else:
   mid=(lo+hi)//2;left=filtered(lo,mid);right=filtered(mid,hi)
   lines.extend([f'theorem {proof} : {node}.filter (fun record => record.name == {json.dumps(name)}) = {result} := by',f'  rw [{node}, List.filter_append, {left}, {right}]','  rfl'])
  return proof
 proof=filtered(0,n);expected='some none' if name not in names else 'some (some record'+str(names.index(name))+')'
 lines.extend([f'theorem captured_{tag}_lookup : lookup actualRecords {json.dumps(name)} = {expected} := by','  unfold lookup',f'  rw [complete_records_balanced, {proof}] <;> rfl'])
lines.extend(['end C11PredefinedLookupCuts',''])
with a.out.open('x') as output:output.write('\n'.join(lines))
