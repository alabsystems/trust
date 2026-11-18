#!/usr/bin/env python3
"""Untrusted checked-cut advice for a complete owner's directive-line fence."""
import argparse
import json
from pathlib import Path


def step(state, char):
    if state is None or char in '\\?\r\0':return None
    mode, beginning, directive = state
    if mode == 'normal':
        if char == '\n':return ('normal', True, False)
        if char in ' \t\v\f':return state
        if char == '/':return ('slash', beginning, directive)
        if char == '#':return ('normal', False, True) if beginning else None
        return ('normal', False, directive)
    if mode == 'slash':return ('block' if char=='*' else 'line', beginning, directive) if char in '/*' else None
    if mode == 'line':return ('normal', True, False) if char=='\n' else state
    if char=='\n' and directive:return None
    if mode=='block':return ('star',beginning,directive) if char=='*' else state
    if char=='/':return ('normal',beginning,directive)
    if char=='*':return state
    return ('block',beginning,directive)


def generate(raw):
    parts=[raw[i:i+8] for i in range(0,len(raw),8)]
    lines=['-- Copyright 2026 Andrew Yates | Apache-2.0',
      'import C11DirectiveLines','import C11GuardHeaderCuts',
      'namespace C11GuardDirectiveCuts','open C11DirectiveLines C11GuardHeaderCuts']
    state=('normal',True,False)
    for i,part in enumerate(parts):
        initial='(some initial)' if i==0 else f'state{i}'
        for char in part:state=step(state,char)
        assert state is not None
        mode,beginning,directive=state
        lines += [f'def state{i+1} : Option C11DirectiveLines.State := some {{ mode := .{mode}, beginning := {str(beginning).lower()}, directive := {str(directive).lower()} }}',
          f'theorem cut{i} : C11DirectiveLines.feed {initial} uint32Full_chunk{i} = state{i+1} := by rfl']
    lines += ['theorem complete_characters_supported : supportedCharacters uint32Full_chunks.flatten = true := by',
      '  rw [← C11DirectiveLines.chunks_exact]',
      '  simp only [supportedChunks, uint32Full_chunks, List.foldl_cons, List.foldl_nil]',
      '  rw ['+', '.join('cut'+str(i) for i in range(len(parts)))+']','  rfl',
      'theorem complete_source_supported : supported C11GuardHeaderData.uint32Full_0 = true := by',
      '  unfold supported',
      '  rw [← uint32Full_string_exact, uint32Full_node_0_'+str(len(parts))+'_characters, uint32Full_flatten_exact]',
      '  exact complete_characters_supported','end C11GuardDirectiveCuts','']
    return '\n'.join(lines)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rows',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();rows=json.loads(a.rows.read_text());assert len(rows)==1
    with a.out.open('x') as f:f.write(generate(rows[0]['raw']))
