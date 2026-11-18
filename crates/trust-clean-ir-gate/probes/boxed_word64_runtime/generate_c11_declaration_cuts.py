#!/usr/bin/env python3
"""Untrusted small-step lexical proof advice; Lean checks all cuts and input links."""
import argparse
import json
from pathlib import Path


def string(value):
    return json.dumps(value, ensure_ascii=False)


def chars(value):
    return '[' + ', '.join('Char.ofNat ' + str(ord(c)) for c in value) + ']'


def state(value):
    if value is None:
        return 'none'
    mode, word, output = value
    return 'some { mode := .' + mode + ', word := ' + chars(word) + ', reversed := [' + ', '.join(map(string, output)) + '] }'


def emit(s, token):
    return ('normal', '', [token] + s[2])


def isword(c):
    return c in '_' or 'a' <= c <= 'z' or 'A' <= c <= 'Z' or '0' <= c <= '9'


def normal(s, c):
    if c in ' \t\v\f':return s
    if c == '\n':return emit(s, '\n')
    if isword(c):return ('word', c, s[2])
    if c in '/#=*':return ({'/':'slash','#':'hash','=':'equal','*':'asterisk'}[c], s[1], s[2])
    if c in '{}[]();,':return emit(s,c)
    return None


def step(s, c):
    if s is None or c in '\\?\r\0':return None
    mode, word, output = s
    if mode == 'normal':return normal(s,c)
    if mode == 'word':return ('word',c+word,output) if isword(c) else normal(emit(s,word[::-1]),c)
    if mode == 'slash':return ('line' if c=='/' else 'block',word,output) if c in '/*' else None
    if mode == 'line':return emit(s,'\n') if c=='\n' else s
    if mode == 'block':return ('star',word,output) if c=='*' else ('block','',['\n']+output) if c=='\n' else s
    if mode == 'star':return ('normal',word,output) if c=='/' else s if c=='*' else ('block','',['\n']+output) if c=='\n' else ('block',word,output)
    pending = {'hash':'#','equal':'=','asterisk':'*'}[mode]
    if (mode=='hash' and c=='#') or (mode=='equal' and c=='=') or (mode=='asterisk' and c in '=/'):return None
    return normal(emit(s,pending),c)


def finish(s):
    mode, word, output = s
    if mode in ['normal','line']:return output[::-1]
    if mode=='word':return ([word[::-1]] + output)[::-1]
    if mode in ['hash','equal','asterisk']:return ([{'hash':'#','equal':'=','asterisk':'*'}[mode]]+output)[::-1]
    raise ValueError(mode)


def generate(rows, selected=None, namespace="C11DeclarationCuts", data_module="C11ActualDeclarationData", balanced_flatten=False):
    selected = ["clean_obj_header", "clean_obj"] if selected is None else selected
    lines=['-- Copyright 2026 Andrew Yates | Apache-2.0','import C11DeclarationLexer','import ' + data_module,'import Init.Data.String.Lemmas.Basic','namespace ' + namespace,'open C11DeclarationLexer','']
    for row in rows:
        if row['name'] not in selected:continue
        tag=row['name'];raw=row['raw'];chunks=[raw[i:i+8] for i in range(0,len(raw),8)];s=('normal','',[])
        lines += [f'def {tag}_state0 : Option State := some initial']
        for i,chunk in enumerate(chunks):
            lines.append(f'def {tag}_chunk{i} : List Char := {chars(chunk)}')
            for char in chunk:s=step(s,char)
            assert s is not None
            lines += [f'def {tag}_state{i+1} : Option State := {state(s)}',f'theorem {tag}_cut{i} : feed '+('('+ 'some initial'+')' if i==0 else f'{tag}_state{i}')+f' {tag}_chunk{i} = {tag}_state{i+1} := by rfl']
        tokens=finish(s)
        lines += [f'def {tag}_chunks : List (List Char) := ['+', '.join(f'{tag}_chunk{i}' for i in range(len(chunks)))+']', f'def {tag}_tokens : List String := ['+', '.join(map(string,tokens))+']',f'theorem {tag}_characters_lex : tokenizeCharacters {tag}_chunks.flatten = some {tag}_tokens := by', '  rw [← chunks_exact]',f'  simp only [tokenizeChunks, {tag}_chunks, List.foldl_cons, List.foldl_nil]', '  rw ['+', '.join(f'{tag}_cut{i}' for i in range(len(chunks)))+']', '  rfl']
        for i,chunk in enumerate(chunks):
            lines += [f'def {tag}_string_leaf{i} : String := {string(chunk)}',
                      f'theorem {tag}_chunk_chars{i} : {tag}_string_leaf{i}.toList = {tag}_chunk{i} := by rfl']
        character_defs=[]
        parts_info={}
        def balanced(lo,hi):
            if hi-lo==1:
                leaf=f'{tag}_string_leaf{lo}'
                if balanced_flatten:
                    part=f'{tag}_parts_leaf{lo}'
                    lines.extend([f'def {part} : List (List Char) := [{tag}_chunk{lo}]',
                        f'theorem {part}_flatten : {tag}_chunk{lo} = {part}.flatten := by',
                        f'  simp only [{part}, List.flatten_cons, List.flatten_nil, List.append_nil]'])
                    parts_info[leaf]=(part,None,part+'_flatten')
                return leaf, f'{tag}_chunk{lo}', f'{tag}_chunk_chars{lo}', chunks[lo], None
            mid=(lo+hi)//2
            left,lc,lp,lt,le=balanced(lo,mid);right,rc,rp,rt,re=balanced(mid,hi)
            node=f'{tag}_node_{lo}_{hi}';character_defs.append(node+'_chars')
            lines.extend([f'def {node} : String := {left} ++ {right}',
                          f'def {node}_chars : List Char := {lc} ++ {rc}',
                          f'theorem {node}_literal : {node} = {string(lt+rt)} := by',
                          f'  unfold {node}'])
            if le:lines.append(f'  rw [{le}]')
            if re:lines.append(f'  rw [{re}]')
            lines.extend(['  cbv',f'theorem {node}_characters : {node}.toList = {node}_chars := by',
                          f'  unfold {node} {node}_chars',f'  rw [String.toList_append, {lp}, {rp}]'])
            if balanced_flatten:
                leftparts,leftliteral,leftflat=parts_info[left];rightparts,rightliteral,rightflat=parts_info[right]
                part=node+'_parts'
                lines.extend([f'def {part} : List (List Char) := {leftparts} ++ {rightparts}',
                    f'theorem {part}_literal : {part} = ['+', '.join(f'{tag}_chunk{i}' for i in range(lo,hi))+'] := by',
                    f'  unfold {part}'])
                if leftliteral:lines.append(f'  rw [{leftliteral}]')
                if rightliteral:lines.append(f'  rw [{rightliteral}]')
                lines.extend(['  rfl',f'theorem {part}_flatten : {node}_chars = {part}.flatten := by',
                    f'  unfold {node}_chars {part}',f'  rw [List.flatten_append, ← {leftflat}, ← {rightflat}]'])
                parts_info[node]=(part,part+'_literal',part+'_flatten')
            return node,node+'_chars',node+'_characters',lt+rt,node+'_literal'
        root,root_chars,root_proof,_,root_literal=balanced(0,len(chunks))
        lines += [f'theorem {tag}_string_exact : {root} = {data_module}.{tag}_0 := by',f'  exact {root_literal}',
                  f'theorem {tag}_flatten_exact : {root_chars} = {tag}_chunks.flatten := by']
        if balanced_flatten:
            part,literal,flat=parts_info[root]
            lines += [f'  rw [{flat}, {literal}]','  rfl']
        else:
            lines += ['  simp only ['+', '.join(character_defs+[tag+'_chunks','List.flatten_cons','List.flatten_nil','List.append_assoc','List.append_nil'])+']']
        lines += [f'theorem {tag}_source_lex : tokenize {data_module}.{tag}_0 = some {tag}_tokens := by',
                  '  unfold tokenize',f'  rw [← {tag}_string_exact, {root_proof}, {tag}_flatten_exact]',
                  f'  exact {tag}_characters_lex','']
    lines += ['end ' + namespace,'']
    return '\n'.join(lines)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--declarations',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--names',nargs='+');p.add_argument('--namespace',default='C11DeclarationCuts');p.add_argument('--data-module',default='C11ActualDeclarationData');p.add_argument('--balanced-flatten',action='store_true');a=p.parse_args()
    with a.out.open('x') as f:f.write(generate(json.loads(a.declarations.read_text()),a.names,a.namespace,a.data_module,a.balanced_flatten))
