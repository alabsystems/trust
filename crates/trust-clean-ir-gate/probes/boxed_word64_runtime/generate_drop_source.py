#!/usr/bin/env python3
"""Untrusted proof-cut advice from exact captured C bytes. Lean checks every cut.
The Clang span is DATA, not a proved whole-TU/source or C11 relation.
"""
import argparse
import json
from pathlib import Path


def emit(mode, word, reversed_, token):
    return 'normal', [], [token] + reversed_


def normal(state, b):
    mode, word, rev = state
    if b in b' \t\n\r\v\f': return state
    if chr(b).isascii() and (chr(b).isalpha() or chr(b).isdigit() or b == 95):
        return 'ident', [b], rev
    if b in [47,62,60,38,33,45]: return {47:'slash',62:'greater',60:'less',38:'amp',33:'bang',45:'dash'}[b], [], rev
    if b in b'(){}*&.,;': return emit(mode,word,rev,chr(b))
    return None


def step(state, b):
    if state is None: return None
    if b in [92,63] or not (b in [9,10] or 32<=b<=126): return None
    mode, word, rev = state
    if mode == 'normal': return normal(state,b)
    if mode == 'ident':
        if chr(b).isascii() and (chr(b).isalnum() or b==95): return mode,[b]+word,rev
        return normal(emit(mode,word,rev,bytes(word[::-1]).decode('ascii')),b)
    if mode == 'slash': return ('line',[],rev) if b==47 else (('block',[],rev) if b==42 else None)
    if mode == 'line': return ('normal' if b==10 else 'line'),word,rev
    if mode == 'block': return ('star' if b==42 else 'block'),word,rev
    if mode == 'star': return ('normal' if b==47 else 'star' if b==42 else 'block'),word,rev
    if mode == 'greater': return emit(mode,word,rev,'>=') if b==61 else normal(emit(mode,word,rev,'>'),b)
    if mode == 'less': return emit(mode,word,rev,'<=') if b==61 else normal(emit(mode,word,rev,'<'),b)
    if mode == 'amp': return emit(mode,word,rev,'&&') if b==38 else normal(emit(mode,word,rev,'&'),b)
    if mode == 'bang': return emit(mode,word,rev,'!=') if b==61 else normal(emit(mode,word,rev,'!'),b)
    if mode == 'dash': return emit(mode,word,rev,'->') if b==62 else None
    raise ValueError(mode)


def generate(raw, kind):
    source=raw.decode('ascii')
    mutants={'actual':source,'changed_guard':source.replace('>= CLEAN_RC_STICKY_DROP','> CLEAN_RC_STICKY_DROP'),
     'changed_old_comparison':source.replace('!= 0','!= 1'),
     'changed_operand':source.replace('atomic_fetch_sub_explicit(&o->header.ref_count','atomic_fetch_sub_explicit(&other->header.ref_count'),
     'missing_fence':source.replace('    atomic_thread_fence(memory_order_acquire);\n',''),
     'changed_fence_order':source.replace('memory_order_acquire','memory_order_relaxed'),
     'missing_rmw':source.replace('    if (atomic_fetch_sub_explicit(&o->header.ref_count, 1, memory_order_release) != 0)\n        return false;\n',''),
     'appended_statement':source+' return true;','unterminated_comment':source+' /*'}
    if kind == 'increment':
        mutants={'actual':source,
          'changed_guard':source.replace('< CLEAN_RC_STICKY','> CLEAN_RC_STICKY'),
          'changed_cutoff':source.replace('< CLEAN_RC_STICKY)', '< CLEAN_RC_STICKY_DROP)'),
          'changed_scalar_guard':source.replace('if (!clean_is_scalar', 'if (clean_is_scalar'),
          'changed_operand':source.replace('atomic_fetch_add_explicit(&o->header.ref_count','atomic_fetch_add_explicit(&other->header.ref_count'),
          'missing_rmw':source.replace('        atomic_fetch_add_explicit(&o->header.ref_count, 1, memory_order_relaxed);\n',''),
          'changed_addend':source.replace(', 1, memory_order_relaxed)', ', 2, memory_order_relaxed)'),
          'appended_statement':source+' return;', 'unterminated_comment':source+' /*'}
    mutants['line_splice']=source.replace('{\n','{ // \\\n',1)
    mutants['trigraph_splice']=source.replace('{\n','{ // ??/\n',1)
    mutants['carriage_return']=source.replace('\n','\r')
    namespace='CAtomicDropSource' if kind=='drop' else 'CAtomicIncrementSource'
    syntax='CAtomicDropSyntax' if kind=='drop' else 'CAtomicIncrementSyntax'
    function='clean_rc_drop' if kind=='drop' else 'clean_inc'
    macro='CLEAN_RC_STICKY_DROP' if kind=='drop' else 'CLEAN_RC_STICKY'
    for name,text in mutants.items():
        assert name=='actual' or text!=source,name
    out=['-- Copyright 2026 Andrew Yates | Apache-2.0','import CAtomicDropSyntax',f'import {syntax}','',
         '/-! Untrusted byte/cut advice. All original bytes+all8 mutants remain. Whole-TU/span, macro/type and C11 execution relations remain open. -/',
         f'namespace {namespace}','open CAtomicDropSyntax',
         f'def proposal : Proposal := ⟨"{function}", "o", "{macro}"⟩','']
    for tag,text in mutants.items():
        data=text.encode('ascii');chunks=[list(data[i:i+8]) for i in range(0,len(data),8)]
        state=('normal',[],[])
        out += [f'def {tag}_r0 : List String := []',f'def {tag}_s0 : State := initial']
        cutnames=[]
        for i,chunk in enumerate(chunks):
            old=state
            for b in chunk: state=step(state,b)
            out.append(f'def {tag}_c{i} : List UInt8 := {chunk}')
            nextExpr='none'
            if state is not None:
                mode,word,rev=state;oldrev=old[2] if old is not None else []
                assert len(rev)>=len(oldrev) and (not oldrev or rev[-len(oldrev):]==oldrev)
                added=rev[:len(rev)-len(oldrev)]
                prefix='['+', '.join(json.dumps(s) for s in added)+']'
                out.append(f'def {tag}_r{i+1} : List String := {prefix} ++ {tag}_r{i}')
                out.append(f'def {tag}_s{i+1} : State := ⟨.{mode}, {word}, {tag}_r{i+1}⟩')
                nextExpr=f'some {tag}_s{i+1}'
            prev=f'some {tag}_s{i}' if old is not None else 'none'
            name=f'{tag}_cut{i}';cutnames.append(name)
            out.append(f'theorem {name} : feed ({prev}) {tag}_c{i} = {nextExpr} := by rfl')
        out.append(f'def {tag}_chunks : List (List UInt8) := ['+', '.join(f'{tag}_c{i}' for i in range(len(chunks)))+']')
        out.append(f'def {"actualSource" if tag=="actual" else tag} : List UInt8 := {tag}_chunks.flatten')
        final=f'some {tag}_s{len(chunks)}' if state is not None else 'none'
        out.append(f'theorem {tag}_feed : {tag}_chunks.foldl feed (some initial) = {final} := by')
        out.append(f'  change {tag}_chunks.foldl feed (some {tag}_s0) = _')
        out.append(f'  simp only [{tag}_chunks, List.foldl_cons, List.foldl_nil]')
        out.append('  rw ['+', '.join(cutnames)+']')
        if tag=='actual':
            out += [f'theorem actual_tokens : tokenize actualSource = some ({syntax}.tokens proposal) := by',
                    '  rw [actualSource, ← chunks_exact, tokenizeChunks, actual_feed]', '  rfl',
                    f'theorem actual_syntax : {syntax}.check actualSource proposal = true := by',
                    f'  unfold {syntax}.check', '  rw [actual_tokens]', '  simp']
        else:
            out += [f'theorem {tag}_refuses : {syntax}.check {tag} proposal = false := by',
                    f'  unfold {syntax}.check',f'  rw [{tag}, ← chunks_exact, tokenizeChunks, {tag}_feed]',
                    '  decide']
        out.append('')
    out += ['#print axioms actual_syntax','#print axioms actual_tokens',f'end {namespace}','']
    return '\n'.join(out)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--kind',choices=['drop','increment'],required=True)
    parser.add_argument('--ast',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    a=parser.parse_args();tree=json.loads(a.ast.read_bytes());nodes=[n for n in tree['inner'] if n.get('kind')=='FunctionDecl' and n.get('name')==('clean_rc_drop' if a.kind=='drop' else 'clean_inc')];assert len(nodes)==1
    n=nodes[0];lo=n['range']['begin']['offset'];hi=n['range']['end']['offset']+n['range']['end']['tokLen'];raw=a.source.read_bytes()[lo:hi];assert raw.startswith(b'static inline ') and raw.endswith(b'}')
    with a.out.open('x') as f:f.write(generate(raw,a.kind))
