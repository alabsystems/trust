#!/usr/bin/env python3
"""Untrusted token/span advice. Lean's separate grammar checks every source step.
No C typing, macro/source binding, C11 execution or runtime authority is supplied.
"""
import argparse
import json
from pathlib import Path
import re

PUNCT = ['[',']','(',')','{','}','.','->','++','--','&','*','+','-','~','!','/','%','<<','>>','<','>','<=','>=','==','!=','^','|','&&','||','?',':',';','...','=','*=','/=','%=','+=','-=','<<=','>>=','&=','^=','|=',',','#','##','<:',':>','<%','%>','%:','%:%:']


def spans(raw):
    text=raw.decode('ascii');out=[];position=0
    while position<len(text):
        tail=text[position:]
        m=re.match(r'[ \t\n]+',tail)
        if m:kind='white';piece=m.group()
        else:
            m=re.match(r'[A-Za-z_][A-Za-z0-9_]*',tail)
            if m:kind='identifier';piece=m.group()
            elif tail[0] in '01':kind='integer01';piece=tail[0]
            else:
                choices=[p for p in PUNCT if tail.startswith(p)]
                if not choices:raise ValueError((position,tail[:20]))
                kind='punctuator';piece=max(choices,key=len)
        out.append((kind,piece));position+=len(piece)
    assert ''.join(piece for _,piece in out).encode('ascii')==raw
    return out


def generate(drop,increment):
    lines=['-- Copyright 2026 Andrew Yates | Apache-2.0','import C11OrdinaryTokens','import CAtomicDropSource','import CAtomicIncrementSource','','/-! Actual complete-byte witnesses for the separate ordinary-fragment grammar. Not a C typing/execution/source-custody theorem. -/','namespace C11ActualTokens','open C11OrdinaryTokens','']
    for tag,raw,source,tokens in [('drop',drop,'CAtomicDropSource.actualSource','CAtomicDropSyntax.tokens CAtomicDropSource.proposal'),('increment',increment,'CAtomicIncrementSource.actualSource','CAtomicIncrementSyntax.tokens CAtomicIncrementSource.proposal')]:
        steps=spans(raw);n=len(steps)
        lines += [f'def {tag}_source{n} : List UInt8 := []',f'def {tag}_tokens{n} : List String := []',f'theorem {tag}_lex{n} : Lexes {tag}_source{n} {tag}_tokens{n} := .done']
        for i in reversed(range(n)):
            kind,piece=steps[i];rawpiece=list(piece.encode('ascii'));string=json.dumps(piece)
            prefix=str(rawpiece)
            lines += [f'def {tag}_source{i} : List UInt8 := {prefix} ++ {tag}_source{i+1}']
            if kind=='white':
                lines += [f'def {tag}_tokens{i} : List String := {tag}_tokens{i+1}',f'theorem {tag}_lex{i} : Lexes {tag}_source{i} {tag}_tokens{i} :=',f'  .whitespace {rawpiece} _ _ (by decide) {tag}_lex{i+1}']
            else:
                lines += [f'def {tag}_tokens{i} : List String := {string} :: {tag}_tokens{i+1}',f'theorem {tag}_bytes{i} : bytes {string} = {rawpiece} := by rfl',f'theorem {tag}_valid{i} : valid .{kind} {rawpiece} {tag}_source{i+1} = true := by decide',f'theorem {tag}_lex{i} : Lexes {tag}_source{i} {tag}_tokens{i} := by',f'  change Lexes ({rawpiece} ++ {tag}_source{i+1}) ({string} :: {tag}_tokens{i+1})',f'  rw [← {tag}_bytes{i}]',f'  exact .token .{kind} {string} _ _ (by rw [{tag}_bytes{i}]; exact {tag}_valid{i}) {tag}_lex{i+1}']
        source_module='CAtomicDropSource' if tag=='drop' else 'CAtomicIncrementSource'
        byte_chunks=(len(raw)+7)//8
        defs=[f'{tag}_source{i}' for i in range(n+1)]+[source_module+'.actualSource',source_module+'.actual_chunks']+[source_module+f'.actual_c{i}' for i in range(byte_chunks)]+['List.flatten_cons','List.flatten_nil','List.cons_append','List.nil_append']
        lines += [f'theorem {tag}_source_exact : {tag}_source0 = {source} := by', '  simp only ['+', '.join(defs)+']',f'theorem {tag}_tokens_exact : {tag}_tokens0 = {tokens} := by rfl',f'theorem {tag}_actual_lexes : Lexes {source} ({tokens}) := by',f'  rw [← {tag}_source_exact, ← {tag}_tokens_exact]',f'  exact {tag}_lex0',f'#print axioms {tag}_actual_lexes','']
    lines += ['end C11ActualTokens','']
    return '\n'.join(lines)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--drop',required=True,type=Path)
    p.add_argument('--increment',required=True,type=Path)
    p.add_argument('--out',required=True,type=Path)
    a=p.parse_args()
    with a.out.open('x') as out:out.write(generate(a.drop.read_bytes(),a.increment.read_bytes()))
