#!/usr/bin/env python3
"""Untrusted source/lexer cut advice for the retained conditional unit control."""
from pathlib import Path
import importlib.util,json
w=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('cuts',w/'generate_c11_declaration_cuts.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
base_step=m.step;base_state=m.state;base_finish=m.finish
ops={'&':'amp','!':'bang','<':'less','>':'greater'}
def canon(s):return (s,'none') if len(s)==3 else s
def state(s):
 if s is None:return 'none'
 b,p=canon(s);return 'some { base := '+base_state(b).removeprefix('some ') +', pending := .'+p+' }'
def start(b,c):
 p=ops.get(c,'none')
 if p!='none' and b[0] in ['normal','word']:
  if b[0]=='word':b=m.emit(b,b[1][::-1])
  return b,p
 b=base_step(b,c);return None if b is None else (b,'none')
def step(s,c):
 if s is None or c in '\\?\r\0':return None
 b,p=canon(s)
 if p=='none':return start(b,c)
 if p=='amp':return (m.emit(b,'&&'),'none') if c=='&' else None
 spelling={'bang':'!','less':'<','greater':'>'}[p]
 if p in ['less','greater'] and c==spelling:return None
 return (m.emit(b,spelling+'='),'none') if c=='=' else start(m.emit(b,spelling),c)
def finish(s):
 b,p=canon(s)
 if p=='amp':raise ValueError('amp')
 if p!='none':b=m.emit(b,{'bang':'!','less':'<','greater':'>'}[p])
 return base_finish(b)
m.step=step;m.state=state;m.finish=finish
import argparse
import hashlib
import generate_c11_directive_line_cuts as fence
p=argparse.ArgumentParser(description='Untrusted full actual owner character/lexer cut advice')
p.add_argument('--input',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
a=p.parse_args();raw=a.input.read_bytes().decode('utf-8');a.out.mkdir()
(a.out/'C11AssertHeaderData.lean').write_text('-- Copyright 2026 Andrew Yates | Apache-2.0\nimport Init\nnamespace C11AssertHeaderData\ndef assertHeader_0 : String := '+json.dumps(raw,ensure_ascii=False)+'\nend C11AssertHeaderData\n')
s=m.generate([{'name':'assertHeader','raw':raw}],['assertHeader'],'C11AssertHeaderCuts','C11AssertHeaderData',True).replace('import C11DeclarationLexer','import C11DirectiveLexer').replace('open C11DeclarationLexer','open C11DirectiveLexer')
(a.out/'C11AssertHeaderCuts.lean').write_text(s)
s=fence.generate(raw).replace('C11GuardHeaderCuts','C11AssertHeaderCuts').replace('C11GuardDirectiveCuts','C11AssertDirectiveCuts').replace('uint32Full','assertHeader').replace('C11GuardHeaderData','C11AssertHeaderData')
(a.out/'C11AssertDirectiveCuts.lean').write_text(s)
(a.out/'INPUT.json').write_text(json.dumps({'bytes':len(raw.encode()),'sha256':hashlib.sha256(raw.encode()).hexdigest(),'scope':'complete captured actual owner; no active context/target/TU/source semantic grant'},indent=2)+'\n')
