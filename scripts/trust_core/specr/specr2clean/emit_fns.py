"""Emit Clean definitions for specr functions and constants."""

import re
from common import *
from lower import Env, FnCtx, Lowerer
from calls import signature, payload_tys
from tyres import resolve, scc


def argmatch_stmts(fd):
    """Merge the arms of a `#[specr::argmatch(p)]` declaration into one match."""
    decl_inputs = fd.inputs
    pos = None
    names = []
    for i, inp in enumerate(decl_inputs):
        ik, iv = one_key(inp)
        if ik == 'receiver':
            names.append('self')
            if fd.argmatch == 'self':
                pos = i
            continue
        pk, pv = one_key(iv['pat'])
        src = pv['ident'] if pk == 'ident' else f'__arg{i}'
        names.append(src)
        if pk == 'ident' and pv['ident'] == fd.argmatch:
            pos = i
    if pos is None:
        raise Refusal('argmatch-parameter', fd.argmatch)
    arms = []
    for a in fd.arms:
        if len(a.inputs) != len(decl_inputs):
            raise Refusal('argmatch-arm-arity', a.display)
        ak, av = one_key(a.inputs[pos])
        if ak != 'typed':
            raise Refusal('argmatch-arm-receiver', a.display)
        pat = av['pat']
        lets = []
        for j, inp in enumerate(a.inputs):
            if j == pos:
                continue
            ik, iv = one_key(inp)
            if ik == 'receiver':
                continue
            pk, pv = one_key(iv['pat'])
            if pk == 'ident' and pv['ident'] == names[j]:
                continue
            lets.append({'let': {'pat': iv['pat'], 'init': {'expr': {'path': {'segments': [{'ident': names[j]}]}}}}})
        body = {'block': {'stmts': lets + (a.stmts or [])}}
        arms.append({'pat': pat, 'body': body})
    scrut = {'path': {'segments': [{'ident': names[pos]}]}}
    return [{'expr': [{'match': {'expr': scrut, 'arms': arms, 'argmatch_arms': True}}, False]}], len(fd.arms)


class Emitted:
    def __init__(self, key, lean_name, header, body, callees, status, detail, display, file, kind, poly):
        self.key, self.lean_name, self.header, self.body = key, lean_name, header, body
        self.callees, self.status, self.detail, self.display, self.file, self.kind = callees, status, detail, display, file, kind
        self.poly = poly


CALL_RE = None


def lower_function(L, fd):
    """Returns an Emitted record. status: translated | refused-body | refused-signature."""
    reset_ids = None
    L.cur_fn = fd
    L.arm_outcomes = []
    L.partial = []
    try:
        sig = signature(L, fd)
    except Refusal as r:
        return Emitted(fd.lean_name, fd.lean_name, None, None, set(), 'refused-signature', r, fd.display, fd.file, 'fn', False)
    fuel = 'fuel'
    binders = []
    env = Env(None)
    outputs = []
    state_binders = []
    for p in sig.params:
        ln = fresh('self' if p.is_self else p.src.strip('_'))
        binders.append(f'({ln} : {lean_type(p.ty)})')
        mutable = p.ref == 'mut' or p.mut_kw
        env = env.bind(p.src, ln, p.ty, mutable=mutable)
        if p.ref == 'mut':
            outputs.append(p.src)
    for p in sig.params:
        if p.is_fn:
            sn = fresh(p.src.strip('_') + '_st')
            state_binders.append(f'({sn} : {p.ty[3][1]})')
            env = env.bind(f'{p.src}#state', sn, p.ty[3], mutable=True)
            outputs.append(f'{p.src}#state')
    env.fn = FnCtx(sig.ret_ty, outputs)
    polys = ''.join(f'({v} : Type) ' for v in sig.polys)
    try:
        ptys = [sig.ret_ty] + [env.vars[o].ty for o in outputs]
        payload = lean_type(tuple_ty(ptys), 'arg')
        dom_tys = [NAME] + [p.ty for p in sig.params] + [p.ty[3] for p in sig.params if p.is_fn]
    except Refusal as r:
        return Emitted(fd.lean_name, fd.lean_name, None, None, set(), 'refused-signature', r, fd.display, fd.file, 'fn', False)
    header = f'def {fd.lean_name} {polys}({fuel} : Nat) ' + ' '.join(binders + state_binders) + f' : SOut {payload}'
    try:
        if fd.argmatch:
            stmts, narms = argmatch_stmts(fd)
        else:
            if fd.stmts is None:
                raise Refusal('function-without-body', fd.display)
            stmts = fd.stmts
        # parameter patterns
        pre = []
        for i, p in enumerate(sig.params):
            if not p.is_self and p.src.startswith('__arg') and not fd.argmatch:
                pre.append({'let': {'pat': p.pat, 'init': {'expr': {'path': {'segments': [{'ident': p.src}]}}}}})
        body = L.lower_block(pre + list(stmts), env, sig.ret_ty, lambda a, t, env2: env2.fn.ret(a, env2))
        status, detail = 'translated', None
        refused_arms = [o for o in L.arm_outcomes if o[2] is not None]
        if refused_arms:
            status = 'translated-with-refused-arms'
            detail = refused_arms
        elif L.partial:
            status = 'translated-with-refused-expressions'
            detail = list(dict.fromkeys(L.partial))
    except Refusal as r:
        body = f'SOut.refused {lean_string(r.construct + " in " + fd.display)}'
        status, detail = 'refused-body', r
    full = f'match {fuel} with | 0 => SOut.fuel | {fuel} + 1 => {body}'
    callees = set(re.findall(r'\b(MRf\.[A-Za-z0-9_.]+?)(?= |\)|$)', body))
    em = Emitted(fd.lean_name, fd.lean_name, header, full, callees, status, detail, fd.display, fd.file, 'fn', bool(sig.polys))
    em.fn_type = 'Type → ' * len(sig.polys) + arrow_type(dom_tys, f'SOut {payload}')
    return em


def lower_const(L, cd):
    L.cur_fn = type('C', (), {'owner': cd.owner, 'generics': cd.generics, 'display': f'{cd.owner}::{cd.name}', 'trait': cd.trait})()
    try:
        ty = resolve(L.prog, cd.ty_json, cd.generics, cd.owner)
    except Refusal as r:
        return Emitted(cd.lean_name, cd.lean_name, None, None, set(), 'refused-signature', r, f'{cd.owner}::{cd.name}', cd.file, 'const', False)
    header = f'def {cd.lean_name} (fuel : Nat) : SOut {lean_type(ty, "arg")}'
    env = Env(FnCtx(ty, []))
    try:
        body = L.lower_expr(cd.expr, env, ty, lambda a, t, env2: f'SOut.ok {a}')
        status, detail = 'translated', None
    except Refusal as r:
        body = f'SOut.refused {lean_string(r.construct)}'
        status, detail = 'refused-body', r
    full = f'match fuel with | 0 => SOut.fuel | fuel + 1 => {body}'
    callees = set(re.findall(r'\b(MRf\.[A-Za-z0-9_.]+?)(?= |\)|$)', body))
    em = Emitted(cd.lean_name, cd.lean_name, header, full, callees, status, detail, f'{cd.owner}::{cd.name}', cd.file, 'const', False)
    em.fn_type = arrow_type([NAME], f'SOut {lean_type(ty, "arg")}')
    return em


def emit_all(L, emitted, out):
    by_name = {e.lean_name: e for e in emitted if e.header is not None}
    nodes = sorted(by_name)
    while True:
        edges = {n: sorted(c for c in by_name[n].callees if c in by_name) for n in nodes}
        comps = scc(nodes, edges)
        # A record of mutually recursive functions cannot hold a polymorphic
        # member (its field type would quantify over `Type`); such members are
        # refused, which removes their calls and breaks the cycle.
        changed = False
        for comp in comps:
            if len(comp) > 1:
                for n in comp:
                    m = by_name[n]
                    if m.poly and m.status != 'refused-body':
                        m.body = f'match fuel with | 0 => SOut.fuel | fuel + 1 => SOut.refused {lean_string("polymorphic-function-in-mutual-recursion in " + m.display)}'
                        m.status = 'refused-body'
                        m.detail = Refusal('polymorphic-function-in-mutual-recursion', ', '.join(comp))
                        m.callees = set()
                        changed = True
        if not changed:
            break
    groups = []
    for comp in comps:
        rec = len(comp) > 1 or comp[0] in edges[comp[0]]
        members = [by_name[n] for n in comp]
        # A recursive definition goes through a record of its group's functions,
        # tied by structural recursion on `fuel`: Clean's own recursion lowering
        # refuses bodies of this size and shape (measured 2026-09-17), and the
        # tie is a two-line structural recursion it always accepts. Polymorphic
        # members cannot be record fields, so those keep direct recursion.
        if len(comp) == 1 and (not rec or members[0].poly):
            e = members[0]
            out.append(f'{e.header} :=')
            out.append(f'  {e.body}')
            out.append('')
            groups.append((comp, 'self-recursive-direct' if rec else 'non-recursive'))
            continue
        if any(m.poly for m in members):
            raise Refusal('polymorphic-function-in-mutual-recursion', str(comp))
        rec_name = 'MR_rec_' + str(len(groups))
        field = {n: 'f_' + n.replace('.', '_') for n in comp}
        out.append(f'structure {rec_name} where')
        for m in members:
            t = m.fn_type
            out.append(f'  {field[m.lean_name]} : {t}')
        out.append('')
        for m in members:
            body = m.body
            for n in comp:
                body = re.sub(r'\b' + re.escape(n) + r' fuel\b', f'(r.{field[n]}) fuel', body)
            h = m.header.replace(f'def {m.lean_name}', f'def {m.lean_name}_open (r : {rec_name})', 1)
            out.append(f'{h} :=')
            out.append(f'  {body}')
            out.append('')
        out.append(f'def {rec_name}.tie : Nat → {rec_name}')
        out.append(f'  | 0 => {rec_name}.mk ' + ' '.join(f'({fuel_out_lambda(m.header)})' for m in members))
        out.append(f'  | n + 1 => {rec_name}.mk ' + ' '.join(f'({m.lean_name}_open ({rec_name}.tie n))' for m in members))
        out.append('')
        for m in members:
            params = header_params(m.header)
            names = ' '.join(p[0] for p in params)
            out.append(f'{m.header} :=')
            out.append(f'  ({rec_name}.tie fuel).{field[m.lean_name]} {names}')
            out.append('')
        groups.append((comp, 'mutual' if len(comp) > 1 else 'self-recursive-tied'))
    return groups


def header_params(header):
    """[(name, type)] of the explicit binders of a generated header."""
    sig = header[header.index(' (fuel : Nat)'):]
    sig = sig[:sig.rindex(' : SOut ')]
    out = []
    depth = 0
    cur = ''
    for ch in sig:
        if ch == '(':
            if depth == 0:
                cur = ''
            else:
                cur += ch
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                name, _, ty = cur.partition(' : ')
                out.append((name.strip(), ty.strip()))
            else:
                cur += ch
        elif depth > 0:
            cur += ch
    return out


def header_type(header):
    params = header_params(header)
    ret = header[header.rindex(' : SOut ') + 3:]
    return ' → '.join([t for _, t in params] + [ret])


def fuel_out_lambda(header):
    params = header_params(header)
    ret = header[header.rindex(' : SOut ') + 3:]
    return 'fun ' + ' '.join(f'(_ : {t})' for _, t in params) + f' => (SOut.fuel : {ret})'
