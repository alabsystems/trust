"""Lowering of specr function bodies to Clean terms.

Every specr function becomes a total Clean function into `SOut`. Imperative
constructs are compiled away:

  * mutation      -> SSA-style rebinding; `&mut` receivers/arguments are
                     returned in the result tuple and written back;
  * control flow  -> continuation-passing: `return`, `?`, `throw_*!` and
                     `break`/`continue` do not call the continuation;
                     branches that fall through share a join point;
  * loops         -> `SLoop.forS` / `SLoop.whileS` over an explicit state tuple;
  * closures      -> `args -> σ -> SOut (result, &mut args, σ)` where σ holds
                     the places the closure mutates (found by a first pass);
  * recursion     -> fuel, decremented on entry to every function.

`lower_*` functions take a continuation `k(atom, ty, env) -> str`.
"""

import itertools
from common import *
from tyres import resolve, param_ref_kind, ty_children

_var_ids = itertools.count()


class Var:
    __slots__ = ('lean', 'ty', 'mutable', 'id')

    def __init__(self, lean, ty, mutable, vid=None):
        self.lean, self.ty, self.mutable = lean, ty, mutable
        self.id = next(_var_ids) if vid is None else vid


class Env:
    def __init__(self, fnctx):
        self.vars = {}          # source name / captured place 'root.f' / closure state 'f#state' -> Var
        self.globs = {}         # glob-imported variant name -> [adt names]
        self.aliases = {}       # `use X as B`: B -> X
        self.loop = None        # LoopCtx
        self.fn = fnctx
        self.outer = None       # names of the enclosing scope (closure capture analysis)

    def copy(self):
        e = Env(self.fn)
        e.vars = dict(self.vars)
        e.globs = dict(self.globs)
        e.aliases = dict(self.aliases)
        e.loop = self.loop
        e.outer = self.outer
        return e

    def bind(self, name, lean, ty, mutable=False):
        e = self.copy()
        e.vars[name] = Var(lean, ty, mutable)
        return e

    def set(self, name, lean):
        e = self.copy()
        v = e.vars[name]
        e.vars[name] = Var(lean, v.ty, v.mutable, v.id)
        return e


class FnCtx:
    """What returning means in a function (closure=False) or closure."""

    def __init__(self, ret_ty, outputs, closure_sigma=None, capture_log=None):
        self.ret_ty = ret_ty
        self.outputs = outputs              # env names returned after the value
        self.closure_sigma = closure_sigma  # list of captured env names, or None for functions
        self.capture_log = capture_log

    def base_payload(self, atom, env):
        parts = [atom] + [env.vars[o].lean for o in self.outputs]
        if self.closure_sigma is not None:
            parts.append(tuple_text([env.vars[c].lean for c in self.closure_sigma]))
        return parts[0] if len(parts) == 1 else '(' + ', '.join(parts) + ')'

    def payload_ty(self, env):
        parts = [self.ret_ty] + [env.vars[o].ty for o in self.outputs]
        if self.closure_sigma is not None:
            parts.append(tuple_ty([env.vars[c].ty for c in self.closure_sigma]))
        return tuple_ty(parts)

    def ret_raw(self, payload):
        return f'SOut.ok {payload}'

    def ret(self, atom, env):
        return self.ret_raw(self.base_payload(atom, env))

    def inner_ty(self, env):
        return lean_type(self.payload_ty(env), 'arg')

    def term_ty(self, env):
        return f'SOut {self.inner_ty(env)}'


class LoopFnCtx:
    """Inside a loop body, returning produces `SCtl.ret payload`."""

    def __init__(self, outer):
        self.outer = outer
        self.ret_ty = outer.ret_ty
        self.outputs = outer.outputs
        self.closure_sigma = outer.closure_sigma
        self.capture_log = outer.capture_log

    def base_payload(self, atom, env):
        return self.outer.base_payload(atom, env)

    def payload_ty(self, env):
        return self.outer.payload_ty(env)

    def ret_raw(self, payload):
        return f'SOut.ok (SCtl.ret {payload})'

    def ret(self, atom, env):
        return self.ret_raw(self.base_payload(atom, env))

    def inner_ty(self, env):
        return self.ctl_ty

    def term_ty(self, env):
        return f'SOut {self.ctl_ty}'


class LoopCtx:
    def __init__(self, state_names, ctl_ty_text):
        self.state_names = state_names
        self.ctl_ty_text = ctl_ty_text

    def state(self, env):
        return tuple_text([env.vars[n].lean for n in self.state_names])


def tuple_text(parts):
    if not parts:
        return '()'
    if len(parts) == 1:
        return parts[0]
    return '(' + ', '.join(parts) + ')'


def ident_of_path_expr(e):
    k, v = one_key(e)
    if k == 'path' and not v.get('qself'):
        segs = v['segments']
        if len(segs) == 1 and not segs[0].get('arguments'):
            return segs[0]['ident']
    return None


def strip_parens(e):
    while True:
        k, v = one_key(e)
        if k in ('paren', 'group'):
            e = v['expr']
            continue
        return e


def mentions(node, acc):
    if isinstance(node, dict):
        for kk, vv in node.items():
            if kk == 'segments' and isinstance(vv, list) and vv:
                acc.add(vv[0]['ident'])
            if kk == 'ident' and isinstance(vv, str):
                acc.add(vv)
            mentions(vv, acc)
    elif isinstance(node, list):
        for x in node:
            mentions(x, acc)
    return acc


def member_name(node):
    """Field name of a syn field access / field value / field pattern node."""
    if 'ident' in node:
        return str(node['ident'])
    if 'index' in node:
        return str(node['index'])
    if 'member' in node:
        m = node['member']
        return str(one_key(m)[1]) if isinstance(m, dict) else str(m)
    raise Refusal('field-member', str(node)[:60])


def has_var(t):
    if t is None:
        return False
    if t[0] == 'var':
        return True
    return any(has_var(c) for c in ty_children(t))


def contains_infer(j):
    if j == '_':
        return True
    if isinstance(j, dict):
        if '_' in j and len(j) == 1:
            return True
        return any(contains_infer(v) for v in j.values())
    if isinstance(j, list):
        return any(contains_infer(v) for v in j)
    return False


def exp_or_none(t):
    """An expected type is only a hint when it is concrete."""
    return None if t is None or has_var(t) else t


def root_of(name):
    return name.split('.')[0].split('#')[0]


def restore_scope(outer, inner):
    """After a nested block keep the outer bindings, with the newest SSA name of
    each mutable variable that is still the same binding (same id)."""
    e = outer.copy()
    for n, v in outer.vars.items():
        iv = inner.vars.get(n)
        if iv is not None and iv.id == v.id:
            e.vars[n] = iv
    return e


def is_simple_atom(a):
    return bool(a) and all(c.isalnum() or c in '_.' for c in a) and not a[0].isdigit()


def field_proj_name(f):
    return lean_field('f' + f if f.isdigit() else f)


def setter_name(f):
    return 'f' + f if f.isdigit() else f


def tuple_proj(atom, n, i):
    out = atom
    for _ in range(i):
        out = f'(Prod.snd {out})'
    if i < n - 1:
        out = f'(Prod.fst {out})'
    return out


class Lowerer:
    def __init__(self, prog, tinfo):
        self.prog = prog
        self.tinfo = tinfo
        self.census = {}
        self.refusals = []
        self.cur_fn = None
        self.fuel = 'fuel'
        self._probe_cache = {}

    def note(self, construct):
        self.census[construct] = self.census.get(construct, 0) + 1

    def panic(self, env, msg):
        return f'(SOut.panic {lean_string(msg)} : {env.fn.term_ty(env)})'

    def rt(self, j):
        fd = self.cur_fn
        return resolve(self.prog, j, fd.generics if fd else {}, fd.owner if fd else None)

    def adt(self, name):
        return self.prog.adts.get(name)

    # ================================================================== places
    def place_of(self, e, env):
        e = strip_parens(e)
        k, v = one_key(e)
        if k == 'path':
            n = ident_of_path_expr(e)
            if n is not None and n in env.vars:
                return (n, [], env.vars[n].ty)
            return None
        if k == 'unary' and v['op'] == '*':
            return self.place_of(v['expr'], env)
        if k == 'reference':
            return self.place_of(v['expr'], env)
        if k == 'field':
            base = self.place_of(v['base'], env)
            if base is None:
                return None
            root, path, bty = base
            fname = member_name(v)
            return (root, path + [fname], self.field_ty(bty, fname))
        return None

    def field_ty(self, ty, fname):
        if ty[0] == 'adt':
            a = self.adt(ty[1])
            if a and a.kind == 'struct':
                for n, t in a.fields:
                    if n == fname:
                        return t
            raise Refusal('field-access', f'{show_ty(ty)}.{fname}')
        if ty[0] == 'tuple':
            return ty[1][int(fname)]
        raise Refusal('field-access-on', f'{show_ty(ty)}.{fname}')

    def resolve_place_var(self, place, env):
        root, path = place[0], place[1]
        for i in range(len(path), -1, -1):
            key = '.'.join([root] + path[:i])
            if key in env.vars:
                return key, path[i:]
        raise Refusal('unbound-place-root', root)

    def read_place(self, place, env):
        name, rest = self.resolve_place_var(place, env)
        full = '.'.join([place[0]] + place[1])
        captured = [x for x in env.vars if x.startswith(full + '.') and env.vars[x].mutable]
        if captured:
            raise Refusal('closure-reads-prefix-of-captured-place', f'{full} / {captured}')
        atom, ty = env.vars[name].lean, env.vars[name].ty
        for f in rest:
            atom, ty = self.project(atom, ty, f)
        return atom, ty

    def project(self, atom, ty, f):
        if ty[0] == 'adt':
            fty = self.field_ty(ty, f)
            return f'(MR_{ty[1]}.{field_proj_name(f)} {atom})', fty
        if ty[0] == 'tuple':
            i = int(f)
            return tuple_proj(atom, len(ty[1]), i), ty[1][i]
        raise Refusal('projection', show_ty(ty))

    def write_place(self, place, new_atom, env):
        root, path = place[0], place[1]
        name, rest = self.resolve_place_var(place, env)
        var = env.vars[name]
        if not var.mutable:
            raise Refusal('write-to-immutable-binding', name)
        log = env.fn.capture_log
        if log is not None and env.outer is not None and env.outer.get(name) == var.id:
            log.add('.'.join([root] + path))
        new_root = self.update_path(var.lean, var.ty, rest, new_atom)
        fresh_name = fresh(name.replace('.', '_').replace('#', '_'))
        return f'let {fresh_name} : {lean_type(var.ty)} := {new_root}; ', env.set(name, fresh_name)

    def update_path(self, atom, ty, path, new_atom):
        if not path:
            return new_atom
        f = path[0]
        sub_atom, sub_ty = self.project(atom, ty, f)
        inner = self.update_path(sub_atom, sub_ty, path[1:], new_atom)
        if ty[0] == 'adt':
            return f'(MR_{ty[1]}.set_{setter_name(f)} {atom} {inner})'
        if ty[0] == 'tuple':
            n = len(ty[1])
            return '(' + ', '.join(tuple_proj(atom, n, i) if i != int(f) else inner for i in range(n)) + ')'
        raise Refusal('place-update', show_ty(ty))

    # ================================================================== helpers
    def let_atom(self, atom, ty, base='t'):
        if is_simple_atom(atom):
            return '', atom
        n = fresh(base)
        return f'let {n} : {lean_type(ty)} := {atom}; ', n

    def bind_simple(self, call, ty, env, k, base='v'):
        n = fresh(base)
        return f'SOut.bind (α := {lean_type(ty, "arg")}) (β := {env.fn.inner_ty(env)}) ({call}) (fun ({n} : {lean_type(ty)}) => {k(n, ty, env)})'

    def bind_tuple(self, call, tys, k_names, env):
        names = [fresh('r') for _ in tys]
        if len(names) == 1:
            return f'SOut.bind (α := {lean_type(tys[0], "arg")}) (β := {env.fn.inner_ty(env)}) ({call}) (fun ({names[0]} : {lean_type(tys[0])}) => {k_names(names)})'
        p = fresh('p')
        return (f'SOut.bind (α := {lean_type(tuple_ty(tys), "arg")}) (β := {env.fn.inner_ty(env)}) ({call}) (fun ({p} : {lean_type(tuple_ty(tys))}) => '
                f'match {p} with | {tuple_text(names)} => {k_names(names)})')

    def join(self, env, ty, k, touched_nodes):
        names = set()
        for n in touched_nodes:
            mentions(n, names)
        state = sorted(n for n, v in env.vars.items() if v.mutable and root_of(n) in names)
        jp = fresh('jp')
        vparam = fresh('jv')
        params = [(vparam, ty)] + [(fresh(n.replace('.', '_').replace('#', '_')), env.vars[n].ty) for n in state]
        env_j = env
        for (pn, _), n in zip(params[1:], state):
            env_j = env_j.set(n, pn)
        body = k(vparam, ty, env_j)
        binders = ' '.join(f'({pn} : {lean_type(pt)})' for pn, pt in params)
        jty = arrow_type([pt for _, pt in params], env.fn.term_ty(env))
        used = [False]

        def prefix():
            return f'let {jp} : {jty} := (fun {binders} => {body}); ' if used[0] else ''

        def jump(atom, env_b):
            used[0] = True
            return f'{jp} ' + ' '.join([atom] + [env_b.vars[n].lean for n in state])
        return prefix, jump

    # ================================================================== blocks
    def lower_block(self, stmts, env, exp, k):
        return self._stmts(list(stmts or []), 0, env, exp, k)

    def _stmts(self, stmts, i, env, exp, k):
        if i >= len(stmts):
            return k('()', UNIT, env)
        sk, sv = one_key(stmts[i])
        last = i == len(stmts) - 1
        if sk == 'item':
            ik, iv = one_key(sv)
            if ik == 'use':
                return self._stmts(stmts, i + 1, self.apply_use(iv['tree'], env), exp, k)
            raise Refusal('item-in-block', ik)
        if sk == 'let':
            self.note('stmt:let')
            return self.lower_let(sv, env, lambda env2: self._stmts(stmts, i + 1, env2, exp, k), rest=stmts[i + 1:])
        if sk == 'expr':
            expr, semi = sv[0], sv[1]
            if last and not semi:
                return self.lower_expr(expr, env, exp, k)
            return self.lower_expr(expr, env, None, lambda a, t, env2: self._stmts(stmts, i + 1, env2, exp, k))
        raise Refusal('statement-kind', sk)

    def apply_use(self, tree, env):
        env = env.copy()
        path = []
        t = tree
        while True:
            if t == '*':
                target = path[-1]
                if target in self.prog.adts and self.prog.adts[target].kind == 'enum':
                    for vname, _, _ in self.prog.adts[target].variants:
                        env.globs[vname] = [target] + [x for x in env.globs.get(vname, []) if x != target]
                    self.note('stmt:use-glob-import')
                    return env
                raise Refusal('use-glob-of-non-enum', '::'.join(path))
            tk, tv = one_key(t)
            if tk == 'path':
                path.append(tv['ident'])
                t = tv['tree']
                continue
            if tk == 'rename':
                env.aliases[tv['rename']] = tv['ident']
                self.note('stmt:use-rename')
                return env
            if tk == 'ident':
                return env
            raise Refusal('use-tree', str(t)[:60])

    def lower_let(self, lv, env, k_env, rest=None):
        pat = lv['pat']
        init = lv.get('init')
        ann = None
        pk, pv = one_key(pat)
        if pk == 'type':
            if contains_infer(pv['ty']):
                self.note('typing:let-annotation-with-inferred-part')
                ann = None
            else:
                ann = self.rt(pv['ty'])
            pat = pv['pat']
            pk, pv = one_key(pat)
        if ann is None and pk == 'ident' and init is not None and rest is not None and self.is_empty_collection(init['expr']):
            ann = self.type_from_use_sites(pv['ident'], rest)
            if ann is not None:
                self.note('typing:empty-collection-from-use-site')
        if init is None:
            raise Refusal('let-without-initializer', '')
        diverge = init.get('diverge')
        if diverge is not None:
            self.note('stmt:let-else')

            def after_init(a, t, env2):
                def fail():
                    return self.lower_expr(diverge, env2, None, lambda a2, t2, env3: self.panic(env3, 'let-else block fell through'))
                return self.lower_pat(pat, a, t, env2, k_env, fail)
            return self.lower_expr(init['expr'], env, ann, after_init)

        def after(a, t, env2):
            return self.lower_pat(pat, a, ann or t, env2, k_env, lambda: self.panic(env2, 'irrefutable let pattern failed'))
        return self.lower_expr(init['expr'], env, ann, after)

    def is_empty_collection(self, e):
        ek, ev = one_key(e)
        if ek == 'call':
            fk, fv = one_key(ev['func'])
            if fk == 'path':
                ids = [x['ident'] for x in fv['segments']]
                if ids[-1] == 'new' and len(ids) >= 2 and ids[-2] in ('Map', 'List', 'Set') and not ev.get('args'):
                    return True
                if ids == ['__m_list'] and not ev.get('args'):
                    return True
        return False

    def type_from_use_sites(self, name, stmts):
        """The type of a variable initialised with an empty collection, taken
        from a later use of the variable at a position whose type is declared:
        a struct-literal field or an enum-variant constructor argument."""
        found = []

        def is_var(e):
            return isinstance(e, dict) and ident_of_path_expr(e) == name if isinstance(e, dict) and len(e) == 1 else False

        def walk(x):
            if isinstance(x, dict):
                if 'struct' in x and isinstance(x['struct'], dict) and 'path' in x['struct'] and 'fields' in x['struct'] and isinstance(x['struct']['fields'], list):
                    sv = x['struct']
                    ids = path_idents(sv['path'])
                    owner = ids[-1]
                    fields = None
                    if len(ids) >= 2 and ids[-2] in self.prog.adts and self.adt(ids[-2]).kind == 'enum':
                        for vn, st, fs in self.adt(ids[-2]).variants:
                            if vn == owner:
                                fields = fs
                    elif owner in self.prog.adts and self.adt(owner).kind == 'struct':
                        fields = self.adt(owner).fields
                    if fields is not None:
                        for f in sv['fields']:
                            if 'expr' in f and is_var(f['expr']):
                                fname = member_name(f)
                                for fn, t in fields:
                                    if fn == fname:
                                        found.append(t)
                if 'call' in x and isinstance(x['call'], dict):
                    cv = x['call']
                    fk, fv = one_key(cv['func'])
                    if fk == 'path':
                        ids = [q['ident'] for q in fv['segments']]
                        if len(ids) >= 2 and ids[-2] in self.prog.adts and self.adt(ids[-2]).kind == 'enum':
                            for vn, st, fs in self.adt(ids[-2]).variants:
                                if vn == ids[-1] and len(fs) == len(cv['args']):
                                    for arg, (fn, t) in zip(cv['args'], fs):
                                        if is_var(arg):
                                            found.append(t)
                for v in x.values():
                    walk(v)
            elif isinstance(x, list):
                for v in x:
                    walk(v)
        walk(stmts)
        return found[0] if found else None

    # ================================================================== patterns
    def lower_pat(self, pat, atom, ty, env, on_ok, on_fail):
        if pat == '_' or pat == 'wild':
            return on_ok(env)
        pk, pv = one_key(pat)
        if pk in ('wild', '_'):
            self.note('pattern:wildcard')
            return on_ok(env)
        if pk == 'ident':
            name = pv['ident']
            if pv.get('subpat'):
                raise Refusal('pattern-binding-at', name)
            variant = self.unit_variant_for(name, ty, env)
            if variant is not None:
                return self.test_variant(variant, atom, env, on_ok, on_fail)
            self.note('pattern:binding')
            pre, a = self.let_atom(atom, ty, name)
            return pre + on_ok(env.bind(name, a, ty, mutable=bool(pv.get('mut'))))
        if pk in ('type', 'paren', 'reference'):
            return self.lower_pat(pv['pat'], atom, ty, env, on_ok, on_fail)
        if pk == 'tuple':
            elems = pv.get('elems', [])
            if ty == UNIT and not elems:
                return on_ok(env)
            if ty[0] != 'tuple':
                raise Refusal('tuple-pattern-on', show_ty(ty))
            if any(e == 'rest' or (isinstance(e, dict) and one_key(e)[0] == 'rest') for e in elems):
                raise Refusal('tuple-pattern-rest', '')
            if len(elems) != len(ty[1]):
                raise Refusal('tuple-pattern-arity', f'{len(elems)} vs {show_ty(ty)}')
            self.note('pattern:tuple')
            names = [fresh('c') for _ in elems]

            def go(i, env2):
                if i == len(elems):
                    return on_ok(env2)
                return self.lower_pat(elems[i], names[i], ty[1][i], env2, lambda env3: go(i + 1, env3), on_fail)
            return f'(match {atom} with | {tuple_text(names)} => {go(0, env)})'
        if pk == 'tuple_struct':
            return self.pat_ctor(path_idents(pv['path']), pv.get('elems', []), None, atom, ty, env, on_ok, on_fail)
        if pk == 'struct':
            return self.pat_ctor(path_idents(pv['path']), None, pv.get('fields', []), atom, ty, env, on_ok, on_fail)
        if pk == 'path':
            return self.pat_ctor(path_idents(pv), [], None, atom, ty, env, on_ok, on_fail, unit=True)
        if pk == 'lit':
            kind, val = lit_value(pv)
            self.note('pattern:literal')
            if kind == 'int':
                return f'(match SInt.beq {atom} {lean_int(val)} with | true => {on_ok(env)} | false => {on_fail()})'
            if kind == 'bool':
                return f'(match {atom} with | {"true" if val else "false"} => {on_ok(env)} | _ => {on_fail()})'
            raise Refusal('literal-pattern', kind)
        if pk == 'or':
            self.note('pattern:or')
            cases = pv['cases']

            def try_case(i):
                if i == len(cases):
                    return on_fail()
                nxt = fresh('alt')
                used = [False]

                def fail_i():
                    used[0] = True
                    return f'{nxt} ()'
                text = self.lower_pat(cases[i], atom, ty, env, on_ok, fail_i)
                if not used[0]:
                    return text
                return f'let {nxt} : Unit → {env.fn.term_ty(env)} := (fun (_ : Unit) => {try_case(i + 1)}); ' + text
            return try_case(0)
        raise Refusal('pattern-kind', pk)

    def unit_variant_for(self, name, ty, env):
        if ty[0] == 'adt':
            a = self.adt(ty[1])
            if a and a.kind == 'enum':
                for vn, style, fs in a.variants:
                    if vn == name and style == 'unit':
                        return (ty[1], vn)
        if ty == ORDERING and name in ('Less', 'Equal', 'Greater'):
            return ('Ordering', name)
        if ty[0] == 'option' and name == 'None':
            return ('Option', 'None')
        return None

    def test_variant(self, variant, atom, env, on_ok, on_fail):
        adt_name, vn = variant
        if adt_name == 'Ordering':
            ln = {'Less': 'SOrdering.less', 'Equal': 'SOrdering.equal', 'Greater': 'SOrdering.greater'}[vn]
            return f'(match {atom} with | {ln} => {on_ok(env)} | _ => {on_fail()})'
        if adt_name == 'Option':
            return f'(match {atom} with | none => {on_ok(env)} | some _ => {on_fail()})'
        a = self.adt(adt_name)
        self.note('pattern:enum-variant')
        tail = f' | _ => {on_fail()}' if len(a.variants) > 1 else ''
        return f'(match {atom} with | MR_{adt_name}.{vn} => {on_ok(env)}{tail})'

    def pat_ctor(self, path, elems, fields, atom, ty, env, on_ok, on_fail, unit=False):
        name = path[-1]
        if ty[0] == 'option' and name in ('Some', 'None'):
            self.note('pattern:option')
            if name == 'None':
                return f'(match {atom} with | none => {on_ok(env)} | some _ => {on_fail()})'
            x = fresh('s')
            inner = self.lower_pat(elems[0], x, ty[1], env, on_ok, on_fail)
            return f'(match {atom} with | some {x} => {inner} | none => {on_fail()})'
        if ty[0] == 'result' and name in ('Ok', 'Err'):
            self.note('pattern:result')
            x = fresh('s')
            inner = self.lower_pat(elems[0], x, ty[2] if name == 'Ok' else ty[1], env, on_ok, on_fail)
            ctor, other = ('ok', 'err _') if name == 'Ok' else ('err', 'ok _')
            return f'(match {atom} with | SRes.{ctor} {x} => {inner} | SRes.{other} => {on_fail()})'
        if ty == ORDERING and name in ('Less', 'Equal', 'Greater'):
            return self.test_variant(('Ordering', name), atom, env, on_ok, on_fail)
        if ty[0] != 'adt':
            raise Refusal('constructor-pattern-on', f'{"::".join(path)} : {show_ty(ty)}')
        a = self.adt(ty[1])
        if a.kind == 'struct':
            if name not in (a.name, 'Self'):
                raise Refusal('struct-pattern-name', f'{"::".join(path)} vs {a.name}')
            vfields, vname, nvariants = a.fields, 'mk', 1
        else:
            owner = path[-2] if len(path) >= 2 else None
            owner = env.aliases.get(owner, owner)
            if owner not in (None, 'Self', a.name) and owner in self.prog.adts:
                raise Refusal('variant-pattern-of-other-enum', f'{"::".join(path)} vs {a.name}')
            found = [v for v in a.variants if v[0] == name]
            if not found:
                raise Refusal('unknown-variant-pattern', f'{"::".join(path)} in {a.name}')
            vname, style, vfields = found[0]
            nvariants = len(a.variants)
            if unit and style == 'unit':
                return self.test_variant((a.name, vname), atom, env, on_ok, on_fail)
        names = [fresh('f') for _ in vfields]
        sub = []
        if fields is not None:
            self.note('pattern:struct')
            by_name = {fname: (n, t) for (fname, t), n in zip(vfields, names)}
            for fp in fields:
                fname = member_name(fp)
                if fname not in by_name:
                    raise Refusal('struct-pattern-field', fname)
                n, t = by_name[fname]
                p = fp.get('pat') or {'ident': {'ident': fname}}
                sub.append((p, n, t))
        else:
            self.note('pattern:tuple-variant')
            elems = elems or []
            rest_idx = [i for i, e in enumerate(elems) if e == 'rest' or (isinstance(e, dict) and one_key(e)[0] == 'rest')]
            if rest_idx:
                r = rest_idx[0]
                before, after = elems[:r], elems[r + 1:]
                pats = before + [None] * (len(vfields) - len(before) - len(after)) + after
            else:
                pats = elems
                if len(pats) != len(vfields):
                    raise Refusal('variant-pattern-arity', f'{"::".join(path)}: {len(pats)} vs {len(vfields)}')
            for p, n, (fname, t) in zip(pats, names, vfields):
                if p is not None:
                    sub.append((p, n, t))
        head = f'MR_{a.name}.{vname}' + ''.join(' ' + n for n in names)

        def go(i, env2):
            if i == len(sub):
                return on_ok(env2)
            p, n, t = sub[i]
            return self.lower_pat(p, n, t, env2, lambda env3: go(i + 1, env3), on_fail)
        tail = f' | _ => {on_fail()}' if nvariants > 1 else ''
        return f'(match {atom} with | {head} => {go(0, env)}{tail})'

    # ================================================================== expressions
    def lower_expr(self, e, env, exp, k):
        ek, ev = one_key(e)
        m = getattr(self, 'x_' + ek, None)
        if m is None:
            raise Refusal('expression-kind', ek)
        return m(ev, env, exp, k)

    def lower_exprs(self, es, env, exps, k):
        es = list(es)

        def go(i, atoms, tys, env2):
            if i == len(es):
                return k(atoms, tys, env2)
            return self.lower_expr(es[i], env2, exps[i] if exps else None,
                                   lambda a, t, env3: go(i + 1, atoms + [a], tys + [t], env3))
        return go(0, [], [], env)

    def x_paren(self, v, env, exp, k):
        return self.lower_expr(v['expr'], env, exp, k)

    def x_group(self, v, env, exp, k):
        return self.lower_expr(v['expr'], env, exp, k)

    def x_reference(self, v, env, exp, k):
        return self.lower_expr(v['expr'], env, exp, k)

    def x_lit(self, v, env, exp, k):
        kind, val = lit_value(v)
        self.note('expr:literal')
        if kind == 'int':
            return k(lean_int(val), INT, env)
        if kind == 'bool':
            return k('true' if val else 'false', BOOL, env)
        if kind == 'str':
            return k(lean_string(val), STR, env)
        raise Refusal('literal', kind)

    def x_block(self, v, env, exp, k):
        self.note('expr:block')
        return self.lower_block(v['stmts'], env.copy(), exp,
                                lambda a, t, env2: k(a, t, restore_scope(env, env2)))

    def x_tuple(self, v, env, exp, k):
        elems = v.get('elems', [])
        if not elems:
            return k('()', UNIT, env)
        self.note('expr:tuple')
        exps = list(exp[1]) if exp and exp[0] == 'tuple' and len(exp[1]) == len(elems) else None
        return self.lower_exprs(elems, env, exps,
                                lambda atoms, tys, env2: k('(' + ', '.join(atoms) + ')', tuple_ty(tys), env2))

    # ------------------------------------------------------------------ paths
    def x_path(self, v, env, exp, k):
        if v.get('qself'):
            raise Refusal('qualified-self-path', '')
        ids = [s['ident'] for s in v['segments']]
        if len(ids) == 1:
            n = ids[0]
            if n in env.vars:
                self.note('expr:variable')
                full_caps = [x for x in env.vars if x.startswith(n + '.') and env.vars[x].mutable]
                if full_caps:
                    raise Refusal('closure-reads-prefix-of-captured-place', f'{n} / {full_caps}')
                var = env.vars[n]
                return k(var.lean, var.ty, env)
            if n == 'None':
                if not exp or exp[0] != 'option':
                    raise Refusal('None-without-expected-type', '')
                self.note('expr:option-constructor')
                return k(f'(none : {lean_type(exp)})', exp, env)
            if n == 'PhantomData':
                return k('()', UNIT, env)
            uv = self.variant_value(ids, exp, env)
            if uv is not None:
                return k(uv[0], uv[1], env)
            raise Refusal('unknown-name', n)
        if ids[-1] == 'PhantomData':
            return k('()', UNIT, env)
        c = self.const_value(ids, env)
        if c is not None:
            return self.use_const(c, env, k)
        uv = self.variant_value(ids, exp, env)
        if uv is not None:
            return k(uv[0], uv[1], env)
        raise Refusal('path-expression', '::'.join(ids))

    def variant_value(self, ids, exp, env):
        name = ids[-1]
        if ids[-2:] == ['Ordering', name] and name in ('Less', 'Equal', 'Greater'):
            return ({'Less': 'SOrdering.less', 'Equal': 'SOrdering.equal', 'Greater': 'SOrdering.greater'}[name], ORDERING)
        cands = []
        if len(ids) >= 2:
            owner = env.aliases.get(ids[-2], ids[-2])
            if owner == 'Self' and self.cur_fn is not None:
                owner = self.cur_fn.owner
            if owner in self.prog.adts:
                cands = [owner]
        else:
            if exp and exp[0] == 'adt' and self.adt(exp[1]).kind == 'enum' and any(vn == name for vn, _, _ in self.adt(exp[1]).variants):
                cands = [exp[1]]
            elif name in env.globs:
                cands = env.globs[name][:1]
            else:
                cands = [a for a in ('Signedness', 'Mutability', 'Endianness') if any(vn == name for vn, _, _ in self.adt(a).variants)]
        for c in cands:
            a = self.adt(c)
            if a.kind != 'enum':
                continue
            for vn, style, fs in a.variants:
                if vn == name and style == 'unit':
                    self.note('expr:unit-variant')
                    return (f'MR_{c}.{vn}', adt(c))
        return None

    def const_value(self, ids, env):
        name, owner = ids[-1], ids[-2]
        lib = {
            ('Size', 'ZERO'): ('(0 : Int)', SIZE), ('Offset', 'ZERO'): ('(0 : Int)', SIZE),
            ('Align', 'ONE'): ('(1 : Int)', ALIGN), ('Int', 'ZERO'): ('(0 : Int)', INT),
            ('Int', 'ONE'): ('(1 : Int)', INT), ('ThreadId', 'ZERO'): ('(0 : Int)', INT),
        }
        if (owner, name) in lib:
            self.note('expr:library-constant')
            return ('pure',) + lib[(owner, name)]
        cfg = self.prog.config['monomorphization']
        target_owner = None
        if owner == 'T' or (len(ids) == 3 and ids[1] == 'T'):
            target_owner = cfg['bound']['Target'][1]
        elif owner == 'Self' and self.cur_fn is not None:
            target_owner = self.cur_fn.owner
        elif owner in self.prog.adts:
            target_owner = owner
        if target_owner:
            c = self.prog.find_const(target_owner, name)
            if c is not None:
                return ('const', c)
        return None

    def use_const(self, c, env, k):
        if c[0] == 'pure':
            return k(c[1], c[2], env)
        cd = c[1]
        ty = resolve(self.prog, cd.ty_json, cd.generics, cd.owner)
        self.note('expr:spec-constant')
        return self.bind_simple(f'{cd.lean_name} {self.fuel}', ty, env, k, 'k')

    # ------------------------------------------------------------------ operators
    def x_unary(self, v, env, exp, k):
        op = v['op']
        if op == '*':
            self.note('expr:deref')
            return self.lower_expr(v['expr'], env, exp, k)

        def after(a, t, env2):
            if op == '!':
                self.note('expr:not')
                if t == BOOL:
                    return k(f'(SBool.not {a})', BOOL, env2)
                if t == INT:
                    return k(f'(SInt.bnot {a})', INT, env2)
            if op == '-' and t == INT:
                self.note('expr:neg')
                return k(f'((0 : Int) - {a})', INT, env2)
            raise Refusal('unary-operator', f'{op} on {show_ty(t)}')
        return self.lower_expr(v['expr'], env, exp, after)

    def x_binary(self, v, env, exp, k):
        op = v['op']
        if op in ('&&', '||'):
            self.note('expr:short-circuit')

            def after_left(a, t, env2):
                pre, jump = self.join(env2, BOOL, k, [v['right']])
                right = self.lower_expr(v['right'], env2, BOOL, lambda b, tb, env3: jump(b, env3))
                if op == '&&':
                    body = f'(match {a} with | true => {right} | false => {jump("false", env2)})'
                else:
                    body = f'(match {a} with | true => {jump("true", env2)} | false => {right})'
                return pre() + body
            return self.lower_expr(v['left'], env, BOOL, after_left)
        if op.endswith('=') and op not in ('==', '!=', '<=', '>='):
            return self.compound_assign(v, env, k)
        return self.lower_expr(v['left'], env, None, lambda a, ta, env2:
                               self.lower_expr(v['right'], env2, ta if op in ('==', '!=') and ta != NEVER else None,
                                               lambda b, tb, env3: self.binop(op, a, ta, b, tb, env3, k)))

    def binop(self, op, a, ta, b, tb, env, k):
        if op in ('==', '!='):
            return self.equality(op, a, ta, b, tb, env, k)
        if op in ('<', '<=', '>', '>='):
            self.note('expr:comparison')
            if is_intlike(ta) and is_intlike(tb):
                txt = {'<': f'(SInt.blt {a} {b})', '<=': f'(SInt.ble {a} {b})',
                       '>': f'(SInt.blt {b} {a})', '>=': f'(SInt.ble {b} {a})'}[op]
                return k(txt, BOOL, env)
            raise Refusal('comparison-on', f'{show_ty(ta)} {op} {show_ty(tb)}')
        if op in ('+', '-', '*'):
            self.note('expr:arith')
            if ta == INT and tb == INT:
                return k(f'({a} {op} {b})', INT, env)
            if op == '+' and ta == SIZE and tb == SIZE:
                return self.bind_simple(f'SSize.add {a} {b}', SIZE, env, k)
            if op == '*' and ta == SIZE and tb == INT:
                return self.bind_simple(f'SSize.mul {a} {b}', SIZE, env, k)
            if op == '*' and ta == INT and tb == SIZE:
                return self.bind_simple(f'SSize.mul {b} {a}', SIZE, env, k)
            raise Refusal('arithmetic-on', f'{show_ty(ta)} {op} {show_ty(tb)}')
        if op in ('/', '%'):
            self.note('expr:div-rem')
            if ta == INT and tb == INT:
                return self.bind_simple(f'SInt.{"div" if op == "/" else "rem"} {a} {b}', INT, env, k)
            raise Refusal('division-on', f'{show_ty(ta)} {op} {show_ty(tb)}')
        if op in ('&', '|', '^'):
            self.note('expr:bitwise')
            if ta == INT and tb == INT:
                return k(f'(SInt.{ {"&": "band", "|": "bor", "^": "bxor"}[op]} {a} {b})', INT, env)
            if ta == BOOL and tb == BOOL:
                return k(f'(SBool.{ {"&": "and", "|": "or", "^": "xor"}[op]} {a} {b})', BOOL, env)
            raise Refusal('bitwise-on', f'{show_ty(ta)} {op} {show_ty(tb)}')
        if op in ('<<', '>>'):
            self.note('expr:shift')
            if ta == INT and tb == INT:
                return self.bind_simple(f'SInt.{"shl" if op == "<<" else "shr"} {a} {b}', INT, env, k)
            raise Refusal('shift-on', f'{show_ty(ta)} {op} {show_ty(tb)}')
        raise Refusal('binary-operator', op)

    def equality(self, op, a, ta, b, tb, env, k):
        self.note('expr:equality')
        t = ta if ta != NEVER else tb
        if is_intlike(ta) and is_intlike(tb):
            t = INT
        neg = op == '!='
        if not self.tinfo.ty_eq_monadic(t):
            txt = f'({self.tinfo.eq_pure(t)} {a} {b})'
            return k(f'(SBool.not {txt})' if neg else txt, BOOL, env)
        n = fresh('eq')
        return f'SOut.bind (α := Bool) (β := {env.fn.inner_ty(env)}) ({self.tinfo.eq_monadic(t, self.fuel)} {a} {b}) (fun ({n} : Bool) => {k(f"(SBool.not {n})" if neg else n, BOOL, env)})'

    def compound_assign(self, v, env, k):
        op = v['op'][:-1]
        place = self.place_of(v['left'], env)
        if place is None:
            raise Refusal('compound-assignment-target', '')
        self.note('expr:compound-assign')

        def after(b, tb, env2):
            cur, cty = self.read_place(place, env2)

            def write(nv, nt, env3):
                pre, env4 = self.write_place(place, nv, env3)
                return pre + k('()', UNIT, env4)
            return self.binop(op, cur, cty, b, tb, env2, write)
        return self.lower_expr(v['right'], env, place[2], after)

    def x_assign(self, v, env, exp, k):
        place = self.place_of(v['left'], env)
        if place is None:
            raise Refusal('assignment-target', str(v['left'])[:80])
        self.note('expr:assign')

        def after(a, t, env2):
            pre, env3 = self.write_place(place, a, env2)
            return pre + k('()', UNIT, env3)
        return self.lower_expr(v['right'], env, place[2], after)

    # ------------------------------------------------------------------ fields / index / range
    def x_field(self, v, env, exp, k):
        fname = member_name(v)
        place = self.place_of({'field': v}, env)
        if place is not None:
            self.note('expr:field')
            atom, ty = self.read_place(place, env)
            return k(atom, ty, env)

        def after(a, t, env2):
            self.note('expr:field')
            atom, ty = self.project(a, t, fname)
            return k(atom, ty, env2)
        return self.lower_expr(v['base'], env, None, after)

    def x_index(self, v, env, exp, k):
        self.note('expr:index')

        def after(atoms, tys, env2):
            (a, i), (ta, ti) = atoms, tys
            if ta[0] == 'list':
                return self.bind_simple(f'SList.index_at {a} {i}', ta[1], env2, k)
            if ta[0] == 'map':
                return self.bind_simple(f'SMap.index_at {self.tinfo.eq_pure(ta[1])} {a} {i}', ta[2], env2, k)
            raise Refusal('index-on', show_ty(ta))
        return self.lower_exprs([v['expr'], v['index']], env, None, after)

    def x_range(self, v, env, exp, k):
        if not v.get('start') or not v.get('end'):
            raise Refusal('open-range', '')
        if v.get('limits') not in (None, '..', 'half_open', 'HalfOpen'):
            raise Refusal('closed-range', str(v.get('limits')))
        self.note('expr:range')
        return self.lower_exprs([v['start'], v['end']], env, [INT, INT],
                                lambda atoms, tys, env2: k(f'(SList.range {atoms[0]} {atoms[1]})', ('iter', INT), env2))

    # ------------------------------------------------------------------ struct literals
    def x_struct(self, v, env, exp, k):
        path = path_idents(v['path'])
        name = env.aliases.get(path[-1], path[-1])
        if path[-1] == 'IntDistribution':
            fields = {member_name(f): f['expr'] for f in v['fields']}
            self.note('expr:struct-literal')
            return self.lower_exprs([fields['start'], fields['end'], fields['divisor']], env, [INT, INT, INT],
                                    lambda atoms, tys, env2: k('(SIntDistribution.mk ' + ' '.join(atoms) + ')', DISTR, env2))
        owner = vfields = ctor = None
        if len(path) >= 2:
            o = env.aliases.get(path[-2], path[-2])
            if o == 'Self' and self.cur_fn is not None:
                o = self.cur_fn.owner
            if o in self.prog.adts and self.adt(o).kind == 'enum':
                for vn, style, fs in self.adt(o).variants:
                    if vn == name:
                        owner, vfields, ctor = o, fs, f'MR_{o}.{vn}'
        if vfields is None:
            if name == 'Self' and self.cur_fn is not None:
                owner = self.cur_fn.owner
                vfields, ctor = self.adt(owner).fields, f'MR_{owner}.mk'
            elif name in self.prog.adts and self.adt(name).kind == 'struct':
                owner, vfields, ctor = name, self.adt(name).fields, f'MR_{name}.mk'
            elif len(path) == 1 and name in env.globs:
                o = env.globs[name][0]
                for vn, style, fs in self.adt(o).variants:
                    if vn == name:
                        owner, vfields, ctor = o, fs, f'MR_{o}.{vn}'
        if vfields is None:
            raise Refusal('struct-literal', '::'.join(path))
        self.note('expr:struct-literal')
        given = {member_name(f): f['expr'] for f in v.get('fields', [])}
        order = [fn for fn, _ in vfields]
        for fn in given:
            if fn not in order:
                raise Refusal('struct-literal-field', f'{name}.{fn}')
        present = [fn for fn in order if fn in given]
        exps = [t for fn, t in vfields if fn in given]
        rest = v.get('rest')

        def after(atoms, tys, env2):
            vals = dict(zip(present, atoms))

            def finish(base_atom, env3):
                args = []
                for fn, t in vfields:
                    if fn in vals:
                        args.append(vals[fn])
                    elif base_atom is not None:
                        args.append(f'(MR_{owner}.{field_proj_name(fn)} {base_atom})')
                    else:
                        raise Refusal('struct-literal-missing-field', f'{name}.{fn}')
                return k(f'({ctor}' + ''.join(' ' + x for x in args) + ')', adt(owner), env3)
            if rest is not None:
                self.note('expr:struct-update-syntax')

                def with_base(b, tb, env3):
                    pre, ba = self.let_atom(b, tb, 'base')
                    return pre + finish(ba, env3)
                return self.lower_expr(rest, env2, adt(owner), with_base)
            return finish(None, env2)
        return self.lower_exprs([given[fn] for fn in present], env, exps, after)

    # ------------------------------------------------------------------ branching
    def branch_type(self, kind, node, env, exp):
        """Type of an `if`/`match` value, found by lowering it once with a probe
        continuation whose text is discarded."""
        if exp is not None:
            return exp
        key = (id(node), tuple(sorted((n, vv.ty) for n, vv in env.vars.items())))
        if key in self._probe_cache:
            return self._probe_cache[key]
        found = []
        saved_census = dict(self.census)
        saved_ref = list(self.refusals)

        def probe_k(a, t, env2):
            if t != NEVER:
                found.append(t)
            return 'SOut.panic "probe"'
        try:
            getattr(self, 'x_' + kind)(node, env, None, probe_k, probing=True)
        finally:
            self.census.clear()
            self.census.update(saved_census)
            self.refusals[:] = saved_ref
        ty = found[0] if found else NEVER
        self._probe_cache[key] = ty
        return ty

    def x_if(self, v, env, exp, k, probing=False):
        cond = v['cond']
        then_b = v['then_branch']
        else_b = v.get('else_branch')
        touched = [cond, then_b] + ([else_b] if else_b else [])
        if probing:
            pre = lambda: ''
            branch_k = k
        else:
            jty = self.branch_type('if', v, env, exp)
            pre, jumpf = self.join(env, jty if jty != NEVER else UNIT, k, touched)
            if exp is None and jty != NEVER:
                exp = jty

            def branch_k(a, t, env2):
                return jumpf(a, env2)

        def then_part(env1):
            try:
                return self.lower_block(then_b, env1.copy(), exp,
                                        lambda a, t, env2: branch_k(a, t, restore_scope(env1, env2)))
            except Refusal:
                if probing:
                    return 'probe'
                raise

        def else_part(env1):
            if else_b is None:
                return branch_k('()', UNIT, env1)
            try:
                return self.lower_expr(else_b, env1, exp, lambda a, t, env2: branch_k(a, t, restore_scope(env1, env2)))
            except Refusal:
                if probing:
                    return 'probe'
                raise

        if self.is_let_chain(cond):
            self.note('expr:if-let')
            conds = self.flatten_let_chain(cond)
            fail_jp = fresh('els')
            # the else branch sees the state the conditions left behind
            names = set()
            mentions([cond, else_b], names)
            estate = sorted(n for n, vv in env.vars.items() if vv.mutable and root_of(n) in names)
            eparams = [(fresh(n.replace('.', '_').replace('#', '_')), env.vars[n].ty) for n in estate]
            env_e = env
            for (pn, _), n in zip(eparams, estate):
                env_e = env_e.set(n, pn)
            binders = ''.join(f' ({pn} : {lean_type(pt)})' for pn, pt in eparams)
            ety = arrow_type([UNIT] + [pt for _, pt in eparams], env.fn.term_ty(env))
            else_text = else_part(env_e)

            def on_fail(env_at):
                return f'{fail_jp} ()' + ''.join(' ' + env_at.vars[n].lean for n in estate)
            body = self.lower_conds(conds, 0, env, then_part, on_fail)
            prefix = f'let {fail_jp} : {ety} := (fun (_ : Unit){binders} => {else_text}); '
            return pre() + prefix + body
        self.note('expr:if')
        body = self.lower_expr(cond, env, BOOL, lambda c, t, env2:
                               f'(match {c} with | true => {then_part(env2)} | false => {else_part(env2)})')
        return (pre() if callable(pre) else pre) + body

    def is_let_chain(self, cond):
        ck, cv = one_key(cond)
        if ck == 'let':
            return True
        if ck == 'binary' and cv['op'] == '&&':
            return self.is_let_chain(cv['left']) or self.is_let_chain(cv['right'])
        return False

    def flatten_let_chain(self, cond):
        ck, cv = one_key(cond)
        if ck == 'binary' and cv['op'] == '&&' and self.is_let_chain(cond):
            return self.flatten_let_chain(cv['left']) + self.flatten_let_chain(cv['right'])
        return [cond]

    def lower_conds(self, conds, i, env, on_ok, on_fail):
        if i == len(conds):
            return on_ok(env)
        ck, cv = one_key(conds[i])
        if ck == 'let':
            return self.lower_expr(cv['expr'], env, None, lambda a, t, env2:
                                   self.lower_pat(cv['pat'], a, t, env2,
                                                  lambda env3: self.lower_conds(conds, i + 1, env3, on_ok, on_fail),
                                                  lambda: on_fail(env2)))
        return self.lower_expr(conds[i], env, BOOL, lambda c, t, env2:
                               f'(match {c} with | true => {self.lower_conds(conds, i + 1, env2, on_ok, on_fail)} | false => {on_fail(env2)})')

    def x_match(self, v, env, exp, k, probing=False):
        arms = v['arms']
        argmatch = v.get('argmatch_arms')
        self.note('expr:match')
        if probing:
            branch_k = k
            pre = lambda: ''
        else:
            jty = self.branch_type('match', v, env, exp)
            touched = [v['expr']] + [a['body'] for a in arms] + [a['guard'] for a in arms if a.get('guard')]
            pre, jumpf = self.join(env, jty if jty != NEVER else UNIT, k, touched)
            if exp is None and jty != NEVER:
                exp = jty

            def branch_k(a, t, env2):
                return jumpf(a, env2)

        def after(s, sty, env2):
            spre, sa = self.let_atom(s, sty, 'scrut')

            def arm(i):
                if i == len(arms):
                    return self.panic(env2, 'no match arm applies')
                a = arms[i]
                fail_name = fresh('next')
                fail_used = [False]

                def fail():
                    fail_used[0] = True
                    return f'{fail_name} ()'

                def on_ok(env3):
                    def body(env4):
                        try:
                            return self.lower_expr(a['body'], env4, exp, lambda r, t, env5: branch_k(r, t, restore_scope(env2, env5)))
                        except Refusal:
                            if probing:
                                return 'probe'
                            raise
                    if a.get('guard'):
                        g = a['guard']
                        if isinstance(g, list):
                            g = g[1]
                        return self.lower_expr(g, env3, BOOL, lambda c, t, env4: f'(match {c} with | true => {body(env4)} | false => {fail()})')
                    return body(env3)
                if argmatch and not probing:
                    try:
                        text = self.lower_pat(a['pat'], sa, sty, env2, on_ok, fail)
                        self.arm_outcomes.append((self.cur_fn.display, i, None))
                    except Refusal as r:
                        self.arm_outcomes.append((self.cur_fn.display, i, r))
                        text = self.lower_pat(a['pat'], sa, sty, env2,
                                              lambda env3: f'SOut.refused {lean_string(r.construct + " in " + self.cur_fn.display + " arm " + str(i))}',
                                              fail)
                else:
                    text = self.lower_pat(a['pat'], sa, sty, env2, on_ok, fail)
                if not fail_used[0]:
                    return text
                return f'let {fail_name} : Unit → {env2.fn.term_ty(env2)} := (fun (_ : Unit) => {arm(i + 1)}); {text}'
            return spre + arm(0)
        body = self.lower_expr(v['expr'], env, None, after)
        return pre() + body

    # ------------------------------------------------------------------ try / return
    def x_try(self, v, env, exp, k):
        self.note('expr:question-mark')

        def after(a, t, env2):
            if t[0] == 'nondet':
                self.note('expr:question-mark-on-nondet')
                return k(a, t[1], env2)   # a prediction, resolved by the interpretation
            if t[0] == 'result':
                x, e = fresh('ok'), fresh('err')
                rt = env2.fn.ret_ty
                if t[2] == NEVER:
                    # `f()?` where f returns `NdResult<!>`: the Ok branch cannot occur
                    self.note('expr:question-mark-on-never')
                    if rt[0] != 'result':
                        raise Refusal('question-mark-on-result-in-non-result-context', show_ty(rt))
                    early = env2.fn.ret(f'(SRes.err {e} : {lean_type(rt)})', env2)
                    return (f'(match {a} with | SRes.ok _ => {self.panic(env2, "value of the never type")} '
                            f'| SRes.err {e} => {early})')
                if rt == ('var', '?'):
                    raise Refusal('closure-return-type-inference-through-question-mark', '')
                if rt[0] != 'result':
                    raise Refusal('question-mark-on-result-in-non-result-context', show_ty(rt))
                early = env2.fn.ret(f'(SRes.err {e} : {lean_type(rt)})', env2)
                return f'(match {a} with | SRes.ok {x} => {k(x, t[2], env2)} | SRes.err {e} => {early})'
            if t[0] == 'option':
                x = fresh('some')
                rt = env2.fn.ret_ty
                if rt[0] != 'option':
                    raise Refusal('question-mark-on-option-in-non-option-context', show_ty(rt))
                early = env2.fn.ret(f'(none : {lean_type(rt)})', env2)
                return f'(match {a} with | some {x} => {k(x, t[1], env2)} | none => {early})'
            return k(a, t, env2)   # Nondet<T>: resolved by the oracle
        return self.lower_expr(v['expr'], env, None, after)

    def x_return(self, v, env, exp, k):
        self.note('expr:return')
        if v.get('expr') is None:
            return env.fn.ret('()', env)
        return self.lower_expr(v['expr'], env, env.fn.ret_ty, lambda a, t, env2: env2.fn.ret(a, env2))

    # ------------------------------------------------------------------ loops
    def x_for_loop(self, v, env, exp, k):
        self.note('stmt:for-loop')
        if v.get('label'):
            raise Refusal('labelled-loop', '')

        def after(xs, t, env2):
            if t[0] in ('list', 'set', 'iter'):
                elem = t[1]
            elif t[0] == 'map':
                elem = ('tuple', (t[1], t[2]))
            else:
                raise Refusal('for-loop-over', show_ty(t))
            return self.loop_common(env2, [v['body'], v['pat']], k, v['body'], items=(xs, v['pat'], elem))
        return self.lower_expr(v['expr'], env, None, after)

    def x_while(self, v, env, exp, k):
        self.note('stmt:while-loop')
        if v.get('label'):
            raise Refusal('labelled-loop', '')
        return self.loop_common(env, [v['body'], v['cond']], k, v['body'], cond=v['cond'])

    def loop_common(self, env, nodes, k, body_stmts, items=None, cond=None):
        names = set()
        for n in nodes:
            mentions(n, names)
        state = sorted(n for n, vv in env.vars.items() if vv.mutable and root_of(n) in names)
        state_ty = tuple_ty([env.vars[n].ty for n in state])
        ctl_ty = f'(SCtl {lean_type(state_ty, "arg")} {lean_type(env.fn.payload_ty(env), "arg")})'
        st = fresh('st')
        st_names = [fresh(n.replace('.', '_').replace('#', '_')) for n in state]
        env_in = env.copy()
        for n, sn in zip(state, st_names):
            env_in = env_in.set(n, sn)
        env_in.fn = LoopFnCtx(env.fn)
        env_in.fn.ctl_ty = ctl_ty
        env_in.loop = LoopCtx(state, ctl_ty)
        lp = env_in.loop

        def cont(env_b):
            return f'SOut.ok (SCtl.next {lp.state(env_b)} : {ctl_ty})'

        def body_text(env_b):
            return self.lower_block(body_stmts, env_b.copy(), UNIT, lambda a, t, env_c: cont(restore_scope(env_b, env_c)))

        st_pat = tuple_text(st_names)
        if items is not None:
            xs, pat, elem_ty = items
            x = fresh('item')
            inner = self.lower_pat(pat, x, elem_ty, env_in, body_text, lambda: self.panic(env_in, 'for-loop pattern failed'))
            loop_text = (f'SLoop.forS (α := {lean_type(elem_ty, "arg")}) (σ := {lean_type(state_ty, "arg")}) (ρ := {lean_type(env.fn.payload_ty(env), "arg")}) {xs} {lp.state(env)} (fun ({x} : {lean_type(elem_ty)}) ({st} : {lean_type(state_ty)}) => '
                         + (f'match {st} with | {st_pat} => {inner})' if state else f'{inner})'))
        else:
            def brk(env_b):
                return f'SOut.ok (SCtl.brk {lp.state(env_b)} : {ctl_ty})'
            ck, cv = one_key(cond)
            if ck == 'let':
                inner = self.lower_expr(cv['expr'], env_in, None, lambda a, t, env2:
                                        self.lower_pat(cv['pat'], a, t, env2, body_text, lambda: brk(env2)))
            else:
                inner = self.lower_expr(cond, env_in, BOOL, lambda c, t, env2:
                                        f'(match {c} with | true => {body_text(env2)} | false => {brk(env2)})')
            loop_text = (f'SLoop.whileS (σ := {lean_type(state_ty, "arg")}) (ρ := {lean_type(env.fn.payload_ty(env), "arg")}) {self.fuel} {lp.state(env)} (fun ({st} : {lean_type(state_ty)}) => '
                         + (f'match {st} with | {st_pat} => {inner})' if state else f'{inner})'))
        c = fresh('ctl')
        after_names = [fresh(n.replace('.', '_').replace('#', '_')) for n in state]
        env_after = env
        for n, an in zip(state, after_names):
            env_after = env_after.set(n, an)
        rest = k('()', UNIT, env_after)
        s2, r = fresh('st'), fresh('ret')
        rj = fresh('rest')
        after_pat = tuple_text(after_names)
        rest_body = f'match {s2} with | {after_pat} => {rest}' if state else rest
        return (f'let {rj} : {arrow_type([state_ty], env.fn.term_ty(env))} := (fun ({s2} : {lean_type(state_ty)}) => {rest_body}); '
                f'SOut.bind (α := {ctl_ty}) (β := {env.fn.inner_ty(env)}) ({loop_text}) (fun ({c} : {ctl_ty}) => match {c} with '
                f'| SCtl.next {s2} => {rj} {s2} | SCtl.brk {s2} => {rj} {s2} | SCtl.ret {r} => {env.fn.ret_raw(r)})')

    def x_break(self, v, env, exp, k):
        if env.loop is None or v.get('expr') or v.get('label'):
            raise Refusal('break-with-value-or-label', '')
        self.note('expr:break')
        return f'SOut.ok (SCtl.brk {env.loop.state(env)} : {env.loop.ctl_ty_text})'

    def x_continue(self, v, env, exp, k):
        if env.loop is None or v.get('label'):
            raise Refusal('labelled-continue', '')
        self.note('expr:continue')
        return f'SOut.ok (SCtl.next {env.loop.state(env)} : {env.loop.ctl_ty_text})'

    # ------------------------------------------------------------------ closures
    def x_closure(self, v, env, exp, k):
        if exp is None or exp[0] != 'fn':
            params = []
            for inp in v.get('inputs', []):
                ik, iv = one_key(inp) if isinstance(inp, dict) else (inp, None)
                if ik != 'type':
                    raise Refusal('closure-bound-to-local-without-parameter-types', '')
                params.append((self.rt(iv['ty']), False))
            exp = ('fn', tuple(params), None, None)
        text, sigma, captured, ret = self.lower_closure(v, env, exp)
        if captured:
            raise Refusal('closure-value-with-mutable-capture', ', '.join(captured))
        self.note('expr:closure-value')
        return k(text, ('fn', exp[1], ret, UNIT), env)

    def lower_closure(self, cl, env, fn_ty):
        """Lower a closure literal against an `impl Fn*` type. Returns
        (lambda text, sigma type, captured env names, return type)."""
        self.note('expr:closure')
        params, ret = fn_ty[1], fn_ty[2]
        if len(cl.get('inputs', [])) != len(params):
            raise Refusal('closure-arity', f'{len(cl.get("inputs", []))} vs {len(params)}')
        if cl.get('output'):
            ret = self.rt(cl['output'])
        saved_census = dict(self.census)
        saved_ref = list(self.refusals)
        log = set()
        try:
            if ret is None or has_var(ret):
                # the closure's return type is that of its body
                found = []
                self._closure_text(cl, env, params, ret, [], log, found)
                ret = next((t for t in found if t != NEVER), None)
                if ret is None:
                    raise Refusal('closure-return-type-unknown', '')
                log = set()
            self._closure_text(cl, env, params, ret, [], log)
        finally:
            self.census.clear()
            self.census.update(saved_census)
            self.refusals[:] = saved_ref
        captured = sorted(log)
        captured = [c for c in captured if not any(c != d and c.startswith(d + '.') for d in captured)]
        text, sigma = self._closure_text(cl, env, params, ret, captured, None)
        return text, sigma, captured, ret

    def _closure_text(self, cl, env, params, ret, captured, log, found=None):
        inner = env.copy()
        inner.loop = None
        inner.outer = {n: v.id for n, v in env.vars.items()}
        names = []
        mut_outputs = []
        pat_binds = []
        for i, ((pty, is_mut), inp) in enumerate(zip(params, cl['inputs'])):
            pk, pv = one_key(inp) if isinstance(inp, dict) else (inp, None)
            if pk == 'type':
                inp = pv['pat']
                pk, pv = one_key(inp) if isinstance(inp, dict) else (inp, None)
            n = fresh('a')
            names.append((n, pty))
            if pk == 'ident' and not pv.get('subpat'):
                inner = inner.bind(pv['ident'], n, pty, mutable=bool(is_mut or pv.get('mut')))
                if is_mut:
                    mut_outputs.append(pv['ident'])
            else:
                syn = f'#arg{i}'
                inner = inner.bind(syn, n, pty, mutable=bool(is_mut))
                if is_mut:
                    mut_outputs.append(syn)
                if pk not in ('wild', '_'):
                    pat_binds.append((inp, n, pty))
                else:
                    self.note('pattern:wildcard')
        cap_names = []
        for c in captured:
            cn = fresh(c.replace('.', '_').replace('#', '_'))
            cap_names.append(cn)
            inner = inner.bind(c, cn, self.place_type(c, env), mutable=True)
        sigma = tuple_ty([self.place_type(c, env) for c in captured])
        inner.fn = FnCtx(ret if ret is not None else ('var', '?'), mut_outputs, closure_sigma=captured, capture_log=log)

        def body_k(a, t, env3):
            if found is not None:
                found.append(t)
                return 'SOut.panic "probe"'
            return env3.fn.ret(a, env3)

        def with_pats(i, env2):
            if i == len(pat_binds):
                return self.lower_expr(cl['body'], env2, ret, body_k)
            p, n, t = pat_binds[i]
            return self.lower_pat(p, n, t, env2, lambda env3: with_pats(i + 1, env3), lambda: self.panic(env2, 'closure parameter pattern failed'))
        body = with_pats(0, inner)
        st = fresh('st')
        binders = ' '.join(f'({n} : {lean_type(t)})' for n, t in names)
        if cap_names:
            text = f'(fun {binders} ({st} : {lean_type(sigma)}) => match {st} with | {tuple_text(cap_names)} => {body})'
        else:
            text = f'(fun {binders} ({st} : {lean_type(sigma)}) => {body})'
        return text, sigma

    def place_type(self, key, env):
        if key in env.vars:
            return env.vars[key].ty
        root, *path = key.split('.')
        name, rest = self.resolve_place_var((root, path), env)
        ty = env.vars[name].ty
        for f in rest:
            ty = self.field_ty(ty, f)
        return ty

    # ------------------------------------------------------------------ calls
    def x_call(self, v, env, exp, k):
        from calls import lower_call
        return lower_call(self, v, env, exp, k)

    def x_method_call(self, v, env, exp, k):
        from calls import lower_method_call
        return lower_method_call(self, v, env, exp, k)

    def x_let(self, v, env, exp, k):
        raise Refusal('let-expression-outside-condition', '')

    def x_macro(self, v, env, exp, k):
        raise Refusal('unexpanded-macro', '')

    def x_cast(self, v, env, exp, k):
        raise Refusal('as-cast', '')

    def x_array(self, v, env, exp, k):
        raise Refusal('array-literal', '')

    def x_loop(self, v, env, exp, k):
        raise Refusal('loop-expression', '')
