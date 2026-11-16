"""Function calls, method calls, prelude macros and the libspecr library surface."""

from common import *
from tyres import resolve, param_ref_kind, ty_children
from lower import (FnCtx, Env, is_simple_atom, tuple_text, ident_of_path_expr, strip_parens,
                   member_name, restore_scope, has_var, exp_or_none)


# ---------------------------------------------------------------------------
# signatures of translated functions

class Param:
    def __init__(self, src, pat, ty, ref, is_self, mut_kw):
        self.src, self.pat, self.ty, self.ref, self.is_self, self.mut_kw = src, pat, ty, ref, is_self, mut_kw

    @property
    def is_fn(self):
        return self.ty[0] == 'fn'


class Sig:
    def __init__(self, fd, params, ret_ty, polys):
        self.fd = fd
        self.params = params
        self.ret_ty = ret_ty
        self.polys = polys          # type variable names bound implicitly

    @property
    def self_param(self):
        return self.params[0] if self.params and self.params[0].is_self else None

    def outputs(self):
        """(param, kind) for each component of the result after the value."""
        out = []
        for p in self.params:
            if p.ref == 'mut':
                out.append((p, 'value'))
        for p in self.params:
            if p.is_fn:
                out.append((p, 'state'))
        return out


def substitute(t, sub):
    if t is None:
        return None
    if t[0] == 'var':
        return sub.get(t[1], t)
    k = t[0]
    if k == 'tuple':
        return ('tuple', tuple(substitute(x, sub) for x in t[1]))
    if k in ('list', 'set', 'option', 'iter'):
        return (k, substitute(t[1], sub))
    if k in ('map', 'result'):
        return (k, substitute(t[1], sub), substitute(t[2], sub))
    if k == 'fn':
        return ('fn', tuple((substitute(p, sub), m) for p, m in t[1]), substitute(t[2], sub),
                substitute(t[3], sub) if t[3] is not None else None)
    return t


def signature(L, fd):
    if getattr(fd, '_sig', None) is not None:
        return fd._sig
    prog = L.prog
    g = fd.generics
    params = []
    polys = [b[1] for b in g.values() if b[0] == 'poly']
    for i, inp in enumerate(fd.inputs):
        ik, iv = one_key(inp)
        if ik == 'receiver':
            ref = 'mut' if (iv.get('ref') and iv.get('mut')) else ('ref' if iv.get('ref') else None)
            params.append(Param('self', None, adt(fd.owner), ref, True, bool(iv.get('mut')) and not iv.get('ref')))
            continue
        pat = iv['pat']
        ty_json = iv['ty']
        ref = param_ref_kind(ty_json)
        ty = resolve(prog, ty_json, g, fd.owner)
        pk, pv = one_key(pat)
        # `Type::Bool: Self` style argmatch arms keep the pattern; the merged
        # declaration binds the parameter by name
        if pk == 'ident' and not pv.get('subpat'):
            src, mut_kw = pv['ident'], bool(pv.get('mut'))
        else:
            src, mut_kw = f'__arg{i}', False
        if ty[0] == 'fn':
            sv = f'S_{src}'
            polys.append(sv)
            ty = ('fn', ty[1], ty[2], ('var', sv))
        params.append(Param(src, pat, ty, ref, False, mut_kw))
    if fd.output is None:
        ret = UNIT
    else:
        ret = resolve(prog, fd.output, g, fd.owner)
        if ret[0] == 'fn':
            ret = ('fn', ret[1], ret[2], UNIT)
    fd._sig = Sig(fd, params, ret, polys)
    return fd._sig


def payload_tys(sig, sub=None):
    sub = sub or {}
    tys = [substitute(sig.ret_ty, sub)]
    for p, kind in sig.outputs():
        if kind == 'value':
            tys.append(substitute(p.ty, sub))
        else:
            tys.append(substitute(p.ty[3], sub))
    return tys


# ---------------------------------------------------------------------------
# argument helpers

def closure_arg(L, arg, env, fn_ty, sub, k2):
    """Lower an argument of `impl Fn*` type, then call
    k2(lambda atom, state atom, state type, writeback, closure return type, env)
    where writeback(state_atom, env) -> (prefix, env) stores the returned state."""
    a = strip_parens(arg)
    ak, av = one_key(a)
    fn_ty = substitute(fn_ty, sub)
    if ak == 'closure':
        text, sigma, captured, ret = L.lower_closure(av, env, fn_ty)
        reads = []
        for c in captured:
            if c in env.vars:
                reads.append(env.vars[c].lean)
            else:
                root, *path = c.split('.')
                reads.append(L.read_place((root, path), env)[0])

        def writeback(state_atom, env2):
            if not captured:
                return '', env2
            names = [fresh('w') for _ in captured]
            text2 = ''
            env3 = env2
            for c, n in zip(captured, names):
                if c in env3.vars:
                    pre, env3 = L.write_place((c, []), n, env3)
                else:
                    root, *path = c.split('.')
                    pre, env3 = L.write_place((root, path), n, env3)
                text2 += pre
            if len(names) == 1:
                return f'let {names[0]} := {state_atom}; ' + text2, env3
            return f'match {state_atom} with | {tuple_text(names)} => ' + text2, env3
        return k2(text, tuple_text(reads), sigma, writeback, ret, env)
    n = ident_of_path_expr(a)
    if n is not None and n in env.vars and env.vars[n].ty[0] == 'fn':
        var = env.vars[n]
        st_key = f'{n}#state'
        L.note('call:closure-variable-argument')
        if st_key in env.vars:
            sv = env.vars[st_key]

            def writeback(state_atom, env2):
                return L.write_place((st_key, []), state_atom, env2)
            return k2(var.lean, sv.lean, sv.ty, writeback, var.ty[2], env)
        return k2(var.lean, '()', UNIT, (lambda s, env2: ('', env2)), var.ty[2], env)

    # an expression producing a closure with no hidden state (e.g. `self.vtable_lookup()`)
    def after(atom, t, env2):
        if t[0] != 'fn' or t[3] not in (UNIT, None):
            raise Refusal('closure-argument-expression', show_ty(t))
        L.note('call:closure-expression-argument')
        return k2(atom, '()', UNIT, (lambda s, env3: ('', env3)), t[2], env2)
    return L.lower_expr(arg, env, fn_ty, after)


def place_arg(L, arg, env):
    """`&mut place` argument: (atom, place)."""
    place = L.place_of(arg, env)
    if place is None:
        raise Refusal('mutable-reference-argument-not-a-place', str(arg)[:80])
    atom, ty = L.read_place(place, env)
    return atom, place


def is_mut_ref_expr(arg):
    ak, av = one_key(arg)
    return ak == 'reference' and av.get('mut')


# ---------------------------------------------------------------------------
# user function calls

def call_user(L, fd, recv, args, env, exp, k, turbofish_sub=None):
    """recv: None or (atom, ty, place-or-None)."""
    sig = signature(L, fd)
    params = sig.params
    L.note('call:spec-function')
    self_p = sig.self_param
    value_params = [p for p in params if not p.is_self]
    if len(args) != len(value_params):
        raise Refusal('call-arity', f'{fd.display}: {len(args)} vs {len(value_params)}')
    sub = {}

    def go(i, atoms, states, wbs, env2):
        if i == len(value_params):
            return emit(atoms, states, wbs, env2)
        p = value_params[i]
        arg = args[i]
        if p.is_fn:
            expected = p.ty

            def with_closure(lam, st, sty, wb, ret, env3):
                # bind the generic return type variable of the callee from the closure
                if p.ty[2][0] == 'var' and ret is not None:
                    sub[p.ty[2][1]] = ret
                elif p.ty[2][0] == 'result' and p.ty[2][2][0] == 'var' and ret is not None and ret[0] == 'result':
                    sub[p.ty[2][2][1]] = ret[2]
                sub[p.ty[3][1]] = sty
                return go(i + 1, atoms + [lam], states + [st], wbs + [('state', wb)], env3)
            return closure_arg(L, arg, env2, expected, {k_: v_ for k_, v_ in sub.items() if k_ != p.ty[3][1]}, with_closure)
        if p.ref == 'mut':
            if not is_mut_ref_expr(arg):
                # implicit reborrow of a `&mut` binding
                L.note('call:implicit-reborrow')
            atom, place = place_arg(L, arg, env2)
            return go(i + 1, atoms + [atom], states, wbs + [('place', place)], env2)
        return L.lower_expr(arg, env2, substitute(p.ty, sub),
                            lambda a, t, env3: go(i + 1, atoms + [a], states, wbs, env3))

    def emit(atoms, states, wbs, env2):
        call_args = [L.fuel]
        if self_p is not None:
            call_args.append(recv[0])
        call_args += atoms + states
        if sig.polys:
            missing = [v for v in sig.polys if v not in sub]
            if missing:
                raise Refusal('polymorphic-call-type-argument-unknown', f'{fd.display}: {missing}')
            call = f'{fd.lean_name} ' + ' '.join([lean_type(sub[v], 'arg') for v in sig.polys] + call_args)
        else:
            call = f'{fd.lean_name} ' + ' '.join(call_args)
        tys = payload_tys(sig, sub)
        out_kinds = []
        if self_p is not None and self_p.ref == 'mut':
            out_kinds.append(('recv', None))
        for p in value_params:
            if p.ref == 'mut':
                out_kinds.append(('place', None))
        state_wbs = [wb for kind, wb in wbs if kind == 'state']
        place_wbs = [wb for kind, wb in wbs if kind == 'place']
        # order in the payload: self (if &mut), &mut params, closure states
        # (Sig.outputs puts the receiver first because it is params[0])

        def after(names):
            text = ''
            env3 = env2
            idx = 1
            pi = 0
            si = 0
            for p, kind in sig.outputs():
                n = names[idx]
                idx += 1
                if kind == 'value':
                    if p.is_self:
                        if recv[2] is not None:
                            pre, env3 = L.write_place(recv[2], n, env3)
                            text += pre
                    else:
                        pre, env3 = L.write_place(place_wbs[pi], n, env3)
                        pi += 1
                        text += pre
                else:
                    pre, env3 = state_wbs[si](n, env3)
                    si += 1
                    text += pre
            ret_ty = substitute(sig.ret_ty, sub)
            return text + k(names[0], ret_ty, env3)
        return L.bind_tuple(call, tys, after, env2)

    return go(0, [], [], [], env)


# ---------------------------------------------------------------------------
# method calls

class Recv:
    def __init__(self, atom, ty, place):
        self.atom, self.ty, self.place = atom, ty, place


def lower_method_call(L, v, env, exp, k):
    method = v['method']
    receiver = v['receiver']
    args = v.get('args', [])
    place = L.place_of(receiver, env)
    if place is not None:
        atom, ty = L.read_place(place, env)
        return dispatch_method(L, method, Recv(atom, ty, place), args, env, exp, k, v)
    return L.lower_expr(receiver, env, None,
                        lambda a, t, env2: dispatch_method(L, method, Recv(a, t, None), args, env2, exp, k, v))


def dispatch_method(L, method, recv, args, env, exp, k, node):
    t = recv.ty
    if t[0] == 'adt' and t[1] not in ('Endianness',):
        fd = find_method(L, t[1], method, len(args))
        if fd is not None:
            return call_user(L, fd, (recv.atom, recv.ty, recv.place), args, env, exp, k)
    if method == 'collect' and node.get('turbofish'):
        targs = node['turbofish']['args']
        tk, tv = one_key(targs[0])
        target = one_key(tv)[1]['segments'][-1]['ident'] if tk == 'type' else None
        elem_t = t[1] if t[0] in ('list', 'iter', 'set') else None
        if target == 'Set' and elem_t is not None:
            exp = ('set', elem_t)
        elif target == 'List' and elem_t is not None:
            exp = ('list', elem_t)
        L.note('typing:collect-turbofish')
    h = LIB.get((kind_of(t), method))
    if h is None:
        raise Refusal('library-method', f'{show_ty(t)}.{method}')
    L.note(f'lib:{kind_of(t)}.{method}')
    return h(L, env, recv, args, exp, k)


def kind_of(t):
    if t[0] == 'adt':
        return 'adt:' + t[1]
    return t[0]


def find_method(L, owner, method, nargs=None):
    """Inherent methods first (Rust's rule for concrete receivers). A receiver
    whose declared type was a generic parameter (e.g. `memory: M`) only sees
    the trait's methods; after monomorphization this shows as an arity mismatch
    with the inherent method, so a method whose arity does not fit is skipped."""
    prog = L.prog
    cands = [f for f in prog.fns if f.owner == owner and f.name == method]
    if nargs is not None:
        fits = [f for f in cands if len([i for i in f.inputs if one_key(i)[0] != 'receiver']) == nargs]
        if fits != cands:
            L.note('call:method-resolved-by-arity')
        cands = fits
    if not cands:
        return None
    inh = [f for f in cands if f.trait is None]
    if inh:
        return inh[0]
    if len(cands) == 1:
        return cands[0]
    raise Refusal('ambiguous-method', f'{owner}::{method}')


def writeback_recv(L, recv, new_atom, env):
    if recv.place is None:
        return '', env
    return L.write_place(recv.place, new_atom, env)


# ---------------------------------------------------------------------------
# free / associated function calls

def lower_call(L, v, env, exp, k):
    func = v['func']
    args = v.get('args', [])
    fk, fv = one_key(func)
    if fk != 'path':
        # calling the closure a method returned: `self.vtable_lookup()(ptr)`
        return L.lower_expr(func, env, None, lambda fa, ft, env2: call_closure_value(L, fa, ft, None, args, env2, exp, k))
    if fv.get('qself'):
        raise Refusal('qualified-self-path', '')
    segs = fv['segments']
    ids = [s['ident'] for s in segs]
    name = ids[-1]
    if len(ids) == 1:
        if name.startswith('__m_'):
            return lower_macro(L, name[4:], args, env, exp, k)
        if name in env.vars and env.vars[name].ty[0] == 'fn':
            var = env.vars[name]
            return call_closure_value(L, var.lean, var.ty, name, args, env, exp, k)
        if name == 'ret':
            return lower_ret(L, args, env, exp, k)
        if name in ('Some', 'Ok', 'Err'):
            return lower_wrap(L, name, args, env, exp, k)
        if name == 'pick':
            return lower_pick(L, args, env, exp, k)
        if name == 'predict':
            return lower_predict(L, args, env, exp, k)
        # tuple struct constructor
        if name in L.prog.adts and L.prog.adts[name].kind == 'struct':
            a = L.prog.adts[name]
            L.note('expr:tuple-struct-constructor')
            return L.lower_exprs(args, env, [t for _, t in a.fields],
                                 lambda atoms, tys, env2: k(f'(MR_{name}.mk ' + ' '.join(atoms) + ')', adt(name), env2))
        # glob-imported / expected-type variant constructor
        ctor = variant_ctor(L, ids, env, exp)
        if ctor is not None:
            return build_variant(L, ctor, args, env, k)
        fd = [f for f in L.prog.fns if f.owner is None and f.name == name]
        if fd:
            return call_user(L, fd[0], None, args, env, exp, k)
        raise Refusal('unknown-function', name)
    owner = env.aliases.get(ids[-2], ids[-2])
    lib = LIB_ASSOC.get((owner, name))
    if lib is not None:
        L.note(f'lib:{owner}::{name}')
        return lib(L, env, args, exp, k)
    cfg = L.prog.config['monomorphization']
    if owner == 'Self' and L.cur_fn is not None:
        owner = L.cur_fn.owner
        cands = [f for f in L.prog.fns if f.owner == owner and f.name == name]
        inh = [f for f in cands if f.trait is None]
        if inh or cands:
            return call_user(L, (inh or cands)[0], None, args, env, exp, k)
    if owner in L.cur_fn.generics if L.cur_fn else False:
        b = L.cur_fn.generics[owner]
        if b[0] == 'bound':
            impl_owner = b[2][1]
            fd = [f for f in L.prog.fns if f.owner == impl_owner and f.name == name and f.trait == b[1]]
            if fd:
                return call_user(L, fd[0], None, args, env, exp, k)
    if owner in L.prog.adts:
        a = L.prog.adts[owner]
        if a.kind == 'enum' and any(vn == name for vn, _, _ in a.variants):
            return build_variant(L, (owner, name), args, env, k)
        cands = [f for f in L.prog.fns if f.owner == owner and f.name == name]
        inh = [f for f in cands if f.trait is None]
        if inh or cands:
            return call_user(L, (inh or cands)[0], None, args, env, exp, k)
    raise Refusal('associated-function', '::'.join(ids))


def variant_ctor(L, ids, env, exp):
    name = ids[-1]
    if exp and exp[0] == 'adt':
        a = L.prog.adts.get(exp[1])
        if a and a.kind == 'enum' and any(vn == name for vn, _, _ in a.variants):
            return (exp[1], name)
    if name in env.globs:
        return (env.globs[name][0], name)
    return None


def build_variant(L, ctor, args, env, k):
    owner, vname = ctor
    a = L.prog.adts[owner]
    fields = [fs for vn, st, fs in a.variants if vn == vname][0]
    if len(fields) != len(args):
        raise Refusal('variant-constructor-arity', f'{owner}::{vname}')
    L.note('expr:variant-constructor')
    return L.lower_exprs(args, env, [t for _, t in fields],
                         lambda atoms, tys, env2: k(f'(MR_{owner}.{vname} ' + ' '.join(atoms) + ')', adt(owner), env2))


def call_closure_value(L, fatom, fty, var_name, args, env, exp, k):
    params, ret, sigma = fty[1], fty[2], fty[3]
    if len(params) != len(args):
        raise Refusal('closure-call-arity', '')
    L.note('call:closure-value')
    st_key = f'{var_name}#state' if var_name else None
    state_atom = env.vars[st_key].lean if st_key and st_key in env.vars else '()'

    def go(i, atoms, places, env2):
        if i == len(args):
            call = f'{fatom} ' + ' '.join(atoms + [state_atom])
            tys = [ret] + [p for p, m in params if m] + [sigma if sigma is not None else UNIT]

            def after(names):
                text = ''
                env3 = env2
                for pl, n in zip(places, names[1:1 + len(places)]):
                    pre, env3 = L.write_place(pl, n, env3)
                    text += pre
                if st_key and st_key in env3.vars:
                    pre, env3 = L.write_place((st_key, []), names[-1], env3)
                    text += pre
                return text + k(names[0], ret, env3)
            return L.bind_tuple(call, tys, after, env2)
        pty, is_mut = params[i]
        if is_mut:
            atom, place = place_arg(L, args[i], env2)
            return go(i + 1, atoms + [atom], places + [place], env2)
        return L.lower_expr(args[i], env2, pty, lambda a, t, env3: go(i + 1, atoms + [a], places, env3))
    return go(0, [], [], env)


def lower_ret(L, args, env, exp, k):
    target = exp
    if target is None or target[0] == 'var':
        raise Refusal('ret-without-expected-type', '')
    L.note('expr:ret')
    if target[0] == 'result':
        def ok(a, t, env2):
            full = ('result', target[1], t) if has_var(target[2]) else target
            return k(f'(SRes.ok {a} : {lean_type(full)})', full, env2)
        return L.lower_expr(args[0], env, exp_or_none(target[2]), ok)
    if target[0] == 'option':
        def some(a, t, env2):
            full = ('option', t) if has_var(target[1]) else target
            return k(f'(some {a} : {lean_type(full)})', full, env2)
        return L.lower_expr(args[0], env, exp_or_none(target[1]), some)
    # Nondet<T>
    return L.lower_expr(args[0], env, target, k)


def lower_wrap(L, name, args, env, exp, k):
    L.note('expr:option-result-constructor')
    if name == 'Some':
        inner = exp_or_none(exp[1]) if exp and exp[0] == 'option' else None
        return L.lower_expr(args[0], env, inner, lambda a, t, env2: k(f'(some {a} : {lean_type(("option", t))})', ('option', t), env2))
    if not exp or exp[0] != 'result' or has_var(exp):
        raise Refusal('Ok-Err-without-expected-result-type', name)
    if name == 'Ok':
        return L.lower_expr(args[0], env, exp[2], lambda a, t, env2: k(f'(SRes.ok {a} : {lean_type(exp)})', exp, env2))
    return L.lower_expr(args[0], env, exp[1], lambda a, t, env2: k(f'(SRes.err {a} : {lean_type(exp)})', exp, env2))


def lower_pick(L, args, env, exp, k):
    """v2: `pick(distr, pred)` is a demonic choice node of the free monad
    (`SPick.choose`); no candidate is resolved in the generated code."""
    L.note('lib:pick')

    def after(da, dt, env2):
        if dt != DISTR:
            raise Refusal('pick-distribution', show_ty(dt))
        fn_ty = ('fn', ((INT, False),), BOOL, None)

        def with_closure(lam, st, sty, wb, ret, env3):
            call = f'SPick.choose (σ := {lean_type(sty, "arg")}) {da} {lam} {st}'

            def done(names):
                pre, env4 = wb(names[1], env3)
                return pre + k(names[0], INT, env4)
            return L.bind_tuple(call, [INT, sty], done, env3)
        return closure_arg(L, args[1], env2, fn_ty, {}, with_closure)
    return L.lower_expr(args[0], env, DISTR, after)


def enum_decoder(L, t):
    """A Clean term `Nat → Option T` enumerating the values of `t`, for the types a
    `predict` ranges over: `Option`, `()`, `bool`, a tuple whose other components
    are `()`, and a struct with exactly one integer field (an id). Anything else is
    refused by name."""
    if t == UNIT:
        return '(fun (i : Nat) => match i with | 0 => some () | _ => none)'
    if t == BOOL:
        return '(fun (i : Nat) => match i with | 0 => some false | 1 => some true | _ => none)'
    if t[0] == 'option':
        inner = enum_decoder(L, t[1])
        ty = lean_type(t)
        return (f'(fun (i : Nat) => match i with | 0 => some (none : {ty}) '
                f'| j + 1 => (match {inner} j with | some v => some (some v : {ty}) | none => none))')
    if t[0] == 'tuple':
        comps = list(t[1])
        live = [j for j, c in enumerate(comps) if c != UNIT]
        if len(live) != 1:
            raise Refusal('predict-domain-not-enumerable', show_ty(t))
        inner = enum_decoder(L, comps[live[0]])
        parts = ['v' if j == live[0] else '()' for j in range(len(comps))]
        return f'(fun (i : Nat) => match {inner} i with | some v => some ({", ".join(parts)}) | none => none)'
    if t[0] == 'adt' and t[1] in L.prog.adts:
        a = L.prog.adts[t[1]]
        if a.kind == 'struct' and len(a.fields) == 1 and a.fields[0][1] == INT:
            return f'(fun (i : Nat) => some (MR_{t[1]}.mk (Int.ofNat i)))'
    raise Refusal('predict-domain-not-enumerable', show_ty(t))


def lower_predict(L, args, env, exp, k):
    """v2: `predict(pred)` is an angelic prediction node of the free monad
    (`SPredict.choose`) over the candidates `enum_decoder` enumerates; the
    predicted type is the closure parameter's annotation."""
    L.note('lib:predict')
    if len(args) != 1:
        raise Refusal('predict-arity', str(len(args)))
    cl = strip_parens(args[0])
    ck, cv = one_key(cl)
    if ck != 'closure' or len(cv.get('inputs', [])) != 1:
        raise Refusal('predict-without-closure-literal', '')
    inp = cv['inputs'][0]
    ik, iv = one_key(inp) if isinstance(inp, dict) else (inp, None)
    if ik != 'type':
        raise Refusal('predict-closure-parameter-without-type', '')
    pty = L.rt(iv['ty'])
    dec = enum_decoder(L, pty)
    fn_ty = ('fn', ((pty, False),), BOOL, None)

    def with_closure(lam, st, sty, wb, ret, env3):
        call = (f'SPredict.choose (β := {lean_type(pty, "arg")}) (σ := {lean_type(sty, "arg")}) '
                f'{dec} {lam} {st}')

        def done(names):
            pre, env4 = wb(names[1], env3)
            # `predict(..)` is `Nondet<T>`: its `?` resolves the prediction and
            # must not be read as `Option`'s `?` when T is an `Option`.
            return pre + k(names[0], ('nondet', pty), env4)
        return L.bind_tuple(call, [pty, sty], done, env3)
    return closure_arg(L, args[0], env, fn_ty, {}, with_closure)


# ---------------------------------------------------------------------------
# prelude macros

def parse_format(fmt):
    """-> list of ('lit', text) | ('arg', index or name, debug?)"""
    out = []
    i = 0
    buf = ''
    auto = 0
    while i < len(fmt):
        c = fmt[i]
        if c == '{':
            if fmt[i + 1:i + 2] == '{':
                buf += '{'
                i += 2
                continue
            j = fmt.index('}', i)
            spec = fmt[i + 1:j]
            if buf:
                out.append(('lit', buf))
                buf = ''
            name, _, fmtspec = spec.partition(':')
            debug = '?' in fmtspec
            if fmtspec not in ('', '?'):
                raise Refusal('format-spec', spec)
            if name == '':
                out.append(('arg', auto, debug))
                auto += 1
            elif name.isdigit():
                out.append(('arg', int(name), debug))
            else:
                out.append(('arg', name, debug))
            i = j + 1
            continue
        if c == '}' and fmt[i + 1:i + 2] == '}':
            buf += '}'
            i += 2
            continue
        buf += c
        i += 1
    if buf:
        out.append(('lit', buf))
    return out


def render(L, t, atom, debug):
    """(text, monadic?) for one format argument."""
    if t == STR:
        if debug:
            return f'(SDebug.str {atom})', False
        return atom, False
    if t in (INT, SIZE, ALIGN):
        if debug and t == SIZE:
            return f'(SDebug.size {atom})', False
        if debug and t == ALIGN:
            return f'(SDebug.align {atom})', False
        return f'(SInt.toString {atom})', False
    if t == BOOL:
        return f'(SBool.toString {atom})', False
    if debug and t[0] == 'adt':
        a = L.prog.adts[t[1]]
        if a.kind == 'enum' and all(st == 'unit' for _, st, _ in a.variants):
            return f'(MR_{t[1]}.debugName {atom})', False
        # the generated derived-Debug walk; it refuses hash containers at the
        # point they occur, so reaching one is a `refused` outcome, not a
        # message the reference would not have printed
        return f'(MR_{t[1]}.debugStr {L.fuel} {atom})', True
    raise Refusal('format-of-structured-value', f'{"{:?}" if debug else "{}"} of {show_ty(t)}')


def lower_format(L, args, env, k):
    ak, av = one_key(args[0])
    if ak != 'lit':
        raise Refusal('format-string-not-literal', '')
    _, fmt = lit_value(av)
    pieces = parse_format(fmt)
    rest = args[1:]
    named = {}
    positional = []
    for a in rest:
        positional.append(a)
    exprs = []
    order = []
    for p in pieces:
        if p[0] == 'arg':
            if isinstance(p[1], int):
                if p[1] >= len(positional):
                    raise Refusal('format-argument-index', str(p[1]))
                exprs.append(positional[p[1]])
            else:
                exprs.append({'path': {'segments': [{'ident': p[1]}]}})

    def after(atoms, tys, env2):
        rendered = []
        i = 0
        for p in pieces:
            if p[0] == 'lit':
                rendered.append((lean_string(p[1]), False))
            else:
                rendered.append(render(L, tys[i], atoms[i], p[2]))
                i += 1

        def build(j, parts, env3):
            if j == len(rendered):
                if not parts:
                    return k('""', STR, env3)
                s = parts[0]
                for q in parts[1:]:
                    s = f'(String.append {s} {q})'
                return k(s, STR, env3)
            text, monadic = rendered[j]
            if not monadic:
                return build(j + 1, parts + [text], env3)
            return L.bind_simple(text[1:-1] if text.startswith('(') and text.endswith(')') else text,
                                 STR, env3, lambda a, t, env4: build(j + 1, parts + [a], env4), 'dbg')
        return build(0, [], env2)
    return L.lower_exprs(exprs, env, None, after)


def lower_macro(L, name, args, env, exp, k):
    L.note(f'macro:{name}!')
    ti = adt('TerminationInfo')
    if name in ('throw_ub', 'throw_ill_formed'):
        variant = 'Ub' if name == 'throw_ub' else 'IllFormed'
        try:
            return lower_format(L, args, env, lambda s, t, env2: throw_term(L, f'(MR_TerminationInfo.{variant} {s})', env2))
        except Refusal as r:
            if not r.construct.startswith('format'):
                raise
            # the termination still happens, but its message cannot be rendered:
            # reaching this point is reported as a refusal, never as that UB
            L.partial.append((L.cur_fn.display, r.construct, r.detail))
            return f'SOut.refused {lean_string(r.construct + " in " + L.cur_fn.display)}'
    simple = {'throw_machine_stop': 'MachineStop', 'throw_abort': 'Abort', 'throw_memory_leak': 'MemoryLeak',
              'throw_deadlock': 'Deadlock'}
    if name in simple:
        return throw_term(L, f'MR_TerminationInfo.{simple[name]}', env)
    if name == 'throw':
        rt = env.fn.ret_ty
        if rt[0] != 'option':
            raise Refusal('throw-in-non-option-function', show_ty(rt))
        return env.fn.ret(f'(none : {lean_type(rt)})', env)
    if name in ('panic', 'unreachable'):
        msg = panic_message(args, name)
        return L.panic(env, msg)
    if name == 'assert':
        msg = panic_message(args[1:], 'assertion failed')
        return L.lower_expr(args[0], env, BOOL, lambda c, t, env2:
                            f'(match {c} with | true => {k("()", UNIT, env2)} | false => {L.panic(env2, msg)})')
    if name == 'assert_eq':
        msg = panic_message(args[2:], 'assertion `left == right` failed')

        def after(atoms, tys, env2):
            return L.binop('==', atoms[0], tys[0], atoms[1], tys[1], env2, lambda c, t, env3:
                           f'(match {c} with | true => {k("()", UNIT, env3)} | false => {L.panic(env3, msg)})')
        return L.lower_exprs(args[:2], env, None, after)
    if name == 'format':
        return lower_format(L, args, env, k)
    if name == 'list':
        elem = exp[1] if exp and exp[0] == 'list' else None
        if not args:
            if elem is None:
                raise Refusal('empty-list-without-expected-type', '')
            return k(f'([] : {lean_type(("list", elem))})', ('list', elem), env)
        return L.lower_exprs(args, env, [elem] * len(args) if elem else None,
                             lambda atoms, tys, env2: k('[' + ', '.join(atoms) + ']', ('list', elem or tys[0]), env2))
    if name == 'list_repeat':
        elem = exp[1] if exp and exp[0] == 'list' else None

        def after(atoms, tys, env2):
            et = elem or tys[0]
            return L.bind_simple(f'SList.from_elem {atoms[0]} {atoms[1]}', ('list', et), env2, k)
        return L.lower_exprs(args, env, [elem, INT], after)
    if name == 'write':
        raise Refusal('write-to-DynWrite', 'output through a shared stream handle is not modelled')
    raise Refusal('macro', name)


def panic_message(args, default):
    if args:
        ak, av = one_key(args[0])
        if ak == 'lit':
            kind, val = lit_value(av)
            if kind == 'str':
                return val
    return default


def throw_term(L, term, env):
    rt = env.fn.ret_ty
    if rt[0] != 'result':
        raise Refusal('throw-in-non-result-function', show_ty(rt))
    return env.fn.ret(f'(SRes.err {term} : {lean_type(rt)})', env)


# ---------------------------------------------------------------------------
# libspecr: associated functions

def lib_pure1(fn_text, ret):
    def h(L, env, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2: k(f'({fn_text} ' + ' '.join(atoms) + ')', ret, env2))
    return h


def lib_monadic(fn_text, ret):
    def h(L, env, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2: L.bind_simple(f'{fn_text} ' + ' '.join(atoms), ret, env2, k))
    return h


def lib_identity(ret):
    def h(L, env, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2: k(atoms[0], ret, env2))
    return h


def lib_new(kind):
    def h(L, env, args, exp, k):
        if not exp or exp[0] not in (kind,):
            raise Refusal(f'{kind}-new-without-expected-type', '')
        return k(f'([] : {lean_type(exp)})', exp, env)
    return h


def lib_from_bytes_const(ret):
    def h(L, env, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2: k(atoms[0], ret, env2))
    return h


LIB_ASSOC = {
    ('Size', 'from_bytes'): lib_pure1('SSize.from_bytes', ('option', SIZE)),
    ('Offset', 'from_bytes'): lib_pure1('SSize.from_bytes', ('option', SIZE)),
    ('Size', 'from_bytes_const'): lib_from_bytes_const(SIZE),
    ('Size', 'from_bits'): lib_monadic('SSize.from_bits', ('option', SIZE)),
    ('Size', 'from_bits_const'): lib_monadic('SSize.from_bits_const', ('option', SIZE)),
    ('Align', 'from_bytes'): lib_pure1('SAlign.from_bytes', ('option', ALIGN)),
    ('Align', 'from_bits'): lib_monadic('SAlign.from_bits', ('option', ALIGN)),
    ('Align', 'from_bits_const'): lib_monadic('SAlign.from_bits_const', ('option', ALIGN)),
    ('Align', 'from_bytes_const'): lib_pure1('SAlign.from_bytes_const', ('option', ALIGN)),
    ('Int', 'from'): lib_identity(INT),
    ('ThreadId', 'from'): lib_identity(INT),
    ('List', 'new'): lib_new('list'),
    ('Map', 'new'): lib_new('map'),
    ('Set', 'new'): lib_new('set'),
}


# ---------------------------------------------------------------------------
# libspecr: methods.  Each handler: h(L, env, recv, args, exp, k)

def m_pure(fn, ret_of):
    """`fn recv args...` is a pure Lean term."""
    def h(L, env, recv, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2:
                             k(f'({fn(L, recv.ty)} {recv.atom}' + ''.join(' ' + a for a in atoms) + ')', ret_of(recv.ty, tys), env2))
    return h


def m_monadic(fn, ret_of, arg_exps=None):
    def h(L, env, recv, args, exp, k):
        exps = arg_exps(recv.ty) if arg_exps else None
        return L.lower_exprs(args, env, exps, lambda atoms, tys, env2:
                             L.bind_simple(f'{fn(L, recv.ty)} {recv.atom}' + ''.join(' ' + a for a in atoms), ret_of(recv.ty, tys), env2, k))
    return h


def m_mut_pure_pair(fn, ret_of, arg_exps=None):
    """`&mut self` method returning (ret, new receiver) as a pure pair."""
    def h(L, env, recv, args, exp, k):
        exps = arg_exps(recv.ty) if arg_exps else None

        def after(atoms, tys, env2):
            p = fresh('mp')
            r, nr = fresh('r'), fresh('nr')
            call = f'({fn(L, recv.ty)} {recv.atom}' + ''.join(' ' + a for a in atoms) + ')'
            pre, env3 = writeback_recv(L, recv, nr, env2)
            return f'(match {call} with | ({r}, {nr}) => {pre}{k(r, ret_of(recv.ty, tys), env3)})'
        return L.lower_exprs(args, env, exps, after)
    return h


def m_mut_new(fn, arg_exps=None, monadic=False):
    """`&mut self` method whose Lean function returns only the new receiver."""
    def h(L, env, recv, args, exp, k):
        exps = arg_exps(recv.ty) if arg_exps else None

        def after(atoms, tys, env2):
            call = f'{fn(L, recv.ty)} {recv.atom}' + ''.join(' ' + a for a in atoms)
            n = fresh('nr')
            pre, env3 = writeback_recv(L, recv, n, env2)
            if monadic:
                return f'SOut.bind (α := {lean_type(recv.ty, "arg")}) (β := {env2.fn.inner_ty(env2)}) ({call}) (fun ({n} : {lean_type(recv.ty)}) => {pre}{k("()", UNIT, env3)})'
            return f'let {n} : {lean_type(recv.ty)} := ({call}); ' + pre + k('()', UNIT, env3)
        return L.lower_exprs(args, env, exps, after)
    return h


def elem(t):
    return t[1]


def keyeq(L, t):
    return L.tinfo.eq_pure(t[1])


def hof_type_args(name, recv_ty, ret, tys, sty):
    elem = recv_ty[1]
    T = lambda n, t: f'({n} := {lean_type(t, "arg")})'
    if name in ('SList.anyS', 'SList.allS', 'SList.findS'):
        return [T('α', elem), T('σ', sty)]
    if name in ('SList.mapS', 'SList.mapWithIdxS'):
        return [T('α', elem), T('β', ret), T('σ', sty)]
    if name == 'SList.flatMapS':
        return [T('α', elem), T('β', ret[1]), T('σ', sty)]
    if name in ('SList.findMapS', 'SList.tryMapOptS'):
        return [T('α', elem), T('β', ret[1]), T('σ', sty)]
    if name == 'SList.tryMapResS':
        return [T('α', elem), T('β', ret[2]), T('ε', ret[1]), T('σ', sty)]
    if name == 'SList.foldWithIdxS':
        return [T('α', elem), T('A', tys[0]), T('σ', sty)]
    raise Refusal('hof-type-arguments', name)


def hof(prelude_fn, fn_params, ret_of, extra_args=0, extra_exps=None, closure_ret=None):
    """Higher-order library method. `fn_params(recv_ty)` gives the closure's
    parameter types; `ret_of(recv_ty, closure_ret, extra_tys)` the result type.
    Leading `extra_args` arguments are ordinary values (e.g. fold init)."""
    def h(L, env, recv, args, exp, k):
        def after_extra(atoms, tys, env2):
            params = tuple((p, False) for p in fn_params(recv.ty, tys))
            fn_ty = ('fn', params, closure_ret(recv.ty, tys) if closure_ret else None, None)

            def with_closure(lam, st, sty, wb, ret, env3):
                rty = ret_of(recv.ty, ret, tys)
                fname = prelude_fn(ret)
                targs = hof_type_args(fname, recv.ty, ret, tys, sty)
                call = f'{fname} ' + ' '.join(targs) + f' {recv.atom} ' + ''.join(a + ' ' for a in atoms) + f'{lam} {st}'

                def done(names):
                    pre, env4 = wb(names[1], env3)
                    return pre + k(names[0], rty, env4)
                return L.bind_tuple(call, [rty, sty], done, env3)
            return closure_arg(L, args[extra_args], env2, fn_ty, {}, with_closure)
        exps = extra_exps(recv.ty) if extra_exps else None
        return L.lower_exprs(args[:extra_args], env, exps, after_extra)
    return h


def try_map_fn(ret):
    if ret is None:
        raise Refusal('try-map-closure-type', '')
    if ret[0] == 'result':
        return 'SList.tryMapResS'
    if ret[0] == 'option':
        return 'SList.tryMapOptS'
    raise Refusal('try-map-closure-return', show_ty(ret))


def try_map_ret(t, ret, _):
    if ret[0] == 'result':
        return ('result', ret[1], ('list', ret[2]))
    return ('option', ('list', ret[1]))


def mutate_at(L, env, recv, args, exp, k):
    """`list.mutate_at(i, |x| ...)` / `try_mutate_at`: the closure takes `&mut T`."""
    def after_idx(i_atom, ti, env2):
        fn_ty = ('fn', ((recv.ty[1], True),), None, None)

        def with_closure(lam, st, sty, wb, ret, env3):
            call = f'SList.mutateAtS (α := {lean_type(recv.ty[1], "arg")}) (O := {lean_type(ret, "arg")}) (σ := {lean_type(sty, "arg")}) {recv.atom} {i_atom} {lam} {st}'

            def done(names):
                pre, env4 = writeback_recv(L, recv, names[1], env3)
                pre2, env5 = wb(names[2], env4)
                return pre + pre2 + k(names[0], ret, env5)
            return L.bind_tuple(call, [ret, recv.ty, sty], done, env3)
        return closure_arg(L, args[1], env2, fn_ty, {}, with_closure)
    return L.lower_expr(args[0], env, INT, after_idx)


def sort_by_key(L, env, recv, args, exp, k):
    fn_ty = ('fn', ((recv.ty[1], False),), None, None)

    def with_closure(lam, st, sty, wb, ret, env2):
        if ret not in (INT, SIZE, ALIGN):
            raise Refusal('sort-by-non-integer-key', show_ty(ret))
        call = f'SList.sortByIntKeyS (α := {lean_type(recv.ty[1], "arg")}) (σ := {lean_type(sty, "arg")}) {recv.atom} {lam} {st}'

        def done(names):
            pre, env3 = writeback_recv(L, recv, names[0], env2)
            pre2, env4 = wb(names[1], env3)
            return pre + pre2 + k('()', UNIT, env4)
        return L.bind_tuple(call, [recv.ty, sty], done, env2)
    return closure_arg(L, args[0], env, fn_ty, {}, with_closure)


def m_collect(L, env, recv, args, exp, k):
    # `.collect::<Set<_>>()` / `.collect::<List<_>>()` / plain `.collect()`
    target = exp
    node_tf = None
    if target is None:
        raise Refusal('collect-without-expected-type', '')
    if target[0] == 'list':
        return k(recv.atom, ('list', recv.ty[1]), env)
    if target[0] == 'set':
        return k(f'(SSet.ofList {L.tinfo.eq_pure(recv.ty[1])} [] {recv.atom})', ('set', recv.ty[1]), env)
    raise Refusal('collect-into', show_ty(target))


def m_cmp(L, env, recv, args, exp, k):
    return L.lower_exprs(args, env, None, lambda atoms, tys, env2:
                         k(f'({"SBool.cmp" if recv.ty == BOOL else "SInt.cmp"} {recv.atom} {atoms[0]})', ORDERING, env2))


def m_minmax(which):
    def h(L, env, recv, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2:
                             k(f'(SInt.{which} {recv.atom} {atoms[0]})', recv.ty, env2))
    return h


def m_in_bounds(name, ret):
    def h(L, env, recv, args, exp, k):
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2:
                             L.bind_simple(f'SInt.{name} {recv.atom} {atoms[0]} {atoms[1]}', ret, env2, k))
    return h


def m_endian(which):
    def h(L, env, recv, args, exp, k):
        ret = INT if which == 'decode' else ('option', ('list', INT))
        return L.lower_exprs(args, env, None, lambda atoms, tys, env2:
                             L.bind_simple(f'SEndian.{which} {recv.atom} ' + ' '.join(atoms), ret, env2, k))
    return h


def m_unwrap(L, env, recv, args, exp, k):
    if recv.ty[0] == 'option':
        return L.bind_simple(f'SOption.unwrap {recv.atom}', recv.ty[1], env, k)
    return L.bind_simple(f'SRes.unwrap {recv.atom}', recv.ty[2], env, k)


def m_expect(L, env, recv, args, exp, k):
    msg = panic_message(args, 'expect')
    if recv.ty[0] == 'option':
        return L.bind_simple(f'SOption.expect {recv.atom} {lean_string(msg)}', recv.ty[1], env, k)
    return L.bind_simple(f'SRes.expect {recv.atom} {lean_string(msg)}', recv.ty[2], env, k)


def m_option_map(L, env, recv, args, exp, k):
    fn_ty = ('fn', ((recv.ty[1], False),), None, None)

    def with_closure(lam, st, sty, wb, ret, env2):
        rty = ('option', ret)

        def done(names):
            pre, env3 = wb(names[1], env2)
            return pre + k(names[0], rty, env3)
        return L.bind_tuple(f'SOption.mapS (α := {lean_type(recv.ty[1], "arg")}) (β := {lean_type(ret, "arg")}) (σ := {lean_type(sty, "arg")}) {recv.atom} {lam} {st}', [rty, sty], done, env2)
    return closure_arg(L, args[0], env, fn_ty, {}, with_closure)


def m_option_map_or(L, env, recv, args, exp, k):
    def after_default(d, dt, env2):
        fn_ty = ('fn', ((recv.ty[1], False),), dt, None)

        def with_closure(lam, st, sty, wb, ret, env3):
            def done(names):
                pre, env4 = wb(names[1], env3)
                return pre + k(names[0], dt, env4)
            return L.bind_tuple(f'SOption.mapOrS (α := {lean_type(recv.ty[1], "arg")}) (β := {lean_type(dt, "arg")}) (σ := {lean_type(sty, "arg")}) {recv.atom} {d} {lam} {st}', [dt, sty], done, env3)
        return closure_arg(L, args[1], env2, fn_ty, {}, with_closure)
    return L.lower_expr(args[0], env, None, after_default)


def m_unwrap_or(L, env, recv, args, exp, k):
    return L.lower_expr(args[0], env, recv.ty[1], lambda a, t, env2: k(f'(SOption.unwrap_or {recv.atom} {a})', recv.ty[1], env2))


def m_map_get(L, env, recv, args, exp, k):
    return L.lower_expr(args[0], env, recv.ty[1], lambda a, t, env2:
                        k(f'(SMap.get {keyeq(L, recv.ty)} {recv.atom} {a})', ('option', recv.ty[2]), env2))


LIB = {}


def reg(kinds, method, h):
    for kk in kinds:
        LIB[(kk, method)] = h


LISTLIKE = ('list', 'iter', 'set')
reg(('list', 'iter'), 'len', m_pure(lambda L, t: 'SList.len', lambda t, tys: INT))
reg(('set',), 'len', m_pure(lambda L, t: 'SList.len', lambda t, tys: INT))
reg(('map',), 'len', m_pure(lambda L, t: 'SList.len', lambda t, tys: INT))
reg(('list', 'set', 'map', 'iter'), 'is_empty', m_pure(lambda L, t: 'SList.is_empty', lambda t, tys: BOOL))
reg(('list', 'iter'), 'first', m_pure(lambda L, t: 'SList.first', lambda t, tys: ('option', t[1])))
reg(('list', 'iter'), 'next', m_pure(lambda L, t: 'SList.first', lambda t, tys: ('option', t[1])))
reg(('list',), 'last', m_pure(lambda L, t: 'SList.last', lambda t, tys: ('option', t[1])))
reg(('list',), 'get', m_monadic(lambda L, t: 'SList.get', lambda t, tys: ('option', t[1]), lambda t: [INT]))
reg(('list',), 'index_at', m_monadic(lambda L, t: 'SList.index_at', lambda t, tys: t[1], lambda t: [INT]))
reg(('list',), 'subslice_with_length', m_monadic(lambda L, t: 'SList.subslice_with_length', lambda t, tys: t, lambda t: [INT, INT]))
reg(('list',), 'zip', m_pure(lambda L, t: 'SList.zip', lambda t, tys: ('list', ('tuple', (t[1], tys[0][1])))))
reg(('list', 'iter', 'set'), 'iter', lambda L, env, recv, args, exp, k: k(recv.atom, ('iter', recv.ty[1]), env))
reg(('list', 'iter', 'set'), 'into_iter', lambda L, env, recv, args, exp, k: k(recv.atom, ('iter', recv.ty[1]), env))
reg(('map',), 'iter', lambda L, env, recv, args, exp, k: k(recv.atom, ('iter', ('tuple', (recv.ty[1], recv.ty[2]))), env))
reg(('map',), 'into_iter', lambda L, env, recv, args, exp, k: k(recv.atom, ('iter', ('tuple', (recv.ty[1], recv.ty[2]))), env))
reg(('iter', 'list'), 'enumerate', m_pure(lambda L, t: 'SList.enumerate', lambda t, tys: ('iter', ('tuple', (INT, t[1])))))
reg(('iter', 'list'), 'collect', m_collect)
reg(('list',), 'set', m_mut_new(lambda L, t: 'SList.set', lambda t: [INT, t[1]], monadic=True))
reg(('list',), 'push', m_mut_new(lambda L, t: 'SList.push', lambda t: [t[1]]))
reg(('list',), 'pop', m_mut_pure_pair(lambda L, t: 'SList.pop', lambda t, tys: ('option', t[1])))
reg(('list',), 'write_subslice_at_index', m_mut_new(lambda L, t: 'SList.write_subslice_at_index', lambda t: [INT, t], monadic=True))
reg(('list',), 'mutate_at', mutate_at)
reg(('list',), 'try_mutate_at', mutate_at)
reg(('list',), 'sort_by_key', sort_by_key)
reg(('list', 'iter', 'set'), 'any', hof(lambda r: 'SList.anyS', lambda t, tys: [t[1]], lambda t, r, tys: BOOL, closure_ret=lambda t, tys: BOOL))
reg(('list', 'iter', 'set'), 'all', hof(lambda r: 'SList.allS', lambda t, tys: [t[1]], lambda t, r, tys: BOOL, closure_ret=lambda t, tys: BOOL))
reg(('list', 'iter'), 'map', hof(lambda r: 'SList.mapS', lambda t, tys: [t[1]], lambda t, r, tys: ('list', r)))
reg(('list', 'iter'), 'flat_map', hof(lambda r: 'SList.flatMapS', lambda t, tys: [t[1]], lambda t, r, tys: ('list', r[1])))
reg(('list', 'iter'), 'find', hof(lambda r: 'SList.findS', lambda t, tys: [t[1]], lambda t, r, tys: ('option', t[1]), closure_ret=lambda t, tys: BOOL))
reg(('list', 'iter'), 'find_map', hof(lambda r: 'SList.findMapS', lambda t, tys: [t[1]], lambda t, r, tys: r))
reg(('list', 'iter'), 'try_map', hof(try_map_fn, lambda t, tys: [t[1]], try_map_ret))
reg(('list',), 'map_with_idx', hof(lambda r: 'SList.mapWithIdxS', lambda t, tys: [INT, t[1]], lambda t, r, tys: ('list', r)))
reg(('list',), 'fold_with_idx', hof(lambda r: 'SList.foldWithIdxS', lambda t, tys: [tys[0], INT, t[1]], lambda t, r, tys: tys[0], extra_args=1, closure_ret=lambda t, tys: tys[0]))
reg(('map',), 'get', m_map_get)
reg(('map',), 'index_at', m_monadic(lambda L, t: f'SMap.index_at {keyeq(L, t)}', lambda t, tys: t[2], lambda t: [t[1]]))
reg(('map',), 'contains_key', m_pure(lambda L, t: f'SMap.contains_key {keyeq(L, t)}', lambda t, tys: BOOL))
reg(('map',), 'insert', m_mut_pure_pair(lambda L, t: f'SMap.insert {keyeq(L, t)}', lambda t, tys: ('option', t[2]), lambda t: [t[1], t[2]]))
reg(('map',), 'remove', m_mut_pure_pair(lambda L, t: f'SMap.remove {keyeq(L, t)}', lambda t, tys: ('option', t[2]), lambda t: [t[1]]))
reg(('map',), 'try_insert', m_mut_pure_pair(lambda L, t: f'SMap.try_insert {keyeq(L, t)}', lambda t, tys: ('result', UNIT, UNIT), lambda t: [t[1], t[2]]))
reg(('map',), 'keys', m_pure(lambda L, t: 'SMap.keys', lambda t, tys: ('iter', t[1])))
reg(('map',), 'values', m_pure(lambda L, t: 'SMap.values', lambda t, tys: ('iter', t[2])))
reg(('set',), 'contains', m_pure(lambda L, t: f'SSet.contains {L.tinfo.eq_pure(t[1])}', lambda t, tys: BOOL))
reg(('set',), 'insert', m_mut_new(lambda L, t: f'SSet.insert {L.tinfo.eq_pure(t[1])}', lambda t: [t[1]]))
reg(('set',), 'try_insert', m_mut_pure_pair(lambda L, t: f'SSet.try_insert {L.tinfo.eq_pure(t[1])}', lambda t, tys: ('result', UNIT, UNIT), lambda t: [t[1]]))
reg(('set',), 'remove', m_mut_new(lambda L, t: f'SSet.removeL {L.tinfo.eq_pure(t[1])}', lambda t: [t[1]]))
reg(('option', 'result'), 'unwrap', m_unwrap)
reg(('option', 'result'), 'expect', m_expect)
reg(('option',), 'is_some', m_pure(lambda L, t: 'SOption.is_some', lambda t, tys: BOOL))
reg(('option',), 'is_none', m_pure(lambda L, t: 'SOption.is_none', lambda t, tys: BOOL))
reg(('option',), 'map', m_option_map)
reg(('option',), 'map_or', m_option_map_or)
reg(('option',), 'unwrap_or', m_unwrap_or)
reg(('result',), 'is_ok', m_pure(lambda L, t: 'SRes.is_ok', lambda t, tys: BOOL))
reg(('result',), 'is_err', m_pure(lambda L, t: 'SRes.is_err', lambda t, tys: BOOL))
reg(('int',), 'in_bounds', m_in_bounds('in_bounds', BOOL))
reg(('int',), 'bring_in_bounds', m_in_bounds('bring_in_bounds', INT))
reg(('int',), 'rem_euclid', m_monadic(lambda L, t: 'SInt.rem_euclid', lambda t, tys: INT, lambda t: [INT]))
reg(('int',), 'pow', m_monadic(lambda L, t: 'SInt.pow', lambda t, tys: INT, lambda t: [INT]))
reg(('int',), 'next_multiple_of', m_monadic(lambda L, t: 'SInt.next_multiple_of', lambda t, tys: INT, lambda t: [INT]))
reg(('int',), 'is_power_of_two', m_pure(lambda L, t: 'SInt.is_power_of_two', lambda t, tys: BOOL))
reg(('int', 'size', 'align', 'bool'), 'cmp', m_cmp)
reg(('int', 'size', 'align'), 'min', m_minmax('min'))
reg(('int', 'size', 'align'), 'max', m_minmax('max'))
reg(('size', 'align'), 'bytes', lambda L, env, recv, args, exp, k: k(recv.atom, INT, env))
reg(('size',), 'bits', m_pure(lambda L, t: 'SSize.bits', lambda t, tys: INT))
reg(('size',), 'is_zero', m_pure(lambda L, t: 'SSize.is_zero', lambda t, tys: BOOL))
reg(('size',), 'align_to', m_monadic(lambda L, t: 'SSize.align_to', lambda t, tys: SIZE, lambda t: [ALIGN]))
reg(('align',), 'is_aligned', m_monadic(lambda L, t: 'SAlign.is_aligned', lambda t, tys: BOOL, lambda t: [INT]))
for _m in ('is_lt', 'is_gt', 'is_le', 'is_ge', 'is_eq', 'is_ne'):
    reg(('ordering',), _m, m_pure(lambda L, t, _m=_m: f'SOrdering.{_m}', lambda t, tys: BOOL))
reg(('ordering',), 'then', m_pure(lambda L, t: 'SOrdering.then', lambda t, tys: ORDERING))
reg(('adt:Endianness',), 'decode', m_endian('decode'))
reg(('adt:Endianness',), 'encode', m_endian('encode'))
