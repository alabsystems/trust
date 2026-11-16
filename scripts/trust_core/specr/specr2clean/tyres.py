"""Resolve syn type JSON to translator types under the monomorphization config."""

from common import *
from items import to_ty

INT_NAMES = {'Int', 'u8', 'u16', 'u32', 'u64', 'u128', 'i8', 'i16', 'i32', 'i64', 'i128', 'usize', 'isize'}


def resolve(prog, j, generics, self_owner=None):
    k, v = one_key(j)
    if k == 'tuple':
        return tuple_ty(resolve(prog, e, generics, self_owner) for e in v.get('elems', []))
    if k == 'reference':
        return resolve(prog, v['elem'], generics, self_owner)
    if k == 'paren':
        return resolve(prog, v, generics, self_owner)
    if k in ('never', '!'):
        return NEVER
    if k == 'impl_trait':
        return resolve_fn_bound(prog, v['bounds'], generics, self_owner)
    if k != 'path':
        raise Refusal('type-syntax', k)
    if v.get('qself'):
        raise Refusal('qualified-self-type', str(v)[:80])
    segs = v['segments']
    ids = [s['ident'] for s in segs]
    last = segs[-1]
    args = lambda: [resolve(prog, a, generics, self_owner) for a in path_generic_args(last)]
    cfg = prog.config['monomorphization']

    if len(ids) >= 2:
        head, tail = ids[:-1], ids[-1]
        # associated types: M::Provenance, Self::Provenance, M::T ...
        if len(ids) == 2 and (ids[0] in generics or ids[0] == 'Self') and tail in cfg['assoc_type']:
            return to_ty(cfg['assoc_type'][tail])
        if ids in (['libspecr', 'Name'],):
            return NAME
        if ids in (['libspecr', 'IntDistribution'],):
            return DISTR
        if ids in (['std', 'cmp', 'Ordering'],):
            return ORDERING
        if ids in (['std', 'marker', 'PhantomData'],):
            return UNIT
        if ids == ['std', 'result', 'Result']:
            a = args()
            return ('result', a[1], a[0])
        if ids == ['libspecr', 'NdResult']:
            a = args()
            return ('result', a[1], a[0])
        if ids[:-1] in (['crate', 'lang'], ['crate', 'mem'], ['lang'], ['mem']) and tail in prog.adts:
            return adt(tail)
        raise Refusal('type-path', '::'.join(ids))

    n = ids[0]
    if n in INT_NAMES:
        return INT
    if n == 'bool':
        return BOOL
    if n in ('String', 'str'):
        return STR
    if n == 'Size':
        return SIZE
    if n == 'Align':
        return ALIGN
    if n == 'Name':
        return NAME
    if n == 'DynWrite':
        return DYNWRITE
    if n == 'IntDistribution':
        return DISTR
    if n == 'Ordering':
        return ORDERING
    if n == 'PhantomData':
        return UNIT
    if n == 'List':
        return ('list', args()[0])
    if n == 'Set':
        return ('set', args()[0])
    if n == 'Map':
        a = args()
        return ('map', a[0], a[1])
    if n == 'Option':
        return ('option', args()[0])
    if n in ('Result', 'NdResult'):
        a = args()
        ok = a[0] if a else UNIT
        err = a[1] if len(a) > 1 else adt('TerminationInfo')
        return ('result', err, ok)
    if n == 'Nondet':
        return args()[0]
    if n == 'Self':
        if self_owner is None:
            raise Refusal('Self-outside-impl', '')
        return adt(self_owner)
    if n in generics:
        b = generics[n]
        if b[0] == 'refused':
            raise Refusal('generic-parameter-not-monomorphized', f'{n}: bounds {b[2]}')
        return b[2]
    if n in prog.aliases:
        params, body, _ = prog.aliases[n]
        a = args()
        sub = dict(generics)
        for i, p in enumerate(params):
            if i < len(a):
                sub[p] = ('param', p, a[i])
            else:
                # defaulted alias parameter; aliases with defaults are Result/NdResult (handled above)
                raise Refusal('alias-default-parameter', f'{n}<{p}>')
        return resolve(prog, body, sub, self_owner)
    if n in prog.adts:
        return adt(n)
    raise Refusal('unknown-type', n)


def resolve_fn_bound(prog, bounds, generics, self_owner):
    for b in bounds:
        bk, bv = one_key(b)
        if bk != 'trait':
            continue
        segs = bv['path']['segments']
        name = segs[-1]['ident']
        if name not in ('Fn', 'FnMut', 'FnOnce'):
            continue
        a = segs[-1].get('arguments')
        ak, av = one_key(a)
        if ak != 'parenthesized':
            raise Refusal('fn-trait-arguments', ak)
        params = []
        for inp in av.get('inputs', []):
            ik, iv = one_key(inp)
            is_mut = ik == 'reference' and iv.get('mut')
            params.append((resolve(prog, inp, generics, self_owner), bool(is_mut)))
        out = av.get('output')
        ret = resolve(prog, out, generics, self_owner) if out else UNIT
        return ('fn', tuple(params), ret, None)
    raise Refusal('impl-trait-not-fn', str(bounds)[:80])


def param_ref_kind(j):
    """'mut' for `&mut T`, 'ref' for `&T`, None for by-value."""
    k, v = one_key(j)
    if k == 'reference':
        return 'mut' if v.get('mut') else 'ref'
    return None


def resolve_adts(prog):
    """Fill field/variant types of every ADT."""
    for a in prog.adts.values():
        raw = getattr(a, 'raw', None)
        if raw is None:
            continue
        g = prog.generic_params(raw.get('generics'))
        try:
            if a.kind == 'struct':
                fk, fv = one_key(raw['fields'])
                if fk == 'named':
                    a.fields = [(f['ident'], resolve(prog, f['ty'], g, a.name)) for f in fv]
                elif fk == 'unnamed':
                    a.tuple_struct = True
                    a.fields = [(str(i), resolve(prog, f['ty'], g, a.name)) for i, f in enumerate(fv)]
                else:
                    a.fields = []
            else:
                for var in raw['variants']:
                    fk, fv = one_key(var['fields'])
                    if fk == 'named':
                        a.variants.append((var['ident'], 'named', [(f['ident'], resolve(prog, f['ty'], g, a.name)) for f in fv]))
                    elif fk == 'unnamed':
                        a.variants.append((var['ident'], 'tuple', [(str(i), resolve(prog, f['ty'], g, a.name)) for i, f in enumerate(fv)]))
                    else:
                        a.variants.append((var['ident'], 'unit', []))
        except Refusal as r:
            a.refused = r


def ty_children(t):
    k = t[0]
    if k == 'tuple':
        return list(t[1])
    if k in ('list', 'set', 'option', 'iter'):
        return [t[1]]
    if k in ('map', 'result'):
        return [t[1], t[2]]
    if k == 'fn':
        out = [p for (p, _) in t[1]] + [t[2]]
        if t[3] is not None:
            out.append(t[3])
        return out
    return []


def ty_adts(t, acc):
    if t[0] == 'adt':
        acc.add(t[1])
    for c in ty_children(t):
        ty_adts(c, acc)
    return acc


def adt_field_types(a):
    if a.kind == 'struct':
        return [t for _, t in a.fields]
    return [t for _, _, fs in a.variants for _, t in fs]


def scc(nodes, edges):
    """Tarjan; returns SCCs in reverse topological order of the condensation
    (dependencies first)."""
    index = {}
    low = {}
    on = set()
    stack = []
    out = []
    counter = [0]

    import sys
    sys.setrecursionlimit(100000)

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in edges.get(v, ()):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))

    for v in nodes:
        if v not in index:
            strong(v)
    return out


def adt_groups(prog):
    names = sorted(prog.adts)
    edges = {}
    for n in names:
        a = prog.adts[n]
        acc = set()
        for t in adt_field_types(a):
            ty_adts(t, acc)
        edges[n] = sorted(x for x in acc if x in prog.adts)
    comps = scc(names, edges)
    groups = []
    for c in comps:
        recursive = len(c) > 1 or c[0] in edges.get(c[0], [])
        groups.append((c, recursive))
    return groups, edges
