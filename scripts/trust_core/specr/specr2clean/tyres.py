"""Resolve syn type JSON to translator types under the monomorphization config."""

from common import *
from items import to_ty, type_param_decls

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
        return qualified_assoc_type(prog, v, generics, self_owner)
    segs = v['segments']
    ids = [s['ident'] for s in segs]
    last = segs[-1]
    args = lambda: [resolve(prog, a, generics, self_owner) for a in path_generic_args(last)]
    cfg = prog.config['monomorphization']

    if len(ids) >= 2:
        head, tail = ids[:-1], ids[-1]
        # associated types: M::Provenance, Self::Provenance, M::T ...
        if len(ids) == 2 and (ids[0] in generics or ids[0] == 'Self') and tail in cfg['assoc_type']:
            configured_assoc_type(prog, ids[0], tail, generics, self_owner)
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
            return adt_ref(prog, tail, last, generics, self_owner)
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
        sub = dict(generics)
        for p, t in zip(params, fill_type_args(prog, f'type alias {n}', params, args(), generics, self_owner)):
            sub[p[0]] = ('param', p[0], t)
        return resolve(prog, body, sub, self_owner)
    if n in prog.adts:
        return adt_ref(prog, n, last, generics, self_owner)
    raise Refusal('unknown-type', n)


def fill_type_args(prog, what, params, given, generics, self_owner):
    """`given` (resolved) followed by the declared default of every parameter it leaves out, each
    default resolved with the earlier parameters bound to their arguments (Rust's rule:
    `struct S<A, B = A>` makes `S<X>` mean `S<X, X>`). A missing argument with no default and a
    surplus argument are refused."""
    if len(given) > len(params):
        raise Refusal('type-argument-count', f'{what} takes {len(params)}, given {len(given)}')
    filled = list(given)
    sub = dict(generics)
    for i, (p, default) in enumerate(params):
        if i >= len(filled):
            if default is None:
                raise Refusal('missing-type-argument', f'{what}: <{p}> has no default')
            filled.append(resolve(prog, default, sub, self_owner))
        sub[p] = ('param', p, filled[i])
    return filled


def adt_ref(prog, n, seg, generics, self_owner):
    """A reference to the spec ADT `n` with the type arguments of the path segment `seg`.

    The translator emits one monomorphic `MR_<n>`: the ADT at its configured instance, each
    parameter bound by the monomorphization (`items.Program.bind_generic`). A reference whose
    arguments, with declared defaults filled, are another instance would be emitted as that one,
    so it is refused (`BasicMemory<T, Path, TreeBorrowsAllocationExtra>` against
    `BasicMemory<x86_64, (), ()>`)."""
    a = prog.adts[n]
    raw = getattr(a, 'raw', None)
    gj = (raw.get('generics') if raw else None) or {}
    for p in gj.get('params', []):
        pk, _ = one_key(p)
        if pk != 'type':
            raise Refusal('adt-non-type-parameter', f'{n}: {pk}')
    params = type_param_decls(gj)
    given = [resolve(prog, x, generics, self_owner) for x in path_generic_args(seg)]
    inst = prog.generic_params(gj) if raw else {}
    want = []
    for p, _ in params:
        b = inst[p]
        if b[0] == 'refused':
            raise Refusal('adt-instance-not-configured', f'{n}<{p}>: bounds {b[2]} are not monomorphized')
        want.append(b[2])
    # the defaults are resolved in the ADT's own scope: its parameters, not the referencing item's
    filled = fill_type_args(prog, n, params, given, inst, n)
    if filled != want:
        raise Refusal('adt-instance-not-configured',
                      f'{n}<{", ".join(show_ty(t) for t in filled)}> is not the configured '
                      f'{n}<{", ".join(show_ty(t) for t in want)}>')
    return adt(n)


def qualified_assoc_type(prog, v, generics, self_owner):
    """`<G as Trait>::X`, an associated type named through its trait: the configured impl's type,
    under configured_assoc_type's rule for `G::X`, and only when `Trait` is a trait `G` is bound to
    there. Every other qualified-self type is refused."""
    q, segs = v['qself'], v['segments']
    qk, qv = one_key(q['ty'])
    simple = (qk == 'path' and not qv.get('qself') and len(qv['segments']) == 1
              and not qv['segments'][0].get('arguments') and q.get('position') == 1 and len(segs) == 2
              and not any(sg.get('arguments') for sg in segs))
    cfg = prog.config['monomorphization']
    if simple:
        head, trait, name = qv['segments'][0]['ident'], segs[0]['ident'], segs[1]['ident']
        if (head in generics or head == 'Self') and name in cfg['assoc_type']:
            configured_assoc_type(prog, head, name, generics, self_owner, trait=trait)
            return to_ty(cfg['assoc_type'][name])
    raise Refusal('qualified-self-type', str(v)[:80])


def configured_assoc_type(prog, head, name, generics, self_owner, trait=None):
    """`monomorphization.assoc_type` holds the associated types of the configured impl of each
    bound trait (`impl Memory for BasicMemory<T>`). `M::X` reads it only when `M` is bound to that
    trait, and `Self::X` only inside an impl whose owner is that trait's configured owner; any other
    `Self::X` (`Self::Provenance` in `impl TreeBorrowsMemory<T>`) or `M::X` names another impl's
    type and is refused."""
    cfg = prog.config['monomorphization']
    if head == 'Self':
        traits = [t for t, ty in sorted(cfg['bound'].items())
                  if self_owner is not None and to_ty(ty) == adt(self_owner)]
    else:
        b = generics[head]
        traits = [b[1]] if b[0] == 'bound' else []
    traits = [t for t in traits if name in prog.trait_assoc_types(t) and trait in (None, t)]
    if len(traits) != 1:
        where = f'impl for {self_owner}' if head == 'Self' else f'{head}: {generics[head][0]}'
        named = f'<{head} as {trait}>::{name}' if trait else f'{head}::{name}'
        raise Refusal('associated-type-outside-configured-impl', f'{named} ({where})')


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
