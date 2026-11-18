"""Collect specr items (ADTs, aliases, traits, impls, functions, constants) from
the front end's JSON AST and resolve types under the monomorphization config."""

from common import *


class ADT:
    def __init__(self, name, kind, file):
        self.name = name
        self.kind = kind            # 'struct' | 'enum'
        self.file = file
        self.fields = []            # struct: [(field_name, Ty)]  (tuple structs use '0', '1', ...)
        self.tuple_struct = False
        self.variants = []          # enum: [(variant_name, style, [(field_name, Ty)])] style in unit|tuple|named
        self.group = None           # recursive group id (None: not recursive)


class FnDef:
    def __init__(self, owner, trait, name, file, generics, inputs, output, stmts, attrs):
        self.owner = owner          # ADT name, or None for free functions
        self.trait = trait          # trait name for trait-impl methods, else None
        self.name = name
        self.file = file
        self.generics = generics    # {param_name: Ty or ('var', name)}
        self.inputs = inputs        # raw JSON inputs
        self.output = output        # raw JSON type or None
        self.stmts = stmts          # raw JSON statements, or None (declaration only)
        self.attrs = attrs
        self.argmatch = None        # parameter name for #[specr::argmatch(..)] declarations
        self.arms = []              # FnDefs merged into an argmatch declaration
        self.self_ty_json = None

    @property
    def lean_name(self):
        # functions live under `MRf.` so a self-reference is never read as
        # dot notation on the type `MR_<Owner>`
        if self.owner is None:
            return f'MRf.fn.{self.name}'
        if self.trait:
            return f'MRf.{self.owner}.{self.trait}.{self.name}'
        return f'MRf.{self.owner}.{self.name}'

    @property
    def display(self):
        if self.owner is None:
            return self.name
        if self.trait:
            return f'<{self.owner} as {self.trait}>::{self.name}'
        return f'{self.owner}::{self.name}'


class ConstDef:
    def __init__(self, owner, trait, name, file, ty_json, expr, generics):
        self.owner, self.trait, self.name, self.file = owner, trait, name, file
        self.ty_json, self.expr, self.generics = ty_json, expr, generics

    @property
    def lean_name(self):
        return f'MRf.{self.owner}.{self.name}' if self.owner else f'MRf.const.{self.name}'


def attr_argmatch(attrs):
    for a in attrs or []:
        k, v = one_key(a['meta'])
        if k == 'list' and path_idents(v['path']) == ['specr', 'argmatch']:
            toks = v['tokens']
            return toks[0]['ident']
    return None


def attr_names(attrs):
    out = []
    for a in attrs or []:
        k, v = one_key(a['meta'])
        p = v['path'] if k in ('list', 'name_value') else v
        if k == 'path':
            p = v
        out.append('::'.join(path_idents(p)))
    return out


class Program:
    def __init__(self, ast, config):
        self.config = config
        self.adts = {}
        self.aliases = {}           # name -> ([(param, default json or None)], json type, file)
        self.traits = {}            # name -> JSON
        self.fns = []               # all FnDef (after argmatch merge, arms are not in this list)
        self.consts = []
        self.refused_items = []     # (item description, construct, detail)
        self.files = []
        self.item_counts = {}
        self._collect(ast)
        self._merge_argmatch()
        self._instantiate_trait_defaults()

    # ---------------------------------------------------------------- collect
    def _collect(self, ast):
        # pass 1: type-level items (so impls in earlier files can name later types)
        for f in ast['files']:
            path = f['path']
            self.files.append((path, f['code_lines']))
            for it in f['ast']['items']:
                k, v = one_key(it)
                self.item_counts[k] = self.item_counts.get(k, 0) + 1
                if k == 'enum':
                    self._enum_raw(v, path)
                elif k == 'struct':
                    self._struct_raw(v, path)
                elif k == 'type':
                    self.aliases[v['ident']] = (type_param_decls(v.get('generics')), v['ty'], path)
                elif k == 'trait':
                    self.traits[v['ident']] = (v, path)
        # pass 2: code
        for f in ast['files']:
            path = f['path']
            for it in f['ast']['items']:
                k, v = one_key(it)
                if k in ('enum', 'struct', 'type', 'trait', 'use'):
                    continue
                if k == 'impl':
                    self._impl(v, path)
                elif k == 'fn':
                    self.fns.append(self._fn(v, None, None, path, {}))
                else:
                    self.refused_items.append((f'{path}: item {k}', 'item-kind', k))

    def _enum_raw(self, v, path):
        a = ADT(v['ident'], 'enum', path)
        a.raw = v
        self.adts[a.name] = a

    def _struct_raw(self, v, path):
        a = ADT(v['ident'], 'struct', path)
        a.raw = v
        self.adts[a.name] = a

    def generic_params(self, generics_json):
        """Map each generic type parameter of an item to its monomorphic
        binding (or to a genuine type variable)."""
        out = {}
        for p in (generics_json or {}).get('params', []):
            pk, pv = one_key(p)
            if pk != 'type':
                continue
            name = pv['ident']
            bounds = []
            for b in pv.get('bounds', []):
                bk, bv = one_key(b)
                if bk == 'trait':
                    bounds.append(path_idents(bv['path'])[-1])
            out[name] = self.bind_generic(name, bounds)
        return out

    def bind_generic(self, name, bounds):
        cfg = self.config['monomorphization']
        for b in bounds:
            if b in cfg['bound']:
                return ('bound', b, to_ty(cfg['bound'][b]))
        if name in cfg['param']:
            return ('param', name, to_ty(cfg['param'][name]))
        if not bounds and name in cfg['polymorphic']:
            return ('poly', name, ('var', name))
        return ('refused', name, bounds)

    def _impl(self, v, path):
        generics = self.generic_params(v.get('generics'))
        trait = None
        if v.get('trait'):
            trait = path_idents(v['trait'][1])[-1]
        sk, sv = one_key(v['self_ty'])
        if sk != 'path':
            self.refused_items.append((f'{path}: impl for {sk}', 'impl-self-type', sk))
            return
        owner_idents = path_idents(sv)
        owner = owner_idents[-1]
        if owner not in self.adts:
            # e.g. `impl<T: DefinedRelation> DefinedRelation for List<T>`
            for item in v['items']:
                ik, iv = one_key(item)
                self.refused_items.append((f'{path}: impl {trait or ""} for {owner}::{iv.get("ident")}',
                                           'impl-on-library-type', f'{owner} (trait {trait})'))
            return
        refusal = self._unconfigured_impl(trait, owner, v['self_ty'], generics)
        if refusal is not None:
            # The monomorphization binds each bound trait to one owner and each ADT to one
            # instance; any other impl would be translated as if it were that one.
            for item in v['items']:
                ik, iv = one_key(item)
                self.refused_items.append((f'{path}: impl {trait or ""} for {owner}::{iv.get("ident")}',
                                           refusal.construct, refusal.detail))
            return
        for item in v['items']:
            ik, iv = one_key(item)
            if ik == 'fn':
                fd = self._fn(iv, owner, trait, path, generics)
                fd.self_ty_json = v['self_ty']
                self.fns.append(fd)
            elif ik == 'const':
                self.consts.append(ConstDef(owner, trait, iv['ident'], path, iv['ty'], iv['expr'], generics))
            elif ik == 'type':
                pass  # associated type definitions are covered by the monomorphization config
            else:
                self.refused_items.append((f'{path}: impl item {ik}', 'impl-item-kind', ik))

    def _unconfigured_impl(self, trait, owner, self_ty_json, generics):
        """The refusal for an impl the monomorphization does not configure, or None.

        (c) an impl of a bound trait (`impl Memory for TreeBorrowsMemory<T>`) whose owner is not
        the configured one (`monomorphization.bound`); (a) an impl whose self type, with its
        declared defaults filled, is not the ADT's configured instance
        (`impl BasicMemory<T, Path, Extra>`): `Self` inside it would mean the configured instance."""
        cfg = self.config['monomorphization']
        if trait in cfg['bound'] and to_ty(cfg['bound'][trait]) != ('adt', owner):
            return Refusal('impl-of-bound-trait-for-unconfigured-owner',
                           f'{trait} for {owner}; the monomorphization binds {trait} to '
                           f'{to_ty(cfg["bound"][trait])[1]}')
        from tyres import resolve  # noqa: PLC0415  (tyres imports this module)
        try:
            resolve(self, self_ty_json, generics, None)
        except Refusal as r:
            return r
        return None

    def trait_assoc_types(self, trait):
        """The associated type names a spec trait declares (`type Provenance;`)."""
        tv, _ = self.traits.get(trait, ({'items': []}, None))
        return {one_key(item)[1]['ident'] for item in tv.get('items', []) if one_key(item)[0] == 'type'}

    def _fn(self, v, owner, trait, path, outer_generics):
        g = dict(outer_generics)
        g.update(self.generic_params(v.get('generics')))
        stmts = v.get('stmts') if 'stmts' in v else v.get('default')
        fd = FnDef(owner, trait, v['ident'], path, g, v.get('inputs', []), v.get('output'), stmts, v.get('attrs'))
        fd.argmatch = attr_argmatch(v.get('attrs'))
        return fd

    # ---------------------------------------------------------------- argmatch
    def _merge_argmatch(self):
        decls = [f for f in self.fns if f.argmatch]
        keep = []
        for f in self.fns:
            if f.argmatch:
                keep.append(f)
                continue
            d = [x for x in decls if x.owner == f.owner and x.trait == f.trait and x.name == f.name]
            if d:
                d[0].arms.append(f)
            else:
                keep.append(f)
        self.fns = keep

    def _instantiate_trait_defaults(self):
        for tname, (tv, path) in self.traits.items():
            impls = {f.owner for f in self.fns if f.trait == tname}
            for item in tv['items']:
                ik, iv = one_key(item)
                if ik != 'fn' or iv.get('default') is None:
                    continue
                for owner in sorted(impls):
                    if any(f.owner == owner and f.trait == tname and f.name == iv['ident'] for f in self.fns):
                        continue
                    g = self.generic_params(tv.get('generics'))
                    fd = self._fn(iv, owner, tname, path, g)
                    fd.default_of_trait = tname
                    self.fns.append(fd)

    def find_fn(self, owner, name, trait=None, prefer_trait=None):
        cands = [f for f in self.fns if f.owner == owner and f.name == name]
        if trait is not None:
            cands = [f for f in cands if f.trait == trait]
        if prefer_trait:
            t = [f for f in cands if f.trait == prefer_trait]
            if t:
                return t[0]
        inh = [f for f in cands if f.trait is None]
        if inh:
            return inh[0]
        if len(cands) == 1:
            return cands[0]
        if len(cands) > 1:
            raise Refusal('ambiguous-method', f'{owner}::{name}: {[c.trait for c in cands]}')
        return None

    def find_const(self, owner, name):
        for c in self.consts:
            if c.owner == owner and c.name == name:
                return c
        return None


def type_param_decls(generics_json):
    """An item's type parameters in order, each with its declared default JSON type or None
    (syn's `TypeParam.default`: `struct Allocation<ProvExtra = (), AllocExtra = ()>`)."""
    out = []
    for p in (generics_json or {}).get('params', []):
        pk, pv = one_key(p)
        if pk == 'type':
            out.append((pv['ident'], pv.get('default')))
    return out


def to_ty(j):
    """Config types are written as JSON lists, e.g. ["tuple", [["adt","AllocId"],["unit"]]]."""
    if isinstance(j, list):
        if j[0] == 'tuple':
            return ('tuple', tuple(to_ty(x) for x in j[1]))
        return tuple([j[0]] + [to_ty(x) if isinstance(x, list) else x for x in j[1:]])
    return j
