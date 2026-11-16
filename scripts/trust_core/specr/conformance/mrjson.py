"""MiniRust program JSON (serde of minirust-rs) -> constructor census and Clean terms.

The JSON layout is serde's default for the types specr-transpile generates:
unit variants are strings, other variants single-key objects (a one-field tuple
variant holds the value, several fields a list, named fields an object);
newtype structs are transparent; libspecr `Map` is a list of `[key, value]`
pairs, `List`/`Set` are lists, `Option` is `null` or the value, `Int`,
`Size`, `Align` and `Name` are numbers.
"""


def ty(t):
    """schema types are JSON lists; turn them into tuples"""
    if isinstance(t, list):
        if t and t[0] == 'tuple':
            return ('tuple', tuple(ty(x) for x in t[1]))
        return tuple(ty(x) if isinstance(x, list) else x for x in t)
    return t


class Walker:
    def __init__(self, schema):
        self.schema = schema

    def adt(self, name):
        return self.schema[name]

    def walk(self, v, t, visit):
        """visit(adt_name, variant_name, value) for every ADT value."""
        k = t[0]
        if k in ('int', 'size', 'align', 'name', 'bool', 'str', 'unit'):
            return
        if k in ('list', 'set'):
            for x in v:
                self.walk(x, t[1], visit)
            return
        if k == 'map':
            for kv in v:
                self.walk(kv[0], t[1], visit)
                self.walk(kv[1], t[2], visit)
            return
        if k == 'option':
            if v is not None:
                self.walk(v, t[1], visit)
            return
        if k == 'tuple':
            for x, xt in zip(v, t[1]):
                self.walk(x, xt, visit)
            return
        if k == 'adt':
            a = self.adt(t[1])
            if a['kind'] == 'enum':
                vname, payload = (v, None) if isinstance(v, str) else next(iter(v.items()))
                visit(t[1], vname, payload)
                for fv, (fname, ft) in self.variant_fields(t[1], vname, payload):
                    self.walk(fv, ty(ft), visit)
            else:
                visit(t[1], None, v)
                for fv, (fname, ft) in self.struct_fields(t[1], v):
                    self.walk(fv, ty(ft), visit)
            return
        raise ValueError(f'type {t}')

    def variant_fields(self, name, vname, payload):
        a = self.adt(name)
        for vn, style, fields in a['variants']:
            if vn == vname:
                if style == 'unit':
                    return []
                if style == 'named':
                    return [(payload[f], (f, ft)) for f, ft in fields]
                if len(fields) == 1:
                    return [(payload, tuple(fields[0]))]
                return list(zip(payload, [tuple(f) for f in fields]))
        raise ValueError(f'{name}::{vname}')

    def struct_fields(self, name, v):
        a = self.adt(name)
        fields = a['fields']
        if a['tuple_struct']:
            if len(fields) == 1:
                return [(v, tuple(fields[0]))]
            return list(zip(v, [tuple(f) for f in fields]))
        if not fields:
            return []
        return [(v[f], (f, ft)) for f, ft in fields]


def lean_int(n):
    # Clean's numeral elaboration refuses `(-N : Int)` for N beyond the u128
    # range (measured 2026-09-17: i128::MIN fails with `Neg Nat`), so negatives
    # are written with the constructor.
    return f'({n} : Int)' if n >= 0 else f'(Int.negSucc {-n - 1})'


def lean_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'


class ToLean(Walker):
    def type_text(self, t, arg=False):
        k = t[0]
        base = {'int': 'Int', 'size': 'Int', 'align': 'Int', 'name': 'Nat', 'bool': 'Bool', 'str': 'String', 'unit': 'Unit'}
        if k in base:
            return base[k]
        if k == 'adt':
            return 'MR_' + t[1]
        if k in ('list', 'set'):
            s = f'List {self.type_text(t[1], True)}'
        elif k == 'map':
            s = f'List ({self.type_text(t[1])} × {self.type_text(t[2])})'
        elif k == 'option':
            s = f'Option {self.type_text(t[1], True)}'
        elif k == 'tuple':
            s = ' × '.join(self.type_text(x, True) for x in t[1])
        else:
            raise ValueError(t)
        return f'({s})' if arg else s

    def term(self, v, t):
        k = t[0]
        if k in ('int', 'size', 'align'):
            return lean_int(int(v))
        if k == 'name':
            return f'({int(v)} : Nat)'
        if k == 'bool':
            return 'true' if v else 'false'
        if k == 'str':
            return lean_str(v)
        if k == 'unit':
            return '()'
        if k in ('list', 'set'):
            if not v:
                return f'([] : {self.type_text(t)})'
            return '[' + ', '.join(self.term(x, t[1]) for x in v) + ']'
        if k == 'map':
            if not v:
                return f'([] : {self.type_text(t)})'
            return '[' + ', '.join(f'({self.term(kv[0], t[1])}, {self.term(kv[1], t[2])})' for kv in v) + ']'
        if k == 'option':
            if v is None:
                return f'(none : {self.type_text(t)})'
            return f'(some {self.term(v, t[1])})'
        if k == 'tuple':
            return '(' + ', '.join(self.term(x, xt) for x, xt in zip(v, t[1])) + ')'
        if k == 'adt':
            a = self.adt(t[1])
            if a['kind'] == 'enum':
                vname, payload = (v, None) if isinstance(v, str) else next(iter(v.items()))
                args = [self.term(fv, ty(ft)) for fv, (fname, ft) in self.variant_fields(t[1], vname, payload)]
                head = f'MR_{t[1]}.{vname}'
            else:
                args = [self.term(fv, ty(ft)) for fv, (fname, ft) in self.struct_fields(t[1], v)]
                head = f'MR_{t[1]}.mk'
            return f'({head}' + ''.join(' ' + x for x in args) + ')' if args else head
        raise ValueError(t)
