"""Shared helpers for the specr -> Clean translator (K8 probe).

Types are plain tuples so they can be compared and hashed:

  ('int',) ('bool',) ('str',) ('unit',) ('never',) ('size',) ('align',)
  ('name',) ('ordering',) ('distr',) ('dynwrite',)
  ('adt', Name)                      spec struct/enum, monomorphic
  ('tuple', (t1, ..., tn))           n >= 2
  ('list', t) ('map', k, v) ('set', t) ('option', t) ('iter', t)
  ('result', err, ok)
  ('fn', ((t, is_mut_ref), ...), ret, sigma)   closure / impl Fn*; sigma is the
                                    type of the hidden state the closure threads
  ('var', 'O')                       a genuine generic type parameter
"""

import itertools
import re

INT = ('int',)
BOOL = ('bool',)
STR = ('str',)
UNIT = ('unit',)
NEVER = ('never',)
SIZE = ('size',)
ALIGN = ('align',)
NAME = ('name',)
ORDERING = ('ordering',)
DISTR = ('distr',)
DYNWRITE = ('dynwrite',)


class Refusal(Exception):
    """A construct the translator does not support. `construct` is the stable
    name counted in the census; `detail` is free text."""

    def __init__(self, construct, detail=''):
        super().__init__(f'{construct}: {detail}')
        self.construct = construct
        self.detail = detail


def adt(n):
    return ('adt', n)


def tuple_ty(ts):
    ts = tuple(ts)
    if len(ts) == 0:
        return UNIT
    if len(ts) == 1:
        return ts[0]
    return ('tuple', ts)


def is_intlike(t):
    return t in (INT, SIZE, ALIGN)


LEAN_KEYWORDS = {
    'at', 'by', 'do', 'else', 'end', 'fun', 'have', 'if', 'in', 'let', 'match',
    'then', 'with', 'from', 'show', 'open', 'namespace', 'section', 'where',
    'deriving', 'instance', 'structure', 'class', 'theorem', 'def', 'mut',
    'return', 'for', 'unless', 'try', 'catch', 'finally', 'break', 'continue',
    'macro', 'syntax', 'local', 'private', 'protected', 'partial', 'unsafe',
    'variable', 'universe', 'export', 'import', 'prefix', 'infix', 'notation',
    'Type', 'Sort', 'Prop', 'forall', 'exists', 'calc', 'suffices', 'obtain',
    'inductive', 'abbrev', 'axiom', 'example', 'mutual', 'nomatch', 'termination_by',
    'decreasing_by', 'this', 'set_option', 'attribute', 'opaque',
}


def lean_field(name):
    """A structure field or constructor argument name."""
    if name in LEAN_KEYWORDS:
        return f'«{name}»'
    if name[0].isdigit():
        return f'f{name}'
    return name


def lean_type(t, ctx='top'):
    """Clean type text. `ctx` is where the text is placed: 'top', 'domain'
    (left of an arrow), 'arg' (argument of a type constructor), 'left' (left
    operand of ×). Clean's parser reads a parenthesised application followed
    by an arrow, e.g. `(List Int) → Int`, as a binder, so applications are only
    parenthesised where they are arguments."""
    k = t[0]
    if k in ('int', 'size', 'align'):
        return 'Int'
    if k == 'bool':
        return 'Bool'
    if k == 'str':
        return 'String'
    if k in ('unit', 'never', 'dynwrite'):
        return 'Unit'
    if k == 'name':
        return 'Nat'
    if k == 'ordering':
        return 'SOrdering'
    if k == 'distr':
        return 'SIntDistribution'
    if k == 'adt':
        return 'MR_' + t[1]
    if k == 'var':
        return t[1]

    def app(text):
        return f'({text})' if ctx == 'arg' else text
    if k == 'tuple':
        parts = list(t[1])
        text = ' × '.join([lean_type(x, 'left') for x in parts[:-1]] + [lean_type(parts[-1], 'right')])
        return f'({text})' if ctx in ('arg', 'left') else text
    if k in ('list', 'set', 'iter'):
        return app(f'List {lean_type(t[1], "arg")}')
    if k == 'map':
        return app(f'List {lean_type(("tuple", (t[1], t[2])), "arg")}')
    if k == 'option':
        return app(f'Option {lean_type(t[1], "arg")}')
    if k == 'result':
        return app(f'SRes {lean_type(t[1], "arg")} {lean_type(t[2], "arg")}')
    if k == 'fn':
        params, ret, sigma = t[1], t[2], t[3]
        outs = [ret] + [p for (p, m) in params if m] + [sigma]
        text = ' → '.join([lean_type(p, 'domain') for (p, _) in params] + [lean_type(sigma, 'domain')]
                          + [f'SOut {lean_type(tuple_ty(outs), "arg")}'])
        return text if ctx == 'top' else f'({text})'
    raise Refusal('type-not-representable', repr(t))


def arrow_type(domains, result_text):
    """`D1 → ... → R` from translator types and a result type text."""
    return ' → '.join([lean_type(d, 'domain') for d in domains] + [result_text])


def show_ty(t):
    """Human-readable spelling, for reports."""
    k = t[0]
    if k == 'adt':
        return t[1]
    if k == 'tuple':
        return '(' + ', '.join(show_ty(x) for x in t[1]) + ')'
    if len(t) == 1:
        return k
    return k + '<' + ', '.join(show_ty(x) if isinstance(x, tuple) and x and isinstance(x[0], str) else str(x) for x in t[1:]) + '>'


# ---------------------------------------------------------------------------
# syn-serde JSON helpers

def one_key(node):
    """syn-serde encodes enums as single-key dicts (or bare strings for unit
    variants). Return (kind, payload)."""
    if isinstance(node, str):
        return node, None
    assert isinstance(node, dict) and len(node) >= 1, node
    if len(node) != 1:
        raise ValueError(f'not a single-key node: {list(node)}')
    k = next(iter(node))
    return k, node[k]


def path_idents(path):
    return [s['ident'] for s in path['segments']]


def path_generic_args(seg):
    """The angle-bracketed type arguments of one path segment (list of JSON types)."""
    a = seg.get('arguments')
    if not a:
        return []
    k, v = one_key(a)
    if k != 'angle_bracketed':
        raise Refusal('parenthesized-path-arguments', str(a)[:80])
    out = []
    for arg in v['args']:
        ak, av = one_key(arg)
        if ak == 'type':
            out.append(av)
        else:
            raise Refusal('non-type-generic-argument', ak)
    return out


def lit_value(lit):
    k, v = one_key(lit)
    if k == 'int':
        s = v.replace('_', '')
        for suf in ('u8', 'u16', 'u32', 'u64', 'u128', 'usize', 'i8', 'i16', 'i32', 'i64', 'i128', 'isize'):
            if s.endswith(suf):
                s = s[: -len(suf)]
                break
        if s.startswith('0b'):
            return 'int', int(s[2:], 2)
        if s.startswith('0x'):
            return 'int', int(s[2:], 16)
        return 'int', int(s)
    if k == 'bool':
        return 'bool', v
    if k == 'str':
        # syn-serde stores the literal's source text including quotes
        import ast as pyast
        return 'str', pyast.literal_eval(v)
    raise Refusal('literal-kind', k)


def lean_string(s):
    out = ['"']
    for ch in s:
        if ch == '"':
            out.append('\\"')
        elif ch == '\\':
            out.append('\\\\')
        elif ch == '\n':
            out.append('\\n')
        else:
            out.append(ch)
    out.append('"')
    return ''.join(out)


def lean_int(n):
    # Clean's numeral elaboration refuses `(-N : Int)` for N beyond the u128
    # range (measured 2026-09-17: i128::MIN fails with `Neg Nat`), so negatives
    # are written with the constructor.
    return f'({n} : Int)' if n >= 0 else f'(Int.negSucc {-n - 1})'


_counter = itertools.count()


def fresh(base):
    base = ''.join(c if (c.isalnum() or c == '_') else '_' for c in base) or 'x'
    if base[0].isdigit():
        base = 'v' + base
    return f'{base}_{next(_counter)}'


def reset_fresh():
    global _counter
    _counter = itertools.count()


_DECL_HEAD = re.compile(r'(?:def|theorem|abbrev|instance)\s+([A-Za-z_][\w]*)\.')
_INDUCTIVE_HEAD = re.compile(r'(?:inductive|structure)\s+([A-Za-z_][\w]*)\s')
_CTOR_LINE = re.compile(r'\s+\|\s+([A-Za-z_][\w]*)')


def qualify_shadowed(text):
    """Lean 4 opens the namespace `N` inside the body of `def N.f`, so a bare `Int` in
    `def MR_Type.beq` names the constructor `MR_Type.Int`, not the type (Clean's
    elaborator does not open it; both accept `_root_.Int`). The translator always writes
    constructors qualified, so in the body of a declaration `N.f` every bare token that is
    a constructor name of the emitted inductive `N` means the root name and is written
    `_root_.<token>` (string literals are left alone). This makes the slice elaborate
    under the pinned Lean 4.30 too, where Clean's reference entry re-checks it."""
    lines = text.split('\n')
    ctors: dict[str, set[str]] = {}
    current = None
    for line in lines:
        m = _INDUCTIVE_HEAD.match(line)
        if m:
            current = m.group(1)
            ctors.setdefault(current, set())
            continue
        if current is not None:
            c = _CTOR_LINE.match(line)
            if c:
                ctors[current].add(c.group(1))
                continue
            if line and not line[0].isspace():
                current = None
    out = []
    names: set[str] = set()
    for line in lines:
        if line and not line[0].isspace():
            m = _DECL_HEAD.match(line)
            names = ctors.get(m.group(1), set()) if m else set()
        out.append(_qualify_line(line, names) if names else line)
    return '\n'.join(out)


def _qualify_line(line, names):
    res = []
    i, n = 0, len(line)
    while i < n:
        ch = line[i]
        if ch == '"':  # a string literal, with backslash escapes
            j = i + 1
            while j < n and line[j] != '"':
                j += 2 if line[j] == '\\' else 1
            res.append(line[i:j + 1])
            i = j + 1
            continue
        if ch.isalpha() or ch == '_':
            j = i
            while j < n and (line[j].isalnum() or line[j] in '_\'!?'):
                j += 1
            tok = line[i:j]
            prev = line[i - 1] if i > 0 else ' '
            if tok in names and prev not in '.«':
                tok = '_root_.' + tok
            res.append(tok)
            i = j
            continue
        res.append(ch)
        i += 1
    return ''.join(res)
