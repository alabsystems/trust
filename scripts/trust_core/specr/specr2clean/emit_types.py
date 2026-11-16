"""Emit Clean declarations for specr ADTs: inductives/structures, projections,
setters and Boolean equality functions."""

from common import *
from tyres import adt_groups, adt_field_types, ty_adts


class TypeInfo:
    """Facts about emitted types that the function lowering consults."""

    def __init__(self, prog):
        self.prog = prog
        self.groups, self.edges = adt_groups(prog)
        self.recursive = set()
        self.encoded_as_inductive = set()   # structs emitted as single-constructor inductives
        for comp, rec in self.groups:
            if rec:
                self.recursive.update(comp)
        for comp, rec in self.groups:
            if rec:
                for n in comp:
                    if prog.adts[n].kind == 'struct':
                        self.encoded_as_inductive.add(n)
        # Is the Boolean equality of this ADT monadic (needs fuel)?  Recursive
        # ADTs, and ADTs that contain one, compare in SOut.
        self.beq_monadic = {}
        for comp, rec in self.groups:  # dependencies first
            for n in comp:
                self.beq_monadic[n] = rec or any(self.ty_eq_monadic(t) for t in adt_field_types(prog.adts[n]))

    def ty_eq_monadic(self, t):
        k = t[0]
        if k == 'adt':
            return self.beq_monadic.get(t[1], t[1] in self.recursive)
        if k == 'fn':
            return False
        from tyres import ty_children
        return any(self.ty_eq_monadic(c) for c in ty_children(t))

    # -- equality expressions ------------------------------------------------
    def eq_pure(self, t):
        """A Lean term `α → α → Bool` for a type whose equality is pure."""
        k = t[0]
        if k in ('int', 'size', 'align'):
            return 'SInt.beq'
        if k == 'bool':
            return 'SBool.beq'
        if k == 'str':
            return 'SString.beq'
        if k == 'name':
            return 'Nat.beq'
        if k in ('unit', 'never', 'dynwrite'):
            return '(fun (_ _ : Unit) => true)'
        if k == 'ordering':
            return 'SOrdering.beq'
        if k == 'adt':
            return f'MR_{t[1]}.beq'
        if k == 'tuple':
            xs = [fresh('a') for _ in t[1]]
            ys = [fresh('b') for _ in t[1]]
            conj = ' && '.join(f'({self.eq_pure(c)} {x} {y})' for c, x, y in zip(t[1], xs, ys))
            return (f'(fun (p q : {lean_type(t)}) => match p with | ({", ".join(xs)}) => '
                    f'match q with | ({", ".join(ys)}) => {conj})')
        if k in ('list', 'iter'):
            return f'(SList.beq {self.eq_pure(t[1])})'
        if k == 'set':
            return f'(SSet.beq {self.eq_pure(t[1])})'
        if k == 'option':
            return f'(SOption.beq {self.eq_pure(t[1])})'
        if k == 'map':
            return f'(SMap.beq {self.eq_pure(t[1])} {self.eq_pure(t[2])})'
        if k == 'result':
            return f'(SRes.beq {self.eq_pure(t[1])} {self.eq_pure(t[2])})'
        raise Refusal('equality-on-type', show_ty(t))

    def eq_monadic(self, t, fuel):
        """A Lean term `α → α → SOut Bool`."""
        if not self.ty_eq_monadic(t):
            return f'(fun (x y : {lean_type(t)}) => SOut.ok ({self.eq_pure(t)} x y))'
        k = t[0]
        if k == 'adt':
            return f'(MR_{t[1]}.beq {fuel})'
        if k == 'tuple':
            xs = [fresh('a') for _ in t[1]]
            ys = [fresh('b') for _ in t[1]]
            body = 'SOut.ok true'
            for c, x, y in reversed(list(zip(t[1], xs, ys))):
                body = f'SOut.bind (α := Bool) (β := Bool) ({self.eq_monadic(c, fuel)} {x} {y}) (fun (e : Bool) => if e then {body} else SOut.ok false)'
            return (f'(fun (p q : {lean_type(t)}) => match p with | ({", ".join(xs)}) => '
                    f'match q with | ({", ".join(ys)}) => {body})')
        if k in ('list', 'iter'):
            return f'(SList.beqM {self.eq_monadic(t[1], fuel)})'
        if k == 'set':
            return f'(SSet.beqM {self.eq_monadic(t[1], fuel)})'
        if k == 'option':
            return f'(SOption.beqM {self.eq_monadic(t[1], fuel)})'
        if k == 'map':
            return f'(SMap.beqM {self.eq_pure(t[1])} {self.eq_monadic(t[2], fuel)})'
        if k == 'result':
            return f'(SRes.beqM {self.eq_monadic(t[1], fuel)} {self.eq_monadic(t[2], fuel)})'
        raise Refusal('equality-on-type', show_ty(t))


def ctor_args(fields):
    return ' '.join(f'({lean_field(fname if not fname.isdigit() else "f" + fname)} : {lean_type(t)})' for fname, t in fields)


def field_lean_name(fname):
    return lean_field('f' + fname if fname.isdigit() else fname)


def emit_adt_decl(a, inductive_struct):
    lines = []
    if a.kind == 'enum':
        lines.append(f'inductive MR_{a.name} where')
        if not a.variants:
            # uninhabited enum
            pass
        for vname, style, fields in a.variants:
            args = ctor_args(fields)
            lines.append(f'  | {vname}' + (f' {args}' if args else ''))
        return lines
    if inductive_struct or not a.fields:
        lines.append(f'inductive MR_{a.name} where')
        args = ctor_args(a.fields)
        lines.append('  | mk' + (f' {args}' if args else ''))
        return lines
    lines.append(f'structure MR_{a.name} where')
    for fname, t in a.fields:
        lines.append(f'  {field_lean_name(fname)} : {lean_type(t)}')
    return lines


def emit_struct_accessors(a, inductive_struct):
    """Projection (for inductive-encoded structs) and setter functions."""
    lines = []
    names = [fresh('x') for _ in a.fields]
    pat = f'MR_{a.name}.mk ' + ' '.join(names) if names else f'MR_{a.name}.mk'
    for i, (fname, t) in enumerate(a.fields):
        fl = field_lean_name(fname)
        if inductive_struct or not a.fields:
            lines.append(f'def MR_{a.name}.{fl} (s : MR_{a.name}) : {lean_type(t)} :=')
            lines.append(f'  match s with | {pat} => {names[i]}')
        newargs = ' '.join('v' if j == i else n for j, n in enumerate(names))
        lines.append(f'def MR_{a.name}.set_{fname if not fname.isdigit() else "f" + fname} (s : MR_{a.name}) (v : {lean_type(t)}) : MR_{a.name} :=')
        lines.append(f'  match s with | {pat} => MR_{a.name}.mk {newargs}')
    return lines


def emit_beq(tinfo, a):
    """Boolean structural equality (derived PartialEq)."""
    monadic = tinfo.beq_monadic[a.name]
    lines = []
    if a.kind == 'struct':
        cases = [('mk', a.fields)]
    else:
        cases = [(v, fs) for v, _, fs in a.variants]
    arms = []
    for cname, fields in cases:
        xs = [fresh('x') for _ in fields]
        ys = [fresh('y') for _ in fields]
        lp = f'MR_{a.name}.{cname}' + ''.join(' ' + x for x in xs)
        rp = f'MR_{a.name}.{cname}' + ''.join(' ' + y for y in ys)
        if monadic:
            body = 'SOut.ok true'
            for (fname, t), x, y in reversed(list(zip(fields, xs, ys))):
                body = f'SOut.bind (α := Bool) (β := Bool) ({tinfo.eq_monadic(t, "fuel")} {x} {y}) (fun (e : Bool) => if e then {body} else SOut.ok false)'
            fail = 'SOut.ok false'
        else:
            body = ' && '.join(f'({tinfo.eq_pure(t)} {x} {y})' for (fname, t), x, y in zip(fields, xs, ys)) or 'true'
            fail = 'false'
        if len(cases) > 1:
            arms.append(f'  | {lp} => (match b with | {rp} => {body} | _ => {fail})')
        else:
            arms.append(f'  | {lp} => (match b with | {rp} => {body})')
    if not cases:
        arms.append('')
    return arms, monadic


def emit_types(prog, tinfo, out, skip=lambda a: False):
    for comp, rec in tinfo.groups:
        adts = [prog.adts[n] for n in comp if not skip(prog.adts[n])]
        if not adts:
            continue
        for a in adts:
            if getattr(a, 'refused', None):
                raise Refusal('adt-field-type', f'{a.name}: {a.refused}')
        if rec:
            out.append('mutual')
        for a in adts:
            out.extend(emit_adt_decl(a, rec and a.kind == 'struct'))
        if rec:
            out.append('end')
        out.append('')
        for a in adts:
            if a.kind == 'struct':
                out.extend(emit_struct_accessors(a, rec))
        out.append('')

    # derived `Debug` for `{:?}` in messages
    for comp, rec in tinfo.groups:
        adts = [prog.adts[n] for n in comp if not skip(prog.adts[n])]
        if adts:
            emit_debug_group(tinfo, adts, rec, out)

    # Debug names of fieldless enums (for `{:?}` in messages)
    for comp, rec in tinfo.groups:
        for n in comp:
            a = prog.adts[n]
            if skip(a) or a.kind != 'enum' or not a.variants or not all(st == 'unit' for _, st, _ in a.variants):
                continue
            out.append(f'def MR_{a.name}.debugName (a : MR_{a.name}) : String :=')
            out.append('  match a with' + ''.join(f' | MR_{a.name}.{v} => {lean_string(v)}' for v, _, _ in a.variants))
            out.append('')

    # equality: pure ones first in dependency order, then monadic groups
    for comp, rec in tinfo.groups:
        adts = [prog.adts[n] for n in comp if not skip(prog.adts[n])]
        if not adts:
            continue
        if not any(tinfo.beq_monadic[a.name] for a in adts):
            for a in adts:
                arms, _ = emit_beq(tinfo, a)
                out.append(f'def MR_{a.name}.beq (a b : MR_{a.name}) : Bool :=')
                if arms == ['']:
                    out.append('  true')
                else:
                    out.append('  match a with')
                    out.extend(arms)
                out.append('')
            continue
        # monadic equality: fuel-indexed; recursive groups are tied through a record
        names = [a.name for a in adts]
        if not rec:
            for a in adts:
                arms, _ = emit_beq(tinfo, a)
                out.append(f'def MR_{a.name}.beq (fuel : Nat) (a b : MR_{a.name}) : SOut Bool :=')
                out.append('  match fuel with')
                out.append('  | 0 => SOut.fuel')
                out.append('  | fuel + 1 =>')
                out.append('  match a with')
                out.extend(arms)
                out.append('')
            continue
        rec_name = 'MR_beqRec_' + '_'.join(names)
        out.append(f'structure {rec_name} where')
        for n in names:
            out.append(f'  beq_{n} : Nat → MR_{n} → MR_{n} → SOut Bool')
        out.append('')
        for a in adts:
            arms, _ = emit_beq(tinfo, a)
            body = '\n'.join(arms)
            # inside the group, recursive calls go through the record
            for n in names:
                body = body.replace(f'(MR_{n}.beq fuel)', f'(r.beq_{n} fuel)')
            out.append(f'def MR_{a.name}.beq_open (r : {rec_name}) (fuel : Nat) (a b : MR_{a.name}) : SOut Bool :=')
            out.append('  match fuel with')
            out.append('  | 0 => SOut.fuel')
            out.append('  | fuel + 1 =>')
            out.append('  match a with')
            out.append(body)
            out.append('')
        out.append(f'def {rec_name}.tie : Nat → {rec_name}')
        out.append(f'  | 0 => {rec_name}.mk ' + ' '.join(f'(fun (_ : Nat) (_ _ : MR_{n}) => (SOut.fuel : SOut Bool))' for n in names))
        out.append(f'  | n + 1 => {rec_name}.mk ' + ' '.join(f'(MR_{n}.beq_open ({rec_name}.tie n))' for n in names))
        out.append('')
        for n in names:
            out.append(f'def MR_{n}.beq (fuel : Nat) (a b : MR_{n}) : SOut Bool := ({rec_name}.tie fuel).beq_{n} fuel a b')
        out.append('')


# ---------------------------------------------------------------------------
# derived Debug (`{:?}`): the structural rendering `#[derive(Debug)]` produces.
# libspecr's `Map`/`Set` are hash containers whose iteration order — and hence
# whose `Debug` text — is unspecified, so those are refused where they occur
# rather than rendered in an order the reference would not reproduce.

def debug_expr(tinfo, t, atom, fuel):
    """A Lean term of type `SOut String` rendering `atom` the way Rust's
    derived `Debug` renders a value of specr type `t`."""
    k = t[0]
    if k == 'int':
        return f'(SOut.ok (SInt.toString {atom}))'
    if k == 'size':
        return f'(SOut.ok (SDebug.size {atom}))'
    if k == 'align':
        return f'(SOut.ok (SDebug.align {atom}))'
    if k == 'bool':
        return f'(SOut.ok (SBool.toString {atom}))'
    if k == 'str':
        return f'(SOut.ok (SDebug.str {atom}))'
    if k == 'name':
        return f'(SOut.ok (SDebug.name {atom}))'
    if k == 'unit':
        return '(SOut.ok "()")'
    if k == 'ordering':
        return f'(SOut.ok (SDebug.ordering {atom}))'
    if k == 'adt':
        return f'(MR_{t[1]}.debugStr {fuel} {atom})'
    if k == 'option':
        inner = fresh('d')
        return (f'(SDebug.option (α := {lean_type(t[1], "arg")}) '
                f'(fun ({inner} : {lean_type(t[1])}) => {debug_expr(tinfo, t[1], inner, fuel)}) {atom})')
    if k in ('list', 'iter'):
        inner = fresh('d')
        return (f'(SDebug.list (α := {lean_type(t[1], "arg")}) '
                f'(fun ({inner} : {lean_type(t[1])}) => {debug_expr(tinfo, t[1], inner, fuel)}) {atom})')
    if k == 'tuple':
        names = [fresh('c') for _ in t[1]]
        parts = [(debug_expr(tinfo, ct, n, fuel), n) for ct, n in zip(t[1], names)]
        body = 'SOut.ok ("(" ++ ' + ' ++ ", " ++ '.join(f'{n}_s' for n in names) + ' ++ ")")'
        for (expr, n), ct in zip(reversed(parts), reversed(t[1])):
            body = f'SOut.bind (α := String) (β := String) {expr} (fun ({n}_s : String) => {body})'
        return f'(match {atom} with | {tuple_text(names)} => {body})'
    if k in ('map', 'set'):
        raise Refusal('debug-of-hash-container', show_ty(t))
    raise Refusal('debug-of-type', show_ty(t))


def tuple_text(parts):
    return '(' + ', '.join(parts) + ')' if len(parts) > 1 else parts[0]


def emit_debug_group(tinfo, adts, rec, out):
    """`MR_X.debugStr : Nat -> MR_X -> SOut String` for one recursive group."""
    bodies = {}
    for a in adts:
        cases = [('mk', a.fields, 'struct' if not a.tuple_struct else 'tuple', a.name)] if a.kind == 'struct' \
            else [(v, fs, st, v) for v, st, fs in a.variants]
        arms = []
        for cname, fields, style, shown in cases:
            names = [fresh('x') for _ in fields]
            pat = f'MR_{a.name}.{cname}' + ''.join(' ' + n for n in names)
            try:
                if not fields:
                    body = f'SOut.ok {lean_string(shown)}'
                else:
                    pieces = []
                    for (fname, ft), n in zip(fields, names):
                        pieces.append((f'{n}_s', debug_expr(tinfo, ft, n, 'fuel'), fname))
                    if style == 'named':
                        text = ' ++ ", " ++ '.join(f'{lean_string(fname + ": ")} ++ {v}' for v, _, fname in pieces)
                        body = f'SOut.ok ({lean_string(shown + " { ")} ++ {text} ++ " }}")'
                    else:
                        text = ' ++ ", " ++ '.join(v for v, _, _ in pieces)
                        body = f'SOut.ok ({lean_string(shown + "(")} ++ {text} ++ ")")'
                    for v, expr, _ in reversed(pieces):
                        body = f'SOut.bind (α := String) (β := String) {expr} (fun ({v} : String) => {body})'
            except Refusal as r:
                body = f'SOut.refused {lean_string(r.construct + " in " + a.name + "::" + cname)}'
            arms.append(f'  | {pat} => {body}')
        bodies[a.name] = arms
    if not rec:
        for a in adts:
            out.append(f'def MR_{a.name}.debugStr (fuel : Nat) (a : MR_{a.name}) : SOut String :=')
            out.append('  match fuel with')
            out.append('  | 0 => SOut.fuel')
            out.append('  | fuel + 1 =>')
            out.append('  match a with')
            out.extend(bodies[a.name])
            out.append('')
        return
    names = [a.name for a in adts]
    rec_name = 'MR_dbgRec_' + '_'.join(names)
    out.append(f'structure {rec_name} where')
    for n in names:
        out.append(f'  dbg_{n} : Nat → MR_{n} → SOut String')
    out.append('')
    for a in adts:
        body = '\n'.join(bodies[a.name])
        for n in names:
            body = body.replace(f'(MR_{n}.debugStr fuel ', f'((r.dbg_{n}) fuel ')
        out.append(f'def MR_{a.name}.debugStr_open (r : {rec_name}) (fuel : Nat) (a : MR_{a.name}) : SOut String :=')
        out.append('  match fuel with')
        out.append('  | 0 => SOut.fuel')
        out.append('  | fuel + 1 =>')
        out.append('  match a with')
        out.append(body)
        out.append('')
    out.append(f'def {rec_name}.tie : Nat → {rec_name}')
    out.append(f'  | 0 => {rec_name}.mk ' + ' '.join(f'(fun (_ : Nat) (_ : MR_{n}) => (SOut.fuel : SOut String))' for n in names))
    out.append(f'  | n + 1 => {rec_name}.mk ' + ' '.join(f'(MR_{n}.debugStr_open ({rec_name}.tie n))' for n in names))
    out.append('')
    for n in names:
        out.append(f'def MR_{n}.debugStr (fuel : Nat) (a : MR_{n}) : SOut String := ({rec_name}.tie fuel).dbg_{n} fuel a')
    out.append('')
