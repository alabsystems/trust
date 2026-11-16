//@ probe-shape: none
//@ probe-expect: discharged
//@ probe-flags: -O
//@ probe-note: RESULT CARRIER IS NOT THE PARAMETERS' CARRIER. aterm's
//@ probe-note: `relay_live::cursor` (crates/aterm-mesh-core), byte for byte: four `bool`
//@ probe-note: flags in, a `u8` cursor code out, `ensures result == spec_cursor(..) by
//@ probe-note: cursor_is_exact`. The E6 tree reader mints the body (`recognize=None`,
//@ probe-note: five blocks); `spec_cursor` and the theorem are island source.
//@ probe-note: MEASURED on Trust build 16387 (trustc 29ebb403d): `unproved`, the post-walk
//@ probe-note: lane's `ClauseOutsideFragment`: "the elaborated goal does not typecheck
//@ probe-note: (TypeMismatch expected Bool, inferred UInt8 at [PiBody x4, AppFn,
//@ probe-note: AppArg])". `atom_domain` typed the
//@ probe-note: relation by every variable in it, call arguments included, so it built
//@ probe-note: `Eq Bool` over two `UInt8` calls. It now takes the result carrier the
//@ probe-note: typed calls declare, and the goal is
//@ probe-note:   (b b1 b2 b3 : Bool) -> @Eq UInt8 (import b b1 b2 b3) (spec_cursor b b1 b2 b3).
//@ probe-note: The close negative is f99; the same bug at two machine widths is f100.
clean {
    def spec_cursor (has fresh same continues : Bool) : UInt8 :=
      if (has && fresh) = true then (if same = true then 1 else if continues = true then 2 else 0) else 0
}
clean {
    theorem cursor_is_exact (a b c d : Bool) :
        trust_import_probe__cursor a b c d = spec_cursor a b c d := by
      cases a <;> cases b <;> cases c <;> cases d <;> rfl
}
pub fn cursor(has: bool, fresh: bool, same: bool, continues: bool) -> u8
    ensures result == spec_cursor(has, fresh, same, continues) by cursor_is_exact
{ if has && fresh { if same { 1 } else if continues { 2 } else { 0 } } else { 0 } }
