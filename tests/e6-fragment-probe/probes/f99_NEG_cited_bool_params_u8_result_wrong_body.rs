//@ probe-shape: none
//@ probe-expect: unproved
//@ probe-flags: -O
//@ probe-note: NEGATIVE, must stay red, and the CLOSE twin of f98: the same
//@ probe-note: specification and clause, but the body returns `2` and `1` the other
//@ probe-note: way round, and the citation names a TRUE theorem that states something
//@ probe-note: else (`spec_cursor` equals itself). The island checks, so the refusal
//@ probe-note: cannot be the incidental "the island was rejected" kind. Typing the
//@ probe-note: relation at the result's carrier makes the goal well-formed; it must
//@ probe-note: not make it true: `@Eq UInt8 (import ..) (spec_cursor ..)` is false for
//@ probe-note: `same = false, continues = true`, and the cited statement is not it.
clean {
    def spec_cursor (has fresh same continues : Bool) : UInt8 :=
      if (has && fresh) = true then (if same = true then 1 else if continues = true then 2 else 0) else 0
    theorem spec_cursor_refl (a b c d : Bool) : spec_cursor a b c d = spec_cursor a b c d := rfl
}
pub fn cursor(has: bool, fresh: bool, same: bool, continues: bool) -> u8
    ensures result == spec_cursor(has, fresh, same, continues) by spec_cursor_refl
{ if has && fresh { if same { 2 } else if continues { 1 } else { 0 } } else { 0 } }
