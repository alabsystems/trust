// LANE SC (follow-on) — `tc::heartbeat_profiler::types::SourcePos::coalesced`: a struct literal
// whose fields are, in order, a PLACE read, an ARITHMETIC result, and a folded constant.
#![allow(dead_code, clippy::all)]

#[derive(Clone, Copy)]
pub struct Pos {
    pub f: u32,
    pub l: u32,
    pub c: u32,
}

impl Pos {
    // the CONVERTING control: every field a place or a constant
    pub fn k3(self) -> Pos {
        Pos { f: self.f, l: self.l, c: 0 }
    }
    // THE CORPUS BODY, verbatim
    pub fn k4(self) -> Pos {
        Pos { f: self.f, l: self.l / 10, c: 0 }
    }
    // the same with no div-guard assert
    pub fn k2(self) -> Pos {
        Pos { f: self.f, l: self.l * 10, c: 0 }
    }
    // the ARITHMETIC FIRST — the order the shim's linear walk already agrees with
    pub fn k5(self) -> Pos {
        Pos { f: self.f * 10, l: self.l, c: 0 }
    }
    // TWO arithmetic fields, both after the place
    pub fn k6(self) -> Pos {
        Pos { f: self.f, l: self.l * 10, c: self.c * 2 }
    }
}

// THE ISOLATING CONTROLS the k2/k4 pair does not provide. `k5` (instruction field FIRST) already
// measures `markers_exact: true` under the CONTROL despite crossing the same assert split, so the
// split is NOT a wall. What is still unmeasured is whether the DIV-GUARD shape
// (`icmp ne; assert; udiv` — not a `checked_unit`) is a SECOND wall beside the field-order rule.
// `k7` puts the DIV in field 0, where the field-order rule does not object.
impl Pos {
    // div in field 0 — instruction first, so `agg_field_order_ok` has no objection
    pub fn k7(self) -> Pos {
        Pos { f: self.f / 10, l: self.l, c: 0 }
    }
    // the same with a NON-constant divisor, so the guard cannot be folded away
    pub fn k8(self, d: u32) -> Pos {
        Pos { f: self.f / d, l: self.l, c: 0 }
    }
    // TWO instruction fields, both before any place — the field-order rule is satisfied
    pub fn k9(self) -> Pos {
        Pos { f: self.f * 2, l: self.l * 3, c: 0 }
    }
}
