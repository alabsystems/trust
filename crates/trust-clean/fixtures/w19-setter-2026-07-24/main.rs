// W19 mutators inc-1 fixture — the &mut-self field-setter shapes.
// set_x: the minimal single-scalar-field setter (post = independent param) — the inc-1 target.
// set_both: two sequential field writes (multi-field; inc-1 boundary — should NOT match a
//   single-field SemFieldSet).
// bump: read-modify-write (self.x += 1; post = f(pre)) — the inc-1.5 shape (deferred).
pub struct S { x: i64, y: i64 }
impl S {
    #[inline(never)] pub fn set_x(&mut self, v: i64) { self.x = v; }
    #[inline(never)] pub fn set_both(&mut self, a: i64, b: i64) { self.x = a; self.y = b; }
    #[inline(never)] pub fn bump(&mut self) { self.x += 1; }
}
