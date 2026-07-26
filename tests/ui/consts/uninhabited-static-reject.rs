// Trust: Regression test for rust-lang#143047 (Part of #860)
// Self-referential static of uninhabited type must be rejected.
// The const evaluator rejects statics with uninhabited types
// before evaluation, preventing infinite loops and UB.

#![deny(uninhabited_static)]

enum Void {}

// The original pattern from rust-lang#143047: self-referential static
static VOID: Void = VOID; //~ ERROR static of uninhabited type
//~| WARN: previously accepted
//~| ERROR cannot move out of static item

fn main() {}
