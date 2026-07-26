// Adversarial fixture: struct state claims a value exists without checking tag.
//
// The main uses consistent states, but Cell { Empty, armed: true } is flawed.

#[derive(Clone, Copy)]
enum Slot {
    Empty,
    Value(u32),
}

#[derive(Clone, Copy)]
struct Cell {
    slot: Slot,
    armed: bool,
}

fn read_armed_unchecked(cell: Cell, fallback: u32) -> u32 {
    if cell.armed {
        match cell.slot {
            Slot::Value(value) => value,
            Slot::Empty => unreachable!(),
        }
    } else {
        fallback
    }
}

fn main() {
    let full = Cell { slot: Slot::Value(9), armed: true };
    let empty = Cell { slot: Slot::Empty, armed: false };
    assert!(read_armed_unchecked(full, 0) == 9);
    assert!(read_armed_unchecked(empty, 4) == 4);
}
