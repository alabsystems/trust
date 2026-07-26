// Adversarial fixture: enum tag and struct state agree before value access.

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

fn read_armed(cell: Cell, fallback: u32) -> u32 {
    match (cell.slot, cell.armed) {
        (Slot::Value(value), true) => value,
        _ => fallback,
    }
}

fn main() {
    let full = Cell { slot: Slot::Value(9), armed: true };
    let empty = Cell { slot: Slot::Empty, armed: false };
    assert!(read_armed(full, 0) == 9);
    assert!(read_armed(empty, 4) == 4);
}
