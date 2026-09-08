//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
// wave-LM: `#[loop_match]` lowers on the `lower_loop` scaffold with the state
// local as an always-carried header param and the existing scalar match doing
// the per-iteration dispatch: `#[const_continue] break 'blk v` sets the state
// and takes the back-edge (a divergence inside the match), `break 'a` exits
// through the ordinary loop ctx, and a fall-through arm's value becomes the
// new state at the join. rustc's own builder jump-threads the const_continue
// edges — an optimization of exactly this model, adjudicated behaviorally by
// the interpreter differential. Integer-shaped scalar states only; floats and
// fieldless-enum states keep their named refusals.

#![allow(incomplete_features)]
#![feature(loop_match)]

pub fn integer(mut state: i32) -> i32 {
    #[loop_match]
    'a: loop {
        state = 'blk: {
            match state {
                -1 => {
                    #[const_continue]
                    break 'blk 2;
                }
                0 => {
                    #[const_continue]
                    break 'blk -1;
                }
                2 => break 'a,
                _ => unreachable!(),
            }
        }
    }
    state
}

pub fn boolean(mut state: bool) -> bool {
    #[loop_match]
    'b: loop {
        state = 'blk: {
            match state {
                true => {
                    #[const_continue]
                    break 'blk false;
                }
                false => break 'b,
            }
        }
    }
    state
}

// wave-LM2: a FIELDLESS-ENUM state — rustc's own supported-type set — dispatches
// through lower_enum_match_general's unit-variant switch, or-alternatives included.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum St {
    A,
    B,
    C,
}

pub fn enum_state(mut state: St) -> St {
    #[loop_match]
    'a: loop {
        state = 'blk: {
            match state {
                St::A | St::B => {
                    #[const_continue]
                    break 'blk St::C;
                }
                St::C => break 'a,
            }
        }
    }
    state
}

fn main() {
    assert_eq!(integer(0), 2);
    assert!(!boolean(true));
    assert_eq!(enum_state(St::A), St::C);
}
