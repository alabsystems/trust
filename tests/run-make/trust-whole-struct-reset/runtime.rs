//! Executable controls for complete aggregate replacement and RHS effects.

pub struct State {
    pub value: u64,
    pub epoch: u64,
}

impl Default for State {
    fn default() -> Self {
        Self { value: 9, epoch: 0 }
    }
}

pub fn reset(state: &mut State) {
    let epoch = state.epoch;
    *state = State::default();
    state.epoch = epoch + 1;
}

pub fn reset_and_observe() -> u64 {
    let mut state = State { value: 17, epoch: 4 };
    reset(&mut state);
    state.value * 100 + state.epoch
}

fn replacement(calls: &mut u64) -> State {
    *calls += 1;
    State { value: *calls + 20, epoch: 0 }
}

pub fn effectful_rhs() -> u64 {
    let mut calls = 2;
    let mut state = State { value: 17, epoch: 4 };
    let reference = &mut state;
    let epoch = reference.epoch;
    *reference = replacement(&mut calls);
    reference.epoch = epoch + 1;
    state.value * 10000 + state.epoch * 100 + calls
}

pub fn repeated_reset() -> u64 {
    let mut state = State { value: 17, epoch: 4 };
    reset(&mut state);
    reset(&mut state);
    state.value * 100 + state.epoch
}

pub fn alias_observes_replacement() -> u64 {
    let mut state = State { value: 17, epoch: 4 };
    let alias = &mut state;
    let before = alias.value;
    reset(alias);
    before * 10000 + state.value * 100 + state.epoch
}

pub struct BorrowedState<'a> {
    pub pointer: &'a mut u64,
    pub epoch: u64,
}

fn replacement_borrowed(pointer: &mut u64) -> BorrowedState<'_> {
    BorrowedState { pointer, epoch: 0 }
}

fn reset_borrowed<'a>(state: &mut BorrowedState<'a>, pointer: &'a mut u64) {
    let epoch = state.epoch;
    *state = replacement_borrowed(pointer);
    state.epoch = epoch + 1;
}

pub fn borrowed_field_reset() -> u64 {
    let mut old = 17;
    let mut new = 9;
    let mut state = BorrowedState { pointer: &mut old, epoch: 4 };
    reset_borrowed(&mut state, &mut new);
    let epoch = state.epoch;
    old * 10000 + new * 100 + epoch
}
