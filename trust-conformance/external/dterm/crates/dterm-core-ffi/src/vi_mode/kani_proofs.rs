#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ViModeState {
    cursor: usize,
    mark: Option<usize>,
    inline_search: Option<u8>,
}

impl ViModeState {
    pub fn new(cursor: usize) -> Self {
        Self {
            cursor,
            mark: None,
            inline_search: None,
        }
    }
}

pub fn dterm_terminal_vi_mode_set_mark_v2(mut state: ViModeState, mark: usize) -> ViModeState {
    state.mark = Some(mark);
    state
}

pub fn dterm_terminal_vi_mode_inline_search_v2(
    mut state: ViModeState,
    needle: u8,
) -> ViModeState {
    state.inline_search = Some(needle);
    state
}

#[cfg(feature = "kani-contracts")]
#[kani::proof_for_contract(dterm_terminal_vi_mode_set_mark_v2)]
#[kani::unwind(32)]
fn dterm_terminal_vi_mode_set_mark_v2_contract() {
    let cursor: usize = kani::any();
    let mark: usize = kani::any();
    let state = ViModeState::new(cursor);
    let updated = dterm_terminal_vi_mode_set_mark_v2(state, mark);
    assert_eq!(updated.mark, Some(mark));
}

#[cfg(feature = "kani-contracts")]
#[kani::proof_for_contract(dterm_terminal_vi_mode_inline_search_v2)]
#[kani::unwind(32)]
fn dterm_terminal_vi_mode_inline_search_v2_contract() {
    let cursor: usize = kani::any();
    let needle: u8 = kani::any();
    let state = ViModeState::new(cursor);
    let updated = dterm_terminal_vi_mode_inline_search_v2(state, needle);
    assert_eq!(updated.inline_search, Some(needle));
}
