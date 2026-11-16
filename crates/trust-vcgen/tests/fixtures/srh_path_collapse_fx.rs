#[derive(Clone, Copy, PartialEq, Eq)]
pub enum State {
    Ground,
    Escape,
    CsiEntry,
    CsiParam,
    CsiIntermediate,
    CsiIgnore,
    DcsEntry,
    DcsParam,
    DcsIntermediate,
    DcsPassthrough,
}

pub struct Carry {
    pub state: State,
    pub params: Vec<u16>,
    pub subparam_mask: u32,
    pub current_param: u16,
    pub param_started: bool,
    pub last_was_colon: bool,
}

pub fn validate_carry(carry: &Carry) -> Result<(), u8> {
    if carry.state == State::DcsPassthrough {
        return Err(0);
    }
    let header = matches!(
        carry.state,
        State::CsiEntry
            | State::CsiParam
            | State::CsiIntermediate
            | State::CsiIgnore
            | State::DcsEntry
            | State::DcsParam
            | State::DcsIntermediate
    );
    let parameters = matches!(
        carry.state,
        State::CsiParam | State::CsiIntermediate | State::DcsParam | State::DcsIntermediate
    );
    let has_params = !carry.params.is_empty()
        || carry.subparam_mask != 0
        || carry.current_param != 0
        || carry.param_started
        || carry.last_was_colon;
    if has_params && !parameters {
        return Err(1);
    }
    if carry.params.len() > 24 {
        return Err(2);
    }
    if carry.subparam_mask >> carry.params.len() != 0 {
        return Err(3);
    }
    if header { Ok(()) } else { Err(4) }
}

pub fn shift_entry(x: u32, s: u32) -> u32 {
    x >> s
}
