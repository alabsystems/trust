// Trust: the outer callee is admitted before either argument registers Borrowed.
pub fn constructed_then_consumed(value: &u64) -> u64 {
    external::consume(external::Borrowed { value })
}

pub fn returned_then_consumed(value: &u64) -> u64 {
    external::consume(external::make(value))
}

pub fn borrowed_scalar(value: &u64) -> u64 {
    external::read(value)
}
