#[trust::requires(
    amount > 0
        && old(balance) >= amount
        && forall(|idx: usize| idx < history.len() ==> history[idx] >= 0)
)]
#[trust::ensures(
    result == old(balance) - amount
        && exists(|idx: usize| idx < ledger.len() && ledger[idx] == amount)
)]
fn withdraw(balance: i32, amount: i32) -> i32 {
    balance - amount
}

// Trust: this struct previously carried
// `#[trust::invariant(self.value >= 0 && self.value <= self.limit)]`, and the
// test below was named `passthrough_attributes_leave_struct_behavior_unchanged`
// — i.e. the repo's own coverage ASSERTED that the erasure was intended
// behaviour, and shipped the annotation as documented usage.
//
// It is removed deliberately. `#[trust::invariant(..)]` has no verified meaning
// on any lane: under tRustc it is now a hard error (`ExpandTrustInvariant`), and
// under stable Rust it is a no-op. A struct-position invariant in particular has
// no program point at all. Keeping a passing test that exercised it would keep
// advertising a guarantee-shaped annotation that guarantees nothing.
//
// The refusal itself is covered by `tests/ui/contracts/trust-spec-invariant-*`.
struct Counter {
    value: i32,
    limit: i32,
}

impl Counter {
    fn new(value: i32, limit: i32) -> Self {
        Self { value, limit }
    }

    #[trust::ensures(result == old(self.value) + 1)]
    fn increment(&mut self) -> i32 {
        self.value += 1;
        self.value
    }
}

#[test]
fn passthrough_attributes_leave_function_behavior_unchanged() {
    assert_eq!(withdraw(10, 3), 7);
}

#[test]
fn passthrough_attributes_leave_method_behavior_unchanged() {
    let mut counter = Counter::new(1, 4);
    assert_eq!(counter.increment(), 2);
    assert_eq!(counter.limit, 4);
}
