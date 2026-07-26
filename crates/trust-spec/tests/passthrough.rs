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

#[trust::invariant(self.value >= 0 && self.value <= self.limit)]
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
fn passthrough_attributes_leave_struct_behavior_unchanged() {
    let mut counter = Counter::new(1, 4);
    assert_eq!(counter.increment(), 2);
    assert_eq!(counter.limit, 4);
}
