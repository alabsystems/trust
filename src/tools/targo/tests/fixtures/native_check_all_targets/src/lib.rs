// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

pub fn checked_value() -> u8 {
    7
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "reject-test-type")]
    const TEST_TARGET_MUST_BE_CHECKED: u8 = "not an integer";

    #[test]
    fn check_must_not_execute_test_bodies() {
        panic!("native check must typecheck this target without executing it");
    }
}
