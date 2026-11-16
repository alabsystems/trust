//! Exact reaching-copy facts do not inherit legacy argument pooling.

pub(super) fn corresponds(
    argument: u32,
    mir_arguments: u32,
    ir_parameters: u32,
    ir_argument: Option<u32>,
) -> bool {
    mir_arguments == ir_parameters && argument < mir_arguments && ir_argument == Some(argument)
}

#[cfg(test)]
mod tests {
    use super::corresponds;

    #[test]
    fn only_the_same_argument_under_aligned_signatures_matches() {
        assert!(corresponds(1, 3, 3, Some(1)));
        assert!(!corresponds(1, 3, 3, Some(0)));
        assert!(!corresponds(1, 3, 2, Some(1)));
        assert!(!corresponds(1, 3, 4, Some(1)));
        assert!(!corresponds(3, 3, 3, Some(3)));
        assert!(!corresponds(1, 3, 3, None));
    }
}
