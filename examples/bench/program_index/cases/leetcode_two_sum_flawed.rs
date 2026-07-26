// Program-index fixture: LeetCode-style two-sum with unchecked pair addition.
//
// The sample main returns before hitting the bad paths, but the helper is
// proof-flawed for callers that provide large addends or no matching pair.

fn two_sum_index_sum_unchecked(nums: &[u32; 4], target: u32) -> usize {
    const NUMS_LEN: usize = 4;

    let mut i = 0;
    while i < NUMS_LEN {
        let mut j = i + 1;
        while j < NUMS_LEN {
            let sum = nums[i] + nums[j];
            if sum == target {
                return i + j;
            }
            j += 1;
        }
        i += 1;
    }
    usize::MAX
}

fn main() {
    let nums = [2, 7, 11, 15];
    let _ = two_sum_index_sum_unchecked(&nums, 9);
}
