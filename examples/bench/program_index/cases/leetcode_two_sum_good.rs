// Program-index fixture: LeetCode-style two-sum with guarded addition.

fn two_sum_index_sum(nums: &[u32; 4], target: u32) -> usize {
    const NUMS_LEN: usize = 4;

    let mut i = 0;
    while i < NUMS_LEN {
        let mut j = i + 1;
        while j < NUMS_LEN {
            if nums[i] <= u32::MAX - nums[j] {
                let sum = nums[i] + nums[j];
                if sum == target {
                    return i + j;
                }
            }
            j += 1;
        }
        i += 1;
    }
    usize::MAX
}

fn main() {
    let nums = [2, 7, 11, 15];
    let _ = two_sum_index_sum(&nums, 9);
}
