#![no_std]
pub fn shift_mask(target_width: u32) -> u32
ensures result <= 127
ensures result <= target_width
{
    if target_width == 8 {
        return 7;
    }
    if target_width == 16 {
        return 15;
    }
    if target_width == 32 {
        return 31;
    }
    if target_width == 64 {
        return 63;
    }
    if target_width == 128 {
        return 127;
    }
    0
}
