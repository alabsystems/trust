#![allow(unreachable_code, unused_must_use, unconditional_panic)]
pub fn array_base_constant() -> u32 {
    ({ return 7; [u32::MAX] })[0];
    9
}
pub fn array_base_dynamic(i: usize) -> u32 {
    ({ return 7; [u32::MAX] })[i];
    9
}
pub fn slice_base_dynamic(i: usize) -> u32 {
    ({ return 7; &[u32::MAX] as &[u32] })[i];
    9
}
pub fn slice_index_returns(s: &[u32]) -> u32 {
    s[{ return 7; 0usize }];
    9
}
pub fn array_index_break() -> u32 {
    'out: loop { [u32::MAX][{ break 'out 7; 0usize }]; }
}
pub fn slice_index_break(s: &[u32]) -> u32 {
    'out: loop { s[{ break 'out 7; 0usize }]; }
}
pub fn ordinary_array(i: usize) -> u32 { [3u32, 5][i] }
pub fn ordinary_slice(s: &[u32], i: usize) -> u32 { s[i] }
pub fn both_diverge() -> u32 {
    ({ return 7; [3u32] })[{ return 8; 0usize }];
    9
}
pub fn array_base_break(i: usize) -> u32 {
    'out: loop { ({ break 'out 7; [3u32, 5] })[i]; }
}
pub fn slice_base_break(i: usize) -> u32 {
    'out: loop { ({ break 'out 7; &[3u32, 5] as &[u32] })[i]; }
}
pub fn inner_array_loop(i: usize) -> u32 { (loop { break [3u32, 5] })[i] }
pub fn inner_slice_loop(s: &[u32], i: usize) -> u32 { s[loop { break i }] }
pub fn conditional_index(s: &[u32], quit: bool, i: usize) -> u32 {
    s[if quit { return 7 } else { i }]
}
pub fn trapping_base() -> u32 {
    ({ let _ = [0u32][1]; [3u32] })[{ return 7; 0usize }];
    9
}
pub fn earlier_refusal(s: &[u32]) -> u32 {
    unsafe { core::arch::asm!("") };
    s[{ return 7; 0usize }];
    9
}
pub fn array_base_with_asm() -> u32 {
    ({ unsafe { core::arch::asm!("") }; return 7; [u32::MAX] })[0];
    9
}
pub fn slice_index_with_asm(s: &[u32]) -> u32 {
    s[{ unsafe { core::arch::asm!("") }; return 7; 0usize }];
    9
}

pub fn slice_return_empty() -> u32 { slice_index_returns(&[]) }
pub fn slice_break_empty() -> u32 { slice_index_break(&[]) }
pub fn inner_slice_values(i: usize) -> u32 { inner_slice_loop(&[3, 5], i) }
pub fn conditional_empty(quit: bool) -> u32 { conditional_index(&[], quit, 0) }
pub fn conditional_values(quit: bool, i: usize) -> u32 {
    conditional_index(&[3, 5], quit, i)
}

pub fn ordinary_slice_values(i: usize) -> u32 { ordinary_slice(&[3, 5], i) }
pub fn ordinary_slice_empty() -> u32 { ordinary_slice(&[], 0) }
