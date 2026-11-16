#![allow(dead_code)]

pub async fn awaited_raw_reads(ptr: *const u8) -> u8 {
    let first = async move { unsafe { *ptr } }.await;
    first ^ unsafe { *ptr }
}
