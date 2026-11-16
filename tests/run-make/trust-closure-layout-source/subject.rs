pub fn once_layout(value: &mut u64, tag: u8) -> u64 {
    let take = move || {
        let consumed = value;
        *consumed + tag as u64
    };
    take()
}

pub fn native_layout() -> (usize, usize, u64) {
    let mut value = 9u64;
    let borrowed = &mut value;
    let tag = 3u8;
    let take = move || {
        let consumed = borrowed;
        *consumed + tag as u64
    };
    let size = std::mem::size_of_val(&take);
    let align = std::mem::align_of_val(&take);
    (size, align, take())
}


pub fn moved_mutable_write(value: &mut u64, tag: u8) -> u64 {
    let take = move || { let consumed = value; *consumed += tag as u64; *consumed };
    take()
}

pub unsafe fn moved_raw_pointer(value: *mut u64, tag: u8) -> u64 {
    let take = move || unsafe { *value + tag as u64 };
    take()
}

pub fn escaped_local() -> *mut u32 {
    let mut value = 9u32;
    let reference = &mut value;
    let take = move || { let moved = reference; moved };
    take() as *mut u32
}

pub fn returned_param(value: &mut u32) -> &mut u32 {
    let take = move || { let moved = value; moved };
    take()
}

pub fn alias_returned_param(value: &mut u32) -> &mut u32 {
    let take = move || { let moved = value; moved };
    let alias = take;
    alias()
}

pub fn local_write_through_result() -> u32 {
    let mut value = 9u32;
    let reference = &mut value;
    let take = move || { let moved = reference; moved };
    let target = take();
    *target += 3;
    *target
}
