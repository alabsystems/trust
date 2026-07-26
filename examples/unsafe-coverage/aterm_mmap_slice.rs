pub struct MmapMut { ptr: *const u8, len: usize }
impl MmapMut {
    // The actual aterm fix: checked_add + bound, then from_raw_parts.
    pub fn slice(&self, start: usize, len: usize) -> Option<&[u8]> {
        let end = start.checked_add(len)?;
        if end > self.len { return None; }
        // SAFETY: start + len <= self.len, so the sub-range is within the map.
        Some(unsafe { std::slice::from_raw_parts(self.ptr.add(start), len) })
    }
}
