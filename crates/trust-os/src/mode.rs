/// Unix permission bits used when creating filesystem objects.
///
/// `UnixMode` stores only the low permission bits. File type bits such as
/// `S_IFREG` are rejected by [`UnixMode::new`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UnixMode(u32);

impl UnixMode {
    /// Owner read/write permissions: `0o600`.
    pub const OWNER_READ_WRITE: Self = Self(0o600);
    /// Owner read/write/execute permissions: `0o700`.
    pub const OWNER_ALL: Self = Self(0o700);
    /// User-readable file permissions: `0o644`.
    pub const USER_READABLE: Self = Self(0o644);
    /// User-searchable directory permissions: `0o755`.
    pub const USER_SEARCHABLE: Self = Self(0o755);

    /// Creates a mode from raw Unix permission bits.
    #[must_use]
    pub const fn new(bits: u32) -> Option<Self> {
        if bits & !0o7777 == 0 { Some(Self(bits)) } else { None }
    }

    /// Creates a mode from raw Unix permission bits, masking off file type bits.
    #[must_use]
    pub const fn from_permissions_truncate(bits: u32) -> Self {
        Self(bits & 0o7777)
    }

    /// Returns the raw permission bits.
    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }
}

impl Default for UnixMode {
    fn default() -> Self {
        Self::OWNER_READ_WRITE
    }
}

#[cfg(test)]
mod tests {
    use super::UnixMode;

    #[test]
    fn rejects_file_type_bits() {
        assert_eq!(UnixMode::new(0o644).map(UnixMode::bits), Some(0o644));
        assert_eq!(UnixMode::new(0o100644), None);
    }
}
