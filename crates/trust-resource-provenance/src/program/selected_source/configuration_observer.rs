//! Configuration producer DATA, not an original source/cache/native capability.
use super::*;

/// An untrusted input observer for the existing configuration parser. A caller
/// may implement this trait over arbitrary DATA; successful observations do NOT
/// authenticate a root, prove read-set completeness, exclude writers, admit a
/// process or create a Seed/SDK. A native consumer must separately retain its
/// genuine concrete original owners through actual closure and all local joins.
///
/// The concrete Bootstrap implementation retains its SAME original graph and
/// physical read-set. Its refusal callback revokes that actual owner, but an
/// arbitrary implementation's callback has no such authority.
pub trait ConfigurationInputObserver: std::fmt::Debug + Send + Sync {
    fn check_current(&self) -> io::Result<()>;
    fn root(&self) -> io::Result<&Path>;
    /// Full original environment DATA. Values may be private: never log them.
    fn environment(&self) -> io::Result<&[(Vec<u8>, Vec<u8>)]>;
    fn capture_input(&self, path: &Path) -> io::Result<SourceRead>;
    fn record_failure(&self);
}
