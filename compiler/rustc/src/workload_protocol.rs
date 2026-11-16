//! Fixed declaration on the actual compiler launcher, not only its driver dylib.

#[repr(C, align(8))]
struct Declaration([u8; 64]);

#[used]
#[unsafe(link_section = "__TEXT,__trust_member")]
static MEMBER_PROTOCOL: Declaration = Declaration(super::WORKLOAD_MEMBER_PROTOCOL_MARKER);

// Trust: separate from the existing standalone BootstrapFixed profile marker.
#[used]
#[unsafe(link_section = "__TEXT,__trust_btfcomp")]
static BOOTSTRAP_FIXED_COMPILER: Declaration =
    Declaration(super::BOOTSTRAP_FIXED_COMPILER_PROTOCOL_MARKER);
