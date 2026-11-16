// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Native Security.framework implementation extracted from aterm keeper.

use core::ffi::c_void;

type CFTypeRef = *const c_void;
type OSStatus = i32;

/// An owned CoreFoundation object, released on drop.
#[derive(Debug)]
pub struct Owned(CFTypeRef);

impl Drop for Owned {
    fn drop(&mut self) {
        if !self.0.is_null() {
            // SAFETY: we own exactly one reference.
            unsafe { CFRelease(self.0) };
        }
    }
}

const K_CF_STRING_ENCODING_UTF8: u32 = 0x0800_0100;

#[link(name = "CoreFoundation", kind = "framework")]
unsafe extern "C" {
    fn CFRelease(cf: CFTypeRef);
    fn CFDataCreate(alloc: CFTypeRef, bytes: *const u8, len: isize) -> CFTypeRef;
    fn CFDictionaryCreate(
        alloc: CFTypeRef,
        keys: *const CFTypeRef,
        values: *const CFTypeRef,
        n: isize,
        key_callbacks: *const c_void,
        value_callbacks: *const c_void,
    ) -> CFTypeRef;
    fn CFStringGetCString(s: CFTypeRef, buf: *mut u8, size: isize, encoding: u32) -> u8;
    fn CFDictionaryGetValue(dict: CFTypeRef, key: CFTypeRef) -> CFTypeRef;
    fn CFStringCreateWithBytes(
        alloc: CFTypeRef,
        bytes: *const u8,
        len: isize,
        encoding: u32,
        is_external_representation: u8,
    ) -> CFTypeRef;
    static kCFTypeDictionaryKeyCallBacks: [u8; 48];
    static kCFTypeDictionaryValueCallBacks: [u8; 40];
}

#[link(name = "Security", kind = "framework")]
unsafe extern "C" {
    fn SecCodeCopySelf(flags: u32, out: *mut CFTypeRef) -> OSStatus;
    fn SecCodeCopyDesignatedRequirement(
        code: CFTypeRef,
        flags: u32,
        out: *mut CFTypeRef,
    ) -> OSStatus;
    fn SecRequirementCopyString(req: CFTypeRef, flags: u32, out: *mut CFTypeRef) -> OSStatus;
    fn SecRequirementCreateWithString(text: CFTypeRef, flags: u32, out: *mut CFTypeRef)
    -> OSStatus;
    fn SecCodeCopyGuestWithAttributes(
        host: CFTypeRef,
        attributes: CFTypeRef,
        flags: u32,
        out: *mut CFTypeRef,
    ) -> OSStatus;
    fn SecCodeCheckValidity(code: CFTypeRef, flags: u32, req: CFTypeRef) -> OSStatus;
    fn SecStaticCodeCreateWithPath(path: CFTypeRef, flags: u32, out: *mut CFTypeRef) -> OSStatus;
    fn SecStaticCodeCheckValidity(code: CFTypeRef, flags: u32, req: CFTypeRef) -> OSStatus;
    fn SecCodeCopySigningInformation(code: CFTypeRef, flags: u32, out: *mut CFTypeRef) -> OSStatus;
    static kSecGuestAttributeAudit: CFTypeRef;
    static kSecCodeInfoTeamIdentifier: CFTypeRef;
    static kSecCodeInfoIdentifier: CFTypeRef;
}

#[link(name = "CoreFoundation", kind = "framework")]
unsafe extern "C" {
    fn CFURLCreateFromFileSystemRepresentation(
        alloc: CFTypeRef,
        buffer: *const u8,
        len: isize,
        is_directory: u8,
    ) -> CFTypeRef;
}

fn owned(cf: CFTypeRef, what: &str) -> Result<Owned, String> {
    if cf.is_null() { Err(format!("{what}: no object")) } else { Ok(Owned(cf)) }
}

fn status(rc: OSStatus, what: &str) -> Result<(), String> {
    if rc == 0 { Ok(()) } else { Err(format!("{what}: OSStatus {rc}")) }
}

/// This process's designated requirement, and its text.
pub fn own_designated_requirement() -> Result<(Owned, String), String> {
    let mut me: CFTypeRef = std::ptr::null();
    // SAFETY: an out-parameter for one new reference.
    status(unsafe { SecCodeCopySelf(0, &mut me) }, "SecCodeCopySelf")?;
    let me = owned(me, "SecCodeCopySelf")?;
    designated_requirement_of(&me)
}

/// The designated requirement of the code on disk at `path` (an executable or a bundle).
pub fn designated_requirement_at(path: &std::path::Path) -> Result<(Owned, String), String> {
    let code = static_code_at(path)?;
    designated_requirement_of(&code)
}

/// `requirement` (requirement-language text) compiled.
pub fn requirement_from_text(requirement: &str) -> Result<(Owned, String), String> {
    let bytes = requirement.as_bytes();
    // SAFETY: `bytes` is `len` live bytes of UTF-8, copied by the call.
    let source = owned(
        unsafe {
            CFStringCreateWithBytes(
                std::ptr::null(),
                bytes.as_ptr(),
                bytes.len() as isize,
                K_CF_STRING_ENCODING_UTF8,
                0,
            )
        },
        "CFStringCreateWithBytes",
    )?;
    let mut req: CFTypeRef = std::ptr::null();
    // SAFETY: `source` is a live CFString; an out-parameter for one reference.
    status(
        unsafe { SecRequirementCreateWithString(source.0, 0, &mut req) },
        "SecRequirementCreateWithString",
    )?;
    let req = owned(req, "SecRequirementCreateWithString")?;
    let text = requirement_text(&req)?;
    Ok((req, text))
}

/// The designated requirement of `code` (a static or a running code object), and its text.
fn designated_requirement_of(code: &Owned) -> Result<(Owned, String), String> {
    let mut req: CFTypeRef = std::ptr::null();
    // SAFETY: `code` is a live code object; an out-parameter for one reference.
    status(
        unsafe { SecCodeCopyDesignatedRequirement(code.0, 0, &mut req) },
        "SecCodeCopyDesignatedRequirement",
    )?;
    let req = owned(req, "SecCodeCopyDesignatedRequirement")?;
    let text = requirement_text(&req)?;
    Ok((req, text))
}

/// A requirement's text, as Security.framework prints it.
fn requirement_text(req: &Owned) -> Result<String, String> {
    let mut text: CFTypeRef = std::ptr::null();
    // SAFETY: `req` is a live requirement; an out-parameter for one reference.
    status(unsafe { SecRequirementCopyString(req.0, 0, &mut text) }, "SecRequirementCopyString")?;
    let text = owned(text, "SecRequirementCopyString")?;
    let mut buf = vec![0u8; 4096];
    // SAFETY: `text` is a live CFString; `buf` is its stated size.
    let ok = unsafe {
        CFStringGetCString(text.0, buf.as_mut_ptr(), buf.len() as isize, K_CF_STRING_ENCODING_UTF8)
    };
    Ok(if ok != 0 {
        let end = buf.iter().position(|b| *b == 0).unwrap_or(buf.len());
        String::from_utf8_lossy(&buf[..end]).into_owned()
    } else {
        "(unprintable)".to_string()
    })
}

/// The static code object for the code on disk at `path`.
fn static_code_at(path: &std::path::Path) -> Result<Owned, String> {
    use std::os::unix::ffi::OsStrExt as _;
    let bytes = path.as_os_str().as_bytes();
    let is_dir = u8::from(path.is_dir());
    // SAFETY: `bytes` is `len` live bytes, copied by the call.
    let url = owned(
        unsafe {
            CFURLCreateFromFileSystemRepresentation(
                std::ptr::null(),
                bytes.as_ptr(),
                bytes.len() as isize,
                is_dir,
            )
        },
        "CFURLCreateFromFileSystemRepresentation",
    )?;
    let mut code: CFTypeRef = std::ptr::null();
    // SAFETY: `url` is a live CFURL; an out-parameter for one reference.
    status(
        unsafe { SecStaticCodeCreateWithPath(url.0, 0, &mut code) },
        "SecStaticCodeCreateWithPath",
    )?;
    owned(code, "SecStaticCodeCreateWithPath")
}

/// Whether the process `token` names runs code satisfying `req`, its status classed by
/// [`guest_validity`].
pub fn check_guest(token: &[u32; 8], req: &Owned) -> Result<(), super::Error> {
    let guest = copy_guest(token).map_err(super::Error::Unchecked)?;
    // SAFETY: both objects are live.
    guest_validity(unsafe { SecCodeCheckValidity(guest.0, 0, req.0) })
}

/// `kSecCSCheckAllArchitectures | kSecCSCheckNestedCode | kSecCSStrictValidate`.
pub const STRICT: u32 = 1 | (1 << 3) | (1 << 4);

/// Check a static image under the supplied native validity flags.
pub fn check_static_with(
    path: &std::path::Path,
    req: &Owned,
    flags: u32,
) -> Result<(), super::Error> {
    let code = static_code_at(path).map_err(super::Error::Unchecked)?;
    // SAFETY: both objects are live.
    static_validity(unsafe { SecStaticCodeCheckValidity(code.0, flags, req.0) })
}

/// Classify only definite code refusals; unknown framework and operational
/// failures remain unchecked, including unreadable or incomplete resources.
pub(super) fn static_validity(rc: OSStatus) -> Result<(), super::Error> {
    validity(rc, "the code", &[])
}

/// [`static_validity`]'s classes for a running guest, which also refuses one whose dynamic
/// validity is lost (errSecCSGuestInvalid) or whose code on disk changed since it started
/// (errSecCSStaticCodeChanged): neither comes back for that process. Any other failure, a
/// framework or trust service one among them, judged nothing and remains unchecked.
pub(super) fn guest_validity(rc: OSStatus) -> Result<(), super::Error> {
    const GUEST_INVALID: OSStatus = -67063;
    const STATIC_CODE_CHANGED: OSStatus = -67034;
    validity(rc, "the peer's code", &[GUEST_INVALID, STATIC_CODE_CHANGED])
}

/// A validity check's status `rc` for `what`: refused for a definite code refusal or one of
/// `also`, unchecked for any other failure.
fn validity(rc: OSStatus, what: &str, also: &[OSStatus]) -> Result<(), super::Error> {
    // Security.framework/Headers/CSCommon.h: errSecCSUnsigned,
    // errSecCSSignatureFailed, errSecCSReqFailed. Unsupported signature
    // formats (including errSecCSSignatureInvalid) remain unchecked.
    const UNSIGNED: OSStatus = -67062;
    const SIGNATURE_FAILED: OSStatus = -67061;
    const REQUIREMENT_FAILED: OSStatus = -67050;
    if rc == 0 {
        return Ok(());
    }
    if matches!(rc, UNSIGNED | SIGNATURE_FAILED | REQUIREMENT_FAILED) || also.contains(&rc) {
        Err(super::Error::Refused(format!(
            "{what} does not satisfy the requirement in force: OSStatus {rc}"
        )))
    } else {
        Err(super::Error::Unchecked(format!(
            "{what} could not be checked against the requirement in force: OSStatus {rc}"
        )))
    }
}

/// The team identifier this process's code is signed by, or `None` (ad hoc, or unsigned).
pub fn own_team() -> Result<Option<String>, String> {
    // SAFETY: reading an immutable framework constant.
    own_signing_value(unsafe { kSecCodeInfoTeamIdentifier })
}

/// The signing identifier this process's code is signed with (`com.aterm.aterm`), or `None`
/// (unsigned).
pub fn own_identifier() -> Result<Option<String>, String> {
    // SAFETY: reading an immutable framework constant.
    own_signing_value(unsafe { kSecCodeInfoIdentifier })
}

/// One string of this process's signing information (`key`, a `kSecCodeInfo…` constant), or
/// `None` when the information has none.
fn own_signing_value(key: CFTypeRef) -> Result<Option<String>, String> {
    const SIGNING_INFORMATION: u32 = 1 << 1;
    let mut me: CFTypeRef = std::ptr::null();
    // SAFETY: an out-parameter for one new reference.
    status(unsafe { SecCodeCopySelf(0, &mut me) }, "SecCodeCopySelf")?;
    let me = owned(me, "SecCodeCopySelf")?;
    let mut info: CFTypeRef = std::ptr::null();
    // SAFETY: `me` is a live code object; an out-parameter for one reference.
    status(
        unsafe { SecCodeCopySigningInformation(me.0, SIGNING_INFORMATION, &mut info) },
        "SecCodeCopySigningInformation",
    )?;
    let info = owned(info, "SecCodeCopySigningInformation")?;
    // SAFETY: `key` is an immutable framework constant; `info` is a live dictionary, and the
    // value it answers is borrowed from it (the Get rule), read while `info` lives.
    let value = unsafe { CFDictionaryGetValue(info.0, key) };
    if value.is_null() {
        return Ok(None);
    }
    let mut buf = vec![0u8; 256];
    // SAFETY: `value` is a CFString `info` keeps alive; `buf` is its stated size.
    let ok = unsafe {
        CFStringGetCString(value, buf.as_mut_ptr(), buf.len() as isize, K_CF_STRING_ENCODING_UTF8)
    };
    if ok == 0 {
        return Err("a signing information string is unprintable".to_string());
    }
    let end = buf.iter().position(|b| *b == 0).unwrap_or(buf.len());
    let value = String::from_utf8_lossy(&buf[..end]).into_owned();
    Ok((!value.is_empty()).then_some(value))
}

/// The code object of the process `token` names.
fn copy_guest(token: &[u32; 8]) -> Result<Owned, String> {
    let mut bytes = [0_u8; 32];
    for (part, word) in bytes.chunks_exact_mut(4).zip(token) {
        part.copy_from_slice(&word.to_ne_bytes());
    }
    // SAFETY: `bytes` is 32 live bytes, copied by CFDataCreate.
    let data = owned(
        unsafe { CFDataCreate(std::ptr::null(), bytes.as_ptr(), bytes.len() as isize) },
        "CFDataCreate",
    )?;
    // SAFETY: reading an immutable framework constant.
    let key = unsafe { kSecGuestAttributeAudit };
    let keys = [key];
    let values = [data.0];
    // SAFETY: one key and one value, both live; the standard CFType callbacks retain them for
    // the dictionary's life.
    let attrs = owned(
        unsafe {
            CFDictionaryCreate(
                std::ptr::null(),
                keys.as_ptr(),
                values.as_ptr(),
                1,
                std::ptr::addr_of!(kCFTypeDictionaryKeyCallBacks).cast(),
                std::ptr::addr_of!(kCFTypeDictionaryValueCallBacks).cast(),
            )
        },
        "CFDictionaryCreate",
    )?;
    let mut guest: CFTypeRef = std::ptr::null();
    // SAFETY: `attrs` is a live dictionary; an out-parameter for one reference.
    status(
        unsafe { SecCodeCopyGuestWithAttributes(std::ptr::null(), attrs.0, 0, &mut guest) },
        "the peer's code (SecCodeCopyGuestWithAttributes)",
    )?;
    owned(guest, "SecCodeCopyGuestWithAttributes")
}
