//! The real link-time C surface. Handles remain opaque pointers at this boundary.

#![allow(dead_code, reason = "shared by the ABI and executed-kernel integration controls")]

use core::ffi::c_void;

use trust_bignum::Nat;

pub type Binary = unsafe extern "C" fn(*const c_void, *const c_void) -> *mut c_void;

unsafe extern "C" {
    pub fn trust_bignum_nat_from_u64(value: u64) -> *mut c_void;
    pub fn trust_bignum_nat_add(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_sub(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_mul(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_div(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_mod(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_beq(a: *const c_void, b: *const c_void) -> bool;
    pub fn trust_bignum_nat_ble(a: *const c_void, b: *const c_void) -> bool;
    pub fn trust_bignum_nat_is_zero(a: *const c_void) -> bool;
    pub fn trust_bignum_nat_fits_u64(a: *const c_void) -> bool;
    pub fn trust_bignum_nat_to_u64(a: *const c_void) -> u64;
    pub fn trust_bignum_nat_clone(a: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_drop(a: *mut c_void);
    pub fn trust_bignum_nat_land(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_lor(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_xor(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_shift_left(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_shift_right(a: *const c_void, b: *const c_void) -> *mut c_void;
    pub fn trust_bignum_nat_pow(a: *const c_void, b: *const c_void) -> *mut c_void;
}

/// A test caller owning exactly one runtime allocation. No Clone implementation:
/// a second owner is obtained only through the actual pinned clone entry point.
pub struct Handle(*mut c_void);

impl Handle {
    pub fn new(value: u64) -> Self {
        let pointer = unsafe { trust_bignum_nat_from_u64(value) };
        assert!(!pointer.is_null());
        Self(pointer)
    }

    /// Build inputs through the ORIGINAL from_u64/add ABI only. The shift,
    /// power and bitwise operations under test do not construct their operands.
    pub fn from_limbs(limbs: &[u64]) -> Self {
        let mut result = Self::new(0);
        for &limb in limbs.iter().rev() {
            for _ in 0..64 {
                result = result.apply(trust_bignum_nat_add, &result);
            }
            result = result.apply(trust_bignum_nat_add, &Self::new(limb));
        }
        assert_eq!(result.value().limbs(), Nat::from_limbs(limbs.to_vec()).limbs());
        result
    }

    pub fn apply(&self, operation: Binary, other: &Self) -> Self {
        let pointer = unsafe { operation(self.0, other.0) };
        assert!(!pointer.is_null());
        Self(pointer)
    }

    pub fn duplicate(&self) -> Self {
        let pointer = unsafe { trust_bignum_nat_clone(self.0) };
        assert!(!pointer.is_null());
        Self(pointer)
    }

    pub fn pointer(&self) -> *mut c_void {
        self.0
    }

    /// Rust-side observation of the concrete Nat the runtime allocated. This
    /// is a pointer borrow, never an integer-to-Nat or abstract-Handle retag.
    pub fn value(&self) -> &Nat {
        unsafe { &*self.0.cast::<Nat>() }
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe { trust_bignum_nat_drop(self.0) }
    }
}
