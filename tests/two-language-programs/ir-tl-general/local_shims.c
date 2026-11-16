/* TEST-LOCAL shims — NOT part of Clean. Written by the parta-lean battery.
 * Clean HEAD (fdda6ac58257) ships a PreludeShim for l_UInt32_ofNat
 * (clean-cli/src/native_build.rs:232-239) but NONE for l_UInt64_ofNat / l_UInt8_ofNat,
 * which the trust-ir backend leaves as undefined externs. These two definitions are the
 * exact analogue of Clean's own UInt32 shim (UIntN.ofNat n = n % 2^N, argument consumed).
 * They are linked ONLY in the second, separately-reported link attempt. */
#include <stdint.h>
#include "clean_runtime.h"
clean_obj* l_UInt64_ofNat(clean_obj* n) {
  unsigned __int128 v = clean_nat_to_u128(n);
  clean_dec(n);
  return clean_nat_of_u64((uint64_t)v);
}
clean_obj* l_UInt8_ofNat(clean_obj* n) {
  unsigned __int128 v = clean_nat_to_u128(n);
  clean_dec(n);
  return clean_nat_of_u64((uint64_t)(v & 0xFFu));
}
