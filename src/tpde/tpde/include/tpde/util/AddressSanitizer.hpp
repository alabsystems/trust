// SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#pragma once

#include <cstddef>

#if __has_feature(address_sanitizer) || defined(__SANITIZE_ADDRESS__)
  #define TPDE_ASAN_BUILD
extern "C" void __asan_poison_memory_region(void const volatile *p,
                                            size_t size);
extern "C" void __asan_unpoison_memory_region(void const volatile *p,
                                              size_t size);
#endif

namespace tpde::util {

#if defined(TPDE_ASAN_BUILD)
constexpr const bool address_sanitizer_active = true;
#else
constexpr const bool address_sanitizer_active = false;
#endif

[[gnu::always_inline]] static inline void
    poison_memory_region([[maybe_unused]] void const volatile *p,
                         [[maybe_unused]] size_t size) {
#if defined(TPDE_ASAN_BUILD)
  __asan_poison_memory_region(p, size);
#endif
}

[[gnu::always_inline]] static inline void
    unpoison_memory_region([[maybe_unused]] void const volatile *p,
                           [[maybe_unused]] size_t size) {
#if defined(TPDE_ASAN_BUILD)
  __asan_unpoison_memory_region(p, size);
#endif
}

} // namespace tpde::util
