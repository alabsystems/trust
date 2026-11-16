#ifndef RUSTC_LLVM_THINLTO_CACHE_KEY_H
#define RUSTC_LLVM_THINLTO_CACHE_KEY_H

#include <optional>
#include <string>
#include <string_view>

namespace RustThinLTO {

// String-only LLVM APIs do not report an authenticated own-build namespace.
// Keep compilation supported without authorizing reuse from such a key.
inline std::optional<std::string_view>
cacheKeyWithIdentity(const std::string &) {
  return std::nullopt;
}

inline std::optional<std::string_view>
cacheKeyWithIdentity(const std::optional<std::string> &Key) {
  if (!Key || Key->empty())
    return std::nullopt;
  return std::string_view(*Key);
}

} // namespace RustThinLTO

#endif
