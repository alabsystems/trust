// SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#pragma once

#include <type_traits>
#include <utility>

namespace tpde::util {

template <typename F>
class function_ref;

template <typename R, typename... Args>
class function_ref<R(Args...)> {
  R (*call)(void *fn, Args... args) = nullptr;
  void *fn;

public:
  function_ref(const function_ref &) = default;

  template <typename F>
  function_ref(F &&fn)
    requires std::is_invocable_r_v<R, F, Args...>
      : fn(const_cast<void *>(static_cast<const void *>(&fn))) {
    call = [](void *fn, Args... args) -> R {
      return (*static_cast<std::remove_reference_t<F> *>(fn))(
          std::forward<Args>(args)...);
    };
  }

  R operator()(Args... args) const {
    return call(fn, std::forward<Args>(args)...);
  }
};

} // namespace tpde::util
