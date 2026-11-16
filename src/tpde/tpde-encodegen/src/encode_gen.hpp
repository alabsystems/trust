// SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
//
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
#pragma once

#include <llvm/CodeGen/MachineFunction.h>

namespace tpde_encgen {
bool create_encode_function(llvm::MachineFunction *,
                            std::string_view name,
                            std::string &decl_lines,
                            unsigned &sym_count,
                            std::string &impl_lines);
}
