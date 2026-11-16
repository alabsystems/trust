; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-lli %s
; RUN: tpde-lli --orc %s

define i32 @main() {
  ret i32 0
}
