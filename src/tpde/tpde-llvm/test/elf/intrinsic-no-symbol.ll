; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-llc --target=x86_64 < %s | llvm-readelf -s - | FileCheck %s
; RUN: tpde-llc --target=aarch64 < %s | llvm-readelf -s - | FileCheck %s

; CHECK: Symbol table '.symtab'
; CHECK-NOT: llvm.donothing

declare void @llvm.donothing()

define void @use() {
  call void @llvm.donothing()
  ret void
}
