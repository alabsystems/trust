; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-lli %s | FileCheck %s
; RUN: tpde-lli --orc %s | FileCheck %s

@hello = private constant [6 x i8] c"Hello\00", align 1
@stdout = external local_unnamed_addr global ptr, align 8

define i32 @main() {
; CHECK: HelloHello
  %stdout = load ptr, ptr @stdout, align 8
  %w = tail call i64 @fwrite(ptr nonnull @hello, i64 5, i64 1, ptr %stdout)
  %p = call i32 @puts(ptr @hello)
  ret i32 0
}

declare i32 @puts(ptr)
declare i64 @fwrite(ptr, i64, i64, ptr)
