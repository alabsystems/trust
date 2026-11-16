; NOTE: Do not autogenerate
; SPDX-FileCopyrightText: 2025 Contributors to TPDE <https://tpde.org>
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; RUN: tpde-lli %s | FileCheck %s
; RUN: tpde-lli --orc %s | FileCheck %s

; CHECK: caught exception

@_ZTIi = external constant ptr

declare ptr @__cxa_allocate_exception(i64)
declare void @__cxa_throw(ptr, ptr, ptr)
declare ptr @__cxa_begin_catch(ptr)
declare void @__cxa_end_catch()
declare i32 @__gxx_personality_v0(...)
declare i32 @puts(ptr)

@msg = private unnamed_addr constant [17 x i8] c"caught exception\00", align 1

define i32 @main() personality ptr @__gxx_personality_v0 {
  %ex = call ptr @__cxa_allocate_exception(i64 4)
  store i32 0, ptr %ex, align 16
  invoke void @__cxa_throw(ptr nonnull %ex, ptr nonnull @_ZTIi, ptr null)
          to label %ret unwind label %unwind

ret:
  ret i32 1

unwind:
  %lp = landingpad { ptr, i32 }
          catch ptr null
  %lpex = extractvalue { ptr, i32 } %lp, 0
  %begin_catch = call ptr @__cxa_begin_catch(ptr %lpex)
  %puts = call i32 @puts(ptr @msg)
  call void @__cxa_end_catch()
  ret i32 0
}
